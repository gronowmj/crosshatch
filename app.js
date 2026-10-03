/* Crosshatch – a small daily cryptic. Plain JS, no build step. */
(function () {
  'use strict';

  var STORE_PREFIX = 'crosshatch:v1:';   // unchanged key: older saves load and are migrated in place
  var SAVE_VERSION = 3;
  var START_SCORE = 100;
  // A word can be checked only once it is full, for −5, and only the first time.
  // There is no letter check and no grid check. Reveal word is a flat −20 once
  // per word. First letter of the selected clue is −8 once. A plain clue is −10
  // once. Time never counts.
  var COST = { 'check-word': 5, 'reveal-first': 8, 'reveal-word': 20, 'plain-clue': 10 };
  var LABEL = {
    'check-word': 'Word check',
    'reveal-letter': 'First letter',
    'reveal-first': 'First letter',
    'reveal-word': 'Revealed word',
    'reveal-grid': 'Grid revealed',
    'plain-clue': 'Plain clue'
  };
  var $ = function (id) { return document.getElementById(id); };
  var reduceMotion = window.matchMedia && window.matchMedia('(prefers-reduced-motion: reduce)').matches;

  // ---------------------------------------------------------------- dates
  function pad(n) { return (n < 10 ? '0' : '') + n; }
  function localISO(d) { return d.getFullYear() + '-' + pad(d.getMonth() + 1) + '-' + pad(d.getDate()); }
  function todayISO() {
    var q = new URLSearchParams(location.search).get('today'); // testing override
    return (q && /^\d{4}-\d{2}-\d{2}$/.test(q)) ? q : localISO(new Date());
  }
  function dateObj(iso) { var p = iso.split('-'); return new Date(+p[0], +p[1] - 1, +p[2]); }
  function prettyDate(iso, style) {
    var o = style === 'short' ? { weekday: 'short', day: 'numeric', month: 'short' }
      : style === 'medium' ? { weekday: 'short', day: 'numeric', month: 'short', year: 'numeric' }
      : { weekday: 'long', day: 'numeric', month: 'long', year: 'numeric' };
    return dateObj(iso).toLocaleDateString('en-GB', o).replace(',', '');
  }
  function fmtTime(ms) {
    var s = Math.floor(ms / 1000), h = Math.floor(s / 3600), m = Math.floor((s % 3600) / 60);
    s = s % 60;
    return h ? h + ':' + pad(m) + ':' + pad(s) : m + ':' + pad(s);
  }
  function plural(n, one, many) { return n + ' ' + (n === 1 ? one : (many || one + 's')); }

  // ---------------------------------------------------------------- hashing
  var subtle = (window.isSecureContext && window.crypto && window.crypto.subtle) ? window.crypto.subtle : null;
  function sha256(str) {
    if (subtle) return subtle.digest('SHA-256', new TextEncoder().encode(str)).then(function (b) { return new Uint8Array(b); });
    return Promise.resolve(window.sha256Bytes(str));
  }
  function hex(bytes) {
    var s = '';
    for (var i = 0; i < bytes.length; i++) s += (bytes[i] < 16 ? '0' : '') + bytes[i].toString(16);
    return s;
  }

  // ---------------------------------------------------------------- state
  var index = [];
  var P = null;          // puzzle JSON (format unchanged)
  var S = null;          // saved progress
  var words = [];        // [{dir,num,text,plain,enumeration,cells,el,li,hint}]
  var hasPlain = false;  // puzzle carries plain ('quick') clues (older puzzle files don't)
  var cellWords = [];
  var cellEls = [];
  var goodWords = {};    // word index -> true when the word is complete and correct (free, not a check)
  var sel = 0, dir = 'across';
  var keystreamCache = null;
  var timerStart = null;
  var userPaused = false;
  var wasFull = false;
  var lastTyped = -1;
  var gen = 0;           // bumps on every letter change, to discard stale async results

  function storeKey(date) { return STORE_PREFIX + date; }
  function blankState(n) {
    var st = { v: SAVE_VERSION, letters: [], revealed: [], checked: [], elapsed: 0, completed: false, solved: false,
      completedAt: null, deductions: [], gaveUp: false, plain: [] };
    for (var i = 0; i < n; i++) { st.letters.push(''); st.revealed.push(false); st.checked.push(0); }
    return st;
  }
  // Saves written before v3 (no score data, or the live harsh migration of 5 per revealed
  // letter and 1 per checked letter) are re-scored ONCE from the letter flags:
  //   each word that owns any revealed letter costs the new reveal-word price (−20), not per letter;
  //   stray checked letters are NOT a word check (the old save cannot prove one) unless a
  //   deduction already names the word; plain clues already recorded cost −10 each.
  // First-letter (−8) did not exist, so it is not invented on top of the −20.
  // A crossing is charged on the word with the most revealed letters, so it is not billed twice.
  var entryCache = {};
  function entriesOf(puz) {
    var out = [];
    ['across', 'down'].forEach(function (d) {
      ((puz.clues || {})[d] || []).forEach(function (c) {
        out.push({ k: c.num + (d === 'across' ? 'A' : 'D'), cells: c.cells || [] });
      });
    });
    return out;
  }
  function isLegacyDeduction(d) {
    return d && (d.t === 'legacy-reveal' || d.t === 'legacy-check' || d.t === 'migrated-reveal' || d.t === 'migrated-check');
  }
  function needsRescore(st) {
    if (!Array.isArray(st.deductions)) return true;
    if (st.deductions.some(isLegacyDeduction)) return true;
    return st.v !== SAVE_VERSION;
  }
  function revealedWordKeys(revealed, entries) {
    var n = revealed.length, i;
    var ents = (entries || []).map(function (e) {
      return { k: e.k, cells: (e.cells || []).filter(function (ci) { return ci >= 0 && ci < n; }) };
    }).filter(function (e) { return e.cells.length; });
    var R = [];
    for (i = 0; i < n; i++) R.push(!!revealed[i]);
    var rCount = ents.map(function (e) { return e.cells.filter(function (ci) { return R[ci]; }).length; });
    var inEntry = [];
    for (i = 0; i < n; i++) inEntry.push([]);
    ents.forEach(function (e, ei) { e.cells.forEach(function (ci) { inEntry[ci].push(ei); }); });
    var assigned = ents.map(function () { return 0; });
    for (i = 0; i < n; i++) {
      if (!R[i]) continue;
      var best = -1;
      inEntry[i].forEach(function (ei) {
        if (best < 0 || rCount[ei] > rCount[best] || (rCount[ei] === rCount[best] && ei < best)) best = ei;
      });
      if (best >= 0) assigned[best]++;
    }
    var keys = [];
    ents.forEach(function (e, ei) { if (assigned[ei]) keys.push(e.k); });
    return keys;
  }
  function rescoreOld(st, entries) {
    var at = Date.now();
    var gaveUp = !!st.gaveUp || (st.deductions || []).some(function (d) { return d.t === 'reveal-grid'; });
    var plain = [];
    (Array.isArray(st.plain) ? st.plain : []).forEach(function (k) { if (plain.indexOf(k) < 0) plain.push(k); });
    (st.deductions || []).forEach(function (d) {
      if (d && d.t === 'plain-clue' && d.w && plain.indexOf(d.w) < 0) plain.push(d.w);
    });
    var deds = [];
    var revealedKeys = revealedWordKeys(st.revealed, entries);
    revealedKeys.forEach(function (k) {
      deds.push({ t: 'reveal-word', c: COST['reveal-word'], n: 1, w: k, at: at });
    });
    // Per-cell checked flags (and a single legacy-check total) cannot prove the player
    // used "check word" on a completed entry rather than checking letters one by one.
    // Only an old deduction that already names the word (t: check-word, w: "3A") counts,
    // and not when that word was fully revealed.
    var seenCheck = {};
    (st.deductions || []).forEach(function (d) {
      if (!d || d.t !== 'check-word' || !d.w || seenCheck[d.w]) return;
      var ent = null;
      (entries || []).forEach(function (e) { if (e.k === d.w) ent = e; });
      if (!ent || !ent.cells.length) return;
      var filled = ent.cells.every(function (ci) { return !!(st.letters && st.letters[ci]); });
      var fullyRevealed = ent.cells.every(function (ci) { return !!(st.revealed && st.revealed[ci]); });
      if (!filled || fullyRevealed) return;
      seenCheck[d.w] = true;
      deds.push({ t: 'check-word', c: COST['check-word'], n: 1, w: d.w, at: at });
    });
    plain.forEach(function (k) {
      deds.push({ t: 'plain-clue', c: COST['plain-clue'], n: 1, w: k, at: at });
    });
    st.plain = plain;
    st.gaveUp = gaveUp;
    if (gaveUp) {
      var sum = 0;
      deds.forEach(function (d) { sum += d.c; });
      deds.push({ t: 'reveal-grid', c: Math.max(0, START_SCORE - sum), at: at });
    }
    st.deductions = deds;
    st.v = SAVE_VERSION;
    return st;
  }
  function migrate(st, n, entries) {
    if (!Array.isArray(st.revealed) || st.revealed.length !== n) st.revealed = st.letters.map(function () { return false; });
    if (!Array.isArray(st.checked) || st.checked.length !== n) st.checked = st.letters.map(function () { return 0; });
    st.elapsed = +st.elapsed || 0;
    if (!Array.isArray(st.plain)) st.plain = [];
    if (!needsRescore(st)) {
      st.gaveUp = !!st.gaveUp;
      st.v = SAVE_VERSION;
      return st;
    }
    // Without the puzzle's words a revealed crossing can't be grouped; leave the save
    // untouched (and unversioned) until the word list is available, then score it once.
    if (!entries || !entries.length) return st;
    return rescoreOld(st, entries);
  }
  function loadState(date, n) {
    var st = null;
    try { st = JSON.parse(localStorage.getItem(storeKey(date)) || 'null'); } catch (e) { st = null; }
    if (!st || !Array.isArray(st.letters) || st.letters.length !== n) return blankState(n);
    return migrate(st, n, entryCache[date]);
  }
  function saveState() {
    if (!P || !S) return;
    var copy = Object.assign({}, S, { elapsed: Math.round(elapsed()), score: scoreOf(S), updated: new Date().toISOString() });
    try { localStorage.setItem(storeKey(P.date), JSON.stringify(copy)); } catch (e) { /* private mode / full */ }
  }
  function rawState(date) {
    try {
      var st = JSON.parse(localStorage.getItem(storeKey(date)) || 'null');
      if (st && Array.isArray(st.letters)) return st;
    } catch (e) { /* ignore */ }
    return null;
  }
  function peekState(date) {
    var st = rawState(date);
    return st ? migrate(st, st.letters.length, entryCache[date]) : null;
  }
  function migrateStored(dates) {
    var todo = dates.filter(function (d) {
      if (P && S && P.date === d) return false;
      var st = rawState(d);
      return st && needsRescore(st);
    });
    return Promise.all(todo.map(function (d) {
      var ready = entryCache[d] ? Promise.resolve() : fetchJSON('puzzles/' + d + '.json').then(function (puz) {
        entryCache[d] = entriesOf(puz);
      });
      return ready.then(function () {
        var st = rawState(d);
        if (!st || !needsRescore(st) || !entryCache[d]) return;
        migrate(st, st.letters.length, entryCache[d]);
        st.score = scoreOf(st);
        try { localStorage.setItem(storeKey(d), JSON.stringify(st)); } catch (e) { /* ignore */ }
      }).catch(function () { /* offline: shown again once the puzzle itself is opened */ });
    }));
  }

  // ---------------------------------------------------------------- scoring
  function scoreOf(st) {
    if (!st) return START_SCORE;
    if (st.gaveUp) return 0;
    var sum = 0;
    (st.deductions || []).forEach(function (d) { sum += d.c; });
    return Math.max(0, START_SCORE - sum);
  }
  function deduct(type, cost, extra) {
    if (cost <= 0) return;
    var before = scoreOf(S);
    S.deductions.push(Object.assign({ t: type, c: cost, at: Date.now() }, extra || {}));
    saveState();
    renderScore(before);
  }
  function groupedDeductions(st) {
    var groups = [], byType = {};
    (st.deductions || []).forEach(function (d) {
      var g = byType[d.t];
      if (!g) { g = byType[d.t] = { t: d.t, count: 0, cost: 0 }; groups.push(g); }
      g.count += d.n || 1;
      g.cost += d.c;
    });
    return groups;
  }
  function helpCount(st) {
    var n = 0;
    (st.deductions || []).forEach(function (d) { n += d.n || 1; });
    return n;
  }
  function renderScore(before) {
    var now = scoreOf(S);
    $('score-val').textContent = now;
    if (before !== undefined && now < before) {
      var pill = $('score');
      pill.classList.remove('hit');
      void pill.offsetWidth;
      pill.classList.add('hit');
      var f = document.createElement('span');
      f.className = 'float-deduct';
      f.textContent = '−' + (before - now);
      $('stats').appendChild(f);
      setTimeout(function () { f.remove(); }, 1500);
    }
  }

  // ---------------------------------------------------------------- timer
  function elapsed() {
    if (!S) return 0;
    return S.elapsed + (timerStart !== null ? performance.now() - timerStart : 0);
  }
  function running() { return timerStart !== null; }
  function shouldRun() {
    return !!(P && S && !S.completed && !userPaused && document.visibilityState === 'visible' && !$('view-puzzle').hidden);
  }
  function syncTimer() {
    if (shouldRun() && !running()) timerStart = performance.now();
    else if (!shouldRun() && running()) {
      S.elapsed += performance.now() - timerStart;
      timerStart = null;
      saveState();
    }
    renderTimer();
  }
  function renderTimer() {
    $('timer-val').textContent = fmtTime(elapsed());
    var t = $('timer');
    t.classList.toggle('done', !!(S && S.completed));
    t.setAttribute('aria-label', userPaused ? 'Resume timer' : 'Pause timer');
  }
  function setPaused(p) {
    if (S && S.completed) p = false;
    userPaused = p;
    $('paused').hidden = !p;
    $('view-puzzle').classList.toggle('is-paused', p);
    syncTimer();
  }

  // ---------------------------------------------------------------- loading & routing
  function fetchJSON(url) {
    return fetch(url, { cache: 'no-cache' }).then(function (r) {
      if (!r.ok) throw new Error(url + ': HTTP ' + r.status);
      return r.json();
    });
  }
  function released() {
    var t = todayISO();
    return index.filter(function (e) { return e.date <= t; });
  }
  function defaultDate() {
    var r = released();
    if (r.length) return r[r.length - 1].date;
    return index.length ? index[0].date : null;
  }
  function route() {
    var h = location.hash || '';
    var m = h.match(/^#\/p\/(\d{4}-\d{2}-\d{2})$/);
    closeOverlays();
    if (h === '#/archive') return showArchive();
    var date = m ? m[1] : defaultDate();
    if (!date) return showError('No puzzles yet.');
    showPuzzleView();
    if (!P || P.date !== date) openPuzzle(date);
    else { syncTimer(); render(); }
  }
  function closeOverlays() {
    ['menu', 'rules', 'modal', 'finish'].forEach(function (id) { $(id).hidden = true; });
    stopFireworks();
  }
  function showError(msg) {
    showPuzzleView();
    $('load-error').hidden = false;
    $('load-error').textContent = msg;
  }
  function showPuzzleView() {
    $('view-archive').hidden = true;
    $('view-puzzle').hidden = false;
    $('dock').hidden = false;
    $('stats').hidden = false;
    $('btn-menu').hidden = false;
  }
  function puzzleName() { return (P && P.title) || ('Crosshatch ' + (P ? P.date : '')); }

  function openPuzzle(date) {
    if (P && S) { syncTimer(); saveState(); }
    timerStart = null;
    userPaused = false;
    $('paused').hidden = true;
    $('view-puzzle').classList.remove('is-paused');
    return fetchJSON('puzzles/' + date + '.json').then(function (puz) {
      P = puz;
      keystreamCache = null;
      entryCache[P.date] = entriesOf(P);
      S = loadState(P.date, P.cells.length);
      saveState();   // persist any migration immediately
      $('load-error').hidden = true;
      goodWords = {};
      buildPuzzle();
      var preview = P.date > todayISO();
      var num = (P.title || '').match(/No\.\s*\d+/);
      $('subtitle').textContent = [num ? num[0] : '', prettyDate(P.date, 'short'), preview ? 'Preview' : '']
        .filter(Boolean).join(' · ');
      document.title = 'Crosshatch – ' + prettyDate(P.date, 'medium');
      wasFull = isFull();
      renderScore();
      syncTimer();
      evaluateWords(words.map(function (_, i) { return i; }), false);
    }).catch(function (err) {
      P = null; S = null;
      showError('Sorry, that puzzle could not be loaded. (' + err.message + ')');
    });
  }

  // ---------------------------------------------------------------- building
  var TICK = '<svg class="tick" viewBox="0 0 24 24" aria-hidden="true"><path d="M5 12.5l4.2 4.2L19 7"/></svg>';
  function buildPuzzle() {
    words = [];
    ['across', 'down'].forEach(function (d) {
      P.clues[d].forEach(function (c) {
        words.push({ dir: d, num: c.num, text: c.text, plain: (typeof c.plain === 'string' ? c.plain.trim() : ''), enumeration: c.enum, cells: c.cells });
      });
    });
    hasPlain = words.some(function (w) { return !!w.plain; });
    cellWords = P.cells.map(function () { return { across: null, down: null }; });
    words.forEach(function (w, wi) { w.cells.forEach(function (ci) { cellWords[ci][w.dir] = wi; }); });

    var grid = $('grid');
    grid.innerHTML = '';
    cellEls = [];
    P.cells.forEach(function (cell, i) {
      var el = document.createElement('div');
      el.className = 'cell';
      el.setAttribute('role', 'gridcell');
      el.dataset.i = i;
      el.style.left = 'calc(var(--cell) * ' + cell.c + ')';
      el.style.top = 'calc(var(--cell) * ' + cell.r + ')';
      if (cell.n) {
        var n = document.createElement('span');
        n.className = 'num';
        n.textContent = cell.n;
        el.appendChild(n);
      }
      var l = document.createElement('span');
      l.className = 'letter';
      el.appendChild(l);
      grid.appendChild(el);
      cellEls.push(el);
    });
    sizeGrid();

    ['across', 'down'].forEach(function (d) {
      var ul = $('clues-' + d);
      ul.innerHTML = '';
      words.forEach(function (w, wi) {
        if (w.dir !== d) return;
        var li = document.createElement('li');
        li.className = 'clue-item';
        var b = document.createElement('button');
        b.type = 'button';
        b.className = 'clue';
        b.dataset.w = wi;
        b.innerHTML = '<span class="cnum"></span><span class="cbody"><span class="ctext"></span> <span class="enum"></span>' +
          '<span class="cplain" hidden><span class="plain-tag">Plain:</span> <span class="ptext"></span> <span class="penum"></span></span></span>' + TICK;
        b.querySelector('.cnum').textContent = w.num;
        b.querySelector('.ctext').textContent = w.text;
        b.querySelector('.enum').textContent = w.enumeration;
        li.appendChild(b);
        if (w.plain) {
          var h = document.createElement('button');
          h.type = 'button';
          h.className = 'hint-btn';
          h.dataset.w = wi;
          h.hidden = true;
          h.innerHTML = '<span>Plain clue</span> <span class="hint-cost">· −' + COST['plain-clue'] + '</span>';
          h.setAttribute('aria-label', 'Show a plain clue for ' + w.num + ' ' + w.dir + ' (costs ' + COST['plain-clue'] + ' points)');
          li.appendChild(h);
          w.hint = h;
        }
        ul.appendChild(li);
        w.el = b;
        w.li = li;
      });
    });
    dir = words[0].dir;
    sel = firstEmpty(words[0]);
    render();
  }
  function sizeGrid() {
    if (!P) return;
    var wrap = $('grid-wrap');
    var avail = wrap.clientWidth || (window.innerWidth - 28);
    var maxByWidth = Math.floor((avail - 6) / P.width);
    var mainH = $('view-puzzle').clientHeight || (window.innerHeight * 0.6);
    var maxByHeight = Math.floor((mainH - 170) / P.height);   // keep ~170px for the first clues
    // prefer a comfortable tap size (>= 30px) and let the clue list scroll if space is tight
    var size = Math.max(22, Math.min(46, maxByWidth, Math.max(30, maxByHeight)));
    document.documentElement.style.setProperty('--cell', size + 'px');
    document.documentElement.style.setProperty('--gap', (size >= 30 ? 4 : 3) + 'px');
    document.documentElement.style.setProperty('--dock-h', ($('dock').hidden ? 0 : $('dock').offsetHeight) + 'px');
    var grid = $('grid');
    grid.style.width = (size * P.width) + 'px';
    grid.style.height = (size * P.height) + 'px';
  }

  // ---------------------------------------------------------------- rendering
  function currentWord() {
    var wi = cellWords[sel][dir];
    if (wi === null) { dir = dir === 'across' ? 'down' : 'across'; wi = cellWords[sel][dir]; }
    return words[wi];
  }
  function render() {
    if (!P) return;
    var w = currentWord();
    var showSel = !S.completed;
    var inWord = {};
    if (showSel) w.cells.forEach(function (ci) { inWord[ci] = true; });
    cellEls.forEach(function (el, i) {
      var letter = S.letters[i] || '';
      var span = el.querySelector('.letter');
      if (span.textContent !== letter) {
        span.textContent = letter;
        if (letter && i === lastTyped && !reduceMotion) {
          span.classList.remove('drop'); void span.offsetWidth; span.classList.add('drop');
        }
      }
      el.classList.toggle('in-word', !!inWord[i]);
      el.classList.toggle('selected', showSel && i === sel);
      el.classList.toggle('revealed', !!S.revealed[i]);
      el.classList.toggle('correct', S.checked[i] === 1 && !S.revealed[i]);
      el.classList.toggle('wrong', S.checked[i] === -1);
      var c = P.cells[i];
      el.setAttribute('aria-label', (c.n ? c.n + ', ' : '') + 'row ' + (c.r + 1) + ', column ' + (c.c + 1) + (letter ? ', ' + letter : ', empty'));
    });
    lastTyped = -1;
    var crossWi = cellWords[sel][dir === 'across' ? 'down' : 'across'];
    words.forEach(function (x, wi) {
      x.el.classList.toggle('active', showSel && x === w);
      x.el.classList.toggle('cross', showSel && wi === crossWi);
      x.el.classList.toggle('filled', x.cells.every(function (ci) { return !!S.letters[ci]; }));
      x.el.classList.toggle('good', !!goodWords[wi]);
    });
    var bar = $('clue-bar-text');
    bar.innerHTML = '';
    var chip = document.createElement('span');
    chip.className = 'chip';
    chip.textContent = w.num + (w.dir === 'across' ? 'A' : 'D');
    var txt = document.createElement('span');
    txt.className = 'bar-lines';
    var main = document.createElement('span');
    main.className = 'bar-cryptic';
    main.textContent = w.text + ' ' + w.enumeration;
    txt.appendChild(main);
    if (plainShown(w)) {
      var pl = document.createElement('span');
      pl.className = 'bar-plain';
      var tag = document.createElement('span');
      tag.className = 'plain-tag';
      tag.textContent = 'Plain:';
      pl.appendChild(tag);
      pl.appendChild(document.createTextNode(' ' + w.plain + ' ' + w.enumeration));
      txt.appendChild(pl);
    }
    bar.appendChild(chip);
    bar.appendChild(txt);
    renderPlain();

    var dock = $('dock');
    if (dock.classList.contains('complete') !== !!S.completed) {
      dock.classList.toggle('complete', !!S.completed);
      setTimeout(sizeGrid, 0);
    }
    $('done-bar').hidden = !S.completed;
    if (S.completed) {
      $('done-text').innerHTML = '';
      var big = document.createElement('span');
      big.className = 'big';
      big.textContent = scoreOf(S) + ' pts';
      $('done-text').appendChild(big);
      $('done-text').appendChild(document.createTextNode(' · ' + fmtTime(S.elapsed) + (S.gaveUp ? ' · revealed' : ' · solved')));
    }
    renderScore();
    renderTimer();
    $('menu').classList.toggle('is-complete', !!S.completed);
  }
  // ---------------------------------------------------------------- plain clue (paid hint)
  function wordKey(w) { return w.num + (w.dir === 'across' ? 'A' : 'D'); }
  function plainShown(w) { return !!(w && w.plain && S && S.plain.indexOf(wordKey(w)) >= 0); }
  function wordSolved(wi) {
    // complete and correct (the free word-complete detection), or every letter revealed/confirmed
    return !!goodWords[wi] || words[wi].cells.every(function (ci) { return locked(ci); });
  }
  function plainStatus(wi) {
    var w = words[wi];
    if (!w || !w.plain) return 'none';
    if (plainShown(w)) return 'shown';
    if (S.completed || wordSolved(wi)) return 'solved';
    return 'available';
  }
  function renderPlain() {
    if (!P || !S) return;
    var cur = words.indexOf(currentWord());
    words.forEach(function (w, wi) {
      var box = w.el.querySelector('.cplain');
      var shown = plainShown(w);
      if (shown && box.hidden) {
        box.querySelector('.ptext').textContent = w.plain;
        box.querySelector('.penum').textContent = w.enumeration;
      }
      box.hidden = !shown;
      if (w.hint) {
        var offer = !S.completed && wi === cur && plainStatus(wi) === 'available';
        w.hint.hidden = !offer;
        w.li.classList.toggle('with-hint', offer);
      }
    });
  }
  function wordFilled(w) {
    return !!(w && w.cells.every(function (ci) { return !!S.letters[ci]; }));
  }
  function wordFullyLocked(w) {
    return !!(w && w.cells.length && w.cells.every(function (ci) { return locked(ci); }));
  }
  // incomplete | confirmed | again | ready
  function checkWordState(w) {
    w = w || currentWord();
    if (!P || !S || !w) return { state: 'incomplete', reason: 'Fill the word first', cost: '−' + COST['check-word'], disabled: true };
    if (!wordFilled(w)) return { state: 'incomplete', reason: 'Fill the word first', cost: '−' + COST['check-word'], disabled: true };
    if (wordFullyLocked(w)) return { state: 'confirmed', reason: 'Already confirmed', cost: 'free', disabled: true };
    if (chargedWord('check-word', wordKey(w))) return { state: 'again', reason: 'Already checked', cost: 'free', disabled: false };
    return { state: 'ready', reason: 'Word is full', cost: '−' + COST['check-word'], disabled: false };
  }
  function firstLetterFree() {
    if (!P || !S) return false;
    var w = currentWord();
    return !!(S.completed || locked(w.cells[0]));
  }
  function renderMenu() {
    var sec = $('menu-plain');
    sec.hidden = !hasPlain;
    var fc = $('first-cost'), fb = document.querySelector('[data-action="reveal-first"]');
    if (fc && P && S) {
      var free = firstLetterFree();
      fc.textContent = free ? 'free' : '−' + COST['reveal-first'];
      if (fb) {
        fb.classList.toggle('is-disabled', free);
        fb.setAttribute('aria-disabled', free ? 'true' : 'false');
      }
    }
    var cb = $('opt-check');
    if (cb && P && S) {
      var cw = checkWordState();
      $('check-for').textContent = cw.reason;
      $('check-cost').textContent = cw.cost;
      $('check-cost').classList.toggle('free', cw.cost === 'free');
      cb.classList.toggle('is-disabled', cw.disabled);
      cb.setAttribute('aria-disabled', cw.disabled ? 'true' : 'false');
      cb.setAttribute('aria-label', 'Check word (' + cw.reason + ', ' + cw.cost + ')');
    }
    if (!hasPlain || !P) return;
    var w = currentWord(), wi = words.indexOf(w), st = plainStatus(wi);
    var b = $('opt-plain');
    var name = w.num + ' ' + (w.dir === 'across' ? 'Across' : 'Down');
    $('plain-for').textContent = st === 'none' ? 'Not available for ' + name
      : st === 'solved' ? name + ' is already solved'
      : st === 'shown' ? 'Shown for ' + name
      : 'For ' + name;
    $('plain-cost').textContent = st === 'shown' ? 'free' : st === 'available' ? '−' + COST['plain-clue'] : '';
    var off = st === 'none' || st === 'solved';
    b.classList.toggle('is-disabled', off);
    b.classList.toggle('is-shown', st === 'shown');
    b.setAttribute('aria-disabled', off ? 'true' : 'false');
  }
  function usePlain(wi) {
    if (!P || S.completed) return;
    var w = words[wi], st = plainStatus(wi);
    if (st === 'none') { toast('No plain clue for this one'); return; }
    if (st === 'solved') { toast('Already solved – no plain clue needed'); return; }
    if (st === 'shown') { toast('Plain clue already shown – no charge'); flashPlain(); return; }
    S.plain.push(wordKey(w));
    deduct('plain-clue', COST['plain-clue'], { w: wordKey(w) });
    render();
    flashPlain();
  }
  function flashPlain() {
    var el = document.querySelector('#clue-bar-text .bar-plain');
    if (!el || reduceMotion) return;
    el.classList.remove('fresh'); void el.offsetWidth; el.classList.add('fresh');
  }

  function scrollClueIntoView() {
    var w = currentWord();
    if (w && w.el && w.el.scrollIntoView) {
      var r = w.el.getBoundingClientRect(), v = $('view-puzzle').getBoundingClientRect();
      if (r.bottom > v.bottom || r.top < v.top) w.el.scrollIntoView({ block: 'nearest', behavior: reduceMotion ? 'auto' : 'smooth' });
    }
  }

  // ---------------------------------------------------------------- selection
  function firstEmpty(w) {
    for (var k = 0; k < w.cells.length; k++) if (!S.letters[w.cells[k]]) return w.cells[k];
    return w.cells[0];
  }
  function selectCell(i) {
    if (i === sel) {
      var other = dir === 'across' ? 'down' : 'across';
      if (cellWords[i][other] !== null) dir = other;
    } else {
      sel = i;
      if (cellWords[i][dir] === null) dir = dir === 'across' ? 'down' : 'across';
    }
    render();
  }
  function selectWord(wi, toStart) {
    var w = words[wi];
    dir = w.dir;
    sel = toStart ? w.cells[0] : firstEmpty(w);
    render();
    scrollClueIntoView();
  }
  function toggleDir() {
    var other = dir === 'across' ? 'down' : 'across';
    if (cellWords[sel][other] !== null) { dir = other; render(); }
  }
  function cycleWord(step) {
    var wi = words.indexOf(currentWord());
    selectWord((wi + step + words.length) % words.length);
  }
  function posInWord(w) { return w.cells.indexOf(sel); }
  function locked(i) { return !!S.revealed[i] || S.checked[i] === 1; }
  function nextIncompleteWord(fromWi) {
    for (var k = 1; k <= words.length; k++) {
      var wi = (fromWi + k) % words.length;
      if (words[wi].cells.some(function (ci) { return !S.letters[ci]; })) return wi;
    }
    return null;
  }
  function wordsOf(ci) {
    var out = [];
    if (cellWords[ci].across !== null) out.push(cellWords[ci].across);
    if (cellWords[ci].down !== null) out.push(cellWords[ci].down);
    return out;
  }
  function cellChanged(ci) {
    gen++;
    wordsOf(ci).forEach(function (wi) { delete goodWords[wi]; });
  }

  // ---------------------------------------------------------------- input
  function inputLetter(ch) {
    if (!P || S.completed || userPaused) return;
    ch = ch.toUpperCase();
    var w = currentWord();
    var typedAt = sel;
    if (!locked(sel) && S.letters[sel] !== ch) {
      S.letters[sel] = ch;
      if (S.checked[sel] === -1) S.checked[sel] = 0;
      lastTyped = sel;
      cellChanged(sel);
    }
    var pos = posInWord(w);
    if (pos < w.cells.length - 1) sel = w.cells[pos + 1];
    else {
      var empty = w.cells.filter(function (ci) { return !S.letters[ci]; });
      if (empty.length) sel = empty[0];
      else {
        var nwi = nextIncompleteWord(words.indexOf(w));
        if (nwi !== null) { dir = words[nwi].dir; sel = firstEmpty(words[nwi]); }
      }
    }
    afterChange(wordsOf(typedAt));
  }
  function backspace() {
    if (!P || S.completed || userPaused) return;
    var w = currentWord();
    if (S.letters[sel] && !locked(sel)) {
      S.letters[sel] = ''; S.checked[sel] = 0; cellChanged(sel);
    } else {
      var pos = posInWord(w);
      if (pos > 0) {
        sel = w.cells[pos - 1];
        if (!locked(sel) && S.letters[sel]) { S.letters[sel] = ''; S.checked[sel] = 0; cellChanged(sel); }
      }
    }
    afterChange([]);
  }
  function moveArrow(dr, dc) {
    if (!P) return;
    var want = dr === 0 ? 'across' : 'down';
    if (dir !== want && cellWords[sel][want] !== null) { dir = want; render(); return; }
    var c = P.cells[sel];
    for (var i = 0; i < P.cells.length; i++) {
      if (P.cells[i].r === c.r + dr && P.cells[i].c === c.c + dc) {
        sel = i;
        if (cellWords[sel][dir] === null) dir = dir === 'across' ? 'down' : 'across';
        render();
        return;
      }
    }
  }
  function afterChange(touchedWords) {
    saveState();
    render();
    if (touchedWords && touchedWords.length) evaluateWords(touchedWords, true);
    var full = isFull();
    if (full && !S.completed) verifyComplete(!wasFull);
    wasFull = full;
  }
  function isFull() { return S.letters.every(function (l) { return !!l; }); }

  // ---------------------------------------------------------------- word-complete detection (free)
  function evaluateWords(wis, animate) {
    var myGen = gen;
    wis.forEach(function (wi) {
      var w = words[wi];
      if (goodWords[wi] || !w.cells.every(function (ci) { return !!S.letters[ci]; })) return;
      Promise.all(w.cells.map(cellCorrect)).then(function (res) {
        if (myGen !== gen || !res.every(Boolean) || goodWords[wi]) return;
        goodWords[wi] = true;
        w.el.classList.add('good');
        renderPlain();
        if (animate) celebrateWord(w);
      });
    });
  }
  function celebrateWord(w) {
    if (navigator.vibrate) { try { navigator.vibrate(12); } catch (e) { /* ignore */ } }
    w.cells.forEach(function (ci, k) {
      var el = cellEls[ci];
      el.classList.remove('pop');
      el.style.animationDelay = reduceMotion ? '0ms' : (k * 45) + 'ms';
      void el.offsetWidth;
      el.classList.add('pop');
      setTimeout(function () { el.classList.remove('pop'); el.style.animationDelay = ''; }, 700 + k * 45);
    });
  }

  // ---------------------------------------------------------------- check / reveal
  function cellCorrect(i) {
    if (!S.letters[i]) return Promise.resolve(false);
    return sha256(P.salt + '|' + P.date + '|' + i + '|' + S.letters[i]).then(function (b) { return hex(b) === P.check[i]; });
  }
  function keystream() {
    if (keystreamCache) return Promise.resolve(keystreamCache);
    var n = P.cells.length, blocks = [];
    for (var b = 0; b * 32 < n; b++) blocks.push(sha256('reveal|' + P.date + '|' + P.salt + '|' + b));
    return Promise.all(blocks).then(function (parts) {
      var out = new Uint8Array(parts.length * 32);
      parts.forEach(function (p, k) { out.set(p, k * 32); });
      keystreamCache = out;
      return out;
    });
  }
  function solutionLetter(i, ks) { return String.fromCharCode(parseInt(P.reveal.substr(i * 2, 2), 16) ^ ks[i]); }
  function targetCells(scope) {
    if (scope === 'letter') return [sel];
    if (scope === 'word') return currentWord().cells.slice();
    return P.cells.map(function (_, i) { return i; });
  }
  function chargedWord(type, key) {
    return (S.deductions || []).some(function (d) { return d.t === type && d.w === key; });
  }
  function check(scope) {
    // Letter checks and grid checks are gone. Only a completed word can be checked.
    if (scope !== 'word') return Promise.resolve();
    var w = currentWord();
    var stt = checkWordState(w);
    if (stt.state === 'incomplete') { toast('Fill every letter of the word first – no charge'); return Promise.resolve(); }
    if (stt.state === 'confirmed') { toast('Already confirmed – no charge'); return Promise.resolve(); }
    var cells = w.cells.filter(function (i) { return S.letters[i] && !locked(i); });
    if (!cells.length) { toast('Nothing new to check – no charge'); return Promise.resolve(); }
    if (stt.state === 'ready') deduct('check-word', COST['check-word'], { w: wordKey(w), n: 1 });
    else toast('Already checked this word – no further charge');
    return Promise.all(cells.map(cellCorrect)).then(function (res) {
      var wrong = 0;
      cells.forEach(function (ci, k) { S.checked[ci] = res[k] ? 1 : -1; if (!res[k]) wrong++; });
      toast(wrong ? plural(wrong, 'letter') + ' wrong' : 'All correct');
      afterChange([]);
    });
  }
  function revealFirst() {
    var w = currentWord(), i = w.cells[0], key = wordKey(w);
    if (locked(i)) { toast('Already revealed – no charge'); return Promise.resolve(); }
    return keystream().then(function (ks) {
      var l = solutionLetter(i, ks);
      if (S.letters[i] === l) {
        S.checked[i] = 1;   // already correct: confirm, never charge
        toast('Already correct – no charge');
        afterChange([]);
        return;
      }
      S.letters[i] = l;
      S.revealed[i] = true;
      S.checked[i] = 0;
      cellChanged(i);
      // One charge per letter. A later reveal of this same cell is locked, so it can't bill again.
      if (!chargedWord('reveal-letter', key) && !chargedWord('reveal-first', key)) deduct('reveal-letter', COST['reveal-first'], { w: key });
      var touched = {};
      wordsOf(i).forEach(function (wi) { touched[wi] = true; });
      afterChange([]);
      evaluateWords(Object.keys(touched).map(Number), false);
    });
  }
  function reveal(scope) {
    if (scope === 'first' || scope === 'letter') return revealFirst();
    var cells = targetCells(scope).filter(function (i) { return !locked(i); });
    if (!cells.length) { toast('Already revealed – no charge'); return Promise.resolve(); }
    return keystream().then(function (ks) {
      var changed = 0;
      cells.forEach(function (i) {
        var l = solutionLetter(i, ks);
        if (S.letters[i] === l) { S.checked[i] = 1; }          // already right: just confirm it
        else { S.letters[i] = l; S.revealed[i] = true; S.checked[i] = 0; changed++; cellChanged(i); }
      });
      if (scope === 'grid') {
        var before = scoreOf(S);
        S.deductions.push({ t: 'reveal-grid', c: before, at: Date.now() });
        S.gaveUp = true;
        renderScore(before);
      } else if (changed === 0) {
        toast('Already correct – no charge');
      } else {
        var key = wordKey(currentWord());
        if (chargedWord('reveal-word', key)) toast('This word was already revealed – no further charge');
        else deduct('reveal-word', COST['reveal-word'], { w: key });
      }
      var touched = {};
      cells.forEach(function (i) { wordsOf(i).forEach(function (wi) { touched[wi] = true; }); });
      afterChange([]);
      evaluateWords(Object.keys(touched).map(Number), false);
    });
  }
  function verifyComplete(announceWrong) {
    var myGen = gen;
    return Promise.all(P.cells.map(function (_, i) { return cellCorrect(i); })).then(function (res) {
      if (S.completed) return;
      if (res.every(Boolean)) {
        S.elapsed = elapsed();
        timerStart = null;
        S.completed = true;
        S.solved = !S.revealed.some(Boolean) && !S.gaveUp;
        S.completedAt = new Date().toISOString();
        saveState();
        words.forEach(function (_, wi) { goodWords[wi] = true; });
        render();
        if (!S.gaveUp && !reduceMotion) {
          cellEls.forEach(function (el, i) {
            var c = P.cells[i];
            el.style.animationDelay = ((c.r + c.c) * 35) + 'ms';
            el.classList.add('flash');
            setTimeout(function () { el.classList.remove('flash'); el.style.animationDelay = ''; }, 1600);
          });
        }
        if (navigator.vibrate && !S.gaveUp) { try { navigator.vibrate([10, 60, 18]); } catch (e) { /* ignore */ } }
        setTimeout(function () { showFinish(true); }, S.gaveUp ? 250 : 950);
      } else if (announceWrong && myGen === gen) {
        toast('Not quite – something isn’t right yet');
      }
    });
  }
  function clearWord() {
    currentWord().cells.forEach(function (i) { if (!locked(i) && S.letters[i]) { S.letters[i] = ''; S.checked[i] = 0; cellChanged(i); } });
    afterChange([]);
  }
  function clearGrid() {
    // Clears your own unconfirmed letters only. Score, time, revealed and confirmed letters are kept,
    // so clearing (or reloading) can never restore points.
    P.cells.forEach(function (_, i) { if (!locked(i) && S.letters[i]) { S.letters[i] = ''; S.checked[i] = 0; cellChanged(i); } });
    wasFull = false;
    setPaused(false);
    selectWord(0, true);
    afterChange([]);
  }

  // ---------------------------------------------------------------- finish screen
  function shareText() {
    var sc = scoreOf(S);
    var url = location.origin + location.pathname;
    var line = puzzleName() + ' · ' + sc + ' pts · ' + fmtTime(S.elapsed) + (S.gaveUp ? ' · grid revealed' : '');
    return line + '\n' + url;
  }
  function showFinish(celebrate) {
    if (!S || !S.completed) return;
    var sc = scoreOf(S);
    $('finish-kicker').textContent = [puzzleName(), prettyDate(P.date, 'short'), P.difficulty].filter(Boolean).join(' · ');
    $('finish-title').textContent = S.gaveUp ? 'Grid revealed' : (sc === START_SCORE ? 'Perfect!' : sc >= 80 ? 'Solved!' : 'Finished');
    $('finish-time').textContent = fmtTime(S.elapsed);
    $('finish-help').textContent = helpCount(S) ? helpCount(S) : 'None';
    var ul = $('finish-breakdown');
    ul.innerHTML = '';
    function li(label, val, cls) {
      var el = document.createElement('li');
      if (cls) el.className = cls;
      var a = document.createElement('span'); a.textContent = label;
      var b = document.createElement('span'); b.textContent = val;
      el.appendChild(a); el.appendChild(b); ul.appendChild(el);
    }
    li('Starting score', String(START_SCORE));
    var groups = groupedDeductions(S);
    if (!groups.length) {
      var none = document.createElement('li');
      none.className = 'none';
      none.textContent = 'No help used – full marks';
      ul.appendChild(none);
    }
    groups.forEach(function (g) {
      var label = (LABEL[g.t] || g.t) + (g.count > 1 || g.t.indexOf('legacy') === 0 ? ' ×' + g.count : '');
      li(label, (g.cost ? '−' + g.cost : '0'), 'minus');
    });
    if (!S.gaveUp && groups.length) {
      var raw = START_SCORE - groups.reduce(function (s, g) { return s + g.cost; }, 0);
      if (raw < 0) li('Floor (score can’t go below 0)', '+' + (-raw));
    }
    li('Final score', sc + ' pts');

    var ring = $('ring');
    ring.classList.toggle('mid', sc < 80 && sc >= 50);
    ring.classList.toggle('low', sc < 50);
    var fill = $('ring-fill');
    var C = 2 * Math.PI * 52;
    fill.style.transition = 'none';
    fill.style.strokeDashoffset = C;
    $('finish').hidden = false;
    void fill.getBoundingClientRect();
    fill.style.transition = '';
    fill.style.strokeDashoffset = C * (1 - sc / START_SCORE);
    countUp($('finish-score'), sc);
    if (celebrate && !reduceMotion) startFireworks();
  }
  function countUp(el, target) {
    if (reduceMotion || target === 0) { el.textContent = target; return; }
    var t0 = performance.now(), dur = 1100;
    (function step(now) {
      var p = Math.min(1, (now - t0) / dur);
      var e = 1 - Math.pow(1 - p, 3);
      el.textContent = Math.round(target * e);
      if (p < 1) requestAnimationFrame(step);
    })(t0);
  }
  function share() {
    var text = shareText();
    if (navigator.share) {
      navigator.share({ title: 'Crosshatch', text: text }).catch(function (err) {
        if (!err || err.name !== 'AbortError') copyText(text);
      });
    } else copyText(text);
  }
  function copyText(text) {
    function fallback() {
      var ta = document.createElement('textarea');
      ta.value = text;
      ta.setAttribute('readonly', '');   // readonly: never summons the iOS keyboard
      ta.style.position = 'fixed'; ta.style.top = '-1000px'; ta.style.opacity = '0';
      document.body.appendChild(ta);
      ta.select();
      ta.setSelectionRange(0, text.length);
      var ok = false;
      try { ok = document.execCommand('copy'); } catch (e) { ok = false; }
      ta.remove();
      toast(ok ? 'Result copied to clipboard' : 'Could not copy – sorry');
    }
    if (navigator.clipboard && navigator.clipboard.writeText) {
      navigator.clipboard.writeText(text).then(function () { toast('Result copied to clipboard'); }, fallback);
    } else fallback();
  }

  // ---------------------------------------------------------------- fireworks (canvas, no library)
  // Rockets rise and burst into radial sparks. Skipped entirely when the
  // phone asks for reduced motion.
  var fireworksRAF = null;
  var fireworksRan = false;
  function startFireworks() {
    if (reduceMotion) return;
    var cv = $('fireworks');
    if (!cv) return;
    var dpr = Math.min(window.devicePixelRatio || 1, 2);
    var W = cv.clientWidth || window.innerWidth, H = cv.clientHeight || window.innerHeight;
    if (W < 2 || H < 2) return;
    cv.width = Math.round(W * dpr); cv.height = Math.round(H * dpr);
    var ctx = cv.getContext('2d');
    ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
    fireworksRan = true;
    var colours = ['#ffe56a', '#ff5d7a', '#7cf0c2', '#8db4ff', '#ffb15a', '#e7d4ff', '#ffffff', '#ff8ad4'];
    var sparks = [];
    function burst(x, y, color, n, speed) {
      for (var i = 0; i < n; i++) {
        var a = (Math.PI * 2 * i) / n + (Math.random() - 0.5) * 0.12;
        var sp = speed * (0.55 + Math.random() * 0.55);
        sparks.push({
          x: x, y: y,
          vx: Math.cos(a) * sp, vy: Math.sin(a) * sp,
          life: 0.85 + Math.random() * 0.75,
          age: 0,
          c: color,
          rad: Math.random() < 0.2 ? 2.6 : 1.6,
          trail: Math.random() < 0.7
        });
      }
    }
    var plan = [
      { delay: 0.05, x: 0.18, y: 0.16 },
      { delay: 0.22, x: 0.82, y: 0.14 },
      { delay: 0.48, x: 0.50, y: 0.08 },
      { delay: 0.72, x: 0.12, y: 0.30 },
      { delay: 1.05, x: 0.88, y: 0.28 },
      { delay: 1.35, x: 0.36, y: 0.18 },
      { delay: 1.7, x: 0.64, y: 0.12 }
    ];
    var rockets = plan.map(function (b, i) {
      return {
        x: W * (0.28 + (i % 3) * 0.22),
        y: H + 6,
        tx: W * b.x,
        ty: H * b.y,
        delay: b.delay,
        c: colours[i % colours.length],
        exploded: false
      };
    });
    var t0 = performance.now();
    cancelAnimationFrame(fireworksRAF);
    (function frame(now) {
      var t = (now - t0) / 1000;
      ctx.clearRect(0, 0, W, H);
      rockets.forEach(function (r) {
        if (t < r.delay || r.exploded) return;
        var u = Math.min(1, (t - r.delay) / 0.52);
        var ease = 1 - Math.pow(1 - u, 2);
        var x = r.x + (r.tx - r.x) * ease;
        var y = r.y + (r.ty - r.y) * ease;
        ctx.save();
        ctx.globalAlpha = 0.95;
        ctx.strokeStyle = r.c;
        ctx.lineWidth = 2;
        ctx.beginPath();
        ctx.moveTo(x, y + 14);
        ctx.lineTo(x, y);
        ctx.stroke();
        ctx.fillStyle = '#fff8e8';
        ctx.beginPath();
        ctx.arc(x, y, 2.4, 0, Math.PI * 2);
        ctx.fill();
        ctx.restore();
        if (u >= 1) {
          r.exploded = true;
          burst(r.tx, r.ty, r.c, 36, 3.1);
          burst(r.tx, r.ty, '#fffef8', 14, 1.5);
        }
      });
      for (var i = sparks.length - 1; i >= 0; i--) {
        var spk = sparks[i];
        spk.age += 1 / 60;
        spk.vy += 0.04;
        spk.vx *= 0.988;
        spk.vy *= 0.988;
        spk.x += spk.vx;
        spk.y += spk.vy;
        var k = 1 - spk.age / spk.life;
        if (k <= 0) { sparks.splice(i, 1); continue; }
        ctx.save();
        ctx.globalAlpha = Math.max(0, k);
        if (spk.trail) {
          ctx.strokeStyle = spk.c;
          ctx.lineWidth = 1.4;
          ctx.beginPath();
          ctx.moveTo(spk.x, spk.y);
          ctx.lineTo(spk.x - spk.vx * 3.2, spk.y - spk.vy * 3.2);
          ctx.stroke();
        }
        ctx.fillStyle = spk.c;
        ctx.beginPath();
        ctx.arc(spk.x, spk.y, spk.rad * (0.35 + k), 0, Math.PI * 2);
        ctx.fill();
        ctx.restore();
      }
      if (t < 3.8) fireworksRAF = requestAnimationFrame(frame);
      else ctx.clearRect(0, 0, W, H);
    })(t0);
  }
  function stopFireworks() {
    cancelAnimationFrame(fireworksRAF);
    fireworksRAF = null;
    var cv = $('fireworks');
    if (cv && cv.getContext) cv.getContext('2d').clearRect(0, 0, cv.width, cv.height);
  }

  // ---------------------------------------------------------------- small UI helpers
  var toastTimer = null;
  var overlayOpenedAt = 0;   // ignore the 'ghost' click that follows the keypress which opened an overlay
  function toast(msg) {
    var t = $('toast');
    t.textContent = msg;
    t.style.bottom = (($('dock').hidden ? 0 : $('dock').offsetHeight) + 12) + 'px';
    t.hidden = true; void t.offsetWidth; t.hidden = false;
    clearTimeout(toastTimer);
    toastTimer = setTimeout(function () { t.hidden = true; }, 2300);
  }
  function showModal(title, body, actions) {
    $('modal-title').textContent = title;
    $('modal-body').textContent = body;
    var box = $('modal-actions');
    box.innerHTML = '';
    actions.forEach(function (a) {
      var b = document.createElement('button');
      b.type = 'button';
      b.className = 'btn ' + (a.primary ? 'primary' : 'ghost');
      b.textContent = a.label;
      b.addEventListener('click', function () {
        if (performance.now() - overlayOpenedAt < 300) return;
        $('modal').hidden = true;
        if (a.action) a.action();
      });
      box.appendChild(b);
    });
    $('modal').hidden = false;
    overlayOpenedAt = performance.now();
  }
  function confirmThen(title, body, label, fn) {
    showModal(title, body, [{ label: 'Cancel' }, { label: label, primary: true, action: fn }]);
  }
  function openRules() {
    var el = $('rules-current');
    el.innerHTML = '';
    if (S) {
      var b = document.createElement('b');
      b.textContent = scoreOf(S);
      el.appendChild(document.createTextNode(S.completed ? 'Your score for this puzzle: ' : 'This puzzle so far: '));
      el.appendChild(b);
      el.appendChild(document.createTextNode(' pts' + (helpCount(S) ? ' (' + plural(helpCount(S), 'use') + ' of help)' : ' – no help used')));
    }
    $('rules').hidden = false;
    overlayOpenedAt = performance.now();
  }

  function buildKeyboard() {
    var rows = ['QWERTYUIOP', 'ASDFGHJKL', 'ZXCVBNM'];
    var kb = $('keyboard');
    rows.forEach(function (row, ri) {
      var r = document.createElement('div');
      r.className = 'krow';
      row.split('').forEach(function (ch) {
        var k = document.createElement('button');
        k.type = 'button';
        k.className = 'key';
        k.dataset.key = ch;
        k.textContent = ch;
        k.tabIndex = -1;
        r.appendChild(k);
      });
      if (ri === 2) {
        var bs = document.createElement('button');
        bs.type = 'button';
        bs.className = 'key wide';
        bs.dataset.key = 'BACKSPACE';
        bs.tabIndex = -1;
        bs.setAttribute('aria-label', 'Delete');
        bs.innerHTML = '<svg viewBox="0 0 24 24" aria-hidden="true"><path d="M9 5.5h10.5a1.5 1.5 0 0 1 1.5 1.5v10a1.5 1.5 0 0 1-1.5 1.5H9L3 12z"/><path d="M12.5 9.5l5 5M17.5 9.5l-5 5"/></svg>';
        r.appendChild(bs);
      }
      kb.appendChild(r);
    });
    var pressed = null, pressedAt = 0;
    function release() {
      if (!pressed) return;
      var k = pressed, wait = Math.max(0, 90 - (performance.now() - pressedAt));
      pressed = null;
      setTimeout(function () { k.classList.remove('pressed'); }, wait);
    }
    kb.addEventListener('pointerdown', function (e) {
      var k = e.target.closest('.key');
      if (!k) return;
      e.preventDefault();
      release();
      pressed = k; pressedAt = performance.now();
      k.classList.add('pressed');
      if (k.dataset.key === 'BACKSPACE') backspace();
      else inputLetter(k.dataset.key);
    });
    ['pointerup', 'pointercancel', 'pointerleave'].forEach(function (ev) { kb.addEventListener(ev, release); });
    kb.addEventListener('contextmenu', function (e) { e.preventDefault(); });
  }

  var archiveSeq = 0;
  function showArchive() {
    if (P && S) { syncTimer(); saveState(); }
    $('view-puzzle').hidden = true;
    $('view-archive').hidden = false;
    $('dock').hidden = true;
    $('stats').hidden = true;
    $('btn-menu').hidden = true;
    $('subtitle').textContent = 'Past puzzles';
    syncTimer();
    var list = $('archive-list');
    list.innerHTML = '';
    var items = released().slice().reverse();
    var previewMode = false;
    if (!items.length && index.length) { items = [index[0]]; previewMode = true; }
    var seq = ++archiveSeq;
    // Re-score old saves with each puzzle's words before badges are painted, so the
    // archive never shows the harsh pre-scoring total.
    migrateStored(items.map(function (e) { return e.date; })).then(function () {
      if (seq !== archiveSeq || $('view-archive').hidden) return;
      paintArchive(list, items, previewMode);
    });
  }
  function paintArchive(list, items, previewMode) {
    list.innerHTML = '';
    var done = 0, total = 0, best = null;
    items.forEach(function (e) {
      var st = peekState(e.date);
      if (st && st.completed) {
        var sc = scoreOf(st);
        done++; total += sc; best = best === null ? sc : Math.max(best, sc);
      }
    });
    var sum = $('archive-summary');
    sum.innerHTML = '';
    [[done, 'Completed'], [done ? Math.round(total / done) : '–', 'Average'], [best === null ? '–' : best, 'Best score']].forEach(function (p) {
      var d = document.createElement('div');
      var b = document.createElement('b'); b.textContent = p[0];
      var s = document.createElement('span'); s.textContent = p[1];
      d.appendChild(b); d.appendChild(s); sum.appendChild(d);
    });
    if (!items.length) {
      var none = document.createElement('li');
      none.className = 'archive-note';
      none.textContent = 'No puzzles yet.';
      list.appendChild(none);
      return;
    }
    items.forEach(function (e) {
      var st = peekState(e.date);
      var li = document.createElement('li');
      var b = document.createElement('button');
      b.type = 'button';
      b.className = 'archive-item' + (P && P.date === e.date ? ' current' : '');
      b.dataset.date = e.date;
      b.innerHTML = '<span class="a-main"><span class="a-date"></span><span class="a-sub"></span></span><span class="a-badge"></span>';
      b.querySelector('.a-date').textContent = prettyDate(e.date, 'medium');
      var badge = b.querySelector('.a-badge');
      var sub;
      if (st && st.completed) {
        var sc = scoreOf(st);
        badge.classList.add('solved');
        badge.innerHTML = '<b></b>pts';
        badge.querySelector('b').textContent = sc;
        sub = (st.gaveUp ? 'Revealed' : 'Solved') + ' · ' + fmtTime(st.elapsed || 0);
      } else if (st && (st.elapsed > 1000 || (st.letters || []).some(Boolean))) {
        badge.classList.add('progress');
        badge.innerHTML = '<b></b>so far';
        badge.querySelector('b').textContent = scoreOf(st);
        sub = 'In progress · ' + fmtTime(st.elapsed || 0);
      } else {
        badge.textContent = 'New';
        sub = 'Not started';
      }
      b.querySelector('.a-sub').textContent = [e.title, e.difficulty, sub, previewMode ? 'Preview' : ''].filter(Boolean).join(' · ');
      b.addEventListener('click', function () { location.hash = '#/p/' + e.date; });
      li.appendChild(b);
      list.appendChild(li);
    });
  }

  // ---------------------------------------------------------------- events
  function bind() {
    $('grid').addEventListener('click', function (e) {
      var c = e.target.closest('.cell');
      if (c && !userPaused) selectCell(+c.dataset.i);
    });
    $('clues').addEventListener('click', function (e) {
      var h = e.target.closest('.hint-btn');
      if (h) {
        if (!userPaused) usePlain(+h.dataset.w);
        return;
      }
      var b = e.target.closest('.clue');
      if (b) {
        selectWord(+b.dataset.w);
        // bring the grid back into view so the selected word is visible
        var v = $('view-puzzle'), g = $('grid-wrap');
        if (g.getBoundingClientRect().top < v.getBoundingClientRect().top - 4) v.scrollTo({ top: 0, behavior: reduceMotion ? 'auto' : 'smooth' });
      }
    });
    $('clue-bar-text').addEventListener('click', toggleDir);
    $('btn-prev').addEventListener('click', function () { cycleWord(-1); });
    $('btn-next').addEventListener('click', function () { cycleWord(1); });
    $('timer').addEventListener('click', function () { if (S && !S.completed) setPaused(!userPaused); });
    $('score').addEventListener('click', openRules);
    $('btn-resume').addEventListener('click', function () { setPaused(false); });
    $('btn-archive').addEventListener('click', function () {
      location.hash = (location.hash === '#/archive') ? (P ? '#/p/' + P.date : '') : '#/archive';
    });
    $('btn-archive-back').addEventListener('click', function () { location.hash = P ? '#/p/' + P.date : ''; });
    $('btn-menu').addEventListener('click', function () {
      if (S && S.completed) { openRules(); return; }
      renderMenu();
      $('menu').hidden = false;
      overlayOpenedAt = performance.now();
    });
    $('btn-results').addEventListener('click', function () { showFinish(false); });
    $('btn-share').addEventListener('click', share);
    $('btn-finish-grid').addEventListener('click', function () { $('finish').hidden = true; stopFireworks(); });
    $('btn-finish-archive').addEventListener('click', function () { location.hash = '#/archive'; });
    $('menu').addEventListener('click', function (e) {
      if (e.target === $('menu')) { if (performance.now() - overlayOpenedAt > 400) $('menu').hidden = true; return; }
      var b = e.target.closest('button[data-action]');
      if (!b || !P) return;
      var a = b.dataset.action;
      $('menu').hidden = true;
      if (a === 'close') return;
      if (a === 'rules') return openRules();
      if (S.completed) { toast('Puzzle already complete'); return; }
      if (userPaused) setPaused(false);
      if (a === 'reset') return confirmThen('Clear the grid?', 'This clears your unconfirmed letters. Your score and time are kept.', 'Clear', clearGrid);
      if (a === 'plain-clue') return usePlain(words.indexOf(currentWord()));
      if (a === 'reveal-grid') return confirmThen('Reveal the grid?', 'This shows every answer and ends the puzzle with 0 points.', 'Reveal', function () { reveal('grid'); });
      var parts = a.split('-');
      if (parts[0] === 'check') check(parts[1]);
      else if (parts[0] === 'reveal') reveal(parts[1]);
      else if (a === 'clear-word') clearWord();
    });
    $('rules').addEventListener('click', function (e) {
      if ((e.target === $('rules') && performance.now() - overlayOpenedAt > 400) || e.target.closest('[data-action="close"]')) $('rules').hidden = true;
    });
    $('modal').addEventListener('click', function (e) {
      if (e.target === $('modal') && performance.now() - overlayOpenedAt > 600) $('modal').hidden = true;
    });

    document.addEventListener('keydown', function (e) {
      if (e.metaKey || e.ctrlKey || e.altKey) return;
      if ($('view-puzzle').hidden || !P) return;
      var overlay = ['modal', 'menu', 'rules', 'finish'].filter(function (id) { return !$(id).hidden; });
      if (overlay.length) {
        if (e.key === 'Escape') { overlay.forEach(function (id) { $(id).hidden = true; }); stopFireworks(); }
        return;
      }
      var k = e.key;
      if (/^[a-zA-Z]$/.test(k)) inputLetter(k);
      else if (k === 'Backspace' || k === 'Delete') backspace();
      else if (k === 'ArrowLeft') moveArrow(0, -1);
      else if (k === 'ArrowRight') moveArrow(0, 1);
      else if (k === 'ArrowUp') moveArrow(-1, 0);
      else if (k === 'ArrowDown') moveArrow(1, 0);
      else if (k === 'Tab' || k === 'Enter') cycleWord(e.shiftKey ? -1 : 1);
      else if (k === ' ') toggleDir();
      else return;
      e.preventDefault();
    });

    document.addEventListener('visibilitychange', syncTimer);
    window.addEventListener('pagehide', function () { syncTimer(); saveState(); });
    window.addEventListener('resize', sizeGrid);
    window.addEventListener('hashchange', route);
    document.addEventListener('gesturestart', function (e) { e.preventDefault(); });
    document.addEventListener('dblclick', function (e) { e.preventDefault(); }, { passive: false });

    setInterval(function () { if (running()) renderTimer(); }, 500);
    setInterval(function () { if (running()) saveState(); }, 5000);
  }

  // ---------------------------------------------------------------- start
  buildKeyboard();
  bind();
  (function () { var cv = $('fireworks'); if (cv) { cv.width = 0; cv.height = 0; } })();
  fetchJSON('puzzles/index.json').then(function (idx) {
    index = (idx.puzzles || []).slice().sort(function (a, b) { return a.date < b.date ? -1 : 1; });
    route();
  }).catch(function (err) {
    showError('Could not load the puzzle list. (' + err.message + ')');
  });

  // tiny hook for automated tests (never exposes answers)
  window.__crosshatch = {
    state: function () { return { sel: sel, dir: dir, S: S, date: P && P.date, running: running(), score: scoreOf(S), good: Object.keys(goodWords).map(Number), hasPlain: hasPlain, fireworks: fireworksRan }; },
    shareText: function () { return S ? shareText() : ''; }
  };
})();
