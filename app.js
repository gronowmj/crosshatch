/* Crosshatch – a small daily cryptic. Plain JS, no build step. */
(function () {
  'use strict';

  var STORE_PREFIX = 'crosshatch:v1:';   // unchanged key: older saves load and are migrated in place
  var START_SCORE = 100;
  var COST = { 'check-letter': 1, 'check-word': 3, 'check-grid': 5, 'reveal-letter': 5, 'reveal-word-each': 5, 'reveal-word-max': 15 };
  var LABEL = {
    'check-letter': 'Letter check',
    'check-word': 'Word check',
    'check-grid': 'Grid check',
    'reveal-letter': 'Letter reveal',
    'reveal-word': 'Word reveal',
    'reveal-grid': 'Grid revealed',
    'legacy-reveal': 'Revealed letters (pre-scoring)',
    'legacy-check': 'Checked letters (pre-scoring)'
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
  var words = [];        // [{dir,num,text,enumeration,cells,el}]
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
    var st = { v: 2, letters: [], revealed: [], checked: [], elapsed: 0, completed: false, solved: false,
      completedAt: null, deductions: [], gaveUp: false };
    for (var i = 0; i < n; i++) { st.letters.push(''); st.revealed.push(false); st.checked.push(0); }
    return st;
  }
  function migrate(st, n) {
    // Older saves have letters/revealed/checked/elapsed/completed/solved but no score data.
    if (!Array.isArray(st.revealed) || st.revealed.length !== n) st.revealed = st.letters.map(function () { return false; });
    if (!Array.isArray(st.checked) || st.checked.length !== n) st.checked = st.letters.map(function () { return 0; });
    st.elapsed = +st.elapsed || 0;
    if (!Array.isArray(st.deductions)) {
      st.deductions = [];
      var nR = 0, nC = 0;
      for (var i = 0; i < n; i++) {
        if (st.revealed[i]) nR++;
        else if (st.checked[i]) nC++;
      }
      if (nR) st.deductions.push({ t: 'legacy-reveal', c: nR * COST['reveal-letter'], n: nR });
      if (nC) st.deductions.push({ t: 'legacy-check', c: nC * COST['check-letter'], n: nC });
      st.gaveUp = false;
    }
    st.gaveUp = !!st.gaveUp;
    st.v = 2;
    return st;
  }
  function loadState(date, n) {
    var st = null;
    try { st = JSON.parse(localStorage.getItem(storeKey(date)) || 'null'); } catch (e) { st = null; }
    if (!st || !Array.isArray(st.letters) || st.letters.length !== n) return blankState(n);
    return migrate(st, n);
  }
  function saveState() {
    if (!P || !S) return;
    var copy = Object.assign({}, S, { elapsed: Math.round(elapsed()), score: scoreOf(S), updated: new Date().toISOString() });
    try { localStorage.setItem(storeKey(P.date), JSON.stringify(copy)); } catch (e) { /* private mode / full */ }
  }
  function peekState(date) {
    try {
      var st = JSON.parse(localStorage.getItem(storeKey(date)) || 'null');
      if (st && Array.isArray(st.letters)) return migrate(st, st.letters.length);
    } catch (e) { /* ignore */ }
    return null;
  }

  // ---------------------------------------------------------------- scoring
  function scoreOf(st) {
    if (!st) return START_SCORE;
    if (st.gaveUp) return 0;
    var sum = 0;
    (st.deductions || []).forEach(function (d) { sum += d.c; });
    return Math.max(0, START_SCORE - sum);
  }
  function deduct(type, cost) {
    if (cost <= 0) return;
    var before = scoreOf(S);
    S.deductions.push({ t: type, c: cost, at: Date.now() });
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
    stopConfetti();
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
      P.clues[d].forEach(function (c) { words.push({ dir: d, num: c.num, text: c.text, enumeration: c.enum, cells: c.cells }); });
    });
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
        var b = document.createElement('button');
        b.type = 'button';
        b.className = 'clue';
        b.dataset.w = wi;
        b.innerHTML = '<span class="cnum"></span><span class="cbody"><span class="ctext"></span> <span class="enum"></span></span>' + TICK;
        b.querySelector('.cnum').textContent = w.num;
        b.querySelector('.ctext').textContent = w.text;
        b.querySelector('.enum').textContent = w.enumeration;
        li.appendChild(b);
        ul.appendChild(li);
        w.el = b;
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
    txt.textContent = w.text + ' ' + w.enumeration;
    bar.appendChild(chip);
    bar.appendChild(txt);

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
  function check(scope) {
    var cells = targetCells(scope).filter(function (i) { return S.letters[i] && !locked(i); });
    if (!cells.length) { toast(scope === 'letter' && !S.letters[sel] ? 'Type a letter first' : 'Nothing new to check – no charge'); return Promise.resolve(); }
    deduct('check-' + scope, COST['check-' + scope]);
    return Promise.all(cells.map(cellCorrect)).then(function (res) {
      var wrong = 0;
      cells.forEach(function (ci, k) { S.checked[ci] = res[k] ? 1 : -1; if (!res[k]) wrong++; });
      toast(wrong ? plural(wrong, 'letter') + ' wrong' : (scope === 'letter' ? 'That letter is right' : 'All correct so far'));
      afterChange([]);
    });
  }
  function reveal(scope) {
    var cells = targetCells(scope).filter(function (i) { return !locked(i); });
    if (!cells.length) { toast('Already revealed – no charge'); return Promise.resolve(); }
    return keystream().then(function (ks) {
      var fixed = 0;
      cells.forEach(function (i) {
        var l = solutionLetter(i, ks);
        if (S.letters[i] === l) { S.checked[i] = 1; }          // already right: just confirm it
        else { S.letters[i] = l; S.revealed[i] = true; S.checked[i] = 0; fixed++; cellChanged(i); }
      });
      if (scope === 'grid') {
        var before = scoreOf(S);
        S.deductions.push({ t: 'reveal-grid', c: before, at: Date.now() });
        S.gaveUp = true;
        renderScore(before);
      } else if (fixed === 0) {
        // nothing needed filling or correcting: it only told you your letters were right
        deduct('check-' + scope, COST['check-' + scope]);
        toast(scope === 'letter' ? 'You already had that one – charged as a check' : 'You already had those – charged as a check');
      } else if (scope === 'letter') {
        deduct('reveal-letter', COST['reveal-letter']);
      } else {
        deduct('reveal-word', Math.min(COST['reveal-word-max'], fixed * COST['reveal-word-each']));
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
    if (celebrate && !S.gaveUp && sc > 0 && !reduceMotion) startConfetti();
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

  // ---------------------------------------------------------------- confetti (canvas, no library)
  var confettiRAF = null;
  function startConfetti() {
    var cv = $('confetti');
    var dpr = Math.min(window.devicePixelRatio || 1, 2);
    var W = cv.clientWidth, H = cv.clientHeight;
    cv.width = W * dpr; cv.height = H * dpr;
    var ctx = cv.getContext('2d');
    ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
    var colours = ['#ffcf4a', '#2a4a7f', '#1f9d55', '#f0703e', '#8db4ff', '#e85d8a'];
    var parts = [];
    for (var i = 0; i < 140; i++) {
      var fromLeft = i % 2 === 0;
      parts.push({
        x: fromLeft ? -10 : W + 10,
        y: H * (0.55 + Math.random() * 0.25),
        vx: (fromLeft ? 1 : -1) * (3 + Math.random() * 6),
        vy: -(8 + Math.random() * 7),
        w: 6 + Math.random() * 6, h: 8 + Math.random() * 8,
        r: Math.random() * Math.PI, vr: (Math.random() - .5) * .3,
        c: colours[i % colours.length], tilt: Math.random() * 10
      });
    }
    var t0 = performance.now();
    cancelAnimationFrame(confettiRAF);
    (function frame(now) {
      var t = (now - t0) / 1000;
      ctx.clearRect(0, 0, W, H);
      parts.forEach(function (p) {
        p.vy += 0.28; p.vx *= 0.992; p.vy *= 0.992;
        p.x += p.vx; p.y += p.vy; p.r += p.vr; p.tilt += 0.1;
        ctx.save();
        ctx.translate(p.x, p.y);
        ctx.rotate(p.r);
        ctx.globalAlpha = Math.max(0, 1 - Math.max(0, t - 2.4) / 0.8);
        ctx.fillStyle = p.c;
        ctx.fillRect(-p.w / 2, -p.h / 2 * Math.abs(Math.cos(p.tilt)), p.w, p.h * Math.abs(Math.cos(p.tilt)));
        ctx.restore();
      });
      if (t < 3.3) confettiRAF = requestAnimationFrame(frame);
      else ctx.clearRect(0, 0, W, H);
    })(t0);
  }
  function stopConfetti() {
    cancelAnimationFrame(confettiRAF);
    var cv = $('confetti');
    if (cv.getContext) cv.getContext('2d').clearRect(0, 0, cv.width, cv.height);
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
      $('menu').hidden = false;
      overlayOpenedAt = performance.now();
    });
    $('btn-results').addEventListener('click', function () { showFinish(false); });
    $('btn-share').addEventListener('click', share);
    $('btn-finish-grid').addEventListener('click', function () { $('finish').hidden = true; stopConfetti(); });
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
        if (e.key === 'Escape') { overlay.forEach(function (id) { $(id).hidden = true; }); stopConfetti(); }
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
  fetchJSON('puzzles/index.json').then(function (idx) {
    index = (idx.puzzles || []).slice().sort(function (a, b) { return a.date < b.date ? -1 : 1; });
    route();
  }).catch(function (err) {
    showError('Could not load the puzzle list. (' + err.message + ')');
  });

  // tiny hook for automated tests (never exposes answers)
  window.__crosshatch = {
    state: function () { return { sel: sel, dir: dir, S: S, date: P && P.date, running: running(), score: scoreOf(S), good: Object.keys(goodWords).map(Number) }; },
    shareText: function () { return S ? shareText() : ''; }
  };
})();
