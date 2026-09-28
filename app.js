/* Crosshatch – a small daily cryptic. Plain JS, no build step. */
(function () {
  'use strict';

  var STORE_PREFIX = 'crosshatch:v1:';
  var $ = function (id) { return document.getElementById(id); };

  // ---------------------------------------------------------------- dates
  function pad(n) { return (n < 10 ? '0' : '') + n; }
  function localISO(d) { return d.getFullYear() + '-' + pad(d.getMonth() + 1) + '-' + pad(d.getDate()); }
  function todayISO() {
    var q = new URLSearchParams(location.search).get('today'); // testing override
    return (q && /^\d{4}-\d{2}-\d{2}$/.test(q)) ? q : localISO(new Date());
  }
  function prettyDate(iso, short) {
    var p = iso.split('-');
    var d = new Date(+p[0], +p[1] - 1, +p[2]);
    return d.toLocaleDateString('en-GB', short
      ? { weekday: 'short', day: 'numeric', month: 'short', year: 'numeric' }
      : { weekday: 'long', day: 'numeric', month: 'long', year: 'numeric' });
  }
  function fmtTime(ms) {
    var s = Math.floor(ms / 1000), h = Math.floor(s / 3600), m = Math.floor((s % 3600) / 60);
    s = s % 60;
    return h ? h + ':' + pad(m) + ':' + pad(s) : m + ':' + pad(s);
  }

  // ---------------------------------------------------------------- hashing
  var subtle = (window.isSecureContext && window.crypto && window.crypto.subtle) ? window.crypto.subtle : null;
  function sha256(str) {
    if (subtle) {
      return subtle.digest('SHA-256', new TextEncoder().encode(str)).then(function (b) { return new Uint8Array(b); });
    }
    return Promise.resolve(window.sha256Bytes(str));
  }
  function hex(bytes) {
    var s = '';
    for (var i = 0; i < bytes.length; i++) s += (bytes[i] < 16 ? '0' : '') + bytes[i].toString(16);
    return s;
  }

  // ---------------------------------------------------------------- state
  var index = [];          // [{date,title,difficulty}]
  var P = null;            // current puzzle JSON
  var S = null;            // current progress state
  var words = [];          // [{dir,num,text,enum,cells,el}]
  var cellWords = [];      // per cell: {across: wordIdx|null, down: wordIdx|null}
  var cellEls = [];
  var sel = 0, dir = 'across';
  var keystreamCache = null;
  var timerStart = null;   // performance.now() when current running stretch began
  var userPaused = false;
  var tickHandle = null, saveHandle = null;
  var wasFull = false;

  function storeKey(date) { return STORE_PREFIX + date; }
  function loadState(date, n) {
    var st = null;
    try { st = JSON.parse(localStorage.getItem(storeKey(date)) || 'null'); } catch (e) { st = null; }
    if (!st || !Array.isArray(st.letters) || st.letters.length !== n) {
      st = { letters: [], revealed: [], checked: [], elapsed: 0, completed: false, solved: false, completedAt: null };
      for (var i = 0; i < n; i++) { st.letters.push(''); st.revealed.push(false); st.checked.push(0); }
    }
    return st;
  }
  function saveState() {
    if (!P || !S) return;
    // S.elapsed is the banked time; the running stretch is added only to the saved copy
    var copy = Object.assign({}, S, { elapsed: Math.round(elapsed()), updated: new Date().toISOString() });
    try { localStorage.setItem(storeKey(P.date), JSON.stringify(copy)); } catch (e) { /* storage full / private mode */ }
  }
  function peekState(date) {
    try { return JSON.parse(localStorage.getItem(storeKey(date)) || 'null'); } catch (e) { return null; }
  }

  // ---------------------------------------------------------------- timer
  function elapsed() {
    if (!S) return 0;
    return S.elapsed + (timerStart !== null ? performance.now() - timerStart : 0);
  }
  function running() { return timerStart !== null; }
  function shouldRun() {
    return P && S && !S.completed && !userPaused && document.visibilityState === 'visible' && !$('view-puzzle').hidden;
  }
  function syncTimer() {
    if (shouldRun() && !running()) {
      timerStart = performance.now();
    } else if (!shouldRun() && running()) {
      S.elapsed += performance.now() - timerStart;
      timerStart = null;
      saveState();
    }
    renderTimer();
  }
  function renderTimer() {
    var t = $('timer');
    t.textContent = fmtTime(elapsed());
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

  // ---------------------------------------------------------------- loading
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
    if (h === '#/archive') return showArchive();
    var date = m ? m[1] : defaultDate();
    if (!date) return showError('No puzzles yet.');
    showPuzzleView();
    if (!P || P.date !== date) openPuzzle(date);
    else syncTimer();
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
    $('timer').hidden = false;
    $('btn-menu').hidden = false;
  }

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
      $('load-error').hidden = true;
      buildPuzzle();
      var preview = P.date > todayISO();
      $('subtitle').textContent = prettyDate(P.date, true) + (P.difficulty ? ' · ' + P.difficulty : '') + (preview ? ' · Preview' : '');
      document.title = 'Crosshatch – ' + prettyDate(P.date, true);
      wasFull = isFull();
      syncTimer();
    }).catch(function (err) {
      P = null; S = null;
      showError('Sorry, that puzzle could not be loaded. (' + err.message + ')');
    });
  }

  // ---------------------------------------------------------------- building
  function buildPuzzle() {
    words = [];
    ['across', 'down'].forEach(function (d) {
      P.clues[d].forEach(function (c) {
        words.push({ dir: d, num: c.num, text: c.text, enumeration: c.enum, cells: c.cells });
      });
    });
    cellWords = P.cells.map(function () { return { across: null, down: null }; });
    words.forEach(function (w, wi) { w.cells.forEach(function (ci) { cellWords[ci][w.dir] = wi; }); });

    // grid
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

    // clue lists
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
        b.innerHTML = '<span class="cnum"></span><span class="cbody"><span class="ctext"></span> <span class="enum"></span></span>';
        b.querySelector('.cnum').textContent = w.num;
        b.querySelector('.ctext').textContent = w.text;
        b.querySelector('.enum').textContent = w.enumeration;
        li.appendChild(b);
        ul.appendChild(li);
        w.el = b;
      });
    });

    // initial selection: first across word, first empty cell
    var first = words[0];
    dir = first.dir;
    sel = firstEmpty(first) ;
    render();
  }

  function sizeGrid() {
    if (!P) return;
    var wrap = $('grid-wrap');
    var avail = wrap.clientWidth || (window.innerWidth - 28);
    var maxByWidth = Math.floor((avail - 4) / P.width);
    // leave room below the grid for the four clues (about 230px)
    var mainH = $('view-puzzle').clientHeight || (window.innerHeight * 0.6);
    var maxByHeight = Math.floor((mainH - 240) / P.height);
    var size = Math.max(20, Math.min(44, maxByWidth, maxByHeight));
    var root = document.documentElement;
    root.style.setProperty('--cell', size + 'px');
    var grid = $('grid');
    grid.style.width = (size * P.width + 1.5) + 'px';
    grid.style.height = (size * P.height + 1.5) + 'px';
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
    var inWord = {};
    var showSel = !S.completed;   // a finished grid is shown clean, without the cursor
    if (showSel) w.cells.forEach(function (ci) { inWord[ci] = true; });
    cellEls.forEach(function (el, i) {
      var letter = S.letters[i] || '';
      el.querySelector('.letter').textContent = letter;
      el.classList.toggle('in-word', !!inWord[i]);
      el.classList.toggle('selected', showSel && i === sel);
      el.classList.toggle('revealed', !!S.revealed[i]);
      el.classList.toggle('correct', S.checked[i] === 1 && !S.revealed[i]);
      el.classList.toggle('wrong', S.checked[i] === -1);
      var c = P.cells[i];
      el.setAttribute('aria-label', (c.n ? c.n + ', ' : '') + 'row ' + (c.r + 1) + ', column ' + (c.c + 1) + (letter ? ', ' + letter : ', empty'));
    });
    var crossWi = cellWords[sel][dir === 'across' ? 'down' : 'across'];
    words.forEach(function (x, wi) {
      x.el.classList.toggle('active', x === w && showSel);
      x.el.classList.toggle('cross', wi === crossWi && showSel);
      x.el.classList.toggle('filled', x.cells.every(function (ci) { return !!S.letters[ci]; }));
    });
    var bar = $('clue-bar-text');
    bar.innerHTML = '';
    var b = document.createElement('b');
    b.textContent = w.num + (w.dir === 'across' ? 'A' : 'D');
    bar.appendChild(b);
    bar.appendChild(document.createTextNode(w.text + ' ' + w.enumeration));
    if ($('dock').classList.contains('complete') !== !!S.completed) {
      $('dock').classList.toggle('complete', !!S.completed);
      setTimeout(sizeGrid, 0);
    }
    $('done-bar').hidden = !S.completed;
    if (S.completed) {
      var nRev = S.revealed.filter(Boolean).length;
      $('done-text').textContent = S.solved ? 'Solved in ' + fmtTime(S.elapsed) + ' – well done'
        : 'Completed in ' + fmtTime(S.elapsed) + ' · ' + nRev + (nRev === 1 ? ' letter' : ' letters') + ' revealed';
    }
    renderTimer();
  }

  function scrollClueIntoView() {
    var w = currentWord();
    if (w && w.el && w.el.scrollIntoView) {
      var r = w.el.getBoundingClientRect(), v = $('view-puzzle').getBoundingClientRect();
      if (r.bottom > v.bottom || r.top < v.top) w.el.scrollIntoView({ block: 'nearest' });
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

  // ---------------------------------------------------------------- input
  function inputLetter(ch) {
    if (!P || S.completed || userPaused) return;
    ch = ch.toUpperCase();
    var w = currentWord();
    if (!locked(sel)) {
      S.letters[sel] = ch;
      if (S.checked[sel] === -1) S.checked[sel] = 0;
    }
    // advance
    var pos = posInWord(w);
    if (pos < w.cells.length - 1) {
      sel = w.cells[pos + 1];
    } else {
      var empty = w.cells.filter(function (ci) { return !S.letters[ci]; });
      if (empty.length) sel = empty[0];
      else {
        var nwi = nextIncompleteWord(words.indexOf(w));
        if (nwi !== null) { dir = words[nwi].dir; sel = firstEmpty(words[nwi]); }
      }
    }
    afterChange();
  }
  function backspace() {
    if (!P || S.completed || userPaused) return;
    var w = currentWord();
    if (S.letters[sel] && !locked(sel)) {
      S.letters[sel] = '';
      S.checked[sel] = 0;
    } else {
      var pos = posInWord(w);
      if (pos > 0) {
        sel = w.cells[pos - 1];
        if (!locked(sel)) { S.letters[sel] = ''; S.checked[sel] = 0; }
      }
    }
    afterChange();
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
  function afterChange() {
    saveState();
    render();
    var full = isFull();
    if (full && !S.completed) verifyComplete(!wasFull);
    wasFull = full;
  }
  function isFull() { return S.letters.every(function (l) { return !!l; }); }

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
  function solutionLetter(i, ks) {
    var byte = parseInt(P.reveal.substr(i * 2, 2), 16) ^ ks[i];
    return String.fromCharCode(byte);
  }
  function targetCells(scope) {
    if (scope === 'letter') return [sel];
    if (scope === 'word') return currentWord().cells.slice();
    return P.cells.map(function (_, i) { return i; });
  }
  function check(scope) {
    var cells = targetCells(scope).filter(function (i) { return S.letters[i] && !S.revealed[i]; });
    if (!cells.length) { toast('Nothing to check yet'); return Promise.resolve(); }
    return Promise.all(cells.map(cellCorrect)).then(function (res) {
      var wrong = 0;
      cells.forEach(function (ci, k) { S.checked[ci] = res[k] ? 1 : -1; if (!res[k]) wrong++; });
      toast(wrong ? (wrong === 1 ? '1 letter is wrong' : wrong + ' letters are wrong') : (scope === 'letter' ? 'That letter is right' : 'All correct so far'));
      afterChange();
    });
  }
  function reveal(scope) {
    var cells = targetCells(scope);
    return keystream().then(function (ks) {
      cells.forEach(function (i) {
        var l = solutionLetter(i, ks);
        if (S.letters[i] === l) {        // already right: just confirm it
          if (!S.revealed[i]) S.checked[i] = 1;
        } else {
          S.letters[i] = l;
          S.revealed[i] = true;
          S.checked[i] = 0;
        }
      });
      afterChange();
    });
  }
  function verifyComplete(announceWrong) {
    return Promise.all(P.cells.map(function (_, i) { return cellCorrect(i); })).then(function (res) {
      if (res.every(Boolean)) {
        syncTimer();
        S.elapsed = elapsed();
        timerStart = null;
        S.completed = true;
        S.solved = !S.revealed.some(Boolean);
        S.completedAt = new Date().toISOString();
        saveState();
        render();
        var nRev = S.revealed.filter(Boolean).length;
        var body = S.solved
          ? 'You solved it in ' + fmtTime(S.elapsed) + '.'
          : (nRev === P.cells.length ? 'Grid revealed after ' + fmtTime(S.elapsed) + '.'
            : 'Finished in ' + fmtTime(S.elapsed) + ', with ' + nRev + (nRev === 1 ? ' letter' : ' letters') + ' revealed.');
        showModal(S.solved ? 'Well done!' : 'Complete', body, [
          { label: 'Archive', action: function () { location.hash = '#/archive'; } },
          { label: 'Close', primary: true }
        ]);
      } else if (announceWrong) {
        toast('Not quite – something isn’t right yet');
      }
    });
  }
  function clearWord() {
    currentWord().cells.forEach(function (i) { if (!locked(i)) { S.letters[i] = ''; S.checked[i] = 0; } });
    afterChange();
  }
  function resetPuzzle() {
    timerStart = null;
    try { localStorage.removeItem(storeKey(P.date)); } catch (e) { /* ignore */ }
    S = loadState(P.date, P.cells.length);
    wasFull = false;
    setPaused(false);
    selectWord(0, true);
    syncTimer();
  }

  // ---------------------------------------------------------------- UI bits
  var toastTimer = null;
  var modalOpenedAt = 0;   // ignore the 'ghost' click that follows the keypress which opened a modal
  function toast(msg) {
    var t = $('toast');
    t.textContent = msg;
    t.hidden = false;
    clearTimeout(toastTimer);
    toastTimer = setTimeout(function () { t.hidden = true; }, 2200);
  }
  function showModal(title, body, actions) {
    $('modal-title').textContent = title;
    $('modal-body').textContent = body;
    var box = $('modal-actions');
    box.innerHTML = '';
    actions.forEach(function (a) {
      var b = document.createElement('button');
      b.type = 'button';
      b.textContent = a.label;
      if (a.primary) b.className = 'primary';
      b.addEventListener('click', function () {
        if (performance.now() - modalOpenedAt < 300) return;
        $('modal').hidden = true;
        if (a.action) a.action();
      });
      box.appendChild(b);
    });
    $('modal').hidden = false;
    modalOpenedAt = performance.now();
  }
  function confirmThen(title, body, label, fn) {
    showModal(title, body, [{ label: 'Cancel' }, { label: label, primary: true, action: fn }]);
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
        bs.innerHTML = '<svg viewBox="0 0 24 24" aria-hidden="true"><path d="M9 5h11v14H9l-6-7z"/><path d="M12 9l5 6M17 9l-5 6"/></svg>';
        r.appendChild(bs);
      }
      kb.appendChild(r);
    });
    // pointerdown gives an immediate response and never focuses anything
    kb.addEventListener('pointerdown', function (e) {
      var k = e.target.closest('.key');
      if (!k) return;
      e.preventDefault();
      k.classList.add('pressed');
      setTimeout(function () { k.classList.remove('pressed'); }, 110);
      if (k.dataset.key === 'BACKSPACE') backspace();
      else inputLetter(k.dataset.key);
    });
    kb.addEventListener('contextmenu', function (e) { e.preventDefault(); });
  }

  function showArchive() {
    if (P && S) { syncTimer(); saveState(); }
    $('view-puzzle').hidden = true;
    $('view-archive').hidden = false;
    $('dock').hidden = true;
    $('timer').hidden = true;
    $('btn-menu').hidden = true;
    $('subtitle').textContent = 'Past puzzles';
    syncTimer();
    var list = $('archive-list');
    list.innerHTML = '';
    var items = released().slice().reverse();
    var previewMode = false;
    if (!items.length && index.length) { items = [index[0]]; previewMode = true; }
    if (!items.length) {
      list.innerHTML = '<li class="archive-note">No puzzles yet.</li>';
      return;
    }
    items.forEach(function (e) {
      var st = peekState(e.date);
      var status = 'Not started', cls = '';
      if (st && st.completed) { status = (st.solved ? 'Solved · ' : 'Revealed · ') + fmtTime(st.elapsed || 0); cls = st.solved ? 'solved' : ''; }
      else if (st && (st.elapsed > 0 || (st.letters || []).some(Boolean))) status = 'In progress · ' + fmtTime(st.elapsed || 0);
      var li = document.createElement('li');
      var b = document.createElement('button');
      b.type = 'button';
      b.className = 'archive-item' + (P && P.date === e.date ? ' current' : '');
      b.dataset.date = e.date;
      b.innerHTML = '<span><span class="a-date"></span><br><span class="a-sub"></span></span><span class="a-status"></span>';
      b.querySelector('.a-date').textContent = prettyDate(e.date);
      b.querySelector('.a-sub').textContent = [e.title, e.difficulty, previewMode ? 'Preview' : ''].filter(Boolean).join(' · ');
      var s = b.querySelector('.a-status');
      s.textContent = status;
      if (cls) s.classList.add(cls);
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
      if (b) selectWord(+b.dataset.w);
    });
    $('clue-bar-text').addEventListener('click', toggleDir);
    $('btn-prev').addEventListener('click', function () { cycleWord(-1); });
    $('btn-next').addEventListener('click', function () { cycleWord(1); });
    $('timer').addEventListener('click', function () { if (S && !S.completed) setPaused(!userPaused); });
    $('btn-resume').addEventListener('click', function () { setPaused(false); });
    $('btn-archive').addEventListener('click', function () {
      location.hash = (location.hash === '#/archive') ? (P ? '#/p/' + P.date : '') : '#/archive';
    });
    $('btn-menu').addEventListener('click', function () { $('menu').hidden = false; });
    $('btn-done-archive').addEventListener('click', function () { location.hash = '#/archive'; });
    $('menu').addEventListener('click', function (e) {
      if (e.target === $('menu')) { $('menu').hidden = true; return; }
      var b = e.target.closest('button[data-action]');
      if (!b || !P) return;
      var a = b.dataset.action;
      $('menu').hidden = true;
      if (a === 'close') return;
      if (a === 'reset') return confirmThen('Reset puzzle?', 'This clears every letter and restarts the timer.', 'Reset', resetPuzzle);
      if (S.completed && a !== 'reset') { toast('Puzzle already complete'); return; }
      if (userPaused) setPaused(false);
      if (a === 'reveal-grid') return confirmThen('Reveal the grid?', 'This shows every answer.', 'Reveal', function () { reveal('grid'); });
      var parts = a.split('-');
      if (parts[0] === 'check') check(parts[1]);
      else if (parts[0] === 'reveal') reveal(parts[1]);
      else if (a === 'clear-word') clearWord();
    });
    $('modal').addEventListener('click', function (e) {
      if (e.target === $('modal') && performance.now() - modalOpenedAt > 600) $('modal').hidden = true;
    });

    document.addEventListener('keydown', function (e) {
      if (e.metaKey || e.ctrlKey || e.altKey) return;
      if ($('view-puzzle').hidden || !P) return;
      if (!$('modal').hidden || !$('menu').hidden) {
        if (e.key === 'Escape') { $('modal').hidden = true; $('menu').hidden = true; }
        return;
      }
      var k = e.key;
      if (/^[a-zA-Z]$/.test(k)) { inputLetter(k); }
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
    // iOS: block pinch-zoom gestures and double-tap zoom on the game surface
    document.addEventListener('gesturestart', function (e) { e.preventDefault(); });
    document.addEventListener('dblclick', function (e) { e.preventDefault(); }, { passive: false });

    tickHandle = setInterval(function () { if (running()) renderTimer(); }, 500);
    saveHandle = setInterval(function () { if (running()) saveState(); }, 5000);
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

  // expose a tiny hook for automated tests (no answers exposed)
  window.__crosshatch = { state: function () { return { sel: sel, dir: dir, S: S, date: P && P.date, running: running() }; } };
})();
