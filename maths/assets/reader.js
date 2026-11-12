/* The paper beside its Lean (12 November 2026).

   Each printed result (a theorem, proposition, corollary or lemma whose id is
   a recorded result label) gains a chip on its heading line. The chip opens a
   pane beside the text: on a wide screen it takes the place of the margin
   contents, on a narrow one it is a sheet over the foot of the page. The pane
   has two tabs: the Lean statement with how it relates to the printed one,
   and a drawing of the Lean files behind it.

   The data is assets/reader/<paper_id>.json, named with its content hash on
   the page's script tag (build_plectis_maths_site.reader_head_html). Without
   this script, or when the data does not load, the page is unchanged.

   Following the text uses the Proof Reader's reading line
   (proof-reader web/src/paper/reading-line.ts): the result at or above 0.34 of
   the viewport is the one being read, settled after 200 ms. The Graph tab's
   layered layout orders each row by the barycentre of its parents, after the
   same reader's map engine (web/src/map/engine/order.ts), reduced to the few
   files a result depends on. */
(function () {
  'use strict';

  var READING_LINE = 0.34;
  var FOLLOW_MS = 200;
  var WIDE = '(min-width: 1100px)';
  var GRAPH_CAP = 14;
  var RESULT_SELECTOR = ['theorem', 'proposition', 'corollary', 'lemma', 'thm', 'lem', 'prop', 'cor']
    .map(function (c) { return 'div.' + c + '[id]'; }).join(',');

  var CHIP_TEXT = {
    exact: 'Lean: exact',
    exact_or_stronger: 'Lean: exact or stronger',
    modulo_named_input: 'Lean: with named assumptions',
    none: 'No Lean statement'
  };
  var RELATION_TEXT = {
    exact: 'The Lean statement is recorded as the same statement as the printed one.',
    exact_or_stronger: 'The Lean statement is recorded as the same as the printed statement or stronger.',
    modulo_named_input: 'The Lean statement is proved from the named assumptions listed below.',
    none: 'No Lean statement is recorded for this result. The proof here is the written one.'
  };
  var FOOT_TEXT = 'The link from a printed result to a Lean declaration was made with AI and records how the two ' +
    'statements relate. Lean, a program that checks mathematical proofs, checks the formal proof. ' +
    'It does not check the wording of the paper.';

  function escapeHtml(text) {
    return String(text == null ? '' : text).replace(/[&<>"']/g, function (c) {
      return { '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[c];
    });
  }
  function extLink(href, text, cls) {
    return '<a' + (cls ? ' class="' + cls + '"' : '') + ' href="' + escapeHtml(href) +
      '" data-link-kind="exogenous" rel="external noopener" target="_blank">' + text + '</a>';
  }
  function nameHtml(text) {
    var safe = escapeHtml(text);
    return safe.length < 20 ? safe : safe.replace(/([._])(?=[^._])/g, '$1<wbr>');
  }
  function shortName(path) {
    var last = String(path || '').split('/').pop();
    return last.replace(/\.lean$/, '');
  }

  /* The map's Comparator wording (universe.js checksHtml), word for word. */
  function comparatorHtml(r, data) {
    var said, runRow = r.run != null ? (data.runs || [])[r.run] : null;
    if (r.comparator === 'compared') {
      said = 'Comparator ran a test using two files: a theorem statement (the challenge) and a proof (the solution). ' +
        'The proof was accepted as proving that exact statement under its stated assumptions.';
      var run = runRow && runRow.id ? (runRow.href ? extLink(runRow.href, 'run ' + escapeHtml(runRow.id)) : 'run ' + escapeHtml(runRow.id)) : '';
      var entries = r.entries || [];
      if (entries.length) {
        said += (run ? ' In ' + run + ' its' : ' Its') + ' corpus entr' + (entries.length > 1 ? 'ies ' : 'y ') +
          entries.map(escapeHtml).join(' and ') + ' passed, with the Lean proof verifier and a second verifier, nanoda, ' +
          (entries.length > 1 ? 'accepting each.' : 'both accepting it.');
      } else if (run) {
        said += ' It passed in ' + run + ', with both the Lean proof verifier and a second verifier, nanoda, accepting the theorem and proof.';
      }
    } else if (r.status === 'exact' || r.status === 'exact_or_stronger') {
      said = escapeHtml(r.comparator === 'pending' && r.queued ?
        'A test of the proof against a separate statement has been queued since ' + r.queued + '.' :
        'No Comparator test of the proof against a separate statement is recorded for this paper result.');
    } else {
      said = 'A comparison test requires an exact Lean statement; none is recorded here.';
    }
    return '<p class="lean-pane__comparator"><b>Comparator.</b> ' + said + '</p>';
  }

  function declHref(d, data) {
    if (d.href) return d.href;
    var file = d.file != null ? (data.files || [])[d.file] : null;
    return data.source && file ? data.source + file + (d.line ? '#L' + d.line : '') : '';
  }

  function leanTabHtml(item) {
    var r = item.result, data = item.data;
    var html = '<p class="lean-pane__relation lean-pane__relation--' + escapeHtml(r.status) + '">' +
      escapeHtml(RELATION_TEXT[r.status] || RELATION_TEXT.none) + '</p>';
    if (r.note || r.reason) {
      html += '<h3 class="lean-pane__sub">How the Lean statement relates</h3>';
      if (r.note) html += '<p class="lean-pane__note">' + r.note + '</p>';
      if (r.reason) html += '<p class="lean-pane__note">' + r.reason + '</p>';
    }
    if ((r.inputs || []).length) {
      html += '<h3 class="lean-pane__sub">Named assumptions</h3><ol class="lean-pane__list">' +
        r.inputs.map(function (input) {
          var name = '<code>' + nameHtml(input.name) + '</code>';
          return '<li>' + (input.href ? extLink(input.href, name, 'lean-pane__name') : '<span class="lean-pane__name">' + name + '</span>') +
            (input.text ? '<pre class="lean-pane__code"><code>' + escapeHtml(input.text) + '</code></pre>' : '') + '</li>';
        }).join('') + '</ol>';
    }
    if ((r.decls || []).length) {
      html += '<h3 class="lean-pane__sub">' + (r.decls.length > 1 ? 'Lean declarations' : 'Lean declaration') + '</h3>' +
        '<ol class="lean-pane__list">' + r.decls.map(function (d) {
          return '<li><p class="lean-pane__decl"><code class="lean-pane__name">' + nameHtml(d.name) + '</code>' +
            (d.kind ? ' <span class="lean-pane__kind">' + escapeHtml(d.kind) + '</span>' : '') + '</p>' +
            (d.sig ? '<pre class="lean-pane__code" tabindex="0" aria-label="Lean signature of ' + escapeHtml(d.name) + '"><code>' + escapeHtml(d.sig) + '</code></pre>' : '') +
            (declHref(d, data) ? '<p class="lean-pane__source">' + extLink(declHref(d, data), 'Open in the Lean source on GitHub' + (d.line ? ', line ' + d.line : '')) + '</p>' : '') +
            '</li>';
        }).join('') + '</ol>';
    }
    if (r.status !== 'none' || r.comparator === 'compared') html += comparatorHtml(r, data);
    if (data.map) {
      html += '<p class="lean-pane__map"><a href="' + escapeHtml(data.map +
        encodeURIComponent('statement:' + data.paper + '#' + item.label)) + '">This result on the map</a></p>';
    }
    return html;
  }

  /* ---- Graph: the Lean files behind a result ------------------------------ */

  var SVG = 'http://www.w3.org/2000/svg';
  function graphHtml(r, data, width) {
    var head = '<h3 class="lean-pane__sub">Lean files this statement depends on</h3>' +
      '<p class="lean-pane__graph-note">The dependencies are between Lean files. Dependencies between individual ' +
      'declarations are not recorded on this site.</p>';
    var roots = (r.modules || []).slice();
    if (!roots.length) return head + '<p class="lean-pane__graph-note">No Lean file is recorded for this result.</p>';
    var out = {};
    (data.imports || []).forEach(function (edge) { (out[edge[0]] = out[edge[0]] || []).push(edge[1]); });
    var layer = {};
    roots.forEach(function (m) { layer[m] = 0; });
    var rows = [roots];
    var hidden = 0;
    for (var step = 1; step <= 2; step++) {
      var next = [];
      rows[step - 1].forEach(function (m) {
        (out[m] || []).forEach(function (t) {
          if (layer[t] === undefined) { layer[t] = step; next.push(t); }
        });
      });
      if (!next.length) break;
      var drawn = rows.reduce(function (n, row) { return n + row.length; }, 0);
      if (step === 2 && drawn + next.length > GRAPH_CAP) { hidden += next.length; break; }
      if (drawn + next.length > GRAPH_CAP) {
        hidden += drawn + next.length - GRAPH_CAP;
        next.forEach(function (t, i) { if (i >= GRAPH_CAP - drawn) delete layer[t]; });
        next = next.slice(0, GRAPH_CAP - drawn);
        rows.push(next);
        // The next step would hide behind a truncated row; count it as hidden.
        var beyond = {};
        rows[step - 1].concat(next).forEach(function (m) {
          (out[m] || []).forEach(function (t) { if (layer[t] === undefined) beyond[t] = true; });
        });
        hidden += Object.keys(beyond).length;
        break;
      }
      rows.push(next);
    }

    // Order each row by the barycentre of its parents in the row above.
    var x = {};
    rows.forEach(function (row, depth) {
      if (depth > 0) {
        var bary = {};
        row.forEach(function (m) {
          var sum = 0, n = 0;
          rows[depth - 1].forEach(function (p) {
            if ((out[p] || []).indexOf(m) >= 0) { sum += x[p]; n += 1; }
          });
          bary[m] = n ? sum / n : 0;
        });
        row.sort(function (a, b) { return bary[a] - bary[b] || a - b; });
      }
      row.forEach(function (m, i) { x[m] = i; });
    });

    // Rows wrap to the pane's width; each wrapped line is a band of its row.
    var W = Math.max(240, Math.floor(width));
    var NODE_H = 30, GAP_X = 10, GAP_Y = 34, BAND_Y = 12, MIN_W = 110;
    var widest = rows.reduce(function (n, row) { return Math.max(n, row.length); }, 1);
    var perLine = Math.max(1, Math.min(widest, Math.floor((W + GAP_X) / (MIN_W + GAP_X))));
    var NODE_W = Math.min(200, Math.floor((W - (perLine - 1) * GAP_X) / perLine));
    var maxChars = Math.max(8, Math.floor((NODE_W - 14) / 6.6));
    var pos = {}, y = 2;
    rows.forEach(function (row, depth) {
      for (var start = 0; start < row.length; start += perLine) {
        var line = row.slice(start, start + perLine);
        var lineW = line.length * NODE_W + (line.length - 1) * GAP_X;
        var left = (W - lineW) / 2;
        line.forEach(function (m, i) { pos[m] = { x: left + i * (NODE_W + GAP_X), y: y, depth: depth }; });
        y += NODE_H + (start + perLine < row.length ? BAND_Y : GAP_Y);
      }
    });
    var H = y - GAP_Y + NODE_H / 2 + 4;
    var uid = 'lean-arrow-' + Math.random().toString(36).slice(2, 8);
    var svg = '<svg class="lean-graph" viewBox="0 0 ' + W + ' ' + Math.ceil(H) + '" width="' + W + '" height="' + Math.ceil(H) +
      '" role="group" aria-label="Lean files this statement depends on" xmlns="' + SVG + '">' +
      '<defs><marker id="' + uid + '" viewBox="0 0 8 8" refX="7" refY="4" markerWidth="7" markerHeight="7" orient="auto-start-reverse">' +
      '<path class="lean-graph__head" d="M0,0 L8,4 L0,8 z"/></marker></defs>';
    (data.imports || []).forEach(function (edge) {
      var a = pos[edge[0]], b = pos[edge[1]];
      if (!a || !b || b.depth !== a.depth + 1) return;
      svg += '<line class="lean-graph__edge" x1="' + (a.x + NODE_W / 2).toFixed(1) + '" y1="' + (a.y + NODE_H).toFixed(1) +
        '" x2="' + (b.x + NODE_W / 2).toFixed(1) + '" y2="' + (b.y - 1).toFixed(1) + '" marker-end="url(#' + uid + ')"/>';
    });
    Object.keys(pos).forEach(function (key) {
      var m = Number(key), p = pos[key], mod = data.modules[m] || {};
      var name = shortName(mod.path || mod.label);
      var shown = name.length > maxChars ? name.slice(0, maxChars - 1) + '…' : name;
      var full = String(mod.path || mod.label || '');
      var root = p.depth === 0;
      svg += '<a class="lean-graph__node' + (root ? ' lean-graph__node--root' : '') + '" href="' + escapeHtml(mod.href || '') +
        '" target="_blank" rel="external noopener" data-link-kind="exogenous" aria-label="' +
        escapeHtml(full + (root ? ', the file this result is stated in' : '') + ', on GitHub') + '">' +
        '<title>' + escapeHtml(full) + '</title>' +
        '<rect x="' + p.x.toFixed(1) + '" y="' + p.y.toFixed(1) + '" width="' + NODE_W + '" height="' + NODE_H + '" rx="6"/>' +
        '<text x="' + (p.x + NODE_W / 2).toFixed(1) + '" y="' + (p.y + NODE_H / 2 + 4).toFixed(1) + '" text-anchor="middle">' +
        escapeHtml(shown) + '</text></a>';
    });
    svg += '</svg>';
    return head + '<div class="lean-graph__frame">' + svg + '</div>' +
      (hidden ? '<p class="lean-pane__graph-note">and ' + hidden + ' more file' + (hidden > 1 ? 's' : '') + '</p>' : '') +
      '<p class="lean-pane__key">An arrow from A to B means the file A imports the file B.</p>';
  }

  /* ---- The reader --------------------------------------------------------- */

  function start() {
    var tag = document.querySelector('script[data-lean-reader]');
    var layout = document.querySelector('.maths-layout');
    if (!tag || !layout || !window.fetch) return;
    var routes;
    try { routes = JSON.parse(tag.getAttribute('data-lean-reader')); } catch (err) { return; }
    var paperIds = Object.keys(routes || {});
    if (!paperIds.length) return;

    // The printed results, in reading order, with their paper and label.
    var found = [];
    Array.prototype.forEach.call(document.querySelectorAll(RESULT_SELECTOR), function (el) {
      if (el.closest('[data-paper-anchor-routes], .lean-pane')) return;
      var id = el.id, paper = null, label = id;
      for (var i = 0; i < paperIds.length; i++) {
        if (id.indexOf(paperIds[i] + '__') === 0) { paper = paperIds[i]; label = id.slice(paperIds[i].length + 2); break; }
      }
      if (!paper) {
        if (paperIds.length !== 1 || id.indexOf('__') >= 0) return;
        paper = paperIds[0];
      }
      found.push({ el: el, paper: paper, label: label });
    });
    var wanted = {};
    found.forEach(function (f) { wanted[f.paper] = true; });
    var hashLean = leanHash();
    var needed = Object.keys(wanted);
    if (!needed.length) return;
    Promise.all(needed.map(function (paper) {
      return fetch(new URL(routes[paper], tag.src).href).then(function (r) {
        if (!r.ok) throw new Error('reader data');
        return r.json();
      }).then(function (data) {
        if (!data || data.paper !== paper || !data.results) throw new Error('reader data');
        return data;
      });
    })).then(function (datas) {
      var byPaper = {};
      datas.forEach(function (d) { byPaper[d.paper] = d; });
      mount(found.filter(function (f) {
        f.data = byPaper[f.paper];
        f.result = f.data && f.data.results[f.label];
        return !!f.result;
      }), layout, hashLean);
    }).catch(function () { /* The page stays as it is. */ });
  }

  function leanHash() {
    var hash = window.location.hash || '';
    if (hash.indexOf('#lean=') !== 0) return null;
    try { return decodeURIComponent(hash.slice(6)); } catch (err) { return hash.slice(6); }
  }

  function mount(items, layout, hashLean) {
    if (!items.length) return;
    var wide = window.matchMedia ? window.matchMedia(WIDE) : { matches: true };
    var current = null, opener = null, following = true, userMoved = false;

    items.forEach(function (item, i) {
      var r = item.result;
      var chip = document.createElement('button');
      chip.type = 'button';
      chip.className = 'lean-chip lean-chip--' + r.status;
      chip.textContent = CHIP_TEXT[r.status] || CHIP_TEXT.none;
      var printed = item.el.querySelector('strong');
      var name = printed ? printed.textContent.trim() : r.label;
      chip.setAttribute('aria-label', 'Lean statement for ' + name);
      chip.setAttribute('aria-controls', 'lean-pane');
      chip.setAttribute('aria-expanded', 'false');
      chip.setAttribute('data-term-auto', 'off');
      var head = item.el.firstElementChild;
      if (head && head.tagName === 'P') head.insertBefore(chip, head.firstChild);
      else item.el.insertBefore(chip, item.el.firstChild);
      item.chip = chip;
      item.index = i;
      chip.addEventListener('click', function () {
        following = false;
        opener = chip;
        show(item, { focus: true, hash: true });
      });
    });

    // The pane, built once; it sits in the layout's grid after the text.
    var pane = document.createElement('aside');
    pane.className = 'lean-pane';
    pane.id = 'lean-pane';
    pane.hidden = true;
    pane.setAttribute('aria-label', 'Lean statement');
    pane.setAttribute('data-term-auto', 'off');
    pane.innerHTML =
      '<div class="lean-pane__head">' +
        '<button type="button" class="lean-pane__label" data-lean-back></button>' +
        '<button type="button" class="lean-pane__close" data-lean-close aria-label="Close the Lean pane">Close</button>' +
      '</div>' +
      '<div class="lean-pane__controls">' +
        '<button type="button" class="lean-pane__follow" data-lean-follow aria-pressed="true">Following the text</button>' +
        '<div class="lean-pane__tabs" role="tablist" aria-label="Lean pane views">' +
          '<button type="button" role="tab" id="lean-tab-lean" aria-controls="lean-panel-lean" aria-selected="true">Lean</button>' +
          '<button type="button" role="tab" id="lean-tab-graph" aria-controls="lean-panel-graph" aria-selected="false" tabindex="-1">Graph</button>' +
        '</div>' +
      '</div>' +
      '<div class="lean-pane__scroll">' +
        '<div class="lean-pane__panel" role="tabpanel" id="lean-panel-lean" aria-labelledby="lean-tab-lean" tabindex="0"></div>' +
        '<div class="lean-pane__panel" role="tabpanel" id="lean-panel-graph" aria-labelledby="lean-tab-graph" tabindex="0" hidden></div>' +
      '</div>' +
      '<p class="lean-pane__foot">' + escapeHtml(FOOT_TEXT) + '</p>';
    layout.appendChild(pane);
    var labelBtn = pane.querySelector('[data-lean-back]');
    var closeBtn = pane.querySelector('[data-lean-close]');
    var followBtn = pane.querySelector('[data-lean-follow]');
    var tabs = Array.prototype.slice.call(pane.querySelectorAll('[role="tab"]'));
    var panels = { lean: pane.querySelector('#lean-panel-lean'), graph: pane.querySelector('#lean-panel-graph') };
    var scroller = pane.querySelector('.lean-pane__scroll');
    var tab = 'lean';

    function setFollowing(on) {
      following = on;
      followBtn.setAttribute('aria-pressed', on ? 'true' : 'false');
    }
    function render() {
      if (!current) return;
      var r = current.result;
      labelBtn.textContent = r.label;
      labelBtn.setAttribute('aria-label', r.label + ': return to it in the text');
      panels.lean.innerHTML = leanTabHtml(current);
      renderGraph();
    }
    function renderGraph() {
      if (!current || tab !== 'graph') return;
      var width = panels.graph.clientWidth || scroller.clientWidth || 360;
      panels.graph.innerHTML = graphHtml(current.result, current.data, width);
    }
    function selectTab(name, focus) {
      tab = name;
      tabs.forEach(function (t) {
        var on = t.id === 'lean-tab-' + name;
        t.setAttribute('aria-selected', on ? 'true' : 'false');
        t.tabIndex = on ? 0 : -1;
        if (on && focus) t.focus();
      });
      panels.lean.hidden = name !== 'lean';
      panels.graph.hidden = name !== 'graph';
      renderGraph();
    }
    function setHash() {
      if (!current || !window.history || !history.replaceState) return;
      history.replaceState(history.state, '', window.location.pathname + window.location.search +
        '#lean=' + encodeURIComponent(current.label).replace(/%3A/g, ':'));
    }
    function show(item, opts) {
      opts = opts || {};
      var changed = current !== item;
      if (current && current.chip) current.chip.setAttribute('aria-expanded', 'false');
      current = item;
      item.chip.setAttribute('aria-expanded', 'true');
      if (pane.hidden) {
        pane.hidden = false;
        layout.classList.add('has-lean-pane');
        document.documentElement.classList.add('has-lean-pane');
      }
      setFollowing(following);
      if (changed || opts.force) { render(); scroller.scrollTop = 0; }
      if (opts.hash) setHash();
      if (opts.focus) labelBtn.focus({ preventScroll: true });
    }
    function close() {
      if (pane.hidden) return;
      pane.hidden = true;
      layout.classList.remove('has-lean-pane');
      document.documentElement.classList.remove('has-lean-pane');
      if (current && current.chip) current.chip.setAttribute('aria-expanded', 'false');
      var back = opener || (current && current.chip);
      current = null;
      if (window.history && history.replaceState && (window.location.hash || '').indexOf('#lean=') === 0) {
        history.replaceState(history.state, '', window.location.pathname + window.location.search);
      }
      if (back) back.focus({ preventScroll: true });
      opener = null;
    }

    // Sections far from the viewport are laid out lazily, so one jump can
    // land short; repeat it until the result holds still or the reader moves.
    var lastInput = 0, settling = 0;
    function bringToTop(el, ms) {
      var started = Date.now(), last = null, mine = ++settling;
      (function settle() {
        if (mine !== settling || lastInput > started || Date.now() - started > ms) return;
        var top = el.getBoundingClientRect().top;
        if (last === null || Math.abs(top - last) > 1) {
          el.scrollIntoView({ block: 'start', behavior: 'auto' });
          last = el.getBoundingClientRect().top;
        }
        window.setTimeout(settle, 60);
      })();
    }
    labelBtn.addEventListener('click', function () {
      if (current) bringToTop(current.el, 1500);
    });
    closeBtn.addEventListener('click', close);
    followBtn.addEventListener('click', function () {
      setFollowing(!following);
      if (following) follow(true);
    });
    tabs.forEach(function (t, i) {
      t.addEventListener('click', function () { selectTab(t.id.slice(9)); });
      t.addEventListener('keydown', function (ev) {
        var step = ev.key === 'ArrowRight' ? 1 : ev.key === 'ArrowLeft' ? -1 : 0;
        if (!step) return;
        ev.preventDefault();
        selectTab(tabs[(i + step + tabs.length) % tabs.length].id.slice(9), true);
      });
    });
    document.addEventListener('keydown', function (ev) {
      if (ev.key === 'Escape' && !pane.hidden && !ev.defaultPrevented) close();
    });

    // Following the text: the result at or above the reading line.
    function atReadingLine() {
      var line = window.innerHeight * READING_LINE, best = null;
      for (var i = 0; i < items.length; i++) {
        var top = items[i].el.getBoundingClientRect().top;
        if (top <= line) best = items[i];
        else break;
      }
      return best || items[0];
    }
    var timer = 0;
    function follow(now) {
      window.clearTimeout(timer);
      var run = function () {
        if (pane.hidden || !following) return;
        var item = atReadingLine();
        if (item && item !== current) { show(item); if (userMoved) setHash(); }
      };
      if (now) run(); else timer = window.setTimeout(run, FOLLOW_MS);
    }
    ['wheel', 'touchstart', 'keydown', 'pointerdown'].forEach(function (name) {
      window.addEventListener(name, function (ev) {
        if (ev.isTrusted) { userMoved = true; lastInput = Date.now(); }
      }, { passive: true, capture: true });
    });
    window.addEventListener('scroll', function () {
      if (userMoved && following && !pane.hidden) follow(false);
    }, { passive: true });
    var resizeTimer = 0;
    window.addEventListener('resize', function () {
      window.clearTimeout(resizeTimer);
      resizeTimer = window.setTimeout(renderGraph, 150);
    });

    function byId(id) {
      for (var i = 0; i < items.length; i++) if (items[i].el.id === id) return items[i];
      return null;
    }
    function byLabel(label) {
      for (var i = 0; i < items.length; i++) if (items[i].label === label) return items[i];
      return null;
    }
    // Arrival: #lean=<label> opens its pane; #<result id> (the map's "Read it
    // in the paper") keeps the browser's scroll and opens the pane when wide.
    function arrive(initial) {
      settling += 1;
      var label = leanHash();
      if (label) {
        var item = byLabel(label);
        if (!item) return;
        show(item, {});
        // Late fonts and the shared runtime can also move the text after
        // the first jump on arrival.
        bringToTop(item.el, initial ? 2400 : 1500);
        return;
      }
      var id = '';
      try { id = decodeURIComponent((window.location.hash || '').slice(1)); } catch (err) { return; }
      var target = id && byId(id);
      if (target && wide.matches) {
        show(target, {});
      }
    }
    arrive(true);
    window.addEventListener('hashchange', function () { arrive(false); });
  }

  if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', start, { once: true });
  else start();
})();
