'use strict';

/* ---------- BMS -> Stability-Mountain-Psi ---------- */

// Only "(", ")", digits, "," and newline survive.
function sanitize(s) {
  return s.replace(/[^0-9(),\n]/g, '');
}

// One line -> columns, padded with 0 up to the longest column.
// "(0)(1,1,1)" becomes "(0,0,0)(1,1,1)".  Returns null when the line has no column.
function parseLine(text) {
  const groups = text.match(/\(([^()]*)\)/g);
  if (!groups || groups.length === 0) return null;
  const cols = groups.map(function (g) {
    const body = g.slice(1, -1);
    if (body === '') return [];
    return body.split(',').map(function (p) {
      return p === '' ? 0 : parseInt(p, 10);
    });
  });
  let r = 0;
  for (const c of cols) if (c.length > r) r = c.length;
  for (const c of cols) while (c.length < r) c.push(0);
  return { cols: cols, r: r };
}

// parent[k][i] = the k-parent of column i, or null.
// Definition 2.1: for k = 0 the structural candidates are all j < i;
// for k > 0 they are the strict (k-1)-ancestors of i.  A candidate is
// valid when cols[j][k] < cols[i][k], and the parent is the largest one.
function computeParents(cols, r) {
  const n = cols.length;
  const parent = [];
  for (let k = 0; k < r; k++) {
    const pk = new Array(n).fill(null);
    for (let i = 0; i < n; i++) {
      const cands = [];
      if (k === 0) {
        for (let j = 0; j < i; j++) cands.push(j);
      } else {
        let j = parent[k - 1][i];
        while (j !== null) { cands.push(j); j = parent[k - 1][j]; }
      }
      let best = null;
      for (const j of cands) {
        if (cols[j][k] < cols[i][k] && (best === null || j > best)) best = j;
      }
      pk[i] = best;
    }
    parent.push(pk);
  }
  return parent;
}

// L(i) = the largest k such that i has a k-parent (0 when i has none).
// P(i) = that k-parent (null when i has none).
function convert(cols, r) {
  const n = cols.length;
  const parent = computeParents(cols, r);
  const L = new Array(n).fill(0);
  const P = new Array(n).fill(null);
  for (let i = 0; i < n; i++) {
    let bestK = null;
    for (let k = 0; k < r; k++) if (parent[k][i] !== null) bestK = k;
    if (bestK !== null) { L[i] = bestK; P[i] = parent[bestK][i]; }
  }
  const children = [];
  for (let i = 0; i < n; i++) children.push([]);
  const roots = [];
  for (let i = 0; i < n; i++) {
    if (P[i] === null) roots.push(i); else children[P[i]].push(i);
  }
  function render(i) {
    const inner = children[i].length === 0 ? '0' : children[i].map(render).join('+');
    return 'p' + L[i] + '(' + inner + ')';
  }
  return { text: roots.map(render).join('+'), L: L, P: P };
}

function lineToStabilityMountainPsi(line) {
  const p = parseLine(line);
  if (p === null) return '';
  return convert(p.cols, p.r).text;
}

// Whole textarea: one output line per input line.
function bmsToStabilityMountainPsi(text) {
  return sanitize(text).split('\n').map(lineToStabilityMountainPsi).join('\n');
}

/* ---------- UI ---------- */

const KEY = 'mountain-psi';
const DEFAULT_INPUT = '(0,0,0)(1,1,1)(2,0,0)(1,1,1)';

const state = (function () {
  try { return JSON.parse(localStorage.getItem(KEY) || '{}'); } catch (e) { return {}; }
})();

function save(patch) {
  Object.assign(state, patch);
  try { localStorage.setItem(KEY, JSON.stringify(state)); } catch (e) { /* ignore */ }
}

const dark = state.dark === undefined ? true : state.dark;
document.documentElement.classList.toggle('light', !dark);

const inEl = document.getElementById('in');
const outEl = document.getElementById('out');
const menuBtn = document.getElementById('menu-btn');
const menu = document.getElementById('menu');
const darkToggle = document.getElementById('dark-toggle');

darkToggle.checked = dark;

// A ?bms= link wins over the saved input.
const qbms = new URLSearchParams(location.search).get('bms');
if (qbms !== null) inEl.value = sanitize(qbms);
else if (state.input !== undefined) inEl.value = state.input;
else inEl.value = DEFAULT_INPUT;

// Drop invalid characters while keeping the caret where the user left it.
function sanitizeField(el) {
  const before = el.value;
  const after = sanitize(before);
  if (after === before) return;
  const pos = el.selectionStart;
  const head = before.slice(0, pos);
  const removed = head.length - sanitize(head).length;
  el.value = after;
  const p = Math.max(0, pos - removed);
  el.setSelectionRange(p, p);
}

function updateURL(text, ok) {
  const u = new URL(location.href);
  if (ok) u.searchParams.set('bms', text); else u.searchParams.delete('bms');
  history.replaceState(null, '', u.pathname + (u.search ? u.search : '') + u.hash);
}

function run() {
  sanitizeField(inEl);
  const lines = inEl.value.split('\n');
  const out = lines.map(lineToStabilityMountainPsi);
  outEl.value = out.join('\n');
  save({ input: inEl.value });
  updateURL(inEl.value, out.some(function (s) { return s !== ''; }));
}

inEl.addEventListener('input', run);

darkToggle.addEventListener('change', function () {
  document.documentElement.classList.toggle('light', !darkToggle.checked);
  save({ dark: darkToggle.checked });
});

menuBtn.addEventListener('click', function () {
  const open = menu.hidden;
  menu.hidden = !open;
  menuBtn.setAttribute('aria-expanded', String(open));
});
document.addEventListener('click', function (e) {
  if (!document.getElementById('menu-wrap').contains(e.target)) {
    menu.hidden = true;
    menuBtn.setAttribute('aria-expanded', 'false');
  }
});

run();
