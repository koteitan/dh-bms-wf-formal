'use strict';

/* ---------- BMS -> Stability-Mountain-Psi ---------- */

// "(0,0,0)(1,1,1)" -> [[0,0,0],[1,1,1]]
function parseBMS(text) {
  const groups = text.match(/\(([^()]*)\)/g);
  if (!groups || groups.length === 0) {
    return { error: 'no column found. write it as (0,0,0)(1,1,1)' };
  }
  const cols = [];
  for (let i = 0; i < groups.length; i++) {
    const body = groups[i].slice(1, -1).trim();
    if (body === '') return { error: 'column ' + i + ' is empty' };
    const parts = body.split(',').map(function (s) { return s.trim(); });
    const nums = [];
    for (const p of parts) {
      if (!/^\d+$/.test(p)) return { error: 'column ' + i + ': "' + p + '" is not a non-negative integer' };
      nums.push(parseInt(p, 10));
    }
    cols.push(nums);
  }
  const r = cols[0].length;
  for (let i = 0; i < cols.length; i++) {
    if (cols[i].length !== r) {
      return { error: 'column ' + i + ' has ' + cols[i].length + ' rows, but column 0 has ' + r };
    }
  }
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
    return 'p_' + L[i] + '(' + inner + ')';
  }
  return { text: roots.map(render).join('+'), L: L, P: P };
}

function bmsToStabilityMountainPsi(text) {
  const parsed = parseBMS(text);
  if (parsed.error) return { error: parsed.error };
  return convert(parsed.cols, parsed.r);
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
const errEl = document.getElementById('err');
const btn = document.getElementById('convert');
const menuBtn = document.getElementById('menu-btn');
const menu = document.getElementById('menu');
const darkToggle = document.getElementById('dark-toggle');

inEl.value = state.input === undefined ? DEFAULT_INPUT : state.input;
darkToggle.checked = dark;

function run() {
  const res = bmsToStabilityMountainPsi(inEl.value);
  if (res.error) { outEl.value = ''; errEl.textContent = res.error; }
  else { outEl.value = res.text; errEl.textContent = ''; }
  save({ input: inEl.value });
}

btn.addEventListener('click', run);
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

if (typeof module !== 'undefined') module.exports = { bmsToStabilityMountainPsi: bmsToStabilityMountainPsi };
