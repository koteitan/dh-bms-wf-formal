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
