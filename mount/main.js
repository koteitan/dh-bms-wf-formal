'use strict';

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
