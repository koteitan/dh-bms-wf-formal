'use strict';

const WELL_FORMED = /^(\(\d+(,\d+)*\))+$/;

function esc(s) {
  return s.replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;');
}

const rows = [];
let broken = 0;
for (const raw of SHEET) {
  let bms, psi, cls;
  if (raw === 'Empty Matrix') {
    bms = '空列';
    psi = '0';
    cls = '';
  } else if (WELL_FORMED.test(raw)) {
    bms = raw;
    psi = lineToStabilityMountainPsi(raw);
    cls = '';
  } else {
    bms = raw;
    psi = '—';
    cls = ' class="broken"';
    broken++;
  }
  rows.push('<tr' + cls + '><td>' + esc(bms) + '</td><td>' + esc(psi) + '</td></tr>');
}

document.querySelector('#sheet tbody').innerHTML = rows.join('');
document.getElementById('note').textContent =
  SHEET.length + ' rows. ' + broken + ' of them have unbalanced parentheses in the source and are left unconverted.';

/* ---------- shared UI bits ---------- */

const KEY = 'mountain-psi';
const state = (function () {
  try { return JSON.parse(localStorage.getItem(KEY) || '{}'); } catch (e) { return {}; }
})();
const dark = state.dark === undefined ? true : state.dark;
document.documentElement.classList.toggle('light', !dark);

const menuBtn = document.getElementById('menu-btn');
const menu = document.getElementById('menu');
const darkToggle = document.getElementById('dark-toggle');
darkToggle.checked = dark;

darkToggle.addEventListener('change', function () {
  document.documentElement.classList.toggle('light', !darkToggle.checked);
  state.dark = darkToggle.checked;
  try { localStorage.setItem(KEY, JSON.stringify(state)); } catch (e) { /* ignore */ }
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
