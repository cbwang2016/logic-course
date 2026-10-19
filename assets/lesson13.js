// Lesson 13: Tarski's undefinability of truth.
// Pure logic first (testable in node), DOM code afterwards.

/* ================= Gödel numbering (same table as Lesson 12) ================= */
const GSYM = [['0', 1], ['S', 2], ['+', 3], ['×', 4], ['=', 5], ['(', 6], [')', 7], ['¬', 8], ['∧', 9], ['∨', 10],
  ['→', 11], ['∀', 12], ['∃', 13], ['x', 14], ['y', 15], ['z', 16]];
const GCODE = Object.fromEntries(GSYM);
const PRIMES = (() => {
  const out = [];
  for (let n = 2; out.length < 200; n++) if (out.every(p => p * p > n || n % p)) out.push(n);
  return out;
})();
function gEncodeStr(str) {
  const syms = [...str.replace(/\s+/g, '')];
  let n = 1n;
  syms.forEach((c, i) => {
    if (!(c in GCODE)) throw new Error('symbol ' + c);
    n *= BigInt(PRIMES[i]) ** BigInt(GCODE[c]);
  });
  return n;
}

/* ================= revision semantics for liar-like systems ================= */
// claims: {A: {to:'B', neg:true}} means A says "B is false".
function revise(claims, v) {
  const out = {};
  for (const k in claims) { const c = claims[k]; out[k] = c.neg ? 1 - v[c.to] : v[c.to]; }
  return out;
}
function fixedPoints(claims) {
  const ks = Object.keys(claims), res = [];
  for (let m = 0; m < (1 << ks.length); m++) {
    const v = {};
    ks.forEach((k, i) => { v[k] = (m >> (ks.length - 1 - i)) & 1; });
    const r = revise(claims, v);
    res.push({ v, fixed: ks.every(k => r[k] === v[k]) });
  }
  return res;
}

/* ================= arithmetic formulas with variables ================= */
// terms: {k:'0'} {k:'S',a} {k:'+',a,b} {k:'×',a,b} {k:'v',v}
// formulas: {t:'eq',a,b} {t:'not',a} {t:'and',a,b} {t:'ex',v,a} {t:'all',v,a}
const T0 = { k: '0' }, TS = a => ({ k: 'S', a }), TV = v => ({ k: 'v', v });
const Tadd = (a, b) => ({ k: '+', a, b }), Tmul = (a, b) => ({ k: '×', a, b });
const num = n => { let t = T0; for (let i = 0; i < n; i++) t = TS(t); return t; };
function tval(t, s) {
  switch (t.k) {
    case '0': return 0;
    case 'S': return tval(t.a, s) + 1;
    case '+': return tval(t.a, s) + tval(t.b, s);
    case '×': return tval(t.a, s) * tval(t.b, s);
    default: return s[t.v];
  }
}
function tshow(t) {
  switch (t.k) {
    case '0': return '0';
    case 'S': return 'S' + (t.a.k === '+' || t.a.k === '×' ? '(' + tshow(t.a) + ')' : tshow(t.a));
    case '+': return tshow(t.a) + '+' + tshow(t.b);
    case '×': return tshow(t.a) + '×' + tshow(t.b);
    default: return t.v;
  }
}
function fshow(f) {
  switch (f.t) {
    case 'eq': return tshow(f.a) + ' = ' + tshow(f.b);
    case 'not': return '¬' + (f.a.t === 'eq' ? '(' + fshow(f.a) + ')' : fshow(f.a));
    case 'and': return '(' + fshow(f.a) + ' ∧ ' + fshow(f.b) + ')';
    case 'ex': return '∃' + f.v + ' ' + (f.a.t === 'eq' ? '(' + fshow(f.a) + ')' : fshow(f.a));
    default: return '∀' + f.v + ' ' + (f.a.t === 'eq' ? '(' + fshow(f.a) + ')' : fshow(f.a));
  }
}
// Truth in ℕ with quantifiers checked up to a bound (exact for the sample sentences used here,
// whose witnesses/counterexamples are small and whose terms grow with the variables).
function sat(f, s, B = 40) {
  switch (f.t) {
    case 'eq': return tval(f.a, s) === tval(f.b, s);
    case 'not': return !sat(f.a, s, B);
    case 'and': return sat(f.a, s, B) && sat(f.b, s, B);
    case 'ex': for (let n = 0; n <= B; n++) if (sat(f.a, { ...s, [f.v]: n }, B)) return true; return false;
    default: for (let n = 0; n <= B; n++) if (!sat(f.a, { ...s, [f.v]: n }, B)) return false; return true;
  }
}
const SAMPLES = [
  { f: { t: 'ex', v: 'x', a: { t: 'eq', a: Tmul(TV('x'), TV('x')), b: num(4) } }, en: '4 is a square', zh: '4 是平方数' },
  { f: { t: 'all', v: 'x', a: { t: 'not', a: { t: 'eq', a: Tmul(TV('x'), TV('x')), b: num(2) } } }, en: '2 is not a square', zh: '2 不是平方数' },
  { f: { t: 'all', v: 'x', a: { t: 'ex', v: 'y', a: { t: 'eq', a: Tadd(TV('x'), TV('y')), b: num(3) } } }, en: 'every x is ≤ 3', zh: '每个 x 都 ≤ 3' },
];

if (typeof module !== 'undefined') module.exports = { gEncodeStr, revise, fixedPoints, sat, fshow, tval, SAMPLES, num, PRIMES };

/* ======================================================================= */
/* ============================ DOM part ================================= */
/* ======================================================================= */
if (typeof document !== 'undefined') {
Lang.init();
Progress.paint();

const $ = id => document.getElementById(id);
const okBox = (box, html, kind = 'ok') => { box.className = 'msg ' + kind; box.innerHTML = html; };
const clearBox = box => { box.className = 'msg'; box.innerHTML = ''; };
const SUBD = '₀₁₂₃₄₅₆₇₈₉';
const subs = n => String(n).split('').map(d => SUBD[d] ?? d).join('');

function svgBi(parent, attrs, en, zh) {
  const t = el('text', attrs, parent);
  const a = el('tspan', { class: 'en' }, t); a.textContent = en;
  const s = el('tspan', { class: 'bisep', fill: '#999' }, t); s.textContent = ' · ';
  const b = el('tspan', { class: 'zh' }, t); b.textContent = zh;
  return t;
}
function svgBi2(parent, attrs, en, zh, dy = 16) {
  const st = attrs['font-size'] ? `font-size:${attrs['font-size']}px` : '';
  const a = el('text', { ...attrs, class: 'en', style: st }, parent); a.textContent = en;
  const b = el('text', { ...attrs, class: 'zh', y: +attrs.y + dy, style: st }, parent); b.textContent = zh;
  return [a, b];
}
const bl = (en, zh) => en === zh ? en : bil(en, zh);
function svgT(parent, attrs, txt) { const t = el('text', attrs, parent); t.textContent = txt; return t; }
// arrow marker shared by all SVGs on the page
(function () {
  const d = el('svg', { width: 0, height: 0, style: 'position:absolute' }, document.body);
  const defs = el('defs', {}, d);
  [['arr13', '#9aa0aa'], ['arr13m', '#ae3ec9'], ['arr13r', '#e03131']].forEach(([id, c]) => {
    const m = el('marker', { id, viewBox: '0 0 10 10', refX: 9, refY: 5, markerWidth: 7, markerHeight: 7, orient: 'auto-start-reverse' }, defs);
    el('path', { d: 'M0,0 L10,5 L0,10 z', fill: c }, m);
  });
})();

function stepper(stepsId, nextId, allId) {
  const steps = [...$(stepsId).querySelectorAll(':scope > .step')];
  let k = 0;
  const all = () => { steps.forEach(s => s.classList.add('on')); k = steps.length; $(nextId).disabled = true; };
  $(nextId).addEventListener('click', () => { if (k < steps.length) steps[k++].classList.add('on'); if (k === steps.length) $(nextId).disabled = true; });
  $(allId).addEventListener('click', all);
  return { all, steps };
}
function tfList(box, items, progId, opts = {}) {
  const L = opts.labels || [['True', '对'], ['False', '错']];
  const solved = items.map(() => false), revealed = items.map(() => false);
  items.forEach((it, i) => {
    const row = document.createElement('div');
    row.className = 'tf';
    row.innerHTML = `<div class="stmt" style="font-size:15px">${it.s}</div>
      <div style="display:flex;gap:8px;flex-wrap:wrap"><button class="btn small" data-v="1">${bil(L[0][0], L[0][1])}</button>
      <button class="btn small" data-v="0">${bil(L[1][0], L[1][1])}</button>
      <button class="btn small ghost" data-v="show">${bil('Show answer', '看答案')}</button></div>
      <div style="flex-basis:100%"><div class="msg"></div></div>`;
    box.appendChild(row);
    const msg = row.querySelector('.msg');
    row.querySelectorAll('button').forEach(b => b.addEventListener('click', () => {
      const verdict = it.ans ? bi(`<b>${L[0][0]}.</b> `, `<b>${L[0][1]}。</b>`) : bi(`<b>${L[1][0]}.</b> `, `<b>${L[1][1]}。</b>`);
      if (b.dataset.v === 'show') { revealed[i] = true; okBox(msg, verdict + bi(it.en, it.zh), 'info'); return; }
      if ((b.dataset.v === '1') === it.ans) {
        okBox(msg, '✓ ' + verdict + bi(it.en, it.zh));
        if (!revealed[i]) solved[i] = true;
        if (progId && solved.every(Boolean)) { Progress.mark(progId); okBox(msg, msg.innerHTML + bi('<br><b>All items solved. ✓</b>', '<br><b>全部答对。✓</b>')); }
      } else okBox(msg, bi('✗ Not quite. Look again carefully.', '✗ 不对。再仔细看看。'), 'bad');
    }));
  });
}
function orderGame(box, steps, progId) {
  const n = steps.length;
  let order;
  do order = [...Array(n).keys()].sort(() => Math.random() - .5); while (order.every((x, i) => x === i));
  let placed = [], revealed = false;
  box.innerHTML = `<div class="row"><div class="col"><h4>${bil('Steps (shuffled)', '步骤（已打乱）')}</h4><div class="ord tray"></div></div>
    <div class="col"><h4>${bil('Your proof', '你的证明')}</h4><div class="ordslots"><div class="ord slots"></div></div></div></div>
    <div class="toolbar"><button class="btn primary chk">${bi('Check', '检查')}</button><button class="btn ghost rst">${bi('Reset', '重置')}</button>
    <button class="btn ghost shw">${bi('Show answer', '看答案')}</button></div><div class="msg"></div>`;
  const tray = box.querySelector('.tray'), slots = box.querySelector('.slots'), msg = box.querySelector('.msg');
  function render(marks) {
    tray.innerHTML = ''; slots.innerHTML = '';
    order.filter(i => !placed.includes(i)).forEach(i => {
      const c = document.createElement('div'); c.className = 'chip'; c.innerHTML = steps[i];
      c.addEventListener('click', () => { placed.push(i); clearBox(msg); render(); });
      tray.appendChild(c);
    });
    placed.forEach((i, k) => {
      const c = document.createElement('div');
      c.className = 'chip' + (marks ? (marks[k] ? ' ok' : ' no') : '');
      c.innerHTML = `<span class="k">${k + 1}.</span> ${steps[i]}`;
      c.addEventListener('click', () => { placed = placed.filter(x => x !== i); clearBox(msg); render(); });
      slots.appendChild(c);
    });
  }
  render();
  box.querySelector('.chk').addEventListener('click', () => {
    if (placed.length < n) { okBox(msg, bi('Place all the steps first.', '请先把所有步骤都放好。'), 'warn'); return; }
    const marks = placed.map((x, k) => x === k);
    render(marks);
    if (marks.every(Boolean)) { okBox(msg, bi('✓ Correct order.', '✓ 顺序正确。')); if (!revealed) Progress.mark(progId); }
    else okBox(msg, bi(`${marks.filter(Boolean).length} / ${n} in the right position (green).`, `${marks.filter(Boolean).length} / ${n} 个位置正确（绿色）。`), 'bad');
  });
  box.querySelector('.rst').addEventListener('click', () => { placed = []; clearBox(msg); render(); });
  box.querySelector('.shw').addEventListener('click', () => { revealed = true; placed = [...Array(n).keys()]; render(placed.map(() => true)); okBox(msg, bi('This is the correct order.', '这是正确的顺序。'), 'info'); });
}
function choices(box, opts, msgBox, onRight) {
  opts.forEach(o => {
    const b = document.createElement('button');
    b.className = 'btn choice';
    b.innerHTML = bi(o.en, o.zh);
    b.addEventListener('click', () => {
      box.querySelectorAll('.choice').forEach(x => x.classList.remove('right', 'wrongc'));
      b.classList.add(o.ok ? 'right' : 'wrongc');
      if (o.ok) { okBox(msgBox, '✓ ' + bi(o.fen, o.fzh)); onRight && onRight(); }
      else okBox(msgBox, '✗ ' + bi(o.fen, o.fzh), 'bad');
    });
    box.appendChild(b);
  });
  return { reveal() { box.querySelectorAll('.choice').forEach((b, i) => opts[i].ok && b.classList.add('right')); } };
}
function pickBar(box, items, onPick, init = 0) {
  items.forEach((it, i) => {
    const b = document.createElement('button');
    b.className = 'btn small' + (i === init ? ' sel' : '');
    b.innerHTML = it.html || bil(it.en, it.zh);
    b.addEventListener('click', () => { box.querySelectorAll('button').forEach((x, j) => x.classList.toggle('sel', j === i)); onPick(i); });
    box.appendChild(b);
  });
}

/* ================= §1 the liar ================= */
(function liar() {
  const PRE = [
    { en: 'Liar', zh: '说谎者', claims: { L: { to: 'L', neg: true } }, pos: { L: [230, 120] },
      say: { L: ['“L is false.”', '“L 是假的。”'] },
      end: ['No fixed point: revision oscillates 1, 0, 1, 0, … forever. The liar has no consistent truth value.', '没有不动点：修正过程永远在 1、0、1、0…… 之间振荡。说谎者句没有自洽的真值。'] },
    { en: 'Truth-teller', zh: '诚实者', claims: { T: { to: 'T', neg: false } }, pos: { T: [230, 120] },
      say: { T: ['“T is true.”', '“T 是真的。”'] },
      end: ['Two fixed points: T = 1 and T = 0 are both stable. Not contradictory, just ungrounded: nothing decides which.', '两个不动点：T = 1 和 T = 0 都是稳定的。不矛盾，只是“无根”：没有任何东西决定取哪一个。'] },
    { en: 'Jourdain’s card', zh: '茹尔丹卡片', claims: { A: { to: 'B', neg: false }, B: { to: 'A', neg: true } }, pos: { A: [120, 120], B: [340, 120] },
      say: { A: ['“B is true.”', '“B 是真的。”'], B: ['“A is false.”', '“A 是假的。”'] },
      end: ['No fixed point, period 4. No sentence refers to itself, yet the loop A → B → A is a liar in disguise.', '没有不动点，周期为 4。没有哪个句子直接谈论自己，但 A → B → A 这个回路就是乔装的说谎者。'] },
    { en: 'Two liars', zh: '两个说谎者', claims: { A: { to: 'B', neg: true }, B: { to: 'A', neg: true } }, pos: { A: [120, 120], B: [340, 120] },
      say: { A: ['“B is false.”', '“B 是假的。”'], B: ['“A is false.”', '“A 是假的。”'] },
      end: ['Two fixed points (1,0) and (0,1). Starting from (1,1) or (0,0) revision oscillates, but consistent assignments exist.', '两个不动点 (1,0) 与 (0,1)。从 (1,1) 或 (0,0) 出发会振荡，但自洽的赋值是存在的。'] },
  ];
  let P, v, hist, timer = null;
  const svg = $('liarSvg');
  function load(i) {
    P = PRE[i];
    v = {}; Object.keys(P.claims).forEach(k => { v[k] = 1; });
    hist = [{ ...v }];
    stop();
    draw();
    fixTable();
    clearBox($('liarMsg'));
  }
  function stop() { if (timer) { clearInterval(timer); timer = null; } }
  function draw() {
    svg.innerHTML = '';
    const ks = Object.keys(P.claims);
    ks.forEach(k => {
      const c = P.claims[k], [x, y] = P.pos[k];
      if (c.to === k) {
        el('path', { d: `M ${x - 20} ${y - 38} C ${x - 70} ${y - 120}, ${x + 70} ${y - 120}, ${x + 20} ${y - 38}`, fill: 'none', stroke: c.neg ? '#e03131' : '#2f9e44', 'stroke-width': 2.5, 'marker-end': c.neg ? 'url(#arr13r)' : 'url(#arr13)' }, svg);
        svgBi(svg, { x, y: y - 98, 'text-anchor': 'middle', 'font-size': 12, 'font-weight': 700, fill: c.neg ? '#e03131' : '#2f9e44' }, c.neg ? 'says: false' : 'says: true', c.neg ? '断言：假' : '断言：真');
      } else {
        const [x2, y2] = P.pos[c.to];
        const up = x < x2 ? -1 : 1;
        el('path', { d: `M ${x + (x2 > x ? 40 : -40)} ${y + up * 12} Q ${(x + x2) / 2} ${y + up * 70} ${x2 + (x2 > x ? -42 : 42)} ${y2 + up * 12}`, fill: 'none', stroke: c.neg ? '#e03131' : '#2f9e44', 'stroke-width': 2.5, 'marker-end': c.neg ? 'url(#arr13r)' : 'url(#arr13)' }, svg);
        svgBi(svg, { x: (x + x2) / 2, y: y + up * 48 + (up < 0 ? 0 : 8), 'text-anchor': 'middle', 'font-size': 12, 'font-weight': 700, fill: c.neg ? '#e03131' : '#2f9e44' }, c.neg ? `${k} says: ${c.to} false` : `${k} says: ${c.to} true`, c.neg ? `${k} 断言 ${c.to} 假` : `${k} 断言 ${c.to} 真`);
      }
    });
    ks.forEach(k => {
      const [x, y] = P.pos[k];
      const g = el('g', { style: 'cursor:pointer' }, svg);
      el('circle', { cx: x, cy: y, r: 40, fill: v[k] ? '#d3f9d8' : '#ffe3e3', stroke: v[k] ? '#2f9e44' : '#e03131', 'stroke-width': 3, class: 'pop' }, g);
      svgT(g, { x, y: y - 4, 'text-anchor': 'middle', 'font-size': 22, 'font-weight': 800 }, k);
      svgT(g, { x, y: y + 20, 'text-anchor': 'middle', 'font-size': 15, 'font-weight': 800, fill: v[k] ? '#2f9e44' : '#e03131' }, v[k] ? '1' : '0');
      svgBi2(g, { x, y: y + 62, 'text-anchor': 'middle', 'font-size': 13 }, P.say[k][0], P.say[k][1], 17);
      g.addEventListener('click', () => { stop(); v[k] = 1 - v[k]; hist = [{ ...v }]; draw(); clearBox($('liarMsg')); });
    });
    // history strip
    let h = '';
    ks.forEach(k => {
      h += `<div class="hrow"><b>${k}</b>${hist.map(s => `<span class="c c${s[k]}">${s[k]}</span>`).join('')}</div>`;
    });
    $('liarHist').innerHTML = `<div class="muted" style="font-family:var(--sans)">${bil('revision history', '修正历史')} →</div>` + h;
    fixTable();
  }
  function fixTable() {
    const fps = fixedPoints(P.claims), ks = Object.keys(P.claims);
    let h = `<table class="fp"><tr>${ks.map(k => `<th>${k}</th>`).join('')}<th>${bil('fixed?', '不动点？')}</th></tr>`;
    fps.forEach(r => {
      const cur = ks.every(k => r.v[k] === v[k]);
      h += `<tr class="${r.fixed ? 'fix' : ''}" style="${cur ? 'outline:2px solid var(--accent)' : ''}">${ks.map(k => `<td>${r.v[k]}</td>`).join('')}<td>${r.fixed ? '✓' : '✗'}</td></tr>`;
    });
    $('liarFix').innerHTML = h + '</table>';
  }
  function step() {
    v = revise(P.claims, v);
    hist.push({ ...v });
    if (hist.length > 18) hist.shift();
    draw();
    const fixed = fixedPoints(P.claims).some(r => r.fixed && Object.keys(P.claims).every(k => r.v[k] === v[k]));
    okBox($('liarMsg'), bi(P.end[0], P.end[1]) + (fixed ? bi('<br>The current assignment is stable.', '<br>当前赋值是稳定的。') : bi('<br>The current assignment is not stable.', '<br>当前赋值不稳定。')), fixed ? 'ok' : 'warn');
  }
  pickBar($('liarPick'), PRE, load);
  $('liarStep').addEventListener('click', () => { stop(); step(); });
  $('liarAuto').addEventListener('click', () => { if (timer) { stop(); return; } let n = 0; timer = setInterval(() => { step(); if (++n >= 12) stop(); }, 650); });
  $('liarReset').addEventListener('click', () => load(PRE.indexOf(P)));
  load(0);
  setTimeout(() => { step(); step(); }, 600);
})();

/* ================= §2 diagonal family tree ================= */
(function family() {
  const N = [
    { id: 'liar', x: 90, y: 50, en: 'Liar', zh: '说谎者', yr: '~400 BCE',
      rows: ['predicates P', '谓词 P'], cols: ['sentence names', '句子的名字'], entry: ['P(name of s)', 'P(s 的名字)'], twist: ['“… is false”', '“……是假的”'],
      out: ['The liar “this sentence is false”: a language that can name its own sentences and contains its own truth predicate, obeying every T-schema instance under classical logic, is inconsistent.', '说谎者句“本句为假”：一个既能给自己的句子命名、又含有自身真谓词的语言，若在经典逻辑下满足全部 T 模式实例，就是不一致的。'],
      B: ['T', 'F'], kind: 'contra', R: 'P', C: 's', D: 'L' },
    { id: 'cantor', x: 300, y: 50, en: 'Cantor', zh: '康托尔', yr: '1891',
      rows: ['subsets f(a)', '子集 f(a)'], cols: ['elements b', '元素 b'], entry: ['b ∈ f(a)?', 'b ∈ f(a)?'], twist: ['1 − x', '1 − x'],
      out: ['D = {a : a ∉ f(a)} differs from every f(a) at a. No f : A → P(A) is onto, so |A| < |P(A)|.', 'D = {a : a ∉ f(a)} 在 a 处与每个 f(a) 都不同。不存在满射 f : A → P(A)，所以 |A| < |P(A)|。'],
      B: ['1', '0'], kind: 'contra', R: 'f', C: 'b', D: 'D' },
    { id: 'russell', x: 430, y: 140, en: 'Russell', zh: '罗素', yr: '1901',
      rows: ['sets x', '集合 x'], cols: ['sets y', '集合 y'], entry: ['y ∈ x?', 'y ∈ x?'], twist: ['∈ ↦ ∉', '∈ ↦ ∉'],
      out: ['R = {x : x ∉ x} would be a row: R ∈ R ↔ R ∉ R. So R is not a set: unrestricted comprehension fails (Lesson 6).', 'R = {x : x ∉ x} 若是一行，则 R ∈ R ↔ R ∉ R。所以 R 不是集合：无限制的概括原则不成立（第 6 课）。'],
      B: ['∈', '∉'], kind: 'contra', R: 'x', C: 'y', D: 'R' },
    { id: 'godel', x: 190, y: 140, en: 'Gödel', zh: '哥德尔', yr: '1931',
      rows: ['formulas φₙ(x)', '公式 φₙ(x)'], cols: ['codes ⌜φₘ⌝', '编码 ⌜φₘ⌝'], entry: ['T ⊢ φₙ(⌜φₘ⌝)?', 'T ⊢ φₙ(⌜φₘ⌝)?'], twist: ['¬Prov', '¬Prov'],
      out: ['The twisted row is a formula, hence in the list: no contradiction but a fixed point G ↔ ¬Prov(⌜G⌝). Consistent T cannot prove G: incompleteness.', '扭转后的一行仍是公式，所以就在清单里：不产生矛盾，而是不动点 G ↔ ¬Prov(⌜G⌝)。一致的 T 证不出 G：不完全性。'],
      B: ['⊢', '⊬'], kind: 'fixed', R: 'φ', C: 'm', D: 'D' },
    { id: 'tarski', x: 100, y: 235, en: 'Tarski', zh: '塔斯基', yr: '1933',
      rows: ['formulas φₙ(x)', '公式 φₙ(x)'], cols: ['codes ⌜φₘ⌝', '编码 ⌜φₘ⌝'], entry: ['ℕ ⊨ φₙ(⌜φₘ⌝)?', 'ℕ ⊨ φₙ(⌜φₘ⌝)?'], twist: ['¬True', '¬True'],
      out: ['If True were definable, ¬True(sub(x,x)) would be a row and its diagonal entry would equal its own negation. So truth is not definable.', '若 True 可定义，¬True(sub(x,x)) 就是某一行，它的对角项将等于自身的否定。所以真不可定义。'],
      B: ['T', 'F'], kind: 'contra', R: 'φ', C: 'm', D: 'L' },
    { id: 'turing', x: 300, y: 235, en: 'Turing', zh: '图灵', yr: '1936',
      rows: ['programs e', '程序 e'], cols: ['inputs n', '输入 n'], entry: ['φₑ(n) halts?', 'φₑ(n) 停机？'], twist: ['halt ↔ loop', '停机 ↔ 不停'],
      out: ['If halting were decidable, the twisted program D would be a row; D(D) halts iff it does not. So the halting problem is undecidable (Lesson 11).', '若停机可判定，扭转后的程序 D 就是某一行；D(D) 停机当且仅当它不停机。所以停机问题不可判定（第 11 课）。'],
      B: ['↓', '↑'], kind: 'contra', R: 'P', C: 'n', D: 'D' },
    { id: 'lawvere', x: 260, y: 325, en: 'Lawvere', zh: '劳维尔', yr: '1969',
      rows: ['a ∈ A, row g(a)', 'a ∈ A，行 g(a)'], cols: ['a′ ∈ A', 'a′ ∈ A'], entry: ['g(a)(a′) ∈ B', 'g(a)(a′) ∈ B'], twist: ['any f : B → B', '任意 f : B → B'],
      out: ['If g : A → B^A is onto, h(a) = f(g(a)(a)) is some row a₀, and h(a₀) = f(h(a₀)) is a fixed point of f. Every node above is an instance.', '若 g : A → B^A 是满射，则 h(a) = f(g(a)(a)) 是某一行 a₀，于是 h(a₀) = f(h(a₀)) 是 f 的不动点。上面每个节点都是它的实例。'],
      B: ['b', 'b′'], kind: 'fixed', R: 'g', C: 'a', D: 'h' },
  ];
  const E = [['liar', 'godel'], ['liar', 'tarski'], ['cantor', 'russell'], ['cantor', 'godel'], ['cantor', 'turing'], ['godel', 'tarski'], ['godel', 'turing']];
  const svg = $('famSvg');
  const byId = Object.fromEntries(N.map(n => [n.id, n]));
  const W = 128, H = 48;
  E.forEach(([a, b]) => {
    const A = byId[a], B = byId[b];
    el('line', { x1: A.x, y1: A.y + H / 2, x2: B.x, y2: B.y - H / 2, stroke: '#9aa0aa', 'stroke-width': 2, 'marker-end': 'url(#arr13)' }, svg);
  });
  N.filter(n => n.id !== 'lawvere').forEach(n => el('line', { x1: byId.lawvere.x, y1: byId.lawvere.y - H / 2, x2: n.x, y2: n.y + H / 2, stroke: '#ae3ec9', 'stroke-width': 1.2, 'stroke-dasharray': '3 5', opacity: .55 }, svg));
  const boxes = {};
  N.forEach(n => {
    const g = el('g', { style: 'cursor:pointer' }, svg);
    const r = el('rect', { x: n.x - W / 2, y: n.y - H / 2, width: W, height: H, rx: 12, fill: n.id === 'lawvere' ? '#f8e7fc' : '#fff', stroke: n.kind === 'fixed' ? '#f08c00' : '#1f2430', 'stroke-width': 2 }, g);
    svgT(g, { x: n.x, y: n.y - 5, 'text-anchor': 'middle', 'font-size': 13, 'font-weight': 800 }, `${n.en} ${n.yr}`);
    svgT(g, { x: n.x, y: n.y + 14, 'text-anchor': 'middle', 'font-size': 12, fill: '#4a5568', class: 'zh', style: 'font-size:12px' }, n.zh);
    boxes[n.id] = r;
    g.addEventListener('click', () => show(n));
  });
  svgBi(svg, { x: 10, y: 372, 'font-size': 11, fill: '#6b7280' }, 'orange frame = fixed point, black = contradiction', '橙框 = 不动点，黑框 = 矛盾');
  let tok = 0;
  async function show(n) {
    Object.values(boxes).forEach(r => r.setAttribute('stroke-width', 2));
    boxes[n.id].setAttribute('stroke-width', 5);
    $('famCard').innerHTML = `<h3>${bil(n.en, n.zh)} <span class="muted" style="font-size:13px">${n.yr}</span></h3>
      <div class="famgrid"><b>${bil('rows', '行')}</b><span>${bil(n.rows[0], n.rows[1])}</span><b>${bil('columns', '列')}</b><span>${bl(n.cols[0], n.cols[1])}</span>
      <b>${bil('entry', '表项')}</b><span class="m">${bl(n.entry[0], n.entry[1])}</span><b>${bil('twist f', '扭转 f')}</b><span class="m">${bl(n.twist[0], n.twist[1])}</span></div>
      <div style="font-size:14px">${bi(n.out[0], n.out[1])}</div>`;
    const my = ++tok;
    const g = $('famGrid');
    g.innerHTML = '';
    const K = 4, CW = 46, CH = 30, x0 = 70, y0 = 34;
    const vals = Array.from({ length: K }, () => Array.from({ length: K }, () => Math.random() < .5 ? 0 : 1));
    for (let c = 0; c < K; c++) svgT(g, { x: x0 + c * CW + CW / 2, y: y0 - 10, 'text-anchor': 'middle', 'font-size': 12, fill: '#3b5bdb', 'font-weight': 700 }, n.C + subs(c));
    const cells = [];
    for (let r = 0; r < K; r++) {
      svgT(g, { x: x0 - 10, y: y0 + r * CH + 20, 'text-anchor': 'end', 'font-size': 12, 'font-weight': 700 }, n.R + subs(r));
      cells.push([]);
      for (let c = 0; c < K; c++) {
        const rect = el('rect', { x: x0 + c * CW + 2, y: y0 + r * CH + 2, width: CW - 4, height: CH - 4, rx: 5, fill: '#f1efe7' }, g);
        svgT(g, { x: x0 + c * CW + CW / 2, y: y0 + r * CH + 20, 'text-anchor': 'middle', 'font-size': 13 }, n.B[vals[r][c]]);
        cells[r].push(rect);
      }
    }
    for (let k = 0; k < K; k++) {
      await sleep(260); if (my !== tok) return;
      cells[k][k].setAttribute('fill', '#f8e7fc'); cells[k][k].setAttribute('stroke', '#ae3ec9'); cells[k][k].setAttribute('stroke-width', 2);
    }
    const yD = y0 + K * CH + 16;
    svgT(g, { x: x0 - 10, y: yD + 20, 'text-anchor': 'end', 'font-size': 12, 'font-weight': 800, fill: '#ae3ec9' }, n.D);
    for (let c = 0; c < K; c++) {
      await sleep(220); if (my !== tok) return;
      el('rect', { x: x0 + c * CW + 2, y: yD + 2, width: CW - 4, height: CH - 4, rx: 5, fill: 'rgba(174,62,201,.18)', stroke: '#ae3ec9', class: 'pop' }, g);
      svgT(g, { x: x0 + c * CW + CW / 2, y: yD + 20, 'text-anchor': 'middle', 'font-size': 13, 'font-weight': 800, fill: '#ae3ec9' }, n.B[1 - vals[c][c]]);
    }
    await sleep(300); if (my !== tok) return;
    if (n.kind === 'contra') {
      svgBi2(g, { x: x0 + K * CW + 10, y: yD + 12, 'font-size': 11, 'font-weight': 700, fill: '#e03131' }, '≠ every row', '与每行都不同', 14);
      svgBi2(g, { x: 10, y: yD + CH + 26, 'font-size': 12, 'font-weight': 700, fill: '#e03131' }, `${n.D} cannot be a row: contradiction`, `${n.D} 不能是一行：矛盾`, 16);
    } else {
      svgBi2(g, { x: x0 + K * CW + 10, y: yD + 12, 'font-size': 11, 'font-weight': 700, fill: '#f08c00' }, `${n.D} is a row!`, `${n.D} 就是一行！`, 14);
      svgBi2(g, { x: 10, y: yD + CH + 26, 'font-size': 12, 'font-weight': 700, fill: '#f08c00' }, `at (${n.D}, ${n.D}): a fixed point of f`, `在 (${n.D}, ${n.D}) 处：f 的不动点`, 16);
    }
  }
  show(byId.tarski);
})();

/* ================= §3 Tarski's theorem ================= */
(function tarski() {
  stepper('tkSteps', 'tkNext', 'tkAll');
  const S = ['0 = 0', '0 = S0', '∀x (0+x = x)', '∀x ∃y (x = y+y)', 'Con(PA)'];
  const TRUTH = [1, 0, 1, 0, 1];
  const C = [
    { f: 'Prov_PA(x)', en: 'Prov_PA(x): provable in PA', zh: 'Prov_PA(x)：在 PA 中可证', v: [1, 0, 1, 0, 0],
      liar: ['L_C is the Gödel sentence of PA. PA ⊬ L_C, so C(⌜L_C⌝) is false and L_C is true.', 'L_C 就是 PA 的哥德尔语句。PA ⊬ L_C，所以 C(⌜L_C⌝) 为假，而 L_C 为真。'], lv: [1, 0],
      sum: ['Provability is definable (Σ₁), but it is not truth: Con(PA) and G are true and unprovable.', '可证性是可定义的（Σ₁），但它不是真：Con(PA) 和 G 都是真的但不可证。'] },
    { f: 'True_Σ₁(x)', en: 'True_Σ₁(x): a true Σ₁ sentence', zh: 'True_Σ₁(x)：真的 Σ₁ 语句', v: [1, 0, 0, 0, 0],
      liar: ['L_C ↔ ¬True_Σ₁(⌜L_C⌝) is not itself Σ₁, so C(⌜L_C⌝) is false, hence L_C is true.', 'L_C ↔ ¬True_Σ₁(⌜L_C⌝) 本身不是 Σ₁ 语句，所以 C(⌜L_C⌝) 为假，从而 L_C 为真。'], lv: [1, 0],
      sum: ['Correct on Σ₁ sentences, blind to everything above: the Π₁ truths ∀x(0+x=x) and Con(PA) are missed.', '在 Σ₁ 语句上都对，对更高的层级一概看不见：Π₁ 真理 ∀x(0+x=x) 和 Con(PA) 都漏掉了。'] },
    { f: 'True_Σ₇(x)', en: 'True_Σ₇(x): a true Σ₇ sentence', zh: 'True_Σ₇(x)：真的 Σ₇ 语句', v: [1, 0, 1, 0, 1],
      liar: ['L_C is Π₇ but not Σ₇, so C(⌜L_C⌝) is false, hence L_C is true.', 'L_C 是 Π₇ 而非 Σ₇ 的，所以 C(⌜L_C⌝) 为假，从而 L_C 为真。'], lv: [1, 0],
      sum: ['Perfect on every test sentence of low complexity, yet it fails at its own liar, which sits one level higher.', '在所有低复杂度的测试语句上全对，却栽在它自己的说谎者上，那个句子恰好高出一层。'] },
    { f: 'EvenLen(x)', en: 'EvenLen(x): an even number of symbols', zh: 'EvenLen(x)：符号个数为偶数', v: [0, 1, 0, 0, null],
      liar: ['If C(⌜L_C⌝) holds then L_C is false; if not, L_C is true. Either way C is wrong about L_C.', '若 C(⌜L_C⌝) 成立，则 L_C 为假；若不成立，则 L_C 为真。无论哪种，C 对 L_C 的判断都是错的。'], lv: null,
      sum: ['A silly candidate fails almost everywhere. The point: even the best candidates fail at L_C.', '一个荒唐的候选几乎处处出错。重点是：再好的候选也会在 L_C 上出错。'] },
  ];
  let tok = 0;
  async function run(i) {
    const my = ++tok, c = C[i];
    const yn = x => x === null ? '<td>—</td>' : `<td class="${x ? 'y' : 'n'}">${x ? '1' : '0'}</td>`;
    let h = `<div class="m" style="margin-bottom:6px">C(x) = ${c.f} &nbsp;⟹&nbsp; ${bil('diagonal lemma', '对角线引理')}: <b>L_C ↔ ¬C(⌜L_C⌝)</b></div>
      <table class="cand"><tr><th>${bil('sentence φ', '语句 φ')}</th><th>${bil('true in ℕ?', 'ℕ 中为真？')}</th><th>C(⌜φ⌝)?</th><th>${bil('agree?', '一致？')}</th></tr>`;
    S.forEach((s, k) => {
      const ok = c.v[k] === null ? null : c.v[k] === TRUTH[k];
      h += `<tr class="hidden${ok === false ? ' miss' : ''}">${'<td>' + s + '</td>'}${yn(TRUTH[k])}${yn(c.v[k])}<td>${ok === null ? '?' : ok ? '✓' : '✗'}</td></tr>`;
    });
    h += `<tr class="hidden miss liar"><td><b>L_C</b></td>${c.lv ? yn(c.lv[0]) + yn(c.lv[1]) : '<td>¬C(⌜L_C⌝)</td><td>C(⌜L_C⌝)</td>'}<td>✗</td></tr></table>`;
    $('candStage').innerHTML = h;
    clearBox($('candMsg'));
    const rows = [...$('candStage').querySelectorAll('tr.hidden')];
    for (const r of rows) { await sleep(320); if (my !== tok) return; r.classList.remove('hidden'); }
    okBox($('candMsg'), bi(`<b>At L_C:</b> ${c.liar[0]} ${c.sum[0]}`, `<b>在 L_C 处：</b>${c.liar[1]}${c.sum[1]}`), 'bad');
  }
  pickBar($('candPick'), C.map(c => ({ html: `<span class="m">${c.f}</span>`, en: c.en, zh: c.zh })), run);
  run(0);
})();

/* ================= §4 arithmetical hierarchy ================= */
(function hierarchy() {
  const svg = $('ahSvg');
  const LY = n => 420 - n * 86;
  const spots = { D0: [320, LY(0)], S1: [140, LY(1)], P1: [500, LY(1)], D1: [320, LY(1)], S2: [140, LY(2)], P2: [500, LY(2)], D2: [320, LY(2)], S3: [140, LY(3)], P3: [500, LY(3)], D3: [320, LY(3)], S4: [140, LY(4)], P4: [500, LY(4)], TOP: [250, 22] };
  const SETS = [
    { nm: 'Primes', zh: '素数集', at: 'D0', en: 'n is prime ⇔ n > 1 ∧ ∀d < n (d ∣ n → d = 1): only bounded quantifiers.', zhx: 'n 是素数 ⇔ n > 1 ∧ ∀d < n (d ∣ n → d = 1)：只用到有界量词。' },
    { nm: 'Proof_PA', zh: 'Proof_PA 关系', at: 'D1', en: '“x codes a PA-proof of y” is decidable (Δ₁; even Δ₀ with suitable coding).', zhx: '“x 编码 y 的一个 PA-证明”是可判定的（Δ₁；适当编码下甚至是 Δ₀）。' },
    { nm: 'Thm_PA', zh: 'PA 的定理集', at: 'S1', en: '∃x Proof_PA(x, y): Σ₁, indeed Σ₁-complete. Provability lives low on the ladder.', zhx: '∃x Proof_PA(x, y)：Σ₁，而且是 Σ₁-完全的。可证性位于梯子的低处。' },
    { nm: 'K', zh: '停机集 K', at: 'S1', en: 'K = {e : φₑ(e)↓} = {e : ∃s (e halts on e within s steps)}: Σ₁-complete.', zhx: 'K = {e : φₑ(e)↓} = {e : ∃s（e 在 s 步内对输入 e 停机）}：Σ₁-完全。' },
    { nm: 'K̄', zh: 'K 的补集', at: 'P1', en: '∀s (e has not halted on e by step s): Π₁-complete, not c.e.', zhx: '∀s（到第 s 步为止 e 在 e 上尚未停机）：Π₁-完全，不是递归可枚举的。' },
    { nm: 'Con(PA)', zh: 'Con(PA)', at: 'P1', en: 'The sentence ∀x ¬Proof_PA(x, ⌜0=1⌝) is Π₁, like Gödel’s G.', zhx: '语句 ∀x ¬Proof_PA(x, ⌜0=1⌝) 是 Π₁ 的，和哥德尔的 G 一样。' },
    { nm: 'Fin', zh: 'Fin', at: 'S2', en: 'Fin = {e : Wₑ finite} = ∃N ∀n > N (n ∉ Wₑ): Σ₂-complete.', zhx: 'Fin = {e : Wₑ 有限} = ∃N ∀n > N (n ∉ Wₑ)：Σ₂-完全。' },
    { nm: 'Tot', zh: 'Tot', at: 'P2', en: 'Tot = {e : φₑ total} = ∀n ∃s (φₑ(n) halts within s steps): Π₂-complete.', zhx: 'Tot = {e : φₑ 是全函数} = ∀n ∃s（φₑ(n) 在 s 步内停机）：Π₂-完全。' },
    { nm: 'Cof', zh: 'Cof', at: 'S3', en: 'Cof = {e : Wₑ cofinite} = ∃N ∀n > N ∃s (n ∈ Wₑ,ₛ): Σ₃-complete.', zhx: 'Cof = {e : Wₑ 余有限} = ∃N ∀n > N ∃s (n ∈ Wₑ,ₛ)：Σ₃-完全。' },
    { nm: 'Th(ℕ)', zh: 'Th(ℕ)', at: 'TOP', en: 'Th(ℕ) is on no rung: for each n it is harder than every Σₙ set. Not arithmetical (Tarski).', zhx: 'Th(ℕ) 不在任何一层：对每个 n，它都比所有 Σₙ 集更难。它不是算术集（塔斯基）。' },
  ];
  const used = {};
  let layer;
  function frame() {
    svg.innerHTML = '';
    const box = (key, lab, sub, col) => {
      const [x, y] = spots[key];
      const w = key.startsWith('D') && key !== 'D0' ? 130 : 190;
      el('rect', { x: x - w / 2, y: y - 30, width: w, height: 62, rx: 12, fill: '#fff', stroke: col, 'stroke-width': 2 }, svg);
      svgT(svg, { x: x - w / 2 + 8, y: y - 14, 'font-size': 14, 'font-weight': 800, fill: col }, lab);
      svgT(svg, { x: x + w / 2 - 8, y: y - 14, 'text-anchor': 'end', 'font-size': 11, fill: '#6b7280' }, sub);
    };
    for (let n = 1; n <= 4; n++) {
      const [sx, sy] = spots['S' + n], [px] = spots['P' + n];
      const below = n === 1 ? spots.D0 : spots['D' + (n - 1)];
      [sx, px].forEach(x => el('line', { x1: x, y1: sy + 32, x2: below[0], y2: below[1] - 30, stroke: '#d8d3c4', 'stroke-width': 2 }, svg));
      if (n <= 3) [sx, px].forEach(x => el('line', { x1: x + (x < 320 ? 95 : -95), y1: sy, x2: 320 + (x < 320 ? -65 : 65), y2: spots['D' + n][1], stroke: '#d8d3c4', 'stroke-width': 2, 'stroke-dasharray': '4 4' }, svg));
    }
    box('D0', 'Δ₀', 'bounded · 有界', '#6b7280');
    for (let n = 1; n <= 4; n++) {
      box('S' + n, 'Σ' + subs(n), n === 1 ? '∃ Δ₀ · c.e.' : ['', '', '∃∀ Δ₀', '∃∀∃ Δ₀', '∃∀∃∀ Δ₀'][n], '#3b5bdb');
      box('P' + n, 'Π' + subs(n), ['', '∀ Δ₀', '∀∃ Δ₀', '∀∃∀ Δ₀', '∀∃∀∃ Δ₀'][n], '#e03131');
      if (n <= 3) box('D' + n, 'Δ' + subs(n), n === 1 ? 'decidable' : '', '#2f9e44');
    }
    svgT(svg, { x: 320, y: LY(4) - 44, 'text-anchor': 'middle', 'font-size': 18, fill: '#aaa' }, '⋮');
    // cloud
    const cl = el('g', {}, svg);
    el('ellipse', { cx: 320, cy: 28, rx: 170, ry: 24, fill: '#f8e7fc', stroke: '#ae3ec9', 'stroke-dasharray': '5 4' }, cl);
    svgBi(cl, { x: 10, y: 14, 'text-anchor': 'start', 'font-size': 11, fill: '#ae3ec9', 'font-weight': 700 }, 'above every rung', '高于每一层');
    layer = el('g', {}, svg);
    for (const k in used) delete used[k];
    $('ahChips').querySelectorAll('.chip').forEach(c => c.classList.remove('used'));
    okBox($('ahMsg'), bi('Click a set above to place it. Σ₁ = c.e. sets, Δ₁ = decidable sets (Post’s theorem: Σₙ₊₁ = c.e. relative to the n-th jump).', '点击上方的集合把它放上去。Σ₁ = 递归可枚举集，Δ₁ = 可判定集（波斯特定理：Σₙ₊₁ = 相对于第 n 次图灵跳跃递归可枚举）。'), 'info');
  }
  function place(s, chip, quiet) {
    if (chip) chip.classList.add('used');
    if (!quiet) okBox($('ahMsg'), `<b>${bil(s.nm, s.zh)}</b> → <b>${s.at === 'TOP' ? bil('no level', '无层级') : s.at.replace(/(\d)/, d => subs(d)).replace('S', 'Σ').replace('P', 'Π').replace('D', 'Δ')}</b><br>` + bi(s.en, s.zhx), s.at === 'TOP' ? 'warn' : 'info');
    if (used[s.nm]) return;
    const cnt = Object.values(used).filter(a => a === s.at).length;
    used[s.nm] = s.at;
    const [x, y] = spots[s.at];
    const tx = s.at === 'TOP' ? x + cnt * 70 : (s.at[0] === 'D' && s.at !== 'D0') ? x + (cnt % 2 ? 30 : -30) : x + (cnt % 3 - 1) * 58, ty = s.at === 'TOP' ? y + 8 : y + 14;
    const g = el('g', {}, layer);
    el('rect', { x: -27, y: -11, width: 54, height: 22, rx: 11, fill: s.at === 'TOP' ? '#ae3ec9' : '#1f2430' }, g);
    svgT(g, { x: 0, y: 4, 'text-anchor': 'middle', 'font-size': s.nm.length > 6 ? 9.5 : 11, fill: '#fff', 'font-weight': 700 }, s.nm);
    g.style.transition = 'transform .8s cubic-bezier(.2,.9,.3,1)';
    g.style.transform = `translate(320px, 470px)`;
    requestAnimationFrame(() => requestAnimationFrame(() => { g.style.transform = `translate(${tx}px, ${ty}px)`; }));
  }
  SETS.forEach(s => {
    const c = document.createElement('div');
    c.className = 'chip';
    c.innerHTML = s.nm === s.zh ? `<span class="m">${s.nm}</span>` : `<span class="m">${s.nm}</span> ${bil('', s.zh)}`;
    c.addEventListener('click', () => place(s, c));
    $('ahChips').appendChild(c);
  });
  let tok = 0;
  async function climb() {
    const my = ++tok;
    const g = el('g', {}, svg);
    const b = el('ellipse', { rx: 44, ry: 15, fill: '#fff3bf', stroke: '#f08c00', 'stroke-width': 2 }, g);
    const t = svgT(g, { 'text-anchor': 'middle', y: 4, 'font-size': 11, 'font-weight': 800, fill: '#b35c00' }, '');
    void b;
    g.style.transition = 'transform .7s ease';
    for (let n = 1; n <= 4; n++) {
      const [x, y] = spots['S' + n];
      t.textContent = 'True_Σ' + subs(n);
      g.style.transform = `translate(${x}px, ${y + 46}px)`;
      okBox($('ahMsg'), bi(`<b>True_Σ${subs(n)}</b> is a Σ${subs(n)} formula that correctly decides truth for all Σ${subs(n)} sentences. Truth up to level ${n} is definable, at level ${n}.`, `<b>True_Σ${subs(n)}</b> 是一个 Σ${subs(n)} 公式，能正确判定所有 Σ${subs(n)} 语句的真假。直到第 ${n} 层的真是可定义的，就在第 ${n} 层上。`), 'info');
      await sleep(1300); if (my !== tok) { g.remove(); return; }
    }
    t.textContent = 'True ?';
    g.style.transform = 'translate(320px, 30px)';
    b.setAttribute('stroke', '#e03131'); b.setAttribute('fill', '#ffe3e3');
    okBox($('ahMsg'), bi('Full truth would need a single formula, at some fixed level n. But then the liar for it lives at level n + 1 and refutes it. Each level of truth is definable; their union is not.', '完整的真需要单个公式，它必然停在某个固定层级 n 上。可这样一来，它的说谎者位于第 n + 1 层，把它驳倒。每一层的真都可定义，它们的并却不可定义。'), 'warn');
  }
  $('ahClimb').addEventListener('click', climb);
  $('ahAll').addEventListener('click', () => { SETS.forEach((s, i) => setTimeout(() => place(s, $('ahChips').children[i], true), i * 120)); });
  $('ahReset').addEventListener('click', () => { tok++; frame(); });
  frame();
  [0, 3].forEach(i => place(SETS[i], $('ahChips').children[i], true));
})();

/* ================= §5 Tarski hierarchy of languages ================= */
(function tower() {
  const svg = $('tbSvg');
  const CX = 280, CY = 214;
  const CHIPS = [
    ['0 = 0 ,  ∀x ∃y (y = Sx)', ''],
    ['True₀(⌜0 = 0⌝)', ''],
    ['True₁(⌜True₀(⌜0=0⌝)⌝)', ''],
    ['True₂(⌜¬True₁(⌜0=S0⌝)⌝)', ''],
  ];
  let lv = 1;
  const dims = k => ({ w: 236 + k * 100, h: 80 + k * 84 });
  function boxAt(k) {
    const { w, h } = dims(k);
    const g = el('g', { class: 'fadein' }, svg);
    const col = ['#f08c00', '#3b5bdb', '#2f9e44', '#ae3ec9'][k];
    el('rect', { x: CX - w / 2, y: CY - h / 2, width: w, height: h, rx: 16, fill: k === 0 ? '#fff3bf' : 'none', stroke: col, 'stroke-width': 2.5, 'stroke-dasharray': k === 0 ? '' : '7 4' }, g);
    const lab = k === 0 ? 'L₀ = {0,S,+,×}' : `L${subs(k)} = L${subs(k - 1)} + True${subs(k - 1)}`;
    svgT(g, { x: CX - w / 2 + 10, y: CY - h / 2 + 17, 'font-size': 12.5, 'font-weight': 800, fill: col }, lab);
    svgT(g, { x: CX, y: k === 0 ? CY + 10 : CY - h / 2 + 34, 'text-anchor': 'middle', 'font-size': 12, fill: '#1f2430' }, CHIPS[k][0]);
    return g;
  }
  function draw() {
    svg.innerHTML = '';
    for (let k = 0; k <= lv; k++) boxAt(k);
    svgBi(svg, { x: 10, y: 392, 'font-size': 11, fill: '#6b7280' }, `truth for L${subs(lv)}: needs L${subs(lv + 1)}`, `L${subs(lv)} 的真：需要 L${subs(lv + 1)}`);
  }
  function msg() {
    okBox($('tbMsg'), lv === 0
      ? bi('L₀ is the glass box of arithmetic. By Tarski, no formula of L₀ defines truth for L₀. Add a box to step outside.', 'L₀ 是算术的玻璃箱。由塔斯基定理，L₀ 中没有公式能定义 L₀ 的真。加一层箱子，走到外面去。')
      : bi(`Box L${subs(lv)} adds a new predicate True${subs(lv - 1)}, applying only to sentences of L${subs(lv - 1)}. It is defined by the recursive clauses of §6, and satisfies every T-schema instance for L${subs(lv - 1)}. But L${subs(lv)} cannot define its own truth: that needs L${subs(lv + 1)}.`,
        `箱子 L${subs(lv)} 新增谓词 True${subs(lv - 1)}，只作用于 L${subs(lv - 1)} 的语句。它由 §6 的递归条款定义，满足 L${subs(lv - 1)} 的所有 T 模式实例。但 L${subs(lv)} 定义不了自己的真：那要到 L${subs(lv + 1)}。`), 'info');
  }
  $('tbAdd').addEventListener('click', () => { if (lv < 3) { lv++; draw(); msg(); } if (lv === 3) $('tbAdd').disabled = true; });
  $('tbReset').addEventListener('click', () => { lv = 0; $('tbAdd').disabled = false; draw(); msg(); });
  $('tbLiar').addEventListener('click', () => {
    draw();
    if (lv === 0) {
      okBox($('tbMsg'), bi('Inside L₀ there is no truth predicate to negate: the liar recipe ¬True(x) has no True to use. (Tarski: every candidate formula C(x) fails at its own liar, §3.) Add a box first.', 'L₀ 内部根本没有真谓词可以取否定：说谎者配方 ¬True(x) 里没有 True 可用。（塔斯基：每个候选公式 C(x) 都栽在它自己的说谎者上，见 §3。）先加一层箱子。'), 'warn');
      return;
    }
    const { h } = dims(lv);
    const g = el('g', { class: 'pop' }, svg);
    const y = CY + h / 2 - 16;
    el('rect', { x: CX - 120, y: y - 15, width: 240, height: 24, rx: 12, fill: '#ffe3e3', stroke: '#e03131' }, g);
    svgT(g, { x: CX, y: y + 2, 'text-anchor': 'middle', 'font-size': 12, 'font-weight': 800, fill: '#e03131' }, `λ ↔ ¬True${subs(lv - 1)}(⌜λ⌝)`);
    okBox($('tbMsg'), bi(`The diagonal lemma in L${subs(lv)} gives λ with λ ↔ ¬True${subs(lv - 1)}(⌜λ⌝). But λ mentions True${subs(lv - 1)}, so λ is <b>not</b> a sentence of L${subs(lv - 1)}. True${subs(lv - 1)} is false of everything outside L${subs(lv - 1)}, so ¬True${subs(lv - 1)}(⌜λ⌝) holds: λ is simply <b>true</b>. No paradox: the liar is defused by the levels.`,
      `在 L${subs(lv)} 中用对角线引理，得到 λ ↔ ¬True${subs(lv - 1)}(⌜λ⌝)。但 λ 中出现了 True${subs(lv - 1)}，所以 λ <b>不是</b> L${subs(lv - 1)} 的语句。True${subs(lv - 1)} 对 L${subs(lv - 1)} 之外的东西一律为假，故 ¬True${subs(lv - 1)}(⌜λ⌝) 成立：λ 就是<b>真的</b>。没有悖论：分层把说谎者拆除了。`), 'ok');
  });
  draw(); msg();
})();

/* ================= §6 T-schema & recursive truth ================= */
(function tschema() {
  const SENT = ['0=0', '∀x¬(Sx=0)', '∃y(y+y=SS0)', '¬(S0=0)', '∀x∃y(y=Sx)'];
  let cur = 0;
  function render() {
    const f = SENT[cur];
    $('tsBox').classList.remove('disq');
    $('tsBox').innerHTML = `<div class="side mention"><span class="qm">True(⌜</span>${f}<span class="qm">⌝)</span><small>${bil('mentioned: a claim about a number', '提及：关于一个数的断言')}</small></div>
      <div style="font-size:26px;color:var(--meta)">↔</div><div class="side use">${f}<small>${bil('used: a claim about numbers', '使用：关于数的断言')}</small></div>`;
    const n = gEncodeStr(f).toString();
    $('tsCode').innerHTML = `⌜${f}⌝ = ${n.length > 90 ? n.slice(0, 60) + '…' + n.slice(-12) + ` (${n.length} ${bil('digits', '位')})` : n}`;
  }
  pickBar($('tsPick'), SENT.map(s => ({ html: `<span class="m">${s}</span>` })), i => { cur = i; render(); });
  $('tsGo').addEventListener('click', () => $('tsBox').classList.add('disq'));
  render();

  // recursive tree
  const box = $('trTree');
  let samp = 0;
  const assignStr = s => Object.keys(s).length ? ' [' + Object.entries(s).map(([k, v]) => `${k}↦${v}`).join(', ') + ']' : '';
  const CL = { eq: ['compute both sides', '计算两边'], not: ['flip', '取反'], and: ['both', '两者皆真'], ex: ['some n ∈ ℕ', '存在 n ∈ ℕ'], all: ['every n ∈ ℕ', '对一切 n ∈ ℕ'] };
  function node(f, s) {
    const li = document.createElement('li');
    const v = sat(f, s);
    const d = document.createElement('div');
    d.className = 'tn' + (f.t === 'eq' ? ' leaf' : '');
    let extra = '';
    if (f.t === 'eq') extra = ` <span class="cl">${tval(f.a, s)} ${tval(f.a, s) === tval(f.b, s) ? '=' : '≠'} ${tval(f.b, s)}</span>`;
    d.innerHTML = `<span class="tog">${f.t === 'eq' ? '' : '▸'}</span>${fshow(f)}<span class="cl">${assignStr(s)}</span>${extra}<span class="bd ${v ? 't' : 'f'}">${v ? 'T' : 'F'}</span><span class="cl">${bil(CL[f.t][0], CL[f.t][1])}</span>`;
    li.appendChild(d);
    if (f.t !== 'eq') {
      let open = false, ul = null;
      li._open = () => {
        if (open) return;
        open = true;
        d.querySelector('.tog').textContent = '▾';
        ul = document.createElement('ul');
        if (f.t === 'not') ul.appendChild(node(f.a, s));
        else if (f.t === 'and') { ul.appendChild(node(f.a, s)); ul.appendChild(node(f.b, s)); }
        else {
          for (let n = 0; n <= 4; n++) ul.appendChild(node(f.a, { ...s, [f.v]: n }));
          const more = document.createElement('li');
          more.innerHTML = `<div class="tn more">⋯ ${f.v} = 5, 6, 7, … ${bil('infinitely many branches', '无穷多个分支')}</div>`;
          ul.appendChild(more);
        }
        li.appendChild(ul);
      };
      li._close = () => { if (!open) return; open = false; d.querySelector('.tog').textContent = '▸'; ul.remove(); };
      d.addEventListener('click', () => (open ? li._close() : li._open()));
    }
    return li;
  }
  function render2() {
    const sm = SAMPLES[samp];
    box.innerHTML = `<div class="muted" style="font-family:var(--sans);font-size:13px;margin-bottom:6px">${bil(sm.en, sm.zh)} · ${bil('truth value in ℕ', 'ℕ 中的真值')}: <b>${sat(sm.f, {}) ? 'T' : 'F'}</b></div>`;
    const ul = document.createElement('ul');
    const root = node(sm.f, {});
    ul.appendChild(root);
    box.appendChild(ul);
    root._open();
  }
  pickBar($('trPick'), SAMPLES.map(s => ({ html: `<span class="m">${fshow(s.f)}</span>` })), i => { samp = i; render2(); });
  $('trExp').addEventListener('click', () => {
    const openAll = li => { if (li._open) { li._open(); li.querySelectorAll(':scope > ul > li').forEach(openAll); } };
    box.querySelectorAll(':scope > ul > li').forEach(openAll);
  });
  $('trCol').addEventListener('click', render2);
  render2();
})();

/* ================= §7 V and truth ================= */
(function vcone() {
  const svg = $('vSvg');
  const LEV = [
    { l: 'V₀', size: '0' }, { l: 'V₁', size: '1' }, { l: 'V₂', size: '2' }, { l: 'V₃', size: '4' }, { l: 'V₄', size: '16' }, { l: 'V₅', size: '65536' },
    { l: 'V_ω', size: 'ℵ₀' }, { l: 'V_ω+1', size: '2^ℵ₀' }, { l: 'V_ω·2', size: 'ℶ_ω' }, { l: 'V', size: bil('proper class', '真类') },
  ];
  const AX = 240, AY = 380, TOPY = 40;
  const yOf = i => AY - 24 - i * ((AY - 24 - TOPY) / 9);
  const half = y => (AY - y) * 0.55;
  let refl = null;
  function draw() {
    const i = +$('vSl').value;
    svg.innerHTML = '';
    el('path', { d: `M ${AX} ${AY} L ${AX - half(TOPY - 10)} ${TOPY - 10} M ${AX} ${AY} L ${AX + half(TOPY - 10)} ${TOPY - 10}`, stroke: '#1f2430', 'stroke-width': 2, fill: 'none' }, svg);
    const y = yOf(i);
    el('path', { d: `M ${AX} ${AY} L ${AX - half(y)} ${y} L ${AX + half(y)} ${y} Z`, fill: i === 9 ? 'rgba(224,49,49,.15)' : 'rgba(59,91,219,.18)', stroke: i === 9 ? '#e03131' : '#3b5bdb', 'stroke-width': 2 }, svg);
    LEV.forEach((L, k) => {
      const yy = yOf(k);
      if (k < 9) el('line', { x1: AX - half(yy), x2: AX + half(yy), y1: yy, y2: yy, stroke: '#d8d3c4', 'stroke-dasharray': '3 4' }, svg);
      svgT(svg, { x: AX + half(yy) + 8, y: yy + 4, 'font-size': 12, 'font-weight': k === i ? 800 : 400, fill: k === i ? '#1f2430' : '#999' }, L.l);
    });
    if (refl !== null) {
      const yy = yOf(8) + 6;
      el('line', { x1: AX - half(yy), x2: AX + half(yy), y1: yy, y2: yy, stroke: '#f08c00', 'stroke-width': 3 }, svg);
      svgT(svg, { x: AX - half(yy) - 6, y: yy + 4, 'text-anchor': 'end', 'font-size': 12, 'font-weight': 800, fill: '#f08c00' }, 'V_α ≺_φ V');
    }
    $('vLab').innerHTML = LEV[i].l.replace('_', '');
    if (i < 9) okBox($('vMsg'), bi(`<b>${LEV[i].l}</b> is a set (size ${LEV[i].size}). The satisfaction relation of (${LEV[i].l}, ∈) is a set built by recursion on formulas, so ZFC defines “(${LEV[i].l}, ∈) ⊨ φ[s]” by one formula, uniformly in φ. ✓`,
      `<b>${LEV[i].l}</b> 是一个集合（大小为 ${LEV[i].size}）。(${LEV[i].l}, ∈) 的满足关系是沿公式递归构造出来的集合，所以 ZFC 能用一个公式、对 φ 一致地定义“(${LEV[i].l}, ∈) ⊨ φ[s]”。✓`), 'ok');
    else okBox($('vMsg'), bi('<b>V</b> is a proper class: there is no set “satisfaction relation of V” to recurse into, and by Tarski no formula Tr(x) can define truth in V. ✗ Only the levels Sat_Σₙ, one formula for each n, exist.', '<b>V</b> 是真类：不存在一个作为集合的“V 的满足关系”可供递归，而由塔斯基定理，没有公式 Tr(x) 能定义 V 中的真。✗ 只有分层的 Sat_Σₙ，每个 n 各有一个公式。'), 'bad');
  }
  const RF = [
    ['∀x ∃y (x ∈ y)', '∀x ∃y (x ∈ y)'],
    ['the power set axiom', '幂集公理'],
    ['“there is an infinite set”', '“存在无穷集”'],
  ];
  $('vRef').addEventListener('click', () => {
    refl = ((refl ?? -1) + 1) % RF.length;
    draw();
    okBox($('vMsg'), bi(`<b>Reflection</b> for φ = ${RF[refl][0]}: ZFC proves there are (unboundedly many) α with φ ↔ φ^(V_α), drawn in orange. One such theorem for each finite list of formulas, never one for all formulas at once.`,
      `对 φ = ${RF[refl][1]} 的<b>反射</b>：ZFC 证明存在（无界多个）α 使 φ ↔ φ^(V_α)，即图中橙线。每个有限的公式列表各对应一条这样的定理，但不存在对所有公式同时成立的单条定理。`), 'warn');
  });
  $('vSl').addEventListener('input', draw);
  draw();
})();

/* ================= §8 summary map ================= */
(function venn() {
  const svg = $('vnSvg');
  el('rect', { x: 10, y: 10, width: 310, height: 310, rx: 16, fill: '#ebfbee', stroke: '#2f9e44', 'stroke-width': 2 }, svg);
  el('rect', { x: 320, y: 10, width: 310, height: 310, rx: 16, fill: '#fff5f5', stroke: '#e03131', 'stroke-width': 2 }, svg);
  svgBi2(svg, { x: 22, y: 32, 'font-size': 13, 'font-weight': 800, fill: '#2f9e44' }, 'TRUE in ℕ: not definable', 'ℕ 中为真：不可定义', 16);
  svgBi2(svg, { x: 332, y: 32, 'font-size': 13, 'font-weight': 800, fill: '#e03131' }, 'FALSE in ℕ', 'ℕ 中为假', 16);
  el('ellipse', { cx: 165, cy: 170, rx: 120, ry: 78, fill: 'rgba(59,91,219,.12)', stroke: '#3b5bdb', 'stroke-width': 2 }, svg);
  el('ellipse', { cx: 475, cy: 170, rx: 120, ry: 78, fill: 'rgba(59,91,219,.12)', stroke: '#3b5bdb', 'stroke-width': 2 }, svg);
  svgBi2(svg, { x: 165, y: 124, 'text-anchor': 'middle', 'font-size': 12, 'font-weight': 700, fill: '#3b5bdb' }, 'PA ⊢ φ (Σ₁-definable)', 'PA ⊢ φ（Σ₁ 可定义）', 15);
  svgT(svg, { x: 475, y: 130, 'text-anchor': 'middle', 'font-size': 12, 'font-weight': 700, fill: '#3b5bdb' }, 'PA ⊢ ¬φ');
  const layer = el('g', {}, svg);
  const SENT = [
    { s: '0 = 0', at: [125, 175], en: 'True and provable.', zh: '真，且可证。' },
    { s: '∀x (0+x = x)', at: [200, 215], en: 'True and provable in PA (by induction), though not in Q.', zh: '真，在 PA 中可证（用归纳法），但在 Q 中不可证。' },
    { s: 'G_PA', at: [70, 280], en: 'True but unprovable in PA (Lesson 12).', zh: '真，但在 PA 中不可证（第 12 课）。' },
    { s: 'Con(PA)', at: [235, 285], en: 'True but unprovable in PA: the second incompleteness theorem.', zh: '真，但在 PA 中不可证：第二不完全性定理。' },
    { s: '0 = S0', at: [470, 185], en: 'False and refutable.', zh: '假，且可否证。' },
    { s: '¬G_PA', at: [380, 280], en: 'False, yet not refutable in PA (PA ⊬ G). Consistent with PA, but false.', zh: '假，但在 PA 中不可否证（因为 PA ⊬ G）。它与 PA 相容，却是假的。' },
    { s: '¬Con(PA)', at: [560, 285], en: 'False but not refutable: PA + ¬Con(PA) is consistent.', zh: '假，但不可否证：PA + ¬Con(PA) 是一致的。' },
    { s: 'Goldbach', at: [320, 60], en: 'Unknown! It is Π₁. If false, a counterexample is a finite computation, so PA refutes it. So it is either refutable, or true (possibly unprovable). It cannot be false-but-unrefutable.', zh: '未知！它是 Π₁ 语句。若为假，反例是一个有限计算，PA 就能否证它。所以它要么可否证，要么为真（可能不可证），不可能“假而不可否证”。' },
  ];
  SENT.forEach(t => {
    const c = document.createElement('div');
    c.className = 'chip';
    c.innerHTML = `<span class="m">${t.s}</span>`;
    c.addEventListener('click', () => {
      c.classList.add('used');
      okBox($('vnMsg'), `<b class="m">${t.s}</b>: ` + bi(t.en, t.zh), 'info');
      if (c._placed) return;
      c._placed = true;
      const g = el('g', { class: 'pop' }, layer);
      const unk = t.s === 'Goldbach';
      el('circle', { cx: t.at[0], cy: t.at[1], r: 6, fill: unk ? '#ae3ec9' : '#1f2430' }, g);
      svgT(g, { x: t.at[0], y: t.at[1] - 10, 'text-anchor': 'middle', 'font-size': 12, 'font-weight': 700, fill: unk ? '#ae3ec9' : '#1f2430' }, unk ? 'Goldbach ?' : t.s);
    });
    $('vnChips').appendChild(c);
  });
  [0, 2].forEach(i => $('vnChips').children[i].click());
  okBox($('vnMsg'), bi('The two blue regions are what PA decides. Everything outside them is undecided, on both sides of the true/false line.', '两块蓝色区域是 PA 能判定的部分。其余都是不可判定的，真假两侧都有。'), 'info');
})();

/* ================= Exercises ================= */
(function e1() {
  const items = [
    { s: bi('<b>Grelling.</b> A word is <i>heterological</i> if it does not describe itself (“long” is heterological). Is “heterological” heterological?', '<b>格雷林悖论.</b> 一个形容词若不描述它自身，就称为<i>异己的</i>（“长的”就是异己的）。“异己的”是异己的吗？'),
      o: [['the word w describes the word w', '词 w 描述词 w 自身', 1], ['the word w is an adjective', '词 w 是形容词', 0], ['w describes some other word', 'w 描述别的某个词', 0]] },
    { s: bi('<b>Barber.</b> The barber shaves exactly those who do not shave themselves.', '<b>理发师悖论.</b> 理发师恰好给所有不给自己刮胡子的人刮胡子。'),
      o: [['the barber shaves x', '理发师给 x 刮胡子', 0], ['x shaves x', 'x 给 x 自己刮胡子', 1], ['x shaves the barber', 'x 给理发师刮胡子', 0]] },
    { s: bi('<b>Quine.</b> “yields falsehood when preceded by its quotation” yields falsehood when preceded by its quotation.', '<b>奎因悖论.</b> “放在自己的引文后面就得出假话”放在自己的引文后面就得出假话。'),
      o: [['negating a sentence', '否定一个句子', 0], ['putting a phrase after its own quotation', '把一个短语放在它自己的引文后面', 1], ['quoting a sentence twice', '把句子引用两次', 0]] },
    { s: bi('<b>Richard.</b> List all reals definable in English; build a real whose n-th digit differs from the n-th digit of the n-th listed real.', '<b>理查德悖论.</b> 把所有能用英语定义的实数列出来，再造一个实数，使其第 n 位与第 n 个实数的第 n 位不同。'),
      o: [['the n-th listed real', '第 n 个实数', 0], ['the n-th digit of the n-th listed real', '第 n 个实数的第 n 位', 1], ['the number of English definitions', '英语定义的个数', 0]] },
  ];
  const done = items.map(() => false), revealed = items.map(() => false);
  items.forEach((it, i) => {
    const d = document.createElement('div');
    d.className = 'tf';
    d.innerHTML = `<div class="stmt" style="flex-basis:100%;font-size:15px">${it.s}</div><div class="opts" style="display:flex;gap:8px;flex-wrap:wrap"></div>
      <button class="btn small ghost">${bil('Show answer', '看答案')}</button><div style="flex-basis:100%"><div class="msg"></div></div>`;
    const msg = d.querySelector('.msg');
    it.o.forEach(([en, zh, ok]) => {
      const b = document.createElement('button');
      b.className = 'btn small';
      b.innerHTML = bil(en, zh);
      b.addEventListener('click', () => {
        d.querySelectorAll('.opts .btn').forEach(x => x.classList.remove('sel'));
        b.classList.add('sel');
        if (ok) {
          okBox(msg, bi('✓ Right: that is the self-application g(a)(a). The twist is negation, and the conclusion is that the described object cannot exist (or the language is inconsistent).', '✓ 对：这就是自我作用 g(a)(a)。扭转是否定，结论是所描述的对象不可能存在（或者该语言不一致）。'));
          if (!revealed[i]) done[i] = true;
          if (done.every(Boolean)) Progress.mark('L13E1');
        } else okBox(msg, bi('✗ Look for the place where something is applied to itself.', '✗ 找找哪里出现了“自己作用于自己”。'), 'bad');
      });
      d.querySelector('.opts').appendChild(b);
    });
    d.querySelector('.ghost').addEventListener('click', () => {
      revealed[i] = true;
      const k = it.o.findIndex(x => x[2]);
      okBox(msg, bi(`Diagonal entry: <b>${it.o[k][0]}</b>.`, `对角项：<b>${it.o[k][1]}</b>。`), 'info');
    });
    $('e1List').appendChild(d);
  });
})();

(function e2() {
  const LV = ['Δ₀', 'Σ₁', 'Π₁', 'Σ₂', 'Π₂', 'Σ₃', 'Π₃', 'none'];
  const LVzh = { none: '不是算术集' };
  const items = [
    ['{n : n is prime}', '{n : n 是素数}', 'Δ₀'],
    ['K = {e : φₑ(e)↓}', 'K = {e : φₑ(e)↓}', 'Σ₁'],
    ['{e : φₑ(e)↑}', '{e : φₑ(e)↑}', 'Π₁'],
    ['{⌜φ⌝ : PA ⊢ φ}', '{⌜φ⌝ : PA ⊢ φ}', 'Σ₁'],
    ['Tot = {e : φₑ total}', 'Tot = {e : φₑ 是全函数}', 'Π₂'],
    ['Fin = {e : Wₑ finite}', 'Fin = {e : Wₑ 有限}', 'Σ₂'],
    ['Cof = {e : Wₑ cofinite}', 'Cof = {e : Wₑ 余有限}', 'Σ₃'],
    ['Th(ℕ)', 'Th(ℕ)', 'none'],
  ];
  const sels = [];
  let revealed = false;
  items.forEach(([en, zh]) => {
    const r = document.createElement('div');
    r.className = 'hlrow';
    r.innerHTML = `<div class="nm m">${bl(en, zh)}</div>`;
    const s = document.createElement('select');
    s.className = 'sel';
    s.innerHTML = '<option value="">?</option>' + LV.map(l => `<option value="${l}">${l === 'none' ? 'not arithmetical · ' + LVzh.none : l}</option>`).join('');
    const mark = document.createElement('b');
    r.appendChild(s); r.appendChild(mark);
    sels.push([s, mark]);
    $('e2List').appendChild(r);
  });
  $('e2Check').addEventListener('click', () => {
    let ok = 0;
    sels.forEach(([s, m], i) => { const g = s.value === items[i][2]; m.textContent = s.value ? (g ? '✓' : '✗') : ''; m.style.color = g ? 'var(--true)' : 'var(--false)'; if (g) ok++; });
    if (ok === items.length) { okBox($('e2Msg'), bi('✓ All placed correctly. Note how provability (Σ₁) sits low, while truth sits nowhere.', '✓ 全部正确。注意可证性（Σ₁）位于低处，而真不在任何一层。')); if (!revealed) Progress.mark('L13E2'); }
    else okBox($('e2Msg'), bi(`${ok} / ${items.length} correct. Write each set’s definition and count the alternations of unbounded quantifiers.`, `答对 ${ok} / ${items.length}。写出每个集合的定义，数一数无界量词交替了几次。`), 'bad');
  });
  $('e2Show').addEventListener('click', () => {
    revealed = true;
    sels.forEach(([s, m], i) => { s.value = items[i][2]; m.textContent = ''; });
    okBox($('e2Msg'), bi('Answers filled in: primes Δ₀; K Σ₁; its complement Π₁; PA-theorems Σ₁; Tot Π₂; Fin Σ₂; Cof Σ₃; Th(ℕ) not arithmetical.', '答案已填入：素数 Δ₀；K 为 Σ₁；其补集 Π₁；PA 定理集 Σ₁；Tot 为 Π₂；Fin 为 Σ₂；Cof 为 Σ₃；Th(ℕ) 不是算术集。'), 'info');
  });
})();

orderGame($('e3Game'), [
  bi('Assume a formula True(x) defines truth in ℕ.', '假设公式 True(x) 定义了 ℕ 中的真。'),
  bi('Apply the diagonal lemma to ¬True(x): Q ⊢ L ↔ ¬True(⌜L⌝).', '对 ¬True(x) 应用对角线引理：Q ⊢ L ↔ ¬True(⌜L⌝)。'),
  bi('Since ℕ ⊨ Q, we get ℕ ⊨ L ↔ ¬True(⌜L⌝); by assumption also ℕ ⊨ True(⌜L⌝) ↔ L.', '由 ℕ ⊨ Q 得 ℕ ⊨ L ↔ ¬True(⌜L⌝)；由假设又有 ℕ ⊨ True(⌜L⌝) ↔ L。'),
  bi('Hence ℕ ⊨ L ↔ ¬L: contradiction.', '于是 ℕ ⊨ L ↔ ¬L：矛盾。'),
  bi('Conclude: Th(ℕ) is not arithmetically definable.', '结论：Th(ℕ) 不是算术可定义的。'),
], 'L13E3');

tfList($('e4List'), [
  { s: '<span class="m">True₀(⌜0=0⌝) ↔ 0=0</span>', ans: true, en: 'A sentence of L₀, mentioned on the left, used on the right.', zh: 'L₀ 的语句，左边被提及，右边被使用。' },
  { s: '<span class="m">True₀(0=0) ↔ 0=0</span>', ans: false, en: 'Ill-formed: True₀ takes a term (the numeral of a code), not a formula.', zh: '不合式：True₀ 的变元必须是一个项（编码的数字项），而不是公式。' },
  { s: '<span class="m">True₀(⌜x=0⌝) ↔ x=0</span>', ans: false, en: 'x = 0 is not a sentence. For formulas with free variables one needs satisfaction Sat(⌜φ⌝, s).', zh: 'x = 0 不是语句。含自由变元的公式需要满足关系 Sat(⌜φ⌝, s)。' },
  { s: '<span class="m">True₀(⌜¬True₀(⌜0=0⌝)⌝) ↔ ¬True₀(⌜0=0⌝)</span>', ans: false, en: 'The quoted sentence contains True₀, so it is in L₁, not L₀. True₀ does not cover it.', zh: '被引用的语句含有 True₀，属于 L₁ 而不属于 L₀，True₀ 管不到它。' },
  { s: '<span class="m">True₁(⌜True₀(⌜0=0⌝)⌝) ↔ True₀(⌜0=0⌝)</span>', ans: true, en: 'A sentence of L₁ handled by the next level up.', zh: 'L₁ 的语句，由上一层的真谓词处理。' },
  { s: '<span class="m">True₀(⌜∀x∃y(y=Sx)⌝) ↔ ∀x∃y(y=Sx)</span>', ans: true, en: 'An arithmetic sentence: a legitimate instance.', zh: '一个算术语句：合法的实例。' },
], 'L13E4', { labels: [['Instance', '是实例'], ['Not an instance', '不是实例']] });

tfList($('e5List'), [
  { s: bi('For each n ≥ 1 there is a Σₙ formula defining truth for Σₙ sentences in ℕ.', '对每个 n ≥ 1，都有一个 Σₙ 公式定义 ℕ 中 Σₙ 语句的真。'), ans: true, en: 'Yes: True_Σₙ. Combined with the diagonal argument, this is why the hierarchy is proper.', zh: '是的：True_Σₙ。再结合对角线论证，就得出层级是真包含的。' },
  { s: bi('There is one formula of arithmetic defining truth for all arithmetic sentences.', '存在单个算术公式定义所有算术语句的真。'), ans: false, en: 'Tarski’s theorem.', zh: '塔斯基定理。' },
  { s: bi('ZFC can define truth in the structure (ℕ, +, ×).', 'ZFC 能定义结构 (ℕ, +, ×) 中的真。'), ans: true, en: 'ℕ is a set; its satisfaction relation is a set defined by recursion. Set theory is a metalanguage for arithmetic.', zh: 'ℕ 是集合，它的满足关系是递归定义的集合。集合论是算术的元语言。' },
  { s: bi('ZFC can define truth in V by a single formula.', 'ZFC 能用单个公式定义 V 中的真。'), ans: false, en: 'Tarski again, inside set theory.', zh: '又是塔斯基定理，这次在集合论内部。' },
  { s: bi('Th(ℕ) is Σ₁₀₀.', 'Th(ℕ) 是 Σ₁₀₀ 的。'), ans: false, en: 'Th(ℕ) is not Σₙ for any n.', zh: 'Th(ℕ) 对任何 n 都不是 Σₙ 的。' },
  { s: bi('The set of codes of PA-theorems is arithmetically definable.', 'PA 定理的编码集是算术可定义的。'), ans: true, en: 'Yes, it is Σ₁: provability is definable, truth is not.', zh: '是的，它是 Σ₁ 的：可证性可定义，真不可定义。' },
], 'L13E5');

(function e6() {
  const proof = document.querySelector('#e6Proof .step');
  let revealed = false;
  const ch = choices($('e6Choice'), [
    { ok: false, en: 'Truth is undefinable, so T cannot contain a predicate True(x); hence T is incomplete.', zh: '真不可定义，所以 T 不能含有谓词 True(x)；因此 T 不完全。', fen: 'Lacking a truth predicate does not by itself mean some sentence is undecided.', fzh: '缺少真谓词本身并不意味着有语句不可判定。' },
    { ok: true, en: 'Thm_T is definable (Σ₁) but Th(ℕ) is not, so they differ; soundness gives Thm_T ⊊ Th(ℕ), so some true σ is unprovable, and so is the false ¬σ.', zh: 'Thm_T 可定义（Σ₁）而 Th(ℕ) 不可定义，所以两者不同；由可靠性 Thm_T ⊊ Th(ℕ)，故有真语句 σ 不可证，而假的 ¬σ 也不可证。', fen: 'Exactly. See the proof below.', fzh: '正是如此。证明见下。' },
    { ok: false, en: 'The liar sentence of arithmetic is neither true nor false, so T cannot decide it.', zh: '算术中的说谎者句既不真也不假，所以 T 判定不了它。', fen: 'There is no liar sentence in arithmetic: that is precisely what Tarski proves. Every arithmetic sentence is true or false in ℕ.', fzh: '算术中根本没有说谎者句：这恰恰是塔斯基所证明的。每个算术语句在 ℕ 中非真即假。' },
    { ok: false, en: 'Tarski shows Th(ℕ) is inconsistent, so T must leave something out.', zh: '塔斯基证明了 Th(ℕ) 不一致，所以 T 必须漏掉一些东西。', fen: 'Th(ℕ) is consistent: ℕ is a model of it.', fzh: 'Th(ℕ) 是一致的：ℕ 就是它的模型。' },
  ], $('e6Msg'), () => { proof.classList.add('on'); if (!revealed) Progress.mark('L13E6'); });
  $('e6Show').addEventListener('click', () => { revealed = true; ch.reveal(); proof.classList.add('on'); okBox($('e6Msg'), bi('The second option is correct.', '第二个选项正确。'), 'info'); });
})();
}
