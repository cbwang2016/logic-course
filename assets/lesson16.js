// Lesson 16 interactions: forcing.

/* ===================================================================
   Pure logic (no DOM). Exported for node unit tests at the bottom.
   Conditions of Fn(ω,2) are written as strings over {0,1,_}:
   character k is p(k), '_' = undefined. A string without '_' is a node
   of the tree 2<sup><ω</sup>.
   =================================================================== */
const F16 = (() => {
  // all binary strings of length ≤ D, in breadth-first (shortlex) order
  function strings(D) {
    const out = [''];
    for (let k = 0; k < out.length; k++) if (out[k].length < D) out.push(out[k] + '0', out[k] + '1');
    return out;
  }
  // partial functions as {n: bit}
  const pf = s => { const o = {}; [...s].forEach((c, i) => { if (c !== '_') o[i] = +c; }); return o; };
  const pfExt = (q, p) => Object.keys(p).every(k => q[k] !== undefined && q[k] === p[k]); // q ≤ p
  const pfCompat = (p, q) => Object.keys(p).every(k => q[k] === undefined || q[k] === p[k]);
  const pfClash = (p, q) => Object.keys(p).filter(k => q[k] !== undefined && q[k] !== p[k]).map(Number);
  // condition p (string over 0,1,_) is in G_g = {p : p ⊆ g}, where g is a known finite prefix
  const inGOf = g => p => [...p].every((c, i) => c === '_' || (i < g.length && +c === +g[i]));

  // shortest extension of string p in D among strings of length ≤ maxD
  function firstExt(p, inD, maxD) {
    const all = strings(maxD);
    const q = all.find(q => q.startsWith(p) && inD(q));
    return q === undefined ? null : q;
  }
  // truncated density test on the tree: every p with |p| ≤ cd has an extension in D of length ≤ sd
  function density(inD, cd = 3, sd = 6) {
    let fail = null;
    for (const p of strings(cd)) if (firstExt(p, inD, sd) === null) { fail = p; break; }
    return { dense: fail === null, fail };
  }

  // ---- P-names. A name is {label, pairs: [[name, cond]], chk?: n} ----
  const chkCache = [];
  function chk(n) {
    if (!chkCache[n]) {
      const pairs = [];
      for (let i = 0; i < n; i++) pairs.push([chk(i), '']);
      chkCache[n] = { label: n + '̌', pairs, chk: n };
    }
    return chkCache[n];
  }
  // val(τ, G) = { val(σ, G) : ∃p ∈ G (σ, p) ∈ τ }; returns {key, els} with canonical key
  function val(tau, inG) {
    const els = [], seen = new Set();
    for (const [s, p] of tau.pairs) {
      if (!inG(p)) continue;
      const v = val(s, inG);
      if (!seen.has(v.key)) { seen.add(v.key); els.push(v); }
    }
    els.sort((a, b) => (a.key < b.key ? -1 : a.key > b.key ? 1 : 0));
    return { key: '{' + els.map(e => e.key).join(',') + '}', els };
  }
  const ordKeys = Array.from({ length: 8 }, (_, n) => val(chk(n), () => true).key);
  function pretty(v) {
    const n = ordKeys.indexOf(v.key);
    if (n >= 0) return String(n);
    const rank = e => { const k = ordKeys.indexOf(e.key); return k >= 0 ? k : 100 + e.key.length; };
    return '{' + v.els.slice().sort((a, b) => rank(a) - rank(b) || (a.key < b.key ? -1 : 1)).map(pretty).join(', ') + '}';
  }
  // sort elements for display: ordinals by size first
  function prettyEls(v) { return v.els.map(pretty); }

  // ---- forcing statements about finitely many bits of ġ ----
  // phi: array of NB bits -> bool. Returns 1 (p ⊩ φ), 0 (p ⊩ ¬φ), null (undecided)
  function decide(p, phi, NB) {
    let t = 0, f = 0;
    for (let m = 0; m < 1 << NB; m++) {
      const b = Array.from({ length: NB }, (_, i) => (m >> (NB - 1 - i)) & 1);
      if ([...p].some((c, i) => i < NB && c !== '_' && +c !== b[i])) continue;
      if (phi(b)) t++; else f++;
    }
    return f === 0 ? 1 : t === 0 ? 0 : null;
  }

  // ---- Δ-systems ----
  const inter = (a, b) => a.filter(x => b.includes(x)).sort((x, y) => x - y);
  function deltaRoot(sets) {
    if (sets.length < 2) return null;
    const r = inter(sets[0], sets[1]).join(',');
    for (let i = 0; i < sets.length; i++)
      for (let j = i + 1; j < sets.length; j++)
        if (inter(sets[i], sets[j]).join(',') !== r) return null;
    return inter(sets[0], sets[1]);
  }
  // largest subfamily (size ≥ 3) that is a Δ-system; returns {idx, root} or null
  function largestDelta(fam) {
    let best = null;
    for (let m = 1; m < 1 << fam.length; m++) {
      const idx = fam.map((_, i) => i).filter(i => (m >> i) & 1);
      if (idx.length < 3 || (best && idx.length <= best.idx.length)) continue;
      const r = deltaRoot(idx.map(i => fam[i]));
      if (r) best = { idx, root: r };
    }
    return best;
  }

  // ---- the generic game ----
  // requirement {type:'x', k} = D_{x_k} = {p : p ⊥ x_k};  {type:'dom', n} = D_n
  function meets(p, req, xs) {
    if (req.type === 'dom') return p.length > req.n;
    return !xs[req.k].startsWith(p);
  }
  function firstDiff(p, x) { for (let i = 0; i < p.length; i++) if (p[i] !== x[i]) return i; return -1; }

  return { strings, pf, pfExt, pfCompat, pfClash, inGOf, firstExt, density, chk, val, pretty, prettyEls, ordKeys,
    decide, deltaRoot, largestDelta, meets, firstDiff };
})();

const E1SETS = [
  { en: '{p : 3 ∈ dom p}', zh: '{p : 3 ∈ dom p}', f: s => s.length > 3, dense: true,
    w: ['Any p extends to have 3 in its domain.', '任何 p 都能加细到让 3 进入定义域。'] },
  { en: '{p : p(0) = 1}', zh: '{p : p(0) = 1}', f: s => s[0] === '1', dense: false,
    w: ['Nothing below {(0,0)} is in it.', '{(0,0)} 下方没有它的元素。'] },
  { en: '{p : |dom p| is even}', zh: '{p : |dom p| 为偶数}', f: s => s.length % 2 === 0, dense: true,
    w: ['If |dom p| is odd, add one more point.', '若 |dom p| 为奇数，再添一个点。'] },
  { en: '{p : p takes the value 1 at most twice}', zh: '{p : p 取值 1 至多两次}', f: s => [...s].filter(c => c === '1').length <= 2, dense: false,
    w: ['Below a p with three 1s, every extension still has three 1s.', '若 p 已有三个 1，它的加细都至少有三个 1。'] },
  { en: '{p : p ⊥ x}, x = 000… (zero real)', zh: '{p : p ⊥ x}，x = 000…（零实数）', f: s => s.includes('1'), dense: true,
    w: ['This is D<sub>x</sub>: add a 1 at a fresh position.', '这就是 D<sub>x</sub>：在一个新位置添上 1。'] },
  { en: '{p : p(n) = p(n+1) = 1 for some n}', zh: '{p : 存在 n 使 p(n) = p(n+1) = 1}', f: s => s.includes('11'), dense: true,
    w: ['Add two 1s at fresh consecutive positions.', '在两个相邻的新位置上添 1。'] },
  { en: '{p : |dom p| ≤ 2}', zh: '{p : |dom p| ≤ 2}', f: s => s.length <= 2, dense: false,
    w: ['Domains only grow; below a p with 3 points there is nothing.', '定义域只会变大；有 3 个点的 p 下方一个元素都没有。'] },
  { en: '{p : p ⊥ q₀}, q₀ = {(0,1)}', zh: '{p : p ⊥ q₀}，q₀ = {(0,1)}', f: s => s[0] === '0', dense: false,
    w: ['Below q₀ itself everything is compatible with q₀.', '在 q₀ 自身下方，所有条件都与 q₀ 相容。'] },
];
const E3 = (() => {
  const c = F16.chk;
  const sigma = { label: 'σ', pairs: [[c(0), '00'], [c(1), '01']] };
  const tau = { label: 'τ', pairs: [[sigma, '0'], [c(1), '01'], [c(2), '1'], [c(0), '']] };
  const cands = [
    { lab: '0', v: F16.val(c(0), () => true) },
    { lab: '1', v: F16.val(c(1), () => true) },
    { lab: '2', v: F16.val(c(2), () => true) },
    { lab: '{1}', v: F16.val({ pairs: [[c(1), '']] }, () => true) },
    { lab: '{2}', v: F16.val({ pairs: [[c(2), '']] }, () => true) },
  ];
  const rounds = ['00', '01', '10'];
  const answer = g => { const v = F16.val(tau, F16.inGOf(g)); return cands.map(cd => v.els.some(e => e.key === cd.v.key)); };
  return { tau, cands, rounds, answer };
})();
if (typeof window === 'undefined') {
  module.exports = { F16, E1SETS, E3 };
} else {
  initLesson16();
}

/* =================================================================== */
function initLesson16() {
Lang.init();
Progress.paint();

const $ = id => document.getElementById(id);
const okBox = (box, html, kind = 'ok') => { box.className = 'msg ' + kind; box.innerHTML = html; };
const clearBox = box => { box.className = 'msg'; box.innerHTML = ''; };
const SUBS = '₀₁₂₃₄₅₆₇₈₉';
const sub = n => String(n).split('').map(d => SUBS[d]).join('');
const fmtS = s => (s === '' ? '∅' : '⟨' + s + '⟩');
const fmtC = c => {
  if (c === '') return '𝟙';
  if (!c.includes('_')) return '⟨' + c + '⟩';
  return '{' + [...c].map((b, i) => (b === '_' ? null : `(${i},${b})`)).filter(Boolean).join(',') + '}';
};
function txt(parent, x, y, s, attrs = {}) {
  const t = el('text', Object.assign({ x, y }, attrs), parent);
  t.textContent = s;
  return t;
}
const shuffle = a => { for (let i = a.length - 1; i > 0; i--) { const j = Math.floor(Math.random() * (i + 1)); [a[i], a[j]] = [a[j], a[i]]; } return a; };
const rbit = () => (Math.random() < 0.5 ? '0' : '1');
const biq = (en, zh) => (en === zh ? en : bi(en, zh));
const bilq = (en, zh) => (en === zh ? en : bil(en, zh));
function btn(html, cls = 'btn small') { const b = document.createElement('button'); b.className = cls; b.innerHTML = html; return b; }
function markDone(id) { Progress.mark(id); const ex = document.querySelector(`.ex[data-prog="${id}"]`); if (ex) ex.classList.add('done'); }
(function paintDoneEx() { const p = Progress.get(); document.querySelectorAll('.ex[data-prog]').forEach(e => e.classList.toggle('done', !!p[e.dataset.prog])); })();

/* ---------- tree of 2^{<ω} ---------- */
function makeTree(svg, opts = {}) {
  const D = opts.D ?? 5, W = opts.W ?? 880, top = opts.top ?? 20, rowH = opts.rowH ?? 44;
  const R = [13, 12, 11, 10, 8, 6.5];
  svg.innerHTML = '';
  const gE = el('g', {}, svg), gN = el('g', {}, svg);
  const nodes = {};
  const pos = s => { const d = s.length, i = d ? parseInt(s, 2) : 0; return { x: 20 + (i + 0.5) * (W - 40) / 2 ** d, y: top + d * rowH }; };
  F16.strings(D).forEach(s => {
    const { x, y } = pos(s);
    const n = { s, x, y };
    if (s) {
      const pp = pos(s.slice(0, -1));
      n.edge = el('line', { x1: pp.x, y1: pp.y, x2: x, y2: y, class: 'te' }, gE);
      if (s.length <= 2) txt(gE, (pp.x + x) / 2 + (s.endsWith('0') ? -7 : 7), (pp.y + y) / 2 - 3, s.slice(-1), { class: 'elab' });
    }
    n.g = el('g', { class: 'tn', transform: `translate(${x},${y})` }, gN);
    el('circle', { r: R[s.length] }, n.g);
    if (s.length <= 3) txt(n.g, 0, 3.5, s || '∅', { 'font-size': s.length >= 3 ? 8 : 10 });
    const ti = el('title', {}, n.g);
    ti.textContent = s ? `p = ${s}` : 'p = ∅ = 𝟙';
    if (opts.onClick) n.g.addEventListener('click', () => opts.onClick(s));
    nodes[s] = n;
  });
  return {
    nodes,
    paint(fn) { for (const s in nodes) nodes[s].g.setAttribute('class', 'tn ' + (fn(s) || '')); },
    edges(fn) { for (const s in nodes) if (nodes[s].edge) nodes[s].edge.setAttribute('class', 'te ' + (fn(s) || '')); },
  };
}

/* ================= §1 big picture ================= */
(function cones() {
  const svg = $('cones');
  const AX = 280, AY = 410, TOP = 90;
  const hw = (y, HW) => HW * Math.sqrt(Math.max(0, AY - y) / (AY - TOP));
  function conePath(HW, yTop) {
    const L = [], Rr = [];
    for (let y = yTop; y <= AY; y += 4) { L.push(`${(AX - hw(y, HW)).toFixed(1)},${y}`); Rr.unshift(`${(AX + hw(y, HW)).toFixed(1)},${y}`); }
    return 'M' + L.join(' L') + ` L${AX},${AY} L` + Rr.join(' L') + ' Z';
  }
  // V (hidden by default)
  const gV = el('g', { opacity: 0 }, svg);
  gV.style.transition = 'opacity .6s';
  el('path', { d: conePath(250, 14).replace(/ Z$/, ''), fill: 'rgba(31,36,48,.03)', stroke: '#9aa0aa', 'stroke-dasharray': '6 5', 'stroke-width': 1.5 }, gV);
  el('line', { x1: AX, y1: TOP, x2: AX, y2: 10, stroke: '#9aa0aa', 'stroke-width': 2, 'stroke-dasharray': '4 4' }, gV);
  txt(gV, 470, 40, 'V', { 'font-size': 22, 'font-weight': 800, fill: '#6b7280' });
  txt(gV, 300, 22, 'Ord (V) · V 的序数', { 'font-size': 11, fill: '#6b7280' });
  // M[G]
  const gMG = el('g', {}, svg);
  gMG.style.transformOrigin = `${AX}px ${AY}px`;
  gMG.style.transition = 'transform 1.1s cubic-bezier(.2,.9,.3,1), opacity 1.1s';
  gMG.style.transform = 'scaleX(0.68)';
  gMG.style.opacity = 0;
  el('path', { d: conePath(140, TOP), fill: 'rgba(174,62,201,.10)', stroke: '#ae3ec9', 'stroke-width': 2.5 }, gMG);
  txt(gMG, AX + 120, TOP + 6, 'M[G]', { 'font-size': 18, 'font-weight': 800, fill: '#ae3ec9' });
  // M
  el('path', { d: conePath(95, TOP), fill: 'rgba(59,91,219,.14)', stroke: '#3b5bdb', 'stroke-width': 2.5 }, svg);
  txt(svg, AX - 128, TOP + 6, 'M', { 'font-size': 18, 'font-weight': 800, fill: '#3b5bdb' });
  // top line o(M)
  el('line', { x1: AX - 150, x2: AX + 150, y1: TOP, y2: TOP, stroke: '#1f2430', 'stroke-dasharray': '3 4', opacity: .5 }, svg);
  // spine
  el('line', { x1: AX, y1: AY, x2: AX, y2: TOP, stroke: '#1f2430', 'stroke-width': 2.5 }, svg);
  // slice line
  const slice = el('g', {}, svg);
  const levels = [
    { y: 382, lab: 'n', en: 'finite n', zh: '有限的 n' },
    { y: 350, lab: 'ω', en: 'ω', zh: 'ω' },
    { y: 334, lab: 'ω+1', en: 'ω+1', zh: 'ω+1' },
    { y: 318, lab: 'ω+2', en: 'ω+2', zh: 'ω+2' },
    { y: 250, lab: 'ω₁^M', en: 'ω₁^M', zh: 'ω₁^M' },
    { y: TOP, lab: 'o(M)', en: 'o(M)', zh: 'o(M)' },
  ];
  [1, 4].forEach(i => txt(svg, AX - 8, levels[i].y + 4, levels[i].lab, { 'text-anchor': 'end', 'font-size': 12, fill: '#1f2430', 'font-weight': 700 }));
  txt(svg, AX + 8, 194, 'ω₂^M', { 'font-size': 12, 'font-weight': 700 });
  txt(svg, AX + 8, TOP - 8, 'o(M) = Ord ∩ M = Ord ∩ M[G]', { 'font-size': 12, 'font-weight': 700 });
  txt(svg, AX + 6, AY + 4, '∅', { 'font-size': 13 });

  let adjoined = false, showV = false;
  const info = {
    x: bi('<b>x ∈ M</b>: a real of the ground model. Its check name <span class="m">x̌</span> evaluates to <span class="m">x</span> under every <span class="m">G</span>, so <span class="m">M ⊆ M[G]</span>. Only countably many reals live in <span class="m">M</span> (seen from outside).',
      '<b>x ∈ M</b>：基础模型里的一个实数。它的典范名字 <span class="m">x̌</span> 在任何 <span class="m">G</span> 下都取值为 <span class="m">x</span>，所以 <span class="m">M ⊆ M[G]</span>。（从外面看）<span class="m">M</span> 里只有可数多个实数。'),
    g: bi('<b>g = ⋃G</b>: the new <b>Cohen real</b>. It sits at level <span class="m">ω+1</span> (a subset of ω), low in the hierarchy, but it is not in <span class="m">M</span>: it disagrees with every real of <span class="m">M</span> (§4).',
      '<b>g = ⋃G</b>：新加入的<b>科恩实数</b>。它位于第 <span class="m">ω+1</span> 层（是 ω 的子集），层级很低，却不在 <span class="m">M</span> 中：它与 <span class="m">M</span> 的每个实数都不同（见 §4）。'),
    G: bi('<b>G ⊆ P</b>: the generic filter. Every element of <span class="m">G</span> is in <span class="m">M</span>, but the set <span class="m">G</span> itself is not (§5). <span class="m">M[G]</span> is the smallest transitive model of ZFC containing <span class="m">M ∪ {G}</span>.',
      '<b>G ⊆ P</b>：脱殊滤子。<span class="m">G</span> 的每个元素都在 <span class="m">M</span> 中，但集合 <span class="m">G</span> 本身不在（见 §5）。<span class="m">M[G]</span> 是包含 <span class="m">M ∪ {G}</span> 的最小 ZFC 传递模型。'),
    w1: bi('<b>ω₁^M</b>: M believes this ordinal is uncountable. From outside it is a countable ordinal, because M is countable (Skolem\'s paradox, L5/L14). Cohen forcing is ccc, so <span class="m">ω₁<sup>M[G]</sup> = ω₁^M</span> (§9).',
      '<b>ω₁^M</b>：M 认为这个序数不可数；从外面看它其实是可数序数，因为 M 本身可数（斯科伦悖论，第 5、14 课）。科恩力迫满足 ccc，所以 <span class="m">ω₁<sup>M[G]</sup> = ω₁^M</span>（见 §9）。'),
    top: bi('<b>Same height.</b> Each <span class="m">val(τ,G)</span> has rank ≤ rank(τ), and names live in <span class="m">M</span>, so <span class="m">M[G]</span> has no new ordinals: <span class="m">Ord ∩ M[G] = Ord ∩ M = o(M)</span>, a countable ordinal.',
      '<b>一样高.</b> 每个 <span class="m">val(τ,G)</span> 的秩都 ≤ rank(τ)，而名字都在 <span class="m">M</span> 中，所以 <span class="m">M[G]</span> 没有新序数：<span class="m">Ord ∩ M[G] = Ord ∩ M = o(M)</span>，这是一个可数序数。'),
  };
  function dot(x, y, key, color, label, r = 8) {
    const g = el('g', { style: 'cursor:pointer' }, svg);
    const c = el('circle', { cx: x, cy: y, r, fill: color, stroke: '#fff', 'stroke-width': 2 }, g);
    const t = txt(g, x + (label === 'G' ? -14 : 12), y + 4, label, { 'font-size': 14, 'font-weight': 800, fill: color, 'text-anchor': label === 'G' ? 'end' : 'start' });
    g.addEventListener('click', () => okBox($('coneMsg'), info[key], 'info'));
    return { g, c, t };
  }
  dot(AX - 30, 334, 'x', '#3b5bdb', 'x');
  const gDot = dot(AX + 58, 334, 'g', '#ae3ec9', 'g');
  const GDot = dot(AX - 62, 300, 'G', '#ae3ec9', 'G');
  [gDot, GDot].forEach(d => { d.g.style.transition = 'opacity .8s'; d.g.style.opacity = 0; });
  dot(AX, 250, 'w1', '#1f2430', '', 6);
  dot(AX, 194, 'top', '#1f2430', '', 5);
  dot(AX, TOP, 'top', '#1f2430', '', 7);

  function drawSlice() {
    const k = +$('coneA').value, L = levels[k];
    $('coneAv').textContent = L.lab;
    slice.innerHTML = '';
    const y = L.y;
    const wM = hw(y, 95), wG = hw(y, 140);
    if (adjoined && k >= 2) {
      el('line', { x1: AX - wG, x2: AX + wG, y1: y, y2: y, stroke: '#ae3ec9', 'stroke-width': 5, opacity: .55 }, slice);
    }
    el('line', { x1: AX - wM, x2: AX + wM, y1: y, y2: y, stroke: '#3b5bdb', 'stroke-width': 5, opacity: .7 }, slice);
    txt(slice, AX - (adjoined ? wG : wM) - 8, y + 4, `V_${L.lab}`, { 'text-anchor': 'end', 'font-size': 12, fill: '#3b5bdb', 'font-weight': 700 });
    const msgs = [
      bi('<b>α finite:</b> <span class="m">V<sub>n</sub><sup>M</sup> = V<sub>n</sub><sup>M[G]</sup> = V<sub>n</sub></span>. Finite sets are absolute.', '<b>α 有限：</b><span class="m">V<sub>n</sub><sup>M</sup> = V<sub>n</sub><sup>M[G]</sup> = V<sub>n</sub></span>。有限集是绝对的。'),
      bi('<b>α = ω:</b> both contain all hereditarily finite sets, <span class="m">V<sub>ω</sub> ⊆ M</span>. Still identical.', '<b>α = ω：</b>两者都含有全部遗传有限集，<span class="m">V<sub>ω</sub> ⊆ M</span>。仍然完全一样。'),
      bi('<b>α = ω+1:</b> <span class="m">V<sub>ω+1</sub></span> is essentially <span class="m">P(ω)</span>. Here the models split: <span class="m">g ∈ V<sub>ω+1</sub><sup>M[G]</sup> ∖ M</span>.', '<b>α = ω+1：</b><span class="m">V<sub>ω+1</sub></span> 本质上就是 <span class="m">P(ω)</span>。两个模型在这里分开了：<span class="m">g ∈ V<sub>ω+1</sub><sup>M[G]</sup> ∖ M</span>。'),
      bi('<b>α = ω+2:</b> new sets of reals, e.g. <span class="m">{g}</span>, <span class="m">M[G] ∩ P(ω)</span> itself, and many more.', '<b>α = ω+2：</b>出现了新的实数集，比如 <span class="m">{g}</span>、<span class="m">M[G] ∩ P(ω)</span> 本身，还有很多。'),
      bi('<b>α = ω₁^M:</b> same level, different width. Cardinals agree in M and M[G] here (ccc).', '<b>α = ω₁^M：</b>同一层，宽度不同。这里 M 与 M[G] 的基数一致（ccc）。'),
      bi('<b>α = o(M):</b> the top. <span class="m">M[G]</span> has the same height as <span class="m">M</span>: no new ordinals.', '<b>α = o(M)：</b>顶端。<span class="m">M[G]</span> 与 <span class="m">M</span> 一样高：没有新序数。'),
    ];
    okBox($('coneSlice'), msgs[k] + (adjoined || k < 2 ? '' : bi(' <i>(Press “Adjoin G” to see the difference.)</i>', ' <i>（按“添加 G”看差别。）</i>')), k >= 2 && adjoined ? 'warn' : 'ok');
  }
  $('coneA').addEventListener('input', drawSlice);
  $('coneG').addEventListener('click', () => {
    adjoined = !adjoined;
    gMG.style.transform = adjoined ? 'scaleX(1)' : 'scaleX(0.68)';
    gMG.style.opacity = adjoined ? 1 : 0;
    [gDot, GDot].forEach(d => d.g.style.opacity = adjoined ? 1 : 0);
    $('coneG').innerHTML = adjoined ? bi('Remove G', '去掉 G') : bi('Adjoin G ▶', '添加 G ▶');
    okBox($('coneMsg'), adjoined
      ? bi('M[G] (purple) appears: <b>wider, not taller</b>. Click <b>g</b> and <b>G</b>. Move the slider to compare levels <span class="m">V<sub>α</sub></span>.', 'M[G]（紫色）出现了：<b>更宽，但没有更高</b>。点一点 <b>g</b> 和 <b>G</b>，拖动滑块比较各层 <span class="m">V<sub>α</sub></span>。')
      : info.x, 'info');
    drawSlice();
  });
  $('coneV').addEventListener('click', () => {
    showV = !showV;
    gV.setAttribute('opacity', showV ? 1 : 0);
    if (showV) okBox($('coneMsg'), bi('<b>V</b>, the real universe, dwarfs both. <span class="m">M</span> is a countable set in <span class="m">V</span>, and its height <span class="m">o(M)</span> is a countable ordinal. That is exactly why there is room to find <span class="m">G</span> outside <span class="m">M</span>.',
      '<b>V</b> 是真正的全域，把两个模型都比得很小。<span class="m">M</span> 是 <span class="m">V</span> 中的可数集，其高度 <span class="m">o(M)</span> 是可数序数。正因为如此，才有余地在 <span class="m">M</span> 之外找到 <span class="m">G</span>。'), 'info');
  });
  okBox($('coneMsg'), bi('Click a dot: <b>x</b>, the spine ordinals <b>ω₁^M</b>, <b>ω₂^M</b>, the top <b>o(M)</b>. Then press <b>Adjoin G</b>.', '点圆点：<b>x</b>、脊柱上的序数 <b>ω₁^M</b>、<b>ω₂^M</b>、顶端 <b>o(M)</b>。然后按<b>添加 G</b>。'), 'info');
  drawSlice();

  // metamathematics tabs
  const tabs = [
    { en: 'A · Countable transitive models', zh: 'A · 可数传递模型', blocks: [
      ['for each finite Ψ ⊆ ZFC: ZFC ⊢ “Ψ has a ctm”', '对 ZFC 的每个有限片段 Ψ：ZFC ⊢“Ψ 有可数传递模型”', 'L14: reflection + LS + Mostowski (a theorem scheme, one theorem per Ψ)', '第 14 课：反射 + LS + 坍塌（定理模式：每个 Ψ 一条定理）'],
      ['G exists over M', '存在 M 上的脱殊滤子 G', '§5 Rasiowa–Sikorski', '§5 拉肖瓦–西科尔斯基'],
      ['M[G] ⊨ Φ + ¬CH', 'M[G] ⊨ Φ + ¬CH', '§8, §9', '§8、§9'],
      ['Con(ZFC) → Con(ZFC + ¬CH)', 'Con(ZFC) → Con(ZFC + ¬CH)', 'finitary argument', '有穷论证'],
    ], en2: 'This is the approach of this lesson. We never claim a ctm of <i>all</i> of ZFC; only of a finite fragment Ψ, chosen large enough for whatever finite Φ we need in <span class="m">M[G]</span>.',
      zh2: '这一课用的就是这种做法。我们从不声称存在<i>整个</i> ZFC 的可数传递模型，只要求某个有限片段 Ψ 有，Ψ 取得足够大，以保证 <span class="m">M[G]</span> 满足我们需要的有限个公理 Φ。' },
    { en: 'B · Boolean-valued models', zh: 'B · 布尔值模型', blocks: [
      ['B = RO(P), a complete Boolean algebra', 'B = RO(P)，完备布尔代数', 'regular open sets', '正则开集'],
      ['V^B: truth values ⟦φ⟧ ∈ B', 'V^B：真值 ⟦φ⟧ ∈ B', 'not just 0/1', '不只是 0/1'],
      ['⟦σ⟧ = 1 for every axiom σ, ⟦¬CH⟧ = 1', '每条公理 σ 有 ⟦σ⟧ = 1，且 ⟦¬CH⟧ = 1', 'ZFC proves each instance', 'ZFC 逐条可证'],
      ['a proof of ⊥ would give ⟦⊥⟧ = 1', '若能证出 ⊥，就有 ⟦⊥⟧ = 1', 'but ⟦⊥⟧ = 0', '可是 ⟦⊥⟧ = 0'],
    ], en2: 'Scott–Solovay–Vopěnka. No countable model and no generic filter needed: everything happens inside <span class="m">V</span>. Since rules of logic preserve truth value 1, a ZFC-proof of CH would give a ZFC-proof of ⟦⊥⟧ = 1 ≠ 0; so if ZFC is consistent, ZFC ⊬ CH. The ctm picture is recovered by taking a generic ultrafilter.',
      zh2: '斯科特、索洛韦、沃彭卡的做法。不需要可数模型，也不需要脱殊滤子，一切都在 <span class="m">V</span> 内完成。因为逻辑规则保持真值 1，若 ZFC 能证 CH，ZFC 就能证 ⟦⊥⟧ = 1 ≠ 0；所以只要 ZFC 一致，就有 ZFC ⊬ CH。取一个脱殊超滤子，又回到可数传递模型的图景。' },
    { en: 'C · Syntactic forcing', zh: 'C · 语法力迫', blocks: [
      ['define p ⊩* φ in V', '在 V 中定义 p ⊩* φ', 'by recursion on φ', '对 φ 递归'],
      ['𝟙 ⊩* each axiom of ZFC', '𝟙 ⊩* ZFC 的每条公理', 'one theorem per axiom', '每条公理一个定理'],
      ['𝟙 ⊩* ¬CH', '𝟙 ⊩* ¬CH', 'ccc + Δ-system', 'ccc + Δ-系统'],
      ['⊩* is closed under logic; 𝟙 ⊮* ⊥', '⊩* 对逻辑推理封闭；𝟙 ⊮* ⊥', 'so ZFC + ¬CH ⊬ ⊥', '故 ZFC + ¬CH ⊬ ⊥'],
    ], en2: 'Here forcing is just a translation of proofs: a ZFC + ¬CH proof of ⊥ becomes a ZFC proof of “𝟙 ⊩* ⊥”, which is refutable. The three approaches prove the same relative consistency result.',
      zh2: '这里力迫只是证明的翻译：从 ZFC + ¬CH 推出 ⊥ 的证明，会被翻译成 ZFC 中“𝟙 ⊩* ⊥”的证明，而后者可以被驳倒。三种做法得到的是同一个相对一致性结果。' },
  ];
  const tb = $('metaTabs');
  tabs.forEach((t, i) => {
    const b = btn(bil(t.en, t.zh));
    b.addEventListener('click', () => {
      tb.querySelectorAll('button').forEach(x => x.classList.remove('sel'));
      b.classList.add('sel');
      let h = '<div class="blocks" style="font-family:var(--sans)">';
      t.blocks.forEach((bk, j) => {
        h += `<div class="${j === t.blocks.length - 1 ? 'p' : 'sub'} pop" style="animation-delay:${j * 0.12}s;flex:1 1 150px">${bi(bk[0], bk[1])}<small>${bil(bk[2], bk[3])}</small></div>`;
        if (j < t.blocks.length - 1) h += '<div style="border:0;background:none;align-self:center;font-size:20px">→</div>';
      });
      $('metaBox').innerHTML = h + `</div><p style="margin:6px 4px 0">${bi(t.en2, t.zh2)}</p>`;
    });
    tb.appendChild(b);
    if (i === 0) setTimeout(() => b.click(), 0);
  });
})();

/* ================= §2 Cohen poset ================= */
(function cohen() {
  let p = null, q = null;
  const T = makeTree($('tree2'), { onClick: s => { if (p === null || q !== null) { p = s; q = null; } else q = s; render(); } });
  function render() {
    T.paint(s => (s === p ? 'sel' : s === q ? 'sel2' : p !== null && s.startsWith(p) ? 'cone' : ''));
    T.edges(s => (p !== null && s.startsWith(p) && s !== p ? 'on' : ''));
    const box = $('tree2Msg');
    if (p === null) { okBox(box, bi('Click a node to choose <span class="m">p</span>.', '点一个节点选作 <span class="m">p</span>。'), 'info'); return; }
    if (q === null) {
      okBox(box, bi(`<span class="m">p = ${fmtS(p)}</span>. The blue cone is <span class="m">{q : q ≤ p}</span>: every way of adding information to <span class="m">p</span>. Going down = stronger. Now click a second node <span class="m">q</span>.`,
        `<span class="m">p = ${fmtS(p)}</span>。蓝色锥形是 <span class="m">{q : q ≤ p}</span>：在 <span class="m">p</span> 上增加信息的所有方式。越往下越强。再点第二个节点作为 <span class="m">q</span>。`), 'info');
      return;
    }
    const P = fmtS(p), Q = fmtS(q);
    if (p === q) okBox(box, bi('Same condition twice. Pick a different <span class="m">q</span>.', '两次选了同一个条件，换一个 <span class="m">q</span>。'), 'info');
    else if (q.startsWith(p)) okBox(box, bi(`<span class="m">q = ${Q} ≤ p = ${P}</span>: q extends p, so q is <b>stronger</b>. Compatible, with common extension q itself.`, `<span class="m">q = ${Q} ≤ p = ${P}</span>：q 延拓了 p，所以 q <b>更强</b>。二者相容，公共加细就是 q 本身。`), 'ok');
    else if (p.startsWith(q)) okBox(box, bi(`<span class="m">p = ${P} ≤ q = ${Q}</span>: p is the stronger one. Compatible.`, `<span class="m">p = ${P} ≤ q = ${Q}</span>：p 更强。二者相容。`), 'ok');
    else {
      let k = 0; while (p[k] === q[k]) k++;
      okBox(box, bi(`<span class="m">p ⊥ q</span>: they disagree at position ${k} (p(${k}) = ${p[k]}, q(${k}) = ${q[k]}). No condition extends both; their cones are disjoint. In the tree, incompatible = neither lies below the other.`,
        `<span class="m">p ⊥ q</span>：它们在第 ${k} 位不一致（p(${k}) = ${p[k]}，q(${k}) = ${q[k]}）。没有条件能同时延拓二者，它们的锥形互不相交。在树中，不相容就是谁也不在谁的下方。`), 'bad');
    }
  }
  render();

  // partial-function rows
  const N = 12;
  const rows = { p: { 0: 1, 3: 0 }, q: { 0: 1, 5: 1, 7: 0 } };
  const stage = $('pfStage');
  function cellsRow(lab, obj, editable) {
    let h = `<div class="cells"><span class="lab">${lab}</span>`;
    for (let i = 0; i < N; i++) {
      const v = obj ? obj[i] : undefined;
      h += `<span class="cell${v === undefined ? '' : ' b' + v}${editable ? '' : ' ro'}" data-i="${i}">${v === undefined ? '' : v}</span>`;
    }
    return h + '<span class="muted">…</span></div>';
  }
  function draw() {
    let h = '<div class="cells"><span class="lab"></span>' + Array.from({ length: N }, (_, i) => `<span class="cell idx">${i}</span>`).join('') + '</div>';
    h += `<div data-row="p">${cellsRow('p', rows.p, true)}</div><div data-row="q">${cellsRow('q', rows.q, true)}</div>`;
    const compat = F16.pfCompat(rows.p, rows.q);
    h += `<div style="margin-top:6px">${cellsRow(compat ? 'p ∪ q' : 'p ∪ q ✗', compat ? Object.assign({}, rows.p, rows.q) : null, false)}</div>`;
    stage.innerHTML = h;
    const clash = F16.pfClash(rows.p, rows.q);
    ['p', 'q'].forEach(r => stage.querySelectorAll(`[data-row="${r}"] .cell`).forEach(c => {
      const i = +c.dataset.i;
      if (clash.includes(i)) c.classList.add('clash');
      c.addEventListener('click', () => {
        const o = rows[r];
        o[i] = o[i] === undefined ? 0 : o[i] === 0 ? 1 : undefined;
        if (o[i] === undefined) delete o[i];
        draw();
      });
    }));
    const qp = F16.pfExt(rows.q, rows.p), pq = F16.pfExt(rows.p, rows.q);
    let msg = '';
    if (qp && pq) msg = bi('p = q.', 'p = q。');
    else if (qp) msg = bi('<b>q ≤ p</b>: q ⊇ p, so q is stronger.', '<b>q ≤ p</b>：q ⊇ p，q 更强。');
    else if (pq) msg = bi('<b>p ≤ q</b>: p ⊇ q, so p is stronger.', '<b>p ≤ q</b>：p ⊇ q，p 更强。');
    else msg = bi('Neither extends the other.', '谁也不是谁的延拓。');
    msg += ' ' + (compat
      ? bi('<b>Compatible</b>: they agree wherever both are defined, and <span class="m">p ∪ q</span> is their greatest common extension.', '<b>相容</b>：两者在公共定义域上取值一致，<span class="m">p ∪ q</span> 就是它们最弱的公共加细。')
      : bi(`<b>Incompatible</b> (purple outline): they disagree at n = ${clash.join(', ')}, so <span class="m">p ∪ q</span> is not a function.`, `<b>不相容</b>（紫框）：在 n = ${clash.join(', ')} 处取值不同，<span class="m">p ∪ q</span> 不是函数。`));
    okBox($('pfMsg'), msg, compat ? 'ok' : 'bad');
  }
  draw();
})();

/* ================= §3 dense sets ================= */
const X0101 = '010101010101010101';
(function dense() {
  const sets = [
    { en: 'D₂ = {p : 2 ∈ dom p}', zh: 'D₂ = {p : 2 ∈ dom p}', f: s => s.length > 2, dense: true },
    { en: 'D<sub>x</sub>, x = 0101…: {p : p ⊥ x}', zh: 'D<sub>x</sub>，x = 0101…：{p : p ⊥ x}', f: s => !X0101.startsWith(s), dense: true },
    { en: 'D<sub>x</sub>, x = 000…: {p : p ⊥ x}', zh: 'D<sub>x</sub>，x = 000…：{p : p ⊥ x}', f: s => s.includes('1'), dense: true },
    { en: '{p : p ends in 11}', zh: '{p : p 以 11 结尾}', f: s => s.endsWith('11'), dense: true },
    { en: '{p : p(0) = 1}  (not dense)', zh: '{p : p(0) = 1}（不稠密）', f: s => s[0] === '1', dense: false,
      why: ['Every extension of ⟨0⟩ has p(0) = 0. Information already given can never be retracted.', '⟨0⟩ 的任何加细都有 p(0) = 0。已经给出的信息永远收不回来。'] },
    { en: '{p : |dom p| ≤ 2}  (not dense)', zh: '{p : |dom p| ≤ 2}（不稠密）', f: s => s.length <= 2, dense: false,
      why: ['Extensions only grow the domain; once |dom p| ≥ 3 there is no way back.', '加细只会让定义域变大；一旦 |dom p| ≥ 3 就回不去了。'] },
  ];
  let cur = 0, walkTok = 0;
  const T = makeTree($('tree3'), { onClick: probe });
  const sel = $('dSel');
  sets.forEach((S, i) => {
    const b = btn(bilq(S.en, S.zh));
    b.addEventListener('click', () => { cur = i; sel.querySelectorAll('.btn').forEach(x => x.classList.remove('sel')); b.classList.add('sel'); paint(); });
    sel.appendChild(b);
    if (i === 0) b.classList.add('sel');
  });
  function paint() {
    walkTok++;
    const S = sets[cur];
    T.paint(s => (S.f(s) ? 'inD' : ''));
    T.edges(() => '');
    okBox($('tree3Msg'), bi(`Green = members of <span class="m">${S.en}</span>. Click any node to test density below it.`, `绿色＝<span class="m">${S.zh}</span> 的元素。点任意节点，检验它下方的稠密性。`), 'info');
  }
  async function probe(p) {
    const my = ++walkTok;
    const S = sets[cur];
    T.paint(s => (s === p ? 'sel' : S.f(s) ? 'inD' : ''));
    T.edges(() => '');
    const q = F16.firstExt(p, S.f, 5);
    if (q !== null) {
      for (let k = p.length + 1; k <= q.length; k++) {
        await sleep(260);
        if (my !== walkTok) return;
        T.nodes[q.slice(0, k)].edge.setAttribute('class', 'te walk');
      }
      T.nodes[q].g.setAttribute('class', 'tn meet');
      okBox($('tree3Msg'), bi(`From <span class="m">p = ${fmtS(p)}</span> the machine found <span class="m">q = ${fmtS(q)} ≤ p</span> in the set${q === p ? ' (p itself)' : ''}.`, `从 <span class="m">p = ${fmtS(p)}</span> 出发，机器找到了集合中的 <span class="m">q = ${fmtS(q)} ≤ p</span>${q === p ? '（就是 p 本身）' : ''}。`), 'ok');
    } else if (S.dense) {
      const deep = F16.firstExt(p, S.f, 9);
      okBox($('tree3Msg'), bi(`The witness lies below the picture: <span class="m">q = ${fmtS(deep)}</span>. The set is still dense.`, `证据在图的下方：<span class="m">q = ${fmtS(deep)}</span>。这个集合依然稠密。`), 'ok');
    } else {
      T.nodes[p].g.setAttribute('class', 'tn fail');
      okBox($('tree3Msg'), bi(`<b>No</b> <span class="m">q ≤ ${fmtS(p)}</span> is in the set, at any depth. ${S.why[0]} So the set is <b>not dense</b>.`, `<span class="m">${fmtS(p)}</span> 下方任何深度都<b>没有</b>集合中的元素。${S.why[1]}所以这个集合<b>不稠密</b>。`), 'bad');
    }
  }
  paint();
})();

/* ================= §4 generic game ================= */
(function game() {
  const svg = $('game');
  const NC = 14, NR = 8, CS = 34, X0 = 60, Y0 = 46;
  let xs, p, j, autoTok = 0;
  const reqs = [];
  for (let k = 0; k < NR; k++) { reqs.push({ type: 'x', k }); reqs.push({ type: 'dom', n: k }); }
  const reqLabel = r => (r.type === 'x' ? `D<sub>x${sub(r.k)}</sub>: p ⊥ x${sub(r.k)}` : `D${sub(r.n)}: ${r.n} ∈ dom p`);
  function reset() {
    autoTok++;
    xs = [Array(NC).fill('0').join(''), Array(NC).fill('1').join('')];
    while (xs.length < NR) xs.push(Array.from({ length: NC }, rbit).join(''));
    xs = [xs[0], xs[2], xs[1], ...xs.slice(3)];
    p = ''; j = 0;
    advance();
    draw();
  }
  function advance() { while (j < reqs.length && F16.meets(p, reqs[j], xs)) j++; }
  function append(b) {
    if (j >= reqs.length) return;
    if (p.length >= NC) { okBox($('gmMsg'), bi('Out of room in this picture. Press “New list” and try the Cantor move.', '图里放不下了。按“换一份清单”，试试康托尔一步。'), 'warn'); return; }
    p += b;
    advance();
    draw();
  }
  function cantorBit() {
    const r = reqs[j];
    if (r && r.type === 'x') return String(1 - +xs[r.k][p.length]);
    return String(1 - +xs[Math.min(p.length, NR - 1)][p.length]);
  }
  function draw() {
    svg.innerHTML = '';
    const r = reqs[j];
    for (let c = 0; c < NC; c++) txt(svg, X0 + c * CS + CS / 2, Y0 - 10, c, { 'text-anchor': 'middle', 'font-size': 12, fill: '#6b7280' });
    txt(svg, X0 - 10, Y0 - 10, 'n', { 'text-anchor': 'end', 'font-size': 12, fill: '#6b7280' });
    for (let k = 0; k < NR; k++) {
      const y = Y0 + k * CS;
      const met = F16.meets(p, { type: 'x', k }, xs);
      if (r && r.type === 'x' && r.k === k) el('rect', { x: 4, y: y - 1, width: X0 + NC * CS + 2, height: CS, rx: 8, fill: '#e7ecff' }, svg);
      txt(svg, X0 - 10, y + CS / 2 + 5, 'x' + sub(k), { 'text-anchor': 'end', 'font-size': 14, 'font-weight': 700 });
      const fd = !met ? -1 : (p.length > k && p[k] !== xs[k][k] ? k : F16.firstDiff(p, xs[k]));
      for (let c = 0; c < NC; c++) {
        const b = xs[k][c];
        el('rect', { x: X0 + c * CS + 2, y: y + 2, width: CS - 4, height: CS - 4, rx: 6, fill: b === '1' ? '#d3f9d8' : '#ffe3e3', opacity: met && c !== fd ? 0.45 : 1,
          stroke: c === fd ? '#ae3ec9' : k === c ? '#c9a3d6' : 'none', 'stroke-width': c === fd ? 3 : 1.5, 'stroke-dasharray': c === fd ? '' : '3 3' }, svg);
        txt(svg, X0 + c * CS + CS / 2, y + CS / 2 + 5, b, { 'text-anchor': 'middle', 'font-size': 14, opacity: met && c !== fd ? 0.5 : 1 });
      }
      if (met) txt(svg, X0 + NC * CS + 6, y + CS / 2 + 5, `g ≠ x${sub(k)}`, { 'font-size': 12, 'font-weight': 700, fill: '#ae3ec9', class: 'fadein' });
    }
    txt(svg, X0 - 10, Y0 + NR * CS + 16, '⋮', { 'text-anchor': 'end', 'font-size': 14, fill: '#999' });
    // p row
    const yp = Y0 + NR * CS + 34;
    txt(svg, X0 - 10, yp + CS / 2 + 5, 'p', { 'text-anchor': 'end', 'font-size': 16, 'font-weight': 800, fill: '#ae3ec9' });
    for (let c = 0; c < NC; c++) {
      const b = p[c];
      el('rect', { x: X0 + c * CS + 2, y: yp + 2, width: CS - 4, height: CS - 4, rx: 6, fill: b === undefined ? '#fff' : '#f8e7fc', stroke: '#ae3ec9', 'stroke-width': b === undefined ? 1 : 2, 'stroke-dasharray': b === undefined ? '3 3' : '' }, svg);
      if (b !== undefined) txt(svg, X0 + c * CS + CS / 2, yp + CS / 2 + 5, b, { 'text-anchor': 'middle', 'font-size': 15, 'font-weight': 800, fill: '#ae3ec9' });
    }
    if (r && r.type === 'dom') el('rect', { x: X0 + r.n * CS, y: yp - 2, width: CS, height: CS + 4, rx: 7, fill: 'none', stroke: '#3b5bdb', 'stroke-width': 3 }, svg);
    if (j >= reqs.length) txt(svg, X0, yp + CS + 26, 'g = ⋃G = ' + p + '…   ∉ {x₀, x₁, …}', { 'font-size': 14, 'font-weight': 700, fill: '#ae3ec9' });
    // requirements list
    let h = `<div class="muted" style="font-size:13px;margin-bottom:4px">${bil('Dense sets of M, listed', 'M 的稠密集清单')}</div>`;
    reqs.forEach((rq, i) => {
      h += `<div class="req ${i < j ? 'met' : i === j ? 'cur' : ''}"><span class="ic">${i < j ? '✓' : i === j ? '▶' : '·'}</span><span class="m">E${sub(i)}</span> ${reqLabel(rq)}</div>`;
    });
    h += `<div class="req"><span class="ic">⋮</span>${bil('…and every other dense set in M', '……以及 M 中其余所有稠密集')}</div>`;
    $('gmReqs').innerHTML = h;
    const box = $('gmMsg');
    if (j >= reqs.length) {
      okBox(box, bi(`All listed requirements met with <span class="m">p = ${fmtS(p)}</span>. Continue forever down the whole list: <span class="m">G = {q : q ⊆ g}</span> is M-generic, and <span class="m">g = ⋃G</span> differs from every <span class="m">xₖ</span> (purple cells). If you used only Cantor moves, p is exactly Cantor\'s diagonal real d(k) = 1 − x<sub>k</sub>(k), and the purple cells run down the diagonal.`,
        `清单上的要求全部满足，<span class="m">p = ${fmtS(p)}</span>。沿整份清单无限地做下去：<span class="m">G = {q : q ⊆ g}</span> 就是 M-脱殊滤子，<span class="m">g = ⋃G</span> 与每个 <span class="m">xₖ</span> 都不同（紫框格）。如果你只用康托尔一步，p 恰好就是康托尔的对角线实数 d(k) = 1 − x<sub>k</sub>(k)，紫框格沿对角线排开。`), 'ok');
    } else if (r.type === 'x') {
      okBox(box, bi(`Current requirement: get <span class="m">p</span> incompatible with <span class="m">x${sub(r.k)}</span> (highlighted row). Right now <span class="m">p = ${fmtS(p)}</span> is still an initial segment of it. Append a bit that disagrees: the Cantor move appends <span class="m">1 − x${sub(r.k)}(${p.length}) = ${cantorBit()}</span>.`,
        `当前要求：让 <span class="m">p</span> 与 <span class="m">x${sub(r.k)}</span>（高亮行）不相容。现在 <span class="m">p = ${fmtS(p)}</span> 仍是它的前段。添一位与它相反的：康托尔一步会添 <span class="m">1 − x${sub(r.k)}(${p.length}) = ${cantorBit()}</span>。`), 'info');
    } else {
      okBox(box, bi(`Current requirement: decide bit ${r.n} (blue box). Any bit will do.`, `当前要求：确定第 ${r.n} 位（蓝框），添 0 或 1 都行。`), 'info');
    }
  }
  $('gm0').addEventListener('click', () => { autoTok++; append('0'); });
  $('gm1').addEventListener('click', () => { autoTok++; append('1'); });
  $('gmC').addEventListener('click', () => { autoTok++; append(cantorBit()); });
  $('gmReset').addEventListener('click', reset);
  $('gmAuto').addEventListener('click', async () => {
    reset();
    const my = autoTok;
    while (j < reqs.length && p.length < NC) {
      await sleep(550);
      if (my !== autoTok) return;
      append(cantorBit());
    }
  });
  reset();
})();

/* ================= §5 Rasiowa–Sikorski ================= */
(function rs() {
  const svg = $('rsSvg');
  const steps = [...document.querySelectorAll('#rsSteps .step')];
  const chain = ['', '1', '10', '100', '1001', '10011'];
  const Ds = [['0 ∈ dom p', '0 ∈ dom p'], ['p ⊥ 111…', 'p ⊥ 111…'], ['2 ∈ dom p', '2 ∈ dom p'], ['p has two 1s', 'p 有两个 1'], ['4 ∈ dom p', '4 ∈ dom p']];
  let k = 0, tok = 0;
  async function draw() {
    const my = ++tok;
    svg.innerHTML = '';
    if (k >= 1) {
      txt(svg, 10, 22, 'dense sets in M · M 中的稠密集', { 'font-size': 11, fill: '#6b7280' });
      Ds.forEach((d, i) => { const t = txt(svg, 10, 70 + i * 48, `D${sub(i)}: ${d[0]}`, { 'font-size': 12, fill: '#3b5bdb', 'font-weight': 700, class: 'fadein' }); t.style.animationDelay = i * 0.1 + 's'; });
      txt(svg, 10, 70 + 5 * 48 - 8, '⋮', { 'font-size': 14, fill: '#3b5bdb' });
    }
    if (k >= 3) {
      el('rect', { x: 150, y: 12, width: 140, height: 296, rx: 14, fill: 'rgba(174,62,201,.08)', stroke: '#ae3ec9', 'stroke-dasharray': '5 4', class: 'fadein' }, svg);
      txt(svg, 220, 322, 'G = ↑{pₙ} · 链的上闭包', { 'font-size': 11, 'text-anchor': 'middle', fill: '#ae3ec9', 'font-weight': 700 });
    }
    if (k >= 2) {
      for (let i = 0; i < chain.length; i++) {
        if (my !== tok) return;
        const y = 22 + i * 48;
        const g = el('g', { class: 'pop' }, svg);
        el('rect', { x: 170, y, width: 100, height: 30, rx: 8, fill: '#fff', stroke: '#ae3ec9', 'stroke-width': 2 }, g);
        txt(g, 220, y + 20, `p${sub(i)} = ${fmtS(chain[i])}`, { 'font-size': 12, 'text-anchor': 'middle', 'font-weight': 700 });
        if (i > 0) {
          txt(svg, 220, y - 5, '≥', { 'font-size': 13, 'text-anchor': 'middle', fill: '#6b7280', transform: `rotate(90 220 ${y - 9})` });
          el('line', { x1: 120, y1: 70 + (i - 1) * 48 - 4, x2: 168, y2: y + 15, stroke: k >= 4 ? '#2f9e44' : '#c3c9f5', 'stroke-width': k >= 4 ? 2.5 : 1.5, 'marker-end': '' }, svg);
          if (k >= 4) txt(svg, 280, y + 20, `∈ D${sub(i - 1)} ✓`, { 'font-size': 12, fill: '#2f9e44', 'font-weight': 700 });
        }
        if (k === 2) await sleep(380);
      }
    }
    if (k >= 5) {
      // mini tree: p, p0, p1
      const bx = 300, by = 30;
      el('rect', { x: bx + 30, y: by - 20, width: 88, height: 152, rx: 10, fill: '#fff', stroke: '#e3dfd3' }, svg);
      txt(svg, bx + 74, by - 4, 'G ∈ M ?', { 'font-size': 12, 'text-anchor': 'middle', 'font-weight': 700 });
      el('line', { x1: bx + 74, y1: by + 20, x2: bx + 50, y2: by + 70, stroke: '#2f9e44', 'stroke-width': 3 }, svg);
      el('line', { x1: bx + 74, y1: by + 20, x2: bx + 98, y2: by + 70, stroke: '#e03131', 'stroke-width': 2, 'stroke-dasharray': '4 3' }, svg);
      el('circle', { cx: bx + 74, cy: by + 20, r: 9, fill: '#ae3ec9' }, svg);
      el('circle', { cx: bx + 50, cy: by + 70, r: 9, fill: '#2f9e44' }, svg);
      el('circle', { cx: bx + 98, cy: by + 70, r: 9, fill: '#ffe3e3', stroke: '#e03131', 'stroke-width': 2 }, svg);
      txt(svg, bx + 74, by + 24, 'p', { 'font-size': 10, 'text-anchor': 'middle', fill: '#fff' });
      txt(svg, bx + 50, by + 92, '∈G', { 'font-size': 11, 'text-anchor': 'middle', fill: '#2f9e44' });
      txt(svg, bx + 98, by + 92, '∉G', { 'font-size': 11, 'text-anchor': 'middle', fill: '#e03131' });
      txt(svg, bx + 74, by + 116, 'P∖G dense', { 'font-size': 10.5, 'text-anchor': 'middle', fill: '#e03131', 'font-weight': 700 });
      txt(svg, bx + 74, by + 128, 'P∖G 稠密', { 'font-size': 10.5, 'text-anchor': 'middle', fill: '#e03131', 'font-weight': 700 });
    }
    if (k === 0) txt(svg, 210, 165, 'Next step ▶ · 下一步 ▶', { 'font-size': 14, 'text-anchor': 'middle', fill: '#9aa0aa' });
  }
  function sync() { steps.forEach((s, i) => s.classList.toggle('on', i < k)); $('rsNext').disabled = k >= steps.length; draw(); }
  $('rsNext').addEventListener('click', () => { if (k < steps.length) k++; sync(); });
  $('rsAll').addEventListener('click', () => { k = steps.length; sync(); });
  $('rsReset').addEventListener('click', () => { k = 1; sync(); });
  k = 1;
  sync();
})();

/* ================= §6 names ================= */
(function names() {
  const c = F16.chk;
  const mk = (label, pairs) => ({ label, pairs });
  const sigma = mk('σ', [[c(0), '00'], [c(1), '010']]);
  const examples = [
    { en: 'τ₁: a flat name', zh: 'τ₁：一层的名字', tau: mk('τ₁', [[c(0), '0'], [c(1), '1'], [c(2), '01']]) },
    { en: 'τ₂: a nested name', zh: 'τ₂：嵌套的名字', tau: mk('τ₂', [[sigma, '0'], [c(1), '11'], [c(0), '']]) },
    { en: 'ġ↾3: the generic real', zh: 'ġ↾3：脱殊实数', tau: mk('ġ↾3', [[c(0), '1'], [c(1), '_1'], [c(2), '__1']]) },
    { en: '2̌: a check name', zh: '2̌：典范名字', tau: mk('2̌', [[c(0), ''], [c(1), '']]) },
  ];
  let ex = 0, tok = 0;
  const g = { 'g(0)': 0, 'g(1)': 1, 'g(2)': 0 };
  const gStr = () => '' + g['g(0)'] + g['g(1)'] + g['g(2)'];
  const pick = $('nmPick');
  examples.forEach((e, i) => {
    const b = btn(bil(e.en, e.zh));
    b.addEventListener('click', () => { ex = i; pick.querySelectorAll('button').forEach(x => x.classList.remove('sel')); b.classList.add('sel'); draw(); });
    if (i === 0) b.classList.add('sel');
    pick.appendChild(b);
  });
  Switches($('nmSw'), ['g(0)', 'g(1)', 'g(2)'], g, () => draw());

  // layout: check names are leaves
  function layout(tau) {
    let leaf = 0;
    const nodes = [];
    (function walk(n, depth, cond, parent) {
      const node = { n, depth, cond, parent, kids: [] };
      nodes.push(node);
      if (n.chk === undefined && n.pairs.length) {
        n.pairs.forEach(([s, p]) => node.kids.push(walk(s, depth + 1, p, node)));
        node.x = (node.kids[0].x + node.kids[node.kids.length - 1].x) / 2;
      } else node.x = leaf++;
      return node;
    })(tau, 0, null, null);
    return { nodes, leaves: leaf };
  }
  async function draw() {
    const my = ++tok;
    const svg = $('nmSvg');
    svg.innerHTML = '';
    const tau = examples[ex].tau;
    const gs = gStr();
    const inG = F16.inGOf(gs);
    const { nodes, leaves } = layout(tau);
    const W = 860, GX = Math.min(170, (W - 80) / leaves);
    const px = n => 40 + GX / 2 + n.x * GX + (W - 80 - leaves * GX) / 2;
    const py = n => 40 + n.depth * 125;
    const gE = el('g', {}, svg), gN = el('g', {}, svg);
    nodes.forEach(n => {
      if (!n.parent) return;
      const on = inG(n.cond);
      const x1 = px(n.parent), y1 = py(n.parent), x2 = px(n), y2 = py(n);
      n.line = el('line', { x1, y1, x2, y2, stroke: on ? '#2f9e44' : '#cfcabb', 'stroke-width': on ? 3.5 : 2, 'stroke-dasharray': on ? '' : '6 5' }, gE);
      const mx = x1 + (x2 - x1) * 0.58, my2 = y1 + (y2 - y1) * 0.58;
      const lab = fmtC(n.cond);
      const w = Math.max(34, lab.length * 8 + 14);
      el('rect', { x: mx - w / 2, y: my2 - 12, width: w, height: 22, rx: 7, fill: on ? '#d3f9d8' : '#f1efe7', stroke: on ? '#2f9e44' : '#cfcabb' }, gE);
      txt(gE, mx, my2 + 4, lab + (on ? ' ∈G' : ' ∉G'), { 'text-anchor': 'middle', 'font-size': 11.5, 'font-weight': 700, fill: on ? '#1b5e20' : '#8d877a' });
    });
    nodes.forEach(n => {
      n.g = el('g', { transform: `translate(${px(n)},${py(n)})` }, gN);
      el('circle', { r: 20, fill: n.n.chk !== undefined ? '#fff3bf' : '#e7ecff', stroke: n.n.chk !== undefined ? '#f08c00' : '#3b5bdb', 'stroke-width': 2.5 }, n.g);
      txt(n.g, 0, 5, n.n.label, { 'text-anchor': 'middle', 'font-size': 14, 'font-weight': 800 });
      n.vt = txt(n.g, n.kids.length ? 26 : 0, n.kids.length ? 5 : 38, '', { 'text-anchor': n.kids.length ? 'start' : 'middle', 'font-size': 13, 'font-weight': 800, fill: '#ae3ec9' });
    });
    // bottom-up evaluation
    const order = [];
    (function post(n) { n.kids.forEach(post); order.push(n); })(nodes[0]);
    for (const n of order) {
      if (my !== tok) return;
      const v = F16.val(n.n, inG);
      n.vt.textContent = '= ' + F16.pretty(v);
      n.vt.classList.add('pop');
      if (n.kids.length) await sleep(260);
    }
    const v = F16.val(tau, inG);
    const used = [...new Set(nodes.filter(n => n.parent).map(n => n.cond))];
    $('nmG').innerHTML = 'G = {p : p ⊆ g}: ' + used.map(c => `${fmtC(c)} ${inG(c) ? '✓' : '✗'}`).join(' · ');
    const extra = ex === 2 ? bi(' This name works for every G: <span class="m">val(ġ↾3, G) = {n < 3 : g(n) = 1}</span>. The full name <span class="m">ġ = {(ň, {(n,1)}) : n ∈ ω}</span> evaluates to the set coding g.',
      ' 这个名字对每个 G 都管用：<span class="m">val(ġ↾3, G) = {n < 3 : g(n) = 1}</span>。完整的名字 <span class="m">ġ = {(ň, {(n,1)}) : n ∈ ω}</span> 取值就是编码 g 的那个集合。')
      : ex === 3 ? bi(' Every condition is 𝟙 ∈ G, so the value never changes: <span class="m">val(x̌, G) = x</span>.', ' 每个条件都是 𝟙 ∈ G，所以取值永远不变：<span class="m">val(x̌, G) = x</span>。')
        : bi(' Flip the switches: the same name, a different G, a different set.', ' 拨动开关：同一个名字，换一个 G，就是另一个集合。');
    okBox($('nmOut'), `<span class="m">g = ${gs}…</span> &nbsp; ⇒ &nbsp; <span class="bigval">val(${tau.label}, G) = ${F16.pretty(v)}</span>` + extra, 'ok');
  }
  draw();
})();

/* ================= §7 forcing relation ================= */
(function forcing() {
  const NB = 5;
  const stmts = [
    { en: 'ġ(2) = 1', zh: 'ġ(2) = 1', f: b => b[2] === 1 },
    { en: 'ġ(0) = ġ(1)', zh: 'ġ(0) = ġ(1)', f: b => b[0] === b[1] },
    { en: 'ġ(0)+ġ(1)+ġ(2)+ġ(3) ≥ 3', zh: 'ġ(0)+ġ(1)+ġ(2)+ġ(3) ≥ 3', f: b => b[0] + b[1] + b[2] + b[3] >= 3 },
    { en: 'ġ ≠ x̌  (x = 0101… ∈ M)', zh: 'ġ ≠ x̌（x = 0101… ∈ M）', all: 1,
      note: ['Every node is green. Even 𝟙 = ∅ forces ġ ≠ x̌: the set D<sub>x</sub> is dense and in M, so every generic meets it.', '所有节点都是绿的，连 𝟙 = ∅ 都力迫 ġ ≠ x̌：D<sub>x</sub> 是 M 中的稠密集，每个脱殊滤子都会碰到它。'] },
    { en: 'ġ has infinitely many 1s', zh: 'ġ 有无穷多个 1', all: 1,
      note: ['Forced by 𝟙: for each n, {p : ∃m ≥ n p(m) = 1} is dense. No finite condition “contains” the witness, yet all of them force it.', '被 𝟙 力迫：对每个 n，{p : ∃m ≥ n p(m) = 1} 稠密。没有哪个有限条件“含有”证据，可每个条件都力迫它。'] },
    { en: 'ġ ∈ M', zh: 'ġ ∈ M', all: 0,
      note: ['Every node is red: 𝟙 ⊩ ġ ∉ M. Truth Lemma with §4: g differs from every real of M. (M itself is not an element of M, so “ġ ∉ M” here abbreviates the family of statements 𝟙 ⊩ ġ ≠ x̌, one for each real x ∈ M.)', '所有节点都是红的：𝟙 ⊩ ġ ∉ M。这就是 §4 的结论配上真值引理：g 与 M 的每个实数都不同。（M 本身不是 M 的元素，所以这里的“ġ ∉ M”是一族命题的简写：对 M 中每个实数 x，𝟙 ⊩ ġ ≠ x̌。）'] },
  ];
  let cur = 0, path = null;
  const T = makeTree($('tree7'), { onClick: s => { path = s; render(); } });
  const dec = (s, S) => (S.all !== undefined ? S.all : F16.decide(s, S.f, NB));
  const pick = $('fsPick');
  stmts.forEach((S, i) => {
    const b = btn(`<span class="m">${bilq(S.en, S.zh)}</span>`);
    b.addEventListener('click', () => { cur = i; path = null; pick.querySelectorAll('button').forEach(x => x.classList.remove('sel')); b.classList.add('sel'); render(); });
    if (i === 0) b.classList.add('sel');
    pick.appendChild(b);
  });
  $('fsReset').addEventListener('click', () => { path = null; render(); });
  function render() {
    const S = stmts[cur];
    T.paint(s => { const d = dec(s, S); return (d === 1 ? 'yes' : d === 0 ? 'no' : 'und') + (path !== null && path.startsWith(s) ? ' path' : ''); });
    T.edges(s => (path !== null && path.startsWith(s) ? 'path' : ''));
    const box = $('fsMsg');
    if (S.all !== undefined) { okBox(box, bi(S.note[0], S.note[1]), S.all ? 'ok' : 'bad'); return; }
    if (path === null) {
      okBox(box, bi('Grey nodes are undecided. Notice: every grey node has green or red nodes below it, so deciding conditions are <b>dense</b>. Click a node to walk a path to it.', '灰色节点尚未判定。注意：每个灰色节点下方都有绿或红的节点，所以“能判定 φ 的条件”是<b>稠密</b>的。点一个节点，走到它的路径就会画出来。'), 'info');
      return;
    }
    let k = -1;
    for (let i = 0; i <= path.length; i++) if (dec(path.slice(0, i), S) !== null) { k = i; break; }
    if (k < 0) okBox(box, bi(`Along the path to <span class="m">${fmtS(path)}</span>, φ is not decided yet. Keep going down: genericity guarantees you eventually hit a deciding condition.`, `沿着到 <span class="m">${fmtS(path)}</span> 的路径，φ 还没被判定。继续往下走：脱殊性保证你迟早会碰到一个能判定它的条件。`), 'info');
    else {
      const q = path.slice(0, k), d = dec(q, S);
      okBox(box, bi(`Decided at <span class="m">${fmtS(q)}</span> (depth ${k}): <span class="m">${fmtS(q)} ⊩ ${d ? '' : '¬'}φ</span>. Every stronger condition agrees, so if the generic goes this way, the Truth Lemma gives <span class="m">M[G] ⊨ ${d ? '' : '¬'}φ</span>.`,
        `在 <span class="m">${fmtS(q)}</span>（深度 ${k}）处被判定：<span class="m">${fmtS(q)} ⊩ ${d ? '' : '¬'}φ</span>。更强的条件都与之一致，所以只要脱殊滤子走这条路，由真值引理就有 <span class="m">M[G] ⊨ ${d ? '' : '¬'}φ</span>。`), d ? 'ok' : 'bad');
    }
  }
  render();
})();

/* ================= §8 axioms ================= */
(function axioms() {
  const tiles = [
    ['=', 'Extensionality', '外延公理', 'M[G] is transitive, and extensionality holds in every transitive class (it is Δ₀).', 'M[G] 是传递的，而外延公理在任何传递类中都成立（它是 Δ₀ 的）。'],
    ['∈↓', 'Foundation', '正则公理', 'M[G] ⊆ V is a set of well-founded sets; ∈ is well-founded on it.', 'M[G] ⊆ V，其元素都是良基集，∈ 在其上良基。'],
    ['{ , }', 'Pairing', '配对公理', 'The name {(σ,𝟙),(τ,𝟙)} ∈ M evaluates to {σ<sub>G</sub>, τ<sub>G</sub>}.', '名字 {(σ,𝟙),(τ,𝟙)} ∈ M 的取值就是 {σ<sub>G</sub>, τ<sub>G</sub>}。'],
    ['⋃', 'Union', '并集公理', '{(π,𝟙) : ∃σ ∈ dom τ, π ∈ dom σ} names a superset of ⋃τ<sub>G</sub>; cut it down by Separation.', '{(π,𝟙) : ∃σ ∈ dom τ, π ∈ dom σ} 命名了 ⋃τ<sub>G</sub> 的一个超集，再用分离公理切出来。'],
    ['ω', 'Infinity', '无穷公理', 'ω ∈ M ⊆ M[G].', 'ω ∈ M ⊆ M[G]。'],
    ['{x∈a : φ}', 'Separation ⚑', '分离公理 ⚑', 'ρ = {(σ,p) : σ ∈ dom τ, p ⊩ (σ ∈ τ ∧ φ(σ))}. ρ ∈ M by Definability; ρ<sub>G</sub> = {x ∈ τ<sub>G</sub> : φ(x)} by the Truth Lemma.', 'ρ = {(σ,p) : σ ∈ dom τ, p ⊩ (σ ∈ τ ∧ φ(σ))}。由可定义性 ρ ∈ M；由真值引理 ρ<sub>G</sub> = {x ∈ τ<sub>G</sub> : φ(x)}。'],
    ['𝒫', 'Power set ⚑', '幂集公理 ⚑', 'ρ = {(θ,𝟙) : θ ⊆ dom τ × P} (power set taken in M). Each y ⊆ τ<sub>G</sub> in M[G] equals θ<sub>G</sub> for θ = {(σ,p) : σ ∈ dom τ, p ⊩ σ ∈ μ} ∈ M, where μ names y.', 'ρ = {(θ,𝟙) : θ ⊆ dom τ × P}（幂集在 M 中取）。M[G] 中每个 y ⊆ τ<sub>G</sub> 都等于 θ<sub>G</sub>，其中 θ = {(σ,p) : σ ∈ dom τ, p ⊩ σ ∈ μ} ∈ M，μ 是 y 的名字。'],
    ['F[a]', 'Replacement ⚑', '替换公理 ⚑', 'Use Replacement in M on the forcing relation to bound the ranks of names needed for the values; collect them into one name.', '对力迫关系在 M 中用替换公理，给所需名字的秩找一个上界，再把它们收进一个名字。'],
    ['≺', 'Choice', '选择公理', 'In M well-order dom τ as {σ<sub>ξ</sub> : ξ < λ}. Then ξ ↦ (σ<sub>ξ</sub>)<sub>G</sub> maps λ onto a superset of τ<sub>G</sub>, giving a well-order in M[G].', '在 M 中把 dom τ 良序为 {σ<sub>ξ</sub> : ξ < λ}。则 ξ ↦ (σ<sub>ξ</sub>)<sub>G</sub> 把 λ 映满 τ<sub>G</sub> 的一个超集，由此在 M[G] 中得到良序。'],
    ['Ord', 'Same ordinals', '序数不变', 'rank(τ<sub>G</sub>) ≤ rank(τ) by induction. So every ordinal of M[G] is < o(M); and M ⊆ M[G].', '归纳可证 rank(τ<sub>G</sub>) ≤ rank(τ)。所以 M[G] 的每个序数都 < o(M)；又 M ⊆ M[G]。'],
    ['⊆', 'M ⊆ M[G] ∋ G, minimal', 'M ⊆ M[G] ∋ G，极小性', 'x = val(x̌,G), G = val(Γ,G). If N ⊇ M is a transitive model of ZF with G ∈ N, then N computes val(τ,G) by the same recursion, so M[G] ⊆ N.', 'x = val(x̌,G)，G = val(Γ,G)。若 N ⊇ M 是含 G 的 ZF 传递模型，N 能用同一个递归算出 val(τ,G)，所以 M[G] ⊆ N。'],
  ];
  const box = $('axTiles');
  const count = () => { const n = box.querySelectorAll('.flip.open').length; $('axCount').innerHTML = `${n} / ${tiles.length} ${bil('opened', '已展开')} &nbsp; ⚑ = ${bil('needs the Forcing Theorem', '需要力迫定理')}`; };
  tiles.forEach(t => {
    const d = document.createElement('div');
    d.className = 'flip';
    d.innerHTML = `<div class="front"><span class="sym">${t[0]}</span>${bil(t[1], t[2])}</div><div class="back">${bi(t[3], t[4])}</div>`;
    d.addEventListener('click', () => { d.classList.toggle('open'); count(); });
    box.appendChild(d);
  });
  $('axAll').addEventListener('click', () => { box.querySelectorAll('.flip').forEach(d => d.classList.add('open')); count(); });
  count();
})();

/* ================= §9 grid of ℵ₂ Cohen reals ================= */
(function grid() {
  const svg = $('grid');
  const cols = ['0', '1', '2', '3', 'ω', 'ω+1', 'ω·2', 'ω²', 'ω^ω', 'ε₀', 'ω₁', 'ω₁+1', 'ω₁·2', 'ω₁²', 'ω₁^ω'];
  const NC = cols.length, NR = 10, CW = 50, CH = 25, X0 = 70, Y0 = 52;
  let cells = {}, selCols = [], tok = 0;
  const key = (a, n) => a + ',' + n;
  const col = a => Array.from({ length: NR }, (_, n) => cells[key(a, n)]);
  function draw() {
    svg.innerHTML = '';
    txt(svg, X0 + NC * CW / 2, 16, 'α < ω₂  (columns · 列)  →', { 'text-anchor': 'middle', 'font-size': 12, fill: '#6b7280' });
    txt(svg, X0 + NC * CW + 14, Y0 + 4 * CH, '… ω₂', { 'font-size': 14, fill: '#9aa0aa', 'font-weight': 700 });
    for (let a = 0; a < NC; a++) {
      const sel = selCols.includes(a);
      const g = el('g', { style: 'cursor:pointer' }, svg);
      el('rect', { x: X0 + a * CW + 2, y: Y0 - 26, width: CW - 4, height: 22, rx: 6, fill: sel ? (selCols[0] === a ? '#3b5bdb' : '#f08c00') : '#f1efe7' }, g);
      txt(g, X0 + a * CW + CW / 2, Y0 - 10, cols[a], { 'text-anchor': 'middle', 'font-size': 11.5, 'font-weight': 700, fill: sel ? '#fff' : '#1f2430' });
      g.addEventListener('click', () => {
        if (selCols.includes(a)) selCols = selCols.filter(x => x !== a);
        else { selCols.push(a); if (selCols.length > 2) selCols.shift(); }
        draw();
      });
      if (sel) el('rect', { x: X0 + a * CW + 1, y: Y0, width: CW - 2, height: NR * CH, rx: 6, fill: 'none', stroke: selCols[0] === a ? '#3b5bdb' : '#f08c00', 'stroke-width': 2.5 }, svg);
    }
    let diffRow = -1;
    if (selCols.length === 2) { const [A, B] = selCols.map(col); diffRow = A.findIndex((v, n) => v !== undefined && B[n] !== undefined && v !== B[n]); }
    for (let n = 0; n < NR; n++) {
      txt(svg, X0 - 10, Y0 + n * CH + CH / 2 + 4, 'n=' + n, { 'text-anchor': 'end', 'font-size': 11, fill: '#6b7280' });
      if (n === diffRow) el('rect', { x: X0 - 2, y: Y0 + n * CH, width: NC * CW + 4, height: CH, rx: 5, fill: 'none', stroke: '#ae3ec9', 'stroke-width': 2, 'stroke-dasharray': '5 3' }, svg);
      for (let a = 0; a < NC; a++) {
        const v = cells[key(a, n)];
        el('rect', { x: X0 + a * CW + 4, y: Y0 + n * CH + 2, width: CW - 8, height: CH - 4, rx: 4, fill: v === undefined ? '#fbfaf6' : v ? '#d3f9d8' : '#ffe3e3', stroke: v === undefined ? '#e3dfd3' : 'none' }, svg);
        if (v !== undefined) txt(svg, X0 + a * CW + CW / 2, Y0 + n * CH + CH / 2 + 4, v, { 'text-anchor': 'middle', 'font-size': 11, fill: v ? '#1b5e20' : '#8a1c1c' });
      }
    }
    txt(svg, X0 - 10, Y0 + NR * CH + 14, '⋮', { 'text-anchor': 'end', 'font-size': 14, fill: '#999' });
    txt(svg, X0, Y0 + NR * CH + 20, 'each column g_α = a real · 每一列 g_α 都是一个实数', { 'font-size': 11.5, fill: '#6b7280' });
    $('gridSep').disabled = selCols.length !== 2;
    const filled = Object.keys(cells).length;
    let msg = bi(`${filled} cells decided so far (each condition is finite; the generic decides all of them).`, `目前已确定 ${filled} 个格（每个条件都是有限的，脱殊滤子最终确定所有格）。`);
    if (selCols.length === 2) {
      const [a, b] = selCols;
      msg += ' ' + (diffRow >= 0
        ? bi(`Columns ${cols[a]} and ${cols[b]} already differ at n = ${diffRow} (purple row): <span class="m">g<sub>${cols[a]}</sub> ≠ g<sub>${cols[b]}</sub></span>.`, `第 ${cols[a]} 列与第 ${cols[b]} 列在 n = ${diffRow} 处已经不同（紫色行）：<span class="m">g<sub>${cols[a]}</sub> ≠ g<sub>${cols[b]}</sub></span>。`)
        : bi(`Columns ${cols[a]} and ${cols[b]} are not separated yet. Press “Meet D<sub>αβ</sub>”.`, `第 ${cols[a]} 列与第 ${cols[b]} 列还没分开，按“碰 D<sub>αβ</sub>”。`));
    } else msg += ' ' + bi('Click two column headers to compare.', '点两个列标题进行比较。');
    okBox($('gridMsg'), msg, 'info');
  }
  function addRandom(k) {
    const empty = [];
    for (let a = 0; a < NC; a++) for (let n = 0; n < NR; n++) if (cells[key(a, n)] === undefined) empty.push([a, n]);
    shuffle(empty).slice(0, k).forEach(([a, n]) => { cells[key(a, n)] = Math.random() < 0.5 ? 0 : 1; });
    return empty.length;
  }
  $('gridStep').addEventListener('click', () => { tok++; addRandom(1 + Math.floor(Math.random() * 3)); draw(); });
  $('gridRun').addEventListener('click', async () => {
    const my = ++tok;
    while (addRandom(4) > 0) { draw(); await sleep(40); if (my !== tok) return; }
    draw();
  });
  $('gridSep').addEventListener('click', () => {
    tok++;
    const [a, b] = selCols;
    const A = col(a), B = col(b);
    if (A.some((v, n) => v !== undefined && B[n] !== undefined && v !== B[n])) { draw(); return; }
    const n = A.findIndex((v, n) => v === undefined || B[n] === undefined);
    if (n < 0) {
      draw();
      okBox($('gridMsg'), bi(`Within these ${NR} rows the two columns agree. D<sub>αβ</sub> is still met: the separating n lies further down (n ≥ ${NR}), where the generic decided them differently.`, `在这 ${NR} 行里两列完全一样。但 D<sub>αβ</sub> 照样被碰到：分开它们的 n 在更下面（n ≥ ${NR}），脱殊滤子在那里给了它们不同的值。`), 'warn');
      return;
    }
    if (A[n] === undefined && B[n] === undefined) { cells[key(a, n)] = 0; cells[key(b, n)] = 1; }
    else if (A[n] === undefined) cells[key(a, n)] = 1 - B[n];
    else cells[key(b, n)] = 1 - A[n];
    draw();
  });
  $('gridReset').addEventListener('click', () => { tok++; cells = {}; selCols = []; draw(); });
  selCols = [4, 10];
  draw();
})();

/* ================= §9 Δ-system ================= */
(function delta() {
  const svg = $('dsSvg');
  const coords = [];
  for (let a = 0; a < 7; a++) for (let n = 0; n < 2; n++) coords.push([a, n]);
  const NCo = coords.length, CW = 50, RH = 28, X0 = 90, Y0 = 46;
  let fam, vals, found = null, pair = null;
  function gen() {
    const ids = shuffle([...Array(NCo).keys()]);
    const root = ids.slice(0, 2), pool = ids.slice(2);
    fam = [];
    for (let i = 0; i < 5; i++) fam.push([...root, ...pool.splice(0, Math.random() < 0.5 ? 1 : 2)]);
    for (let i = 0; i < 3; i++) fam.push(shuffle([...Array(NCo).keys()]).slice(0, 3));
    fam = shuffle(fam).map(s => s.sort((x, y) => x - y));
    vals = fam.map(s => Object.fromEntries(s.map(c => [c, Math.random() < 0.5 ? 0 : 1])));
    found = null; pair = null;
    draw();
    okBox($('dsMsg'), bi('Eight conditions in <span class="m">Fn(ω₂ × ω, 2)</span>, each with a finite domain of coordinates <span class="m">(α, n)</span>. Step 1 looks for a Δ-system among the domains.', '<span class="m">Fn(ω₂ × ω, 2)</span> 中的八个条件，各有一个由坐标 <span class="m">(α, n)</span> 组成的有限定义域。第 1 步在这些定义域中找 Δ-系统。'), 'info');
  }
  function draw() {
    svg.innerHTML = '';
    const root = found ? found.root : [];
    coords.forEach(([a, n], c) => {
      if (root.includes(c)) el('rect', { x: X0 + c * CW + 1, y: Y0 - 30, width: CW - 2, height: fam.length * RH + 34 + (pair ? RH + 14 : 0), rx: 8, fill: '#fff3bf', stroke: '#f08c00', 'stroke-width': 2 }, svg);
      txt(svg, X0 + c * CW + CW / 2, Y0 - 10, `(${a},${n})`, { 'text-anchor': 'middle', 'font-size': 11, fill: '#6b7280' });
    });
    fam.forEach((s, i) => {
      const y = Y0 + i * RH;
      const inD = !found || found.idx.includes(i);
      const inP = pair && pair.includes(i);
      if (inP) el('rect', { x: 6, y: y, width: X0 + NCo * CW, height: RH, rx: 7, fill: 'none', stroke: '#3b5bdb', 'stroke-width': 3 }, svg);
      txt(svg, X0 - 12, y + RH / 2 + 5, 'p' + sub(i), { 'text-anchor': 'end', 'font-size': 14, 'font-weight': 700, opacity: inD ? 1 : 0.3 });
      for (let c = 0; c < NCo; c++) {
        const v = vals[i][c];
        el('rect', { x: X0 + c * CW + 5, y: y + 3, width: CW - 10, height: RH - 6, rx: 5, fill: v === undefined ? '#f6f4ee' : v ? '#d3f9d8' : '#ffe3e3', opacity: inD ? 1 : 0.25 }, svg);
        if (v !== undefined) txt(svg, X0 + c * CW + CW / 2, y + RH / 2 + 5, v, { 'text-anchor': 'middle', 'font-size': 12, 'font-weight': 700, opacity: inD ? 1 : 0.3 });
      }
    });
    if (pair) {
      const y = Y0 + fam.length * RH + 14;
      const u = Object.assign({}, vals[pair[0]], vals[pair[1]]);
      txt(svg, X0 - 12, y + RH / 2 + 5, `p${sub(pair[0])}∪p${sub(pair[1])}`, { 'text-anchor': 'end', 'font-size': 12, 'font-weight': 800, fill: '#3b5bdb' });
      for (let c = 0; c < NCo; c++) {
        const v = u[c];
        el('rect', { x: X0 + c * CW + 5, y: y + 3, width: CW - 10, height: RH - 6, rx: 5, fill: v === undefined ? '#f6f4ee' : v ? '#d3f9d8' : '#ffe3e3', stroke: v === undefined ? 'none' : '#3b5bdb', 'stroke-width': 1.5, class: 'pop' }, svg);
        if (v !== undefined) txt(svg, X0 + c * CW + CW / 2, y + RH / 2 + 5, v, { 'text-anchor': 'middle', 'font-size': 12, 'font-weight': 700 });
      }
    }
  }
  const fmtCo = c => `(${coords[c][0]},${coords[c][1]})`;
  $('dsNew').addEventListener('click', gen);
  $('dsFind').addEventListener('click', () => {
    found = F16.largestDelta(fam);
    pair = null;
    draw();
    if (!found) { okBox($('dsMsg'), bi('No Δ-system of size ≥ 3 here; try a new family.', '这里没有大小 ≥ 3 的 Δ-系统，换一族试试。'), 'warn'); return; }
    okBox($('dsMsg'), bi(`Rows ${found.idx.map(i => 'p' + sub(i)).join(', ')} form a Δ-system: any two of their domains meet in exactly the root <span class="m">r = {${found.root.map(fmtCo).join(', ')}}</span> (gold). The Δ-system lemma promises such a subfamily, <b>uncountable</b>, inside any uncountable family.`,
      `${found.idx.map(i => 'p' + sub(i)).join('、')} 构成 Δ-系统：任两行的定义域恰好交于根 <span class="m">r = {${found.root.map(fmtCo).join(', ')}}</span>（金色）。Δ-系统引理保证：任何不可数族里都有这样一个<b>不可数</b>子族。`), 'info');
  });
  $('dsPig').addEventListener('click', () => {
    if (!found) $('dsFind').click();
    if (!found) return;
    const groups = {};
    found.idx.forEach(i => { const k = found.root.map(c => vals[i][c]).join(''); (groups[k] = groups[k] || []).push(i); });
    const g = Object.values(groups).find(x => x.length >= 2);
    if (!g) { pair = null; draw(); okBox($('dsMsg'), bi(`Here ${found.idx.length} conditions but ${2 ** found.root.length} patterns on the root: the pigeonhole may fail in a finite example. With uncountably many conditions it cannot fail.`, `这里只有 ${found.idx.length} 个条件，而根上有 ${2 ** found.root.length} 种取法：有限例子里抽屉原理可能不够用；条件有不可数多个时就一定够用。`), 'warn'); return; }
    pair = g.slice(0, 2);
    draw();
    okBox($('dsMsg'), bi(`Only <span class="m">2<sup>|r|</sup> = ${2 ** found.root.length}</span> possible patterns on the root, but ${found.idx.length} conditions: <span class="m">p${sub(pair[0])}</span> and <span class="m">p${sub(pair[1])}</span> agree on <span class="m">r</span>. Off the root their domains are disjoint, so <span class="m">p${sub(pair[0])} ∪ p${sub(pair[1])}</span> is a condition: they are <b>compatible</b>. Hence no uncountable antichain: <b>ccc</b>.`,
      `根上只有 <span class="m">2<sup>|r|</sup> = ${2 ** found.root.length}</span> 种取法，却有 ${found.idx.length} 个条件：<span class="m">p${sub(pair[0])}</span> 与 <span class="m">p${sub(pair[1])}</span> 在 <span class="m">r</span> 上取值相同。根之外它们的定义域互不相交，所以 <span class="m">p${sub(pair[0])} ∪ p${sub(pair[1])}</span> 是一个条件：二者<b>相容</b>。因此不存在不可数反链，即 <b>ccc</b>。`), 'ok');
  });
  gen();
})();

/* ================= §10 flowchart ================= */
(function flow() {
  const svg = $('flow');
  const B = [
    { id: 'zf', x: 290, y: 14, w: 300, en: 'Con(ZF)', zh: '假设 ZF 一致', tag: '', c: '#1f2430',
      cap: ['Start: assume ZF is consistent. Everything below is relative to this assumption.', '起点：假设 ZF 一致。下面的一切都是相对于这个假设的。'] },
    { id: 'L', x: 30, y: 100, w: 340, en: 'L ⊨ ZFC + V = L + GCH', zh: '可构成宇宙 L 满足 ZFC + V = L + GCH', tag: 'L15', c: '#2f9e44',
      cap: ['L15: inside any model of ZF, build Gödel\'s L. It satisfies ZFC + V = L, and V = L implies GCH.', '第 15 课：在 ZF 的任意模型里构造哥德尔的 L，它满足 ZFC + V = L，而 V = L 蕴涵 GCH。'] },
    { id: 'conCH', x: 30, y: 186, w: 340, en: 'Con(ZFC + CH)', zh: 'ZFC + CH 一致', tag: 'L15', c: '#2f9e44',
      cap: ['So Con(ZF) → Con(ZFC + GCH) → Con(ZFC + CH).', '所以 Con(ZF) → Con(ZFC + GCH) → Con(ZFC + CH)。'] },
    { id: 'noNCH', x: 30, y: 372, w: 340, en: 'ZFC ⊬ ¬CH', zh: 'ZFC 证不出 ¬CH', tag: 'L15', c: '#2f9e44',
      cap: ['If ZFC proved ¬CH, then ZFC + CH would be inconsistent. So ZFC ⊬ ¬CH (assuming Con(ZF)).', '若 ZFC 能证 ¬CH，则 ZFC + CH 不一致。所以（在 Con(ZF) 之下）ZFC ⊬ ¬CH。'] },
    { id: 'conZFC', x: 510, y: 100, w: 340, en: 'Con(ZFC)', zh: 'ZFC 一致', tag: 'L15', c: '#3b5bdb',
      cap: ['Also from L: AC holds in L, so Con(ZF) → Con(ZFC). Now start the forcing branch.', '同样来自 L：选择公理在 L 中成立，所以 Con(ZF) → Con(ZFC)。现在进入力迫分支。'] },
    { id: 'ctm', x: 510, y: 186, w: 340, en: 'ctm M ⊨ Ψ (finite Ψ ⊆ ZFC)', zh: '有限片段 Ψ 的可数传递模型 M', tag: 'L14', c: '#3b5bdb',
      cap: ['L14: reflection gives V<sub>α</sub> ⊨ Ψ; LS gives a countable elementary submodel; Mostowski collapses it to a ctm M. (Only for finite Ψ: ZFC cannot prove there is a model of all of ZFC.)', '第 14 课：反射原理给出 V<sub>α</sub> ⊨ Ψ；LS 定理给出可数初等子模型；莫斯托夫斯基坍塌把它变成可数传递模型 M。（只对有限的 Ψ：ZFC 证不出全体 ZFC 有模型。）'] },
    { id: 'G', x: 510, y: 272, w: 340, en: 'P = Fn(ω₂×ω, 2) ∈ M, G generic', zh: 'P = Fn(ω₂×ω, 2) ∈ M，取脱殊 G', tag: '§5', c: '#ae3ec9',
      cap: ['§5: since M is countable, Rasiowa–Sikorski gives an M-generic G.', '§5：M 可数，所以由拉肖瓦–西科尔斯基引理得到 M-脱殊滤子 G。'] },
    { id: 'MG', x: 510, y: 358, w: 340, en: 'M[G] ⊨ Φ + 2^ℵ₀ ≥ ℵ₂', zh: 'M[G] ⊨ Φ + 2^ℵ₀ ≥ ℵ₂', tag: '§8 §9', c: '#ae3ec9',
      cap: ['§8: M[G] satisfies any prescribed finite Φ ⊆ ZFC (Ψ chosen large enough). §9: ℵ₂ distinct Cohen reals, and ccc keeps ω₂^M = ω₂<sup>M[G]</sup>. So ¬CH holds in M[G].', '§8：只要 Ψ 取得足够大，M[G] 就满足预先指定的有限片段 Φ ⊆ ZFC。§9：ℵ₂ 个互不相同的科恩实数，ccc 保证 ω₂^M = ω₂<sup>M[G]</sup>，所以 M[G] 中 ¬CH 成立。'] },
    { id: 'noCH', x: 510, y: 430, w: 340, en: 'Con(ZFC + ¬CH), so ZFC ⊬ CH', zh: 'ZFC + ¬CH 一致，故 ZFC ⊬ CH', tag: '§10', c: '#ae3ec9',
      cap: ['Every finite part of ZFC + ¬CH has a model, so ZFC + ¬CH is consistent (by the finitary argument below). Hence ZFC ⊬ CH.', 'ZFC + ¬CH 的每个有限部分都有模型，所以 ZFC + ¬CH 一致（见下方的有穷论证）。因此 ZFC ⊬ CH。'] },
    { id: 'ind', x: 190, y: 470, w: 280, en: 'CH is independent of ZFC', zh: 'CH 独立于 ZFC', tag: '', c: '#f08c00',
      cap: ['Both branches together: neither CH nor ¬CH is provable from ZFC (if ZF is consistent). Gödel did the left half in 1938, Cohen the right half in 1963.', '两个分支合起来：ZFC 既证不出 CH，也证不出 ¬CH（只要 ZF 一致）。左半边是哥德尔 1938 年的工作，右半边是科恩 1963 年的工作。'] },
  ];
  const H = 46;
  const E = [['zf', 'L', 'build L · 构造 L'], ['zf', 'conZFC', ''], ['L', 'conCH', ''], ['conCH', 'noNCH', ''], ['conZFC', 'ctm', 'reflection · 反射'], ['ctm', 'G', 'R–S'], ['G', 'MG', 'forcing · 力迫'], ['MG', 'noCH', ''], ['noNCH', 'ind', ''], ['noCH', 'ind', '']];
  const order = ['zf', 'L', 'conCH', 'noNCH', 'conZFC', 'ctm', 'G', 'MG', 'noCH', 'ind'];
  const byId = Object.fromEntries(B.map(b => [b.id, b]));
  el('defs', {}, svg).innerHTML = '<marker id="fa" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse"><path d="M0,0 L10,5 L0,10 z" fill="#6b7280"/></marker>';
  const gA = el('g', {}, svg), gB = el('g', {}, svg);
  E.forEach(e => {
    const a = byId[e[0]], b = byId[e[1]];
    let x1 = a.x + a.w / 2, y1 = a.y + H, x2 = b.x + b.w / 2, y2 = b.y;
    if (e[0] === 'zf') { x1 = e[1] === 'L' ? a.x + 40 : a.x + a.w - 40; y1 = a.y + H; }
    if (e[0] === 'conCH') { x1 = a.x + a.w / 2; x2 = b.x + b.w / 2; }
    if (e[0] === 'noNCH') { x1 = a.x + 200; y1 = a.y + H; x2 = b.x + 60; y2 = b.y; }
    if (e[0] === 'noCH') { x1 = a.x; y1 = a.y + H / 2 + 10; x2 = b.x + b.w; y2 = b.y + H / 2; }
    const g = el('g', { class: 'flowarrow off' }, gA);
    el('line', { x1, y1, x2, y2, stroke: '#6b7280', 'stroke-width': 2, 'marker-end': 'url(#fa)' }, g);
    if (e[2]) txt(g, (x1 + x2) / 2 + 6, (y1 + y2) / 2, e[2], { 'font-size': 11, fill: '#6b7280' });
    e.g = g;
  });
  B.forEach(b => {
    const g = el('g', { class: 'flowbox off' }, gB);
    el('rect', { x: b.x, y: b.y, width: b.w, height: H, rx: 12, fill: '#fff', stroke: b.c, 'stroke-width': 2.5 }, g);
    txt(g, b.x + b.w / 2, b.y + 20, b.en, { 'text-anchor': 'middle', 'font-size': 13.5, 'font-weight': 800, fill: b.c });
    txt(g, b.x + b.w / 2, b.y + 37, b.zh, { 'text-anchor': 'middle', 'font-size': 12, fill: '#4a5568' });
    if (b.tag) { el('rect', { x: b.x + b.w - 44, y: b.y - 9, width: 42, height: 17, rx: 8, fill: b.c }, g); txt(g, b.x + b.w - 23, b.y + 3, b.tag, { 'text-anchor': 'middle', 'font-size': 10, fill: '#fff', 'font-weight': 700 }); }
    g.style.cursor = 'pointer';
    g.addEventListener('click', () => okBox($('flMsg'), bi(b.cap[0], b.cap[1]), 'info'));
    b.g = g;
  });
  let k = 0;
  function sync() {
    const shown = new Set(order.slice(0, k));
    B.forEach(b => { b.g.classList.toggle('off', !shown.has(b.id)); b.g.classList.toggle('cur', order[k - 1] === b.id); });
    E.forEach(e => e.g.classList.toggle('off', !(shown.has(e[0]) && shown.has(e[1]))));
    $('flNext').disabled = k >= order.length;
    if (k === 0) okBox($('flMsg'), bi('Press “Next step”. (Shown boxes are clickable.)', '按“下一步”。（已显示的方框可以点击。）'), 'info');
    else { const b = byId[order[k - 1]]; okBox($('flMsg'), bi(b.cap[0], b.cap[1]), k === order.length ? 'ok' : 'info'); }
  }
  $('flNext').addEventListener('click', () => { if (k < order.length) k++; sync(); });
  $('flAll').addEventListener('click', () => { k = order.length; sync(); });
  $('flReset').addEventListener('click', () => { k = 0; sync(); });
  sync();
})();

/* ================= §11 gallery ================= */
(function gallery() {
  const cards = [
    ['SH', 'Suslin\'s hypothesis', '苏斯林假设',
      'Is every ccc dense complete linear order without endpoints isomorphic to ℝ? Independent: ◇ (true in L) gives a Suslin line (Jensen); MA + ¬CH implies SH (Solovay–Tennenbaum 1971, the first <b>iterated</b> forcing).',
      '满足 ccc 的稠密、完备、无端点线性序都同构于 ℝ 吗？这是独立的：◇（在 L 中成立）给出苏斯林线（詹森）；MA + ¬CH 蕴涵 SH（索洛韦–坦南鲍姆 1971，第一次用到<b>迭代</b>力迫）。'],
    ['MA', 'Martin\'s axiom', '马丁公理',
      'MA: for every ccc poset and fewer than 2^ℵ₀ dense sets, a filter meets them all. It is Rasiowa–Sikorski pushed beyond countable. MA + ¬CH is consistent; it decides many questions of analysis and topology (e.g. 2^κ = 2^ℵ₀ for κ < 2^ℵ₀).',
      'MA：对任何满足 ccc 的偏序，以及少于 2^ℵ₀ 个稠密集，都有滤子与它们全部相交。这就是把拉肖瓦–西科尔斯基引理推广到不可数的情形。MA + ¬CH 是一致的，它能判定分析和拓扑中的许多问题（例如当 κ < 2^ℵ₀ 时 2^κ = 2^ℵ₀）。'],
    ['2^κ', 'Easton\'s theorem', '伊斯顿定理',
      'For <b>regular</b> κ, ZFC only proves monotonicity and König (cf 2^κ > κ). Easton (1970): over a model of GCH, any such (definable) class function κ ↦ 2^κ on regular κ can be realized by forcing. Singular cardinals are different: Silver\'s theorem, Shelah\'s pcf theory (e.g. 2<sup>ℵ<sub>ω</sub></sup> < ℵ<sub>ω₄</sub> if ℵ<sub>ω</sub> is a strong limit).',
      '对<b>正则</b>基数 κ，ZFC 只能证明单调性和柯尼希定理（cf 2^κ > κ）。伊斯顿（1970）：从 GCH 的模型出发，正则基数上任何满足这些条件的（可定义）类函数 κ ↦ 2^κ 都能用力迫实现。奇异基数则不同：有西尔弗定理和谢拉赫的 pcf 理论（例如若 ℵ<sub>ω</sub> 是强极限，则 2<sup>ℵ<sub>ω</sub></sup> < ℵ<sub>ω₄</sub>）。'],
    ['Ext', 'Whitehead\'s problem', '怀特海问题',
      'Is every abelian group A with Ext(A, ℤ) = 0 free? Shelah (1974): independent. V = L gives yes; MA + ¬CH gives no. One of the first independence results in mainstream algebra.',
      '满足 Ext(A, ℤ) = 0 的阿贝尔群 A 一定是自由的吗？谢拉赫（1974）：独立。V = L 时答案是肯定的；MA + ¬CH 时答案是否定的。这是主流代数中最早的独立性结果之一。'],
    ['μ', 'Solovay\'s model', '索洛韦模型',
      'From an inaccessible cardinal, Solovay (1970) forced a model of ZF + DC in which every set of reals is Lebesgue measurable. So the non-measurable sets of L10 really need AC.',
      '索洛韦（1970）从一个不可达基数出发，力迫出 ZF + DC 的一个模型，其中每个实数集都勒贝格可测。所以第 10 课中的不可测集确实离不开选择公理。'],
    ['κ', 'Large cardinals (→ L23–L25)', '大基数（→ 第 23–25 课）',
      'Forcing cannot settle CH, and large cardinals do not either, but they calibrate consistency strength and make forcing axioms (PFA, MM, which give 2^ℵ₀ = ℵ₂) possible. Lessons 23–25 take this up, with determinacy in L25.',
      '力迫判定不了 CH，大基数也判定不了；但大基数能刻画一致性强度，也是力迫公理（PFA、MM，它们推出 2^ℵ₀ = ℵ₂）的基础。第 23–25 课会展开，第 25 课还会讲决定性。'],
    ['HOD', 'Woodin\'s program (→ L22)', '伍丁纲领（→ 第 22 课）',
      'Under large cardinals, the theory of L(ℝ) cannot be changed by forcing (generic absoluteness). Woodin\'s Ω-logic and “Ultimate L” aim at a canonical inner model, built around HOD (Lesson 22). Asperó–Schindler (2021): MM⁺⁺ implies Woodin\'s axiom (*), and (*) gives 2^ℵ₀ = ℵ₂. CH remains open as a question about which axioms to adopt.',
      '在大基数假设下，L(ℝ) 的理论不能被力迫改变（脱殊绝对性）。伍丁的 Ω-逻辑和“终极 L”纲领试图找到一个典范的内模型，其核心是 HOD（第 22 课）。阿斯佩罗–申德勒（2021）：MM⁺⁺ 蕴涵伍丁公理 (*)，而 (*) 推出 2^ℵ₀ = ℵ₂。CH 仍是一个悬而未决的问题：我们该接受哪些新公理？'],
  ];
  const box = $('galTiles');
  cards.forEach(c => {
    const d = document.createElement('div');
    d.className = 'flip gal';
    d.innerHTML = `<div class="front"><span class="sym" style="color:var(--meta)">${c[0]}</span>${bil(c[1], c[2])}</div><div class="back">${bi(c[3], c[4])}</div>`;
    d.addEventListener('click', () => d.classList.toggle('open'));
    box.appendChild(d);
  });
})();

/* ================= E1 dense? ================= */
(function e1() {
  const ans = E1SETS.map(() => null);
  let cur = 0, revealed = false;
  const T = makeTree($('e1Tree'), { onClick: probe });
  const list = $('e1List');
  E1SETS.forEach((S, i) => {
    const row = document.createElement('div');
    row.className = 'dense-row';
    row.innerHTML = `<span class="stmt m">${String.fromCharCode(97 + i)}) ${bilq(S.en, S.zh)}</span>`;
    const bY = btn(bil('Dense', '稠密')), bN = btn(bil('Not dense', '不稠密')), bE = btn(bil('Show on tree', '画在树上'), 'btn small ghost');
    bY.addEventListener('click', () => { ans[i] = true; bY.classList.add('sel'); bN.classList.remove('sel'); row.classList.remove('right', 'wrong'); });
    bN.addEventListener('click', () => { ans[i] = false; bN.classList.add('sel'); bY.classList.remove('sel'); row.classList.remove('right', 'wrong'); });
    bE.addEventListener('click', () => { cur = i; paint(); });
    row.append(bY, bN, bE);
    S.row = row;
    list.appendChild(row);
  });
  function paint() {
    const S = E1SETS[cur];
    T.paint(s => (S.f(s) ? 'inD' : ''));
    T.edges(() => '');
    okBox($('e1Probe'), bi(`Showing set ${String.fromCharCode(97 + cur)}). Green = member. Click a node to look for an extension in the set.`, `正在显示集合 ${String.fromCharCode(97 + cur)}）。绿色＝元素。点一个节点，找它在集合中的加细。`), 'info');
  }
  function probe(p) {
    const S = E1SETS[cur];
    const q = F16.firstExt(p, S.f, 9);
    T.paint(s => (s === p ? (q === null ? 'fail' : 'sel') : q !== null && s === q ? 'meet' : S.f(s) ? 'inD' : ''));
    T.edges(s => (q !== null && q.startsWith(s) && s.length > p.length ? 'walk' : ''));
    if (q === null) okBox($('e1Probe'), bi(`No extension of <span class="m">${fmtS(p)}</span> in the set (searched 9 levels deep). Is this a proof? Think about why.`, `在集合中找不到 <span class="m">${fmtS(p)}</span> 的加细（往下搜了 9 层）。这算证明吗？想想为什么。`), 'warn');
    else okBox($('e1Probe'), bi(`<span class="m">${fmtS(q)} ≤ ${fmtS(p)}</span> is in the set.`, `<span class="m">${fmtS(q)} ≤ ${fmtS(p)}</span> 在集合中。`), 'ok');
  }
  function check(reveal) {
    let ok = 0;
    E1SETS.forEach((S, i) => {
      if (reveal) ans[i] = S.dense;
      S.row.classList.remove('right', 'wrong');
      S.row.querySelectorAll('button').forEach((b, j) => { if (j < 2) b.classList.toggle('sel', ans[i] === (j === 0)); });
      if (ans[i] === S.dense) { ok++; S.row.classList.add('right'); } else if (ans[i] !== null) S.row.classList.add('wrong');
      let w = S.row.querySelector('.why');
      if (reveal || ans[i] === S.dense) {
        if (!w) { w = document.createElement('div'); w.className = 'why muted'; w.style.flexBasis = '100%'; w.style.fontSize = '13px'; S.row.appendChild(w); }
        w.innerHTML = (S.dense ? bil('Dense. ', '稠密。') : bil('Not dense. ', '不稠密。')) + bil(S.w[0], S.w[1]);
      }
    });
    if (reveal) { revealed = true; okBox($('e1Msg'), bi('Answers shown, with reasons.', '已显示答案及理由。'), 'info'); return; }
    if (ok === E1SETS.length) { okBox($('e1Msg'), bi('✓ All correct. The pattern: a set is dense iff you can always still get in. Sets defined by “already decided” information that excludes some condition (p(0) = 1, small domains) are never dense.', '✓ 全对。规律是：稠密就是“无论如何都还进得去”。凡是被某些已确定信息挡在外面的集合（p(0) = 1、定义域很小）都不稠密。')); if (!revealed) markDone('L16E1'); }
    else okBox($('e1Msg'), bi(`${ok} / ${E1SETS.length} correct. Red rows are wrong; uncolored rows are unanswered. Probe them on the tree.`, `答对 ${ok} / ${E1SETS.length}。红色行答错了，没上色的行还没作答。到树上试探一下。`), 'warn');
  }
  $('e1Check').addEventListener('click', () => check(false));
  $('e1Show').addEventListener('click', () => check(true));
  paint();
})();

/* ================= E2 extend a condition ================= */
(function e2() {
  const N = 10, fixed = { 1: 1, 4: 0 };
  let q = Object.assign({}, fixed);
  const reqs = [
    { en: 'D₆: 6 ∈ dom q', zh: 'D₆：6 ∈ dom q', f: q => q[6] !== undefined },
    { en: 'D<sub>x</sub>, x = 0101…: q(n) ≠ n mod 2 for some n', zh: 'D<sub>x</sub>，x = 0101…：存在 n 使 q(n) ≠ n mod 2', f: q => Object.keys(q).some(n => q[n] !== n % 2) },
    { en: 'q(n) = q(n+1) = 1 for some n', zh: '存在 n 使 q(n) = q(n+1) = 1', f: q => Object.keys(q).some(n => q[n] === 1 && q[+n + 1] === 1) },
    { en: 'q takes the value 0 at least three times', zh: 'q 至少三次取值 0', f: q => Object.values(q).filter(v => v === 0).length >= 3 },
  ];
  let revealed = false;
  function draw() {
    let h = '<div class="cells"><span class="lab"></span>' + Array.from({ length: N }, (_, i) => `<span class="cell idx">${i}</span>`).join('') + '</div>';
    h += '<div class="cells"><span class="lab">p</span>';
    for (let i = 0; i < N; i++) h += `<span class="cell ro${fixed[i] === undefined ? '' : ' b' + fixed[i] + ' fixed'}">${fixed[i] ?? ''}</span>`;
    h += '</div><div class="cells"><span class="lab">q ≤ p</span>';
    for (let i = 0; i < N; i++) h += `<span class="cell${q[i] === undefined ? '' : ' b' + q[i]}${fixed[i] !== undefined ? ' fixed' : ''}" data-i="${i}">${q[i] ?? ''}</span>`;
    $('e2Cells').innerHTML = h + '<span class="muted">…</span></div>';
    $('e2Cells').querySelectorAll('[data-i]').forEach(c => c.addEventListener('click', () => {
      const i = +c.dataset.i;
      if (fixed[i] !== undefined) return;
      q[i] = q[i] === undefined ? 0 : q[i] === 0 ? 1 : undefined;
      if (q[i] === undefined) delete q[i];
      draw();
    }));
    let all = true;
    $('e2Reqs').innerHTML = reqs.map(r => { const m = r.f(q); all = all && m; return `<div class="req ${m ? 'met' : ''}"><span class="ic">${m ? '✓' : '·'}</span>${bilq(r.en, r.zh)}</div>`; }).join('');
    if (all) {
      okBox($('e2Msg'), bi(`✓ <span class="m">q = {${Object.keys(q).map(n => `(${n},${q[n]})`).join(', ')}}</span> extends p and lies in all four dense sets.`, `✓ <span class="m">q = {${Object.keys(q).map(n => `(${n},${q[n]})`).join(', ')}}</span> 延拓了 p，并且同时属于四个稠密集。`), revealed ? 'info' : 'ok');
      if (!revealed) markDone('L16E2');
    } else okBox($('e2Msg'), bi('Click the q cells (blank → 0 → 1). Unmet requirements have no ✓.', '点 q 那一行的格子（空 → 0 → 1）。未满足的要求没有 ✓。'), 'info');
  }
  $('e2Clear').addEventListener('click', () => { q = Object.assign({}, fixed); draw(); });
  $('e2Show').addEventListener('click', () => { revealed = true; q = { 0: 1, 1: 1, 2: 0, 3: 0, 4: 0, 6: 0 }; draw(); });
  draw();
})();

/* ================= E3 evaluate a name ================= */
(function e3() {
  const box = $('e3Rounds');
  const picks = E3.rounds.map(() => E3.cands.map(() => false));
  let revealed = false;
  E3.rounds.forEach((g, r) => {
    const d = document.createElement('div');
    d.className = 'tf';
    d.innerHTML = `<div class="stmt">g = ${g}…, G = {p : p ⊆ g}: <b>val(τ, G) ∋</b></div><div class="chs"></div><div class="res" style="flex-basis:100%"></div>`;
    E3.cands.forEach((cd, i) => {
      const ch = document.createElement('span');
      ch.className = 'ordchip';
      ch.textContent = cd.lab;
      ch.addEventListener('click', () => { picks[r][i] = !picks[r][i]; ch.classList.toggle('on', picks[r][i]); ch.classList.remove('right', 'wrong', 'miss'); });
      d.querySelector('.chs').appendChild(ch);
    });
    box.appendChild(d);
  });
  function check(reveal) {
    let ok = 0;
    [...box.children].forEach((d, r) => {
      const want = E3.answer(E3.rounds[r]);
      if (reveal) picks[r] = want.slice();
      const chips = d.querySelectorAll('.ordchip');
      let rowOk = true;
      chips.forEach((ch, i) => {
        ch.classList.toggle('on', picks[r][i]);
        ch.classList.remove('right', 'wrong');
        ch.classList.remove('miss');
        if (picks[r][i] && want[i]) ch.classList.add('right');
        else if (picks[r][i] !== want[i]) { ch.classList.add(picks[r][i] ? 'wrong' : 'miss'); rowOk = false; }
      });
      if (rowOk) ok++;
      const els = E3.cands.filter((_, i) => want[i]).map(c => c.lab).join(', ');
      d.querySelector('.res').innerHTML = rowOk || reveal ? `<span class="m muted">val(τ, G) = {${els}}</span>` : '';
    });
    if (reveal) { revealed = true; okBox($('e3Msg'), bi('Answers shown. Work: σ<sub>G</sub> collects 0 if ⟨00⟩ ∈ G and 1 if ⟨01⟩ ∈ G; then τ<sub>G</sub> collects σ<sub>G</sub> (if ⟨0⟩ ∈ G), 1 (if ⟨01⟩ ∈ G), 2 (if ⟨1⟩ ∈ G) and always 0.', '已显示答案。计算过程：若 ⟨00⟩ ∈ G 则 σ<sub>G</sub> 含 0，若 ⟨01⟩ ∈ G 则 σ<sub>G</sub> 含 1；然后 τ<sub>G</sub> 收集 σ<sub>G</sub>（若 ⟨0⟩ ∈ G）、1（若 ⟨01⟩ ∈ G）、2（若 ⟨1⟩ ∈ G），以及永远在内的 0。'), 'info'); return; }
    if (ok === E3.rounds.length) { okBox($('e3Msg'), bi('✓ All three right. Note round 1: σ<sub>G</sub> = {0} = 1, so the element contributed by σ coincides with the ordinal 1. Different names can have the same value.', '✓ 三轮全对。注意第一轮：σ<sub>G</sub> = {0} = 1，所以 σ 贡献的元素恰好就是序数 1。不同的名字可以取相同的值。')); if (!revealed) markDone('L16E3'); }
    else okBox($('e3Msg'), bi(`${ok} / 3 rounds right. Red = wrongly picked, blue outline = missing. Evaluate σ first.`, `答对 ${ok} / 3 轮。红色＝选错，蓝色＝漏选。先算 σ 的值。`), 'warn');
  }
  $('e3Check').addEventListener('click', () => check(false));
  $('e3Show').addEventListener('click', () => check(true));
})();

/* ================= E4 order the ccc proof ================= */
(function e4() {
  const steps = [
    ['It suffices that every regular uncountable cardinal λ of M stays regular in M[G]: every cardinal is a successor (hence regular) or a limit of successors.', '只需证明 M 的每个不可数正则基数 λ 在 M[G] 中仍正则：每个基数要么是后继基数（从而正则），要么是后继基数的极限。'],
    ['Suppose not: in M[G] there is a cofinal f : μ → λ with μ < λ. Fix a name ḟ and p ∈ G with p ⊩ “ḟ : μ̌ → λ̌ is cofinal”.', '假设不然：M[G] 中有共尾映射 f : μ → λ，μ < λ。取名字 ḟ 及 p ∈ G，使 p ⊩“ḟ : μ̌ → λ̌ 共尾”。'],
    ['In M, define F(ξ) = {β < λ : ∃q ≤ p, q ⊩ ḟ(ξ̌) = β̌}. This is possible by definability of ⊩.', '在 M 中定义 F(ξ) = {β < λ : ∃q ≤ p, q ⊩ ḟ(ξ̌) = β̌}。由 ⊩ 的可定义性，这可以做到。'],
    ['f(ξ) ∈ F(ξ): by the Truth Lemma some q ∈ G, q ≤ p, forces ḟ(ξ̌) = f(ξ)ˇ.', 'f(ξ) ∈ F(ξ)：由真值引理，有 q ∈ G、q ≤ p 力迫 ḟ(ξ̌) = f(ξ)ˇ。'],
    ['Conditions forcing different values of ḟ(ξ̌) are incompatible. Picking one witness per β gives an antichain, so by ccc each F(ξ) is countable in M.', '力迫 ḟ(ξ̌) 取不同值的条件互不相容。对每个 β 取一个见证条件，得到一个反链；由 ccc，每个 F(ξ) 在 M 中可数。'],
    ['In M, ⋃<sub>ξ<μ</sub> F(ξ) has size ≤ μ·ℵ₀ < λ, so it is bounded in the regular λ. But it contains ran f, which is cofinal. Contradiction.', '在 M 中，⋃<sub>ξ<μ</sub> F(ξ) 的势 ≤ μ·ℵ₀ < λ，因而在正则的 λ 中有界；可它包含共尾的 ran f。矛盾。'],
  ];
  const ok = [[0, 1, 2, 3, 4, 5], [0, 1, 2, 4, 3, 5]];
  let seq = [], revealed = false;
  const order = shuffle([...steps.keys()]);
  function draw() {
    const pool = $('e4Pool'), s = $('e4Seq');
    pool.innerHTML = ''; s.innerHTML = '';
    order.filter(i => !seq.includes(i)).forEach(i => {
      const c = document.createElement('div');
      c.className = 'chip';
      c.innerHTML = bi(steps[i][0], steps[i][1]);
      c.addEventListener('click', () => { seq.push(i); draw(); clearBox($('e4Msg')); });
      pool.appendChild(c);
    });
    seq.forEach((i, k) => {
      const c = document.createElement('div');
      c.className = 'chip';
      c.innerHTML = `<span class="num">${k + 1}.</span>` + bi(steps[i][0], steps[i][1]);
      c.addEventListener('click', () => { seq = seq.filter(x => x !== i); draw(); clearBox($('e4Msg')); });
      s.appendChild(c);
    });
  }
  $('e4Check').addEventListener('click', () => {
    if (seq.length < steps.length) { okBox($('e4Msg'), bi('Place all six steps first.', '先把六步都放好。'), 'warn'); return; }
    const right = ok.some(o => o.every((v, k) => v === seq[k]));
    const chips = $('e4Seq').querySelectorAll('.chip');
    seq.forEach((v, k) => chips[k].classList.add(ok.some(o => o[k] === v) ? 'ok' : 'no'));
    if (right) { okBox($('e4Msg'), bi('✓ Correct. (Steps 4 and 5 may be swapped.) This is the approximation lemma at work: everything M[G] knows about f, M already knew up to countable ambiguity.', '✓ 正确。（第 4、5 步可以互换。）这就是逼近引理的威力：M[G] 关于 f 所知道的一切，M 早就知道，只差一个可数的不确定性。')); if (!revealed) markDone('L16E4'); }
    else okBox($('e4Msg'), bi('Not yet. Red steps are out of place. Hint: you need the name before you can define F, and you need F before counting.', '还不对，红色的步骤位置不对。提示：先有名字才能定义 F，先有 F 才能计数。'), 'bad');
  });
  $('e4Show').addEventListener('click', () => {
    revealed = true;
    seq = [0, 1, 2, 3, 4, 5];
    draw();
    $('e4Seq').querySelectorAll('.chip').forEach(c => c.classList.add('ok'));
    okBox($('e4Msg'), bi('The proof in order. (Steps 4 and 5 may be swapped.)', '按顺序排好的证明。（第 4、5 步可以互换。）'), 'info');
  });
  draw();
})();

/* ================= E5 why countable ================= */
(function e5() {
  const solved = { a: false, b: false };
  let revealed5 = false;
  function mc(boxId, msgId, part, opts) {
    const box = $(boxId);
    opts.forEach(o => {
      const b = btn(biq(o.en, o.zh), 'btn choice');
      b.addEventListener('click', () => {
        box.querySelectorAll('.choice').forEach(x => x.classList.remove('right', 'wrongc'));
        b.classList.add(o.ok ? 'right' : 'wrongc');
        okBox($(msgId), bi(o.r[0], o.r[1]), o.ok ? 'ok' : 'bad');
        if (o.ok) { solved[part] = true; if (solved.a && solved.b && !revealed5) markDone('L16E5'); }
      });
      o.b = b;
      box.appendChild(b);
    });
    return opts;
  }
  const A = mc('e5a', 'e5aMsg', 'a', [
    { en: 'D₅ = {p : 5 ∈ dom p}', zh: 'D₅ = {p : 5 ∈ dom p}', ok: false, r: ['G meets every D<sub>n</sub> by assumption.', '按假设 G 与每个 D<sub>n</sub> 都相交。'] },
    { en: 'D<sub>g</sub> = {p : p ⊥ g}, where g = ⋃G', zh: 'D<sub>g</sub> = {p : p ⊥ g}，其中 g = ⋃G', ok: true, r: ['✓ D<sub>g</sub> ∈ V is dense, but any p ∈ G is a piece of g, hence compatible with g. So G ∩ D<sub>g</sub> = ∅.', '✓ D<sub>g</sub> ∈ V 是稠密集，但 G 中任何 p 都是 g 的一部分，因而与 g 相容。所以 G ∩ D<sub>g</sub> = ∅。'] },
    { en: 'D<sub>x</sub> for x = 000…', zh: 'D<sub>x</sub>，x = 000…', ok: false, r: ['G can meet this: just put a 1 somewhere in g.', 'G 能碰到它：只要 g 中某处是 1。'] },
    { en: '{p : |dom p| is even}', zh: '{p : |dom p| 为偶数}', ok: false, r: ['Any filter with all D<sub>n</sub> contains conditions of even size.', '与所有 D<sub>n</sub> 相交的滤子必含定义域大小为偶数的条件。'] },
  ]);
  const Bq = mc('e5b', 'e5bMsg', 'b', [
    { en: 'To make G upward closed', zh: '为了让 G 向上封闭', ok: false, r: ['Upward closure is free: we just defined G that way.', '向上封闭是白送的：G 本来就是这样定义的。'] },
    { en: 'To list all dense sets of M as D₀, D₁, … so the chain p₀ ≥ p₁ ≥ … can visit each one at a finite stage', zh: '为了把 M 的所有稠密集排成 D₀, D₁, …，使递降链 p₀ ≥ p₁ ≥ … 在有限步内逐个碰到', ok: true, r: ['✓ An ω-length chain handles only countably many requirements. In general one cannot continue at limit stages: a decreasing ω-sequence in Fn(ω,2) need not have a lower bound.', '✓ 长度为 ω 的链只能满足可数多个要求。一般也无法在极限步继续：Fn(ω,2) 中的 ω-递降链未必有下界。'] },
    { en: 'To make sure g = ⋃G is a total function', zh: '为了保证 g = ⋃G 是全函数', ok: false, r: ['That only needs the countably many D<sub>n</sub>, which exist in any model.', '这只需要可数多个 D<sub>n</sub>，它们在任何模型中都存在。'] },
  ]);
  $('e5Show').addEventListener('click', () => {
    revealed5 = true;
    A[1].b.classList.add('right'); Bq[1].b.classList.add('right');
    okBox($('e5aMsg'), bi(A[1].r[0], A[1].r[1]), 'info');
    okBox($('e5bMsg'), bi(Bq[1].r[0], Bq[1].r[1]), 'info');
    document.querySelector('#e5Proof .step').classList.add('on');
  });
})();

/* ================= E6 continuum ================= */
(function e6() {
  const solved = { a: false, b: false };
  let revealed6 = false;
  function mc(boxId, msgId, part, opts) {
    const box = $(boxId);
    opts.forEach(o => {
      const b = btn(o.lab, 'btn');
      b.style.fontFamily = 'var(--mono)';
      b.addEventListener('click', () => {
        box.querySelectorAll('.btn').forEach(x => x.classList.remove('right2', 'wrong2'));
        b.classList.add(o.ok ? 'right2' : 'wrong2');
        okBox($(msgId), bi(o.r[0], o.r[1]), o.ok ? 'ok' : 'bad');
        if (o.ok) { solved[part] = true; if (solved.a && solved.b && !revealed6) markDone('L16E6'); }
      });
      o.b = b;
      box.appendChild(b);
    });
    return opts;
  }
  const A = mc('e6a', 'e6aMsg', 'a', [
    { lab: 'ℵ₁', ok: false, r: ['No: the ℵ₂ Cohen reals are distinct and ω₂ is preserved, so 2^ℵ₀ ≥ ℵ₂.', '不对：ℵ₂ 个科恩实数互不相同，且 ω₂ 被保持，所以 2^ℵ₀ ≥ ℵ₂。'] },
    { lab: 'ℵ₂', ok: true, r: ['✓ ≥ ℵ₂ from the grid; ≤ from counting nice names: |P| = ℵ₂, and in M, ℵ₂^ℵ₀ = ℵ₂ by GCH (cf ω₂ > ω). So M[G] ⊨ 2^ℵ₀ = ℵ₂.', '✓ 由格子图得 ≥ ℵ₂；由好名字计数得 ≤：|P| = ℵ₂，而在 M 中由 GCH（cf ω₂ > ω）有 ℵ₂^ℵ₀ = ℵ₂。所以 M[G] ⊨ 2^ℵ₀ = ℵ₂。'] },
    { lab: 'ℵ₃', ok: false, r: ['Too big: there are only ℵ₂^ℵ₀ = ℵ₂ nice names (GCH in M).', '太大了：好名字只有 ℵ₂^ℵ₀ = ℵ₂ 个（M 中 GCH 成立）。'] },
  ]);
  const Bq = mc('e6b', 'e6bMsg', 'b', [
    { lab: 'ℵ<sub>ω</sub>', ok: false, r: ['Impossible in any model: König\'s theorem (L9) gives cf(2^ℵ₀) > ℵ₀, while cf ℵ<sub>ω</sub> = ℵ₀.', '在任何模型里都不可能：柯尼希定理（第 9 课）给出 cf(2^ℵ₀) > ℵ₀，而 cf ℵ<sub>ω</sub> = ℵ₀。'] },
    { lab: 'ℵ<sub>ω+1</sub>', ok: true, r: ['✓ At least ℵ<sub>ω</sub> reals, so by König at least ℵ<sub>ω+1</sub>; at most ℵ<sub>ω</sub><sup>ℵ₀</sup> = ℵ<sub>ω+1</sub> nice names (GCH in M). The forcing “overshoots” to the next cardinal of uncountable cofinality.', '✓ 至少有 ℵ<sub>ω</sub> 个实数，由柯尼希定理至少 ℵ<sub>ω+1</sub>；而好名字至多 ℵ<sub>ω</sub><sup>ℵ₀</sup> = ℵ<sub>ω+1</sub> 个（M 中 GCH）。力迫“越过”ℵ<sub>ω</sub>，落在下一个共尾性不可数的基数上。'] },
    { lab: 'ℵ₁', ok: false, r: ['No: there are ℵ<sub>ω</sub> distinct Cohen reals and ccc preserves all cardinals.', '不对：有 ℵ<sub>ω</sub> 个互不相同的科恩实数，ccc 又保持所有基数。'] },
  ]);
  $('e6Show').addEventListener('click', () => {
    revealed6 = true;
    [A[1], Bq[1]].forEach(o => o.b.classList.add('right2'));
    okBox($('e6aMsg'), bi(A[1].r[0], A[1].r[1]), 'info');
    okBox($('e6bMsg'), bi(Bq[1].r[0], Bq[1].r[1]), 'info');
  });
})();

/* ================= Recap: course map ================= */
(function courseMap() {
  const svg = $('cmap');
  const L = [
    [1, 0, 'Propositional logic', '命题逻辑', 'Formulas (syntax) vs valuations (semantics); and the first diagonal: valuations are uncountable.', '公式（语法）与赋值（语义）；第一次对角线：赋值不可数。'],
    [2, 0, 'Proofs & completeness', '证明与完备性', 'The first bridge: ⊢ = ⊨ for propositional logic; compactness.', '第一座桥：命题逻辑中 ⊢ = ⊨；紧致性。'],
    [3, 0.65, 'First-order structures', '一阶结构', 'Structures and Tarski\'s definition of satisfaction.', '结构与塔斯基的满足定义。'],
    [4, 0, 'Gödel completeness', '哥德尔完备性', 'Every consistent theory has a model: the bridge we use to turn Con(T) into a model.', '一致的理论都有模型：把 Con(T) 变成模型的桥梁。'],
    [5, 0.55, 'Compactness & LS', '紧致性与 LS', 'Countable models exist (Skolem\'s paradox). This is why ctm\'s make sense.', '可数模型存在（斯科伦悖论），可数传递模型由此而来。'],
    [6, -0.55, 'Russell & ZF', '罗素悖论与 ZF', 'Russell\'s paradox is a diagonal argument; ZF is the syntactic response.', '罗素悖论就是对角线论证；ZF 公理是语法上的应对。'],
    [7, 0.5, 'ℕ, ℤ, ℚ, ℝ from sets', '用集合造数', 'Mathematics lives inside the universe of sets.', '数学可以在集合宇宙里实现。'],
    [8, 0.65, 'Ordinals', '序数', 'The spine of V; the height of a model.', 'V 的脊梁；模型的高度。'],
    [9, 0.4, 'Cardinals', '基数', 'Cantor: 2^κ > κ (diagonal); König: cf 2^κ > κ. CH is a question about 2^ℵ₀.', '康托尔：2^κ > κ（对角线）；柯尼希：cf 2^κ > κ。CH 问的是 2^ℵ₀。'],
    [10, -0.35, 'Axiom of Choice', '选择公理', 'An axiom beyond ZF; its independence also needs forcing.', 'ZF 之外的公理；它的独立性同样要靠力迫。'],
    [11, -0.75, 'Halting problem', '停机问题', 'Diagonal argument against all programs.', '针对一切程序的对角线论证。'],
    [12, -0.45, 'Incompleteness', '不完全性', 'Diagonal sentence: provability ≠ truth; ZFC cannot prove Con(ZFC).', '对角线句子：可证 ≠ 真；ZFC 证不出 Con(ZFC)。'],
    [13, -0.2, 'Tarski: truth', '塔斯基：真', 'Diagonal again: truth is not definable in the same language.', '还是对角线：真在同一语言中不可定义。'],
    [14, 0.75, 'Models & V', '模型与 V', 'V_α, absoluteness, reflection, Mostowski collapse, ctm\'s.', 'V_α、绝对性、反射原理、坍塌、可数传递模型。'],
    [15, 0.4, 'L & GCH', 'L 与 GCH', 'Inner model: Con(ZF) → Con(ZFC + GCH).', '内模型：Con(ZF) → Con(ZFC + GCH)。'],
    [16, 0, 'Forcing', '力迫法', 'Outer model by a diagonal real: Con(ZF) → Con(ZFC + ¬CH). Semantics (models) proving syntax (unprovability).', '用对角线实数造外模型：Con(ZF) → Con(ZFC + ¬CH)。用语义（模型）证明语法结论（不可证性）。'],
  ];
  const threads = {
    diag: { en: 'The diagonal thread', zh: '对角线线索', c: '#f08c00', ls: [1, 6, 9, 11, 12, 13, 16],
      d: ['Cantor\'s diagonal, again and again: valuations (L1), Russell (L6), 2^κ > κ (L9), halting (L11), the Gödel sentence (L12), the liar and truth (L13), and the Cohen real that escapes M\'s list (L16).', '康托尔的对角线一次又一次出现：赋值（L1）、罗素（L6）、2^κ > κ（L9）、停机（L11）、哥德尔句（L12）、说谎者与真（L13），以及逃出 M 清单的科恩实数（L16）。'] },
    bridge: { en: '⊢ ↔ ⊨ bridges', zh: '⊢ ↔ ⊨ 的桥梁', c: '#3b5bdb', ls: [1, 2, 4, 5],
      d: ['Soundness and completeness make proofs and models interchangeable, and compactness/LS give countable models: the foundation of every consistency proof.', '可靠性与完备性让证明和模型可以互换，紧致性与 LS 定理给出可数模型：这是一切一致性证明的基础。'] },
    models: { en: 'Models of set theory', zh: '集合论的模型', c: '#ae3ec9', ls: [5, 8, 9, 14, 15, 16],
      d: ['From countable models to ordinals and cardinals, to V and absoluteness, to the inner model L and the outer model M[G]: CH is independent.', '从可数模型到序数与基数，再到 V 与绝对性，最后是内模型 L 与外模型 M[G]：CH 独立。'] },
    limits: { en: 'Limits of formal systems', zh: '形式系统的极限', c: '#e03131', ls: [11, 12, 13, 16],
      d: ['What formal systems cannot do: decide halting, prove all truths, define their own truth, settle CH.', '形式系统做不到的事：判定停机、证明所有真命题、定义自身的真、判定 CH。'] },
  };
  const CX = 450, SX = 250, Y0 = 52, DY = 29.5;
  const pos = l => ({ x: CX + l[1] * SX, y: Y0 + (l[0] - 1) * DY });
  el('line', { x1: CX, y1: 22, x2: CX, y2: 540, stroke: '#9aa0aa', 'stroke-width': 2, 'stroke-dasharray': '6 6' }, svg);
  txt(svg, 30, 26, 'SYNTAX ⊢ · 语法', { 'font-size': 14, 'font-weight': 800, fill: '#1f2430' });
  txt(svg, 870, 26, 'SEMANTICS ⊨ · 语义', { 'font-size': 14, 'font-weight': 800, fill: '#1f2430', 'text-anchor': 'end' });
  const parts = [[1, 5, '#3b5bdb'], [6, 10, '#2f9e44'], [11, 13, '#f08c00'], [14, 16, '#ae3ec9']];
  const partNames = ['I', 'II', 'III', 'IV'];
  parts.forEach(([a, b, c], i) => {
    el('rect', { x: 4, y: Y0 + (a - 1) * DY - 13, width: 8, height: (b - a) * DY + 26, rx: 4, fill: c, opacity: .5 }, svg);
    txt(svg, 18, Y0 + ((a + b) / 2 - 1) * DY + 4, partNames[i], { 'font-size': 11, 'font-weight': 800, fill: c });
  });
  const gT = el('g', {}, svg), gN = el('g', {}, svg);
  Object.entries(threads).forEach(([k, t]) => {
    const pts = t.ls.map(n => pos(L[n - 1]));
    let d = `M${pts[0].x},${pts[0].y}`;
    for (let i = 1; i < pts.length; i++) { const a = pts[i - 1], b = pts[i]; const my = (a.y + b.y) / 2; d += ` C${a.x},${my} ${b.x},${my} ${b.x},${b.y}`; }
    t.path = el('path', { d, fill: 'none', stroke: t.c, 'stroke-width': 5, opacity: .55, 'stroke-linecap': 'round', class: 'thread' }, gT);
  });
  L.forEach(l => {
    const { x, y } = pos(l);
    const a = el('a', { href: `lesson${l[0]}.html`, class: 'mapnode' }, gN);
    const part = parts.findIndex(([s, e]) => l[0] >= s && l[0] <= e);
    const col = parts[part][2];
    const isDiag = threads.diag.ls.includes(l[0]);
    el('circle', { cx: x, cy: y, r: 12, fill: l[0] === 16 ? col : '#fff', stroke: isDiag ? '#f08c00' : col, 'stroke-width': isDiag ? 4 : 2.5 }, a);
    txt(a, x, y + 4, l[0], { 'text-anchor': 'middle', 'font-size': 11, 'font-weight': 800, fill: l[0] === 16 ? '#fff' : col });
    const left = l[1] < 0;
    txt(a, x + (left ? -18 : 18), y + 4, `${l[2]} · ${l[3]}`, { 'text-anchor': left ? 'end' : 'start', 'font-size': 12, fill: '#1f2430' });
    a.addEventListener('mouseenter', () => okBox($('mapMsg'), `<b>L${l[0]}</b> · ` + bi(l[4], l[5]), 'info'));
    l.a = a;
  });
  const tabs = $('mapTabs');
  const opts = [['all', 'Everything', '全部'], ...Object.entries(threads).map(([k, t]) => [k, t.en, t.zh])];
  opts.forEach(([k, en, zh], i) => {
    const b = btn(bil(en, zh));
    if (k !== 'all') b.style.borderColor = threads[k].c;
    b.addEventListener('click', () => {
      tabs.querySelectorAll('button').forEach(x => x.classList.remove('sel'));
      b.classList.add('sel');
      Object.entries(threads).forEach(([kk, t]) => t.path.classList.toggle('dim', k !== 'all' && kk !== k));
      L.forEach(l => l.a.classList.toggle('dim', k !== 'all' && !threads[k].ls.includes(l[0])));
      okBox($('mapMsg'), k === 'all'
        ? bi('Gold rings mark lessons where the diagonal method appears. Lesson 16, filled, is where you are now.', '金色圆环标出用到对角线方法的各课。实心的第 16 课就是你现在所在的位置。')
        : bi(threads[k].d[0], threads[k].d[1]), 'info');
    });
    tabs.appendChild(b);
    if (i === 0) b.click();
  });
})();
}
