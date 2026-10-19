// Lesson 27 interactions: frontiers of set theory.

/*PURE-START*/
// ---------- Cichoń's diagram: ZFC-provable inequalities (x → y means x ≤ y) ----------
const CI_NODES = ['addN', 'addM', 'covN', 'nonM', 'b', 'd', 'covM', 'nonN', 'cofM', 'cofN', 'c'];
const CI_EDGES = [
  ['al1', 'addN'], ['addN', 'addM'], ['addM', 'covM'], ['covM', 'nonN'], ['nonN', 'cofN'],
  ['addN', 'covN'], ['covN', 'nonM'], ['nonM', 'cofM'], ['cofM', 'cofN'], ['cofN', 'c'],
  ['addM', 'b'], ['b', 'nonM'], ['covM', 'd'], ['d', 'cofM'], ['b', 'd'],
];
// v: map node -> 1 (ℵ₁) or 2 (ℵ₂); 'al1' is always 1.
function cichonCheck(v) {
  const val = k => (k === 'al1' ? 1 : v[k]);
  const badEdges = CI_EDGES.filter(([a, b]) => val(a) > val(b));
  const eqAdd = v.addM === Math.min(v.b, v.covM);
  const eqCof = v.cofM === Math.max(v.d, v.nonM);
  return { badEdges, eqAdd, eqCof, ok: !badEdges.length && eqAdd && eqCof };
}
function cichonCount(requireC2) {
  let n = 0;
  for (let m = 0; m < (1 << CI_NODES.length); m++) {
    const v = {};
    CI_NODES.forEach((k, i) => { v[k] = (m >> i) & 1 ? 2 : 1; });
    if (requireC2 && v.c !== 2) continue;
    if (cichonCheck(v).ok) n++;
  }
  return n;
}
// ---------- König: can 2^κ have this cofinality? ----------
// Aleph index encoded as {lim: 'fin'|'om'|'om2'|'w1'|..., cf} – we store cf directly in the data.
/*PURE-END*/

Lang.init();
Progress.paint();

const $ = id => document.getElementById(id);
const okBox = (box, html, kind = 'ok') => { box.className = 'msg ' + kind; box.innerHTML = html; };
const clearBox = box => { box.className = 'msg'; box.innerHTML = ''; };
const C = { ink: '#1f2430', muted: '#6b7280', line: '#e3dfd3', accent: '#3b5bdb', accentSoft: '#e7ecff', tru: '#2f9e44', truSoft: '#d3f9d8',
  fal: '#e03131', falSoft: '#ffe3e3', meta: '#ae3ec9', metaSoft: '#f8e7fc', gold: '#f08c00', goldSoft: '#fff3bf', teal: '#0c8599', tealSoft: '#e3fafc', slate: '#5c677d' };
function T(parent, x, y, s, attrs = {}) {
  const t = el('text', Object.assign({ x, y, 'font-size': 13, fill: C.ink, class: 'lbl' }, attrs), parent);
  if (!/<su[bp]>/.test(s)) { t.textContent = s; return t; }
  const fs = +(attrs['font-size'] || 13);
  s.split(/(<su[bp]>.*?<\/su[bp]>)/).forEach(part => {
    if (!part) return;
    const m = part.match(/^<(su[bp])>(.*)<\/su[bp]>$/);
    if (!m) { el('tspan', {}, t).textContent = part; return; }
    const ts = el('tspan', { 'font-size': fs * 0.72, dy: m[1] === 'sub' ? fs * 0.3 : -fs * 0.4 }, t);
    ts.textContent = m[2];
    el('tspan', { dy: m[1] === 'sub' ? -fs * 0.3 : fs * 0.4 }, t).textContent = '\u200b';
  });
  return t;
}
const subN = n => String(n).split('').map(d => '₀₁₂₃₄₅₆₇₈₉'[d]).join('');
const shuffle = a => { for (let i = a.length - 1; i > 0; i--) { const j = Math.floor(Math.random() * (i + 1)); [a[i], a[j]] = [a[j], a[i]]; } return a; };
function animate(ms, step) {
  return new Promise(res => {
    const t0 = performance.now();
    function f() { const u = Math.min(1, (performance.now() - t0) / ms); step(u < 1 ? 1 - Math.pow(1 - u, 3) : 1); if (u < 1) setTimeout(f, 16); else res(); }
    setTimeout(f, 16);
  });
}
const ST = {
  thm: () => `<span class="status st-thm">${bi('THEOREM', '定理')}</span>`,
  ind: () => `<span class="status st-ind">${bi('INDEPENDENT', '独立')}</span>`,
  open: () => `<span class="status st-open">${bi('OPEN', '未解决')}</span>`,
  prog: () => `<span class="status st-prog">${bi('PROGRAM / CONJECTURE', '纲领 / 猜想')}</span>`,
  phil: () => `<span class="status st-phil">${bi('PHILOSOPHICAL', '哲学性')}</span>`,
  no: () => `<span class="status st-no">${bi('REFUTED in ZFC', '在 ZFC 中被否证')}</span>`,
};

/* ================= check-yourself ================= */
function checkYourself(id, q, opts, expl) {
  const box = $(id);
  box.innerHTML = `<div class="q">✎ ${bil('Check yourself', '自我检测')}: ${bi(q[0], q[1])}</div><div class="opts"></div><div class="msg"></div>`;
  const ob = box.querySelector('.opts'), msg = box.querySelector('.msg');
  const btns = opts.map(o => {
    const b = document.createElement('button');
    b.className = 'btn small';
    b.innerHTML = o[0] === o[1] ? o[0] : bil(o[0], o[1]);
    b.addEventListener('click', () => {
      btns.forEach(x => x.classList.remove('right', 'wrongc'));
      b.classList.add(o[2] ? 'right' : 'wrongc');
      okBox(msg, (o[2] ? '✓ ' : '✗ ') + bi(o[2] ? expl[0] : (o[3] || 'Not quite. Think again, or press “Show answer”.'), o[2] ? expl[1] : (o[4] || '不太对。再想想，或者点“看答案”。')), o[2] ? 'ok' : 'bad');
    });
    ob.appendChild(b);
    return b;
  });
  const sh = document.createElement('button');
  sh.className = 'btn small ghost';
  sh.innerHTML = bil('Show answer', '看答案');
  sh.addEventListener('click', () => {
    btns.forEach((x, k) => { x.classList.remove('right', 'wrongc'); if (opts[k][2]) x.classList.add('right'); });
    okBox(msg, bi(expl[0], expl[1]), 'info');
  });
  ob.appendChild(sh);
}

/* ================= §1 dashboard ================= */
(function dashboard() {
  const tiles = [
    { k: 'ind', s: 's2', q: ['Do large cardinals decide CH?', '大基数能判定 CH 吗？'], a: ['No: Lévy–Solovay 1967 (small forcing).', '不能：列维–索洛维 1967（小力迫）。'] },
    { k: 'thm', s: 's3', q: ['Are projective questions frozen?', '投影层级的问题被冻结了吗？'], a: ['Yes, with a proper class of Woodin cardinals (Woodin).', '是的，在真类多个伍丁基数下（伍丁）。'] },
    { k: 'thm', s: 's4', q: ['Forcing axioms ⇒ 2^ℵ₀ = ℵ₂', '力迫公理 ⇒ 2^ℵ₀ = ℵ₂'], a: ['MM (1988), PFA; MM⁺⁺ ⇒ (*) (Asperó–Schindler 2021).', 'MM（1988）、PFA；MM⁺⁺ ⇒ (*)（Asperó–Schindler 2021）。'] },
    { k: 'open', s: 's4', q: ['Exact consistency strength of PFA', 'PFA 的精确一致性强度'], a: ['Upper bound: supercompact. Matching lower bound unknown.', '上界：超紧基数。相匹配的下界未知。'] },
    { k: 'prog', s: 's5', q: ['V = Ultimate L (⇒ CH)', 'V = 终极 L（⇒ CH）'], a: ['Woodin\'s program; the Ultimate-L Conjecture is open.', '伍丁的纲领；终极 L 猜想尚未解决。'] },
    { k: 'open', s: 's5', q: ['Woodin\'s Ω Conjecture', '伍丁的 Ω 猜想'], a: ['Is Ω-validity = Ω-provability?', 'Ω-有效是否等于 Ω-可证？'] },
    { k: 'open', s: 's6', q: ['Inner model for a supercompact', '超紧基数的内模型'], a: ['Proved iterability reaches a Woodin limit of Woodins (Neeman 2002).', '已证可迭代性到达伍丁基数之极限的伍丁基数（Neeman 2002）。'] },
    { k: 'open', s: 's7', q: ['The HOD Conjecture', 'HOD 猜想'], a: ['Is HOD always close to V above an extendible?', '在可扩基数之上，HOD 是否总是接近 V？'] },
    { k: 'open', s: 's8', q: ['Is ZF + Reinhardt consistent?', 'ZF + Reinhardt 一致吗？'], a: ['Refuted under AC (Kunen 1971); open in ZF.', '在 AC 下被否证（库能 1971）；在 ZF 中未解决。'] },
    { k: 'open', s: 's9', q: ['2^ℵ<sub>ω</sub> < ℵ<sub>ω₁</sub>?', '2^ℵ<sub>ω</sub> < ℵ<sub>ω₁</sub>？'], a: ['Shelah: < ℵ<sub>ω₄</sub> (ℵ<sub>ω</sub> strong limit). ω₁ vs ω₄ open.', 'Shelah：< ℵ<sub>ω₄</sub>（ℵ<sub>ω</sub> 为强极限）。ω₁ 与 ω₄ 之间未解决。'] },
    { k: 'thm', s: 's10', q: ['Cichoń\'s Maximum', 'Cichoń 极大'], a: ['All 10 values distinct: GKS 2019, no large cardinals GKMS 2022.', '十个值互不相同：GKS 2019；去掉大基数：GKMS 2022。'] },
    { k: 'ind', s: 's11', q: ['Whitehead, Suslin, Borel, Kaplansky, Calkin', '怀特海、苏斯林、博雷尔、Kaplansky、Calkin'], a: ['All independent of ZFC.', '全部独立于 ZFC。'] },
    { k: 'phil', s: 's12', q: ['One universe or a multiverse?', '一个宇宙还是多宇宙？'], a: ['Does CH have a definite truth value?', 'CH 有确定的真值吗？'] },
  ];
  const kinds = [['all', 'All', '全部'], ['thm', 'Theorem', '定理'], ['ind', 'Independent', '独立'], ['open', 'Open', '未解决'], ['prog', 'Program', '纲领'], ['phil', 'Philosophical', '哲学性']];
  const box = $('dash');
  const els = tiles.map(t => {
    const d = document.createElement('div');
    d.className = 'tile2 k-' + t.k;
    d.innerHTML = `${ST[t.k]()}<div class="tq">${bil(t.q[0], t.q[1])}</div><div class="ts">${bi(t.a[0], t.a[1])}</div><div class="go">§${t.s.slice(1)} →</div>`;
    d.addEventListener('click', () => {
      const sec = $(t.s);
      sec.scrollIntoView({ behavior: 'smooth', block: 'start' });
      sec.classList.remove('flash'); void sec.offsetWidth; sec.classList.add('flash');
    });
    box.appendChild(d);
    return d;
  });
  const fb = $('dashFilter');
  const btns = kinds.map(([k, en, zh]) => {
    const b = document.createElement('button');
    b.className = 'btn small' + (k === 'all' ? ' sel' : '');
    b.innerHTML = bil(en, zh);
    b.addEventListener('click', () => {
      btns.forEach(x => x.classList.remove('sel'));
      b.classList.add('sel');
      els.forEach((d, i) => d.classList.toggle('faded', k !== 'all' && tiles[i].k !== k));
    });
    fb.appendChild(b);
    return b;
  });
  checkYourself('cy1', ['CH is independent of ZFC. So the status of “CH” on this map is…', 'CH 独立于 ZFC。那么 CH 在这张地图上的状态是……'], [
    ['open, because nobody knows if it is true', '未解决，因为没人知道它真不真', false, 'Careful: its <i>independence</i> is a proved theorem. What is open is whether a justified new axiom settles it.', '注意：它的<i>独立性</i>是已证明的定理。悬而未决的是：有没有站得住脚的新公理能判定它。'],
    ['independent of ZFC (a theorem), with the choice of new axioms still open', '独立于 ZFC（这是定理），而选择什么新公理仍悬而未决', true],
    ['refuted', '已被否证', false],
  ], ['Right. Gödel (1938) + Cohen (1963) make independence a theorem. The live question is which extension of ZFC, if any, deserves to be accepted.', '对。哥德尔（1938）加科恩（1963）使独立性成为定理。真正活着的问题是：哪个 ZFC 扩张（如果有的话）值得被接受。']);
})();

/* ================= §2 Lévy–Solovay ================= */
(function levySolovay() {
  const svg = $('lsSvg');
  const AX = 430, Y = { a0: 350, a1: 312, a2: 282, a3: 252, inac: 200, kappa: 150, delta: 102, lam: 56 };
  const rungs = [
    { key: 'kappa', en: 'κ measurable', zh: '可测' },
    { key: 'delta', en: 'δ Woodin', zh: '伍丁' },
    { key: 'lam', en: 'λ supercompact', zh: '超紧' },
  ];
  let st;
  const gMain = el('g', {}, svg);
  function reset() {
    st = { c: 1, alive: { kappa: true, delta: true, lam: true }, hist: [], busy: false, size: null };
    st.hist.push({ s: 'GCH; κ δ λ ✓' });
    draw(st.c, null);
    okBox($('lsInfo'), bi('Ground model V satisfies GCH and has a measurable κ, a Woodin δ and a supercompact λ. Press a forcing button.', '基础模型 V 满足 GCH，并有可测基数 κ、伍丁基数 δ 和超紧基数 λ。按一个力迫按钮。'), 'info');
  }
  const cY = c => (c === 1 ? Y.a1 : c === 2 ? Y.a2 : Y.a3);
  function draw(cVal, size, pulse) {
    gMain.innerHTML = '';
    // axis
    el('line', { x1: AX, y1: 365, x2: AX, y2: 22, stroke: C.ink, 'stroke-width': 2.5 }, gMain);
    el('path', { d: `M${AX - 6},28 L${AX},16 L${AX + 6},28 Z`, fill: C.ink }, gMain);
    T(gMain, AX + 10, 20, 'cardinals ↑ · 基数', { 'font-size': 12, fill: C.muted });
    const ticks = [['a0', 'ℵ₀'], ['a1', 'ℵ₁'], ['a2', 'ℵ₂'], ['a3', 'ℵ₃'], ['inac', 'least inaccessible > 2^ℵ₀ · 2^ℵ₀ 之上第一个不可达']];
    ticks.forEach(([k, s]) => {
      el('line', { x1: AX - 6, x2: AX + 6, y1: Y[k], y2: Y[k], stroke: C.ink, 'stroke-width': 2 }, gMain);
      T(gMain, AX + 12, Y[k] + 4, s, { 'font-size': k === 'inac' ? 11.5 : 13, fill: k === 'inac' ? C.muted : C.ink });
    });
    // break mark between ℵ₃ and inaccessible
    el('path', { d: `M${AX - 8},230 l16,-6 M${AX - 8},236 l16,-6`, stroke: C.muted, 'stroke-width': 1.5 }, gMain);
    // CH zone band
    el('rect', { x: 140, y: 238, width: 300, height: 122, rx: 10, fill: C.accentSoft, opacity: .55 }, gMain);
    T(gMain, 150, 255, 'where CH lives · CH 所在之处', { 'font-size': 12, fill: C.accent, 'font-weight': 700 });
    // rungs
    rungs.forEach(r => {
      const alive = st.alive[r.key];
      const g = el('g', {}, gMain);
      el('line', { x1: AX - 6, x2: AX + 6, y1: Y[r.key], y2: Y[r.key], stroke: C.ink, 'stroke-width': 2 }, g);
      const rect = el('rect', { x: 560, y: Y[r.key] - 16, width: 270, height: 32, rx: 9, fill: alive ? C.truSoft : C.falSoft, stroke: alive ? C.tru : C.fal, 'stroke-width': 2 }, g);
      T(g, 574, Y[r.key] + 5, `${r.en} · ${r.zh}`, { 'font-size': 13.5, 'font-weight': 700, fill: alive ? '#1b5e20' : '#8a1c1c' });
      T(g, 806, Y[r.key] + 6, alive ? '✓' : '✗', { 'font-size': 17, 'font-weight': 800, fill: alive ? C.tru : C.fal });
      el('line', { x1: AX + 6, x2: 560, y1: Y[r.key], y2: Y[r.key], stroke: alive ? C.tru : C.fal, 'stroke-dasharray': '3 4' }, g);
      if (!alive) el('line', { x1: 566, x2: 824, y1: Y[r.key], y2: Y[r.key], stroke: C.fal, 'stroke-width': 2.5 }, g);
      if (pulse && alive) { rect.classList.add('pop'); }
    });
    // continuum marker
    const y = typeof cVal === 'number' && cVal > 3 ? cVal : cY(cVal);
    el('path', { d: `M${AX - 10},${y} l-14,-8 v16 Z`, fill: C.meta }, gMain);
    T(gMain, 150, y + 5, `2^ℵ₀ = ℵ${'₀₁₂₃'[st.c]}  ${st.c === 1 ? '(CH)' : '(¬CH)'}`, { 'font-size': 15, 'font-weight': 800, fill: C.meta, 'font-family': 'var(--mono)' });
    // forcing size bar
    if (size) {
      el('rect', { x: 372, y: size.y, width: 26, height: 360 - size.y, rx: 6, fill: size.big ? C.fal : '#9aa0aa', opacity: .55 }, gMain);
      T(gMain, 385, size.y - 8, '|ℙ|', { 'font-size': 13, 'font-weight': 800, 'text-anchor': 'middle', fill: size.big ? C.fal : C.ink });
    }
    // history
    T(gMain, 14, 22, 'models visited · 走过的模型', { 'font-size': 12, fill: C.muted, 'font-weight': 700 });
    st.hist.slice(-9).forEach((h, i) => {
      const n = st.hist.length - Math.min(9, st.hist.length) + i;
      T(gMain, 14, 42 + i * 20, `M${subN(n)}: ${h.s}`, { 'font-size': 11.5, fill: n === st.hist.length - 1 ? C.ink : C.muted, 'font-family': 'var(--mono)' });
    });
    T(gMain, 14, 232, 'M₀ = V; Mₙ₊₁ = Mₙ[G]', { 'font-size': 11, fill: C.muted });
  }
  async function act(kind) {
    if (st.busy) return;
    st.busy = true;
    const old = st.c;
    let size, msg;
    if (kind === 'neg') {
      st.c = Math.max(st.c, 2);
      size = { y: Y.a2 };
      st.hist.push({ s: `Add(ω,ω₂) → 2^ℵ₀=ℵ${'₀₁₂₃'[st.c]}; κ δ λ ✓` });
      msg = bi(`Added ℵ₂ Cohen reals with <span class="m">Add(ω, ω₂)</span>, a forcing of size ℵ₂. Now <span class="m">2^ℵ₀ = ℵ${'₀₁₂₃'[st.c]}</span>. The size bar stays far below κ, so by Lévy–Solovay every large cardinal on the ladder survives.`,
        `用 <span class="m">Add(ω, ω₂)</span> 添加了 ℵ₂ 个科恩实数，这个力迫的大小是 ℵ₂。现在 <span class="m">2^ℵ₀ = ℵ${'₀₁₂₃'[st.c]}</span>。大小条远低于 κ，所以由列维–索洛维定理，梯子上的每个大基数都安然无恙。`);
    } else if (kind === 'neg3') {
      st.c = 3;
      size = { y: Y.a3 };
      st.hist.push({ s: 'Add(ω,ω₃) → 2^ℵ₀=ℵ₃; κ δ λ ✓' });
      msg = bi('Added ℵ₃ Cohen reals: <span class="m">2^ℵ₀ = ℵ₃</span>. Same story: the forcing has size ℵ₃, still tiny compared to κ.', '添加 ℵ₃ 个科恩实数：<span class="m">2^ℵ₀ = ℵ₃</span>。同样的道理：力迫大小为 ℵ₃，与 κ 相比仍微不足道。');
    } else if (kind === 'pos') {
      st.c = 1;
      size = { y: cY(old) - 6 };
      st.hist.push({ s: 'Col(ω₁,2^ℵ₀) → CH; κ δ λ ✓' });
      msg = bi(`Collapsed <span class="m">2^ℵ₀</span> to ℵ₁ with <span class="m">Col(ω₁, 2^ℵ₀)</span> (countable conditions, so no new reals are added). Now CH holds. The forcing has size <span class="m">2^ℵ₀</span>, again below κ, so the large cardinals survive. You can go back and forth forever.`,
        `用 <span class="m">Col(ω₁, 2^ℵ₀)</span>（条件可数，因此不添加新实数）把 <span class="m">2^ℵ₀</span> 坍缩为 ℵ₁。现在 CH 成立。力迫大小为 <span class="m">2^ℵ₀</span>，仍低于 κ，所以大基数都幸存。你可以这样来回切换，永无止境。`);
    } else {
      size = { y: Y.kappa - 4, big: true };
      if (!st.alive.kappa) { st.busy = false; okBox($('lsInfo'), bi('κ is already collapsed. Reset to start over.', 'κ 已经被坍缩了。点“重置”重新开始。'), 'warn'); return; }
      st.alive.kappa = false;
      st.c = 1;
      st.hist.push({ s: 'Col(ω₁,κ) → CH; κ ✗, δ λ ✓' });
      msg = bi('A <b>large</b> forcing: <span class="m">Col(ω₁, κ)</span> has size κ and makes κ the new ω₂. κ is no longer measurable (it is not even inaccessible). But note: δ and λ are <b>above</b> the forcing, so Lévy–Solovay still protects them. Large cardinals are destroyed only by forcings that reach up to them; CH is decided by forcings that stay at the bottom.',
        '一个<b>大</b>力迫：<span class="m">Col(ω₁, κ)</span> 的大小是 κ，它让 κ 变成新的 ω₂。κ 不再可测（甚至不再不可达）。但请注意：δ 和 λ 位于力迫<b>之上</b>，列维–索洛维定理仍然保护着它们。只有“够得着”大基数的力迫才会摧毁它；而 CH 由停留在底层的力迫就能决定。');
    }
    // animate size bar growth then marker
    await animate(650, u => {
      const y = 360 - (360 - size.y) * u;
      draw(old, { y, big: size.big });
    });
    await animate(500, u => draw(cY(old) + (cY(st.c) - cY(old)) * u, size, u === 1));
    draw(st.c, size, true);
    okBox($('lsInfo'), msg, kind === 'big' ? 'warn' : 'info');
    st.busy = false;
  }
  $('lsNeg').addEventListener('click', () => act('neg'));
  $('lsNeg3').addEventListener('click', () => act('neg3'));
  $('lsPos').addEventListener('click', () => act('pos'));
  $('lsBig').addEventListener('click', () => act('big'));
  $('lsReset').addEventListener('click', reset);
  reset();
  checkYourself('cy2', ['Why can\'t “there is a supercompact cardinal” decide CH?', '为什么“存在超紧基数”判定不了 CH？'], [
    ['Because supercompacts are inconsistent', '因为超紧基数不一致', false],
    ['Because CH and ¬CH can both be forced by posets much smaller than the supercompact, and small forcing preserves it', '因为 CH 与 ¬CH 都能用比超紧基数小得多的偏序力迫出来，而小力迫保持超紧性', true],
    ['Because supercompacts imply CH', '因为超紧基数推出 CH', false, 'No: they are compatible with both CH and ¬CH.', '不对：它们与 CH 和 ¬CH 都相容。'],
  ], ['Exactly: the Lévy–Solovay phenomenon. CH is a “small” statement; large cardinals are invisible to small forcing.', '正是：列维–索洛维现象。CH 是“小”命题；大基数对小力迫是不可见的。']);
})();

/* ================= §3 generic absoluteness ================= */
(function genericAbs() {
  const svg = $('gaSvg');
  const levels = [
    { en: 'Arithmetic (statements about ℕ)', zh: '算术（关于 ℕ 的命题）', ex: 'e.g. Goldbach, Con(ZFC)', exz: '如哥德巴赫猜想、Con(ZFC)' },
    { en: 'Σ¹₂ / Π¹₂', zh: 'Σ¹₂ / Π¹₂', ex: 'e.g. “this recursive order is a well-order”', exz: '如“这个递归序是良序”' },
    { en: 'Σ¹₃ / Π¹₃', zh: 'Σ¹₃ / Π¹₃', ex: 'e.g. “there is a non-constructible real”', exz: '如“存在不可构成的实数”' },
    { en: 'All projective statements', zh: '全体投影命题', ex: 'e.g. “all projective sets are Lebesgue measurable”', exz: '如“所有投影集都勒贝格可测”' },
    { en: 'Theory of L(ℝ)', zh: 'L(ℝ) 的理论', ex: 'e.g. “AD holds in L(ℝ)”', exz: '如“L(ℝ) 满足 AD”' },
    { en: 'Σ²₁ (sets of reals, ∃ A ⊆ ℝ …)', zh: 'Σ²₁（实数集层次，∃ A ⊆ ℝ …）', ex: 'e.g. CH', exz: '如 CH' },
    { en: 'Beyond Σ²₁', zh: 'Σ²₁ 之上', ex: 'e.g. 2^ℵ₁ = ℵ₂', exz: '如 2^ℵ₁ = ℵ₂' },
  ];
  const settings = [
    { en: 'ZFC only', zh: '仅 ZFC', frozen: 2 },
    { en: '+ proper class of measurables', zh: '+ 真类多个可测基数', frozen: 3 },
    { en: '+ proper class of Woodins', zh: '+ 真类多个伍丁基数', frozen: 5 },
    { en: '+ proper class of measurable Woodins', zh: '+ 真类多个可测伍丁基数', frozen: 5, ch: true },
    { en: '+ any known large cardinals', zh: '+ 任何已知大基数', frozen: 5, ch: true },
  ];
  const info = [
    ['In ZFC alone: arithmetic statements can\'t change (forcing adds no natural numbers), and Shoenfield absoluteness freezes Σ¹₂. A Cohen real already changes Σ¹₃ facts: over L it adds a non-constructible real.',
      '仅 ZFC：算术命题不会变（力迫不添加自然数），Shoenfield 绝对性冻结了 Σ¹₂。一个科恩实数就能改变 Σ¹₃ 事实：在 L 上它添加了一个不可构成的实数。'],
    ['If every set has a sharp (e.g. a proper class of measurables), Σ¹₃ statements are absolute for set forcing (Martin–Solovay). Higher projective levels can still move.',
      '若每个集合都有升号（例如存在真类多个可测基数），则 Σ¹₃ 命题对集合力迫绝对（Martin–Solovay）。更高的投影层仍可能变动。'],
    ['With a proper class of Woodin cardinals, the whole theory of L(ℝ), including every projective statement, is the same in every set-forcing extension (Woodin). The Σ²₁ level is still open to forcing: CH can be switched on and off (§2).',
      '有真类多个伍丁基数时，整个 L(ℝ) 的理论（包括每个投影命题）在每个集合力迫扩张中都相同（伍丁）。Σ²₁ 层依然对力迫敞开：CH 可以随意开关（§2）。'],
    ['Woodin\'s Σ²₁ theorem: with a proper class of measurable Woodins, CH “decides” Σ²₁. Among forcing extensions that satisfy CH, every Σ²₁ sentence has the same truth value. Tick “assume CH” to see it. Without CH, Σ²₁ stays unfrozen.',
      '伍丁的 Σ²₁ 定理：有真类多个可测伍丁基数时，CH “判定”了 Σ²₁。在满足 CH 的力迫扩张之间，每个 Σ²₁ 语句真值相同。勾选“假设 CH”即可看到。不假设 CH 时，Σ²₁ 依然未被冻结。'],
    ['Stronger large cardinals add nothing at Σ²₁: by Lévy–Solovay, CH itself, a Σ²₁ sentence, can still be forced either way. The boundary between “settled by large cardinals” and “not” lies exactly between L(ℝ) and Σ²₁.',
      '更强的大基数在 Σ²₁ 层什么也加不了：由列维–索洛维定理，CH 本身（一个 Σ²₁ 语句）仍可被力迫成真或假。“由大基数判定”与“判定不了”的分界线，恰好位于 L(ℝ) 与 Σ²₁ 之间。'],
  ];
  function draw() {
    const s = +$('gaSlider').value, set = settings[s], ch = $('gaCH').checked;
    $('gaName').innerHTML = bil(set.en, set.zh);
    svg.innerHTML = '';
    const H = 48, X0 = 40, W = 620;
    levels.forEach((lv, i) => {
      const y = 360 - (i + 1) * H;
      const frozen = i < set.frozen;
      const cond = !frozen && i === 5 && set.ch && ch;
      const fill = frozen ? '#d0ebff' : cond ? '#e5dbff' : '#f8f9fa';
      const stroke = frozen ? '#1c7ed6' : cond ? '#7048e8' : '#ced4da';
      const g = el('g', { class: 'pop' }, svg);
      g.style.animationDelay = (i * 0.04) + 's';
      el('rect', { x: X0, y, width: W, height: H - 6, rx: 9, fill, stroke, 'stroke-width': 2 }, g);
      T(g, X0 + 14, y + 18, `${lv.en} · ${lv.zh}`, { 'font-size': 13.5, 'font-weight': 700 });
      T(g, X0 + 14, y + 35, `${lv.ex} · ${lv.exz}`, { 'font-size': 11.5, fill: C.muted });
      T(g, X0 + W - 16, y + 26, frozen ? '🔒 frozen · 冻结' : cond ? '🔒 if CH · 若 CH' : '↕ can change · 可变', { 'font-size': 12.5, 'text-anchor': 'end', 'font-weight': 700, fill: frozen ? '#1c7ed6' : cond ? '#7048e8' : C.muted });
      if (i === 5) {
        el('rect', { x: X0 + W + 14, y: y + 4, width: 150, height: H - 14, rx: 8, fill: C.goldSoft, stroke: C.gold }, svg);
        T(svg, X0 + W + 24, y + 22, 'CH lives here', { 'font-size': 12, 'font-weight': 700, fill: '#8a5a00' });
        T(svg, X0 + W + 24, y + 37, 'CH 在这一层', { 'font-size': 12, fill: '#8a5a00' });
      }
    });
    // boundary line between L(ℝ) and Σ²₁
    const yb = 360 - 5 * H - 3;
    el('line', { x1: X0 - 20, x2: X0 + W + 20, y1: yb, y2: yb, stroke: C.fal, 'stroke-width': 2.5, 'stroke-dasharray': '8 5' }, svg);
    T(svg, X0 + W + 24, yb + 18, 'large-cardinal', { 'font-size': 11.5, fill: C.fal, 'font-weight': 700 });
    T(svg, X0 + W + 24, yb + 33, 'boundary · 大基数的边界', { 'font-size': 11.5, fill: C.fal, 'font-weight': 700 });
    T(svg, X0, 384, 'frozen = unchanged by any set forcing · 冻结＝任何集合力迫都改变不了；if CH = unchanged among models of CH · 若 CH＝在满足 CH 的模型之间不变', { 'font-size': 11.5, fill: C.muted });
    okBox($('gaInfo'), bi(info[s][0], info[s][1]) + (s >= 3 && ch ? bi('<br><b>CH assumed:</b> the Σ²₁ band is now frozen <i>conditionally</i>, among extensions that satisfy CH.', '<br><b>已假设 CH：</b>Σ²₁ 带现在被<i>有条件地</i>冻结，即在满足 CH 的扩张之间不变。') : ''), 'info');
  }
  $('gaSlider').addEventListener('input', draw);
  $('gaCH').addEventListener('change', draw);
  draw();
  checkYourself('cy3', ['Assume a proper class of Woodin cardinals. Which can still be changed by set forcing?', '设存在真类多个伍丁基数。下列哪个仍能被集合力迫改变？'], [
    ['“Every projective set is Lebesgue measurable”', '“每个投影集都勒贝格可测”', false, 'That is a statement about L(ℝ), so it is frozen (and true).', '这是关于 L(ℝ) 的命题，已被冻结（且为真）。'],
    ['“AD holds in L(ℝ)”', '“L(ℝ) 满足 AD”', false],
    ['CH', 'CH', true],
  ], ['Right. CH is Σ²₁, one level above L(ℝ), and small forcing toggles it.', '对。CH 是 Σ²₁ 的，比 L(ℝ) 高一层，小力迫就能拨动它。']);
})();

/* ================= §4 forcing axioms ================= */
(function forcingAxioms() {
  const svg = $('faSvg');
  const classes = [
    { k: 'all', en: 'all forcings', zh: '所有力迫', ax: 'FA(all)', c: 'false', col: C.fal,
      d: ['FA for all forcings is <b>false</b> in ZFC: for <span class="m">Col(ω, ω₁)</span>, a filter meeting ℵ₁ dense sets would give a surjection ω → ω₁. This forcing collapses ω₁, so it certainly does not preserve stationary subsets of ω₁.',
        '对所有力迫的力迫公理在 ZFC 中<b>不成立</b>：对 <span class="m">Col(ω, ω₁)</span>，与 ℵ₁ 个稠密集相交的滤会给出一个满射 ω → ω₁。这个力迫坍缩了 ω₁，当然不保持 ω₁ 的平稳子集。'] },
    { k: 'ssp', en: 'stationary-set-preserving', zh: '保平稳集', ax: 'MM', c: 'ℵ₂', col: C.meta,
      d: ['<b>Martin\'s Maximum</b> (Foreman–Magidor–Shelah 1988): FA for all forcings that preserve stationary subsets of ω₁. Consistent relative to a supercompact. Implies <span class="m">2^ℵ₀ = ℵ₂</span>, SCH, and that the nonstationary ideal on ω₁ is saturated. This is the largest class for which the forcing axiom can hold.',
        '<b>马丁极大</b>（Foreman–Magidor–Shelah 1988）：对所有保持 ω₁ 平稳子集的力迫的力迫公理。相对于超紧基数一致。推出 <span class="m">2^ℵ₀ = ℵ₂</span>、SCH，以及 ω₁ 上的非平稳理想是饱和的。这是力迫公理可能成立的最大一类。'] },
    { k: 'semi', en: 'semiproper', zh: '半真', ax: 'SPFA', c: 'ℵ₂', col: '#7048e8',
      d: ['<b>SPFA</b>: FA for semiproper forcings. Shelah showed SPFA is equivalent to MM, even though the class is (provably) smaller.',
        '<b>SPFA</b>：对半真力迫的力迫公理。Shelah 证明了 SPFA 与 MM 等价，尽管这一类（可证地）更小。'] },
    { k: 'proper', en: 'proper', zh: '真力迫', ax: 'PFA', c: 'ℵ₂', col: C.accent,
      d: ['<b>Proper Forcing Axiom</b> (Baumgartner, consistent relative to a supercompact, 1984). Proper forcings preserve ω₁ and include ccc and countably closed forcings. PFA ⇒ <span class="m">2^ℵ₀ = ℵ₂</span> (Todorčević; Veličković), PFA ⇒ OCA and SCH (Viale 2006). Exact consistency strength: <b>open</b>.',
        '<b>真力迫公理</b>（Baumgartner，相对于超紧基数一致，1984）。真力迫保持 ω₁，包括 ccc 力迫和可数闭力迫。PFA ⇒ <span class="m">2^ℵ₀ = ℵ₂</span>（Todorčević；Veličković），PFA ⇒ OCA 与 SCH（Viale 2006）。精确的一致性强度：<b>未解决</b>。'] },
    { k: 'ccc', en: 'ccc', zh: 'ccc', ax: 'MA<sub>ℵ₁</sub>', c: '≥ℵ₂', col: C.tru,
      d: ['<b>Martin\'s Axiom MA<sub>ℵ₁</sub></b>: FA for ccc forcings. Consistent relative to ZFC alone, no large cardinals needed. Implies <span class="m">2^ℵ₀ ≥ ℵ₂</span> (so ¬CH), Suslin\'s Hypothesis, and that all ℵ₁-sized unions of null sets are null. But <span class="m">2^ℵ₀</span> can be ℵ₂, ℵ₃, or any regular cardinal: MA does not pin it down.',
        '<b>马丁公理 MA<sub>ℵ₁</sub></b>：对 ccc 力迫的力迫公理。仅相对于 ZFC 就一致，不需要大基数。推出 <span class="m">2^ℵ₀ ≥ ℵ₂</span>（从而 ¬CH）、苏斯林假设，以及 ℵ₁ 个零测集之并仍零测。但 <span class="m">2^ℵ₀</span> 可以是 ℵ₂、ℵ₃ 或任何正则基数：MA 并不把它钉死。'] },
  ];
  const nodes = [];
  function draw(sel) {
    svg.innerHTML = '';
    const cx = 250, cy = 170;
    classes.forEach((c, i) => {
      const w = 470 - i * 82, h = 300 - i * 52;
      const g = el('g', { class: 'node2' + (sel === c.k ? ' sel' : '') }, svg);
      el('rect', { x: cx - w / 2, y: cy - h / 2, width: w, height: h, rx: 22, fill: i === 0 ? '#fff5f5' : '#fff', 'fill-opacity': i === 0 ? 1 : .92, stroke: c.col, 'stroke-width': sel === c.k ? 4 : 2, 'stroke-dasharray': i === 0 ? '7 5' : '' }, g);
      T(g, cx - w / 2 + 14, cy - h / 2 + 20, `${c.en} · ${c.zh}`, { 'font-size': 12.5, 'font-weight': 700, fill: c.col });
      T(g, cx + w / 2 - 14, cy - h / 2 + 20, c.ax, { 'font-size': 12.5, 'font-weight': 800, fill: c.col, 'text-anchor': 'end', 'font-family': 'var(--mono)' });
      g.addEventListener('click', e => { e.stopPropagation(); pick(c.k); });
    });
    // continuum dial on the right
    const X = 560;
    T(svg, X, 34, 'What it says about 2^ℵ₀ · 对 2^ℵ₀ 的结论', { 'font-size': 13, 'font-weight': 700 });
    const vals = ['ℵ₁', 'ℵ₂', 'ℵ₃', 'ℵ₄', '…'];
    const c = classes.find(x => x.k === sel);
    vals.forEach((v, i) => {
      const y = 70 + i * 46;
      let on = false;
      if (c) on = c.c === 'ℵ₂' ? i === 1 : c.c === '≥ℵ₂' ? i >= 1 : false;
      el('rect', { x: X, y, width: 120, height: 34, rx: 8, fill: on ? C.truSoft : '#f1efe7', stroke: on ? C.tru : '#ccc', 'stroke-width': on ? 2.5 : 1 }, svg);
      T(svg, X + 60, y + 23, v, { 'font-size': 16, 'text-anchor': 'middle', 'font-weight': 700, 'font-family': 'var(--mono)', fill: on ? '#1b5e20' : C.muted });
    });
    if (c) {
      const msg = c.c === 'false' ? 'axiom is FALSE · 公理为假' : c.c === '≥ℵ₂' ? 'any value ≥ ℵ₂ (regular) · 任意 ≥ ℵ₂（正则）' : 'exactly ℵ₂ · 恰为 ℵ₂';
      T(svg, X + 135, 140, msg, { 'font-size': 12, fill: c.c === 'false' ? C.fal : C.ink, 'font-weight': 700 });
    } else T(svg, X + 135, 140, '← click a class · 点击一类', { 'font-size': 12, fill: C.muted });
  }
  function pick(k) {
    draw(k);
    const c = classes.find(x => x.k === k);
    okBox($('faInfo'), bi(c.d[0], c.d[1]), k === 'all' ? 'warn' : 'info');
  }
  draw(null);
  okBox($('faInfo'), bi('Inner boxes are smaller classes (weaker axioms). Click one.', '越靠内的框是越小的类（越弱的公理）。点击其中一个。'), 'info');
  checkYourself('cy4', ['Which is true?', '下列哪个正确？'], [
    ['MA<sub>ℵ₁</sub> implies 2^ℵ₀ = ℵ₂', 'MA<sub>ℵ₁</sub> 推出 2^ℵ₀ = ℵ₂', false, 'MA<sub>ℵ₁</sub> only gives 2^ℵ₀ ≥ ℵ₂; it is consistent with 2^ℵ₀ = ℵ₃.', 'MA<sub>ℵ₁</sub> 只给出 2^ℵ₀ ≥ ℵ₂；它与 2^ℵ₀ = ℵ₃ 相容。'],
    ['PFA implies 2^ℵ₀ = ℵ₂', 'PFA 推出 2^ℵ₀ = ℵ₂', true],
    ['PFA is known to be equiconsistent with a supercompact', '已知 PFA 与超紧基数等一致', false, 'Only the upper bound is known. The exact strength is open.', '只知道上界。精确强度尚未解决。'],
  ], ['Right (Todorčević, Veličković). Note the asymmetry: we know PFA\'s consequences well, but not its exact consistency strength.', '对（Todorčević、Veličković）。注意这种不对称：我们很清楚 PFA 的推论，却不知道它的精确一致性强度。']);
})();

/* ================= §5 the fork ================= */
(function fork() {
  const svg = $('fkSvg');
  const years = ['1963', '1988', '1999–2001', '2010s', '2021', '2025–26'];
  const nodes = [
    { id: 'root', yr: 0, x: 430, y: 385, w: 300, en: 'ZFC + large cardinals', zh: 'ZFC + 大基数', st: 'ind',
      d: ['CH is independent of ZFC (Gödel 1938, Cohen 1963) and of ZFC + any standard large cardinal (Lévy–Solovay 1967).', 'CH 独立于 ZFC（哥德尔 1938，科恩 1963），也独立于 ZFC + 任一标准大基数（列维–索洛维 1967）。'] },
    { id: 'max', yr: 1, x: 250, y: 305, w: 250, en: 'Maximize: forcing axioms', zh: '极大化：力迫公理', st: 'thm',
      d: ['Foreman–Magidor–Shelah (1988): MM is consistent from a supercompact and implies 2^ℵ₀ = ℵ₂. Motivation: the universe should contain everything that could be forced to exist.', 'Foreman–Magidor–Shelah（1988）：MM 相对于超紧基数一致，并推出 2^ℵ₀ = ℵ₂。动机：凡是能力迫出来的东西，宇宙里都应该有。'] },
    { id: 'star', yr: 2, x: 150, y: 225, w: 250, en: '(*) via ℙ<sub>max</sub> (Woodin 1999)', zh: '(*)，经由 ℙ<sub>max</sub>（伍丁 1999）', st: 'thm',
      d: ['Woodin\'s axiom (*): L(P(ω₁)) is a ℙ<sub>max</sub>-extension of L(ℝ) (with AD in L(ℝ)). It implies 2^ℵ₀ = ℵ₂ and makes H(ω₂) Π₂-maximal.', '伍丁的 (*) 公理：L(P(ω₁)) 是 L(ℝ) 的 ℙ<sub>max</sub>-扩张（且 L(ℝ) 满足 AD）。它推出 2^ℵ₀ = ℵ₂，并使 H(ω₂) 是 Π₂-极大的。'] },
    { id: 'omega', yr: 2, x: 410, y: 225, w: 230, en: 'Ω-logic argument (2001)', zh: 'Ω-逻辑论证（2001）', st: 'prog',
      d: ['Woodin (2001): assuming the (strong) Ω Conjecture, any axiom making the theory of H(ω₂) Ω-complete must imply ¬CH. This was an argument <b>against</b> CH. The Ω Conjecture remains <b>open</b>.', '伍丁（2001）：假设（强）Ω 猜想，任何使 H(ω₂) 的理论 Ω-完全的公理都必然推出 ¬CH。这是一个<b>反对</b> CH 的论证。Ω 猜想仍<b>未解决</b>。'] },
    { id: 'as', yr: 4, x: 150, y: 145, w: 250, en: 'MM⁺⁺ ⇒ (*) (Asperó–Schindler)', zh: 'MM⁺⁺ ⇒ (*)（Asperó–Schindler）', st: 'thm',
      d: ['Annals of Mathematics 2021: the two routes to ℵ₂ merge. Quanta (2021) called it a unification of two rival axioms.', '《数学年刊》2021：通往 ℵ₂ 的两条路线汇合了。Quanta（2021）称之为两条竞争公理的统一。'] },
    { id: 'aleph2', yr: 1, x: 150, y: 60, w: 220, en: '2^ℵ₀ = ℵ₂', zh: '2^ℵ₀ = ℵ₂', st: 'leaf', col: C.accent,
      d: ['The forcing-axiom answer to the continuum problem.', '力迫公理对连续统问题的回答。'] },
    { id: 'can', yr: 3, x: 670, y: 305, w: 250, en: 'Canonical: L-like inner models', zh: '典范：像 L 的内模型', st: 'prog',
      d: ['Motivation: V = L settled CH and much more, but it refutes measurable cardinals. Can one find an L-like axiom compatible with all large cardinals?', '动机：V = L 判定了 CH 以及更多问题，但它否定可测基数。能否找到一条像 L 一样、又与所有大基数相容的公理？'] },
    { id: 'ul', yr: 3, x: 670, y: 225, w: 250, en: 'V = Ultimate L ⇒ CH', zh: 'V = 终极 L ⇒ CH', st: 'thm',
      d: ['Theorem (Woodin): the axiom V = Ultimate L implies CH and V = HOD. Whether the axiom is compatible with all large cardinals is the open Ultimate-L Conjecture.', '定理（伍丁）：公理 V = 终极 L 推出 CH 与 V = HOD。它能否与所有大基数相容，就是尚未解决的终极 L 猜想。'] },
    { id: 'ulc', yr: 5, x: 670, y: 145, w: 250, en: 'Ultimate-L Conjecture', zh: '终极 L 猜想', st: 'open',
      d: ['Open as of 2026. Woodin\'s Takagi Lectures (2025, published 2026) present the AD⁺ duality program as a route to it, linked to the HOD Conjecture (§7).', '截至 2026 年仍未解决。伍丁的高木讲座（2025 年，2026 年发表）把 AD⁺ 对偶纲领作为通向它的路线，并与 HOD 猜想（§7）相联系。'] },
    { id: 'aleph1', yr: 3, x: 670, y: 60, w: 220, en: '2^ℵ₀ = ℵ₁ (CH)', zh: '2^ℵ₀ = ℵ₁（CH）', st: 'leaf', col: C.meta,
      d: ['The Ultimate-L answer to the continuum problem.', '终极 L 对连续统问题的回答。'] },
  ];
  const edges = [['root', 'max'], ['max', 'star'], ['max', 'omega'], ['star', 'as'], ['as', 'aleph2'], ['root', 'can'], ['can', 'ul'], ['ul', 'ulc'], ['ulc', 'aleph1']];
  const stCol = { thm: C.tru, ind: C.accent, open: C.gold, prog: C.meta, leaf: C.ink };
  let selId = null;
  function draw() {
    const yi = +$('fkYear').value;
    $('fkYearLab').textContent = years[yi];
    svg.innerHTML = '';
    const byId = Object.fromEntries(nodes.map(n => [n.id, n]));
    edges.forEach(([a, b]) => {
      const A = byId[a], B = byId[b];
      if (B.yr > yi) return;
      el('path', { d: `M${A.x},${A.y - 21} C${A.x},${(A.y + B.y) / 2} ${B.x},${(A.y + B.y) / 2} ${B.x},${B.y + 21}`, fill: 'none', stroke: '#b8b3a6', 'stroke-width': 2.5 }, svg);
    });
    T(svg, 30, 405, 'maximality · 极大性', { 'font-size': 13, 'font-weight': 800, fill: C.accent });
    T(svg, 830, 405, 'canonicity · 典范性', { 'font-size': 13, 'font-weight': 800, fill: C.meta, 'text-anchor': 'end' });
    nodes.forEach(n => {
      if (n.yr > yi) return;
      const g = el('g', { class: 'node2 pop' + (selId === n.id ? ' sel' : '') }, svg);
      const col = n.col || stCol[n.st];
      el('rect', { x: n.x - n.w / 2, y: n.y - 21, width: n.w, height: 42, rx: 10, fill: n.st === 'leaf' ? col : '#fff', stroke: col, 'stroke-width': 2.2 }, g);
      T(g, n.x, n.y - 3, n.en, { 'font-size': 12.5, 'text-anchor': 'middle', 'font-weight': 700, fill: n.st === 'leaf' ? '#fff' : C.ink });
      T(g, n.x, n.y + 13, n.zh, { 'font-size': 11.5, 'text-anchor': 'middle', fill: n.st === 'leaf' ? '#fff' : C.muted });
      g.addEventListener('click', () => { selId = n.id; draw(); show(n); });
    });
    // Woodin's position marker
    if (yi >= 2) {
      const left = yi === 2;
      const wx = left ? 410 : 670, wy = left ? 225 : 225;
      const g = el('g', {}, svg);
      el('circle', { cx: wx + (left ? 132 : 142), cy: wy - 22, r: 13, fill: C.gold }, g);
      T(g, wx + (left ? 132 : 142), wy - 17, 'W', { 'font-size': 13, 'font-weight': 800, fill: '#fff', 'text-anchor': 'middle' });
      T(g, wx + (left ? 132 : 142), wy - 40, left ? 'Woodin c. 2001' : 'Woodin now', { 'font-size': 11, 'text-anchor': 'middle', fill: '#8a5a00', 'font-weight': 700 });
    }
    const yrMsg = [
      ['1963: Cohen completes the independence of CH. The fork has not appeared yet.', '1963 年：科恩完成了 CH 的独立性证明。岔路尚未出现。'],
      ['1988: Martin\'s Maximum gives 2^ℵ₀ = ℵ₂. The “maximize” branch opens.', '1988 年：马丁极大给出 2^ℵ₀ = ℵ₂。“极大化”分支开启。'],
      ['1999–2001: Woodin\'s ℙ<sub>max</sub> and (*), and his Ω-logic argument against CH. Woodin (gold W) stands on the ¬CH side.', '1999–2001 年：伍丁的 ℙ<sub>max</sub> 与 (*)，以及他基于 Ω-逻辑的反 CH 论证。伍丁（金色 W）站在 ¬CH 一边。'],
      ['2010s: Woodin develops Ultimate L, proves V = Ultimate L ⇒ CH, and says he now believes CH is true. The W moves to the right branch.', '2010 年代：伍丁发展终极 L，证明 V = 终极 L ⇒ CH，并表示他现在相信 CH 为真。W 移到右支。'],
      ['2021: Asperó–Schindler prove MM⁺⁺ ⇒ (*). The left branch becomes one coherent picture.', '2021 年：Asperó–Schindler 证明 MM⁺⁺ ⇒ (*)。左支合成一幅协调的图景。'],
      ['2025–26: Woodin\'s Takagi Lectures frame the Ultimate-L Conjecture as the key open problem. Both branches are alive.', '2025–26 年：伍丁的高木讲座把终极 L 猜想定为关键的未解问题。两条分支都依然活跃。'],
    ];
    if (!selId) okBox($('fkInfo'), bi(yrMsg[yi][0], yrMsg[yi][1]), 'info');
  }
  function show(n) {
    const tag = n.st === 'leaf' ? '' : ST[n.st]() + ' ';
    okBox($('fkInfo'), tag + bi(n.d[0], n.d[1]), 'info');
  }
  $('fkYear').addEventListener('input', () => { selId = null; draw(); });
  draw();
  checkYourself('cy5', ['Which statement is a <b>theorem</b>?', '哪个是<b>定理</b>？'], [
    ['CH is true', 'CH 为真', false],
    ['V = Ultimate L implies CH', 'V = 终极 L 推出 CH', true],
    ['V = Ultimate L is consistent with a supercompact cardinal', 'V = 终极 L 与超紧基数相容', false, 'That is (part of) the Ultimate-L Conjecture: open.', '这是终极 L 猜想（的一部分）：尚未解决。'],
  ], ['Right. The implication is proved; the consistency of the antecedent with large cardinals is the open conjecture.', '对。蕴涵已证明；前件与大基数的相容性才是未解决的猜想。']);
})();

/* ================= §6 inner model frontier ================= */
(function innerModels() {
  const svg = $('imSvg');
  const years = ['1938', '1971', '1984', '1994', '1990s', '2002', '2010s', '2020s'];
  // status by year index: when proved (p), when conditional (c), when under development (u)
  const rungs = [
    { en: 'L (no large cardinals)', zh: 'L（无大基数）', p: 0, who: 'Gödel 1938' },
    { en: 'one measurable: L[U]', zh: '一个可测：L[U]', p: 1, who: 'Silver 1971; Kunen 1970' },
    { en: 'many measurables, o(κ)', zh: '多个可测、o(κ)', p: 2, who: 'Mitchell 1974–84' },
    { en: 'strong cardinals', zh: '强基数', p: 2, who: 'Mitchell; Dodd; Koepke (1980s)' },
    { en: 'one Woodin', zh: '一个伍丁', p: 3, who: 'Mitchell–Steel 1994' },
    { en: 'n and ω Woodins', zh: 'n 个和 ω 个伍丁', p: 4, who: 'Steel; Martin–Steel; Woodin' },
    { en: 'Woodin limit of Woodins', zh: '伍丁基数之极限的伍丁基数', p: 5, who: 'Neeman 2002' },
    { en: 'superstrong', zh: '超强', c: 6, who: 'fine structure; iterability assumed' },
    { en: 'subcompact', zh: '次紧', c: 6, who: 'Schimmerling–Zeman; Neeman–Steel' },
    { en: 'κ⁺ⁿ-supercompact (long extenders)', zh: 'κ⁺ⁿ-超紧（长扩张子）', u: 7, who: 'Woodin; Neeman–Steel; Schlutzenberg' },
    { en: 'supercompact', zh: '超紧', open: true, who: 'THE inner model problem' },
    { en: 'extendible, huge, I0, …', zh: '可扩、巨大、I0……', open: true, who: 'conjecturally: Ultimate L' },
  ];
  function draw() {
    const yi = +$('imYear').value;
    $('imYearLab').textContent = years[yi];
    svg.innerHTML = '';
    const X = 150, W = 420, H = 34, Y0 = 505;
    let topProved = -1, topCond = -1;
    rungs.forEach((r, i) => {
      const y = Y0 - (i + 1) * (H + 3);
      let kind = 'none';
      if (r.p !== undefined && r.p <= yi) kind = 'p';
      else if (r.c !== undefined && r.c <= yi) kind = 'c';
      else if (r.u !== undefined && r.u <= yi) kind = 'u';
      else if (r.open) kind = 'o';
      if (kind === 'p') topProved = i;
      if (kind === 'c') topCond = i;
      const fill = { p: C.truSoft, c: '#e6f4ea', u: C.goldSoft, o: '#f1f3f5', none: '#fafafa' }[kind];
      const stroke = { p: C.tru, c: C.tru, u: C.gold, o: '#adb5bd', none: '#dee2e6' }[kind];
      el('rect', { x: X, y, width: W, height: H, rx: 8, fill, stroke, 'stroke-width': 2, 'stroke-dasharray': kind === 'c' ? '6 4' : '' }, svg);
      T(svg, X + 12, y + 22, `${r.en} · ${r.zh}`, { 'font-size': 13, 'font-weight': 700, fill: kind === 'none' ? '#adb5bd' : C.ink });
      const tag = { p: 'built · 已建成', c: 'conditional · 有条件', u: 'in progress · 进行中', o: 'OPEN · 未解决', none: '' }[kind];
      T(svg, X + W + 12, y + 15, tag, { 'font-size': 11.5, 'font-weight': 700, fill: stroke });
      T(svg, X + W + 12, y + 29, kind === 'none' ? '' : r.who, { 'font-size': 11, fill: C.muted });
    });
    // frontier lines
    const yOf = i => Y0 - (i + 1) * (H + 3);
    if (topProved >= 0) {
      const y = yOf(topProved) - 2;
      el('line', { x1: X - 40, x2: X + W + 4, y1: y, y2: y, stroke: C.tru, 'stroke-width': 3.5 }, svg);
      T(svg, X - 44, y + 4, 'proved', { 'font-size': 11.5, fill: C.tru, 'font-weight': 800, 'text-anchor': 'end' });
      T(svg, X - 44, y + 18, '已证', { 'font-size': 11.5, fill: C.tru, 'font-weight': 800, 'text-anchor': 'end' });
    }
    if (topCond >= 0) {
      const y = yOf(topCond) - 2;
      el('line', { x1: X - 40, x2: X + W + 4, y1: y, y2: y, stroke: C.tru, 'stroke-width': 2.5, 'stroke-dasharray': '7 5' }, svg);
      T(svg, X - 44, y + 4, 'if iterable', { 'font-size': 11.5, fill: C.tru, 'font-weight': 700, 'text-anchor': 'end' });
      T(svg, X - 44, y + 18, '若可迭代', { 'font-size': 11.5, fill: C.tru, 'font-weight': 700, 'text-anchor': 'end' });
    }
    T(svg, X, 18, 'consistency strength ↑ · 一致性强度 ↑', { 'font-size': 12, fill: C.muted, 'font-weight': 700 });
    const msgs = [
      ['1938: Gödel\'s L, the first canonical inner model. It has no measurable cardinal (Scott 1961).', '1938 年：哥德尔的 L，第一个典范内模型。它没有可测基数（Scott 1961）。'],
      ['Around 1970: L[U] for a measurable. Kunen showed it is unique in a strong sense; it satisfies GCH.', '约 1970 年：可测基数的 L[U]。Kunen 证明它在很强的意义下唯一；它满足 GCH。'],
      ['Mitchell builds models for many measurables, up to high Mitchell order, using coherent sequences of measures.', 'Mitchell 用相干测度序列构造出含多个可测基数、直到很高 Mitchell 序的模型。'],
      ['1994: Mitchell–Steel fine structure reaches a Woodin cardinal: extender models with iteration trees.', '1994 年：Mitchell–Steel 的精细结构到达一个伍丁基数：使用迭代树的扩张子模型。'],
      ['1990s: models with finitely and infinitely many Woodins. This is the inner-model side of PD (L25): PD ⇔ these mice exist and are iterable.', '1990 年代：含有限多个和无穷多个伍丁基数的模型。这是 PD 的内模型一面（第 25 课）：PD ⇔ 这些鼠存在且可迭代。'],
      ['2002: Neeman proves iterability up to a Woodin limit of Woodin cardinals (and slightly beyond). To our knowledge, iterability proved from large cardinals alone still stops in this region, well below a superstrong cardinal.', '2002 年：Neeman 证明可迭代性直到伍丁基数之极限的伍丁基数。据我们所知，仅从大基数出发证明的可迭代性至今仍停留在这一区域，远低于超强基数。'],
      ['Fine structure reaches superstrong and subcompact cardinals, but iterability there is an extra hypothesis (dashed line).', '精细结构到达超强基数和次紧基数，但那里的可迭代性是额外假设（虚线）。'],
      ['Now: long-extender fine structure for κ⁺ⁿ-supercompactness is being developed; whether these constructions succeed is not known. A canonical inner model for a full supercompact is OPEN.', '现在：κ⁺ⁿ-超紧的长扩张子精细结构正在发展中，这些构造能否成功尚不可知。完整超紧基数的典范内模型仍<b>未解决</b>。'],
    ];
    okBox($('imInfo'), bi(msgs[yi][0], msgs[yi][1]), 'info');
  }
  $('imYear').addEventListener('input', draw);
  draw();
  checkYourself('cy6', ['What does an inner model for a large cardinal usually give us?', '大基数的内模型通常给我们带来什么？'], [
    ['A proof that the large cardinal exists in V', '大基数在 V 中存在的证明', false, 'No: inner models are built <i>from</i> large cardinals (or used to show their absence has consequences).', '不对：内模型是<i>从</i>大基数构造出来的（或用来说明大基数不存在会带来什么后果）。'],
    ['Lower bounds on consistency strength, via core models', '通过核心模型得到一致性强度的下界', true],
    ['A proof that V = L', 'V = L 的证明', false],
  ], ['Yes. Core model theory turns “statement S holds” into “an inner model with a certain large cardinal exists”, giving equiconsistencies.', '是的。核心模型理论把“命题 S 成立”转化为“存在含某大基数的内模型”，由此得到等一致性。']);
})();

/* ================= §7 HOD dichotomy ================= */
(function hod() {
  const svg = $('hodSvg');
  let mode = 'close';
  // cardinals above δ: s = singular, r = regular (successor of singular marked)
  const cards = [
    { x: 150, lab: 'δ', kind: 'd' },
    { x: 250, lab: 'μ', kind: 'r', note: 'regular' },
    { x: 370, lab: 'γ', kind: 's', note: 'singular' },
    { x: 470, lab: 'γ⁺', kind: 'r', succ: true },
    { x: 590, lab: 'ν', kind: 'r' },
    { x: 700, lab: 'γ′', kind: 's' },
    { x: 790, lab: 'γ′⁺', kind: 'r', succ: true },
  ];
  function draw() {
    svg.innerHTML = '';
    const yV = 70, yH = 190;
    const isL = mode === 'L';
    T(svg, 30, yV + 5, 'V', { 'font-size': 18, 'font-weight': 800 });
    T(svg, 30, yH + 5, isL ? 'L' : 'HOD', { 'font-size': 16, 'font-weight': 800, fill: C.meta });
    [yV, yH].forEach(y => el('line', { x1: 90, x2: 840, y1: y, y2: y, stroke: y === yV ? C.ink : C.meta, 'stroke-width': 2.5 }, svg));
    const far = mode !== 'close';
    cards.forEach((c, i) => {
      if (isL && c.kind === 'd') return;
      // V tick
      el('line', { x1: c.x, x2: c.x, y1: yV - 8, y2: yV + 8, stroke: C.ink, 'stroke-width': 2 }, svg);
      T(svg, c.x, yV - 16, c.lab, { 'font-size': 15, 'font-weight': 700, 'text-anchor': 'middle', 'font-family': 'var(--mono)' });
      T(svg, c.x, yV + 26, c.kind === 's' ? 'singular · 奇异' : c.kind === 'r' ? 'regular · 正则' : 'extendible', { 'font-size': 10.5, 'text-anchor': 'middle', fill: C.muted });
      // connection
      const good = !far || c.kind === 'd';
      el('line', { x1: c.x, x2: c.x, y1: yV + 34, y2: yH - 30, stroke: good ? C.tru : C.fal, 'stroke-width': 2, 'stroke-dasharray': good ? '' : '5 4' }, svg);
      // HOD tick
      el('line', { x1: c.x, x2: c.x, y1: yH - 8, y2: yH + 8, stroke: C.meta, 'stroke-width': 2 }, svg);
      let lab2;
      if (c.kind === 'd') lab2 = 'δ';
      else if (!far) lab2 = c.kind === 's' ? 'singular ✓' : c.succ ? '= (γ⁺)^HOD ✓' : 'regular';
      else lab2 = isL ? 'inaccessible in L ★' : 'measurable in HOD ★';
      T(svg, c.x, yH + 26, lab2, { 'font-size': 10.5, 'text-anchor': 'middle', fill: far && c.kind !== 'd' ? C.fal : C.meta, 'font-weight': 700 });
      if (far && c.kind !== 'd') {
        T(svg, c.x, yH - 14, '★', { 'font-size': 18, 'text-anchor': 'middle', fill: C.gold });
      }
      if (far && c.succ) {
        // HOD's successor of γ falls short of the real one
        const xs = c.x - 45;
        el('line', { x1: xs, x2: xs, y1: yH - 6, y2: yH + 6, stroke: C.meta, 'stroke-width': 2 }, svg);
        T(svg, xs, yH + 44, isL ? '(γ⁺)^L' : '(γ⁺)^HOD', { 'font-size': 10.5, 'text-anchor': 'middle', fill: C.meta, 'font-weight': 700 });
        el('path', { d: `M${xs},${yH + 32} L${c.x - 4},${yH + 32}`, stroke: C.fal, 'stroke-width': 1.5, 'marker-end': '' }, svg);
        T(svg, (xs + c.x) / 2, yH + 58, '<', { 'font-size': 13, 'text-anchor': 'middle', fill: C.fal, 'font-weight': 800 });
      }
    });
    const caption = mode === 'close'
      ? 'Case (1): HOD is “close” — singulars stay singular, successors are computed correctly · 情形 (1)：HOD 接近 V'
      : mode === 'far' ? 'Case (2): HOD is “far” — every regular γ > δ is ω-strongly measurable in HOD · 情形 (2)：HOD 远离 V'
        : 'Jensen for L: if 0# exists, every uncountable V-cardinal is inaccessible in L · L 的 Jensen 二分';
    T(svg, 430, 262, caption, { 'font-size': 12.5, 'text-anchor': 'middle', 'font-weight': 700, fill: mode === 'close' ? C.tru : C.fal });
    const msgs = {
      close: ['Case (1): above δ, HOD agrees with V about which cardinals are singular and computes successors of singular cardinals correctly. Woodin also shows this is equivalent to HOD being a weak extender model for “δ is supercompact”: HOD inherits supercompactness. The HOD Conjecture predicts this case.',
        '情形 (1)：在 δ 之上，HOD 与 V 对哪些基数是奇异的看法一致，并能正确计算奇异基数的后继。伍丁还证明这等价于 HOD 是“δ 超紧”的弱扩张子模型：HOD 继承了超紧性。HOD 猜想预言的就是这种情形。'],
      far: ['Case (2): every regular cardinal above δ is ω-strongly measurable in HOD, so measurable there. In particular HOD gets γ⁺ wrong for singular γ: the true γ⁺ is regular, hence measurable (so a limit cardinal) in HOD. HOD is then radically far from V.',
        '情形 (2)：δ 之上每个正则基数在 HOD 中都是 ω-强可测的，从而在那里可测。特别地，对奇异的 γ，HOD 会把 γ⁺ 算错：真正的 γ⁺ 是正则的，因此在 HOD 中可测（从而是极限基数）。此时 HOD 与 V 天差地别。'],
      L: ['The model for this theorem: Jensen\'s covering lemma for L. Either L computes successors of singular cardinals correctly (no 0#), or 0# exists and then every uncountable cardinal of V is inaccessible in L. For L, the “far” side really happens (with a measurable). For HOD, no analogue of 0# is known, which is why the HOD Conjecture is plausible.',
        '这个定理的原型：L 的 Jensen 覆盖引理。要么 L 能正确计算奇异基数的后继（0# 不存在），要么 0# 存在，此时 V 的每个不可数基数在 L 中都是不可达的。对 L 而言，“远离”一侧确实会发生（只要有一个可测基数）。对 HOD 而言，目前不知道有 0# 的类似物，这正是 HOD 猜想看起来可信的原因。'],
    };
    okBox($('hodInfo'), bi(msgs[mode][0], msgs[mode][1]), mode === 'close' ? 'ok' : 'warn');
  }
  const btns = { close: $('hodClose'), far: $('hodFar'), L: $('hodL') };
  Object.entries(btns).forEach(([k, b]) => b.addEventListener('click', () => {
    mode = k;
    Object.values(btns).forEach(x => x.classList.remove('sel'));
    b.classList.add('sel');
    draw();
  }));
  draw();
  checkYourself('cy7', ['Assume an extendible δ. If HOD computes γ⁺ correctly for even <b>one</b> singular γ > δ, which case holds?', '设 δ 可扩。如果对<b>某一个</b>奇异 γ > δ，HOD 正确算出了 γ⁺，那么哪种情形成立？'], [
    ['Case (1)', '情形 (1)', true],
    ['Case (2)', '情形 (2)', false, 'In case (2), γ⁺ (regular in V) would be measurable in HOD, so HOD could not think it is a successor.', '在情形 (2) 中，γ⁺（在 V 中正则）在 HOD 中会可测，HOD 就不可能认为它是后继基数。'],
    ['Cannot tell', '无法判断', false],
  ], ['Case (1). The dichotomy is all-or-nothing: one correct successor above δ already rules out case (2).', '情形 (1)。二分是“全有或全无”的：δ 之上只要有一个后继算对了，就排除了情形 (2)。']);
})();

/* ================= §8 choiceless cardinals ================= */
(function choiceless() {
  const svg = $('acSvg');
  const v = { AC: 1 };
  const rungs = [
    { en: 'measurable', zh: '可测', z: 'ok' },
    { en: 'Woodin', zh: '伍丁', z: 'ok' },
    { en: 'supercompact', zh: '超紧', z: 'ok' },
    { en: 'extendible', zh: '可扩', z: 'ok' },
    { en: 'huge', zh: '巨大', z: 'ok' },
    { en: 'I3, I1', zh: 'I3、I1', z: 'ok' },
    { en: 'I0: j : L(V<sub>λ+1</sub>) → L(V<sub>λ+1</sub>)', zh: 'I0', z: 'ok' },
    { wall: true },
    { en: 'j : V<sub>λ+2</sub> → V<sub>λ+2</sub>', zh: '', z: 'v2', d: ['Refuted by Kunen\'s argument under AC. In ZF: consistent relative to ZFC + I0 (Schlutzenberg).', '在 AC 下被库能的论证否证。在 ZF 中：相对于 ZFC + I0 一致（Schlutzenberg）。'] },
    { en: 'Reinhardt: j : V → V', zh: 'Reinhardt 基数', z: 'open', d: ['ZFC refutes it (Kunen 1971). ZF + Reinhardt: consistency OPEN. With DC it implies Con(ZFC + I0) (Goldberg). A 2026 claimed refutation was withdrawn.', 'ZFC 否证它（库能 1971）。ZF + Reinhardt：一致性未解决。加上 DC 时它推出 Con(ZFC + I0)（Goldberg）。2026 年一个声称的否证已撤回。'] },
    { en: 'super Reinhardt', zh: '超 Reinhardt', z: 'open', d: ['κ is super Reinhardt if for every λ there is j : V → V with crit κ and j(κ) > λ. ZF-consistency OPEN.', '若对每个 λ 都有临界点为 κ、且 j(κ) > λ 的 j : V → V，则称 κ 为超 Reinhardt 基数。在 ZF 中的一致性未解决。'] },
    { en: 'Berkeley', zh: 'Berkeley 基数', z: 'open', d: ['Introduced by Woodin; studied by Bagaria–Koellner–Woodin (2019). Even stronger. ZF-consistency OPEN; BKW argue that if they are consistent, the (weak) Ultimate-L Conjecture fails.', '由伍丁提出，Bagaria–Koellner–Woodin（2019）系统研究。更强。在 ZF 中的一致性未解决；BKW 论证：如果它们一致，（弱）终极 L 猜想就不成立。'] },
  ];
  let sel = null;
  function draw() {
    svg.innerHTML = '';
    const ac = !!v.AC;
    const X = 200, W = 380, H = 28, Y0 = 425;
    rungs.forEach((r, i) => {
      const y = Y0 - (i + 1) * (H + 4);
      if (r.wall) {
        el('rect', { x: X - 40, y: y + 4, width: W + 80, height: H - 8, rx: 4, fill: ac ? '#495057' : '#dee2e6', stroke: ac ? '#212529' : '#adb5bd', 'stroke-dasharray': ac ? '' : '6 4' }, svg);
        for (let k = 0; k < 14; k++) el('line', { x1: X - 30 + k * 32, x2: X - 30 + k * 32, y1: y + 4, y2: y + H - 4, stroke: ac ? '#868e96' : '#ced4da' }, svg);
        T(svg, X + W / 2, y + 19, ac ? 'Kunen\'s wall (needs AC) · 库能之墙（需要 AC）' : 'no AC: the wall is gone? · 无 AC：墙还在吗？', { 'font-size': 12.5, 'font-weight': 800, 'text-anchor': 'middle', fill: ac ? '#fff' : C.muted });
        return;
      }
      let fill, stroke, tag;
      if (r.z === 'ok') { fill = C.truSoft; stroke = C.tru; tag = 'not refuted · 未被否证'; }
      else if (ac) { fill = C.falSoft; stroke = C.fal; tag = '✗ refuted in ZFC · ZFC 否证'; }
      else if (r.z === 'v2') { fill = '#e6f4ea'; stroke = C.tru; tag = 'consistent rel. I0 · 相对 I0 一致'; }
      else { fill = C.goldSoft; stroke = C.gold; tag = 'OPEN in ZF · ZF 中未解决'; }
      const g = el('g', { class: 'node2' + (sel === i ? ' sel' : '') }, svg);
      el('rect', { x: X, y, width: W, height: H, rx: 7, fill, stroke, 'stroke-width': sel === i ? 3.5 : 2 }, g);
      T(g, X + 12, y + 19, r.zh ? `${r.en} · ${r.zh}` : r.en, { 'font-size': 12.5, 'font-weight': 700 });
      T(g, X + W + 12, y + 19, tag, { 'font-size': 11.5, 'font-weight': 700, fill: stroke });
      if (ac && r.z !== 'ok') el('line', { x1: X + 6, x2: X + W - 6, y1: y + H / 2, y2: y + H / 2, stroke: C.fal, 'stroke-width': 2 }, g);
      if (r.d) g.addEventListener('click', () => { sel = i; draw(); okBox($('acInfo'), bi(r.d[0], r.d[1]), 'info'); });
    });
    T(svg, X, 16, 'consistency strength ↑ · 一致性强度 ↑', { 'font-size': 12, fill: C.muted, 'font-weight': 700 });
    if (sel === null) okBox($('acInfo'), ac
      ? bi('With AC: Kunen\'s theorem refutes everything above the wall. Note: the rungs below (up to I0) are <i>not known</i> to be consistent either; we only know no proof of inconsistency, and they are widely believed consistent.', '有 AC 时：库能定理否证了墙以上的一切。注意：墙以下的阶梯（直到 I0）也<i>并未被证明</i>一致；我们只知道还没有不一致性的证明，而它们被普遍相信是一致的。')
      : bi('Without AC: Kunen\'s proof breaks down. The rungs above the wall are not refuted. Click them for their status.', '没有 AC 时：库能的证明失效了。墙以上的阶梯没有被否证。点击查看它们的状态。'), ac ? 'warn' : 'info');
  }
  Switches($('acSw'), ['AC'], v, () => { sel = null; draw(); });
  draw();
  checkYourself('cy8', ['Which is a theorem?', '哪个是定理？'], [
    ['ZF proves there is no Reinhardt cardinal', 'ZF 证明不存在 Reinhardt 基数', false, 'Open: Kunen\'s proof uses AC.', '未解决：库能的证明用到了 AC。'],
    ['ZFC proves there is no Reinhardt cardinal', 'ZFC 证明不存在 Reinhardt 基数', true],
    ['ZF + Reinhardt is consistent relative to I0', 'ZF + Reinhardt 相对于 I0 一致', false, 'Not known. Schlutzenberg\'s result is for j : V<sub>λ+2</sub> → V<sub>λ+2</sub>, a much weaker embedding.', '未知。Schlutzenberg 的结果针对的是 j : V<sub>λ+2</sub> → V<sub>λ+2</sub>，一个弱得多的嵌入。'],
  ], ['Right: Kunen 1971.', '对：库能 1971。']);
})();

/* ================= §9 cardinal arithmetic ================= */
(function cardArith() {
  // Part A: König for 2^ℵ₀
  const vals0 = [
    { s: 'ℵ₁', ok: true, en: 'Allowed: this is CH (cf ℵ₁ = ℵ₁ > ℵ₀).', zh: '可以：这就是 CH（cf ℵ₁ = ℵ₁ > ℵ₀）。' },
    { s: 'ℵ₂', ok: true, en: 'Allowed (Cohen): regular, so cofinality ℵ₂ > ℵ₀.', zh: '可以（科恩）：正则，共尾性 ℵ₂ > ℵ₀。' },
    { s: 'ℵ₁₇', ok: true, en: 'Allowed: any regular ℵₙ works.', zh: '可以：任何正则的 ℵₙ 都行。' },
    { s: 'ℵ<sub>ω</sub>', ok: false, en: 'Impossible: cf(ℵ<sub>ω</sub>) = ω, but König\'s theorem says cf(2^ℵ₀) > ℵ₀.', zh: '不可能：cf(ℵ<sub>ω</sub>) = ω，而 König 定理说 cf(2^ℵ₀) > ℵ₀。' },
    { s: 'ℵ<sub>ω+1</sub>', ok: true, en: 'Allowed: regular.', zh: '可以：正则。' },
    { s: 'ℵ<sub>ω·2</sub>', ok: false, en: 'Impossible: cofinality ω.', zh: '不可能：共尾性为 ω。' },
    { s: 'ℵ<sub>ω₁</sub>', ok: true, en: 'Allowed, even though ℵ<sub>ω₁</sub> is singular: its cofinality is ω₁ > ω. (Solovay: 2^ℵ₀ can be any κ with cf κ > ω.)', zh: '可以，尽管 ℵ<sub>ω₁</sub> 是奇异的：它的共尾性是 ω₁ > ω。（Solovay：2^ℵ₀ 可以是任何满足 cf κ > ω 的 κ。）' },
    { s: 'ℵ<sub>ω<sub>ω</sub></sub>', ok: false, en: 'Impossible: cf(ω<sub>ω</sub>) = ω.', zh: '不可能：cf(ω<sub>ω</sub>) = ω。' },
  ];
  const b0 = $('c0Btns');
  vals0.forEach(v => {
    const b = document.createElement('button');
    b.className = 'btn small';
    b.innerHTML = `<span class="m">2^ℵ₀ = ${v.s}</span>`;
    b.addEventListener('click', () => {
      b0.querySelectorAll('button').forEach(x => x.classList.remove('sel'));
      b.classList.add('sel');
      okBox($('c0Info'), (v.ok ? '✓ ' : '✗ ') + bi(v.en, v.zh), v.ok ? 'ok' : 'bad');
    });
    b0.appendChild(b);
  });
  // Part B: ℵ<sub>ω</sub> strong limit
  const svg = $('pcfSvg');
  const pts = [
    { s: 'ℵ<sub>ω</sub>', x: 40, z: 'no', en: 'Impossible: 2^κ > κ (Cantor).', zh: '不可能：2^κ > κ（康托尔）。' },
    { s: 'ℵ<sub>ω+1</sub>', x: 100, z: 'ok', en: 'Consistent: this is SCH at ℵ<sub>ω</sub>, which follows from GCH. No large cardinals needed.', zh: '一致：这就是 ℵ<sub>ω</sub> 处的 SCH，由 GCH 推出，不需要大基数。' },
    { s: 'ℵ<sub>ω+2</sub>', x: 160, z: 'ok', en: 'Consistent relative to large cardinals (Magidor 1977; Gitik–Magidor; Woodin: a (κ+2)-strong cardinal suffices for this value). Failing SCH needs the strength of o(κ) = κ⁺⁺ (Gitik).', zh: '相对于大基数一致（Magidor 1977；Gitik–Magidor；伍丁：一个 (κ+2)-强基数对这个值就够了）。SCH 失败需要 o(κ) = κ⁺⁺ 的强度（Gitik）。' },
    { s: 'ℵ<sub>ω+17</sub>', x: 222, z: 'ok', en: 'Consistent relative to large cardinals: 2^ℵ<sub>ω</sub> = ℵ<sub>ω+α+1</sub> for any countable α ≥ 1.', zh: '相对于大基数一致：对任意可数 α ≥ 1，2^ℵ<sub>ω</sub> = ℵ<sub>ω+α+1</sub> 都一致。' },
    { s: 'ℵ<sub>ω·2</sub>', x: 285, z: 'no', en: 'Impossible: by König, cf(2^ℵ<sub>ω</sub>) > ℵ<sub>ω</sub>, but cf(ℵ<sub>ω·2</sub>) = ω.', zh: '不可能：由 König 定理，cf(2^ℵ<sub>ω</sub>) > ℵ<sub>ω</sub>，而 cf(ℵ<sub>ω·2</sub>) = ω。' },
    { s: 'ℵ<sub>ω·2+1</sub>', x: 348, z: 'ok', en: 'Consistent (α = ω).', zh: '一致（α = ω）。' },
    { s: 'ℵ<sub>ω²+1</sub>', x: 412, z: 'ok', en: 'Consistent (α = ω²): still a countable index.', zh: '一致（α = ω²）：下标仍可数。' },
    { s: 'ℵ<sub>ω₁</sub>', x: 480, z: 'no', en: 'Impossible: cf(ℵ<sub>ω₁</sub>) = ω₁ < ℵ<sub>ω</sub>, violating König\'s cf(2^ℵ<sub>ω</sub>) > ℵ<sub>ω</sub>.', zh: '不可能：cf(ℵ<sub>ω₁</sub>) = ω₁ < ℵ<sub>ω</sub>，违反 König 定理 cf(2^ℵ<sub>ω</sub>) > ℵ<sub>ω</sub>。' },
    { s: 'ℵ<sub>ω₁+1</sub>', x: 545, z: 'open', en: 'OPEN. Nobody knows whether 2^ℵ<sub>ω</sub> ≥ ℵ<sub>ω₁</sub> is possible when ℵ<sub>ω</sub> is a strong limit. This is the central open problem of pcf theory.', zh: '未解决。当 ℵ<sub>ω</sub> 为强极限时，2^ℵ<sub>ω</sub> ≥ ℵ<sub>ω₁</sub> 是否可能，无人知晓。这是 pcf 理论的核心未解问题。' },
    { s: 'ℵ<sub>ω₂+1</sub>', x: 615, z: 'open', en: 'OPEN: between ℵ<sub>ω₁</sub> and Shelah\'s bound ℵ<sub>ω₄</sub>.', zh: '未解决：位于 ℵ<sub>ω₁</sub> 与 Shelah 上界 ℵ<sub>ω₄</sub> 之间。' },
    { s: 'ℵ<sub>ω₃+1</sub>', x: 685, z: 'open', en: 'OPEN: still below ℵ<sub>ω₄</sub>.', zh: '未解决：仍低于 ℵ<sub>ω₄</sub>。' },
    { s: 'ℵ<sub>ω₄</sub>', x: 752, z: 'no', en: 'Impossible: Shelah\'s theorem gives 2^ℵ<sub>ω</sub> < ℵ<sub>ω₄</sub>.', zh: '不可能：Shelah 定理给出 2^ℵ<sub>ω</sub> < ℵ<sub>ω₄</sub>。' },
    { s: 'ℵ<sub>ω₄+1</sub>', x: 818, z: 'no', en: 'Impossible: above Shelah\'s bound.', zh: '不可能：超出 Shelah 上界。' },
  ];
  const zc = { ok: C.tru, open: C.gold, no: C.fal };
  let sel = -1;
  function draw() {
    svg.innerHTML = '';
    const y = 120;
    // bands
    el('rect', { x: 70, y: y - 46, width: 445, height: 92, rx: 10, fill: C.truSoft, opacity: .5 }, svg);
    el('rect', { x: 515, y: y - 46, width: 210, height: 92, rx: 10, fill: C.goldSoft, opacity: .8 }, svg);
    el('rect', { x: 725, y: y - 46, width: 125, height: 92, rx: 10, fill: C.falSoft, opacity: .6 }, svg);
    T(svg, 80, y - 30, 'ℵ<sub>ω+α+1</sub>, α < ω₁: consistent · 一致', { 'font-size': 11.5, 'font-weight': 700, fill: '#1b5e20' });
    T(svg, 522, y - 30, 'OPEN gap · 未解决的缺口', { 'font-size': 11.5, 'font-weight': 700, fill: '#8a5a00' });
    T(svg, 730, y - 30, 'Shelah: < ℵ<sub>ω₄</sub>', { 'font-size': 11.5, 'font-weight': 700, fill: '#8a1c1c' });
    el('line', { x1: 20, x2: 850, y1: y, y2: y, stroke: C.ink, 'stroke-width': 2.5 }, svg);
    pts.forEach((p, i) => {
      const g = el('g', { class: 'node2' }, svg);
      el('circle', { cx: p.x, cy: y, r: sel === i ? 11 : 8, fill: zc[p.z], stroke: sel === i ? C.ink : '#fff', 'stroke-width': 2.5 }, g);
      T(g, p.x, i % 2 ? y + 34 : y + 22, p.s, { 'font-size': 11.5, 'text-anchor': 'middle', 'font-family': 'var(--mono)', 'font-weight': 700 });
      el('rect', { x: p.x - 26, y: y - 16, width: 52, height: 60, fill: 'transparent' }, g);
      g.addEventListener('click', () => { sel = i; draw(); okBox($('pcfInfo'), `<span class="m">2^ℵ<sub>ω</sub> = ${p.s}</span>: ` + bi(p.en, p.zh), p.z === 'ok' ? 'ok' : p.z === 'open' ? 'warn' : 'bad'); });
    });
    T(svg, 430, 215, 'not to scale: between any two marks lie many alephs · 非等比例：任意两个标记之间都有许多阿列夫', { 'font-size': 11.5, 'text-anchor': 'middle', fill: C.muted });
  }
  draw();
  okBox($('pcfInfo'), bi('Click a point on the line.', '点击数轴上的一个点。'), 'info');
  checkYourself('cy9', ['ℵ<sub>ω</sub> is a strong limit. Which value of 2^ℵ<sub>ω</sub> is <b>known to be impossible</b>?', 'ℵ<sub>ω</sub> 为强极限。2^ℵ<sub>ω</sub> 的哪个值<b>已知不可能</b>？'], [
    ['ℵ<sub>ω+5</sub>', 'ℵ<sub>ω+5</sub>', false, 'That one is consistent relative to large cardinals.', '这个值相对于大基数是一致的。'],
    ['ℵ<sub>ω₂+1</sub>', 'ℵ<sub>ω₂+1</sub>', false, 'Open: it lies in the gap between ω₁ and ω₄.', '未解决：它位于 ω₁ 与 ω₄ 之间的缺口里。'],
    ['ℵ<sub>ω₅</sub>', 'ℵ<sub>ω₅</sub>', true],
  ], ['Right: Shelah\'s bound 2^ℵ<sub>ω</sub> < ℵ<sub>ω₄</sub> excludes it (and König excludes it too, since cf = ω₅ < ℵ<sub>ω</sub>).', '对：Shelah 的上界 2^ℵ<sub>ω</sub> < ℵ<sub>ω₄</sub> 排除了它（König 定理也排除了它，因为 cf = ω₅ < ℵ<sub>ω</sub>）。']);
})();

/* ================= §10 Cichoń's diagram ================= */
const CI_POS = {
  al1: [55, 280], addN: [175, 280], addM: [345, 280], covM: [515, 280], nonN: [685, 280],
  covN: [175, 60], nonM: [345, 60], cofM: [515, 60], cofN: [685, 60], c: [810, 60],
  b: [345, 170], d: [515, 170],
};
const CI_LAB = { al1: 'ℵ₁', addN: 'add(𝓝)', addM: 'add(𝓜)', covM: 'cov(𝓜)', nonN: 'non(𝓝)', covN: 'cov(𝓝)', nonM: 'non(𝓜)', cofM: 'cof(𝓜)', cofN: 'cof(𝓝)', c: '2^ℵ₀', b: 'b', d: 'd' };
function drawCichon(svg, v, opts = {}) {
  svg.innerHTML = '';
  const res = cichonCheck(v);
  const bad = new Set(res.badEdges.map(e => e.join('>')));
  const defs = el('defs', {}, svg);
  [['ah', '#9aa0aa'], ['ahr', C.fal]].forEach(([id, col]) => {
    const m = el('marker', { id: id + (opts.sfx || ''), viewBox: '0 0 10 10', refX: 9, refY: 5, markerWidth: 7, markerHeight: 7, orient: 'auto-start-reverse' }, defs);
    el('path', { d: 'M0,0 L10,5 L0,10 Z', fill: col }, m);
  });
  CI_EDGES.forEach(([a, b]) => {
    const [x1, y1] = CI_POS[a], [x2, y2] = CI_POS[b];
    const isBad = bad.has(a + '>' + b);
    const dx = x2 - x1, dy = y2 - y1, L = Math.hypot(dx, dy);
    const ox = dx / L, oy = dy / L;
    const pad = (ux, uy) => (Math.abs(ux) > Math.abs(uy) ? 52 : 22);
    const p = pad(ox, oy);
    el('line', { x1: x1 + ox * p, y1: y1 + oy * p, x2: x2 - ox * p, y2: y2 - oy * p, stroke: isBad ? C.fal : '#9aa0aa', 'stroke-width': isBad ? 3.5 : 2, 'marker-end': `url(#${isBad ? 'ahr' : 'ah'}${opts.sfx || ''})` }, svg);
  });
  // equality badges
  const eq = (x, y, txt, ok) => {
    el('rect', { x: x - 82, y: y - 13, width: 164, height: 24, rx: 7, fill: ok ? '#fff' : C.falSoft, stroke: ok ? '#ccc' : C.fal, 'stroke-dasharray': '4 3' }, svg);
    T(svg, x, y + 4, txt, { 'font-size': 11.5, 'text-anchor': 'middle', 'font-family': 'var(--mono)', fill: ok ? C.muted : C.fal, 'font-weight': 700 });
  };
  eq(250, 325, 'add(𝓜) = min(b, cov(𝓜))', res.eqAdd);
  eq(610, 18, 'cof(𝓜) = max(d, non(𝓜))', res.eqCof);
  Object.entries(CI_POS).forEach(([k, [x, y]]) => {
    const val = k === 'al1' ? 1 : v[k];
    const g = el('g', { class: k === 'al1' || opts.static ? '' : 'cich-node' }, svg);
    el('rect', { x: x - 48, y: y - 18, width: 96, height: 36, rx: 9, fill: val === 2 ? C.accentSoft : '#fff', stroke: val === 2 ? C.accent : '#adb5bd', 'stroke-width': 2 }, g);
    T(g, x, y - 1, CI_LAB[k], { 'font-size': 13, 'text-anchor': 'middle', 'font-weight': 700, 'font-family': 'var(--mono)' });
    T(g, x, y + 13, val === 2 ? 'ℵ₂' : 'ℵ₁', { 'font-size': 11, 'text-anchor': 'middle', fill: val === 2 ? C.accent : C.muted, 'font-weight': 700 });
    if (k !== 'al1' && !opts.static && opts.onToggle) g.addEventListener('click', () => opts.onToggle(k));
  });
  return res;
}
(function cichon() {
  const v = {};
  CI_NODES.forEach(k => { v[k] = 1; });
  const presets = {
    all1: {},
    ma: Object.fromEntries(CI_NODES.map(k => [k, 2])),
    cohen: { covM: 2, d: 2, nonN: 2, cofM: 2, cofN: 2, c: 2 },
    random: { covN: 2, nonM: 2, cofM: 2, cofN: 2, c: 2 },
  };
  const pmsg = {
    all1: ['Under CH every entry is ℵ₁, trivially consistent.', '在 CH 下所有项都是 ℵ₁，平凡地一致。'],
    ma: ['Martin\'s Axiom implies add(𝓝) = 2^ℵ₀, so every entry is ℵ₂.', '马丁公理推出 add(𝓝) = 2^ℵ₀，于是所有项都是 ℵ₂。'],
    cohen: ['Add ℵ₂ Cohen reals to a CH model: the ground-model reals stay non-meager (non(𝓜) = ℵ₁), while cov(𝓜) = ℵ₂.', '在 CH 模型上添加 ℵ₂ 个科恩实数：基础模型的实数仍是非贫的（non(𝓜) = ℵ₁），而 cov(𝓜) = ℵ₂。'],
    random: ['Add ℵ₂ random reals: the dual picture, cov(𝓝) = ℵ₂ but non(𝓝) = ℵ₁, and d = ℵ₁ (random forcing is ω^ω-bounding).', '添加 ℵ₂ 个随机实数：对偶的图景，cov(𝓝) = ℵ₂ 而 non(𝓝) = ℵ₁，且 d = ℵ₁（随机力迫是 ω^ω-有界的）。'],
  };
  const svg = $('ciSvg');
  function render(extra) {
    const res = drawCichon(svg, v, { onToggle: k => { v[k] = 3 - v[k]; render(); } });
    let h;
    if (res.ok) h = '✓ ' + bi('All ZFC constraints hold. By the ℵ₁/ℵ₂ completeness theorem, this assignment is <b>consistent</b> with ZFC.', '所有 ZFC 约束都满足。由 ℵ₁/ℵ₂ 完全性定理，这个赋值与 ZFC <b>一致</b>。');
    else {
      const parts = res.badEdges.map(([a, b]) => `${CI_LAB[a]} ≤ ${CI_LAB[b]}`);
      if (!res.eqAdd) parts.push('add(𝓜) = min(b, cov(𝓜))');
      if (!res.eqCof) parts.push('cof(𝓜) = max(d, non(𝓜))');
      h = '✗ ' + bi(`Violates ZFC: <span class="m">${parts.join('; ')}</span>. Impossible in any model.`, `违反 ZFC：<span class="m">${parts.join('；')}</span>。在任何模型中都不可能。`);
    }
    okBox($('ciInfo'), (extra ? bi(extra[0], extra[1]) + '<br>' : '') + h, res.ok ? 'ok' : 'bad');
  }
  const setP = p => { CI_NODES.forEach(k => { v[k] = presets[p][k] || 1; }); render(pmsg[p]); };
  $('ciAll1').addEventListener('click', () => setP('all1'));
  $('ciMA').addEventListener('click', () => setP('ma'));
  $('ciCohen').addEventListener('click', () => setP('cohen'));
  $('ciRandom').addEventListener('click', () => setP('random'));
  $('ciRand').addEventListener('click', () => { CI_NODES.forEach(k => { v[k] = Math.random() < .5 ? 1 : 2; }); render(); });
  setP('cohen');
  checkYourself('cy10', [`Of the 2¹⁰ = 1024 ways to assign ℵ₁/ℵ₂ to the ten entries other than ℵ₁ and 2^ℵ₀ = ℵ₂, how many are consistent?`, `在 2^ℵ₀ = ℵ₂ 时，给除 ℵ₁ 与 2^ℵ₀ 外的十项赋 ℵ₁/ℵ₂ 共有 2¹⁰ = 1024 种方式，其中有多少种是一致的？`], [
    ['all 1024', '全部 1024 种', false],
    [String(cichonCount(true)), String(cichonCount(true)), true],
    ['only 2', '只有 2 种', false],
  ], [`${cichonCount(true)} (counted live by this page's checker from the ZFC arrows and equalities). The ZFC arrows cut 1024 down to ${cichonCount(true)}, and by the ℵ₁/ℵ₂ completeness theorem (Bartoszyński–Judah 1995, ch. 7) every survivor is realized by some forcing extension.`, `${cichonCount(true)} 种（由本页检查器根据 ZFC 箭头与等式实时计数）。ZFC 箭头把 1024 削减到 ${cichonCount(true)}，而由 ℵ₁/ℵ₂ 完全性定理（Bartoszyński–Judah 1995 第 7 章），每个幸存者都能由某个力迫扩张实现。`]);
})();

/* ================= §11 independence matrix ================= */
(function matrix() {
  const axes = [['VL', 'V = L', 'V = L'], ['CH', 'CH', 'CH'], ['MA', 'MA + ¬CH', 'MA + ¬CH'], ['PFA', 'PFA', 'PFA']];
  // y = yes, n = no, u = undecided by this axiom, - = not covered here
  const rows = [
    { en: 'Every Whitehead group is free', zh: '每个怀特海群都是自由群', a: { VL: 'y', CH: 'u', MA: 'n', PFA: 'n' } },
    { en: 'Suslin\'s Hypothesis', zh: '苏斯林假设', a: { VL: 'n', CH: 'u', MA: 'y', PFA: 'y' } },
    { en: 'Borel conjecture', zh: '博雷尔猜想', a: { VL: 'n', CH: 'n', MA: 'n', PFA: 'n' } },
    { en: 'Every homomorphism C(X) → Banach algebra is continuous', zh: 'C(X) 到巴拿赫代数的同态都连续', a: { VL: 'n', CH: 'n', MA: '-', PFA: '-' } },
    { en: 'The Calkin algebra has an outer automorphism', zh: 'Calkin 代数有外自同构', a: { VL: 'y', CH: 'y', MA: '-', PFA: 'n' } },
    { en: '2^ℵ₀ = ℵ₂', zh: '2^ℵ₀ = ℵ₂', a: { VL: 'n', CH: 'n', MA: 'u', PFA: 'y' } },
  ];
  let ax = 'PFA';
  const lab = { y: ['YES', '是'], n: ['NO', '否'], u: ['undecided', '不定'], '-': ['—', '—'] };
  const cls = { y: 'yes', n: 'no', u: 'und', '-': 'na' };
  function render() {
    let h = `<table class="mini mx"><tr><th>${bil('Problem', '问题')}</th>`;
    axes.forEach(([k, en]) => { h += `<th class="${k === ax ? 'hl' : ''}" style="text-align:center">${en}</th>`; });
    h += '</tr>';
    rows.forEach(r => {
      h += `<tr><td>${bil(r.en, r.zh)}</td>`;
      axes.forEach(([k]) => { const c = r.a[k]; h += `<td class="c ${cls[c]} ${k === ax ? 'hl' : ''}">${c === '-' ? '—' : bil(lab[c][0], lab[c][1])}</td>`; });
      h += '</tr>';
    });
    $('mxTable').innerHTML = h + '</table>';
  }
  const bb = $('mxBtns');
  axes.forEach(([k, en, zh]) => {
    const b = document.createElement('button');
    b.className = 'btn small' + (k === ax ? ' sel' : '');
    b.innerHTML = `${bil('Assume', '假设')} <span class="m">${en}</span>`;
    b.addEventListener('click', () => { ax = k; bb.querySelectorAll('button').forEach(x => x.classList.remove('sel')); b.classList.add('sel'); render(); });
    bb.appendChild(b);
  });
  render();
  const cards = [
    { st: 'ind', t: ['Whitehead\'s problem (algebra)', '怀特海问题（代数）'],
      d: ['Is every abelian group A with Ext(A, ℤ) = 0 free? Shelah (1974): V = L ⇒ yes; MA + ¬CH ⇒ no. Shelah later showed it is independent even of ZFC + CH. The first major algebra problem shown independent.', '满足 Ext(A, ℤ) = 0 的阿贝尔群 A 都是自由群吗？Shelah（1974）：V = L ⇒ 是；MA + ¬CH ⇒ 否。Shelah 后来证明它甚至独立于 ZFC + CH。这是第一个被证明独立的重大代数问题。'] },
    { st: 'ind', t: ['Suslin\'s problem (order theory)', '苏斯林问题（序理论）'],
      d: ['Is every complete dense linear order without endpoints satisfying the countable chain condition isomorphic to ℝ? A Suslin line is consistent (Jech, Tennenbaum 1967–68) and follows from V = L via ◇ (Jensen). MA + ¬CH implies none exists (Solovay–Tennenbaum 1971). With CH it is still undecided (Jensen).', '每个满足可数链条件、无端点的稠密完备线序都与 ℝ 同构吗？苏斯林线的存在是一致的（Jech、Tennenbaum 1967–68），并由 V = L 经 ◇ 推出（Jensen）。MA + ¬CH 推出它不存在（Solovay–Tennenbaum 1971）。在 CH 下仍不定（Jensen）。'] },
    { st: 'ind', t: ['Borel conjecture (real analysis)', '博雷尔猜想（实分析）'],
      d: ['Is every strong measure zero set of reals countable? CH gives an uncountable counterexample (Luzin/Sierpiński-type sets); MA does too. Laver (1976) built a model where it holds.', '每个强测度零的实数集都可数吗？CH 给出不可数反例（Luzin/Sierpiński 型集合）；MA 也给出反例。Laver（1976）构造了使它成立的模型。'] },
    { st: 'ind', t: ['Kaplansky\'s question (Banach algebras)', 'Kaplansky 问题（巴拿赫代数）'],
      d: ['Is every algebra homomorphism from C(X) (X compact Hausdorff) into a Banach algebra continuous? Under CH, no: Dales and Esterle (independently, 1976–77) built discontinuous ones. Solovay (c. 1976) found a model where all are continuous, and Woodin (PhD thesis, 1984) found one that also satisfies MA<sub>ℵ₁</sub> (see Dales–Woodin 1987). Martin\'s Maximum implies all are continuous. ¬CH alone does not decide it: Woodin (1993) found a discontinuous one after adding ℵ₂ Cohen reals.', '从 C(X)（X 紧豪斯多夫）到巴拿赫代数的代数同态都连续吗？在 CH 下否：Dales 与 Esterle（1976–77，各自独立）构造了不连续的同态。Solovay（约 1976）找到了“全部连续”的模型，伍丁（1984 年博士论文）找到了同时满足 MA<sub>ℵ₁</sub> 的这样的模型（见 Dales–Woodin 1987）。马丁极大推出“全部连续”。单靠 ¬CH 判定不了它：伍丁（1993）在添加 ℵ₂ 个科恩实数后得到了不连续的同态。'] },
    { st: 'ind', t: ['Calkin algebra automorphisms (operator algebras)', 'Calkin 代数的自同构（算子代数）'],
      d: ['Does the Calkin algebra B(H)/K(H) have outer automorphisms (a question from Brown–Douglas–Fillmore)? Phillips–Weaver (2007): yes under CH. Farah (Annals 2011): under OCA, hence under PFA, all automorphisms are inner.', 'Calkin 代数 B(H)/K(H) 有外自同构吗（源自 Brown–Douglas–Fillmore 的问题）？Phillips–Weaver（2007）：在 CH 下有。Farah（《数学年刊》2011）：在 OCA 下（从而在 PFA 下）所有自同构都是内自同构。'] },
  ];
  const box = $('mxCards');
  cards.forEach(c => {
    const d = document.createElement('div');
    d.className = 'ocard';
    d.innerHTML = `${ST[c.st]()} <b>${bil(c.t[0], c.t[1])}</b><div class="more">${bi(c.d[0], c.d[1])}</div><div class="muted" style="font-size:12px;margin-top:4px">${bil('click to expand', '点击展开')}</div>`;
    d.addEventListener('click', () => d.classList.toggle('open'));
    box.appendChild(d);
  });
  checkYourself('cy11', ['Under PFA, which of these is decided “the nice way” (YES)?', '在 PFA 下，下列哪个得到“好的”答案（是）？'], [
    ['Borel conjecture', '博雷尔猜想', false, 'No: PFA ⇒ MA, and MA refutes the Borel conjecture.', '不对：PFA ⇒ MA，而 MA 否定博雷尔猜想。'],
    ['Suslin\'s Hypothesis', '苏斯林假设', true],
    ['Every Whitehead group is free', '每个怀特海群都是自由群', false, 'No: MA + ¬CH (which follows from PFA) gives a non-free Whitehead group.', '不对：MA + ¬CH（由 PFA 推出）给出非自由的怀特海群。'],
  ], ['Right: PFA ⇒ MA<sub>ℵ₁</sub> ⇒ SH. But “nice” is relative: PFA kills the Borel conjecture.', '对：PFA ⇒ MA<sub>ℵ₁</sub> ⇒ SH。但“好”是相对的：PFA 否定了博雷尔猜想。']);
})();

/* ================= §12 multiverse ================= */
(function multiverse() {
  const rows = [
    { q: ['Does CH have a definite truth value?', 'CH 有确定的真值吗？'],
      u: ['Yes. There is one universe of sets; ZFC is simply an incomplete description of it, as every axiom system for a rich structure must be.', '有。集合宇宙只有一个；ZFC 只是对它的一个不完全描述，任何描述丰富结构的公理系统都必然如此。'],
      m: ['Not a single one. CH holds in some universes and fails in others, and each universe can be extended to one where it flips.', '没有唯一的真值。CH 在一些宇宙中成立，在另一些中不成立，而每个宇宙都可以扩张到一个让它翻转的宇宙。'] },
    { q: ['What is a forcing extension?', '力迫扩张是什么？'],
      u: ['A tool: a model (or Boolean-valued model) we build to prove independence. V[G] is a device, not another reality.', '一种工具：为证明独立性而构造的模型（或布尔值模型）。V[G] 是装置，不是另一个现实。'],
      m: ['A genuine universe, as real as V. Every universe has forcing extensions and grounds; set theory studies this whole web.', '一个真正的宇宙，与 V 同样真实。每个宇宙都有力迫扩张和基础模型；集合论研究的就是这张大网。'] },
    { q: ['What would count as solving the continuum problem?', '怎样才算解决了连续统问题？'],
      u: ['Finding a new axiom with compelling justification that decides it: e.g. MM⁺⁺/(*) (ℵ₂) or V = Ultimate L (ℵ₁).', '找到一条有充分理由、并能判定它的新公理：例如 MM⁺⁺/(*)（ℵ₂）或 V = 终极 L（ℵ₁）。'],
      m: ['Hamkins: it is already answered, by our detailed knowledge of how CH behaves across the multiverse. No “dream solution” can erase our experience of both CH and ¬CH worlds.', 'Hamkins：它已经被回答了，答案就是我们对 CH 在多宇宙中如何表现的详尽了解。任何“理想解答”都抹不去我们对 CH 世界与 ¬CH 世界两方面的经验。'] },
    { q: ['What are large cardinals?', '大基数是什么？'],
      u: ['True axioms about V, supported by the consistency-strength ladder and the determinacy picture (L25).', '关于 V 的真公理，由一致性强度阶梯和决定性图景（第 25 课）所支持。'],
      m: ['Features that some universes have; the consistency-strength hierarchy is a robust map of the multiverse.', '某些宇宙具有的特征；一致性强度层级是多宇宙的一张可靠地图。'] },
    { q: ['Main criticism of the other side', '对另一方的主要批评'],
      u: ['Woodin: if the Ω Conjecture holds, truth in the generic multiverse reduces to Ω-logic and is essentially a form of formalism; it does not respect a “transcendence” requirement for truth.', '伍丁：若 Ω 猜想成立，脱殊多宇宙中的“真”就归结为 Ω-逻辑，本质上是一种形式主义；它不满足关于真的“超越性”要求。'],
      m: ['Hamkins: the universe view must explain away the vast, coherent experience of many models as “illusory”, and its preferred axioms keep competing (ℵ₁ vs ℵ₂).', 'Hamkins：宇宙观必须把大量协调一致的多模型经验解释为“幻象”，而且它所偏爱的公理之间还在相互竞争（ℵ₁ 对 ℵ₂）。'] },
  ];
  const grid = $('mvGrid');
  let h = `<div class="colh" style="background:${C.accentSoft};color:${C.accent}">${bi('Universe view (one V)', '宇宙观（唯一的 V）')}</div><div class="colh" style="background:${C.metaSoft};color:${C.meta}">${bi('Multiverse view (many universes)', '多宇宙观（多个宇宙）')}</div>`;
  rows.forEach((r, i) => {
    h += `<div class="qrow">${i + 1}. ${bil(r.q[0], r.q[1])}</div><div class="cell hid">${bi(r.u[0], r.u[1])}</div><div class="cell hid">${bi(r.m[0], r.m[1])}</div>`;
  });
  grid.innerHTML = h;
  grid.querySelectorAll('.cell').forEach(c => c.addEventListener('click', () => c.classList.remove('hid')));
  $('mvAll').addEventListener('click', () => grid.querySelectorAll('.cell').forEach(c => c.classList.remove('hid')));
  checkYourself('cy12', ['The universe/multiverse debate is…', '宇宙观与多宇宙观之争是……'], [
    ['settled by Cohen\'s theorem in favour of the multiverse', '已由科恩定理判定多宇宙观胜出', false],
    ['settled by Gödel\'s theorem in favour of one universe', '已由哥德尔定理判定宇宙观胜出', false],
    ['a philosophical question that theorems inform but do not settle', '一个由定理提供信息、但定理无法了断的哲学问题', true],
  ], ['Right. Both sides accept all the same theorems; they disagree about what the theorems mean.', '对。双方接受完全相同的定理，分歧在于这些定理意味着什么。']);
})();

/* ================= exercises: generic select-based checker ================= */
function selectExercise(cfg) {
  const { listId, items, options, checkId, showId, msgId, prog, okMsg } = cfg;
  const box = $(listId);
  let revealed = false;
  const sels = items.map((it, i) => {
    const row = document.createElement('div');
    row.className = 'matchrow';
    const s = document.createElement('select');
    s.innerHTML = `<option value="">${'— ' + 'choose / 选择' + ' —'}</option>` + options.map((o, k) => `<option value="${k}">${o[0]} · ${o[1]}</option>`).join('');
    row.innerHTML = `<div class="cond">${String.fromCharCode(97 + i)}) ${bil(it.q[0], it.q[1])}</div>`;
    row.appendChild(s);
    const note = document.createElement('div');
    note.style.flexBasis = '100%';
    note.className = 'muted';
    note.style.fontSize = '13px';
    row.appendChild(note);
    s.addEventListener('change', () => { s.classList.remove('right', 'wrong'); note.innerHTML = ''; });
    box.appendChild(row);
    return { s, note };
  });
  function grade(reveal) {
    let right = 0;
    sels.forEach(({ s, note }, i) => {
      if (reveal) s.value = String(items[i].a);
      s.classList.remove('right', 'wrong');
      if (s.value === '') { note.innerHTML = ''; return; }
      const ok = +s.value === items[i].a;
      s.classList.add(ok ? 'right' : 'wrong');
      if (ok) right++;
      note.innerHTML = (ok || reveal) && items[i].why ? bi(items[i].why[0], items[i].why[1]) : '';
    });
    if (reveal) { revealed = true; okBox($(msgId), bi('Answers filled in, with reasons. (Revealing does not mark the exercise as solved.)', '已填入答案及理由。（看答案不计为完成。）'), 'info'); return; }
    if (right === items.length) { okBox($(msgId), '✓ ' + bi(okMsg[0], okMsg[1])); if (!revealed) Progress.mark(prog); }
    else okBox($(msgId), bi(`${right} / ${items.length} correct. Red = wrong or unanswered choices to revisit.`, `答对 ${right} / ${items.length}。红色为错误，请再看看。`), 'warn');
  }
  $(checkId).addEventListener('click', () => grade(false));
  $(showId).addEventListener('click', () => grade(true));
}

/* ---- E1 ---- */
selectExercise({
  listId: 'e1List', checkId: 'e1Check', showId: 'e1Show', msgId: 'e1Msg', prog: 'L27E1',
  options: [['THEOREM (proved)', '定理（已证明）'], ['INDEPENDENT of ZFC', '独立于 ZFC'], ['OPEN', '未解决']],
  okMsg: ['All correct. Keep the three apart: “provable implication”, “independent statement”, “nobody knows”.', '全对。把三者分清：“可证的蕴涵”“独立的命题”“无人知晓”。'],
  items: [
    { q: ['MM implies 2^ℵ₀ = ℵ₂.', 'MM 推出 2^ℵ₀ = ℵ₂。'], a: 0, why: ['Foreman–Magidor–Shelah 1988.', 'Foreman–Magidor–Shelah 1988。'] },
    { q: ['2^ℵ₀ = ℵ₂.', '2^ℵ₀ = ℵ₂。'], a: 1, why: ['Cohen (consistency of the statement) and Gödel (consistency of its negation, via CH in L).', '科恩（该命题的一致性）与哥德尔（经由 L 中的 CH 得到其否定的一致性）。'] },
    { q: ['The HOD Conjecture.', 'HOD 猜想。'], a: 2, why: ['Open; the HOD Dichotomy is the theorem.', '未解决；HOD 二分才是定理。'] },
    { q: ['MM⁺⁺ implies Woodin\'s axiom (*).', 'MM⁺⁺ 推出伍丁的 (*) 公理。'], a: 0, why: ['Asperó–Schindler, Annals 2021.', 'Asperó–Schindler，《数学年刊》2021。'] },
    { q: ['ZF + “there is a Reinhardt cardinal” is consistent.', 'ZF + “存在 Reinhardt 基数”是一致的。'], a: 2, why: ['Open in ZF (refuted only under AC by Kunen).', '在 ZF 中未解决（只在 AC 下被库能否证）。'] },
    { q: ['Every Whitehead group is free.', '每个怀特海群都是自由群。'], a: 1, why: ['Shelah 1974.', 'Shelah 1974。'] },
    { q: ['If ℵ<sub>ω</sub> is a strong limit then 2^ℵ<sub>ω</sub> < ℵ<sub>ω₁</sub>.', '若 ℵ<sub>ω</sub> 是强极限，则 2^ℵ<sub>ω</sub> < ℵ<sub>ω₁</sub>。'], a: 2, why: ['Open; Shelah proved the ω₄ bound.', '未解决；Shelah 证明的是 ω₄ 上界。'] },
    { q: ['V = Ultimate L implies CH.', 'V = 终极 L 推出 CH。'], a: 0, why: ['Woodin.', '伍丁。'] },
    { q: ['Suslin\'s Hypothesis.', '苏斯林假设。'], a: 1, why: ['V = L refutes it, MA + ¬CH proves it.', 'V = L 否定它，MA + ¬CH 证明它。'] },
    { q: ['If ℵ<sub>ω</sub> is a strong limit then 2^ℵ<sub>ω</sub> < ℵ<sub>ω₄</sub>.', '若 ℵ<sub>ω</sub> 是强极限，则 2^ℵ<sub>ω</sub> < ℵ<sub>ω₄</sub>。'], a: 0, why: ['Shelah, pcf theory.', 'Shelah，pcf 理论。'] },
  ],
});

/* ---- E2 ---- */
selectExercise({
  listId: 'e2List', checkId: 'e2Check', showId: 'e2Show', msgId: 'e2Msg', prog: 'L27E2',
  options: [['Gödel', '哥德尔'], ['Cohen', '科恩'], ['Lévy–Solovay', '列维–索洛维'], ['Foreman–Magidor–Shelah', 'Foreman–Magidor–Shelah'], ['Asperó–Schindler', 'Asperó–Schindler'], ['Shelah', 'Shelah'], ['Goldstern–Kellner–Shelah', 'Goldstern–Kellner–Shelah'], ['Kunen', '库能'], ['Phillips–Weaver', 'Phillips–Weaver'], ['Woodin', '伍丁'], ['Neeman', 'Neeman']],
  okMsg: ['All matched.', '全部配对正确。'],
  items: [
    { q: ['Con(ZFC) ⇒ Con(ZFC + CH), via L (1938)', 'Con(ZFC) ⇒ Con(ZFC + CH)，经由 L（1938）'], a: 0 },
    { q: ['Con(ZFC) ⇒ Con(ZFC + ¬CH), via forcing (1963)', 'Con(ZFC) ⇒ Con(ZFC + ¬CH)，经由力迫（1963）'], a: 1 },
    { q: ['Small forcing preserves measurable cardinals (1967)', '小力迫保持可测基数（1967）'], a: 2 },
    { q: ['MM is consistent from a supercompact and implies 2^ℵ₀ = ℵ₂ (1988)', 'MM 相对于超紧基数一致，并推出 2^ℵ₀ = ℵ₂（1988）'], a: 3 },
    { q: ['MM⁺⁺ ⇒ (*) (2021)', 'MM⁺⁺ ⇒ (*)（2021）'], a: 4 },
    { q: ['2^ℵ<sub>ω</sub> < ℵ<sub>ω₄</sub> if ℵ<sub>ω</sub> is a strong limit', '若 ℵ<sub>ω</sub> 为强极限，则 2^ℵ<sub>ω</sub> < ℵ<sub>ω₄</sub>'], a: 5 },
    { q: ['Cichoń\'s Maximum from four strongly compact cardinals (Annals 2019)', '从四个强紧基数得到 Cichoń 极大（《数学年刊》2019）'], a: 6 },
    { q: ['No nontrivial j : V → V under AC (1971)', '在 AC 下不存在非平凡 j : V → V（1971）'], a: 7 },
    { q: ['Under CH the Calkin algebra has outer automorphisms (2007)', '在 CH 下 Calkin 代数有外自同构（2007）'], a: 8 },
    { q: ['The HOD Dichotomy theorem', 'HOD 二分定理'], a: 9 },
    { q: ['Iterable extender models up to a Woodin limit of Woodins (2002)', '直到伍丁基数之极限的伍丁基数的可迭代扩张子模型（2002）'], a: 10 },
  ],
});

/* ---- E3 Cichoń ---- */
(function e3() {
  const rows = [
    ['covM', 'd', 'nonN', 'cofM', 'cofN'],
    ['b'],
    ['covN', 'nonM', 'cofM', 'cofN'],
    ['addM', 'b', 'covM', 'd', 'nonM', 'nonN', 'cofM', 'cofN', 'covN'],
    ['b', 'd', 'nonM', 'cofM', 'cofN'],
    ['addM', 'b', 'd', 'nonM', 'cofM', 'cofN'],
    ['nonM', 'cofM', 'cofN'],
    ['d', 'nonN', 'cofN'],
  ];
  const data = rows.map(r => {
    const v = {};
    CI_NODES.forEach(k => { v[k] = r.includes(k) || k === 'c' ? 2 : 1; });
    return { r, v, res: cichonCheck(v) };
  });
  const box = $('e3List');
  const state = data.map(() => null);
  let revealed = false;
  const views = data.map((dt, i) => {
    const row = document.createElement('div');
    row.className = 'tf';
    row.innerHTML = `<div class="stmt" style="font-size:14px">${String.fromCharCode(97 + i)}) ℵ₂: ${dt.r.map(k => CI_LAB[k]).join(', ')}</div>
      <button class="btn small" data-v="1">${bil('consistent', '一致')}</button>
      <button class="btn small" data-v="0">${bil('violates ZFC', '违反 ZFC')}</button>
      <div style="flex-basis:100%"><div class="msg"></div><div class="mini-svg"></div></div>`;
    box.appendChild(row);
    const btns = [...row.querySelectorAll('button')];
    btns.forEach(b => b.addEventListener('click', () => {
      state[i] = b.dataset.v === '1';
      btns.forEach(x => x.classList.remove('sel'));
      b.classList.add('sel');
    }));
    return { row, btns, msg: row.querySelector('.msg'), mini: row.querySelector('.mini-svg') };
  });
  function explain(dt) {
    if (dt.res.ok) return bi('Consistent: every arrow and both equalities hold.', '一致：所有箭头和两条等式都满足。');
    const parts = dt.res.badEdges.map(([a, b]) => `${CI_LAB[a]} ≤ ${CI_LAB[b]}`);
    if (!dt.res.eqAdd) parts.push('add(𝓜) = min(b, cov(𝓜))');
    if (!dt.res.eqCof) parts.push('cof(𝓜) = max(d, non(𝓜))');
    return bi(`Violates: <span class="m">${parts.join('; ')}</span>.`, `违反：<span class="m">${parts.join('；')}</span>。`);
  }
  function grade(reveal) {
    let right = 0;
    data.forEach((dt, i) => {
      const vw = views[i];
      if (reveal) state[i] = dt.res.ok;
      if (state[i] === null) { vw.msg.className = 'msg'; vw.msg.innerHTML = ''; return; }
      const ok = state[i] === dt.res.ok;
      if (ok) right++;
      okBox(vw.msg, (reveal ? '' : ok ? '✓ ' : '✗ ') + explain(dt), reveal ? 'info' : ok ? 'ok' : 'bad');
      vw.mini.innerHTML = '';
      if (!dt.res.ok || reveal) {
        const s = el('svg', { viewBox: '0 0 860 340', width: 520, height: 206 });
        vw.mini.appendChild(s);
        drawCichon(s, dt.v, { static: true, sfx: 'e3' + i });
      }
    });
    if (reveal) { revealed = true; views.forEach((vw, i) => vw.btns.forEach(x => x.classList.toggle('sel', (x.dataset.v === '1') === state[i]))); okBox($('e3Msg'), bi('Answers revealed with diagrams of the violations. (Revealing does not mark the exercise as solved.)', '已揭示答案，并附上违反情况的图。（看答案不计为完成。）'), 'info'); return; }
    if (right === data.length) { okBox($('e3Msg'), '✓ ' + bi('All correct. Tip: always check the two equalities; they are easy to forget.', '全对。提示：一定要检查那两条等式，它们最容易被忽略。')); if (!revealed) Progress.mark('L27E3'); }
    else okBox($('e3Msg'), bi(`${right} / ${data.length} correct.`, `答对 ${right} / ${data.length}。`), 'warn');
  }
  $('e3Check').addEventListener('click', () => grade(false));
  $('e3Show').addEventListener('click', () => grade(true));
})();

/* ---- E4 ordering ---- */
(function e4() {
  const correct = [
    ['Assume ZFC + “κ is measurable” is consistent, and take a model V of it.', '设 ZFC + “κ 可测”一致，取它的一个模型 V。'],
    ['In V, κ is inaccessible, so 2^ℵ₀ < κ.', '在 V 中 κ 不可达，所以 2^ℵ₀ < κ。'],
    ['The forcings Add(ω, ω₂) and Col(ω₁, 2^ℵ₀) both have size < κ.', '力迫 Add(ω, ω₂) 与 Col(ω₁, 2^ℵ₀) 的大小都 < κ。'],
    ['By Lévy–Solovay, κ is still measurable in V[G] and in V[H].', '由列维–索洛维定理，κ 在 V[G] 和 V[H] 中仍可测。'],
    ['V[G] ⊨ ¬CH and V[H] ⊨ CH.', 'V[G] ⊨ ¬CH 且 V[H] ⊨ CH。'],
    ['So ZFC + “κ is measurable” proves neither CH nor ¬CH.', '所以 ZFC + “κ 可测”既证不了 CH，也证不了 ¬CH。'],
  ];
  let order = shuffle(correct.map((_, i) => i));
  let revealed = false;
  if (order.every((c, i) => c === i)) order.reverse();
  const list = $('e4List');
  function render(marks) {
    list.innerHTML = '';
    order.forEach((ci, pos) => {
      const d = document.createElement('div');
      d.className = 'chip' + (marks ? (marks[pos] ? ' ok' : ' no') : '');
      d.innerHTML = `<span class="num">${pos + 1}</span><span class="sp">${bil(correct[ci][0], correct[ci][1])}</span><button data-d="-1">↑</button><button data-d="1">↓</button>`;
      d.querySelectorAll('button').forEach(b => b.addEventListener('click', () => {
        const np = pos + +b.dataset.d;
        if (np < 0 || np >= order.length) return;
        [order[pos], order[np]] = [order[np], order[pos]];
        render(); clearBox($('e4Msg'));
      }));
      list.appendChild(d);
    });
  }
  render();
  $('e4Check').addEventListener('click', () => {
    // steps 4 and 5 could be argued in either order; accept both
    const ok = order.every((c, i) => c === i) || order.join() === '0,1,2,4,3,5';
    render(order.map((c, i) => c === i || (ok && (i === 3 || i === 4))));
    if (ok) { okBox($('e4Msg'), '✓ ' + bi('A correct proof. The key step is 2→3: CH is decided by forcings that live below κ.', '一个正确的证明。关键在第 2→3 步：CH 由位于 κ 之下的力迫决定。')); if (!revealed) Progress.mark('L27E4'); }
    else okBox($('e4Msg'), bi('Not yet. Ask: which fact is needed before you can say the forcings are small? (Green = in the right place.)', '还不对。想一想：要说力迫“小”，之前需要先知道什么？（绿色＝位置正确。）'), 'warn');
  });
  $('e4Show').addEventListener('click', () => {
    order = correct.map((_, i) => i);
    revealed = true;
    render(order.map(() => true));
    okBox($('e4Msg'), bi('The correct order is shown. (Revealing does not mark it solved.)', '已显示正确顺序。（看答案不计为完成。）'), 'info');
  });
})();

/* ---- E5 ---- */
selectExercise({
  listId: 'e5List', checkId: 'e5Check', showId: 'e5Show', msgId: 'e5Msg', prog: 'L27E5',
  options: [['impossible in ZFC', 'ZFC 中不可能'], ['known consistent', '已知一致'], ['open', '未解决']],
  okMsg: ['All correct. König rules out countable cofinality, Shelah rules out ≥ ℵ<sub>ω₄</sub>, forcing gives everything with a countable index, and the rest is open.', '全对。König 排除了可数共尾，Shelah 排除了 ≥ ℵ<sub>ω₄</sub>，力迫给出下标可数的所有值，其余尚未解决。'],
  items: [
    { q: ['2^ℵ<sub>ω</sub> = ℵ<sub>ω+1</sub>', '2^ℵ<sub>ω</sub> = ℵ<sub>ω+1</sub>'], a: 1, why: ['GCH.', 'GCH。'] },
    { q: ['2^ℵ<sub>ω</sub> = ℵ<sub>ω+5</sub>', '2^ℵ<sub>ω</sub> = ℵ<sub>ω+5</sub>'], a: 1, why: ['Magidor; Gitik–Magidor (large cardinals).', 'Magidor；Gitik–Magidor（大基数）。'] },
    { q: ['2^ℵ<sub>ω</sub> = ℵ<sub>ω·2</sub>', '2^ℵ<sub>ω</sub> = ℵ<sub>ω·2</sub>'], a: 0, why: ['cofinality ω: König.', '共尾性为 ω：König。'] },
    { q: ['2^ℵ<sub>ω</sub> = ℵ<sub>ω²+1</sub>', '2^ℵ<sub>ω</sub> = ℵ<sub>ω²+1</sub>'], a: 1, why: ['countable index (Shelah; Gitik–Magidor).', '下标可数（Shelah；Gitik–Magidor）。'] },
    { q: ['2^ℵ<sub>ω</sub> = ℵ<sub>ω₁</sub>', '2^ℵ<sub>ω</sub> = ℵ<sub>ω₁</sub>'], a: 0, why: ['cofinality ω₁ < ℵ<sub>ω</sub>: König.', '共尾性 ω₁ < ℵ<sub>ω</sub>：König。'] },
    { q: ['2^ℵ<sub>ω</sub> = ℵ<sub>ω₂+1</sub>', '2^ℵ<sub>ω</sub> = ℵ<sub>ω₂+1</sub>'], a: 2, why: ['in the ω₁–ω₄ gap.', '位于 ω₁–ω₄ 缺口中。'] },
    { q: ['2^ℵ<sub>ω</sub> = ℵ<sub>ω₄+1</sub>', '2^ℵ<sub>ω</sub> = ℵ<sub>ω₄+1</sub>'], a: 0, why: ['Shelah\'s bound.', 'Shelah 上界。'] },
  ],
});

/* ---- E6 ---- */
selectExercise({
  listId: 'e6List', checkId: 'e6Check', showId: 'e6Show', msgId: 'e6Msg', prog: 'L27E6',
  options: [['implies 2^ℵ₀ = ℵ₁ (CH)', '推出 2^ℵ₀ = ℵ₁（CH）'], ['implies 2^ℵ₀ = ℵ₂', '推出 2^ℵ₀ = ℵ₂'], ['does not determine 2^ℵ₀', '不能确定 2^ℵ₀']],
  okMsg: ['All correct. Notice where the two camps of §5 sit, and that large cardinals and MA alone stay silent.', '全对。注意 §5 两大阵营各自的位置，以及大基数和单独的 MA 都保持沉默。'],
  items: [
    { q: ['V = L', 'V = L'], a: 0, why: ['Gödel: L ⊨ GCH.', '哥德尔：L ⊨ GCH。'] },
    { q: ['V = Ultimate L', 'V = 终极 L'], a: 0, why: ['Woodin.', '伍丁。'] },
    { q: ['PFA', 'PFA'], a: 1, why: ['Todorčević; Veličković.', 'Todorčević；Veličković。'] },
    { q: ['BPFA (bounded PFA)', 'BPFA（有界 PFA）'], a: 1, why: ['Moore 2005.', 'Moore 2005。'] },
    { q: ['Woodin\'s axiom (*)', '伍丁的 (*) 公理'], a: 1, why: ['ℙ<sub>max</sub> extensions satisfy 2^ℵ₀ = ℵ₂.', 'ℙ<sub>max</sub> 扩张满足 2^ℵ₀ = ℵ₂。'] },
    { q: ['MA<sub>ℵ₁</sub>', 'MA<sub>ℵ₁</sub>'], a: 2, why: ['Only 2^ℵ₀ ≥ ℵ₂; ℵ₃ is possible too.', '只给出 2^ℵ₀ ≥ ℵ₂；ℵ₃ 也可能。'] },
    { q: ['A proper class of Woodin cardinals', '真类多个伍丁基数'], a: 2, why: ['Lévy–Solovay.', '列维–索洛维。'] },
    { q: ['A supercompact cardinal', '一个超紧基数'], a: 2, why: ['Lévy–Solovay (even though a supercompact is what we use to force MM).', '列维–索洛维（尽管我们正是用超紧基数来力迫 MM）。'] },
  ],
});
