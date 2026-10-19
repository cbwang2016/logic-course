// Lesson 25 interactions: large cardinals III & determinacy.

/*PURE-START*/
// ---------- pure game logic (unit-tested in node) ----------
// A complete game tree with branching b and depth d is stored level by level:
// level k has b^k nodes; node (k, i) has children (k+1, i*b + c), c < b.
// Player I moves at even depths, player II at odd depths.
function moverAt(k) { return k % 2 === 0 ? 'I' : 'II'; }

// leaves: array of 'I' | 'II' (length b^d). Returns labels[k][i] = winner from node (k, i).
function solveGame(leaves, b, d) {
  const labels = [];
  labels[d] = leaves.slice();
  for (let k = d - 1; k >= 0; k--) {
    const n = Math.pow(b, k), row = [];
    const m = moverAt(k), other = m === 'I' ? 'II' : 'I';
    for (let i = 0; i < n; i++) {
      let some = false;
      for (let c = 0; c < b; c++) if (labels[k + 1][i * b + c] === m) some = true;
      row.push(some ? m : other);
    }
    labels[k] = row;
  }
  return labels;
}

// Edges of the winner’s strategy, restricted to positions reachable when the winner follows it.
// Returns a Set of keys "k,i" of child nodes whose incoming edge belongs to the strategy tree.
function strategyEdges(labels, b, d) {
  const W = labels[0][0], out = new Set();
  (function walk(k, i) {
    if (k === d) return;
    if (moverAt(k) === W) {
      for (let c = 0; c < b; c++) {
        const j = i * b + c;
        if (labels[k + 1][j] === W) { out.add((k + 1) + ',' + j); walk(k + 1, j); return; }
      }
    } else {
      for (let c = 0; c < b; c++) { const j = i * b + c; out.add((k + 1) + ',' + j); walk(k + 1, j); }
    }
  })(0, 0);
  return out;
}

// Brute force: does player P have a winning strategy? (enumerates all strategies; tiny trees only)
function bruteForceWinner(leaves, b, d) {
  function wins(P, k, i) {
    if (k === d) return leaves[i] === P;
    const kids = [];
    for (let c = 0; c < b; c++) kids.push(i * b + c);
    // P picks one child (strategy choice) / opponent may pick any child
    if (moverAt(k) === P) return kids.some(j => wins(P, k + 1, j));
    return kids.every(j => wins(P, k + 1, j));
  }
  // Enumerate strategies explicitly for I to double-check the recursive characterization.
  const nodesI = [];
  for (let k = 0; k < d; k += 2) for (let i = 0; i < Math.pow(b, k); i++) nodesI.push([k, i]);
  const total = Math.pow(b, nodesI.length);
  let explicitI = false;
  for (let s = 0; s < total && !explicitI; s++) {
    const choice = new Map();
    let t = s;
    nodesI.forEach(([k, i]) => { choice.set(k + ',' + i, t % b); t = Math.floor(t / b); });
    const ok = (function play(k, i) {
      if (k === d) return leaves[i] === 'I';
      if (moverAt(k) === 'I') return play(k + 1, i * b + choice.get(k + ',' + i));
      for (let c = 0; c < b; c++) if (!play(k + 1, i * b + c)) return false;
      return true;
    })(0, 0);
    if (ok) explicitI = true;
  }
  return { I: wins('I', 0, 0), II: wins('II', 0, 0), explicitI };
}

// Open game toy: binary tree of depth d, targets = Set of "k,i" (k ≥ 1).
// rank[k][i] = number of further moves I needs to force reaching a target (0 if already reached),
// Infinity if II can keep the play away from all targets (a "safe" position for II).
function openRanks(targets, b, d) {
  const hit = [];
  for (let k = 0; k <= d; k++) {
    hit[k] = [];
    for (let i = 0; i < Math.pow(b, k); i++) {
      const parentHit = k > 0 && hit[k - 1][Math.floor(i / b)];
      hit[k][i] = parentHit || targets.has(k + ',' + i);
    }
  }
  const rank = [];
  rank[d] = hit[d].map(h => h ? 0 : Infinity);
  for (let k = d - 1; k >= 0; k--) {
    rank[k] = [];
    for (let i = 0; i < Math.pow(b, k); i++) {
      if (hit[k][i]) { rank[k][i] = 0; continue; }
      const kids = [];
      for (let c = 0; c < b; c++) kids.push(rank[k + 1][i * b + c]);
      rank[k][i] = moverAt(k) === 'I' ? 1 + Math.min(...kids) : 1 + Math.max(...kids);
    }
  }
  return { rank, hit };
}
/*PURE-END*/

Lang.init();
Progress.paint();

const $ = id => document.getElementById(id);
const okBox = (box, html, kind = 'ok') => { box.className = 'msg ' + kind; box.innerHTML = html; };
const clearBox = box => { box.className = 'msg'; box.innerHTML = ''; };
const C = { ink: '#1f2430', muted: '#6b7280', line: '#e3dfd3', accent: '#3b5bdb', accentSoft: '#e7ecff', tru: '#2f9e44', truSoft: '#d3f9d8',
  fal: '#e03131', falSoft: '#ffe3e3', meta: '#ae3ec9', metaSoft: '#f8e7fc', gold: '#f08c00', goldSoft: '#fff3bf', teal: '#1098ad' };
// SVG text; "_{..}" / "_x" become subscripts and "^{..}" / "^x" superscripts.
function T(parent, x, y, s, attrs = {}) {
  const t = el('text', Object.assign({ x, y, 'font-size': 13, fill: C.ink, class: 'lbl' }, attrs), parent);
  t.style.fontSize = (attrs['font-size'] || 13) + 'px'; // beat the shared `.m { font-size }` rule
  const re = /([_^])(\{[^}]*\}|[^\s])/g;
  let last = 0, m;
  while ((m = re.exec(s))) {
    if (m.index > last) el('tspan', {}, t).textContent = s.slice(last, m.index);
    const body = m[2][0] === '{' ? m[2].slice(1, -1) : m[2];
    const sp = el('tspan', { 'baseline-shift': m[1] === '_' ? 'sub' : 'super', 'font-size': '72%' }, t);
    sp.textContent = body;
    last = re.lastIndex;
  }
  if (last < s.length) el('tspan', {}, t).textContent = s.slice(last);
  return t;
}
const shuffle = a => { for (let i = a.length - 1; i > 0; i--) { const j = Math.floor(Math.random() * (i + 1)); [a[i], a[j]] = [a[j], a[i]]; } return a; };
function animate(ms, step) {
  return new Promise(res => {
    const t0 = performance.now();
    function f(t) { const u = Math.min(1, (t - t0) / ms); step(u < 1 ? 1 - Math.pow(1 - u, 3) : 1); if (u < 1) requestAnimationFrame(f); else res(); }
    requestAnimationFrame(f);
  });
}

/* ================= check-yourself & steppers ================= */
function checkYourself(id, q, opts, expl) {
  const box = $(id);
  box.innerHTML = `<div class="q">✎ ${bil('Check yourself', '自我检测')}: ${bi(q[0], q[1])}</div><div class="opts"></div><div class="msg"></div>`;
  const ob = box.querySelector('.opts'), msg = box.querySelector('.msg');
  const btns = opts.map(o => {
    const b = document.createElement('button');
    b.className = 'btn small';
    b.innerHTML = bil(o[0], o[1]);
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
document.querySelectorAll('[data-next]').forEach(b => b.addEventListener('click', () => {
  const st = [...$(b.dataset.next).querySelectorAll('.step')];
  const nx = st.find(s => !s.classList.contains('on'));
  if (nx) nx.classList.add('on');
  if (st.every(s => s.classList.contains('on'))) b.disabled = true;
}));
document.querySelectorAll('[data-all]').forEach(b => b.addEventListener('click', () => {
  $(b.dataset.all).querySelectorAll('.step').forEach(s => s.classList.add('on'));
  const nb = document.querySelector(`[data-next="${b.dataset.all}"]`);
  if (nb) nb.disabled = true;
}));

/* ================= §1 paradigm ================= */
(function paradigm() {
  const svg = $('parSvg');
  const AX = 330, AY = 410, TOP = 30, HW = 280;
  const yOf = f => AY - f * (AY - TOP);
  const hw = y => HW * (AY - y) / (AY - TOP);
  const stages = [
    { en: 'measurable', zh: '可测', agree: 0.27, mw: 0.12, col: C.accent, agreeLab: 'V_{κ+1} ⊆ M',
      marks: [[0.18, 'κ'], [0.27, 'κ+1'], [0.46, 'j(κ)']],
      info: ['<b>Measurable.</b> Take j = the ultrapower by a normal measure U on κ. Then <span class="m"><sup>κ</sup>M ⊆ M</span> and <span class="m">V<sub>κ+1</sub> ⊆ M</span>, but <span class="m">U ∉ M</span>, so already <span class="m">V<sub>κ+2</sub> ⊄ M</span>. M is still far from V.',
        '<b>可测.</b> 取 j 为由 κ 上正规测度 U 得到的超幂。则 <span class="m"><sup>κ</sup>M ⊆ M</span> 且 <span class="m">V<sub>κ+1</sub> ⊆ M</span>，但 <span class="m">U ∉ M</span>，所以 <span class="m">V<sub>κ+2</sub> ⊄ M</span>。此时 M 离 V 还很远。'] },
    { en: 'λ-strong', zh: 'λ-强', agree: 0.5, mw: 0.26, col: C.accent, agreeLab: 'V_λ ⊆ M',
      marks: [[0.18, 'κ'], [0.5, 'λ'], [0.6, 'j(κ) > λ']],
      info: ['<b>λ-strong.</b> <span class="m">V<sub>λ</sub> ⊆ M</span> and <span class="m">j(κ) &gt; λ</span>. <b>Strong</b> = λ-strong for <i>every</i> λ: for each λ there is some embedding, and different λ use different j.',
        '<b>λ-强.</b> <span class="m">V<sub>λ</sub> ⊆ M</span> 且 <span class="m">j(κ) &gt; λ</span>。<b>强基数</b>即对<i>每个</i> λ 都 λ-强：每个 λ 各有一个嵌入，不同的 λ 用的是不同的 j。'] },
    { en: 'λ-supercompact', zh: 'λ-超紧', agree: 0.55, mw: 0.45, col: C.accent, agreeLab: 'H(λ⁺) ⊆ M',
      marks: [[0.18, 'κ'], [0.55, 'λ'], [0.64, 'j(κ) > λ']],
      info: ['<b>λ-supercompact.</b> <span class="m">j(κ) &gt; λ</span> and <span class="m"><sup>λ</sup>M ⊆ M</span>: every λ-sequence of elements of M is in M. Consequences: <span class="m">j″λ ∈ M</span>, <span class="m">P(λ) ⊆ M</span>, and every set hereditarily of size ≤ λ is in M (<span class="m">H(λ⁺) ⊆ M</span>). Closure also constrains the <i>upper</i> part of M, not only an initial segment. <b>Supercompact</b> = for every λ.',
        '<b>λ-超紧.</b> <span class="m">j(κ) &gt; λ</span> 且 <span class="m"><sup>λ</sup>M ⊆ M</span>：M 中元素组成的每个 λ-序列都在 M 中。推论：<span class="m">j″λ ∈ M</span>、<span class="m">P(λ) ⊆ M</span>，且每个遗传势 ≤ λ 的集合都在 M 中（<span class="m">H(λ⁺) ⊆ M</span>）。封闭性约束的还有 M 的<i>上层</i>，不只是一个初始段。<b>超紧</b>即对每个 λ 都成立。'] },
    { en: 'huge', zh: '巨大', agree: 0.7, mw: 0.62, col: C.accent, agreeLab: 'V_{j(κ)+1} ⊆ M',
      marks: [[0.18, 'κ'], [0.7, 'j(κ)']],
      info: ['<b>Huge.</b> <span class="m"><sup>j(κ)</sup>M ⊆ M</span>: closure all the way up to the image of the critical point (hence <span class="m">V<sub>j(κ)+1</sub> ⊆ M</span>). Only <b>one</b> such j is required, which is why huge does not imply supercompact.',
        '<b>巨大.</b> <span class="m"><sup>j(κ)</sup>M ⊆ M</span>：封闭性一直延伸到临界点的像（因而 <span class="m">V<sub>j(κ)+1</sub> ⊆ M</span>）。只要求<b>一个</b>这样的 j，所以巨大不蕴涵超紧。'] },
    { en: 'rank-into-rank', zh: '秩入秩', agree: 0.86, mw: 0.82, col: C.meta, agreeLab: 'j : V_λ → V_λ',
      marks: [[0.18, 'κ₀ = κ'], [0.5, 'κ₁ = j(κ)'], [0.68, 'κ₂'], [0.78, 'κ₃'], [0.86, 'λ = sup κₙ']],
      info: ['<b>Rank-into-rank (I3).</b> Now j maps an initial segment of the universe <i>into itself</i>: <span class="m">j : V<sub>λ</sub> → V<sub>λ</sub></span>, with λ the supremum of the critical sequence. Stronger variants reach <span class="m">V<sub>λ+1</sub></span> (I1) and <span class="m">L(V<sub>λ+1</sub>)</span> (I0). See §6.',
        '<b>秩入秩（I3）.</b> 现在 j 把宇宙的一个初始段映入<i>自身</i>：<span class="m">j : V<sub>λ</sub> → V<sub>λ</sub></span>，λ 是临界序列的上确界。更强的版本延伸到 <span class="m">V<sub>λ+1</sub></span>（I1）和 <span class="m">L(V<sub>λ+1</sub>)</span>（I0）。见 §6。'] },
    { en: 'Reinhardt: M = V', zh: '莱因哈特：M = V', agree: 1, mw: 1, col: C.fal, agreeLab: 'M = V',
      marks: [[0.18, 'κ'], [0.5, 'j(κ)']],
      info: ['<b>Reinhardt.</b> <span class="m">j : V → V</span>. This is the end of the road. <span class="status st-no">ZFC ⊢ ¬</span> by Kunen’s theorem (§6). In ZF without choice its consistency is <span class="status st-open">open</span>.',
        '<b>莱因哈特.</b> <span class="m">j : V → V</span>。路走到头了。由库能定理（§6）<span class="status st-no">ZFC ⊢ ¬</span>。在不含选择公理的 ZF 中，其一致性<span class="status st-open">未解决</span>。'] },
  ];
  let cur = { agree: stages[0].agree, mw: stages[0].mw }, token = 0;
  function draw(state, s) {
    svg.innerHTML = '';
    // V cone
    el('polygon', { points: `${AX},${AY} ${AX - HW},${TOP} ${AX + HW},${TOP}`, fill: '#f1efe7', stroke: '#b8b3a6', 'stroke-width': 2 }, svg);
    T(svg, AX - HW - 4, TOP - 8, 'V', { 'font-size': 18, 'font-weight': 700 });
    const ya = yOf(state.agree), w = hw(ya), mt = state.mw * HW;
    // M above the agreement
    el('polygon', { points: `${AX - w},${ya} ${AX - mt},${TOP} ${AX + mt},${TOP} ${AX + w},${ya}`, fill: s.col, 'fill-opacity': 0.18, stroke: s.col, 'stroke-width': 1.5, 'stroke-dasharray': '5 4' }, svg);
    // agreement region
    el('polygon', { points: `${AX},${AY} ${AX - w},${ya} ${AX + w},${ya}`, fill: s.col, 'fill-opacity': 0.55, stroke: s.col, 'stroke-width': 2 }, svg);
    T(svg, AX, Math.min(AY - 18, ya + (AY - ya) * 0.55), s.agreeLab, { 'text-anchor': 'middle', fill: '#fff', 'font-weight': 700, 'font-size': 14, class: 'm', stroke: s.col, 'stroke-width': 4, 'paint-order': 'stroke' });
    if (state.mw < 0.999) T(svg, AX, TOP + 22, 'M', { 'text-anchor': 'middle', fill: s.col, 'font-weight': 800, 'font-size': 18 });
    // ordinal axis
    el('line', { x1: AX, y1: AY, x2: AX, y2: TOP - 6, stroke: C.ink, 'stroke-width': 1.5 }, svg);
    T(svg, AX + 6, TOP - 10, 'Ord', { 'font-size': 12, fill: C.muted });
    // marks
    s.marks.forEach(([f, lab]) => {
      const y = yOf(f);
      el('line', { x1: AX - hw(y), y1: y, x2: AX + hw(y) + 6, y2: y, stroke: C.ink, 'stroke-opacity': 0.35, 'stroke-dasharray': '2 3' }, svg);
      T(svg, AX + hw(y) + 10, y + 4, lab, { class: 'm', 'font-size': 13 });
    });
    // j arrow from κ to j(κ) on the left of the axis
    const k0 = yOf(0.18), k1 = yOf(s.marks.find(m => /j\(κ\)|κ₁/.test(m[1]))[0]);
    el('path', { d: `M ${AX - 4} ${k0} C ${AX - 70} ${k0 - 10}, ${AX - 70} ${k1 + 10}, ${AX - 6} ${k1}`, fill: 'none', stroke: C.meta, 'stroke-width': 2.5, 'marker-end': 'url(#parArr)' }, svg);
    T(svg, AX - 66, (k0 + k1) / 2, 'j', { 'font-size': 16, 'font-weight': 700, fill: C.meta });
    const defs = el('defs', {}, svg);
    const mk = el('marker', { id: 'parArr', viewBox: '0 0 10 10', refX: 8, refY: 5, markerWidth: 7, markerHeight: 7, orient: 'auto-start-reverse' }, defs);
    el('path', { d: 'M0,0 L10,5 L0,10 z', fill: C.meta }, mk);
    // right-hand legend
    const lx = 650;
    T(svg, lx, 60, 'solid = M agrees with V', { 'font-size': 12, fill: C.muted });
    T(svg, lx, 76, '实心 = M 与 V 一致', { 'font-size': 12, fill: C.muted });
    T(svg, lx, 100, 'dashed = M ⊊ V above', { 'font-size': 12, fill: C.muted });
    T(svg, lx, 116, '虚线 = 上方 M 真包含于 V', { 'font-size': 12, fill: C.muted });
    T(svg, lx, 140, 'axis: all ordinals ⊆ M', { 'font-size': 12, fill: C.muted });
    T(svg, lx, 156, '竖轴：全体序数都在 M 中', { 'font-size': 12, fill: C.muted });
    if (s.col === C.fal) {
      el('rect', { x: AX - HW - 10, y: TOP - 24, width: 2 * HW + 20, height: AY - TOP + 30, fill: 'none', stroke: C.fal, 'stroke-width': 3, rx: 10, 'stroke-dasharray': '10 6' }, svg);
      T(svg, AX, AY + 14, 'refuted in ZFC (Kunen) · 在 ZFC 中被否证（库能）', { 'text-anchor': 'middle', fill: C.fal, 'font-weight': 700 });
    }
  }
  async function go(i) {
    const s = stages[i], my = ++token, from = { ...cur };
    $('parName').innerHTML = bil(s.en, s.zh);
    okBox($('parInfo'), bi(s.info[0], s.info[1]), s.col === C.fal ? 'bad' : 'info');
    await animate(500, u => {
      if (my !== token) return;
      cur = { agree: from.agree + (s.agree - from.agree) * u, mw: from.mw + (s.mw - from.mw) * u };
      draw(cur, s);
    });
  }
  $('parSlider').addEventListener('input', e => go(+e.target.value));
  draw(cur, stages[0]);
  go(0);
  checkYourself('cy1', ['Which change makes an embedding axiom <b>stronger</b>?', '下列哪种改变会让嵌入公理<b>更强</b>？'], [
    ['M must contain more of V', 'M 必须包含更多的 V', true],
    ['the critical point must be smaller', '临界点必须更小', false, 'No. The critical point of any such j is a measurable cardinal; making it small does not add strength.', '不对。任何这样的 j 的临界点都是可测基数；要求它小并不增加强度。'],
    ['M must be a smaller class', 'M 必须是更小的类', false, 'Backwards: a smaller M is a weaker requirement. The closer M is to V, the stronger the axiom.', '反了：M 越小，要求越弱。M 越接近 V，公理越强。'],
  ], ['Right. The whole hierarchy from measurable to I0 is organized by how much of V the target model M must capture. At M = V it collapses (§6).', '对。从可测到 I0 的整个层级，都是按目标模型 M 必须捕获多少 V 来组织的。到 M = V 时就崩溃了（§6）。']);
})();

/* ================= §2 strong ================= */
(function strong() {
  const svg = $('strSvg');
  const ticks = [['0', 60], ['ω', 130], ['κ', 300], ['κ+1', 390], ['κ+2', 480], ['κ+3', 560], ['κ+ω', 650], ['κ+κ', 730], ['…', 810]];
  const X = Object.fromEntries(ticks);
  const choices = [
    { lab: 'κ+1', x: X['κ+1'], en: 'λ = κ+1: exactly what the measure ultrapower gives. Every subset of κ is in M, but the measure U itself (a set of subsets of κ, rank κ+1) is <b>not</b>: <span class="m">U ∉ Ult(V, U)</span>. So κ+1-strong ⇔ measurable.', zh: 'λ = κ+1：正是测度超幂给出的。κ 的每个子集都在 M 中，但测度 U 本身（κ 的子集构成的集合，秩为 κ+1）<b>不在</b>：<span class="m">U ∉ Ult(V, U)</span>。所以 κ+1-强 ⇔ 可测。' },
    { lab: 'κ+2', x: X['κ+2'], en: 'λ = κ+2: now <span class="m">U ∈ M</span>, so M thinks κ is measurable. Then by elementarity κ is a limit of measurable cardinals (the measurables below κ belong to the normal measure derived from j). This is strictly stronger than measurability.', zh: 'λ = κ+2：现在 <span class="m">U ∈ M</span>，所以 M 认为 κ 可测。由初等性，κ 是可测基数的极限（κ 以下的可测基数属于由 j 导出的正规测度）。这严格强于可测性。' },
    { lab: 'κ+ω', x: X['κ+ω'], en: 'λ = κ+ω: M contains <span class="m">P(κ), P(P(κ)), P(P(P(κ))), …</span>, every finite iterate.', zh: 'λ = κ+ω：M 包含 <span class="m">P(κ)、P(P(κ))、P(P(P(κ)))、…</span>，所有有限次迭代。' },
    { lab: 'κ+κ', x: X['κ+κ'], en: 'λ = κ+κ: and so on. Note that <span class="m">j(κ) &gt; λ</span> is required, so j(κ) is pushed past λ.', zh: 'λ = κ+κ：依此类推。注意定义要求 <span class="m">j(κ) &gt; λ</span>，所以 j(κ) 也被推到 λ 之后。' },
    { lab: bil('every λ (strong)', '每个 λ（强）'), x: 840, en: '<b>Strong</b>: for <i>every</i> λ some embedding has <span class="m">V<sub>λ</sub> ⊆ M</span>. Different λ need different j. No single j can do it for all λ at once: that would force M = V, which Kunen’s theorem (§6) forbids.', zh: '<b>强基数</b>：对<i>每个</i> λ，都有某个嵌入满足 <span class="m">V<sub>λ</sub> ⊆ M</span>。不同的 λ 需要不同的 j。没有哪一个 j 能同时对所有 λ 做到：否则 M = V，而这被库能定理（§6）禁止。' },
  ];
  const items = [
    { r: X['κ'], y: 70, en: 'x ⊆ κ', zh: 'κ 的子集', need: X['κ+1'] },
    { r: X['κ+1'], y: 40, en: 'U ⊆ P(κ)', zh: '测度 U', need: X['κ+2'] },
    { r: X['κ+2'], y: 70, en: 'W ⊆ P(P(κ))', zh: '任意 W', need: X['κ+3'] },
  ];
  let sel = 0;
  function draw() {
    svg.innerHTML = '';
    const lam = choices[sel].x;
    T(svg, 20, 128, 'V', { 'font-weight': 800, 'font-size': 16 });
    el('rect', { x: 60, y: 112, width: 790, height: 22, rx: 6, fill: '#f1efe7', stroke: '#b8b3a6' }, svg);
    T(svg, 20, 172, 'M', { 'font-weight': 800, 'font-size': 16, fill: C.accent });
    el('rect', { x: 60, y: 156, width: 790, height: 22, rx: 6, fill: '#fff', stroke: C.accent, 'stroke-dasharray': '4 4' }, svg);
    const r = el('rect', { x: 60, y: 156, width: 0, height: 22, rx: 6, fill: C.accent, 'fill-opacity': 0.6 }, svg);
    r.style.transition = 'width .5s';
    requestAnimationFrame(() => r.setAttribute('width', Math.min(790, lam - 60)));
    T(svg, Math.min(lam, 790) - 6, 172, sel === 4 ? 'V_λ ⊆ M  (∀λ, different j)' : 'V_λ ⊆ M', { 'text-anchor': 'end', fill: '#fff', 'font-weight': 700, class: 'm' });
    ticks.forEach(([lab, x]) => {
      el('line', { x1: x, y1: 108, x2: x, y2: 186, stroke: C.ink, 'stroke-opacity': 0.25 }, svg);
      T(svg, x, 204, lab, { 'text-anchor': 'middle', class: 'm', 'font-size': 13 });
    });
    if (sel < 4) {
      el('path', { d: `M ${lam} 96 L ${lam} 192`, stroke: C.meta, 'stroke-width': 3 }, svg);
      T(svg, lam, 226, 'λ', { 'text-anchor': 'middle', fill: C.meta, 'font-weight': 800, 'font-size': 16 });
    }
    T(svg, 455, 244, 'a set of rank ρ lies in V_λ iff ρ < λ · 秩为 ρ 的集合属于 V_λ 当且仅当 ρ < λ', { 'text-anchor': 'middle', 'font-size': 12, fill: C.muted });
    items.forEach(it => {
      const inM = lam >= it.need;
      const g = el('g', { class: 'pop' }, svg);
      el('circle', { cx: it.r + 18, cy: it.y + 20, r: 7, fill: inM ? C.tru : C.fal }, g);
      T(g, it.r + 30, it.y + 25, `${it.en}${it.zh ? ' · ' + it.zh : ''}  ${inM ? '∈ M ✓' : '∉ M ✗'}`, { 'font-size': 12.5, fill: inM ? C.tru : C.fal, 'font-weight': 700 });
    });
    okBox($('strInfo'), bi(choices[sel].en, choices[sel].zh), 'info');
  }
  const box = $('strBtns');
  choices.forEach((c, i) => {
    const b = document.createElement('button');
    b.className = 'btn small' + (i === 0 ? ' sel' : '');
    b.innerHTML = c.lab.includes('<') ? c.lab : `<span class="m">${c.lab}</span>`;
    b.addEventListener('click', () => { sel = i; box.querySelectorAll('button').forEach((x, k) => x.classList.toggle('sel', k === i)); draw(); });
    box.appendChild(b);
  });
  draw();
  checkYourself('cy2', ['κ is measurable and j is the ultrapower by a normal measure U. Is <span class="m">U ∈ M</span>?', 'κ 可测，j 是由正规测度 U 得到的超幂。<span class="m">U ∈ M</span> 吗？'], [
    ['Yes, because V<sub>κ+1</sub> ⊆ M', '是，因为 V<sub>κ+1</sub> ⊆ M', false, 'U has rank κ+1, so it lives in V<sub>κ+2</sub>, not V<sub>κ+1</sub>. Containing every subset of κ is not the same as containing a particular <i>collection</i> of them.', 'U 的秩是 κ+1，它属于 V<sub>κ+2</sub> 而非 V<sub>κ+1</sub>。包含 κ 的每个子集，不等于包含由它们组成的某个特定<i>集族</i>。'],
    ['No', '否', true],
  ], ['Correct: <span class="m">U ∉ Ult(V, U)</span> (a standard fact from L24). That is exactly why κ+2-strong is a genuinely stronger hypothesis than measurable.', '正确：<span class="m">U ∉ Ult(V, U)</span>（第 24 课的标准事实）。正因如此，κ+2-强才是比可测真正更强的假设。']);
})();

/* ================= §3 Woodin ================= */
(function woodin() {
  const svg = $('wdSvg');
  const X0 = 40, XD = 600;
  const fns = [
    { lab: 'f: α ↦ α+1', n: 34, en: 'Closure points of α ↦ α+1: exactly the limit ordinals (and 0). Plenty of them.', zh: 'α ↦ α+1 的封闭点：恰好是极限序数（以及 0）。非常多。' },
    { lab: 'f: α ↦ ω<sup>α</sup>', n: 16, en: 'Closure points of α ↦ ω<sup>α</sup>: 0 and the ε-numbers <span class="m">κ = ω<sup>κ</sup></span> below δ. (Not ω: already <span class="m">ω<sup>1</sup> = ω</span>.)', zh: 'α ↦ ω<sup>α</sup> 的封闭点：0 以及 δ 以下的 ε 数 <span class="m">κ = ω<sup>κ</sup></span>。（ω 不是：<span class="m">ω<sup>1</sup> = ω</span> 已经不小于 ω。）' },
    { lab: 'f: α ↦ |V<sub>α</sub>|⁺', n: 8, en: 'Closure points of α ↦ |V<sub>α</sub>|⁺: ω and the uncountable ℶ-fixed points <span class="m">κ = ℶ<sub>κ</sub></span>. Sparser.', zh: 'α ↦ |V<sub>α</sub>|⁺ 的封闭点：ω 以及不可数的 ℶ 不动点 <span class="m">κ = ℶ<sub>κ</sub></span>。更稀疏了。' },
    { lab: bil('f: α ↦ next inaccessible', 'f: α ↦ 下一个不可达'), n: 4, plain: true, en: 'Closure points of “next inaccessible above α”: the limits of inaccessible cardinals. Very sparse, yet Woodinness still promises a strong-enough κ among them.', zh: '“α 之上的下一个不可达基数”的封闭点：不可达基数的极限。非常稀疏，但伍丁性仍保证其中有足够强的 κ。' },
  ];
  let fi = 0, pick = 14;
  function pts() {
    const n = fns[fi].n, out = [];
    for (let i = 1; i <= n; i++) out.push(X0 + (XD - X0) * (1 - Math.pow(1 - i / (n + 1), 1.35)));
    return out;
  }
  function draw() {
    svg.innerHTML = '';
    const defs = el('defs', {}, svg);
    const mk = el('marker', { id: 'wdArr', viewBox: '0 0 10 10', refX: 8, refY: 5, markerWidth: 6, markerHeight: 6, orient: 'auto' }, defs);
    el('path', { d: 'M0,0 L10,5 L0,10 z', fill: C.meta }, mk);
    T(svg, 8, 74, 'V', { 'font-weight': 800, 'font-size': 15 });
    el('line', { x1: X0, y1: 70, x2: XD, y2: 70, stroke: C.ink, 'stroke-width': 2 }, svg);
    el('line', { x1: XD, y1: 58, x2: XD, y2: 82, stroke: C.ink, 'stroke-width': 3 }, svg);
    T(svg, XD + 8, 75, 'δ (Woodin · 伍丁)', { 'font-weight': 700 });
    T(svg, X0, 100, '0', { 'text-anchor': 'middle', class: 'm' });
    const P = pts();
    P.forEach((x, i) => {
      const g = el('g', { class: 'gnode' }, svg);
      el('rect', { x: x - 6, y: 54, width: 12, height: 32, fill: 'transparent' }, g);
      el('line', { x1: x, y1: 60, x2: x, y2: 80, stroke: i === pick ? C.meta : C.accent, 'stroke-width': i === pick ? 4 : 2 }, g);
      g.addEventListener('click', () => { pick = i; draw(); fire(); });
    });
    T(svg, X0, 40, 'closure points of f (click one) · f 的封闭点（点一个）', { fill: C.accent, 'font-size': 12.5 });
    if (pick < 0) {
      T(svg, 430, 190, '← click a tick to fire j with crit(j) = κ · 点击刻度，发射临界点为 κ 的 j', { 'text-anchor': 'middle', fill: C.muted });
      return;
    }
    const k = P[pick];
    // closure arrows: a few β < κ with f(β) < κ
    for (let t = 1; t <= 3; t++) {
      const b = X0 + (k - X0) * (t / 5), fb = b + (k - b) * 0.6;
      el('path', { d: `M ${b} 66 Q ${(b + fb) / 2} ${40 - t * 4} ${fb} 66`, fill: 'none', stroke: C.tru, 'stroke-width': 1.6, 'marker-end': 'url(#wdArr)' }, svg);
    }
    T(svg, k, 108, 'κ', { 'text-anchor': 'middle', fill: C.meta, 'font-weight': 800, 'font-size': 16 });
    T(svg, (X0 + k) / 2, 124, 'f″κ ⊆ κ', { 'text-anchor': 'middle', fill: C.tru, class: 'm', 'font-size': 12 });
    // M line
    const yM = 200;
    T(svg, 8, yM + 4, 'M', { 'font-weight': 800, 'font-size': 15, fill: C.accent });
    el('line', { x1: X0, y1: yM, x2: 840, y2: yM, stroke: C.accent, 'stroke-width': 2 }, svg);
    const jf = Math.min(k + 150 + (3 - fi) * 20, 700), jk = Math.min(jf + 110, 830);
    const br = el('rect', { x: X0, y: yM - 10, width: 0, height: 20, rx: 5, fill: C.accent, 'fill-opacity': 0.25 }, svg);
    br.style.transition = 'width .7s';
    requestAnimationFrame(() => br.setAttribute('width', jf - X0));
    T(svg, (X0 + jf) / 2, yM + 32, 'V_{j(f)(κ)} ⊆ M', { 'text-anchor': 'middle', class: 'm', fill: C.accent, 'font-weight': 700 });
    [[k, 'κ'], [jf, 'j(f)(κ)'], [jk, 'j(κ)']].forEach(([x, s]) => {
      el('line', { x1: x, y1: yM - 12, x2: x, y2: yM + 12, stroke: C.meta, 'stroke-width': 3 }, svg);
      T(svg, x, yM - 18, s, { 'text-anchor': 'middle', class: 'm', fill: C.meta, 'font-weight': 700 });
    });
    el('path', { d: `M ${k} 84 C ${k} 150, ${jk} 130, ${jk} ${yM - 30}`, fill: 'none', stroke: C.meta, 'stroke-width': 2.2, 'stroke-dasharray': '6 4', 'marker-end': 'url(#wdArr)' }, svg);
    T(svg, (k + jk) / 2, 140, 'j', { fill: C.meta, 'font-weight': 800, 'font-size': 16 });
    T(svg, 430, 262, 'positions are schematic · 位置仅为示意', { 'text-anchor': 'middle', fill: C.muted, 'font-size': 11.5 });
  }
  function fire() {
    okBox($('wdInfo'), bi(`${fns[fi].en}<br>You picked a closure point κ. Woodinness of δ promises that for <i>this</i> f <b>some</b> closure point κ &lt; δ is the critical point of a <span class="m">j : V → M</span> with <span class="m">V<sub>j(f)(κ)</sub> ⊆ M</span>. Change f and the witness κ may have to change.`,
      `${fns[fi].zh}<br>你选了一个封闭点 κ。δ 是伍丁基数，保证对<i>这个</i> f，<b>某个</b>封闭点 κ &lt; δ 是某个 <span class="m">j : V → M</span> 的临界点，且 <span class="m">V<sub>j(f)(κ)</sub> ⊆ M</span>。换一个 f，见证者 κ 可能就得跟着换。`), 'info');
  }
  const box = $('wdBtns');
  fns.forEach((f, i) => {
    const b = document.createElement('button');
    b.className = 'btn small' + (i === 0 ? ' sel' : '');
    b.innerHTML = f.plain ? f.lab : `<span class="m">${f.lab}</span>`;
    b.addEventListener('click', () => { fi = i; pick = -1; box.querySelectorAll('button').forEach((x, k) => x.classList.toggle('sel', k === i)); draw(); okBox($('wdInfo'), bi(f.en, f.zh), 'info'); });
    box.appendChild(b);
  });
  draw();
  fire();
  checkYourself('cy3', ['Must the <b>least</b> Woodin cardinal be measurable?', '<b>最小</b>的伍丁基数一定可测吗？'], [
    ['Yes', '是', false, 'No: the least Woodin cardinal is not even weakly compact. Its witnesses κ < δ are measurable, but δ itself need not be.', '不是：最小的伍丁基数连弱紧都不是。它的见证者 κ < δ 是可测的，但 δ 本身不必可测。'],
    ['No', '否', true],
  ], ['Right. The least Woodin cardinal is Mahlo (measurables below it are stationary) but not weakly compact, so not measurable. Woodinness is a property witnessed <i>below</i> δ.', '对。最小的伍丁基数是马洛基数（其下的可测基数构成平稳集），但不是弱紧的，因而不可测。伍丁性是在 δ <i>下方</i>得到见证的性质。']);
})();

/* ================= §4 supercompact / strongly compact ================= */
(function sc() {
  const svg = $('scSvg');
  let mode = 'sup';
  function draw() {
    svg.innerHTML = '';
    const n = 12, kN = 4, x0 = 70, gap = 34;
    T(svg, 14, 54, 'λ', { 'font-weight': 800, 'font-size': 16, class: 'm' });
    el('line', { x1: x0 - 20, y1: 50, x2: x0 + n * gap, y2: 50, stroke: C.ink, 'stroke-width': 1.5 }, svg);
    el('rect', { x: x0 - 14, y: 34, width: kN * gap, height: 32, rx: 8, fill: C.goldSoft, stroke: C.gold }, svg);
    T(svg, x0 - 14 + kN * gap / 2, 26, 'α < κ', { 'text-anchor': 'middle', fill: C.gold, class: 'm', 'font-size': 12 });
    T(svg, x0 + n * gap + 6, 54, 'α < λ', { class: 'm', 'font-size': 12, fill: C.muted });
    const y2 = 190, imgX = [];
    for (let i = 0; i < n; i++) imgX.push(i < kN ? x0 + i * gap : 330 + (i - kN) * 58);
    T(svg, 14, y2 + 4, 'M', { 'font-weight': 800, 'font-size': 16, fill: C.accent });
    el('line', { x1: x0 - 20, y1: y2, x2: 845, y2: y2, stroke: C.accent, 'stroke-width': 1.5 }, svg);
    el('line', { x1: 300, y1: y2 - 14, x2: 300, y2: y2 + 14, stroke: C.meta, 'stroke-width': 3 }, svg);
    T(svg, 300, y2 + 32, 'j(κ) > λ', { 'text-anchor': 'middle', class: 'm', fill: C.meta, 'font-weight': 700 });
    // D for strongly compact
    if (mode === 'str') {
      const D = el('rect', { x: x0 - 16, y: y2 - 26, width: 805 - x0, height: 52, rx: 24, fill: C.goldSoft, 'fill-opacity': 0.7, stroke: C.gold, 'stroke-width': 2, 'stroke-dasharray': '6 4', class: 'fadein' }, svg);
      D.style.animationDelay = '0.5s';
      for (let i = 0; i < 18; i++) {
        const x = x0 + 4 * gap + 10 + i * 24;
        if (imgX.some(v => Math.abs(v - x) < 10)) continue;
        const c = el('circle', { cx: x, cy: y2, r: 4, fill: '#b8a46a', class: 'pop' }, svg);
        c.style.animationDelay = (0.6 + i * 0.03) + 's';
      }
      T(svg, 840, y2 - 34, 'D ∈ M, j″λ ⊆ D, |D|^M < j(κ)', { 'text-anchor': 'end', class: 'm', fill: '#8a5a00', 'font-weight': 700 });
    } else {
      const L = el('rect', { x: x0 - 16, y: y2 - 18, width: 805 - x0, height: 36, rx: 18, fill: 'none', stroke: C.tru, 'stroke-width': 3, class: 'fadein' }, svg);
      L.style.animationDelay = '0.5s';
      T(svg, 840, y2 - 26, 'j″λ ∈ M  (from ^λM ⊆ M)', { 'text-anchor': 'end', class: 'm', fill: C.tru, 'font-weight': 700 });
    }
    for (let i = 0; i < n; i++) {
      const x = x0 + i * gap;
      el('circle', { cx: x, cy: 50, r: 6, fill: i < kN ? C.gold : C.ink }, svg);
      const ln = el('line', { x1: x, y1: 58, x2: imgX[i], y2: y2 - 8, stroke: i < kN ? C.gold : C.meta, 'stroke-width': 1.4, 'stroke-opacity': 0.7, class: 'fadein' }, svg);
      ln.style.animationDelay = (i * 0.04) + 's';
      const c = el('circle', { cx: imgX[i], cy: y2, r: 6, fill: i < kN ? C.gold : C.meta, class: 'pop' }, svg);
      c.style.animationDelay = (0.2 + i * 0.04) + 's';
    }
    T(svg, 160, 120, 'j(α) = α for α < κ', { class: 'm', fill: C.gold, 'font-size': 12 });
    T(svg, 520, 120, 'j(α) ≥ j(κ) > λ for κ ≤ α < λ', { class: 'm', fill: C.meta, 'font-size': 12 });
    T(svg, 430, 250, 'schematic · 示意图', { 'text-anchor': 'middle', fill: C.muted, 'font-size': 11.5 });
    okBox($('scInfo'), mode === 'sup'
      ? bi('<b>λ-supercompact:</b> the set <span class="m">j″λ</span> itself (green ring) is an element of M. Its M-cardinality is λ < j(κ). Normality of the derived measure <span class="m">U = {X ⊆ P<sub>κ</sub>(λ) : j″λ ∈ j(X)}</span> comes from using exactly <span class="m">j″λ</span> as the “seed”.',
        '<b>λ-超紧：</b>集合 <span class="m">j″λ</span> 本身（绿圈）是 M 的元素，它在 M 中的势是 λ < j(κ)。导出测度 <span class="m">U = {X ⊆ P<sub>κ</sub>(λ) : j″λ ∈ j(X)}</span> 之所以正规，正是因为用 <span class="m">j″λ</span> 本身作“种子”。')
      : bi('<b>λ-strongly compact:</b> M need only contain some set D (gold) that <i>covers</i> <span class="m">j″λ</span> and is small in M. The derived ultrafilter <span class="m">{X ⊆ P<sub>κ</sub>(λ) : D ∩ j(λ) ∈ j(X)}</span> is fine and κ-complete but need not be normal. Covering is weaker than capturing.',
        '<b>λ-强紧：</b>M 只需包含某个<i>覆盖</i> <span class="m">j″λ</span> 并且在 M 中很小的集合 D（金色）。导出的超滤 <span class="m">{X ⊆ P<sub>κ</sub>(λ) : D ∩ j(λ) ∈ j(X)}</span> 是精细且 κ-完全的，但不一定正规。“覆盖”比“捕获”弱。'), 'info');
  }
  $('scSup').addEventListener('click', () => { mode = 'sup'; $('scSup').classList.add('sel'); $('scStr').classList.remove('sel'); draw(); });
  $('scStr').addEventListener('click', () => { mode = 'str'; $('scStr').classList.add('sel'); $('scSup').classList.remove('sel'); draw(); });
  draw();
  checkYourself('cy4', ['Which is accurate?', '哪个说法准确？'], [
    ['Supercompact ⇒ strongly compact; whether they are equiconsistent is open', '超紧 ⇒ 强紧；两者是否等一致尚未解决', true],
    ['Supercompact ⇒ strongly compact, and they are known to be equiconsistent', '超紧 ⇒ 强紧，且已知两者等一致', false, 'Equiconsistency is conjectured by some but unproved; a proof seems to require an inner model theory for supercompact cardinals.', '有人猜测两者等一致，但尚未证明；证明似乎需要超紧基数的内模型理论。'],
    ['Strongly compact ⇒ supercompact', '强紧 ⇒ 超紧', false, 'No. Magidor: it is consistent that the least strongly compact is the least measurable, and the least measurable is never supercompact.', '不对。马吉多尔：最小强紧基数可以就是最小可测基数，而最小可测基数绝不是超紧的。'],
  ], ['Right. Normal fine ⇒ fine, so supercompact ⇒ strongly compact (ZFC). The exact consistency strength of a strongly compact cardinal is unknown.', '对。正规精细 ⇒ 精细，所以超紧 ⇒ 强紧（ZFC）。强紧基数的确切一致性强度未知。']);
})();

/* ================= §5 extendible & huge ================= */
(function huge() {
  const svg = $('hgSvg');
  const KX = [60, 210, 380, 530, 650, 735], LX = 800;
  const names = [
    ['n = 0: measurable (ultrapower)', 'n = 0：可测（超幂）'],
    ['n = 1: huge', 'n = 1：巨大'],
    ['n = 2: 2-huge', 'n = 2：2-巨大'],
    ['n = 3: 3-huge', 'n = 3：3-巨大'],
    ['n = 4: 4-huge', 'n = 4：4-巨大'],
    ['n = ω: ω-huge (inconsistent!)', 'n = ω：ω-巨大（矛盾！）'],
  ];
  let n = 1, shown = 6, token = 0;
  function draw() {
    svg.innerHTML = '';
    const defs = el('defs', {}, svg);
    const mk = el('marker', { id: 'hgArr', viewBox: '0 0 10 10', refX: 8, refY: 5, markerWidth: 6, markerHeight: 6, orient: 'auto' }, defs);
    el('path', { d: 'M0,0 L10,5 L0,10 z', fill: C.meta }, mk);
    const y = 130, omega = n === 5;
    const end = omega ? LX : KX[n];
    el('rect', { x: 30, y: y - 16, width: Math.max(0, end - 30), height: 32, rx: 8, fill: omega ? C.fal : C.accent, 'fill-opacity': 0.22, stroke: omega ? C.fal : C.accent }, svg);
    T(svg, 36, y + 64, omega ? '^λ M ⊆ M with λ = sup κₙ  — refuted in ZFC (Kunen) · 被 ZFC 否证（库能）' : `^{κ${'₀₁₂₃₄'[n]}} M ⊆ M`, { class: 'm', fill: omega ? C.fal : C.accent, 'font-weight': 700 });
    el('line', { x1: 20, y1: y, x2: 845, y2: y, stroke: C.ink, 'stroke-width': 1.5 }, svg);
    KX.slice(0, 5).forEach((x, i) => {
      if (i >= shown) return;
      el('line', { x1: x, y1: y - 10, x2: x, y2: y + 10, stroke: C.ink, 'stroke-width': 2.5 }, svg);
      T(svg, x, y + 30 + (i % 2 ? 0 : 0), `κ${'₀₁₂₃₄'[i]}`, { 'text-anchor': 'middle', class: 'm', 'font-weight': 700, 'font-size': 14 });
      if (i < 4 && i + 1 < shown) {
        const x2 = KX[i + 1];
        el('path', { d: `M ${x + 4} ${y - 14} Q ${(x + x2) / 2} ${y - 70 - (4 - i) * 6} ${x2 - 4} ${y - 14}`, fill: 'none', stroke: C.meta, 'stroke-width': 2, 'marker-end': 'url(#hgArr)', class: 'fadein' }, svg);
        T(svg, (x + x2) / 2, y - 14 - (70 + (4 - i) * 6) / 2 - 6, 'j', { 'text-anchor': 'middle', fill: C.meta, 'font-weight': 800 });
      }
    });
    if (shown > 4) T(svg, 700, y + 4, '…', { 'font-size': 18 });
    el('line', { x1: LX, y1: y - 18, x2: LX, y2: y + 18, stroke: C.fal, 'stroke-width': 3 }, svg);
    T(svg, LX, y + 32, 'λ = sup κₙ', { 'text-anchor': 'middle', class: 'm', fill: C.fal, 'font-weight': 700 });
    T(svg, 30, 24, 'critical sequence κ₀ = κ, κₙ₊₁ = j(κₙ) · 临界序列', { fill: C.muted, 'font-size': 12.5 });
    $('hgName').innerHTML = bil(names[n][0], names[n][1]);
    okBox($('hgInfo'), omega
      ? bi('ω-huge would mean <span class="m"><sup>λ</sup>M ⊆ M</span> for <span class="m">λ = sup<sub>n</sub> κ<sub>n</sub></span>. Then <span class="m">j″λ ∈ M</span>, which Kunen’s argument (§6) shows is impossible in ZFC. The ladder of n-huge cardinals has no top rung of this form.', 'ω-巨大意味着对 <span class="m">λ = sup<sub>n</sub> κ<sub>n</sub></span> 有 <span class="m"><sup>λ</sup>M ⊆ M</span>。于是 <span class="m">j″λ ∈ M</span>，而库能的论证（§6）表明这在 ZFC 中不可能。n-巨大的阶梯没有这种形式的顶端。', )
      : n === 0 ? bi('n = 0: closure under κ-sequences only. That is the measure ultrapower (L24).', 'n = 0：只对 κ-序列封闭。这正是测度超幂（第 24 课）。')
        : bi(`${n}-huge: M is closed under <span class="m">κ<sub>${n}</sub> = ${n === 1 ? 'j(κ)' : `j<sup>${n}</sup>(κ)`}</span>-sequences. Each extra step of the critical sequence is a big jump in consistency strength.`, `${n}-巨大：M 对 <span class="m">κ<sub>${n}</sub> = ${n === 1 ? 'j(κ)' : `j<sup>${n}</sup>(κ)`}</span>-序列封闭。临界序列每多走一步，一致性强度都大幅跃升。`), omega ? 'bad' : 'info');
  }
  $('hgN').addEventListener('input', e => { n = +e.target.value; draw(); });
  $('hgPlay').addEventListener('click', async () => {
    const my = ++token;
    for (shown = 1; shown <= 6; shown++) { if (my !== token) return; draw(); await sleep(450); }
    shown = 6;
  });
  draw();
  checkYourself('cy5', ['Suppose huge and supercompact cardinals both exist; κ is the least huge and μ the least supercompact. Then…', '设巨大基数与超紧基数都存在；κ 是最小巨大基数，μ 是最小超紧基数。那么……'], [
    ['κ < μ', 'κ < μ', true],
    ['κ > μ', 'κ > μ', false, 'It is the other way round: huge has higher <i>consistency strength</i>, but the least huge is <i>smaller</i>.', '恰恰相反：巨大的<i>一致性强度</i>更高，但最小巨大基数<i>更小</i>。'],
    ['κ = μ', 'κ = μ', false],
  ], ['Right: κ < μ. Strength in the sense of consistency is not the same as size. (Reason: if some κ ≥ μ were huge, the supercompactness of μ would reflect “there is a huge cardinal” down below μ.)', '对：κ < μ。一致性意义上的强度不同于大小。（理由：若某个 κ ≥ μ 是巨大基数，μ 的超紧性会把“存在巨大基数”反射到 μ 以下。）']);
})();

/* ================= §6 rank-into-rank & Kunen ================= */
(function rir() {
  const svg = $('rrSvg');
  const P = { k0: 70, k1: 190, k2: 300, k3: 380, lam: 520, l1: 610, l2: 700 };
  const modes = [
    { b: 'I3', en: '<b>I3</b>: <span class="m">j : V<sub>λ</sub> → V<sub>λ</sub></span>. The domain and target are the same rank initial segment.', zh: '<b>I3</b>：<span class="m">j : V<sub>λ</sub> → V<sub>λ</sub></span>。定义域与目标是同一个秩初始段。', to: P.lam },
    { b: 'I2', en: '<b>I2</b>: <span class="m">j : V → M</span> with <span class="m">V<sub>λ</sub> ⊆ M</span>. Strictly between I3 and I1 in strength.', zh: '<b>I2</b>：<span class="m">j : V → M</span>，且 <span class="m">V<sub>λ</sub> ⊆ M</span>。强度严格介于 I3 与 I1 之间。', to: P.lam, i2: true },
    { b: 'I1', en: '<b>I1</b>: <span class="m">j : V<sub>λ+1</sub> → V<sub>λ+1</sub></span>. One level more: j acts on all subsets of <span class="m">V<sub>λ</sub></span>.', zh: '<b>I1</b>：<span class="m">j : V<sub>λ+1</sub> → V<sub>λ+1</sub></span>。再高一层：j 作用在 <span class="m">V<sub>λ</sub></span> 的所有子集上。', to: P.l1 },
    { b: 'I0', en: '<b>I0</b>: <span class="m">j : L(V<sub>λ+1</sub>) → L(V<sub>λ+1</sub>)</span>, crit < λ. <span class="m">L(V<sub>λ+1</sub>)</span> sticks out above <span class="m">V<sub>λ+1</sub></span> but does not contain all of <span class="m">V<sub>λ+2</sub></span>, and AC fails in it, so Kunen’s argument does not apply. Woodin: I0 ⇒ <span class="m">AD<sup>L(ℝ)</sup></span>, and <span class="m">L(V<sub>λ+1</sub>)</span> behaves strikingly like <span class="m">L(ℝ)</span> under AD.', zh: '<b>I0</b>：<span class="m">j : L(V<sub>λ+1</sub>) → L(V<sub>λ+1</sub>)</span>，crit < λ。<span class="m">L(V<sub>λ+1</sub>)</span> 伸出 <span class="m">V<sub>λ+1</sub></span> 之上，但不包含整个 <span class="m">V<sub>λ+2</sub></span>，且其中 AC 不成立，所以库能的论证用不上。伍丁：I0 ⇒ <span class="m">AD<sup>L(ℝ)</sup></span>，并且 <span class="m">L(V<sub>λ+1</sub>)</span> 与 AD 下的 <span class="m">L(ℝ)</span> 惊人地相似。', to: P.l1, i0: true },
    { b: 'V<sub>λ+2</sub>', en: '<span class="m">j : V<sub>λ+2</sub> → V<sub>λ+2</sub></span>: <span class="status st-no">ZFC ⊢ ¬</span> (Kunen). The wall.', zh: '<span class="m">j : V<sub>λ+2</sub> → V<sub>λ+2</sub></span>：<span class="status st-no">ZFC ⊢ ¬</span>（库能）。这就是那堵墙。', to: P.l2, bad: true },
    { b: 'j : V → V', en: '<b>Reinhardt</b>: <span class="m">j : V → V</span>. Restricting to <span class="m">V<sub>λ+2</sub></span> hits the wall, so <span class="status st-no">ZFC ⊢ ¬</span>. In ZF: <span class="status st-open">open</span>.', zh: '<b>莱因哈特</b>：<span class="m">j : V → V</span>。限制到 <span class="m">V<sub>λ+2</sub></span> 就撞墙，所以 <span class="status st-no">ZFC ⊢ ¬</span>。在 ZF 中：<span class="status st-open">未解决</span>。', to: 850, bad: true },
  ];
  let mi = 0;
  function draw() {
    svg.innerHTML = '';
    const m = modes[mi], y = 150;
    const defs = el('defs', {}, svg);
    const pat = el('pattern', { id: 'brick', width: 24, height: 14, patternUnits: 'userSpaceOnUse' }, defs);
    el('rect', { width: 24, height: 14, fill: '#c92a2a' }, pat);
    el('path', { d: 'M0 7 H24 M12 0 V7 M0 7 V14 M24 7 V14', stroke: '#ffe3e3', 'stroke-width': 1.5 }, pat);
    const mk = el('marker', { id: 'rrArr', viewBox: '0 0 10 10', refX: 8, refY: 5, markerWidth: 6, markerHeight: 6, orient: 'auto' }, defs);
    el('path', { d: 'M0,0 L10,5 L0,10 z', fill: C.meta }, mk);
    // domain bar
    const col = m.bad ? C.fal : C.meta;
    el('rect', { x: 30, y: y - 18, width: Math.min(m.to, 850) - 30, height: 36, rx: 8, fill: col, 'fill-opacity': 0.2, stroke: col, 'stroke-width': 2 }, svg);
    if (m.i0) {
      el('path', { d: `M ${P.l1 - 40} ${y - 18} C ${P.l1 + 10} ${y - 70}, ${P.l2 + 10} ${y - 60}, ${P.l2 - 30} ${y - 18}`, fill: col, 'fill-opacity': 0.2, stroke: col, 'stroke-width': 2, 'stroke-dasharray': '5 4' }, svg);
      T(svg, P.l1 + 40, y - 58, 'L(V_{λ+1})', { 'text-anchor': 'middle', class: 'm', fill: col, 'font-weight': 700 });
    }
    if (m.i2) T(svg, 300, y - 26, 'j : V → M,  V_λ ⊆ M', { 'text-anchor': 'middle', class: 'm', fill: col, 'font-weight': 700 });
    // self-map arrow
    if (!m.i2) {
      const xe = Math.min(m.to, 840) - 20;
      el('path', { d: `M ${xe - 40} ${y + 22} C ${xe - 20} ${y + 80}, ${xe + 30} ${y + 70}, ${xe} ${y + 22}`, fill: 'none', stroke: col, 'stroke-width': 2.2, 'marker-end': 'url(#rrArr)' }, svg);
      T(svg, xe - 10, y + 88, 'j : X → X', { 'text-anchor': 'middle', class: 'm', fill: col, 'font-weight': 700 });
    }
    el('line', { x1: 20, y1: y, x2: 850, y2: y, stroke: C.ink, 'stroke-width': 1.2 }, svg);
    [['κ₀', P.k0], ['κ₁', P.k1], ['κ₂', P.k2], ['κ₃', P.k3], ['λ', P.lam], ['λ+1', P.l1], ['λ+2', P.l2]].forEach(([s, x]) => {
      el('line', { x1: x, y1: y - 8, x2: x, y2: y + 8, stroke: C.ink, 'stroke-width': 2 }, svg);
      T(svg, s === 'λ+2' ? x - 30 : x, y + 112, s, { 'text-anchor': 'middle', class: 'm', 'font-weight': 700 });
      el('line', { x1: x, y1: y + 8, x2: x, y2: y + 98, stroke: C.ink, 'stroke-opacity': 0.12 }, svg);
    });
    T(svg, 440, y + 4, '…', { 'font-size': 16 });
    // wall
    el('rect', { x: P.l2 - 10, y: 20, width: 20, height: 250, fill: 'url(#brick)', stroke: '#8a1c1c' }, svg);
    T(svg, P.l2 + 16, 36, 'Kunen wall (ZFC)', { fill: C.fal, 'font-weight': 700 });
    T(svg, P.l2 + 16, 52, '库能之墙（ZFC）', { fill: C.fal, 'font-weight': 700 });
    T(svg, 30, 30, 'rank · 秩 →', { fill: C.muted, 'font-size': 12 });
    okBox($('rrInfo'), bi(m.en, m.zh), m.bad ? 'bad' : 'info');
  }
  const box = $('rrBtns');
  modes.forEach((m, i) => {
    const b = document.createElement('button');
    b.className = 'btn small' + (i === 0 ? ' sel' : '');
    b.innerHTML = `<span class="m">${m.b}</span>`;
    b.addEventListener('click', () => { mi = i; box.querySelectorAll('button').forEach((x, k) => x.classList.toggle('sel', k === i)); draw(); });
    box.appendChild(b);
  });
  draw();
  checkYourself('cy6', ['Which of these does Kunen’s theorem refute in ZFC?', '库能定理在 ZFC 中否证了下面哪一个？'], [
    ['I3', 'I3', false, 'No. I3 lives at V<sub>λ</sub>, below the wall; it is not known to be inconsistent.', '不对。I3 位于 V<sub>λ</sub>，在墙下方；尚未发现它矛盾。'],
    ['I0', 'I0', false, 'No. L(V<sub>λ+1</sub>) does not satisfy AC, and Kunen’s proof needs a choice function in the domain of j.', '不对。L(V<sub>λ+1</sub>) 不满足 AC，而库能的证明需要 j 的定义域中有选择函数。'],
    ['a nontrivial j : V<sub>λ+2</sub> → V<sub>λ+2</sub>', '非平凡的 j : V<sub>λ+2</sub> → V<sub>λ+2</sub>', true],
  ], ['Right. The ω-Jónsson function lives in V<sub>λ+2</sub> and exists by AC; that is the precise location of the wall.', '对。ω-琼森函数位于 V<sub>λ+2</sub>，其存在依赖 AC；墙的确切位置就在这里。']);
})();

/* ================= §7 ladder ================= */
(function ladder() {
  const svg = $('ladSvg');
  const R = {
    L: { col: '#2f9e44', en: 'compatible with V = L', zh: '与 V = L 相容' },
    S: { col: '#1098ad', en: 'implies 0♯ (so V ≠ L)', zh: '蕴涵 0♯（故 V ≠ L）' },
    K: { col: '#3b5bdb', en: 'canonical inner models known', zh: '已知典范内模型' },
    B: { col: '#f08c00', en: 'beyond current inner model theory', zh: '超出现有内模型理论' },
    X: { col: '#e03131', en: 'inconsistent with AC (ZF: open)', zh: '与 AC 矛盾（ZF 中未解决）' },
  };
  const rungs = [
    ['L', 'inaccessible', '不可达基数', 'κ uncountable, regular, strong limit. If κ is inaccessible in V it is inaccessible in L, so this is compatible with V = L. V_κ ⊨ ZFC, hence ZFC ⊬ “there is an inaccessible” (Gödel II).', 'κ 不可数、正则、强极限。在 V 中不可达，则在 L 中也不可达，所以与 V = L 相容。V_κ ⊨ ZFC，因此 ZFC 证不出“存在不可达基数”（哥德尔第二定理）。'],
    ['L', 'Mahlo', '马洛基数', 'The inaccessibles below κ form a stationary set. Also downward absolute to L.', 'κ 以下的不可达基数构成平稳集。同样向下绝对到 L。'],
    ['L', 'weakly compact', '弱紧基数', 'κ → (κ)²₂; equivalently Π¹₁-indescribable. Weakly compact cardinals are weakly compact in L (L23).', 'κ → (κ)²₂；等价于 Π¹₁-不可描述。弱紧基数在 L 中仍弱紧（第 23 课）。'],
    ['S', 'Ramsey', '拉姆齐基数', 'κ → (κ)^{<ω}_2. A Ramsey cardinal implies that 0♯ exists, so V ≠ L. (Everything above also implies 0♯.)', 'κ → (κ)^{<ω}_2。拉姆齐基数蕴涵 0♯ 存在，故 V ≠ L。（其上的一切也都蕴涵 0♯。）'],
    ['K', 'measurable', '可测基数', 'Critical point of j : V → M (L24). Scott: V ≠ L. Canonical inner model: L[U]. Martin: implies Π¹₁-determinacy.', 'j : V → M 的临界点（第 24 课）。斯科特：V ≠ L。典范内模型：L[U]。马丁：蕴涵 Π¹₁-决定性。'],
    ['K', 'strong', '强基数', 'V_λ ⊆ M for every λ (§2). Inner models: Mitchell-style extender models.', '对每个 λ 有 V_λ ⊆ M（§2）。内模型：米切尔式扩张子模型。'],
    ['K', 'Woodin', '伍丁基数', '§3. With a measurable above: Π¹₂-determinacy. Inner models with Woodin cardinals (Mitchell–Steel) are well developed.', '§3。上方再有可测基数：Π¹₂-决定性。含伍丁基数的内模型（米切尔–斯蒂尔）已发展成熟。'],
    ['K', 'ω Woodins', 'ω 个伍丁基数', 'Infinitely many Woodins ⇒ PD. Con(ZFC + ω Woodins) ⇔ Con(ZF + AD) (Woodin). With a measurable above: AD^{L(ℝ)} (§10).', '无穷多个伍丁 ⇒ PD。Con(ZFC + ω 个伍丁) ⇔ Con(ZF + AD)（伍丁）。上方再有可测：AD^{L(ℝ)}（§10）。'],
    ['B', 'superstrong', '超强基数', 'V_{j(κ)} ⊆ M. Fine-structural extender models (Mitchell–Steel) are designed for hypotheses below a superstrong, and their iterability is proved only well below that (roughly up to a Woodin limit of Woodin cardinals). So the edge of “canonical inner models known” lies somewhere between ω Woodins and here; the boundary is approximate.', 'V_{j(κ)} ⊆ M。精细结构的扩张子模型（米切尔–斯蒂尔）是为低于超强基数的假设设计的，而其可迭代性只在远低于此处得到证明（大约到“伍丁基数的伍丁极限”）。所以“已知典范内模型”的边界位于 ω 个伍丁基数与这里之间；这条边界只是大致的。'],
    ['B', 'strongly compact', '强紧基数', '§4. Exact consistency strength UNKNOWN: placed between Woodin (well above it) and supercompact (upper bound). Whether it equals supercompact is open.', '§4。确切一致性强度<b>未知</b>：介于伍丁（远高于它）与超紧（上界）之间。是否等于超紧尚未解决。', true],
    ['B', 'supercompact', '超紧基数', '^λM ⊆ M for all λ (§4). Finding a canonical inner model for a supercompact is a central open problem (Ultimate L, §11).', '对所有 λ 有 ^λM ⊆ M（§4）。为超紧基数找典范内模型是核心未解决问题（终极 L，§11）。'],
    ['B', 'extendible', '可扩基数', 'j : V_{κ+η} → V_ζ for all η (§5). Extendible ⇒ supercompact.', '对所有 η 有 j : V_{κ+η} → V_ζ（§5）。可扩 ⇒ 超紧。'],
    ['B', "Vopěnka’s principle", '沃彭卡原理', 'Every proper class of structures (same type) has one that elementarily embeds into another. Implies a proper class of extendibles. (A schema / class statement.)', '每个由同类结构组成的真类中，都有一个能初等嵌入到另一个之中。蕴涵存在真类多个可扩基数。（这是一个公理模式 / 类陈述。）'],
    ['B', 'huge', '巨大基数', '^{j(κ)}M ⊆ M (§5). Higher consistency strength than supercompact, though the least huge is below the least supercompact.', '^{j(κ)}M ⊆ M（§5）。一致性强度高于超紧，但最小巨大基数小于最小超紧基数。'],
    ['B', 'n-huge (n ≥ 2)', 'n-巨大（n ≥ 2）', '^{jⁿ(κ)}M ⊆ M. Strictly increasing in n.', '^{jⁿ(κ)}M ⊆ M。随 n 严格递增。'],
    ['B', 'I3', 'I3', 'j : V_λ → V_λ (§6). Above every n-huge.', 'j : V_λ → V_λ（§6）。高于所有 n-巨大。'],
    ['B', 'I2', 'I2', 'j : V → M, V_λ ⊆ M, λ = sup of the critical sequence.', 'j : V → M，V_λ ⊆ M，λ 为临界序列的上确界。'],
    ['B', 'I1', 'I1', 'j : V_{λ+1} → V_{λ+1}.', 'j : V_{λ+1} → V_{λ+1}。'],
    ['B', 'I0', 'I0', 'j : L(V_{λ+1}) → L(V_{λ+1}), crit < λ. The strongest commonly studied axiom not known to be inconsistent with ZFC.', 'j : L(V_{λ+1}) → L(V_{λ+1})，crit < λ。常被研究的、尚未发现与 ZFC 矛盾的最强公理。'],
    ['W'],
    ['X', 'Reinhardt', '莱因哈特基数', 'crit of j : V → V. ZFC ⊢ ¬ (Kunen). Consistency with ZF: OPEN.', 'j : V → V 的临界点。ZFC ⊢ ¬（库能）。与 ZF 的一致性：<b>未解决</b>。'],
    ['X', 'super Reinhardt', '超莱因哈特基数', 'For every α there is j : V → V with crit κ and j(κ) > α. ZF: open.', '对每个 α，存在 crit 为 κ 且 j(κ) > α 的 j : V → V。ZF 中：未解决。'],
    ['X', 'Berkeley', '伯克利基数', 'Every transitive M ∋ δ has nontrivial j : M → M with crit below δ and above any given α < δ (§6). Stronger than Reinhardt. ZF: open.', '每个含 δ 的传递集 M 都有非平凡 j : M → M，其临界点低于 δ 且高于任给的 α < δ（§6）。强于莱因哈特。ZF 中：未解决。'],
  ];
  const H = 40, Y0 = 950, X1 = 120, W = 330;
  let sel = -1, focus = null;
  const legend = $('ladLegend');
  Object.entries(R).forEach(([k, r]) => {
    const b = document.createElement('button');
    b.className = 'btn small';
    b.style.borderLeft = `6px solid ${r.col}`;
    b.innerHTML = bil(r.en, r.zh);
    b.addEventListener('click', () => { focus = focus === k ? null : k; legend.querySelectorAll('button').forEach(x => x.classList.toggle('sel', x === b && focus === k)); draw(); });
    legend.appendChild(b);
  });
  function draw() {
    svg.innerHTML = '';
    T(svg, 14, 20, 'stronger ↑ · 更强 ↑', { fill: C.muted, 'font-size': 12 });
    // ladder rails
    el('line', { x1: X1 - 8, y1: 30, x2: X1 - 8, y2: Y0 + 10, stroke: '#b8b3a6', 'stroke-width': 4 }, svg);
    el('line', { x1: X1 + W + 8, y1: 30, x2: X1 + W + 8, y2: Y0 + 10, stroke: '#b8b3a6', 'stroke-width': 4 }, svg);
    // region bands
    let start = 0;
    for (let i = 0; i <= rungs.length; i++) {
      const cur = rungs[start][0];
      if (i === rungs.length || rungs[i][0] !== cur) {
        if (cur !== 'W') {
          const yTop = Y0 - i * H + 6, yBot = Y0 - start * H + 6;
          el('rect', { x: 18, y: yTop + 2, width: 18, height: yBot - yTop - 4, rx: 6, fill: R[cur].col, opacity: focus && focus !== cur ? 0.2 : 0.9 }, svg);
        }
        start = i;
      }
    }
    rungs.forEach((r, i) => {
      const y = Y0 - (i + 1) * H + 10;
      if (r[0] === 'W') {
        const pat = el('pattern', { id: 'brick2', width: 24, height: 14, patternUnits: 'userSpaceOnUse' }, svg);
        el('rect', { width: 24, height: 14, fill: '#c92a2a' }, pat);
        el('path', { d: 'M0 7 H24 M12 0 V7 M0 7 V14 M24 7 V14', stroke: '#ffe3e3', 'stroke-width': 1.5 }, pat);
        el('rect', { x: X1 - 30, y: y + 4, width: W + 60, height: 26, fill: 'url(#brick2)' }, svg);
        T(svg, X1 + W / 2, y + 22, 'KUNEN WALL (ZFC) · 库能之墙', { 'text-anchor': 'middle', fill: '#fff', 'font-weight': 800, stroke: '#8a1c1c', 'stroke-width': 5, 'paint-order': 'stroke' });
        return;
      }
      const g = el('g', { class: 'ladder-rung' + (i === sel ? ' sel' : '') }, svg);
      const dim = focus && focus !== r[0];
      g.style.opacity = dim ? 0.25 : 1;
      el('rect', { class: 'bar', x: X1, y, width: W, height: H - 8, rx: 8, fill: R[r[0]].col, 'fill-opacity': 0.16, stroke: R[r[0]].col, 'stroke-width': 1.5, 'stroke-dasharray': r[5] ? '6 4' : 'none' }, g);
      T(g, X1 + 12, y + 21, r[1], { 'font-weight': 700 });
      T(g, X1 + W - 12, y + 21, r[2], { 'text-anchor': 'end', fill: '#4a5568' });
      g.addEventListener('click', () => { sel = i; draw(); info(); });
    });
    // strongly compact bracket
    const iW = rungs.findIndex(r => r[1] === 'Woodin'), iS = rungs.findIndex(r => r[1] === 'supercompact');
    const yA = Y0 - (iS + 1) * H + 10, yB = Y0 - (iW + 1) * H + 10 + H - 8;
    el('path', { d: `M ${X1 + W + 100} ${yA} h 10 V ${yB} h -10`, fill: 'none', stroke: C.gold, 'stroke-width': 2, 'stroke-dasharray': '5 4' }, svg);
    T(svg, X1 + W + 116, (yA + yB) / 2 - 6, 'strongly', { fill: '#8a5a00', 'font-size': 11.5 });
    T(svg, X1 + W + 116, (yA + yB) / 2 + 8, 'compact: ?', { fill: '#8a5a00', 'font-size': 11.5 });
    T(svg, X1 + W + 116, (yA + yB) / 2 + 22, '强紧：?', { fill: '#8a5a00', 'font-size': 11.5 });
    // determinacy markers
    const iWs = rungs.findIndex(r => r[1] === 'ω Woodins'), iM = rungs.findIndex(r => r[1] === 'measurable');
    T(svg, X1 + W + 22, Y0 - (iWs + 1) * H + 31, '≡ AD', { fill: C.teal, 'font-weight': 700, 'font-size': 12 });
    T(svg, X1 + W + 22, Y0 - (iM + 1) * H + 31, '⇒ Π¹₁-Det', { fill: C.teal, 'font-weight': 700, 'font-size': 12 });
  }
  function info() {
    const r = rungs[sel];
    okBox($('ladInfo'), `<b>${bil(r[1], r[2])}</b><br><span class="status" style="background:${R[r[0]].col}">${bil(R[r[0]].en, R[r[0]].zh)}</span><br>` + bi(r[3], r[4]), 'info');
  }
  draw();
  okBox($('ladInfo'), bi('Click a rung of the ladder. Colors mark regions; click a legend button to highlight one region. The region of a rung is the <i>first</i> description that applies (every rung above 0♯ also implies 0♯).',
    '点击阶梯的某一级。颜色表示区域；点图例按钮可突出某个区域。每一级的区域取<i>第一个</i>适用的描述（0♯ 以上的每一级也都蕴涵 0♯）。'), 'info');
  checkYourself('cy7', ['Is “all large-cardinal axioms are linearly ordered by consistency strength” a theorem?', '“所有大基数公理都按一致性强度线性排序”是定理吗？'], [
    ['Yes, of ZFC', '是，是 ZFC 的定理', false, 'It cannot even be stated as a theorem: there is no formal definition of “large-cardinal axiom”. It is an empirical observation.', '它甚至无法作为定理陈述：“大基数公理”并无形式定义。这是一个经验观察。'],
    ['No, it is an observation (with gaps, e.g. strongly compact)', '不是，它是一个观察（且有空缺，如强紧）', true],
  ], ['Right. It is a striking, unexplained regularity, and in some cases (strongly compact) we do not even know where the rung goes.', '对。这是一个惊人且尚未得到解释的规律；在某些情形（强紧）我们甚至不知道这一级该放在哪里。']);
})();

/* ================= game tree drawing (shared by §8 and E2) ================= */
function GameTree(svg, opts) {
  const b = 2, d = 4, W = 860, H = 330;
  const leafX = i => 40 + i * ((W - 80) / (Math.pow(b, d) - 1));
  const yOf = k => 34 + k * 66;
  const xs = [];
  for (let k = d; k >= 0; k--) {
    xs[k] = [];
    for (let i = 0; i < Math.pow(b, k); i++) xs[k][i] = k === d ? leafX(i) : (xs[k + 1][i * b] + xs[k + 1][i * b + b - 1]) / 2;
  }
  const state = { leaves: opts.leaves.slice(), labels: null, user: null, win: null };
  function render() {
    svg.innerHTML = '';
    for (let k = 0; k < d; k++) {
      T(svg, 4, yOf(k) + 4, moverAt(k), { 'font-size': 11, fill: moverAt(k) === 'I' ? C.accent : C.gold, 'font-weight': 800 });
    }
    T(svg, 4, yOf(d) + 4, '⚑', { 'font-size': 12, fill: C.muted });
    for (let k = 1; k <= d; k++) for (let i = 0; i < Math.pow(b, k); i++) {
      const p = Math.floor(i / b);
      el('line', { class: 'gedge' + (state.win && state.win.has(k + ',' + i) ? ' win' : ''), x1: xs[k - 1][p], y1: yOf(k - 1), x2: xs[k][i], y2: yOf(k) }, svg);
    }
    for (let k = 0; k <= d; k++) for (let i = 0; i < Math.pow(b, k); i++) {
      const g = el('g', { class: 'gnode', transform: `translate(${xs[k][i]},${yOf(k)})` }, svg);
      let lab = '', fill = '#fff', stroke = '#9aa0aa';
      if (k === d) lab = state.leaves[i];
      else if (state.user) lab = state.user[k][i] || '?';
      else if (state.labels) lab = state.labels[k][i];
      if (lab === 'I') { fill = C.accentSoft; stroke = C.accent; }
      if (lab === 'II') { fill = C.goldSoft; stroke = C.gold; }
      if (state.marks && state.marks[k + ',' + i] === false) stroke = C.fal;
      if (k === d) el('rect', { x: -14, y: -13, width: 28, height: 26, rx: 5, fill, stroke, 'stroke-width': 2 }, g);
      else el('circle', { r: 16, fill, stroke }, g);
      const t = T(g, 0, 5, lab, { 'text-anchor': 'middle', 'font-weight': 800, 'font-size': 12.5, fill: lab === 'I' ? C.accent : lab === 'II' ? '#8a5a00' : C.muted });
      if (k === d && opts.onLeaf) g.addEventListener('click', () => opts.onLeaf(i));
      if (k < d && opts.onInner) g.addEventListener('click', () => opts.onInner(k, i));
    }
    T(svg, W - 8, H - 6, 'I / II = who wins from this node · 从该结点出发谁必胜', { 'text-anchor': 'end', 'font-size': 11, fill: C.muted });
  }
  state.render = render;
  render();
  return state;
}

/* ================= §8 finite games ================= */
(function finite() {
  const b = 2, d = 4;
  const rand = () => Array.from({ length: 16 }, () => Math.random() < 0.5 ? 'I' : 'II');
  let token = 0;
  const G = GameTree($('fgSvg'), { leaves: rand(), onLeaf: i => { token++; G.leaves[i] = G.leaves[i] === 'I' ? 'II' : 'I'; G.labels = null; G.win = null; G.render(); clearBox($('fgMsg')); } });
  async function solve() {
    const my = ++token;
    const full = solveGame(G.leaves, b, d);
    G.labels = full.map((row, k) => k === d ? row : row.map(() => ''));
    G.win = null;
    G.render();
    for (let k = d - 1; k >= 0; k--) {
      await sleep(450);
      if (my !== token) return;
      G.labels[k] = full[k].slice();
      G.render();
    }
    await sleep(300);
    if (my !== token) return;
    G.win = strategyEdges(full, b, d);
    G.render();
    const W = full[0][0];
    okBox($('fgMsg'), bi(`Root labelled <b>${W}</b>: player ${W} has a winning strategy (purple edges). At ${W}'s nodes the strategy picks one good child; at the opponent’s nodes it must answer <i>every</i> child.`,
      `根结点标为 <b>${W}</b>：玩家 ${W} 有获胜策略（紫色边）。在 ${W} 的结点，策略只选一个好的子结点；在对手的结点，必须应对<i>每一个</i>子结点。`), 'ok');
  }
  $('fgSolve').addEventListener('click', solve);
  $('fgRand').addEventListener('click', () => { token++; G.leaves = rand(); G.labels = null; G.win = null; G.render(); clearBox($('fgMsg')); });
  $('fgClear').addEventListener('click', () => { token++; G.labels = null; G.win = null; G.render(); clearBox($('fgMsg')); });
  checkYourself('cy8', ['At a node where <b>II</b> is to move, the node is labelled I exactly when…', '在轮到 <b>II</b> 走的结点，该结点标为 I 当且仅当……'], [
    ['some child is labelled I', '某个子结点标为 I', false, 'That would let II simply avoid that child. II chooses, so I needs <i>every</i> option to be good for I.', '那样 II 只要避开那个子结点就行了。是 II 在选，所以 I 需要<i>每个</i>选项都对 I 有利。'],
    ['every child is labelled I', '每个子结点都标为 I', true],
  ], ['Right: ∀ at the opponent’s nodes, ∃ at your own. This is the alternation <span class="m">∃a₀∀b₀∃a₁∀b₁…</span> evaluated bottom-up.', '对：对手的结点用 ∀，自己的结点用 ∃。这正是自下而上地计算交替量词 <span class="m">∃a₀∀b₀∃a₁∀b₁…</span>。']);
})();

/* ================= §9 infinite games ================= */
(function openGame() {
  const svg = $('opSvg');
  const b = 2, d = 5, W = 860;
  const yOf = k => 26 + k * 52;
  const xs = [];
  for (let k = d; k >= 0; k--) {
    xs[k] = [];
    for (let i = 0; i < Math.pow(b, k); i++) xs[k][i] = k === d ? 30 + i * ((W - 60) / 31) : (xs[k + 1][i * b] + xs[k + 1][i * b + 1]) / 2;
  }
  let targets = new Set(['2,1', '3,6', '4,12', '3,4', '4,9']), ranks = null;
  function render() {
    svg.innerHTML = '';
    const hitInfo = openRanks(targets, b, d).hit;
    for (let k = 0; k < d; k++) T(svg, 2, yOf(k) + 4, moverAt(k), { 'font-size': 11, 'font-weight': 800, fill: moverAt(k) === 'I' ? C.accent : C.gold });
    for (let k = 1; k <= d; k++) for (let i = 0; i < Math.pow(b, k); i++) {
      const p = Math.floor(i / b);
      el('line', { x1: xs[k - 1][p], y1: yOf(k - 1), x2: xs[k][i], y2: yOf(k), stroke: '#c9c4b6', 'stroke-width': 1.6 }, svg);
      T(svg, (xs[k - 1][p] + xs[k][i]) / 2 + (i % 2 ? 4 : -10), (yOf(k - 1) + yOf(k)) / 2, String(i % 2), { 'font-size': 9.5, fill: C.muted, class: 'm' });
    }
    for (let k = 0; k <= d; k++) for (let i = 0; i < Math.pow(b, k); i++) {
      const key = k + ',' + i, isT = targets.has(key), inT = hitInfo[k][i] && !isT;
      const r = k <= 2 ? 13 : k === 3 ? 11 : k === 4 ? 9.5 : 7.5;
      const g = el('g', { class: 'gnode', transform: `translate(${xs[k][i]},${yOf(k)})` }, svg);
      let fill = '#fff', stroke = '#9aa0aa', lab = '';
      if (isT) { fill = C.gold; stroke = '#8a5a00'; }
      else if (inT) { fill = C.goldSoft; stroke = C.gold; }
      if (ranks) {
        const rk = ranks[k][i];
        if (!isT && !inT) {
          if (rk === Infinity) { fill = C.falSoft; stroke = C.fal; lab = '∞'; }
          else { fill = C.truSoft; stroke = C.tru; lab = String(rk); }
        }
      }
      el('circle', { r, fill, stroke, 'stroke-width': 2 }, g);
      if (isT) T(g, 0, 4, '★', { 'text-anchor': 'middle', fill: '#fff', 'font-size': r });
      else if (lab) T(g, 0, 4, lab, { 'text-anchor': 'middle', 'font-size': Math.min(12, r + 1), 'font-weight': 800, fill: lab === '∞' ? C.fal : C.tru });
      if (k > 0) g.addEventListener('click', () => { targets.has(key) ? targets.delete(key) : targets.add(key); ranks = null; render(); clearBox($('opMsg')); });
    }
    T(svg, W - 6, 322, '★ target · 目标   number = moves I still needs · 数字 = I 还需的步数   ∞ = safe for II · II 的安全位置', { 'text-anchor': 'end', 'font-size': 11, fill: C.muted });
  }
  $('opRank').addEventListener('click', () => {
    ranks = openRanks(targets, b, d).rank;
    render();
    const r0 = ranks[0][0];
    okBox($('opMsg'), r0 === Infinity
      ? bi('The root is <b>safe for II</b> (∞). II wins by always moving to a red ∞ position, the Gale–Stewart strategy of Step 2 below. Every finite stage stays outside all targets, so the infinite play avoids the open set A.', '根结点对 II <b>安全</b>（∞）。II 只要始终走到红色 ∞ 位置就能获胜，这正是下面第 2 步的盖尔–斯图尔特策略。每个有限阶段都在目标之外，所以无穷对局避开了开集 A。')
      : bi(`The root has rank <b>${r0}</b>: I can force a target within ${r0} move${r0 === 1 ? '' : 's'}, so I wins. At I’s nodes the rank is 1 + min over children; at II’s nodes it is 1 + max. In the real game on ω, II may have infinitely many options, and then the ranks are countable ordinals (sup instead of max).`, `根结点的秩为 <b>${r0}</b>：I 能在 ${r0} 步内强迫命中目标，所以 I 获胜。在 I 的结点，秩 = 1 + 子结点的最小值；在 II 的结点，秩 = 1 + 最大值。在 ω 上真正的博弈中，II 可能有无穷多个选择，这时秩就是可数序数（用上确界代替最大值）。`), r0 === Infinity ? 'warn' : 'ok');
  });
  $('opRand').addEventListener('click', () => {
    targets = new Set();
    const n = 3 + Math.floor(Math.random() * 4);
    while (targets.size < n) { const k = 2 + Math.floor(Math.random() * 3); targets.add(k + ',' + Math.floor(Math.random() * Math.pow(2, k))); }
    ranks = null; render(); clearBox($('opMsg'));
  });
  render();
})();

(function adVsAc() {
  const svg = $('adSvg');
  const N = 6;
  let stage = 0;
  function render() {
    svg.innerHTML = '';
    T(svg, 8, 22, 'σ_α: strategies of I · I 的策略', { 'text-anchor': 'start', 'font-weight': 700, fill: C.accent, 'font-size': 12 });
    T(svg, 852, 22, 'τ_α: strategies of II · II 的策略', { 'text-anchor': 'end', 'font-weight': 700, fill: '#8a5a00', 'font-size': 12 });
    el('rect', { x: 170, y: 36, width: 520, height: 210, rx: 18, fill: '#f1efe7', stroke: '#b8b3a6' }, svg);
    T(svg, 430, 56, 'all plays ω^ω · 全部对局', { 'text-anchor': 'middle', fill: C.muted, 'font-size': 12 });
    el('ellipse', { cx: 330, cy: 150, rx: 130, ry: 80, fill: C.truSoft, stroke: C.tru, 'stroke-width': 2 }, svg);
    T(svg, 250, 92, 'A (I wins) · A（I 胜）', { fill: C.tru, 'font-weight': 700, 'font-size': 12 });
    T(svg, 580, 92, 'kept out of A · 留在 A 外', { 'text-anchor': 'middle', fill: C.fal, 'font-weight': 700, 'font-size': 12 });
    for (let a = 0; a < N; a++) {
      const y = 50 + a * 34, done = a < stage;
      const sub = '₀₁₂₃₄₅'[a];
      T(svg, 70, y + 12, `σ${sub}${done ? '  ✗' : ''}`, { 'text-anchor': 'middle', class: 'm', 'font-weight': 700, fill: done ? C.fal : C.accent, 'text-decoration': done ? 'line-through' : 'none' });
      T(svg, 790, y + 12, `τ${sub}${done ? '  ✗' : ''}`, { 'text-anchor': 'middle', class: 'm', 'font-weight': 700, fill: done ? C.fal : '#8a5a00', 'text-decoration': done ? 'line-through' : 'none' });
      if (done) {
        const xa = 270 + (a % 3) * 55, ya = 125 + Math.floor(a / 3) * 45;
        const xb = 520 + (a % 3) * 55, yb = 125 + Math.floor(a / 3) * 45;
        const l1 = el('line', { x1: 760, y1: y + 8, x2: xa + 6, y2: ya, stroke: C.gold, 'stroke-width': 1.2, 'stroke-dasharray': '4 3', class: 'fadein' }, svg);
        const l2 = el('line', { x1: 100, y1: y + 8, x2: xb - 6, y2: yb, stroke: C.accent, 'stroke-width': 1.2, 'stroke-dasharray': '4 3', class: 'fadein' }, svg);
        void l1; void l2;
        el('circle', { cx: xa, cy: ya, r: 8, fill: C.tru, class: a === stage - 1 ? 'pop' : '' }, svg);
        T(svg, xa, ya + 22, `x${sub}`, { 'text-anchor': 'middle', class: 'm', 'font-size': 12, fill: C.tru, 'font-weight': 700 });
        el('circle', { cx: xb, cy: yb, r: 8, fill: C.fal, class: a === stage - 1 ? 'pop' : '' }, svg);
        T(svg, xb, yb + 22, `y${sub}`, { 'text-anchor': 'middle', class: 'm', 'font-size': 12, fill: C.fal, 'font-weight': 700 });
      }
    }
    T(svg, 430, 268, stage < N ? `stage ${stage}: ${2 * stage} plays chosen so far (always < 2^ℵ₀) · 第 ${stage} 步：已选 ${2 * stage} 个对局（始终 < 2^ℵ₀）`
      : '… continue for all α < 2^ℵ₀: every strategy is defeated · 对所有 α < 2^ℵ₀ 继续：每个策略都被击败', { 'text-anchor': 'middle', 'font-size': 12.5, fill: stage < N ? C.ink : C.meta, 'font-weight': 700 });
    if (stage > 0 && stage <= N) {
      const a = stage - 1, sub = '₀₁₂₃₄₅'[a];
      T(svg, 430, 236, `x${sub} follows τ${sub} → put in A (τ${sub} loses);  y${sub} follows σ${sub} → keep out (σ${sub} loses)`, { 'text-anchor': 'middle', class: 'm', 'font-size': 11.5, fill: C.ink });
    }
  }
  $('adNext').addEventListener('click', () => { if (stage < N) stage++; render(); });
  $('adReset').addEventListener('click', () => { stage = 0; render(); });
  render();
  checkYourself('cy9', ['Where exactly does the proof that AD fails use the Axiom of Choice?', '“AD 不成立”的证明究竟在哪里用到了选择公理？'], [
    ['counting that there are 2<sup>ℵ₀</sup> strategies', '计数：策略共有 2<sup>ℵ₀</sup> 个', false, 'No: ℵ₀^ℵ₀ = 2^ℵ₀ holds in ZF (an explicit bijection).', '不是：ℵ₀^ℵ₀ = 2^ℵ₀ 在 ZF 中就成立（有显式双射）。'],
    ['well-ordering the strategies (and plays) in order type 2<sup>ℵ₀</sup>', '把策略（和对局）良序排成序型 2<sup>ℵ₀</sup>', true],
    ['the Gale–Stewart theorem', '盖尔–斯图尔特定理', false, 'Gale–Stewart is not used, and its proof needs no choice (take the least good move).', '没有用到盖尔–斯图尔特定理，而且它的证明也不需要选择（取最小的好着法即可）。'],
  ], ['Right. The diagonal recursion needs a well-ordering of the continuum, so that at every stage fewer than 2<sup>ℵ₀</sup> plays are used up. That is AC.', '对。对角线递归需要连续统的良序，才能保证每一步用掉的对局少于 2<sup>ℵ₀</sup> 个。这就是 AC。']);
})();

/* ================= §10 large cardinals ⇔ determinacy ================= */
(function lcDet() {
  const svg = $('ldSvg');
  const levels = [
    ['Borel = Δ¹₁', 'Borel'],
    ['Σ¹₁ / Π¹₁', 'P1'],
    ['Σ¹₂ / Π¹₂', 'P2'],
    ['Σ¹₃ / Π¹₃', 'P3'],
    ['Σ¹₄ / Π¹₄', 'P4'],
    ['⋮  all projective (PD)', 'PD'],
    ['all sets of reals in L(ℝ)', 'LR'],
  ];
  const hyps = [
    { en: 'ZFC alone', zh: '仅 ZFC', det: 1, reg: ['Borel'], info: ['ZFC proves Borel determinacy (Martin), but not <span class="m">Π¹₁</span>-determinacy: in L it fails. Regularity is provable for <span class="m">Σ¹₁</span> sets (L19), not for <span class="m">Σ¹₂</span>.', 'ZFC 能证明博雷尔决定性（马丁），但证不出 <span class="m">Π¹₁</span>-决定性：它在 L 中不成立。正则性对 <span class="m">Σ¹₁</span> 集可证（第 19 课），对 <span class="m">Σ¹₂</span> 集不可证。'] },
    { en: 'a measurable cardinal', zh: '一个可测基数', det: 2, reg: 'Σ¹₂', info: ['Martin: <span class="m">Π¹₁</span>-determinacy. (Exactly as strong as “<span class="m">x<sup>♯</sup></span> exists for every real x”.) Also every <span class="m">Σ¹₂</span> set is Lebesgue measurable, has the Baire property and the perfect set property.', '马丁：<span class="m">Π¹₁</span>-决定性。（其强度恰好等于“对每个实数 x，<span class="m">x<sup>♯</sup></span> 存在”。）此外每个 <span class="m">Σ¹₂</span> 集都勒贝格可测、具有贝尔性质和完美集性质。'] },
    { en: '1 Woodin + a measurable above', zh: '1 个伍丁 + 上方一个可测', det: 3, reg: 'Σ¹₃', info: ['Martin–Steel with n = 1: <span class="m">Π¹₂</span>-determinacy, hence (by unfolding the regularity games) every <span class="m">Σ¹₃</span> set is regular.', '马丁–斯蒂尔，n = 1：<span class="m">Π¹₂</span>-决定性；由此（把正则性博弈“展开”）每个 <span class="m">Σ¹₃</span> 集都是正则的。'] },
    { en: '2 Woodins + a measurable above', zh: '2 个伍丁 + 上方一个可测', det: 4, reg: 'Σ¹₄', info: ['n = 2: <span class="m">Π¹₃</span>-determinacy.', 'n = 2：<span class="m">Π¹₃</span>-决定性。'] },
    { en: '3 Woodins + a measurable above', zh: '3 个伍丁 + 上方一个可测', det: 5, reg: 'Σ¹₅', info: ['n = 3: <span class="m">Π¹₄</span>-determinacy (so Σ¹₅ sets are regular). One Woodin per level.', 'n = 3：<span class="m">Π¹₄</span>-决定性（因而 Σ¹₅ 集正则）。每层一个伍丁。'] },
    { en: 'infinitely many Woodins', zh: '无穷多个伍丁', det: 6, reg: 'proj', info: ['PD: every projective set is determined, hence every projective set is Lebesgue measurable, has the Baire property and the perfect set property (the answer to the questions left open in L19).', 'PD：每个投影集都是确定的，因此每个投影集都勒贝格可测、具有贝尔性质和完美集性质（这回答了第 19 课遗留的问题）。'] },
    { en: 'ω Woodins + a measurable above', zh: 'ω 个伍丁 + 上方一个可测', det: 7, reg: 'LR', info: ['Woodin: <span class="m">AD<sup>L(ℝ)</sup></span>. Every set of reals in L(ℝ) is determined and regular. Meanwhile V still satisfies AC.', '伍丁：<span class="m">AD<sup>L(ℝ)</sup></span>。L(ℝ) 中每个实数集都是确定且正则的。与此同时 V 仍满足 AC。'] },
  ];
  function draw(h) {
    svg.innerHTML = '';
    const H = hyps[h];
    T(svg, 160, 22, 'determined · 确定的', { 'text-anchor': 'middle', 'font-weight': 700, fill: C.tru });
    T(svg, 620, 22, 'regular (LM, BP, PSP) · 正则', { 'text-anchor': 'middle', 'font-weight': 700, fill: C.accent });
    const regLit = i => i <= 1 || (i <= 4 && h >= i - 1) || (i === 5 && h >= 5) || (i === 6 && h === 6);
    const regLab = ['Borel', 'Σ¹₁', 'Σ¹₂', 'Σ¹₃', 'Σ¹₄', '⋮  all projective', 'all sets of reals in L(ℝ)'];
    levels.forEach((lv, i) => {
      const y = 318 - i * 46, lit = i < H.det, rl = regLit(i);
      const g = el('g', {}, svg);
      el('rect', { x: 40, y, width: 240, height: 36, rx: 8, fill: lit ? C.truSoft : '#f1efe7', stroke: lit ? C.tru : '#c9c4b6', 'stroke-width': lit ? 2.5 : 1.5 }, g);
      T(g, 160, y + 23, lv[0], { 'text-anchor': 'middle', 'font-size': 13.5, 'font-weight': lit ? 800 : 500, fill: lit ? '#1b5e20' : C.muted });
      el('rect', { x: 500, y, width: 240, height: 36, rx: 8, fill: rl ? C.accentSoft : '#f1efe7', stroke: rl ? C.accent : '#c9c4b6', 'stroke-width': rl ? 2.5 : 1.5 }, g);
      T(g, 620, y + 23, regLab[i], { 'text-anchor': 'middle', 'font-size': 13.5, 'font-weight': rl ? 800 : 500, fill: rl ? '#23336e' : C.muted });
      // Π¹ₙ-Det ⇒ Σ¹ₙ₊₁ regular (one row up); PD ⇒ projective; AD^L(ℝ) ⇒ L(ℝ)
      if (lit && ((i >= 1 && i <= 3) || i >= 5)) {
        const up = i <= 3 ? 46 : 0;
        el('path', { d: `M 284 ${y + 18} L 496 ${y + 18 - up}`, stroke: C.accent, 'stroke-width': 1.4, 'stroke-dasharray': '4 3', fill: 'none', opacity: 0.6 }, g);
      }
    });
    T(svg, 390, 372, 'arrows: Π¹ₙ-Det ⇒ Σ¹ₙ₊₁ regular · 箭头：Π¹ₙ-决定性 ⇒ Σ¹ₙ₊₁ 正则', { 'text-anchor': 'middle', 'font-size': 11.5, fill: C.muted });
    $('ldName').innerHTML = bil(H.en, H.zh);
    okBox($('ldInfo'), bi(H.info[0], H.info[1]), 'info');
  }
  $('ldSlider').addEventListener('input', e => draw(+e.target.value));
  draw(0);
  checkYourself('cy10', ['With 2 Woodin cardinals and a measurable above them, which class is (at least) determined?', '有 2 个伍丁基数，上方还有一个可测基数时，（至少）哪个类是确定的？'], [
    ['Π¹₂', 'Π¹₂', false, 'That needs only one Woodin (plus a measurable above). Two give one more level.', '这只需一个伍丁（加上方的可测）。两个能再多一层。'],
    ['Π¹₃', 'Π¹₃', true],
    ['all projective sets', '全部投影集', false, 'That needs infinitely many Woodins (or, for consistency, n Woodins for every n).', '那需要无穷多个伍丁（若只谈一致性，则需对每个 n 都有 n 个伍丁）。'],
  ], ['Right: n Woodins + measurable above ⇒ Π¹ₙ₊₁-determinacy (Martin–Steel), here n = 2.', '对：n 个伍丁 + 上方可测 ⇒ Π¹ₙ₊₁-决定性（马丁–斯蒂尔），这里 n = 2。']);
})();

/* ================= §11 outlook ================= */
(function outlook() {
  const cards = [
    ['Inner model program', '内模型纲领', 'open', 'Goal: for each large cardinal, an L-like canonical inner model (a “mouse”) with fine structure, comparison and iterability. Achieved well beyond Woodin cardinals (Mitchell, Steel, Neeman, …). For a supercompact cardinal no such model is known.', '目标：为每个大基数构造一个类似 L 的典范内模型（“鼠”），具备精细结构、可比较性与可迭代性。已在伍丁基数之上很远处实现（米切尔、斯蒂尔、尼曼等）。对超紧基数，尚无此类模型。'],
    ['Ultimate L', '终极 L', 'open', 'Woodin’s conjecture: there is an L-like inner model (“Ultimate L”) that can accommodate a supercompact, hence (by his results) all known large cardinals. The axiom “V = Ultimate L” would settle CH. Status: a precise conjecture, unproved.', '伍丁的猜想：存在一个类似 L、能容纳超紧基数（由他的结果，进而容纳所有已知大基数）的内模型（“终极 L”）。公理“V = 终极 L”将判定 CH。现状：已精确表述，尚未证明。'],
    ['HOD Conjecture', 'HOD 猜想', 'open', 'Proved (Woodin’s HOD Dichotomy): if δ is extendible, then above δ HOD is either very close to V (it computes successors of singular cardinals correctly) or very far (every regular cardinal &gt; δ is ω-strongly measurable in HOD). The HOD Conjecture says the “far” side never happens. Open. (L22)', '已证（伍丁 HOD 二分定理）：若 δ 是可扩基数，则在 δ 之上 HOD 要么非常接近 V（能正确计算奇异基数的后继），要么非常远离 V（每个大于 δ 的正则基数在 HOD 中都是 ω-强可测的）。HOD 猜想断言“远离”的情形不会发生。未解决。（第 22 课）'],
    ['Ω-conjecture', 'Ω 猜想', 'open', 'Woodin’s Ω-logic: a statement is Ω-valid if it holds in every V_α that satisfies ZFC, in every forcing extension. The Ω-conjecture says Ω-validity coincides with Ω-provability (proofs certified by universally Baire sets), in the presence of a proper class of Woodin cardinals. Open.', '伍丁的 Ω 逻辑：若一个命题在每个力迫扩张中、每个满足 ZFC 的 V_α 里都成立，则称它 Ω-有效。Ω 猜想断言（在存在真类多个伍丁基数时）Ω-有效与 Ω-可证（由普遍贝尔集验证的证明）一致。未解决。'],
    ['Strongly compact vs supercompact', '强紧与超紧', 'open', 'Are they equiconsistent? Widely suspected, unproved; a proof seems to need inner models for supercompacts.', '两者等一致吗？普遍猜测如此，尚未证明；证明似乎需要超紧基数的内模型。'],
    ['Choiceless cardinals', '无选择的大基数', 'open', 'Is ZF + a Reinhardt (or Berkeley) cardinal consistent? Open. If so, AC is what stands between ZF and Kunen’s wall. Woodin and others have argued both directions; there is no consensus.', 'ZF + 莱因哈特（或伯克利）基数一致吗？未解决。若一致，挡在 ZF 与库能之墙之间的就是 AC。伍丁等人对两个方向都有论证，尚无共识。'],
  ];
  const box = $('outCards');
  cards.forEach(c => {
    const d = document.createElement('div');
    d.className = 'ocard';
    d.innerHTML = `<span class="status st-open">${bil('open', '未解决')}</span> <b>${bil(c[0], c[1])}</b><div class="more">${bi(c[3], c[4])}</div><div class="muted" style="font-size:12px;margin-top:4px">${bil('click to expand', '点击展开')}</div>`;
    d.addEventListener('click', () => d.classList.toggle('open'));
    box.appendChild(d);
  });
  checkYourself('cy11', ['The HOD Conjecture is…', 'HOD 猜想是……'], [
    ['a theorem of Woodin', '伍丁证明的定理', false, 'Woodin proved the HOD <i>Dichotomy</i> theorem. The <i>Conjecture</i> (that the “far” side does not occur) is open.', '伍丁证明的是 HOD <i>二分定理</i>。<i>猜想</i>（“远离”情形不发生）尚未解决。'],
    ['open', '尚未解决', true],
    ['refuted by Kunen’s theorem', '已被库能定理否证', false],
  ], ['Right. See Lesson 27 for the full story.', '对。完整故事见第 27 课。']);
})();

/* ================= E1 ordering ================= */
(function e1() {
  const correct = [
    ['inaccessible', '不可达基数'], ['measurable', '可测基数'], ['strong', '强基数'], ['Woodin', '伍丁基数'],
    ['supercompact', '超紧基数'], ['extendible', '可扩基数'], ['huge', '巨大基数'], ['I3', 'I3'], ['I0', 'I0'],
  ];
  let order = shuffle(correct.map((_, i) => i)), revealed = false;
  const list = $('e1List');
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
        render(); clearBox($('e1Msg'));
      }));
      list.appendChild(d);
    });
  }
  render();
  $('e1Check').addEventListener('click', () => {
    const marks = order.map((ci, pos) => ci === pos);
    render(marks);
    const n = marks.filter(Boolean).length;
    if (n === order.length) {
      if (revealed) { okBox($('e1Msg'), bi('Correct order, but the answer was shown earlier in this session, so it is not counted. Reload the page to try again from scratch.', '顺序正确，但本次访问中已经看过答案，所以不计分。刷新页面后可重新作答。'), 'info'); return; }
      okBox($('e1Msg'), bi('✓ Perfect. Notice that “huge” sits above “supercompact” in strength although the least huge cardinal is smaller than the least supercompact.', '✓ 完全正确。注意“巨大”在强度上高于“超紧”，尽管最小巨大基数小于最小超紧基数。'));
      Progress.mark('L25E1');
    } else okBox($('e1Msg'), bi(`${n} / ${order.length} in the right place (green). Hint: Woodin sits between strong and supercompact; the rank-into-rank axioms are at the very top.`, `${n} / ${order.length} 个位置正确（绿色）。提示：伍丁介于强与超紧之间；秩入秩公理在最顶端。`), 'warn');
  });
  $('e1Shuffle').addEventListener('click', () => { order = shuffle(order); render(); clearBox($('e1Msg')); });
  $('e1Show').addEventListener('click', () => { order = correct.map((_, i) => i); revealed = true; render(order.map(() => true)); okBox($('e1Msg'), bi('Answer: inaccessible < measurable < strong < Woodin < supercompact < extendible < huge < I3 < I0.', '答案：不可达 < 可测 < 强 < 伍丁 < 超紧 < 可扩 < 巨大 < I3 < I0。'), 'info'); });
})();

/* ================= E2 backward induction by hand ================= */
(function e2() {
  const b = 2, d = 4;
  const solvedPatterns = new Set();
  let G, answer, revealed = false, everRevealed = false;
  function fresh() {
    revealed = false;
    let leaves;
    do leaves = Array.from({ length: 16 }, () => Math.random() < 0.5 ? 'I' : 'II'); while (solvedPatterns.has(leaves.join()));
    answer = solveGame(leaves, b, d);
    G = GameTree($('e2Svg'), {
      leaves,
      onInner: (k, i) => {
        const cur = G.user[k][i];
        G.user[k][i] = cur === '' ? 'I' : cur === 'I' ? 'II' : '';
        G.marks = null;
        G.render();
      },
    });
    G.user = answer.map((row, k) => k === d ? row : row.map(() => ''));
    G.render();
    clearBox($('e2Msg'));
  }
  function count() { $('e2Count').innerHTML = bil(`solved: ${Math.min(solvedPatterns.size, 2)} / 2`, `已解出：${Math.min(solvedPatterns.size, 2)} / 2`); }
  fresh(); count();
  $('e2Check').addEventListener('click', () => {
    let wrong = 0, blank = 0;
    G.marks = {};
    for (let k = 0; k < d; k++) for (let i = 0; i < Math.pow(b, k); i++) {
      const u = G.user[k][i];
      if (!u) { blank++; continue; }
      if (u !== answer[k][i]) { wrong++; G.marks[k + ',' + i] = false; }
    }
    G.render();
    if (!wrong && !blank && revealed) { okBox($('e2Msg'), bi('That is the revealed answer (not counted). Press “New game”.', '这是显示出来的答案（不计分）。点“换一局”。'), 'info'); return; }
    if (!wrong && !blank) {
      solvedPatterns.add(G.leaves.join());
      count();
      okBox($('e2Msg'), bi(`✓ All 15 labels correct. Player ${answer[0][0]} wins.${solvedPatterns.size < 2 ? ' Press “New game” for one more.' : ''}`, `✓ 15 个标注全对。玩家 ${answer[0][0]} 获胜。${solvedPatterns.size < 2 ? '点“换一局”再来一局。' : ''}`));
      if (solvedPatterns.size >= 2 && !everRevealed) Progress.mark('L25E2');
      else if (everRevealed) okBox($('e2Msg'), bi(`✓ All 15 labels correct. (An answer was shown earlier in this session, so the exercise is not marked as solved; reload the page to start fresh.)`, `✓ 15 个标注全对。（本次访问中曾看过答案，所以本题不记为完成；刷新页面可重新开始。）`), 'info');
    } else okBox($('e2Msg'), bi(`${wrong} wrong (red ring), ${blank} still blank. Work from the bottom row upwards.`, `${wrong} 个错误（红圈），${blank} 个未填。从最下面一行往上做。`), 'bad');
  });
  $('e2New').addEventListener('click', fresh);
  $('e2Show').addEventListener('click', () => {
    revealed = true; everRevealed = true;
    G.user = answer.map(r => r.slice());
    G.marks = null;
    G.win = strategyEdges(answer, b, d);
    G.render();
    okBox($('e2Msg'), bi(`Answer shown (not counted). Player ${answer[0][0]} wins; purple edges are a winning strategy.`, `已显示答案（不计分）。玩家 ${answer[0][0]} 获胜；紫色边是一个获胜策略。`), 'info');
  });
})();

/* ================= E3 true/false ================= */
(function e3() {
  const items = [
    ['Every finite two-player game of perfect information without draws is determined.', '每个无平局、完全信息的有限二人博弈都是确定的。', true, 'True: Zermelo / backward induction (§8).', '对：策梅洛定理 / 逆向归纳（§8）。'],
    ['AD is consistent with ZFC (assuming large cardinals).', '（假定大基数）AD 与 ZFC 一致。', false, 'False: ZFC ⊢ ¬AD by the diagonal construction of §9. What is consistent with ZFC is AD<sup>L(ℝ)</sup>.', '错：由 §9 的对角线构造，ZFC ⊢ ¬AD。与 ZFC 相容的是 AD<sup>L(ℝ)</sup>。'],
    ['ZFC proves that every open game on ω is determined.', 'ZFC 能证明 ω 上的每个开博弈都是确定的。', true, 'True: Gale–Stewart (1953).', '对：盖尔–斯图尔特（1953）。'],
    ['Under AD (in ZF), every set of reals is Lebesgue measurable.', '在 AD 下（ZF 中），每个实数集都勒贝格可测。', true, 'True: Mycielski–Świerczkowski.', '对：梅齐尔斯基–希维尔奇科夫斯基。'],
    ['ZFC proves projective determinacy.', 'ZFC 能证明投影决定性。', false, 'False (if ZFC is consistent): in L there is a non-determined Π¹₁ set.', '错（若 ZFC 一致）：L 中存在不确定的 Π¹₁ 集。'],
    ['If there is a measurable cardinal, then every analytic (Σ¹₁) game is determined.', '若存在可测基数，则每个解析（Σ¹₁）博弈都是确定的。', true, 'True: Martin (1970).', '对：马丁（1970）。'],
    ['Borel determinacy can be proved in Zermelo set theory (no Replacement).', '博雷尔决定性能在策梅洛集合论（无替换公理）中证明。', false, 'False: Friedman showed Replacement (many iterations of the power set) is genuinely needed.', '错：弗里德曼证明了确实需要替换公理（多次迭代幂集）。'],
    ['Woodin: Con(ZF + AD) ⇔ Con(ZFC + infinitely many Woodin cardinals).', '伍丁：Con(ZF + AD) ⇔ Con(ZFC + 无穷多个伍丁基数)。', true, 'True: an equiconsistency theorem.', '对：这是一个等一致性定理。'],
  ];
  const solved = items.map(() => false), shown = items.map(() => false);
  const box = $('e3List');
  items.forEach((it, i) => {
    const row = document.createElement('div');
    row.className = 'tf';
    row.innerHTML = `<div class="stmt" style="font-family:var(--sans);font-size:15px">${bi(it[0], it[1])}</div>
      <button class="btn small" data-v="1">${bil('True', '对')}</button>
      <button class="btn small" data-v="0">${bil('False', '错')}</button>
      <button class="btn small ghost" data-v="s">${bil('Show answer', '看答案')}</button>
      <div style="flex-basis:100%"><div class="msg"></div></div>`;
    box.appendChild(row);
    row.querySelectorAll('button').forEach(bt => bt.addEventListener('click', () => {
      const msg = row.querySelector('.msg');
      if (bt.dataset.v === 's') { shown[i] = true; okBox(msg, bi(it[3], it[4]), 'info'); return; }
      if ((bt.dataset.v === '1') === it[2]) {
        okBox(msg, '✓ ' + bi(it[3], it[4]));
        if (!shown[i]) solved[i] = true;
        if (solved.every(Boolean)) Progress.mark('L25E3');
      } else okBox(msg, bi('✗ Not quite. Check §8–§10.', '✗ 不对。回看 §8–§10。'), 'bad');
    }));
  });
})();

/* ================= E4 AD vs AC ordering ================= */
(function e4() {
  const steps = [
    ['Count: each player has exactly 2<sup>ℵ₀</sup> strategies.', '计数：每位玩家恰有 2<sup>ℵ₀</sup> 个策略。'],
    ['Use AC to list them as ⟨σ<sub>α</sub>⟩ and ⟨τ<sub>α</sub>⟩, α < 2<sup>ℵ₀</sup> (2<sup>ℵ₀</sup> an initial ordinal).', '用 AC 把它们排成 ⟨σ<sub>α</sub>⟩ 与 ⟨τ<sub>α</sub>⟩，α < 2<sup>ℵ₀</sup>（2<sup>ℵ₀</sup> 取初始序数）。'],
    ['At stage α fewer than 2<sup>ℵ₀</sup> plays have been used, while 2<sup>ℵ₀</sup> plays follow τ<sub>α</sub> and 2<sup>ℵ₀</sup> plays follow σ<sub>α</sub>.', '第 α 步时用掉的对局少于 2<sup>ℵ₀</sup> 个，而遵循 τ<sub>α</sub> 的对局与遵循 σ<sub>α</sub> 的对局各有 2<sup>ℵ₀</sup> 个。'],
    ['Pick a fresh x<sub>α</sub> following τ<sub>α</sub> and put it into A; pick a fresh y<sub>α</sub> following σ<sub>α</sub> and keep it out of A.', '挑一个新的、遵循 τ<sub>α</sub> 的 x<sub>α</sub> 放进 A；挑一个新的、遵循 σ<sub>α</sub> 的 y<sub>α</sub> 留在 A 外。'],
    ['Each τ<sub>α</sub> loses on x<sub>α</sub> ∈ A and each σ<sub>α</sub> loses on y<sub>α</sub> ∉ A, so G<sub>A</sub> is not determined.', '每个 τ<sub>α</sub> 在 x<sub>α</sub> ∈ A 上输，每个 σ<sub>α</sub> 在 y<sub>α</sub> ∉ A 上输，所以 G<sub>A</sub> 不是确定的。'],
  ];
  let seq = [], revealed = false;
  const pool = $('e4Pool'), ol = $('e4Seq');
  const perm = shuffle(steps.map((_, i) => i));
  function render(marks) {
    pool.innerHTML = '';
    perm.forEach(i => {
      const c = document.createElement('div');
      c.className = 'chip' + (seq.includes(i) ? ' used' : '');
      c.innerHTML = bi(steps[i][0], steps[i][1]);
      c.addEventListener('click', () => { if (!seq.includes(i)) { seq.push(i); render(); clearBox($('e4Msg')); } });
      pool.appendChild(c);
    });
    ol.innerHTML = seq.map((i, p) => `<li class="fadein" style="${marks ? `color:${marks[p] ? 'var(--true)' : 'var(--false)'}` : ''}">${bi(steps[i][0], steps[i][1])}</li>`).join('');
  }
  render();
  $('e4Check').addEventListener('click', () => {
    if (seq.length < steps.length) { okBox($('e4Msg'), bi('Place all five steps first.', '先把五步都排好。'), 'warn'); return; }
    const marks = seq.map((i, p) => i === p);
    render(marks);
    if (marks.every(Boolean) && revealed) { okBox($('e4Msg'), bi('Correct order, but the answer was shown earlier in this session, so it is not counted. Reload the page to try again from scratch.', '顺序正确，但本次访问中已经看过答案，所以不计分。刷新页面后可重新作答。'), 'info'); return; }
    if (marks.every(Boolean)) {
      okBox($('e4Msg'), bi('✓ Correct. This is Cantor’s diagonal method again: every strategy gets its own stage at which it is defeated.', '✓ 正确。这又是康托尔对角线法：每个策略都有属于自己的一步，并在那一步被击败。'));
      Progress.mark('L25E4');
    } else okBox($('e4Msg'), bi('Some steps are out of order (red). Ask: what must be known before each step can be carried out?', '有几步顺序不对（红色）。想一想：每一步执行之前必须先知道什么？'), 'bad');
  });
  $('e4Reset').addEventListener('click', () => { seq = []; render(); clearBox($('e4Msg')); });
  $('e4Show').addEventListener('click', () => { seq = steps.map((_, i) => i); revealed = true; render(seq.map(() => true)); okBox($('e4Msg'), bi('Answer shown (not counted).', '已显示答案（不计分）。'), 'info'); });
})();

/* ================= E5 matching ================= */
(function e5() {
  const names = [
    ['measurable', '可测'], ['λ-strong', 'λ-强'], ['strong', '强'], ['superstrong', '超强'], ['λ-supercompact', 'λ-超紧'],
    ['huge', '巨大'], ['extendible', '可扩'], ['I3', 'I3'], ['Reinhardt (refuted in ZFC)', '莱因哈特（ZFC 中被否证）'],
  ];
  const rows = [
    ['<sup>κ</sup>M ⊆ M', 0],
    ['j(κ) &gt; λ and V<sub>λ</sub> ⊆ M', 1],
    ['for every λ, some j with j(κ) &gt; λ, V<sub>λ</sub> ⊆ M', 2],
    ['V<sub>j(κ)</sub> ⊆ M', 3],
    ['j(κ) &gt; λ and <sup>λ</sup>M ⊆ M', 4],
    ['<sup>j(κ)</sup>M ⊆ M', 5],
    ['for every η &gt; 0, some j : V<sub>κ+η</sub> → V<sub>ζ</sub> with crit κ', 6],
    ['nontrivial j : V<sub>λ</sub> → V<sub>λ</sub> (a set map)', 7],
    ['nontrivial j : V → V', 8],
  ];
  const box = $('e5List');
  let revealed = false;
  const sels = rows.map(r => {
    const d = document.createElement('div');
    d.className = 'matchrow';
    const opts = shuffle(names.map((_, i) => i)).map(i => `<option value="${i}">${names[i][0]} · ${names[i][1]}</option>`).join('');
    d.innerHTML = `<div class="cond">${r[0]}</div><select><option value="">— ${'choose · 选择'} —</option>${opts}</select>`;
    box.appendChild(d);
    const s = d.querySelector('select');
    s.addEventListener('change', () => { s.classList.remove('right', 'wrong'); clearBox($('e5Msg')); });
    return s;
  });
  $('e5Check').addEventListener('click', () => {
    let ok = 0;
    sels.forEach((s, i) => {
      s.classList.remove('right', 'wrong');
      if (s.value === '') return;
      if (+s.value === rows[i][1]) { ok++; s.classList.add('right'); } else s.classList.add('wrong');
    });
    if (ok === rows.length && revealed) { okBox($('e5Msg'), bi('All matched, but the answer was shown earlier in this session, so it is not counted. Reload the page to try again from scratch.', '全部正确，但本次访问中已经看过答案，所以不计分。刷新页面后可重新作答。'), 'info'); return; }
    if (ok === rows.length) {
      okBox($('e5Msg'), bi('✓ All matched. Read the column top to bottom: M swallows more and more of V until M = V.', '✓ 全部配对正确。从上往下读：M 吞下越来越多的 V，直到 M = V。'));
      Progress.mark('L25E5');
    } else okBox($('e5Msg'), bi(`${ok} / ${rows.length} correct.`, `${ok} / ${rows.length} 正确。`), 'warn');
  });
  $('e5Show').addEventListener('click', () => {
    revealed = true;
    sels.forEach((s, i) => { s.value = String(rows[i][1]); s.classList.remove('wrong'); s.classList.add('right'); });
    okBox($('e5Msg'), bi('Answer shown (not counted).', '已显示答案（不计分）。'), 'info');
  });
})();

/* ================= E6 status classification ================= */
(function e6() {
  const cats = [['thm', 'proved theorem', '已证定理'], ['ind', 'independent of ZFC', '独立于 ZFC'], ['ref', 'refutable in ZFC', 'ZFC 中可否证'], ['open', 'open problem', '未解决问题']];
  const items = [
    ['Every Borel game on ω is determined.', 'ω 上每个博雷尔博弈都是确定的。', 'thm', 'Martin, in ZFC.', '马丁，在 ZFC 中。'],
    ['Every analytic game on ω is determined.', 'ω 上每个解析博弈都是确定的。', 'ind', 'Fails in L; follows from a measurable.', '在 L 中不成立；由可测基数推出。'],
    ['There is a nontrivial elementary j : V<sub>λ+2</sub> → V<sub>λ+2</sub>.', '存在非平凡初等嵌入 j : V<sub>λ+2</sub> → V<sub>λ+2</sub>。', 'ref', 'Kunen.', '库能。'],
    ['There is a measurable cardinal.', '存在可测基数。', 'ind', 'Unprovable (Gödel II); not refutable if it is consistent.', '不可证（哥德尔第二定理）；若一致则不可否证。'],
    ['ZF + “there is a Reinhardt cardinal” is consistent.', 'ZF +“存在莱因哈特基数”是一致的。', 'open', 'Nobody knows.', '尚无人知道。'],
    ['Con(ZFC + strongly compact) ⇒ Con(ZFC + supercompact).', 'Con(ZFC + 强紧) ⇒ Con(ZFC + 超紧)。', 'open', 'Open.', '未解决。'],
    ['Con(ZF + AD) ⇔ Con(ZFC + infinitely many Woodin cardinals).', 'Con(ZF + AD) ⇔ Con(ZFC + 无穷多个伍丁基数)。', 'thm', 'Woodin.', '伍丁。'],
    ['The full axiom of determinacy AD.', '完整的决定性公理 AD。', 'ref', 'Diagonal argument with AC (§9).', '借助 AC 的对角线论证（§9）。'],
    ['The HOD Conjecture.', 'HOD 猜想。', 'open', 'Open (the Dichotomy is the theorem).', '未解决（二分定理才是已证定理）。'],
    ['Every supercompact cardinal is strongly compact.', '每个超紧基数都是强紧的。', 'thm', 'Normal fine ⇒ fine.', '正规精细 ⇒ 精细。'],
  ];
  const box = $('e6List');
  let revealed = false;
  const sels = items.map(it => {
    const d = document.createElement('div');
    d.className = 'matchrow';
    d.innerHTML = `<div class="cond" style="font-family:var(--sans)">${bi(it[0], it[1])}</div><select><option value="">— choose · 选择 —</option>${cats.map(c => `<option value="${c[0]}">${c[1]} · ${c[2]}</option>`).join('')}</select><div class="muted why" style="flex-basis:100%;font-size:13px"></div>`;
    box.appendChild(d);
    const s = d.querySelector('select');
    s.addEventListener('change', () => { s.classList.remove('right', 'wrong'); d.querySelector('.why').innerHTML = ''; });
    return s;
  });
  function check(show) {
    let ok = 0;
    sels.forEach((s, i) => {
      if (show) s.value = items[i][2];
      s.classList.remove('right', 'wrong');
      const why = s.parentNode.querySelector('.why');
      why.innerHTML = '';
      if (s.value === '') return;
      if (s.value === items[i][2]) { ok++; s.classList.add('right'); why.innerHTML = bil(items[i][3], items[i][4]); } else s.classList.add('wrong');
    });
    if (show) { revealed = true; okBox($('e6Msg'), bi('Answer shown (not counted).', '已显示答案（不计分）。'), 'info'); return; }
    if (ok === items.length && revealed) { okBox($('e6Msg'), bi('All correct, but the answer was shown earlier in this session, so it is not counted. Reload the page to try again from scratch.', '全对，但本次访问中已经看过答案，所以不计分。刷新页面后可重新作答。'), 'info'); return; }
    if (ok === items.length) {
      okBox($('e6Msg'), bi('✓ All correct. Keeping these four statuses apart is the single most important habit in this subject.', '✓ 全对。把这四种状态分清楚，是这门学科里最重要的习惯。'));
      Progress.mark('L25E6');
    } else okBox($('e6Msg'), bi(`${ok} / ${items.length} correct.`, `${ok} / ${items.length} 正确。`), 'warn');
  }
  $('e6Check').addEventListener('click', () => check(false));
  $('e6Show').addEventListener('click', () => check(true));
})();

/* ================= Atlas ================= */
(function atlas() {
  const svg = $('atSvg');
  const parts = [
    { col: '#3b5bdb', en: 'I · Logic', zh: '逻辑', ls: [1, 2, 3, 4, 5] },
    { col: '#2f9e44', en: 'II · Sets', zh: '集合', ls: [6, 7, 8, 9, 10] },
    { col: '#f08c00', en: 'III · Limits', zh: '极限', ls: [11, 12, 13] },
    { col: '#ae3ec9', en: 'IV · Independence', zh: '独立性', ls: [14, 15, 16] },
    { col: '#c2255c', en: 'V · Hierarchies', zh: '层级', ls: [17, 18, 19, 20, 21, 22, 23, 24, 25] },
  ];
  const L = {
    1: ['Propositional logic', '命题逻辑', 'formula depth', '公式深度'],
    2: ['Proofs & compactness', '证明与紧致性', '⊢ = ⊨', '⊢ = ⊨'],
    3: ['First-order logic', '一阶逻辑', 'quantifier alternation', '量词交替'],
    4: ['Gödel completeness', '哥德尔完备性', 'syntax ↔ models', '语法 ↔ 模型'],
    5: ['Compactness & LS', '紧致性与 LS', 'sizes of models', '模型的大小'],
    6: ['ZF axioms', 'ZF 公理', 'axioms as closure', '公理即封闭性'],
    7: ['ℕ, ℤ, ℚ, ℝ from sets', '构造数系', 'number systems', '数系'],
    8: ['Ordinals', '序数', 'well-orders', '良序'],
    9: ['Cardinals', '基数', 'ℵ hierarchy', 'ℵ 层级'],
    10: ['Axiom of Choice', '选择公理', 'AC vs AD', 'AC 对 AD'],
    11: ['Computability', '可计算性', 'halting', '停机'],
    12: ['Incompleteness', '不完全性', 'Con(T)', 'Con(T)'],
    13: ['Tarski', '塔斯基', 'truth hierarchy', '真的层级'],
    14: ['Models of ZFC & V', 'ZFC 模型与 V', 'V_α', 'V_α'],
    15: ['Constructible L', '可构成宇宙 L', 'L_α', 'L_α'],
    16: ['Forcing', '力迫法', 'independence', '独立性'],
    17: ['Arithmetical hierarchy', '算术层级', 'Σ⁰ₙ, Turing degrees', 'Σ⁰ₙ、图灵度'],
    18: ['Analytical hierarchy', '分析层级', 'Σ¹ₙ, ω₁^CK', 'Σ¹ₙ、ω₁^CK'],
    19: ['Borel & projective', '博雷尔与投影', 'Σ⁰_α, Σ¹ₙ on ℝ', 'ℝ 上的 Σ⁰_α、Σ¹ₙ'],
    20: ['Lévy hierarchy', '列维层级', 'Σₙ, absoluteness', 'Σₙ、绝对性'],
    21: ['Ordinal notations', '序数记号', 'ε₀, Γ₀, f_α', 'ε₀、Γ₀、f_α'],
    22: ['OD & HOD', 'OD 与 HOD', 'L ⊆ HOD ⊆ V', 'L ⊆ HOD ⊆ V'],
    23: ['Large cardinals I', '大基数（一）', 'Mahlo, weakly compact', '马洛、弱紧'],
    24: ['Large cardinals II', '大基数（二）', 'j : V → M', 'j : V → M'],
    25: ['Large cardinals III', '大基数（三）', 'Woodin…I0, AD', '伍丁…I0、AD'],
  };
  const E = [
    [1, 2, 'soundness & completeness for propositions', '命题的可靠性与完备性'], [3, 4, 'proofs for quantifiers', '量词的证明'], [2, 5, 'compactness lifts to first order', '紧致性推广到一阶'], [4, 5, '', ''],
    [4, 12, 'complete yet incomplete: different senses', '完备却不完全：两种含义'], [6, 7, '', ''], [7, 8, '', ''], [8, 9, '', ''], [9, 10, '', ''],
    [11, 12, 'computability powers Gödel', '可计算性驱动哥德尔定理'], [12, 13, 'diagonal lemma', '对角引理'], [11, 17, 'halting = Σ⁰₁-complete', '停机问题是 Σ⁰₁-完全的'],
    [17, 18, 'number quantifiers → set quantifiers', '数量词 → 集合量词'], [18, 19, 'lightface ↔ boldface', '细体 ↔ 黑体'], [18, 21, 'ω₁^CK bounds recursive notations', 'ω₁^CK 限制递归记号'],
    [8, 21, 'ordinals get names', '给序数起名字'], [13, 20, 'Σₙ-truth is definable, full truth is not', 'Σₙ-真可定义，全真不可定义'], [14, 20, 'absoluteness between models', '模型之间的绝对性'],
    [14, 15, 'V_α vs L_α', 'V_α 对 L_α'], [15, 16, 'L satisfies GCH; forcing breaks it', 'L 满足 GCH；力迫法打破它'], [15, 22, 'L ⊆ HOD', 'L ⊆ HOD'], [20, 22, 'reflection defines OD', '反射原理定义 OD'],
    [9, 23, 'cardinals beyond ZFC', '超出 ZFC 的基数'], [23, 24, 'from combinatorics to embeddings', '从组合到嵌入'], [24, 25, 'make M closer to V', '让 M 更接近 V'],
    [15, 24, 'measurable ⇒ V ≠ L', '可测 ⇒ V ≠ L'], [12, 25, 'consistency strength ladder', '一致性强度阶梯'], [19, 25, 'Woodins ⇒ projective determinacy & regularity', '伍丁 ⇒ 投影决定性与正则性'],
    [10, 25, 'AD contradicts AC', 'AD 与 AC 矛盾'], [16, 25, 'Magidor; independence of PD-level statements', '马吉多尔；PD 层次命题的独立性'], [22, 25, 'HOD Conjecture', 'HOD 猜想'],
  ];
  const pos = {};
  const colX = [16, 196, 376, 556, 736], BW = 156, BH = 50;
  parts.forEach((p, ci) => {
    const n = p.ls.length, gap = ci === 4 ? 61 : 80;
    p.ls.forEach((l, k) => { pos[l] = { x: colX[ci], y: 50 + k * gap, col: p.col }; });
  });
  let selN = null;
  const edgeEls = [], nodeEls = {};
  function render() {
    svg.innerHTML = '';
    parts.forEach((p, ci) => {
      T(svg, colX[ci] + BW / 2, 18, p.en, { 'text-anchor': 'middle', 'font-weight': 800, fill: p.col, 'font-size': 12.5 });
      T(svg, colX[ci] + BW / 2, 34, p.zh, { 'text-anchor': 'middle', fill: p.col, 'font-size': 11.5 });
    });
    const gE = el('g', {}, svg);
    E.forEach(([a, b]) => {
      const A = pos[a], B = pos[b];
      let d;
      if (A.x === B.x) { const bul = 10 + 7 * Math.abs(A.y - B.y) / 61; d = `M ${A.x + BW} ${A.y + BH / 2} C ${A.x + BW + bul} ${A.y + BH / 2}, ${B.x + BW + bul} ${B.y + BH / 2}, ${B.x + BW} ${B.y + BH / 2}`; }
      else {
        const [P, Q] = A.x < B.x ? [A, B] : [B, A];
        d = `M ${P.x + BW} ${P.y + BH / 2} C ${P.x + BW + 30} ${P.y + BH / 2}, ${Q.x - 30} ${Q.y + BH / 2}, ${Q.x} ${Q.y + BH / 2}`;
      }
      const e = el('path', { d, fill: 'none', stroke: '#b8b3a6', 'stroke-width': 1.6, class: 'atlas-edge' }, gE);
      edgeEls.push({ e, a, b });
    });
    Object.keys(L).forEach(n => {
      const p = pos[n];
      const a = el('a', { href: `lesson${n}.html` }, svg);
      const g = el('g', { class: 'atlas-node' }, a);
      el('rect', { x: p.x, y: p.y, width: BW, height: BH, rx: 9, fill: '#fff', stroke: p.col, 'stroke-width': n == 25 ? 3.5 : 2 }, g);
      T(g, p.x + 7, p.y + 15, `L${n} ${L[n][0]}`, { 'font-size': 11, 'font-weight': 700, fill: p.col });
      T(g, p.x + 7, p.y + 30, L[n][1], { 'font-size': 10.5, fill: '#4a5568' });
      T(g, p.x + 7, p.y + 44, L[n][2], { 'font-size': 9.5, fill: C.muted, class: 'm' });
      a.addEventListener('click', ev => { if (selN !== n) { ev.preventDefault(); select(n); } });
      nodeEls[n] = g;
    });
  }
  function select(n) {
    selN = n;
    const nb = new Set([+n]);
    edgeEls.forEach(({ e, a, b }) => {
      const on = a == n || b == n;
      e.classList.toggle('dimmed', !on);
      e.setAttribute('stroke', on ? pos[n].col : '#b8b3a6');
      e.setAttribute('stroke-width', on ? 3 : 1.6);
      if (on) { nb.add(a); nb.add(b); }
    });
    Object.entries(nodeEls).forEach(([k, g]) => g.classList.toggle('dimmed', !nb.has(+k)));
    const links = E.filter(([a, b]) => a == n || b == n).map(([a, b, en, zh]) => {
      const o = a == n ? b : a;
      return `<li><a href="lesson${o}.html">L${o}</a> · ${bil(L[o][0], L[o][1])}${en ? ' — ' + bil(en, zh) : ''}</li>`;
    }).join('');
    okBox($('atInfo'), `<b>L${n} · ${bil(L[n][0], L[n][1])}</b> &nbsp; <span class="m">${L[n][2]}</span><br>${bil('Connections', '关联')}:<ul style="margin:4px 0">${links}</ul><a class="btn small" href="lesson${n}.html" style="text-decoration:none">${bil('Open lesson', '打开本课')} ${n} →</a>`, 'info');
  }
  render();
  select('25');
})();
