// Lesson 20 interactions: the Lévy hierarchy & absoluteness.
Lang.init();
Progress.paint();

const $ = id => document.getElementById(id);
const okBox = (box, html, kind = 'ok') => { box.className = 'msg ' + kind; box.innerHTML = html; };
const clearBox = box => { box.className = 'msg'; box.innerHTML = ''; };
const T = (svg, x, y, s, attrs = {}) => { const t = el('text', { x, y, ...attrs }, svg); t.textContent = s; return t; };
const selIn = (group, btn) => { group.forEach(b => b.classList.toggle('sel', b === btn)); };
const SUBS = '₀₁₂₃₄₅₆₇₈₉';
const sub = n => String(n).split('').map(d => SUBS[d]).join('');

function arrowDefs(svg, id, color) {
  const defs = el('defs', {}, svg);
  const m = el('marker', { id, viewBox: '0 0 10 10', refX: 9, refY: 5, markerWidth: 11, markerHeight: 11, markerUnits: 'userSpaceOnUse', orient: 'auto-start-reverse' }, defs);
  el('path', { d: 'M0,0 L10,5 L0,10 z', fill: color }, m);
}

/* ================= check-yourself ================= */
function CY(id, q, opts, expl) {
  const box = $(id);
  box.innerHTML = `<div class="q">✎ ${bil('Check yourself', '自测')}: ${q}</div><div class="opts"></div>
    <div class="toolbar" style="margin:4px 0"><button class="btn small ghost">${bil('Show answer', '显示答案')}</button></div><div class="msg"></div>`;
  const wrap = box.querySelector('.opts'), msg = box.querySelector('.msg');
  const btns = opts.map(o => {
    const b = document.createElement('button');
    b.className = 'btn small';
    b.innerHTML = o.h;
    b.addEventListener('click', () => {
      btns.forEach(x => x.classList.remove('right', 'wrongc'));
      b.classList.add(o.ok ? 'right' : 'wrongc');
      if (o.ok) okBox(msg, '✓ ' + expl);
      else okBox(msg, '✗ ' + (o.why || bi('Not quite. Try another option.', '不太对，换一个选项试试。')), 'bad');
    });
    wrap.appendChild(b);
    return b;
  });
  box.querySelector('.ghost').addEventListener('click', () => {
    btns.forEach((x, i) => { x.classList.remove('right', 'wrongc'); if (opts[i].ok) x.classList.add('right'); });
    okBox(msg, expl, 'info');
  });
}

/* ================= stepwise proofs ================= */
document.querySelectorAll('.proof').forEach(pf => {
  const steps = [...pf.querySelectorAll('.step')];
  let k = 0;
  const nx = pf.querySelector('[data-pnext]'), all = pf.querySelector('[data-pall]');
  nx.addEventListener('click', () => { if (k < steps.length) steps[k++].classList.add('on'); if (k === steps.length) nx.disabled = true; });
  all.addEventListener('click', () => { steps.forEach(s => s.classList.add('on')); k = steps.length; nx.disabled = true; });
});

/* ================= §1 Δ₀ search ================= */
(function delta0() {
  const SETS = {
    '0': [], '1': ['0'], '2': ['0', '1'], '3': ['0', '1', '2'],
    '{1}': ['1'], '{0,2}': ['0', '2'], '{0,1,{1}}': ['0', '1', '{1}'],
  };
  const rank = k => SETS[k].length ? 1 + Math.max(...SETS[k].map(rank)) : 0;
  const cands = ['3', '{0,1,{1}}', '{1}', '{0,2}'];
  const props = [
    { id: 'trans', h: bil('x is transitive', 'x 是传递集'), f: '∀y∈x ∀z∈y (z∈x)' },
    { id: 'ord', h: bil('x is an ordinal', 'x 是序数'), f: 'trans(x) ∧ ∀y∈x ∀z∈x (y∈z ∨ y=z ∨ z∈y)' },
    { id: 'unb', h: bil('∃y (x ∈ y), unbounded', '∃y (x ∈ y)，无界'), f: '∃y (x∈y)' },
  ];
  let cur = '{0,1,{1}}', prop = 'trans', token = 0;
  const svg = $('d0svg');
  const setBtns = cands.map(c => {
    const b = document.createElement('button');
    b.className = 'btn small' + (c === cur ? ' sel' : '');
    b.innerHTML = `x = <span class="m">${c}</span>`;
    b.addEventListener('click', () => { cur = c; selIn(setBtns, b); run(); });
    $('d0sets').appendChild(b);
    return b;
  });
  const propBtns = props.map(p => {
    const b = document.createElement('button');
    b.className = 'btn' + (p.id === prop ? ' sel' : '');
    b.innerHTML = p.h;
    b.addEventListener('click', () => { prop = p.id; selIn(propBtns, b); run(); });
    $('d0props').appendChild(b);
    return b;
  });
  const replay = document.createElement('button');
  replay.className = 'btn primary';
  replay.innerHTML = bi('Run the search ▶', '运行搜索 ▶');
  replay.addEventListener('click', () => run());
  $('d0props').appendChild(replay);

  let pos = {}, nodeG = {}, edgeEl = {};
  function draw() {
    svg.innerHTML = '';
    arrowDefs(svg, 'd0arr', '#9aa0aa');
    const nodes = new Set();
    (function walk(k) { if (nodes.has(k)) return; nodes.add(k); SETS[k].forEach(walk); })(cur);
    const byRank = {};
    nodes.forEach(k => { const r = rank(k); (byRank[r] = byRank[r] || []).push(k); });
    pos = {};
    Object.keys(byRank).forEach(r => {
      const row = byRank[r].sort();
      const zig = row.length === 1 ? (r % 2 ? 60 : -60) : 0; // zigzag so that edges skipping a rank do not run through nodes
      row.forEach((k, i) => { pos[k] = { x: 260 + zig + (i - (row.length - 1) / 2) * 150, y: 290 - r * 72 }; });
    });
    el('rect', { x: 60, y: 40, width: 400, height: 275, rx: 18, fill: 'none', stroke: '#c5cdf5', 'stroke-dasharray': '6 6' }, svg);
    T(svg, 70, 58, 'trcl({x})', { class: 'small', fill: '#3b5bdb' });
    edgeEl = {};
    nodes.forEach(k => SETS[k].forEach(c => {
      const a = pos[c], b = pos[k];
      const dx = b.x - a.x, dy = b.y - a.y, L = Math.hypot(dx, dy);
      const ln = el('line', { x1: a.x + dx / L * 22, y1: a.y + dy / L * 22, x2: b.x - dx / L * 24, y2: b.y - dy / L * 24, stroke: '#9aa0aa', 'stroke-width': 2, 'marker-end': 'url(#d0arr)' }, svg);
      edgeEl[c + '>' + k] = ln;
    }));
    nodeG = {};
    nodes.forEach(k => {
      const g = el('g', { transform: `translate(${pos[k].x},${pos[k].y})` }, svg);
      const isX = k === cur;
      const hw = Math.max(21, k.length * 5 + 8);
      el('rect', { x: -hw, y: -21, width: 2 * hw, height: 42, rx: 21, fill: isX ? '#f8e7fc' : '#fff', stroke: isX ? '#ae3ec9' : '#1f2430', 'stroke-width': 2 }, g);
      T(g, 0, 5, k, { 'text-anchor': 'middle', 'font-size': k.length > 2 ? 13 : 15, 'font-weight': 700 });
      if (isX) T(g, 0, -28, 'x', { 'text-anchor': 'middle', 'font-size': 14, fill: '#ae3ec9', 'font-weight': 700 });
      nodeG[k] = g;
    });
    T(svg, 490, 300, 'arrow u → v means u ∈ v', { class: 'small', fill: '#6b7280' });
    T(svg, 490, 316, '箭头 u → v 表示 u ∈ v', { class: 'small', fill: '#6b7280' });
  }
  const mark = (k, color) => nodeG[k] && nodeG[k].querySelector('rect').setAttribute('fill', color);
  const unmarkAll = () => Object.keys(nodeG).forEach(k => mark(k, k === cur ? '#f8e7fc' : '#fff'));
  async function run() {
    const my = ++token;
    draw();
    const P = props.find(p => p.id === prop);
    const log = el('text', { x: 490, y: 90, 'font-size': 13, 'font-weight': 700 }, svg);
    const log2 = el('text', { x: 490, y: 112, 'font-size': 12, fill: '#6b7280' }, svg);
    const res = el('text', { x: 490, y: 150, 'font-size': 14, 'font-weight': 800 }, svg);
    T(svg, 490, 60, P.f, { 'font-size': 11.5, fill: '#1f2430' });
    let visited = new Set([cur]), ok = true, steps = 0;
    const wait = async ms => { await sleep(ms); return my === token; };
    if (prop === 'unb') {
      // unbounded search: needs sets outside the picture
      const g = el('g', {}, svg);
      const path = el('path', { d: `M${pos[cur].x},${pos[cur].y - 22} C ${pos[cur].x + 30},10 600,10 720,-30`, fill: 'none', stroke: '#e03131', 'stroke-width': 3, 'stroke-dasharray': '7 6' }, g);
      path.classList.add('fadein');
      log.textContent = 'searching for y with x ∈ y …';
      log2.textContent = '在全宇宙里找 y 使 x ∈ y …';
      if (!(await wait(900))) return;
      res.setAttribute('fill', '#e03131');
      res.textContent = 'no such y inside trcl({x}) ∪ {x}';
      T(svg, 490, 172, '框内找不到这样的 y', { 'font-size': 13, fill: '#e03131', 'font-weight': 700 });
      T(svg, 490, 205, 'in V: true, take y = {x}', { 'font-size': 13, fill: '#2f9e44', 'font-weight': 700 });
      T(svg, 490, 225, '在 V 中：真，取 y = {x}', { 'font-size': 13, fill: '#2f9e44', 'font-weight': 700 });
      okBox($('d0msg'), bi(`The answer depends on <b>where</b> you search. In the transitive set <span class="m">M = trcl({x}) ∪ {x}</span> the sentence <span class="m">∃y (x∈y)</span> is false, while in V it is true. This is not Δ₀ (it is Σ₁), and §5 explains why a Σ₁ statement can be true in V but false in a transitive M.`,
        `答案取决于在<b>哪里</b>搜。在传递集 <span class="m">M = trcl({x}) ∪ {x}</span> 中，<span class="m">∃y (x∈y)</span> 为假；在 V 中为真。它不是 Δ₀ 的（是 Σ₁ 的）；§5 会解释为什么 Σ₁ 命题可以在 V 中真、在传递的 M 中假。`), 'warn');
      return;
    }
    okBox($('d0msg'), bi('Searching… blue = y being inspected, gold = z being inspected.', '搜索中……蓝色＝正在检查的 y，金色＝正在检查的 z。'), 'info');
    const els = SETS[cur];
    // transitivity
    for (const y of els) {
      for (const z of SETS[y]) {
        if (!(await wait(520))) return;
        unmarkAll(); mark(y, '#e7ecff'); mark(z, '#fff3bf');
        visited.add(y); visited.add(z); steps++;
        const good = els.includes(z);
        const e = edgeEl[z + '>' + y];
        if (e) { e.setAttribute('stroke', good ? '#2f9e44' : '#e03131'); e.setAttribute('stroke-width', 4); }
        log.textContent = `y = ${y}, z = ${z}: z ∈ x ? ${good ? 'yes' : 'NO'}`;
        log2.textContent = `y = ${y}，z = ${z}：z ∈ x 吗？${good ? '是' : '否'}`;
        if (!good) ok = false;
      }
    }
    let ordOk = ok;
    if (prop === 'ord' && ok) {
      for (let i = 0; i < els.length; i++) for (let j = i + 1; j < els.length; j++) {
        if (!(await wait(560))) return;
        const y = els[i], z = els[j];
        unmarkAll(); mark(y, '#e7ecff'); mark(z, '#fff3bf'); steps++;
        const good = SETS[z].includes(y) || SETS[y].includes(z);
        log.textContent = `${y} vs ${z}: comparable by ∈ ? ${good ? 'yes' : 'NO'}`;
        log2.textContent = `${y} 与 ${z}：可用 ∈ 比较吗？${good ? '是' : '否'}`;
        if (!good) ordOk = false;
      }
    }
    if (!(await wait(400))) return;
    unmarkAll();
    const verdict = prop === 'trans' ? ok : ordOk;
    res.setAttribute('fill', verdict ? '#2f9e44' : '#e03131');
    res.textContent = (verdict ? 'TRUE' : 'FALSE') + ` after ${steps} checks`;
    T(svg, 490, 172, `${verdict ? '为真' : '为假'}，共检查 ${steps} 次`, { 'font-size': 13, fill: verdict ? '#2f9e44' : '#e03131', 'font-weight': 700 });
    T(svg, 490, 205, `sets visited: ${visited.size}, all inside the box`, { 'font-size': 12, fill: '#3b5bdb' });
    T(svg, 490, 223, `访问过的集合：${visited.size} 个，全在框内`, { 'font-size': 12, fill: '#3b5bdb' });
    let extra = '';
    if (cur === '{0,1,{1}}' && prop === 'ord') extra = bi(' Here x is transitive but not an ordinal: <span class="m">0</span> and <span class="m">{1}</span> are ∈-incomparable.', ' 这里 x 是传递集但不是序数：<span class="m">0</span> 与 <span class="m">{1}</span> 无法用 ∈ 比较。');
    if (prop === 'ord' && !ok) extra = bi(' Not even transitive, so the ordinal test fails at the first conjunct.', ' 连传递都不满足，序数检验在第一个合取项就失败了。');
    okBox($('d0msg'), bi(`The search only ever looked at elements of elements of x. Any transitive universe that contains x contains everything it looked at, so it gets the same answer.`,
      `搜索只看了 x 的元素的元素……任何包含 x 的传递宇宙都包含它看过的一切，所以会得到同样的答案。`) + extra, verdict ? 'ok' : 'warn');
  }
  run();
  CY('cy1', bi('Which formula is Δ₀ (as written)?', '下列哪个公式（照字面）是 Δ₀ 的？'), [
    { h: '<span class="m">∀y∈x ∃z∈y (z = z)</span>', ok: true },
    { h: '<span class="m">∃y (x ∈ y)</span>', why: bi('∃y is unbounded: it ranges over all of V.', '∃y 是无界的，取遍整个 V。') },
    { h: '<span class="m">∃z∈𝒫(x) (z = z)</span>', why: bi('𝒫(x) is not a variable. Unfolding it needs “w = 𝒫(x)”, which is Π₁, not Δ₀.', '𝒫(x) 不是变元；展开需要“w = 𝒫(x)”，它是 Π₁ 的，不是 Δ₀ 的。') },
  ], bi('Both quantifiers are bounded by variables (x, then y). (It says: every element of x is non-empty.)', '两个量词都以变元为界（先是 x，再是 y）。（它的意思是：x 的每个元素都非空。）'));
})();

/* ================= §2/§3 shared quantifier machinery ================= */
const VARS = ['x', 'y', 'z', 'u', 'v', 'w', 't', 's', 'r', 'q'];
// codes: 'E','A' unbounded; 'bE','bA' bounded by most recent variable (or parameter a)
function codesToQ(codes) {
  const q = [];
  codes.forEach((c, i) => {
    const v = VARS[i % VARS.length] + (i >= VARS.length ? "'" : '');
    const bound = q.length ? q[q.length - 1].v : 'a';
    q.push({ t: c.endsWith('E') ? 'E' : 'A', b: c.startsWith('b') ? bound : null, v });
  });
  return q;
}
const qStr = z => (z.t === 'E' ? '∃' : '∀') + z.v + (z.b ? '∈' + z.b : '');
function formulaStr(q) { const vs = q.filter(z => !z.fresh).map(z => z.v); return q.map(qStr).join(' ') + ' φ₀(a' + (vs.length ? ', ' + vs.join(', ') : '') + ')'; }
function blocksOf(q) {
  const out = [];
  q.filter(z => !z.b).forEach(z => { if (!out.length || out[out.length - 1] !== z.t) out.push(z.t); });
  return out;
}
function zfClass(q) {
  const bl = blocksOf(q);
  if (!bl.length) return 'Δ₀';
  return (bl[0] === 'E' ? 'Σ' : 'Π') + sub(bl.length);
}
function literalClass(q) {
  let lastU = -1;
  q.forEach((z, i) => { if (!z.b) lastU = i; });
  const badBounded = q.some((z, i) => z.b && i < lastU);
  if (badBounded) return null;
  return zfClass(q);
}
// one rewriting step: returns null if already normal
function rewriteStep(q, used) {
  for (let i = 0; i + 1 < q.length; i++) {
    const B = q[i], U = q[i + 1];
    if (B.b && !U.b) {
      if (B.t === U.t) {
        return { q: [...q.slice(0, i), U, B, ...q.slice(i + 2)], i, rule: 'swap' };
      }
      let k = 1, w;
      do { w = 'b' + sub(k++); } while (used.has(w));
      used.add(w);
      const nq = [...q.slice(0, i), { t: U.t, b: null, v: w, fresh: true }, B, { t: U.t, b: w, v: U.v }, ...q.slice(i + 2)];
      return { q: nq, i, rule: B.t === 'A' ? 'coll' : 'dual', w };
    }
  }
  return null;
}
function normalize(q) {
  const used = new Set(q.map(z => z.v));
  const trace = [];
  let cur = q, st;
  let guard = 0;
  while ((st = rewriteStep(cur, used)) && guard++ < 200) { trace.push(st); cur = st.q; }
  return { q: cur, trace };
}
if (typeof module !== 'undefined') module.exports = { codesToQ, normalize, zfClass, literalClass, blocksOf, formulaStr };

function renderBar(bar, q, hot = new Set()) {
  bar.innerHTML = '';
  q.forEach((z, i) => {
    const s = document.createElement('span');
    s.className = 'qtok ' + (z.b ? 'bd' : z.t) + (hot.has(i) ? ' hot' : '') + (z.fresh ? ' newb' : '');
    s.textContent = qStr(z);
    bar.appendChild(s);
  });
  const m = document.createElement('span');
  m.className = 'qtok mx';
  m.textContent = 'φ₀ (Δ₀)';
  bar.appendChild(m);
}

/* ================= §2 builder ================= */
let builderCodes = ['A', 'bE', 'E'];
(function builder() {
  const svg = $('qstairs');
  function render() {
    const q = codesToQ(builderCodes);
    renderBar($('qbar'), q);
    svg.innerHTML = '';
    const n = q.length;
    const W = 760, x0 = 30, cw = Math.min(90, (W - 200) / Math.max(n, 1));
    el('line', { x1: x0, y1: 125, x2: x0 + n * cw + 120, y2: 125, stroke: '#ccc' }, svg);
    let block = 0, last = null;
    q.forEach((z, i) => {
      const x = x0 + i * cw;
      if (!z.b) { if (z.t !== last) { block++; last = z.t; } }
      const h = z.b ? 14 : 22 * block;
      const r = el('rect', { x: x + 3, y: 125 - h - (z.b ? 0 : 0), width: cw - 6, height: h, rx: 5,
        fill: z.b ? '#eceae3' : z.t === 'E' ? '#e7ecff' : '#ffe3e3', stroke: z.b ? '#999' : z.t === 'E' ? '#3b5bdb' : '#e03131', 'stroke-dasharray': z.b ? '4 3' : '' }, svg);
      r.classList.add('fadein');
      T(svg, x + cw / 2, 125 - h - 6, qStr(z), { 'text-anchor': 'middle', 'font-size': cw < 60 ? 10 : 13, 'font-weight': 700, fill: z.b ? '#777' : '#1f2430' });
      if (!z.b) T(svg, x + cw / 2, 141, 'block ' + block, { 'text-anchor': 'middle', 'font-size': 10, fill: '#6b7280' });
    });
    el('rect', { x: x0 + n * cw + 4, y: 103, width: 100, height: 22, rx: 5, fill: '#fff3bf', stroke: '#f08c00' }, svg);
    T(svg, x0 + n * cw + 54, 119, 'φ₀ Δ₀', { 'text-anchor': 'middle', 'font-size': 13, 'font-weight': 700 });
    const lit = literalClass(q), zf = zfClass(q);
    const bl = blocksOf(q).length;
    let h = `<span class="m" style="font-size:16px">${formulaStr(q)}</span><br>`;
    if (lit) h += bi(`<b>As written:</b> a ${lit} formula (${bl} unbounded block${bl === 1 ? '' : 's'}; bounded quantifiers sit inside the matrix).`,
      `<b>照字面：</b>${lit} 公式（${bl} 个无界量词块；有界量词都在母式里）。`);
    else h += bi(`<b>As written:</b> not literally of the form Σₙ/Πₙ, because a bounded quantifier stands <i>in front of</i> an unbounded one. <b>Modulo ZF</b> it is <b>${zf}</b>; see the normalizer in §3.`,
      `<b>照字面：</b>不是 Σₙ/Πₙ 的标准形式，因为有个有界量词挡在无界量词<i>前面</i>。<b>模 ZF</b> 它是 <b>${zf}</b> 的，见 §3 的规范化器。`);
    if (zf !== 'Δ₀') h += '<br>' + bi(`It is then also Σₘ and Πₘ for every m &gt; ${bl}, by adding dummy quantifiers.`, `补哑量词后，它对每个 m &gt; ${bl} 也是 Σₘ 和 Πₘ 的。`);
    okBox($('qmsg'), h, lit ? 'info' : 'warn');
  }
  document.querySelectorAll('[data-q]').forEach(b => b.addEventListener('click', () => { if (builderCodes.length < 9) builderCodes.push(b.dataset.q); render(); }));
  $('qUndo').addEventListener('click', () => { builderCodes.pop(); render(); });
  $('qClear').addEventListener('click', () => { builderCodes = []; render(); });
  document.querySelectorAll('[data-pre]').forEach(b => b.addEventListener('click', () => { builderCodes = b.dataset.pre.split(','); render(); }));
  render();
  CY('cy2', bi('With φ₀ Δ₀, the formula <span class="m">∀x ∃y ∀z φ₀</span> is literally…', '设 φ₀ 为 Δ₀，公式 <span class="m">∀x ∃y ∀z φ₀</span> 照字面是……'), [
    { h: 'Σ₃', why: bi('It starts with ∀, so it is a Π-class.', '它以 ∀ 开头，属于 Π 类。') },
    { h: 'Π₃', ok: true },
    { h: 'Π₂', why: bi('Count the blocks: ∀ | ∃ | ∀ gives three.', '数一数块：∀ | ∃ | ∀，共三块。') },
  ], bi('Three alternating unbounded blocks, starting with ∀: Π₃.', '三个交替的无界块，以 ∀ 开头：Π₃。'));
})();

/* ================= §3 normalizer ================= */
(function normalizer() {
  const presets = [
    { c: ['bA', 'E'] }, { c: ['bE', 'A'] }, { c: ['bA', 'bE', 'A'] },
    { c: ['E', 'bA', 'E', 'A'] }, { c: ['bA', 'bA', 'E', 'A'] },
  ];
  const sel = $('nzPre');
  presets.forEach((p, i) => { const o = document.createElement('option'); o.value = i; o.textContent = formulaStr(codesToQ(p.c)); sel.appendChild(o); });
  let q0, cur, used, lines;
  function load(q) {
    q0 = q; cur = q; used = new Set(q.map(z => z.v));
    lines = 0;
    $('nzlog').innerHTML = '';
    addLine(q, bi('start', '起点'));
    renderBar($('nzbar'), cur);
    $('nzStep').disabled = false;
    clearBox($('nzmsg'));
    if (!rewriteStep(cur, new Set(used))) finish();
  }
  function addLine(q, why) {
    const li = document.createElement('li');
    li.className = 'fadein';
    li.innerHTML = `${formulaStr(q)}<span class="why">${why}</span>`;
    $('nzlog').appendChild(li);
  }
  function finish() {
    $('nzStep').disabled = true;
    const c = zfClass(cur);
    okBox($('nzmsg'), bi(`Normal form reached: every bounded quantifier is now inside the matrix. Unbounded blocks: <b>${blocksOf(cur).join(' | ').replace(/E/g, '∃').replace(/A/g, '∀') || 'none'}</b>, so the formula is <b>${c}<sup>ZF</sup></b>. The sequence of unbounded quantifier <i>types</i> never changed: that is why “ignore bounded quantifiers” is a correct shortcut modulo ZF.`,
      `已到规范形：所有有界量词都进了母式。无界量词块为 <b>${blocksOf(cur).join(' | ').replace(/E/g, '∃').replace(/A/g, '∀') || '无'}</b>，所以公式是 <b>${c}<sup>ZF</sup></b> 的。无界量词的<i>类型序列</i>始终没变，这就是为什么“模 ZF 时忽略有界量词”是正确的捷径。`));
  }
  function step() {
    const st = rewriteStep(cur, used);
    if (!st) { finish(); return false; }
    const B = cur[st.i], U = cur[st.i + 1];
    let why;
    if (st.rule === 'swap') why = bi(`pure logic: ${qStr(B)} ${qStr(U)} ↔ ${qStr(U)} ${qStr(B)} (same type, ${U.v} not free in the bound ${B.b})`, `纯逻辑：${qStr(B)} ${qStr(U)} ↔ ${qStr(U)} ${qStr(B)}（同类型，${U.v} 不在界 ${B.b} 中自由出现）`);
    else if (st.rule === 'coll') why = bi(`Collection: ${qStr(B)} ∃${U.v} ψ ↔ ∃${st.w} ${qStr(B)} ∃${U.v}∈${st.w} ψ`, `收集原理：${qStr(B)} ∃${U.v} ψ ↔ ∃${st.w} ${qStr(B)} ∃${U.v}∈${st.w} ψ`);
    else why = bi(`dual Collection (negate both sides): ${qStr(B)} ∀${U.v} ψ ↔ ∀${st.w} ${qStr(B)} ∀${U.v}∈${st.w} ψ`, `对偶收集（两边取否定）：${qStr(B)} ∀${U.v} ψ ↔ ∀${st.w} ${qStr(B)} ∀${U.v}∈${st.w} ψ`);
    cur = st.q;
    const hot = st.rule === 'swap' ? new Set([st.i, st.i + 1]) : new Set([st.i, st.i + 1, st.i + 2]);
    renderBar($('nzbar'), cur, hot);
    addLine(cur, why);
    if (!rewriteStep(cur, new Set(used))) finish();
    return true;
  }
  sel.addEventListener('change', () => load(codesToQ(presets[+sel.value].c)));
  $('nzFromBuilder').addEventListener('click', () => load(codesToQ(builderCodes)));
  $('nzStep').addEventListener('click', step);
  $('nzAll').addEventListener('click', async () => { while (step()) await sleep(450); });
  load(codesToQ(presets[0].c));

  const fin = {
    S: bi('<b>Σ₁:</b> ∃w ∃n ∃f ( w = ω ∧ n ∈ w ∧ f is a bijection from n onto x )<br><span style="font-family:var(--sans)">“w = ω” and “f is a bijection n → x” are Δ₀.</span>',
      '<b>Σ₁：</b>∃w ∃n ∃f ( w = ω ∧ n ∈ w ∧ f 是从 n 到 x 的双射 )<br><span style="font-family:var(--sans)">“w = ω”与“f 是 n → x 的双射”都是 Δ₀ 的。</span>'),
    P: bi('<b>Π₁:</b> ∀F ( (F ≠ ∅ ∧ ∀u∈F (u ⊆ x)) → ∃u∈F ∀v∈F ¬(u ⊊ v) )<br><span style="font-family:var(--sans)">“Every non-empty family of subsets of x has a ⊆-maximal member” (Tarski-finiteness). ZF proves it is equivalent to finiteness. Both forms are ZF-equivalent, so “finite” is Δ₁<sup>ZF</sup>.</span>',
      '<b>Π₁：</b>∀F ( (F ≠ ∅ ∧ ∀u∈F (u ⊆ x)) → ∃u∈F ∀v∈F ¬(u ⊊ v) )<br><span style="font-family:var(--sans)">“x 的子集组成的每个非空族都有 ⊆-极大元”（塔斯基有限）。ZF 证明它与有限等价。两种形式在 ZF 中等价，所以“有限”是 Δ₁<sup>ZF</sup> 的。</span>'),
  };
  const fb = [$('finS'), $('finP')];
  $('finS').addEventListener('click', () => { selIn(fb, $('finS')); $('finBox').innerHTML = fin.S; });
  $('finP').addEventListener('click', () => { selIn(fb, $('finP')); $('finBox').innerHTML = fin.P; });
  $('finBox').innerHTML = fin.S;
  CY('cy3', bi('Modulo ZF, <span class="m">∃u ∀x∈u ∃y ∀z∈y φ₀</span> (φ₀ Δ₀) is…', '模 ZF，<span class="m">∃u ∀x∈u ∃y ∀z∈y φ₀</span>（φ₀ 为 Δ₀）是……'), [
    { h: 'Σ₁', ok: true },
    { h: 'Σ₂', why: bi('∀x∈u and ∀z∈y are bounded and do not count.', '∀x∈u 和 ∀z∈y 都有界，不计数。') },
    { h: 'Π₂', why: bi('The unbounded quantifiers are ∃u and ∃y only.', '无界量词只有 ∃u 和 ∃y。') },
  ], bi('Unbounded quantifiers: ∃u, ∃y, one ∃-block. Collection turns ∀x∈u ∃y into ∃b ∀x∈u ∃y∈b, giving ∃u ∃b [Δ₀]: Σ₁<sup>ZF</sup>.', '无界量词只有 ∃u、∃y，构成一个 ∃ 块。收集原理把 ∀x∈u ∃y 改成 ∃b ∀x∈u ∃y∈b，得到 ∃u ∃b [Δ₀]：Σ₁<sup>ZF</sup>。'));
})();

/* ================= §4 transitive vs not ================= */
(function transitive() {
  const svg = $('trsvg');
  let trans = true, token = 0;
  function draw() {
    svg.innerHTML = '';
    arrowDefs(svg, 'trArr', '#3b5bdb');
    el('rect', { x: 10, y: 10, width: 740, height: 280, rx: 20, fill: '#fbfaf6', stroke: '#1f2430', 'stroke-width': 2 }, svg);
    T(svg, 26, 34, 'V', { 'font-size': 20, 'font-weight': 800 });
    el('ellipse', { cx: trans ? 300 : 250, cy: 160, rx: trans ? 230 : 150, ry: 115, fill: 'rgba(174,62,201,.10)', stroke: '#ae3ec9', 'stroke-width': 2.5 }, svg);
    T(svg, trans ? 150 : 150, 95, trans ? 'M (transitive · 传递)' : 'M (not transitive · 不传递)', { 'font-size': 14, 'font-weight': 700, fill: '#ae3ec9' });
    const nodes = { x: [250, 120], a: [trans ? 180 : 560, 220], b: [trans ? 340 : 650, 220] };
    [['a', 'x'], ['b', 'x']].forEach(([u, v]) => {
      el('line', { x1: nodes[u][0], y1: nodes[u][1] - 18, x2: nodes[v][0], y2: nodes[v][1] + 20, stroke: '#9aa0aa', 'stroke-width': 2 }, svg);
    });
    for (const k in nodes) {
      const g = el('g', { transform: `translate(${nodes[k][0]},${nodes[k][1]})`, id: 'tr_' + k }, svg);
      el('circle', { r: 19, fill: '#fff', stroke: '#1f2430', 'stroke-width': 2 }, g);
      T(g, 0, 6, k, { 'text-anchor': 'middle', 'font-size': 17, 'font-weight': 700 });
    }
    T(svg, 285, 115, 'x = {a, b}', { 'font-size': 13, fill: '#555' });
    return nodes;
  }
  async function run() {
    const my = ++token;
    const nodes = draw();
    clearBox($('trmsg'));
    const ask = async (who, color, x0, see) => {
      const lab = T(svg, x0, 270, who === 'M' ? 'M searches its own elements of x · M 在自己里面找 x 的元素' : 'V searches all elements of x · V 找 x 的所有元素', { 'font-size': 12, fill: color, 'font-weight': 700 });
      for (const k of ['a', 'b']) {
        await sleep(600); if (my !== token) return null;
        const visible = see(k);
        el('line', { x1: nodes.x[0], y1: nodes.x[1] + 20, x2: nodes[k][0], y2: nodes[k][1] - 20, stroke: visible ? color : '#ccc', 'stroke-width': 3.5, 'stroke-dasharray': visible ? '' : '5 5', 'marker-end': visible ? 'url(#trArr)' : '' }, svg);
        if (!visible) T(svg, nodes[k][0], nodes[k][1] + 36, '∉ M', { 'font-size': 12, fill: '#e03131', 'text-anchor': 'middle', 'font-weight': 700 });
      }
      await sleep(400);
      lab.remove();
      return true;
    };
    if (!(await ask('M', '#ae3ec9', 30, k => trans))) return;
    const mAns = !trans;
    if (!(await ask('V', '#3b5bdb', 30, () => true))) return;
    const res = el('text', { x: 400, y: 40, 'font-size': 15, 'font-weight': 800, fill: mAns ? '#e03131' : '#2f9e44' }, svg);
    res.textContent = `M: x = ∅ ? ${mAns ? 'yes' : 'no'}   ·   V: x = ∅ ? no`;
    if (trans) okBox($('trmsg'), bi('Both say <b>no</b>. Since M is transitive, a, b ∈ M, so M sees exactly the elements V sees. A Δ₀ question is answered the same way.', '两边都说<b>不是</b>。M 传递，所以 a, b ∈ M，M 看到的元素和 V 完全一样，Δ₀ 问题的答案也一样。'));
    else okBox($('trmsg'), bi('M says <b>“x = ∅”</b> but V says no. M contains x but not its elements, so a bounded search inside M finds nothing. Δ₀ absoluteness fails, and this is precisely why the theorem assumes transitivity.', 'M 说<b>“x = ∅”</b>，V 却说不是。M 含有 x 却不含 x 的元素，所以 M 内部的有界搜索一无所获。Δ₀ 绝对性失效，这正是定理要假设传递性的原因。'), 'bad');
  }
  const bs = [$('trT'), $('trN')];
  $('trT').addEventListener('click', () => { trans = true; selIn(bs, $('trT')); token++; draw(); clearBox($('trmsg')); });
  $('trN').addEventListener('click', () => { trans = false; selIn(bs, $('trN')); token++; draw(); clearBox($('trmsg')); });
  $('trRun').addEventListener('click', run);
  draw();
  CY('cy4', bi('Which property of M does the proof of Δ₀ absoluteness actually use?', 'Δ₀ 绝对性的证明真正用到了 M 的哪条性质？'), [
    { h: bil('M ⊨ ZF', 'M ⊨ ZF'), why: bi('No axioms are needed. Only the bounded-quantifier step uses anything about M.', '不需要任何公理；只有有界量词那一步用到了 M 的性质。') },
    { h: bil('M is transitive', 'M 是传递的'), ok: true },
    { h: bil('M is countable', 'M 是可数的'), why: bi('Size plays no role: V itself is a transitive class.', '大小无关紧要：V 本身就是传递类。') },
  ], bi('Only transitivity: in the bounded-quantifier step, x ∈ y ∈ M ⇒ x ∈ M.', '只用到传递性：有界量词那一步需要 x ∈ y ∈ M ⇒ x ∈ M。'));
})();

/* ================= §5 ladder ================= */
(function ladder() {
  const rows = [
    { k: 'd0', cls: 'Δ₀', arr: '↕', c: 'arrowU', en: 'absolute for every transitive M', zh: '对每个传递的 M 绝对' },
    { k: 's1', cls: 'Σ₁', arr: '↑', c: 'arrowU', en: 'upward: M ⊨ φ ⇒ V ⊨ φ', zh: '向上：M ⊨ φ ⇒ V ⊨ φ' },
    { k: 'p1', cls: 'Π₁', arr: '↓', c: 'arrowD', en: 'downward: V ⊨ φ ⇒ M ⊨ φ', zh: '向下：V ⊨ φ ⇒ M ⊨ φ' },
    { k: 'd1', cls: 'Δ₁<sup>ZF</sup>', arr: '↕', c: 'arrowU', en: 'absolute if M ⊨ ZF (finite, well-founded, rank, L_α…)', zh: '若 M ⊨ ZF 则绝对（有限、良基、秩、L_α……）' },
    { k: 's2', cls: 'Σ₂ / Π₂', arr: '✗', c: 'arrowN', en: 'no general guarantee (e.g. CH)', zh: '一般没有保证（如 CH）' },
  ];
  const exs = [
    { row: 'd0', h: bil('“x is an ordinal”', '“x 是序数”'), stmt: 'Ord(x)', where: 'none', M: true, V: true,
      en: 'Δ₀: no witness needed at all. M and V agree, so the ordinals of M are exactly the V-ordinals that lie in M.', zh: 'Δ₀：根本不需要证据。M 与 V 一致，所以 M 的序数恰好是 V 中属于 M 的那些序数。' },
    { row: 's1', h: bil('“ω is countable”', '“ω 可数”'), stmt: '∃f (f: ω ↠ ω)', where: 'M', M: true, V: true,
      en: 'Σ₁ with a witness (the identity) already in M. The same witness works in V: upward absoluteness.', zh: 'Σ₁，证据（恒等映射）已在 M 中；同一个证据在 V 中照样成立：向上绝对。' },
    { row: 's1', h: bil('“ω₁<sup>M</sup> is countable”', '“ω₁<sup>M</sup> 可数”'), stmt: '∃f (f: ω ↠ ω₁ᴹ)', where: 'V', M: false, V: true,
      en: 'Σ₁, and the witness f exists in V (M is countable), but f ∉ M. False in M, true in V. This is allowed, since Σ₁ is only guaranteed to go <i>up</i>.', zh: 'Σ₁，证据 f 在 V 中存在（因为 M 可数），但 f ∉ M。M 中为假、V 中为真。这是允许的，因为 Σ₁ 只保证<i>向上</i>。' },
    { row: 'p1', h: bil('“ω₁<sup>M</sup> is a cardinal”', '“ω₁<sup>M</sup> 是基数”'), stmt: '∀f ∀β∈ω₁ᴹ ¬(f: β ↠ ω₁ᴹ)', where: 'V', M: true, V: false, ce: true,
      en: 'Π₁. M finds no counterexample, so it is true in M. V has a counterexample (a surjection from ω), so it is false in V. Π₁ is only guaranteed to go <i>down</i>.', zh: 'Π₁。M 里找不到反例，所以在 M 中为真；V 里有反例（一个从 ω 出发的满射），所以在 V 中为假。Π₁ 只保证<i>向下</i>。' },
    { row: 'p1', h: bil('“y = 𝒫(ω)” for y = 𝒫(ω)<sup>M</sup>', '“y = 𝒫(ω)”，其中 y = 𝒫(ω)<sup>M</sup>'), stmt: '∀z (z ⊆ ω → z ∈ y)', where: 'V', M: true, V: false, ce: true,
      en: 'Π₁. 𝒫(ω)<sup>M</sup> = 𝒫(ω) ∩ M is countable here, so V contains a subset of ω missing from it: a counterexample outside M.', zh: 'Π₁。这里 𝒫(ω)<sup>M</sup> = 𝒫(ω) ∩ M 是可数的，所以 V 中有一个不在其中的 ω 的子集：一个 M 之外的反例。' },
  ];
  let cur = 2, token = 0;
  const svg = $('ladsvg');
  const tb = $('ladTable');
  tb.innerHTML = `<tr><th>${bil('class', '层级')}</th><th></th><th>${bil('guarantee for transitive M', '对传递 M 的保证')}</th></tr>` +
    rows.map(r => `<tr data-k="${r.k}"><td class="m">${r.cls}</td><td class="${r.c}" style="font-size:20px">${r.arr}</td><td>${bi(r.en, r.zh)}</td></tr>`).join('');
  tb.querySelectorAll('tr[data-k]').forEach(tr => tr.addEventListener('click', () => {
    const i = exs.findIndex(e => e.row === tr.dataset.k);
    if (i >= 0) { cur = i; selIn(btns, btns[i]); paint(); run(); }
    else if (tr.dataset.k === 'd1') okBox($('ladmsg'), bi('Δ₁<sup>ZF</sup> example: “x is finite” has a Σ₁ form and a Π₁ form (§3). If M ⊨ ZF, M proves them equivalent, so the Σ₁ form gives ↑ and the Π₁ form gives ↓. Same for “R is well-founded”, rank, and “y = L_α”.', 'Δ₁<sup>ZF</sup> 的例子：“x 是有限集”既有 Σ₁ 形式也有 Π₁ 形式（§3）。若 M ⊨ ZF，M 能证明两者等价，于是 Σ₁ 形式给出 ↑，Π₁ 形式给出 ↓。“R 良基”、秩、“y = L_α”同理。'), 'ok');
    else okBox($('ladmsg'), bi('Σ₂ example: CH says “∃ a bijection between ω₁ and 𝒫(ω)”, which needs the Π₁ facts “y = 𝒫(ω)” and “z = ω₁” inside a ∃. L ⊨ CH, but a forcing extension can make CH false: no transfer in either direction is guaranteed.', 'Σ₂ 的例子：CH 说“ω₁ 与 𝒫(ω) 之间存在双射”，要在 ∃ 里面用到 Π₁ 事实“y = 𝒫(ω)”和“z = ω₁”。L ⊨ CH，但力迫扩张可以让 CH 为假：任何方向都没有保证。'), 'warn');
  }));
  function paint() { tb.querySelectorAll('tr[data-k]').forEach(tr => tr.classList.toggle('sel', tr.dataset.k === exs[cur].row)); }
  const btns = exs.map((e, i) => {
    const b = document.createElement('button');
    b.className = 'btn small' + (i === cur ? ' sel' : '');
    b.innerHTML = e.h;
    b.addEventListener('click', () => { cur = i; selIn(btns, b); paint(); run(); });
    $('ladEx').appendChild(b);
    return b;
  });
  function base() {
    svg.innerHTML = '';
    el('path', { d: 'M220,330 L20,20 L420,20 Z', fill: '#f1efe7', stroke: '#1f2430', 'stroke-width': 2 }, svg);
    T(svg, 62, 46, 'V', { 'font-size': 20, 'font-weight': 800 });
    el('path', { d: 'M220,330 L150,150 L290,150 Z', fill: 'rgba(174,62,201,.14)', stroke: '#ae3ec9', 'stroke-width': 2.5 }, svg);
    T(svg, 220, 112, 'M: countable, transitive', { 'font-size': 11, fill: '#ae3ec9', 'font-weight': 700, 'text-anchor': 'middle' });
    T(svg, 220, 127, 'M：可数、传递', { 'font-size': 11, fill: '#ae3ec9', 'font-weight': 700, 'text-anchor': 'middle' });
    el('line', { x1: 140, y1: 150, x2: 300, y2: 150, stroke: '#ae3ec9', 'stroke-dasharray': '3 4' }, svg);
    T(svg, 304, 154, 'Ord ∩ M', { 'font-size': 11, fill: '#ae3ec9' });
    T(svg, 225, 40, exs[cur].stmt, { 'text-anchor': 'middle', 'font-size': 13, 'font-weight': 700 });
    const p = el('g', { transform: 'translate(215,250)' }, svg);
    el('circle', { r: 8, fill: '#f08c00' }, p);
    el('line', { x1: 8, y1: 4, x2: 84, y2: 40, stroke: '#9a5a00' }, p);
    T(p, 86, 44, 'parameter · 参数', { 'font-size': 11, fill: '#9a5a00' });
  }
  async function run() {
    const my = ++token;
    base();
    const e = exs[cur];
    clearBox($('ladmsg'));
    const light = el('circle', { cx: 220, cy: 250, r: 5, fill: 'rgba(174,62,201,.18)', stroke: '#ae3ec9' }, svg);
    for (let r = 5; r <= 70; r += 5) { await sleep(35); if (my !== token) return; light.setAttribute('r', r); }
    const mtxt = T(svg, 20, 300, '', { 'font-size': 13, 'font-weight': 800 });
    if (e.where === 'M') {
      star(225, 200, e.ce ? '#e03131' : '#2f9e44');
      T(svg, 240, 204, e.ce ? 'counterexample' : 'witness ∈ M', { 'font-size': 11, fill: '#2f9e44' });
    }
    mtxt.textContent = `M ⊨ φ ? ${e.M ? 'yes · 是' : 'no · 否'}`;
    mtxt.setAttribute('fill', e.M ? '#2f9e44' : '#e03131');
    await sleep(700); if (my !== token) return;
    light.setAttribute('stroke', '#3b5bdb'); light.setAttribute('fill', 'rgba(59,91,219,.08)');
    for (let r = 70; r <= 210; r += 10) { await sleep(30); if (my !== token) return; light.setAttribute('r', r); }
    if (e.where === 'V') {
      star(345, 95, e.ce ? '#e03131' : '#2f9e44');
      T(svg, 330, 80, e.ce ? 'counterexample ∉ M · 反例' : 'witness ∉ M · 证据', { 'font-size': 11, fill: e.ce ? '#e03131' : '#2f9e44', 'font-weight': 700, 'text-anchor': 'end' });
    }
    const vt = T(svg, 20, 320, `V ⊨ φ ? ${e.V ? 'yes · 是' : 'no · 否'}`, { 'font-size': 13, 'font-weight': 800, fill: e.V ? '#2f9e44' : '#e03131' });
    vt.classList.add('fadein');
    okBox($('ladmsg'), bi(e.en, e.zh), e.M === e.V ? 'ok' : 'warn');
  }
  function star(x, y, color) {
    const pts = [];
    for (let i = 0; i < 10; i++) { const r = i % 2 ? 5 : 12, a = -Math.PI / 2 + i * Math.PI / 5; pts.push((x + r * Math.cos(a)).toFixed(1) + ',' + (y + r * Math.sin(a)).toFixed(1)); }
    const s = el('polygon', { points: pts.join(' '), fill: color }, svg);
    s.classList.add('pop');
  }
  paint();
  base();
  CY('cy5', bi('M is transitive and M ⊨ “κ is a cardinal”. May you conclude that κ is a cardinal in V?', 'M 传递且 M ⊨“κ 是基数”。能否推出 κ 在 V 中也是基数？'), [
    { h: bil('Yes, being a cardinal is absolute', '能，“是基数”是绝对的'), why: bi('“Cardinal” is Π₁: ∀f (no surjection from a smaller ordinal). V may have a surjection that M lacks.', '“基数”是 Π₁ 的：∀f（不存在从更小序数出发的满射）。V 可能有 M 没有的满射。') },
    { h: bil('No, only the downward direction is guaranteed', '不能，只保证向下'), ok: true },
  ], bi('Π₁ properties only transfer downward. ω₁<sup>M</sup> for a countable M is the standard counterexample.', 'Π₁ 性质只向下传递。可数 M 的 ω₁<sup>M</sup> 就是标准反例。'));
})();

/* ================= §6 Lévy H_κ ================= */
(function levy() {
  const svg = $('levysvg');
  let kap = 1, token = 0;
  const lvl = { 1: 250, 2: 185, 3: 120 };
  const halfW = { 1: 32, 2: 52, 3: 72 };
  const apex = [380, 345];
  function base() {
    svg.innerHTML = '';
    el('path', { d: `M${apex[0]},${apex[1]} L60,15 L700,15 Z`, fill: '#f6f4ec', stroke: '#1f2430', 'stroke-width': 2 }, svg);
    T(svg, 100, 40, 'V', { 'font-size': 20, 'font-weight': 800 });
    [3, 2, 1].forEach(k => {
      const y = lvl[k], w = halfW[k];
      const on = k === kap;
      el('path', { d: `M${apex[0]},${apex[1]} L${apex[0] - w},${y} L${apex[0] + w},${y} Z`, fill: on ? 'rgba(47,158,68,.22)' : 'rgba(47,158,68,.07)', stroke: '#2f9e44', 'stroke-width': on ? 2.5 : 1 }, svg);
      T(svg, apex[0] + w + 6, y + 4, `H_ω${sub(k)}`, { 'font-size': 12, fill: '#2f9e44', 'font-weight': on ? 800 : 500 });
      const xl = apex[0] - (apex[0] - 60) * (apex[1] - y) / (apex[1] - 15);
      el('line', { x1: xl, y1: y, x2: apex[0] - w - 4, y2: y, stroke: '#bbb', 'stroke-dasharray': '3 4' }, svg);
      T(svg, xl + 4, y - 4, `V_ω${sub(k)}`, { 'font-size': 11, fill: '#888' });
    });
    T(svg, 540, 290, 'H_κ ⊆ V_κ, but much thinner:', { 'font-size': 11, fill: '#555' });
    T(svg, 540, 305, 'only sets with |trcl| < κ', { 'font-size': 11, fill: '#555' });
    T(svg, 540, 320, 'H_κ ⊆ V_κ，但细得多：', { 'font-size': 11, fill: '#555' });
    T(svg, 540, 335, '只含 |trcl| < κ 的集合', { 'font-size': 11, fill: '#555' });
  }
  function dot(x, y, color, r = 5) {
    const g = el('g', {}, svg);
    g.style.transition = 'transform 1.4s cubic-bezier(.3,.8,.3,1)';
    g.style.transform = `translate(${x}px,${y}px)`;
    el('circle', { r, fill: color }, g);
    return g;
  }
  async function run() {
    const my = ++token;
    base();
    const ok = () => my === token;
    const msg = $('levymsg');
    const ps = [[372, 318], [388, 312], [380, 300]].map(([x, y]) => dot(x, y, '#f08c00', 5));
    T(svg, 400, 322, 'p̄ ∈ H_κ', { 'font-size': 12, fill: '#9a5a00', 'font-weight': 700 });
    okBox(msg, bi('Step 1. A Σ₁ fact ∃w ψ(w, p̄) with parameters p̄ ∈ H_κ…', '第 1 步：一个 Σ₁ 事实 ∃w ψ(w, p̄)，参数 p̄ ∈ H_κ……'), 'info');
    await sleep(900); if (!ok()) return;
    const wg = dot(560, 60, '#e03131', 8);
    const wl1 = T(svg, 545, 64, 'w: a witness, maybe of huge rank', { 'font-size': 12, fill: '#e03131', 'font-weight': 700, 'text-anchor': 'end' });
    const wl2 = T(svg, 545, 80, 'w：证据，秩可能极大', { 'font-size': 12, fill: '#e03131', 'text-anchor': 'end' });
    okBox(msg, bi('Step 2. …has a witness w somewhere in V, perhaps far outside H_κ.', '第 2 步：……在 V 的某处有证据 w，可能远在 H_κ 之外。'), 'info');
    await sleep(1200); if (!ok()) return;
    el('path', { d: `M${apex[0]},${apex[1]} L110,40 L650,40 Z`, fill: 'none', stroke: '#3b5bdb', 'stroke-width': 1.5, 'stroke-dasharray': '6 5' }, svg);
    T(svg, 160, 58, 'H_θ (θ large regular)', { 'font-size': 12, fill: '#3b5bdb' });
    const cloud = [[300, 120], [470, 110], [250, 200], [520, 180], [430, 240], [330, 260], [600, 90], [200, 90]];
    const xs = cloud.map(([x, y]) => dot(x, y, '#3b5bdb', 4));
    okBox(msg, bi('Step 3. Löwenheim–Skolem: a hull X ≺ H_θ containing trcl({p̄}) and w (blue dots), with |X| ≤ |trcl({p̄})| + ℵ₀ &lt; κ.', '第 3 步：勒文海姆–斯科伦：取包含 trcl({p̄}) 和 w 的 X ≺ H_θ（蓝点），|X| ≤ |trcl({p̄})| + ℵ₀ &lt; κ。'), 'info');
    await sleep(1500); if (!ok()) return;
    const y = lvl[kap], w = halfW[kap];
    const inside = i => {
      const yy = apex[1] - 20 - (apex[1] - 20 - (y + 12)) * ((i * 37) % 100) / 100;
      const half = w * (apex[1] - yy) / (apex[1] - y) * 0.7;
      return [apex[0] + half * (((i * 53) % 100) / 50 - 1), yy];
    };
    xs.forEach((g, i) => { const [a, b] = inside(i); g.style.transform = `translate(${a}px,${b}px)`; });
    wl1.remove(); wl2.remove();
    const [wx, wy] = [apex[0] + 4, y + 18];
    wg.style.transform = `translate(${wx}px,${wy}px)`;
    okBox(msg, bi('Step 4. Mostowski collapse π: X ≅ N. Points of trcl({p̄}) stay fixed, everything else falls into a transitive N of size &lt; κ, so N ⊆ H_κ.', '第 4 步：莫斯托夫斯基坍塌 π: X ≅ N。trcl({p̄}) 中的点不动，其余都落进大小 &lt; κ 的传递集 N，于是 N ⊆ H_κ。'), 'info');
    await sleep(1600); if (!ok()) return;
    T(svg, wx + 12, wy + 2, 'π(w) ∈ H_κ', { 'font-size': 12, 'font-weight': 800, fill: '#e03131' });
    okBox(msg, bi(`Done: π(w) is a witness inside H_ω${sub(kap)}, so H_ω${sub(kap)} ⊨ ∃w ψ(w, p̄). The witness was <b>shrunk</b>, not merely copied: w itself may be far too big for H_κ.`,
      `完成：π(w) 是 H_ω${sub(kap)} 内部的证据，所以 H_ω${sub(kap)} ⊨ ∃w ψ(w, p̄)。证据是被<b>压缩</b>下来的，而不只是复制：w 本身对 H_κ 来说可能大得多。`), 'ok');
  }
  const kb = [...document.querySelectorAll('[data-kap]')];
  kb.forEach(b => b.addEventListener('click', () => { kap = +b.dataset.kap; selIn(kb, b); token++; base(); }));
  $('levyRun').addEventListener('click', run);
  base();
  okBox($('levymsg'), bi('Press “Run the argument”.', '点击“演示论证”。'), 'info');
  CY('cy6', bi('Where exactly does the proof use that κ is uncountable?', '证明中究竟在哪里用到了 κ 不可数？'), [
    { h: bil('To get |X| ≤ |trcl({p̄})| + ℵ₀ &lt; κ', '为了得到 |X| ≤ |trcl({p̄})| + ℵ₀ &lt; κ'), ok: true },
    { h: bil('To make H_κ transitive', '为了让 H_κ 传递'), why: bi('H_κ is transitive for every κ, including H_ω = V_ω.', '对任何 κ（包括 H_ω = V_ω），H_κ 都是传递的。') },
    { h: bil('To make the Mostowski collapse exist', '为了让莫斯托夫斯基坍塌存在'), why: bi('The collapse exists for any well-founded extensional X.', '对任何良基、外延的 X，坍塌都存在。') },
  ], bi('An elementary submodel is always at least countably infinite, so its size is &lt; κ only if κ &gt; ℵ₀. For κ = ω the statement fails: ∃x (x is a nonzero limit ordinal), i.e. “there is an infinite set”, is Σ₁, true in V, false in V_ω.', '初等子模型至少是可数无穷的，所以只有 κ &gt; ℵ₀ 时其大小才 &lt; κ。κ = ω 时结论不成立：∃x (x 是非零极限序数)，即“存在无穷集”，是 Σ₁ 的，在 V 中为真，在 V_ω 中为假。'));
})();

/* ================= §7 Reflection ================= */
(function reflection() {
  const svg = $('refsvg');
  const apex = [330, 365];
  const y0 = 330, gap0 = 95, ratio = 0.55, yLim = y0 - gap0 / (1 - ratio);
  let k = 0, done = false;
  const yAt = j => y0 - gap0 * (1 - Math.pow(ratio, j)) / (1 - ratio);
  const halfAt = y => (apex[1] - y) * 0.85;
  function base() {
    svg.innerHTML = '';
    arrowDefs(svg, 'refArr', '#e03131');
    el('path', { d: `M${apex[0]},${apex[1]} L${apex[0] - halfAt(10)},10 L${apex[0] + halfAt(10)},10 Z`, fill: '#f6f4ec', stroke: '#1f2430', 'stroke-width': 2 }, svg);
    T(svg, 70, 30, 'V', { 'font-size': 20, 'font-weight': 800 });
    // club strip on the right
    el('line', { x1: 650, y1: 350, x2: 650, y2: 20, stroke: '#999', 'stroke-width': 2 }, svg);
    T(svg, 660, 24, 'Ord', { 'font-size': 12, fill: '#666' });
    T(svg, 600, 368, 'C: reflecting α · 反射点', { 'font-size': 11, fill: '#2f9e44' });
    const cs = [330, 300, 285, 277, 273, 271, 240, 215, 203, 197, 194, 150, 120, 104, 96, 92, 90, 60, 40];
    cs.forEach((y, i) => el('circle', { cx: 650, cy: y, r: [5, 10, 16].includes(i) ? 5 : 3, fill: [5, 10, 16].includes(i) ? '#ae3ec9' : '#2f9e44' }, svg));
    T(svg, 660, 274, '← sup ∈ C', { 'font-size': 10, fill: '#ae3ec9' });
    T(svg, 660, 197, '← closed · 闭', { 'font-size': 10, fill: '#ae3ec9' });
    T(svg, 660, 50, '↑ unbounded', { 'font-size': 10, fill: '#2f9e44' });
    T(svg, 660, 64, '  无界', { 'font-size': 10, fill: '#2f9e44' });
  }
  function level(j, color = '#3b5bdb', label) {
    const y = yAt(j), h = halfAt(y);
    el('line', { x1: apex[0] - h, y1: y, x2: apex[0] + h, y2: y, stroke: color, 'stroke-width': 2 }, svg).classList.add('fadein');
    T(svg, apex[0] + h + 6, y + 4, label || `β${sub(j)}`, { 'font-size': 12, fill: color, 'font-weight': 700 });
  }
  function reset() {
    base(); k = 0; done = false;
    level(0);
    el('path', { d: `M${apex[0]},${apex[1]} L${apex[0] - halfAt(y0)},${y0} L${apex[0] + halfAt(y0)},${y0} Z`, fill: 'rgba(59,91,219,.12)' }, svg);
    $('refStep').disabled = false;
    okBox($('refmsg'), bi('V_β₀ is shaded. Each round asks every ∃-subformula about every parameter tuple in the current level, and raises the level until all witnesses fit.', '阴影是 V_β₀。每一轮，对当前层中的每组参数，问遍每个 ∃-子公式，然后把高度提升到所有证据都放得下为止。'), 'info');
  }
  let rnd = 1;
  const rand = () => { rnd = (rnd * 9301 + 49297) % 233280; return rnd / 233280; };
  async function stepRound() {
    if (done || k >= 6) return;
    const yC = yAt(k), yN = yAt(k + 1);
    const hC = halfAt(yC);
    const pts = [];
    for (let i = 0; i < 5; i++) {
      const py = yC + 8 + rand() * (apex[1] - yC - 30);
      const ph = halfAt(py) * 0.8;
      const px = apex[0] - ph + rand() * 2 * ph;
      const wy = i === 0 ? yN + 3 : yC - 6 - rand() * (yC - yN - 8);
      const wh = halfAt(wy) * 0.85;
      const wx = Math.max(apex[0] - wh, Math.min(apex[0] + wh, px + (rand() - 0.5) * 120));
      pts.push([px, py, wx, wy]);
    }
    for (const [px, py, wx, wy] of pts) {
      el('circle', { cx: px, cy: py, r: 3.5, fill: '#f08c00' }, svg);
      const ln = el('line', { x1: px, y1: py, x2: wx, y2: wy, stroke: '#e03131', 'stroke-width': 1.5, 'marker-end': 'url(#refArr)' }, svg);
      ln.classList.add('fadein');
      el('circle', { cx: wx, cy: wy, r: 3.5, fill: '#e03131' }, svg).classList.add('pop');
      await sleep(160);
    }
    el('path', { d: `M${apex[0] - hC},${yC} L${apex[0] - halfAt(yN)},${yN} L${apex[0] + halfAt(yN)},${yN} L${apex[0] + hC},${yC} Z`, fill: 'rgba(59,91,219,.08)' }, svg);
    k++;
    level(k);
    okBox($('refmsg'), bi(`Round ${k}: parameters (orange) from V_β${sub(k - 1)} have witnesses (red). β${sub(k)} = G(β${sub(k - 1)}) is high enough to contain all of them. New parameters appear in the new layer, so we must go again.`,
      `第 ${k} 轮：V_β${sub(k - 1)} 中的参数（橙点）有证据（红点）。β${sub(k)} = G(β${sub(k - 1)}) 足够高，能装下所有证据。新的一层里又出现新参数，所以还得继续。`), 'info');
    if (k >= 6) $('refStep').disabled = true;
  }
  function takeSup() {
    if (done) return;
    done = true;
    for (let j = k + 1; j < 14; j++) { const y = yAt(j), h = halfAt(y); el('line', { x1: apex[0] - h, y1: y, x2: apex[0] + h, y2: y, stroke: '#3b5bdb', 'stroke-width': 0.8, opacity: 0.5 }, svg); }
    const h = halfAt(yLim);
    el('line', { x1: apex[0] - h, y1: yLim, x2: apex[0] + h, y2: yLim, stroke: '#ae3ec9', 'stroke-width': 4 }, svg).classList.add('fadein');
    el('path', { d: `M${apex[0]},${apex[1]} L${apex[0] - h},${yLim} L${apex[0] + h},${yLim} Z`, fill: 'rgba(174,62,201,.10)', stroke: '#ae3ec9', 'stroke-width': 1.5 }, svg);
    T(svg, apex[0] - h - 8, yLim - 8, 'α = sup βₖ', { 'text-anchor': 'end', 'font-size': 14, fill: '#ae3ec9', 'font-weight': 800 });
    T(svg, apex[0], yLim - 30, 'V_α reflects φ₁ … φ_k', { 'text-anchor': 'middle', 'font-size': 12, fill: '#ae3ec9', 'font-weight': 700 });
    T(svg, apex[0], yLim - 14, 'V_α 反射 φ₁ … φ_k', { 'text-anchor': 'middle', 'font-size': 12, fill: '#ae3ec9', 'font-weight': 700 });
    $('refStep').disabled = true;
    okBox($('refmsg'), bi('The ω-sequence β₀ &lt; β₁ &lt; … converges to a limit α. Any parameter in V_α already appeared in some V_βₖ, and its witnesses are in V_βₖ₊₁ ⊆ V_α. Nothing is left unanswered, which is the Tarski–Vaught criterion for these finitely many formulas.',
      'ω 序列 β₀ &lt; β₁ &lt; … 收敛到极限 α。V_α 中的任何参数早已出现在某个 V_βₖ 中，其证据在 V_βₖ₊₁ ⊆ V_α 中。没有任何问题悬而未答，这正是这有限多个公式的塔斯基–沃特判别条件。'));
  }
  $('refStep').addEventListener('click', stepRound);
  $('refSup').addEventListener('click', takeSup);
  $('refReset').addEventListener('click', () => { rnd = 1; reset(); });
  reset();
  CY('cy7', bi('Which of these is a single theorem of ZF?', '下列哪一个是 ZF 的一条定理？'), [
    { h: '<span class="m">∃α (V_α ≺ V)</span>', why: bi('Not even expressible: it needs a truth predicate for all formulas (Tarski).', '根本无法表达：它需要一个对所有公式都适用的真谓词（塔斯基）。') },
    { h: bil('“C(3) = {α : V_α ≺<sub>Σ₃</sub> V} is club”', '“C(3) = {α : V_α ≺<sub>Σ₃</sub> V} 是闭无界类”'), ok: true },
    { h: bil('“for every n ∈ ω, C(n) is club”', '“对每个 n ∈ ω，C(n) 都是闭无界类”'), why: bi('Here n would be a variable inside the theory, and there is no uniform formula for C(n). You get one theorem per metatheoretic n.', '这里 n 成了理论内部的变量，而 C(n) 没有统一的定义公式。对每个元理论中的 n，各得一条定理。') },
  ], bi('For each fixed n, Sat_{Σₙ} is a formula, so “V_α ≺<sub>Σₙ</sub> V” is a formula and the club statement is one ZF-theorem.', '对每个固定的 n，Sat_{Σₙ} 是一个公式，所以“V_α ≺<sub>Σₙ</sub> V”也是公式，“闭无界”的断言就是 ZF 的一条定理。'));
})();

/* ================= §8 partial truth ================= */
(function truth() {
  const svg = $('satsvg');
  let pick = 2;
  const opts = [1, 2, 3, 'all'];
  const bs = opts.map(o => {
    const b = document.createElement('button');
    b.className = 'btn' + (o === pick ? ' sel' : '');
    b.innerHTML = o === 'all' ? bil('Tr: all formulas?', 'Tr：所有公式？') : `Sat<sub>Σ${sub(o)}</sub>`;
    b.addEventListener('click', () => { pick = o; selIn(bs, b); draw(); });
    $('satBtns').appendChild(b);
    return b;
  });
  function draw() {
    svg.innerHTML = '';
    const L = 6, cw = 92, x0 = 150, yb = 225;
    T(svg, 20, 30, 'formulas by level', { 'font-size': 12, fill: '#666' });
    T(svg, 20, 46, '公式按层级排列', { 'font-size': 12, fill: '#666' });
    const all = pick === 'all';
    const inDom = (m, side) => all || (m === 0) || (side === 'S' && m <= pick) || (side === 'P' && m < pick);
    T(svg, x0 + cw, 62, 'top row Σₘ, bottom row Πₘ · 上行 Σₘ，下行 Πₘ', { 'font-size': 11, fill: '#666' });
    for (let m = 0; m < L; m++) {
      const x = x0 + m * cw;
      const lab = m === L - 1 ? '⋯' : m === 0 ? 'Δ₀' : null;
      if (m === 0) {
        el('rect', { x, y: 70, width: cw - 8, height: 140, rx: 8, fill: inDom(0) ? 'rgba(59,91,219,.20)' : '#f1efe7', stroke: '#3b5bdb' }, svg);
        T(svg, x + (cw - 8) / 2, 145, 'Δ₀', { 'text-anchor': 'middle', 'font-size': 16, 'font-weight': 700 });
        continue;
      }
      ['S', 'P'].forEach((side, j) => {
        const y = 70 + j * 72;
        const on = m < L - 1 ? inDom(m, side) : all;
        el('rect', { x, y, width: cw - 8, height: 66, rx: 8, fill: on ? 'rgba(59,91,219,.20)' : '#f1efe7', stroke: on ? '#3b5bdb' : '#ccc' }, svg);
        T(svg, x + (cw - 8) / 2, y + 39, lab || (side === 'S' ? 'Σ' : 'Π') + sub(m), { 'text-anchor': 'middle', 'font-size': 16, 'font-weight': 700, fill: '#1f2430' });
      });
    }
    T(svg, x0, yb + 12, 'blue = formulas the predicate evaluates correctly · 蓝色 = 该谓词能正确求值的公式', { 'font-size': 11.5, fill: '#3b5bdb' });
    // place the predicate itself and its liar
    let predX, predY, liarX, liarY;
    if (!all) {
      predX = x0 + pick * cw + cw - 26; predY = 90;
      liarX = x0 + pick * cw + cw - 26; liarY = 162;
    } else {
      predX = x0 + 5 * cw + 20; predY = 120; liarX = x0 + 5 * cw + 60; liarY = 190;
    }
    const g = el('g', { class: 'pop' }, svg);
    el('circle', { cx: predX, cy: predY - 4, r: 13, fill: '#2f9e44' }, g);
    T(g, predX, predY + 1, 'S', { 'text-anchor': 'middle', 'font-size': 13, fill: '#fff', 'font-weight': 800 });
    const g2 = el('g', { class: 'pop' }, svg);
    g2.style.animationDelay = '.3s';
    el('circle', { cx: liarX, cy: liarY - 4, r: 13, fill: all ? '#e03131' : '#f08c00' }, g2);
    T(g2, liarX, liarY + 1, 'δ', { 'text-anchor': 'middle', 'font-size': 14, fill: '#fff', 'font-weight': 800 });
    T(svg, 20, 258, 'S = the predicate itself · 谓词本身；  δ ↔ ¬S(⌜δ⌝) = its liar · 它的说谎者', { 'font-size': 11.5, fill: '#555' });
    if (all) okBox($('satmsg'), bi('If Tr evaluated <b>every</b> formula, the liar δ would be inside its domain, so ZF ⊢ δ ↔ Tr(⌜δ⌝) ↔ ¬δ, and ZF would be inconsistent. Hence no such formula exists: Tarski’s undefinability theorem (L13).', '若 Tr 能对<b>所有</b>公式求值，说谎者 δ 就落在其管辖范围内，于是 ZF ⊢ δ ↔ Tr(⌜δ⌝) ↔ ¬δ，ZF 不一致。所以这样的公式不存在：塔斯基不可定义性定理（第 13 课）。'), 'bad');
    else okBox($('satmsg'), bi(`Sat<sub>Σ${sub(pick)}</sub> is itself a Σ${sub(pick)} formula and correctly evaluates everything up to Σ${sub(pick)} (and Π<sub>m</sub> for m &lt; ${pick}). Its liar δ ↔ ¬Sat<sub>Σ${sub(pick)}</sub>(⌜δ⌝) is (equivalent to) a Π${sub(pick)}-type statement, and it cannot be a Σ${sub(pick)} formula, otherwise ZF would be inconsistent. So δ lands outside the blue region, and there is no paradox.`,
      `Sat<sub>Σ${sub(pick)}</sub> 本身是 Σ${sub(pick)} 公式，能对 Σ${sub(pick)} 及以下（以及 m &lt; ${pick} 的 Π<sub>m</sub>）的公式正确求值。它的说谎者 δ ↔ ¬Sat<sub>Σ${sub(pick)}</sub>(⌜δ⌝) 是（等价于）Π${sub(pick)} 型的命题，它不可能是 Σ${sub(pick)} 公式，否则 ZF 不一致。所以 δ 落在蓝色区域之外，没有悖论。`), 'ok');
  }
  draw();
  CY('cy8', bi('By the diagonal lemma there is δ with ZF ⊢ δ ↔ ¬Sat<sub>Σ₂</sub>(⌜δ⌝). Assuming ZF is consistent, what follows?', '由对角线引理，存在 δ 使 ZF ⊢ δ ↔ ¬Sat<sub>Σ₂</sub>(⌜δ⌝)。设 ZF 一致，可以推出什么？'), [
    { h: bil('Sat<sub>Σ₂</sub> cannot be definable', 'Sat<sub>Σ₂</sub> 不可定义'), why: bi('It is definable; we just used it as a formula.', '它是可定义的，我们刚刚就把它当公式用了。') },
    { h: bil('δ is not a Σ₂ formula', 'δ 不是 Σ₂ 公式'), ok: true },
    { h: bil('ZF is inconsistent', 'ZF 不一致'), why: bi('Only if δ were Σ₂, and it is not.', '只有当 δ 是 Σ₂ 公式时才会如此，而它不是。') },
  ], bi('If δ were Σ₂, then Sat<sub>Σ₂</sub>(⌜δ⌝) ↔ δ, giving δ ↔ ¬δ. So the liar escapes the predicate’s domain.', '若 δ 是 Σ₂ 的，则 Sat<sub>Σ₂</sub>(⌜δ⌝) ↔ δ，得 δ ↔ ¬δ。所以说谎者逃出了该谓词的管辖范围。'));
})();

/* ================= §9 Shoenfield tree ================= */
(function shoenfield() {
  const svg = $('shsvg');
  let big = true, token = 0;
  // branch ordinal values (as heights on the axis 0..1 where 1 = ω₁); cutoff = Ord ∩ M (countable M)
  const vals = [0.82, 0.55, 0.7, 0.3, 0.62, 0.45, 0.2];
  const cut = 0.5;
  function base() {
    svg.innerHTML = '';
    el('rect', { x: 520, y: 20, width: 220, height: 320, rx: 12, fill: '#fbfaf6', stroke: '#ddd' }, svg);
    el('line', { x1: 560, y1: 320, x2: 560, y2: 40, stroke: '#1f2430', 'stroke-width': 2 }, svg);
    T(svg, 548, 325, '0', { 'font-size': 12, 'text-anchor': 'end' });
    T(svg, 548, 44, 'ω₁', { 'font-size': 13, 'text-anchor': 'end', 'font-weight': 700 });
    T(svg, 575, 36, 'values of f (ranks)', { 'font-size': 11, fill: '#666' });
    T(svg, 575, 50, 'f 的取值（秩）', { 'font-size': 11, fill: '#666' });
    if (!big) {
      const yc = 320 - cut * 280;
      el('rect', { x: 561, y: 40, width: 175, height: yc - 40, fill: 'rgba(224,49,49,.10)' }, svg);
      el('line', { x1: 552, y1: yc, x2: 736, y2: yc, stroke: '#e03131', 'stroke-width': 2, 'stroke-dasharray': '5 4' }, svg);
      T(svg, 548, yc + 4, 'Ord∩M', { 'font-size': 12, 'text-anchor': 'end', fill: '#e03131', 'font-weight': 700 });
      T(svg, 690, 64, 'invisible to M', { 'font-size': 11, fill: '#e03131', 'text-anchor': 'middle' });
      T(svg, 690, 78, 'M 看不见', { 'font-size': 11, fill: '#e03131', 'text-anchor': 'middle' });
    }
    T(svg, 20, 24, 'S: tree of attempts (x↾n, f↾n) on ω × ω₁', { 'font-size': 12, fill: '#1f2430', 'font-weight': 700 });
    T(svg, 20, 40, 'S：ω × ω₁ 上的“尝试树”', { 'font-size': 12, fill: '#1f2430' });
  }
  async function grow() {
    const my = ++token;
    base();
    const levels = 6, X0 = 260, Y0 = 62, DY = 42;
    const branch = [0];
    let prev = [[X0, Y0, 0]];
    el('circle', { cx: X0, cy: Y0, r: 7, fill: '#1f2430' }, svg);
    let bx = X0, by = Y0;
    for (let d = 1; d <= levels; d++) {
      await sleep(330); if (my !== token) return;
      const cur = [];
      const n = Math.min(2 + d, 7);
      for (let i = 0; i < n; i++) {
        const x = 40 + (i + 0.5) * (440 / n) + (d % 2) * 8;
        const y = Y0 + d * DY;
        const par = prev[Math.min(prev.length - 1, Math.floor(i * prev.length / n))];
        el('line', { x1: par[0], y1: par[1], x2: x, y2: y, stroke: '#c9c4b5', 'stroke-width': 1.5 }, svg).classList.add('fadein');
        const dead = (i + d) % 3 === 0 && i !== Math.floor(n / 2);
        el('circle', { cx: x, cy: y, r: 5, fill: dead ? '#ccc' : '#9aa0aa' }, svg).classList.add('pop');
        cur.push([x, y, i]);
      }
      prev = cur;
    }
    // highlight branch
    let px = X0, py = Y0;
    const pathPts = [];
    for (let d = 1; d <= levels; d++) {
      const n = Math.min(2 + d, 7);
      const x = 40 + (Math.floor(n / 2) + 0.5) * (440 / n) + (d % 2) * 8;
      const y = Y0 + d * DY;
      pathPts.push([px, py, x, y, d]);
      px = x; py = y;
    }
    let invisible = false;
    for (const [a, b, x, y, d] of pathPts) {
      await sleep(320); if (my !== token) return;
      const v = vals[(d - 1) % vals.length];
      const hidden = !big && v > cut;
      if (hidden) invisible = true;
      el('line', { x1: a, y1: b, x2: x, y2: y, stroke: hidden ? '#e03131' : '#ae3ec9', 'stroke-width': 4, 'stroke-dasharray': hidden ? '6 4' : '' }, svg).classList.add('fadein');
      el('circle', { cx: x, cy: y, r: 7, fill: hidden ? '#e03131' : '#ae3ec9' }, svg).classList.add('pop');
      T(svg, x + 10, y - 6, `(x↾${d}, ξ${sub(d)})`, { 'font-size': 11, fill: '#555' });
      const yy = 320 - v * 280;
      el('circle', { cx: 580 + d * 22, cy: yy, r: 5, fill: hidden ? '#e03131' : '#ae3ec9' }, svg).classList.add('pop');
      T(svg, 580 + d * 22, yy - 9, `ξ${sub(d)}`, { 'font-size': 10, 'text-anchor': 'middle', fill: '#555' });
    }
    T(svg, px - 6, py + 30, '⋮  infinite branch (x, f) · 无穷分支', { 'font-size': 12, fill: invisible ? '#e03131' : '#ae3ec9', 'font-weight': 700 });
    if (big) okBox($('shmsg'), bi('The purple branch is a real x together with a rank function f on T_x. It certifies the Σ¹₂ statement. Because ω₁ ⊆ M, every countable piece S_δ of S (values &lt; δ) is computed the same way in M and in V, and “S_δ has an infinite branch” is absolute (well-foundedness is Δ₁<sup>ZF</sup>). So M and V agree, even if the particular branch shown is not in M: M has <i>some</i> branch. (This does not need ω₁<sup>M</sup> = ω₁, which can fail even for M = L.)',
      '紫色分支就是一个实数 x 加上 T_x 上的一个秩函数 f，它证实了这个 Σ¹₂ 命题。因为 ω₁ ⊆ M，S 的每个可数部分 S_δ（取值 &lt; δ）在 M 和 V 中算出来都一样；而“S_δ 有无穷分支”是绝对的（良基性是 Δ₁<sup>ZF</sup> 的）。所以 M 与 V 一致。即使图中这条分支不在 M 里，M 中也一定有<i>某条</i>分支。（这并不需要 ω₁<sup>M</sup> = ω₁；即使 M = L，后者也可能不成立。）'));
    else okBox($('shmsg'), bi('Now M is countable: M only sees attempts whose ordinals lie in M, i.e. are below the countable ordinal Ord ∩ M. This branch uses ranks above Ord ∩ M (red), and if <i>every</i> branch does, every tree S_δ that M can build is well-founded and M ⊨ ¬σ although V ⊨ σ. Example: “some real codes a well-founded model of ZFC” is Σ¹₂. It can be true in V and false in the least countable transitive model of ZFC. Upward absoluteness still holds: a branch M finds is a real branch.',
      '现在 M 可数：M 只看得到所用序数属于 M（即小于可数序数 Ord ∩ M）的尝试。这条分支用到了不低于 Ord ∩ M 的秩（红色）。若<i>每条</i>分支都如此，M 能造出的每棵树 S_δ 都是良基的，于是 M ⊨ ¬σ，而 V ⊨ σ。例子：“某个实数编码了 ZFC 的一个良基模型”是 Σ¹₂ 命题，它可以在 V 中为真，却在 ZFC 最小的可数传递模型中为假。向上绝对性仍然成立：M 找到的分支确实是真分支。'), 'warn');
  }
  const bs = [$('shBig'), $('shSmall')];
  $('shBig').addEventListener('click', () => { big = true; selIn(bs, $('shBig')); grow(); });
  $('shSmall').addEventListener('click', () => { big = false; selIn(bs, $('shSmall')); grow(); });
  $('shGrow').addEventListener('click', grow);
  grow();
  CY('cy9', bi('Can a forcing extension V[G] make a Π¹₂ sentence (without parameters) true that is false in V?', '力迫扩张 V[G] 能否让一个在 V 中为假的（无参数）Π¹₂ 句子变真？'), [
    { h: bil('Yes, forcing changes CH, so it can change this too', '能，力迫能改 CH，也就能改它'), why: bi('CH is not Σ¹₂ / Π¹₂. Shoenfield applies inside V[G] to its inner model V, which contains ω₁<sup>V[G]</sup>.', 'CH 不是 Σ¹₂ / Π¹₂ 的。在 V[G] 内部对其内模型 V 应用舍恩菲尔德定理即可，而 V 包含 ω₁<sup>V[G]</sup>。') },
    { h: bil('No', '不能'), ok: true },
  ], bi('V is a transitive class model of ZF inside V[G] containing all ordinals, so Shoenfield (applied in V[G]) makes every Π¹₂ sentence absolute between V and V[G].', 'V 是 V[G] 中包含全部序数的 ZF 传递类模型，在 V[G] 中应用舍恩菲尔德定理，每个 Π¹₂ 句子在 V 与 V[G] 之间都绝对。'));
})();

/* ================= §10 atlas ================= */
(function atlas() {
  const svg = $('atlas');
  let univ = 'Vw';
  const X = { L: 130, M: 380, R: 630 }, W = 200, H = 46;
  const rowY = { 1: 125, 2: 200, 3: 275 };
  const uname = { Vw: 'V_ω', HC: 'H_ω₁', V: 'V' };
  let cells = {};
  function cell(key, x, y, label, color, h = H, onClick) {
    const g = el('g', { class: 'hcell' }, svg);
    const r = el('rect', { x: x - W / 2, y: y - h / 2, width: W, height: h, rx: 10, fill: '#fff', stroke: color, 'stroke-width': 2 }, g);
    T(g, x, y + 6, label, { 'text-anchor': 'middle', 'font-size': 16, 'font-weight': 700, fill: '#1f2430' });
    g.addEventListener('click', onClick);
    cells[key] = { g, r, x, y, h, color };
  }
  function draw() {
    svg.innerHTML = '';
    cells = {};
    T(svg, X.L, 28, 'Arithmetical · 算术', { 'text-anchor': 'middle', 'font-size': 13, 'font-weight': 700, fill: '#f08c00' });
    T(svg, X.L, 44, 'A ⊆ ω, ∃n ∀m …', { 'text-anchor': 'middle', 'font-size': 11, fill: '#666' });
    T(svg, X.M, 28, `Lévy, over ${uname[univ]} · 列维`, { 'text-anchor': 'middle', 'font-size': 13, 'font-weight': 700, fill: '#ae3ec9' });
    T(svg, X.M, 44, 'unbounded ∃x ∀y over sets', { 'text-anchor': 'middle', 'font-size': 11, fill: '#666' });
    T(svg, X.R, 28, 'Analytical · 分析', { 'text-anchor': 'middle', 'font-size': 13, 'font-weight': 700, fill: '#3b5bdb' });
    T(svg, X.R, 44, 'A ⊆ ω^ω, ∃x∈ω^ω …', { 'text-anchor': 'middle', 'font-size': 11, fill: '#666' });
    cell('R1', X.R, 72, 'Σ¹₁ / Π¹₁', '#3b5bdb', 32, () => show('R', 1));
    [1, 2, 3].forEach(n => {
      cell('L' + n, X.L, rowY[n], `Σ⁰${sub(n)}`, '#f08c00', H, () => show('L', n));
      cell('M' + n, X.M, rowY[n], `Σ${sub(n)}(${uname[univ]})`, '#ae3ec9', H, () => show('M', n));
      cell('R' + (n + 1), X.R, rowY[n], `Σ¹${sub(n + 1)}`, '#3b5bdb', H, () => show('R', n + 1));
    });
    T(svg, 755, 320, 'row n: Σ¹ₙ₊₁ beside Σₙ · 第 n 行：Σ¹ₙ₊₁ 与 Σₙ 并排', { 'text-anchor': 'end', 'font-size': 11, fill: '#3b5bdb' });
    T(svg, X.M, 320, '⋮', { 'text-anchor': 'middle', 'font-size': 16, fill: '#999' });
  }
  function link(a, b, color = '#2f9e44', label = '') {
    const A = cells[a], B = cells[b];
    const x1 = A.x + (B.x > A.x ? W / 2 : -W / 2), x2 = B.x + (B.x > A.x ? -W / 2 : W / 2);
    const ln = el('line', { x1, y1: A.y, x2, y2: B.y, stroke: color, 'stroke-width': 4, 'stroke-dasharray': label === '⊆' ? '6 4' : '' }, svg);
    ln.classList.add('fadein');
    if (label) T(svg, (x1 + x2) / 2, (A.y + B.y) / 2 - 7, label, { 'text-anchor': 'middle', 'font-size': 14, 'font-weight': 800, fill: color });
    [A, B].forEach(c => c.r.setAttribute('fill', '#d3f9d8'));
  }
  function setUniv(u) { univ = u; selIn(ub, ub.find(b => b.dataset.univ === u)); draw(); }
  function show(col, n) {
    draw();
    const m = $('atlasmsg');
    if (col === 'R' && n === 1) {
      cells.R1.r.setAttribute('fill', '#d3f9d8');
      okBox(m, bi('Σ¹₁ and Π¹₁ sit <i>below</i> the correspondence. Both are Δ₁ over H_ω₁ (a Π¹₁ fact is “a tree is well-founded”, i.e. “a rank function exists”), and Δ₁<sup>ZF</sup> over V. That is why they are absolute for every transitive model of ZF (Mostowski absoluteness).',
        'Σ¹₁ 与 Π¹₁ 位于这个对应关系的<i>下方</i>：它们在 H_ω₁ 上都是 Δ₁ 的（Π¹₁ 事实就是“某棵树良基”，即“存在秩函数”），在 V 上则是 Δ₁<sup>ZF</sup> 的。这就是它们对 ZF 的每个传递模型都绝对的原因（莫斯托夫斯基绝对性）。'), 'info');
      return;
    }
    if (col === 'L') { setUniv('Vw'); link('L' + n, 'M' + n, '#2f9e44', '='); okBox(m, bi(`A ⊆ ω is Σ⁰${sub(n)} ⟺ A is Σ${sub(n)}-definable over (V_ω, ∈). V_ω and (ℕ, +, ×) interpret each other (Ackermann coding), and bounded set quantifiers become bounded number quantifiers.`, `A ⊆ ω 是 Σ⁰${sub(n)} 的 ⟺ A 在 (V_ω, ∈) 上 Σ${sub(n)} 可定义。V_ω 与 (ℕ, +, ×) 可以互相解释（阿克曼编码），有界集合量词变成有界数量词。`)); return; }
    if (col === 'R') { setUniv('HC'); link('M' + (n - 1), 'R' + n, '#2f9e44', '='); okBox(m, bi(`A ⊆ ω^ω is Σ¹${sub(n)} ⟺ A is Σ${sub(n - 1)}-definable over (H_ω₁, ∈). Note the shift by one: a real quantifier “∃x ∈ ω^ω” costs a set quantifier, but quantifiers over countable objects inside H_ω₁ absorb one level of real quantification.`, `A ⊆ ω^ω 是 Σ¹${sub(n)} 的 ⟺ A 在 (H_ω₁, ∈) 上 Σ${sub(n - 1)} 可定义。注意错开了一位：H_ω₁ 中对可数对象的量化能吸收一层实数量化。`)); return; }
    // middle column
    if (univ === 'Vw') { link('L' + n, 'M' + n, '#2f9e44', '='); okBox(m, bi(`Over V_ω: Σ${sub(n)}(V_ω) = Σ⁰${sub(n)} (n ≥ 1). Hereditarily finite sets are just natural numbers in disguise.`, `在 V_ω 上：Σ${sub(n)}(V_ω) = Σ⁰${sub(n)}（n ≥ 1）。遗传有限集不过是伪装过的自然数。`)); }
    else if (univ === 'HC') { link('M' + n, 'R' + (n + 1), '#2f9e44', '='); okBox(m, bi(`Over H_ω₁: Σ${sub(n)}(H_ω₁) = Σ¹${sub(n + 1)} for sets of reals (n ≥ 1; no parameters ↔ lightface, parameters ↔ boldface).`, `在 H_ω₁ 上：对实数集，Σ${sub(n)}(H_ω₁) = Σ¹${sub(n + 1)}（n ≥ 1；无参数 ↔ 细体，带参数 ↔ 粗体）。`)); }
    else {
      if (n === 1) {
        link('M1', 'R2', '#2f9e44', '=');
        link('L1', 'M1', '#f08c00', '⊆');
        okBox(m, bi('Over V (ZFC): for sets of reals, Σ₁ over V with parameters in H_ω₁ equals Σ₁ over H_ω₁ (Lévy, §6), which is Σ¹₂. Every arithmetical set, indeed every Σ⁰ₙ set for any n, is Δ₁<sup>ZF</sup> (Δ₀ in the parameter ω), so the whole arithmetical column sits inside level 1 (dashed).',
          '在 V 上（ZFC）：对实数集，V 上以 H_ω₁ 元素为参数的 Σ₁ 等于 H_ω₁ 上的 Σ₁（列维，§6），也就是 Σ¹₂。每个算术集（任意 n 的 Σ⁰ₙ 集）都是 Δ₁<sup>ZF</sup> 的（以 ω 为参数的 Δ₀），所以整列算术层级都在第 1 层之内（虚线）。'));
      } else {
        cells['M' + n].r.setAttribute('fill', '#fff3bf');
        okBox(m, bi(`Over V, Σ${sub(n)} for n ≥ 2 is no longer about reals alone: it can quantify over uncountable sets. CH, “there is an inaccessible”, and “there is a measurable” are all Σ₂ sentences. Since H_ω₁ ⊀<sub>Σ₂</sub> V (E6), there is no analytical counterpart here.`,
          `在 V 上，n ≥ 2 时的 Σ${sub(n)} 不再只谈实数：它可以对不可数集量化。CH、“存在不可达基数”“存在可测基数”都是 Σ₂ 句子。由于 H_ω₁ ⊀<sub>Σ₂</sub> V（E6），这里没有分析层级的对应物。`), 'warn');
      }
    }
  }
  const ub = [...document.querySelectorAll('[data-univ]')];
  ub.forEach(b => b.addEventListener('click', () => { setUniv(b.dataset.univ); clearBox($('atlasmsg')); }));
  draw();
  CY('cy10', bi('Σ¹₃ sets of reals are exactly the sets of reals that are…', 'Σ¹₃ 实数集恰好是那些……的实数集'), [
    { h: bil('Σ₂-definable over H_ω₁', '在 H_ω₁ 上 Σ₂ 可定义'), ok: true },
    { h: bil('Σ₃-definable over H_ω₁', '在 H_ω₁ 上 Σ₃ 可定义'), why: bi('The index shifts: Σ¹ₙ₊₁ ↔ Σₙ(H_ω₁).', '下标要错开：Σ¹ₙ₊₁ ↔ Σₙ(H_ω₁)。') },
    { h: bil('Σ₂-definable over V_ω', '在 V_ω 上 Σ₂ 可定义'), why: bi('Σₙ over V_ω gives arithmetical sets (Σ⁰ₙ) only.', 'V_ω 上的 Σₙ 只给出算术集（Σ⁰ₙ）。') },
  ], bi('Σ¹ₙ₊₁ = Σₙ over H_ω₁ (n ≥ 1), so Σ¹₃ = Σ₂(H_ω₁).', 'Σ¹ₙ₊₁ = H_ω₁ 上的 Σₙ（n ≥ 1），所以 Σ¹₃ = Σ₂(H_ω₁)。'));
})();

/* ================= exercises: generic multiple-choice grid ================= */
function ChoiceGrid(gridId, items, labels, onSolved) {
  const grid = $(gridId);
  const picks = items.map(() => null);
  let revealed = false; // after Show answer, no progress this page session
  const rows = items.map((it, i) => {
    const s = document.createElement('div');
    s.className = 'stmt';
    s.innerHTML = it.s;
    const c = document.createElement('div');
    c.className = 'sel3';
    const bs = (it.labels || labels).map((lab, j) => {
      const b = document.createElement('button');
      b.className = 'btn small';
      b.innerHTML = lab;
      b.addEventListener('click', () => { picks[i] = j; bs.forEach(x => x.classList.remove('sel', 'right', 'wrongc')); b.classList.add('sel'); });
      c.appendChild(b);
      return b;
    });
    grid.appendChild(s); grid.appendChild(c);
    return bs;
  });
  return {
    check(msg) {
      let right = 0;
      rows.forEach((bs, i) => {
        bs.forEach(b => b.classList.remove('right', 'wrongc'));
        if (picks[i] === null) return;
        if (picks[i] === items[i].a) { right++; bs[picks[i]].classList.add('right'); } else bs[picks[i]].classList.add('wrongc');
      });
      if (right === items.length) { okBox(msg, '✓ ' + bi('All correct!', '全对！') + '<br>' + items.map(it => it.why).filter(Boolean).join('<br>')); if (!revealed) onSolved(); }
      else okBox(msg, bi(`${right} / ${items.length} correct. Red = wrong, unmarked = unanswered.`, `答对 ${right} / ${items.length}。红色为错，未标记为未作答。`), 'warn');
    },
    show(msg) {
      revealed = true;
      rows.forEach((bs, i) => { bs.forEach(b => b.classList.remove('sel', 'right', 'wrongc')); bs[items[i].a].classList.add('right'); picks[i] = null; });
      okBox(msg, items.map(it => it.why).filter(Boolean).join('<br>'), 'info');
    },
  };
}

/* E1 */
(function e1() {
  const L = ['Δ₀', 'Δ₁', 'Σ₁', 'Π₁', 'Σ₂', 'Π₂'];
  const items = [
    { s: bil('x is transitive', 'x 是传递集'), a: 0, why: bi('transitive: ∀y∈x ∀z∈y z∈x. Δ₀.', '传递：∀y∈x ∀z∈y z∈x，Δ₀。') },
    { s: bil('x is finite', 'x 是有限集'), a: 1, why: bi('finite: Σ₁ (∃ bijection with some n∈ω) and Π₁ (Tarski-finite). Δ₁<sup>ZF</sup>.', '有限：Σ₁（存在与某个 n∈ω 的双射）且 Π₁（塔斯基有限），Δ₁<sup>ZF</sup>。') },
    { s: bil('x is countable', 'x 可数'), a: 2, why: bi('countable: ∃f (f maps ω onto x, or x = ∅). Σ₁.', '可数：∃f（f 把 ω 映满 x，或 x = ∅），Σ₁。') },
    { s: bil('κ is a cardinal', 'κ 是基数'), a: 3, why: bi('cardinal: ordinal ∧ ∀f ∀β∈κ ¬(f: β ↠ κ). Π₁.', '基数：序数 ∧ ∀f ∀β∈κ ¬(f: β ↠ κ)，Π₁。') },
    { s: '<span class="m">y = 𝒫(x)</span>', a: 3, why: bi('y = 𝒫(x): ∀z (z ⊆ x → z ∈ y) ∧ ∀z∈y (z ⊆ x). Π₁.', 'y = 𝒫(x)：∀z (z ⊆ x → z ∈ y) ∧ ∀z∈y (z ⊆ x)，Π₁。') },
    { s: bil('CH', 'CH（连续统假设）'), a: 4, why: bi('CH: ∃y ∃z ∃f (y = 𝒫(ω) ∧ z = ω₁ ∧ f: z → y bijection). “y = 𝒫(ω)” is Π₁; “z = ω₁” is Π₁ (an uncountable ordinal) ∧ Σ₁ (every β∈z is countable). So the matrix is Σ₂ (indeed Δ₂), and Σ₂ is closed under ∃: Σ₂.', 'CH：∃y ∃z ∃f (y = 𝒫(ω) ∧ z = ω₁ ∧ f: z → y 双射)。“y = 𝒫(ω)”是 Π₁ 的；“z = ω₁”是 Π₁（不可数序数）∧ Σ₁（z 中每个 β 都可数）。所以母式是 Σ₂ 的（其实是 Δ₂），而 Σ₂ 对 ∃ 封闭：Σ₂。') },
    { s: '<span class="m">V = L</span>', a: 5, why: bi('V = L: ∀x ∃α (x ∈ L_α), and “x ∈ L_α” is Δ₁<sup>ZF</sup>: Π₂.', 'V = L：∀x ∃α (x ∈ L_α)，“x ∈ L_α”是 Δ₁<sup>ZF</sup> 的：Π₂。') },
    { s: bil('there is an inaccessible cardinal', '存在不可达基数'), a: 4, why: bi('∃κ (κ inaccessible), and “inaccessible” is Π₁: Σ₂.', '∃κ (κ 不可达)，“不可达”是 Π₁ 的：Σ₂。') },
  ];
  const g = ChoiceGrid('e1grid', items, L, () => Progress.mark('L20E1'));
  $('e1Check').addEventListener('click', () => g.check($('e1msg')));
  $('e1Show').addEventListener('click', () => g.show($('e1msg')));
})();

/* E2 */
(function e2() {
  const L = ['↕ ' + bil('absolute', '绝对'), '↑ ' + bil('only M⇒V', '仅 M⇒V'), '↓ ' + bil('only V⇒M', '仅 V⇒M'), '✗ ' + bil('no guarantee', '无保证')];
  const items = [
    { s: bil('x is an ordinal', 'x 是序数'), a: 0, why: bi('ordinal: Δ₀ → absolute.', '序数：Δ₀ → 绝对。') },
    { s: bil('x is finite', 'x 是有限集'), a: 0, why: bi('finite: Δ₁<sup>ZF</sup> and M ⊨ ZF → absolute.', '有限：Δ₁<sup>ZF</sup> 且 M ⊨ ZF → 绝对。') },
    { s: bil('x is countable', 'x 可数'), a: 1, why: bi('countable: Σ₁ → upward (ω₁<sup>M</sup> shows downward fails).', '可数：Σ₁ → 向上（ω₁<sup>M</sup> 说明向下不成立）。') },
    { s: bil('x is uncountable', 'x 不可数'), a: 2, why: bi('uncountable: Π₁ → downward.', '不可数：Π₁ → 向下。') },
    { s: bil('κ is a cardinal', 'κ 是基数'), a: 2, why: bi('cardinal: Π₁ → downward.', '基数：Π₁ → 向下。') },
    { s: '<span class="m">y = 𝒫(x)</span>', a: 2, why: bi('y = 𝒫(x): Π₁ → downward (𝒫<sup>M</sup>(x) = 𝒫(x) ∩ M).', 'y = 𝒫(x)：Π₁ → 向下（𝒫<sup>M</sup>(x) = 𝒫(x) ∩ M）。') },
    { s: 'CH', a: 3, why: bi('CH: Σ₂. L ⊨ CH while V may not (↑ fails for M = L); a model of ¬CH inside a CH universe breaks ↓.', 'CH：Σ₂。L ⊨ CH 而 V 可能不满足（M = L 时 ↑ 失效）；在满足 CH 的宇宙中取一个 ¬CH 的模型则 ↓ 失效。') },
  ];
  const g = ChoiceGrid('e2grid', items, L, () => Progress.mark('L20E2'));
  $('e2Check').addEventListener('click', () => g.check($('e2msg')));
  $('e2Show').addEventListener('click', () => g.show($('e2msg')));
})();

/* E3 */
(function e3() {
  const items = [
    { h: bil('Con(ZFC)', 'Con(ZFC)'), ok: true, why: bi('arithmetical (Π⁰₁): ω and finite proofs are the same in L and V.', '算术命题（Π⁰₁）：ω 与有限证明在 L 和 V 中都一样。') },
    { h: bil('Goldbach’s conjecture', '哥德巴赫猜想'), ok: true, why: bi('arithmetical: absolute.', '算术命题：绝对。') },
    { h: bil('a given Π¹₂ sentence', '某个给定的 Π¹₂ 句子'), ok: true, why: bi('Shoenfield.', '舍恩菲尔德定理。') },
    { h: bil('a given Σ¹₂(a) sentence with a ∈ L', '某个给定的 Σ¹₂(a) 句子，a ∈ L'), ok: true, why: bi('Shoenfield with a constructible parameter.', '带可构成参数的舍恩菲尔德定理。') },
    { h: bil('“every real is constructible”', '“每个实数都是可构成的”'), ok: false, why: bi('Π¹₃: true in L, false after adding a Cohen real.', 'Π¹₃：在 L 中为真，添加科恩实数后为假。') },
    { h: 'CH', ok: false, why: bi('true in L, can fail in V.', '在 L 中为真，在 V 中可能不成立。') },
    { h: '<span class="m">2^ℵ₀ = ℵ₂</span>', ok: false, why: bi('false in L (GCH holds there), can be true in V.', '在 L 中为假（L 满足 GCH），在 V 中可能为真。') },
  ];
  const box = $('e3list');
  let revealed = false;
  const cbs = items.map(it => {
    const d = document.createElement('label');
    d.className = 'cb';
    d.innerHTML = `<input type="checkbox"><div>${it.h}<div class="why muted" style="font-size:13px;display:none">${it.why}</div></div>`;
    box.appendChild(d);
    return d;
  });
  function mark(reveal) {
    let ok = 0;
    cbs.forEach((d, i) => {
      const inp = d.querySelector('input');
      if (reveal) inp.checked = items[i].ok;
      const good = inp.checked === items[i].ok;
      if (good) ok++;
      d.classList.toggle('right', good);
      d.classList.toggle('wrong', !good);
      d.querySelector('.why').style.display = reveal || good ? 'block' : 'none';
    });
    return ok;
  }
  $('e3Check').addEventListener('click', () => {
    const ok = mark(false);
    if (ok === items.length) { okBox($('e3msg'), '✓ ' + bi('Exactly right. Shoenfield draws the line at Σ¹₂ / Π¹₂.', '完全正确。舍恩菲尔德定理的界线就在 Σ¹₂ / Π¹₂。')); if (!revealed) Progress.mark('L20E3'); }
    else okBox($('e3msg'), bi(`${ok} / ${items.length} lines correct.`, `${ok} / ${items.length} 行正确。`), 'warn');
  });
  $('e3Show').addEventListener('click', () => { revealed = true; mark(true); okBox($('e3msg'), bi('Checked = guaranteed absolute.', '勾选的就是保证绝对的。'), 'info'); });
})();

/* E4 */
(function e4() {
  const steps = [
    bi('Close the finite list of formulas under subformulas.', '把有限公式列对子公式封闭。'),
    bi('For each ∃-subformula ∃y ψ(y, p̄), let F(p̄) be the least γ such that V_γ contains a witness if one exists.', '对每个 ∃-子公式 ∃y ψ(y, p̄)，令 F(p̄) 为最小的 γ，使得只要有证据，V_γ 中就有一个。'),
    bi('By Replacement, G(β) = sup{F(p̄) : p̄ ∈ V_β} is an ordinal.', '由替换公理，G(β) = sup{F(p̄) : p̄ ∈ V_β} 是序数。'),
    bi('Iterate βₖ₊₁ = max(βₖ + 1, G(βₖ)) and let α = sup βₖ.', '迭代 βₖ₊₁ = max(βₖ + 1, G(βₖ))，令 α = sup βₖ。'),
    bi('Verify the Tarski–Vaught condition for V_α and conclude by induction on subformulas.', '验证 V_α 满足塔斯基–沃特条件，再对子公式归纳得出结论。'),
  ];
  const order = [3, 0, 4, 2, 1];
  let picked = [], revealed = false;
  const ul = $('e4list');
  const lis = order.map(i => {
    const li = document.createElement('li');
    li.dataset.i = i;
    li.innerHTML = `<span class="num"></span>${steps[i]}`;
    li.addEventListener('click', () => {
      const pos = picked.indexOf(i);
      if (pos >= 0) picked.splice(pos, 1); else picked.push(i);
      paint();
    });
    ul.appendChild(li);
    return li;
  });
  function paint(res) {
    lis.forEach(li => {
      const i = +li.dataset.i, pos = picked.indexOf(i);
      li.querySelector('.num').textContent = pos >= 0 ? (pos + 1) + '.' : '';
      li.className = pos >= 0 ? 'picked' : '';
      if (res && pos >= 0) li.className = pos === i ? 'right' : 'wrong';
    });
  }
  $('e4Check').addEventListener('click', () => {
    paint(true);
    if (picked.length < steps.length) { okBox($('e4msg'), bi('Pick all five steps first.', '请先把五步都排好。'), 'warn'); return; }
    if (picked.every((v, k) => v === k)) { okBox($('e4msg'), '✓ ' + bi('Correct: close off, measure witness heights, bound them with Replacement, iterate to a limit, verify Tarski–Vaught.', '正确：封闭子公式，度量证据高度，用替换公理取上界，迭代到极限，验证塔斯基–沃特条件。')); if (!revealed) Progress.mark('L20E4'); }
    else okBox($('e4msg'), bi('Some steps are out of place (red). Hint: G is needed before you can iterate it.', '有些步骤位置不对（红色）。提示：要先有 G，才能迭代它。'), 'bad');
  });
  $('e4Reset').addEventListener('click', () => { picked = []; paint(); clearBox($('e4msg')); });
  $('e4Show').addEventListener('click', () => { revealed = true; picked = [0, 1, 2, 3, 4]; paint(true); okBox($('e4msg'), bi('The correct order is shown.', '已显示正确顺序。'), 'info'); });
})();

/* E5 */
(function e5() {
  const L = [bil('True', '对'), bil('False', '错')];
  const items = [
    { s: bil('No forcing extension can change the truth value of Goldbach’s conjecture.', '任何力迫扩张都改变不了哥德巴赫猜想的真值。'), a: 0, why: bi('(1) True: arithmetic is absolute between transitive models with the same ω.', '(1) 对：算术命题在 ω 相同的传递模型之间绝对。') },
    { s: bil('If ZFC + V=L proves a Π¹₂ sentence σ, then ZFC proves σ.', '若 ZFC + V=L 证明了 Π¹₂ 句子 σ，则 ZFC 也证明 σ。'), a: 0, why: bi('(2) True: in ZFC, L ⊨ σ, and Shoenfield transfers σ to V.', '(2) 对：在 ZFC 中有 L ⊨ σ，再由舍恩菲尔德定理把 σ 传到 V。') },
    { s: bil('Forcing can never change the truth value of a Σ¹₃ sentence.', '力迫法永远改变不了 Σ¹₃ 句子的真值。'), a: 1, why: bi('(3) False: “∃ a non-constructible real” is Σ¹₃, false in L and true in L[c] for a Cohen real c.', '(3) 错：“存在不可构成实数”是 Σ¹₃ 的，在 L 中为假，在 L[c]（c 为科恩实数）中为真。') },
    { s: bil('Shoenfield absoluteness holds in both directions for every countable transitive model of ZFC.', '舍恩菲尔德绝对性对 ZFC 的每个可数传递模型都双向成立。'), a: 1, why: bi('(4) False: without ω₁ ⊆ M only upward absoluteness of Σ¹₂ is guaranteed.', '(4) 错：没有 ω₁ ⊆ M 时，只保证 Σ¹₂ 向上绝对。') },
    { s: bil('Every Σ¹₂ sentence (no parameters) true in V is true in L.', '每个在 V 中为真的（无参数）Σ¹₂ 句子在 L 中也为真。'), a: 0, why: bi('(5) True: this is the downward half of Shoenfield, the hard direction.', '(5) 对：这正是舍恩菲尔德定理的向下那一半，也是难的那个方向。') },
    { s: bil('If ZFC is consistent, CH is not ZFC-provably equivalent to any Σ¹₂ sentence.', '若 ZFC 一致，则 CH 不与任何 Σ¹₂ 句子 ZFC-可证等价。'), a: 0, why: bi('(6) True: otherwise L ⊨ CH would push that Σ¹₂ sentence, hence CH, up to every model of ZFC, so ZFC ⊢ CH, contradicting Cohen.', '(6) 对：否则由 L ⊨ CH，那个 Σ¹₂ 句子（从而 CH）会被推到 ZFC 的每个模型中，于是 ZFC ⊢ CH，与科恩的结果矛盾。') },
  ];
  const g = ChoiceGrid('e5grid', items, L, () => Progress.mark('L20E5'));
  $('e5Check').addEventListener('click', () => g.check($('e5msg')));
  $('e5Show').addEventListener('click', () => g.show($('e5msg')));
})();

/* E6 */
(function e6() {
  const items = [
    { s: bil('(a) The natural class of σ is…', '(a) σ 的自然层级是……'), labels: ['Σ₁', 'Π₁', 'Σ₂', 'Π₂'], a: 2, why: bi('(a) ∃x [Π₁ “x is uncountable”]: Σ₂.', '(a) ∃x [Π₁ “x 不可数”]：Σ₂。') },
    { s: bil('(b) Is σ true in V?', '(b) σ 在 V 中成立吗？'), labels: [bil('yes', '是'), bil('no', '否')], a: 0, why: bi('(b) Yes: 𝒫(ω) is uncountable (Cantor).', '(b) 是：𝒫(ω) 不可数（康托尔）。') },
    { s: bil('(c) Is σ true in H_ω₁ (i.e. σ<sup>H_ω₁</sup>)?', '(c) σ 在 H_ω₁ 中成立吗（即 σ<sup>H_ω₁</sup>）？'), labels: [bil('yes', '是'), bil('no', '否')], a: 1, why: bi('(c) No: each x ∈ H_ω₁ is countable, and a surjection f: ω ↠ x is a hereditarily countable set, so f ∈ H_ω₁. Hence H_ω₁ ⊨ “every set is countable”. Conclusion: H_ω₁ ≺<sub>Σ₁</sub> V but H_ω₁ ⊀<sub>Σ₂</sub> V.', '(c) 否：每个 x ∈ H_ω₁ 都可数，满射 f: ω ↠ x 是遗传可数集，所以 f ∈ H_ω₁。于是 H_ω₁ ⊨“每个集合都可数”。结论：H_ω₁ ≺<sub>Σ₁</sub> V，但 H_ω₁ ⊀<sub>Σ₂</sub> V。') },
  ];
  const g = ChoiceGrid('e6grid', items, null, () => Progress.mark('L20E6'));
  $('e6Check').addEventListener('click', () => g.check($('e6msg')));
  $('e6Show').addEventListener('click', () => g.show($('e6msg')));
})();
