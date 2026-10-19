// Lesson 28 interactions: frontiers of model theory, computability & proof theory.
Lang.init();
Progress.paint();

const $ = id => document.getElementById(id);
const okBox = (box, html, kind = 'ok') => { box.className = 'msg ' + kind; box.innerHTML = html; };
const clearBox = box => { box.className = 'msg'; box.innerHTML = ''; };
const C = { ink: '#1f2430', acc: '#3b5bdb', tru: '#2f9e44', fal: '#e03131', meta: '#ae3ec9', gold: '#f08c00', teal: '#0c8599', grey: '#868e96', claim: '#d9480f', line: '#d8d3c4', ind: '#1098ad' };
const ST_TXT = {
  thm: ['THEOREM', '定理'], open: ['OPEN', '未解决'], conj: ['CONJECTURE', '猜想'],
  prog: ['PROGRAM', '研究纲领'], ind: ['INDEPENDENT', '独立'], claim: ['CLAIMED 2026', '新近声称'], ann: ['ANNOUNCED', '已宣布'],
};
const ST = k => `<span class="status st-${k}">${bi(ST_TXT[k][0], ST_TXT[k][1])}</span>`;
const ST_COL = { thm: C.tru, open: C.gold, conj: C.meta, prog: C.acc, ind: C.ind, claim: C.claim, ann: '#e8590c' };
document.querySelectorAll('[data-st]').forEach(e => { const k = e.dataset.st; e.innerHTML = bi(ST_TXT[k][0], ST_TXT[k][1]); });

// SVG text helper
function T(svg, x, y, s, a = {}) {
  const t = el('text', Object.assign({ x, y, 'font-size': 12, fill: C.ink, class: 's' }, a), svg);
  t.textContent = s;
  return t;
}
function T2(svg, x, y, lines, a = {}, lh = 14) { lines.forEach((s, i) => T(svg, x, y + i * lh, s, a)); }

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
// segmented buttons: items [{key, en, zh}], onPick(key)
function segButtons(box, items, onPick, initial) {
  box.innerHTML = '';
  const bs = items.map(it => {
    const b = document.createElement('button');
    b.className = 'btn small';
    b.innerHTML = bil(it.en, it.zh);
    b.addEventListener('click', () => { bs.forEach(x => x.classList.remove('sel')); b.classList.add('sel'); onPick(it.key); });
    box.appendChild(b);
    return b;
  });
  if (initial !== undefined) { const k = items.findIndex(i => i.key === initial); if (k >= 0) { bs[k].classList.add('sel'); onPick(initial); } }
  return bs;
}

/* ================= §1 universe of theories ================= */
(function universe() {
  const svg = $('uniSvg');
  const regions = [
    { k: 'all', x: 20, y: 30, w: 860, h: 475, fill: '#f8f9fa', stroke: '#adb5bd', lab: ['all complete theories · 所有完备理论'], lx: 30, ly: 50 },
    { k: 'ntp2', x: 140, y: 80, w: 630, h: 398, fill: 'rgba(16,152,173,.07)', stroke: C.ind, lab: ['NTP₂'], lx: 150, ly: 100 },
    { k: 'nsop1', x: 40, y: 170, w: 430, h: 308, fill: 'rgba(174,62,201,.07)', stroke: C.meta, lab: ['NSOP₁', '= NSOP₂'], lx: 48, ly: 192 },
    { k: 'simple', x: 140, y: 170, w: 330, h: 306, fill: 'rgba(174,62,201,.09)', stroke: C.meta, lab: ['simple · 简单'], lx: 150, ly: 192 },
    { k: 'nip', x: 320, y: 140, w: 425, h: 336, fill: 'rgba(59,91,219,.09)', stroke: C.acc, lab: ['NIP'], lx: 690, ly: 160 },
    { k: 'stable', x: 320, y: 170, w: 150, h: 306, fill: 'rgba(47,158,68,.16)', stroke: C.tru, lab: ['stable · 稳定'], lx: 328, ly: 190 },
    { k: 'superstable', x: 328, y: 250, w: 134, h: 220, fill: 'rgba(47,158,68,.16)', stroke: C.tru, lab: ['superstable', '超稳定'], lx: 334, ly: 266 },
    { k: 'omega', x: 336, y: 340, w: 118, h: 124, fill: 'rgba(47,158,68,.2)', stroke: C.tru, lab: ['ω-stable · ω-稳定'], lx: 342, ly: 356 },
  ];
  const RINFO = {
    all: ['Every complete first-order theory lives somewhere in this rectangle. Outside all the coloured regions are the “wild” theories, like arithmetic.', '每个完备一阶理论都位于这个矩形中某处。所有彩色区域之外是“狂野”的理论，比如算术。'],
    ntp2: ['<b>NTP₂</b>: no formula φ(x;y) and array (a<sub>ij</sub>) such that each row is k-inconsistent but every path through the array (one entry from each row) is consistent. Contains simple and NIP theories (Shelah). Structure theory developed by Chernikov, Kaplan, Ben Yaacov and others.', '<b>NTP₂</b>：不存在公式 φ(x;y) 与阵列 (a<sub>ij</sub>)，使每一行都 k-不一致、而每条穿过阵列的路径（每行取一个）都一致。它包含简单理论与 NIP 理论（谢拉赫）。结构理论由 Chernikov、Kaplan、Ben Yaacov 等人发展。'],
    nsop1: ['<b>NSOP₁</b>: a tree condition weaker than simplicity. Kaplan–Ramsey (2017–) developed <i>Kim-independence</i>, a replacement for forking. Mutchnik (arXiv 2022; J. Eur. Math. Soc. 2026) proved NSOP₁ = NSOP₂, answering a question of Džamonja–Shelah. Is NSOP₂ = NSOP₃? Open as of 2025; Chernikov\'s August 2026 preprint “SOP₂ = SOP₃” claims yes ' + ST('claim') + '.', '<b>NSOP₁</b>：比简单性弱的一种树条件。Kaplan–Ramsey（2017 起）发展了 <i>Kim-独立性</i>，用以替代分叉。Mutchnik（2022 年 arXiv；2026 年发表于 J. Eur. Math. Soc.）证明 NSOP₁ = NSOP₂，回答了 Džamonja–Shelah 的一个问题。NSOP₂ 是否等于 NSOP₃？以 2025 年为准未解决；Chernikov 2026 年 8 月的预印本《SOP₂ = SOP₃》声称答案是肯定的 ' + ST('claim') + '。'],
    simple: ['<b>Simple</b>: no formula has the tree property (a tree of instances, siblings k-inconsistent, branches consistent). Forking independence is symmetric and transitive (Kim 1998, Kim–Pillay 1997). Examples: random graph, pseudofinite fields.', '<b>简单理论</b>：没有公式具有树性质（一棵由实例组成的树，兄弟节点 k-不一致，每条枝一致）。分叉独立性对称且传递（Kim 1998，Kim–Pillay 1997）。例子：随机图、伪有限域。'],
    nip: ['<b>NIP</b>: no formula has the independence property, equivalently every definable family has finite VC dimension (§5). Examples: o-minimal theories, ℚ<sub>p</sub>, valued fields like ACVF, all stable theories.', '<b>NIP</b>：没有公式具有独立性质，等价地，每个可定义集族的 VC 维有限（§5）。例子：o-极小理论、ℚ<sub>p</sub>、ACVF 这类赋值域，以及所有稳定理论。'],
    stable: ['<b>Stable</b>: no formula has the order property. Equivalently, over every set of size λ there are at most λ types for suitable λ. Forking gives a well-behaved independence notion. Theorem: stable = NIP ∩ simple.', '<b>稳定</b>：没有公式具有序性质。等价地，对适当的 λ，在每个大小为 λ 的集合上至多有 λ 个型。分叉给出性质良好的独立性概念。定理：稳定 = NIP ∩ 简单。'],
    superstable: ['<b>Superstable</b>: stable in every λ ≥ 2<sup>ℵ₀</sup>. The Main Gap is fought on this territory: a superstable theory may still have the maximum number of models, depending on finer properties (DOP, OTOP, depth).', '<b>超稳定</b>：在每个 λ ≥ 2<sup>ℵ₀</sup> 上都稳定。主间隙定理的战场就在这里：超稳定理论仍可能有最多的模型，取决于更精细的性质（DOP、OTOP、深度）。'],
    omega: ['<b>ω-stable</b>: only countably many types over each countable set. Morley rank exists. Every uncountably categorical countable theory is ω-stable (Morley 1965), and has 1 or ℵ₀ countable models (Baldwin–Lachlan 1971).', '<b>ω-稳定</b>：在每个可数集上只有可数多个型。莫利秩存在。每个不可数范畴的可数理论都是 ω-稳定的（莫利 1965），且可数模型个数为 1 或 ℵ₀（Baldwin–Lachlan 1971）。'],
  };
  // props: [stable, NIP, simple, NTP2, NSOP1]
  const TH = [
    { n: 'ACF', x: 372, y: 412, p: [1, 1, 1, 1, 1], en: 'Algebraically closed fields of fixed characteristic. Strongly minimal, hence ω-stable and uncountably categorical: a model is determined by its transcendence degree (Steinitz).', zh: '固定特征的代数闭域。强极小，因而 ω-稳定且不可数范畴：模型由超越次数唯一确定（施泰尼茨）。' },
    { n: 'DCF₀', x: 418, y: 444, p: [1, 1, 1, 1, 1], en: 'Differentially closed fields of characteristic 0. ω-stable (Blum); prime models (differential closures) are unique (Shelah). Used in Hrushovski\'s proof of Mordell–Lang for function fields of characteristic 0 (1996).', zh: '特征 0 的微分闭域。ω-稳定（Blum）；素模型（微分闭包）唯一（谢拉赫）。赫鲁晓夫斯基对特征 0 函数域上莫德尔–朗猜想的证明（1996）用到了它。' },
    { n: '(ℤ,+)', x: 395, y: 300, p: [1, 1, 1, 1, 1], en: 'Superstable but not ω-stable: there are 2<sup>ℵ₀</sup> 1-types (a type fixes the residue mod every n). Every abelian group, indeed every module, has a stable theory.', zh: '超稳定但不是 ω-稳定：有 2<sup>ℵ₀</sup> 个 1-型（一个型要确定模每个 n 的余数）。每个阿贝尔群，乃至每个模，其理论都是稳定的。' },
    { n: 'free group', x: 338, y: 212, p: [1, 1, 1, 1, 1], en: 'Non-abelian free groups: stable but not superstable (Sela 2013), a by-product of the positive solution to Tarski\'s problem that all non-abelian free groups are elementarily equivalent (Sela; Kharlampovich–Myasnikov, 2006).', zh: '非交换自由群：稳定但不超稳定（Sela 2013），这是塔斯基问题（所有非交换自由群初等等价）获得肯定解答（Sela；Kharlampovich–Myasnikov，2006）的副产品。' },
    { n: 'random graph', x: 165, y: 245, p: [0, 0, 1, 1, 1], en: 'The Rado graph: ℵ₀-categorical, simple of SU-rank 1, but E(x; y) has the independence property: for any finite A and S ⊆ A some vertex is adjacent to exactly the vertices in S.', zh: '拉多图：ℵ₀-范畴，SU-秩为 1 的简单理论，但 E(x; y) 有独立性质：对任意有限集 A 与 S ⊆ A，总有一个顶点恰与 S 中的顶点相邻。' },
    { n: 'pseudofinite fields', x: 160, y: 400, p: [0, 0, 1, 1, 1], en: 'Infinite models of the theory of all finite fields (Ax 1968). Supersimple of SU-rank 1 (Hrushovski; Chatzidakis–van den Dries–Macintyre 1992), not NIP.', zh: '所有有限域之理论的无穷模型（Ax 1968）。SU-秩为 1 的超简单理论（赫鲁晓夫斯基；Chatzidakis–van den Dries–Macintyre 1992），不是 NIP。' },
    { n: 'ω-free PAC', x: 90, y: 330, p: [0, 0, 0, 0, 1], en: 'ω-free PAC fields, and vector spaces with a generic bilinear form (Granger): NSOP₁ but not simple. These are the motivating examples of Kaplan–Ramsey\'s Kim-independence.', zh: 'ω-自由 PAC 域，以及带一般双线性型的向量空间（Granger）：NSOP₁ 但不简单。它们是 Kaplan–Ramsey 的 Kim-独立性的出发点。' },
    { n: 'RCF', x: 560, y: 230, p: [0, 1, 0, 1, 0], en: 'Real closed fields (ℝ, +, ·): o-minimal, so NIP; unstable because the order x &lt; y has the order property. Quantifier elimination and decidability: Tarski.', zh: '实闭域 (ℝ, +, ·)：o-极小，因而 NIP；由于序 x &lt; y 有序性质，所以不稳定。量词消去与可判定性：塔斯基。' },
    { n: 'ℚₚ', x: 560, y: 340, p: [0, 1, 0, 1, 0], en: 'The p-adic field: quantifier elimination (Macintyre 1976), NIP, unstable (balls form infinite chains). Decidable (Ax–Kochen, Ershov).', zh: 'p 进数域：量词消去（Macintyre 1976），NIP，不稳定（球构成无穷链）。可判定（Ax–Kochen、Ershov）。' },
    { n: 'DLO', x: 660, y: 420, p: [0, 1, 0, 1, 0], en: 'Dense linear orders without endpoints, e.g. (ℚ, &lt;). ℵ₀-categorical, o-minimal, unstable. The simplest unstable NIP theory.', zh: '无端点稠密线序，如 (ℚ, &lt;)。ℵ₀-范畴、o-极小、不稳定。最简单的不稳定 NIP 理论。' },
    { n: '∏ℚₚ/𝒰', x: 600, y: 112, p: [0, 0, 0, 1, 0], en: 'A non-principal ultraproduct of the p-adic fields: NTP₂ (Chernikov 2014) but neither simple nor NIP (its residue field is pseudofinite, its value group is ordered).', zh: 'p 进数域的非主超积：NTP₂（Chernikov 2014），但既不简单也不是 NIP（剩余域是伪有限域，值群是有序群）。' },
    { n: '(ℤ,+,·)', x: 828, y: 260, p: [0, 0, 0, 0, 0], en: 'Arithmetic. Defines every arithmetical set (Gödel), so it has the order property, the independence property, TP₂, SOP, everything. Undecidable. The far side of every dividing line.', zh: '算术。能定义每个算术集（哥德尔），因而具有序性质、独立性质、TP₂、SOP，应有尽有。不可判定。位于每条分界线的另一侧。' },
  ];
  const PN = ['stable', 'NIP', 'simple', 'NTP₂', 'NSOP₁'];
  const info = $('uniInfo');
  regions.forEach(r => {
    const g = el('g', { class: 'clk' }, svg);
    el('rect', { x: r.x, y: r.y, width: r.w, height: r.h, rx: 14, fill: r.fill, stroke: r.stroke, 'stroke-width': 2 }, g);
    g.addEventListener('click', e => { e.stopPropagation(); okBox(info, bi(RINFO[r.k][0], RINFO[r.k][1]), 'info'); });
  });
  regions.forEach(r => T2(svg, r.lx, r.ly, r.lab, { 'font-size': 12.5, 'font-weight': 700, fill: r.stroke === '#adb5bd' ? C.grey : r.stroke, 'pointer-events': 'none' }));
  T2(svg, 785, 70, ['wild · 狂野', 'IP + SOP + TP₂'], { 'font-size': 12, 'font-weight': 700, fill: C.fal });
  TH.forEach((t, i) => {
    const g = el('g', { class: 'clk pop' }, svg);
    g.style.animationDelay = (i * 0.07) + 's';
    el('circle', { cx: t.x, cy: t.y, r: 8, fill: '#fff', stroke: C.ink, 'stroke-width': 2.5 }, g);
    T(g, t.x + 12, t.y + 4, t.n, { 'font-size': 12.5, 'font-weight': 700 });
    g.addEventListener('click', e => {
      e.stopPropagation();
      svg.querySelectorAll('circle.hl').forEach(c => c.remove());
      el('circle', { cx: t.x, cy: t.y, r: 14, fill: 'none', stroke: C.claim, 'stroke-width': 3, class: 'hl' }, svg);
      const chips = PN.map((p, k) => `<span class="status ${t.p[k] ? 'st-thm' : 'st-open'}" style="background:${t.p[k] ? C.tru : C.fal}">${p} ${t.p[k] ? '✓' : '✗'}</span>`).join(' ');
      okBox(info, `<b>${t.n}</b> &nbsp; ${chips}<br>` + bi(t.en, t.zh), 'info');
    });
  });
  okBox(info, bi('Click any dot (a theory) or any coloured region (a dividing line).', '点击任意圆点（一个理论）或任意彩色区域（一条分界线）。'), 'info');
  checkYourself('cy1', ['T is a complete theory in a countable language, and T has exactly one model of size ℵ₁ up to isomorphism. Must T have exactly one model of size ℵ₅?', 'T 是可数语言中的完备理论，且在同构意义下恰有一个大小为 ℵ₁ 的模型。T 在 ℵ₅ 上一定也只有一个模型吗？'], [
    ['Yes', '是', true],
    ['No', '不一定', false, 'Morley\'s theorem says categoricity in one uncountable cardinal transfers to all of them.', '莫利定理：在一个不可数基数上范畴，就在所有不可数基数上范畴。'],
    ['It depends on CH', '取决于 CH', false, 'No set-theoretic hypothesis is needed: Morley\'s theorem is a theorem of ZFC.', '不需要任何集合论假设：莫利定理是 ZFC 的定理。'],
  ], ['Yes, by Morley\'s theorem (1965). Note that it says nothing about <i>countable</i> models: ACF₀ is uncountably categorical but has ℵ₀ countable models.', '是，由莫利定理（1965）。注意它对<i>可数</i>模型什么也没说：ACF₀ 不可数范畴，却有 ℵ₀ 个可数模型。']);
})();

/* ================= §2 Vaught ================= */
(function vaught() {
  const svg = $('vSvg'), info = $('vInfo');
  let k = 2;
  const placed = [];
  const EX = [
    { key: 'dlo', en: 'DLO', zh: 'DLO', v: '1', why: ['(ℚ, &lt;) is the only countable dense linear order without endpoints (Cantor\'s back-and-forth), so I = 1.', '由康托尔的来回论证，(ℚ, &lt;) 是唯一的可数无端点稠密线序，所以 I = 1。'] },
    { key: 'ehr', en: 'Ehrenfeucht', zh: '埃伦弗赫特例子', v: '3', why: ['(ℚ, &lt;, c₀ &lt; c₁ &lt; …) with increasing constants has exactly 3 countable models: the sup of the cᵢ is missing, or is a limit that is realized, etc. For every n ≥ 3 there are theories with exactly n countable models; exactly 2 is impossible (Vaught).', '带递增常元的 (ℚ, &lt;, c₀ &lt; c₁ &lt; …) 恰有 3 个可数模型（取决于 cᵢ 的上确界的情形）。对每个 n ≥ 3 都有恰好 n 个可数模型的理论；恰好 2 个是不可能的（沃特）。'] },
    { key: 'zs', en: '(ℤ, succ)', zh: '(ℤ, succ)', v: 'a0', why: ['A countable model is a disjoint union of k copies of ℤ, k = 1, 2, …, ℵ₀. So I = ℵ₀.', '可数模型是 k 份 ℤ 的不交并，k = 1, 2, …, ℵ₀。所以 I = ℵ₀。'] },
    { key: 'acf', en: 'ACF₀', zh: 'ACF₀', v: 'a0', why: ['A countable algebraically closed field of characteristic 0 is determined by its transcendence degree 0, 1, 2, …, ℵ₀. So I = ℵ₀.', '特征 0 的可数代数闭域由超越次数 0, 1, 2, …, ℵ₀ 确定。所以 I = ℵ₀。'] },
    { key: 'rcf', en: 'RCF', zh: 'RCF', v: 'c', why: ['RCF has 2<sup>ℵ₀</sup> complete 1-types (one for each cut in the real algebraic numbers). A countable model realizes only countably many types, so 2<sup>ℵ₀</sup> countable models are needed.', 'RCF 有 2<sup>ℵ₀</sup> 个完全 1-型（实代数数的每个分割对应一个）。每个可数模型只实现可数多个型，所以需要 2<sup>ℵ₀</sup> 个可数模型。'] },
    { key: 'ta', en: 'Th(ℕ, +, ·)', zh: 'Th(ℕ, +, ·)', v: 'c', why: ['True arithmetic has 2<sup>ℵ₀</sup> types (any set of primes can be the set of primes dividing a non-standard element), hence 2<sup>ℵ₀</sup> countable models.', '真算术有 2<sup>ℵ₀</sup> 个型（任意一个素数集都可以是某个非标准元的素因子集），因而有 2<sup>ℵ₀</sup> 个可数模型。'] },
  ];
  function xpos(v) {
    if (v === 'a0') return 380;
    if (v === 'c') return 820;
    if (v.startsWith('a')) { const i = +v.slice(1); return 460 + (i - 1) * (300 / Math.max(1, k - 1)); }
    return { 1: 60, 2: 115, 3: 170, 4: 220, 5: 270 }[v];
  }
  function draw() {
    svg.innerHTML = '';
    const Y = 150;
    el('line', { x1: 30, y1: Y, x2: 880, y2: Y, stroke: C.ink, 'stroke-width': 2 }, svg);
    // forbidden zone
    if (k >= 2) {
      el('rect', { x: 400, y: Y - 40, width: 370, height: 80, rx: 10, fill: 'rgba(224,49,49,.08)', stroke: C.fal, 'stroke-dasharray': '6 4' }, svg);
      T(svg, 585, Y + 58, 'conjectured empty · 猜想中为空', { 'text-anchor': 'middle', fill: C.fal, 'font-size': 12, 'font-weight': 700 });
    }
    [1, 2, 3, 4, 5].forEach(n => {
      const x = xpos(String(n));
      el('line', { x1: x, y1: Y - 6, x2: x, y2: Y + 6, stroke: C.ink, 'stroke-width': 2 }, svg);
      T(svg, x, Y + 24, String(n), { 'text-anchor': 'middle', 'font-size': 15, 'font-weight': 700 });
    });
    T(svg, 320, Y + 24, '…', { 'text-anchor': 'middle', 'font-size': 15 });
    // 2 forbidden
    T(svg, 115, Y - 14, '✗', { 'text-anchor': 'middle', fill: C.fal, 'font-size': 20, 'font-weight': 800 });
    T(svg, 115, Y + 44, 'Vaught 1961', { 'text-anchor': 'middle', fill: C.fal, 'font-size': 11 });
    el('line', { x1: 380, y1: Y - 8, x2: 380, y2: Y + 8, stroke: C.ink, 'stroke-width': 3 }, svg);
    T(svg, 380, Y + 26, 'ℵ₀', { 'text-anchor': 'middle', 'font-size': 16, 'font-weight': 800 });
    for (let i = 1; i < k; i++) {
      const x = xpos('a' + i);
      el('line', { x1: x, y1: Y - 8, x2: x, y2: Y + 8, stroke: C.ink, 'stroke-width': 2 }, svg);
      T(svg, x, Y + 26, 'ℵ' + '₀₁₂₃₄'[i], { 'text-anchor': 'middle', 'font-size': 15, 'font-weight': 700 });
      if (i === 1) {
        T(svg, x, Y - 14, '?', { 'text-anchor': 'middle', fill: C.gold, 'font-size': 22, 'font-weight': 800 });
        T2(svg, x, Y - 100, ['the only possible', 'counterexample', '唯一可能的反例'], { 'text-anchor': 'middle', fill: C.gold, 'font-size': 11, 'font-weight': 700 }, 13);
      } else {
        T(svg, x, Y - 14, '✗', { 'text-anchor': 'middle', fill: C.fal, 'font-size': 20, 'font-weight': 800 });
        T(svg, x, Y + 44, 'Morley 1970', { 'text-anchor': 'middle', fill: C.fal, 'font-size': 11 });
      }
    }
    el('line', { x1: 820, y1: Y - 8, x2: 820, y2: Y + 8, stroke: C.ink, 'stroke-width': 3 }, svg);
    T(svg, 820, Y + 26, `2^ℵ₀ = ℵ${'₀₁₂₃₄'[k]}`, { 'text-anchor': 'middle', 'font-size': 15, 'font-weight': 800 });
    T(svg, 30, 22, 'I(T, ℵ₀) = number of countable models · 可数模型个数', { 'font-size': 13, 'font-weight': 700, fill: C.grey });
    // placed examples
    const stack = {};
    placed.forEach(e => {
      const x = xpos(e.v), s = stack[e.v] = (stack[e.v] || 0) + 1;
      const g = el('g', { class: 'pop' }, svg);
      el('circle', { cx: x, cy: Y - 8 - s * 22 + 2, r: 7, fill: C.acc }, g);
      T(g, x + 10, Y - 4 - s * 22 + 2, e.en, { 'font-size': 11.5, 'font-weight': 700, fill: C.acc });
    });
    if (k === 1) okBox(info, bi('<b>CH holds here</b> (2<sup>ℵ₀</sup> = ℵ₁): there is no cardinal strictly between ℵ₀ and 2<sup>ℵ₀</sup>, so the naive form of the conjecture is trivially true. The real question, “ℵ₁ models but no perfect set of them?”, is still open in this universe too.', '<b>这里 CH 成立</b>（2<sup>ℵ₀</sup> = ℵ₁）：ℵ₀ 与 2<sup>ℵ₀</sup> 之间没有基数，所以朴素形式的猜想平凡为真。但真正的问题“有 ℵ₁ 个模型却没有完美集？”在这个宇宙里同样悬而未决。'), 'warn');
    else okBox(info, bi(`Here 2<sup>ℵ₀</sup> = ℵ${'₀₁₂₃₄'[k]}. Morley rules out ${k > 2 ? 'ℵ₂' + (k > 3 ? ', ℵ₃' : '') : 'nothing extra'} in the red zone; only ℵ₁ remains possible, and Vaught's conjecture says it never happens. Click the theory buttons to place examples.`, `这里 2<sup>ℵ₀</sup> = ℵ${'₀₁₂₃₄'[k]}。莫利定理${k > 2 ? '排除了红区中的 ℵ₂' + (k > 3 ? '、ℵ₃' : '') : '在红区中没有额外排除什么'}；只剩 ℵ₁ 可能出现，而沃特猜想说它永远不会出现。点击理论按钮放置例子。`), 'info');
  }
  $('vk').addEventListener('input', () => { k = +$('vk').value; $('vkLab').textContent = '₀₁₂₃₄'[k]; draw(); });
  const box = $('vBtns');
  EX.forEach(e => {
    const b = document.createElement('button');
    b.className = 'btn small';
    b.innerHTML = bil(e.en, e.zh);
    b.addEventListener('click', () => {
      if (!placed.includes(e)) placed.push(e);
      draw();
      okBox(info, `<b>${e.en}</b>: ` + bi(e.why[0], e.why[1]), 'info');
    });
    box.appendChild(b);
  });
  draw();
  checkYourself('cy2', ['Assume CH. Could some theory have exactly ℵ₁ countable models?', '假设 CH。某个理论能恰有 ℵ₁ 个可数模型吗？'], [
    ['No, Morley\'s theorem forbids it', '不能，莫利定理禁止', false, 'Morley allows ℵ₁; it forbids only cardinals strictly between ℵ₁ and 2^ℵ₀.', '莫利定理允许 ℵ₁；它只禁止严格介于 ℵ₁ 与 2^ℵ₀ 之间的基数。'],
    ['Yes, e.g. RCF', '能，比如 RCF', true],
  ], ['Yes: under CH, ℵ₁ = 2<sup>ℵ₀</sup>, and RCF has 2<sup>ℵ₀</sup> = ℵ₁ countable models. That is no counterexample, because RCF has a <i>perfect set</i> of pairwise non-isomorphic countable models. A counterexample would need ℵ₁ models <b>without</b> a perfect set.', '能：在 CH 下 ℵ₁ = 2<sup>ℵ₀</sup>，而 RCF 有 2<sup>ℵ₀</sup> = ℵ₁ 个可数模型。这不是反例，因为 RCF 有一个由两两不同构的可数模型组成的<i>完美集</i>。反例必须有 ℵ₁ 个模型却<b>没有</b>完美集。']);
})();

/* ================= §3 o-minimality ================= */
(function omin() {
  const svg = $('omSvg'), info = $('omInfo');
  const FN = {
    poly: { R: 3.2, f: x => x * x * x - 4 * x, lab: 'x³ − 4x', zeros: [-2, 0, 2], om: true, en: '(ℝ, +, ·): semialgebraic sets. o-minimal by Tarski\'s quantifier elimination. Zero set: 3 points. {f &gt; 0}: 2 intervals.', zh: '(ℝ, +, ·)：半代数集。由塔斯基量词消去，它是 o-极小的。零点集：3 个点。{f &gt; 0}：2 个区间。' },
    exp: { R: 3, f: x => Math.exp(x) - 3 * x, lab: 'eˣ − 3x', om: true, en: 'ℝ<sub>exp</sub>: o-minimal by Wilkie\'s theorem (1996). Zero set: 2 points, as Khovanskii\'s theory of fewnomials predicts in general (finitely many zeros for exponential polynomials).', zh: 'ℝ<sub>exp</sub>：由威尔基定理（1996）是 o-极小的。零点集：2 个点；一般地，Khovanskii 的“少项式”理论保证指数多项式只有有限多个零点。' },
    atan: { R: 6, f: x => Math.atan(x) - x / 3, lab: 'arctan x − x/3', om: true, en: 'arctan on all of ℝ is definable in ℝ<sub>an</sub> (use arctan(1/x) for |x| &gt; 1), which is o-minimal (van den Dries 1986). Zero set: 3 points.', zh: '整个 ℝ 上的 arctan 可在 ℝ<sub>an</sub> 中定义（|x| &gt; 1 时用 arctan(1/x)），而 ℝ<sub>an</sub> 是 o-极小的（van den Dries 1986）。零点集：3 个点。' },
    sin: { R: 40, f: x => Math.sin(x), lab: 'sin x', om: false, en: '(ℝ, +, ·, sin): the zero set of sin is πℤ, infinitely many isolated points, so <b>not</b> o-minimal. Worse, it defines ℤ = {x : sin(πx) = 0}, and then all of arithmetic (Gödel): undecidable, wild.', zh: '(ℝ, +, ·, sin)：sin 的零点集是 πℤ，无穷多个孤立点，所以<b>不是</b> o-极小的。更糟的是，它能定义 ℤ = {x : sin(πx) = 0}，进而定义全部算术（哥德尔）：不可判定，狂野。' },
  };
  function zerosOf(f, R) {
    const z = [], h = R / 20000;
    for (let x = -R; x < R; x += h) { const a = f(x), b = f(x + h); if (a === 0 || a * b < 0) z.push(x + h / 2); }
    return z;
  }
  function draw(key) {
    const F = FN[key];
    svg.innerHTML = '';
    const Rr = F.R, X = x => 450 + x * 420 / Rr, Y = y => 110 - y * 18;
    el('line', { x1: 20, y1: 110, x2: 880, y2: 110, stroke: '#ccc' }, svg);
    el('line', { x1: 450, y1: 10, x2: 450, y2: 200, stroke: '#eee' }, svg);
    let d = '';
    for (let x = -Rr; x <= Rr; x += Rr / 600) { const y = Math.max(-5.5, Math.min(5.5, F.f(x))); d += (d ? 'L' : 'M') + X(x).toFixed(1) + ',' + Y(y).toFixed(1); }
    el('path', { d, fill: 'none', stroke: C.acc, 'stroke-width': 2.5 }, svg);
    T(svg, 30, 26, `y = ${F.lab}   (x ∈ [−${Rr}, ${Rr}])`, { 'font-size': 14, 'font-weight': 700, fill: C.acc });
    // number line of {f>0} and zeros
    const LY = 220;
    el('line', { x1: 20, y1: LY, x2: 880, y2: LY, stroke: C.ink, 'stroke-width': 1.5 }, svg);
    let start = null;
    for (let x = -Rr; x <= Rr * 1.0001; x += Rr / 1500) {
      const pos = F.f(x) > 0;
      if (pos && start === null) start = x;
      if ((!pos || x > Rr * 0.999) && start !== null) { el('rect', { x: X(start), y: LY - 5, width: X(x) - X(start), height: 10, fill: 'rgba(47,158,68,.45)' }, svg); start = null; }
    }
    const zs = zerosOf(F.f, Rr);
    zs.forEach((z, i) => {
      const c = el('circle', { cx: X(z), cy: LY, r: 5, fill: F.om ? C.ink : C.fal, class: 'pop' }, svg);
      c.style.animationDelay = (i * 0.05) + 's';
      el('circle', { cx: X(z), cy: Y(0), r: 4, fill: F.om ? C.ink : C.fal }, svg);
    });
    T(svg, 20, LY + 24, 'on the line: green = {x : f(x) > 0}, dots = {x : f(x) = 0} · 直线上：绿 = {f > 0}，点 = {f = 0}', { 'font-size': 12, fill: C.grey });
    if (!F.om) T(svg, 870, LY - 12, '… ∞ many → not o-minimal · 无穷多 → 非 o-极小', { 'text-anchor': 'end', 'font-size': 12.5, 'font-weight': 700, fill: C.fal });
    okBox(info, (F.om ? '✓ ' : '✗ ') + bi(F.en, F.zh), F.om ? 'ok' : 'bad');
  }
  segButtons($('omBtns'), [
    { key: 'poly', en: 'polynomial', zh: '多项式' }, { key: 'exp', en: 'exponential', zh: '指数' },
    { key: 'atan', en: 'arctan', zh: 'arctan' }, { key: 'sin', en: 'sin on ℝ', zh: 'ℝ 上的 sin' }], draw, 'poly');

  // Pila–Wilkie counting
  const gcd = (a, b) => { a = Math.abs(a); while (b) [a, b] = [b, a % b]; return a; };
  const MAXN = 100;
  const cntM = new Array(MAXN + 1).fill(0);
  const pts = []; // [x, m] for parabola points with |x| <= 3
  for (let b = 1; b <= MAXN; b++) for (let a = -MAXN; a <= MAXN; a++) {
    if (gcd(a, b) !== 1) continue;
    const m = Math.max(Math.abs(a), b);
    cntM[m]++;
    if (Math.abs(a / b) <= 3) pts.push([a / b, m]);
  }
  pts.sort((p, q) => p[1] - q[1]);
  const cum = []; let s = 0;
  for (let m = 0; m <= MAXN; m++) { s += cntM[m]; cum[m] = s; }
  const parab = H => cum[Math.floor(Math.sqrt(H) + 1e-9)];
  const expc = H => 2 * Math.floor(Math.log2(H) + 1e-9) + 1;
  const pw = $('pwSvg');
  function drawPW() {
    const sv = +$('pwS').value, H = Math.round(Math.pow(10, sv / 10));
    $('pwH').textContent = H.toLocaleString('en-US');
    pw.innerHTML = '';
    // plane
    const X = x => 215 + x * 65, Y = y => 270 - y * 28;
    el('line', { x1: 15, y1: 270, x2: 420, y2: 270, stroke: '#ccc' }, pw);
    el('line', { x1: 215, y1: 20, x2: 215, y2: 285, stroke: '#ccc' }, pw);
    let d1 = '', d2 = '';
    for (let x = -3; x <= 3.001; x += 0.02) {
      d1 += (d1 ? 'L' : 'M') + X(x).toFixed(1) + ',' + Y(Math.min(9, x * x)).toFixed(1);
      d2 += (d2 ? 'L' : 'M') + X(x).toFixed(1) + ',' + Y(Math.min(9, Math.pow(2, x))).toFixed(1);
    }
    el('path', { d: d1, fill: 'none', stroke: C.acc, 'stroke-width': 2 }, pw);
    el('path', { d: d2, fill: 'none', stroke: C.claim, 'stroke-width': 2 }, pw);
    const lim = Math.floor(Math.sqrt(H) + 1e-9);
    let drawn = 0;
    for (const [x, m] of pts) { if (m > lim || drawn > 1600) break; el('circle', { cx: X(x), cy: Y(x * x), r: 2, fill: C.acc }, pw); drawn++; }
    for (let n = -3; n <= 3; n++) if (Math.pow(2, Math.abs(n)) <= H) el('circle', { cx: X(n), cy: Y(Math.pow(2, n)), r: 4.5, fill: C.claim }, pw);
    T(pw, 225, 22, 'y = x² (algebraic · 代数)', { fill: C.acc, 'font-size': 12.5, 'font-weight': 700 });
    T(pw, 225, 40, 'y = 2ˣ (transcendental · 超越)', { fill: C.claim, 'font-size': 12.5, 'font-weight': 700 });
    // log-log chart
    const LX = v => 500 + v * 92, LY = v => 260 - v * 46;
    el('line', { x1: 500, y1: 260, x2: 880, y2: 260, stroke: C.ink }, pw);
    el('line', { x1: 500, y1: 20, x2: 500, y2: 260, stroke: C.ink }, pw);
    for (let i = 0; i <= 4; i++) { T(pw, LX(i), 278, '10' + '⁰¹²³⁴'[i], { 'text-anchor': 'middle', 'font-size': 11 }); T(pw, 494, LY(i) + 4, '10' + '⁰¹²³⁴'[i], { 'text-anchor': 'end', 'font-size': 11 }); el('line', { x1: 500, x2: 880, y1: LY(i), y2: LY(i), stroke: '#eee' }, pw); }
    T(pw, 880, 294, 'H', { 'text-anchor': 'end', 'font-size': 12, 'font-weight': 700 });
    T(pw, 506, 16, '# rational points of height ≤ H · 高度 ≤ H 的有理点个数', { 'font-size': 11.5, 'font-weight': 700 });
    let a = '', b = '', g = '';
    for (let v = 0; v <= 4.001; v += 0.05) {
      const h = Math.pow(10, v);
      a += (a ? 'L' : 'M') + LX(v).toFixed(1) + ',' + LY(Math.log10(parab(Math.round(h)))).toFixed(1);
      b += (b ? 'L' : 'M') + LX(v).toFixed(1) + ',' + LY(Math.log10(expc(h))).toFixed(1);
      g += (g ? 'L' : 'M') + LX(v).toFixed(1) + ',' + LY(Math.log10(4 * Math.pow(h, 0.2))).toFixed(1);
    }
    el('path', { d: a, fill: 'none', stroke: C.acc, 'stroke-width': 2.5 }, pw);
    el('path', { d: b, fill: 'none', stroke: C.claim, 'stroke-width': 2.5 }, pw);
    el('path', { d: g, fill: 'none', stroke: C.grey, 'stroke-width': 1.5, 'stroke-dasharray': '5 4' }, pw);
    T(pw, 820, LY(Math.log10(4 * Math.pow(10, 0.8))) + 18, '4·H^0.2', { fill: C.grey, 'font-size': 11 });
    const v0 = sv / 10;
    el('line', { x1: LX(v0), x2: LX(v0), y1: 20, y2: 260, stroke: C.gold, 'stroke-width': 1.5 }, pw);
    const pa = parab(H), pe = expc(H);
    T(pw, LX(v0) + 4, LY(Math.log10(pa)) - 6, String(pa), { fill: C.acc, 'font-size': 12, 'font-weight': 700 });
    T(pw, LX(v0) + 4, LY(Math.log10(pe)) + 16, String(pe), { fill: C.claim, 'font-size': 12, 'font-weight': 700 });
  }
  $('pwS').addEventListener('input', drawPW);
  drawPW();
  checkYourself('cy3', ['Is the structure (ℝ, +, ·, sin) o-minimal?', '结构 (ℝ, +, ·, sin) 是 o-极小的吗？'], [
    ['Yes, because sin is analytic', '是，因为 sin 解析', false, 'Analyticity on all of ℝ is not enough; only restricted analytic functions (on compact boxes) are safe.', '在整个 ℝ 上解析并不够；只有限制在紧致方块上的解析函数才安全。'],
    ['No', '不是', true],
  ], ['No: {x : sin x = 0} = πℤ is an infinite discrete set, not a finite union of points and intervals. (ℝ, +, ·, sin restricted to [0, 1]) is fine, though: it is a reduct of ℝ<sub>an</sub>.', '不是：{x : sin x = 0} = πℤ 是无穷离散集，不是有限多个点与区间之并。不过 (ℝ, +, ·, 限制在 [0, 1] 上的 sin) 没问题：它是 ℝ<sub>an</sub> 的约化。']);
})();

/* ================= §4 exponentiation ================= */
(function expo() {
  const svg = $('exSvg'), info = $('exInfo');
  const N = {
    SC: { x: 110, y: 50, l: ['Schanuel (SC)', '沙努埃尔猜想'], s: 'conj' },
    EPI: { x: 330, y: 50, l: ['e, π alg. independent', 'e、π 代数无关'], s: 'open' },
    EPL: { x: 550, y: 50, l: ['e + π transcendental', 'e + π 是超越数'], s: 'open' },
    LW: { x: 330, y: 130, l: ['Lindemann–Weierstrass', '林德曼–魏尔斯特拉斯'], s: 'thm' },
    RSC: { x: 110, y: 210, l: ['real Schanuel', '实沙努埃尔猜想'], s: 'conj' },
    WIL: { x: 330, y: 210, l: ['ℝₑₓₚ o-minimal (Wilkie)', 'ℝₑₓₚ o-极小（威尔基）'], s: 'thm' },
    DEC: { x: 220, y: 335, l: ['Th(ℝₑₓₚ) decidable', 'Th(ℝₑₓₚ) 可判定'], s: 'open' },
    SEC: { x: 570, y: 170, l: ['strong exp-alg closed', '强指数代数闭'], s: 'conj' },
    EC: { x: 570, y: 260, l: ['ℂₑₓₚ exp-alg closed', 'ℂₑₓₚ 指数代数闭'], s: 'conj' },
    QM: { x: 570, y: 350, l: ['ℂₑₓₚ quasiminimal', 'ℂₑₓₚ 拟极小'], s: 'conj' },
    BEX: { x: 790, y: 170, l: ['Bₑₓₚ exists (Zilber)', 'Bₑₓₚ 存在（齐尔伯）'], s: 'thm' },
    ISO: { x: 790, y: 260, l: ['ℂₑₓₚ ≅ Bₑₓₚ', 'ℂₑₓₚ ≅ Bₑₓₚ'], s: 'conj' },
  };
  const E = [
    ['SC', 'EPI', ''], ['EPI', 'EPL', ''], ['SC', 'LW', 'special case'], ['SC', 'RSC', ''], ['RSC', 'DEC', 'Macintyre–Wilkie'], ['WIL', 'DEC', ''],
    ['SEC', 'EC', ''], ['EC', 'QM', 'Bays–Kirby 2018'], ['SEC', 'ISO', ''], ['BEX', 'ISO', ''], ['ISO', 'QM', ''],
  ];
  const INFO = {
    SC: ['Schanuel\'s conjecture (1960s). Contains essentially all known and conjectured transcendence statements about e and π as special cases.', '沙努埃尔猜想（1960 年代）。关于 e 与 π 的几乎所有已知和猜想中的超越性结论都是它的特例。'],
    EPI: ['Follows from SC with z = (1, 2πi): trdeg ℚ(1, 2πi, e, 1) ≥ 2. Unknown today.', '由 SC 取 z = (1, 2πi) 可得：trdeg ℚ(1, 2πi, e, 1) ≥ 2。今天仍未知。'],
    EPL: ['If e and π are algebraically independent, then e + π is transcendental. Not even its irrationality is known.', '若 e 与 π 代数无关，则 e + π 是超越数。今天连它是否无理都不知道。'],
    LW: ['Lindemann–Weierstrass (1885): if algebraic α₁, …, αₙ are ℚ-linearly independent, then e^α₁, …, e^αₙ are algebraically independent. This is SC for algebraic zᵢ, and it is proved.', '林德曼–魏尔斯特拉斯定理（1885）：若代数数 α₁, …, αₙ 在 ℚ 上线性无关，则 e^α₁, …, e^αₙ 代数无关。这正是 zᵢ 为代数数时的 SC，已被证明。'],
    RSC: ['SC restricted to real z₁, …, zₙ. Implied by SC. This is all Macintyre–Wilkie need.', '限制在实数 z₁, …, zₙ 上的 SC。由 SC 推出。Macintyre–Wilkie 只需要这个。'],
    WIL: ['Wilkie 1996: ℝₑₓₚ is model complete and o-minimal. Model completeness reduces every formula to an existential one; Khovanskii\'s finiteness theorem then gives o-minimality.', '威尔基 1996：ℝₑₓₚ 模型完全且 o-极小。模型完全性把每个公式化归为存在公式；再用 Khovanskii 的有限性定理得到 o-极小性。'],
    DEC: ['Tarski\'s exponential function problem: OPEN. Macintyre–Wilkie 1996: decidable if real SC holds. The difficulty: to decide an existential sentence you must be able to tell whether an exponential polynomial vanishes exactly at some point, and SC gives the bound that makes that search terminate.', '塔斯基指数函数问题：未解决。Macintyre–Wilkie 1996：若实 SC 成立则可判定。难点在于：要判定一个存在句，必须能判断某个指数多项式是否在某点恰好为零；SC 给出的界正好能让这个搜索终止。'],
    SEC: ['“Strong exponential-algebraic closedness”: certain systems of exponential equations have solutions that are generic over any given finite set. Conjectured for ℂₑₓₚ.', '“强指数代数闭性”：某些指数方程组有在任意给定有限集上“一般”的解。对 ℂₑₓₚ 猜想成立。'],
    EC: ['Exponential-algebraic closedness: every “free and rotund” algebraic variety meets the graph of exp. No genericity required. Conjectured for ℂₑₓₚ; partial results are known (to our knowledge, e.g. work of Brownawell–Masser, D\'Aquino–Fornasiero–Terzo, Gallinaro).', '指数代数闭性：每个“自由且饱满”的代数簇都与 exp 的图像相交。不要求一般性。对 ℂₑₓₚ 猜想成立；已有部分结果（据我们所知，如 Brownawell–Masser、D\'Aquino–Fornasiero–Terzo、Gallinaro 的结果）。'],
    QM: ['Zilber\'s quasiminimality conjecture: every definable subset of ℂ in ℂₑₓₚ is countable or co-countable. Bays–Kirby 2018: follows from exponential-algebraic closedness alone. The analogue for complex powers was proved by Gallinaro–Kirby (2023).', '齐尔伯拟极小性猜想：ℂₑₓₚ 中每个可定义的 ℂ 的子集都可数或余可数。Bays–Kirby 2018：仅由指数代数闭性即可推出。复幂函数的类似结论已由 Gallinaro–Kirby 证明（2023）。'],
    BEX: ['Zilber 2005: there is a unique pseudo-exponential field Bₑₓₚ of size continuum; its theory in L<sub>ω₁,ω</sub>(Q) is uncountably categorical and it is quasiminimal. It satisfies SC by construction.', '齐尔伯 2005：存在唯一的连续统大小的伪指数域 Bₑₓₚ；它在 L<sub>ω₁,ω</sub>(Q) 中的理论不可数范畴，且它是拟极小的。它按构造满足 SC。'],
    ISO: ['Zilber\'s conjecture ℂₑₓₚ ≅ Bₑₓₚ. Equivalent to SC + strong exponential-algebraic closedness for ℂₑₓₚ. It would make the complex exponential field “categorical”: a purely algebraic description of ℂₑₓₚ.', '齐尔伯猜想 ℂₑₓₚ ≅ Bₑₓₚ。等价于 SC 加上 ℂₑₓₚ 的强指数代数闭性。若成立，复指数域就是“范畴的”：ℂₑₓₚ 将有纯代数的刻画。'],
  };
  const assume = { SC: false, SEC: false, EC: false };
  function derived() {
    const t = new Set(Object.keys(N).filter(k => N[k].s === 'thm'));
    Object.keys(assume).forEach(k => assume[k] && t.add(k));
    let ch = true;
    while (ch) {
      ch = false;
      const add = k => { if (!t.has(k)) { t.add(k); ch = true; } };
      if (t.has('SC')) { add('EPI'); add('RSC'); }
      if (t.has('EPI')) add('EPL');
      if (t.has('RSC') && t.has('WIL')) add('DEC');
      if (t.has('SEC')) add('EC');
      if (t.has('EC')) add('QM');
      if (t.has('SC') && t.has('SEC')) add('ISO');
      if (t.has('ISO')) add('QM');
    }
    return t;
  }
  function draw() {
    svg.innerHTML = '';
    const t = derived();
    const defs = el('defs', {}, svg);
    const mk = el('marker', { id: 'exArr', viewBox: '0 0 10 10', refX: 9, refY: 5, markerWidth: 7, markerHeight: 7, orient: 'auto' }, defs);
    el('path', { d: 'M0,0 L10,5 L0,10 z', fill: '#868e96' }, mk);
    const W = 100, H = 23;
    E.forEach(([a, b, lab]) => {
      const A = N[a], B = N[b];
      let x1 = A.x, y1 = A.y, x2 = B.x, y2 = B.y;
      const dx = x2 - x1, dy = y2 - y1;
      const sA = Math.min(Math.abs(dx) > 0 ? W / Math.abs(dx) : 1e9, Math.abs(dy) > 0 ? H / Math.abs(dy) : 1e9);
      x1 += dx * sA; y1 += dy * sA; x2 -= dx * sA; y2 -= dy * sA;
      const on = t.has(a) && t.has(b);
      el('line', { x1, y1, x2, y2, stroke: on ? C.claim : '#adb5bd', 'stroke-width': on ? 3 : 2, 'marker-end': 'url(#exArr)', 'stroke-dasharray': lab === 'special case' ? '5 4' : '' }, svg);
      if (lab) T(svg, (x1 + x2) / 2 + 6, (y1 + y2) / 2 - 4, lab, { 'font-size': 11, fill: C.grey, 'font-style': 'italic' });
    });
    Object.entries(N).forEach(([k, n]) => {
      const g = el('g', { class: 'clk' }, svg);
      const isA = assume[k], isT = n.s === 'thm', isD = t.has(k) && !isA && !isT;
      el('rect', { x: n.x - W, y: n.y - H, width: 2 * W, height: 2 * H, rx: 10, fill: isA ? '#f3d9fa' : isT ? C.tru : isD ? '#ffe8cc' : '#fff', stroke: isT ? C.tru : isA ? C.meta : isD ? C.claim : ST_COL[n.s], 'stroke-width': isD || isA ? 3 : 2 }, g);
      T(g, n.x, n.y - 3, n.l[0], { 'text-anchor': 'middle', 'font-size': 12.5, 'font-weight': 700, fill: isT ? '#fff' : C.ink });
      T(g, n.x, n.y + 13, n.l[1] + (isA ? ' (assumed · 假设)' : isD ? ' ⇐ follows · 可推出' : ''), { 'text-anchor': 'middle', 'font-size': 11, fill: isT ? '#fff' : C.grey });
      g.addEventListener('click', () => okBox(info, `${ST(n.s)} ` + bi(INFO[k][0], INFO[k][1]), 'info'));
    });
  }
  const box = $('exBtns');
  [['SC', 'Assume Schanuel', '假设沙努埃尔猜想'], ['EC', 'Assume exp-alg closedness', '假设指数代数闭性'], ['SEC', 'Assume strong exp-alg closedness', '假设强指数代数闭性']].forEach(([k, en, zh]) => {
    const b = document.createElement('button');
    b.className = 'btn small';
    b.innerHTML = bil(en, zh);
    b.addEventListener('click', () => { assume[k] = !assume[k]; b.classList.toggle('sel', assume[k]); draw(); });
    box.appendChild(b);
  });
  draw();
  okBox(info, bi('Green = proved. Toggle assumptions: orange boxes are what would follow. Click any box for details. Note that no assumption makes “Th(ℝ<sub>exp</sub>) decidable” light up except (real) Schanuel.', '绿色 = 已证明。切换假设：橙色框是能推出的结论。点击任意框查看详情。注意：除了（实）沙努埃尔猜想，没有别的假设能让“Th(ℝ<sub>exp</sub>) 可判定”亮起来。'), 'info');

  // trichotomy tiles
  const tri = [
    { h: ['Trivial', '平凡型'], ex: ['pure set', '纯集合'], en: '<b>Trivial</b>: acl(A) = ⋃<sub>a∈A</sub> acl(a). Example: an infinite set with no structure. No interaction between points at all.', zh: '<b>平凡型</b>：acl(A) = ⋃<sub>a∈A</sub> acl(a)。例子：没有任何结构的无穷集合。点与点之间毫无相互作用。' },
    { h: ['Locally modular', '局部模'], ex: ['vector spaces', '向量空间'], en: '<b>Locally modular (group-like)</b>: the geometry behaves like linear algebra; dim(A ∪ B) + dim(A ∩ B) = dim A + dim B for closed sets (after localizing). Hrushovski: a non-trivial locally modular strongly minimal set interprets an infinite group.', zh: '<b>局部模（群型）</b>：几何的行为像线性代数；对闭集（局部化之后）有 dim(A ∪ B) + dim(A ∩ B) = dim A + dim B。赫鲁晓夫斯基：非平凡的局部模强极小集能解释一个无穷群。' },
    { h: ['Field-like', '域型'], ex: ['ACF', '代数闭域'], en: '<b>Field-like</b>: acl is algebraic closure in an algebraically closed field; e.g. curves through two points form a 2-dimensional family. Zilber conjectured (around 1980) that every non-locally-modular strongly minimal set interprets such a field.', zh: '<b>域型</b>：acl 就是代数闭域中的代数闭包；例如过两点的曲线构成二维族。齐尔伯（约 1980 年）猜想：每个非局部模的强极小集都能解释这样一个域。' },
    { h: ['Hrushovski 1993', '赫鲁晓夫斯基 1993'], ex: ['a new strongly minimal set', '新的强极小集'], en: '<b>Counterexample</b> <span class="status st-thm">' + bi('THEOREM', '定理') + '</span>: using a “predimension” amalgamation, Hrushovski built a strongly minimal set that is not locally modular but interprets no infinite group, let alone a field. So the trichotomy fails in general. It holds for Zariski geometries (Hrushovski–Zilber 1996) and for strongly minimal structures interpreted in ACF (restricted trichotomy: Castle 2024 in characteristic 0; all characteristics: Castle–Hasson–Ye, 2024 preprint).', zh: '<b>反例</b> <span class="status st-thm">' + bi('THEOREM', '定理') + '</span>：赫鲁晓夫斯基用“预维数”融合构造了一个强极小集，它不是局部模的，却不能解释任何无穷群，更别说域了。所以三分法一般不成立。它对 Zariski 几何成立（Hrushovski–Zilber 1996），对可在 ACF 中解释的强极小结构也成立（受限三分法：特征 0 为 Castle 2024；所有特征为 Castle–Hasson–Ye 2024 年预印本）。' },
  ];
  const tb = $('triTiles');
  tri.forEach((c, i) => {
    const d = document.createElement('div');
    d.className = 'tile2';
    d.style.borderColor = i === 3 ? C.claim : '';
    d.innerHTML = `<div style="font-weight:800">${bil(c.h[0], c.h[1])}</div><div class="muted">${bil(c.ex[0], c.ex[1])}</div>`;
    d.addEventListener('click', () => { tb.querySelectorAll('.tile2').forEach(x => x.classList.remove('sel')); d.classList.add('sel'); okBox($('triInfo'), bi(c.en, c.zh), 'info'); });
    tb.appendChild(d);
  });
  checkYourself('cy4', ['Which of these is a theorem (as of 2025)?', '下面哪一条是定理（以 2025 年为准）？'], [
    ['Th(ℝₑₓₚ) is decidable', 'Th(ℝₑₓₚ) 可判定', false, 'Only conditionally, on (real) Schanuel.', '只是在（实）沙努埃尔猜想下有条件地成立。'],
    ['ℝₑₓₚ is o-minimal', 'ℝₑₓₚ 是 o-极小的', true],
    ['e + π is transcendental', 'e + π 是超越数', false, 'Would follow from SC; unknown.', '可由 SC 推出；目前未知。'],
    ['ℂₑₓₚ is quasiminimal', 'ℂₑₓₚ 是拟极小的', false, 'Zilber\'s conjecture; reduced by Bays–Kirby to exponential-algebraic closedness, still open.', '齐尔伯猜想；Bays–Kirby 将其归结为指数代数闭性，仍未解决。'],
  ], ['Wilkie\'s theorem (1996). Everything else on this list is open or conditional.', '威尔基定理（1996）。列表里其他各条都是未解决或有条件的。']);
})();

/* ================= §5 VC dimension ================= */
(function vc() {
  const svg = $('vcSvg'), W = 500, H = 340, AY = 170;
  let mode = 'hp', P = [], hover = -1;
  const names = 'ABCDEF';
  function realize(mask) {
    const k = P.length, all = (1 << k) - 1;
    if (mode === 'int') {
      if (mask === 0) return { ok: true };
      const idx = P.map((p, i) => [p.x, i]).sort((a, b) => a[0] - b[0]).map(a => a[1]);
      const ins = idx.map(i => (mask >> i) & 1);
      const f = ins.indexOf(1), l = ins.lastIndexOf(1);
      for (let j = f; j <= l; j++) if (!ins[j]) return { ok: false };
      const xs = idx.map(i => P[i].x);
      const lo = f > 0 ? (xs[f - 1] + xs[f]) / 2 : xs[f] - 15, hi = l < k - 1 ? (xs[l] + xs[l + 1]) / 2 : xs[l] + 15;
      return { ok: true, lo, hi };
    }
    if (mask === 0 || mask === all) return { ok: true, triv: mask };
    for (let s = 0; s < 1440; s++) {
      const th = s / 1440 * 2 * Math.PI, ux = Math.cos(th), uy = Math.sin(th);
      let mn = Infinity, mx = -Infinity;
      P.forEach((p, i) => { const v = p.x * ux + p.y * uy; if ((mask >> i) & 1) mn = Math.min(mn, v); else mx = Math.max(mx, v); });
      if (mn > mx + 1e-6) return { ok: true, ux, uy, t: (mn + mx) / 2 };
    }
    return { ok: false };
  }
  function draw() {
    svg.innerHTML = '';
    if (mode === 'int') {
      el('line', { x1: 10, y1: AY, x2: W - 10, y2: AY, stroke: C.ink, 'stroke-width': 2 }, svg);
      T(svg, 12, 24, 'intervals [a, b] on a line · 直线上的区间', { 'font-size': 12.5, 'font-weight': 700, fill: C.grey });
    } else T(svg, 12, 24, 'half-planes in the plane · 平面中的半平面', { 'font-size': 12.5, 'font-weight': 700, fill: C.grey });
    if (hover >= 0) {
      const r = realize(hover);
      if (r.ok && mode === 'int' && r.lo !== undefined) el('rect', { x: r.lo, y: AY - 14, width: r.hi - r.lo, height: 28, rx: 8, fill: 'rgba(47,158,68,.25)', stroke: C.tru, 'stroke-width': 2 }, svg);
      if (r.ok && mode === 'hp' && r.ux !== undefined) {
        const px = r.t * r.ux, py = r.t * r.uy, dx = -r.uy, dy = r.ux, L = 2000;
        el('polygon', { points: `${px - L * dx},${py - L * dy} ${px + L * dx},${py + L * dy} ${px + L * dx + L * r.ux},${py + L * dy + L * r.uy} ${px - L * dx + L * r.ux},${py - L * dy + L * r.uy}`, fill: 'rgba(47,158,68,.18)' }, svg);
        el('line', { x1: px - L * dx, y1: py - L * dy, x2: px + L * dx, y2: py + L * dy, stroke: C.tru, 'stroke-width': 2.5 }, svg);
      }
      if (r.ok && mode === 'hp' && r.triv !== undefined && r.triv) el('rect', { x: 0, y: 0, width: W, height: H, fill: 'rgba(47,158,68,.12)' }, svg);
    }
    P.forEach((p, i) => {
      const inS = hover >= 0 && ((hover >> i) & 1);
      el('circle', { cx: p.x, cy: p.y, r: 9, fill: inS ? C.tru : '#fff', stroke: C.ink, 'stroke-width': 2.5 }, svg);
      T(svg, p.x, p.y - 14, names[i], { 'text-anchor': 'middle', 'font-size': 13, 'font-weight': 800 });
    });
  }
  function summary() {
    const k = P.length, box = $('vcSubs');
    box.innerHTML = '';
    let r = 0;
    const tot = 1 << k;
    for (let m = 0; m < tot; m++) {
      const ok = realize(m).ok;
      if (ok) r++;
      const s = document.createElement('span');
      s.className = ok ? 'ok' : 'no';
      s.textContent = '{' + [...names.slice(0, k)].filter((_, i) => (m >> i) & 1).join('') + '}';
      s.addEventListener('mouseenter', () => { hover = m; draw(); });
      s.addEventListener('mouseleave', () => { hover = -1; draw(); });
      s.addEventListener('click', () => { hover = m; draw(); });
      box.appendChild(s);
    }
    const d = mode === 'int' ? 2 : 3;
    let ss = 0, c = 1;
    for (let i = 0; i <= d; i++) { ss += c; c = c * (k - i) / (i + 1); }
    if (!k) { okBox($('vcSummary'), bi('Click inside the box to place points.', '在框内点击放置点。'), 'info'); return; }
    okBox($('vcSummary'), bi(`${k} point${k > 1 ? 's' : ''}: the family cuts out <b>${r}</b> of the 2<sup>${k}</sup> = ${tot} subsets. ${r === tot ? '<b>Shattered!</b>' : 'Not shattered (red subsets are impossible).'}<br>Sauer–Shelah bound with d = ${d}: Σ<sub>i≤${d}</sub> C(${k}, i) = ${ss}.`,
      `${k} 个点：该集族切出了 2<sup>${k}</sup> = ${tot} 个子集中的 <b>${r}</b> 个。${r === tot ? '<b>被打散了！</b>' : '没有被打散（红色子集切不出来）。'}<br>d = ${d} 时的 Sauer–Shelah 上界：Σ<sub>i≤${d}</sub> C(${k}, i) = ${ss}。`), r === tot ? 'ok' : 'info');
  }
  svg.addEventListener('click', e => {
    if (P.length >= 6) return;
    const pt = svg.createSVGPoint(); pt.x = e.clientX; pt.y = e.clientY;
    const q = pt.matrixTransform(svg.getScreenCTM().inverse());
    P.push({ x: q.x, y: mode === 'int' ? AY : q.y });
    draw(); summary();
  });
  function reset(m, empty) {
    mode = m; hover = -1;
    P = empty ? [] : m === 'int' ? [{ x: 120, y: AY }, { x: 250, y: AY }, { x: 380, y: AY }] : [{ x: 150, y: 250 }, { x: 330, y: 260 }, { x: 240, y: 90 }];
    draw(); summary();
  }
  segButtons($('vcMode'), [{ key: 'int', en: 'intervals on ℝ', zh: 'ℝ 上的区间' }, { key: 'hp', en: 'half-planes in ℝ²', zh: 'ℝ² 中的半平面' }], reset, 'hp');
  $('vcClear').addEventListener('click', () => reset(mode, true));
  $('vcRand').addEventListener('click', () => {
    P = [];
    const n = mode === 'int' ? 3 : 4;
    for (let i = 0; i < n; i++) P.push({ x: 60 + Math.random() * 380, y: mode === 'int' ? AY : 60 + Math.random() * 240 });
    hover = -1; draw(); summary();
  });
  checkYourself('cy5', ['What is the VC dimension of half-planes in ℝ²?', 'ℝ² 中半平面族的 VC 维是多少？'], [
    ['2', '2', false, 'Three points in general position (a triangle) are shattered. Try it above.', '处于一般位置的三点（三角形）可以被打散。在上面试试。'],
    ['3', '3', true], ['4', '4', false, 'No 4 points are shattered: either one is inside the triangle of the other three, or they form a convex quadrilateral and the two diagonals cannot be separated (Radon).', '没有 4 点集能被打散：要么一点在另三点的三角形内，要么四点构成凸四边形，两条对角线的端点无法分开（Radon 定理）。'],
  ], ['3. A triangle is shattered, and no 4 points are (Radon\'s theorem: any 4 points in the plane split into two parts whose convex hulls meet). In ℝⁿ half-spaces have VC dimension n + 1.', '3。三角形能被打散，而没有 4 点集能被打散（Radon 定理：平面上任意 4 点可分成两部分，其凸包相交）。在 ℝⁿ 中半空间族的 VC 维是 n + 1。']);
})();

/* ================= §6 Hilbert's 10th ================= */
(function h10() {
  const svg = $('h10Svg'), info = $('h10Info');
  const EQ = {
    pell: { lab: 'x² − 2y² = 1', f: (x, y) => x * x - 2 * y * y === 1, en: 'Pell\'s equation: infinitely many solutions (3, 2), (17, 12), (99, 70), …, all found by the search eventually.', zh: '佩尔方程：有无穷多组解 (3, 2), (17, 12), (99, 70), …，搜索迟早都能找到。' },
    c25: { lab: 'x² + y² = 25', f: (x, y) => x * x + y * y === 25, en: '12 solutions on a circle. Found quickly.', zh: '圆上的 12 组解。很快就找到。' },
    s3: { lab: 'x² + y² = 3', f: (x, y) => x * x + y * y === 3, en: 'The search finds nothing, but it could never <i>conclude</i> that. A proof does: squares are 0 or 1 mod 4, so x² + y² ∈ {0, 1, 2} mod 4, never 3. (There are no rational solutions either.)', zh: '搜索什么也找不到，但它永远无法<i>断定</i>这一点。证明可以：平方数模 4 余 0 或 1，所以 x² + y² 模 4 只能是 0、1、2，不会是 3。（有理解也不存在。）' },
    m3: { lab: 'x² − 3y² = −1', f: (x, y) => x * x - 3 * y * y === -1, en: 'No solutions: mod 3 this says x² ≡ 2, but squares mod 3 are 0 or 1. Again the search alone cannot tell.', zh: '无解：模 3 后变成 x² ≡ 2，而平方数模 3 只能是 0 或 1。同样，单靠搜索无法得知。' },
  };
  let cur = 'pell', tok = 0;
  const R = 40, CS = 3.2, OX = 20, OY = 14;
  function grid() {
    svg.innerHTML = '';
    el('rect', { x: OX, y: OY, width: (2 * R + 1) * CS, height: (2 * R + 1) * CS, fill: '#f1efe7' }, svg);
    el('line', { x1: OX + R * CS + CS / 2, x2: OX + R * CS + CS / 2, y1: OY, y2: OY + (2 * R + 1) * CS, stroke: '#ccc' }, svg);
    el('line', { y1: OY + R * CS + CS / 2, y2: OY + R * CS + CS / 2, x1: OX, x2: OX + (2 * R + 1) * CS, stroke: '#ccc' }, svg);
    T(svg, 320, 30, EQ[cur].lab, { 'font-size': 22, 'font-weight': 800, fill: C.acc });
  }
  async function run() {
    const my = ++tok;
    grid();
    const E = EQ[cur];
    const g = el('g', {}, svg), sol = el('g', {}, svg);
    const status = T(svg, 320, 70, '', { 'font-size': 15, 'font-weight': 700 });
    const ring = el('rect', { fill: 'none', stroke: C.gold, 'stroke-width': 2 }, svg);
    let found = 0;
    for (let r = 0; r <= R; r++) {
      if (my !== tok) return;
      for (let x = -r; x <= r; x++) for (let y = -r; y <= r; y++) {
        if (Math.max(Math.abs(x), Math.abs(y)) !== r) continue;
        if (E.f(x, y)) {
          found++;
          el('circle', { cx: OX + (x + R) * CS + CS / 2, cy: OY + (R - y) * CS + CS / 2, r: 4.5, fill: C.tru, class: 'pop' }, sol);
        }
      }
      g.innerHTML = '';
      el('rect', { x: OX + (R - r) * CS, y: OY + (R - r) * CS, width: (2 * r + 1) * CS, height: (2 * r + 1) * CS, fill: 'rgba(59,91,219,.16)' }, g);
      ring.setAttribute('x', OX + (R - r) * CS); ring.setAttribute('y', OY + (R - r) * CS);
      ring.setAttribute('width', (2 * r + 1) * CS); ring.setAttribute('height', (2 * r + 1) * CS);
      status.textContent = `|x|, |y| ≤ ${r}: ${found} solution(s) found · 找到 ${found} 组解`;
      status.setAttribute('fill', found ? C.tru : C.ink);
      await sleep(45);
    }
    if (my !== tok) return;
    T2(svg, 320, 110, found
      ? ['Search says YES as soon as it finds one.', '一旦找到解，搜索就能回答“有”。']
      : ['Nothing up to 40. Does a solution exist further out?', '到 40 为止一无所获。更远处有解吗？', 'The search alone can never answer “no”.', '单靠搜索永远无法回答“没有”。'], { 'font-size': 14, fill: found ? C.tru : C.fal, 'font-weight': 700 }, 22);
    T2(svg, 320, 220, ['MRDP: no single algorithm answers “no” correctly', 'for every equation over ℤ. · MRDP：不存在对ℤ上', '所有方程都能正确回答“无解”的统一算法。'], { 'font-size': 12.5, fill: C.grey }, 17);
    okBox(info, bi(E.en, E.zh), found ? 'ok' : 'warn');
  }
  segButtons($('h10Eq'), Object.entries(EQ).map(([k, e]) => ({ key: k, en: e.lab, zh: e.lab })), k => { cur = k; tok++; grid(); clearBox(info); });
  $('h10Eq').querySelector('button').classList.add('sel');
  grid();
  $('h10Go').addEventListener('click', run);
  setTimeout(run, 400);

  const rings = [
    { r: 'ℤ', s: 'thm', d: false, en: 'Undecidable: MRDP (Davis–Putnam–Robinson 1961, Matiyasevich 1970). Even with a fixed small number of variables (e.g. 11 over ℤ, Sun 2021; 9 over ℕ, Matiyasevich–Jones).', zh: '不可判定：MRDP（Davis–Putnam–Robinson 1961，马季亚谢维奇 1970）。即使固定很少的变量个数也不可判定（如 ℤ 上 11 个变量，孙智伟 2021；ℕ 上 9 个变量，马季亚谢维奇–Jones）。' },
    { r: '𝒪<sub>K</sub>', s: 'thm', d: false, en: 'Rings of integers of number fields, e.g. ℤ[i], ℤ[√2], ℤ[∛2]: undecidable for every number field K (Koymans–Pagano, arXiv 2024, J. Amer. Math. Soc. 2026; Alpöge–Bhargava–Ho–Shnidman, arXiv 2025, Invent. Math. 2026). Before that only many special families were known (Denef, Pheidas, Shlapentokh, Videla, …).', zh: '数域的整数环，如 ℤ[i]、ℤ[√2]、ℤ[∛2]：对每个数域 K 都不可判定（Koymans–Pagano，2024 年 arXiv，2026 年发表于 J. Amer. Math. Soc.；Alpöge–Bhargava–Ho–Shnidman，2025 年 arXiv，2026 年发表于 Invent. Math.）。此前只知道许多特殊族（Denef、Pheidas、Shlapentokh、Videla 等）。' },
    { r: 'ℚ', s: 'open', claim: true, d: null, en: 'OPEN as of 2025. An AI-generated manuscript in OpenAI\'s release (dated 24 Sept 2026, revised 6 Oct) claims undecidability. It has no Lean formalization and has not been refereed or independently verified (a follow-up preprint by Z.-W. Sun, Oct 2026, already builds on it). The natural route, defining ℤ existentially in ℚ, is blocked if Mazur\'s conjecture holds; Koenigsmann (2016) showed ℤ is universally definable in ℚ, which is not enough.', zh: '以 2025 年为准未解决。OpenAI 公布的一篇 AI 生成手稿（注明日期 2026 年 9 月 24 日，10 月 6 日修订）声称不可判定。它没有 Lean 形式化，也未经审稿或独立核实（孙智伟 2026 年 10 月的后续预印本已以其为基础）。最自然的路线是在 ℚ 中存在定义 ℤ，但若马祖尔猜想成立，这条路就走不通；Koenigsmann（2016）证明 ℤ 在 ℚ 中可全称定义，但这还不够。' },
    { r: 'ℝ, ℂ', s: 'thm', d: true, en: 'Decidable (for integer or algebraic coefficients): Tarski\'s quantifier elimination for real closed and algebraically closed fields decides the whole first-order theory, not just equations.', zh: '可判定（系数为整数或代数数时）：塔斯基对实闭域和代数闭域的量词消去可以判定整个一阶理论，不仅仅是方程。' },
    { r: 'ℚₚ', s: 'thm', d: true, en: 'Decidable: the full first-order theory of ℚₚ is decidable (Ax–Kochen, Ershov 1965).', zh: '可判定：ℚₚ 的完整一阶理论可判定（Ax–Kochen、Ershov 1965）。' },
    { r: '𝔽<sub>q</sub>(t)', s: 'thm', d: false, en: 'Undecidable: Pheidas 1991 (q odd), Videla 1994 (q even).', zh: '不可判定：Pheidas 1991（q 奇），Videla 1994（q 偶）。' },
    { r: 'ℝ(t)', s: 'thm', d: false, en: 'Undecidable: Denef 1978 (any formally real constant field).', zh: '不可判定：Denef 1978（任意形式实常数域）。' },
    { r: 'ℂ(t₁, t₂)', s: 'thm', d: false, en: 'Undecidable: Kim–Roush 1992; Eisenträger extended to function fields of varieties of dimension ≥ 2 over ℂ.', zh: '不可判定：Kim–Roush 1992；Eisenträger 推广到 ℂ 上维数 ≥ 2 的簇的函数域。' },
    { r: 'ℂ(t)', s: 'open', d: null, en: 'OPEN (to our knowledge, as of 2025). One variable over an algebraically closed field: the known methods (rank-one elliptic curves, non-closed constant fields) do not apply.', zh: '未解决（据我们所知，以 2025 年为准）。代数闭域上的单变量函数域：已知方法（秩一椭圆曲线、非代数闭的常数域）都用不上。' },
  ];
  const tb = $('ringTiles');
  rings.forEach(r => {
    const d = document.createElement('div');
    d.className = 'tile2';
    d.style.borderColor = r.d === true ? C.tru : r.d === false ? C.fal : C.gold;
    d.innerHTML = `<div class="ring">${r.r}</div><div style="font-size:13px">${r.d === true ? bil('decidable', '可判定') : r.d === false ? bil('undecidable', '不可判定') : bil('unknown', '未知')}</div>`;
    d.addEventListener('click', () => {
      tb.querySelectorAll('.tile2').forEach(x => x.classList.remove('sel')); d.classList.add('sel');
      okBox($('ringInfo'), `<b class="m">${r.r}</b> ${ST(r.s)}${r.claim ? ST('claim') : ''}<br>` + bi(r.en, r.zh), 'info');
    });
    tb.appendChild(d);
  });
  checkYourself('cy6', ['For which ring is “does this integer polynomial equation have a solution in R?” decidable?', '对哪个环，“这个整系数多项式方程在 R 中有解吗？”是可判定的？'], [
    ['ℤ[i]', 'ℤ[i]', false, 'ℤ[i] is the ring of integers of ℚ(i); undecidable (already Denef 1975 for this case).', 'ℤ[i] 是 ℚ(i) 的整数环；不可判定（这个情形 Denef 1975 已解决）。'],
    ['ℂ', 'ℂ', true],
    ['ℚ', 'ℚ', false, 'Unknown as of 2025 (claimed undecidable in 2026).', '以 2025 年为准未知（2026 年有人声称不可判定）。'],
  ], ['ℂ: a system of polynomial equations has a complex solution unless 1 is in the ideal it generates (Nullstellensatz), which Gröbner bases or Tarski\'s quantifier elimination can check.', 'ℂ：多项式方程组有复数解，除非 1 属于它们生成的理想（零点定理），而这可以用 Gröbner 基或塔斯基量词消去来检验。']);
})();

/* ================= §7 Turing degrees ================= */
(function turing() {
  const svg = $('tdSvg'), info = $('tdInfo');
  const N = {
    z: { x: 215, y: 370, l: '0', en: '<b>0</b>, the degree of the computable sets: the least element. Fixed by every automorphism.', zh: '<b>0</b>，可计算集的度：最小元。每个自同构都固定它。' },
    a: { x: 120, y: 290, l: 'a', en: '<b>a</b> and <b>b</b>: incomparable degrees below 0′ (Kleene–Post 1954; even c.e. ones, Friedberg–Muchnik 1956). Locally they look interchangeable. Is there an automorphism moving a? As of 2025: unknown. Slaman–Woodin: any automorphism is induced by an arithmetic function and determined by finitely many values. A 2026 AI-generated manuscript (OpenAI, with a Lean formalization) claims that no automorphism moves any degree ' + ST('claim') + '.', zh: '<b>a</b> 与 <b>b</b>：0′ 之下互不可比的度（Kleene–Post 1954；甚至可以是可计算可枚举的，Friedberg–Muchnik 1956）。局部看起来可以互换。有没有自同构移动 a？以 2025 年为准：未知。Slaman–Woodin：任何自同构都由某个算术函数诱导，且由有限多个值决定。2026 年一篇 AI 生成的手稿（OpenAI，附 Lean 形式化）声称没有任何自同构移动任何度 ' + ST('claim') + '。' },
    b: { x: 310, y: 290, l: 'b', en: 'See <b>a</b>.', zh: '见 <b>a</b>。' },
    m: { x: 50, y: 320, l: 'm', en: '<b>m</b>: a minimal degree (Spector 1956): nothing strictly between 0 and m. Being minimal is definable, so automorphisms send minimal degrees to minimal degrees, but there are 2<sup>ℵ₀</sup> of them.', zh: '<b>m</b>：极小度（Spector 1956）：0 与 m 之间严格地什么也没有。“极小”是可定义的，所以自同构把极小度映到极小度，但极小度有 2<sup>ℵ₀</sup> 个。' },
    ab: { x: 215, y: 230, l: 'a∨b', en: '<b>a ∨ b</b>: the join (least upper bound) exists for any two degrees; meets need not exist, so 𝒟 is an upper semilattice, not a lattice (Lachlan, Lerman).', zh: '<b>a ∨ b</b>：任意两个度的并（最小上界）都存在；交不一定存在，所以 𝒟 是上半格而不是格。' },
    j1: { x: 215, y: 170, l: "0′", en: '<b>0′</b>, the halting problem. Definable in 𝒟, since the jump is definable (Shore–Slaman 1999): fixed by every automorphism.', zh: '<b>0′</b>，停机问题。由于跳跃在 𝒟 中可定义（Shore–Slaman 1999），它被每个自同构固定。' },
    j2: { x: 215, y: 110, l: "0″", en: '<b>0″</b>. Slaman–Woodin: every automorphism fixes every degree ≥ 0″ (the shaded cone).', zh: '<b>0″</b>。Slaman–Woodin：每个自同构都固定每个 ≥ 0″ 的度（阴影锥）。' },
    j3: { x: 215, y: 50, l: "0‴", en: 'Inside the rigid cone.', zh: '位于刚性锥内。' },
  };
  const E = [['z', 'a'], ['z', 'b'], ['z', 'm'], ['a', 'ab'], ['b', 'ab'], ['ab', 'j1'], ['j1', 'j2'], ['j2', 'j3']];
  let swapped = false;
  function draw() {
    svg.innerHTML = '';
    el('polygon', { points: '215,92 20,8 410,8', fill: 'rgba(47,158,68,.14)', stroke: C.tru, 'stroke-dasharray': '5 4' }, svg);
    T(svg, 300, 26, 'rigid cone · 刚性锥', { 'font-size': 12, fill: C.tru, 'font-weight': 700 });
    const pos = k => (swapped && k === 'a') ? N.b : (swapped && k === 'b') ? N.a : N[k];
    E.forEach(([u, v]) => { const A = N[u], B = N[v]; el('line', { x1: A.x, y1: A.y, x2: B.x, y2: B.y, stroke: '#adb5bd', 'stroke-width': 2 }, svg); });
    T(svg, 215, 200, 'jump · 跳跃 ↑', { 'text-anchor': 'middle', 'font-size': 10.5, fill: C.grey });
    Object.entries(N).forEach(([k, n]) => {
      const p = pos(k);
      const g = el('g', { class: 'clk', transform: `translate(${p.x},${p.y})` }, svg);
      g.style.transition = 'transform .8s';
      const fixed = ['z', 'j1', 'j2', 'j3'].includes(k);
      el('circle', { r: 17, fill: fixed ? C.tru : '#fff', stroke: fixed ? C.tru : C.ink, 'stroke-width': 2.5 }, g);
      T(g, 0, 5, n.l, { 'text-anchor': 'middle', 'font-size': 13, 'font-weight': 800, fill: fixed ? '#fff' : C.ink });
      g.addEventListener('click', () => okBox(info, bi(n.en, n.zh), 'info'));
    });
    const bt = el('g', { class: 'clk' }, svg);
    el('rect', { x: 290, y: 345, width: 130, height: 40, rx: 10, fill: C.gold }, bt);
    T2(bt, 355, 362, [swapped ? 'undo swap · 撤销' : 'swap a ↔ b ?', swapped ? '' : '交换 a ↔ b ?'], { 'text-anchor': 'middle', 'font-size': 12, 'font-weight': 700, fill: '#fff' });
    bt.addEventListener('click', () => {
      swapped = !swapped; draw();
      if (swapped) okBox(info, bi('You moved a and b. Their relations to 0, a∨b and 0′ are preserved, so this picture can\'t tell. But an automorphism must preserve ≤<sub>T</sub> with <i>all</i> 2<sup>ℵ₀</sup> degrees. Slaman–Woodin showed it must fix the cone above 0″ and be induced by an arithmetic function. Whether a non-trivial automorphism exists was the <b>rigidity problem</b> ' + ST('open') + ' (as of 2025). In 2026 an AI-generated manuscript (OpenAI) claimed that none exists, with a Lean formalization and an exposition by A. Marks; it is not yet refereed ' + ST('claim') + '.', '你交换了 a 和 b。它们与 0、a∨b、0′ 的关系都保持不变，所以这张小图看不出问题。但自同构必须保持与<i>全部</i> 2<sup>ℵ₀</sup> 个度的 ≤<sub>T</sub> 关系。Slaman–Woodin 证明它必须固定 0″ 以上的锥，并且由某个算术函数诱导。是否存在非平凡自同构，就是<b>刚性问题</b> ' + ST('open') + '（以 2025 年为准）。2026 年一篇 AI 生成的手稿（OpenAI）声称不存在，附有 Lean 形式化，A. Marks 也写了阐释；它尚未经过审稿 ' + ST('claim') + '。'), 'warn');
    });
  }
  draw();

  // Martin
  const ms = $('mcSvg');
  const F = [
    { k: 'c', lab: 'x ↦ 0′', h: () => 250, col: C.grey, en: '<b>Constant</b> (up to ≡<sub>T</sub>): the first alternative of Part I.', zh: '<b>常数函数</b>（在 ≡<sub>T</sub> 意义下）：(I) 的第一种情形。' },
    { k: 'id', lab: 'x ↦ x', h: x => 290 - 0.8 * x, col: C.acc, en: '<b>Identity</b>: the bottom of the hierarchy of functions with f(x) ≥<sub>T</sub> x.', zh: '<b>恒等函数</b>：满足 f(x) ≥<sub>T</sub> x 的函数层级的最底层。' },
    { k: 'id2', lab: 'x ↦ x ⊕ 0′', h: x => 290 - 0.8 * x, col: C.acc, dash: true, en: '<b>x ⊕ 0′</b> looks new, but on the cone above 0′ we have x ⊕ 0′ ≡<sub>T</sub> x. Martin\'s conjecture only cares about behaviour on a cone, so this is the identity again.', zh: '<b>x ⊕ 0′</b> 看似新函数，但在 0′ 以上的锥上 x ⊕ 0′ ≡<sub>T</sub> x。马丁猜想只关心在某个锥上的行为，所以它仍是恒等函数。' },
    { k: 'j', lab: "x ↦ x′", h: x => 252 - x * 0.8, col: C.meta, en: '<b>The jump</b>: the successor of the identity in the Martin order (Part II).', zh: '<b>跳跃</b>：在马丁序中是恒等函数的后继（(II)）。' },
    { k: 'jj', lab: "x ↦ x″", h: x => 214 - x * 0.8, col: C.meta, en: '<b>Double jump</b>: the next successor. Then x‴, …', zh: '<b>二次跳跃</b>：再下一个后继。然后是 x‴, …' },
    { k: 'jw', lab: 'x ↦ x⁽ω⁾', h: x => 170 - x * 0.62, col: C.claim, en: '<b>ω-jump</b>: a limit stage. The conjecture says the natural functions above the identity are exactly the transfinite jumps (and are well-ordered by growth on a cone).', zh: '<b>ω 次跳跃</b>：极限阶段。猜想说：恒等函数之上的自然函数恰好是各个超限跳跃（并按在锥上的增长良序排列）。' },
    { k: 'inc', lab: 'x ↦ “some y | x”', h: null, col: C.fal, en: '<b>Pick a degree incomparable with x.</b> With the axiom of choice such a Turing-invariant f exists. It is neither constant on a cone nor ≥ the identity on a cone, so Part I predicts that no such f exists under AD, i.e. no “definable” one.', zh: '<b>选一个与 x 不可比的度。</b>借助选择公理，这样的图灵不变函数存在。它在任何锥上既不是常数，也不 ≥ 恒等函数，所以 (I) 预言：在 AD 下不存在这样的 f，也就是说不存在“可定义”的这种函数。' },
  ];
  let sel = 'id';
  function drawM() {
    ms.innerHTML = '';
    el('line', { x1: 40, y1: 300, x2: 420, y2: 300, stroke: C.ink }, ms);
    el('line', { x1: 40, y1: 300, x2: 40, y2: 10, stroke: C.ink }, ms);
    T(ms, 420, 318, 'x (on a cone · 在锥上) →', { 'text-anchor': 'end', 'font-size': 11 });
    T(ms, 46, 18, 'f(x)', { 'font-size': 12, 'font-weight': 700 });
    el('rect', { x: 40, y: 10, width: 70, height: 290, fill: 'rgba(134,142,150,.12)' }, ms);
    T(ms, 75, 292, 'ignored', { 'text-anchor': 'middle', 'font-size': 10, fill: C.grey });
    F.forEach(f => {
      if (!f.h) return;
      let d = '';
      for (let x = 0; x <= 240; x += 4) d += (d ? 'L' : 'M') + (110 + x) + ',' + Math.max(12, f.h(x));
      el('path', { d, fill: 'none', stroke: f.col, 'stroke-width': sel === f.k ? 4 : 1.5, opacity: sel === f.k ? 1 : .45, 'stroke-dasharray': f.dash ? '6 4' : '' }, ms);
    });
    if (sel === 'inc') {
      for (let i = 0; i < 40; i++) { const x = 110 + i * 6; el('circle', { cx: x, cy: 60 + ((i * 97) % 220), r: 3, fill: C.fal }, ms); }
      T(ms, 260, 40, 'no pattern on any cone? · 在任何锥上都无规律？', { 'text-anchor': 'middle', fill: C.fal, 'font-size': 11, 'font-weight': 700 });
    }
  }
  segButtons($('mcBtns'), F.map(f => ({ key: f.k, en: f.lab, zh: f.lab })), k => { sel = k; drawM(); const f = F.find(z => z.k === k); okBox(info, bi(f.en, f.zh), 'info'); }, 'id');
  checkYourself('cy7', ['Under Martin\'s Part I, which case is f(x) = x ⊕ 0′ in?', '按马丁猜想 (I)，f(x) = x ⊕ 0′ 属于哪种情形？'], [
    ['constant on a cone', '在某个锥上为常数', false, 'It takes infinitely many values on every cone.', '它在每个锥上都取无穷多个值。'],
    ['≥ identity on a cone', '在某个锥上 ≥ 恒等函数', true],
  ], ['x ⊕ 0′ ≥<sub>T</sub> x always, and on the cone above 0′ it is ≡<sub>T</sub> x. (Here this is a fact, not a conjecture: the function is simple enough.)', 'x ⊕ 0′ ≥<sub>T</sub> x 恒成立，并且在 0′ 以上的锥上 ≡<sub>T</sub> x。（这里是事实而非猜想：这个函数足够简单。）']);
})();

/* ================= §8 reverse mathematics ================= */
(function rm() {
  const svg = $('rmSvg'), info = $('rmInfo');
  const R = {
    RCA: { y: 430, l: 'RCA₀', o: 'ω^ω', en: '<b>RCA₀</b>: computable mathematics. Its ω-models contain only what can be computed from what is there. Proves: intermediate value theorem, Baire category theorem, existence of algebraic closures of countable fields.', zh: '<b>RCA₀</b>：可计算数学。它的 ω-模型只含能从已有集合计算出来的东西。可证：介值定理、贝尔纲定理、可数域代数闭包的存在性。' },
    WKL: { y: 345, l: 'WKL₀', o: 'ω^ω', en: '<b>WKL₀</b>: compactness. ≡ Heine–Borel for [0, 1] (countable covers), Gödel completeness (countable languages), Brouwer fixed point theorem, Hahn–Banach (separable). Π⁰₂-conservative over PRA (Friedman): “finitistically reducible”.', zh: '<b>WKL₀</b>：紧致性。≡ [0, 1] 的海涅–博雷尔定理（可数覆盖）、哥德尔完备性定理（可数语言）、布劳威尔不动点定理、哈恩–巴拿赫定理（可分情形）。在 PRA 上 Π⁰₂-保守（Friedman）：“可有穷归约”。' },
    ACA: { y: 255, l: 'ACA₀', o: 'ε₀', en: '<b>ACA₀</b>: arithmetical comprehension (the jump). ≡ Bolzano–Weierstrass, every countable vector space has a basis, every countable commutative ring has a maximal ideal, Kőnig\'s lemma, RT³₂. Conservative over PA for arithmetic sentences.', zh: '<b>ACA₀</b>：算术概括（跳跃）。≡ 波尔查诺–魏尔斯特拉斯定理、每个可数向量空间有基、每个可数交换环有极大理想、柯尼希引理、RT³₂。对算术句子在 PA 上保守。' },
    ATR: { y: 145, l: 'ATR₀', o: 'Γ₀', en: '<b>ATR₀</b>: iterate the jump along any countable well-order. ≡ comparability of countable well-orders, perfect set theorem for closed sets, open (Σ⁰₁) determinacy, Ulm\'s theorem. Γ₀ is the classical limit of “predicative” mathematics (Feferman–Schütte).', zh: '<b>ATR₀</b>：沿任意可数良序迭代跳跃。≡ 可数良序的可比性、闭集的完美集定理、开集（Σ⁰₁）决定性、Ulm 定理。Γ₀ 是“直谓”数学的经典极限（Feferman–Schütte）。' },
    PI: { y: 55, l: 'Π¹₁-CA₀', o: 'ψ(Ω_ω)', en: '<b>Π¹₁-CA₀</b>: impredicative. ≡ Cantor–Bendixson theorem, every countable abelian group is divisible ⊕ reduced. Strongest of the Big Five.', zh: '<b>Π¹₁-CA₀</b>：非直谓。≡ 康托尔–本迪克松定理、每个可数阿贝尔群是可除群 ⊕ 约化群。五大系统中最强的。' },
  };
  const Z = {
    RT22: { x: 640, y: 320, l: 'RT²₂', en: '<b>RT²₂</b>: Ramsey for pairs, 2 colours. Strictly between RCA₀ and ACA₀, incomparable with WKL₀. Its exact first-order part is <b>open</b> (between BΣ⁰₂ and IΣ⁰₂).', zh: '<b>RT²₂</b>：二元、两色的拉姆齐定理。严格介于 RCA₀ 与 ACA₀ 之间，与 WKL₀ 不可比。它的一阶部分究竟是什么<b>仍未解决</b>（介于 BΣ⁰₂ 与 IΣ⁰₂ 之间）。' },
    SRT: { x: 560, y: 410, l: 'SRT²₂', en: '<b>SRT²₂</b>: RT²₂ for <i>stable</i> colourings (each point eventually has one colour with all later points).', zh: '<b>SRT²₂</b>：限于<i>稳定</i>染色（每个点与后面的点最终都同色）的 RT²₂。' },
    COH: { x: 740, y: 410, l: 'COH', en: '<b>COH</b>: for any sequence of sets there is an infinite set “cohesive” for all of them. RT²₂ ↔ SRT²₂ + COH (Cholak–Jockusch–Slaman 2001).', zh: '<b>COH</b>：对任意集合序列，存在一个对它们全都“内聚”的无穷集。RT²₂ ↔ SRT²₂ + COH（Cholak–Jockusch–Slaman 2001）。' },
    HT: { x: 640, y: 200, l: 'Hindman', en: '<b>Hindman\'s theorem</b> (finite sums): implies ACA₀, provable in ACA₀⁺ (Blass–Hirst–Simpson 1987). Exact strength <b>open</b>.', zh: '<b>Hindman 定理</b>（有限和）：蕴涵 ACA₀，可在 ACA₀⁺ 中证明（Blass–Hirst–Simpson 1987）。确切强度<b>仍未解决</b>。' },
    ACAP: { x: 640, y: 120, l: 'ACA₀⁺', en: '<b>ACA₀⁺</b>: ACA₀ + the ω-jump of every set exists. Strictly between ACA₀ and ATR₀.', zh: '<b>ACA₀⁺</b>：ACA₀ + 每个集合的 ω 次跳跃存在。严格介于 ACA₀ 与 ATR₀ 之间。' },
  };
  const LX = 230;
  const pos = k => R[k] ? { x: LX, y: R[k].y } : Z[k];
  // arrows: [from, to, kind, en, zh]  kind: 'imp' | 'no' | 'q'
  const A = [
    ['ACA', 'RT22', 'imp', 'ACA₀ proves RT²₂ (classical proof via the jump).', 'ACA₀ 能证明 RT²₂（借助跳跃的经典证明）。'],
    ['RT22', 'ACA', 'no', 'RT²₂ ⊬ ACA₀: Seetapun (with Slaman) 1995 built an ω-model of RT²₂ not containing 0′.', 'RT²₂ ⊬ ACA₀：Seetapun（与 Slaman）1995 构造了一个不含 0′ 的 RT²₂ 的 ω-模型。'],
    ['RT22', 'WKL', 'no', 'RT²₂ ⊬ WKL₀: Liu Lu (2012) showed every computable 2-colouring has an infinite homogeneous set that does not compute a PA degree.', 'RT²₂ ⊬ WKL₀：刘路（2012）证明每个可计算 2-染色都有一个不能计算 PA 度的无穷齐次集。'],
    ['WKL', 'RT22', 'no', 'WKL₀ ⊬ RT²₂: Jockusch (1972) gave a computable colouring with no infinite Δ⁰₂ homogeneous set, while WKL₀ has an ω-model of low (hence Δ⁰₂) sets.', 'WKL₀ ⊬ RT²₂：Jockusch（1972）给出一个没有无穷 Δ⁰₂ 齐次集的可计算染色，而 WKL₀ 有一个只含低集（因而 Δ⁰₂）的 ω-模型。'],
    ['RT22', 'SRT', 'imp', 'Trivially RT²₂ → SRT²₂.', 'RT²₂ → SRT²₂ 是显然的。'],
    ['RT22', 'COH', 'imp', 'RT²₂ → COH (Cholak–Jockusch–Slaman 2001; Mileti).', 'RT²₂ → COH（Cholak–Jockusch–Slaman 2001；Mileti）。'],
    ['SRT', 'RT22', 'no', 'SRT²₂ ⊬ RT²₂: Chong–Slaman–Yang 2014 (non-standard model); in ω-models: Monin–Patey 2021.', 'SRT²₂ ⊬ RT²₂：Chong–Slaman–Yang 2014（非标准模型）；ω-模型情形：Monin–Patey 2021。'],
    ['COH', 'SRT', 'no', 'COH ⊬ SRT²₂ (Cholak–Jockusch–Slaman 2001).', 'COH ⊬ SRT²₂（Cholak–Jockusch–Slaman 2001）。'],
    ['HT', 'ACA', 'imp', 'Hindman → ACA₀ (Blass–Hirst–Simpson 1987).', 'Hindman → ACA₀（Blass–Hirst–Simpson 1987）。'],
    ['ACAP', 'HT', 'imp', 'ACA₀⁺ → Hindman (Blass–Hirst–Simpson 1987). Whether Hindman → ACA₀⁺, or Hindman is equivalent to ACA₀, is OPEN.', 'ACA₀⁺ → Hindman（Blass–Hirst–Simpson 1987）。Hindman 是否 → ACA₀⁺，或是否等价于 ACA₀，仍未解决。'],
    ['ATR', 'ACAP', 'imp', 'ATR₀ → ACA₀⁺.', 'ATR₀ → ACA₀⁺。'],
  ];
  const placed = {};
  const TH = [
    ['IVT', 'intermediate value thm', '介值定理', 'RCA'], ['BC', 'Baire category thm', '贝尔纲定理', 'RCA'],
    ['HB', 'Heine–Borel [0,1]', '海涅–博雷尔', 'WKL'], ['GC', 'Gödel completeness', '哥德尔完备性', 'WKL'], ['BF', 'Brouwer fixed point', '布劳威尔不动点', 'WKL'],
    ['BW', 'Bolzano–Weierstrass', '波尔查诺–魏尔斯特拉斯', 'ACA'], ['VB', 'vector spaces have bases', '向量空间有基', 'ACA'], ['RT3', 'RT³₂', 'RT³₂', 'ACA'],
    ['CW', 'comparability of well-orders', '良序可比性', 'ATR'], ['OD', 'open determinacy', '开集决定性', 'ATR'],
    ['CB', 'Cantor–Bendixson', '康托尔–本迪克松', 'PI'], ['AG', 'abelian group = div ⊕ red', '阿贝尔群分解', 'PI'],
  ];
  function draw() {
    svg.innerHTML = '';
    const defs = el('defs', {}, svg);
    [['rmA', '#495057'], ['rmN', C.fal]].forEach(([id, c]) => {
      const mk = el('marker', { id, viewBox: '0 0 10 10', refX: 9, refY: 5, markerWidth: 7, markerHeight: 7, orient: 'auto' }, defs);
      el('path', { d: 'M0,0 L10,5 L0,10 z', fill: c }, mk);
    });
    el('line', { x1: LX - 120, y1: 40, x2: LX - 120, y2: 450, stroke: '#a07c4a', 'stroke-width': 6 }, svg);
    el('line', { x1: LX + 120, y1: 40, x2: LX + 120, y2: 450, stroke: '#a07c4a', 'stroke-width': 6 }, svg);
    T(svg, 20, 20, 'stronger ↑ · 更强 ↑', { 'font-size': 12, fill: C.grey, 'font-weight': 700 });
    Object.entries(R).forEach(([k, r]) => {
      const g = el('g', { class: 'clk' }, svg);
      el('rect', { x: LX - 125, y: r.y - 16, width: 250, height: 32, rx: 8, fill: '#f4e3c3', stroke: '#a07c4a', 'stroke-width': 2 }, g);
      T(g, LX - 110, r.y + 5, r.l, { 'font-size': 15, 'font-weight': 800 });
      T(g, LX + 110, r.y + 5, '|·| = ' + r.o, { 'font-size': 11.5, 'text-anchor': 'end', fill: '#7a5a2a' });
      g.addEventListener('click', () => okBox(info, bi(r.en, r.zh), 'info'));
      const list = TH.filter(t => placed[t[0]] && t[3] === k);
      list.forEach((t, i) => {
        const c = el('g', { class: 'pop' }, svg);
        T(c, LX + 135, r.y - 4 + i * 13 - (list.length - 1) * 6, '◂ ' + t[1], { 'font-size': 11, fill: C.acc, 'font-weight': 700 });
      });
    });
    Object.entries(Z).forEach(([k, z]) => {
      const g = el('g', { class: 'clk' }, svg);
      el('rect', { x: z.x - 52, y: z.y - 16, width: 104, height: 32, rx: 16, fill: k === 'RT22' ? '#e7ecff' : '#fff', stroke: C.acc, 'stroke-width': 2 }, g);
      T(g, z.x, z.y + 5, z.l, { 'text-anchor': 'middle', 'font-size': 14, 'font-weight': 800 });
      g.addEventListener('click', () => okBox(info, bi(z.en, z.zh), 'info'));
    });
    A.forEach(([u, v, kind, en, zh], i) => {
      const p = pos(u), q = pos(v);
      let x1 = R[u] ? LX + 125 : p.x, y1 = p.y, x2 = R[v] ? LX + 125 : q.x, y2 = q.y;
      const dx = x2 - x1, dy = y2 - y1, L = Math.hypot(dx, dy);
      const sh = (kind === 'no' ? 8 : -8) * (u < v ? 1 : -1);  // opposite arrows on opposite sides
      const ox = -dy / L * sh, oy = dx / L * sh;
      const cut1 = R[u] ? 0 : 22, cut2 = R[v] ? 4 : 22;
      x1 += dx / L * cut1 + ox; y1 += dy / L * cut1 + oy; x2 -= dx / L * cut2 - ox; y2 -= dy / L * cut2 - oy;
      const g = el('g', { class: 'clk' }, svg);
      el('line', { x1, y1, x2, y2, stroke: 'transparent', 'stroke-width': 12 }, g);
      el('line', { x1, y1, x2, y2, stroke: kind === 'no' ? C.fal : '#495057', 'stroke-width': 2.2, 'stroke-dasharray': kind === 'no' ? '6 4' : '', 'marker-end': `url(#${kind === 'no' ? 'rmN' : 'rmA'})` }, g);
      if (kind === 'no') T(g, (x1 + x2) / 2 + ox, (y1 + y2) / 2 + oy + 4, '✗', { 'text-anchor': 'middle', fill: C.fal, 'font-size': 15, 'font-weight': 800 });
      g.addEventListener('click', () => okBox(info, (kind === 'no' ? ST('thm') + ' ' : '') + bi(en, zh), 'info'));
    });
    T(svg, 640, 255, '? exact strength · 确切强度 ?', { 'text-anchor': 'middle', 'font-size': 11, fill: C.gold, 'font-weight': 700 });
    T(svg, 640, 290, '? first-order part · 一阶部分 ?', { 'text-anchor': 'middle', 'font-size': 11, fill: C.gold, 'font-weight': 700 });
    T2(svg, 790, 30, ['→ implies (over RCA₀) · 蕴涵', '✗ does not imply · 不蕴涵'], { 'font-size': 11.5, fill: C.grey, 'text-anchor': 'middle' }, 15);
  }
  const cb = $('rmChips');
  TH.forEach(t => {
    const c = document.createElement('span');
    c.className = 'chip';
    c.innerHTML = bil(t[1], t[2]);
    c.addEventListener('click', () => {
      placed[t[0]] = !placed[t[0]];
      c.classList.toggle('on', placed[t[0]]);
      draw();
      if (placed[t[0]]) okBox(info, bi(`<b>${t[1]}</b> is equivalent over RCA₀ to <b>${R[t[3]].l}</b>${t[3] === 'RCA' ? ' (i.e. provable in RCA₀)' : ''}.`, `<b>${t[2]}</b> 在 RCA₀ 上等价于 <b>${R[t[3]].l}</b>${t[3] === 'RCA' ? '（即在 RCA₀ 中可证）' : ''}。`), 'info');
    });
    cb.appendChild(c);
  });
  draw();
  okBox(info, bi('The left ladder is linear; the right “zoo” is not. Click arrows: black = implication, red dashed ✗ = proved non-implication.', '左边的梯子是线性的，右边的“动物园”则不是。点击箭头：黑色 = 蕴涵，红色虚线 ✗ = 已证明的不蕴涵。'), 'info');
  checkYourself('cy8', ['Which statement is correct (over RCA₀)?', '哪个说法正确（在 RCA₀ 上）？'], [
    ['RT²₂ is equivalent to ACA₀', 'RT²₂ 等价于 ACA₀', false, 'RT³₂ is; RT²₂ is strictly weaker (Seetapun 1995).', 'RT³₂ 才是；RT²₂ 严格更弱（Seetapun 1995）。'],
    ['WKL₀ and RT²₂ are incomparable', 'WKL₀ 与 RT²₂ 互不可比', true],
    ['RT²₂ is provable in RCA₀', 'RT²₂ 在 RCA₀ 中可证', false, 'There are computable colourings with no computable (even no Δ⁰₂) infinite homogeneous set (Jockusch 1972).', '存在可计算染色，没有可计算的（甚至没有 Δ⁰₂ 的）无穷齐次集（Jockusch 1972）。'],
  ], ['Neither implies the other: Jockusch 1972 (WKL₀ ⊬ RT²₂) and Liu 2012 (RT²₂ ⊬ WKL₀).', '谁也推不出谁：Jockusch 1972（WKL₀ ⊬ RT²₂）与刘路 2012（RT²₂ ⊬ WKL₀）。']);
})();

/* ================= §9 randomness ================= */
(function rand() {
  const N = 256;
  function isqrt(n) { if (n < 2n) return n; let x = n, y = (x + 1n) >> 1n; while (y < x) { x = y; y = (x + n / x) >> 1n; } return x; }
  const sqrt2 = () => { const v = isqrt(2n << BigInt(2 * (N - 1))); return v.toString(2).slice(0, N); };
  const SRC = {
    zero: { en: 'all zeros', zh: '全 0', g: () => '0'.repeat(N), p: ['print 256 zeros', '输出 256 个 0'] },
    per: { en: 'period 0110', zh: '周期 0110', g: () => '0110'.repeat(N / 4), p: ['print “0110” 64 times', '把 “0110” 输出 64 次'] },
    tm: { en: 'Thue–Morse', zh: '图厄–莫尔斯', g: () => [...Array(N)].map((_, i) => (i.toString(2).split('1').length - 1) % 2).join(''), p: ['bit i = parity of the 1s in binary i', '第 i 位 = i 的二进制中 1 的个数的奇偶'] },
    s2: { en: '√2 in binary', zh: '√2 的二进制', g: sqrt2, p: ['compute √2 to 256 bits (Newton)', '用牛顿法算 √2 到 256 位'] },
    coin: { en: 'coin flips', zh: '抛硬币', g: () => [...Array(N)].map(() => Math.random() < .5 ? 1 : 0).join(''), p: null },
  };
  function lz78(s) {
    const dict = new Map([['', 0]]); let w = '', p = 0, bits = 0;
    for (const c of s) {
      if (dict.has(w + c)) { w += c; continue; }
      p++; bits += Math.ceil(Math.log2(p)) + 1; dict.set(w + c, p); w = '';
    }
    if (w) { p++; bits += Math.ceil(Math.log2(p)) + 1; }
    return { p, bits };
  }
  function show(s, src) {
    s = s.replace(/[^01]/g, '');
    if (!s.length) return;
    $('krIn').value = s;
    $('krBits').textContent = s;
    const n = s.length, z = lz78(s), pr = src && src.p;
    const w = v => Math.min(100, v / n * 100);
    $('krBars').innerHTML = `<div class="m" style="font-size:13px">${bil('length', '长度')} n = ${n}</div><div class="bar" style="width:100%;background:#adb5bd"></div>
      <div class="m" style="font-size:13px;margin-top:6px">${bil('LZ78 code (an upper bound on K, up to a constant)', 'LZ78 编码（K 的上界，相差一个常数）')}: ${z.bits} bits</div><div class="bar" style="width:${w(z.bits)}%;background:${z.bits < n ? C.tru : C.fal}"></div>`;
    let h;
    if (z.bits >= n) h = bi(`LZ78 saves nothing (${z.bits} ≥ ${n} bits).`, `LZ78 一点也没省（${z.bits} ≥ ${n} 位）。`);
    else h = bi(`LZ78 saves ${n - z.bits} bits.`, `LZ78 省了 ${n - z.bits} 位。`);
    if (pr) h += bi(` But a <b>short program</b> exists: “${pr[0]}”, so K(x) ≤ K(n) + c ≈ 2 log₂ n + c, tiny compared with n.`, ` 但存在一个<b>短程序</b>：“${pr[1]}”，所以 K(x) ≤ K(n) + c ≈ 2 log₂ n + c，与 n 相比微不足道。`);
    else if (src) h += bi(' For genuine coin flips, with probability ≥ 1 − 2<sup>−c</sup> no description is shorter than n − c (panel b). But no algorithm can <i>certify</i> that this particular string is incompressible.', ' 对真正的抛硬币序列，以 ≥ 1 − 2<sup>−c</sup> 的概率没有比 n − c 更短的描述（见 (b)）。但没有算法能<i>认证</i>这个具体的串不可压缩。');
    okBox($('krInfo'), h, 'info');
  }
  const box = $('krBtns');
  Object.values(SRC).forEach(src => {
    const b = document.createElement('button');
    b.className = 'btn small';
    b.innerHTML = bil(src.en, src.zh);
    b.addEventListener('click', () => { box.querySelectorAll('.btn').forEach(x => x.classList.remove('sel')); b.classList.add('sel'); show(src.g(), src); });
    box.appendChild(b);
  });
  $('krIn').addEventListener('change', () => show($('krIn').value, null));
  box.querySelectorAll('.btn')[4].click();
  // counting
  const cs = $('ccSvg');
  function cc() {
    const c = +$('ccS').value; $('ccV').textContent = c;
    cs.innerHTML = '';
    const n = 20;
    T(cs, 10, 24, `2^${n} = 1,048,576 strings of length ${n} · 长为 ${n} 的串`, { 'font-size': 12, 'font-weight': 700 });
    el('rect', { x: 10, y: 34, width: 400, height: 34, rx: 6, fill: '#dee2e6' }, cs);
    const progs = Math.pow(2, n - c) - 1;
    T(cs, 10, 96, `programs shorter than n − c = ${n - c}: 2^${n - c} − 1 = ${progs.toLocaleString('en-US')}`, { 'font-size': 12, 'font-weight': 700 });
    T(cs, 10, 112, `比 n − c 短的程序 · each outputs ≤ 1 string · 每个至多输出一个串`, { 'font-size': 11, fill: C.grey });
    const wd = Math.max(1.5, 400 * progs / Math.pow(2, n));
    el('rect', { x: 10, y: 120, width: wd, height: 34, rx: 6, fill: C.claim, class: 'pop' }, cs);
    const pct = 100 * progs / Math.pow(2, n);
    T2(cs, 10, 180, [`⇒ fewer than 2^−${c} = ${(100 / Math.pow(2, c)).toPrecision(3)}% of strings have K < n − ${c}`,
      `⇒ 少于 ${pct.toPrecision(3)}% 的串满足 K < n − ${c}：绝大多数串不可压缩`], { 'font-size': 12, fill: C.ink, 'font-weight': 700 }, 18);
  }
  $('ccS').addEventListener('input', cc);
  cc();
  checkYourself('cy9', ['A 1000-bit string compresses (with LZ) to 1100 bits. Is K(x) ≥ 1000 − c for a small c?', '一个 1000 位的串用 LZ 压缩后有 1100 位。是否 K(x) ≥ 1000 − c（c 较小）？'], [
    ['Yes, LZ found no pattern', '是，LZ 找不到规律', false, 'LZ misses most patterns, e.g. the digits of √2.', 'LZ 会漏掉大多数规律，比如 √2 的数字。'],
    ['Can\'t tell from this', '据此无法判断', true],
  ], ['A compressor gives only an upper bound on K. Lower bounds on K are not computable, and (Chaitin) a consistent theory like ZFC can prove K(x) &gt; m only for m below a fixed constant.', '压缩程序只给出 K 的上界。K 的下界不可计算，而且（蔡廷）像 ZFC 这样的一致理论只能对小于某个固定常数的 m 证明 K(x) &gt; m。']);
})();

/* ================= §10 complexity ================= */
(function cx() {
  const s = $('ttnSvg');
  function draw() {
    const n = +$('ttn').value; $('ttnV').textContent = n;
    s.innerHTML = '';
    const X = v => 40 + v * 4.6, Y = v => 230 - v * 7.3;
    el('line', { x1: 40, y1: 230, x2: 410, y2: 230, stroke: C.ink }, s);
    el('line', { x1: 40, y1: 230, x2: 40, y2: 10, stroke: C.ink }, s);
    for (let e = 0; e <= 30; e += 10) { T(s, 34, Y(e) + 4, '10' + ['⁰', '¹⁰', '²⁰', '³⁰'][e / 10], { 'text-anchor': 'end', 'font-size': 10 }); el('line', { x1: 40, x2: 410, y1: Y(e), y2: Y(e), stroke: '#eee' }, s); }
    T(s, 410, 248, 'n atoms · 原子数', { 'text-anchor': 'end', 'font-size': 11 });
    const curve = (f, col, lab) => {
      let d = '';
      for (let m = 1; m <= 80; m++) d += (d ? 'L' : 'M') + X(m) + ',' + Math.max(10, Y(Math.log10(f(m))));
      el('path', { d, fill: 'none', stroke: col, 'stroke-width': 2.5 }, s);
      T(s, 330, Math.max(20, Y(Math.log10(f(70)))) - 6, lab, { fill: col, 'font-size': 12, 'font-weight': 700 });
    };
    curve(m => Math.pow(2, m), C.fal, '2ⁿ rows · 行');
    curve(m => Math.pow(m, 3), C.tru, 'n³');
    const uni = Math.log10(4.35e17 * 1e9);
    el('line', { x1: 40, x2: 410, y1: Y(uni), y2: Y(uni), stroke: C.gold, 'stroke-dasharray': '5 4' }, s);
    T(s, 45, Y(uni) + 14, 'ns since the Big Bang · 宇宙年龄（纳秒）', { fill: C.gold, 'font-size': 10.5 });
    el('line', { x1: X(n), x2: X(n), y1: 10, y2: 230, stroke: C.acc }, s);
    const secs = Math.pow(2, n) / 1e9;
    const t = secs < 1 ? '< 1 s' : secs < 3600 * 24 * 365 ? (secs / 3600).toPrecision(3) + ' h' : (secs / 3.15e7).toExponential(2) + ' years · 年';
    T(s, 50, 26, `n = ${n}: 2ⁿ = ${Math.pow(2, n).toExponential(2)} rows; at 10⁹ rows/s: ${t}`, { 'font-size': 11.5, 'font-weight': 700 });
  }
  $('ttn').addEventListener('input', draw);
  draw();
  const d = $('dcSvg'), info = $('dcInfo');
  const CL = [
    { k: 'PSPACE', cx: 210, cy: 155, rx: 205, ry: 145, ly: 28, col: '#495057', en: '<b>PSPACE</b> = FO(PFP) on ordered structures (Vardi 1982; Abiteboul–Vianu) = SO(TC) (Immerman). NL ⊊ PSPACE (space hierarchy). P vs PSPACE: <b>open</b>.', zh: '<b>PSPACE</b> = 有序结构上的 FO(PFP)（Vardi 1982；Abiteboul–Vianu）= SO(TC)（Immerman）。NL ⊊ PSPACE（空间层级定理）。P 与 PSPACE：<b>未解决</b>。' },
    { k: 'PH', cx: 210, cy: 170, rx: 190, ry: 125, ly: 62, col: C.meta, en: '<b>PH</b> (polynomial hierarchy) = full second-order logic SO (Stockmeyer 1977). Whether PH collapses is <b>open</b>.', zh: '<b>PH</b>（多项式层级）= 完整的二阶逻辑 SO（Stockmeyer 1977）。PH 是否坍缩<b>仍未解决</b>。' },
    { k: 'NP', cx: 175, cy: 175, rx: 115, ry: 95, ly: 0, lx: 95, col: C.fal, en: '<b>NP</b> = existential second-order logic ∃SO (Fagin 1974), on all finite structures, no order needed. Example: 3-colourability is “∃R ∃G ∃B (every vertex has a colour, and no edge joins two vertices of the same colour)”.', zh: '<b>NP</b> = 存在二阶逻辑 ∃SO（Fagin 1974），对所有有限结构成立，不需要序。例子：3-可着色性就是“∃R ∃G ∃B（每个顶点都有颜色，且没有边连接同色顶点）”。' },
    { k: 'coNP', cx: 245, cy: 175, rx: 115, ry: 95, ly: 0, lx: 330, col: C.claim, en: '<b>coNP</b> = universal second-order logic ∀SO. TAUT (propositional tautologies, L1) is coNP-complete. NP = coNP? <b>open</b>; equivalent to the existence of a polynomially bounded proof system (Cook–Reckhow 1979).', zh: '<b>coNP</b> = 全称二阶逻辑 ∀SO。TAUT（命题重言式，第 1 课）是 coNP-完全的。NP = coNP？<b>未解决</b>；等价于存在多项式有界的证明系统（Cook–Reckhow 1979）。' },
    { k: 'P', cx: 210, cy: 180, rx: 62, ry: 58, ly: 138, col: C.tru, en: '<b>P</b> = FO(LFP) on <i>ordered</i> finite structures (Immerman, Vardi 1982). On unordered structures no logic is known to capture P (Gurevich\'s question, <b>open</b>). P vs NP: <b>open</b> (Clay Millennium problem).', zh: '<b>P</b> = <i>有序</i>有限结构上的 FO(LFP)（Immerman、Vardi 1982）。在无序结构上，尚不知有哪种逻辑能刻画 P（Gurevich 的问题，<b>未解决</b>）。P 与 NP：<b>未解决</b>（克莱千禧年难题）。' },
    { k: 'NL', cx: 210, cy: 195, rx: 46, ry: 40, ly: 168, col: C.acc, en: '<b>NL</b> = FO(TC) on ordered structures (Immerman 1987). NL = coNL (Immerman–Szelepcsényi 1987), a theorem proved via this logical view.', zh: '<b>NL</b> = 有序结构上的 FO(TC)（Immerman 1987）。NL = coNL（Immerman–Szelepcsényi 1987），正是借助这种逻辑视角证明的定理。' },
    { k: 'L', cx: 210, cy: 208, rx: 32, ry: 26, ly: 194, col: C.teal, en: '<b>L</b> (logspace) = FO(DTC) on ordered structures. L vs P: <b>open</b>.', zh: '<b>L</b>（对数空间）= 有序结构上的 FO(DTC)。L 与 P：<b>未解决</b>。' },
    { k: 'AC⁰', cx: 210, cy: 220, rx: 18, ry: 12, ly: 224, col: C.gold, en: '<b>AC⁰</b> (uniform) = first-order logic FO (Barrington–Immerman–Straubing 1990). Parity is not in AC⁰ (Ajtai 1983; Furst–Saxe–Sipser 1984): FO cannot express “even size”, a fact you can also see with Ehrenfeucht–Fraïssé games.', zh: '<b>AC⁰</b>（一致）= 一阶逻辑 FO（Barrington–Immerman–Straubing 1990）。奇偶性不在 AC⁰ 中（Ajtai 1983；Furst–Saxe–Sipser 1984）：FO 无法表达“元素个数为偶数”，这一点也可以用埃伦弗赫特–弗赖斯游戏看出。' },
  ];
  CL.forEach(c => {
    const g = el('g', { class: 'clk' }, d);
    el('ellipse', { cx: c.cx, cy: c.cy, rx: c.rx, ry: c.ry, fill: c.col, 'fill-opacity': .07, stroke: c.col, 'stroke-width': 2 }, g);
    g.addEventListener('click', e => { e.stopPropagation(); okBox(info, bi(c.en, c.zh), 'info'); });
  });
  CL.forEach(c => T(d, c.lx || 210, c.ly || 175, c.k, { 'text-anchor': 'middle', 'font-size': c.k === 'AC⁰' ? 9.5 : 12.5, 'font-weight': 800, fill: c.col, 'pointer-events': 'none' }));
  okBox(info, bi('Click a class. Each one equals a logic (Fagin, Immerman, Vardi). Picture is schematic: only AC⁰ ⊊ L and NL ⊊ PSPACE are known to be strict among these.', '点击一个复杂性类。每个类都等于某种逻辑（Fagin、Immerman、Vardi）。图只是示意：其中只有 AC⁰ ⊊ L 与 NL ⊊ PSPACE 已知是严格包含。'), 'info');
  checkYourself('cy10', ['Suppose someone proves NP ≠ coNP. What follows?', '假设有人证明了 NP ≠ coNP。能推出什么？'], [
    ['P ≠ NP', 'P ≠ NP', true], ['P = NP', 'P = NP', false], ['Nothing about P vs NP', '对 P 与 NP 毫无结论', false],
  ], ['P is closed under complement, so P = NP would give NP = P = coP = coNP. Contrapositive: NP ≠ coNP ⇒ P ≠ NP. (The converse is not known.)', 'P 对补运算封闭，所以 P = NP 会给出 NP = P = coP = coNP。取逆否：NP ≠ coNP ⇒ P ≠ NP。（反方向未知。）']);
})();

/* ================= §11 ordinal analysis ================= */
(function oa() {
  const svg = $('oaSvg'), info = $('oaInfo');
  const P = [
    { x: 60, o: 'ω^ω', t: 'RCA₀, WKL₀, IΣ₁, PRA', s: 'thm', en: 'PRA, IΣ₁, RCA₀ and WKL₀ all have ordinal ω<sup>ω</sup>. Their provably total functions are the primitive recursive ones.', zh: 'PRA、IΣ₁、RCA₀、WKL₀ 的序数都是 ω<sup>ω</sup>。它们的可证全函数恰好是原始递归函数。' },
    { x: 165, o: 'ε₀', t: 'PA, ACA₀', s: 'thm', en: 'Gentzen 1936: PRA + TI(ε₀) proves Con(PA), and PA proves TI(α) for each α &lt; ε₀ but not for ε₀ (Gentzen 1943). Provably total functions: below f<sub>ε₀</sub> (L21).', zh: '根岑 1936：PRA + TI(ε₀) 证明 Con(PA)，且 PA 能证明每个 α &lt; ε₀ 的 TI(α)，却不能证明 ε₀ 的（根岑 1943）。可证全函数：在 f<sub>ε₀</sub> 之下（第 21 课）。' },
    { x: 270, o: 'Γ₀', t: 'ATR₀', s: 'thm', en: 'Γ₀, the Feferman–Schütte ordinal, the limit of predicativity. |ATR₀| = Γ₀ (Friedman–McAloon–Simpson 1982).', zh: 'Γ₀，Feferman–Schütte 序数，直谓性的极限。|ATR₀| = Γ₀（Friedman–McAloon–Simpson 1982）。' },
    { x: 375, o: 'BH', t: 'ID₁, KP', s: 'thm', en: 'The Bachmann–Howard ordinal ψ(ε<sub>Ω+1</sub>): Kripke–Platek set theory and the theory ID₁ of one inductive definition. First uses of “collapsing functions” ψ.', zh: 'Bachmann–Howard 序数 ψ(ε<sub>Ω+1</sub>)：克里普克–普拉特克集合论与单次归纳定义理论 ID₁。首次用到“坍缩函数”ψ。' },
    { x: 480, o: 'ψ(Ω_ω)', t: 'Π¹₁-CA₀', s: 'thm', en: 'Π¹₁-CA₀, the strongest Big Five system (Buchholz, Pohlers, Takeuti; 1970s–80s).', zh: 'Π¹₁-CA₀，五大系统中最强者（Buchholz、Pohlers、Takeuti；1970–80 年代）。' },
    { x: 590, o: '…', t: 'Δ¹₂-CA+BI, Π¹₂-CA⁻', s: 'thm', en: 'Rathjen (Arch. Math. Logic 2005): ordinal analyses of Δ¹₂-CA + BI and of parameter-free Π¹₂-comprehension, via “stability” in set theory (KP + Σ₁-separation-like principles).', zh: 'Rathjen（Arch. Math. Logic 2005）：对 Δ¹₂-CA + BI 及无参数 Π¹₂-概括给出序数分析，借助集合论中的“稳定性”（类似 KP + Σ₁-分离的原则）。' },
    { x: 690, o: '?', t: 'Π¹₂-CA₀', s: 'ann', en: 'Announced by Rathjen in the 1990s, but to our knowledge the full analysis has never been published in full. Treat it as the current frontier.', zh: 'Rathjen 在 1990 年代宣布，但据我们所知，完整的分析从未全部发表。可视为当前前沿。' },
    { x: 785, o: '?', t: 'Z₂', s: 'ann', en: 'Full second-order arithmetic: analyses claimed by Arai (arXiv 2023) and Towsner (arXiv 2024, self-described as work in progress). Neither is refereed; later papers still call them claims.', zh: '完整二阶算术：Arai（2023 年 arXiv）和 Towsner（2024 年 arXiv，自称仍在进行中）声称给出了分析。两者都未经审稿；后来的论文仍称之为声称。' },
    { x: 870, o: '?', t: 'ZF(C)', s: 'open', en: 'No ordinal analysis of ZF or ZFC, and no accepted strategy. The ordinals involved would have to encode large parts of the set-theoretic universe.', zh: 'ZF 或 ZFC 尚无序数分析，也没有公认的策略。所涉及的序数将不得不编码集合论宇宙的大片区域。' },
  ];
  el('rect', { x: 640, y: 30, width: 260, height: 230, fill: 'url(#oaH)' }, svg);
  const defs = el('defs', {}, svg);
  const pat = el('pattern', { id: 'oaH', width: 10, height: 10, patternUnits: 'userSpaceOnUse', patternTransform: 'rotate(45)' }, defs);
  el('line', { x1: 0, y1: 0, x2: 0, y2: 10, stroke: '#ffd8a8', 'stroke-width': 5 }, pat);
  T(svg, 770, 50, 'the Π¹₂ wall · Π¹₂ 之墙', { 'text-anchor': 'middle', 'font-size': 13, 'font-weight': 800, fill: C.claim });
  el('line', { x1: 30, y1: 160, x2: 890, y2: 160, stroke: C.ink, 'stroke-width': 2.5 }, svg);
  T(svg, 30, 285, 'not to scale: each step is incomparably larger · 不按比例：每一步都大得无法比较', { 'font-size': 11.5, fill: C.grey });
  P.forEach((p, i) => {
    const g = el('g', { class: 'clk pop' }, svg);
    g.style.animationDelay = (i * .1) + 's';
    el('circle', { cx: p.x, cy: 160, r: 12, fill: ST_COL[p.s], stroke: '#fff', 'stroke-width': 2 }, g);
    T(g, p.x, 132, p.o, { 'text-anchor': 'middle', 'font-size': 14, 'font-weight': 800 });
    const words = p.t.split(', ');
    T2(g, p.x, 196, words, { 'text-anchor': 'middle', 'font-size': 11.5, fill: C.acc, 'font-weight': 700 }, 14);
    g.addEventListener('click', () => okBox(info, `${ST(p.s)} <b>${p.t}</b>: ` + bi(p.en, p.zh), 'info'));
  });
  okBox(info, bi('Click a point. Colour = status (green: theorem, orange-red: announced, gold: open).', '点击一个点。颜色 = 状态（绿：定理；橙红：已宣布；金：未解决）。'), 'info');
  checkYourself('cy11', ['What is the proof-theoretic ordinal of ATR₀?', 'ATR₀ 的证明论序数是什么？'], [
    ['ε₀', 'ε₀', false, 'That is PA and ACA₀.', '那是 PA 与 ACA₀ 的。'], ['Γ₀', 'Γ₀', true], ['ψ(Ω<sub>ω</sub>)', 'ψ(Ω<sub>ω</sub>)', false, 'That is Π¹₁-CA₀.', '那是 Π¹₁-CA₀ 的。'],
  ], ['Γ₀, the Feferman–Schütte ordinal (Friedman–McAloon–Simpson 1982). The finite Kruskal theorem needs more than that, which is why ATR₀ cannot prove it (§12).', 'Γ₀，即 Feferman–Schütte 序数（Friedman–McAloon–Simpson 1982）。有限克鲁斯卡尔定理需要比它更多的东西，所以 ATR₀ 证明不了它（§12）。']);
})();

/* ================= §12 Goodstein & concrete incompleteness ================= */
(function good() {
  const SUP = { 0: '⁰', 1: '¹', 2: '²', 3: '³', 4: '⁴', 5: '⁵', 6: '⁶', 7: '⁷', 8: '⁸', 9: '⁹' };
  // digits of n in base b, least significant first: [[exp(BigInt), coef(BigInt)]]
  function terms(n, b) { const t = []; let e = 0n; while (n > 0n) { const c = n % b; if (c) t.push([e, c]); n /= b; e++; } return t.reverse(); }
  function bump(n, b) { if (n === 0n) return 0n; let s = 0n; for (const [e, c] of terms(n, b)) s += c * (b + 1n) ** bump(e, b); return s; }
  function ord(n, b) {
    if (n === 0n) return '0';
    return terms(n, b).map(([e, c]) => {
      if (e === 0n) return c.toString();
      const ex = ord(e, b);
      const base = e === 1n ? 'ω' : (ex.length === 1 ? 'ω' + (SUP[ex] || '^' + ex) : 'ω^(' + ex + ')');
      return c === 1n ? base : base + '·' + c;
    }).join(' + ');
  }
  function fmt(n) { const s = n.toString(); return s.length <= 14 ? Number(n).toLocaleString('en-US') : s[0] + '.' + s.slice(1, 4) + ' × 10^' + (s.length - 1); }
  let rows = [], m = 4n;
  function start(v) { m = BigInt(v); rows = [{ k: 0, b: 2n, n: m }]; render(); }
  function step() {
    const r = rows[rows.length - 1];
    if (r.n === 0n) return;
    const nn = bump(r.n, r.b) - 1n;
    rows.push({ k: r.k + 1, b: r.b + 1n, n: nn });
  }
  function render() {
    let h = `<tr><th>k</th><th>${bil('base', '底')}</th><th>${bil('value', '值')}</th><th>${bil('ordinal (b → ω)', '序数（b → ω）')}</th></tr>`;
    rows.slice(-40).forEach(r => h += `<tr><td>${r.k}</td><td>${r.b}</td><td>${fmt(r.n)}</td><td style="color:${C.meta}">${ord(r.n, r.b)}</td></tr>`);
    $('gsTab').innerHTML = h;
    const box = $('gsTab').parentElement; box.scrollTop = box.scrollHeight;
    const s = $('gsSvg'); s.innerHTML = '';
    el('line', { x1: 40, y1: 260, x2: 370, y2: 260, stroke: C.ink }, s);
    el('line', { x1: 40, y1: 260, x2: 40, y2: 20, stroke: C.ink }, s);
    T(s, 46, 16, 'log₁₀(value · 值)', { 'font-size': 11, 'font-weight': 700 });
    T(s, 370, 280, 'step k · 步数', { 'text-anchor': 'end', 'font-size': 11 });
    const mx = Math.max(1, ...rows.map(r => r.n.toString().length));
    const K = Math.max(10, rows.length);
    let d = '';
    rows.forEach((r, i) => {
      const lg = r.n === 0n ? 0 : (r.n.toString().length - 1) + Math.log10(+('0.' + r.n.toString().slice(0, 6)) * 10);
      const x = 40 + i / K * 320, y = 260 - lg / Math.max(1, mx) * 230;
      d += (d ? 'L' : 'M') + x.toFixed(1) + ',' + y.toFixed(1);
    });
    el('path', { d, fill: 'none', stroke: C.claim, 'stroke-width': 2.5 }, s);
    T(s, 46, 40, `max ≈ 10^${mx - 1}`, { 'font-size': 11, fill: C.grey });
    const last = rows[rows.length - 1];
    okBox($('gsInfo'), last.n === 0n
      ? bi(`Reached 0 after ${last.k} steps.`, `${last.k} 步后到达 0。`)
      : bi(`After ${last.k} steps the value is ${fmt(last.n)}, yet the ordinal keeps strictly decreasing, and ordinals below ε₀ cannot decrease forever. ${m === 4n ? 'G(4) reaches 0 only after about 3·2<sup>402653211</sup> steps.' : ''} PA proves each specific instance “G(m) reaches 0” (it is a true Σ⁰₁ statement), but not the statement for all m.`,
        `走了 ${last.k} 步，值为 ${fmt(last.n)}，但序数始终严格递减，而 ε₀ 以下的序数不可能无穷递减。${m === 4n ? 'G(4) 要走约 3·2<sup>402653211</sup> 步才到 0。' : ''}PA 能证明每个具体实例“G(m) 到达 0”（它是真的 Σ⁰₁ 命题），但证明不了对所有 m 的全称命题。`), last.n === 0n ? 'ok' : 'info');
  }
  segButtons($('gsBtns'), [3, 4, 5, 8, 16].map(v => ({ key: v, en: String(v), zh: String(v) })), start, 4);
  for (let i = 0; i < 8; i++) step();
  render();
  $('gsStep').addEventListener('click', () => { step(); render(); });
  $('gsRun').addEventListener('click', () => { for (let i = 0; i < 25; i++) step(); render(); });

  const CI = [
    { t: ['Gödel sentence, Con(PA)', '哥德尔句、Con(PA)'], th: 'PA', y: '1931', en: 'Metamathematical: true, unprovable in PA (L12). Natural to logicians, artificial to most mathematicians.', zh: '元数学命题：真，但在 PA 中不可证（第 12 课）。逻辑学家觉得自然，多数数学家觉得做作。' },
    { t: ['Paris–Harrington', '帕里斯–哈灵顿'], th: 'PA', y: '1977', en: 'For all n, k, m there is N such that every k-colouring of the n-subsets of {0, …, N} has a homogeneous set H of size ≥ m with |H| ≥ min H. Provable in ACA₀⁺/ZFC; unprovable in PA because its witness function grows like f<sub>ε₀</sub>.', zh: '对任意 n、k、m，存在 N，使 {0, …, N} 的 n 元子集的每个 k-染色都有大小 ≥ m 且 |H| ≥ min H 的齐次集 H。在 ACA₀⁺ / ZFC 中可证；在 PA 中不可证，因为其见证函数增长得像 f<sub>ε₀</sub>。' },
    { t: ['Goodstein; Hydra', '古德斯坦；九头蛇'], th: 'PA', y: '1944 / 1982', en: 'Kirby–Paris 1982: Goodstein\'s theorem and the termination of the Hercules–Hydra game are unprovable in PA, by the ε₀ analysis of §11.', zh: 'Kirby–Paris 1982：古德斯坦定理与赫拉克勒斯–九头蛇游戏的终止性在 PA 中不可证，依据是 §11 中的 ε₀ 分析。' },
    { t: ['finite Kruskal', '有限克鲁斯卡尔'], th: 'ATR₀', y: '1980s', en: 'Friedman: for every k there is n such that any sequence T₁, …, Tₙ of finite trees with |Tᵢ| ≤ k + i has i &lt; j with Tᵢ embeddable in Tⱼ. Unprovable in ATR₀; the numbers involved (e.g. TREE(3)) are beyond comprehension.', zh: '弗里德曼：对每个 k 存在 n，使任意满足 |Tᵢ| ≤ k + i 的有限树序列 T₁, …, Tₙ 中都有 i &lt; j 使 Tᵢ 可嵌入 Tⱼ。在 ATR₀ 中不可证；涉及的数（如 TREE(3)）大得超乎想象。' },
    { t: ['graph minor theorem', '图子式定理'], th: 'Π¹₁-CA₀', y: '1987', en: 'Robertson–Seymour: finite graphs are well-quasi-ordered by the minor relation. Friedman–Robertson–Seymour 1987: not provable in Π¹₁-CA₀. A central theorem of modern combinatorics with real proof-theoretic strength.', zh: 'Robertson–Seymour：有限图在子式关系下是良拟序。Friedman–Robertson–Seymour 1987：在 Π¹₁-CA₀ 中不可证。这是现代组合学的核心定理，具有实在的证明论强度。' },
    { t: ['Boolean relation theory', '布尔关系理论'], th: 'ZFC', y: '1990s–', en: 'Friedman: explicit statements about functions on ℕ, provable in ZFC + “for each n there is an n-Mahlo cardinal” but not in ZFC (if consistent). Program status: debated how “natural” they are.', zh: '弗里德曼：关于 ℕ 上函数的明确命题，可在 ZFC +“对每个 n 存在 n-马洛基数”中证明，但（若一致）在 ZFC 中不可证。纲领状态：它们有多“自然”仍有争论。' },
  ];
  const tb = $('ciTiles');
  CI.forEach(c => {
    const d = document.createElement('div');
    d.className = 'tile2';
    d.innerHTML = `<div style="font-weight:800">${bil(c.t[0], c.t[1])}</div><div class="muted m" style="font-size:12px">${bil('unprovable in', '不可证于')} ${c.th} · ${c.y}</div>`;
    d.addEventListener('click', () => { tb.querySelectorAll('.tile2').forEach(x => x.classList.remove('sel')); d.classList.add('sel'); okBox($('ciInfo'), bi(c.en, c.zh), 'info'); });
    tb.appendChild(d);
  });
  checkYourself('cy12', ['Goodstein\'s theorem is…', '古德斯坦定理是……'], [
    ['false, the sequences can grow forever', '假的，序列可以永远增长', false],
    ['true, but not provable in PA', '真的，但在 PA 中不可证', true],
    ['independent of ZFC', '独立于 ZFC', false, 'ZFC proves it easily, using the well-ordering of ε₀.', 'ZFC 借助 ε₀ 的良序性可以轻松证明它。'],
  ], ['True (Goodstein 1944, via ordinals below ε₀) and unprovable in PA (Kirby–Paris 1982).', '真（古德斯坦 1944，借助 ε₀ 以下的序数），且在 PA 中不可证（Kirby–Paris 1982）。']);
})();

/* ================= §13 machines ================= */
(function machines() {
  const svg = $('tlSvg'), info = $('tlInfo');
  const EV = [
    [1976, 'Four Colour (computer)', '四色定理（计算机辅助）', 'Appel–Haken: computer-assisted proof, not a formal proof; it checked many configurations by program.', 'Appel–Haken：计算机辅助证明，但不是形式证明；用程序检验了大量构型。'],
    [2005, '4CT in Coq', '四色定理 Coq 化', 'Gonthier: a fully formal proof of the Four Colour Theorem in Coq.', 'Gonthier：在 Coq 中给出四色定理的完全形式证明。'],
    [2009, 'univalence', '泛等公理', 'Around 2009 Voevodsky formulated the univalence axiom and the simplicial model.', '约 2009 年，沃耶沃德斯基提出泛等公理与单纯集模型。'],
    [2012, 'Feit–Thompson', 'Feit–Thompson', 'Gonthier et al.: the odd order theorem (255 journal pages) formalized in Coq.', 'Gonthier 等：奇阶定理（期刊 255 页）在 Coq 中形式化。'],
    [2013, 'HoTT book', 'HoTT 之书', 'The Univalent Foundations Program at IAS publishes the HoTT book.', '普林斯顿高等研究院“泛等基础”项目出版 HoTT 之书。'],
    [2014, 'Flyspeck (Kepler)', 'Flyspeck（开普勒）', 'Hales et al. complete the formal proof of the Kepler conjecture (HOL Light + Isabelle); paper 2017.', 'Hales 等完成开普勒猜想的形式证明（HOL Light + Isabelle）；论文 2017 年发表。'],
    [2017, 'mathlib starts', 'mathlib 起步', 'The Lean mathematical library begins; by the mid-2020s it has well over 200,000 theorems.', 'Lean 数学库起步；到 2020 年代中期已有远超 20 万条定理。'],
    [2018, 'cubical TT', '立方类型论', 'Cohen–Coquand–Huber–Mörtberg: cubical type theory, a constructive model where univalence computes.', 'Cohen–Coquand–Huber–Mörtberg：立方类型论，一个让泛等公理能计算的构造性模型。'],
    [2022, 'Liquid Tensor', '液态张量实验', 'Scholze\'s 2020 challenge, a key theorem of condensed mathematics, fully formalized in Lean (July 2022).', 'Scholze 2020 年提出的挑战：凝聚数学的一个关键定理，在 Lean 中完全形式化（2022 年 7 月）。'],
    [2023, 'PFR in 3 weeks', 'PFR 三周完成', 'Gowers–Green–Manners–Tao prove the polynomial Freiman–Ruzsa conjecture (Nov 2023); a Lean formalization led by Tao is complete on 5 Dec 2023.', 'Gowers–Green–Manners–Tao 证明多项式 Freiman–Ruzsa 猜想（2023 年 11 月）；陶哲轩牵头的 Lean 形式化于 2023 年 12 月 5 日完成。'],
    [2024, 'AlphaProof', 'AlphaProof', 'DeepMind\'s AlphaProof/AlphaGeometry reach IMO silver-medal level; AlphaProof\'s solutions are Lean-checked.', 'DeepMind 的 AlphaProof/AlphaGeometry 达到 IMO 银牌水平；AlphaProof 的解答经 Lean 检验。'],
    [2025, 'IMO gold (LLMs)', 'IMO 金牌（大模型）', 'Systems from Google DeepMind and OpenAI reach gold-medal level at the IMO in natural language.', 'Google DeepMind 与 OpenAI 的系统以自然语言达到 IMO 金牌水平。'],
    [2026, 'AI manuscripts', 'AI 手稿', 'On 6 Oct 2026 OpenAI releases 722 AI-generated manuscripts claiming many results. OpenAI reports Lean formalizations for about 42% of the top-line results. Three manuscripts were withdrawn the next day for an error. Independent review has just begun.', '2026 年 10 月 6 日，OpenAI 公布 722 篇 AI 生成的手稿，声称了许多结果。据 OpenAI 称，约 42% 的主要结果有 Lean 形式化。次日有三篇因错误被撤回。独立审查才刚开始。'],
  ];
  el('line', { x1: 30, y1: 115, x2: 880, y2: 115, stroke: C.ink, 'stroke-width': 2.5 }, svg);
  T(svg, 880, 14, 'evenly spaced, not to scale · 等距排列，非比例', { 'text-anchor': 'end', 'font-size': 10.5, fill: C.grey });
  EV.forEach((e, i) => {
    const up = i % 2 === 0, lvl = Math.floor(i / 2) % 2;
    const x = 75 + i * 63, y = up ? 70 - lvl * 40 : 165 + lvl * 40;
    const g = el('g', { class: 'clk' }, svg);
    el('line', { x1: x, y1: 115, x2: x, y2: y + (up ? 6 : -14), stroke: '#ced4da' }, g);
    el('circle', { cx: x, cy: 115, r: 6, fill: e[0] === 2026 ? C.claim : C.acc }, g);
    T(g, x, y, e[1], { 'text-anchor': 'middle', 'font-size': 11, 'font-weight': 700, fill: e[0] === 2026 ? C.claim : C.ink });
    T(g, x, y + 13, `${e[0]}`, { 'text-anchor': 'middle', 'font-size': 10, fill: C.grey });
    g.addEventListener('click', () => okBox(info, `<b>${e[0]}</b> · ` + bi(e[3], e[4]), 'info'));
  });
  okBox(info, bi('Click an event.', '点击一个事件。'), 'info');
  const tr = $('trSvg'), tinfo = $('trInfo');
  const B = [
    { l: ['informal theorem', '非形式定理'], c: '#fff', who: 'human', en: 'What the paper claims, in words. Humans read it.', zh: '论文用文字声称的内容。由人来读。' },
    { l: ['formal statement', '形式陈述'], c: '#fff3bf', who: 'human!', en: '<b>The weak point.</b> Someone must check that the Lean statement means what the paper says: same definitions, no missing hypotheses, no trivializing typo. The kernel cannot check this.', zh: '<b>薄弱环节。</b>必须有人核对 Lean 陈述与论文的意思一致：定义相同、没有漏掉假设、没有让命题变平凡的笔误。内核无法检查这一点。' },
    { l: ['formal proof', '形式证明'], c: '#fff', who: 'anyone/AI', en: 'May be written by a human, an automated prover or an AI. Its origin does not matter for correctness.', zh: '可以由人、自动证明器或 AI 写出。对正确性而言，出处无关紧要。' },
    { l: ['kernel check', '内核检查'], c: '#d3f9d8', who: 'machine', en: 'A small trusted program checks every inference step. Kernel bugs are possible but rare; independent re-checkers reduce the risk.', zh: '一个小而可信的程序检查每一步推理。内核漏洞可能存在但罕见；独立的复核程序进一步降低风险。' },
    { l: ['axioms used', '所用公理'], c: '#e7ecff', who: 'logic', en: 'Lean\'s foundation: dependent type theory with universes, plus propositional extensionality, quotients and choice. Its consistency strength is that of ZFC + “for each n there are n inaccessible cardinals” (Carneiro 2019).', zh: 'Lean 的基础：带宇宙的依赖类型论，加上命题外延性、商类型与选择公理。其一致性强度等于 ZFC +“对每个 n 存在 n 个不可达基数”（Carneiro 2019）。' },
  ];
  B.forEach((b, i) => {
    const x = 20 + i * 178;
    const g = el('g', { class: 'clk' }, tr);
    el('rect', { x, y: 50, width: 150, height: 70, rx: 12, fill: b.c, stroke: i === 1 ? C.gold : C.ink, 'stroke-width': i === 1 ? 3.5 : 2 }, g);
    T(g, x + 75, 80, b.l[0], { 'text-anchor': 'middle', 'font-size': 13, 'font-weight': 800 });
    T(g, x + 75, 99, b.l[1], { 'text-anchor': 'middle', 'font-size': 12, fill: C.grey });
    T(g, x + 75, 145, b.who, { 'text-anchor': 'middle', 'font-size': 11.5, fill: i === 1 ? C.claim : C.acc, 'font-weight': 700 });
    if (i < B.length - 1) el('path', { d: `M${x + 152},85 L${x + 176},85`, stroke: C.ink, 'stroke-width': 2 }, tr);
    g.addEventListener('click', () => okBox(tinfo, bi(b.en, b.zh), i === 1 ? 'warn' : 'info'));
  });
  T(tr, 20, 30, 'chain of trust · 信任链 (click · 点击)', { 'font-size': 12.5, 'font-weight': 700, fill: C.grey });
  okBox(tinfo, bi('Click a box. The yellow one is where humans are still essential.', '点击方框。黄色那一环仍然离不开人。'), 'info');
  checkYourself('cy13', ['Lean accepted a proof of theorem X. What is guaranteed?', 'Lean 接受了定理 X 的一个证明。什么得到了保证？'], [
    ['X as stated in the paper is true', '论文中所述的 X 为真', false, 'Only if the formal statement faithfully expresses the paper\'s X.', '只有当形式陈述忠实地表达了论文中的 X 时才成立。'],
    ['The formal statement follows from Lean\'s axioms (if the kernel is correct)', '形式陈述可由 Lean 的公理推出（假定内核正确）', true],
    ['X is new and important', 'X 是新的、重要的', false],
  ], ['Exactly that, and no more. Faithfulness of the statement, and whether X matters, are human judgements.', '正是这个，仅此而已。陈述是否忠实、X 是否重要，都要由人来判断。']);
})();

/* ================= §14 frontier map ================= */
const FRONTIER = [
  { a: 'set', t: 'indep', s: 'ind', en: 'The continuum problem (CH)', zh: '连续统问题（CH）', l: 27, m: ['Independent of ZFC (Gödel 1938, Cohen 1963). The live question: which new axioms are justified, and what do they say about 2<sup>ℵ₀</sup>?', '独立于 ZFC（哥德尔 1938，科恩 1963）。仍在争论的是：哪些新公理是合理的，它们对 2<sup>ℵ₀</sup> 说了什么？'] },
  { a: 'set', t: 'struct', s: 'conj', en: 'Ultimate L conjecture', zh: '终极 L 猜想', l: 27, m: ['Woodin: an L-like inner model that accommodates all large cardinals would give a canonical picture of V.', '伍丁：一个容纳所有大基数、像 L 一样的内模型将给出 V 的典范图景。'] },
  { a: 'set', t: 'struct', s: 'conj', en: 'HOD conjecture', zh: 'HOD 猜想', l: 22, m: ['Is HOD “close to V” above an extendible cardinal? Woodin\'s HOD dichotomy (a theorem) makes it the fork in the road.', '在可扩基数之上 HOD 是否“接近 V”？伍丁的 HOD 二分定理使它成为道路的分岔口。'] },
  { a: 'set', t: 'indep', s: 'thm', en: 'MM⁺⁺ ⇒ (*)', zh: 'MM⁺⁺ ⇒ (*)', l: 27, m: ['Asperó–Schindler 2021: two rival strong axioms agree, both giving 2<sup>ℵ₀</sup> = ℵ₂.', 'Asperó–Schindler 2021：两条相互竞争的强公理一致，都给出 2<sup>ℵ₀</sup> = ℵ₂。'] },
  { a: 'set', t: 'struct', s: 'open', en: 'pcf: is ℵ<sub>ω₄</sub> sharp?', zh: 'pcf：ℵ<sub>ω₄</sub> 是最优界吗？', l: 27, m: ['Shelah: if ℵ<sub>ω</sub> is a strong limit then 2<sup>ℵ<sub>ω</sub></sup> < ℵ<sub>ω₄</sub>. Can ω₄ be improved to ω₁?', '谢拉赫：若 ℵ<sub>ω</sub> 是强极限，则 2<sup>ℵ<sub>ω</sub></sup> < ℵ<sub>ω₄</sub>。ω₄ 能改进为 ω₁ 吗？'] },
  { a: 'set', t: 'struct', s: 'open', en: 'Inner model for a supercompact', zh: '超紧基数的内模型', l: 25, m: ['Extending fine-structural inner model theory beyond Woodin cardinals.', '把精细结构内模型理论推广到伍丁基数之上。'] },
  { a: 'model', t: 'class', s: 'open', en: 'Vaught\'s conjecture', zh: '沃特猜想', l: 28, sec: 's2', m: ['How hard is it to classify the countable models of a theory? (First-order version open; a 2026 counterexample for L<sub>ω₁,ω</sub> is claimed.)', '分类一个理论的可数模型有多难？（一阶版本未解决；2026 年有人声称给出了 L<sub>ω₁,ω</sub> 版本的反例。）'] },
  { a: 'model', t: 'class', s: 'open', c: 1, en: 'NSOP₂ = NSOP₃?', zh: 'NSOP₂ = NSOP₃？', l: 28, sec: 's1', m: ['Where exactly are the dividing lines above simplicity? (Claimed yes: Chernikov, Aug 2026 preprint.)', '简单性之上的分界线到底在哪里？（Chernikov 2026 年 8 月的预印本声称答案为是。）'] },
  { a: 'model', t: 'class', s: 'conj', c: 1, en: 'Eventual categoricity (AECs)', zh: '最终范畴性（抽象初等类）', l: 28, sec: 's1', m: ['Morley\'s theorem beyond first-order logic.', '把莫利定理推广到一阶逻辑之外。'] },
  { a: 'model', t: 'dec', s: 'open', en: 'Tarski\'s exponential problem', zh: '塔斯基指数函数问题', l: 28, sec: 's4', m: ['Can an algorithm decide every statement about (ℝ, +, ·, exp)?', '能否用算法判定关于 (ℝ, +, ·, exp) 的每个命题？'] },
  { a: 'model', t: 'struct', s: 'conj', en: 'Schanuel\'s conjecture', zh: '沙努埃尔猜想', l: 28, sec: 's4', m: ['The master conjecture of transcendence theory; implies decidability of ℝ<sub>exp</sub>.', '超越数论的总猜想；蕴涵 ℝ<sub>exp</sub> 的可判定性。'] },
  { a: 'model', t: 'class', s: 'conj', en: 'Zilber: ℂ<sub>exp</sub> quasiminimal', zh: '齐尔伯：ℂ<sub>exp</sub> 拟极小', l: 28, sec: 's4', m: ['Is complex exponentiation as tame as it could possibly be?', '复指数函数是否驯顺到了极致？'] },
  { a: 'model', t: 'struct', s: 'conj', en: 'Zilber–Pink conjecture', zh: '齐尔伯–平克猜想', l: 28, sec: 's3', m: ['Unlikely intersections; o-minimal counting is the main tool.', '不太可能的交；o-极小计数是主要工具。'] },
  { a: 'comp', t: 'dec', s: 'open', c: 1, en: 'Hilbert\'s 10th problem over ℚ', zh: 'ℚ 上的希尔伯特第十问题', l: 28, sec: 's6', m: ['Can an algorithm decide whether a variety has a rational point?', '能否用算法判断一个代数簇有没有有理点？'] },
  { a: 'comp', t: 'dec', s: 'open', en: 'Hilbert\'s 10th problem over ℂ(t)', zh: 'ℂ(t) 上的希尔伯特第十问题', l: 28, sec: 's6', m: ['The hardest remaining function-field case.', '函数域情形中最难的遗留问题。'] },
  { a: 'comp', t: 'struct', s: 'open', c: 1, en: 'Rigidity of the Turing degrees', zh: '图灵度的刚性', l: 17, sec: 's7', m: ['Does ≤<sub>T</sub> alone determine every degree?', '单凭 ≤<sub>T</sub> 能否确定每个度？'] },
  { a: 'comp', t: 'class', s: 'conj', en: 'Martin\'s conjecture', zh: '马丁猜想', l: 17, sec: 's7', m: ['Why are natural degrees always iterated jumps?', '为什么自然的度总是迭代跳跃？'] },
  { a: 'comp', t: 'indep', s: 'open', en: 'First-order part of RT²₂', zh: 'RT²₂ 的一阶部分', l: 28, sec: 's8', m: ['Exactly which arithmetic does Ramsey\'s theorem for pairs prove?', '二元拉姆齐定理究竟能证明哪些算术命题？'] },
  { a: 'comp', t: 'indep', s: 'open', en: 'Strength of Hindman\'s theorem', zh: 'Hindman 定理的强度', l: 28, sec: 's8', m: ['Where does a natural combinatorial theorem sit above ACA₀?', '一个自然的组合定理在 ACA₀ 之上处于什么位置？'] },
  { a: 'comp', t: 'class', s: 'open', en: 'KL randomness = ML randomness?', zh: 'KL 随机 = ML 随机？', l: 28, sec: 's9', m: ['Which definition of an individual random sequence is the right one?', '哪个“单个随机序列”的定义才是对的？'] },
  { a: 'proof', t: 'dec', s: 'conj', en: 'P vs NP', zh: 'P 与 NP', l: 28, sec: 's10', m: ['Is finding a solution harder than checking one?', '找到解是否比验证解更难？'] },
  { a: 'proof', t: 'dec', s: 'open', en: 'Frege lower bounds / NP vs coNP', zh: '弗雷格下界 / NP 与 coNP', l: 28, sec: 's10', m: ['Do some tautologies need exponentially long proofs?', '是否有些重言式需要指数长的证明？'] },
  { a: 'proof', t: 'class', s: 'open', en: 'A logic for P', zh: '刻画 P 的逻辑', l: 28, sec: 's10', m: ['Can polynomial time be captured by a logic on unordered structures?', '能否在无序结构上用一种逻辑刻画多项式时间？'] },
  { a: 'proof', t: 'struct', s: 'prog', en: 'Ordinal analysis of Π¹₂-CA₀, Z₂, ZFC', zh: 'Π¹₂-CA₀、Z₂、ZFC 的序数分析', l: 21, sec: 's11', m: ['Consistency proofs with a precise price tag for stronger theories.', '为更强的理论给出附带精确价签的一致性证明。'] },
  { a: 'proof', t: 'indep', s: 'prog', en: 'Natural statements needing large cardinals', zh: '需要大基数的自然命题', l: 12, sec: 's12', m: ['Does ordinary finite mathematics ever need axioms beyond ZFC?', '普通的有限数学是否会需要 ZFC 之外的公理？'] },
  { a: 'found', t: 'struct', s: 'open', en: 'Semi-simplicial types in HoTT', zh: 'HoTT 中的半单纯类型', l: 28, sec: 's13', m: ['Can type theory express infinite coherence internally?', '类型论能否在内部表达无穷的相干性？'] },
  { a: 'found', t: 'struct', s: 'prog', en: 'Formalizing modern mathematics (e.g. FLT in Lean)', zh: '形式化现代数学（如在 Lean 中证 FLT）', l: 28, sec: 's13', m: ['Make proofs machine-checkable at research scale.', '让研究规模的证明能被机器检验。'] },
];
const AREAS = { set: ['Set theory (L27)', '集合论（第 27 课）', '#2f9e44'], model: ['Model theory', '模型论', '#0c8599'], comp: ['Computability', '可计算性', '#c2255c'], proof: ['Proofs & complexity', '证明与复杂性', '#5f3dc4'], found: ['Foundations', '基础', '#f08c00'] };
const TYPES = { class: ['classification', '分类'], indep: ['independence / strength', '独立性 / 强度'], dec: ['decidability', '可判定性'], struct: ['structure', '结构'] };
(function fmap() {
  const flt = { a: null, t: null, s: null };
  const svg = $('fmSvg'), cards = $('fmCards');
  const centers = { set: [160, 115], model: [450, 105], comp: [740, 125], proof: [300, 320], found: [640, 325] };
  const pos = [];
  Object.keys(AREAS).forEach(a => {
    const list = FRONTIER.filter(f => f.a === a), [cx, cy] = centers[a];
    list.forEach((f, i) => { const ang = i / list.length * 2 * Math.PI - Math.PI / 2, r = 72; pos[FRONTIER.indexOf(f)] = [cx + r * Math.cos(ang), cy + r * 0.78 * Math.sin(ang)]; });
  });
  const pass = f => (!flt.a || f.a === flt.a) && (!flt.t || f.t === flt.t) && (!flt.s || f.s === flt.s || (flt.s === 'claim' && f.c));
  function cardHtml(f, i) {
    const href = f.l === 28 ? '#' + f.sec : `lesson${f.l}.html`;
    return `<div class="fcard" id="fc${i}" style="border-left-color:${AREAS[f.a][2]}"><div class="t">${bil(f.en, f.zh)}</div>
      <div style="margin:3px 0">${ST(f.s)}${f.c ? ST('claim') : ''}<span class="muted" style="font-size:12px">${bil(TYPES[f.t][0], TYPES[f.t][1])}</span></div>
      ${bi(f.m[0], f.m[1])} <a href="${href}">→ ${f.l === 28 ? '§' + f.sec.slice(1) : 'L' + f.l}</a></div>`;
  }
  function draw() {
    svg.innerHTML = '';
    Object.entries(centers).forEach(([a, [cx, cy]]) => {
      el('ellipse', { cx, cy, rx: 130, ry: 95, fill: AREAS[a][2], 'fill-opacity': flt.a && flt.a !== a ? .03 : .08, stroke: AREAS[a][2], 'stroke-dasharray': '4 4' }, svg);
      T(svg, cx, cy + 4, AREAS[a][0], { 'text-anchor': 'middle', 'font-size': 12.5, 'font-weight': 800, fill: AREAS[a][2] });
      T(svg, cx, cy + 19, AREAS[a][1], { 'text-anchor': 'middle', 'font-size': 11.5, fill: AREAS[a][2] });
    });
    FRONTIER.forEach((f, i) => {
      const [x, y] = pos[i], ok = pass(f);
      const g = el('g', { class: 'clk', opacity: ok ? 1 : .15 }, svg);
      el('circle', { cx: x, cy: y, r: 10, fill: ST_COL[f.s], stroke: f.c ? C.claim : '#fff', 'stroke-width': f.c ? 3.5 : 2 }, g);
      const title = el('title', {}, g); title.textContent = (f.en + ' · ' + f.zh).replace(/<[^>]+>/g, '');
      g.addEventListener('click', () => {
        const c = $('fc' + i);
        cards.querySelectorAll('.fcard').forEach(x => x.classList.remove('hi'));
        if (c) { c.classList.add('hi'); c.scrollIntoView({ block: 'nearest', behavior: 'smooth' }); }
      });
      g.addEventListener('mouseenter', () => { const lab = T(svg, x, y - 15, f.en.replace(/<[^>]+>/g, ''), { 'text-anchor': 'middle', 'font-size': 11.5, 'font-weight': 700, class: 'hov s' }); lab.style.pointerEvents = 'none'; });
      g.addEventListener('mouseleave', () => svg.querySelectorAll('.hov').forEach(z => z.remove()));
    });
    const sl = Object.keys(ST_COL).filter(k => k !== 'ind' && k !== 'ann');
    sl.forEach((k, i) => { el('circle', { cx: 30 + i * 140, cy: 455, r: 7, fill: ST_COL[k] }, svg); T(svg, 42 + i * 140, 459, ST_TXT[k][0] + ' · ' + ST_TXT[k][1], { 'font-size': 11 }); });
    cards.innerHTML = FRONTIER.map((f, i) => pass(f) ? cardHtml(f, i) : '').join('');
  }
  function chipbar(box, label, items, key) {
    box.innerHTML = `<span class="muted" style="font-size:13px;min-width:70px">${label}</span>`;
    const all = [[null, 'all', '全部'], ...items];
    all.forEach(([k, en, zh]) => {
      const c = document.createElement('span');
      c.className = 'chip' + (k === null ? ' on' : '');
      c.innerHTML = bil(en, zh);
      c.addEventListener('click', () => { flt[key] = k; box.querySelectorAll('.chip').forEach(x => x.classList.remove('on')); c.classList.add('on'); draw(); });
      box.appendChild(c);
    });
  }
  chipbar($('fmArea'), bil('Area', '领域'), Object.entries(AREAS).map(([k, v]) => [k, v[0], v[1]]), 'a');
  chipbar($('fmType'), bil('Type', '类型'), Object.entries(TYPES).map(([k, v]) => [k, v[0], v[1]]), 't');
  chipbar($('fmStat'), bil('Status', '状态'), ['thm', 'open', 'conj', 'prog', 'ind', 'claim'].map(k => [k, ST_TXT[k][0], ST_TXT[k][1]]), 's');
  draw();
  checkYourself('cy14', ['Which of these is a research program rather than a yes/no question?', '下列哪一个是研究纲领，而不是是非题？'], [
    ['Vaught\'s conjecture', '沃特猜想', false],
    ['Finding natural statements that need large cardinals', '寻找需要大基数的自然命题', true],
    ['Hilbert\'s tenth problem over ℚ', 'ℚ 上的希尔伯特第十问题', false],
  ], ['“Natural” is not a mathematical predicate, so concrete incompleteness is a program: success is judged by how convincing the examples are, not by a single proof.', '“自然”不是数学谓词，所以具体不完全性是一个纲领：成功与否取决于例子有多令人信服，而不是某一个证明。']);
})();

/* ================= Exercises ================= */
function selectRow(box, it, opts) {
  const row = document.createElement('div');
  row.className = 'matchrow';
  row.innerHTML = `<div class="cond">${it.q}</div><select><option value="">—</option>${opts.map(o => `<option value="${o[0]}" data-en="${o[1]}" data-zh="${o[2] || o[1]}">${optLabel(o[1], o[2] || o[1])}</option>`).join('')}</select><span class="fb muted" style="font-size:13px"></span>`;
  box.appendChild(row);
  return row;
}
// Option labels inside <select> can't hold spans, so they are relabelled whenever the language switch is used.
const optLabel = (en, zh) => { const m = localStorage.getItem('lang') || 'both'; return m === 'en' ? en : m === 'zh' ? zh : (en === zh ? en : `${en} · ${zh}`); };
document.querySelectorAll('.lang-switch button').forEach(b => b.addEventListener('click', () => {
  document.querySelectorAll('option[data-en]').forEach(o => { o.textContent = optLabel(o.dataset.en, o.dataset.zh); });
}));
// Exercises whose answer has been shown in this page session: never marked as solved afterwards.
const revealed = new Set();
const NOT_COUNTED = ['(The answer was shown earlier, so this is not counted as solved.)', '（之前已看过答案，因此不计为完成。）'];
function markIfEarned(id) { if (!revealed.has(id)) { Progress.mark(id); return ''; } return ' ' + bi(NOT_COUNTED[0], NOT_COUNTED[1]); }
function gradeSelects(rows, items, show, msg, id, okText) {
  let right = 0;
  if (show) revealed.add(id);
  rows.forEach((r, i) => {
    const s = r.querySelector('select');
    if (show) s.value = items[i].a;
    s.classList.remove('right', 'wrong');
    const fb = r.querySelector('.fb');
    if (s.value === items[i].a) { right++; s.classList.add('right'); fb.innerHTML = items[i].why ? bi(items[i].why[0], items[i].why[1]) : ''; }
    else { if (s.value) s.classList.add('wrong'); fb.innerHTML = ''; }
  });
  if (show) { okBox(msg, bi('Answers filled in (not counted as solved).', '已填入答案（不计为完成）。'), 'info'); return; }
  if (right === items.length) { const extra = markIfEarned(id); okBox(msg, '✓ ' + bi(okText[0], okText[1]) + extra); }
  else okBox(msg, bi(`${right} / ${items.length} correct. Red ones are wrong.`, `答对 ${right} / ${items.length}，红色的错了。`), 'warn');
}

/* E1 */
(function e1() {
  const O = [['thm', 'theorem', '定理'], ['open', 'open question', '未解决问题'], ['conj', 'conjecture', '猜想'], ['claim', 'claimed 2026, unverified', '2026 年新近声称、未核实']];
  const items = [
    { q: bi('Morley: categoricity in one uncountable cardinal implies categoricity in all.', '莫利：在一个不可数基数上范畴蕴涵在所有不可数基数上范畴。'), a: 'thm', why: ['Morley 1965.', '莫利 1965。'] },
    { q: bi('Is Th(ℝ, +, ·, exp) decidable?', 'Th(ℝ, +, ·, exp) 可判定吗？'), a: 'open', why: ['Tarski\'s problem; known only conditionally.', '塔斯基问题；只有条件性结果。'] },
    { q: bi('Schanuel\'s conjecture.', '沙努埃尔猜想。'), a: 'conj' },
    { q: bi('H10 is undecidable over the ring of integers of every number field.', '对每个数域的整数环，第十问题都不可判定。'), a: 'thm', why: ['Koymans–Pagano (arXiv 2024; JAMS 2026) and Alpöge–Bhargava–Ho–Shnidman (arXiv 2025; Invent. Math. 2026).', 'Koymans–Pagano（2024 年 arXiv；2026 年 JAMS）与 Alpöge–Bhargava–Ho–Shnidman（2025 年 arXiv；2026 年 Invent. Math.）。'] },
    { q: bi('H10 is undecidable over ℚ.', 'ℚ 上的第十问题不可判定。'), a: 'claim', why: ['Open as of 2025. An AI-generated manuscript (OpenAI, Sept 2026) claims it; no Lean formalization, not yet verified.', '以 2025 年为准未解决。2026 年 9 月一篇 AI 生成的手稿（OpenAI）声称证明了它；没有 Lean 形式化，尚未核实。'] },
    { q: bi('ℝ<sub>exp</sub> is o-minimal.', 'ℝ<sub>exp</sub> 是 o-极小的。'), a: 'thm', why: ['Wilkie 1996.', '威尔基 1996。'] },
    { q: bi('Is Kolmogorov–Loveland randomness the same as Martin-Löf randomness?', '柯尔莫哥洛夫–洛夫兰随机性与马丁-洛夫随机性相同吗？'), a: 'open' },
    { q: bi('P ≠ NP.', 'P ≠ NP。'), a: 'conj' },
    { q: bi('RT²₂ does not imply WKL₀ over RCA₀.', '在 RCA₀ 上 RT²₂ 不蕴涵 WKL₀。'), a: 'thm', why: ['Liu 2012.', '刘路 2012。'] },
    { q: bi('The Turing degrees have no non-trivial automorphism.', '图灵度没有非平凡自同构。'), a: 'claim', why: ['Open as of 2025. Claimed in an AI-generated manuscript (OpenAI, Sept 2026) with a Lean formalization and an exposition by A. Marks; not yet refereed.', '以 2025 年为准未解决。2026 年 9 月一篇 AI 生成的手稿（OpenAI）声称证明了它，附 Lean 形式化，A. Marks 写了阐释；尚未经过审稿。'] },
    { q: bi('The André–Oort conjecture (in full generality).', '安德烈–奥尔特猜想（一般情形）。'), a: 'thm', why: ['Despite the name: Pila–Shankar–Tsimerman 2021.', '别被名字骗了：Pila–Shankar–Tsimerman 2021。'] },
    { q: bi('Martin\'s conjecture.', '马丁猜想。'), a: 'conj', why: ['Partial results: Slaman–Steel, Lutz–Siskind.', '部分结果：Slaman–Steel、Lutz–Siskind。'] },
  ];
  const box = $('e1List');
  const rows = items.map(it => selectRow(box, it, O));
  $('e1Check').addEventListener('click', () => gradeSelects(rows, items, false, $('e1Msg'), 'L28E1', ['All correct. Note the traps: a “conjecture” by name can be a theorem (André–Oort), and a 2026 announcement is not yet a theorem.', '全对。注意陷阱：名字叫“猜想”的可能已是定理（安德烈–奥尔特），而 2026 年的宣布还不是定理。']));
  $('e1Show').addEventListener('click', () => gradeSelects(rows, items, true, $('e1Msg'), 'L28E1'));
})();

/* E2 */
(function e2() {
  const O = [['RCA', 'RCA₀'], ['WKL', 'WKL₀'], ['ACA', 'ACA₀'], ['ATR', 'ATR₀'], ['PI', 'Π¹₁-CA₀'], ['none', 'none of the Big Five', '不属于五大系统']];
  const items = [
    { q: bi('Bolzano–Weierstrass theorem', '波尔查诺–魏尔斯特拉斯定理'), a: 'ACA' },
    { q: bi('Heine–Borel: every countable open cover of [0, 1] has a finite subcover', '海涅–博雷尔：[0, 1] 的每个可数开覆盖都有有限子覆盖'), a: 'WKL' },
    { q: bi('Any two countable well-orders are comparable', '任意两个可数良序可比较'), a: 'ATR' },
    { q: bi('Cantor–Bendixson: every closed set = perfect ∪ countable', '康托尔–本迪克松：每个闭集 = 完美集 ∪ 可数集'), a: 'PI' },
    { q: bi('Intermediate value theorem', '介值定理'), a: 'RCA' },
    { q: bi('Gödel\'s completeness theorem (countable languages)', '哥德尔完备性定理（可数语言）'), a: 'WKL' },
    { q: bi('Ramsey\'s theorem for pairs, 2 colours (RT²₂)', '二元两色拉姆齐定理（RT²₂）'), a: 'none', why: ['Strictly between RCA₀ and ACA₀, incomparable with WKL₀.', '严格介于 RCA₀ 与 ACA₀ 之间，与 WKL₀ 不可比。'] },
    { q: bi('Ramsey\'s theorem for triples, 2 colours (RT³₂)', '三元两色拉姆齐定理（RT³₂）'), a: 'ACA' },
    { q: bi('Every countable vector space over ℚ has a basis', 'ℚ 上每个可数向量空间都有基'), a: 'ACA' },
    { q: bi('Open (Σ⁰₁) determinacy', '开集（Σ⁰₁）决定性'), a: 'ATR' },
  ];
  const box = $('e2List');
  const rows = items.map(it => selectRow(box, it, O));
  $('e2Check').addEventListener('click', () => gradeSelects(rows, items, false, $('e2Msg'), 'L28E2', ['All placed. The Big Five pattern is remarkably robust; Ramsey for pairs is the famous exception.', '全部放对。五大格局非常稳健；二元拉姆齐定理是著名的例外。']));
  $('e2Show').addEventListener('click', () => gradeSelects(rows, items, true, $('e2Msg'), 'L28E2'));
})();

/* E3 */
(function e3() {
  const TH = [['ACF', [1, 1, 1]], ['RCF', [0, 1, 0]], ['random graph · 随机图', [0, 0, 1]], ['pseudofinite fields · 伪有限域', [0, 0, 1]], ['(ℤ, +)', [1, 1, 1]], ['(ℤ, +, ·)', [0, 0, 0]], ['ℚₚ', [0, 1, 0]], ['DLO', [0, 1, 0]]];
  const COLS = [['stable', '稳定'], ['NIP', 'NIP'], ['simple', '简单']];
  const st = TH.map(() => [null, null, null]);
  let h = `<table class="grid3"><tr><th></th>${COLS.map(c => `<th>${bil(c[0], c[1])}</th>`).join('')}</tr>`;
  TH.forEach((t, r) => { h += `<tr><th style="text-align:left">${t[0]}</th>${COLS.map((_, c) => `<td class="c" data-r="${r}" data-c="${c}"></td>`).join('')}</tr>`; });
  $('e3Grid').innerHTML = h + '</table>';
  const cells = [...$('e3Grid').querySelectorAll('td.c')];
  const paint = td => { const v = st[td.dataset.r][td.dataset.c]; td.textContent = v === null ? '' : v ? '✓' : '✗'; td.style.color = v ? C.tru : C.fal; };
  cells.forEach(td => td.addEventListener('click', () => {
    const r = +td.dataset.r, c = +td.dataset.c;
    st[r][c] = st[r][c] === null ? 1 : st[r][c] === 1 ? 0 : null;
    td.classList.remove('right', 'wrong'); paint(td);
  }));
  function check(show) {
    let ok = 0;
    cells.forEach(td => {
      const r = +td.dataset.r, c = +td.dataset.c, want = TH[r][1][c];
      if (show) st[r][c] = want;
      paint(td);
      td.classList.remove('right', 'wrong');
      if (st[r][c] === want) { ok++; td.classList.add('right'); } else if (st[r][c] !== null) td.classList.add('wrong');
    });
    if (show) revealed.add('L28E3');
    if (show) return okBox($('e3Msg'), bi('Answers filled in. Reasons are in the §1 map: click each theory there.', '已填入答案。理由见 §1 的地图：在那里点击各个理论。'), 'info');
    if (ok === cells.length) { okBox($('e3Msg'), '✓ ' + bi('All 24 correct. Check the consistency rule: every row with stable ✓ has NIP ✓ and simple ✓, and no row has NIP ✓ and simple ✓ without stable ✓.', '24 格全对。检查一致性规则：凡稳定为 ✓ 的行，NIP 与简单都是 ✓；没有哪一行 NIP 与简单都是 ✓ 而稳定不是 ✓。') + markIfEarned('L28E3')); }
    else okBox($('e3Msg'), bi(`${ok} / ${cells.length} correct.`, `答对 ${ok} / ${cells.length}。`), 'warn');
  }
  $('e3Check').addEventListener('click', () => check(false));
  $('e3Show').addEventListener('click', () => check(true));
})();

/* E4 */
(function e4() {
  const svg = $('e4Svg');
  const XS = [80, 220, 330, 470, 610];
  const st = XS.map(() => 0); // 0 none, 1 chosen, 2 chosen & in subset
  let aDone = false;
  function draw() {
    svg.innerHTML = '';
    el('line', { x1: 30, y1: 60, x2: 670, y2: 60, stroke: C.ink, 'stroke-width': 2 }, svg);
    XS.forEach((x, i) => {
      const g = el('g', { class: 'clk' }, svg);
      el('circle', { cx: x, cy: 60, r: 13, fill: st[i] === 2 ? C.tru : st[i] === 1 ? '#fff' : '#e9ecef', stroke: st[i] ? C.ink : '#adb5bd', 'stroke-width': st[i] ? 3 : 1.5 }, g);
      T(g, x, 34, 'PQRST'[i], { 'text-anchor': 'middle', 'font-size': 14, 'font-weight': 800 });
      T(g, x, 98, ['', 'chosen · 选中', 'in subset · 子集内'][st[i]], { 'text-anchor': 'middle', 'font-size': 11, fill: C.grey });
      g.addEventListener('click', () => { st[i] = (st[i] + 1) % 3; draw(); checkA(false); });
    });
  }
  function checkA(verbose) {
    const ch = st.map((v, i) => v ? i : -1).filter(i => i >= 0);
    const msg = $('e4aMsg');
    aDone = false;
    if (ch.length !== 3) { if (verbose || ch.length > 3) okBox(msg, bi(`Click points to cycle: grey → chosen (white) → in subset (green). You have ${ch.length} chosen; choose exactly 3.`, `点击点循环切换：灰 → 选中（白）→ 子集内（绿）。你选了 ${ch.length} 个；请恰好选 3 个。`), 'info'); else clearBox(msg); return; }
    const ins = ch.map(i => st[i] === 2);
    const f = ins.indexOf(true), l = ins.lastIndexOf(true);
    let gap = false;
    for (let j = f; j <= l && f >= 0; j++) if (!ins[j]) gap = true;
    if (gap) { aDone = true; okBox(msg, '✓ ' + bi('Right: an interval containing the two outer points contains the middle one too. Every 3-point set fails this way, so intervals have VC dimension 2.', '对：包含两端两点的区间必然包含中间的点。任何 3 点集都这样失败，所以区间族的 VC 维是 2。')); }
    else okBox(msg, bi('An interval can cut out this subset of your 3 points. Look for a subset with a “gap”.', '区间可以从你的 3 个点中切出这个子集。找一个中间“断开”的子集。'), 'warn');
  }
  $('e4Mode').innerHTML = `<button class="btn small ghost" id="e4Reset">${bil('Reset points', '重置点')}</button>`;
  $('e4Reset').addEventListener('click', () => { st.fill(0); draw(); clearBox($('e4aMsg')); });
  draw();
  const isInf = v => /^(∞|inf|infinite|infinity|无穷|无穷大|无限)$/i.test(v.trim());
  $('e4Check').addEventListener('click', () => {
    checkA(true);
    const a = $('e4i').value.trim() === '2', b = $('e4h').value.trim() === '3', c = isInf($('e4r').value);
    [['e4i', a], ['e4h', b], ['e4r', c]].forEach(([id, ok]) => $(id).style.borderColor = ok ? C.tru : C.fal);
    if (aDone && a && b && c) { okBox($('e4Msg'), '✓ ' + bi('All correct. 2, 3, and ∞: the random graph shatters every finite set (extension axioms), which is exactly the independence property.', '全对。2、3、∞：随机图能打散每个有限集（扩张公理），这正是独立性质。') + markIfEarned('L28E4')); }
    else okBox($('e4Msg'), bi(`${aDone ? '(a) done. ' : '(a) not yet. '}Numbers: ${[a, b, c].filter(Boolean).length} / 3 correct.`, `${aDone ? '(a) 已完成。' : '(a) 尚未完成。'}数值：答对 ${[a, b, c].filter(Boolean).length} / 3。`), 'warn');
  });
  $('e4Show').addEventListener('click', () => {
    revealed.add('L28E4');
    st.fill(0); st[0] = 2; st[2] = 1; st[4] = 2; draw(); checkA(true);
    $('e4i').value = '2'; $('e4h').value = '3'; $('e4r').value = '∞';
    okBox($('e4Msg'), bi('Answer: choose P, R, T and the subset {P, T}. VC dimensions: intervals 2, half-planes 3, edge relation of the random graph ∞. (Not counted as solved.)', '答案：选 P、R、T，子集取 {P, T}。VC 维：区间 2，半平面 3，随机图的边关系 ∞。（不计为完成。）'), 'info');
  });
})();

/* E5 */
(function e5() {
  const M = [
    ['cls', 'measure how hard it is to classify countable models', '衡量分类可数模型有多难'],
    ['nat', 'explain why natural degrees are iterated jumps', '解释为什么自然的度都是迭代跳跃'],
    ['rat', 'decide algorithmically whether varieties have rational points', '用算法判断代数簇是否有有理点'],
    ['nt', 'use logic to count rational points in number theory', '用逻辑来数数论中的有理点'],
    ['con', 'consistency proofs with a precise price tag', '附带精确价签的一致性证明'],
    ['np', 'show some tautologies need long proofs (NP ≠ coNP)', '证明有些重言式需要很长的证明（NP ≠ coNP）'],
    ['rnd', 'find the right definition of a random sequence', '找到随机序列的正确定义'],
    ['inc', 'show incompleteness affects ordinary combinatorics', '表明不完全性会影响普通组合数学'],
  ];
  const items = [
    { q: bi('Vaught\'s conjecture', '沃特猜想'), a: 'cls' }, { q: bi('Martin\'s conjecture', '马丁猜想'), a: 'nat' },
    { q: bi('Hilbert\'s tenth problem over ℚ', 'ℚ 上的希尔伯特第十问题'), a: 'rat' }, { q: bi('Pila–Wilkie and André–Oort', '皮拉–威尔基与安德烈–奥尔特'), a: 'nt' },
    { q: bi('Ordinal analysis of Π¹₂-CA₀', 'Π¹₂-CA₀ 的序数分析'), a: 'con' }, { q: bi('Lower bounds for Frege proofs', '弗雷格证明的下界'), a: 'np' },
    { q: bi('KL randomness vs ML randomness', 'KL 随机性与 ML 随机性'), a: 'rnd' }, { q: bi('Paris–Harrington, graph minor unprovability', '帕里斯–哈灵顿、图子式定理的不可证性'), a: 'inc' },
  ];
  const box = $('e5List');
  const shuffled = [...M].sort(() => Math.random() - .5);
  const rows = items.map(it => selectRow(box, it, shuffled));
  $('e5Check').addEventListener('click', () => gradeSelects(rows, items, false, $('e5Msg'), 'L28E5', ['All matched. Knowing <i>why</i> a problem matters is what lets you judge partial progress.', '全部配对正确。知道一个问题<i>为什么</i>重要，你才能判断部分进展的价值。']));
  $('e5Show').addEventListener('click', () => gradeSelects(rows, items, true, $('e5Msg'), 'L28E5'));
})();

/* E6 */
(function e6() {
  const items = [
    { s: ['Schanuel\'s conjecture ⇒ Th(ℝ<sub>exp</sub>) is decidable', '沙努埃尔猜想 ⇒ Th(ℝ<sub>exp</sub>) 可判定'], a: 1, en: 'Known: Macintyre–Wilkie 1996 (via real Schanuel).', zh: '已知：Macintyre–Wilkie 1996（经由实沙努埃尔猜想）。' },
    { s: ['P = NP ⇒ NP = coNP', 'P = NP ⇒ NP = coNP'], a: 1, en: 'Known, from definitions: P is closed under complement.', zh: '已知，由定义即得：P 对补运算封闭。' },
    { s: ['NP = coNP ⇒ P = NP', 'NP = coNP ⇒ P = NP'], a: 0, en: 'Not known. NP = coNP is consistent with P ≠ NP as far as anyone knows.', zh: '未知。就目前所知，NP = coNP 与 P ≠ NP 并不矛盾。' },
    { s: ['CH ⇒ every countable complete T has ≤ ℵ₀ or exactly 2<sup>ℵ₀</sup> countable models', 'CH ⇒ 每个可数完备理论 T 的可数模型个数 ≤ ℵ₀ 或恰为 2<sup>ℵ₀</sup>'], a: 1, en: 'Known (trivially): under CH an infinite I(T, ℵ₀) ≤ 2<sup>ℵ₀</sup> = ℵ₁ is ℵ₀ or ℵ₁ = 2<sup>ℵ₀</sup>. The perfect-set version remains open.', zh: '已知（平凡）：在 CH 下无穷的 I(T, ℵ₀) ≤ 2<sup>ℵ₀</sup> = ℵ₁，只能是 ℵ₀ 或 ℵ₁ = 2<sup>ℵ₀</sup>。完美集版本仍未解决。' },
    { s: ['ℝ<sub>exp</sub> is o-minimal ⇒ Th(ℝ<sub>exp</sub>) is decidable', 'ℝ<sub>exp</sub> 是 o-极小的 ⇒ Th(ℝ<sub>exp</sub>) 可判定'], a: 0, en: 'Not known: o-minimality is proved, decidability is open. Tameness ≠ decidability.', zh: '未知：o-极小性已证明，可判定性仍未解决。驯顺 ≠ 可判定。' },
    { s: ['T is NIP and simple ⇒ T is stable', 'T 是 NIP 且简单 ⇒ T 稳定'], a: 1, en: 'Known (Shelah): stable = NIP ∩ simple.', zh: '已知（谢拉赫）：稳定 = NIP ∩ 简单。' },
    { s: ['RCA₀ + RT²₂ ⊢ WKL₀', 'RCA₀ + RT²₂ ⊢ WKL₀'], a: 0, en: 'Not a theorem; in fact false (Liu 2012).', zh: '不是定理；事实上为假（刘路 2012）。' },
    { s: ['No propositional proof system is polynomially bounded ⇒ NP ≠ coNP', '没有多项式有界的命题证明系统 ⇒ NP ≠ coNP'], a: 1, en: 'Known: Cook–Reckhow 1979.', zh: '已知：Cook–Reckhow 1979。' },
    { s: ['ℂ<sub>exp</sub> exponentially-algebraically closed ⇒ ℂ<sub>exp</sub> quasiminimal', 'ℂ<sub>exp</sub> 指数代数闭 ⇒ ℂ<sub>exp</sub> 拟极小'], a: 1, en: 'Known: Bays–Kirby 2018.', zh: '已知：Bays–Kirby 2018。' },
  ];
  const solved = items.map(() => false);
  const box = $('e6List');
  items.forEach((it, i) => {
    const row = document.createElement('div');
    row.className = 'tf';
    row.innerHTML = `<div class="stmt" style="font-family:var(--sans);font-size:15px">${bi(it.s[0], it.s[1])}</div>
      <button class="btn small" data-v="1">${bil('known theorem', '已知定理')}</button>
      <button class="btn small" data-v="0">${bil('not known', '未知')}</button>
      <div style="flex-basis:100%"><div class="msg"></div></div>`;
    box.appendChild(row);
    row.querySelectorAll('button').forEach(b => b.addEventListener('click', () => {
      const m = row.querySelector('.msg');
      row.querySelectorAll('button').forEach(x => x.classList.remove('right', 'wrongc'));
      if (+b.dataset.v === it.a) { b.classList.add('right'); okBox(m, '✓ ' + bi(it.en, it.zh)); solved[i] = true; }
      else { b.classList.add('wrongc'); okBox(m, '✗ ' + bi('Not quite. Ask: is there a published proof of exactly this implication?', '不对。问问自己：恰好这个蕴涵有没有已发表的证明？'), 'bad'); solved[i] = false; }
    }));
  });
  $('e6Check').addEventListener('click', () => {
    const n = solved.filter(Boolean).length;
    if (n === items.length) { okBox($('e6Msg'), '✓ ' + bi('All correct. Separating “known implication” from “known conclusion” is the core skill for reading research claims.', '全对。区分“已知的蕴涵”与“已知的结论”，是阅读研究论断的核心能力。') + markIfEarned('L28E6')); }
    else okBox($('e6Msg'), bi(`${n} / ${items.length} answered correctly so far.`, `目前答对 ${n} / ${items.length}。`), 'warn');
  });
  $('e6Show').addEventListener('click', () => {
    revealed.add('L28E6');
    box.querySelectorAll('.tf').forEach((row, i) => {
      row.querySelectorAll('button').forEach(x => { x.classList.remove('right', 'wrongc'); if (+x.dataset.v === items[i].a) x.classList.add('right'); });
      okBox(row.querySelector('.msg'), bi(items[i].en, items[i].zh), 'info');
    });
    okBox($('e6Msg'), bi('Answers shown (not counted as solved).', '已显示答案（不计为完成）。'), 'info');
  });
})();

/* ================= Field map ================= */
(function fieldMap() {
  const svg = $('fieldSvg'), info = $('fieldInfo');
  const TITLES = [
    ['Propositional logic', '命题逻辑'], ['Proofs & completeness', '证明与完备性'], ['First-order logic', '一阶逻辑'], ['Gödel completeness', '哥德尔完备性'], ['Compactness & LS', '紧致性与 LS'],
    ['ZF axioms', 'ZF 公理'], ['Building ℕ…ℝ', '构造 ℕ…ℝ'], ['Ordinals', '序数'], ['Cardinals', '基数'], ['Axiom of Choice', '选择公理'],
    ['Computability', '可计算性'], ['Incompleteness', '不完全性'], ['Tarski: truth', '塔斯基：真'],
    ['Models of ZFC, V', 'ZFC 的模型与 V'], ['Constructible L', '可构成宇宙 L'], ['Forcing', '力迫法'],
    ['Arithmetical hierarchy', '算术层级'], ['Analytical hierarchy', '分析层级'], ['Borel & projective', '博雷尔与投影'], ['Lévy & absoluteness', '列维层级与绝对性'], ['Ordinal notations', '序数记号'], ['OD & HOD', 'OD 与 HOD'],
    ['Large cardinals I', '大基数（一）'], ['Large cardinals II', '大基数（二）'], ['Large cardinals III', '大基数（三）'],
    ['Big picture', '全景'], ['Set theory frontiers', '集合论前沿'], ['This lesson', '本课'],
  ];
  const P = [[90, 90], [190, 60], [290, 80], [360, 140], [300, 210],
    [80, 400], [70, 500], [170, 545], [280, 505], [200, 430],
    [490, 60], [590, 95], [560, 175],
    [380, 500], [470, 545], [570, 490],
    [700, 70], [800, 110], [880, 190], [880, 290], [780, 330], [870, 400], [840, 490], [740, 545], [650, 560],
    [440, 300], [570, 360], [440, 395]];
  const PCOL = ['#3b5bdb', '#3b5bdb', '#3b5bdb', '#3b5bdb', '#3b5bdb', '#2f9e44', '#2f9e44', '#2f9e44', '#2f9e44', '#2f9e44', '#f08c00', '#f08c00', '#f08c00', '#ae3ec9', '#ae3ec9', '#ae3ec9', '#c2255c', '#c2255c', '#c2255c', '#c2255c', '#c2255c', '#c2255c', '#c2255c', '#c2255c', '#c2255c', '#0c8599', '#0c8599', '#0c8599'];
  const E = [[1, 2], [2, 3], [3, 4], [4, 5], [6, 7], [7, 8], [8, 9], [9, 10], [11, 12], [12, 13], [14, 15], [15, 16], [17, 18], [18, 19], [19, 20], [20, 21], [21, 22], [23, 24], [24, 25],
    [2, 4], [3, 5], [4, 12], [11, 17], [12, 21], [8, 21], [6, 14], [10, 16], [16, 27], [15, 22], [9, 23], [19, 25], [20, 16], [25, 27], [26, 27], [27, 28], [26, 28], [5, 28], [13, 28], [17, 28], [21, 28], [1, 28], [5, 26], [12, 26], [16, 26]];
  const FR = [
    ['Vaught', '沃特', 5, [250, 255]], ['Tarski exp', '塔斯基指数', 13, [600, 230]], ['classification', '分类理论', 3, [150, 145]], ['H10 / ℚ', 'ℚ 上第十问题', 11, [430, 25]],
    ['rigidity, Martin', '刚性、马丁', 17, [690, 20]], ['RT²₂', 'RT²₂', 18, [770, 180]], ['P vs NP', 'P 与 NP', 1, [70, 30]], ['Π¹₂ wall', 'Π¹₂ 之墙', 21, [700, 400]],
    ['concrete incomp.', '具体不完全性', 12, [650, 140]], ['CH', 'CH', 16, [610, 420]], ['Ultimate L', '终极 L', 15, [400, 462]], ['HOD conj.', 'HOD 猜想', 22, [770, 445]], ['pcf', 'pcf', 9, [320, 445]], ['KL vs ML', 'KL 与 ML', 11, [520, 120]],
  ];
  const pillars = [['SETS · 集合', 150, 470], ['MODELS · 模型', 230, 300], ['COMPUTATION · 计算', 610, 25], ['PROOFS · 证明', 700, 250]];
  pillars.forEach(([s, x, y]) => T(svg, x, y, s, { 'font-size': 26, 'font-weight': 900, fill: '#e9ecef', 'text-anchor': 'middle' }));
  const edgeEls = [];
  E.forEach(([a, b]) => edgeEls.push({ a, b, e: el('line', { x1: P[a - 1][0], y1: P[a - 1][1], x2: P[b - 1][0], y2: P[b - 1][1], stroke: '#ced4da', 'stroke-width': 1.5 }, svg) }));
  const frEls = FR.map(f => {
    const [x, y] = f[3], [lx, ly] = P[f[2] - 1];
    const ln = el('line', { x1: lx, y1: ly, x2: x, y2: y, stroke: C.gold, 'stroke-dasharray': '3 3' }, svg);
    const g = el('g', {}, svg);
    el('path', { d: `M${x},${y - 7} L${x + 7},${y} L${x},${y + 7} L${x - 7},${y} z`, fill: C.gold }, g);
    T(g, x + 10, y + 4, f[0] + ' · ' + f[1], { 'font-size': 10.5, fill: '#8a5a00', 'font-weight': 700 });
    return { ln, g, l: f[2] };
  });
  const nodes = P.map(([x, y], i) => {
    const a = el('a', { href: `lesson${i + 1}.html` }, svg);
    const g = el('g', { class: 'pop' }, a);
    g.style.animationDelay = (i * 0.03) + 's';
    el('circle', { cx: x, cy: y, r: i === 27 ? 22 : 17, fill: i === 27 ? PCOL[i] : '#fff', stroke: PCOL[i], 'stroke-width': 3 }, g);
    T(g, x, y + 5, String(i + 1), { 'text-anchor': 'middle', 'font-size': 13, 'font-weight': 800, fill: i === 27 ? '#fff' : PCOL[i] });
    const t = el('title', {}, a); t.textContent = `L${i + 1} · ${TITLES[i][0]} · ${TITLES[i][1]}`;
    a.addEventListener('mouseenter', () => {
      const n = i + 1, nb = new Set([n]);
      edgeEls.forEach(e => { const on = e.a === n || e.b === n; e.e.setAttribute('stroke', on ? PCOL[i] : '#e9ecef'); e.e.setAttribute('stroke-width', on ? 3 : 1.5); if (on) { nb.add(e.a); nb.add(e.b); } });
      nodes.forEach((g2, k) => g2.setAttribute('opacity', nb.has(k + 1) ? 1 : .3));
      frEls.forEach(f => { const on = f.l === n; f.g.setAttribute('opacity', on ? 1 : .25); f.ln.setAttribute('opacity', on ? 1 : .25); });
      const fr = FR.filter(f => f[2] === n).map(f => bil(f[0], f[1])).join(', ');
      okBox(info, `<b>L${n}</b> · ${bil(TITLES[i][0], TITLES[i][1])}${fr ? ' — ' + bil('frontiers', '前沿') + ': ' + fr : ''}`, 'info');
    });
    a.addEventListener('mouseleave', () => {
      edgeEls.forEach(e => { e.e.setAttribute('stroke', '#ced4da'); e.e.setAttribute('stroke-width', 1.5); });
      nodes.forEach(g2 => g2.setAttribute('opacity', 1));
      frEls.forEach(f => { f.g.setAttribute('opacity', 1); f.ln.setAttribute('opacity', 1); });
    });
    return g;
  });
  okBox(info, bi('Hover a lesson to see its connections and the frontier problems (gold diamonds) that grow out of it; click to open it.', '鼠标停在某一课上，可看到它的联系以及由它生长出来的前沿问题（金色菱形）；点击即可打开。'), 'info');
})();
