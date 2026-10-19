// Lesson 10 interactions: Axiom of Choice, Zorn's lemma, Banach–Tarski.
Lang.init();
Progress.paint();

/* ================= small helpers ================= */
const $ = id => document.getElementById(id);
const okBox = (box, html, kind = 'ok') => { box.className = 'msg ' + kind; box.innerHTML = html; };
const clearBox = box => { box.className = 'msg'; box.innerHTML = ''; };
const SUB = '₀₁₂₃₄₅₆₇₈₉';
const sub = n => String(n).split('').map(d => SUB[d]).join('');
const C = { ink: '#1f2430', muted: '#6b7280', line: '#e3dfd3', accent: '#3b5bdb', accentSoft: '#e7ecff', tru: '#2f9e44', truSoft: '#d3f9d8',
  fal: '#e03131', falSoft: '#ffe3e3', meta: '#ae3ec9', metaSoft: '#f8e7fc', gold: '#f08c00', goldSoft: '#fff3bf' };

function txt(parent, x, y, s, attrs = {}) {
  const t = el('text', { x, y, ...attrs }, parent);
  t.textContent = s;
  return t;
}
// Two-line bilingual SVG label centred near (x, y). Font sizes go through inline style so the
// shared `.lang-both .zh { font-size }` rule cannot override them.
function txt2(parent, x, y, en, zh, size = 13, attrs = {}) {
  const g = el('g', {}, parent);
  const a = el('text', { x, y: y - 3, 'text-anchor': 'middle', class: 'en en2', ...attrs }, g);
  a.style.fontSize = size + 'px';
  a.textContent = en;
  const b = el('text', { x, y: y + size, 'text-anchor': 'middle', class: 'zh zh2', ...attrs }, g);
  b.style.fontSize = (size - 1) + 'px';
  b.textContent = zh;
  return g;
}
function mkBtn(en, zh, cls = 'btn') {
  const b = document.createElement('button');
  b.className = cls;
  b.innerHTML = bi(en, zh);
  return b;
}
function shuffle(a) {
  const r = [...a];
  for (let i = r.length - 1; i > 0; i--) { const j = Math.floor(Math.random() * (i + 1)); [r[i], r[j]] = [r[j], r[i]]; }
  return r;
}
function seg(id, attr, init, onSel) {
  const bs = [...$(id).querySelectorAll('button')];
  const set = v => { bs.forEach(b => b.classList.toggle('sel', b.dataset[attr] === v)); onSel(v); };
  bs.forEach(b => b.addEventListener('click', () => set(b.dataset[attr])));
  set(init);
}
// Step-by-step reveal with "Next" / "Show all" / "Reset". Never gated.
function Stepper(box, steps, opts = {}) {
  box.innerHTML = '';
  const wrap = document.createElement('div');
  wrap.className = 'steps';
  const els = steps.map((s, i) => {
    const d = document.createElement('div');
    d.className = 'step pstep';
    d.innerHTML = `<span class="snum">${i + 1}</span>${s}`;
    wrap.appendChild(d);
    return d;
  });
  box.appendChild(wrap);
  const bar = document.createElement('div');
  bar.className = 'toolbar';
  const nx = mkBtn('Next step ▶', '下一步 ▶', 'btn primary small');
  const al = mkBtn('Show all', '全部显示', 'btn ghost small');
  const rs = mkBtn('Reset', '重来', 'btn ghost small');
  bar.append(nx, al, rs);
  box.appendChild(bar);
  let k = 0;
  const sync = () => {
    els.forEach((e, i) => e.classList.toggle('on', i < k));
    nx.disabled = k >= els.length;
    if (opts.onStep) opts.onStep(k);
  };
  nx.addEventListener('click', () => { if (k < els.length) k++; sync(); });
  al.addEventListener('click', () => { k = els.length; sync(); });
  rs.addEventListener('click', () => { k = 0; sync(); });
  sync();
  return { showAll() { k = els.length; sync(); } };
}
const P = (en, zh) => bi(en, zh);

/* ================= §1 drawers ================= */
(function drawers() {
  const svg = $('drawers');
  let kind = 'sock', N = 'inf', picks = [], tail = null;
  const count = () => (N === 'inf' ? 7 : +N);
  function drawShoe(g, left) {
    const s = el('g', { transform: `scale(${left ? -0.85 : 0.85},0.85)` }, g);
    el('path', { d: 'M -20 8 L -20 -6 Q -20 -14 -12 -14 L -6 -14 Q -4 -4 6 -2 L 14 0 Q 22 2 22 10 L 22 13 L -20 13 Z', fill: '#8d5a3b', stroke: '#4a2f1f', 'stroke-width': 1.5 }, s);
    el('rect', { x: -21, y: 12, width: 44, height: 4, rx: 2, fill: '#4a2f1f' }, s);
    txt(g, 0, -17, left ? 'L' : 'R', { 'text-anchor': 'middle', 'font-size': 11, 'font-weight': 700, fill: '#4a2f1f' });
  }
  function drawSock(g) {
    const s = el('g', { transform: 'scale(0.85)' }, g);
    el('path', { d: 'M -8 -22 L 8 -22 L 8 2 L 16 8 Q 23 13 16 19 L -2 19 Q -13 19 -10 8 Z', fill: '#748ffc', stroke: '#364fc7', 'stroke-width': 1.5 }, s);
    el('rect', { x: -8, y: -22, width: 16, height: 6, fill: '#364fc7' }, s);
  }
  function draw() {
    svg.innerHTML = '';
    const n = count(), W = 96, G = 10;
    const total = n * W + (n - 1) * G + (N === 'inf' ? 130 : 0);
    const x0 = (880 - total) / 2;
    for (let i = 0; i < n; i++) {
      const x = x0 + i * (W + G);
      const g = el('g', {}, svg);
      el('rect', { x, y: 40, width: W, height: 150, rx: 10, fill: '#f3ead9', stroke: '#c9b48a', 'stroke-width': 2 }, g);
      el('rect', { x: x + W / 2 - 12, y: 50, width: 24, height: 6, rx: 3, fill: '#c9b48a' }, g);
      txt(g, x + W / 2, 30, 'D' + sub(i + 1), { 'text-anchor': 'middle', 'font-size': 14, 'font-weight': 700 });
      [0, 1].forEach(side => {
        const it = el('g', { class: 'clk', transform: `translate(${x + 26 + side * 44},120)` }, g);
        const on = picks[i] === side;
        el('circle', { r: 21, fill: on ? C.goldSoft : 'rgba(255,255,255,0.001)', stroke: on ? C.gold : 'none', 'stroke-width': 2.5 }, it);
        if (kind === 'shoe') drawShoe(it, side === 0); else drawSock(it);
        it.addEventListener('click', () => { picks[i] = side; tail = null; draw(); report(); });
      });
      if (picks[i] != null) {
        txt(g, x + W / 2, 178, kind === 'shoe' ? `f(D${sub(i + 1)}) = ${picks[i] ? 'R' : 'L'}` : `f(D${sub(i + 1)}) ✓`,
          { 'text-anchor': 'middle', 'font-size': 12, fill: C.gold, 'font-weight': 700 });
      }
    }
    if (N === 'inf') {
      const x = x0 + n * (W + G) + 6;
      txt(svg, x + 50, 125, '⋯', { 'text-anchor': 'middle', 'font-size': 40, fill: '#999' });
      txt(svg, x + 50, 30, 'D₈, D₉, …', { 'text-anchor': 'middle', 'font-size': 14, 'font-weight': 700, fill: '#999' });
      if (tail === 'rule') txt2(svg, x + 50, 165, 'all: f = left', '全部：取左脚', 12, { fill: C.tru, 'font-weight': 700 });
      if (tail === 'ac') txt2(svg, x + 50, 165, 'all: f ∃ by AC', '全部：AC 保证', 12, { fill: C.meta, 'font-weight': 700 });
    }
    txt(svg, 440, 238, kind === 'shoe' ? 'f(D) = the left shoe of D  ·  f(D) = D 中的左脚鞋' : 'f(D) ∈ D  ·  {s, s′}: indistinguishable · 无从区分',
      { 'text-anchor': 'middle', 'font-size': 13, fill: C.muted });
  }
  function report() {
    const n = count();
    const k = picks.slice(0, n).filter(x => x != null).length;
    const box = $('drMsg');
    if (tail === 'rule') return;
    if (tail === 'ac') return;
    if (N !== 'inf') {
      if (k < n) okBox(box, bi(`You have chosen from ${k} of ${n} drawers. Click one item in each drawer.`, `已经从 ${n} 个抽屉中的 ${k} 个里选了。每个抽屉点一件。`), 'info');
      else okBox(box, bi(`Done: a choice function on ${n} drawers. For <b>finitely many</b> nonempty sets this is a theorem of ZF, proved by induction (below). No axiom of choice is needed.`,
        `完成：${n} 个抽屉上的一个选择函数。对<b>有限个</b>非空集合，这是 ZF 的定理，用归纳法即可证明（见下文），不需要选择公理。`));
    } else if (k < n) {
      okBox(box, bi(`Chosen from ${k} drawers so far. The row never ends: D₈, D₉, … are still waiting.`, `目前选了 ${k} 个抽屉。这一排没有尽头：D₈, D₉, … 还在等着。`), 'info');
    } else {
      okBox(box, bi('All visible drawers are done, but infinitely many remain. A proof is a finite object, so it can make only finitely many individual choices. To handle all drawers at once you need a <b>rule</b> (shoes) or the <b>Axiom of Choice</b> (socks).',
        '看得见的抽屉都选完了，可还剩无穷多个。证明是有限的对象，只能做有限次单独的选择。要一次性处理所有抽屉，要么有<b>规则</b>（鞋），要么动用<b>选择公理</b>（袜子）。'), 'warn');
    }
  }
  function reset() { picks = []; tail = null; draw(); report(); }
  seg('drKind', 'k', 'sock', v => { kind = v; reset(); });
  seg('drN', 'n', 'inf', v => { N = v; reset(); });
  $('drReset').addEventListener('click', reset);
  $('drRule').addEventListener('click', () => {
    if (kind === 'shoe') {
      picks = Array(count()).fill(0);
      tail = N === 'inf' ? 'rule' : null;
      draw();
      okBox($('drMsg'), bi('The rule “f(D) = the left shoe in D” is a formula, so by Separation <span class="m">f = {(D, s) : s is the left shoe in D}</span> is a set. It works for infinitely many drawers at once, and <b>no choice is needed</b>.',
        '规则“f(D) = D 中的左脚鞋”是一个公式，由分离公理，<span class="m">f = {(D, s) : s 是 D 中的左脚鞋}</span> 是集合。它对无穷多个抽屉同时适用，<b>不需要选择公理</b>。'));
    } else {
      okBox($('drMsg'), bi('Which rule? Each drawer is just a 2-element set {s, s′}, and nothing distinguishes s from s′, so “the left one” means nothing. In fact it is consistent with ZF that some countable family of 2-element sets has <b>no choice function at all</b> (Cohen-style symmetric models).',
        '用什么规则？每个抽屉只是一个二元集 {s, s′}，s 与 s′ 没有任何区别，“左边那只”无从谈起。事实上，“存在某个可数的二元集族<b>根本没有选择函数</b>”与 ZF 是相容的（科恩式的对称模型）。'), 'bad');
    }
  });
  $('drAC').addEventListener('click', () => {
    picks = Array.from({ length: count() }, () => (Math.random() < 0.5 ? 0 : 1));
    tail = N === 'inf' ? 'ac' : null;
    draw();
    okBox($('drMsg'), bi('AC asserts that a choice function f on the <b>whole</b> family exists. It does not say which item f picks, and f need not be given by any formula. The highlighted picks are just one possible f.',
      'AC 断言<b>整个</b>集族上存在选择函数 f。它不告诉你 f 挑了哪一只，f 也未必能用任何公式写出来。图中高亮的只是某一个可能的 f。'), 'info');
  });

  Stepper($('finSteps'), [
    P('<b>One set.</b> “A ≠ ∅” means ∃a (a ∈ A). Naming such an a is ordinary logic (existential instantiation, ∃-elimination). No axiom is involved.',
      '<b>一个集合.</b> “A ≠ ∅”就是 ∃a (a ∈ A)。给这样的 a 取个名字，是普通的逻辑推理（存在消去），不涉及任何公理。'),
    P('<b>Induction on n.</b> Suppose every family of n nonempty sets has a choice function. Given A₁, …, Aₙ₊₁, take a choice function f for the first n, pick one a ∈ Aₙ₊₁, and set f′ = f ∪ {(Aₙ₊₁, a)}.',
      '<b>对 n 归纳.</b> 设任意 n 个非空集合都有选择函数。给定 A₁, …, Aₙ₊₁，取前 n 个的选择函数 f，再从 Aₙ₊₁ 中取一个 a，令 f′ = f ∪ {(Aₙ₊₁, a)}。'),
    P('So “every <b>finite</b> family of nonempty sets has a choice function” is a theorem of ZF. Formally, induction over n ∈ ω proves the statement “every family of size n has a choice function” for every n.',
      '所以“每个<b>有限</b>非空集族都有选择函数”是 ZF 的定理。形式上，就是对 n ∈ ω 归纳证明“每个 n 元集族都有选择函数”。'),
    P('<b>Where it breaks.</b> Induction gives a choice function for each finite stage, but it never produces one function for the infinite family: for that, the stage-n functions would have to be chosen so that they fit together, and nothing chooses them. AC fills exactly this gap. If ZF is consistent, AC is independent of ZF (Gödel 1938, Cohen 1963; Lessons 15–16).',
      '<b>卡在哪里.</b> 归纳法为每个有限阶段给出选择函数，却永远得不到整个无穷集族上的单个函数：那需要把各阶段的函数选得彼此相容，而没有什么东西替我们做这件选择。AC 恰好填补这道缺口。若 ZF 相容，则 AC 独立于 ZF（哥德尔 1938，科恩 1963；见第 15–16 课）。'),
  ]);
})();

/* ================= §2 equivalences ================= */
(function equivalences() {
  const svg = $('eqSvg');
  const nodes = {
    AC: { x: 320, y: 50, en: 'AC', zh: '选择公理',
      st: P('<b>AC.</b> Every family of nonempty sets has a choice function.', '<b>选择公理.</b> 每个非空集合族都有选择函数。') },
    WO: { x: 110, y: 190, en: 'Well-ordering thm', zh: '良序定理',
      st: P('<b>Well-ordering theorem.</b> Every set can be well-ordered (equivalently, is in bijection with an ordinal).', '<b>良序定理.</b> 每个集合都可以良序化（等价地：与某个序数之间有双射）。') },
    Zorn: { x: 530, y: 190, en: "Zorn's lemma", zh: '佐恩引理',
      st: P("<b>Zorn's lemma.</b> If every chain in a nonempty poset P has an upper bound in P, then P has a maximal element.", '<b>佐恩引理.</b> 若非空偏序集 P 中每条链在 P 中都有上界，则 P 有极大元。') },
    SRI: { x: 320, y: 330, en: 'Surjections split', zh: '满射有右逆',
      st: P('<b>Surjections split.</b> Every surjection f : X ↠ Y has a right inverse g : Y → X, i.e. f ∘ g = id<sub>Y</sub>.', '<b>满射有右逆.</b> 每个满射 f : X ↠ Y 都有右逆 g : Y → X，即 f ∘ g = id<sub>Y</sub>。') },
  };
  const proofs = {
    'AC>WO': { t: 'AC ⇒ WO', s: [
      P('Let A be a set and f a choice function on 𝒫(A) ∖ {∅}.', '设 A 为集合，f 是 𝒫(A) ∖ {∅} 上的选择函数。'),
      P('Transfinite recursion (Lesson 8): a<sub>α</sub> = f(A ∖ {a<sub>β</sub> : β &lt; α}), as long as that set is nonempty. Each step picks something not yet used.', '超限递归（第 8 课）：只要 A ∖ {a<sub>β</sub> : β &lt; α} 非空，就令 a<sub>α</sub> = f(A ∖ {a<sub>β</sub> : β &lt; α})。每一步都挑一个还没用过的元素。'),
      P('α ↦ a<sub>α</sub> is injective. By Hartogs’ theorem some ordinal does not inject into A, so the recursion stops at some θ with A = {a<sub>β</sub> : β &lt; θ}.', 'α ↦ a<sub>α</sub> 是单射。由哈托格斯定理，存在不能单射进 A 的序数，所以递归必在某个 θ 处停止，且 A = {a<sub>β</sub> : β &lt; θ}。'),
      P('Then a<sub>β</sub> ↦ β is a bijection A → θ. Pull back the order of θ: a<sub>β</sub> ≺ a<sub>γ</sub> ⇔ β &lt; γ is a well-order of A. ∎', '于是 a<sub>β</sub> ↦ β 是 A → θ 的双射。把 θ 上的序拉回来：a<sub>β</sub> ≺ a<sub>γ</sub> ⇔ β &lt; γ，就是 A 上的良序。∎'),
    ] },
    'WO>AC': { t: 'WO ⇒ AC', s: [
      P('Let X be a family of nonempty sets. Well-order ⋃X by ≺.', '设 X 是非空集合族。把 ⋃X 用 ≺ 良序化。'),
      P('Define f(A) = the ≺-least element of A. Every nonempty A ⊆ ⋃X has one, and f is defined by a formula, so it is a set by Separation. ∎', '令 f(A) = A 中关于 ≺ 的最小元。每个非空 A ⊆ ⋃X 都有最小元，而且 f 由公式定义，由分离公理是集合。∎'),
      P('Moral: a well-order is a <b>uniform rule</b> for choosing, like “the left shoe”.', '寓意：良序就是一条<b>统一的选取规则</b>，就像“拿左脚那只”。'),
    ] },
    'AC>Zorn': { t: 'AC ⇒ Zorn', s: [
      P('Suppose every chain in P has an upper bound, but P has no maximal element. Then every chain C even has a <b>strict</b> upper bound: take an upper bound u; u is not maximal, so some v &gt; u.', '设 P 中每条链都有上界，但 P 没有极大元。则每条链 C 甚至都有<b>严格</b>上界：取上界 u，u 不是极大元，故有 v &gt; u。'),
      P('By AC fix g choosing a strict upper bound g(C) for every chain C.', '由 AC，取定 g，为每条链 C 选一个严格上界 g(C)。'),
      P('Recursion: p<sub>α</sub> = g({p<sub>β</sub> : β &lt; α}). By induction this set is always a chain, so the recursion never gets stuck, not even at limit stages.', '递归：p<sub>α</sub> = g({p<sub>β</sub> : β &lt; α})。归纳可知这个集合始终是链，所以递归永远不会卡住，极限阶段也不会。'),
      P('Then α ↦ p<sub>α</sub> injects every ordinal into the set P, which contradicts Hartogs’ theorem. ∎ (§3 animates this.)', '于是 α ↦ p<sub>α</sub> 把所有序数单射进集合 P，与哈托格斯定理矛盾。∎（§3 有动画演示。）'),
    ] },
    'Zorn>AC': { t: 'Zorn ⇒ AC', s: [
      P('Let X be a family of nonempty sets. Let P be the set of <b>partial choice functions</b>: g with dom g ⊆ X and g(A) ∈ A. Order P by ⊆. P ≠ ∅ because ∅ ∈ P.', '设 X 为非空集合族。令 P 为所有<b>部分选择函数</b>构成的集合：dom g ⊆ X 且 g(A) ∈ A。按 ⊆ 排序。∅ ∈ P，所以 P ≠ ∅。'),
      P('The union of a chain of such functions is again a function (any two members agree where both are defined), so it is a partial choice function and an upper bound.', '一条链中这些函数的并仍是函数（任意两个在公共定义域上取值一致），因此是部分选择函数，并且是上界。'),
      P('Zorn gives a maximal g. If some A ∈ X ∖ dom g existed, pick one a ∈ A (a single choice) and g ∪ {(A, a)} would be strictly larger. So dom g = X. ∎', '由佐恩引理得到极大的 g。若有 A ∈ X ∖ dom g，从 A 中取一个 a（只是一次选择），g ∪ {(A, a)} 就严格更大，矛盾。所以 dom g = X。∎'),
    ] },
    'Zorn>WO': { t: 'Zorn ⇒ WO', s: [
      P('Let P be the set of pairs (B, &lt;) with B ⊆ A and &lt; a well-order of B. Order them by <b>end-extension</b>: (B, &lt;) ≼ (B′, &lt;′) if B is an initial segment of B′ and &lt;′ agrees with &lt; on B.', '令 P 为所有 (B, &lt;) 构成的集合，其中 B ⊆ A，&lt; 是 B 上的良序。按<b>尾扩张</b>排序：若 B 是 B′ 的前段且 &lt;′ 在 B 上与 &lt; 一致，就规定 (B, &lt;) ≼ (B′, &lt;′)。'),
      P('The union of a chain is a well-order: an element’s predecessors are fixed once it appears, so a least element of any nonempty subset can be found inside one member of the chain.', '链的并仍是良序：一个元素一旦出现，它的前驱就固定不变，因此任一非空子集的最小元都能在链中某一个成员里找到。'),
      P('Take a maximal (B, &lt;). If B ≠ A, put a new element on top, which gives a strictly larger element. So B = A. ∎', '取极大的 (B, &lt;)。若 B ≠ A，就在顶端加一个新元素，得到严格更大的元素，矛盾。所以 B = A。∎'),
    ] },
    'AC>SRI': { t: 'AC ⇒ surjections split', s: [
      P('Let f : X ↠ Y. The fibres f⁻¹(y), y ∈ Y, are nonempty because f is onto.', '设 f : X ↠ Y。因为 f 是满射，各纤维 f⁻¹(y)（y ∈ Y）都非空。'),
      P('Take a choice function c on {f⁻¹(y) : y ∈ Y} and put g(y) = c(f⁻¹(y)). Then f(g(y)) = y. ∎', '取 {f⁻¹(y) : y ∈ Y} 上的选择函数 c，令 g(y) = c(f⁻¹(y))，则 f(g(y)) = y。∎'),
    ] },
    'SRI>AC': { t: 'Surjections split ⇒ AC', s: [
      P('Let X be a family of nonempty sets. Form E = {(A, a) : A ∈ X, a ∈ A} and π : E → X, π(A, a) = A.', '设 X 为非空集合族。令 E = {(A, a) : A ∈ X, a ∈ A}，π : E → X，π(A, a) = A。'),
      P('π is onto precisely because every A is nonempty. Let s be a right inverse: π(s(A)) = A, so s(A) = (A, a) for some a ∈ A.', 'π 是满射，恰恰因为每个 A 都非空。取右逆 s：π(s(A)) = A，所以 s(A) = (A, a)，其中 a ∈ A。'),
      P('f(A) = second coordinate of s(A) is a choice function. ∎', '令 f(A) 为 s(A) 的第二个坐标，即得选择函数。∎'),
    ] },
  };
  const arrows = [
    { id: 'AC>WO', a: 'AC', b: 'WO', off: 9 }, { id: 'WO>AC', a: 'WO', b: 'AC', off: 9 },
    { id: 'AC>Zorn', a: 'AC', b: 'Zorn', off: 9 }, { id: 'Zorn>AC', a: 'Zorn', b: 'AC', off: 9 },
    { id: 'AC>SRI', a: 'AC', b: 'SRI', off: 9 }, { id: 'SRI>AC', a: 'SRI', b: 'AC', off: 9 },
    { id: 'Zorn>WO', a: 'Zorn', b: 'WO', ctrl: [320, 268] },
  ];
  const HW = 85, HH = 26;
  const seen = new Set();
  let active = null;
  const exitPt = (c, dx, dy) => { const t = Math.min(dx ? HW / Math.abs(dx) : 1e9, dy ? HH / Math.abs(dy) : 1e9); return [c.x + dx * t, c.y + dy * t]; };
  function draw() {
    svg.innerHTML = '';
    arrows.forEach(ar => {
      const A = nodes[ar.a], B = nodes[ar.b];
      let dx = B.x - A.x, dy = B.y - A.y;
      const len = Math.hypot(dx, dy); dx /= len; dy /= len;
      const off = ar.off || 0, nx = -dy * off, ny = dx * off;
      let s, e, c;
      if (ar.ctrl) {
        c = ar.ctrl;
        let sx = c[0] - A.x, sy = c[1] - A.y; const sl = Math.hypot(sx, sy); sx /= sl; sy /= sl;
        let ex = c[0] - B.x, ey = c[1] - B.y; const el2 = Math.hypot(ex, ey); ex /= el2; ey /= el2;
        s = exitPt(A, sx, sy); s = [s[0] + sx * 4, s[1] + sy * 4];
        e = exitPt(B, ex, ey); e = [e[0] + ex * 4, e[1] + ey * 4];
      } else {
        s = exitPt(A, dx, dy); s = [s[0] + dx * 4 + nx, s[1] + dy * 4 + ny];
        e = exitPt(B, -dx, -dy); e = [e[0] - dx * 4 + nx, e[1] - dy * 4 + ny];
        c = [(s[0] + e[0]) / 2, (s[1] + e[1]) / 2];
      }
      const col = active === ar.id ? C.meta : seen.has(ar.id) ? C.tru : '#8a8f99';
      const g = el('g', { class: 'eqarrow' }, svg);
      const d = `M${s[0]},${s[1]} Q${c[0]},${c[1]} ${e[0]},${e[1]}`;
      el('path', { d, stroke: 'transparent', 'stroke-width': 16, fill: 'none' }, g);
      el('path', { d, class: 'vis', stroke: col, 'stroke-width': active === ar.id ? 4 : 2.5, fill: 'none' }, g);
      let tx = e[0] - c[0], ty = e[1] - c[1]; const tl = Math.hypot(tx, ty) || 1; tx /= tl; ty /= tl;
      const bx = e[0] - tx * 12, by = e[1] - ty * 12;
      el('polygon', { points: `${e[0]},${e[1]} ${bx - ty * 6},${by + tx * 6} ${bx + ty * 6},${by - tx * 6}`, fill: col }, g);
      const tt = el('title', {}, g); tt.textContent = proofs[ar.id].t;
      g.addEventListener('click', () => openProof(ar.id));
    });
    Object.entries(nodes).forEach(([k, n]) => {
      const g = el('g', { class: 'clk' }, svg);
      el('rect', { x: n.x - HW, y: n.y - HH, width: 2 * HW, height: 2 * HH, rx: 12, fill: k === 'AC' ? C.metaSoft : '#fff', stroke: k === 'AC' ? C.meta : C.ink, 'stroke-width': 2 }, g);
      txt2(g, n.x, n.y + 2, n.en, n.zh, 15, { 'font-weight': 700 });
      g.addEventListener('click', () => { active = null; draw(); $('eqPanel').innerHTML = n.st + `<p class="muted" style="font-size:13px">${bi('Now click an arrow leaving or entering this box.', '现在点一个进出这个方框的箭头。')}</p>`; });
    });
    $('eqCount').innerHTML = bi(`Proofs opened: ${seen.size} / ${arrows.length}`, `已查看的证明：${seen.size} / ${arrows.length}`);
  }
  function openProof(id) {
    active = id;
    seen.add(id);
    draw();
    const pr = proofs[id];
    const [a, b] = id.split('>');
    $('eqPanel').innerHTML = `<h3 style="margin-top:0">${pr.t}</h3><div class="muted" style="font-size:13px">${bi('Assume:', '假设：')}</div>${nodes[a].st}<div class="muted" style="font-size:13px">${bi('Prove:', '要证：')}</div>${nodes[b].st}<div id="eqSteps"></div>`;
    Stepper($('eqSteps'), pr.s);
  }
  draw();
  $('eqPanel').innerHTML = bi('<b>Click an arrow</b> to see the proof of that implication. A cycle AC → Zorn → WO → AC already proves all three equivalent; the extra arrows give direct proofs.',
    '<b>点一个箭头</b>查看该蕴涵的证明。只要有一个环路 AC → 佐恩 → 良序 → AC，三者就已经等价；多出来的箭头给出的是直接证明。');
})();

/* ================= posets (shared by §3 and E5) ================= */
function makePoset(nodes, covers, extra = {}) {
  const ids = nodes.map(n => n.id);
  const up = {}, adj = {};
  ids.forEach(i => { up[i] = new Set([i]); adj[i] = []; });
  covers.forEach(([l, h]) => adj[l].push(h));
  ids.forEach(i => {
    const st = [i];
    while (st.length) { const x = st.pop(); adj[x].forEach(y => { if (!up[i].has(y)) { up[i].add(y); st.push(y); } }); }
  });
  const leq = (a, b) => up[a].has(b);
  return { nodes, covers, ids, leq, lt: (a, b) => a !== b && leq(a, b), byId: Object.fromEntries(nodes.map(n => [n.id, n])), ...extra };
}
const incomparablePair = (Pn, S) => {
  for (let i = 0; i < S.length; i++) for (let j = i + 1; j < S.length; j++) if (!Pn.leq(S[i], S[j]) && !Pn.leq(S[j], S[i])) return [S[i], S[j]];
  return null;
};
const upperBounds = (Pn, S) => Pn.ids.filter(u => S.every(s => Pn.leq(s, u)));
const maximals = Pn => (Pn.noMax ? [] : Pn.ids.filter(m => !Pn.ids.some(x => Pn.lt(m, x))));
const sortChain = (Pn, S) => [...S].sort((x, y) => (Pn.leq(x, y) ? -1 : 1));
function drawHasse(svg, Pn, st) {
  svg.innerHTML = '';
  Pn.covers.forEach(([l, h]) => {
    const A = Pn.byId[l], B = Pn.byId[h];
    const at = { x1: A.x, y1: A.y, x2: B.x, y2: B.y, stroke: '#b9b4a6', 'stroke-width': 2 };
    if (Pn.dashed && Pn.dashed(l, h)) at['stroke-dasharray'] = '5 6';
    el('line', at, svg);
  });
  if (Pn.decor) Pn.decor(svg);
  if (st.path && st.path.length > 1) {
    el('polyline', { points: st.path.map(i => `${Pn.byId[i].x},${Pn.byId[i].y}`).join(' '), fill: 'none', stroke: C.meta, 'stroke-width': 7, opacity: 0.35, 'stroke-linecap': 'round', 'stroke-linejoin': 'round' }, svg);
  }
  if (st.bad) {
    const [a, b] = st.bad.map(i => Pn.byId[i]);
    el('line', { x1: a.x, y1: a.y, x2: b.x, y2: b.y, stroke: C.fal, 'stroke-width': 2.5, 'stroke-dasharray': '6 5' }, svg);
  }
  Pn.nodes.forEach(n => {
    const g = el('g', { class: 'hnode clk', transform: `translate(${n.x},${n.y})` }, svg);
    if (st.cand && st.cand.has(n.id)) el('circle', { r: 25, fill: C.goldSoft, stroke: 'none' }, g);
    if (st.ub && st.ub.has(n.id)) el('circle', { r: 23, fill: 'none', stroke: C.gold, 'stroke-width': 3 }, g);
    if (st.ring && st.ring.has(n.id)) el('circle', { r: 23, fill: 'none', stroke: C.meta, 'stroke-width': 3, 'stroke-dasharray': '4 3' }, g);
    const sel = st.sel && st.sel.has(n.id);
    let fill = sel ? C.metaSoft : '#fff', stroke = sel ? C.meta : C.ink;
    if (st.good && st.good.has(n.id)) { fill = C.truSoft; stroke = C.tru; }
    if (st.wrong && st.wrong.has(n.id)) { fill = C.falSoft; stroke = C.fal; }
    el('circle', { r: 17, fill, stroke, 'stroke-width': sel ? 3 : 2 }, g);
    txt(g, 0, 5, n.id, { 'text-anchor': 'middle', 'font-size': 15, 'font-weight': 700 });
    if (st.star && st.star.has(n.id)) txt(g, 16, -12, '★', { 'font-size': 18, fill: C.gold });
    if (st.labels && st.labels[n.id]) txt(g, -24, 5, st.labels[n.id], { 'text-anchor': 'end', 'font-size': 13, fill: C.meta, 'font-weight': 700 });
    if (st.onClick) g.addEventListener('click', () => st.onClick(n.id));
  });
}

/* ================= §3 Zorn ================= */
(function zorn() {
  const svg = $('zSvg');
  const fin = makePoset([
    { id: 'a', x: 300, y: 370 }, { id: 'b', x: 150, y: 290 }, { id: 'c', x: 300, y: 290 }, { id: 'd', x: 450, y: 290 },
    { id: 'e', x: 90, y: 200 }, { id: 'f', x: 225, y: 200 }, { id: 'g', x: 375, y: 200 }, { id: 'h', x: 510, y: 200 },
    { id: 'i', x: 150, y: 110 }, { id: 'j', x: 300, y: 110 }, { id: 'k', x: 300, y: 30 },
  ], [['a', 'b'], ['a', 'c'], ['a', 'd'], ['b', 'e'], ['b', 'f'], ['c', 'f'], ['c', 'g'], ['d', 'g'], ['d', 'h'], ['e', 'i'], ['f', 'i'], ['f', 'j'], ['g', 'j'], ['j', 'k']]);
  const ladderNodes = [0, 1, 2, 3, 4, 5].map(n => ({ id: String(n), x: 300, y: 370 - n * 55 }));
  const ladderCovers = [0, 1, 2, 3, 4].map(n => [String(n), String(n + 1)]);
  const nat = makePoset(ladderNodes, ladderCovers, {
    noMax: true, infinite: true,
    decor: s => {
      el('line', { x1: 300, y1: 95, x2: 300, y2: 20, stroke: '#b9b4a6', 'stroke-width': 2, 'stroke-dasharray': '5 6' }, s);
      txt(s, 330, 60, '⋮  6, 7, 8, …', { 'font-size': 15, fill: '#999' });
    },
  });
  const natw = makePoset([...ladderNodes, { id: 'ω', x: 300, y: 25 }], [...ladderCovers, ['5', 'ω']], {
    infinite: true,
    dashed: (l, h) => h === 'ω',
    decor: s => txt(s, 330, 64, '⋮  6, 7, 8, …', { 'font-size': 15, fill: '#999' }),
  });
  const POS = { fin, nat, natw };
  let cur = 'fin', S = [], showMax = false, climbSeq = [], cand = new Set(), tok = 0, labels = {};
  const fmtSet = A => '{' + A.join(', ') + '}';
  function render() {
    const Pn = POS[cur];
    const bad = S.length > 1 ? incomparablePair(Pn, S) : null;
    const ub = new Set(climbSeq.length ? [] : upperBounds(Pn, S));
    const path = climbSeq.length ? climbSeq : (!bad && S.length > 1 ? sortChain(Pn, S) : []);
    drawHasse(svg, Pn, {
      sel: new Set(S), ub, cand, bad, path, labels,
      star: new Set(showMax ? maximals(Pn) : []),
      onClick: id => {
        tok++; climbSeq = []; labels = {}; cand = new Set();
        S = S.includes(id) ? S.filter(x => x !== id) : [...S, id];
        clearBox($('zLog'));
        render();
      },
    });
    let h = `<div class="m" style="font-size:16px">S = ${fmtSet(sortChain(Pn, S))}</div>`;
    if (climbSeq.length) {
      h += bi('<p>Climbing… the purple path is the chain C built so far; gold discs are its strict upper bounds, the candidates for g(C).</p>',
        '<p>正在往上爬……紫色路径是目前建好的链 C；金色圆盘是它的严格上界，也就是 g(C) 的候选。</p>');
    } else {
      h += bad ? `<p>✗ ${bi(`<b>Not a chain</b>: ${bad[0]} and ${bad[1]} are incomparable (red dashes).`, `<b>不是链</b>：${bad[0]} 与 ${bad[1]} 不可比较（红色虚线）。`)}</p>`
        : `<p>✓ ${bi('<b>A chain</b>: any two elements are comparable.', '<b>是链</b>：任意两个元素都可比较。')}</p>`;
      const u = [...ub];
      const items = u.filter(x => x !== 'ω');
      if (Pn.infinite && !S.includes('ω')) items.push('6, 7, …');
      if (u.includes('ω')) items.push('ω');
      h += `<p>${bil('Upper bounds (gold rings)', '上界（金圈）')}: <span class="m">${items.length ? '{' + items.join(', ') + '}' : '∅'}</span></p>`;
      if (!S.length) h += `<p class="muted" style="font-size:13px">${bi('The empty chain: every element is (vacuously) an upper bound. That is why Zorn needs P ≠ ∅.', '空链：每个元素都（空真地）是它的上界。这就是佐恩引理要求 P ≠ ∅ 的原因。')}</p>`;
      if (cur === 'nat') h += `<p class="muted" style="font-size:13px">${bi('In ℕ the chain ℕ itself has <b>no</b> upper bound, so Zorn’s hypothesis fails here.', '在 ℕ 中，链 ℕ 本身<b>没有</b>上界，佐恩引理的条件在这里不成立。')}</p>`;
    }
    if (showMax) {
      const m = maximals(Pn);
      h += `<p>★ ${bil('Maximal elements', '极大元')}: <span class="m">${m.length ? fmtSet(m) : bil('none', '没有')}</span></p>`;
      if (cur === 'fin') h += `<p class="muted" style="font-size:13px">${bi('Three maximal elements and no maximum: “maximal” means nothing is above it, not that it is above everything.', '有三个极大元，却没有最大元：“极大”是说没有元素比它大，而不是说它比所有元素都大。')}</p>`;
    }
    $('zInfo').innerHTML = h;
  }
  async function climb() {
    const my = ++tok;
    const Pn = POS[cur];
    S = []; climbSeq = []; labels = {}; cand = new Set();
    const log = [];
    const say = () => okBox($('zLog'), log.join('<br>'), 'info');
    render();
    if (cur !== 'fin') {
      for (let n = 0; n <= 5; n++) {
        cand = new Set(Pn.ids.filter(u => climbSeq.every(c => Pn.lt(c, u))));
        render(); await sleep(450); if (my !== tok) return;
        climbSeq.push(String(n)); labels[String(n)] = 'p' + sub(n); cand = new Set();
        log.push(`p${sub(n)} = g(C) = ${n}`); say(); render(); await sleep(350); if (my !== tok) return;
      }
      log.push(bi('… p<sub>n</sub> = n for every n &lt; ω (one stage at a time).', '…… 对每个 n &lt; ω，p<sub>n</sub> = n（逐阶段进行）。')); say();
      await sleep(900); if (my !== tok) return;
      if (cur === 'nat') {
        log.push(bi('<b>Stage ω:</b> the chain C = ℕ has <b>no upper bound</b>. The hypothesis of Zorn fails, the climb is stuck, and indeed ℕ has no maximal element.',
          '<b>第 ω 阶段：</b>链 C = ℕ <b>没有上界</b>。佐恩引理的条件不成立，攀爬卡住了，而 ℕ 确实没有极大元。'));
        say(); okBox($('zLog'), log.join('<br>'), 'warn');
      } else {
        cand = new Set(['ω']); render(); await sleep(700); if (my !== tok) return;
        climbSeq.push('ω'); labels['ω'] = 'p' + 'ω'; cand = new Set();
        log.push(bi('<b>Limit stage ω:</b> the chain {0, 1, 2, …} has the upper bound ω, so g picks p<sub>ω</sub> = ω.', '<b>极限阶段 ω：</b>链 {0, 1, 2, …} 有上界 ω，于是 g 取 p<sub>ω</sub> = ω。'));
        say(); render(); await sleep(700); if (my !== tok) return;
        log.push(bi('<b>Stage ω+1:</b> no strict upper bound remains, so ω is maximal. ★', '<b>第 ω+1 阶段：</b>不再有严格上界，所以 ω 是极大元。★'));
        okBox($('zLog'), log.join('<br>'), 'ok');
        showMax = true; render();
      }
      return;
    }
    for (let stage = 0; ; stage++) {
      const T = Pn.ids.filter(u => climbSeq.every(c => Pn.lt(c, u)));
      cand = new Set(T); render();
      await sleep(800); if (my !== tok) return;
      if (!T.length) {
        const top = climbSeq[climbSeq.length - 1];
        log.push(bi(`<b>Stage ${stage}:</b> the chain has no strict upper bound, so its top element <b>${top}</b> is maximal (anything above ${top} would be a strict upper bound). ★`,
          `<b>第 ${stage} 阶段：</b>链没有严格上界，所以链顶 <b>${top}</b> 是极大元（任何比 ${top} 大的元素都会是严格上界）。★`));
        okBox($('zLog'), log.join('<br>'), 'ok');
        cand = new Set(); showMax = false; render();
        const g = svg.querySelectorAll('.hnode')[Pn.ids.indexOf(top)];
        txt(g, 16, -12, '★', { 'font-size': 20, fill: C.gold, class: 'pop' });
        return;
      }
      const low = T.filter(t => !T.some(u => Pn.lt(u, t)));
      const pick = low[Math.floor(Math.random() * low.length)];
      climbSeq.push(pick); labels[pick] = 'p' + sub(stage); cand = new Set();
      log.push(`p${sub(stage)} = g(C) = <b>${pick}</b> <span class="muted">${bil(`(${T.length} strict upper bounds; this g picks a lowest one, but any choice works)`, `（共 ${T.length} 个严格上界；这里的 g 挑最低的一个，其实挑哪个都行）`)}</span>`);
      say(); render();
      await sleep(550); if (my !== tok) return;
    }
  }
  seg('zPoset', 'p', 'fin', v => { cur = v; tok++; S = []; climbSeq = []; labels = {}; cand = new Set(); clearBox($('zLog')); render(); });
  $('zClimb').addEventListener('click', climb);
  $('zMax').addEventListener('click', () => { showMax = !showMax; render(); });
  $('zClear').addEventListener('click', () => { tok++; S = []; climbSeq = []; labels = {}; cand = new Set(); showMax = false; clearBox($('zLog')); render(); });

  Stepper($('zSteps'), [
    P('Assume P ≠ ∅, every chain has an upper bound, and (for a contradiction) P has no maximal element. Then every chain C has a <b>strict</b> upper bound: an upper bound u is not maximal, so some v &gt; u exists.',
      '设 P ≠ ∅，每条链都有上界，并（为导出矛盾）假设 P 没有极大元。则每条链 C 都有<b>严格</b>上界：上界 u 不是极大元，故存在 v &gt; u。'),
    P('By AC, fix a function g that assigns to every chain C a strict upper bound g(C). This is the only use of choice, and it is a single choice function on 𝒫(P), not infinitely many separate choices.',
      '由 AC，取定函数 g，给每条链 C 指定一个严格上界 g(C)。这是唯一用到选择的地方：一个定义在 𝒫(P) 上的选择函数，而不是无穷多次各自独立的选择。'),
    P('Transfinite recursion (Lesson 8): p<sub>α</sub> = g({p<sub>β</sub> : β &lt; α}). Induction shows {p<sub>β</sub> : β &lt; α} is a chain at every α: at successors, the new point lies above all old ones; at limits, it is a union of an increasing sequence of chains. So g is always applicable.',
      '超限递归（第 8 课）：p<sub>α</sub> = g({p<sub>β</sub> : β &lt; α})。归纳可证，对每个 α，{p<sub>β</sub> : β &lt; α} 都是链：后继阶段，新点在所有旧点之上；极限阶段，它是一列递增链的并。所以 g 总能用上。'),
    P('β &lt; α ⇒ p<sub>β</sub> &lt; p<sub>α</sub>, so α ↦ p<sub>α</sub> is an injection of the class of all ordinals into the set P. By Hartogs’ theorem (or Replacement plus Burali-Forti) this is impossible. ∎',
      'β &lt; α ⇒ p<sub>β</sub> &lt; p<sub>α</sub>，所以 α ↦ p<sub>α</sub> 把全体序数构成的类单射进集合 P。由哈托格斯定理（或替换公理加布拉利–福尔蒂悖论），这不可能。∎'),
    P('The animation is the finite shadow of this proof: the random pick plays the role of g, and the climb stops exactly when it reaches a maximal element. In ℕ ∪ {ω} you can see a limit stage, and in ℕ you can see what goes wrong when a chain has no upper bound.',
      '上面的动画就是这个证明的有限投影：随机挑选扮演 g 的角色，攀爬恰好停在极大元处。在 ℕ ∪ {ω} 中可以看到极限阶段；在 ℕ 中则可以看到链没有上界时会出什么问题。'),
  ]);
})();

/* ================= §4 bases ================= */
(function bases() {
  const fsvg = $('fano'), psvg = $('indPoset');
  const POS = { 1: [180, 30], 2: [30, 290], 4: [330, 290], 3: [105, 160], 5: [255, 160], 6: [180, 290], 7: [180, 203.3] };
  const LINES = [[1, 3, 2], [1, 5, 4], [2, 6, 4], [1, 7, 6], [2, 7, 5], [4, 7, 3]];
  const lab = v => v.toString(2).padStart(3, '0');
  let S = [], flash = null;
  const span = A => { let s = new Set([0]); A.forEach(v => { s = new Set([...s, ...[...s].map(x => x ^ v)]); }); return s; };
  const relation = (A, v) => {
    for (let m = 1; m < (1 << A.length); m++) {
      let x = 0; const part = [];
      A.forEach((a, i) => { if (m >> i & 1) { x ^= a; part.push(a); } });
      if (x === v) return part;
    }
    return null;
  };
  // independent sets by level
  const levels = [[[]], [], [], []];
  for (let a = 1; a <= 7; a++) levels[1].push([a]);
  for (let a = 1; a <= 7; a++) for (let b = a + 1; b <= 7; b++) levels[2].push([a, b]);
  for (let a = 1; a <= 7; a++) for (let b = a + 1; b <= 7; b++) for (let c = b + 1; c <= 7; c++) if ((a ^ b ^ c) !== 0) levels[3].push([a, b, c]);
  const key = A => [...A].sort((x, y) => x - y).join(',');
  const dotPos = {};
  levels.forEach((L, k) => L.forEach((A, i) => { dotPos[key(A)] = [120 + (i + 0.5) * (390 / L.length), 300 - k * 88]; }));

  function renderFano() {
    fsvg.innerHTML = '';
    const sp = span(S);
    const lineCol = ln => (flash && ln.every(p => flash.includes(p)) ? C.fal : '#c9c4b6');
    LINES.forEach(ln => {
      const [a, , c] = ln;
      el('line', { x1: POS[a][0], y1: POS[a][1], x2: POS[c][0], y2: POS[c][1], stroke: lineCol(ln), 'stroke-width': flash && ln.every(p => flash.includes(p)) ? 4 : 2 }, fsvg);
    });
    el('circle', { cx: 180, cy: 203.3, r: 86.6, fill: 'none', stroke: lineCol([3, 5, 6]), 'stroke-width': flash && [3, 5, 6].every(p => flash.includes(p)) ? 4 : 2 }, fsvg);
    for (let v = 1; v <= 7; v++) {
      const [x, y] = POS[v];
      const g = el('g', { class: 'clk', transform: `translate(${x},${y})` }, fsvg);
      const inS = S.includes(v), inSpan = sp.has(v);
      const isFlash = flash && flash.includes(v);
      if (!inSpan && S.length < 3) el('circle', { r: 25, fill: 'none', stroke: C.tru, 'stroke-width': 2, 'stroke-dasharray': '4 3' }, g);
      el('circle', { r: 20, fill: isFlash ? C.falSoft : inS ? C.accent : inSpan ? C.accentSoft : '#fff', stroke: isFlash ? C.fal : C.accent, 'stroke-width': 2 }, g);
      txt(g, 0, 4, lab(v), { 'text-anchor': 'middle', 'font-size': 12, 'font-weight': 700, fill: inS ? '#fff' : C.ink });
      g.addEventListener('click', () => click(v));
    }
  }
  function renderPoset() {
    psvg.innerHTML = '';
    const names = [['∅', '空集'], ['1 vector', '1 个向量'], ['2 vectors', '2 个向量'], ['bases', '基']];
    levels.forEach((L, k) => {
      txt2(psvg, 52, 300 - k * 88 + 2, `${names[k][0]}: ${L.length}`, `${names[k][1]}：${L.length}`, 12, { fill: k === 3 ? C.gold : C.muted, 'font-weight': 700 });
    });
    const chain = [];
    for (let i = 0; i <= S.length; i++) chain.push(key(S.slice(0, i)));
    const curKey = key(S);
    const sp = span(S);
    if (S.length < 3) {
      for (let v = 1; v <= 7; v++) if (!sp.has(v)) {
        const a = dotPos[curKey], b = dotPos[key([...S, v])];
        el('line', { x1: a[0], y1: a[1], x2: b[0], y2: b[1], stroke: C.tru, 'stroke-width': 1.2, opacity: 0.5 }, psvg);
      }
    }
    el('polyline', { points: chain.map(k => dotPos[k].join(',')).join(' '), fill: 'none', stroke: C.meta, 'stroke-width': 4, 'stroke-linejoin': 'round' }, psvg);
    levels.forEach((L, k) => L.forEach(A => {
      const kk = key(A), [x, y] = dotPos[kk];
      const on = chain.includes(kk);
      const c = el('circle', { cx: x, cy: y, r: on ? 7 : k === 3 ? 5 : 5.5, fill: on ? C.meta : k === 3 ? C.goldSoft : '#fff', stroke: k === 3 ? C.gold : '#9aa0aa', 'stroke-width': 1.5 }, psvg);
      const t = el('title', {}, c); t.textContent = '{' + A.map(lab).join(', ') + '}';
    }));
    const [cx, cy] = dotPos[curKey];
    if (S.length) txt(psvg, Math.min(Math.max(cx, 160), 460), cy - 13, '{' + S.map(lab).join(', ') + '}', { 'text-anchor': 'middle', 'font-size': 12, fill: C.meta, 'font-weight': 700 });
  }
  function report(extra) {
    const sp = span(S);
    let h = extra || '';
    if (S.length === 3) h += bi(`<b>Maximal!</b> No point can be added, because every point is already in span(S). So span(S) = V and S = {${S.map(lab).join(', ')}} is a <b>basis</b>. You reached one of the 28 gold maximal elements of the poset.`,
      `<b>极大了！</b>再也加不进任何点，因为每个点都已在 span(S) 中。于是 span(S) = V，S = {${S.map(lab).join(', ')}} 是一组<b>基</b>。你到达了偏序集中 28 个金色极大元之一。`);
    else h += bi(`S = {${S.map(lab).join(', ')}} is independent. Light-blue points lie in span(S) (${sp.size - 1} of 7); the dashed green rings mark points you can still add. The purple path on the right is your chain ∅ ⊂ … ⊂ S.`,
      `S = {${S.map(lab).join(', ')}} 线性无关。浅蓝色的点在 span(S) 中（7 个中有 ${sp.size - 1} 个）；绿色虚线圈是还能加入的点。右边的紫色路径就是你走出的链 ∅ ⊂ … ⊂ S。`);
    okBox($('fanoMsg'), h, S.length === 3 ? 'ok' : 'info');
  }
  function click(v) {
    flash = null;
    if (S.includes(v)) { S = S.filter(x => x !== v); render(); report(); return; }
    if (span(S).has(v)) {
      const rel = relation(S, v);
      flash = [...rel, v];
      render();
      okBox($('fanoMsg'), bi(`✗ ${lab(v)} = ${rel.map(lab).join(' + ')} (mod 2), so adding it would make S dependent. The red line is that relation.`,
        `✗ ${lab(v)} = ${rel.map(lab).join(' + ')}（模 2），加入后 S 就线性相关了。红线就是这个关系。`), 'bad');
      setTimeout(() => { flash = null; renderFano(); }, 1400);
      return;
    }
    S = [...S, v];
    render(); report();
  }
  function render() { renderFano(); renderPoset(); }
  $('fanoReset').addEventListener('click', () => { S = []; flash = null; render(); report(); });
  render(); report();

  Stepper($('basisSteps'), [
    P('Let P be the set of linearly independent subsets of V, ordered by ⊆. P ≠ ∅ since ∅ ∈ P.', '令 P 为 V 的全体线性无关子集，按 ⊆ 排序。∅ ∈ P，故 P ≠ ∅。'),
    P('Let 𝒞 be a chain in P and U = ⋃𝒞. A linear dependency involves only <b>finitely many</b> vectors v₁, …, vₙ ∈ U. Each lies in some member of 𝒞, and 𝒞 is a chain, so one member contains all of them. That member is independent, so the dependency cannot exist: U ∈ P is an upper bound.',
      '设 𝒞 是 P 中的链，U = ⋃𝒞。一个线性相关关系只涉及<b>有限个</b>向量 v₁, …, vₙ ∈ U。每个都属于 𝒞 的某个成员，而 𝒞 是链，所以有一个成员把它们全部包含。这个成员线性无关，所以这样的相关关系不存在：U ∈ P 是上界。'),
    P('By Zorn’s lemma, P has a maximal element B.', '由佐恩引理，P 有极大元 B。'),
    P('B spans V: if v ∉ span(B), then B ∪ {v} is still independent (in a dependency v would need a nonzero coefficient, putting v in span(B)), contradicting maximality. So B is a basis. ∎ This is the same mechanism you used in the Fano plane.',
      'B 张成 V：若 v ∉ span(B)，则 B ∪ {v} 仍线性无关（否则相关关系中 v 的系数非零，v 就落在 span(B) 中），与极大性矛盾。所以 B 是基。∎ 这和你在法诺平面上做的是同一个机制。'),
    P('Conversely, “every vector space has a basis” implies AC over ZF (Blass 1984). So this application is as strong as the axiom itself.', '反过来，在 ZF 上“每个向量空间都有基”蕴涵 AC（布拉斯，1984）。所以这个应用和公理本身一样强。'),
  ]);

  // ℝ over ℚ
  const items = [
    { l: '1', v: [1, 0, 0, 0, 0] }, { l: '½', v: [0.5, 0, 0, 0, 0] }, { l: '√2', v: [0, 1, 0, 0, 0] }, { l: '√8', v: [0, 2, 0, 0, 0] },
    { l: '√3', v: [0, 0, 1, 0, 0] }, { l: '√12', v: [0, 0, 2, 0, 0] }, { l: '√6', v: [0, 0, 0, 1, 0] }, { l: '√2+√3', v: [0, 1, 1, 0, 0] },
    { l: '(1+√2)²', v: [3, 2, 0, 0, 0] }, { l: 'π', v: [0, 0, 0, 0, 1] }, { l: 'π+½', v: [0.5, 0, 0, 0, 1] },
  ];
  const frac = x => {
    for (let d = 1; d <= 64; d++) { const n = Math.round(x * d); if (Math.abs(n / d - x) < 1e-9) return d === 1 ? String(n) : `${n}/${d}`; }
    return x.toFixed(4);
  };
  // Solve sum x_i * cols[i] = v; return coefficients or null.
  function solve(cols, v) {
    const m = 5, n = cols.length;
    const A = Array.from({ length: m }, (_, r) => [...cols.map(c => c[r]), v[r]]);
    let row = 0; const piv = [];
    for (let c = 0; c < n && row < m; c++) {
      let p = row; for (let r = row; r < m; r++) if (Math.abs(A[r][c]) > Math.abs(A[p][c])) p = r;
      if (Math.abs(A[p][c]) < 1e-12) continue;
      [A[row], A[p]] = [A[p], A[row]];
      const d = A[row][c]; for (let j = c; j <= n; j++) A[row][j] /= d;
      for (let r = 0; r < m; r++) if (r !== row && Math.abs(A[r][c]) > 1e-12) { const f = A[r][c]; for (let j = c; j <= n; j++) A[r][j] -= f * A[row][j]; }
      piv.push(c); row++;
    }
    for (let r = row; r < m; r++) if (Math.abs(A[r][n]) > 1e-9) return null;
    const x = Array(n).fill(0); piv.forEach((c, r) => { x[c] = A[r][n]; });
    return x;
  }
  let sel = [];
  const box = $('hamelChips');
  function renderChips() {
    box.innerHTML = '';
    items.forEach((it, i) => {
      const d = document.createElement('div');
      d.className = 'chip m' + (sel.includes(i) ? ' ok' : '');
      d.textContent = it.l;
      d.addEventListener('click', () => toggle(i, d));
      box.appendChild(d);
    });
  }
  function toggle(i, d) {
    if (sel.includes(i)) { sel = sel.filter(x => x !== i); renderChips(); show(); return; }
    const x = solve(sel.map(j => items[j].v), items[i].v);
    if (x) {
      const terms = sel.map((j, k) => [x[k], items[j].l]).filter(([c]) => Math.abs(c) > 1e-9).map(([c, l]) => `${frac(c) === '1' ? '' : frac(c) + '·'}${l}`);
      renderChips();
      box.children[i].classList.add('no');
      okBox($('hamelMsg'), bi(`✗ <span class="m">${items[i].l} = ${terms.join(' + ')}</span> with rational coefficients: dependent over ℚ, so it is not added.`,
        `✗ <span class="m">${items[i].l} = ${terms.join(' + ')}</span>，系数都是有理数：在 ℚ 上线性相关，不能加入。`), 'bad');
      return;
    }
    sel.push(i); renderChips(); show();
  }
  function show() {
    if (!sel.length) { okBox($('hamelMsg'), bi('Click numbers to build a ℚ-independent set.', '点击数字，组建一个在 ℚ 上线性无关的集合。'), 'info'); return; }
    okBox($('hamelMsg'), bi(`✓ {${sel.map(i => items[i].l).join(', ')}} is ℚ-linearly independent: its ℚ-span has dimension ${sel.length}. Zorn extends it to a Hamel basis, which is uncountable since ℝ is.`,
      `✓ {${sel.map(i => items[i].l).join(', ')}} 在 ℚ 上线性无关，它张成的 ℚ-子空间维数为 ${sel.length}。佐恩引理可把它扩充成哈默尔基；由于 ℝ 不可数，这组基也不可数。`), 'ok');
  }
  renderChips(); show();
})();

/* ================= §5 ultrafilters ================= */
(function ultrafilters() {
  const svg = $('ufSvg');
  const pc = m => [0, 1, 2, 3].filter(i => m >> i & 1).length;
  const name = m => (m === 0 ? '∅' : '{' + [0, 1, 2, 3].filter(i => m >> i & 1).map(i => i + 1).join(',') + '}');
  const byLevel = [[], [], [], [], []];
  for (let m = 0; m < 16; m++) byLevel[pc(m)].push(m);
  byLevel.forEach(L => L.sort((a, b) => name(a).localeCompare(name(b))));
  const pos = {};
  byLevel.forEach((L, k) => L.forEach((m, i) => { pos[m] = [350 + (i - (L.length - 1) / 2) * 108, 300 - k * 68]; }));
  let gens = new Set(), hover = null;
  const B = () => [...gens].reduce((a, g) => a & g, 15);
  const rects = [], labs = [], caps = [];
  function build() {
    svg.innerHTML = '';
    for (let m = 0; m < 16; m++) for (let i = 0; i < 4; i++) if (!(m >> i & 1)) {
      const [x1, y1] = pos[m], [x2, y2] = pos[m | 1 << i];
      el('line', { x1, y1, x2, y2, stroke: '#d6d1c2', 'stroke-width': 1.5 }, svg);
    }
    for (let m = 0; m < 16; m++) {
      const [x, y] = pos[m];
      const g = el('g', { class: 'hnode clk', transform: `translate(${x},${y})` }, svg);
      rects[m] = el('rect', { x: -42, y: -15, width: 84, height: 30, rx: 9 }, g);
      labs[m] = txt(g, 0, 5, m === 15 ? 'S' : name(m), { 'text-anchor': 'middle', 'font-size': 13 });
      caps[m] = txt(g, 47, -6, '⋂', { 'font-size': 16, fill: C.meta, 'font-weight': 700 });
      g.addEventListener('click', () => { if (gens.has(m)) gens.delete(m); else gens.add(m); render(); report(); hov(); });
      g.addEventListener('mouseenter', () => { hover = m; render(); hov(); });
      g.addEventListener('mouseleave', () => { hover = null; render(); clearBox($('ufHover')); });
    }
  }
  function render() {
    const b = B(), improper = gens.size && b === 0;
    for (let m = 0; m < 16; m++) {
      const inF = improper || (m & b) === b;
      const isH = hover !== null && (m === hover || m === (15 ^ hover));
      const r = rects[m];
      r.setAttribute('fill', improper ? C.falSoft : inF ? C.accentSoft : '#fff');
      r.setAttribute('stroke', gens.has(m) ? C.meta : isH ? C.gold : inF ? C.accent : '#b9b4a6');
      r.setAttribute('stroke-width', gens.has(m) ? 3.5 : isH ? 3 : 1.5);
      r.setAttribute('stroke-dasharray', isH && !gens.has(m) ? '5 3' : 'none');
      labs[m].setAttribute('font-weight', inF ? 700 : 400);
      labs[m].setAttribute('fill', inF ? (improper ? C.fal : C.accent) : C.muted);
      caps[m].setAttribute('opacity', !improper && gens.size && m === b ? 1 : 0);
    }
  }
  build();
  function hov() {
    if (hover === null) return;
    const b = B(), improper = gens.size && b === 0;
    const inF = m => improper || (m & b) === b;
    const A = hover, Ac = 15 ^ hover;
    const mk = v => (v ? '✓' : '✗');
    okBox($('ufHover'), `<span class="m">A = ${name(A)}: ${mk(inF(A))} ∈ F &nbsp;·&nbsp; S∖A = ${name(Ac)}: ${mk(inF(Ac))} ∈ F</span> ` +
      (inF(A) !== inF(Ac) ? bil('exactly one: F decides A', '恰有一个：F 对 A 作出了裁决') : !improper ? bil('neither: F does not decide A', '两个都不在：F 对 A 没有裁决') : ''), 'info');
  }
  function report() {
    const b = B(), box = $('ufMsg');
    const elts = [0, 1, 2, 3].filter(i => b >> i & 1).map(i => i + 1);
    if (!gens.size) okBox(box, bi('No generators yet: the generated filter is just {S}. Click some sets.', '还没有生成元：生成的滤子只有 {S}。点几个集合试试。'), 'info');
    else if (b === 0) okBox(box, bi('The generators have <b>empty intersection</b>, so ∅ would be forced into the filter. No proper filter contains them: the finite intersection property fails. Remove a generator.',
      '这些生成元的<b>交为空</b>，∅ 就被迫进入滤子。没有任何真滤子包含它们：有限交性质不成立。去掉一个生成元吧。'), 'bad');
    else if (elts.length === 1) okBox(box, bi(`<b>Ultrafilter ✓</b> F = {A : ${elts[0]} ∈ A}, the principal ultrafilter at ${elts[0]}. For every A, exactly one of A and S∖A contains ${elts[0]}. Hover any box to check.`,
      `<b>超滤子 ✓</b> F = {A : ${elts[0]} ∈ A}，即 ${elts[0]} 处的主超滤子。对每个 A，A 与 S∖A 中恰有一个含 ${elts[0]}。把鼠标移到任一方框上验证。`), 'ok');
    else okBox(box, bi(`Proper filter F = {A : A ⊇ B} with B = ⋂(generators) = {${elts.join(',')}}, so |F| = ${1 << (4 - elts.length)}. <b>Not ultra</b>: A = {${elts[0]}} and S∖A both fail to contain B.`,
      `真滤子 F = {A : A ⊇ B}，其中 B = ⋂(生成元) = {${elts.join(',')}}，|F| = ${1 << (4 - elts.length)}。<b>不是超滤子</b>：A = {${elts[0]}} 与 S∖A 都不包含 B。`), 'info');
  }
  $('ufExtend').addEventListener('click', () => {
    const b = B();
    if (gens.size && b === 0) { report(); return; }
    const k = [0, 1, 2, 3].find(i => b >> i & 1);
    gens.add(1 << k);
    render(); report();
    $('ufMsg').innerHTML += bi(`<br>Extended by adding {${k + 1}}. On a finite set no Zorn is needed: just pick some k ∈ B.`, `<br>加入 {${k + 1}} 完成扩张。有限集上用不着佐恩引理：在 B 中任取一个 k 即可。`);
  });
  $('ufReset').addEventListener('click', () => { gens = new Set(); render(); report(); });
  render(); report();

  // ℕ strip
  const nsvg = $('natSvg');
  const isPrime = n => { if (n < 2) return false; for (let d = 2; d * d <= n; d++) if (n % d === 0) return false; return true; };
  const sets = [
    { en: 'cofinite {n ≥ 10}', zh: '余有限集 {n ≥ 10}', f: n => n >= 10, v: 'in' },
    { en: 'finite {0,…,9}', zh: '有限集 {0,…,9}', f: n => n < 10, v: 'out' },
    { en: 'evens', zh: '偶数', f: n => n % 2 === 0, v: '?' },
    { en: 'odds', zh: '奇数', f: n => n % 2 === 1, v: '?' },
    { en: 'primes', zh: '素数', f: isPrime, v: '?' },
    { en: 'non-primes', zh: '非素数', f: n => !isPrime(n), v: '?' },
  ];
  function strip(f, col) {
    nsvg.innerHTML = '';
    for (let n = 0; n < 40; n++) {
      const x = 20 + n * 20;
      el('rect', { x, y: 14, width: 18, height: 30, rx: 4, fill: f(n) ? col : '#f1efe7', stroke: f(n) ? 'none' : '#ddd' }, nsvg);
      txt(nsvg, x + 9, 64, String(n), { 'text-anchor': 'middle', fill: C.muted });
    }
    txt(nsvg, 830, 36, '…', { 'font-size': 22, fill: '#999' });
  }
  const bar = $('natSets');
  sets.forEach(s => {
    const b = mkBtn(s.en, s.zh, 'btn small');
    b.addEventListener('click', () => {
      bar.querySelectorAll('button').forEach(x => x.classList.remove('sel'));
      b.classList.add('sel');
      strip(s.f, s.v === 'in' ? C.tru : s.v === 'out' ? C.fal : C.meta);
      if (s.v === 'in') okBox($('natMsg'), bi('<b>∈ U</b> for every non-principal U: U contains the Fréchet filter of all cofinite sets.', '对每个非主超滤子 U 都 <b>∈ U</b>：U 包含由全体余有限集构成的弗雷歇滤子。'), 'ok');
      else if (s.v === 'out') okBox($('natMsg'), bi('<b>∉ U</b>: its complement is cofinite, hence in U, and U cannot contain both a set and its complement (their intersection is ∅).', '<b>∉ U</b>：它的补集是余有限集，属于 U；而 U 不能同时含一个集合及其补集（二者之交为 ∅）。'), 'bad');
      else okBox($('natMsg'), bi(`This set and its complement are both infinite. U contains <b>exactly one</b> of them, but nothing tells you which: there are non-principal ultrafilters of both kinds, and ZFC cannot single out any particular one by a formula.`,
        `这个集合与它的补集都是无穷集。U 恰好包含其中<b>一个</b>，却没有任何东西告诉你是哪一个：两种情形的非主超滤子都存在，而 ZFC 无法用公式具体指定其中任何一个。`), 'warn');
    });
    bar.appendChild(b);
  });
  const hyp = () => {
    const n = +$('hypN').value;
    $('hypNv').textContent = n;
    bar.querySelectorAll('button').forEach(x => x.classList.remove('sel'));
    strip(k => k > n, C.tru);
    okBox($('natMsg'), bi(`Green: {k : k &gt; ${n}}. It is cofinite, hence in U, so <span class="m">[(0,1,2,3,…)] &gt; ${n}</span> in ℝ^ℕ/U. This works for every n, so the class is an infinite hypernatural number.`,
      `绿色：{k : k &gt; ${n}}。它是余有限集，属于 U，所以在 ℝ^ℕ/U 中 <span class="m">[(0,1,2,3,…)] &gt; ${n}</span>。对每个 n 都如此，所以这个等价类是一个无穷大的超自然数。`), 'ok');
  };
  $('hypN').addEventListener('input', hyp);
  bar.querySelector('button').click();

  Stepper($('ufSteps'), [
    P('<b>Ultrafilter lemma.</b> Let F be a proper filter on S. Let P be the set of proper filters G ⊇ F, ordered by ⊆. F ∈ P.', '<b>超滤子引理.</b> 设 F 是 S 上的真滤子。令 P 为所有包含 F 的真滤子 G 构成的集合，按 ⊆ 排序。F ∈ P。'),
    P('The union of a chain of proper filters is a proper filter: each axiom mentions only finitely many sets, which all lie in one member of the chain, and ∅ is in none of them. So chains have upper bounds.', '一条真滤子链的并仍是真滤子：每条公理只涉及有限个集合，它们都落在链的某一个成员中，而 ∅ 不在任何成员中。所以链都有上界。'),
    P('By Zorn, there is a maximal proper filter U ⊇ F.', '由佐恩引理，存在极大的真滤子 U ⊇ F。'),
    P('U is ultra. Let A ⊆ S. If every X ∈ U meets A, then {Y : Y ⊇ X ∩ A for some X ∈ U} is a proper filter containing U and A, so A ∈ U by maximality. Otherwise some X ∈ U has X ∩ A = ∅, i.e. X ⊆ S∖A, so S∖A ∈ U. ∎',
      'U 是超滤子。设 A ⊆ S。若 U 的每个成员 X 都与 A 相交，则 {Y : 存在 X ∈ U 使 Y ⊇ X ∩ A} 是包含 U 和 A 的真滤子，由极大性 A ∈ U。否则有 X ∈ U 使 X ∩ A = ∅，即 X ⊆ S∖A，于是 S∖A ∈ U。∎'),
    P('The ultrafilter lemma is strictly weaker than AC (Halpern–Lévy 1971) but not provable in ZF (Feferman 1965). It is equivalent to the <b>compactness theorem</b> of first-order logic (Lesson 5).', '超滤子引理严格弱于 AC（哈尔彭–莱维，1971），但在 ZF 中证明不了（费弗曼，1965）。它等价于一阶逻辑的<b>紧致性定理</b>（第 5 课）。'),
  ]);
})();

/* ================= §6 Vitali ================= */
(function vitali() {
  const svg = $('vSvg');
  const CX = 210, CY = 210, R = 160;
  const COLORS = ['#e03131', '#3b5bdb', '#2f9e44', '#f08c00', '#ae3ec9', '#0c8599'];
  const OFFS = [0.0071, 0.0213, 0.0362, 0.0498, 0.0641, 0.0779];
  let orbits = [], reps = null, q = 0, clicked = null, animQ = false;
  const ang = t => 2 * Math.PI * t - Math.PI / 2;
  const pt = (t, r = R) => [CX + r * Math.cos(ang(t)), CY + r * Math.sin(ang(t))];
  function star(g, x, y, r, fill, stroke) {
    const pts = [];
    for (let i = 0; i < 10; i++) { const a = -Math.PI / 2 + i * Math.PI / 5, rr = i % 2 ? r * 0.45 : r; pts.push(`${x + rr * Math.cos(a)},${y + rr * Math.sin(a)}`); }
    return el('polygon', { points: pts.join(' '), fill, stroke, 'stroke-width': 1.5 }, g);
  }
  function render() {
    svg.innerHTML = '';
    el('circle', { cx: CX, cy: CY, r: R, fill: 'none', stroke: '#c9c4b6', 'stroke-width': 2 }, svg);
    for (let k = 0; k < 12; k++) {
      const [x1, y1] = pt(k / 12, R - 6), [x2, y2] = pt(k / 12, R + 6);
      el('line', { x1, y1, x2, y2, stroke: '#ddd' }, svg);
    }
    txt(svg, CX, CY - 8, '𝕋 = ℝ/ℤ', { 'text-anchor': 'middle', 'font-size': 15, fill: C.muted });
    txt(svg, CX, CY + 14, reps ? 'V = {★}' : '', { 'text-anchor': 'middle', 'font-size': 14, fill: C.ink, 'font-weight': 700 });
    if (clicked) {
      const o = orbits[clicked.o];
      const [x1, y1] = pt(o.x + reps[clicked.o] / 12), [x2, y2] = pt(o.x + clicked.k / 12);
      el('line', { x1, y1, x2, y2, stroke: o.col, 'stroke-width': 2, 'stroke-dasharray': '4 4' }, svg);
    }
    orbits.forEach((o, oi) => {
      for (let k = 0; k < 12; k++) {
        const [x, y] = pt(o.x + k / 12);
        const isRep = reps && reps[oi] === k;
        const g = el('g', { class: 'clk' }, svg);
        if (isRep) star(g, x, y, 10, o.col, C.ink);
        else el('circle', { cx: x, cy: y, r: clicked && clicked.o === oi && clicked.k === k ? 7 : 4.5, fill: o.col, stroke: '#fff', 'stroke-width': 1 }, g);
        g.addEventListener('click', () => pick(oi, k));
      }
    });
    if (reps && q) {
      const g = el('g', {}, svg);
      g.style.transformOrigin = `${CX}px ${CY}px`;
      g.style.transformBox = 'view-box';
      g.style.transition = 'transform 1.1s cubic-bezier(.3,.9,.3,1)';
      orbits.forEach((o, oi) => { const [x, y] = pt(o.x + reps[oi] / 12, R + 20); star(g, x, y, 8, 'none', C.meta); });
      const [lx, ly] = pt(reps.length ? orbits[0].x + reps[0] / 12 : 0, R + 38);
      txt(g, lx, ly + 4, 'V+q', { 'text-anchor': 'middle', 'font-size': 12, fill: C.meta, 'font-weight': 700 });
      if (animQ) requestAnimationFrame(() => requestAnimationFrame(() => { g.style.transform = `rotate(${q * 30}deg)`; }));
      else { g.style.transition = 'none'; g.style.transform = `rotate(${q * 30}deg)`; }
      animQ = false;
    }
  }
  function pick(oi, k) {
    if (!reps) { okBox($('vMsg'), bi('First choose the representatives (AC).', '请先选出代表元（AC）。'), 'warn'); return; }
    clicked = { o: oi, k };
    render();
    const d = ((k - reps[oi]) % 12 + 12) % 12;
    okBox($('vMsg'), bi(`This point is x + ${k}/12 in the class of x (color). Its chosen representative is v = x + ${reps[oi]}/12, so the point equals v + q with <b>q = ${d}/12 ∈ ℚ</b>. It lies in V + ${d}/12 and in no other translate, since every other representative differs from it by an irrational.`,
      `这个点是同色等价类中的 x + ${k}/12。该类选出的代表元是 v = x + ${reps[oi]}/12，所以这个点等于 v + q，其中 <b>q = ${d}/12 ∈ ℚ</b>。它属于 V + ${d}/12，而不属于其他任何平移，因为它与别的代表元之差都是无理数。`), 'info');
  }
  function addOrbit() {
    if (orbits.length >= 6) { okBox($('vMsg'), bi('Enough for the picture. There are 2^ℵ₀ classes in reality.', '图上画这些就够了。实际上有 2^ℵ₀ 个等价类。'), 'info'); return; }
    orbits.push({ x: OFFS[orbits.length], col: COLORS[orbits.length] });
    if (reps) reps.push(Math.floor(Math.random() * 12));
    render();
    okBox($('vMsg'), bi(`${orbits.length} classes shown. Each class x + ℚ is countable and dense in 𝕋. We draw only its 12 points x + k/12.`, `已显示 ${orbits.length} 个等价类。每个等价类 x + ℚ 在 𝕋 中可数且稠密，这里只画出其中 12 个点 x + k/12。`), 'info');
  }
  $('vAdd').addEventListener('click', addOrbit);
  $('vChoose').addEventListener('click', () => {
    reps = orbits.map(() => Math.floor(Math.random() * 12));
    clicked = null; render();
    okBox($('vMsg'), bi('★ = the chosen point of each class. V = {★} meets every class exactly once. For 2^ℵ₀ classes with no rule to pick a point, this needs AC. Press again for a different V.',
      '★ = 每个等价类中选出的点。V = {★} 与每个等价类恰好交于一点。面对 2^ℵ₀ 个等价类且没有选点规则，这一步要用 AC。再按一次会得到另一个 V。'), 'ok');
  });
  const qs = [0, 1, 2, 3, 4, 6, 8, 10];
  const qlab = k => (k === 0 ? '0' : (() => { const g = (a, b) => (b ? g(b, a % b) : a); const d = g(k, 12); return `${k / d}/${12 / d}`; })());
  qs.forEach(k => {
    const b = document.createElement('button');
    b.dataset.q = String(k);
    b.textContent = qlab(k);
    $('vQ').appendChild(b);
  });
  seg('vQ', 'q', '0', v => {
    q = +v; animQ = true;
    if (!reps && q) { okBox($('vMsg'), bi('First choose the representatives (AC).', '请先选出代表元（AC）。'), 'warn'); }
    else if (q) okBox($('vMsg'), bi(`The purple outline stars are V + ${qlab(q)}: V rotated by ${q * 30}°. Each one sits on a dot of its own class and never on a ★ of V, so V + ${qlab(q)} and V are disjoint.`,
      `紫色空心星是 V + ${qlab(q)}，即 V 旋转 ${q * 30}° 的结果。每颗都落在本类的某个点上，绝不会落到 V 的 ★ 上，所以 V + ${qlab(q)} 与 V 不交。`), 'info');
    render();
  });
  $('vReset').addEventListener('click', () => { orbits = []; reps = null; clicked = null; for (let i = 0; i < 3; i++) addOrbit(); });
  for (let i = 0; i < 3; i++) addOrbit();

  // measure bar
  const bsv = $('vBar');
  const cval = () => +$('vC').value / 40;
  let btok = 0;
  const yOf = v => 260 - v * 190;
  function axes() {
    bsv.innerHTML = '';
    el('line', { x1: 50, y1: 260, x2: 360, y2: 260, stroke: '#999' }, bsv);
    el('line', { x1: 50, y1: 20, x2: 50, y2: 260, stroke: '#999' }, bsv);
    el('line', { x1: 50, y1: yOf(1), x2: 360, y2: yOf(1), stroke: C.fal, 'stroke-width': 2, 'stroke-dasharray': '6 4' }, bsv);
    txt(bsv, 356, yOf(1) - 6, 'μ(𝕋) = 1', { 'text-anchor': 'end', 'font-size': 13, fill: C.fal, 'font-weight': 700 });
    txt(bsv, 44, 264, '0', { 'text-anchor': 'end', 'font-size': 12, fill: C.muted });
    txt(bsv, 44, yOf(1) + 4, '1', { 'text-anchor': 'end', 'font-size': 12, fill: C.muted });
  }
  function showC() { $('vCv').textContent = cval() === 0 ? '0' : cval().toFixed(3); }
  async function sum() {
    const my = ++btok;
    axes();
    const c = cval();
    const counter = txt(bsv, 200, 290, '', { 'text-anchor': 'middle', 'font-size': 14, 'font-weight': 700 });
    let total = 0;
    for (let n = 1; n <= 40; n++) {
      if (my !== btok) return;
      if (yOf(total + c) < 20) {
        el('polygon', { points: '120,14 100,30 140,30', fill: C.meta, class: 'pop' }, bsv);
        txt(bsv, 150, 26, '→ ∞', { 'font-size': 16, fill: C.meta, 'font-weight': 800 });
        counter.textContent = `Σ = ∞ ≠ 1`;
        okBox($('vSumMsg'), bi(`With c = ${c.toFixed(3)} &gt; 0 the partial sums pass 1 after ${Math.ceil(1 / c - 1e-9)} translates and grow without bound: Σ<sub>q</sub> c = ∞ ≠ 1. Contradiction.`,
          `取 c = ${c.toFixed(3)} &gt; 0，累加 ${Math.ceil(1 / c - 1e-9)} 个平移后部分和就超过 1，并且无限增长：Σ<sub>q</sub> c = ∞ ≠ 1。矛盾。`), 'bad');
        return;
      }
      const h = c * 190;
      if (h > 0) el('rect', { x: 100, y: yOf(total + c), width: 40, height: Math.max(h - 0.6, 0.5), fill: n % 2 ? '#d0bfff' : '#b197fc', class: 'fadein' }, bsv);
      total += c;
      counter.textContent = `n = ${n}:  μ(V+q₁) + … + μ(V+qₙ) = ${total.toFixed(3)}`;
      await sleep(c === 0 ? 40 : 110);
    }
    okBox($('vSumMsg'), bi('With c = 0 every partial sum is 0, so Σ<sub>q</sub> 0 = 0 ≠ 1. Contradiction. Either way V cannot have a length.', '取 c = 0，每个部分和都是 0，于是 Σ<sub>q</sub> 0 = 0 ≠ 1，矛盾。无论哪种情形，V 都不可能有长度。'), 'bad');
  }
  $('vC').addEventListener('input', () => { showC(); btok++; axes(); clearBox($('vSumMsg')); });
  $('vSum').addEventListener('click', sum);
  showC(); axes();

  Stepper($('vSteps'), [
    P('On 𝕋 = ℝ/ℤ let x ~ y ⇔ x − y ∈ ℚ. Each class x + ℚ is countable, so there are 2^ℵ₀ classes.', '在 𝕋 = ℝ/ℤ 上令 x ~ y ⇔ x − y ∈ ℚ。每个等价类 x + ℚ 可数，所以共有 2^ℵ₀ 个等价类。'),
    P('By AC choose V ⊆ 𝕋 containing exactly one point of each class (a <b>Vitali set</b>).', '由 AC 取 V ⊆ 𝕋，使它恰好含每个等价类中的一个点（<b>维塔利集</b>）。'),
    P('For q ∈ ℚ ∩ [0,1) the translates V + q (mod 1) are pairwise disjoint: v + q = v′ + q′ gives v ~ v′, so v = v′ and q = q′. They cover 𝕋: any x is ~ its representative v, and x = v + (x − v).',
      '对 q ∈ ℚ ∩ [0,1)，各平移 V + q（模 1）两两不交：由 v + q = v′ + q′ 得 v ~ v′，从而 v = v′，q = q′。它们覆盖 𝕋：任一 x 与其代表元 v 等价，且 x = v + (x − v)。'),
    P('Suppose μ is countably additive and rotation-invariant, μ(𝕋) = 1, and μ(V) is defined. Then 1 = Σ<sub>q</sub> μ(V + q) = Σ<sub>q</sub> μ(V), which is 0 or ∞. Contradiction. In particular V is <b>not Lebesgue measurable</b>. ∎',
      '设 μ 可数可加、旋转不变、μ(𝕋) = 1，且 μ(V) 有定义。则 1 = Σ<sub>q</sub> μ(V + q) = Σ<sub>q</sub> μ(V)，而右边只能是 0 或 ∞，矛盾。特别地，V <b>不是勒贝格可测集</b>。∎'),
    P('Choice is essential: Solovay (1970), assuming an inaccessible cardinal, built a model of ZF + DC in which <b>every</b> set of reals is Lebesgue measurable.', '选择公理不可缺少：索洛维（1970）在假设存在不可达基数的前提下，构造了 ZF + DC 的一个模型，其中<b>每个</b>实数集都是勒贝格可测的。'),
  ]);
})();

/* ================= free group words (shared by §7, E3) ================= */
const INV = { a: 'A', A: 'a', b: 'B', B: 'b' };
function reduceWord(w) {
  const st = [];
  for (const c of w) { if (st.length && st[st.length - 1] === INV[c]) st.pop(); else st.push(c); }
  return st.join('');
}
const LET = { a: 'a', A: 'a⁻¹', b: 'b', B: 'b⁻¹' };
const fmtWord = w => (w === '' ? 'e' : [...w].map(c => LET[c]).join(''));
const PIECE_COL = { a: '#e03131', A: '#f08c00', b: '#3b5bdb', B: '#2f9e44', '': '#1f2430' };
const pieceName = w => (w === '' ? '{e}' : `W(${LET[w[0]]})`);

/* ================= §7 free group ================= */
(function freeGroup() {
  const svg = $('fgSvg');
  const D = 5, L0 = 140, RATIO = 0.47, CX = 320, CY = 320;
  const DIR = { a: [1, 0], A: [-1, 0], b: [0, -1], B: [0, 1] };
  const RAD = [9, 7, 5.2, 3.8, 2.8, 2.1];
  const WID = [3.2, 2.4, 1.7, 1.2, 0.9];
  const words = [''], pos = { '': [CX, CY] };
  for (let i = 0; i < words.length; i++) {
    const w = words[i];
    if (w.length >= D) continue;
    for (const x of 'aAbB') {
      if (w.length && INV[x] === w[w.length - 1]) continue;
      const nw = w + x, len = L0 * Math.pow(RATIO, w.length);
      pos[nw] = [pos[w][0] + DIR[x][0] * len, pos[w][1] + DIR[x][1] * len];
      words.push(nw);
    }
  }
  const nodeEl = {}, edgeEl = {};
  let tok = 0;
  function build() {
    svg.innerHTML = '';
    const gE = el('g', {}, svg), gN = el('g', {}, svg);
    words.forEach(w => {
      if (!w) return;
      const p = w.slice(0, -1);
      edgeEl[w] = el('line', { x1: pos[p][0], y1: pos[p][1], x2: pos[w][0], y2: pos[w][1], stroke: PIECE_COL[w[0]], 'stroke-width': WID[w.length - 1], opacity: 0.75 }, gE);
    });
    words.forEach(w => {
      const c = el('circle', { cx: pos[w][0], cy: pos[w][1], r: RAD[w.length], fill: PIECE_COL[w[0] || ''], stroke: '#fff', 'stroke-width': w.length < 3 ? 1.5 : 0.5, class: 'clk' }, gN);
      const t = el('title', {}, c); t.textContent = fmtWord(w);
      c.addEventListener('click', () => info(w));
      nodeEl[w] = c;
    });
    [['a', 'a'], ['A', 'a⁻¹'], ['b', 'b'], ['B', 'b⁻¹']].forEach(([x, s]) => {
      const p = pos[x];
      txt(svg, p[0] + 12, p[1] - 10, s, { 'font-size': 15, 'font-weight': 800, fill: PIECE_COL[x], stroke: '#fbfaf6', 'stroke-width': 4, 'paint-order': 'stroke' });
    });
    txt(svg, CX + 12, CY - 10, 'e', { 'font-size': 15, 'font-weight': 800, stroke: '#fbfaf6', 'stroke-width': 4, 'paint-order': 'stroke' });
  }
  function info(w) {
    const aw = reduceWord('a' + w), bw = reduceWord('b' + w);
    $('fgInfo').innerHTML = `<div class="m" style="font-size:17px"><b>w = ${fmtWord(w)}</b></div>
      <div>${bil('piece', '所属块')}: <b style="color:${PIECE_COL[w[0] || '']}">${pieceName(w)}</b></div>
      <div class="m">a·w = ${fmtWord(aw)} <span style="color:${PIECE_COL[aw[0] || '']}">∈ ${pieceName(aw)}</span></div>
      <div class="m">b·w = ${fmtWord(bw)} <span style="color:${PIECE_COL[bw[0] || '']}">∈ ${pieceName(bw)}</span></div>
      <p class="muted" style="font-size:13px">${bi('Left multiplication by a sends W(a⁻¹) onto F₂ ∖ W(a). Try a node in the orange piece.', '左乘 a 把 W(a⁻¹) 映满 F₂ ∖ W(a)。点一下橙色块里的节点试试。')}</p>`;
  }
  function legend() {
    $('fgLegend').innerHTML = [['a', 'W(a)'], ['A', 'W(a⁻¹)'], ['b', 'W(b)'], ['B', 'W(b⁻¹)'], ['', 'e']]
      .map(([k, s]) => `<span><i style="background:${PIECE_COL[k]}"></i><span class="m">${s}</span></span>`).join('');
  }
  async function animate(x) {
    const my = ++tok;
    build();
    const X = x.toUpperCase();
    const movers = words.filter(w => w[0] === X);
    words.forEach(w => {
      if (w[0] === X || w[0] === x) return;
      nodeEl[w].setAttribute('opacity', 0.12);
      if (edgeEl[w]) edgeEl[w].setAttribute('opacity', 0.08);
    });
    edgeEl[X].setAttribute('opacity', 0);
    const target = w => pos[reduceWord(x + w)];
    const T = 1800, t0 = performance.now();
    okBox($('fgMsg'), bi(`Multiplying every word of ${pieceName(X)} on the left by ${x}…`, `把 ${pieceName(X)} 中的每个字左乘 ${x}……`), 'info');
    await new Promise(res => {
      function frame(now) {
        if (my !== tok) return res();
        let s = Math.min(1, (now - t0) / T);
        s = s < 0.5 ? 2 * s * s : 1 - Math.pow(-2 * s + 2, 2) / 2;
        const P2 = w => { const a = pos[w], b = target(w); return [a[0] + (b[0] - a[0]) * s, a[1] + (b[1] - a[1]) * s]; };
        movers.forEach(w => {
          const p = P2(w);
          nodeEl[w].setAttribute('cx', p[0]); nodeEl[w].setAttribute('cy', p[1]);
          nodeEl[w].setAttribute('r', RAD[w.length] + (RAD[w.length - 1] - RAD[w.length]) * s);
          if (w.length >= 2) {
            const q = P2(w.slice(0, -1));
            const e = edgeEl[w];
            e.setAttribute('x1', q[0]); e.setAttribute('y1', q[1]); e.setAttribute('x2', p[0]); e.setAttribute('y2', p[1]);
            e.setAttribute('stroke-width', WID[w.length - 1] + ((WID[w.length - 2] || 3.2) - WID[w.length - 1]) * s);
          }
        });
        if (s < 1) requestAnimationFrame(frame); else res();
      }
      requestAnimationFrame(frame);
    });
    if (my !== tok) return;
    const nm = x === 'a' ? ['W(a)', 'a·W(a⁻¹)', 'red', '红色'] : ['W(b)', 'b·W(b⁻¹)', 'blue', '蓝色'];
    okBox($('fgMsg'), bi(`Done. The ${nm[2]} piece ${nm[0]} stayed put, and ${nm[1]} now covers <b>every other vertex</b>: e and the other three branches. So F₂ = ${nm[0]} ⊔ ${nm[1]}. (The picture is cut at depth ${D}; the moved piece fills everything up to depth ${D - 1}.)`,
      `完成。${nm[3]}块 ${nm[0]} 原地不动，而 ${nm[1]} 现在覆盖了<b>其余所有顶点</b>：e 和另外三根分支。所以 F₂ = ${nm[0]} ⊔ ${nm[1]}。（图只画到深度 ${D}；移动后的块填满了深度 ${D - 1} 以内的一切。）`), 'ok');
  }
  $('fgA').addEventListener('click', () => animate('a'));
  $('fgB').addEventListener('click', () => animate('b'));
  $('fgReset').addEventListener('click', () => { tok++; build(); clearBox($('fgMsg')); });
  legend(); build(); info('Ab');
})();

/* ================= §8 rotations + Banach–Tarski ================= */
// Exact arithmetic: a point (a, b√2, c)/3^k is stored as integers [a, b, c].
// ρ = rotation about z, σ = rotation about x, both by arccos(1/3).
const ROT = {
  r: v => [v[0] - 4 * v[1], v[1] + 2 * v[0], 3 * v[2]],
  R: v => [v[0] + 4 * v[1], v[1] - 2 * v[0], 3 * v[2]],
  s: v => [3 * v[0], v[1] - 2 * v[2], v[2] + 4 * v[1]],
  S: v => [3 * v[0], v[1] + 2 * v[2], v[2] - 4 * v[1]],
};
const RINV = { r: 'R', R: 'r', s: 'S', S: 's' };
const RLET = { r: 'ρ', R: 'ρ⁻¹', s: 'σ', S: 'σ⁻¹' };
function reduceRot(w) {
  const st = [];
  for (const c of w) { if (st.length && st[st.length - 1] === RINV[c]) st.pop(); else st.push(c); }
  return st.join('');
}
const fmtRot = w => (w === '' ? 'id' : [...w].map(c => RLET[c]).join(''));
function rotTrace(w) {
  let v = [1, 0, 0];
  const rows = [{ letter: '', v, k: 0 }];
  for (let i = w.length - 1, k = 1; i >= 0; i--, k++) { v = ROT[w[i]](v); rows.push({ letter: w[i], v, k }); }
  return rows;
}
const mod3 = n => ((n % 3) + 3) % 3;
const toUnit = (v, k) => [v[0] / 3 ** k, v[1] * Math.SQRT2 / 3 ** k, v[2] / 3 ** k];

(function rotations() {
  let word = '';
  const keys = $('rotKeys');
  [['r', 'ρ'], ['R', 'ρ⁻¹'], ['s', 'σ'], ['S', 'σ⁻¹']].forEach(([c, s]) => {
    const b = document.createElement('button');
    b.className = 'btn kbd';
    b.textContent = s;
    b.addEventListener('click', () => { if (word.length < 14) { word = reduceRot(word + c); update(); } });
    keys.appendChild(b);
  });
  const back = mkBtn('⌫', '⌫', 'btn kbd'); back.innerHTML = '⌫';
  back.addEventListener('click', () => { word = word.slice(0, -1); update(); });
  const clr = mkBtn('Clear', '清空', 'btn small ghost');
  clr.addEventListener('click', () => { word = ''; update(); });
  const rnd = mkBtn('Random word', '随机字', 'btn small');
  rnd.addEventListener('click', () => {
    let w = '';
    while (w.length < 7) { const c = 'rRsS'[Math.floor(Math.random() * 4)]; if (!w.length || RINV[c] !== w[w.length - 1]) w += c; }
    word = w; update();
  });
  keys.append(back, clr, rnd);

  // sphere projection
  const sv = $('rotSphere');
  const phi = -0.6, tilt = 0.35;
  const proj = p => {
    const x1 = p[0] * Math.cos(phi) - p[1] * Math.sin(phi), y1 = p[0] * Math.sin(phi) + p[1] * Math.cos(phi), z1 = p[2];
    const y2 = y1 * Math.cos(tilt) - z1 * Math.sin(tilt), z2 = y1 * Math.sin(tilt) + z1 * Math.cos(tilt);
    return { X: 150 + 120 * x1, Y: 150 - 120 * z2, front: y2 < 0 };
  };
  function slerp(a, b, t) {
    const d = Math.min(1, Math.max(-1, a[0] * b[0] + a[1] * b[1] + a[2] * b[2])), om = Math.acos(d);
    if (om < 1e-6) return a;
    const s1 = Math.sin((1 - t) * om) / Math.sin(om), s2 = Math.sin(t * om) / Math.sin(om);
    return [a[0] * s1 + b[0] * s2, a[1] * s1 + b[1] * s2, a[2] * s1 + b[2] * s2];
  }
  function drawSphere(pts) {
    sv.innerHTML = '';
    el('circle', { cx: 150, cy: 150, r: 120, fill: '#f4f6ff', stroke: '#9aa5d6', 'stroke-width': 1.5 }, sv);
    const eq = []; for (let i = 0; i <= 60; i++) { const t = i / 60 * 2 * Math.PI; const q = proj([Math.cos(t), Math.sin(t), 0]); eq.push(`${q.X},${q.Y}`); }
    el('polyline', { points: eq.join(' '), fill: 'none', stroke: '#c5cbe8', 'stroke-dasharray': '3 3' }, sv);
    [[[0, 0, 1], 'ρ (z)'], [[1, 0, 0], 'σ (x)']].forEach(([ax, s]) => {
      const a = proj(ax), b = proj(ax.map(t => -t));
      el('line', { x1: b.X, y1: b.Y, x2: a.X, y2: a.Y, stroke: '#9aa0aa', 'stroke-dasharray': '2 3' }, sv);
      txt(sv, b.X + (b.X < 150 ? -4 : 4), b.Y + (b.Y > 150 ? 14 : -4), s, { 'font-size': 12, fill: C.muted, 'text-anchor': b.X < 150 ? 'end' : 'start' });
    });
    for (let i = 1; i < pts.length; i++) {
      for (let j = 0; j < 12; j++) {
        const p = proj(slerp(pts[i - 1], pts[i], j / 12)), q = proj(slerp(pts[i - 1], pts[i], (j + 1) / 12));
        el('line', { x1: p.X, y1: p.Y, x2: q.X, y2: q.Y, stroke: C.meta, 'stroke-width': p.front ? 2.2 : 1.2, opacity: p.front ? 0.9 : 0.35 }, sv);
      }
    }
    pts.forEach((p, i) => {
      const q = proj(p);
      el('circle', { cx: q.X, cy: q.Y, r: i === 0 ? 6 : 4, fill: i === 0 ? C.ink : i === pts.length - 1 ? C.gold : C.meta, opacity: q.front ? 1 : 0.45 }, sv);
    });
    const s0 = proj([1, 0, 0]);
    txt(sv, s0.X - 8, s0.Y - 10, '(1,0,0)', { 'font-size': 11, 'font-weight': 700, 'text-anchor': 'end' });
  }
  function update() {
    $('rotWord').textContent = 'w = ' + fmtRot(word);
    if (!word) {
      $('rotTable').innerHTML = '';
      okBox($('rotMsg'), bi('The empty word is the identity. Press some letters; adjacent inverse pairs cancel automatically.', '空字就是恒等变换。按几个字母试试；相邻的互逆字母会自动抵消。'), 'info');
      drawSphere([[1, 0, 0]]);
      return;
    }
    let test = word, note = '';
    if ('sS'.includes(word[word.length - 1])) {
      test = reduceRot('r' + word + 'R');
      note = bi(`w ends in σ<sup>±1</sup>, so we test the conjugate u = ρ·w·ρ⁻¹ = <b>${fmtRot(test)}</b>, which is reduced and ends in ρ⁻¹. Clearly w = id ⇔ u = id.<br>`,
        `w 以 σ<sup>±1</sup> 结尾，所以改测它的共轭 u = ρ·w·ρ⁻¹ = <b>${fmtRot(test)}</b>，它是既约字且以 ρ⁻¹ 结尾。显然 w = id ⇔ u = id。<br>`);
    }
    const rows = rotTrace(test);
    let h = `<table class="rot"><tr><th>#</th><th>${bil('apply', '作用')}</th><th>a</th><th>b</th><th>c</th><th>k</th><th>b mod 3</th><th>(x, y, z)</th></tr>`;
    rows.forEach((r, i) => {
      const u = toUnit(r.v, r.k);
      h += `<tr><td>${i}</td><td>${r.letter ? RLET[r.letter] : bil('start', '起点')}</td><td>${r.v[0]}</td><td>${r.v[1]}</td><td>${r.v[2]}</td><td>${r.k}</td>
        <td class="${i && mod3(r.v[1]) ? 'hit' : ''}">${i ? mod3(r.v[1]) : '–'}</td><td>(${u.map(t => t.toFixed(3)).join(', ')})</td></tr>`;
    });
    $('rotTable').innerHTML = h + '</table>';
    const last = rows[rows.length - 1];
    const ok = mod3(last.v[1]) !== 0;
    okBox($('rotMsg'), note + (ok ? bi(`Final point = (a, b√2, c)/3<sup>${last.k}</sup> with b = ${last.v[1]} ≢ 0 (mod 3). So b ≠ 0, the point is not (1,0,0), and <b>${fmtRot(word)} ≠ id</b>.`,
      `终点 = (a, b√2, c)/3<sup>${last.k}</sup>，其中 b = ${last.v[1]} ≢ 0 (mod 3)。所以 b ≠ 0，终点不是 (1,0,0)，<b>${fmtRot(word)} ≠ id</b>。`)
      : bi('Unexpected: b ≡ 0 (mod 3).', '意外：b ≡ 0 (mod 3)。')), ok ? 'ok' : 'bad');
    drawSphere(rows.map(r => toUnit(r.v, r.k)));
  }
  word = 'rsR';
  update();
})();

(function banachTarski() {
  const svg = $('btSvg');
  const DIR = { a: [1, 0], A: [-1, 0], b: [0, -1], B: [0, 1] };
  function miniTree(g, cx, cy, L, depth, colored) {
    const ws = [''], pos = { '': [cx, cy] };
    for (let i = 0; i < ws.length; i++) {
      const w = ws[i];
      if (w.length >= depth) continue;
      for (const x of 'aAbB') {
        if (w.length && INV[x] === w[w.length - 1]) continue;
        const nw = w + x, len = L * Math.pow(0.47, w.length);
        pos[nw] = [pos[w][0] + DIR[x][0] * len, pos[w][1] + DIR[x][1] * len];
        ws.push(nw);
      }
    }
    ws.forEach(w => { if (!w) return; const p = pos[w.slice(0, -1)]; el('line', { x1: p[0], y1: p[1], x2: pos[w][0], y2: pos[w][1], stroke: colored ? PIECE_COL[w[0]] : '#9aa0aa', 'stroke-width': 2.2 - 0.5 * w.length }, g); });
    ws.forEach(w => { if (w) el('circle', { cx: pos[w][0], cy: pos[w][1], r: 3.6 - 0.7 * w.length, fill: colored ? PIECE_COL[w[0]] : '#9aa0aa' }, g); });
    const pts = [];
    for (let i = 0; i < 10; i++) { const a = -Math.PI / 2 + i * Math.PI / 5, rr = i % 2 ? 3.4 : 8; pts.push(`${cx + rr * Math.cos(a)},${cy + rr * Math.sin(a)}`); }
    el('polygon', { points: pts.join(' '), fill: C.gold, stroke: C.ink, 'stroke-width': 1 }, g);
  }
  function sphere(g, cx, cy, r, fill = '#eef1ff') {
    el('circle', { cx, cy, r, fill, stroke: '#7c8bd6', 'stroke-width': 1.5 }, g);
    el('ellipse', { cx, cy, rx: r, ry: r * 0.3, fill: 'none', stroke: '#b6bfe8', 'stroke-dasharray': '3 3' }, g);
  }
  function cap(en, zh) { txt2(svg, 210, 268, en, zh, 13, { fill: C.ink, 'font-weight': 700 }); }
  function draw(k) {
    svg.innerHTML = '';
    if (k === 0) { txt2(svg, 210, 140, 'Press “Next step”', '请按“下一步”', 15, { fill: C.muted }); return; }
    if (k === 1) {
      sphere(svg, 210, 125, 95);
      el('line', { x1: 210, y1: 15, x2: 210, y2: 235, stroke: C.accent, 'stroke-width': 2 }, svg);
      el('line', { x1: 95, y1: 160, x2: 325, y2: 90, stroke: C.tru, 'stroke-width': 2 }, svg);
      el('path', { d: 'M 185 30 A 25 8 0 1 0 235 30', fill: 'none', stroke: C.accent, 'stroke-width': 2.5 }, svg);
      txt(svg, 244, 34, 'ρ', { 'font-size': 18, fill: C.accent, 'font-weight': 800 });
      el('path', { d: 'M 300 82 A 8 22 -17 1 1 312 112', fill: 'none', stroke: C.tru, 'stroke-width': 2.5 }, svg);
      txt(svg, 326, 82, 'σ', { 'font-size': 18, fill: C.tru, 'font-weight': 800 });
      cap('⟨ρ, σ⟩ ≅ F₂ acting on S²', '⟨ρ, σ⟩ ≅ F₂ 作用于 S²');
    } else if (k === 2) {
      sphere(svg, 210, 125, 95);
      [[150, 70, 270, 180], [240, 40, 180, 210], [120, 120, 300, 130], [175, 160, 245, 90]].forEach(([x1, y1, x2, y2]) => {
        el('line', { x1, y1, x2, y2, stroke: '#ffc9c9', 'stroke-dasharray': '3 3' }, svg);
        el('circle', { cx: x1, cy: y1, r: 4, fill: C.fal }, svg); el('circle', { cx: x2, cy: y2, r: 4, fill: C.fal }, svg);
      });
      txt(svg, 330, 60, 'D', { 'font-size': 20, fill: C.fal, 'font-weight': 800 });
      cap('D = fixed points: countable', 'D = 不动点集：可数');
    } else if (k === 3 || k === 4) {
      [72, 210, 348].forEach(cx => miniTree(svg, cx, 115, 38, 3, k === 4));
      txt2(svg, 210, 210, k === 3 ? '★ = M: one point from each orbit (AC)' : 'A_x = W(x)·M', k === 3 ? '★ = M：每条轨道取一点（AC）' : '按首字母着色：A_x = W(x)·M', 13, { fill: k === 3 ? C.gold : C.ink, 'font-weight': 700 });
      cap(k === 3 ? 'each orbit is a copy of the Cayley tree' : 'S²∖D = M ⊔ A_ρ ⊔ A_ρ⁻¹ ⊔ A_σ ⊔ A_σ⁻¹', k === 3 ? '每条轨道都是凯莱树的一个副本' : '同一个悖论分解，搬到了每条轨道上');
    } else if (k === 5) {
      sphere(svg, 210, 125, 95);
      const pts = [[150, 80], [175, 62], [205, 52], [236, 55], [263, 68]];
      pts.forEach(([x, y], i) => { el('circle', { cx: x, cy: y, r: 5, fill: i ? '#ffa8a8' : C.fal }, svg); if (i) txt(svg, x, y - 9, `τ${i > 1 ? sup(i) : ''}D`, { 'text-anchor': 'middle', 'font-size': 10, fill: C.fal }); });
      txt(svg, 132, 84, 'D', { 'font-size': 13, fill: C.fal, 'font-weight': 800 });
      el('path', { d: 'M 150 100 Q 210 80 265 92', fill: 'none', stroke: C.meta, 'stroke-width': 2 }, svg);
      cap('S² ∼ S² ∖ D: shift E = D ∪ τD ∪ τ²D ∪ ⋯ by τ', 'S² ∼ S² ∖ D：用 τ 把 E 整体推一格');
    } else {
      el('circle', { cx: 90, cy: 125, r: 70, fill: '#dbe4ff', stroke: C.accent, 'stroke-width': 2 }, svg);
      txt(svg, 90, 130, 'B', { 'text-anchor': 'middle', 'font-size': 22, 'font-weight': 800, fill: C.accent });
      txt(svg, 190, 132, '⟹', { 'text-anchor': 'middle', 'font-size': 30, fill: C.meta });
      el('circle', { cx: 280, cy: 85, r: 52, fill: '#ffe8cc', stroke: C.gold, 'stroke-width': 2 }, svg);
      el('circle', { cx: 345, cy: 175, r: 52, fill: '#d3f9d8', stroke: C.tru, 'stroke-width': 2 }, svg);
      txt(svg, 280, 91, 'B', { 'text-anchor': 'middle', 'font-size': 18, 'font-weight': 800 });
      txt(svg, 345, 181, 'B', { 'text-anchor': 'middle', 'font-size': 18, 'font-weight': 800 });
      cap('radial extension: B ∼ B ⊔ B', '沿半径延拓：B ∼ B ⊔ B');
    }
  }
  const sup = n => '⁰¹²³⁴⁵⁶⁷⁸⁹'[n];
  Stepper($('btSteps'), [
    P('<b>Free group.</b> G = ⟨ρ, σ⟩ ⊂ SO(3) is free on ρ, σ (ingredient 1 above), so it carries the paradoxical decomposition of §7.', '<b>自由群.</b> G = ⟨ρ, σ⟩ ⊂ SO(3) 是由 ρ, σ 生成的自由群（上面的要素一），因此带有 §7 的悖论分解。'),
    P('<b>Remove fixed points.</b> Each g ≠ id in G fixes exactly 2 antipodal points of S². G is countable, so the set D of all such points is countable. G maps S² ∖ D to itself, and on it no g ≠ id has a fixed point: the action is <b>free</b>.',
      '<b>去掉不动点.</b> G 中每个 g ≠ id 在 S² 上恰有 2 个（对径的）不动点。G 可数，所以所有这样的点构成的集合 D 可数。G 把 S² ∖ D 映到自身，并且在其上任何 g ≠ id 都没有不动点：作用是<b>自由的</b>。'),
    P('<b>Choose orbit representatives (AC).</b> S² ∖ D splits into G-orbits. By AC choose M containing exactly one point of each orbit. Freeness means every x ∈ S² ∖ D is g·m for a <b>unique</b> g ∈ G and m ∈ M, so each orbit is a copy of the Cayley tree.',
      '<b>选轨道代表元（AC）.</b> S² ∖ D 分解为若干 G-轨道。由 AC 取 M，使它恰好含每条轨道中的一个点。作用自由意味着每个 x ∈ S² ∖ D 都能<b>唯一地</b>写成 g·m（g ∈ G，m ∈ M），所以每条轨道都是凯莱树的一个副本。'),
    P('<b>Transfer the paradox.</b> Put A<sub>x</sub> = W(x)·M for x ∈ {ρ, ρ⁻¹, σ, σ⁻¹}. Then S²∖D = M ⊔ A<sub>ρ</sub> ⊔ A<sub>ρ⁻¹</sub> ⊔ A<sub>σ</sub> ⊔ A<sub>σ⁻¹</sub>, while S²∖D = A<sub>ρ</sub> ⊔ ρA<sub>ρ⁻¹</sub> = A<sub>σ</sub> ⊔ σA<sub>σ⁻¹</sub>. Four pieces, rotated, make <b>two</b> copies of S² ∖ D.',
      '<b>搬运悖论.</b> 对 x ∈ {ρ, ρ⁻¹, σ, σ⁻¹} 令 A<sub>x</sub> = W(x)·M。则 S²∖D = M ⊔ A<sub>ρ</sub> ⊔ A<sub>ρ⁻¹</sub> ⊔ A<sub>σ</sub> ⊔ A<sub>σ⁻¹</sub>，同时 S²∖D = A<sub>ρ</sub> ⊔ ρA<sub>ρ⁻¹</sub> = A<sub>σ</sub> ⊔ σA<sub>σ⁻¹</sub>。四块经旋转拼成<b>两份</b> S² ∖ D。'),
    P('<b>Absorb D.</b> Choose a rotation τ about an axis missing D such that the sets τⁿD (n ≥ 0) are pairwise disjoint; only countably many angles fail. With E = ⋃ₙ τⁿD we get S² = (S²∖E) ⊔ E and S²∖D = (S²∖E) ⊔ τE. So S² is equidecomposable with S² ∖ D, and S² is paradoxical too.',
      '<b>吸收 D.</b> 取一个旋转轴避开 D 的旋转 τ，使 τⁿD（n ≥ 0）两两不交；不满足条件的角度只有可数多个。令 E = ⋃ₙ τⁿD，则 S² = (S²∖E) ⊔ E，S²∖D = (S²∖E) ⊔ τE。所以 S² 与 S² ∖ D 可等度分解，S² 也是悖论集。'),
    P('<b>To the ball.</b> Replace each x ∈ S² by its radius {tx : 0 &lt; t ≤ 1}. This makes B ∖ {0} paradoxical. The centre is absorbed by the same trick, using a rotation about an axis that does not pass through 0. Hence B is equidecomposable with two disjoint copies of B. ∎',
      '<b>推广到实心球.</b> 把每个 x ∈ S² 换成半径 {tx : 0 &lt; t ≤ 1}，得 B ∖ {0} 是悖论集。球心用同样的技巧吸收掉，只需绕一条不过原点的轴旋转。于是 B 与两个不交的 B 可等度分解。∎'),
  ], { onStep: draw });
})();

/* ================= §9 weak forms ================= */
(function weakForms() {
  const svg = $('wkSvg');
  const N = {
    AC: { x: 430, y: 40, en: 'AC', zh: '选择公理',
      i: P('<b>Axiom of Choice.</b> Every family of nonempty sets has a choice function. Equivalent over ZF: Zorn, well-ordering, Tychonoff’s theorem (Kelley 1950), “every vector space has a basis” (Blass 1984), “every ring with 1 has a maximal ideal” (Hodges 1979), comparability of any two cardinals (Hartogs 1915).',
        '<b>选择公理.</b> 每个非空集合族都有选择函数。在 ZF 上与之等价的有：佐恩引理、良序定理、吉洪诺夫定理（凯莱，1950）、“每个向量空间都有基”（布拉斯，1984）、“每个含幺环都有极大理想”（霍奇斯，1979）、任意两个基数可比较（哈托格斯，1915）。') },
    DC: { x: 230, y: 135, en: 'DC: dependent choice', zh: '依赖选择公理',
      i: P('<b>Dependent choice.</b> If R is a relation on a nonempty set X with ∀x ∃y (x R y), then there is a sequence x₀ R x₁ R x₂ R ⋯. This is exactly what step-by-step constructions in analysis need, and it is equivalent to the Baire category theorem for complete metric spaces. <b>Fails to give</b> a Vitali set: Solovay’s model satisfies ZF + DC + “every set of reals is Lebesgue measurable”.',
        '<b>依赖选择公理.</b> 若 R 是非空集合 X 上的关系，且 ∀x ∃y (x R y)，则存在序列 x₀ R x₁ R x₂ R ⋯。分析中“一步接一步”的构造需要的正是它；它等价于完备度量空间的贝尔纲定理。它<b>推不出</b>维塔利集：索洛维模型满足 ZF + DC +“每个实数集都勒贝格可测”。') },
    BPI: { x: 640, y: 135, en: 'BPI = ultrafilter lemma', zh: '布尔素理想定理 = 超滤子引理',
      i: P('<b>Boolean prime ideal theorem</b>, equivalently the ultrafilter lemma (§5). Equivalent to the compactness theorem of first-order logic, and to Tychonoff for compact Hausdorff spaces. Strictly weaker than AC (Halpern–Lévy 1971), and independent of DC in both directions.',
        '<b>布尔素理想定理</b>，等价于超滤子引理（§5）。它等价于一阶逻辑的紧致性定理，也等价于紧豪斯多夫空间的吉洪诺夫定理。严格弱于 AC（哈尔彭–莱维，1971），且与 DC 互不蕴涵。') },
    ACw: { x: 230, y: 235, en: 'ACω: countable choice', zh: '可数选择公理',
      i: P('<b>Countable choice.</b> Every countable family of nonempty sets has a choice function. It gives: countable unions of countable sets are countable; every infinite set has a countably infinite subset; sequential continuity equals ε–δ continuity for f : ℝ → ℝ; Lebesgue measure is countably additive.',
        '<b>可数选择公理.</b> 每个可数非空集合族都有选择函数。由它可得：可数个可数集之并可数；每个无穷集都有可数无穷子集；对 f : ℝ → ℝ，序列连续等价于 ε–δ 连续；勒贝格测度可数可加。') },
    HB: { x: 530, y: 235, en: 'Hahn–Banach', zh: '哈恩–巴拿赫定理',
      i: P('<b>Hahn–Banach theorem.</b> A bounded linear functional on a subspace extends to the whole normed space with the same norm. It follows from BPI (Łoś–Ryll-Nardzewski, Luxemburg) and is strictly weaker.',
        '<b>哈恩–巴拿赫定理.</b> 子空间上的有界线性泛函可以保范延拓到整个赋范空间。它可由 BPI 推出（沃希–雷尔-纳尔杰夫斯基、卢森堡），且严格更弱。') },
    NM: { x: 750, y: 235, en: 'a non-measurable set', zh: '存在不可测集',
      i: P('<b>There is a non-Lebesgue-measurable set of reals.</b> It follows from BPI: a non-principal ultrafilter on ℕ, viewed as a set of 0/1 sequences, is not measurable (Sierpiński). It fails in Solovay’s model.',
        '<b>存在勒贝格不可测的实数集.</b> 它可由 BPI 推出：把 ℕ 上的非主超滤子看成 0/1 序列的集合，它是不可测的（谢尔宾斯基）。在索洛维模型中它不成立。') },
    CUCC: { x: 120, y: 335, en: '⋃ of ℵ₀ ctbl sets is ctbl', zh: '可数个可数集之并可数',
      i: P('<b>A countable union of countable sets is countable.</b> The proof must choose an enumeration of each of the countably many sets, which uses ACω. It fails in the Feferman–Lévy model, where ℝ itself is a countable union of countable sets.',
        '<b>可数个可数集之并可数.</b> 证明中要为可数多个集合各选一个枚举，这要用 ACω。在费弗曼–莱维模型中它不成立：那里 ℝ 本身就是可数个可数集之并。') },
    DI: { x: 360, y: 335, en: 'infinite ⇒ ⊇ copy of ℕ', zh: '无穷集含可数无穷子集',
      i: P('<b>Every infinite set has a countably infinite subset</b> (it is Dedekind-infinite). It follows from ACω. It fails in Cohen’s first model, which contains an infinite set of reals with no countably infinite subset.',
        '<b>每个无穷集都含有可数无穷子集</b>（即是戴德金无穷的）。它可由 ACω 推出。在科恩的第一个模型中它不成立：那里有一个无穷实数集，没有可数无穷子集。') },
    ZF: { x: 700, y: 335, en: 'ZF alone', zh: '仅用 ZF',
      i: P('<b>No choice needed:</b> Cantor’s theorem, uncountability of ℝ, Schröder–Bernstein, transfinite recursion, Hartogs’ theorem and the existence of ω₁, well-ordering a countable set, choosing from finitely many sets.',
        '<b>无需选择公理：</b>康托尔定理、ℝ 不可数、施罗德–伯恩斯坦定理、超限递归、哈托格斯定理与 ω₁ 的存在、可数集的良序化、从有限个集合中选取。') },
  };
  const E = [['AC', 'DC'], ['AC', 'BPI'], ['DC', 'ACw'], ['ACw', 'CUCC'], ['ACw', 'DI'], ['BPI', 'HB'], ['BPI', 'NM']];
  const thms = [
    ['Every vector space has a basis', '每个向量空间都有基', 'AC', 'Equivalent to AC (Blass).', '与 AC 等价（布拉斯）。'],
    ['Tychonoff’s theorem', '吉洪诺夫定理', 'AC', 'Equivalent to AC (Kelley).', '与 AC 等价（凯莱）。'],
    ['Every ring with 1 has a maximal ideal', '含幺环必有极大理想', 'AC', 'Equivalent to AC (Hodges).', '与 AC 等价（霍奇斯）。'],
    ['Construct a Vitali set (§6)', '构造维塔利集（§6）', 'AC', 'The proof in §6 uses AC; DC is not enough (Solovay’s model).', '§6 的证明用了 AC；DC 不够（索洛维模型）。'],
    ['Compactness theorem (first-order logic)', '一阶逻辑紧致性定理', 'BPI', 'Equivalent to BPI.', '与 BPI 等价。'],
    ['Every field has an algebraic closure', '每个域都有代数闭包', 'BPI', 'BPI suffices.', 'BPI 就够了。'],
    ['Every set can be linearly ordered', '每个集合都可线性排序', 'BPI', 'BPI suffices; strictly weaker than BPI.', 'BPI 就够了；它比 BPI 严格更弱。'],
    ['Baire category theorem', '贝尔纲定理', 'DC', 'Equivalent to DC.', '与 DC 等价。'],
    ['ℝ is not a countable union of countable sets', 'ℝ 不是可数个可数集之并', 'ACw', 'ACω suffices; fails in the Feferman–Lévy model.', 'ACω 就够了；在费弗曼–莱维模型中不成立。'],
    ['Lebesgue measure is countably additive', '勒贝格测度可数可加', 'ACw', 'ACω suffices.', 'ACω 就够了。'],
    ['Cantor: |X| &lt; |𝒫(X)|', '康托尔：|X| &lt; |𝒫(X)|', 'ZF', 'Pure ZF: the diagonal set needs no choice.', '纯 ZF：对角线集合不需要任何选择。'],
    ['ℝ is uncountable', 'ℝ 不可数', 'ZF', 'Pure ZF (Cantor’s diagonal or nested intervals).', '纯 ZF（康托尔对角线或区间套）。'],
  ];
  let lit = null;
  const NW = 210, NH = 46;
  function draw() {
    svg.innerHTML = '';
    E.forEach(([a, b]) => {
      const A = N[a], B = N[b];
      const y1 = A.y + NH / 2, y2 = B.y - NH / 2;
      el('line', { x1: A.x, y1, x2: B.x, y2: y2 - 9, stroke: '#8a8f99', 'stroke-width': 2 }, svg);
      let dx = B.x - A.x, dy = y2 - y1; const l = Math.hypot(dx, dy); dx /= l; dy /= l;
      const bx = B.x - dx * 11, by = y2 - dy * 11;
      el('polygon', { points: `${B.x},${y2} ${bx - dy * 6},${by + dx * 6} ${bx + dy * 6},${by - dx * 6}`, fill: '#8a8f99' }, svg);
    });
    Object.entries(N).forEach(([k, n]) => {
      const g = el('g', { class: 'clk' }, svg);
      const on = lit === k;
      el('rect', { x: n.x - NW / 2, y: n.y - NH / 2, width: NW, height: NH, rx: 10,
        fill: on ? C.metaSoft : k === 'AC' ? '#fff4e6' : k === 'ZF' ? '#f1f3f5' : '#fff',
        stroke: on ? C.meta : k === 'ZF' ? '#adb5bd' : C.ink, 'stroke-width': on ? 3.5 : 1.5, 'stroke-dasharray': k === 'ZF' ? '5 4' : '' }, g);
      txt2(g, n.x, n.y + 1, n.en, n.zh, 13, { 'font-weight': 700 });
      g.addEventListener('click', () => { lit = k; draw(); $('wkInfo').innerHTML = n.i; chipsOff(); });
    });
  }
  const chipsBox = $('wkChips');
  const chipsOff = () => chipsBox.querySelectorAll('.chip').forEach(c => c.classList.remove('lit'));
  thms.forEach(([en, zh, node, wen, wzh]) => {
    const c = document.createElement('div');
    c.className = 'chip';
    c.innerHTML = bil(en, zh);
    c.addEventListener('click', () => {
      lit = node; draw(); chipsOff(); c.classList.add('lit');
      $('wkInfo').innerHTML = `<p><b>${bil(en, zh)}</b> → <b style="color:${C.meta}">${bil(N[node].en, N[node].zh)}</b>. ${bi(wen, wzh)}</p>` + N[node].i;
    });
    chipsBox.appendChild(c);
  });
  draw();
  $('wkInfo').innerHTML = bi('Click a box or a theorem chip.', '点击方框或定理标签。');

  // timeline
  const tl = $('tlSvg');
  const ev = [
    [1904, 'Zermelo', '策梅洛', 'Zermelo proves the well-ordering theorem from AC, making AC explicit for the first time and causing an uproar.', '策梅洛由 AC 证明良序定理，第一次明确提出选择公理，引起轩然大波。'],
    [1908, 'Zermelo axioms', '策梅洛公理', 'Zermelo’s axiomatization of set theory, with AC among the axioms.', '策梅洛给出集合论公理化系统，AC 是其中一条公理。'],
    [1922, 'Fraenkel', '弗兰克尔', 'Fraenkel’s permutation models: AC is independent of set theory <i>with atoms</i>. That was the first independence proof, though not yet for ZF.', '弗兰克尔的置换模型：AC 独立于<i>带原子的</i>集合论。这是最早的独立性证明，但还不是针对 ZF 的。'],
    [1924, 'Banach–Tarski', '巴拿赫–塔斯基', 'Banach and Tarski publish the paradoxical decomposition of the ball (§8).', '巴拿赫与塔斯基发表实心球的悖论分解（§8）。'],
    [1938, 'Gödel: L', '哥德尔：L', 'Gödel builds the constructible universe L, in which AC (and GCH) holds. So Con(ZF) ⇒ Con(ZFC): AC cannot be <b>refuted</b> in ZF. → Lesson 15.', '哥德尔构造可构成宇宙 L，在其中 AC（以及 GCH）成立。于是 Con(ZF) ⇒ Con(ZFC)：ZF <b>否证</b>不了 AC。→ 第 15 课。'],
    [1963, 'Cohen: forcing', '科恩：力迫法', 'Cohen invents forcing and builds a model of ZF + ¬AC. So Con(ZF) ⇒ Con(ZF + ¬AC): AC cannot be <b>proved</b> in ZF. → Lesson 16.', '科恩发明力迫法，构造出 ZF + ¬AC 的模型。于是 Con(ZF) ⇒ Con(ZF + ¬AC)：ZF <b>证明</b>不了 AC。→ 第 16 课。'],
    [1970, 'Solovay', '索洛维', 'Solovay: from an inaccessible cardinal, a model of ZF + DC in which every set of reals is Lebesgue measurable. Analysis without Vitali sets.', '索洛维：从不可达基数出发，得到 ZF + DC 的一个模型，其中每个实数集都勒贝格可测。这是没有维塔利集的分析学。'],
  ];
  
  el('line', { x1: 30, y1: 64, x2: 840, y2: 64, stroke: '#c9c4b6', 'stroke-width': 3 }, tl);
  ev.forEach(([y, en, zh, ien, izh], i) => {
    const x = 70 + i * 120;
    const g = el('g', { class: 'tline-dot clk' }, tl);
    el('circle', { cx: x, cy: 64, r: 9, fill: y === 1938 || y === 1963 ? C.meta : C.accent, stroke: '#fff', 'stroke-width': 2 }, g);
    txt(g, x, 98, String(y), { 'text-anchor': 'middle', 'font-size': 12, 'font-weight': 700 });
    const up = i % 2 === 0;
    txt(g, x, up ? 22 : 42, `${en} · ${zh}`, { 'text-anchor': 'middle', 'font-size': 11, fill: C.muted });
    el('line', { x1: x, y1: up ? 26 : 46, x2: x, y2: 54, stroke: '#ddd' }, g);
    g.addEventListener('click', () => okBox($('tlMsg'), `<b>${y}</b> · ` + bi(ien, izh), 'info'));
  });
  okBox($('tlMsg'), bi('Click a dot.', '点击圆点。'), 'info');
})();

/* ================= E1 ================= */
(function e1() {
  const cards = [
    { en: 'Choose an element from each of 5 nonempty sets', zh: '从 5 个非空集合中各取一个元素', a: 'ZF', wen: 'Finite choice: induction on n.', wzh: '有限次选择：对 n 归纳。' },
    { en: 'Choose an element from each nonempty subset of ℕ', zh: '从 ℕ 的每个非空子集中各取一个元素', a: 'ZF', wen: 'Rule: take the least element.', wzh: '规则：取最小元。' },
    { en: 'Choose a point from each nonempty open subset of ℝ', zh: '从 ℝ 的每个非空开集中各取一点', a: 'ZF', wen: 'Fix an enumeration of ℚ and take the first rational in the set.', wzh: '固定 ℚ 的一个枚举，取集合中排在最前的有理数。' },
    { en: 'One shoe from each of infinitely many pairs', zh: '从无穷多双鞋中各取一只', a: 'ZF', wen: 'Rule: the left shoe.', wzh: '规则：取左脚。' },
    { en: 'A right inverse for a surjection ℕ ↠ X', zh: '满射 ℕ ↠ X 的右逆', a: 'ZF', wen: 'g(x) = the least n with f(n) = x.', wzh: 'g(x) = 满足 f(n) = x 的最小 n。' },
    { en: 'A well-ordering of ℚ', zh: 'ℚ 的一个良序', a: 'ZF', wen: 'ℚ is countable: pull back the order of ℕ along an explicit bijection.', wzh: 'ℚ 可数：沿一个具体的双射把 ℕ 的序拉回来。' },
    { en: 'One sock from each of infinitely many pairs', zh: '从无穷多双袜子中各取一只', a: 'AC', wen: 'No rule distinguishes the socks; even countable choice for pairs is unprovable in ZF.', wzh: '没有规则能区分两只袜子；即使只对可数个二元集做选择，ZF 也证明不了。' },
    { en: 'Choose an element from each nonempty subset of ℝ', zh: '从 ℝ 的每个非空子集中各取一个元素', a: 'AC', wen: 'This is AC for 𝒫(ℝ), equivalent to well-ordering ℝ.', wzh: '这就是 𝒫(ℝ) 上的 AC，等价于把 ℝ 良序化。' },
    { en: 'A countable union of countable sets is countable', zh: '可数个可数集之并可数', a: 'AC', wen: 'Needs ACω to choose the enumerations; fails in the Feferman–Lévy model.', wzh: '需要 ACω 来选取各个枚举；在费弗曼–莱维模型中不成立。' },
    { en: 'A Vitali set exists', zh: '维塔利集存在', a: 'AC', wen: 'Fails in Solovay’s model.', wzh: '在索洛维模型中不成立。' },
    { en: 'Every vector space has a basis', zh: '每个向量空间都有基', a: 'AC', wen: 'Equivalent to AC (Blass).', wzh: '与 AC 等价（布拉斯）。' },
    { en: 'A well-ordering of ℝ', zh: 'ℝ 的一个良序', a: 'AC', wen: 'Not provable in ZF (Cohen). Feferman showed that even ZFC does not prove the existence of a <i>definable</i> well-order of ℝ.', wzh: 'ZF 中不可证（科恩）。费弗曼还证明了：即使在 ZFC 中，也证明不了存在 ℝ 的<i>可定义</i>良序。' },
    { en: 'Cantor’s theorem |X| &lt; |𝒫(X)|', zh: '康托尔定理 |X| &lt; |𝒫(X)|', a: 'ZF', wen: 'The diagonal set {x : x ∉ f(x)} is defined explicitly.', wzh: '对角线集 {x : x ∉ f(x)} 是显式定义的。' },
  ];
  const order = shuffle(cards.map((_, i) => i));
  const pos = cards.map(() => 'tray');
  const cycle = ['tray', 'ZF', 'AC'];
  const els = [];
  let revealed = false;
  function render() {
    ['e1Tray', 'e1ZF', 'e1AC'].forEach(id => { $(id).innerHTML = ''; });
    order.forEach(i => {
      const c = cards[i];
      const d = document.createElement('div');
      d.className = 'chip';
      d.innerHTML = bi(c.en, c.zh);
      d.addEventListener('click', () => { pos[i] = cycle[(cycle.indexOf(pos[i]) + 1) % 3]; render(); clearBox($('e1Msg')); });
      els[i] = d;
      $({ tray: 'e1Tray', ZF: 'e1ZF', AC: 'e1AC' }[pos[i]]).appendChild(d);
    });
  }
  function why() {
    $('e1Why').innerHTML = '<ul>' + cards.map(c => `<li>${bil(c.en, c.zh)} → <b>${c.a === 'ZF' ? 'ZF' : bil('choice', '选择')}</b>: ${bil(c.wen, c.wzh)}</li>`).join('') + '</ul>';
  }
  render();
  $('e1Check').addEventListener('click', () => {
    let right = 0, placed = 0;
    cards.forEach((c, i) => {
      els[i].classList.remove('ok', 'no');
      if (pos[i] === 'tray') return;
      placed++;
      if (pos[i] === c.a) { right++; els[i].classList.add('ok'); } else els[i].classList.add('no');
    });
    if (right === cards.length) {
      okBox($('e1Msg'), bi('✓ All correct. The pattern: choice is needed exactly when there is no definable rule.', '✓ 全对。规律是：恰在没有可定义规则的时候，才需要选择公理。'));
      why();
      if (!revealed) Progress.mark('L10E1');
    } else okBox($('e1Msg'), bi(`${right} / ${cards.length} correct${placed < cards.length ? ' (some cards are still in the tray)' : ''}. Red cards are misplaced. Look for a rule such as “least”, “left”, or “first in a fixed enumeration”.`,
      `答对 ${right} / ${cards.length}${placed < cards.length ? '（还有卡片没分类）' : ''}。红色卡片放错了。找找看有没有“最小的”“左边的”“固定枚举中第一个”这类规则。`), 'warn');
  });
  $('e1Show').addEventListener('click', () => {
    revealed = true;
    cards.forEach((c, i) => { pos[i] = c.a; });
    render();
    cards.forEach((c, i) => els[i].classList.add('ok'));
    okBox($('e1Msg'), bi('Answer shown, with reasons below.', '答案已显示，理由见下。'), 'info');
    why();
  });
})();

/* ================= E2 ================= */
(function e2() {
  const steps = [
    P('Let P be the set of linearly independent subsets of V, ordered by ⊆.', '令 P 为 V 的线性无关子集全体，按 ⊆ 排序。'),
    P('P ≠ ∅, because ∅ is linearly independent.', 'P ≠ ∅，因为 ∅ 线性无关。'),
    P('Let 𝒞 be a chain in P and put U = ⋃𝒞.', '设 𝒞 是 P 中的链，令 U = ⋃𝒞。'),
    P('Any finitely many vectors of U lie in a single member of 𝒞, so U is independent: an upper bound of 𝒞.', 'U 中任意有限个向量都落在 𝒞 的同一个成员里，所以 U 线性无关，是 𝒞 的上界。'),
    P('By Zorn’s lemma, P has a maximal element B.', '由佐恩引理，P 有极大元 B。'),
    P('If v ∉ span(B), then B ∪ {v} ∈ P is strictly bigger, which contradicts maximality. So B spans V: a basis.', '若 v ∉ span(B)，则 B ∪ {v} ∈ P 严格更大，与极大性矛盾。所以 B 张成 V，是一组基。'),
  ];
  let pool = shuffle(steps.map((_, i) => i)), seq = [], revealed = false;
  function render(mark) {
    $('e2Pool').innerHTML = ''; $('e2Seq').innerHTML = '';
    pool.forEach(i => {
      const d = document.createElement('div');
      d.className = 'chip';
      d.innerHTML = steps[i];
      d.addEventListener('click', () => { pool = pool.filter(x => x !== i); seq.push(i); render(); clearBox($('e2Msg')); });
      $('e2Pool').appendChild(d);
    });
    seq.forEach((i, k) => {
      const d = document.createElement('div');
      d.className = 'chip' + (mark ? (i === k ? ' ok' : ' no') : '');
      d.innerHTML = `<b class="num">${k + 1}.</b> ${steps[i]}`;
      d.addEventListener('click', () => { seq = seq.filter(x => x !== i); pool.push(i); render(); clearBox($('e2Msg')); });
      $('e2Seq').appendChild(d);
    });
  }
  render();
  $('e2Check').addEventListener('click', () => {
    if (seq.length < steps.length) { okBox($('e2Msg'), bi(`Place all ${steps.length} cards first.`, `请先把 ${steps.length} 张卡片全部排好。`), 'warn'); return; }
    render(true);
    if (seq.every((i, k) => i === k)) {
      okBox($('e2Msg'), bi('✓ That is the standard Zorn template: define P, check P ≠ ∅, bound chains, take a maximal element, and show that maximal means what you want.', '✓ 这正是佐恩引理的标准模板：定义 P，验证 P ≠ ∅，给链找上界，取极大元，再证明“极大”恰好就是你想要的性质。'));
      if (!revealed) Progress.mark('L10E2');
    } else okBox($('e2Msg'), bi('Not yet: red cards are out of place. A Zorn proof always runs: set up the poset → nonempty → chains bounded → maximal element → maximal means done.', '还不对：红色卡片位置错了。佐恩论证的顺序总是：设偏序集 → 非空 → 链有上界 → 取极大元 → 极大即所求。'), 'bad');
  });
  $('e2Show').addEventListener('click', () => {
    revealed = true;
    seq = steps.map((_, i) => i); pool = [];
    render(true);
    okBox($('e2Msg'), bi('Answer shown.', '答案已显示。'), 'info');
  });
})();

/* ================= E3 ================= */
(function e3() {
  const targets = ['b', '', 'A', 'Ba', 'ab'];
  const answers = ['Ab', 'A', 'AA', 'ABa', null];
  const solved = targets.map(() => false);
  let last = null, revealed = false;
  const list = $('e3List');
  const keys = document.createElement('div');
  keys.className = 'toolbar';
  [['a', 'a'], ['A', 'a⁻¹'], ['b', 'b'], ['B', 'b⁻¹'], ['⌫', '⌫']].forEach(([c, s]) => {
    const b = document.createElement('button');
    b.className = 'btn kbd small';
    b.textContent = s;
    b.addEventListener('click', () => {
      if (!last) last = list.querySelector('input');
      last.value = c === '⌫' ? last.value.slice(0, -1) : last.value + c;
      last.dispatchEvent(new Event('input'));
      last.focus();
    });
    keys.appendChild(b);
  });
  list.appendChild(keys);
  const parseW = s => s.replace(/a\^-1|a⁻¹/g, 'A').replace(/b\^-1|b⁻¹/g, 'B').replace(/[^aAbB]/g, '');
  const finish = () => { if (!revealed && solved.every(Boolean)) { Progress.mark('L10E3'); okBox($('e3Msg'), bi('✓ All five. You have checked a·W(a⁻¹) = F₂ ∖ W(a) on examples, including the one element it must miss.', '✓ 五题全对。你已在例子上验证了 a·W(a⁻¹) = F₂ ∖ W(a)，也包括它必然漏掉的那一种。')); } };
  const rows = targets.map((u, i) => {
    const row = document.createElement('div');
    row.className = 'tf';
    row.innerHTML = `<div class="stmt">u = ${fmtWord(u)} <span style="color:${PIECE_COL[u[0] || '']}">∈ ${pieceName(u)}</span></div>
      <input class="formula" style="min-width:140px;width:160px" placeholder="w = …">
      <button class="btn small">${bil('No such w', '不存在这样的 w')}</button>
      <div style="flex-basis:100%"><div class="msg"></div></div>`;
    list.appendChild(row);
    const inp = row.querySelector('input'), msg = row.querySelector('.msg'), no = row.querySelector('button');
    inp.addEventListener('focus', () => { last = inp; });
    inp.addEventListener('input', () => {
      const raw = parseW(inp.value);
      if (!raw) { clearBox(msg); return; }
      const w = reduceWord(raw), aw = reduceWord('a' + w);
      const inA = w[0] === 'A', hit = aw === u;
      const head = `<span class="m">${raw !== w ? bil(`reduces to w = ${fmtWord(w)}`, `约简为 w = ${fmtWord(w)}`) : 'w = ' + fmtWord(w)} · w ∈ ${pieceName(w)} · a·w = ${fmtWord(aw)}</span><br>`;
      if (inA && hit) {
        okBox(msg, head + bi('✓ w ∈ W(a⁻¹) and a·w = u.', '✓ w ∈ W(a⁻¹) 且 a·w = u。'));
        solved[i] = true; finish();
      } else if (!inA) okBox(msg, head + bi('✗ w must start with a⁻¹.', '✗ w 必须以 a⁻¹ 开头。'), 'bad');
      else okBox(msg, head + bi('✗ a·w ≠ u. Hint: try w = a⁻¹·u.', '✗ a·w ≠ u。提示：试试 w = a⁻¹·u。'), 'bad');
    });
    no.addEventListener('click', () => {
      if (answers[i] === null) {
        okBox(msg, bi('✓ Right: u ∈ W(a), and a·W(a⁻¹) never meets W(a). The only w with a·w = ab is w = b, which does not start with a⁻¹.', '✓ 对：u ∈ W(a)，而 a·W(a⁻¹) 与 W(a) 不相交。满足 a·w = ab 的唯一 w 是 b，它不以 a⁻¹ 开头。'));
        solved[i] = true; finish();
      } else okBox(msg, bi(`✗ There is one: u ∉ W(a), so a⁻¹·u starts with a⁻¹.`, `✗ 存在：u ∉ W(a)，所以 a⁻¹·u 以 a⁻¹ 开头。`), 'bad');
    });
    return { inp, msg };
  });
  $('e3Show').addEventListener('click', () => {
    revealed = true;
    rows.forEach((r, i) => {
      if (answers[i] === null) { r.inp.value = ''; okBox(r.msg, bi('No such w: u = ab ∈ W(a), and a·W(a⁻¹) ∩ W(a) = ∅.', '不存在：u = ab ∈ W(a)，而 a·W(a⁻¹) ∩ W(a) = ∅。'), 'info'); }
      else { r.inp.value = answers[i]; okBox(r.msg, `<span class="m">w = a⁻¹·u = ${fmtWord(answers[i])}, a·w = ${fmtWord(targets[i])}</span>`, 'info'); }
    });
    okBox($('e3Msg'), bi('Answers shown. The recipe: w = a⁻¹u, which starts with a⁻¹ exactly when u does not start with a.', '答案已显示。做法：w = a⁻¹u；它以 a⁻¹ 开头，当且仅当 u 不以 a 开头。'), 'info');
  });
})();

/* ================= E4 ================= */
(function e4() {
  const items = [
    { en: '(a) Two distinct points of V differ by an irrational number.', zh: '(a) V 中两个不同的点之差是无理数。', ans: true,
      wen: 'True: if v − v′ ∈ ℚ they would be in the same class, and V has only one point per class.', wzh: '对：若 v − v′ ∈ ℚ，它们就在同一个等价类中，而 V 在每类中只有一个点。' },
    { en: '(b) V could be Lebesgue measurable with measure 0.', zh: '(b) V 可能是测度为 0 的勒贝格可测集。', ans: false,
      wen: 'False: then 𝕋 = ⨆<sub>q</sub>(V+q) would have measure Σ0 = 0, not 1.', wzh: '错：那样 𝕋 = ⨆<sub>q</sub>(V+q) 的测度就是 Σ0 = 0，而不是 1。' },
    { en: '(c) V is uncountable.', zh: '(c) V 不可数。', ans: true,
      wen: 'True: 𝕋 = ⋃<sub>q</sub>(V + q) is a countable union of copies of V. If V were countable, 𝕋 would be countable.', wzh: '对：𝕋 = ⋃<sub>q</sub>(V + q) 是可数个 V 的副本之并。若 V 可数，𝕋 也就可数了。' },
    { en: '(d) The same argument rules out every <i>finitely</i> additive rotation-invariant measure on all subsets of 𝕋 with μ(𝕋) = 1.', zh: '(d) 同样的论证也排除了 𝕋 的全体子集上一切<i>有限</i>可加、旋转不变且 μ(𝕋) = 1 的测度。', ans: false,
      wen: 'False: the argument needs <b>countable</b> additivity. Banach showed that finitely additive invariant measures on all subsets of 𝕋 (and of ℝ, ℝ²) do exist. In ℝ³ Banach–Tarski kills them.', wzh: '错：论证要用<b>可数</b>可加性。巴拿赫证明了 𝕋（以及 ℝ、ℝ²）的全体子集上确实存在有限可加的不变测度。到了 ℝ³，巴拿赫–塔斯基悖论才把它们排除掉。' },
    { en: '(e) ZF alone proves that a Vitali set exists.', zh: '(e) 仅凭 ZF 就能证明维塔利集存在。', ans: false,
      wen: 'False (if ZF + “an inaccessible exists” is consistent): in Solovay’s model of ZF + DC every set of reals is measurable.', wzh: '错（假设 ZF +“存在不可达基数”相容）：在 ZF + DC 的索洛维模型中，每个实数集都可测。' },
  ];
  const solved = items.map(() => false), revealed = items.map(() => false);
  const box = $('e4List');
  items.forEach((it, i) => {
    const row = document.createElement('div');
    row.className = 'tf';
    row.innerHTML = `<div class="stmt" style="font-family:var(--sans);font-size:15px">${bi(it.en, it.zh)}</div>
      <button class="btn small" data-v="1">${bil('True', '对')}</button>
      <button class="btn small" data-v="0">${bil('False', '错')}</button>
      <button class="btn small ghost" data-v="show">${bil('Show answer', '看答案')}</button>
      <div style="flex-basis:100%"><div class="msg"></div></div>`;
    box.appendChild(row);
    row.querySelectorAll('button').forEach(b => b.addEventListener('click', () => {
      const msg = row.querySelector('.msg');
      if (b.dataset.v === 'show') { revealed[i] = true; okBox(msg, bi(it.wen, it.wzh), 'info'); return; }
      if ((b.dataset.v === '1') === it.ans) {
        okBox(msg, '✓ ' + bi(it.wen, it.wzh));
        if (!revealed[i]) solved[i] = true;
        if (solved.every(Boolean)) Progress.mark('L10E4');
      } else okBox(msg, bi('✗ Not quite. Revisit the picture in §6.', '✗ 不对。回到 §6 的图再看看。'), 'bad');
    }));
  });
})();

/* ================= E5 ================= */
(function e5() {
  const Pn = makePoset([
    { id: 'a', x: 190, y: 300 }, { id: 'b', x: 100, y: 225 }, { id: 'c', x: 280, y: 225 },
    { id: 'd', x: 50, y: 145 }, { id: 'e', x: 190, y: 145 }, { id: 'f', x: 330, y: 145 },
    { id: 'g', x: 110, y: 60 }, { id: 'h', x: 260, y: 60 },
  ], [['a', 'b'], ['a', 'c'], ['b', 'd'], ['b', 'e'], ['c', 'e'], ['c', 'f'], ['d', 'g'], ['e', 'g'], ['e', 'h']]);
  const S = ['b', 'e'];
  const wantMax = new Set(maximals(Pn)), wantUb = new Set(upperBounds(Pn, S));
  let A = new Set(), Bset = new Set(), mark = false, reveal = false, revealedEver = false;
  function render() {
    const sa = { sel: A, onClick: id => { A.has(id) ? A.delete(id) : A.add(id); mark = false; reveal = false; render(); } };
    const sb = { sel: Bset, ring: new Set(S), onClick: id => { Bset.has(id) ? Bset.delete(id) : Bset.add(id); mark = false; reveal = false; render(); } };
    if (mark) {
      sa.good = new Set([...A].filter(x => wantMax.has(x))); sa.wrong = new Set([...A].filter(x => !wantMax.has(x)));
      sb.good = new Set([...Bset].filter(x => wantUb.has(x))); sb.wrong = new Set([...Bset].filter(x => !wantUb.has(x)));
    }
    if (reveal) { sa.star = wantMax; sb.ub = wantUb; }
    drawHasse($('e5a'), Pn, sa);
    drawHasse($('e5b'), Pn, sb);
    txt($('e5a'), 10, 20, '(a) ★ ?', { 'font-size': 14, 'font-weight': 700, fill: C.muted });
    txt($('e5b'), 10, 20, '(b) S = {b, e}', { 'font-size': 14, 'font-weight': 700, fill: C.meta });
  }
  const same = (X, Y) => X.size === Y.size && [...X].every(x => Y.has(x));
  $('e5Check').addEventListener('click', () => {
    mark = true; reveal = false; render();
    const okA = same(A, wantMax), okB = same(Bset, wantUb);
    if (okA && okB) {
      okBox($('e5Msg'), bi('✓ Maximal: {f, g, h}. Upper bounds of {b, e}: {e, g, h}. Note that e itself counts, because an upper bound may belong to S.', '✓ 极大元：{f, g, h}。{b, e} 的上界：{e, g, h}。注意 e 本身也算，因为上界可以属于 S。'));
      if (!revealedEver) Progress.mark('L10E5');
    } else {
      const tips = [];
      if (!okA) tips.push(bi('(a) A maximal element has nothing above it. Look at the top of every branch, not just the highest row.', '(a) 极大元上方没有任何元素。看每一根分支的顶端，而不只是最高的那一行。'));
      if (!okB) tips.push(bi('(b) u is an upper bound iff b ≤ u and e ≤ u. Can u be in S itself?', '(b) u 是上界当且仅当 b ≤ u 且 e ≤ u。u 能不能就在 S 里？'));
      okBox($('e5Msg'), tips.join('<br>'), 'bad');
    }
  });
  $('e5Show').addEventListener('click', () => {
    reveal = true; revealedEver = true; mark = false; render();
    okBox($('e5Msg'), bi('(a) ★ = {f, g, h}: f is maximal even though it sits low. (b) gold rings = {e, g, h}.', '(a) ★ = {f, g, h}：f 位置虽低，也是极大元。(b) 金圈 = {e, g, h}。'), 'info');
  });
  render();
})();

/* ================= E6 ================= */
(function e6() {
  const opts = [
    { ok: false, en: 'All linear orders on X, ordered by ⊆.', zh: 'X 上的全体线性序，按 ⊆ 排序。',
      why: P('Two distinct linear orders on X are never ⊆-comparable, so every element is trivially maximal. Nothing forces the order to contain ≤.', 'X 上两个不同的线性序之间不可能有 ⊆ 关系，所以每个元素都平凡地是极大元。没有任何东西保证它包含 ≤。') },
    { ok: true, en: 'All partial orders on X that contain ≤, ordered by ⊆.', zh: 'X 上所有包含 ≤ 的偏序，按 ⊆ 排序。' },
    { ok: false, en: 'All chains of (X, ≤), ordered by ⊆.', zh: '(X, ≤) 中的全体链，按 ⊆ 排序。',
      why: P('That gives a maximal chain (the Hausdorff maximal principle), which is a subset of X, not an order on all of X.', '这样得到的是一条极大链（豪斯多夫极大原理），它是 X 的子集，而不是整个 X 上的序。') },
    { ok: false, en: 'All well-orders of subsets of X, ordered by end-extension.', zh: 'X 的各子集上的良序，按尾扩张排序。',
      why: P('That proves the well-ordering theorem, but the resulting well-order has nothing to do with ≤.', '这证明的是良序定理，得到的良序与 ≤ 毫无关系。') },
  ];
  const proof = [
    P('P = {R : R is a partial order on X and ≤ ⊆ R}, ordered by ⊆. Since ≤ ∈ P, P ≠ ∅.', 'P = {R : R 是 X 上的偏序且 ≤ ⊆ R}，按 ⊆ 排序。≤ ∈ P，故 P ≠ ∅。'),
    P('For a chain 𝒞 ⊆ P, ⋃𝒞 is a partial order containing ≤: reflexivity is clear, and transitivity and antisymmetry each mention at most three pairs, which all lie in one member of the chain. So chains have upper bounds.', '对链 𝒞 ⊆ P，⋃𝒞 是包含 ≤ 的偏序：自反性显然；传递性与反对称性各自只涉及至多三个序对，它们都落在链的某一个成员中。所以链都有上界。'),
    P('Zorn gives a maximal R ∈ P.', '由佐恩引理得到极大的 R ∈ P。'),
    P('Suppose a, b are R-incomparable. Let R′ = R ∪ {(x, y) : x R a and b R y}. A short case check shows R′ is transitive. It is antisymmetric, since a new pair (x, y) together with (y, x) ∈ R′ would give b R a. And (a, b) ∈ R′ ∖ R. This contradicts maximality, so R is linear. ∎',
      '设 a, b 关于 R 不可比较。令 R′ = R ∪ {(x, y) : x R a 且 b R y}。简单分情形可验证 R′ 是传递的；它是反对称的，因为新序对 (x, y) 若与 (y, x) ∈ R′ 并存，就会推出 b R a。并且 (a, b) ∈ R′ ∖ R。这与极大性矛盾，所以 R 是线性序。∎'),
    P('For finite X no choice is needed (topological sorting). In general the theorem is strictly weaker than AC: BPI already proves it.', '对有限的 X 不需要选择公理（拓扑排序即可）。一般情形下，该定理严格弱于 AC：BPI 就能证明它。'),
  ];
  const box = $('e6Choice');
  let shown = false, revealed = false;
  const showProof = () => { if (!shown) { shown = true; Stepper($('e6Proof'), proof).showAll(); } };
  opts.forEach(o => {
    const b = document.createElement('button');
    b.className = 'btn choice';
    b.innerHTML = bi(o.en, o.zh);
    b.addEventListener('click', () => {
      box.querySelectorAll('.choice').forEach(x => x.classList.remove('right', 'wrongc'));
      b.classList.add(o.ok ? 'right' : 'wrongc');
      if (o.ok) {
        okBox($('e6Msg'), bi('✓ Right. The full proof:', '✓ 对。完整证明如下：'));
        showProof();
        if (!revealed) Progress.mark('L10E6');
      } else okBox($('e6Msg'), '✗ ' + o.why, 'bad');
    });
    box.appendChild(b);
  });
  $('e6Show').addEventListener('click', () => {
    revealed = true;
    box.querySelectorAll('.choice')[1].classList.add('right');
    okBox($('e6Msg'), bi('Answer: partial orders extending ≤, ordered by ⊆.', '答案：所有扩张 ≤ 的偏序，按 ⊆ 排序。'), 'info');
    showProof();
  });
})();
