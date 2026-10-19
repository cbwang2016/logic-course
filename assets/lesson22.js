// Lesson 22 interactions: OD & HOD.
Lang.init();
Progress.paint();

const $ = id => document.getElementById(id);
const okBox = (box, html, kind = 'ok') => { box.className = 'msg ' + kind; box.innerHTML = html; };
const clearBox = box => { box.className = 'msg'; box.innerHTML = ''; };
function txt(parent, x, y, s, attrs = {}) {
  const t = el('text', Object.assign({ x, y }, attrs), parent);
  t.textContent = s;
  return t;
}
const C = { ink: '#1f2430', muted: '#6b7280', line: '#e3dfd3', accent: '#3b5bdb', accentSoft: '#e7ecff', ok: '#2f9e44', okSoft: '#d3f9d8',
  bad: '#e03131', badSoft: '#ffe3e3', meta: '#ae3ec9', metaSoft: '#f8e7fc', gold: '#f08c00', goldSoft: '#fff3bf', paper: '#fbfaf6' };

/* ---------- ordinals below ω₁·2: [a, b, c] = ω₁·a + ω·b + c ---------- */
const ocmp = (u, v) => { for (let i = 0; i < 3; i++) if (u[i] !== v[i]) return u[i] - v[i]; return 0; };
function ostr(v) {
  const [a, b, c] = v, parts = [];
  if (a) parts.push(a === 1 ? 'ω₁' : 'ω₁·' + a);
  if (b) parts.push(b === 1 ? 'ω' : 'ω·' + b);
  if (c || !parts.length) parts.push(String(c));
  return parts.join('+');
}
const osucc = v => [v[0], v[1], v[2] + 1];
const lexLess = (p, q) => { for (let i = 0; i < Math.min(p.length, q.length); i++) if (p[i] !== q[i]) return p[i] < q[i]; return p.length < q.length; };

/* ---------- generic multiple choice (check-yourself and exercises) ---------- */
function mcq(box, { head, q, opts, expl }, onSolve) {
  box.innerHTML = (head === false ? '' : `<div class="cyh">${head || bil('Check yourself', '自测')}</div>`) + `<div style="margin:4px 0 6px">${q}</div>`;
  const wrap = document.createElement('div');
  const tb = document.createElement('div'); tb.className = 'toolbar';
  tb.innerHTML = `<button class="btn ghost small">${bil('Show answer', '显示答案')}</button>`;
  const msg = document.createElement('div'); msg.className = 'msg';
  let revealed = false;
  opts.forEach(o => {
    const b = document.createElement('button');
    b.className = 'btn choice';
    b.innerHTML = o.h;
    b.addEventListener('click', () => {
      wrap.querySelectorAll('.choice').forEach(x => x.classList.remove('right', 'wrongc'));
      b.classList.add(o.ok ? 'right' : 'wrongc');
      if (o.ok) { okBox(msg, '✓ ' + expl); if (!revealed && onSolve) onSolve(); }
      else okBox(msg, o.why || bi('✗ Not quite. Re-read the definition box above and try again.', '✗ 不对。重读上面的定义框，再试一次。'), 'bad');
    });
    wrap.appendChild(b);
  });
  box.appendChild(wrap); box.appendChild(tb); box.appendChild(msg);
  tb.querySelector('button').addEventListener('click', () => {
    revealed = true;
    wrap.querySelectorAll('.choice').forEach((x, i) => { x.classList.remove('wrongc'); if (opts[i].ok) x.classList.add('right'); });
    okBox(msg, expl, 'info');
  });
}

/* ---------- step-by-step reveal ---------- */
function stepper(stepsId, nextId, allId) {
  const steps = [...document.querySelectorAll(`#${stepsId} .step`)];
  let k = 0;
  $(nextId).addEventListener('click', () => {
    if (k < steps.length) steps[k++].classList.add('on');
    if (k === steps.length) $(nextId).disabled = true;
  });
  $(allId).addEventListener('click', () => { steps.forEach(s => s.classList.add('on')); k = steps.length; $(nextId).disabled = true; });
}
stepper('reflSteps', 'reflNext', 'reflAll');
stepper('hodSteps', 'hodNext', 'hodAll');
stepper('eqSteps', 'eqNext', 'eqAll');

/* ---------- segmented control ---------- */
function seg(box, items, onPick, start = 0) {
  box.innerHTML = '';
  const bs = items.map((it, i) => {
    const b = document.createElement('button');
    b.innerHTML = it.h;
    b.addEventListener('click', () => { bs.forEach(x => x.classList.remove('on')); b.classList.add('on'); onPick(it.k); });
    box.appendChild(b);
    return b;
  });
  bs[start].classList.add('on');
  onPick(items[start].k);
}
function btnBar(box, items, onPick, start = 0) {
  box.innerHTML = '';
  const bs = items.map(it => {
    const b = document.createElement('button');
    b.className = 'btn small';
    b.innerHTML = it.h;
    b.addEventListener('click', () => { bs.forEach(x => x.classList.remove('sel')); b.classList.add('sel'); onPick(it.k); });
    box.appendChild(b);
    return b;
  });
  if (start !== null) { bs[start].classList.add('sel'); onPick(items[start].k); }
  return bs;
}

/* ================= §1 ordinal-parameter lens ================= */
(function lens() {
  const svg = $('lensSvg');
  const AX = 350, AY = 385, TOP = 25, SLOPE = 0.78;
  const half = y => (AY - y) * SLOPE;
  function yOf(v) {
    const [a, b, c] = v;
    if (a === 0 && b === 0) return 362 - c * 20;
    if (a === 0 && b === 1) return 235 - c * 15;
    if (a === 0 && b === 2) return 165 - c * 12;
    return 105 - c * 13;
  }
  const betas = [[0, 0, 2], [0, 0, 5], [0, 1, 0], [0, 1, 1], [0, 2, 0], [1, 0, 0]];
  let beta = betas[2], tpl = 'P';
  function base() {
    svg.innerHTML = '';
    el('polygon', { points: `${AX},${AY} ${AX - half(TOP)},${TOP} ${AX + half(TOP)},${TOP}`, fill: '#f4f1e8', stroke: '#c9c3b0', 'stroke-width': 1.5 }, svg);
    el('polygon', { points: `${AX},${AY} ${AX - half(TOP) * 0.22},${TOP} ${AX + half(TOP) * 0.22},${TOP}`, fill: C.accentSoft, stroke: C.accent, 'stroke-width': 1, 'stroke-dasharray': '4 3', opacity: 0.8 }, svg);
    txt(svg, AX + half(TOP) * 0.22 + 6, TOP + 16, 'L', { 'font-size': 14, fill: C.accent, 'font-weight': 700 });
    txt(svg, AX + half(TOP) - 40, TOP + 16, 'V', { 'font-size': 18, fill: C.ink, 'font-weight': 700 });
    el('line', { x1: AX, y1: AY, x2: AX, y2: TOP, stroke: C.ink, 'stroke-width': 1.5 }, svg);
    txt(svg, AX + 6, TOP - 6, 'Ord', { 'font-size': 13, fill: C.ink });
    betas.forEach(b => {
      const y = yOf(b);
      el('line', { x1: AX - 5, y1: y, x2: AX + 5, y2: y, stroke: C.ink }, svg);
      txt(svg, AX - half(y) - 8, y + 4, ostr(b), { 'font-size': 12, 'text-anchor': 'end', fill: C.muted });
    });
  }
  function draw() {
    base();
    const y = yOf(beta), ys = yOf(osucc(beta)), g = el('g', { class: 'fadein' }, svg);
    const finite = beta[0] === 0 && beta[1] === 0;
    let formula, inL;
    if (tpl === 'single') {
      el('circle', { cx: AX, cy: y, r: 5, fill: C.meta }, g);
      el('circle', { cx: AX + 26, cy: ys, r: 7, fill: C.goldSoft, stroke: C.gold, 'stroke-width': 2, class: 'pop' }, g);
      txt(g, AX + 38, ys + 4, `{${ostr(beta)}}`, { 'font-size': 13, fill: C.gold, 'font-weight': 700 });
      formula = 'φ(z, β) :≡ ∀w (w ∈ z ↔ w = β)';
      inL = bi('<b>In L?</b> Always: β ∈ L and L is closed under pairing.', '<b>属于 L 吗？</b>总是：β ∈ L，而 L 对配对封闭。');
    } else if (tpl === 'V') {
      el('polygon', { points: `${AX},${AY} ${AX - half(y)},${y} ${AX + half(y)},${y}`, fill: C.goldSoft, stroke: C.gold, 'stroke-width': 2, opacity: 0.85 }, g);
      txt(g, AX + half(y) + 8, y + 4, `V_${ostr(beta)}`, { 'font-size': 14, fill: C.gold, 'font-weight': 700 });
      formula = 'φ(z, β) :≡ z = V_β   (V_β by transfinite recursion on β: one formula, parameter β)';
      inL = (beta[0] === 0 && beta[1] === 0) || ocmp(beta, [0, 1, 0]) === 0
        ? bi('<b>In L?</b> Yes: V<sub>β</sub> for β ≤ ω consists of hereditarily finite sets, all constructible (V<sub>ω</sub> = L<sub>ω</sub>).', '<b>属于 L 吗？</b>是：β ≤ ω 时 V<sub>β</sub> 由遗传有限集构成，它们都可构成（V<sub>ω</sub> = L<sub>ω</sub>）。')
        : bi('<b>In L?</b> Only if V<sub>β</sub> ⊆ L. For β ≥ ω+1 this fails as soon as some real is non-constructible (e.g. in L[c]).', '<b>属于 L 吗？</b>仅当 V<sub>β</sub> ⊆ L。β ≥ ω+1 时，只要存在不可构成的实数（如 L[c] 中）就不成立。');
    } else if (tpl === 'L') {
      const h = half(y) * 0.22;
      el('polygon', { points: `${AX},${AY} ${AX - h},${y} ${AX + h},${y}`, fill: C.accent, opacity: 0.55 }, g);
      txt(g, AX + h + 8, y + 4, `L_${ostr(beta)}`, { 'font-size': 14, fill: C.accent, 'font-weight': 700 });
      formula = 'φ(z, β) :≡ z = L_β';
      inL = bi('<b>In L?</b> Always. L<sub>β</sub> is constructible by definition, so this one is OD for a cheap reason.', '<b>属于 L 吗？</b>总是。L<sub>β</sub> 按定义就是可构成的，所以它是 OD 并不稀奇。');
    } else {
      const n = 13, w = half(ys) * 0.9;
      const hollow = finite ? [] : [2, 5, 9, 11];
      for (let i = 0; i < n; i++) {
        const x = AX - w + (2 * w * i) / (n - 1);
        const ho = hollow.includes(i);
        const d = el('circle', { cx: x, cy: ys, r: 5, fill: ho ? '#fff' : C.ok, stroke: ho ? C.bad : C.ok, 'stroke-width': 2, class: 'pop' }, g);
        d.style.animationDelay = (i * 0.04) + 's';
      }
      el('line', { x1: AX - w - 8, y1: ys - 10, x2: AX + w + 8, y2: ys - 10, stroke: C.ok, 'stroke-dasharray': '3 3' }, g);
      txt(g, AX + w + 12, ys + 4, `P(${ostr(beta)})`, { 'font-size': 14, fill: C.ok, 'font-weight': 700 });
      if (!finite) txt(g, 14, 394, '○ hollow = possibly non-constructible · 空心＝可能不可构成', { 'font-size': 11.5, fill: C.bad });
      formula = 'φ(z, β) :≡ ∀w (w ∈ z ↔ w ⊆ β)';
      inL = finite
        ? bi('<b>In L?</b> Yes: β is finite, so every subset of β is finite and constructible.', '<b>属于 L 吗？</b>是：β 有限，它的子集都是有限集，都可构成。')
        : bi('<b>In L?</b> Only if every subset of β is constructible. Under V = L, yes. In L[c] (c a Cohen real), P(ω) ∉ L because c ∉ L. P(β) is still OD in every case: it is defined from β alone.',
          '<b>属于 L 吗？</b>仅当 β 的每个子集都可构成。在 V = L 下是的；在 L[c]（c 为科恩实数）中 P(ω) ∉ L，因为 c ∉ L。但无论如何 P(β) 都是 OD：它只用 β 就定义出来了。');
    }
    el('circle', { cx: AX, cy: y, r: 4, fill: C.meta }, g);
    okBox($('lensInfo'), `<div class="m">${formula}</div>` +
      bi(`<b>OD?</b> Yes: it is the unique z with φ(z, ${ostr(beta)}). One formula, one ordinal parameter.`, `<b>是 OD 吗？</b>是：它是满足 φ(z, ${ostr(beta)}) 的唯一 z，一条公式、一个序数参数。`) + inL, 'info');
  }
  btnBar($('lensOrd'), betas.map(b => ({ k: b, h: ostr(b) })), k => { beta = k; draw(); }, 2);
  btnBar($('lensTpl'), [
    { k: 'single', h: '{β}' }, { k: 'V', h: 'V<sub>β</sub>' }, { k: 'L', h: 'L<sub>β</sub>' }, { k: 'P', h: 'P(β)' },
  ], k => { tpl = k; draw(); }, 3);
})();

mcq($('cy1'), {
  q: bi('Which statement about <span class="m">P(ω)</span> is correct (in ZF)?', '关于 <span class="m">P(ω)</span>，哪一项正确（在 ZF 中）？'),
  opts: [
    { h: bi('P(ω) is OD, and P(ω) ∈ L always.', 'P(ω) 是 OD，且总有 P(ω) ∈ L。') },
    { ok: true, h: bi('P(ω) is OD; P(ω) ∈ L iff every real is constructible.', 'P(ω) 是 OD；P(ω) ∈ L 当且仅当每个实数都可构成。') },
    { h: bi('P(ω) is OD only if V = L.', '只有在 V = L 时 P(ω) 才是 OD。') },
  ],
  expl: bi('P(ω) is defined without parameters, so it is OD in every model. If P(ω) ∈ L, then every real is in L by transitivity of L. Conversely, if all reals are in L, then P(ω) = P(ω)<sup>L</sup> ∈ L. So OD can be strictly bigger than L.',
    'P(ω) 不用参数即可定义，在任何模型中都是 OD。若 P(ω) ∈ L，由 L 的传递性每个实数都在 L 中；反之若所有实数都在 L 中，则 P(ω) = P(ω)<sup>L</sup> ∈ L。所以 OD 可以严格大于 L。'),
});

/* ================= §2 Sat table ================= */
(function satTable() {
  const svg = $('satSvg');
  let mode = 'Va', run = 0;
  const rows = [
    ['∃y (y ∈ a)', 'a = ∅', '0'],
    ['∀y∈a (y ∈ b)', 'a = 1, b = 2', '1'],
    ['∃y (a ∈ y ∧ b ∈ y)', 'a = 0, b = ω', '1'],
    ['∀y ∃u (y ∈ u)', '—', '?'],
    ['⋮', '⋮', '⋮'],
  ];
  function frame() {
    svg.innerHTML = '';
    if (mode === 'Va') {
      el('circle', { cx: 120, cy: 135, r: 80, fill: C.goldSoft, stroke: C.gold, 'stroke-width': 2.5 }, svg);
      txt(svg, 120, 130, '(V_α, ∈)', { 'font-size': 16, 'text-anchor': 'middle', 'font-weight': 700 });
      txt(svg, 120, 152, 'a set · 一个集合', { 'font-size': 12, 'text-anchor': 'middle', fill: C.muted });
    } else {
      el('polygon', { points: '120,250 20,10 220,10', fill: '#f4f1e8', stroke: '#c9c3b0', 'stroke-width': 2 }, svg);
      txt(svg, 120, 120, '(V, ∈)', { 'font-size': 16, 'text-anchor': 'middle', 'font-weight': 700 });
      txt(svg, 120, 142, 'a proper class · 真类', { 'font-size': 12, 'text-anchor': 'middle', fill: C.muted });
    }
    const head = mode === 'Va' ? 'Sat(V_α, ∈, ⌜φ⌝, ā)' : mode === 'V' ? 'Sat_V(⌜φ⌝, ā) for ALL φ ?' : 'Sat_Σ₂(⌜φ⌝, ā), φ ∈ Σ₂ only';
    txt(svg, 470, 26, head, { 'font-size': 14, 'text-anchor': 'middle', 'font-weight': 700, fill: mode === 'V' ? C.bad : C.ink });
    [['φ', 300], ['ā', 470], ['value', 630]].forEach(([h, x]) => txt(svg, x, 52, h, { 'font-size': 12, 'text-anchor': 'middle', fill: C.muted }));
    el('line', { x1: 250, y1: 58, x2: 690, y2: 58, stroke: C.line }, svg);
  }
  async function fill() {
    const my = ++run;
    frame();
    clearBox($('satMsg'));
    for (let i = 0; i < rows.length; i++) {
      await sleep(380);
      if (my !== run) return;
      const y = 82 + i * 30;
      let [f, a, v] = rows[i];
      if (i === 3) {
        if (mode === 'Va') v = '1/0';
        else if (mode === 'Vn') { f = 'Σ₃ formula'; a = '…'; v = '✗ not in table'; }
      }
      const g = el('g', { class: 'fadein' }, svg);
      txt(g, 300, y, f, { 'font-size': 13, 'text-anchor': 'middle' });
      txt(g, 470, y, a, { 'font-size': 13, 'text-anchor': 'middle' });
      txt(g, 630, y, v, { 'font-size': 13, 'text-anchor': 'middle', 'font-weight': 700, fill: v === '1' ? C.ok : v === '0' ? C.bad : C.muted });
      if (mode === 'V' && i === 2) {
        await sleep(450);
        if (my !== run) return;
        const x = el('g', { class: 'pop' }, svg);
        el('line', { x1: 270, y1: 40, x2: 690, y2: 230, stroke: C.bad, 'stroke-width': 6, opacity: 0.8 }, x);
        el('line', { x1: 690, y1: 40, x2: 270, y2: 230, stroke: C.bad, 'stroke-width': 6, opacity: 0.8 }, x);
        txt(x, 480, 258, 'Tarski: no such formula · 塔斯基：不存在这样的公式', { 'font-size': 13, 'text-anchor': 'middle', fill: C.bad, 'font-weight': 700 });
        okBox($('satMsg'), bi('✗ One formula Sat<sub>V</sub> with Sat<sub>V</sub>(⌜φ⌝, ā) ↔ φ(ā) for <b>every</b> φ would be a truth definition for V, which Tarski\'s theorem rules out (L13). The recursion that works for sets breaks down here: its clause for ∃ would range over the proper class V, so the recursion cannot produce a set.',
          '✗ 若有一条公式 Sat<sub>V</sub> 使得对<b>每个</b> φ 都有 Sat<sub>V</sub>(⌜φ⌝, ā) ↔ φ(ā)，它就是 V 的真定义，而塔斯基定理排除了这种可能（第 13 课）。对集合行得通的递归在这里失效：∃ 那一条要跑遍真类 V，递归无法产生一个集合。'), 'bad');
        return;
      }
    }
    if (mode === 'Va') okBox($('satMsg'), bi('✓ The whole table is a <b>set</b> ⊆ ω × V<sub>α</sub><sup>&lt;ω</sup>, built by recursion on formulas. ZF proves it exists, for every set structure, uniformly: <b>one</b> formula Sat(M, E, k, s) works for all of them.', '✓ 整张表是一个<b>集合</b> ⊆ ω × V<sub>α</sub><sup>&lt;ω</sup>，沿公式递归构造。ZF 对每个集合结构都一致地证明它存在：<b>一条</b>公式 Sat(M, E, k, s) 对所有集合结构都适用。'));
    else okBox($('satMsg'), bi('✓ For a <b>fixed</b> n, Σ<sub>n</sub>-truth in V is definable by a Σ<sub>n</sub> formula (L20). But a Σ<sub>3</sub> formula is not covered, and no single n covers all formulas. That is exactly why Tarski is not contradicted.', '✓ 对<b>固定</b>的 n，V 中的 Σ<sub>n</sub> 真可用一条 Σ<sub>n</sub> 公式定义（第 20 课）。但它管不到 Σ<sub>3</sub> 公式，也没有哪个 n 能管住所有公式。这正是它不与塔斯基定理矛盾的原因。'), 'info');
  }
  seg($('satSeg'), [
    { k: 'Va', h: bi('(V<sub>α</sub>, ∈): a set', '(V<sub>α</sub>, ∈)：集合') },
    { k: 'V', h: bi('(V, ∈): all formulas', '(V, ∈)：所有公式') },
    { k: 'Vn', h: bi('(V, ∈): Σ<sub>2</sub> only', '(V, ∈)：只限 Σ<sub>2</sub>') },
  ], k => { mode = k; fill(); });
  $('satRun').addEventListener('click', fill);
})();

mcq($('cy2'), {
  q: bi('For each fixed n, Σ<sub>n</sub>-truth in V is definable (L20). Does this contradict Tarski?', '对每个固定的 n，V 中的 Σ<sub>n</sub> 真是可定义的（第 20 课）。这与塔斯基定理矛盾吗？'),
  opts: [
    { h: bi('Yes. Tarski must then be false for set theory.', '矛盾，那么塔斯基定理对集合论不成立。') },
    { ok: true, h: bi('No. Tarski only forbids one formula that works for all formulas at once.', '不矛盾。塔斯基只禁止一条公式同时对所有公式都管用。') },
    { h: bi('No, because Σ<sub>n</sub>-truth is only definable with parameters.', '不矛盾，因为 Σ<sub>n</sub> 真只有带参数时才可定义。') },
  ],
  expl: bi('Sat<sub>Σn</sub> is itself a Σ<sub>n</sub> formula (n ≥ 1). It cannot evaluate Σ<sub>n+1</sub> formulas. Tarski\'s diagonal argument needs a truth predicate that also evaluates formulas built from the predicate itself, which are more complex than Σ<sub>n</sub>. So no contradiction arises.',
    'Sat<sub>Σn</sub> 本身是 Σ<sub>n</sub> 公式（n ≥ 1），它无法判定 Σ<sub>n+1</sub> 公式。塔斯基的对角线论证需要一个真谓词也能判定由它自身构造出的公式，而这些公式比 Σ<sub>n</sub> 更复杂。所以不会产生矛盾。'),
});

/* ================= §3 reflection climber ================= */
(function reflection() {
  const svg = $('reflSvg');
  const AX = 230, AY = 410, TOP = 30, SL = 0.55, MAX = 15;
  const yA = a => AY - a * 25;
  const half = y => (AY - y) * SL;
  const RANKX = 5, BETAS = [2, 7], REFL = [3, 6, 10, 13, 15];
  let alpha = 1, timer = null;
  const seen = new Set();
  function draw() {
    svg.innerHTML = '';
    el('polygon', { points: `${AX},${AY} ${AX - half(TOP)},${TOP} ${AX + half(TOP)},${TOP}`, fill: '#f4f1e8', stroke: '#c9c3b0', 'stroke-width': 1.5 }, svg);
    txt(svg, AX + half(TOP) - 26, TOP + 18, 'V', { 'font-size': 18, 'font-weight': 700 });
    const y = yA(alpha), ok3 = REFL.includes(alpha);
    el('polygon', { points: `${AX},${AY} ${AX - half(y)},${y} ${AX + half(y)},${y}`, fill: ok3 ? C.okSoft : C.accentSoft, stroke: ok3 ? C.ok : C.accent, 'stroke-width': 2, opacity: 0.9 }, svg);
    txt(svg, AX + half(y) + 6, y + 4, `V_${alpha}`, { 'font-size': 13, fill: ok3 ? C.ok : C.accent, 'font-weight': 700 });
    el('line', { x1: AX, y1: AY, x2: AX, y2: TOP, stroke: C.ink, 'stroke-width': 1.2 }, svg);
    for (let a = 1; a <= MAX; a++) {
      el('line', { x1: AX - 4, y1: yA(a), x2: AX + 4, y2: yA(a), stroke: C.ink }, svg);
      if (seen.has(a) && REFL.includes(a)) el('rect', { x: AX + 8, y: yA(a) - 4, width: 8, height: 8, fill: C.ok, transform: `rotate(45 ${AX + 12} ${yA(a)})` }, svg);
    }
    txt(svg, 8, 424, '◆ = φ reflects here (seen) · φ 在此反射（已访问）', { 'font-size': 11, fill: C.ok });
    BETAS.forEach((b, i) => {
      el('circle', { cx: AX, cy: yA(b), r: 6, fill: C.meta }, svg);
      txt(svg, AX - 10, yA(b) + 4, `β${'₁₂'[i]} = ${b}`, { 'font-size': 12, 'text-anchor': 'end', fill: C.meta, 'font-weight': 700 });
    });
    const yx = AY - (RANKX + 0.5) * 25;
    el('circle', { cx: AX - 50, cy: yx, r: 8, fill: C.gold, stroke: '#b36200', 'stroke-width': 2 }, svg);
    txt(svg, AX - 64, yx + 4, 'x (rank 5)', { 'font-size': 12, fill: '#b36200', 'font-weight': 700, 'text-anchor': 'end' });
    const l1 = alpha > RANKX, l2 = BETAS.every(b => b < alpha);
    if (l1 && !ok3) {
      const yg = AY - 3.5 * 25;
      const g = el('g', { class: 'pop' }, svg);
      el('circle', { cx: AX + 40, cy: yg, r: 8, fill: '#fff', stroke: C.bad, 'stroke-width': 2, 'stroke-dasharray': '3 2' }, g);
      txt(g, AX + 54, yg + 4, 'fake z′', { 'font-size': 12, fill: C.bad });
    }
    $('reflAlpha').innerHTML = `α = ${alpha}`;
    const lamp = (on, en, zh) => `<li class="${on ? 'on' : 'off'}"><span class="dot"></span>${bil(en, zh)}</li>`;
    $('reflLamps').innerHTML =
      lamp(l1, `x ∈ V<sub>α</sub> &nbsp;(rank x = ${RANKX} &lt; α)`, `x ∈ V<sub>α</sub>（rank x = ${RANKX} &lt; α）`) +
      lamp(l2, 'β₁, β₂ ∈ V<sub>α</sub> &nbsp;(β₁, β₂ &lt; α)', 'β₁, β₂ ∈ V<sub>α</sub>（β₁, β₂ &lt; α）') +
      lamp(ok3, 'φ absolute between V<sub>α</sub> and V', 'φ 在 V<sub>α</sub> 与 V 之间绝对');
    if (l1 && l2 && ok3) okBox($('reflMsg'), bi(`✓ All green at α = ${alpha}. x is the <b>unique</b> z ∈ V<sub>${alpha}</sub> with (V<sub>${alpha}</sub>, ∈) ⊨ φ[z, β₁, β₂]. That is a statement about a <b>set</b> structure, so it is expressible with Sat. Hence x ∈ OD.`,
      `✓ α = ${alpha} 时全绿。x 是 V<sub>${alpha}</sub> 中满足 (V<sub>${alpha}</sub>, ∈) ⊨ φ[z, β₁, β₂] 的<b>唯一</b> z。这是关于<b>集合</b>结构的命题，可以用 Sat 表达，所以 x ∈ OD。`));
    else if (!l1 || !l2) okBox($('reflMsg'), bi('V<sub>α</sub> is too small: a structure can only define its own elements, from its own elements.', 'V<sub>α</sub> 太小：一个结构只能用自己的元素，定义自己的元素。'), 'warn');
    else okBox($('reflMsg'), bi('Everything is inside V<sub>α</sub>, but φ is <b>not</b> absolute here. V<sub>α</sub>\'s own opinion of φ can be wrong, e.g. it may think a “fake” z′ ≠ x satisfies φ. Keep climbing: reflection guarantees arbitrarily high good levels.', '东西都在 V<sub>α</sub> 里了，但 φ 在这里<b>不</b>绝对。V<sub>α</sub> 自己对 φ 的判断可能出错，例如它可能认为一个“冒牌”的 z′ ≠ x 满足 φ。继续爬：反射原理保证好的层要多高有多高。'), 'bad');
    seen.add(alpha);
  }
  const set = a => { alpha = Math.max(1, Math.min(MAX, a)); draw(); };
  const stop = () => { if (timer) { clearInterval(timer); timer = null; } };
  $('reflUp').addEventListener('click', () => { stop(); set(alpha + 1); });
  $('reflDown').addEventListener('click', () => { stop(); set(alpha - 1); });
  $('reflReset').addEventListener('click', () => { stop(); seen.clear(); set(1); });
  $('reflClimb').addEventListener('click', () => {
    stop();
    const good = a => a > RANKX && BETAS.every(b => b < a) && REFL.includes(a);
    if (good(alpha)) set(alpha + 1);
    timer = setInterval(() => {
      if (good(alpha) || alpha >= MAX) { stop(); return; }
      set(alpha + 1);
      if (good(alpha)) stop();
    }, 420);
  });
  draw();
})();

mcq($('cy3'), {
  q: bi('Which direction of “x is definable in V from ordinals ⇔ x ∈ OD” uses the reflection theorem?', '“x 在 V 中由序数可定义 ⇔ x ∈ OD”的哪个方向用到了反射原理？'),
  opts: [
    { ok: true, h: bi('⇒ : from a definition over V to a definition over some V<sub>α</sub>.', '⇒ ：从 V 上的定义得到某个 V<sub>α</sub> 上的定义。') },
    { h: bi('⇐ : from a definition over V<sub>α</sub> to one over V.', '⇐ ：从 V<sub>α</sub> 上的定义得到 V 上的定义。') },
    { h: bi('Both directions.', '两个方向都用到。') },
  ],
  expl: bi('⇒ needs some V<sub>α</sub> that agrees with V about φ, which is what reflection supplies (one instance per φ). ⇐ is free: the formula χ(z, α, k, <span class="ov">β</span>) only mentions the set V<sub>α</sub> and Sat for sets.',
    '⇒ 需要一个在 φ 上与 V 意见一致的 V<sub>α</sub>，这正是反射原理提供的（每个 φ 用一次）。⇐ 不费力：公式 χ(z, α, k, <span class="ov">β</span>) 只涉及集合 V<sub>α</sub> 和集合上的 Sat。'),
});

/* ================= §4 climbing α₁ ================= */
(function climb() {
  const svg = $('climbSvg');
  const LIST = [[0, 0, 0], [0, 0, 1], [0, 0, 2], [0, 0, 3], [0, 0, 4], [0, 0, 5], [0, 0, 6], [0, 1, 0], [0, 1, 1], [0, 1, 2], [0, 1, 3], [0, 2, 0], [1, 0, 0], [1, 0, 1], [1, 0, 2]];
  const X = i => 40 + i * 46;
  const idx = v => LIST.findIndex(w => ocmp(v, w) === 0);
  const T = [
    { k: '3', s: '3', rank: [0, 0, 3], f: 'φ(z) :≡ z is an ordinal with exactly three elements', p: [] },
    { k: 's3', s: '{3}', rank: [0, 0, 4], f: 'φ(z, α₂) :≡ ∀w (w ∈ z ↔ w = α₂)', p: [[0, 0, 3]] },
    { k: 'w', s: 'ω', rank: [0, 1, 0], f: 'φ(z) :≡ z is the least nonzero limit ordinal', p: [] },
    { k: 'R', s: 'ℝ = P(ω)', rank: [0, 1, 1], f: 'φ(z) :≡ ∀w (w ∈ z ↔ w ⊆ ω)   (ω as above)', p: [] },
    { k: 'wR', s: '{ω, ℝ}', rank: [0, 1, 2], f: 'φ(z) :≡ z = {ω, P(ω)}', p: [] },
    { k: 'w2', s: 'ω·2', rank: [0, 2, 0], f: 'φ(z, α₂) :≡ z = α₂', p: [[0, 2, 0]] },
    { k: 'w1', s: 'ω₁', rank: [1, 0, 0], f: 'φ(z) :≡ z is the least uncountable ordinal', p: [] },
    { k: 'c', s: bil('c in L[c]', 'L[c] 中的 c'), rank: [0, 1, 0], f: '—', p: [], never: true },
  ];
  let t = T[3], a = 0, timer = null;
  const status = () => {
    if (t.never) return 'never';
    if (ocmp(t.rank, LIST[a]) >= 0) return 'rank';
    if (t.p.some(p => ocmp(p, LIST[a]) >= 0)) return 'param';
    return 'ok';
  };
  function draw() {
    svg.innerHTML = '';
    const st = status(), ax = X(a);
    if (a > 0) el('rect', { x: X(0) - 14, y: 70, width: Math.max(0, ax - X(0) + 4), height: 44, rx: 8, fill: st === 'ok' ? C.okSoft : C.accentSoft, stroke: st === 'ok' ? C.ok : C.accent, 'stroke-width': 1.5 }, svg);
    if (ax - X(0) > 120) txt(svg, X(0), 97, `V_α₁ = {rank < ${ostr(LIST[a])}}`, { 'font-size': 12, fill: st === 'ok' ? C.ok : C.accent, 'font-weight': 700 });
    el('line', { x1: X(0) - 10, y1: 140, x2: X(LIST.length - 1) + 14, y2: 140, stroke: C.ink, 'stroke-width': 1.5 }, svg);
    LIST.forEach((v, i) => {
      el('line', { x1: X(i), y1: 134, x2: X(i), y2: 146, stroke: C.ink }, svg);
      txt(svg, X(i), 164, ostr(v), { 'font-size': 12, 'text-anchor': 'middle', fill: i === a ? C.ink : C.muted, 'font-weight': i === a ? 800 : 400 });
    });
    [[6, 7], [11, 12]].forEach(([i, j]) => txt(svg, (X(i) + X(j)) / 2, 158, '…', { 'font-size': 13, 'text-anchor': 'middle', fill: C.muted }));
    el('path', { d: `M${ax},128 l-8,-14 h16 z`, fill: C.ink }, svg);
    txt(svg, ax, 184, 'α₁', { 'font-size': 13, 'text-anchor': 'middle', 'font-weight': 800 });
    if (!t.never) {
      const ri = idx(t.rank), rx = X(ri);
      const g = el('g', {}, svg);
      el('circle', { cx: rx, cy: 50, r: 9, fill: C.gold, stroke: '#b36200', 'stroke-width': 2 }, g);
      el('line', { x1: rx, y1: 59, x2: rx, y2: 134, stroke: '#b36200', 'stroke-dasharray': '3 3' }, g);
      txt(g, rx + 14, 46, `S, rank ${ostr(t.rank)}`, { 'font-size': 12, fill: '#b36200', 'font-weight': 700 });
      t.p.forEach((p, i) => {
        const px = X(idx(p));
        el('rect', { x: px - 7, y: 14 + i * 4, width: 14, height: 14, rx: 3, fill: C.meta }, svg);
        txt(svg, px + 12, 25, `α${'₂₃'[i]} = ${ostr(p)}`, { 'font-size': 12, fill: C.meta, 'font-weight': 700 });
      });
    } else {
      txt(svg, 360, 40, 'c: no rung of any ladder · 没有任何一级', { 'font-size': 13, 'text-anchor': 'middle', fill: C.bad, 'font-weight': 700 });
    }
    const A = ostr(LIST[a]);
    let m;
    if (st === 'never') m = [bi(`α₁ = ${A}: no. In L[c] there is <b>no</b> α₁ and no formula at all: c ∉ OD. Climbing cannot show this, since the ruler is finite and the claim is about all ordinals. It is a <b>theorem</b> about Cohen forcing (homogeneity).`, `α₁ = ${A}：不行。在 L[c] 中<b>根本不存在</b>合适的 α₁ 和公式：c ∉ OD。这一点靠攀登无法证明（尺子是有限的，而命题涉及所有序数），它是关于科恩力迫的一条<b>定理</b>（齐性）。`), 'bad'];
    else if (st === 'rank') m = [bi(`✗ α₁ = ${A}: S ∉ V<sub>α₁</sub>, since rank(S) = ${ostr(t.rank)} ≥ α₁. The structure does not contain S, so it cannot define it.`, `✗ α₁ = ${A}：S ∉ V<sub>α₁</sub>，因为 rank(S) = ${ostr(t.rank)} ≥ α₁。结构里没有 S，自然定义不了它。`), 'bad'];
    else if (st === 'param') m = [bi(`✗ α₁ = ${A}: S is in V<sub>α₁</sub>, but the parameter ${ostr(t.p[0])} is not (it is ≥ α₁). Parameters must be elements of the structure.`, `✗ α₁ = ${A}：S 在 V<sub>α₁</sub> 中，但参数 ${ostr(t.p[0])} 不在（它 ≥ α₁）。参数必须是结构中的元素。`), 'bad'];
    else {
      const tup = [A, ...t.p.map(ostr)].join('; ');
      m = [bi(`✓ α₁ = ${A}: S is the unique z ∈ V<sub>α₁</sub> with (V<sub>α₁</sub>, ∈) ⊨ ${t.p.length ? 'φ[z, α₂]' : 'φ[z]'}. Witness: (${tup}).`, `✓ α₁ = ${A}：S 是 V<sub>α₁</sub> 中唯一满足 (V<sub>α₁</sub>, ∈) ⊨ ${t.p.length ? 'φ[z, α₂]' : 'φ[z]'} 的 z。见证：(${tup})。`), 'ok'];
    }
    okBox($('climbMsg'), `<div class="m">${t.f}</div>` + m[0], m[1]);
  }
  const stop = () => { if (timer) { clearInterval(timer); timer = null; } };
  btnBar($('climbTargets'), T.map(x => ({ k: x, h: x.s })), k => { stop(); t = k; a = 0; draw(); }, 3);
  $('climbUp').addEventListener('click', () => { stop(); a = Math.min(LIST.length - 1, a + 1); draw(); });
  $('climbDown').addEventListener('click', () => { stop(); a = Math.max(0, a - 1); draw(); });
  $('climbGo').addEventListener('click', () => {
    stop();
    if (status() === 'ok' || a === LIST.length - 1) a = 0;
    draw();
    timer = setInterval(() => {
      if (status() === 'ok' || a >= LIST.length - 1) { stop(); return; }
      a++; draw();
    }, 480);
  });
})();

mcq($('cy4'), {
  q: bi('In “S is defined in V<sub>α₁</sub> from α₂, …, αₙ”, why must α₂, …, αₙ be &lt; α₁?', '在“S 在 V<sub>α₁</sub> 中由 α₂, …, αₙ 定义”中，为什么必须有 α₂, …, αₙ &lt; α₁？'),
  opts: [
    { h: bi('To avoid Russell\'s paradox.', '为了避免罗素悖论。') },
    { ok: true, h: bi('Parameters must be elements of the structure V<sub>α₁</sub>, and an ordinal β ∈ V<sub>α₁</sub> iff β &lt; α₁.', '参数必须是结构 V<sub>α₁</sub> 的元素，而序数 β ∈ V<sub>α₁</sub> 当且仅当 β &lt; α₁。') },
    { h: bi('It is not necessary; larger parameters would give a bigger class.', '不必要；参数更大会得到更大的类。') },
  ],
  expl: bi('rank(β) = β for every ordinal, so β ∈ V<sub>α₁</sub> ⇔ β &lt; α₁. Allowing “larger parameters” would not even make sense: (V<sub>α₁</sub>, ∈) ⊨ φ[a] is only defined for a ∈ V<sub>α₁</sub>. Nothing is lost either, since α₁ can always be raised.',
    '每个序数 β 都有 rank(β) = β，所以 β ∈ V<sub>α₁</sub> ⇔ β &lt; α₁。“允许更大的参数”根本无意义：(V<sub>α₁</sub>, ∈) ⊨ φ[a] 只对 a ∈ V<sub>α₁</sub> 有定义。而且也不会损失什么，因为 α₁ 总可以调高。'),
});

/* ================= §5 well-ordering ladder ================= */
(function ladder() {
  const box = $('ladder');
  const items = [
    { s: '∅', a: [0, 0, 1], k: 3, p: [] },
    { s: '1 = {∅}', a: [0, 0, 2], k: 5, p: [] },
    { s: '2 = {0,1}', a: [0, 0, 3], k: 8, p: [] },
    { s: '{{∅}}', a: [0, 0, 3], k: 11, p: [] },
    { s: '{3, 5}', a: [0, 0, 7], k: 40, p: [3, 5] },
    { s: '{4, 5}', a: [0, 0, 7], k: 40, p: [4, 5] },
    { s: 'ω', a: [0, 1, 1], k: 6, p: [] },
    { s: 'V<sub>ω</sub>', a: [0, 1, 1], k: 19, p: [] },
    { s: 'ℝ = P(ω)', a: [0, 1, 2], k: 14, p: [] },
    { s: 'ω₁', a: [1, 0, 1], k: 23, p: [] },
  ];
  const less = (x, y) => {
    const c = ocmp(x.a, y.a);
    if (c) return c < 0;
    if (x.k !== y.k) return x.k < y.k;
    return lexLess(x.p, y.p);
  };
  const why = (x, y) => {
    const c = ocmp(x.a, y.a);
    if (c) return bi(`first key decides: α = ${ostr(x.a)} &lt; ${ostr(y.a)}`, `第一关键字决定：α = ${ostr(x.a)} &lt; ${ostr(y.a)}`);
    if (x.k !== y.k) return bi(`same α = ${ostr(x.a)}; second key decides: #${x.k} &lt; #${y.k}`, `α 相同（= ${ostr(x.a)}）；第二关键字决定：#${x.k} &lt; #${y.k}`);
    return bi(`same α and same formula #${x.k}; third key decides: (${x.p}) &lt;<sub>lex</sub> (${y.p})`, `α 相同、公式 #${x.k} 也相同；第三关键字决定：(${x.p}) &lt;<sub>lex</sub> (${y.p})`);
  };
  items.forEach(it => {
    const d = document.createElement('div');
    d.className = 'rung';
    d.innerHTML = `<span class="pos"></span><span class="set">${it.s}</span><span class="key">key = (${ostr(it.a)}, #${it.k}, ${it.p.length ? '(' + it.p.join(',') + ')' : '()'})</span>`;
    d.addEventListener('click', () => pick(it));
    box.appendChild(d);
    it.el = d;
  });
  let order = [], picked = [];
  function place() { order.forEach((it, i) => { it.el.style.transform = `translateY(${i * 50}px)`; }); }
  function shuffle() {
    order = items.slice();
    for (let i = order.length - 1; i > 0; i--) { const j = Math.floor(Math.random() * (i + 1)); [order[i], order[j]] = [order[j], order[i]]; }
    box.classList.remove('sorted');
    place();
    okBox($('ladMsg'), bi('Shuffled. Press “Sort”, or click two rungs to compare them.', '已打乱。点“排序”，或点两级梯子比较它们。'), 'info');
  }
  async function sort() {
    // animated insertion sort: one move at a time
    for (let i = 1; i < order.length; i++) {
      let j = i;
      while (j > 0 && less(order[j], order[j - 1])) {
        [order[j], order[j - 1]] = [order[j - 1], order[j]];
        j--;
      }
      place();
      await sleep(160);
    }
    order.forEach((it, i) => { it.el.querySelector('.pos').textContent = '#' + (i + 1); });
    box.classList.add('sorted');
    okBox($('ladMsg'), bi('Sorted. Each set has a unique least key, so the order is linear. Keys are ordered lexicographically with ordinal entries, so it is a well-order. Rung numbers rank only these ten sets.', '排好了。每个集合有唯一的最小关键字，所以这是线序；关键字按以序数为分量的字典序比较，所以是良序。梯级编号只是这十个集合之间的名次。'), 'ok');
  }
  function pick(it) {
    if (picked.includes(it)) return;
    picked.push(it);
    it.el.classList.add('pick');
    if (picked.length === 2) {
      const [x, y] = picked;
      const [lo, hi] = less(x, y) ? [x, y] : [y, x];
      okBox($('ladMsg'), `<span class="m">${lo.s} &lt;<sub>OD</sub> ${hi.s}</span> &nbsp;·&nbsp; ${why(lo, hi)}`, 'info');
      setTimeout(() => { x.el.classList.remove('pick'); y.el.classList.remove('pick'); }, 900);
      picked = [];
    }
  }
  $('ladSort').addEventListener('click', sort);
  $('ladShuffle').addEventListener('click', shuffle);
  shuffle();
})();

mcq($('cy5'), {
  q: bi('Why is &lt;<sub>OD</sub> a <b>well</b>-order and not just a linear order?', '为什么 &lt;<sub>OD</sub> 是<b>良</b>序，而不仅仅是线序？'),
  opts: [
    { h: bi('Because AC gives a well-ordering of every set.', '因为选择公理给每个集合都提供良序。') },
    { ok: true, h: bi('Keys (α, k, <span class="ov">β</span>) have ordinal/natural entries, <span class="ov">β</span> has a length fixed by k, and lexicographic order on such fixed-length tuples is a well-order.', '关键字 (α, k, <span class="ov">β</span>) 的分量是序数或自然数，<span class="ov">β</span> 的长度由 k 固定，而这种定长元组上的字典序是良序。') },
    { h: bi('Because OD is a set.', '因为 OD 是一个集合。') },
  ],
  expl: bi('A descending sequence of keys would have eventually-constant α, then eventually-constant k (so a fixed length n), and then would descend in ordinal n-tuples, which is impossible. No choice is used, and OD is a proper class (it contains every ordinal).',
    '一个下降的关键字序列，α 最终会固定，然后 k 最终会固定（于是长度 n 固定），再往下就是在序数 n 元组中下降，这不可能。这里没用选择公理；而且 OD 是真类（它包含所有序数）。'),
});

/* ================= §6 reals: OD glasses ================= */
(function reals() {
  const svg = $('realsSvg');
  let uni = 'L', glasses = false;
  const NON = [3, 9, 14, 20, 27, 33, 38];
  const labels = { 0: '∅', 1: 'ω', 2: 'evens', 3: 'c', 9: 'ω∖c', 14: 'c△{0}', 6: '{0}', 17: 'primes' };
  const pos = i => [50 + (i % 8) * 46, 60 + Math.floor(i / 8) * 52];
  function info(i) {
    const non = uni === 'Lc' && NON.includes(i), lab = labels[i];
    if (non) okBox($('realsMsg'), bi(`${lab ? '<b>' + lab + '</b>' : 'This real'} is <b>not OD</b> in L[c]. It is a non-constructible real, and in L[c] the OD reals are exactly the constructible ones. Yet it is an element of the OD set ℝ.`, `${lab ? '<b>' + lab + '</b>' : '这个实数'}在 L[c] 中<b>不是 OD</b>。它是不可构成的实数，而 L[c] 中的 OD 实数恰好就是可构成的实数。但它是 OD 集合 ℝ 的元素。`), 'warn');
    else okBox($('realsMsg'), bi(`${lab ? '<b>' + lab + '</b>' : 'This real'} is OD${uni === 'Lc' ? ' (it is constructible, hence OD in L[c] as well)' : ' (in L every set is OD)'}.`, `${lab ? '<b>' + lab + '</b>' : '这个实数'}是 OD${uni === 'Lc' ? '（它可构成，所以在 L[c] 中也是 OD）' : '（在 L 中每个集合都是 OD）'}。`), 'ok');
  }
  function draw() {
    svg.innerHTML = '';
    el('rect', { x: 20, y: 22, width: 390, height: 290, rx: 18, fill: C.accentSoft, stroke: C.accent, 'stroke-width': 2 }, svg);
    txt(svg, 34, 44, 'ℝ = P(ω)   [OD ✓]', { 'font-size': 14, 'font-weight': 700, fill: C.accent });
    for (let i = 0; i < 40; i++) {
      const [x, y] = pos(i), non = uni === 'Lc' && NON.includes(i);
      const c = el('circle', { cx: x, cy: y + 10, r: 9, fill: non ? '#fff' : C.ok, stroke: non ? C.bad : C.ok, 'stroke-width': 2.5, style: 'cursor:pointer;transition:opacity .6s', opacity: glasses && non ? 0.07 : 1 }, svg);
      c.addEventListener('click', () => info(i));
      if (labels[i] && (non || !NON.includes(i) || uni === 'L')) {
        const t = txt(svg, x, y + 33, labels[i], { 'font-size': 11, 'text-anchor': 'middle', fill: non ? C.bad : C.muted, opacity: glasses && non ? 0.07 : 1 });
        t.style.transition = 'opacity .6s';
      }
    }
    const bx = 440;
    el('rect', { x: bx, y: 22, width: 260, height: 130, rx: 14, fill: C.okSoft, stroke: C.ok, 'stroke-width': 2 }, svg);
    txt(svg, bx + 12, 44, 'ℝ ∩ OD   [OD ✓]', { 'font-size': 13, 'font-weight': 700, fill: C.ok });
    for (let i = 0; i < 14; i++) el('circle', { cx: bx + 26 + (i % 7) * 34, cy: 76 + Math.floor(i / 7) * 36, r: 7, fill: C.ok }, svg);
    el('rect', { x: bx, y: 172, width: 260, height: 140, rx: 14, fill: C.badSoft, stroke: C.bad, 'stroke-width': 2 }, svg);
    txt(svg, bx + 12, 194, 'ℝ ∖ OD   [OD ✓]', { 'font-size': 13, 'font-weight': 700, fill: C.bad });
    if (uni === 'L') txt(svg, bx + 130, 250, '= ∅  (V = L ⇒ V = OD)', { 'font-size': 13, 'text-anchor': 'middle', fill: C.bad });
    else {
      for (let i = 0; i < 10; i++) {
        const c = el('circle', { cx: bx + 30 + (i % 5) * 48, cy: 228 + Math.floor(i / 5) * 40, r: 7, fill: '#fff', stroke: C.bad, 'stroke-width': 2.5, opacity: glasses ? 0.07 : 1 }, svg);
        c.style.transition = 'opacity .6s';
      }
      if (glasses) txt(svg, bx + 130, 260, 'looks like ∅ · 看起来像 ∅', { 'font-size': 13, 'text-anchor': 'middle', fill: C.bad, 'font-weight': 700, class: 'fadein' });
    }
    if (glasses) okBox($('realsMsg'), uni === 'L'
      ? bi('In L nothing disappears: V = L implies V = OD.', '在 L 中什么都不会消失：V = L 蕴涵 V = OD。')
      : bi('Through OD glasses the hollow reals vanish. <b>ℝ ∖ OD</b> now looks exactly like <b>∅</b>: two different OD sets with the same OD elements. So (OD, ∈) ⊭ Extensionality. Likewise ℝ and ℝ ∩ OD look identical.',
        '戴上 OD 眼镜，空心的实数都消失了。<b>ℝ ∖ OD</b> 现在看起来和 <b>∅</b> 一模一样：两个不同的 OD 集合，OD 元素却相同。所以 (OD, ∈) ⊭ 外延公理。同理，ℝ 与 ℝ ∩ OD 看起来也完全一样。'), uni === 'L' ? 'info' : 'warn');
  }
  seg($('realsSeg'), [
    { k: 'L', h: bi('Universe L', '宇宙 L') },
    { k: 'Lc', h: bi('Universe L[c]', '宇宙 L[c]') },
  ], k => {
    uni = k; glasses = false; draw();
    okBox($('realsMsg'), k === 'L' ? bi('In L every real is OD (filled). Click any dot.', '在 L 中每个实数都是 OD（实心）。点任意一个点。') : bi('In L[c] the hollow reals (c, ω∖c, c△{0}, …: every non-constructible real) are not OD. Click a dot, then try the glasses.', '在 L[c] 中，空心实数（c、ω∖c、c△{0}……即所有不可构成的实数）都不是 OD。点一个点，再试试眼镜。'), 'info');
  }, 1);
  $('realsGlasses').addEventListener('click', () => { glasses = !glasses; draw(); if (!glasses) clearBox($('realsMsg')); });
})();

mcq($('cy6'), {
  q: bi('In L[c], c ⊆ ω and every element of c is OD (a natural number). Is c ∈ OD?', '在 L[c] 中，c ⊆ ω，且 c 的每个元素都是 OD（自然数）。c ∈ OD 吗？'),
  opts: [
    { h: bi('Yes: a set whose elements are all OD is OD.', '是：元素都为 OD 的集合也是 OD。') },
    { ok: true, h: bi('No. Having only OD elements does not make a set OD.', '不是。元素都是 OD，并不能使集合本身成为 OD。') },
  ],
  expl: bi('OD fails in both directions. An OD set can have non-OD elements (ℝ ∋ c), and a set of OD elements can fail to be OD (c itself). OD is about defining the set as a whole, not about its elements.',
    'OD 两个方向都不成立：OD 集合可以有非 OD 元素（ℝ ∋ c）；元素全是 OD 的集合也可以不是 OD（c 本身）。OD 关心的是能否把集合作为整体定义出来，而不是它的元素。'),
});

/* ================= §7 HOD tree walk + cones ================= */
(function hodTree() {
  const svg = $('hodSvg');
  const nat = { l: '0, 1, 2, …', od: true };
  const P = [
    { k: 'a', h: '{∅, ω}', t: { l: '{∅, ω}', od: true, c: [{ l: '∅', od: true }, { l: 'ω', od: true, c: [nat] }] } },
    { k: 'b', h: 'ℝ', t: { l: 'ℝ', od: true, c: [{ l: 'OD reals', od: true, c: [nat] }, { l: 'c', od: false, c: [nat] }, { l: 'ω∖c, …', od: false }] } },
    { k: 'c', h: 'ℝ ∩ OD', t: { l: 'ℝ ∩ OD', od: true, c: [{ l: 'OD reals', od: true, c: [nat] }] } },
    { k: 'd', h: 'ℝ ∖ OD', t: { l: 'ℝ ∖ OD', od: true, c: [{ l: 'c, ω∖c, …', od: false, c: [nat] }] } },
    { k: 'e', h: '{c}', t: { l: '{c}', od: false, c: [{ l: 'c', od: false, c: [nat] }] } },
    { k: 'f', h: 'ω₁', t: { l: 'ω₁', od: true, c: [{ l: 'countable ordinals', od: true, c: [{ l: 'smaller ordinals', od: true }] }] } },
  ];
  let run = 0;
  async function walk(tree) {
    const my = ++run;
    svg.innerHTML = '';
    clearBox($('hodMsg'));
    const levels = [];
    const placed = new Set();
    (function lay(n, d) { if (placed.has(n)) return; placed.add(n); (levels[d] = levels[d] || []).push(n); (n.c || []).forEach(k => lay(k, d + 1)); })(tree, 0);
    levels.forEach((lv, d) => lv.forEach((n, i) => { n.x = 360 + (i - (lv.length - 1) / 2) * 175; n.y = 40 + d * 85; }));
    const edges = el('g', {}, svg);
    levels.forEach(lv => lv.forEach(n => (n.c || []).forEach(k => el('line', { x1: n.x, y1: n.y + 16, x2: k.x, y2: k.y - 16, stroke: '#9aa0aa', 'stroke-width': 2 }, edges))));
    const order = [].concat(...levels);
    order.forEach(n => {
      n.g = el('g', {}, svg);
      n.r = el('rect', { x: n.x - 70, y: n.y - 16, width: 140, height: 32, rx: 10, fill: '#fff', stroke: C.ink, 'stroke-width': 1.5 }, n.g);
      txt(n.g, n.x, n.y + 5, n.l, { 'font-size': 13, 'text-anchor': 'middle', 'font-weight': 700 });
    });
    let all = true;
    for (const n of order) {
      await sleep(420);
      if (my !== run) return;
      n.r.setAttribute('fill', n.od ? C.okSoft : C.badSoft);
      n.r.setAttribute('stroke', n.od ? C.ok : C.bad);
      txt(n.g, n.x + 60, n.y - 20, n.od ? 'OD ✓' : 'OD ✗', { 'font-size': 11, 'text-anchor': 'end', fill: n.od ? C.ok : C.bad, 'font-weight': 800, class: 'fadein' });
      if (!n.od) all = false;
    }
    const rootOD = tree.od;
    if (all) okBox($('hodMsg'), bi(`<b>${tree.l} ∈ HOD.</b> Every node of trcl({x}) is OD.`, `<b>${tree.l} ∈ HOD。</b>trcl({x}) 的每个节点都是 OD。`), 'ok');
    else okBox($('hodMsg'), rootOD
      ? bi(`<b>${tree.l} ∈ OD but ∉ HOD.</b> The top node is OD, but a red node below it is not.`, `<b>${tree.l} ∈ OD 但 ∉ HOD。</b>顶端节点是 OD，但下面有红色节点不是。`)
      : bi(`<b>${tree.l} ∉ OD, so ∉ HOD.</b>${tree.l === '{c}' ? ' If {c} were OD, then c = “the unique element of {c}” would be OD too.' : ''}`, `<b>${tree.l} ∉ OD，因此 ∉ HOD。</b>${tree.l === '{c}' ? '若 {c} 是 OD，则 c = “{c} 的唯一元素”也会是 OD。' : ''}`), 'bad');
  }
  btnBar($('hodTargets'), P.map(p => ({ k: p.t, h: p.h })), walk, 1);

  const cs = $('conesSvg');
  async function cones() {
    cs.innerHTML = '';
    const AX = 360, AY = 318, TOP = 22;
    const tri = (f, attrs) => el('polygon', Object.assign({ points: `${AX},${AY} ${AX - (AY - TOP) * f},${TOP} ${AX + (AY - TOP) * f},${TOP}` }, attrs), cs);
    tri(0.9, { fill: '#f4f1e8', stroke: '#c9c3b0', 'stroke-width': 2, class: 'fadein' });
    txt(cs, AX + 150, 110, 'V', { 'font-size': 18, 'font-weight': 700, class: 'fadein' });
    await sleep(500);
    const h = tri(0.55, { fill: C.okSoft, stroke: C.ok, 'stroke-width': 2, class: 'fadein' });
    txt(cs, AX + 50, 156, 'HOD', { 'font-size': 15, 'font-weight': 700, fill: C.ok, class: 'fadein' });
    txt(cs, 708, 300, 'HOD: transitive, ⊨ ZFC · 传递，⊨ ZFC', { 'font-size': 11, fill: C.ok, 'text-anchor': 'end', class: 'fadein' });
    await sleep(500);
    tri(0.22, { fill: C.accentSoft, stroke: C.accent, 'stroke-width': 2, class: 'fadein' });
    txt(cs, AX + 12, 156, 'L', { 'font-size': 15, 'font-weight': 700, fill: C.accent, class: 'fadein' });
    el('line', { x1: AX, y1: AY, x2: AX, y2: TOP, stroke: C.ink, 'stroke-width': 1.2 }, cs);
    txt(cs, 708, 282, 'spine = Ord ⊆ L ⊆ HOD · 中轴＝Ord', { 'font-size': 11, fill: C.ink, 'text-anchor': 'end' });
    await sleep(500);
    const pts = [[-1, 60], [1, 85], [-1, 120], [1, 150], [-1, 175], [1, 205], [-1, 225]].map(([s, y]) => [s * 0.72 * (AY - y), y]);
    pts.forEach(([dx, y], i) => {
      const c = el('circle', { cx: AX + dx, cy: y, r: 6, fill: C.gold, stroke: '#b36200', 'stroke-width': 1.5, class: 'pop' }, cs);
      c.style.animationDelay = (i * 0.08) + 's';
    });
    txt(cs, 12, 300, '● OD ∖ HOD, e.g. ℝ in L[c] · OD 但不属于 HOD', { 'font-size': 11, fill: '#b36200', class: 'fadein' });
    void h;
  }
  $('conesGo').addEventListener('click', cones);
  cones();
})();

mcq($('cy7'), {
  q: bi('Which inclusions hold in every model of ZF?', '在 ZF 的每个模型中，哪些包含关系成立？'),
  opts: [
    { h: bi('OD ⊆ HOD', 'OD ⊆ HOD') },
    { ok: true, h: bi('HOD ⊆ OD and L ⊆ HOD', 'HOD ⊆ OD 且 L ⊆ HOD') },
    { h: bi('HOD ⊆ L', 'HOD ⊆ L') },
  ],
  expl: bi('HOD ⊆ OD by definition (x ∈ trcl({x})). L ⊆ HOD because HOD is an inner model of ZF and L is the least one. OD ⊆ HOD fails in L[c] (ℝ). HOD ⊆ L fails e.g. in L[0<sup>#</sup>] if 0<sup>#</sup> exists, or in McAloon\'s model (Step 9).',
    'HOD ⊆ OD 由定义即得（x ∈ trcl({x})）。L ⊆ HOD，因为 HOD 是 ZF 的内模型，而 L 是最小的内模型。OD ⊆ HOD 在 L[c] 中不成立（ℝ）。HOD ⊆ L 也可能不成立，例如 0<sup>#</sup> 存在时的 L[0<sup>#</sup>]，或 McAloon 的模型（第 9 步）。'),
});

/* ================= §8 symmetric model: supports ================= */
(function sym() {
  const svg = $('symSvg');
  const N = 8, CX = 170, CY = 150, R = 105;
  const slot = i => [CX + R * Math.cos(-Math.PI / 2 + i * 2 * Math.PI / N), CY + R * Math.sin(-Math.PI / 2 + i * 2 * Math.PI / N)];
  const pinned = new Set([0]);
  let at = [...Array(N).keys()];   // at[i] = slot currently holding a_i
  let lastPi = null;
  el('circle', { cx: CX, cy: CY, r: R, fill: 'none', stroke: C.line, 'stroke-dasharray': '4 4' }, svg);
  txt(svg, CX, CY - 4, 'A = {a₀, a₁, …}', { 'font-size': 14, 'text-anchor': 'middle', 'font-weight': 700 });
  txt(svg, CX, CY + 16, 'click = pin · 点击＝钉住', { 'font-size': 11, 'text-anchor': 'middle', fill: C.muted });
  txt(svg, CX, 292, '(only 8 drawn; A is infinite · 只画了 8 个，A 是无穷的)', { 'font-size': 10.5, 'text-anchor': 'middle', fill: C.muted });
  const nodes = [...Array(N).keys()].map(i => {
    const g = el('g', { style: 'cursor:pointer;transition:transform .9s cubic-bezier(.3,1.2,.4,1)' }, svg);
    const c = el('circle', { r: 20, fill: '#fff', stroke: C.ink, 'stroke-width': 2 }, g);
    txt(g, 0, 5, 'a' + '₀₁₂₃₄₅₆₇'[i], { 'font-size': 14, 'text-anchor': 'middle', 'font-weight': 700 });
    const pin = txt(g, 14, -14, '📌', { 'font-size': 14 });
    g.addEventListener('click', () => { if (pinned.has(i)) pinned.delete(i); else pinned.add(i); lastPi = null; paint(); });
    return { g, c, pin };
  });
  function paint() {
    nodes.forEach((n, i) => {
      const [x, y] = slot(at[i]);
      n.g.style.transform = `translate(${x}px, ${y}px)`;
      n.c.setAttribute('fill', pinned.has(i) ? C.metaSoft : '#fff');
      n.c.setAttribute('stroke', pinned.has(i) ? C.meta : C.ink);
      n.pin.style.display = pinned.has(i) ? '' : 'none';
    });
    table();
  }
  function table() {
    const moved = lastPi && lastPi.some((j, i) => j !== i);
    const pins = [...pinned].sort((a, b) => a - b).map(i => 'a' + '₀₁₂₃₄₅₆₇'[i]);
    const free = [...Array(N).keys()].filter(i => !pinned.has(i));
    const fx = free.length ? 'a' + '₀₁₂₃₄₅₆₇'[free[0]] : '—';
    const row = (obj, fixed, en, zh) => `<tr><td class="m">${obj}</td><td class="${fixed === null ? '' : fixed ? 'right' : 'wrong'}">${fixed === null ? '—' : fixed ? bil('fixed ✓', '不动 ✓') : bil('moved ✗', '被移动 ✗')}</td><td>${bil(en, zh)}</td></tr>`;
    const st = v => (lastPi ? v : null);
    $('symTable').innerHTML = `<table class="odt"><tr><th>${bil('object', '对象')}</th><th>${bil('after π', '经 π 作用后')}</th><th>${bil('in N?', '在 N 中？')}</th></tr>` +
      row('A', st(true), 'yes (support ∅)', '是（支撑 ∅）') +
      row(pins.length ? `{${pins.join(', ')}}` : '∅', st(true), 'yes (support = the pins)', '是（支撑 = 钉住的元素）') +
      row(`{${fx}}`, st(!moved || (lastPi && free.length && lastPi[free[0]] === free[0])), `yes, but its support must contain ${fx}`, `是，但它的支撑必须包含 ${fx}`) +
      row('a₀ ◁ a₁ ◁ a₂ ◁ …', st(!moved), 'no well-ordering of A has a finite support', 'A 的任何良序都没有有限支撑') + '</table>';
  }
  $('symGo').addEventListener('click', () => {
    const free = [...Array(N).keys()].filter(i => !pinned.has(i));
    if (free.length < 2) {
      okBox($('symMsg'), bi('Leave at least two a\'s unpinned. In the real model A is infinite, so any finite support leaves infinitely many free.', '至少留两个 a 不钉。在真正的模型中 A 是无穷的，任何有限支撑之外都还剩无穷多个自由元素。'), 'warn');
      return;
    }
    let img;
    do { img = free.slice().sort(() => Math.random() - 0.5); } while (img.every((v, k) => v === free[k]));
    const pi = [...Array(N).keys()];
    free.forEach((v, k) => { pi[v] = img[k]; });
    lastPi = pi;
    const nat = at.slice();
    for (let i = 0; i < N; i++) at[i] = nat[pi[i]];
    paint();
    const desc = free.filter(i => pi[i] !== i).map(i => `a${'₀₁₂₃₄₅₆₇'[i]}↦a${'₀₁₂₃₄₅₆₇'[pi[i]]}`).join(', ');
    okBox($('symMsg'), bi(`π: ${desc}. A and everything supported by the pins is unchanged. The ordering a₀ ◁ a₁ ◁ … is moved. Every pin set is finite, so some π like this always exists, and no well-ordering of A belongs to N.`,
      `π：${desc}。A 以及以钉子为支撑的一切都不变，但序 a₀ ◁ a₁ ◁ … 被移动了。钉子集总是有限的，所以总有这样的 π，于是 A 的任何良序都不在 N 中。`), 'info');
  });
  $('symClear').addEventListener('click', () => { pinned.clear(); lastPi = null; paint(); });
  paint();
})();

mcq($('cy8'), {
  q: bi('Does the proof that HOD ⊨ AC use the Axiom of Choice in V?', '证明 HOD ⊨ AC 时，用到 V 中的选择公理了吗？'),
  opts: [
    { h: bi('Yes, to choose a definition for each OD set.', '用到了，为每个 OD 集合选一个定义。') },
    { ok: true, h: bi('No. The least definition is picked canonically, so ZF ⊢ “HOD ⊨ AC”.', '没有。最小定义是规范地取出的，所以 ZF ⊢ “HOD ⊨ AC”。') },
    { h: bi('Only for uncountable sets.', '只在不可数集合上用到。') },
  ],
  expl: bi('“The least key” is a definable choice-free selection. That is why HOD gives Con(ZF) ⇒ Con(ZFC), and why even Cohen\'s ¬AC model N has HOD<sup>N</sup> ⊨ ZFC.',
    '“最小关键字”是一种可定义、不用选择的挑选方式。正因如此，HOD 能给出 Con(ZF) ⇒ Con(ZFC)；即使在科恩的 ¬AC 模型 N 中，也有 HOD<sup>N</sup> ⊨ ZFC。'),
});

/* ================= §9 universes ================= */
(function universes() {
  const svg = $('uniSvg');
  const AX = 360, AY = 290, TOP = 30;
  let cur = { V: 0.9, H: 0.9, H2: 0.9, L: 0.9 }, anim = 0;
  const U = {
    L: { f: { V: 0.9, H: 0.9, H2: 0.9, L: 0.9 }, lab: 'V = HOD = L',
      m: bi('<span class="status thm">ZF ⊢</span> V = L ⇒ V = HOD = OD. The order &lt;<sub>L</sub> is a parameter-free definable well-ordering of V.', '<span class="status thm">ZF ⊢</span> V = L ⇒ V = HOD = OD。&lt;<sub>L</sub> 是 V 上无参数可定义的良序。') },
    Lc: { f: { V: 0.9, H: 0.3, H2: 0.3, L: 0.3 }, lab: 'L = HOD ⊊ V = L[c]',
      m: bi('<span class="status con">Con(ZF) ⇒ Con</span> Let c be Cohen over L. In L[c], HOD = L: Cohen forcing is weakly homogeneous and OD, so HOD<sup>L[c]</sup> ⊆ HOD<sup>L</sup> = L. Since c ∉ HOD, L[c] ⊨ ZFC + V ≠ HOD. So <b>AC does not imply V = HOD</b>.',
        '<span class="status con">Con(ZF) ⇒ Con</span> 设 c 是 L 上的科恩实数。在 L[c] 中 HOD = L：科恩力迫弱齐性且是 OD，故 HOD<sup>L[c]</sup> ⊆ HOD<sup>L</sup> = L。由于 c ∉ HOD，L[c] ⊨ ZFC + V ≠ HOD。所以 <b>AC 不蕴涵 V = HOD</b>。') },
    Mc: { f: { V: 0.9, H: 0.9, H2: 0.9, L: 0.3 }, lab: 'L ⊊ HOD = V',
      m: bi('<span class="status con">Con(ZF) ⇒ Con</span> <b>McAloon (1971).</b> Force over L, coding the generic G into the pattern of the continuum function at regular cardinals. Then G is OD, every element of L[G] is definable from G and ordinals, and L[G] ⊨ V = HOD while G ∉ L. So <b>V = HOD does not imply V = L</b>. (Without forcing, if 0<sup>#</sup> exists then L[0<sup>#</sup>] ⊨ V = HOD ≠ L.)',
        '<span class="status con">Con(ZF) ⇒ Con</span> <b>McAloon（1971）.</b> 在 L 上力迫，把泛型 G 编码进正则基数处连续统函数的取值模式。于是 G 是 OD，L[G] 的每个元素都由 G 和序数可定义，故 L[G] ⊨ V = HOD，而 G ∉ L。所以 <b>V = HOD 不蕴涵 V = L</b>。（不用力迫也有例子：若 0<sup>#</sup> 存在，则 L[0<sup>#</sup>] ⊨ V = HOD ≠ L。）') },
    Z: { f: { V: 0.9, H: 0.58, H2: 0.58, L: 0.3 }, lab: 'L ⊊ HOD ⊊ V',
      m: bi('<span class="status cond">if 0<sup>#</sup> exists</span> Let c be Cohen over L[0<sup>#</sup>]. In L[0<sup>#</sup>][c], 0<sup>#</sup> is still OD (its definition is absolute), so L[0<sup>#</sup>] ⊆ HOD. Homogeneity gives HOD ⊆ HOD<sup>L[0#]</sup> = L[0<sup>#</sup>]. Hence HOD = L[0<sup>#</sup>], strictly between L and V.',
        '<span class="status cond">若 0<sup>#</sup> 存在</span> 设 c 是 L[0<sup>#</sup>] 上的科恩实数。在 L[0<sup>#</sup>][c] 中 0<sup>#</sup> 仍是 OD（它的定义是绝对的），故 L[0<sup>#</sup>] ⊆ HOD；由齐性，HOD ⊆ HOD<sup>L[0#]</sup> = L[0<sup>#</sup>]。所以 HOD = L[0<sup>#</sup>]，严格介于 L 与 V 之间。') },
    it: { f: { V: 0.9, H: 0.66, H2: 0.44, L: 0.22 }, lab: 'V ⊋ HOD ⊋ HOD^HOD ⊋ …',
      m: bi('<span class="status con">Con</span> <b>McAloon (1974)</b>: models in which HOD<sup>n+1</sup> = HOD<sup>HOD<sup>n</sup></sup> strictly decreases for all n &lt; ω. In particular HOD ⊭ “V = HOD” is possible. Compare L ⊨ “V = L”, which always holds.',
        '<span class="status con">Con</span> <b>McAloon（1974）</b>：存在模型，其中 HOD<sup>n+1</sup> = HOD<sup>HOD<sup>n</sup></sup> 对所有 n &lt; ω 严格递减。特别地，HOD ⊭ “V = HOD” 是可能的。对比：L ⊨ “V = L” 总是成立。') },
  };
  let key = 'L';
  function draw(f) {
    svg.innerHTML = '';
    const tri = (w, attrs) => el('polygon', Object.assign({ points: `${AX},${AY} ${AX - (AY - TOP) * w},${TOP} ${AX + (AY - TOP) * w},${TOP}` }, attrs), svg);
    tri(f.V, { fill: '#f4f1e8', stroke: '#c9c3b0', 'stroke-width': 2 });
    tri(f.H, { fill: C.okSoft, stroke: C.ok, 'stroke-width': 2, opacity: 0.95 });
    if (key === 'it') tri(f.H2, { fill: '#b2f2bb', stroke: C.ok, 'stroke-width': 1.5, 'stroke-dasharray': '4 3' });
    tri(f.L, { fill: C.accentSoft, stroke: C.accent, 'stroke-width': 2 });
    el('line', { x1: AX, y1: AY, x2: AX, y2: TOP, stroke: C.ink, 'stroke-width': 1 }, svg);
    const lx = w => AX + (AY - TOP) * w * 0.82;
    txt(svg, lx(f.V) + 8, TOP + 26, 'V', { 'font-size': 16, 'font-weight': 700 });
    if (Math.abs(f.H - f.V) > 0.05) txt(svg, lx(f.H) - 6, TOP + 46, 'HOD', { 'font-size': 14, 'font-weight': 700, fill: C.ok });
    if (key === 'it') txt(svg, lx(f.H2) - 10, TOP + 66, 'HOD^HOD', { 'font-size': 12, 'font-weight': 700, fill: C.ok, 'text-anchor': 'end' });
    if (Math.abs(f.L - f.H) > 0.05) txt(svg, AX + 6, TOP + 86, key === 'it' ? '…' : 'L', { 'font-size': 14, 'font-weight': 700, fill: C.accent });
    txt(svg, 20, 24, U[key].lab, { 'font-size': 15, 'font-weight': 800, fill: C.ink });
    if (key === 'Lc') { el('circle', { cx: AX + 170, cy: 120, r: 7, fill: '#fff', stroke: C.bad, 'stroke-width': 2.5 }, svg); txt(svg, AX + 182, 124, 'c ∉ HOD', { 'font-size': 12, fill: C.bad, 'font-weight': 700 }); }
    if (key === 'Mc') { el('circle', { cx: AX + 140, cy: 120, r: 7, fill: C.ok }, svg); txt(svg, AX + 152, 124, 'G ∈ HOD ∖ L', { 'font-size': 12, fill: C.ok, 'font-weight': 700 }); }
    if (key === 'Z') { el('circle', { cx: AX + 70, cy: 110, r: 6, fill: C.ok }, svg); txt(svg, AX + 80, 114, '0#', { 'font-size': 12, fill: C.ok, 'font-weight': 700 });
      el('circle', { cx: AX + 190, cy: 120, r: 7, fill: '#fff', stroke: C.bad, 'stroke-width': 2.5 }, svg); txt(svg, AX + 202, 124, 'c', { 'font-size': 12, fill: C.bad, 'font-weight': 700 }); }
  }
  async function go(k) {
    key = k;
    const my = ++anim, from = Object.assign({}, cur), to = U[k].f;
    okBox($('uniMsg'), U[k].m, 'info');
    for (let s = 1; s <= 18; s++) {
      if (my !== anim) return;
      const e = s / 18, t = e * e * (3 - 2 * e);
      for (const q in cur) cur[q] = from[q] + (to[q] - from[q]) * t;
      draw(cur);
      await sleep(28);
    }
  }
  seg($('uniSeg'), [
    { k: 'L', h: 'V = L' }, { k: 'Lc', h: 'L[c]' }, { k: 'Mc', h: bi('McAloon 1971', 'McAloon 1971') },
    { k: 'Z', h: 'L[0#][c]' }, { k: 'it', h: bi('iterated HOD', '迭代 HOD') },
  ], go);
})();

mcq($('cy9'), {
  q: bi('Which is a theorem of ZF?', '哪一项是 ZF 的定理？'),
  opts: [
    { h: bi('HOD ⊨ “V = HOD”.', 'HOD ⊨ “V = HOD”。') },
    { ok: true, h: bi('If V = HOD then HOD ⊨ “V = HOD”.', '若 V = HOD，则 HOD ⊨ “V = HOD”。') },
    { h: bi('AC ⇒ V = HOD.', 'AC ⇒ V = HOD。') },
  ],
  expl: bi('If V = HOD then HOD<sup>HOD</sup> = HOD<sup>V</sup> = HOD, trivially. In general HOD<sup>HOD</sup> may be smaller (McAloon), and AC ⇏ V = HOD (L[c]).',
    '若 V = HOD，则 HOD<sup>HOD</sup> = HOD<sup>V</sup> = HOD，显然成立。一般情况下 HOD<sup>HOD</sup> 可能更小（McAloon），且 AC ⇏ V = HOD（L[c]）。'),
});

/* ================= §10 dichotomy ================= */
(function dichotomy() {
  const svg = $('dichSvg');
  const box = (x, y, w, h, l1, l2, col, soft) => {
    const g = el('g', { style: 'cursor:pointer' }, svg);
    const r = el('rect', { x: x - w / 2, y, width: w, height: h, rx: 12, fill: soft, stroke: col, 'stroke-width': 2 }, g);
    txt(g, x, y + 22, l1, { 'font-size': 14, 'text-anchor': 'middle', 'font-weight': 700, fill: col });
    if (l2) txt(g, x, y + 42, l2, { 'font-size': 11.5, 'text-anchor': 'middle', fill: C.ink });
    return { g, r };
  };
  el('path', { d: 'M360,66 C360,100 180,90 180,128', fill: 'none', stroke: C.ink, 'stroke-width': 2 }, svg);
  el('path', { d: 'M360,66 C360,100 540,90 540,128', fill: 'none', stroke: C.ink, 'stroke-width': 2 }, svg);
  const root = box(360, 14, 260, 52, 'δ extendible · δ 可扩张', 'exactly one of · 恰有一个成立', C.ink, '#fff');
  const b1 = box(180, 128, 300, 58, '(1) HOD close to V · 靠近 V', 'singular γ>δ stay singular, γ⁺ correct', C.ok, C.okSoft);
  const b2 = box(540, 128, 300, 58, '(2) HOD far from V · 远离 V', 'every regular >δ measurable in HOD', C.bad, C.badSoft);
  txt(svg, 180, 214, 'HOD Conjecture: always (1) · HOD 猜想：总是 (1)', { 'font-size': 12, 'text-anchor': 'middle', fill: C.ok, 'font-weight': 700 });
  el('rect', { x: 130, y: 222, width: 100, height: 20, rx: 10, fill: C.bad }, svg);
  txt(svg, 180, 236, 'OPEN · 未解决', { 'font-size': 11.5, 'text-anchor': 'middle', fill: '#fff', 'font-weight': 800 });
  el('path', { d: 'M540,268 L540,192', stroke: C.gold, 'stroke-width': 2, 'stroke-dasharray': '5 4', fill: 'none', 'marker-end': 'url(#dArrow)' }, svg);
  const defs = el('defs', {}, svg);
  const mk = el('marker', { id: 'dArrow', viewBox: '0 0 10 10', refX: 8, refY: 5, markerWidth: 7, markerHeight: 7, orient: 'auto' }, defs);
  el('path', { d: 'M0,0 L10,5 L0,10 z', fill: C.gold }, mk);
  txt(svg, 700, 284, 'exacting above an extendible (ABL 2024) ⇒ (2)', { 'font-size': 11.5, 'text-anchor': 'end', fill: C.gold, 'font-weight': 700 });
  txt(svg, 700, 298, 'consistency unknown · 一致性未知', { 'font-size': 11, 'text-anchor': 'end', fill: C.gold });
  const msgs = {
    root: bi('<span class="status thm">Theorem</span> Woodin\'s HOD Dichotomy needs an extendible cardinal δ. Its conclusion is that HOD is either very close to V or very far from it. There is no middle ground above δ.', '<span class="status thm">定理</span> Woodin 的 HOD 二分定理需要一个可扩张基数 δ。结论是：HOD 要么离 V 很近，要么离 V 很远，在 δ 之上没有中间状态。'),
    b1: bi('<b>Case (1).</b> HOD correctly computes successors of singular cardinals above δ and keeps them singular, a covering-like property. HOD is then a weak extender model for “δ is supercompact”. The HOD Conjecture predicts that this case always holds. <span class="status open">OPEN</span>', '<b>情形 (1).</b> HOD 正确计算 δ 之上奇异基数的后继，并保持它们奇异，这是一种类似覆盖的性质。此时 HOD 是“δ 超紧”的弱扩张子模型。HOD 猜想预言总是这种情形。<span class="status open">未解决</span>'),
    b2: bi('<b>Case (2).</b> Every regular cardinal above δ is measurable in HOD (in fact ω-strongly measurable). This is analogous to “0<sup>#</sup> exists” for L, where every uncountable cardinal is inaccessible in L. Woodin showed that case (2) is absolute between V and its forcing extensions by posets in V<sub>δ</sub>, so such small forcing can neither create nor destroy it. Aguilera–Bagaria–Lücke (2024–25) showed that an exacting cardinal above an extendible yields case (2); whether that is consistent is unknown.', '<b>情形 (2).</b> δ 之上的每个正则基数在 HOD 中都是可测的（事实上是 ω-强可测的）。这类似于 L 的“0<sup>#</sup> 存在”：那时每个不可数基数在 L 中都是不可达的。Woodin 证明了情形 (2) 在 V 与其由 V<sub>δ</sub> 中偏序集得到的力迫扩张之间是绝对的，所以这种小力迫既造不出它，也消灭不了它。Aguilera–Bagaria–Lücke（2024–25）证明可扩张基数之上的 exacting 基数会导致情形 (2)；但这是否一致，目前未知。'),
  };
  const all = [root, b1, b2];
  [[root, 'root'], [b1, 'b1'], [b2, 'b2']].forEach(([b, k]) => b.g.addEventListener('click', () => {
    all.forEach(x => x.r.setAttribute('stroke-width', 2));
    b.r.setAttribute('stroke-width', 4.5);
    okBox($('dichMsg'), msgs[k], 'info');
  }));
  okBox($('dichMsg'), msgs.root, 'info');
})();

mcq($('cy10'), {
  q: bi('What is the status of the HOD Conjecture?', 'HOD 猜想目前的状态是什么？'),
  opts: [
    { h: bi('A theorem of ZFC + “there is an extendible cardinal”.', '是 ZFC + “存在可扩张基数”的定理。') },
    { ok: true, h: bi('Open. Woodin proved the dichotomy, not which side holds.', '尚未解决。Woodin 证明的是二分定理，而不是哪一边成立。') },
    { h: bi('Refuted outright by Aguilera–Bagaria–Lücke.', '已被 Aguilera–Bagaria–Lücke 彻底推翻。') },
  ],
  expl: bi('The refutation by Aguilera–Bagaria–Lücke is conditional on the consistency of an exacting cardinal above an extendible, which is not known.', 'Aguilera–Bagaria–Lücke 的反驳是有条件的：它依赖于“可扩张基数之上存在 exacting 基数”的一致性，而这一点尚不清楚。'),
});

/* ================= E1 ================= */
(function e1() {
  const rows = [
    { s: 'ω', od: 1, hod: 1, en: 'Parameter-free definable; its elements are natural numbers, all OD.', zh: '无参数可定义；元素是自然数，都是 OD。' },
    { s: '{∅, ω}', od: 1, hod: 1, en: 'Definable from ∅ and ω; trcl = {∅, ω} ∪ ω, all OD.', zh: '由 ∅ 和 ω 可定义；传递闭包 = {∅, ω} ∪ ω，全是 OD。' },
    { s: 'ω₁', od: 1, hod: 1, en: 'An ordinal; every ordinal is in HOD.', zh: '是序数；每个序数都在 HOD 中。' },
    { s: bil('0<sup>#</sup> (assume it exists)', '0<sup>#</sup>（假设存在）'), od: 1, hod: 1, en: '0<sup>#</sup> is definable in V without parameters (the unique well-founded remarkable EM blueprint). It is a real (a set of natural numbers), so it is in HOD, and it is not in L.', zh: '0<sup>#</sup> 在 V 中无参数可定义（唯一良基且满足 remarkable 条件的 EM 蓝图）。它是实数（自然数集），所以在 HOD 中，但不在 L 中。' },
    { s: bil('ℝ, in L[c]', 'L[c] 中的 ℝ'), od: 1, hod: 0, en: 'OD (parameter-free), but c ∈ ℝ is not OD.', zh: '是 OD（无参数可定义），但 c ∈ ℝ 不是 OD。' },
    { s: bil('c, in L[c]', 'L[c] 中的 c'), od: 0, hod: 0, en: 'HOD<sup>L[c]</sup> = L by homogeneity, and for a real, OD ⇔ HOD.', zh: '由齐性 HOD<sup>L[c]</sup> = L；对实数而言 OD ⇔ HOD。' },
    { s: bil('ℝ ∩ OD, in L[c]', 'L[c] 中的 ℝ ∩ OD'), od: 1, hod: 1, en: 'Definable (OD is a definable class); its elements are OD reals, which are in HOD.', zh: '可定义（OD 是可定义类）；元素是 OD 实数，它们都在 HOD 中。' },
    { s: bil('ℝ ∖ OD, in L[c]', 'L[c] 中的 ℝ ∖ OD'), od: 1, hod: 0, en: 'Definable, but none of its elements is OD.', zh: '可定义，但它的元素没有一个是 OD。' },
    { s: bil('{c}, in L[c]', 'L[c] 中的 {c}'), od: 0, hod: 0, en: 'If {c} were OD, c = “the element of {c}” would be OD.', zh: '若 {c} 是 OD，则 c = “{c} 的元素”也会是 OD。' },
  ];
  const state = rows.map(() => ({ od: null, hod: null }));
  let revealed = false;
  const lab = v => v === null ? '?' : v ? bil('yes', '是') : bil('no', '否');
  let h = `<table class="odt"><tr><th>${bil('set', '集合')}</th><th>OD</th><th>HOD</th><th></th></tr>`;
  rows.forEach((r, i) => {
    h += `<tr><td class="m">${r.s}</td><td class="ans" data-i="${i}" data-f="od"><button class="btn small tog">?</button></td><td class="ans" data-i="${i}" data-f="hod"><button class="btn small tog">?</button></td><td class="muted" style="font-size:13px" id="e1x${i}"></td></tr>`;
  });
  $('e1Table').innerHTML = h + '</table>';
  $('e1Table').querySelectorAll('td.ans').forEach(td => {
    const b = td.querySelector('button'), i = +td.dataset.i, f = td.dataset.f;
    b.addEventListener('click', () => {
      const v = state[i][f];
      state[i][f] = v === null ? 1 : v === 1 ? 0 : null;
      b.innerHTML = lab(state[i][f]);
      td.classList.remove('right', 'wrong');
    });
  });
  function check(reveal) {
    if (reveal) revealed = true;
    let ok = 0, bad = false;
    $('e1Table').querySelectorAll('td.ans').forEach(td => {
      const i = +td.dataset.i, f = td.dataset.f;
      if (reveal) { state[i][f] = rows[i][f]; td.querySelector('button').innerHTML = lab(rows[i][f]); }
      td.classList.remove('right', 'wrong');
      if (state[i][f] === rows[i][f]) { ok++; td.classList.add('right'); } else if (state[i][f] !== null) td.classList.add('wrong');
    });
    rows.forEach((r, i) => {
      if (state[i].hod === 1 && state[i].od === 0) bad = true;
      if (reveal || (state[i].od === r.od && state[i].hod === r.hod)) $('e1x' + i).innerHTML = bi(r.en, r.zh);
    });
    const total = rows.length * 2;
    if (reveal) okBox($('e1Msg'), bi('Answers filled in, with reasons.', '已填入答案及理由。'), 'info');
    else if (ok === total) { okBox($('e1Msg'), bi('✓ All correct. Pattern: OD is about the top level, HOD about every level.', '✓ 全对。规律：OD 只看最上面一层，HOD 要看每一层。')); if (!revealed) Progress.mark('L22E1'); }
    else okBox($('e1Msg'), bi(`${ok} / ${total} correct.${bad ? ' Note: HOD ⊆ OD, so “HOD yes, OD no” is impossible.' : ''}`, `${ok} / ${total} 正确。${bad ? '注意：HOD ⊆ OD，所以“HOD 是、OD 否”不可能。' : ''}`), 'warn');
  }
  $('e1Check').addEventListener('click', () => check(false));
  $('e1Show').addEventListener('click', () => check(true));
})();

/* ================= E2 ================= */
(function e2() {
  const items = [
    { id: 'A', en: 'Fix a formula φ(z, ȳ) in the metatheory; in ZF take ordinals <span class="ov">β</span> and x with ∀z (φ(z, <span class="ov">β</span>) ↔ z = x).', zh: '在元理论中固定公式 φ(z, ȳ)；在 ZF 中取序数 <span class="ov">β</span> 和 x，使 ∀z (φ(z, <span class="ov">β</span>) ↔ z = x)。' },
    { id: 'B', en: 'Apply the reflection theorem to φ: get α > rank(x), <span class="ov">β</span> with φ absolute between V<sub>α</sub> and V.', zh: '对 φ 用反射原理：得到 α > rank(x), <span class="ov">β</span>，使 φ 在 V<sub>α</sub> 与 V 之间绝对。' },
    { id: 'C', en: 'Conclude: x is the unique z ∈ V<sub>α</sub> with φ<sup>V<sub>α</sub></sup>(z, <span class="ov">β</span>).', zh: '得出：x 是 V<sub>α</sub> 中唯一满足 φ<sup>V<sub>α</sub></sup>(z, <span class="ov">β</span>) 的 z。' },
    { id: 'D', en: 'Replace φ<sup>V<sub>α</sub></sup> by Sat(V<sub>α</sub>, ∈, ⌜φ⌝, z, <span class="ov">β</span>); legitimate because V<sub>α</sub> is a set.', zh: '把 φ<sup>V<sub>α</sub></sup> 换成 Sat(V<sub>α</sub>, ∈, ⌜φ⌝, z, <span class="ov">β</span>)；因为 V<sub>α</sub> 是集合，这是合法的。' },
    { id: 'E', en: 'So (α, ⌜φ⌝, <span class="ov">β</span>) witnesses the single formula “x ∈ OD”.', zh: '于是 (α, ⌜φ⌝, <span class="ov">β</span>) 见证了单独一条公式“x ∈ OD”。' },
    { id: 'F', en: 'Use the truth predicate Sat<sub>V</sub>(⌜φ⌝, ā) for V itself.', zh: '使用 V 本身的真谓词 Sat<sub>V</sub>(⌜φ⌝, ā)。' },
  ];
  const right = ['A', 'B', 'C', 'D', 'E'];
  let done = [];
  let revealed = false;
  const shuffled = items.slice().sort(() => Math.random() - 0.5);
  function render() {
    $('e2Pool').innerHTML = `<div class="muted" style="font-size:13px">${bil('Pool (click to append)', '候选（点击追加）')}</div>`;
    $('e2Done').innerHTML = `<div class="muted" style="font-size:13px">${bil('Your proof (click to remove)', '你的证明（点击移除）')}</div>`;
    shuffled.filter(it => !done.includes(it.id)).forEach(it => {
      const d = document.createElement('div'); d.className = 'chip'; d.innerHTML = bi(it.en, it.zh);
      d.addEventListener('click', () => { done.push(it.id); render(); clearBox($('e2Msg')); });
      $('e2Pool').appendChild(d);
    });
    done.forEach((id, k) => {
      const it = items.find(x => x.id === id);
      const d = document.createElement('div'); d.className = 'chip'; d.style.cursor = 'pointer';
      d.innerHTML = `<span class="n">${k + 1}.</span>` + bi(it.en, it.zh);
      d.addEventListener('click', () => { done = done.filter(x => x !== id); render(); clearBox($('e2Msg')); });
      $('e2Done').appendChild(d);
    });
  }
  render();
  $('e2Check').addEventListener('click', () => {
    if (done.includes('F')) { okBox($('e2Msg'), bi('✗ The step “use Sat<sub>V</sub>” is impossible: no such formula exists (Tarski). The whole point is to avoid it.', '✗ “使用 Sat<sub>V</sub>”这一步做不到：这样的公式不存在（塔斯基）。整个证明的要点就是绕开它。'), 'bad'); return; }
    if (done.join('') === right.join('')) { okBox($('e2Msg'), bi('✓ Correct. Reflection (step 2) is used once, for this particular φ. That is why the result is a schema.', '✓ 正确。反射（第 2 步）只针对这一个 φ 用了一次，所以结论是一个模式。')); if (!revealed) Progress.mark('L22E2'); }
    else okBox($('e2Msg'), bi(`Not yet (${done.length}/5 steps placed). The statement about V must be reflected before anything about V<sub>α</sub> can be concluded.`, `还不对（已放 ${done.length}/5 步）。必须先把关于 V 的命题反射下去，才能得出关于 V<sub>α</sub> 的结论。`), 'warn');
  });
  $('e2Reset').addEventListener('click', () => { done = []; render(); clearBox($('e2Msg')); });
  $('e2Show').addEventListener('click', () => { revealed = true; done = right.slice(); render(); okBox($('e2Msg'), bi('Order: A, B, C, D, E. Step F is a distractor: Sat<sub>V</sub> does not exist.', '顺序：A、B、C、D、E。F 是干扰项：Sat<sub>V</sub> 并不存在。'), 'info'); });
})();

/* ================= E3 ================= */
(function e3() {
  const box = $('e3Box');
  const a = document.createElement('div'), b = document.createElement('div');
  box.appendChild(a); box.appendChild(b);
  const solved = [false, false];
  const fin = i => () => { solved[i] = true; if (solved[0] && solved[1]) Progress.mark('L22E3'); };
  mcq(a, {
    head: bil('(a) Choose the best explanation', '(a) 选出最好的解释'),
    q: bi('Tarski says truth in V is not definable. Why is the definition of OD nevertheless legitimate?', '塔斯基说 V 中的真不可定义。为什么 OD 的定义仍然合法？'),
    opts: [
      { h: bi('Tarski only concerns parameter-free definitions, and OD uses ordinal parameters.', '塔斯基只涉及无参数定义，而 OD 用了序数参数。') },
      { ok: true, h: bi('The definition never mentions truth in V. It uses Sat for set-sized structures (V<sub>α</sub>, ∈), which is definable. Reflection shows, as a metatheoretic schema, that this captures every definition over V.', 'OD 的定义从不提 V 中的真，它用的是集合大小的结构 (V<sub>α</sub>, ∈) 上的 Sat，而后者可定义。反射原理（作为元理论中的模式）说明这样能涵盖 V 上的每个定义。') },
      { h: bi('It does violate Tarski, which is why OD is a proper class rather than a set.', '它确实违反了塔斯基定理，所以 OD 是真类而不是集合。') },
      { h: bi('Tarski\'s theorem fails in ZF because of the reflection theorem.', '由于反射原理，塔斯基定理在 ZF 中不成立。') },
    ],
    expl: bi('Exactly. Tarski is never contradicted: we never get one formula Sat<sub>V</sub>. We only get, for each φ separately, some α where V<sub>α</sub> agrees with V about φ.', '正是。塔斯基定理从未被违反：我们从没得到一条公式 Sat<sub>V</sub>，只是对每个 φ 分别得到某个 α，使 V<sub>α</sub> 在 φ 上与 V 一致。'),
  }, fin(0));
  mcq(b, {
    head: bil('(b) Formula or schema?', '(b) 公式还是模式？'),
    q: bi('“x ∈ OD” (as defined in Step 3) is …', '“x ∈ OD”（按第 3 步的定义）是……'),
    opts: [
      { ok: true, h: bi('a single formula of set theory (in fact Σ<sub>2</sub>).', '集合论的一条公式（实际上是 Σ<sub>2</sub> 公式）。') },
      { h: bi('a schema: one formula for each φ.', '一个模式：每个 φ 一条公式。') },
      { h: bi('not expressible in the language of set theory.', '无法在集合论语言中表达。') },
    ],
    expl: bi('It quantifies over α, over k ∈ ω and over <span class="ov">β</span> inside one formula. The <i>schema</i> is the metatheorem “every set definable in V from ordinals is OD”.', '它在一条公式里对 α、k ∈ ω 和 <span class="ov">β</span> 作量词。<i>模式</i>指的是元定理“每个在 V 中由序数可定义的集合都是 OD”。'),
  }, fin(1));
})();

/* ================= E4 ================= */
(function e4() {
  const svg = $('e4Svg');
  const N = { L: [100, 70, 'V = L'], H: [360, 70, 'V = HOD'], A: [620, 70, 'AC'], O: [360, 190, 'V = OD'] };
  const arrows = [
    { a: 'L', b: 'H', ans: 1, d: 'M150,58 Q230,20 305,58', en: 'L ⊆ HOD always, so V = L gives V = HOD.', zh: '总有 L ⊆ HOD，所以由 V = L 得 V = HOD。' },
    { a: 'H', b: 'L', ans: 0, d: 'M305,84 Q230,122 150,84', en: 'McAloon (1971): V = HOD + V ≠ L is consistent. (Also L[0<sup>#</sup>] if 0<sup>#</sup> exists.)', zh: 'McAloon（1971）：V = HOD + V ≠ L 是一致的。（若 0<sup>#</sup> 存在，L[0<sup>#</sup>] 也是例子。）' },
    { a: 'H', b: 'A', ans: 1, d: 'M415,58 Q490,20 585,58', en: 'HOD ⊨ AC (provably in ZF), and V = HOD.', zh: 'HOD ⊨ AC（在 ZF 中可证），而 V = HOD。' },
    { a: 'A', b: 'H', ans: 0, d: 'M585,84 Q490,122 415,84', en: 'L[c] ⊨ ZFC + V ≠ HOD.', zh: 'L[c] ⊨ ZFC + V ≠ HOD。' },
    { a: 'O', b: 'H', ans: 1, d: 'M340,172 L340,92', en: 'If every set is OD, every element of every trcl is OD.', zh: '若每个集合都是 OD，则任何传递闭包的元素都是 OD。' },
    { a: 'H', b: 'O', ans: 1, d: 'M380,92 L380,172', en: 'HOD ⊆ OD.', zh: 'HOD ⊆ OD。' },
  ];
  const defs = el('defs', {}, svg);
  ['g', 'k', 'r', 'o'].forEach((c, i) => {
    const m = el('marker', { id: 'e4m' + c, viewBox: '0 0 10 10', refX: 8, refY: 5, markerWidth: 7, markerHeight: 7, orient: 'auto' }, defs);
    el('path', { d: 'M0,0 L10,5 L0,10 z', fill: ['#2f9e44', '#1f2430', '#e03131', '#bbb'][i] }, m);
  });
  arrows.forEach(ar => { ar.p = el('path', { d: ar.d, fill: 'none', stroke: '#bbb', 'stroke-width': 2.5, 'marker-end': 'url(#e4mo)' }, svg); });
  for (const k in N) {
    const [x, y, l] = N[k];
    el('rect', { x: x - 55, y: y - 18, width: 110, height: 36, rx: 12, fill: '#fff', stroke: C.ink, 'stroke-width': 2 }, svg);
    txt(svg, x, y + 5, l, { 'font-size': 15, 'text-anchor': 'middle', 'font-weight': 700 });
  }
  txt(svg, 20, 220, 'solid = provable · 实线＝可证    dashed ✗ = not provable · 虚线＝不可证', { 'font-size': 11.5, fill: C.muted });
  const choice = arrows.map(() => null);
  let revealed = false;
  function paint(checked) {
    arrows.forEach((ar, i) => {
      const c = choice[i];
      const col = c === null ? 'o' : !checked ? 'k' : c === ar.ans ? 'g' : 'r';
      ar.p.setAttribute('stroke', { o: '#bbb', k: '#1f2430', g: '#2f9e44', r: '#e03131' }[col]);
      ar.p.setAttribute('marker-end', `url(#e4m${col})`);
      ar.p.setAttribute('stroke-dasharray', c === 0 ? '7 5' : '');
    });
  }
  const rowsBox = $('e4Rows');
  arrows.forEach((ar, i) => {
    const r = document.createElement('div');
    r.className = 'arrowrow';
    r.innerHTML = `<div class="stmt">${N[ar.a][2]} ⇒ ${N[ar.b][2]}</div>
      <button class="btn small" data-v="1">${bil('provable', '可证')}</button>
      <button class="btn small" data-v="0">${bil('not provable', '不可证')}</button>
      <div class="muted" style="flex-basis:100%;font-size:13px"></div>`;
    r.querySelectorAll('button').forEach(b => b.addEventListener('click', () => {
      choice[i] = +b.dataset.v;
      r.querySelectorAll('button').forEach(x => x.classList.toggle('sel', x === b));
      paint(false);
    }));
    ar.row = r;
    rowsBox.appendChild(r);
  });
  function check(reveal) {
    if (reveal) revealed = true;
    let ok = 0;
    arrows.forEach((ar, i) => {
      if (reveal) { choice[i] = ar.ans; ar.row.querySelectorAll('button').forEach(x => x.classList.toggle('sel', +x.dataset.v === ar.ans)); }
      if (choice[i] === ar.ans) ok++;
      ar.row.querySelector('.muted').innerHTML = (reveal || choice[i] !== null) ? (choice[i] === ar.ans ? '✓ ' : '✗ ') + bi(ar.en, ar.zh) : '';
    });
    paint(true);
    if (reveal) okBox($('e4Msg'), bi('Answers shown. Summary: V = L ⇒ V = HOD ⇔ V = OD ⇒ AC, and no arrow reverses.', '已显示答案。小结：V = L ⇒ V = HOD ⇔ V = OD ⇒ AC，且没有一个箭头可以反过来。'), 'info');
    else if (ok === arrows.length) { okBox($('e4Msg'), bi('✓ All six correct.', '✓ 六个全对。')); if (!revealed) Progress.mark('L22E4'); }
    else okBox($('e4Msg'), bi(`${ok} / 6 correct (red arrows are wrong).`, `${ok} / 6 正确（红色箭头答错了）。`), 'warn');
  }
  $('e4Check').addEventListener('click', () => check(false));
  $('e4Show').addEventListener('click', () => check(true));
  paint(false);
})();

/* ================= E5 ================= */
(function e5() {
  const items = [
    { s: bi('(a) Every OD set of ordinals is in HOD.', '(a) 每个 OD 的序数集都在 HOD 中。'), ans: true, en: 'Its transitive closure consists of itself and ordinals.', zh: '它的传递闭包由它自身和序数组成。' },
    { s: bi('(b) Every OD set of reals is in HOD.', '(b) 每个 OD 的实数集都在 HOD 中。'), ans: false, en: 'ℝ in L[c] is OD but contains the non-OD real c.', zh: 'L[c] 中的 ℝ 是 OD，但含有非 OD 的实数 c。' },
    { s: bi('(c) Every OD real (x ⊆ ω) is in HOD.', '(c) 每个 OD 实数（x ⊆ ω）都在 HOD 中。'), ans: true, en: 'Special case of (a): ω ⊆ Ord.', zh: '(a) 的特例：ω ⊆ Ord。' },
    { s: bi('(d) (ZFC) If every set of ordinals is OD, then V = HOD.', '(d)（ZFC）若每个序数集都是 OD，则 V = HOD。'), ans: true, en: 'Using AC, code trcl({x}) by a well-founded relation E on some ordinal γ, i.e. a set of ordinals via pairing. E is OD, and x is definable from E (the image of the top point under the Mostowski collapse), so x is OD.', zh: '用 AC 把 trcl({x}) 编码成某个序数 γ 上的良基关系 E（经配对函数，即一个序数集）。E 是 OD，x 由 E 可定义（莫斯托夫斯基坍塌下顶点的像），所以 x 是 OD。' },
  ];
  const solved = items.map(() => false);
  let revealed = false;
  const box = $('e5List');
  items.forEach((it, i) => {
    const row = document.createElement('div');
    row.className = 'tf';
    row.innerHTML = `<div class="stmt" style="font-family:var(--sans);font-size:15px">${it.s}</div>
      <button class="btn small" data-v="1">${bil('True', '对')}</button><button class="btn small" data-v="0">${bil('False', '错')}</button>
      <div style="flex-basis:100%"><div class="msg"></div></div>`;
    row.querySelectorAll('button').forEach(b => b.addEventListener('click', () => {
      const g = b.dataset.v === '1', msg = row.querySelector('.msg');
      if (g === it.ans) {
        okBox(msg, '✓ ' + bi(it.en, it.zh));
        solved[i] = true;
        if (solved.every(Boolean)) { if (!revealed) Progress.mark('L22E5'); document.querySelector('#e5Proof .step').classList.add('on'); }
      } else okBox(msg, bi('✗ Think about the transitive closure, and about ℝ in L[c].', '✗ 想想传递闭包，再想想 L[c] 中的 ℝ。'), 'bad');
    }));
    it.row = row;
    box.appendChild(row);
  });
  $('e5Show').addEventListener('click', () => {
    revealed = true;
    items.forEach(it => okBox(it.row.querySelector('.msg'), (it.ans ? bi('<b>True.</b> ', '<b>对。</b>') : bi('<b>False.</b> ', '<b>错。</b>')) + bi(it.en, it.zh), 'info'));
    document.querySelector('#e5Proof .step').classList.add('on');
  });
})();

/* ================= E6 ================= */
(function e6() {
  const pairs = [
    { h: '(∅, ℝ ∖ OD)', ok: true, en: 'Both OD, different (c ∈ ℝ∖OD), neither has an OD element.', zh: '都是 OD，互不相同（c ∈ ℝ∖OD），都没有 OD 元素。' },
    { h: '(ℝ, ℝ ∩ OD)', ok: true, en: 'Both OD, different (c), and their OD elements are the same: the OD reals.', zh: '都是 OD，互不相同（差一个 c 等），OD 元素都恰是 OD 实数。' },
    { h: '(ω, ω+1)', ok: false, en: 'ω ∈ ω+1 is OD, but ω ∉ ω.', zh: 'ω ∈ ω+1 是 OD，但 ω ∉ ω。' },
    { h: '(∅, {c})', ok: false, en: '{c} is not OD, so it is not a point of (OD, ∈).', zh: '{c} 不是 OD，根本不是 (OD, ∈) 中的点。' },
    { h: '({ℝ}, {ℝ ∩ OD})', ok: false, en: 'Both OD, but their OD elements ℝ and ℝ∩OD differ.', zh: '都是 OD，但它们的 OD 元素 ℝ 与 ℝ∩OD 不同。' },
    { h: '(ℝ ∖ OD, (ℝ ∖ OD) ∪ {∅})', ok: false, en: '∅ is an OD element of the second set only.', zh: '∅ 是只属于第二个集合的 OD 元素。' },
  ];
  const sel = new Set();
  let revealed = false;
  const chips = pairs.map((p, i) => {
    const d = document.createElement('div');
    d.className = 'chip m';
    d.innerHTML = p.h;
    d.addEventListener('click', () => { if (sel.has(i)) sel.delete(i); else sel.add(i); d.classList.toggle('sel', sel.has(i)); chips.forEach(c => c.classList.remove('ok', 'no')); clearBox($('e6Msg')); });
    $('e6Chips').appendChild(d);
    return d;
  });
  const expl = () => pairs.map(p => `<div>${p.ok ? '✓' : '✗'} <span class="m">${p.h}</span>: ${bil(p.en, p.zh)}</div>`).join('');
  $('e6Check').addEventListener('click', () => {
    let right = true;
    pairs.forEach((p, i) => {
      chips[i].classList.remove('ok', 'no');
      if (sel.has(i)) chips[i].classList.add(p.ok ? 'ok' : 'no');
      if (sel.has(i) !== p.ok) right = false;
    });
    if (right) { okBox($('e6Msg'), '✓ ' + bi('Exactly these two.', '恰好是这两对。') + expl()); if (!revealed) Progress.mark('L22E6'); }
    else okBox($('e6Msg'), bi('Not quite. For each pair check: (1) both OD? (2) different? (3) same OD elements? Red chips are wrong picks; there may also be missing ones.', '还不对。逐对检查：(1) 都是 OD 吗？(2) 不同吗？(3) OD 元素相同吗？红色是选错的，也可能还有漏选。'), 'warn');
  });
  $('e6Show').addEventListener('click', () => {
    revealed = true;
    pairs.forEach((p, i) => { if (p.ok) sel.add(i); else sel.delete(i); chips[i].classList.toggle('sel', p.ok); chips[i].classList.toggle('ok', p.ok); chips[i].classList.remove('no'); });
    okBox($('e6Msg'), expl(), 'info');
  });
})();
