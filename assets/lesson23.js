// Lesson 23 interactions: large cardinals I (inaccessible → weakly compact).
Lang.init();
Progress.paint();

const $ = id => document.getElementById(id);
const setMsg = (box, html, kind = 'info') => { box.className = 'msg ' + kind; box.innerHTML = html; };
const L2 = (en, zh) => en + ' · ' + zh; // SVG label
function T(parent, x, y, txt, attrs = {}) {
  const t = el('text', Object.assign({ x, y }, attrs), parent);
  t.textContent = txt;
  return t;
}
function btn(html, cls = 'btn small') {
  const b = document.createElement('button');
  b.className = cls;
  b.innerHTML = html;
  return b;
}
function TS(parent, x, y, str, attrs = {}) {
  const t = el('text', Object.assign({ x, y }, attrs), parent);
  let size = +(attrs['font-size'] || 14);
  str.split('_').forEach((p, i) => {
    const ts = el('tspan', i ? { dy: size * 0.3, 'font-size': size * 0.75 } : {}, t);
    if (i) size *= 0.75;
    ts.textContent = p;
  });
  return t;
}
const C = { gold: '#f08c00', blue: '#3b5bdb', red: '#e03131', green: '#2f9e44', grey: '#9aa0aa', ink: '#1f2430', meta: '#ae3ec9' };

/* ================= generic: proof steps ================= */
document.querySelectorAll('.proofbox[data-proof]').forEach(pb => {
  const steps = [...pb.querySelectorAll('.step')];
  let k = 0;
  const bar = document.createElement('div');
  bar.className = 'toolbar';
  const bN = btn(bil('Next step ▶', '下一步 ▶'), 'btn small primary');
  const bA = btn(bil('Show all', '全部显示'), 'btn small');
  const bH = btn(bil('Hide', '收起'), 'btn small ghost');
  bar.append(bN, bA, bH);
  pb.appendChild(bar);
  const upd = () => { bN.disabled = k >= steps.length; };
  bN.addEventListener('click', () => { if (k < steps.length) steps[k++].classList.add('on'); upd(); });
  bA.addEventListener('click', () => { steps.forEach(s => s.classList.add('on')); k = steps.length; upd(); });
  bH.addEventListener('click', () => { steps.forEach(s => s.classList.remove('on')); k = 0; upd(); });
});

/* ================= generic: check yourself ================= */
const CY = {
  cy1: { q: ['Suppose ZFC proves that some cardinal with property P exists. Assuming ZFC is consistent, can P be a large cardinal property?', '假设 ZFC 能证明存在具有性质 P 的基数。在 ZFC 一致的前提下，P 能是大基数性质吗？'],
    opts: [['Yes', '能'], ['No', '不能'], ['Only if P implies regularity', '仅当 P 蕴涵正则性时']], a: 1,
    why: ['No. Criterion (ii) would give ZFC ⊢ Con(ZFC), contradicting Gödel 2. Example: “κ = ℵ<sub>κ</sub>” is provably instantiated in ZFC, so it is not a large cardinal property.', '不能。由判据 (ii) 会得到 ZFC ⊢ Con(ZFC)，与哥德尔第二定理矛盾。例：ZFC 可证存在满足“κ = ℵ<sub>κ</sub>”的基数，所以它不是大基数性质。'] },
  cy2: { q: ['ZFC + A ⊢ Con(ZFC + B), and both theories are consistent. Can ZFC + B also prove Con(ZFC + A)?', '设 ZFC + A ⊢ Con(ZFC + B)，且两个理论都一致。ZFC + B 还能证明 Con(ZFC + A) 吗？'],
    opts: [['Yes, that would make them equiconsistent', '能，那样它们就等相容'], ['No', '不能']], a: 1,
    why: ['No. Otherwise ZFC + A proves Con(ZFC + B) and (by formalized Σ₁-completeness) “if ZFC + A were inconsistent, ZFC + B would prove it, contradicting Con(ZFC + B)”. So ZFC + A ⊢ Con(ZFC + A), impossible by Gödel 2. This is why the three cases in Step 2 are mutually exclusive.', '不能。否则 ZFC + A 证明 Con(ZFC + B)，又（由形式化的 Σ₁-完全性）证明“若 ZFC + A 不一致，则 ZFC + B 能证明这一点，与 Con(ZFC + B) 矛盾”。于是 ZFC + A ⊢ Con(ZFC + A)，与哥德尔第二定理矛盾。这就是第 2 步三种情形互斥的原因。'] },
  cy3: { q: ['κ₀ = the least cardinal with ℵ<sub>κ₀</sub> = κ₀. Is κ₀ weakly inaccessible?', 'κ₀ = 满足 ℵ<sub>κ₀</sub> = κ₀ 的最小基数。κ₀ 弱不可达吗？'],
    opts: [['Yes, it is a fixed point', '是，它是不动点'], ['No, it is singular', '不是，它是奇异基数'], ['ZFC cannot decide', 'ZFC 无法判定']], a: 1,
    why: ['κ₀ = sup{ω, ℵ<sub>ω</sub>, ℵ<sub>ℵ<sub>ω</sub></sub>, …}, the supremum of an ω-sequence, so cf(κ₀) = ω &lt; κ₀. Being a fixed point is necessary for inaccessibility, not sufficient.', 'κ₀ = sup{ω, ℵ<sub>ω</sub>, ℵ<sub>ℵ<sub>ω</sub></sub>, …} 是一个 ω 序列的上确界，所以 cf(κ₀) = ω &lt; κ₀。是不动点只是不可达的必要条件，不是充分条件。'] },
  cy4: { q: ['In the proof that V<sub>κ</sub> ⊨ ZFC, which property of κ makes F[x] ∈ V<sub>κ</sub> in the Replacement step?', '在证明 V<sub>κ</sub> ⊨ ZFC 的替换公理一步中，哪条性质保证了 F[x] ∈ V<sub>κ</sub>？'],
    opts: [['κ &gt; ω', 'κ &gt; ω'], ['Regularity of κ (together with |x| &lt; κ)', 'κ 的正则性（加上 |x| &lt; κ）'], ['GCH', 'GCH']], a: 1,
    why: ['F[x] has fewer than κ elements, each of rank &lt; κ. Regularity bounds these ranks below κ. (The strong-limit property was used earlier, to get |V<sub>α</sub>| &lt; κ and hence |x| &lt; κ.)', 'F[x] 的元素少于 κ 个，每个秩都 &lt; κ。正则性保证这些秩有小于 κ 的上界。（强极限性质用在前面：得到 |V<sub>α</sub>| &lt; κ，从而 |x| &lt; κ。）'] },
  cy5: { q: ['L ⊨ “κ is inaccessible”. Must κ be inaccessible in V?', 'L ⊨ “κ 不可达”。κ 在 V 中一定不可达吗？'],
    opts: [['Yes', '一定'], ['No', '不一定']], a: 1,
    why: ['No. V may have new functions that collapse κ or make it singular. If 0<sup>#</sup> exists, ℵ₁<sup>V</sup> is inaccessible in L. Only V → L is guaranteed.', '不一定。V 中可能有 L 里没有的函数，把 κ 坍塌或使它奇异。若 0<sup>#</sup> 存在，ℵ₁<sup>V</sup> 在 L 中不可达。只有 V → L 方向有保证。'] },
  cy6: { q: ['Is the set of successor ordinals below κ stationary in κ?', 'κ 以下的后继序数构成的集合在 κ 中平稳吗？'],
    opts: [['Yes, it is unbounded', '是，它无界'], ['No', '不是']], a: 1,
    why: ['It is disjoint from the club of limit ordinals below κ, so it is not stationary, although it is unbounded.', '它与 κ 以下极限序数构成的 club 不相交，所以不平稳，尽管它无界。'] },
  cy7: { q: ['κ is inaccessible and the inaccessibles below κ are unbounded in κ. Must κ be Mahlo?', 'κ 不可达，且 κ 以下的不可达基数在 κ 中无界。κ 一定是马洛基数吗？'],
    opts: [['Yes', '一定'], ['No', '不一定']], a: 1,
    why: ['No (scenario A). For the least such κ, the limits of inaccessibles below κ form a club with no inaccessible in it, so the inaccessibles are not stationary.', '不一定（情景 A）。对最小的这种 κ，κ 以下不可达基数的极限点构成一个不含不可达基数的 club，所以不可达基数不平稳。'] },
  cy8: { q: ['Which is a theorem of ZFC?', '下面哪个是 ZFC 的定理？'],
    opts: [['ω₁ → (ω₁)²₂', 'ω₁ → (ω₁)²₂'], ['ω → (ω)²₂, but ω₁ ↛ (ω₁)²₂', 'ω → (ω)²₂，但 ω₁ ↛ (ω₁)²₂'], ['every regular uncountable κ satisfies κ → (κ)²₂', '每个正则不可数 κ 都满足 κ → (κ)²₂']], a: 1,
    why: ['Ramsey’s theorem and Sierpiński’s coloring. The third option would make ω₁ weakly compact, hence inaccessible: absurd.', '拉姆齐定理和 Sierpiński 染色。第三个选项会使 ω₁ 弱紧，从而不可达，这显然荒谬。'] },
  cy9: { q: ['In ZFC, which cardinals have the tree property?', '在 ZFC 中，哪些基数有树性质？'],
    opts: [['ω yes, ω₁ no', 'ω 有，ω₁ 没有'], ['ω no, ω₁ yes', 'ω 没有，ω₁ 有'], ['both', '都有']], a: 0,
    why: ['Kőnig’s lemma gives the tree property at ω; Aronszajn’s tree refutes it at ω₁.', '柯尼希引理给出 ω 的树性质；阿龙扎扬树否定了 ω₁ 的树性质。'] },
  cy10: { q: ['κ is the least inaccessible. Is κ Π¹₁-indescribable?', 'κ 是最小的不可达基数。κ 是 Π¹₁-不可描述的吗？'],
    opts: [['Yes', '是'], ['No', '不是']], a: 1,
    why: ['“Ord is inaccessible” is Π¹₁, true in V<sub>κ</sub>, and false in every V<sub>α</sub> with α &lt; κ, since no α &lt; κ is inaccessible. (Consistent with the theorem: Π¹₁-indescribable = weakly compact, which is far above the least inaccessible.)', '“Ord 不可达”是 Π¹₁ 语句，在 V<sub>κ</sub> 中成立，而在每个 V<sub>α</sub>（α &lt; κ）中都不成立，因为没有 α &lt; κ 是不可达的。（与定理吻合：Π¹₁-不可描述 = 弱紧，远在最小不可达之上。）'] },
  cy11: { q: ['Does ZFC + “∃ weakly compact” prove Con(ZFC + “∃ Mahlo”)?', 'ZFC + “存在弱紧基数” 能证明 Con(ZFC + “存在马洛基数”) 吗？'],
    opts: [['Yes', '能'], ['No', '不能'], ['Open', '未知']], a: 0,
    why: ['Yes. If κ is weakly compact, V<sub>κ</sub> ⊨ ZFC (κ is inaccessible) and V<sub>κ</sub> contains Mahlo cardinals λ &lt; κ, which are Mahlo in V<sub>κ</sub> too (V<sub>κ</sub> sees all subsets of λ).', '能。若 κ 弱紧，则 V<sub>κ</sub> ⊨ ZFC（κ 不可达），并且 V<sub>κ</sub> 含有马洛基数 λ &lt; κ，它们在 V<sub>κ</sub> 中仍是马洛的（V<sub>κ</sub> 看得到 λ 的所有子集）。'] },
};
Object.entries(CY).forEach(([id, c]) => {
  const box = $(id);
  if (!box) return;
  box.innerHTML = `<h4>✎ ${bil('Check yourself', '自测')}</h4><div>${bi(c.q[0], c.q[1])}</div><div class="opts"></div><div class="toolbar" style="margin:4px 0"></div><div class="msg"></div>`;
  const opts = box.querySelector('.opts'), msg = box.querySelector('.msg');
  const bs = c.opts.map((o, i) => {
    const b = btn(bil(o[0], o[1]));
    b.addEventListener('click', () => {
      bs.forEach(x => x.classList.remove('choice', 'right', 'wrongc'));
      b.classList.add('choice', i === c.a ? 'right' : 'wrongc');
      b.style.width = 'auto';
      setMsg(msg, (i === c.a ? '✓ ' : '✗ ') + bi(c.why[0], c.why[1]), i === c.a ? 'ok' : 'bad');
    });
    opts.appendChild(b);
    return b;
  });
  const show = btn(bil('Show answer', '显示答案'), 'btn small ghost');
  show.addEventListener('click', () => {
    bs[c.a].classList.add('choice', 'right'); bs[c.a].style.width = 'auto';
    setMsg(msg, bi(c.why[0], c.why[1]), 'info');
  });
  box.querySelector('.toolbar').appendChild(show);
});

/* ================= §1 rocket: reaching κ from below ================= */
(function rocket() {
  const svg = $('rocket');
  const X0 = 40, XK = 800;
  const xs = n => X0 + (XK - 40 - X0) * (1 - Math.pow(0.74, n));
  let mode = 'inacc', n = 0, reached = false, pts = [];
  const modes = [
    ['inacc', 'κ inaccessible', 'κ 不可达'],
    ['w1', 'κ = ℵ₁', 'κ = ℵ₁'],
    ['wom', 'κ = ℵ<sub>ω</sub>', 'κ = ℵ<sub>ω</sub>'],
  ];
  const mBox = $('rkMode');
  mBox.innerHTML = `<span class="lab">${bil('Target κ:', '目标 κ：')}</span>`;
  const mBtns = modes.map(([id, en, zh]) => {
    const b = btn(bil(en, zh));
    b.addEventListener('click', () => { mode = id; reset(); });
    mBox.appendChild(b);
    return [id, b];
  });
  const ops = [
    ['succ', 'λ ↦ λ⁺', 'λ ↦ λ⁺'],
    ['pow', 'λ ↦ 2<sup>λ</sup>', 'λ ↦ 2<sup>λ</sup>'],
    ['sup', 'sup of a short sequence', '取较短序列的上确界'],
  ];
  const oBox = $('rkOps');
  ops.forEach(([id, en, zh]) => {
    const b = btn(bil(en, zh), 'btn');
    b.addEventListener('click', () => op(id));
    oBox.appendChild(b);
  });
  const rb = btn(bil('Reset', '重置'), 'btn ghost');
  rb.addEventListener('click', reset);
  oBox.appendChild(rb);

  function kLabel() { return mode === 'inacc' ? 'κ' : mode === 'w1' ? 'κ = ℵ₁' : 'κ = ℵ_ω'; }
  function draw() {
    svg.innerHTML = '';
    el('line', { x1: 20, x2: 840, y1: 110, y2: 110, stroke: '#ccc', 'stroke-width': 2 }, svg);
    el('line', { x1: XK, x2: XK, y1: 25, y2: 165, stroke: C.red, 'stroke-width': 3, 'stroke-dasharray': '6 5' }, svg);
    T(svg, XK, 20, kLabel(), { 'text-anchor': 'middle', fill: C.red, 'font-weight': 700, 'font-size': 15 });
    T(svg, XK + 6, 180, L2('unreachable?', '够不着？'), { 'text-anchor': 'middle', fill: C.red, 'font-size': 11, class: 'lbl' });
    pts.forEach((p, i) => {
      if (i > 0) {
        const a = pts[i - 1];
        const mx = (a.x + p.x) / 2, h = Math.max(14, Math.min(50, (p.x - a.x) * 0.6));
        el('path', { d: `M${a.x},104 Q${mx},${104 - h} ${p.x},104`, fill: 'none', stroke: p.col || C.blue, 'stroke-width': 1.6, class: 'fadein' }, svg);
      }
      const g = el('g', { class: 'pop' }, svg);
      el('circle', { cx: p.x, cy: 110, r: 6, fill: p.col || C.blue }, g);
      if (p.lab) T(g, p.x, i % 2 ? 140 : 155, p.lab, { 'text-anchor': 'middle', 'font-size': 12, fill: C.ink });
    });
  }
  function reset() {
    n = 0; reached = false;
    pts = [{ x: X0, lab: 'ℵ₀' }];
    mBtns.forEach(([id, b]) => b.classList.toggle('sel', id === mode));
    draw();
    setMsg($('rkMsg'), bi('Start: ℵ₀. Choose an operation.', '起点：ℵ₀。选择一种运算。'));
  }
  const curName = () => mode === 'wom' ? `ℵ${['₀', '₁', '₂', '₃', '₄', '₅', '₆', '₇', '₈', '₉'][n] || '_' + n}` : (n === 0 ? 'ℵ₀' : `λ${['₀', '₁', '₂', '₃', '₄', '₅', '₆', '₇', '₈', '₉'][n] || n}`);
  function op(id) {
    const box = $('rkMsg');
    if (reached) { setMsg(box, bi('κ has been reached, so it is not inaccessible. Press Reset or choose another target.', 'κ 已被够着了，所以它不是不可达的。按“重置”或换个目标。'), 'warn'); return; }
    if (mode === 'inacc') {
      if (n >= 14) { setMsg(box, bi('And so on forever: every stage stays strictly below κ. Even iterating these operations κ times is not a “short” sequence; it is exactly how κ is approached, never reached in fewer than κ steps.', '如此以至无穷：每一步都严格停在 κ 之下。即便把这些运算迭代 κ 次，那也不再是“较短”的序列；κ 只能被这样逼近，用少于 κ 步永远够不着。')); return; }
      const prev = curName();
      n += id === 'sup' ? 2 : 1;
      const nm = curName();
      pts.push({ x: xs(n), lab: n <= 7 ? nm : '' });
      draw();
      if (id === 'succ') setMsg(box, bi(`${nm} = ${prev}⁺ &lt; κ, because κ is a <b>limit</b> cardinal.`, `${nm} = ${prev}⁺ &lt; κ，因为 κ 是<b>极限</b>基数。`));
      if (id === 'pow') setMsg(box, bi(`${nm} = 2<sup>${prev}</sup> &lt; κ, because κ is a <b>strong limit</b>.`, `${nm} = 2<sup>${prev}</sup> &lt; κ，因为 κ 是<b>强极限</b>。`));
      if (id === 'sup') setMsg(box, bi(`${nm} = the sup of a sequence of length &lt; κ of cardinals &lt; κ. It is still &lt; κ, because κ is <b>regular</b>.`, `${nm} = 一个长度 &lt; κ、各项 &lt; κ 的序列的上确界，仍然 &lt; κ，因为 κ <b>正则</b>。`));
    } else if (mode === 'w1') {
      if (id === 'succ') { reached = true; pts.push({ x: XK, lab: 'ℵ₀⁺ = ℵ₁', col: C.red }); draw(); setMsg(box, bi('ℵ₀⁺ = ℵ₁ = κ. Reached in one step: ℵ₁ is a successor cardinal, not a limit.', 'ℵ₀⁺ = ℵ₁ = κ，一步就够着了：ℵ₁ 是后继基数，不是极限基数。'), 'bad'); }
      if (id === 'pow') { reached = true; pts.push({ x: XK, lab: '2^ℵ₀ ≥ ℵ₁', col: C.red }); draw(); setMsg(box, bi('2<sup>ℵ₀</sup> ≥ ℵ₁ (Cantor). The power set reaches or overshoots κ: ℵ₁ is not a strong limit.', '2<sup>ℵ₀</sup> ≥ ℵ₁（康托尔）。幂集够着甚至越过了 κ：ℵ₁ 不是强极限。'), 'bad'); }
      if (id === 'sup') setMsg(box, bi('A countable sequence of countable ordinals has a countable supremum (ω₁ is regular), so this button alone gets you nowhere. But regularity is only one of the tests.', '可数个可数序数的上确界仍可数（ω₁ 正则），所以单靠这个按钮哪儿也去不了。但正则只是三关中的一关。'));
    } else {
      if (id === 'succ') {
        if (n >= 9) { setMsg(box, bi('Successors alone never reach ℵ<sub>ω</sub>. Try the sup button.', '只取后继永远到不了 ℵ<sub>ω</sub>。试试上确界按钮。')); return; }
        const prev = curName(); n++; pts.push({ x: xs(n), lab: n <= 6 ? curName() : '' }); draw();
        setMsg(box, bi(`${prev}⁺ = ${curName()} &lt; ℵ<sub>ω</sub>: ℵ<sub>ω</sub> is a limit cardinal.`, `${prev}⁺ = ${curName()} &lt; ℵ<sub>ω</sub>：ℵ<sub>ω</sub> 是极限基数。`));
      }
      if (id === 'pow') setMsg(box, bi(`2<sup>${curName()}</sup> = ? ZFC cannot say whether it is below ℵ<sub>ω</sub>. Under GCH it is; if 2<sup>ℵ₀</sup> = ℵ<sub>ω+1</sub> it is not.`, `2<sup>${curName()}</sup> = ? ZFC 无法确定它是否小于 ℵ<sub>ω</sub>。在 GCH 下是；若 2<sup>ℵ₀</sup> = ℵ<sub>ω+1</sub> 则不是。`), 'warn');
      if (id === 'sup') { reached = true; pts.push({ x: XK, lab: 'sup ℵₙ', col: C.red }); draw(); setMsg(box, bi('sup{ℵ₀, ℵ₁, ℵ₂, …} = ℵ<sub>ω</sub> = κ. Reached by a sequence of length ω &lt; κ: ℵ<sub>ω</sub> is <b>singular</b>.', 'sup{ℵ₀, ℵ₁, ℵ₂, …} = ℵ<sub>ω</sub> = κ。用一个长度 ω &lt; κ 的序列就够着了：ℵ<sub>ω</sub> 是<b>奇异</b>基数。'), 'bad'); }
    }
  }
  reset();
})();

/* ================= §2 two ladders ================= */
(function ladders() {
  const svg = $('ladders');
  const N = [
    { id: 'world', en: 'worldly', zh: 'worldly', s: 0, z: 0,
      info: ['<b>Worldly:</b> V<sub>κ</sub> ⊨ ZFC. Every inaccessible is worldly and is a limit of worldly cardinals, so the least worldly cardinal lies below the least inaccessible in both orders.', '<b>worldly：</b>V<sub>κ</sub> ⊨ ZFC。每个不可达基数都是 worldly 的，并且是 worldly 基数的极限，所以在两种序下，最小 worldly 基数都在最小不可达之下。'] },
    { id: 'inac', en: 'inaccessible', zh: '不可达', s: 1, z: 1,
      info: ['<b>Inaccessible:</b> ZFC + ∃inaccessible ⊢ Con(ZFC + ∃worldly), because V<sub>κ</sub> is a model of ZFC containing worldly cardinals. Size: the least inaccessible is above the least worldly.', '<b>不可达：</b>ZFC + 存在不可达 ⊢ Con(ZFC + 存在 worldly)，因为 V<sub>κ</sub> 是含有 worldly 基数的 ZFC 模型。大小：最小不可达在最小 worldly 之上。'] },
    { id: 'mahlo', en: 'Mahlo', zh: '马洛', s: 2, z: 2,
      info: ['<b>Mahlo:</b> the inaccessibles below κ are stationary. ZFC + ∃Mahlo ⊢ Con(ZFC + ∃inaccessible). Size: a Mahlo has inaccessibles below it.', '<b>马洛：</b>κ 以下的不可达基数平稳。ZFC + 存在马洛 ⊢ Con(ZFC + 存在不可达)。大小：马洛基数下方有不可达基数。'] },
    { id: 'wc', en: 'weakly compact', zh: '弱紧', s: 3, z: 3,
      info: ['<b>Weakly compact:</b> the Mahlo cardinals below κ are stationary (Step 10), so ZFC + ∃wc ⊢ Con(ZFC + ∃Mahlo), and the least weakly compact is above the least Mahlo.', '<b>弱紧：</b>κ 以下的马洛基数平稳（第 10 步），所以 ZFC + 存在弱紧 ⊢ Con(ZFC + 存在马洛)，且最小弱紧在最小马洛之上。'] },
    { id: 'meas', en: 'measurable', zh: '可测', s: 4, z: 4,
      info: ['<b>Measurable (Lesson 24):</b> every measurable is weakly compact and a limit of weakly compact cardinals. Stronger and bigger.', '<b>可测（第 24 课）：</b>每个可测基数都是弱紧的，并且是弱紧基数的极限。更强，也更大。'] },
    { id: 'sc', en: 'supercompact', zh: '超紧', s: 5, z: 6,
      info: ['<b>Supercompact (Lesson 25):</b> in strength, between measurable and huge. In size, the least supercompact lies <b>above</b> the least huge (if both exist).', '<b>超紧（第 25 课）：</b>强度介于可测与巨大之间。大小上，最小超紧基数在最小巨大基数<b>之上</b>（若两者都存在）。'] },
    { id: 'huge', en: 'huge', zh: '巨大', s: 6, z: 5,
      info: ['<b>Huge (Lesson 25):</b> far stronger than supercompact in consistency strength, yet the least huge cardinal is <b>smaller</b> than the least supercompact (if both exist). The lines cross here.', '<b>巨大（第 25 课）：</b>一致性强度远高于超紧，但最小巨大基数却<b>小于</b>最小超紧基数（若两者都存在）。两条线在这里交叉。'] },
  ];
  const LX = 150, RX = 610, Y = r => 360 - r * 50;
  let sel = null;
  function draw() {
    svg.innerHTML = '';
    T(svg, LX, 22, L2('consistency strength ↑', '一致性强度 ↑'), { 'text-anchor': 'middle', 'font-weight': 700, fill: C.meta, 'font-size': 13, class: 'lbl' });
    T(svg, RX, 22, L2('size of least witness ↑', '最小实例的大小 ↑'), { 'text-anchor': 'middle', 'font-weight': 700, fill: C.gold, 'font-size': 13, class: 'lbl' });
    [LX, RX].forEach((x, k) => {
      el('line', { x1: x - 100, x2: x - 100, y1: 40, y2: 385, stroke: '#d8d3c4', 'stroke-width': 4 }, svg);
      el('line', { x1: x + 100, x2: x + 100, y1: 40, y2: 385, stroke: '#d8d3c4', 'stroke-width': 4 }, svg);
    });
    N.forEach(nd => {
      const on = sel === nd.id;
      const crossing = nd.id === 'sc' || nd.id === 'huge';
      el('line', { x1: LX + 100, y1: Y(nd.s), x2: RX - 100, y2: Y(nd.z), stroke: on ? C.blue : crossing ? C.red : '#c9c4b6', 'stroke-width': on ? 4 : 2, 'stroke-dasharray': crossing && !on ? '6 4' : '' }, svg);
    });
    N.forEach(nd => {
      const on = sel === nd.id;
      [[LX, nd.s, C.meta], [RX, nd.z, C.gold]].forEach(([x, r, col]) => {
        const g = el('g', { class: 'hit' }, svg);
        el('rect', { x: x - 96, y: Y(r) - 16, width: 192, height: 32, rx: 9, fill: on ? '#e7ecff' : '#fff', stroke: on ? C.blue : col, 'stroke-width': on ? 3 : 1.5 }, g);
        T(g, x, Y(r) + 5, L2(nd.en, nd.zh), { 'text-anchor': 'middle', 'font-size': 13, class: 'lbl', fill: C.ink });
        g.addEventListener('click', () => { sel = nd.id; draw(); setMsg($('ladMsg'), bi(nd.info[0], nd.info[1])); });
      });
    });
  }
  draw();
  setMsg($('ladMsg'), bi('Click any rung. Dashed red lines mark the crossing: huge vs supercompact.', '点击任意一级。红色虚线标出了交叉：巨大基数与超紧基数。'));
})();

/* ================= §3 cardinal ladder ================= */
const CANDS = [
  { id: 'a0', lab: 'ℵ₀', x: 40,
    r: { unc: ['N', 'countable', '可数'], reg: ['Y', 'a finite union of finite sets is finite', '有限个有限集之并仍有限'], lim: ['Y', 'not a successor cardinal (n+1 &lt; ω)', '不是后继基数（n+1 &lt; ω）'], sl: ['Y', '2<sup>n</sup> is finite', '2<sup>n</sup> 有限'] } },
  { id: 'a1', lab: 'ℵ₁', x: 120,
    r: { unc: ['Y', '', ''], reg: ['Y', 'with AC, a countable union of countable sets is countable', '在选择公理下，可数个可数集之并可数'], lim: ['N', 'ℵ₁ = ℵ₀⁺', 'ℵ₁ = ℵ₀⁺'], sl: ['N', '2<sup>ℵ₀</sup> ≥ ℵ₁', '2<sup>ℵ₀</sup> ≥ ℵ₁'] } },
  { id: 'aw', lab: 'ℵ_ω', x: 220,
    r: { unc: ['Y', '', ''], reg: ['N', 'cf = ω: ℵ<sub>ω</sub> = sup ℵ<sub>n</sub>', 'cf = ω：ℵ<sub>ω</sub> = sup ℵ<sub>n</sub>'], lim: ['Y', 'index ω is a limit ordinal', '下标 ω 是极限序数'], sl: ['U', 'yes under GCH; no if 2<sup>ℵ₀</sup> = ℵ<sub>ω+1</sub>', 'GCH 下是；若 2<sup>ℵ₀</sup> = ℵ<sub>ω+1</sub> 则否'] } },
  { id: 'aw1', lab: 'ℵ_ω+1', x: 300,
    r: { unc: ['Y', '', ''], reg: ['Y', 'successor cardinals are regular (AC)', '后继基数都正则（选择公理）'], lim: ['N', 'a successor', '是后继基数'], sl: ['N', '2<sup>ℵ<sub>ω</sub></sup> ≥ ℵ<sub>ω+1</sub>', '2<sup>ℵ<sub>ω</sub></sup> ≥ ℵ<sub>ω+1</sub>'] } },
  { id: 'aw1b', lab: 'ℵ_ω₁', x: 390,
    r: { unc: ['Y', '', ''], reg: ['N', 'cf = ω₁ &lt; ℵ<sub>ω₁</sub>', 'cf = ω₁ &lt; ℵ<sub>ω₁</sub>'], lim: ['Y', 'index ω₁ is a limit ordinal', '下标 ω₁ 是极限序数'], sl: ['U', 'depends on the continuum function', '取决于连续统函数'] } },
  { id: 'k0', lab: 'κ₀', x: 530, sub: ['least fixed pt', '最小不动点'],
    r: { unc: ['Y', '', ''], reg: ['N', 'cf = ω: κ₀ = sup{ω, ℵ<sub>ω</sub>, ℵ<sub>ℵ<sub>ω</sub></sub>, …}', 'cf = ω：κ₀ = sup{ω, ℵ<sub>ω</sub>, ℵ<sub>ℵ<sub>ω</sub></sub>, …}'], lim: ['Y', 'κ₀ = ℵ<sub>κ₀</sub> with κ₀ a limit ordinal', 'κ₀ = ℵ<sub>κ₀</sub>，κ₀ 是极限序数'], sl: ['U', 'yes under GCH; no if 2<sup>ℵ₀</sup> &gt; κ₀ (consistent)', 'GCH 下是；若 2<sup>ℵ₀</sup> &gt; κ₀（一致）则否'] } },
  { id: 'k1', lab: 'κ_ω₁', x: 660, sub: ['ω₁-th fixed pt', '第 ω₁ 个不动点'],
    r: { unc: ['Y', '', ''], reg: ['N', 'cf = ω₁: the sup of the first ω₁ fixed points', 'cf = ω₁：前 ω₁ 个不动点的上确界'], lim: ['Y', 'a fixed point, so a limit', '是不动点，所以是极限'], sl: ['U', 'depends on the continuum function', '取决于连续统函数'] } },
  { id: 'ki', lab: 'κ', x: 790, sub: ['inaccessible', '不可达'],
    r: { unc: ['Y', '', ''], reg: ['Y', 'by assumption', '由假设'], lim: ['Y', 'strong limit ⇒ limit', '强极限 ⇒ 极限'], sl: ['Y', 'by assumption; κ = ℵ<sub>κ</sub>, and the fixed points below κ form a club in κ', '由假设；κ = ℵ<sub>κ</sub>，且 κ 以下的不动点构成 κ 的 club'] } },
];
function verdicts(c) {
  const r = c.r;
  const wi = r.unc[0] === 'Y' && r.reg[0] === 'Y' && r.lim[0] === 'Y' ? 'Y' : 'N';
  const si = r.unc[0] === 'Y' && r.reg[0] === 'Y' && r.sl[0] === 'Y' ? 'Y' : (r.unc[0] === 'N' || r.reg[0] === 'N' || r.sl[0] === 'N') ? 'N' : 'U';
  return { wi, si };
}
const VMARK = { Y: '<span class="yes">✓</span>', N: '<span class="no">✗</span>', U: '<span class="unk">?</span>' };
(function cardLadder() {
  const svg = $('cladder');
  let sel = 'aw';
  function draw() {
    svg.innerHTML = '';
    el('line', { x1: 20, x2: 840, y1: 95, y2: 95, stroke: '#bbb', 'stroke-width': 2 }, svg);
    el('path', { d: 'M840,95 l-10,-5 v10 z', fill: '#bbb' }, svg);
    CANDS.forEach(c => {
      const g = el('g', { class: 'hit' }, svg);
      const on = c.id === sel;
      const v = verdicts(c);
      el('circle', { cx: c.x, cy: 95, r: on ? 11 : 8, fill: v.si === 'Y' ? C.gold : '#fff', stroke: on ? C.blue : C.ink, 'stroke-width': on ? 3 : 2 }, g);
      TS(g, c.x, 125, c.lab, { 'text-anchor': 'middle', 'font-size': 16, 'font-weight': 700, fill: on ? C.blue : C.ink, class: 'lbl' });
      if (c.sub) { T(g, c.x, 146, c.sub[0], { 'text-anchor': 'middle', 'font-size': 10.5, fill: C.ink, class: 'lbl' }); T(g, c.x, 160, c.sub[1], { 'text-anchor': 'middle', 'font-size': 10.5, fill: '#4a5568', class: 'lbl' }); }
      el('rect', { x: c.x - 34, y: 70, width: 68, height: 85, fill: 'transparent' }, g);
      g.addEventListener('click', () => { sel = c.id; draw(); table(); });
    });
  }
  function table() {
    const c = CANDS.find(x => x.id === sel), r = c.r, v = verdicts(c);
    const row = (en, zh, [m, e, z]) => `<tr><td style="text-align:left">${bil(en, zh)}</td><td>${VMARK[m]}</td><td style="text-align:left">${e ? bi(e, z) : ''}</td></tr>`;
    const why = v.si === 'Y' ? ['passes every test', '通过所有检验'] : c.id === 'a0' ? ['regular strong limit, but countable: excluded by definition', '正则强极限，但可数：按定义排除'] : r.reg[0] === 'N' ? ['singular', '奇异'] : ['not a limit cardinal', '不是极限基数'];
    $('cTable').innerHTML = `<table class="cls"><tr><th colspan="3" class="m">${c.lab.replace('_ω₁', '<sub>ω₁</sub>').replace('_ω+1', '<sub>ω+1</sub>').replace('_ω', '<sub>ω</sub>')}</th></tr>` +
      row('uncountable', '不可数', r.unc) + row('regular', '正则', r.reg) + row('limit cardinal', '极限基数', r.lim) + row('strong limit', '强极限', r.sl) +
      row('weakly inaccessible', '弱不可达', [v.wi, ...why]) + row('strongly inaccessible', '强不可达', [v.si, ...why]) + '</table>';
  }
  draw(); table();

  $('fpGo').addEventListener('click', async () => {
    draw();
    const xs = [40, 220, 380, 455, 492, 511, 520, 525, 527.5, 529];
    const labs = ['ω', 'ℵ_ω', 'ℵ_ℵ_ω', '…'];
    for (let i = 1; i < xs.length; i++) {
      const a = xs[i - 1], b = xs[i], h = Math.max(8, (b - a) * 0.35);
      el('path', { d: `M${a},88 Q${(a + b) / 2},${88 - h} ${b},88`, fill: 'none', stroke: C.meta, 'stroke-width': 2, class: 'fadein' }, svg);
      if (i < 4 && i > 0) TS(svg, b, 88 - h - 6, labs[i], { 'text-anchor': 'middle', 'font-size': 12, fill: C.meta, class: 'lbl' });
      await sleep(260);
    }
    T(svg, 530, 22, L2('ω-sequence → cf κ₀ = ω', 'ω 序列 → cf κ₀ = ω'), { 'text-anchor': 'middle', 'font-size': 12, fill: C.meta, 'font-weight': 700, class: 'lbl' });
    setMsg($('fpMsg'), bi('x₀ = ω, x<sub>n+1</sub> = ℵ<sub>x<sub>n</sub></sub>. The limit κ₀ = sup x<sub>n</sub> satisfies ℵ<sub>κ₀</sub> = sup ℵ<sub>x<sub>n</sub></sub> = sup x<sub>n+1</sub> = κ₀. It is the least fixed point, and it is the limit of an ω-sequence, so it is singular.',
      'x₀ = ω，x<sub>n+1</sub> = ℵ<sub>x<sub>n</sub></sub>。极限 κ₀ = sup x<sub>n</sub> 满足 ℵ<sub>κ₀</sub> = sup ℵ<sub>x<sub>n</sub></sub> = sup x<sub>n+1</sub> = κ₀。它是最小不动点，又是一个 ω 序列的极限，所以是奇异基数。'));
  });
})();

/* ================= §4 V_κ ⊨ ZFC ================= */
(function vcone() {
  const AX = [
    ['ext', 'Extensionality', '外延公理'], ['fnd', 'Foundation', '正则（基础）公理'], ['pair', 'Pairing', '配对公理'],
    ['union', 'Union', '并集公理'], ['pow', 'Power Set', '幂集公理'], ['inf', 'Infinity', '无穷公理'],
    ['sep', 'Separation', '分离公理'], ['rep', 'Replacement', '替换公理'], ['ac', 'Choice', '选择公理'],
  ];
  const OK = {
    ext: ['V<sub>α</sub> is transitive, so ∈-extensionality holds in it.', 'V<sub>α</sub> 是传递集，所以外延公理在其中成立。'],
    fnd: ['∈ is well-founded on every set.', '∈ 在任何集合上都是良基的。'],
    pair: ['α is a limit: x, y ∈ V<sub>β</sub> ⇒ {x, y} ∈ V<sub>β+1</sub>.', 'α 是极限序数：x, y ∈ V<sub>β</sub> ⇒ {x, y} ∈ V<sub>β+1</sub>。'],
    union: ['rank(⋃x) ≤ rank(x).', 'rank(⋃x) ≤ rank(x)。'],
    pow: ['x ∈ V<sub>β</sub> ⇒ P(x) ∈ V<sub>β+2</sub>, and β+2 &lt; α since α is a limit.', 'x ∈ V<sub>β</sub> ⇒ P(x) ∈ V<sub>β+2</sub>，而 α 是极限，所以 β+2 &lt; α。'],
    inf: ['ω ∈ V<sub>ω+1</sub> ⊆ V<sub>α</sub> since α &gt; ω.', 'α &gt; ω，所以 ω ∈ V<sub>ω+1</sub> ⊆ V<sub>α</sub>。'],
    sep: ['Every subset of x ∈ V<sub>β</sub> lies in V<sub>β+1</sub>.', 'x ∈ V<sub>β</sub> 的每个子集都在 V<sub>β+1</sub> 中。'],
    rep: ['κ regular and |V<sub>β</sub>| &lt; κ: F[x] has &lt; κ elements of rank &lt; κ, and these ranks are bounded below κ.', 'κ 正则且 |V<sub>β</sub>| &lt; κ：F[x] 只有 &lt; κ 个秩 &lt; κ 的元素，这些秩有小于 κ 的上界。'],
    ac: ['A well-order of x ∈ V<sub>β</sub> lies in V<sub>β+3</sub>.', 'x ∈ V<sub>β</sub> 的良序在 V<sub>β+3</sub> 中。'],
  };
  const CUTS = [
    { id: 'w', en: 'α = ω', zh: 'α = ω', y: 245, bad: { inf: ['Every element of V<sub>ω</sub> is finite, and ω ∉ V<sub>ω</sub>. (All other axioms hold: V<sub>ω</sub> is the hereditarily finite sets.)', 'V<sub>ω</sub> 的元素都是有限集，ω ∉ V<sub>ω</sub>。（其余公理都成立：V<sub>ω</sub> 就是遗传有限集。）'] },
      ok: { inf: null, rep: ['F[x] is finite when x is finite, so it is in V<sub>ω</sub>.', 'x 有限时 F[x] 也有限，所以属于 V<sub>ω</sub>。'] } },
    { id: 'ww', en: 'α = ω+ω', zh: 'α = ω+ω', y: 215, bad: { rep: ['n ↦ ω+n is definable, with domain ω ∈ V<sub>ω+ω</sub>; but the image {ω+n : n &lt; ω} has rank ω+ω, so it is not in V<sub>ω+ω</sub>. (V<sub>ω+ω</sub> is a model of Zermelo set theory Z.)', 'n ↦ ω+n 可定义，定义域 ω ∈ V<sub>ω+ω</sub>；但像集 {ω+n : n &lt; ω} 的秩是 ω+ω，不属于 V<sub>ω+ω</sub>。（V<sub>ω+ω</sub> 是策梅洛集合论 Z 的模型。）'] } },
    { id: 'w1', en: 'α = ω₁', zh: 'α = ω₁', y: 180, bad: { rep: ['Every countable ordinal is the order type of a well-order R of ω. On the set WO ⊆ P(ω×ω) (which is in V<sub>ω₁</sub>), the map R ↦ otp(R) is definable, and its image ω₁ is not in V<sub>ω₁</sub>.', '每个可数序数都是 ω 上某个良序 R 的序型。在集合 WO ⊆ P(ω×ω)（属于 V<sub>ω₁</sub>）上，映射 R ↦ otp(R) 可定义，其像集 ω₁ 不属于 V<sub>ω₁</sub>。'] } },
    { id: 'wk', en: 'κ weakly inacc., 2<sup>ℵ₀</sup> ≥ κ', zh: 'κ 弱不可达，2<sup>ℵ₀</sup> ≥ κ', y: 140, bad: { rep: ['Every α &lt; κ ≤ 2<sup>ℵ₀</sup> is the order type of a well-order of a subset of P(ω). These well-orders form a set in V<sub>κ</sub>, and R ↦ otp(R) is definable with image κ ∉ V<sub>κ</sub>. Regularity alone is not enough: the strong-limit property is needed.', '每个 α &lt; κ ≤ 2<sup>ℵ₀</sup> 都是 P(ω) 某个子集上良序的序型。这些良序构成 V<sub>κ</sub> 中的一个集合，R ↦ otp(R) 可定义，像集为 κ ∉ V<sub>κ</sub>。单有正则性不够，还需要强极限性质。'] } },
    { id: 'lw', en: 'κ = least worldly', zh: 'κ = 最小 worldly', y: 105, ok: { rep: ['Holds by definition of worldly. Yet cf κ = ω: there is a cofinal ω-sequence in κ, but no function definable over V<sub>κ</sub> produces one. Replacement only speaks about definable functions.', '由 worldly 的定义成立。然而 cf κ = ω：κ 中有共尾的 ω 序列，只是没有任何在 V<sub>κ</sub> 上可定义的函数能产生它。替换公理只涉及可定义的函数。'] } },
    { id: 'in', en: 'κ inaccessible', zh: 'κ 不可达', y: 70 },
  ];
  let cut = 'in', selAx = 'rep';
  const pick = $('cutPick');
  pick.innerHTML = `<span class="lab">${bil('Cut at:', '截断于：')}</span>`;
  const pBtns = CUTS.map(c => {
    const b = btn(bil(c.en, c.zh));
    b.addEventListener('click', () => { cut = c.id; render(); });
    pick.appendChild(b);
    return [c.id, b];
  });
  const grid = $('axGrid');
  const tiles = AX.map(([id, en, zh]) => {
    const d = document.createElement('div');
    d.innerHTML = bi(en, zh);
    d.addEventListener('click', () => { selAx = id; render(); });
    grid.appendChild(d);
    return [id, d];
  });
  function status(c, id) {
    if (c.bad && c.bad[id]) return { ok: false, why: c.bad[id] };
    if (c.ok && c.ok[id]) return { ok: true, why: c.ok[id] };
    if (c.id === 'w' && id === 'pow') return { ok: true, why: ['The power set of a finite set is finite, and V<sub>ω</sub> is closed under it.', '有限集的幂集有限，V<sub>ω</sub> 对它封闭。'] };
    return { ok: true, why: OK[id] };
  }
  function render() {
    const c = CUTS.find(x => x.id === cut);
    pBtns.forEach(([id, b]) => b.classList.toggle('sel', id === cut));
    tiles.forEach(([id, d]) => {
      const s = status(c, id);
      d.className = (s.ok ? 'ok' : 'bad') + (id === selAx ? ' sel' : '');
      d.innerHTML = bi((s.ok ? '✓ ' : '✗ ') + AX.find(a => a[0] === id)[1], (s.ok ? '✓ ' : '✗ ') + AX.find(a => a[0] === id)[2]);
    });
    const s = status(c, selAx), nm = AX.find(a => a[0] === selAx);
    const all = AX.every(([id]) => status(c, id).ok);
    setMsg($('axMsg'), `<b>${bil(nm[1], nm[2])}:</b> ` + bi(s.why[0], s.why[1]) +
      (all ? `<div style="margin-top:6px">${bi('<b>All axioms hold: V<sub>α</sub> ⊨ ZFC.</b>', '<b>所有公理都成立：V<sub>α</sub> ⊨ ZFC。</b>')}</div>` : ''), s.ok ? 'ok' : 'bad');
    drawCone(c);
  }
  function drawCone(c) {
    const svg = $('vcone');
    svg.innerHTML = '';
    const ax = 155, ay = 285, top = 15, half = 140;
    const wAt = y => (ay - y) / (ay - top) * half;
    el('path', { d: `M${ax - half},${top} L${ax},${ay} L${ax + half},${top}`, fill: 'none', stroke: C.ink, 'stroke-width': 2 }, svg);
    const w = wAt(c.y);
    el('path', { d: `M${ax - w},${c.y} L${ax},${ay} L${ax + w},${c.y} Z`, fill: CUTS.indexOf(c) === CUTS.length - 1 || c.id === 'lw' ? '#d3f9d8' : '#ffe3e3', opacity: .8, class: 'fadein' }, svg);
    [[245, 'ω'], [215, 'ω+ω'], [180, 'ω₁'], [140, ''], [105, ''], [70, '']].forEach(([y, l]) => {
      el('line', { x1: ax - wAt(y), x2: ax + wAt(y), y1: y, y2: y, stroke: '#ccc', 'stroke-dasharray': '2 4' }, svg);
    });
    el('line', { x1: ax - half - 8, x2: ax + half + 8, y1: c.y, y2: c.y, stroke: C.red, 'stroke-width': 2.5, 'stroke-dasharray': '7 4' }, svg);
    TS(svg, ax - w * 0.55, c.y - 8, 'V_' + (c.id === 'w' ? 'ω' : c.id === 'ww' ? 'ω+ω' : c.id === 'w1' ? 'ω₁' : 'κ'), { 'text-anchor': 'middle', 'font-weight': 700, 'font-size': 15, fill: C.red, class: 'lbl' });
    T(svg, ax, 300 - 2, '∅ = V₀', { 'text-anchor': 'middle', 'font-size': 10, fill: C.grey });
    T(svg, ax + half - 10, top + 14, 'V', { 'font-size': 16, 'font-weight': 700, fill: C.ink });
  }
  render();
})();

/* ================= §5 down to L ================= */
(function downL() {
  const svg = $('vl');
  let sharp = false, token = 0;
  function base() {
    svg.innerHTML = '';
    const cone = (cx, hw, col, lab) => {
      el('path', { d: `M${cx - hw},20 L${cx},270 L${cx + hw},20`, fill: 'none', stroke: col, 'stroke-width': 2.5 }, svg);
      T(svg, cx, 16, lab, { 'text-anchor': 'middle', 'font-weight': 700, 'font-size': 15, fill: col });
    };
    cone(190, 160, C.ink, 'V');
    cone(570, 110, C.green, 'L ⊆ V');
    el('line', { x1: 20, x2: 740, y1: 110, y2: 110, stroke: C.red, 'stroke-dasharray': '6 5', 'stroke-width': 2 }, svg);
    T(svg, 742, 106, sharp ? 'ℵ₁ᵛ' : 'κ', { 'text-anchor': 'end', fill: C.red, 'font-weight': 700, 'font-size': 14 });
  }
  const PROPS = [
    { en: 'regular', zh: '正则', v: '✓', l: '✓', why: ['a cofinal map in L would be one in V', 'L 中的共尾映射也是 V 中的'] },
    { en: 'limit cardinal', zh: '极限基数', v: '✓', l: '✓', why: ['V-cardinals are L-cardinals; (λ⁺)ᴸ ≤ λ⁺ &lt; κ', 'V 的基数是 L 的基数；(λ⁺)ᴸ ≤ λ⁺ &lt; κ'] },
    { en: '2^λ < κ', zh: '2^λ < κ', v: '?', l: '✓', why: ['L ⊨ GCH, so 2<sup>λ</sup> = λ⁺ &lt; κ in L', 'L ⊨ GCH，所以在 L 中 2<sup>λ</sup> = λ⁺ &lt; κ'] },
  ];
  async function go() {
    const my = ++token;
    sharp = false; base();
    setMsg($('vlMsg'), bi('κ is weakly inaccessible in V (strong limit unknown).', 'κ 在 V 中弱不可达（是否强极限未知）。'));
    for (let i = 0; i < PROPS.length; i++) {
      if (my !== token) return;
      const p = PROPS[i], y = 150 + i * 36;
      const g = el('g', {}, svg);
      g.style.transition = 'transform 1s cubic-bezier(.3,.8,.3,1)';
      g.style.transform = 'translate(0px,0px)';
      el('rect', { x: 110, y: y - 15, width: 160, height: 26, rx: 13, fill: p.v === '✓' ? '#d3f9d8' : '#fff3bf', stroke: p.v === '✓' ? C.green : C.gold }, g);
      T(g, 190, y + 3, `${L2(p.en, p.zh)} ${p.v}`, { 'text-anchor': 'middle', 'font-size': 12, class: 'lbl' });
      await sleep(500);
      if (my !== token) return;
      g.style.transform = 'translate(380px,0px)';
      await sleep(1000);
      if (my !== token) return;
      const g2 = el('g', { class: 'pop' }, svg);
      el('rect', { x: 490, y: y - 15, width: 160, height: 26, rx: 13, fill: '#d3f9d8', stroke: C.green, 'stroke-width': 2 }, g2);
      T(g2, 570, y + 3, `${L2(p.en, p.zh)} ✓`, { 'text-anchor': 'middle', 'font-size': 12, class: 'lbl', 'font-weight': 700 });
      g.remove();
      setMsg($('vlMsg'), bi(`<b>${p.en}</b> goes down: ${p.why[0]}.`, `<b>${p.zh}</b> 下传：${p.why[1]}。`));
      await sleep(700);
    }
    if (my !== token) return;
    T(svg, 570, 268 - 4, '', {});
    setMsg($('vlMsg'), bi('Result: L ⊨ “κ is strongly inaccessible”, so L<sub>κ</sub> ⊨ ZFC. From a weakly inaccessible we get a model with a strongly inaccessible: equiconsistency.', '结果：L ⊨ “κ 强不可达”，所以 L<sub>κ</sub> ⊨ ZFC。由弱不可达得到一个含强不可达的模型：二者等相容。'), 'ok');
  }
  function sharpScene() {
    token++; sharp = true; base();
    const box = (cx, y, txt, ok) => {
      const g = el('g', { class: 'pop' }, svg);
      el('rect', { x: cx - 105, y: y - 15, width: 210, height: 26, rx: 13, fill: ok ? '#d3f9d8' : '#ffe3e3', stroke: ok ? C.green : C.red }, g);
      T(g, cx, y + 3, txt, { 'text-anchor': 'middle', 'font-size': 12, class: 'lbl' });
    };
    box(190, 150, L2('ℵ₁ = ℵ₀⁺: not a limit', 'ℵ₁ = ℵ₀⁺：非极限'), false);
    box(190, 186, L2('not inaccessible in V', '在 V 中不可达？否'), false);
    box(570, 150, L2('inaccessible in L', '在 L 中不可达'), true);
    el('path', { d: 'M470,186 L300,186', stroke: C.red, 'stroke-width': 2.5, 'marker-end': '' }, svg);
    T(svg, 385, 180, '✗', { 'text-anchor': 'middle', fill: C.red, 'font-size': 22, 'font-weight': 700 });
    T(svg, 385, 210, L2('does not go up', '不能上传'), { 'text-anchor': 'middle', fill: C.red, 'font-size': 12, class: 'lbl' });
    setMsg($('vlMsg'), bi('If 0<sup>#</sup> exists, ℵ₁<sup>V</sup> is inaccessible in L: L lacks the bijections showing ℵ₁ = ℵ₀⁺ in V, so L thinks ℵ₁<sup>V</sup> is a limit (and much more). Inaccessibility in L does not transfer up to V.', '若 0<sup>#</sup> 存在，ℵ₁<sup>V</sup> 在 L 中不可达：L 里缺少那些说明 ℵ₁ = ℵ₀⁺ 的双射，所以 L 认为 ℵ₁<sup>V</sup> 是极限基数（还远不止于此）。L 中的不可达性不能上传到 V。'), 'warn');
  }
  $('vlGo').addEventListener('click', go);
  $('vlSharp').addEventListener('click', sharpScene);
  base();
  setMsg($('vlMsg'), bi('Press the button to start.', '按按钮开始。'));
})();

/* ================= §6 zipper ================= */
(function zipper() {
  const svg = $('zip');
  let mode = 'reg', data = null, token = 0;
  const AY = 95;
  function gen() {
    if (mode === 'reg') {
      const g = 380 + Math.random() * 200, r = 0.6;
      const Cs = [], Ds = [];
      for (let k = 0; k < 9; k++) { Cs.push(g - 170 * Math.pow(r, 2 * k)); Ds.push(g - 170 * Math.pow(r, 2 * k + 1)); }
      const extra = (lo, hi, m) => Array.from({ length: m }, () => lo + Math.random() * (hi - lo));
      const tail = Array.from({ length: 8 }, (_, k) => 800 - 60 * Math.pow(0.6, k));
      data = { g, Cs, Ds, C: [...extra(40, g - 190, 4), ...Cs, g, ...extra(g + 20, 730, 4), ...tail.filter((_, k) => k % 2 === 0)],
        D: [...extra(40, g - 190, 4), ...Ds, g, ...extra(g + 20, 730, 4), ...tail.filter((_, k) => k % 2 === 1)] };
    } else {
      const P = Array.from({ length: 13 }, (_, n) => 800 - 760 * Math.pow(0.62, n));
      data = { P, C: P.filter((_, n) => n % 2 === 0), D: P.filter((_, n) => n % 2 === 1) };
    }
  }
  function draw() {
    svg.innerHTML = '';
    el('line', { x1: 30, x2: 800, y1: AY, y2: AY, stroke: '#bbb', 'stroke-width': 2 }, svg);
    el('line', { x1: 812, x2: 812, y1: 60, y2: 130, stroke: C.ink, 'stroke-width': 2, 'stroke-dasharray': '4 3' }, svg);
    TS(svg, 812, 52, mode === 'reg' ? 'κ' : 'ℵ_ω', { 'text-anchor': 'middle', 'font-weight': 700, 'font-size': 15, class: 'lbl' });
    T(svg, 30, 112 + 40, '0', { 'font-size': 11, fill: C.grey });
    data.C.forEach(x => el('line', { x1: x, x2: x, y1: AY - 22, y2: AY - 4, stroke: C.blue, 'stroke-width': 2 }, svg));
    data.D.forEach(x => el('line', { x1: x, x2: x, y1: AY + 4, y2: AY + 22, stroke: C.red, 'stroke-width': 2 }, svg));
    T(svg, 36, AY - 30, L2('club C', 'club C'), { fill: C.blue, 'font-size': 12, 'font-weight': 700, class: 'lbl' });
    T(svg, 36, AY + 40, L2('club D', 'club D'), { fill: C.red, 'font-size': 12, 'font-weight': 700, class: 'lbl' });
    if (mode === 'om') data.P.slice(0, 5).forEach((x, n) => T(svg, x, AY + 58, `ℵ${'₀₁₂₃₄'[n]}`, { 'text-anchor': 'middle', 'font-size': 11, fill: C.ink }));
  }
  function reset() {
    token++; gen(); draw();
    $('zipMode').innerHTML = mode === 'reg' ? bi('Switch to κ = ℵ<sub>ω</sub>', '切换到 κ = ℵ<sub>ω</sub>') : bi('Back to regular uncountable κ', '回到正则不可数 κ');
    setMsg($('zipMsg'), mode === 'reg' ? bi('κ regular uncountable. Press “Zip”.', 'κ 为正则不可数基数。按“拉链”。') :
      bi('κ = ℵ<sub>ω</sub>, cf κ = ω. C = {ℵ<sub>0</sub>, ℵ<sub>2</sub>, ℵ<sub>4</sub>, …}, D = {ℵ<sub>1</sub>, ℵ<sub>3</sub>, …}. Both are unbounded, and both are closed (no α &lt; ℵ<sub>ω</sub> is a limit of their points). Press “Zip”.', 'κ = ℵ<sub>ω</sub>，cf κ = ω。C = {ℵ<sub>0</sub>, ℵ<sub>2</sub>, ℵ<sub>4</sub>, …}，D = {ℵ<sub>1</sub>, ℵ<sub>3</sub>, …}。两者都无界，也都闭（没有 α &lt; ℵ<sub>ω</sub> 是它们的点的极限）。按“拉链”。'));
  }
  async function zip() {
    const my = ++token;
    draw();
    const seq = mode === 'reg' ? data.Cs.flatMap((c, k) => [[c, 'C'], [data.Ds[k], 'D']]) : data.P.map((x, n) => [x, n % 2 ? 'D' : 'C']);
    let prev = null;
    for (const [x, w] of seq) {
      if (my !== token) return;
      const y = w === 'C' ? AY - 13 : AY + 13;
      el('circle', { cx: x, cy: y, r: 4, fill: w === 'C' ? C.blue : C.red, class: 'pop' }, svg);
      if (prev) el('line', { x1: prev[0], y1: prev[1], x2: x, y2: y, stroke: C.meta, 'stroke-width': 1.5, class: 'fadein' }, svg);
      prev = [x, y];
      await sleep(Math.max(90, 380 - seq.indexOf(seq.find(s => s[0] === x)) * 30));
    }
    if (my !== token) return;
    if (mode === 'reg') {
      const g = el('g', { class: 'pop' }, svg);
      el('circle', { cx: data.g, cy: AY, r: 10, fill: 'none', stroke: C.green, 'stroke-width': 3 }, g);
      el('circle', { cx: data.g, cy: AY, r: 4, fill: C.green }, g);
      T(g, data.g, AY + 62, L2('γ = sup ∈ C ∩ D', 'γ = 上确界 ∈ C ∩ D'), { 'text-anchor': 'middle', fill: C.green, 'font-weight': 700, 'font-size': 12, class: 'lbl' });
      setMsg($('zipMsg'), bi('γ = sup{c₀, d₀, c₁, d₁, …}. This is an ω-sequence and cf κ &gt; ω, so γ &lt; κ. Both C ∩ γ and D ∩ γ are unbounded in γ, so closedness puts γ in C and in D. Start above any β to see that C ∩ D is unbounded; it is closed as an intersection of closed sets. So C ∩ D is club.',
        'γ = sup{c₀, d₀, c₁, d₁, …}。这是 ω 序列，而 cf κ &gt; ω，所以 γ &lt; κ。C ∩ γ 与 D ∩ γ 在 γ 中都无界，由闭性 γ 既属于 C 也属于 D。从任意 β 之上开始拉链，可见 C ∩ D 无界；闭集之交仍闭。所以 C ∩ D 是 club。'), 'ok');
    } else {
      T(svg, 812, 150, L2('escapes to κ', '逃到 κ'), { 'text-anchor': 'end', fill: C.red, 'font-weight': 700, 'font-size': 12, class: 'lbl' });
      setMsg($('zipMsg'), bi('The zipper never lands below κ: its sup is ℵ<sub>ω</sub> itself, because cf(ℵ<sub>ω</sub>) = ω. C ∩ D = ∅ although both are club. This is why stationarity is only studied at uncountable cofinality.', '拉链永远停不到 κ 之下：上确界就是 ℵ<sub>ω</sub> 本身，因为 cf(ℵ<sub>ω</sub>) = ω。C ∩ D = ∅，尽管两者都是 club。这就是平稳性只在不可数共尾性处研究的原因。'), 'bad');
    }
  }
  $('zipGo').addEventListener('click', zip);
  $('zipNew').addEventListener('click', reset);
  $('zipMode').addEventListener('click', () => { mode = mode === 'reg' ? 'om' : 'reg'; reset(); });
  reset();
})();

/* ================= §7 Mahlo ================= */
(function mahlo() {
  const svg = $('mahlo');
  let scen = 'A', token = 0;
  const AY = 100;
  // blue limit points (limits of inaccessibles), accumulating toward κ at 800
  const B = [130, 260, 370, 465, 545, 612, 668, 712, 745, 768, 784, 794];
  const special = new Set([2, 5, 8]); // in scenario B: these limits are themselves inaccessible
  function golds() {
    const out = [];
    let prev = 30;
    B.forEach(b => {
      const gap = b - prev;
      for (let k = 1; k <= 5; k++) out.push(b - gap * Math.pow(0.55, k) * 0.9);
      prev = b;
    });
    return out;
  }
  const G = golds();
  const diamond = (p, x, y, s, fill, stroke) => el('path', { d: `M${x},${y - s} L${x + s},${y} L${x},${y + s} L${x - s},${y} Z`, fill, stroke: stroke || 'none', 'stroke-width': 1.5 }, p);
  function draw() {
    svg.innerHTML = '';
    el('line', { x1: 30, x2: 800, y1: AY, y2: AY, stroke: '#bbb', 'stroke-width': 2 }, svg);
    el('line', { x1: 812, x2: 812, y1: 60, y2: 140, stroke: C.ink, 'stroke-width': 2, 'stroke-dasharray': '4 3' }, svg);
    T(svg, 812, 52, 'κ', { 'text-anchor': 'middle', 'font-weight': 700, 'font-size': 15 });
    G.forEach(x => diamond(svg, x, AY, 4.5, C.gold));
    B.forEach((x, i) => {
      if (scen === 'B' && special.has(i)) { diamond(svg, x, AY, 8, C.gold, C.blue); el('circle', { cx: x, cy: AY, r: 11, fill: 'none', stroke: C.blue, 'stroke-width': 2 }, svg); }
      else el('circle', { cx: x, cy: AY, r: 5, fill: '#fff', stroke: C.blue, 'stroke-width': 2.5 }, svg);
    });
    diamond(svg, 40, 172, 5, C.gold);
    T(svg, 52, 176, L2('inaccessible', '不可达'), { 'font-size': 11, class: 'lbl' });
    el('circle', { cx: 170, cy: 172, r: 5, fill: '#fff', stroke: C.blue, 'stroke-width': 2.5 }, svg);
    T(svg, 182, 176, L2('limit of inaccessibles (singular)', '不可达之极限（奇异）'), { 'font-size': 11, class: 'lbl' });
    if (scen === 'B') {
      diamond(svg, 500, 172, 6, C.gold, C.blue);
      T(svg, 512, 176, L2('inaccessible limit of inaccessibles', '不可达之不可达极限'), { 'font-size': 11, class: 'lbl' });
    }
  }
  async function throwClub() {
    const my = ++token;
    draw();
    if (scen === 'A') {
      for (let i = 0; i < B.length; i++) {
        if (my !== token) return;
        el('line', { x1: B[i], x2: B[i], y1: AY - 34, y2: AY - 12, stroke: C.meta, 'stroke-width': 3, class: 'fadein' }, svg);
        await sleep(120);
      }
      T(svg, 420, 40, L2('club L = limits of inaccessibles: misses every ◆', 'club L = 不可达之极限：一个 ◆ 也碰不到'), { 'text-anchor': 'middle', fill: C.meta, 'font-weight': 700, 'font-size': 12, class: 'lbl' });
      setMsg($('mhMsg'), bi('κ is the least inaccessible limit of inaccessibles. L = {λ &lt; κ : λ a limit of inaccessibles} is club in κ (Step 7 proof). An inaccessible in L would be an inaccessible limit of inaccessibles below κ, contradicting leastness. So L avoids all inaccessibles: they are <b>not stationary</b>, and κ is <b>not Mahlo</b>.',
        'κ 是最小的“不可达基数的不可达极限”。L = {λ &lt; κ : λ 是不可达基数的极限} 是 κ 中的 club（见本步证明）。L 中若有不可达基数，它就是 κ 以下的不可达基数的不可达极限，与最小性矛盾。所以 L 避开了所有不可达基数：它们<b>不平稳</b>，κ <b>不是马洛基数</b>。'), 'bad');
    } else {
      // a random schematic club: accumulation points chosen among some limits, at least one special
      const acc = B.filter((_, i) => Math.random() < 0.45);
      const sp = [...special][Math.floor(Math.random() * special.size)];
      if (!acc.includes(B[sp])) acc.push(B[sp]);
      acc.sort((a, b) => a - b);
      const pts = [];
      let prev = 30;
      acc.forEach(a => {
        const gap = a - prev;
        for (let k = 1; k <= 4; k++) pts.push(a - gap * Math.pow(0.5, k) * (0.6 + 0.3 * Math.random()));
        pts.push(a); prev = a;
      });
      for (let k = 1; k < 6; k++) pts.push(800 - (800 - prev) * Math.pow(0.5, k));
      pts.sort((a, b) => a - b);
      for (const x of pts) {
        if (my !== token) return;
        el('line', { x1: x, x2: x, y1: AY - 34, y2: AY - 12, stroke: C.meta, 'stroke-width': 2.5, class: 'fadein' }, svg);
        await sleep(55);
      }
      if (my !== token) return;
      const hits = acc.filter(a => special.has(B.indexOf(a)));
      hits.forEach(a => {
        const g = el('g', { class: 'pop' }, svg);
        el('circle', { cx: a, cy: AY, r: 16, fill: 'none', stroke: C.green, 'stroke-width': 3 }, g);
      });
      T(svg, 420, 40, L2(`club C meets the inaccessibles (${hits.length} hit${hits.length > 1 ? 's' : ''} shown)`, `club C 碰到了不可达基数（图中 ${hits.length} 处）`), { 'text-anchor': 'middle', fill: C.green, 'font-weight': 700, 'font-size': 12, class: 'lbl' });
      setMsg($('mhMsg'), bi('κ Mahlo: whatever club you throw, some of its points are inaccessible (circled). Press again for another club. Even more is true: intersect C with the club of its own limit points and with the club of limits of inaccessibles; the result still meets the inaccessibles. So C contains inaccessible limits of inaccessibles, as drawn.',
        'κ 是马洛基数：无论扔出哪个 club，总有它的点是不可达基数（绿圈）。再按一次换一个 club。实际上还能更多：把 C 与它自身极限点构成的 club、以及“不可达基数的极限点”构成的 club 相交，结果仍与不可达基数相交。所以 C 中含有“不可达基数的不可达极限”，正如图中所画。'), 'ok');
    }
  }
  function setScen(s) {
    token++; scen = s;
    $('mhA').classList.toggle('sel', s === 'A'); $('mhB').classList.toggle('sel', s === 'B');
    draw();
    setMsg($('mhMsg'), s === 'A' ? bi('Scenario A: inaccessibles are unbounded below κ. Press “Throw a club”.', '情景 A：不可达基数在 κ 下无界。按“扔一个 club”。') :
      bi('Scenario B: κ Mahlo. Some limits of inaccessibles are themselves inaccessible (ringed diamonds). Press “Throw a club”.', '情景 B：κ 是马洛基数。有些不可达基数的极限本身也是不可达的（带圈菱形）。按“扔一个 club”。'));
  }
  $('mhA').addEventListener('click', () => setScen('A'));
  $('mhB').addEventListener('click', () => setScen('B'));
  $('mhClub').addEventListener('click', throwClub);
  setScen('A');
})();

/* ================= Ramsey graph component (§8, E5) ================= */
function monoTriangles(n, col) {
  const out = [];
  const c = (i, j) => col[i < j ? i + '-' + j : j + '-' + i] || 0;
  for (let i = 0; i < n; i++) for (let j = i + 1; j < n; j++) for (let k = j + 1; k < n; k++) {
    const a = c(i, j);
    if (a && a === c(i, k) && a === c(j, k)) out.push([i, j, k, a]);
  }
  return out;
}
function RamseyGraph(svg, opts = {}) {
  const S = { n: opts.n || 6, col: {}, onChange: opts.onChange || (() => {}), extra: [] };
  const CX = 190, CY = 170, R = 130;
  const pos = i => [CX + R * Math.cos(-Math.PI / 2 + 2 * Math.PI * i / S.n), CY + R * Math.sin(-Math.PI / 2 + 2 * Math.PI * i / S.n)];
  const COL = ['#c9c4b6', C.red, C.blue];
  S.key = (i, j) => (i < j ? i + '-' + j : j + '-' + i);
  S.complete = () => { for (let i = 0; i < S.n; i++) for (let j = i + 1; j < S.n; j++) if (!S.col[S.key(i, j)]) return false; return true; };
  S.tris = () => monoTriangles(S.n, S.col);
  S.draw = (hl = {}) => {
    svg.innerHTML = '';
    const tris = S.tris();
    tris.forEach(([i, j, k, a]) => {
      const p = [pos(i), pos(j), pos(k)];
      el('polygon', { points: p.map(q => q.join(',')).join(' '), fill: a === 1 ? 'rgba(224,49,49,.16)' : 'rgba(59,91,219,.16)', class: 'fadein' }, svg);
    });
    for (let i = 0; i < S.n; i++) for (let j = i + 1; j < S.n; j++) {
      const k = S.key(i, j), [x1, y1] = pos(i), [x2, y2] = pos(j), c = S.col[k] || 0;
      const thick = hl.edges && hl.edges.includes(k);
      el('line', { x1, y1, x2, y2, stroke: COL[c], 'stroke-width': thick ? 7 : c ? 3.5 : 2, 'stroke-dasharray': c ? '' : '5 5', opacity: hl.edges && !thick ? 0.35 : 1 }, svg);
      const hit = el('line', { x1, y1, x2, y2, stroke: 'transparent', 'stroke-width': 14, class: 'hit' }, svg);
      hit.addEventListener('click', () => { S.col[k] = ((S.col[k] || 0) + 1) % 3; S.draw(); S.onChange(S); });
    }
    for (let i = 0; i < S.n; i++) {
      const [x, y] = pos(i);
      el('circle', { cx: x, cy: y, r: 13, fill: hl.v === i ? C.gold : '#fff', stroke: C.ink, 'stroke-width': 2 }, svg);
      T(svg, x, y + 4, String(i + 1), { 'text-anchor': 'middle', 'font-size': 12, 'font-weight': 700 });
    }
  };
  S.setN = n => { S.n = n; S.col = {}; S.draw(); S.onChange(S); };
  S.clear = () => { S.col = {}; S.draw(); S.onChange(S); };
  S.random = () => { for (let i = 0; i < S.n; i++) for (let j = i + 1; j < S.n; j++) S.col[S.key(i, j)] = 1 + (Math.random() < .5 ? 1 : 0); S.draw(); S.onChange(S); };
  S.draw();
  return S;
}

(function ramsey() {
  const box = $('rgMsg');
  let busy = 0;
  const report = S => {
    const t = S.tris(), full = S.complete();
    if (t.length) setMsg(box, bi(`Monochromatic triangle${t.length > 1 ? 's' : ''}: ${t.map(x => '{' + x.slice(0, 3).map(v => v + 1).join(',') + '}').join(' ')}.`, `同色三角形：${t.map(x => '{' + x.slice(0, 3).map(v => v + 1).join(',') + '}').join(' ')}。`), 'warn');
    else if (full) setMsg(box, bi(`Every edge of K${S.n} is colored and there is no monochromatic triangle.${S.n === 5 ? ' This is why R(3,3) &gt; 5.' : ''}`, `K${S.n} 的边全部染好，且没有同色三角形。${S.n === 5 ? '这说明 R(3,3) &gt; 5。' : ''}`), 'ok');
    else setMsg(box, bi('Keep coloring. Grey dashed edges are uncolored.', '继续染色。灰色虚线是尚未染色的边。'));
  };
  const G = RamseyGraph($('rg'), { n: 6, onChange: report });
  const nb = $('rgN');
  nb.innerHTML = `<span class="lab">${bil('Graph:', '图：')}</span>`;
  const nBtns = [4, 5, 6].map(n => {
    const b = btn('K' + '₄₅₆'[n - 4]);
    b.addEventListener('click', () => { busy++; nBtns.forEach(x => x.classList.toggle('sel', x === b)); G.setN(n); });
    nb.appendChild(b);
    return b;
  });
  nBtns[2].classList.add('sel');
  $('rgRand').addEventListener('click', () => { busy++; G.random(); });
  $('rgClear').addEventListener('click', () => { busy++; G.clear(); });
  $('rgProof').addEventListener('click', async () => {
    const my = ++busy;
    if (G.n !== 6) { nBtns.forEach(x => x.classList.toggle('sel', x === nBtns[2])); G.setN(6); }
    if (!G.complete()) G.random();
    const others = [1, 2, 3, 4, 5];
    const byCol = { 1: others.filter(j => G.col[G.key(0, j)] === 1), 2: others.filter(j => G.col[G.key(0, j)] === 2) };
    G.draw({ v: 0, edges: others.map(j => G.key(0, j)) });
    setMsg(box, bi('Step 1. Look at vertex 1 and its 5 edges.', '第 1 步：看顶点 1 和它的 5 条边。'));
    await sleep(1500); if (my !== busy) return;
    const c = byCol[1].length >= 3 ? 1 : 2, nbrs = byCol[c].slice(0, 3);
    const cn = c === 1 ? ['red', '红'] : ['blue', '蓝'];
    G.draw({ v: 0, edges: nbrs.map(j => G.key(0, j)) });
    setMsg(box, bi(`Step 2. Pigeonhole: 5 edges, 2 colors, so at least 3 share a color. Here ${cn[0]}: to ${nbrs.map(v => v + 1).join(', ')}.`, `第 2 步：鸽笼原理。5 条边 2 种颜色，至少 3 条同色。这里是${cn[1]}色：连向 ${nbrs.map(v => v + 1).join('、')}。`));
    await sleep(2200); if (my !== busy) return;
    const inner = [[nbrs[0], nbrs[1]], [nbrs[0], nbrs[2]], [nbrs[1], nbrs[2]]];
    const same = inner.find(([a, b]) => G.col[G.key(a, b)] === c);
    if (same) {
      G.draw({ v: 0, edges: [G.key(0, same[0]), G.key(0, same[1]), G.key(same[0], same[1])] });
      setMsg(box, bi(`Step 3. Among ${nbrs.map(v => v + 1).join(', ')}, the edge {${same[0] + 1},${same[1] + 1}} is ${cn[0]} too, giving a ${cn[0]} triangle with vertex 1. ∎`, `第 3 步：在 ${nbrs.map(v => v + 1).join('、')} 之间，边 {${same[0] + 1},${same[1] + 1}} 也是${cn[1]}色，与顶点 1 构成${cn[1]}色三角形。∎`), 'ok');
    } else {
      G.draw({ edges: inner.map(([a, b]) => G.key(a, b)) });
      setMsg(box, bi(`Step 3. No edge among ${nbrs.map(v => v + 1).join(', ')} is ${cn[0]}, so all three have the other color: a monochromatic triangle. ∎`, `第 3 步：${nbrs.map(v => v + 1).join('、')} 之间没有${cn[1]}色边，所以三条边都是另一种颜色：同色三角形。∎`), 'ok');
    }
  });
  G.random();
})();

/* ================= §9 Kőnig tree ================= */
(function konig() {
  const svg = $('tree');
  const D = 6;
  let nodes, root, path, showAll = false, token = 0;
  function gen() {
    for (let tries = 0; tries < 400; tries++) {
      nodes = [];
      const mk = (depth, parent) => { const n = { id: nodes.length, depth, parent, ch: [] }; nodes.push(n); return n; };
      root = mk(0, null);
      const levels = [[root]];
      let ok = true;
      for (let d = 0; d < D; d++) {
        const next = [];
        levels[d].forEach(p => {
          let k = d === 0 ? 3 : [0, 0, 1, 1, 1, 2, 2, 2, 3][Math.floor(Math.random() * 9)];
          for (let i = 0; i < k; i++) { const c = mk(d + 1, p); p.ch.push(c); next.push(c); }
        });
        if (next.length > 15 || next.length === 0) { ok = false; break; }
        levels.push(next);
      }
      if (!ok) continue;
      nodes.forEach(n => { n.alive = undefined; });
      const alive = n => (n.alive !== undefined ? n.alive : (n.alive = n.depth === D || n.ch.some(alive)));
      nodes.forEach(alive);
      const dead = nodes.filter(n => !n.alive).length;
      const deadRootKids = root.ch.filter(c => !c.alive).length;
      if (root.alive && dead >= 6 && deadRootKids >= 1) break;
    }
    // layout
    let leaf = 0;
    const lay = n => { if (!n.ch.length) n.x = leaf++; else { n.ch.forEach(lay); n.x = (n.ch[0].x + n.ch[n.ch.length - 1].x) / 2; } };
    lay(root);
    const W = 800 / Math.max(leaf, 1);
    nodes.forEach(n => { n.px = 30 + (n.x + 0.5) * W; n.py = 25 + n.depth * 50; });
  }
  function draw() {
    svg.innerHTML = '';
    for (let d = 0; d <= D; d++) T(svg, 4, 29 + d * 50, String(d), { 'font-size': 11, fill: C.grey });
    const onPath = new Set(path.map(n => n.id));
    nodes.forEach(n => { if (n.parent) el('line', { x1: n.parent.px, y1: n.parent.py, x2: n.px, y2: n.py, stroke: onPath.has(n.id) && onPath.has(n.parent.id) ? C.blue : '#c9c4b6', 'stroke-width': onPath.has(n.id) && onPath.has(n.parent.id) ? 4 : 1.8 }, svg); });
    nodes.forEach(n => {
      const known = showAll || onPath.has(n.id);
      const fill = known ? (n.alive ? '#d3f9d8' : '#e9ecef') : '#fff';
      const stroke = onPath.has(n.id) ? C.blue : known ? (n.alive ? C.green : C.grey) : C.ink;
      const g = el('g', { class: 'hit' }, svg);
      el('circle', { cx: n.px, cy: n.py, r: 9, fill, stroke, 'stroke-width': onPath.has(n.id) ? 3 : 1.6 }, g);
      g.addEventListener('click', () => click(n));
    });
    el('line', { x1: 20, x2: 840, y1: 25 + D * 50 + 18, y2: 25 + D * 50 + 18, stroke: C.gold, 'stroke-dasharray': '4 4' }, svg);
    T(svg, 838, 25 + D * 50 + 36, L2('bottom row = stand-in for “infinitely far”', '最底层＝“无穷远”的替身'), { 'text-anchor': 'end', 'font-size': 11, fill: C.gold, class: 'lbl' });
  }
  function click(n) {
    token++;
    const last = path[path.length - 1];
    if (n.parent !== last) { setMsg($('trMsg'), bi('Click a child of the last node on your path (blue).', '请点击路径（蓝色）末端节点的某个子节点。'), 'warn'); return; }
    path.push(n); draw(); report();
  }
  function report() {
    const last = path[path.length - 1];
    if (last.depth === D) setMsg($('trMsg'), bi(`You reached the bottom: a branch through all ${D + 1} levels. In the infinite tree, Kőnig’s rule continues forever and yields an infinite branch.`, `到达底层：一条穿过全部 ${D + 1} 层的枝。在无穷树中，柯尼希的规则可以永远走下去，得到一条无穷枝。`), 'ok');
    else if (!last.alive) setMsg($('trMsg'), bi(`Dead end: this node has no descendants on the bottom row (in the infinite picture: only finitely many descendants). Kőnig’s rule would never step here. Restart the walk.`, '死胡同：这个节点在最底层没有后代（在无穷的情形里：只有有限多个后代）。柯尼希的规则绝不会走到这里。请重新开始。'), 'bad');
    else setMsg($('trMsg'), bi(`Level ${last.depth}: still alive. Of its ${last.ch.length} children, ${last.ch.filter(c => c.alive).length} are alive.`, `第 ${last.depth} 层：仍然是活的。它的 ${last.ch.length} 个子节点中有 ${last.ch.filter(c => c.alive).length} 个是活的。`));
  }
  function restart() { token++; path = [root]; draw(); setMsg($('trMsg'), bi('Start at the root (level 0). Click a child.', '从根（第 0 层）出发，点击一个子节点。')); }
  $('trNew').addEventListener('click', () => { gen(); restart(); });
  $('trReset').addEventListener('click', restart);
  $('trShow').addEventListener('click', () => { showAll = !showAll; draw(); });
  $('trKonig').addEventListener('click', async () => {
    const my = ++token;
    path = [root]; draw();
    while (path[path.length - 1].depth < D) {
      await sleep(450); if (my !== token) return;
      const last = path[path.length - 1];
      path.push(last.ch.find(c => c.alive)); draw();
      setMsg($('trMsg'), bi(`Kőnig: among ${last.ch.length} children, at least one has “infinitely many” descendants; step there.`, `柯尼希：${last.ch.length} 个子节点中至少有一个有“无穷多”后代，就走那一个。`));
    }
    report();
  });
  gen(); restart();
})();

/* ================= §10 reflection machine ================= */
const RK = [
  { id: 'i', rank: 1, en: 'least inaccessible', zh: '最小不可达' },
  { id: 'm', rank: 2, en: 'least Mahlo', zh: '最小马洛' },
  { id: 'w', rank: 3, en: 'least weakly compact', zh: '最小弱紧' },
  { id: 'p', rank: 4, en: 'a Π¹₂-indescribable', zh: '某个 Π¹₂-不可描述基数', notLeast: true },
];
const RP = [
  { lvl: 0, cx: 'Π¹₁', en: 'Ord is uncountable and regular', zh: 'Ord 不可数且正则', f: '∃ uncountable ordinal ∧ ∀X ∀β (X: β → Ord ⇒ ran X bounded)' },
  { lvl: 1, cx: 'Π¹₁', en: 'Ord is inaccessible', zh: 'Ord 不可达', f: 'regular ∧ uncountable ∧ ∀β ∃ ordinal ≈ P(β)' },
  { lvl: 2, cx: 'Π¹₁', en: 'Ord is Mahlo', zh: 'Ord 是马洛的', f: 'inaccessible ∧ ∀X (X club → ∃λ ∈ X inaccessible)' },
  { lvl: 3, cx: 'Π¹₂', en: 'Ord is weakly compact', zh: 'Ord 是弱紧的', f: 'inaccessible ∧ ∀T (T a tree … → ∃B cofinal branch)' },
];
// Outcome of reflecting sentence p at cardinal k: 'false' | 'fails' | 'reflects'
function reflectOutcome(k, p) {
  const trueAtK = p.lvl === 0 || k.rank >= p.lvl;
  if (!trueAtK) return 'false';
  if (p.lvl === 0) return 'reflects';
  return p.lvl < k.rank ? 'reflects' : 'fails';
}
(function reflMachine() {
  let K = RK[0], P = RP[1], token = 0;
  const kb = $('rfK'), pb = $('rfP');
  kb.innerHTML = `<span class="lab">κ =</span>`;
  pb.innerHTML = `<span class="lab">φ =</span>`;
  const kBtns = RK.map(k => { const b = btn(bil(k.en, k.zh)); b.addEventListener('click', () => { K = k; run(); }); kb.appendChild(b); return [k, b]; });
  const pBtns = RP.map(p => { const b = btn(`<span class="m">${p.cx}</span> ` + bil(p.en, p.zh)); b.addEventListener('click', () => { P = p; run(); }); pb.appendChild(b); return [p, b]; });
  const svg = $('refl');
  const tower = (cx, top, w, col, lab, fill) => {
    el('path', { d: `M${cx - w},${top} L${cx},245 L${cx + w},${top} Z`, fill, stroke: col, 'stroke-width': 2.5 }, svg);
    TS(svg, cx, top - 8, lab, { 'text-anchor': 'middle', 'font-weight': 700, 'font-size': 15, fill: col, class: 'lbl' });
  };
  function witness(k, p) {
    if (p.lvl === 0) return ['α = ω₁ works: V<sub>ω₁</sub> sees that ω₁ is uncountable and regular.', 'α = ω₁ 即可：V<sub>ω₁</sub> 看到 ω₁ 不可数且正则。'];
    if (p.lvl === 1) return ['any inaccessible α &lt; κ works (there are stationarily many).', '任取一个不可达 α &lt; κ 即可（平稳多个）。'];
    if (p.lvl === 2) return ['any Mahlo α &lt; κ works (stationarily many, by the theorem below).', '任取一个马洛基数 α &lt; κ 即可（由下方定理，平稳多个）。'];
    return ['any weakly compact α &lt; κ works (stationarily many below a Π¹₂-indescribable).', '任取一个弱紧 α &lt; κ 即可（Π¹₂-不可描述基数之下有平稳多个）。'];
  }
  async function run() {
    const my = ++token;
    kBtns.forEach(([k, b]) => b.classList.toggle('sel', k === K));
    pBtns.forEach(([p, b]) => b.classList.toggle('sel', p === P));
    svg.innerHTML = '';
    tower(540, 30, 210, C.ink, 'V_κ', '#fff');
    T(svg, 540, 62, P.cx + ': ' + P.en, { 'text-anchor': 'middle', 'font-size': 13, 'font-weight': 700, fill: C.meta, class: 'lbl' });
    T(svg, 540, 80, P.zh, { 'text-anchor': 'middle', 'font-size': 12, fill: C.meta, class: 'lbl' });
    T(svg, 540, 98, P.f, { 'text-anchor': 'middle', 'font-size': 10, fill: C.grey });
    const out = reflectOutcome(K, P);
    await sleep(350); if (my !== token) return;
    if (out === 'false') {
      T(svg, 540, 130, L2('false at κ', '在 κ 处为假'), { 'text-anchor': 'middle', 'font-size': 13, 'font-weight': 700, fill: C.red, class: 'lbl' });
      setMsg($('rfMsg'), bi(`φ is <b>false</b> in V<sub>κ</sub>: the ${K.en} is not ${P.en.replace('Ord is ', '')}. Nothing to reflect.`, `φ 在 V<sub>κ</sub> 中<b>为假</b>：${K.zh}基数不满足“${P.zh.replace('Ord ', '')}”。没有可反射的东西。`), 'warn');
      return;
    }
    T(svg, 540, 130, L2('true at κ ✓', '在 κ 处为真 ✓'), { 'text-anchor': 'middle', 'font-size': 13, 'font-weight': 700, fill: C.green, class: 'lbl' });
    await sleep(500); if (my !== token) return;
    const arrow = el('path', { d: 'M345,120 C300,95 260,105 235,135', fill: 'none', stroke: out === 'reflects' ? C.green : C.red, 'stroke-width': 3, 'stroke-dasharray': out === 'reflects' ? '' : '7 5', class: 'fadein' }, svg);
    if (out === 'reflects') {
      tower(150, 110, 80, C.green, 'V_α', '#d3f9d8');
      T(svg, 150, 255, '(α < κ)', { 'text-anchor': 'middle', 'font-size': 12, fill: C.green });
      T(svg, 150, 160, 'φ ✓', { 'text-anchor': 'middle', 'font-size': 16, 'font-weight': 700, fill: C.green });
      const w = witness(K, P);
      setMsg($('rfMsg'), bi(`<b>Reflects.</b> ${w[0]}`, `<b>能反射.</b> ${w[1]}`), 'ok');
    } else {
      T(svg, 150, 140, '✗', { 'text-anchor': 'middle', 'font-size': 40, 'font-weight': 700, fill: C.red });
      T(svg, 150, 175, L2('no α < κ works', '没有 α < κ 满足'), { 'text-anchor': 'middle', 'font-size': 12, fill: C.red, class: 'lbl' });
      setMsg($('rfMsg'), bi(`<b>Fails to reflect.</b> κ is the <i>least</i> cardinal with this property, so φ describes κ from below. Hence κ is not ${P.cx}-indescribable.`, `<b>反射失败.</b> κ 是具有此性质的<i>最小</i>基数，φ 从下方把 κ 描述出来了。所以 κ 不是 ${P.cx}-不可描述的。`), 'bad');
    }
    void arrow;
  }
  run();
})();

/* ================= §11 ladder ================= */
(function ladder() {
  const R = [
    { en: 'ZFC', zh: 'ZFC', info: ['Base theory. If consistent, it cannot prove Con(ZFC) (Gödel 2).', '基础理论。若一致，则证明不了 Con(ZFC)（哥德尔第二定理）。'] },
    { en: 'worldly', zh: 'worldly', info: ['V<sub>κ</sub> ⊨ ZFC. ZFC + ∃worldly ⊢ Con(ZFC). The least worldly cardinal is singular (cf ω).', 'V<sub>κ</sub> ⊨ ZFC。ZFC + 存在 worldly ⊢ Con(ZFC)。最小的 worldly 基数是奇异的（cf ω）。'] },
    { en: 'inaccessible', zh: '不可达', info: ['Weakly ~ strongly inaccessible (equiconsistent via L, Step 5). V<sub>κ</sub> ⊨ ZFC + “there are worldly cardinals”, so ZFC + ∃inacc ⊢ Con(ZFC + ∃worldly).', '弱不可达与强不可达等相容（通过 L，第 5 步）。V<sub>κ</sub> ⊨ ZFC + “存在 worldly 基数”，所以 ZFC + 存在不可达 ⊢ Con(ZFC + 存在 worldly)。'] },
    { en: 'α-inaccessible, hyper-inacc.', zh: 'α-不可达、超不可达', info: ['Inaccessible limits of inaccessibles, iterated through all α. If κ is 1-inaccessible, V<sub>κ</sub> ⊨ ZFC + “a proper class of inaccessibles”. “Hyper-inaccessible” is ambiguous: check the definition.', '不可达基数的不可达极限，并对所有 α 迭代。若 κ 是 1-不可达的，则 V<sub>κ</sub> ⊨ ZFC + “不可达基数构成真类”。“超不可达”一词有歧义，需看定义。'] },
    { en: 'Mahlo', zh: '马洛', info: ['The inaccessibles below κ are stationary. κ is α-inaccessible for all α ≤ κ. Weakly Mahlo ~ Mahlo (equiconsistent via L).', 'κ 以下的不可达基数平稳。对所有 α ≤ κ，κ 都是 α-不可达的。弱马洛与马洛等相容（通过 L）。'] },
    { en: 'weakly compact = Π¹₁-indescr.', zh: '弱紧 = Π¹₁-不可描述', info: ['κ → (κ)²₂ ⇔ inaccessible + tree property ⇔ Π¹₁-indescribable ⇔ L<sub>κ,κ</sub> weak compactness. The Mahlos below κ are stationary. Weakly compact cardinals remain weakly compact in L.', 'κ → (κ)²₂ ⇔ 不可达 + 树性质 ⇔ Π¹₁-不可描述 ⇔ L<sub>κ,κ</sub> 弱紧致性。κ 以下的马洛基数平稳。弱紧基数在 L 中仍是弱紧的。'] },
    { en: 'Π¹ₙ-indescribable', zh: 'Π¹ₙ-不可描述', info: ['Each Π¹<sub>n+1</sub>-indescribable has stationarily many Π¹<sub>n</sub>-indescribables below it. The least weakly compact is not Π¹₂-indescribable.', '每个 Π¹<sub>n+1</sub>-不可描述基数之下都有平稳多个 Π¹<sub>n</sub>-不可描述基数。最小弱紧基数不是 Π¹₂-不可描述的。'] },
    { en: 'totally indescribable', zh: '完全不可描述', info: ['Π<sup>m</sup><sub>n</sub>-indescribable for all m, n: no finite-order sentence (with a predicate) singles κ out.', '对所有 m、n 都 Π<sup>m</sup><sub>n</sub>-不可描述：任何有限阶语句（带谓词）都无法把 κ 单独挑出。'] },
    { en: '… unfoldable, subtle, ineffable, Ramsey …', zh: '…… 可展开、subtle、ineffable、拉姆齐 ……', gap: true, info: ['Many more rungs (see Wikipedia’s list). Around here the axioms start to contradict V = L: e.g. a Ramsey cardinal implies that 0<sup>#</sup> exists.', '这里还有许多级（见维基百科的列表）。大约从这里开始，公理与 V = L 矛盾：例如拉姆齐基数蕴涵 0<sup>#</sup> 存在。'] },
    { en: 'measurable → L24', zh: '可测 → 第 24 课', link: 'lesson24.html', info: ['A κ-complete nonprincipal ultrafilter on κ; equivalently an elementary embedding j: V → M with critical point κ. Implies V ≠ L (Scott). Every measurable is weakly compact and a limit of weakly compacts.', 'κ 上的 κ-完全非主超滤子；等价于临界点为 κ 的初等嵌入 j: V → M。蕴涵 V ≠ L（Scott）。每个可测基数都是弱紧的，并且是弱紧基数的极限。'] },
    { en: 'Woodin … huge … I0 → L25', zh: '伍丁……巨大……I0 → 第 25 课', link: 'lesson25.html', info: ['Strong, Woodin, supercompact, huge, rank-into-rank; their link to determinacy. Beyond them: Reinhardt cardinals are inconsistent with ZFC (Kunen) but not known to be inconsistent with ZF.', '强基数、伍丁基数、超紧、巨大、秩入秩；以及它们与决定性的联系。再往上：莱因哈特基数与 ZFC 矛盾（Kunen），但目前不知道是否与 ZF 矛盾。'] },
  ];
  const svg = $('ladder');
  let sel = 5;
  function draw() {
    svg.innerHTML = '';
    el('line', { x1: 40, x2: 40, y1: 10, y2: 550, stroke: '#d8d3c4', 'stroke-width': 6 }, svg);
    el('line', { x1: 360, x2: 360, y1: 10, y2: 550, stroke: '#d8d3c4', 'stroke-width': 6 }, svg);
    T(svg, 20, 280, '', {});
    R.forEach((r, i) => {
      const y = 525 - i * 48, on = i === sel;
      const g = el('g', { class: 'hit' }, svg);
      el('rect', { x: 50, y: y - 17, width: 300, height: 34, rx: 9, fill: on ? '#e7ecff' : r.gap ? '#f6f4ee' : i >= 9 ? '#fff0f6' : '#fff', stroke: on ? C.blue : r.gap ? '#c9c4b6' : i >= 9 ? '#c2255c' : C.ink, 'stroke-width': on ? 3 : 1.5, 'stroke-dasharray': r.gap ? '5 4' : '' }, g);
      T(g, 200, y - 1, r.en, { 'text-anchor': 'middle', 'font-size': 12.5, 'font-weight': 700, class: 'lbl' });
      T(g, 200, y + 12, r.zh, { 'text-anchor': 'middle', 'font-size': 10.5, fill: '#4a5568', class: 'lbl' });
      g.addEventListener('click', () => { sel = i; draw(); info(); });
    });
    el('path', { d: 'M20,520 L20,30', stroke: C.meta, 'stroke-width': 2.5 }, svg);
    el('path', { d: 'M20,22 l-6,12 h12 z', fill: C.meta }, svg);
    const t = T(svg, 14, 300, L2('stronger', '更强'), { 'font-size': 11, fill: C.meta, transform: 'rotate(-90 14 300)', 'text-anchor': 'middle', class: 'lbl' });
    void t;
  }
  function info() {
    const r = R[sel];
    const prev = sel > 0 ? R[sel - 1] : null;
    const extra = prev && !r.gap && sel <= 7 ? `<div class="muted" style="margin-top:6px">${bi(`ZFC + this rung ⊢ Con(ZFC + ${prev.en}).`, `ZFC + 本级 ⊢ Con(ZFC + ${prev.zh})。`)}</div>` : '';
    const link = r.link ? bi(` <a href="${r.link}">Go →</a>`, ` <a href="${r.link}">前往 →</a>`) : '';
    setMsg($('ldMsg'), `<b>${bil(r.en, r.zh)}</b><br>` + bi(r.info[0], r.info[1]) + extra + link);
  }
  draw(); info();
})();

/* ================= generic choice list (E2, E4, E6) ================= */
function choiceList(container, items, prog, optsDefault) {
  const solved = items.map(() => false);
  const done = () => { if (solved.every(Boolean)) { Progress.mark(prog); container.closest('.ex').classList.add('done'); } };
  items.forEach((it, idx) => {
    const row = document.createElement('div');
    row.className = 'tfrow';
    const opts = it.opts || optsDefault;
    row.innerHTML = `<div class="stmt">${idx + 1}. ${bi(it.s[0], it.s[1])}${it.pic ? `<div>${it.pic}</div>` : ''}</div><div class="toolbar" style="margin:0"></div><div class="why msg"></div>`;
    const bar = row.querySelector('.toolbar'), why = row.querySelector('.why');
    let revealed = false;
    const bs = opts.map((o, i) => {
      const b = btn(bil(o[0], o[1]));
      b.addEventListener('click', () => {
        bs.forEach(x => x.classList.remove('sel'));
        b.classList.add('sel');
        const ok = i === it.a;
        if (ok && !revealed) { solved[idx] = true; done(); }
        setMsg(why, (ok ? '✓ ' : '✗ ') + (ok ? bi(it.why[0], it.why[1]) : bi('Not quite. Think again, or press “Show answer”.', '不太对。再想想，或按“显示答案”。')), ok ? 'ok' : 'bad');
      });
      bar.appendChild(b);
      return b;
    });
    const sh = btn(bil('Show answer', '显示答案'), 'btn small ghost');
    sh.addEventListener('click', () => {
      revealed = true;
      bs.forEach((x, i) => x.classList.toggle('sel', i === it.a));
      setMsg(why, bi(`Answer: <b>${opts[it.a][0]}</b>. ${it.why[0]}`, `答案：<b>${opts[it.a][1]}</b>。${it.why[1]}`), 'info');
    });
    bar.appendChild(sh);
    container.appendChild(row);
  });
}
const TF = [['True', '对'], ['False', '错']];

/* ---- E1 classify ---- */
const E1_ROWS = [
  { lab: 'ℵ₀', a: ['Y', 'Y', 'Y', 'N'], why: ['ℵ₀ is regular and a strong limit, but inaccessibility requires uncountability.', 'ℵ₀ 正则且是强极限，但不可达要求不可数。'] },
  { lab: 'ℵ<sub>ω</sub>', a: ['N', 'Y', 'U', 'N'], why: ['cf ℵ<sub>ω</sub> = ω. Strong limit: yes under GCH, no if 2<sup>ℵ₀</sup> = ℵ<sub>ω+1</sub>.', 'cf ℵ<sub>ω</sub> = ω。强极限：GCH 下是，若 2<sup>ℵ₀</sup> = ℵ<sub>ω+1</sub> 则否。'] },
  { lab: 'ℵ<sub>ω+1</sub>', a: ['Y', 'N', 'N', 'N'], why: ['A successor cardinal: regular (AC) but not a limit, and 2<sup>ℵ<sub>ω</sub></sup> ≥ ℵ<sub>ω+1</sub>.', '后继基数：正则（选择公理）但不是极限，且 2<sup>ℵ<sub>ω</sub></sup> ≥ ℵ<sub>ω+1</sub>。'] },
  { lab: 'ℵ<sub>ℵ<sub>ω</sub></sub>', a: ['N', 'Y', 'U', 'N'], why: ['cf(ℵ<sub>ℵ<sub>ω</sub></sub>) = cf(ℵ<sub>ω</sub>) = ω. Index ℵ<sub>ω</sub> is a limit ordinal, so it is a limit cardinal. Strong limit: independent, as for ℵ<sub>ω</sub>.', 'cf(ℵ<sub>ℵ<sub>ω</sub></sub>) = cf(ℵ<sub>ω</sub>) = ω。下标 ℵ<sub>ω</sub> 是极限序数，所以它是极限基数。强极限：与 ℵ<sub>ω</sub> 一样，独立于 ZFC。'] },
  { lab: 'κ₀', a: ['N', 'Y', 'U', 'N'], why: ['κ₀ = sup{ω, ℵ<sub>ω</sub>, ℵ<sub>ℵ<sub>ω</sub></sub>, …} has cofinality ω. Strong limit: yes under GCH; it is consistent that 2<sup>ℵ₀</sup> &gt; κ₀.', 'κ₀ = sup{ω, ℵ<sub>ω</sub>, ℵ<sub>ℵ<sub>ω</sub></sub>, …} 的共尾性为 ω。强极限：GCH 下是；2<sup>ℵ₀</sup> &gt; κ₀ 也是一致的。'] },
];
(function e1() {
  const cols = [['regular', '正则'], ['limit', '极限'], ['strong limit', '强极限'], ['inaccessible', '不可达']];
  const cyc = ['', 'Y', 'N', 'U'];
  const show = v => v === 'Y' ? bil('yes', '是') : v === 'N' ? bil('no', '否') : v === 'U' ? '?' : '';
  const st = E1_ROWS.map(() => cols.map(() => ''));
  let revealed = false;
  let h = `<table class="cls"><tr><th></th>${cols.map(c => `<th>${bil(c[0], c[1])}</th>`).join('')}</tr>`;
  E1_ROWS.forEach((r, i) => { h += `<tr><td class="lbl">${r.lab}</td>${cols.map((_, j) => `<td class="click" data-i="${i}" data-j="${j}"></td>`).join('')}</tr>`; });
  $('e1T').innerHTML = h + '</table>';
  const cells = [...$('e1T').querySelectorAll('td.click')];
  cells.forEach(td => td.addEventListener('click', () => {
    const i = +td.dataset.i, j = +td.dataset.j;
    st[i][j] = cyc[(cyc.indexOf(st[i][j]) + 1) % 4];
    td.innerHTML = show(st[i][j]); td.classList.remove('right', 'wrong');
  }));
  $('e1C').addEventListener('click', () => {
    let wrong = 0, blank = 0;
    cells.forEach(td => {
      const i = +td.dataset.i, j = +td.dataset.j;
      td.classList.remove('right', 'wrong');
      if (!st[i][j]) { blank++; return; }
      const ok = st[i][j] === E1_ROWS[i].a[j];
      td.classList.add(ok ? 'right' : 'wrong');
      if (!ok) wrong++;
    });
    if (!wrong && !blank) { if (!revealed) { Progress.mark('L23E1'); $('e1').classList.add('done'); } setMsg($('e1M'), bi('All correct! Note the three “?” cells: strong-limitness at singular cardinals depends on the continuum function, which ZFC leaves open.', '全对！注意三个“?”：奇异基数处是否为强极限取决于连续统函数，ZFC 对此不作决定。'), 'ok'); }
    else setMsg($('e1M'), bi(`${wrong} wrong (red), ${blank} blank.`, `${wrong} 处错误（红色），${blank} 处空白。`), 'bad');
  });
  $('e1S').addEventListener('click', () => {
    revealed = true;
    cells.forEach(td => { const i = +td.dataset.i, j = +td.dataset.j; st[i][j] = E1_ROWS[i].a[j]; td.innerHTML = show(st[i][j]); td.classList.remove('wrong'); td.classList.add('right'); });
    setMsg($('e1M'), E1_ROWS.map(r => `<b>${r.lab}</b>: ` + bi(r.why[0], r.why[1])).join(''), 'info');
  });
})();

/* ---- E2 club / stationary ---- */
function picLimit(included) {
  const xs = [30, 120, 170, 200, 218, 229, 236, 240];
  return `<svg viewBox="0 0 330 46" width="330" height="46"><line x1="10" y1="24" x2="320" y2="24" stroke="#bbb" stroke-width="2"/>` +
    xs.map(x => `<line x1="${x}" y1="14" x2="${x}" y2="34" stroke="${C.blue}" stroke-width="2"/>`).join('') +
    `<circle cx="250" cy="24" r="6" fill="${included ? C.blue : '#fff'}" stroke="${C.blue}" stroke-width="2"/>` +
    `<text x="250" y="44" text-anchor="middle" font-size="11">λ &lt; κ</text><text x="318" y="18" text-anchor="end" font-size="12" font-weight="700">κ</text></svg>`;
}
choiceList($('e2L'), [
  { s: ['The set of limit ordinals below κ is club in κ.', 'κ 以下的极限序数构成 κ 中的 club。'], a: 0, why: ['A limit of limit ordinals is a limit ordinal (closed), and above any β there is β+ω (unbounded).', '极限序数的极限仍是极限序数（闭）；任意 β 之上有 β+ω（无界）。'] },
  { s: ['The set of successor ordinals below κ is stationary.', 'κ 以下的后继序数构成平稳集。'], a: 1, why: ['It is disjoint from the club of limit ordinals.', '它与“极限序数”这个 club 不相交。'] },
  { s: ['Every stationary subset of κ is unbounded in κ.', 'κ 的每个平稳子集都在 κ 中无界。'], a: 0, why: ['If S ⊆ β &lt; κ, then the club {γ : β &lt; γ &lt; κ} misses S.', '若 S ⊆ β &lt; κ，则 club {γ : β &lt; γ &lt; κ} 与 S 不相交。'] },
  { s: ['If C and D are club in κ, then C ∩ D is club.', '若 C、D 是 κ 中的 club，则 C ∩ D 也是 club。'], a: 0, why: ['The zipper argument; it uses cf κ &gt; ω.', '拉拉链论证；用到 cf κ &gt; ω。'] },
  { s: ['If S and T are stationary in κ, then S ∩ T is stationary.', '若 S、T 在 κ 中平稳，则 S ∩ T 平稳。'], a: 1, why: ['In ω₂, S<sup>ω₂</sup><sub>ω</sub> and S<sup>ω₂</sup><sub>ω₁</sub> are both stationary and disjoint.', '在 ω₂ 中，S<sup>ω₂</sup><sub>ω</sub> 与 S<sup>ω₂</sup><sub>ω₁</sub> 都平稳，却不相交。'] },
  { s: ['The blue set X below accumulates at λ &lt; κ, but λ ∉ X (hollow). X can be closed in κ.', '下图蓝色集合 X 在 λ &lt; κ 处聚集，但 λ ∉ X（空心）。X 可以在 κ 中是闭的。'], pic: picLimit(false), a: 1, why: ['sup(X ∩ λ) = λ, so closedness demands λ ∈ X.', 'sup(X ∩ λ) = λ，闭性要求 λ ∈ X。'] },
  { s: ['In ℵ<sub>ω</sub>, the set {ℵ<sub>2n</sub> : n &lt; ω} is club.', '在 ℵ<sub>ω</sub> 中，集合 {ℵ<sub>2n</sub> : n &lt; ω} 是 club。'], a: 0, why: ['Unbounded, and closed vacuously: below ℵ<sub>ω</sub> it has no limit points. (Together with {ℵ<sub>2n+1</sub>} this gives two disjoint clubs: cf ω trivializes the theory.)', '它无界，并且闭性空洞成立：在 ℵ<sub>ω</sub> 以下它没有极限点。（与 {ℵ<sub>2n+1</sub>} 一起给出两个不相交的 club：共尾性 ω 使理论变得平凡。）'] },
  { s: ['f(α+1) = α is regressive and injective on the successor ordinals below κ, which contradicts Fodor’s lemma.', '在 κ 以下的后继序数上，f(α+1) = α 是退缩的单射，这与 Fodor 引理矛盾。'], a: 1, why: ['No contradiction: the successor ordinals are not stationary, so Fodor’s lemma does not apply.', '没有矛盾：后继序数不构成平稳集，Fodor 引理不适用。'] },
], 'L23E2', TF);

/* ---- E3 proof order ---- */
const E3_STEPS = [
  { id: 1, s: ['ZFC ⊢ “if κ is inaccessible, then |V<sub>α</sub>| &lt; κ for all α &lt; κ”.', 'ZFC ⊢ “若 κ 不可达，则对所有 α &lt; κ 有 |V<sub>α</sub>| &lt; κ”。'] },
  { id: 2, s: ['ZFC ⊢ “if κ is inaccessible, then V<sub>κ</sub> ⊨ ZFC” (Replacement via regularity).', 'ZFC ⊢ “若 κ 不可达，则 V<sub>κ</sub> ⊨ ZFC”（替换公理用正则性）。'] },
  { id: 3, s: ['Hence ZFC + ∃inaccessible ⊢ “ZFC has a set model” ⊢ Con(ZFC).', '因此 ZFC + 存在不可达 ⊢ “ZFC 有集合模型” ⊢ Con(ZFC)。'] },
  { id: 4, s: ['Suppose ZFC ⊢ ∃inaccessible. Then ZFC ⊢ Con(ZFC).', '假设 ZFC ⊢ 存在不可达，则 ZFC ⊢ Con(ZFC)。'] },
  { id: 5, s: ['By Gödel 2, a theory extending ZFC that proves its own consistency is inconsistent; so ZFC is inconsistent.', '由哥德尔第二定理，证明了自身一致性的 ZFC 扩张理论是不一致的；所以 ZFC 不一致。'] },
  { id: 6, s: ['Contrapositive: if Con(ZFC), then ZFC ⊬ ∃inaccessible.', '逆否：若 Con(ZFC)，则 ZFC ⊬ 存在不可达。'] },
  { id: 'x1', s: ['Since V<sub>κ</sub> ⊨ ZFC, V<sub>κ</sub> ⊨ “there is an inaccessible”.', '由于 V<sub>κ</sub> ⊨ ZFC，所以 V<sub>κ</sub> ⊨ “存在不可达”。'], bad: ['Distractor: false for the least inaccessible κ, where V<sub>κ</sub> has none.', '干扰项：对最小的不可达 κ，V<sub>κ</sub> 中一个不可达都没有。'] },
  { id: 'x2', s: ['ZFC ⊢ Con(ZFC), so ZFC ⊢ ∃inaccessible.', 'ZFC ⊢ Con(ZFC)，所以 ZFC ⊢ 存在不可达。'], bad: ['Distractor: wrong direction, and ZFC ⊢ Con(ZFC) holds only if ZFC is inconsistent.', '干扰项：方向反了，而且 ZFC ⊢ Con(ZFC) 仅在 ZFC 不一致时成立。'] },
];
(function e3() {
  const order = [...E3_STEPS].sort(() => Math.random() - 0.5);
  let seq = [];
  let revealed = false;
  function render() {
    const pool = $('e3Pool'), sq = $('e3Seq');
    pool.innerHTML = ''; sq.innerHTML = '';
    order.filter(s => !seq.includes(s)).forEach(s => {
      const d = document.createElement('div'); d.className = 'chip'; d.innerHTML = bi(s.s[0], s.s[1]);
      d.addEventListener('click', () => { seq.push(s); render(); });
      pool.appendChild(d);
    });
    seq.forEach((s, i) => {
      const d = document.createElement('div'); d.className = 'chip'; d.innerHTML = `<span class="num">${i + 1}.</span>` + bi(s.s[0], s.s[1]);
      d.dataset.k = i;
      d.addEventListener('click', () => { seq.splice(i, 1); render(); });
      sq.appendChild(d);
    });
  }
  render();
  $('e3C').addEventListener('click', () => {
    const chips = [...$('e3Seq').children];
    const bad = seq.find(s => s.bad);
    let firstWrong = -1;
    seq.forEach((s, i) => { const ok = s.id === i + 1; chips[i].classList.add(ok ? 'ok' : 'no'); if (!ok && firstWrong < 0) firstWrong = i; });
    if (!bad && seq.length === 6 && firstWrong < 0) { if (!revealed) { Progress.mark('L23E3'); $('e3').classList.add('done'); } setMsg($('e3M'), bi('Correct! Steps 1–3 happen inside ZFC; steps 4–6 are the metamathematical Gödel 2 argument.', '正确！第 1–3 步在 ZFC 内部完成；第 4–6 步是元数学层面的哥德尔第二定理论证。'), 'ok'); }
    else if (bad) setMsg($('e3M'), bi(bad.bad[0], bad.bad[1]), 'bad');
    else setMsg($('e3M'), bi(`Not yet: ${seq.length < 6 ? 'the proof needs 6 steps' : 'step ' + (firstWrong + 1) + ' is out of place'}.`, `还不对：${seq.length < 6 ? '证明需要 6 步' : '第 ' + (firstWrong + 1) + ' 步位置不对'}。`), 'bad');
  });
  $('e3S').addEventListener('click', () => {
    revealed = true;
    seq = E3_STEPS.filter(s => !s.bad); render();
    setMsg($('e3M'), bi('The two leftover chips are distractors.', '剩下的两张卡片是干扰项。'), 'info');
  });
})();

/* ---- E4 strength vs size ---- */
choiceList($('e4L'), [
  { s: ['If κ is the least inaccessible and λ the least Mahlo, then κ &lt; λ.', '若 κ 是最小不可达、λ 是最小马洛，则 κ &lt; λ。'], a: 0, why: ['λ is Mahlo, so it has (stationarily many) inaccessibles below it.', 'λ 是马洛基数，其下有（平稳多个）不可达基数。'] },
  { s: ['The least huge cardinal is below the least supercompact (if both exist), so “huge” is the consistency-weaker axiom.', '最小巨大基数小于最小超紧基数（若两者都存在），所以“巨大”是一致性更弱的公理。'], a: 1, why: ['Huge is much stronger in consistency strength. Size and strength are different orders.', '巨大基数的一致性强度高得多。大小和强度是两种不同的序。'] },
  { s: ['“∃ weakly inaccessible” and “∃ strongly inaccessible” are equiconsistent over ZFC.', '在 ZFC 上，“存在弱不可达”与“存在强不可达”等相容。'], a: 0, why: ['A weakly inaccessible is strongly inaccessible in L (Step 5).', '弱不可达基数在 L 中是强不可达的（第 5 步）。'] },
  { s: ['ZFC + ∃Mahlo ⊢ Con(ZFC + ∃inaccessible).', 'ZFC + 存在马洛 ⊢ Con(ZFC + 存在不可达)。'], a: 0, why: ['If κ is Mahlo, V<sub>κ</sub> is a model of ZFC with (many) inaccessibles.', '若 κ 是马洛基数，V<sub>κ</sub> 是含（许多）不可达基数的 ZFC 模型。'] },
  { s: ['It is a theorem that any two large cardinal axioms are comparable in consistency strength.', '“任意两条大基数公理在一致性强度上可比较”是一条定理。'], a: 1, why: ['It is an observation; “large cardinal axiom” has no formal definition.', '这只是观察；“大基数公理”没有形式定义。'] },
  { s: ['ZFC + ∃inaccessible ⊢ Con(ZFC + ∃inaccessible).', 'ZFC + 存在不可达 ⊢ Con(ZFC + 存在不可达)。'], a: 1, why: ['Gödel 2: a consistent theory cannot prove its own consistency.', '哥德尔第二定理：一致的理论证明不了自身的一致性。'] },
  { s: ['Every weakly compact cardinal is Mahlo (provable in ZFC).', '每个弱紧基数都是马洛基数（ZFC 可证）。'], a: 0, why: ['Π¹₁ reflection (Step 10).', 'Π¹₁ 反射（第 10 步）。'] },
  { s: ['Every worldly cardinal is inaccessible.', '每个 worldly 基数都是不可达的。'], a: 1, why: ['The least worldly cardinal has cofinality ω.', '最小的 worldly 基数共尾性为 ω。'] },
], 'L23E4', TF);

/* ---- E5 R(3,3) game ---- */
(function e5() {
  let n = 5, shown = false;
  const box = $('e5M');
  const report = S => {
    const t = S.tris(), full = S.complete();
    if (S.n === 5) {
      if (full && !t.length) {
        if (!shown) { Progress.mark('L23E5'); $('e5').classList.add('done'); }
        setMsg(box, bi('Solved: K₅ with no monochromatic triangle, so R(3,3) &gt; 5. Now try K₆.', '成功：K₅ 没有同色三角形，所以 R(3,3) &gt; 5。现在试试 K₆。'), 'ok');
      } else if (t.length) setMsg(box, bi(`Monochromatic triangle at {${t[0].slice(0, 3).map(v => v + 1).join(',')}}. Recolor.`, `{${t[0].slice(0, 3).map(v => v + 1).join(',')}} 是同色三角形，请重新染色。`), 'bad');
      else setMsg(box, bi('Color every edge (click to cycle grey → red → blue).', '给每条边染色（点击切换 灰 → 红 → 蓝）。'));
    } else {
      if (full) setMsg(box, bi(`As promised: K₆ always contains a monochromatic triangle (here ${t.length}). Together with K₅: R(3,3) = 6.`, `果然：K₆ 总含同色三角形（这里有 ${t.length} 个）。结合 K₅：R(3,3) = 6。`), 'warn');
      else setMsg(box, bi(t.length ? 'Already a monochromatic triangle. Keep going, or clear and retry.' : 'Try to color all 15 edges without a monochromatic triangle.', t.length ? '已出现同色三角形。继续，或清空重来。' : '试着给 15 条边全部染色而不出现同色三角形。'), t.length ? 'warn' : 'info');
    }
  };
  const G = RamseyGraph($('e5G'), { n: 5, onChange: report });
  const setN = k => { n = k; $('e5n5').classList.toggle('sel', k === 5); $('e5n6').classList.toggle('sel', k === 6); G.setN(k); };
  $('e5n5').addEventListener('click', () => setN(5));
  $('e5n6').addEventListener('click', () => setN(6));
  $('e5Clr').addEventListener('click', () => G.clear());
  $('e5S').addEventListener('click', () => {
    shown = true;
    if (G.n !== 5) setN(5);
    const col = {};
    for (let i = 0; i < 5; i++) for (let j = i + 1; j < 5; j++) col[G.key(i, j)] = (j - i === 1 || j - i === 4) ? 1 : 2;
    G.col = col; G.draw();
    setMsg(box, bi('Answer: the pentagon (cycle 1-2-3-4-5) red, the pentagram (the diagonals) blue. Both color classes are 5-cycles, which contain no triangle.', '答案：五边形（环 1-2-3-4-5）染红，五角星（对角线）染蓝。两个颜色类都是 5-圈，不含三角形。'), 'info');
  });
  report(G);
})();

/* ---- E6 reflection predictions ---- */
const E6_PAIRS = [[0, 1], [1, 1], [1, 2], [0, 2], [2, 2], [2, 3]];
(function e6() {
  const O = [['reflects', '能反射'], ['fails to reflect', '反射失败'], ['not true at κ', '在 κ 处不成立']];
  const key = { reflects: 0, fails: 1, false: 2 };
  const whyOf = (k, p, o) => o === 'reflects' ? [`Below the ${k.en} there are cardinals that are ${p.en.replace('Ord is ', '')}.`, `${k.zh}基数之下存在满足“${p.zh.replace('Ord ', '')}”的基数。`]
    : o === 'fails' ? [`The ${k.en} is the least cardinal with this property, so nothing below satisfies φ.`, `${k.zh}基数是具有此性质的最小基数，其下没有满足 φ 的。`]
    : [`The ${k.en} does not have this property.`, `${k.zh}基数不具有此性质。`];
  choiceList($('e6L'), E6_PAIRS.map(([ki, pi]) => {
    const k = RK[ki], p = RP[pi], o = reflectOutcome(k, p);
    return { s: [`κ = ${k.en}; φ = “${p.en}” (${p.cx})`, `κ = ${k.zh}；φ = “${p.zh}”（${p.cx}）`], a: key[o], why: whyOf(k, p, o) };
  }), 'L23E6', O);
})();

// Export for node unit tests.
if (typeof module !== 'undefined') module.exports = { monoTriangles, reflectOutcome, RK, RP, verdicts, CANDS, E1_ROWS };
