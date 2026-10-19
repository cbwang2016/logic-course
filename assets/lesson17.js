// Lesson 17 interactions: arithmetical hierarchy & Turing degrees.
Lang.init();
Progress.paint();

const $ = id => document.getElementById(id);
const okBox = (box, html, kind = 'ok') => { box.className = 'msg ' + kind; box.innerHTML = html; };
const clearBox = box => { box.className = 'msg'; box.innerHTML = ''; };
const SUBD = '₀₁₂₃₄₅₆₇₈₉';
const sub = n => String(n).split('').map(d => SUBD[d]).join('');
const svgText = (parent, x, y, s, attrs = {}) => { const t = el('text', Object.assign({ x, y }, attrs), parent); t.textContent = s; return t; };
function tween(ms, fn) {
  return new Promise(res => {
    const t0 = performance.now();
    function f(t) { const k = Math.min(1, Math.max(0, (t - t0) / ms)); fn(k); if (k < 1) requestAnimationFrame(f); else res(); }
    requestAnimationFrame(f);
  });
}
function selectIn(selector, btn) { document.querySelectorAll(selector).forEach(b => b.classList.toggle('sel', b === btn)); }

/*PURE-START*/
// ---------- quantifier prefixes ----------
// Prefix items: 'E' = ∃ (unbounded), 'A' = ∀ (unbounded), 'e' = ∃y<t (bounded), 'a' = ∀y<t (bounded).
function collapsePrefix(p) {
  const blocks = [];
  p.forEach((q, i) => {
    if (q !== 'E' && q !== 'A') return;
    const last = blocks[blocks.length - 1];
    if (last && last.q === q) last.idx.push(i); else blocks.push({ q, idx: [i] });
  });
  return blocks;
}
function classifyPrefix(p) {
  const b = collapsePrefix(p);
  if (!b.length) return { t: 'D', n: 0 };
  return { t: b[0].q === 'E' ? 'S' : 'P', n: b.length };
}
// ---------- toy oracle programs (generators yield queries, receive answers) ----------
const ORACLE_PROGS = {
  comp: function* (x) { const b = yield x; return 1 - b; },
  pair: function* (x) { const a = yield x; const b = yield x + 1; return a & b; },
  adapt: function* (x) { const a = yield x; const b = yield (a ? 2 * x : 2 * x + 1); return b; },
  parity: function* (x) { let c = 0; for (let i = 0; i <= x; i++) c += yield i; return c % 2 === 0 ? 1 : 0; },
};
function runOracle(prog, x, B) {
  const g = ORACLE_PROGS[prog](x), qs = [];
  let r = g.next();
  while (!r.done) { qs.push(r.value); r = g.next(B[r.value]); }
  return { out: r.value, queries: qs };
}
// ---------- Kleene–Post toy engine ----------
const DIV = { div: true };
const KP_FUNS = [
  { en: 'Φ₀^X(n) = X(n)', f: (n, X) => X(n) },
  { en: 'Φ₁^X(n) = 1 − X(n)', f: (n, X) => 1 - X(n) },
  { en: 'Φ₂^X(n) = X(2n+1)', f: (n, X) => X(2 * n + 1) },
  { en: 'Φ₃^X(n) = X(n) XOR X(n+1)', f: (n, X) => X(n) ^ X(n + 1) },
  { en: 'Φ₄^X(n) = 0', f: () => 0 },
  { en: 'Φ₅^X(n) = X(n+2) if X(n) = 1, else ↑', f: (n, X) => (X(n) === 1 ? X(n + 2) : DIV) },
  { en: 'Φ₆^X(n) = ↑ (never halts)', f: () => DIV },
];
// Search for an extension of the finite oracle string `str` on which f(n, ·) converges.
// Branches on each oracle query beyond the current string (0 first, then 1).
function kpSearch(str, n, f) {
  function rec(assign) {
    const q = [];
    const X = i => {
      if (i < str.length) { q.push(i); return str[i]; }
      if (assign.has(i)) { q.push(i); return assign.get(i); }
      throw { need: i };
    };
    try {
      const v = f(n, X);
      return v === DIV ? null : { assign, val: v, queried: q };
    } catch (e) {
      if (e && e.need !== undefined) {
        for (const b of [0, 1]) { const m = new Map(assign); m.set(e.need, b); const r = rec(m); if (r) return r; }
        return null;
      }
      throw e;
    }
  }
  const r = rec(new Map());
  if (!r) return null;
  const maxI = Math.max(str.length - 1, ...r.assign.keys());
  const ext = str.slice();
  for (let i = str.length; i <= maxI; i++) ext.push(r.assign.has(i) ? r.assign.get(i) : 0);
  return { ext, val: r.val, queried: r.queried };
}
// One stage s: s = 2e handles R_{2e}: A ≠ Φ_e^B; s = 2e+1 handles R_{2e+1}: B ≠ Φ_e^A.
function kpStage(state, s) {
  const e = Math.floor(s / 2), f = KP_FUNS[e].f;
  const targetKey = s % 2 === 0 ? 'A' : 'B', oracleKey = s % 2 === 0 ? 'B' : 'A';
  const target = state[targetKey], oracle = state[oracleKey];
  const n = target.length;
  const r = kpSearch(oracle, n, f);
  let bit, info;
  if (r) {
    const oldLen = oracle.length;
    state[oracleKey] = r.ext;
    bit = r.val === 0 ? 1 : 0;
    info = { e, n, targetKey, oracleKey, conv: true, val: r.val, queried: r.queried, added: r.ext.length - oldLen };
  } else {
    bit = 0;
    info = { e, n, targetKey, oracleKey, conv: false };
  }
  state[targetKey] = target.concat([bit]);
  info.bit = bit;
  state.witness.push({ e, n, targetKey, oracleKey });
  return info;
}
// Evaluate f(n, ·) on a finite string; undefined if it needs bits beyond the string, DIV if diverges.
function kpEval(str, n, f) {
  try { return f(n, i => { if (i >= str.length) throw { need: i }; return str[i]; }); } catch (e) { if (e && e.need !== undefined) return undefined; throw e; }
}
/*PURE-END*/

/* ================= check-yourself boxes ================= */
const CYS = {
  cy1: { q: bi('Is the set of primes Δ₀-definable?', '素数集是 Δ₀ 可定义的吗？'),
    o: [[bi('Yes', '是'), 1], [bi('No: primality needs an unbounded search', '否：判定素数需要无界搜索'), 0]],
    a: bi('Yes: <span class="m">Prime(x) :⟺ 1 &lt; x ∧ ∀y&lt;x ∀z&lt;x (y·z = x → (y = 1 ∨ z = 1))</span>. All quantifiers are bounded by x.',
      '是：<span class="m">Prime(x) :⟺ 1 &lt; x ∧ ∀y&lt;x ∀z&lt;x (y·z = x → (y = 1 ∨ z = 1))</span>，所有量词都以 x 为界。') },
  cy2: { q: bi('What is the level of <span class="m">∀u ∃y ∃z&lt;y ∀w&lt;z θ</span> (θ Δ₀)?', '<span class="m">∀u ∃y ∃z&lt;y ∀w&lt;z θ</span>（θ 为 Δ₀）属于哪一层？'),
    o: [['Σ⁰₂', 0], ['Π⁰₂', 1], ['Π⁰₄', 0], ['Π⁰₁', 0]],
    a: bi('Π⁰₂. The bounded <span class="m">∃z&lt;y ∀w&lt;z</span> are absorbed into the matrix, leaving ∀u ∃y: two blocks, starting with ∀.',
      'Π⁰₂。有界的 <span class="m">∃z&lt;y ∀w&lt;z</span> 被吸收进母式，剩下 ∀u ∃y：两个块，以 ∀ 开头。') },
  cy3: { q: bi('A is r.e. and ℕ∖A is r.e. Must A be decidable?', 'A 递归可枚举，ℕ∖A 也递归可枚举。A 一定可判定吗？'),
    o: [[bi('Yes', '是'), 1], [bi('No', '否'), 0], [bi('Only if A is infinite', '仅当 A 无限时'), 0]],
    a: bi('Yes. Run both enumerations in parallel; every x shows up in exactly one of them after finitely many steps (the race above).',
      '是。把两个枚举并行运行，每个 x 都会在有限步后恰好出现在其中一个里（就是上面的赛跑）。') },
  cy4: { q: bi('Inf is Π⁰₂-complete. Could Inf also be Σ⁰₂?', 'Inf 是 Π⁰₂-完全的。Inf 有没有可能同时是 Σ⁰₂ 集？'),
    o: [[bi('Yes: Σ and Π overlap in Δ', '可能：Σ 与 Π 在 Δ 处重叠'), 0], [bi('No', '不可能'), 1]],
    a: bi('No. Every Π⁰₂ set is ≤_m Inf, so it would be Σ⁰₂ too. That gives Π⁰₂ ⊆ Σ⁰₂, and taking complements Σ⁰₂ ⊆ Π⁰₂, so Σ⁰₂ = Π⁰₂, which contradicts the hierarchy theorem (Step 5).',
      '不可能。每个 Π⁰₂ 集都 ≤_m Inf，于是也成了 Σ⁰₂ 集，得到 Π⁰₂ ⊆ Σ⁰₂；取补集又得 Σ⁰₂ ⊆ Π⁰₂，所以 Σ⁰₂ = Π⁰₂，与层级定理（第 5 步）矛盾。') },
  cy5: { q: bi('Is there a decidable U ⊆ ℕ² whose sections U⁽ᵉ⁾ are exactly all the decidable subsets of ℕ?', '是否存在可判定的 U ⊆ ℕ²，使其截面 U⁽ᵉ⁾ 恰好是 ℕ 的全体可判定子集？'),
    o: [[bi('Yes', '存在'), 0], [bi('No', '不存在'), 1]],
    a: bi('No. D = {x : (x,x) ∉ U} would be decidable but differ from every section at the diagonal. This is why the universal set U₁ for Σ⁰₁ is r.e. but not decidable.',
      '不存在。否则 D = {x : (x,x) ∉ U} 可判定，却在对角线上与每个截面都不同。这也说明为什么 Σ⁰₁ 的通用集 U₁ 递归可枚举却不可判定。') },
  cy6: { q: bi('A ≤_T B and B is decidable. Then A is …', 'A ≤_T B，且 B 可判定。那么 A …'),
    o: [[bi('decidable', '可判定'), 1], [bi('r.e., but maybe not decidable', '递归可枚举，但未必可判定'), 0], [bi('could be anything', '可以是任何集合'), 0]],
    a: bi('Decidable: replace every oracle query by a call to B’s decision procedure.', '可判定：把每次谕示询问都换成调用 B 的判定程序即可。') },
  cy7: { q: bi('A is Σ⁰₂-complete. Then ℕ∖A is …', 'A 是 Σ⁰₂-完全的，那么 ℕ∖A …'),
    o: [[bi('Π⁰₂-complete', 'Π⁰₂-完全'), 1], [bi('Σ⁰₂-complete as well', '也是 Σ⁰₂-完全'), 0], [bi('Δ⁰₂', 'Δ⁰₂ 集'), 0]],
    a: bi('Π⁰₂-complete: if B ∈ Π⁰₂ then B̄ ∈ Σ⁰₂, so B̄ ≤_m A via some f, and the same f gives B ≤_m Ā.',
      'Π⁰₂-完全：若 B ∈ Π⁰₂，则 B̄ ∈ Σ⁰₂，于是存在 f 使 B̄ ≤_m A，同一个 f 就给出 B ≤_m Ā。') },
  cy8: { q: bi('What is the least n with Fin ≤_T ∅⁽ⁿ⁾?', '使 Fin ≤_T ∅⁽ⁿ⁾ 成立的最小 n 是多少？'),
    o: [['n = 1', 0], ['n = 2', 1], ['n = 3', 0]],
    a: bi('n = 2. Fin ∈ Σ⁰₂ ⊆ Δ⁰₃, so Fin ≤_T ∅″ by Post (c). Fin is Σ⁰₂-complete, hence not Δ⁰₂, so Fin ≰_T ∅′.',
      'n = 2。Fin ∈ Σ⁰₂ ⊆ Δ⁰₃，由波斯特定理 (c) 得 Fin ≤_T ∅″。Fin 是 Σ⁰₂-完全的，因而不是 Δ⁰₂ 集，所以 Fin ≰_T ∅′。') },
  cy9: { q: bi('Why are the Kleene–Post sets A and B computable from ∅′?', '为什么克莱尼–波斯特构造的 A、B 由 ∅′ 可计算？'),
    o: [[bi('Each stage asks one Σ⁰₁ question (“does some extension make the computation converge?”), which ∅′ answers; everything else is a computable search.', '每个阶段只问一个 Σ⁰₁ 问题（“是否存在使计算收敛的扩张？”），∅′ 能回答；其余部分都是可计算的搜索。'), 1],
      [bi('Because A and B are r.e.', '因为 A、B 递归可枚举'), 0], [bi('Because every set is computable from ∅′', '因为每个集合都由 ∅′ 可计算'), 0]],
    a: bi('The first. (A and B need not be r.e., and the sets computable from ∅′ are only the countably many Δ⁰₂ sets.)', '第一个。（A、B 不一定递归可枚举；由 ∅′ 可计算的集合只有可数多个，即全体 Δ⁰₂ 集。）') },
  cy10: { q: bi('Is the set of (codes of) true Π⁰₁ sentences a Σ⁰₁ set?', '真 Π⁰₁ 句子（的编码）构成的集合是 Σ⁰₁ 集吗？'),
    o: [[bi('Yes', '是'), 0], [bi('No', '不是'), 1]],
    a: bi('No. It is Π⁰₁-complete: K̄ ≤_m it via e ↦ ⌜∀s ¬T(ē,ē,s)⌝. If it were Σ⁰₁, K̄ would be r.e.',
      '不是。它是 Π⁰₁-完全的：经 e ↦ ⌜∀s ¬T(ē,ē,s)⌝ 有 K̄ ≤_m 它。若它是 Σ⁰₁ 的，K̄ 就递归可枚举了。') },
};
Object.entries(CYS).forEach(([id, c]) => {
  const box = $(id);
  if (!box) return;
  box.innerHTML = `<div class="q">✎ ${bil('Check yourself', '自测')}: ${c.q}</div><div class="opts"></div>
    <button class="btn small ghost">${bil('Show answer', '显示答案')}</button><div class="msg"></div>`;
  const opts = box.querySelector('.opts'), msg = box.querySelector('.msg');
  const btns = c.o.map(([h, ok]) => {
    const b = document.createElement('button');
    b.className = 'btn small';
    b.innerHTML = h;
    b.addEventListener('click', () => {
      btns.forEach(x => x.classList.remove('right', 'wrongc'));
      b.classList.add(ok ? 'right' : 'wrongc');
      okBox(msg, (ok ? '✓ ' : '✗ ') + (ok ? c.a : bi('Not quite. Think again, or press “Show answer”.', '不对。再想想，或点“显示答案”。')), ok ? 'ok' : 'bad');
    });
    opts.appendChild(b);
    return { b, ok };
  }).map(x => (x.b.dataset.ok = x.ok, x.b));
  box.querySelector('.btn.ghost').addEventListener('click', () => {
    btns.forEach(x => x.classList.toggle('right', x.dataset.ok === '1'));
    okBox(msg, c.a, 'info');
  });
});

/* ================= proof steps ================= */
document.querySelectorAll('[data-next]').forEach(b => b.addEventListener('click', () => {
  const st = [...document.querySelectorAll(`#${b.dataset.next} .step`)];
  const nx = st.find(s => !s.classList.contains('on'));
  if (nx) nx.classList.add('on');
  if (st.every(s => s.classList.contains('on'))) b.disabled = true;
}));
document.querySelectorAll('[data-all]').forEach(b => b.addEventListener('click', () => {
  document.querySelectorAll(`#${b.dataset.all} .step`).forEach(s => s.classList.add('on'));
  const nb = document.querySelector(`[data-next="${b.dataset.all}"]`);
  if (nb) nb.disabled = true;
}));

/* ================= §1 bounded search ================= */
(function boundedSearch() {
  const N = 28;
  const HALT = [3, null, 11, null, 6, 19, null, 2, 24, null, 15, 8, null, 21, 5, null, 13, 1, null, 17, 9, null, 26, 4, null];
  let mode = 0, token = 0;
  const row = $('bsRow'), msg = $('bsMsg');
  function draw() {
    const x = +$('bsX').value;
    row.innerHTML = '';
    for (let y = 0; y < N; y++) {
      const d = document.createElement('div');
      d.textContent = y;
      d.dataset.y = y;
      row.appendChild(d);
      if (mode === 0 && y === x) { const w = document.createElement('div'); w.className = 'wall'; w.title = 'bound'; row.appendChild(w); }
    }
    const more = document.createElement('div');
    more.textContent = '…';
    more.style.background = 'transparent';
    row.appendChild(more);
    clearBox(msg);
  }
  async function run() {
    const my = ++token;
    draw();
    const x = +$('bsX').value;
    const cells = [...row.querySelectorAll('[data-y]')];
    const test = y => mode === 2 ? HALT[x] === y : y * y === x;
    const limit = mode === 0 ? x : N - 1;
    for (let y = 0; y <= limit; y++) {
      if (my !== token) return;
      cells[y].classList.add('cur');
      await sleep(mode === 0 ? 120 : 90);
      if (my !== token) return;
      cells[y].classList.remove('cur');
      if (test(y)) {
        cells[y].classList.add('hit');
        const why = mode === 2 ? bi(`machine ${x} halts on input ${x} at step s = ${y}`, `机器 ${x} 在输入 ${x} 上于第 s = ${y} 步停机`) : `${y}·${y} = ${x}`;
msg.className = 'msg ok';
        msg.innerHTML = '✓ ' + bi(`Witness found at y = ${y}. The formula is true at x = ${x}.`, `在 y = ${y} 处找到见证，公式在 x = ${x} 处为真。`) + '<br>' + why;
        return;
      }
      cells[y].classList.add('seen');
    }
    if (mode === 0) okBox(msg, bi(`✗ Hit the wall at y = ${x}: no witness, so the formula is <b>false</b> at x = ${x}. Finitely many checks, then a definite answer.`, `✗ 在 y = ${x} 处碰墙：没有见证，所以公式在 x = ${x} 处<b>为假</b>。有限次检查后给出确定答案。`), 'bad');
    else if (mode === 1) okBox(msg, bi(`No witness yet, and nothing tells the search to stop… In this case we can <i>prove</i> that a witness, if any, is ≤ x, so the unbounded ∃y is equivalent to the bounded one and the set is still decidable. Unbounded quantifiers are only dangerous when no computable bound exists.`, `仍未找到见证，搜索也没有理由停下……不过这里我们能<i>证明</i>：若有见证，必 ≤ x。所以无界的 ∃y 与有界版本等价，这个集合仍可判定。只有当不存在可计算的上界时，无界量词才真正危险。`), 'warn');
    else okBox(msg, bi(`Still running… (toy halting times). For the halting predicate there is <b>no</b> computable bound on s: this is K, which is Σ⁰₁ but not decidable. Searching can confirm “yes” but never “no”.`, `还在运行……（玩具停机时间）。对停机谓词，s <b>不存在</b>可计算的上界：这就是 K，它是 Σ⁰₁ 集但不可判定。搜索只能确认“是”，永远确认不了“否”。`), 'warn');
  }
  document.querySelectorAll('[data-bs]').forEach(b => b.addEventListener('click', () => { mode = +b.dataset.bs; selectIn('[data-bs]', b); token++; draw(); }));
  $('bsX').addEventListener('input', () => { $('bsXv').textContent = $('bsX').value; token++; draw(); });
  $('bsGo').addEventListener('click', run);
  draw();
})();

/* ================= §2 prefix classifier ================= */
function prefixLabels(p) {
  // variable y_{i+1} for item i; bounded items are bounded by the previous variable (or x for the first).
  return p.map((q, i) => {
    const v = 'y' + sub(i + 1), bound = i === 0 ? 'x' : 'y' + sub(i);
    if (q === 'E') return '∃' + v;
    if (q === 'A') return '∀' + v;
    if (q === 'e') return `∃${v}&lt;${bound}`;
    return `∀${v}&lt;${bound}`;
  });
}
function chipHTML(q, label, extra = '') {
  const cls = q === 'E' ? 'E' : q === 'A' ? 'A' : 'b';
  const kind = q === 'E' || q === 'A' ? bil('unbounded', '无界') : bil('bounded', '有界');
  return `<span class="qc ${cls} ${extra}">${label}<small>${kind}</small></span>`;
}
const MATRIX = `<span class="qc mat">θ<small>Δ₀</small></span>`;
function levelBadge(c) {
  if (c.t === 'D') return `<span class="lvl D">Δ₀</span>`;
  return `<span class="lvl ${c.t}">${c.t === 'S' ? 'Σ' : 'Π'}⁰${sub(c.n)}</span>`;
}
(function classifier() {
  let p = ['A', 'E', 'e', 'E', 'a', 'A'];
  let token = 0;
  function render() {
    token++;
    const labels = prefixLabels(p);
    $('pfRow').innerHTML = p.map((q, i) => chipHTML(q, labels[i])).join('') + MATRIX + `<span class="m" style="margin-left:6px;color:var(--muted)">(x)</span>`;
    $('pfOut').innerHTML = '';
    clearBox($('pfMsg'));
  }
  async function normalize() {
    const my = ++token;
    const labels = prefixLabels(p);
    const out = $('pfOut');
    out.innerHTML = '';
    clearBox($('pfMsg'));
    const chips = [...$('pfRow').querySelectorAll('.qc')];
    const hasB = p.some(q => q === 'e' || q === 'a');
    // Step 1: absorb bounded quantifiers
    if (hasB) {
      p.forEach((q, i) => { if (q === 'e' || q === 'a') chips[i].classList.add('vanish'); });
      out.innerHTML = `<div class="fadein">${bi('<b>Rule (b):</b> bounded quantifiers are absorbed into the matrix (collection). The matrix stays Δ₀.', '<b>规则 (b)：</b>有界量词被吸收进母式（收集原理），母式仍是 Δ₀。')}</div>`;
      await sleep(1100);
      if (my !== token) return;
    }
    const ub = p.map((q, i) => ({ q, l: labels[i] })).filter(o => o.q === 'E' || o.q === 'A');
    const mat = hasB ? `<span class="qc mat">θ′<small>Δ₀</small></span>` : MATRIX;
    const row1 = `<div class="qrow fadein" style="margin-top:6px">${ub.map(o => chipHTML(o.q, o.l)).join('')}${mat}</div>`;
    out.innerHTML += row1;
    await sleep(900);
    if (my !== token) return;
    // Step 2: merge like neighbours
    const blocks = collapsePrefix(p);
    const merges = blocks.filter(b => b.idx.length > 1);
    let html = `<div class="fadein" style="margin-top:10px">${merges.length
      ? bi('<b>Rule (a):</b> adjacent like quantifiers merge into one, using a pairing code ⟨·,·⟩.', '<b>规则 (a)：</b>相邻的同类量词借助配对编码 ⟨·,·⟩ 合并为一个。')
      : bi('<b>Rule (a):</b> no adjacent like quantifiers to merge.', '<b>规则 (a)：</b>没有相邻的同类量词可合并。')}</div><div class="qrow fadein" style="margin-top:4px;align-items:flex-end">`;
    blocks.forEach((b, k) => {
      const vars = b.idx.map(i => 'y' + sub(i + 1));
      const lab = (b.q === 'E' ? '∃' : '∀') + (vars.length > 1 ? `⟨${vars.join(',')}⟩` : vars[0]);
      html += `<span class="blk"><span class="bl">${bil('block', '块')} ${k + 1}</span>${chipHTML(b.q, lab, vars.length > 1 ? 'merge' : '')}</span>`;
    });
    html += `${mat}</div>`;
    out.innerHTML += html;
    await sleep(900);
    if (my !== token) return;
    const c = classifyPrefix(p);
    let verdict;
    if (c.t === 'D') verdict = bi('No unbounded quantifiers: the formula is Δ₀, so the set it defines is decidable.', '没有无界量词：公式是 Δ₀ 的，所定义的集合可判定。');
    else verdict = bi(`${c.n} alternating block${c.n > 1 ? 's' : ''}, starting with ${c.t === 'S' ? '∃' : '∀'}: the formula is ${c.t === 'S' ? 'Σ' : 'Π'}⁰${sub(c.n)}. The set it defines is ${c.t === 'S' ? 'Σ' : 'Π'}⁰${sub(c.n)} (an upper bound; it may be simpler).`,
      `${c.n} 个交替块，以 ${c.t === 'S' ? '∃' : '∀'} 开头：公式是 ${c.t === 'S' ? 'Σ' : 'Π'}⁰${sub(c.n)} 的，所定义的集合属于 ${c.t === 'S' ? 'Σ' : 'Π'}⁰${sub(c.n)}（这只是上界，实际可能更简单）。`);
    okBox($('pfMsg'), `${levelBadge(c)} &nbsp; ${verdict}`, 'info');
  }
  document.querySelectorAll('[data-q]').forEach(b => b.addEventListener('click', () => { if (p.length < 9) p.push(b.dataset.q); render(); }));
  $('pfBack').addEventListener('click', () => { p.pop(); render(); });
  $('pfClear').addEventListener('click', () => { p = []; render(); });
  $('pfRand').addEventListener('click', () => {
    const n = 3 + Math.floor(Math.random() * 4);
    p = Array.from({ length: n }, () => 'EAEAea'[Math.floor(Math.random() * 6)]);
    render();
  });
  $('pfGo').addEventListener('click', normalize);
  render();
})();

/* ================= §3 race ================= */
(function race() {
  const KH = [3, null, 7, 12, null, 5, null, 9, 2, null];
  let mode = 'even', token = 0;
  function lanes(l1, l2, none2) {
    return `<div class="lane"><div>${l1}</div><div class="bar" id="rb1"><i></i></div><div class="st" id="rs1"></div></div>
      <div class="lane"><div>${l2}</div><div class="bar ${none2 ? 'none' : ''}" id="rb2"><i></i></div><div class="st" id="rs2">${none2 ? '∄' : ''}</div></div>`;
  }
  function setup() {
    token++;
    clearBox($('raceMsg'));
    if (mode === 'even') $('raceStage').innerHTML = lanes(bi('Lane 1: x ∈ A ⟸ ∃y (2y = x)', '第 1 道：x ∈ A ⟸ ∃y (2y = x)'), bi('Lane 2: x ∉ A ⟸ ∃y (2y+1 = x)', '第 2 道：x ∉ A ⟸ ∃y (2y+1 = x)'));
    else $('raceStage').innerHTML = lanes(bi('Lane 1: x ∈ K ⟸ ∃s T(x,x,s)', '第 1 道：x ∈ K ⟸ ∃s T(x,x,s)'), bi('Lane 2: x ∉ K ⟸ ??? (K̄ is not Σ⁰₁)', '第 2 道：x ∉ K ⟸ ???（K̄ 不是 Σ⁰₁）'), true);
  }
  async function go() {
    setup();
    const my = token, x = +$('raceX').value;
    const b1 = $('rb1'), b2 = $('rb2');
    if (mode === 'even') {
      const MAX = 6;
      for (let y = 0; y < MAX; y++) {
        for (const lane of [1, 2]) {
          if (my !== token) return;
          const bar = lane === 1 ? b1 : b2, val = lane === 1 ? 2 * y : 2 * y + 1;
          bar.querySelector('i').style.width = ((y + 1) / MAX * 100) + '%';
          $('rs' + lane).textContent = `y=${y}: ${val} ${val === x ? '=' : '≠'} ${x}`;
          await sleep(260);
          if (val === x) {
            bar.classList.add('win');
            okBox($('raceMsg'), lane === 1 ? bi(`Lane 1 wins: ${x} = 2·${y}, so ${x} ∈ A. Decided after finitely many steps.`, `第 1 道胜出：${x} = 2·${y}，所以 ${x} ∈ A。有限步内判定完毕。`)
              : bi(`Lane 2 wins: ${x} = 2·${y}+1, so ${x} ∉ A. Decided after finitely many steps.`, `第 2 道胜出：${x} = 2·${y}+1，所以 ${x} ∉ A。有限步内判定完毕。`), 'ok');
            return;
          }
        }
      }
    } else {
      const MAX = 40, h = KH[x];
      for (let s = 0; s <= MAX; s++) {
        if (my !== token) return;
        b1.querySelector('i').style.width = (Math.min(s, MAX) / MAX * 100) + '%';
        $('rs1').textContent = `s = ${s}`;
        if (h === s) {
          b1.classList.add('win');
          okBox($('raceMsg'), bi(`Machine ${x} halts on input ${x} at step ${s}: ${x} ∈ K. Lane 1 confirms membership.`, `机器 ${x} 在输入 ${x} 上第 ${s} 步停机：${x} ∈ K。第 1 道确认了属于关系。`), 'ok');
          return;
        }
        await sleep(70);
      }
      okBox($('raceMsg'), bi(`After ${MAX} steps machine ${x} is still running (toy data). Maybe it halts at step 10⁹, maybe never. With no lane 2 we can never safely answer “x ∉ K”. That is exactly why K is r.e. but not decidable.`,
        `${MAX} 步后机器 ${x} 仍在运行（玩具数据）。也许第 10⁹ 步停机，也许永不停机。没有第 2 道，我们永远无法放心地回答“x ∉ K”。这正是 K 递归可枚举却不可判定的原因。`), 'warn');
    }
  }
  document.querySelectorAll('[data-race]').forEach(b => b.addEventListener('click', () => { mode = b.dataset.race; selectIn('[data-race]', b); setup(); }));
  $('raceX').addEventListener('input', () => { $('raceXv').textContent = $('raceX').value; setup(); });
  $('raceGo').addEventListener('click', go);
  setup();
})();

/* ================= §4 ladder ================= */
const fq = s => s.replace(/</g, '&lt;').replace(/∃[a-z](?:&lt;[a-z]+)?/g, m => `<span class="qE">${m}</span>`).replace(/∀[a-z](?:&lt;[a-z]+)?/g, m => `<span class="qA">${m}</span>`);
const LADDER_SETS = {
  Primes: { at: 'D1', f: 'Prime(x) ⟺ 1<x ∧ ∀y<x ∀z<x (y·z = x → y = 1 ∨ z = 1)',
    en: 'Decidable; even Δ₀-definable (only bounded quantifiers).', zh: '可判定；甚至是 Δ₀ 可定义的（只用到有界量词）。' },
  K: { at: 'S1', f: 'e ∈ K ⟺ ∃s T(e,e,s)',
    en: '<b>Σ⁰₁-complete.</b> Every r.e. set Wᵢ is ≤_m K (L11). Hence K ∉ Π⁰₁.', zh: '<b>Σ⁰₁-完全.</b> 每个递归可枚举集 Wᵢ 都 ≤_m K（L11）。所以 K ∉ Π⁰₁。' },
  'K̄': { at: 'P1', f: 'e ∈ K̄ ⟺ ∀s ¬T(e,e,s)',
    en: '<b>Π⁰₁-complete</b> (complement of a Σ⁰₁-complete set).', zh: '<b>Π⁰₁-完全</b>（Σ⁰₁-完全集的补集）。' },
  Emp: { at: 'P1', f: 'e ∈ Emp ⟺ ∀x ∀s (x ∉ Wₑ,ₛ)',
    en: '<b>Π⁰₁-complete.</b> {e : Wₑ = ∅}. The two ∀ merge into one block.', zh: '<b>Π⁰₁-完全.</b> {e : Wₑ = ∅}。两个 ∀ 合并成一个块。' },
  'K⊕K̄': { at: 'D2', f: 'K ⊕ K̄ = {2x : x ∈ K} ∪ {2x+1 : x ∉ K}',
    en: '<b>Δ⁰₂, but neither Σ⁰₁ nor Π⁰₁.</b> It is ≤_T K, hence Δ⁰₂ (Post, Step 8). K̄ ≤_m it via x ↦ 2x+1, so it is not Σ⁰₁; K ≤_m it via x ↦ 2x, so it is not Π⁰₁. This shows Σ⁰₁ ∪ Π⁰₁ ⊊ Δ⁰₂.',
    zh: '<b>Δ⁰₂ 集，但既非 Σ⁰₁ 也非 Π⁰₁.</b> 它 ≤_T K，所以是 Δ⁰₂（波斯特定理，第 8 步）。K̄ 经 x ↦ 2x+1 多一归约到它，所以它不是 Σ⁰₁；K 经 x ↦ 2x 多一归约到它，所以它不是 Π⁰₁。这说明 Σ⁰₁ ∪ Π⁰₁ ⊊ Δ⁰₂。' },
  Fin: { at: 'S2', f: 'e ∈ Fin ⟺ ∃n ∀x ∀s (x > n → x ∉ Wₑ,ₛ)',
    en: '<b>Σ⁰₂-complete.</b> {e : Wₑ finite}: “there is a point beyond which nothing is ever enumerated”.', zh: '<b>Σ⁰₂-完全.</b> {e : Wₑ 有限}：“存在某个点，此后再也不会枚举出任何元素”。' },
  Inf: { at: 'P2', f: 'e ∈ Inf ⟺ ∀n ∃x ∃s (x > n ∧ x ∈ Wₑ,ₛ)',
    en: '<b>Π⁰₂-complete.</b> {e : Wₑ infinite} = complement of Fin.', zh: '<b>Π⁰₂-完全.</b> {e : Wₑ 无限}，即 Fin 的补集。' },
  Tot: { at: 'P2', f: 'e ∈ Tot ⟺ ∀x ∃s T(e,x,s)',
    en: '<b>Π⁰₂-complete.</b> {e : φₑ total}: “for every input, a halting computation exists”.', zh: '<b>Π⁰₂-完全.</b> {e : φₑ 是全函数}：“对每个输入，都存在一个停机计算”。' },
  Cof: { at: 'S3', f: 'e ∈ Cof ⟺ ∃n ∀x ∃s (x > n → x ∈ Wₑ,ₛ)',
    en: '<b>Σ⁰₃-complete.</b> {e : Wₑ cofinite}: “from some point on, every number is eventually enumerated”.', zh: '<b>Σ⁰₃-完全.</b> {e : Wₑ 余有限}：“从某处起，每个数迟早都会被枚举出来”。' },
  Rec: { at: 'S3', f: 'e ∈ Rec ⟺ ∃j ∀x [∃s (x ∈ Wₑ,ₛ ∨ x ∈ Wⱼ,ₛ) ∧ ∀s ¬(x ∈ Wₑ,ₛ ∧ x ∈ Wⱼ,ₛ)]',
    en: '<b>Σ⁰₃-complete.</b> {e : Wₑ decidable} ⟺ some Wⱼ is exactly the complement of Wₑ (Step 3). The bracket is Σ⁰₁ ∧ Π⁰₁, so Π⁰₂ after ∀x, and Σ⁰₃ after ∃j. That this cannot be improved is a theorem (Soare, Ch. IV).',
    zh: '<b>Σ⁰₃-完全.</b> {e : Wₑ 可判定} ⟺ 存在某个 Wⱼ 恰好是 Wₑ 的补集（第 3 步）。方括号内是 Σ⁰₁ ∧ Π⁰₁，加上 ∀x 后为 Π⁰₂，再加 ∃j 后为 Σ⁰₃。不能再改进，这是一个定理（Soare 第 IV 章）。' },
  Cpl: { at: 'S4', f: 'e ∈ Cpl ⟺ ∃i [Φᵢ^{Wₑ} = χ_K]   (bracket: Π⁰₃)',
    en: '<b>Σ⁰₄-complete.</b> {e : Wₑ ≡_T K}. Since Wₑ ≤_T K always holds, this says K ≤_T Wₑ: some i computes K from Wₑ. “Φᵢ^{Wₑ} is total and equals χ_K” is Π⁰₃.',
    zh: '<b>Σ⁰₄-完全.</b> {e : Wₑ ≡_T K}。由于 Wₑ ≤_T K 总成立，这等于说 K ≤_T Wₑ：存在 i 用 Wₑ 算出 K。“Φᵢ^{Wₑ} 是全函数且等于 χ_K”是 Π⁰₃ 的。' },
};
const LADDER_NODES = {
  D1: { en: 'Δ⁰₁ = decidable sets', zh: 'Δ⁰₁ = 可判定集', d: bi('Σ⁰₁ ∩ Π⁰₁ = the computable sets (Step 3). Equivalently ≤_T ∅.', 'Σ⁰₁ ∩ Π⁰₁ = 可计算集（第 3 步）。等价地说，≤_T ∅。') },
};
for (let n = 1; n <= 4; n++) {
  const pre = n === 1 ? '∃' : n === 2 ? '∃∀' : n === 3 ? '∃∀∃' : '∃∀∃∀';
  const preA = pre.replace(/∃|∀/g, c => (c === '∃' ? '∀' : '∃'));
  LADDER_NODES['S' + n] = { d: bi(`Sets definable by ${pre} θ (θ Δ₀). By Post's theorem: the sets r.e. in ∅⁽${n - 1}⁾. Complete set: ∅⁽${n}⁾. Closed under ∧, ∨, ∃, bounded ∀, and downward under ≤_m.`,
    `可由 ${pre} θ（θ 为 Δ₀）定义的集合。由波斯特定理：即关于 ∅⁽${n - 1}⁾ 递归可枚举的集合。完全集：∅⁽${n}⁾。对 ∧、∨、∃、有界 ∀ 封闭，并对 ≤_m 向下封闭。`), t: `Σ⁰${sub(n)}` };
  LADDER_NODES['P' + n] = { d: bi(`Complements of Σ⁰${sub(n)} sets; definable by ${preA} θ. Complete set: the complement of ∅⁽${n}⁾.`,
    `Σ⁰${sub(n)} 集的补集；可由 ${preA} θ 定义。完全集：∅⁽${n}⁾ 的补集。`), t: `Π⁰${sub(n)}` };
  if (n >= 2) LADDER_NODES['D' + n] = { d: bi(`Σ⁰${sub(n)} ∩ Π⁰${sub(n)} = the sets computable from ∅⁽${n - 1}⁾ (Post). Strictly contains Σ⁰${sub(n - 1)} ∪ Π⁰${sub(n - 1)}. Has no universal set that is itself Δ⁰${sub(n)} (diagonalize, as in Step 5).`,
    `Σ⁰${sub(n)} ∩ Π⁰${sub(n)} = 由 ∅⁽${n - 1}⁾ 可计算的集合（波斯特）。真包含 Σ⁰${sub(n - 1)} ∪ Π⁰${sub(n - 1)}。没有本身属于 Δ⁰${sub(n)} 的通用集（像第 5 步那样对角化即可）。`), t: `Δ⁰${sub(n)}` };
}
LADDER_NODES.D1.t = 'Δ⁰₁';
(function ladder() {
  const svg = $('ladder');
  const CX = 380, SX = 250, PX = 510;
  const Y = { D1: 592, S1: 524, P1: 524, D2: 456, S2: 388, P2: 388, D3: 320, S3: 252, P3: 252, D4: 184, S4: 116, P4: 116 };
  const X = k => (k[0] === 'S' ? SX : k[0] === 'P' ? PX : CX);
  const defs = el('defs', {}, svg);
  const mk = el('marker', { id: 'arr17', viewBox: '0 0 10 10', refX: 9, refY: 5, markerWidth: 7, markerHeight: 7, orient: 'auto-start-reverse' }, defs);
  el('path', { d: 'M0,0 L10,5 L0,10 z', fill: '#9aa0aa' }, mk);
  svgText(svg, CX, 24, 'Arithmetical sets = ⋃ₙ Σ⁰ₙ · 算术集', { 'text-anchor': 'middle', 'font-size': 15, 'font-weight': 700, fill: '#c2255c' });
  svgText(svg, CX, 44, 'TA, ∅^(ω) lie above every level · 高于每一层', { 'text-anchor': 'middle', 'font-size': 12, fill: '#888' });
  svgText(svg, CX, 78, '⋮', { 'text-anchor': 'middle', 'font-size': 24, fill: '#999' });
  const edge = (a, b) => {
    const x1 = X(a), y1 = Y[a], x2 = X(b), y2 = Y[b];
    const dx = x2 - x1, dy = y2 - y1, L = Math.hypot(dx, dy);
    const s = 24 / L, e = 24 / L;
    el('line', { x1: x1 + dx * s, y1: y1 + dy * s, x2: x2 - dx * e, y2: y2 - dy * e, stroke: '#9aa0aa', 'stroke-width': 2, 'marker-end': 'url(#arr17)' }, svg);
  };
  for (let n = 1; n <= 4; n++) {
    edge('D' + n, 'S' + n); edge('D' + n, 'P' + n);
    if (n < 4) { edge('S' + n, 'D' + (n + 1)); edge('P' + n, 'D' + (n + 1)); }
  }
  [['S4', 'top'], ['P4', 'top']].forEach(([k]) => el('line', { x1: X(k), y1: Y[k] - 20, x2: CX + (X(k) - CX) * 0.35, y2: 92, stroke: '#ccc', 'stroke-width': 2, 'stroke-dasharray': '3 5' }, svg));
  const nodeEls = {};
  Object.keys(Y).forEach(k => {
    const g = el('g', { class: 'node', transform: `translate(${X(k)},${Y[k]})` }, svg);
    const col = k[0] === 'S' ? ['#d3f9d8', '#2f9e44'] : k[0] === 'P' ? ['#e7ecff', '#3b5bdb'] : ['#fff3bf', '#f08c00'];
    el('rect', { x: -32, y: -17, width: 64, height: 34, rx: 10, fill: col[0], stroke: col[1], 'stroke-width': 2 }, g);
    svgText(g, 0, 6, LADDER_NODES[k].t, { 'text-anchor': 'middle', 'font-size': 17, 'font-weight': 800, fill: col[1] });
    g.addEventListener('click', () => showNode(k));
    nodeEls[k] = g;
  });
  // set pills
  const pillEls = {};
  const used = {};
  Object.entries(LADDER_SETS).forEach(([name, s]) => {
    const k = s.at;
    const w = [...name].length * 10 + 22;
    const j = used[k] || 0;
    used[k] = j + 1;
    let x, y = Y[k];
    if (k[0] === 'S') x = SX - 42 - w - j * 72;
    else if (k[0] === 'P') x = PX + 42 + j * 60;
    else if (k === 'D1') x = CX - 160;
    else { x = CX - w / 2; y = Y[k] + 38; }
    const g = el('g', { class: 'pill', transform: `translate(${x},${y})` }, svg);
    const fill = k[0] === 'S' ? '#2f9e44' : k[0] === 'P' ? '#3b5bdb' : '#f08c00';
    el('rect', { x: 0, y: -12, width: w, height: 24, rx: 12, fill }, g);
    svgText(g, w / 2, 5, name, { 'text-anchor': 'middle', 'font-size': 14, 'font-weight': 700, fill: '#fff' });
    g.addEventListener('click', () => showSet(name));
    pillEls[name] = g;
  });
  function clearOn() { Object.values(nodeEls).forEach(g => g.classList.remove('on')); Object.values(pillEls).forEach(g => g.classList.remove('on')); }
  function showNode(k) {
    clearOn(); nodeEls[k].classList.add('on');
    $('ladInfo').innerHTML = `<h4 class="fadein">${LADDER_NODES[k].t}</h4><div class="fadein">${LADDER_NODES[k].d}</div>`;
  }
  function showSet(name) {
    clearOn(); pillEls[name].classList.add('on'); nodeEls[LADDER_SETS[name].at].classList.add('on');
    const s = LADDER_SETS[name];
    $('ladInfo').innerHTML = `<h4 class="fadein">${name} &nbsp;→&nbsp; ${LADDER_NODES[s.at].t}</h4><div class="fm fadein">${fq(s.f)}</div><div class="fadein" style="margin-top:6px">${bi(s.en, s.zh)}</div>`;
  }
  showSet('Fin');
})();

/* ================= §5 diagonal ================= */
(function diagonal() {
  const svg = $('diag');
  const N = 8, CS = 36, X0 = 120, Y0 = 56;
  let U = [], D = [], done = false, token = 0;
  function draw() {
    token++;
    done = false;
    svg.innerHTML = '';
    clearBox($('dgMsg'));
    U = Array.from({ length: N }, () => Array.from({ length: N }, () => Math.random() < 0.5));
    svgText(svg, X0 + N * CS / 2, 18, 'x →', { 'text-anchor': 'middle', 'font-size': 13, fill: '#888' });
    for (let c = 0; c < N; c++) svgText(svg, X0 + c * CS + CS / 2, Y0 - 10, c, { 'text-anchor': 'middle', 'font-size': 14, fill: '#f08c00', 'font-weight': 700 });
    svgText(svg, X0 + N * CS + 14, Y0 - 10, '…', { 'font-size': 14, fill: '#999' });
    for (let r = 0; r < N; r++) {
      svgText(svg, X0 - 12, Y0 + r * CS + CS / 2 + 5, `U⁽${'⁰¹²³⁴⁵⁶⁷'[r]}⁾`, { 'text-anchor': 'end', 'font-size': 14, 'font-weight': 700 });
      for (let c = 0; c < N; c++) {
        el('rect', { x: X0 + c * CS + 2, y: Y0 + r * CS + 2, width: CS - 4, height: CS - 4, rx: 6, fill: U[r][c] ? '#d3f9d8' : '#f1efe7', id: `dg${r}_${c}` }, svg);
        el('circle', { cx: X0 + c * CS + CS / 2, cy: Y0 + r * CS + CS / 2, r: 7, fill: U[r][c] ? '#2f9e44' : 'none', stroke: U[r][c] ? '#2f9e44' : '#bbb', 'stroke-width': 2 }, svg);
      }
      svgText(svg, X0 + N * CS + 14, Y0 + r * CS + CS / 2 + 5, '…', { 'font-size': 14, fill: '#999' });
    }
    svgText(svg, 8, Y0 + N * CS + 6, '⋮', { 'font-size': 14, fill: '#999' });
    svgText(svg, X0 - 12, Y0 + N * CS + 64, 'D', { 'text-anchor': 'end', 'font-size': 16, 'font-weight': 800, fill: '#ae3ec9' });
    svgText(svg, 6, Y0 + N * CS + 26, 'rows = all Σ⁰ₙ sets · 每行一个 Σ⁰ₙ 集', { 'font-size': 12, fill: '#666' });
  }
  async function run(fast) {
    if (done) return true;
    const my = ++token;
    D = [];
    const yD = Y0 + N * CS + 44;
    for (let k = 0; k < N; k++) {
      if (!fast) await sleep(380);
      if (my !== token) return false;
      const cell = svg.querySelector(`#dg${k}_${k}`);
      cell.setAttribute('stroke', '#ae3ec9'); cell.setAttribute('stroke-width', 3);
      D[k] = !U[k][k];
      el('rect', { x: X0 + k * CS + 2, y: yD + 2, width: CS - 4, height: CS - 4, rx: 6, fill: '#f8e7fc', stroke: '#ae3ec9', 'stroke-width': 2, class: 'pop' }, svg);
      el('circle', { cx: X0 + k * CS + CS / 2, cy: yD + CS / 2, r: 7, fill: D[k] ? '#ae3ec9' : 'none', stroke: '#ae3ec9', 'stroke-width': 2, class: 'pop' }, svg);
      svgText(svg, X0 + N * CS + 34, Y0 + k * CS + CS / 2 + 5, `D ≠ U⁽${'⁰¹²³⁴⁵⁶⁷'[k]}⁾ at x=${k}`, { 'font-size': 12, fill: '#e03131', 'font-weight': 700 });
    }
    svgText(svg, X0, yD + CS + 22, 'x ∈ D ⟺ (x,x) ∉ Uₙ   ⇒  D is Π⁰ₙ, and D is no row', { 'font-size': 12.5, fill: '#ae3ec9', 'font-weight': 700 });
    svgText(svg, X0, yD + CS + 40, 'D 是 Π⁰ₙ 集，且不等于任何一行', { 'font-size': 12.5, fill: '#ae3ec9', 'font-weight': 700 });
    done = true;
    okBox($('dgMsg'), bi('D differs from row e at column e, for every e. Since every Σ⁰ₙ set is a row, D is not Σ⁰ₙ, yet D is Π⁰ₙ.', '对每个 e，D 与第 e 行在第 e 列不同。每个 Σ⁰ₙ 集都是某一行，所以 D 不是 Σ⁰ₙ 集，而 D 却是 Π⁰ₙ 集。'), 'ok');
    return true;
  }
  async function suppose() {
    if (!(await run(true))) return;
    const e0 = Math.floor(Math.random() * N);
    svg.querySelectorAll('.suprow').forEach(x => x.remove());
    el('rect', { x: X0 - 2, y: Y0 + e0 * CS, width: N * CS + 4, height: CS, rx: 8, fill: 'none', stroke: '#e03131', 'stroke-width': 3, class: 'suprow fadein' }, svg);
    const yD = Y0 + N * CS + 44;
    el('rect', { x: X0 + e0 * CS, y: yD, width: CS, height: CS, rx: 8, fill: 'none', stroke: '#e03131', 'stroke-width': 3, class: 'suprow pop' }, svg);
    el('line', { x1: X0 + e0 * CS + CS / 2, y1: Y0 + e0 * CS + CS, x2: X0 + e0 * CS + CS / 2, y2: yD, stroke: '#e03131', 'stroke-width': 2, 'stroke-dasharray': '4 4', class: 'suprow fadein' }, svg);
    const inU = U[e0][e0];
    okBox($('dgMsg'), bi(`Suppose D = U⁽${e0}⁾. Look at x = ${e0}: ${e0} ${inU ? '∈' : '∉'} U⁽${e0}⁾, but by definition ${e0} ${inU ? '∉' : '∈'} D. So D ≠ U⁽${e0}⁾. Contradiction! The same happens for every e₀.`,
      `假设 D = U⁽${e0}⁾。看 x = ${e0}：${e0} ${inU ? '∈' : '∉'} U⁽${e0}⁾，可按定义 ${e0} ${inU ? '∉' : '∈'} D。所以 D ≠ U⁽${e0}⁾，矛盾！对任何 e₀ 都是如此。`), 'bad');
  }
  $('dgGo').addEventListener('click', () => run(false));
  $('dgSup').addEventListener('click', suppose);
  $('dgNew').addEventListener('click', draw);
  draw();
})();

/* ================= §6 oracle machine ================= */
(function oracle() {
  const svg = $('orcSvg');
  const NB = 24;
  let B = [], prog = 'comp', token = 0, peek = false;
  const DESC = {
    comp: bi('Φ^B(x): ask “x ∈ B?”, output the opposite. So B̄ ≤_T B.', 'Φ^B(x)：问“x ∈ B？”，输出相反的值。所以 B̄ ≤_T B。'),
    pair: bi('Φ^B(x): ask “x ∈ B?” and “x+1 ∈ B?”, output 1 iff both are yes.', 'Φ^B(x)：问“x ∈ B？”与“x+1 ∈ B？”，两者都是“是”才输出 1。'),
    adapt: bi('Φ^B(x): ask “x ∈ B?”; if yes, ask “2x ∈ B?”, else ask “2x+1 ∈ B?”. Output the second answer. The second question depends on the first answer.', 'Φ^B(x)：问“x ∈ B？”；若是，再问“2x ∈ B？”，否则问“2x+1 ∈ B？”，输出第二个回答。第二个问题取决于第一个回答。'),
    parity: bi('Φ^B(x): ask about 0, 1, …, x and count the yeses; output 1 iff the count is even. Many questions, plus post-processing.', 'Φ^B(x)：依次问 0, 1, …, x，数出“是”的个数，个数为偶数时输出 1。问题很多，还要再加工。'),
  };
  function newB() { B = Array.from({ length: NB }, () => (Math.random() < 0.5 ? 1 : 0)); }
  function bits(lit = new Set()) {
    $('orcBits').className = 'bitstrip' + (peek ? ' peek' : '');
    $('orcBits').innerHTML = B.map((b, i) => `<span class="${lit.has(i) ? 'lit' : ''}">${b}<small>${i}</small></span>`).join('');
  }
  function frame() {
    svg.innerHTML = '';
    // input
    el('rect', { x: 14, y: 70, width: 120, height: 56, rx: 10, fill: '#fff3bf', stroke: '#f08c00', 'stroke-width': 2 }, svg);
    svgText(svg, 74, 92, 'input · 输入', { 'text-anchor': 'middle', 'font-size': 12, fill: '#8a5a00' });
    svgText(svg, 74, 116, 'x = ' + $('orcX').value, { 'text-anchor': 'middle', 'font-size': 18, 'font-weight': 700 });
    el('line', { x1: 134, y1: 98, x2: 220, y2: 98, stroke: '#999', 'stroke-width': 2, 'marker-end': 'url(#arr17)' }, svg);
    // machine
    el('rect', { x: 222, y: 30, width: 250, height: 190, rx: 16, fill: '#fff', stroke: '#1f2430', 'stroke-width': 2.5 }, svg);
    svgText(svg, 347, 54, 'oracle machine Φ · 谕示机', { 'text-anchor': 'middle', 'font-size': 13, 'font-weight': 700 });
    const gear = svgText(svg, 250, 84, '⚙', { 'font-size': 22, fill: '#3b5bdb', id: 'orcGear' });
    gear.style.transformBox = 'fill-box'; gear.style.transformOrigin = 'center';
    el('g', { id: 'orcLog' }, svg);
    // oracle
    el('rect', { x: 600, y: 40, width: 166, height: 170, rx: 16, fill: '#2b2f3a' }, svg);
    svgText(svg, 683, 112, 'B', { 'text-anchor': 'middle', 'font-size': 40, 'font-weight': 800, fill: '#fff' });
    svgText(svg, 683, 140, 'oracle · 谕示', { 'text-anchor': 'middle', 'font-size': 12, fill: '#bbb' });
    svgText(svg, 683, 160, '(black box · 黑盒)', { 'text-anchor': 'middle', 'font-size': 11, fill: '#999' });
    el('line', { x1: 472, y1: 100, x2: 598, y2: 100, stroke: '#ccc', 'stroke-width': 1.5, 'stroke-dasharray': '4 4' }, svg);
    el('line', { x1: 598, y1: 150, x2: 472, y2: 150, stroke: '#ccc', 'stroke-width': 1.5, 'stroke-dasharray': '4 4' }, svg);
    svgText(svg, 535, 92, 'query · 询问', { 'text-anchor': 'middle', 'font-size': 11, fill: '#888' });
    svgText(svg, 535, 168, 'answer · 回答', { 'text-anchor': 'middle', 'font-size': 11, fill: '#888' });
    // output
    el('rect', { x: 14, y: 150, width: 120, height: 56, rx: 10, fill: '#f1efe7', stroke: '#999', 'stroke-width': 2, id: 'orcOutBox' }, svg);
    svgText(svg, 74, 172, 'output · 输出', { 'text-anchor': 'middle', 'font-size': 12, fill: '#666' });
    svgText(svg, 74, 196, '?', { 'text-anchor': 'middle', 'font-size': 18, 'font-weight': 700, id: 'orcOut' });
    el('line', { x1: 222, y1: 178, x2: 136, y2: 178, stroke: '#999', 'stroke-width': 2, 'marker-end': 'url(#arr17)' }, svg);
  }
  async function run() {
    const my = ++token;
    frame();
    bits();
    clearBox($('orcMsg'));
    const x = +$('orcX').value;
    const g = ORACLE_PROGS[prog](x);
    const lit = new Set();
    const log = svg.querySelector('#orcLog');
    let r = g.next(), line = 0, ang = 0;
    while (!r.done) {
      const q = r.value;
      const msg = el('g', {}, svg);
      el('rect', { x: -26, y: -14, width: 52, height: 26, rx: 13, fill: '#ae3ec9' }, msg);
      svgText(msg, 0, 4, `${q} ∈ B?`, { 'text-anchor': 'middle', 'font-size': 12, 'font-weight': 700, fill: '#fff' });
      await tween(520, k => { msg.setAttribute('transform', `translate(${476 + k * 150},${100})`); ang += 6; svg.querySelector('#orcGear').style.transform = `rotate(${ang}deg)`; });
      if (my !== token) return;
      lit.add(q); bits(lit);
      const ans = B[q];
      msg.remove();
      const back = el('g', {}, svg);
      el('rect', { x: -24, y: -14, width: 48, height: 26, rx: 13, fill: ans ? '#2f9e44' : '#e03131' }, back);
      svgText(back, 0, 4, ans ? 'yes 是' : 'no 否', { 'text-anchor': 'middle', 'font-size': 12, 'font-weight': 700, fill: '#fff' });
      await tween(520, k => back.setAttribute('transform', `translate(${626 - k * 150},${150})`));
      if (my !== token) return;
      back.remove();
      if (line < 6) svgText(log, 286, 84 + line * 20, `ask ${q} → ${ans}`, { 'font-size': 13, fill: '#333' });
      else if (line === 6) svgText(log, 286, 84 + line * 20, '…', { 'font-size': 13, fill: '#333' });
      line++;
      r = g.next(ans);
    }
    const out = r.value;
    svg.querySelector('#orcOut').textContent = out;
    svg.querySelector('#orcOutBox').setAttribute('fill', out ? '#d3f9d8' : '#ffe3e3');
    okBox($('orcMsg'), bi(`Φ^B(${x}) = ${out}, after ${lit.size} distinct quer${lit.size === 1 ? 'y' : 'ies'}. The computation only used B on {${[...lit].sort((a, b) => a - b).join(', ')}}: change B anywhere else and the answer stays the same (use principle).`,
      `Φ^B(${x}) = ${out}，共询问了 ${lit.size} 个不同的位。计算只用到了 B 在 {${[...lit].sort((a, b) => a - b).join(', ')}} 上的值：在别处改动 B，结果不变（使用原理）。`), 'ok');
  }
  document.querySelectorAll('[data-orc]').forEach(b => b.addEventListener('click', () => {
    prog = b.dataset.orc; selectIn('[data-orc]', b); token++; frame(); bits(); okBox($('orcMsg'), DESC[prog], 'info');
  }));
  $('orcX').addEventListener('input', () => { $('orcXv').textContent = $('orcX').value; token++; frame(); bits(); });
  $('orcGo').addEventListener('click', run);
  $('orcNew').addEventListener('click', () => { token++; newB(); frame(); bits(); clearBox($('orcMsg')); });
  $('orcPeek').addEventListener('click', () => { peek = !peek; $('orcBits').classList.toggle('peek', peek); });
  newB(); frame(); bits(); okBox($('orcMsg'), DESC[prog], 'info');
})();

/* ================= §7 m vs T ================= */
(function mVsT() {
  const svg = $('mtSvg');
  const box = (x, y, w, h, fill, stroke, label, sz = 13) => {
    el('rect', { x, y, width: w, height: h, rx: 10, fill, stroke, 'stroke-width': 2 }, svg);
    svgText(svg, x + w / 2, y + h / 2 + 5, label, { 'text-anchor': 'middle', 'font-size': sz, 'font-weight': 700 });
  };
  const arrow = (x1, y1, x2, y2, cls = '') => {
    const l = el('line', { x1, y1, x2, y2, stroke: '#7a808c', 'stroke-width': 2, 'marker-end': 'url(#arr17)' }, svg);
    if (cls) { l.setAttribute('stroke-dasharray', '6 5'); l.innerHTML = '<animate attributeName="stroke-dashoffset" from="22" to="0" dur="1s" repeatCount="indefinite"/>'; }
  };
  svgText(svg, 10, 22, 'A ≤_m B : one query, answer passed on unchanged · 一次询问，回答原样输出', { 'font-size': 13, 'font-weight': 700, fill: '#f08c00' });
  box(10, 40, 60, 40, '#fff3bf', '#f08c00', 'x');
  arrow(70, 60, 120, 60, 1);
  box(122, 40, 130, 40, '#fff', '#1f2430', 'f (computable)', 12);
  arrow(252, 60, 300, 60, 1);
  box(302, 40, 90, 40, '#fff', '#999', 'f(x)');
  arrow(392, 60, 450, 60, 1);
  box(452, 40, 100, 40, '#2b2f3a', '#2b2f3a', '');
  svgText(svg, 502, 65, 'B ?', { 'text-anchor': 'middle', 'font-size': 15, 'font-weight': 800, fill: '#fff' });
  arrow(552, 60, 620, 60, 1);
  box(622, 40, 150, 40, '#d3f9d8', '#2f9e44', 'x ∈ A ⟺ yes', 12);
  svgText(svg, 10, 124, 'A ≤_T B : many adaptive queries + post-processing · 多次自适应询问 + 再加工', { 'font-size': 13, 'font-weight': 700, fill: '#ae3ec9' });
  box(10, 150, 60, 40, '#fff3bf', '#f08c00', 'x');
  arrow(70, 170, 120, 170, 1);
  box(122, 140, 270, 64, '#fff', '#1f2430', 'oracle machine Φ · 谕示机');
  box(452, 140, 100, 64, '#2b2f3a', '#2b2f3a', '');
  svgText(svg, 502, 177, 'B ?', { 'text-anchor': 'middle', 'font-size': 15, 'font-weight': 800, fill: '#fff' });
  [146, 162, 178, 194].forEach((y, i) => { if (i % 2 === 0) arrow(392, y, 450, y, 1); else arrow(452, y, 394, y, 1); });
  arrow(552, 172, 620, 172, 0);
  box(622, 152, 150, 40, '#f8e7fc', '#ae3ec9', 'any computation', 12);
})();
(function sorter() {
  const items = [
    { h: 'K ≤ K₀', a: 'M', en: 'K₀ = {⟨e,x⟩ : x ∈ Wₑ}. Use e ↦ ⟨e,e⟩.', zh: 'K₀ = {⟨e,x⟩ : x ∈ Wₑ}。取 e ↦ ⟨e,e⟩。' },
    { h: 'K̄ ≤ K', a: 'T', en: 'Ask once and flip: ≤_T. Not ≤_m, since K̄ would then be r.e.', zh: '问一次再取反：≤_T 成立。≤_m 不成立，否则 K̄ 递归可枚举。' },
    { h: 'K ≤ Tot', a: 'M', en: 'e ↦ an index of “ignore the input, run φₑ(e)” (s-m-n). This is total iff e ∈ K.', zh: 'e ↦ 程序“忽略输入，运行 φₑ(e)”的编号（s-m-n 定理）。它是全函数当且仅当 e ∈ K。' },
    { h: 'Tot ≤ K', a: 'N', en: 'Tot is Π⁰₂-complete, so it is not Δ⁰₂, i.e. not computable from K = ∅′ (Post).', zh: 'Tot 是 Π⁰₂-完全的，所以不是 Δ⁰₂ 集，即不能由 K = ∅′ 计算（波斯特）。' },
    { h: 'Fin ≤ ∅″', a: 'M', en: 'Fin ∈ Σ⁰₂ and ∅″ is Σ⁰₂-complete.', zh: 'Fin ∈ Σ⁰₂，而 ∅″ 是 Σ⁰₂-完全的。' },
    { h: 'Inf ≤ ∅″', a: 'T', en: 'Inf = complement of Fin, so ≤_T ∅″. Not ≤_m: Inf is Π⁰₂-complete, hence not Σ⁰₂.', zh: 'Inf 是 Fin 的补集，所以 ≤_T ∅″。≤_m 不成立：Inf 是 Π⁰₂-完全的，因而不是 Σ⁰₂ 集。' },
    { h: 'Emp ≤ K', a: 'T', en: 'Emp is Π⁰₁ ⊆ Δ⁰₂, so ≤_T K. Not ≤_m, since Emp is Π⁰₁-complete and not Σ⁰₁.', zh: 'Emp 属于 Π⁰₁ ⊆ Δ⁰₂，所以 ≤_T K。≤_m 不成立，因为 Emp 是 Π⁰₁-完全的，不是 Σ⁰₁ 集。' },
  ];
  const zones = ['tray', 'M', 'T', 'N'], ids = { tray: 'rsTray', M: 'rsM', T: 'rsT', N: 'rsN' };
  const pos = items.map(() => 'tray');
  function render() {
    Object.values(ids).forEach(id => ($(id).innerHTML = ''));
    items.forEach((it, i) => {
      const d = document.createElement('div');
      d.className = 'chip m';
      d.innerHTML = it.h;
      d.title = it.en;
      d.addEventListener('click', () => { pos[i] = zones[(zones.indexOf(pos[i]) + 1) % 4]; render(); clearBox($('rsMsg')); });
      it.el = d;
      $(ids[pos[i]]).appendChild(d);
    });
  }
  render();
  function explain() { return '<ul style="margin:6px 0 0">' + items.map(it => `<li><b class="m">${it.h}</b>: ${bil(it.en, it.zh)}</li>`).join('') + '</ul>'; }
  $('rsCheck').addEventListener('click', () => {
    let ok = 0;
    items.forEach((it, i) => { it.el.classList.remove('ok', 'no'); if (pos[i] === 'tray') return; if (pos[i] === it.a) { ok++; it.el.classList.add('ok'); } else it.el.classList.add('no'); });
    if (ok === items.length) okBox($('rsMsg'), '✓ ' + bi('All correct!', '全对！') + explain(), 'ok');
    else okBox($('rsMsg'), bi(`${ok} / ${items.length} correct. Red cards are misplaced. Ask: is the left set in the same Σ/Π class as (or below) a complete set on the right?`, `答对 ${ok} / ${items.length}。红色卡片放错了。问问自己：左边的集合是否与右边的完全集处于同一个 Σ/Π 类（或更低）？`), 'warn');
  });
  $('rsShow').addEventListener('click', () => { items.forEach((it, i) => (pos[i] = it.a)); render(); items.forEach(it => it.el.classList.add('ok')); okBox($('rsMsg'), explain(), 'info'); });
})();

/* ================= §8 Post ladder ================= */
(function postLadder() {
  const svg = $('postSvg');
  const R = [{ y: 470, l: '∅', s: 'empty set · 空集' }, { y: 395, l: '∅′', s: '≡ K' }, { y: 320, l: '∅″', s: '≡_m Fin' }, { y: 245, l: '∅‴', s: '≡_m Cof, Rec' }, { y: 170, l: '∅⁽⁴⁾', s: '≡_m Cpl' }, { y: 50, l: '∅⁽ω⁾', s: '≡_T TA' }];
  const INFO = [
    bi('<b>Rung 0: ∅.</b> Computable from ∅ = <b>Δ⁰₁</b> (decidable sets, e.g. the primes). R.e. in ∅ = <b>Σ⁰₁</b> (e.g. K).', '<b>第 0 级：∅.</b> 由 ∅ 可计算 = <b>Δ⁰₁</b>（可判定集，例如素数集）。关于 ∅ 递归可枚举 = <b>Σ⁰₁</b>（例如 K）。'),
    bi('<b>Rung 1: ∅′ = K</b>, Σ⁰₁-complete. Computable from ∅′ = <b>Δ⁰₂</b> (e.g. K̄, K ⊕ K̄, the Kleene–Post sets). R.e. in ∅′ = <b>Σ⁰₂</b> (e.g. Fin).', '<b>第 1 级：∅′ = K</b>，Σ⁰₁-完全。由 ∅′ 可计算 = <b>Δ⁰₂</b>（例如 K̄、K ⊕ K̄、克莱尼–波斯特集）。关于 ∅′ 递归可枚举 = <b>Σ⁰₂</b>（例如 Fin）。'),
    bi('<b>Rung 2: ∅″</b>, Σ⁰₂-complete (≡_m Fin). Computable from ∅″ = <b>Δ⁰₃</b> (e.g. Fin, Inf, Tot). R.e. in ∅″ = <b>Σ⁰₃</b> (e.g. Cof, Rec).', '<b>第 2 级：∅″</b>，Σ⁰₂-完全（≡_m Fin）。由 ∅″ 可计算 = <b>Δ⁰₃</b>（例如 Fin、Inf、Tot）。关于 ∅″ 递归可枚举 = <b>Σ⁰₃</b>（例如 Cof、Rec）。'),
    bi('<b>Rung 3: ∅‴</b>, Σ⁰₃-complete (≡_m Cof ≡_m Rec). Computable from it = <b>Δ⁰₄</b>. R.e. in it = <b>Σ⁰₄</b> (e.g. Cpl).', '<b>第 3 级：∅‴</b>，Σ⁰₃-完全（≡_m Cof ≡_m Rec）。由它可计算 = <b>Δ⁰₄</b>。关于它递归可枚举 = <b>Σ⁰₄</b>（例如 Cpl）。'),
    bi('<b>Rung 4: ∅⁽⁴⁾</b>, Σ⁰₄-complete (≡_m Cpl). And so on: ∅⁽ⁿ⁾ is Σ⁰ₙ-complete for every n ≥ 1, and each rung is strictly higher than the last (a &lt; a′).', '<b>第 4 级：∅⁽⁴⁾</b>，Σ⁰₄-完全（≡_m Cpl）。以此类推：对每个 n ≥ 1，∅⁽ⁿ⁾ 是 Σ⁰ₙ-完全的，而且每一级都严格高于前一级（a &lt; a′）。'),
    bi('<b>∅⁽ω⁾ = {⟨n,x⟩ : x ∈ ∅⁽ⁿ⁾}</b>, the ω-jump. It is not the jump of any rung below; it is a limit that sits above all of them. Every arithmetical set is ≤_m ∅⁽ω⁾, but ∅⁽ω⁾ is not arithmetical. Its degree is that of true arithmetic (Step 10). Lesson 18 keeps climbing.', '<b>∅⁽ω⁾ = {⟨n,x⟩ : x ∈ ∅⁽ⁿ⁾}</b>，即 ω-跳跃。它不是下面任何一级的跳跃，而是位于所有各级之上的“极限”。每个算术集都 ≤_m ∅⁽ω⁾，但 ∅⁽ω⁾ 本身不是算术集。它的度就是真算术的度（第 10 步）。第 18 课会继续往上爬。'),
  ];
  el('line', { x1: 60, y1: 495, x2: 60, y2: 140, stroke: '#8a6d3b', 'stroke-width': 6, 'stroke-linecap': 'round' }, svg);
  el('line', { x1: 150, y1: 495, x2: 150, y2: 140, stroke: '#8a6d3b', 'stroke-width': 6, 'stroke-linecap': 'round' }, svg);
  el('line', { x1: 60, y1: 140, x2: 60, y2: 70, stroke: '#8a6d3b', 'stroke-width': 4, 'stroke-dasharray': '3 8' }, svg);
  el('line', { x1: 150, y1: 140, x2: 150, y2: 70, stroke: '#8a6d3b', 'stroke-width': 4, 'stroke-dasharray': '3 8' }, svg);
  svgText(svg, 105, 118, '⋮', { 'text-anchor': 'middle', 'font-size': 26, fill: '#8a6d3b' });
  const rungs = R.map((r, i) => {
    const g = el('g', { class: 'node' }, svg);
    if (i < 5) el('line', { x1: 60, y1: r.y, x2: 150, y2: r.y, stroke: '#8a6d3b', 'stroke-width': 6, 'stroke-linecap': 'round' }, g);
    else el('rect', { x: 40, y: r.y - 16, width: 130, height: 32, rx: 10, fill: '#fde7f0', stroke: '#c2255c', 'stroke-width': 2 }, g);
    el('rect', { x: 175, y: r.y - 18, width: 235, height: 36, rx: 9, fill: '#fff', stroke: '#d8d3c4', 'stroke-width': 1.5 }, g);
    svgText(g, 188, r.y + 6, r.l, { 'font-size': 17, 'font-weight': 800, fill: i === 5 ? '#c2255c' : '#1f2430' });
    svgText(g, 245, r.y - 2, r.s, { 'font-size': 12, fill: '#666' });
    if (i < 5) svgText(g, 245, r.y + 12, `→ Δ⁰${sub(i + 1)} | Σ⁰${sub(i + 1)}`, { 'font-size': 11.5, fill: '#2f9e44', 'font-weight': 700 });
    g.addEventListener('click', () => show(i));
    return g;
  });
  const climber = el('g', {}, svg);
  el('circle', { r: 13, fill: '#3b5bdb', stroke: '#fff', 'stroke-width': 3 }, climber);
  svgText(climber, 0, 5, '★', { 'text-anchor': 'middle', 'font-size': 13, fill: '#fff' });
  let cur = 0, busy = false;
  climber.setAttribute('transform', `translate(105,${R[0].y})`);
  function show(i) {
    rungs.forEach((g, k) => g.classList.toggle('on', k === i));
    const y0 = R[cur].y, y1 = R[i].y;
    cur = i;
    tween(500, k => climber.setAttribute('transform', `translate(105,${y0 + (y1 - y0) * k})`));
    $('postInfo').innerHTML = `<div class="fadein">${INFO[i]}</div><div class="muted fadein" style="margin-top:8px;font-size:13px">${bi('Green labels: (computable from this oracle) | (r.e. in this oracle).', '绿色标签：（由此谕示可计算的）|（关于此谕示递归可枚举的）。')}</div>`;
  }
  $('plClimb').addEventListener('click', async () => {
    if (busy) return;
    busy = true;
    for (let i = 0; i < R.length; i++) { show(i); await sleep(1200); }
    busy = false;
  });
  show(1);
})();

/* ================= §9 degrees picture ================= */
(function degrees() {
  const svg = $('degSvg');
  const N = {
    z: { x: 210, y: 440, l: '0', d: bi('<b>0</b>: the degree of the computable sets. The least degree.', '<b>0</b>：可计算集的度，是最小的度。') },
    a: { x: 110, y: 340, l: 'a', re: 1, d: bi('<b>a = deg(A)</b>, A r.e. (Friedberg–Muchnik). 0 &lt; a &lt; 0′, and a | b (incomparable). Existence proved by the priority method.', '<b>a = deg(A)</b>，A 递归可枚举（弗里德伯格–穆奇尼克）。0 &lt; a &lt; 0′，且 a | b（不可比较）。其存在性由优先方法证明。') },
    b: { x: 310, y: 340, l: 'b', re: 1, d: bi('<b>b = deg(B)</b>, B r.e., incomparable with a.', '<b>b = deg(B)</b>，B 递归可枚举，与 a 不可比较。') },
    c: { x: 165, y: 270, l: 'c', d: bi('<b>c, d</b>: a Kleene–Post pair, built below 0′ by finite extensions with ∅′ answering questions. Incomparable; Δ⁰₂, but not r.e. in general.', '<b>c, d</b>：克莱尼–波斯特对，借助 ∅′ 回答问题、用有限扩张在 0′ 之下构造出来。互不可比较；是 Δ⁰₂ 的，但一般不是递归可枚举的。') },
    d: { x: 255, y: 270, l: 'd', d: bi('<b>d</b>: the other half of the Kleene–Post pair.', '<b>d</b>：克莱尼–波斯特对的另一半。') },
    j: { x: 210, y: 195, l: '0′', re: 1, d: bi('<b>0′ = deg(K)</b>: the largest r.e. degree. The degrees ≤ 0′ are exactly the degrees of Δ⁰₂ sets.', '<b>0′ = deg(K)</b>：最大的递归可枚举度。≤ 0′ 的度恰好是 Δ⁰₂ 集的度。') },
    jj: { x: 210, y: 130, l: '0″', d: bi('<b>0″</b> = (0′)′. Strictly above 0′.', '<b>0″</b> = (0′)′，严格高于 0′。') },
    w: { x: 210, y: 30, l: '0⁽ω⁾', d: bi('<b>0⁽ω⁾</b> = deg(∅⁽ω⁾) = deg(TA). Above every 0⁽ⁿ⁾.', '<b>0⁽ω⁾</b> = deg(∅⁽ω⁾) = deg(TA)，高于每个 0⁽ⁿ⁾。') },
  };
  el('ellipse', { cx: 210, cy: 318, rx: 170, ry: 132, fill: '#fbf7ff', stroke: '#d0bfe0', 'stroke-width': 1.5, 'stroke-dasharray': '5 5' }, svg);
  svgText(svg, 262, 418, 'degrees ≤ 0′ (Δ⁰₂)', { 'font-size': 11.5, fill: '#8a6aa8' });
  svgText(svg, 262, 433, '≤ 0′ 的度', { 'font-size': 11.5, fill: '#8a6aa8' });
  const E = [['z', 'a'], ['z', 'b'], ['a', 'j'], ['b', 'j'], ['z', 'c'], ['z', 'd'], ['c', 'j'], ['d', 'j'], ['j', 'jj']];
  E.forEach(([p, q]) => el('line', { x1: N[p].x, y1: N[p].y, x2: N[q].x, y2: N[q].y, stroke: '#9aa0aa', 'stroke-width': 2 }, svg));
  el('line', { x1: 210, y1: 112, x2: 210, y2: 50, stroke: '#9aa0aa', 'stroke-width': 2, 'stroke-dasharray': '3 6' }, svg);
  svgText(svg, 226, 85, '0‴, 0⁽⁴⁾, …', { 'font-size': 12, fill: '#888' });
  el('line', { x1: 132, y1: 340, x2: 288, y2: 340, stroke: '#e03131', 'stroke-width': 2, 'stroke-dasharray': '2 5' }, svg);
  svgText(svg, 210, 334, 'a | b', { 'text-anchor': 'middle', 'font-size': 12, fill: '#e03131', 'font-weight': 700 });
  svgText(svg, 210, 360, 'incomparable · 不可比较', { 'text-anchor': 'middle', 'font-size': 11, fill: '#e03131' });
  const gs = {};
  Object.entries(N).forEach(([k, n]) => {
    const g = el('g', { class: 'node', transform: `translate(${n.x},${n.y})` }, svg);
    el('circle', { r: 18, fill: n.re ? '#3b5bdb' : '#fff', stroke: k === 'w' ? '#c2255c' : '#3b5bdb', 'stroke-width': 2.5 }, g);
    svgText(g, 0, 5, n.l, { 'text-anchor': 'middle', 'font-size': n.l.length > 2 ? 11 : 15, 'font-weight': 800, fill: n.re ? '#fff' : '#1f2430' });
    g.addEventListener('click', () => { Object.values(gs).forEach(x => x.classList.remove('on')); g.classList.add('on'); $('degInfo').innerHTML = `<div class="fadein">${n.d}</div>${legend}`; });
    gs[k] = g;
  });
  const legend = `<div class="muted" style="margin-top:10px;font-size:13px">${bi('Filled = r.e. degree; hollow = not r.e. (in general). Lines go upward for ≤. Click a node.', '实心 = 递归可枚举度；空心 = （一般）非递归可枚举度。连线向上表示 ≤。点击节点查看说明。')}</div>`;
  $('degInfo').innerHTML = `<div>${N.a.d}</div>${legend}`;
  gs.a.classList.add('on');
})();

/* ================= §9 Kleene–Post ================= */
(function kleenePost() {
  $('kpFuns').innerHTML = KP_FUNS.map(f => `<div>${f.en}</div>`).join('');
  const STAGES = KP_FUNS.length * 2;
  let st, s, timer = null;
  function reset() {
    if (timer) { clearInterval(timer); timer = null; }
    st = { A: [], B: [], witness: [] }; s = 0;
    $('kpLog').innerHTML = '';
    render(null);
    okBox($('kpMsg'), bi(`Stage 0 of ${STAGES}. σ = τ = empty string.`, `第 0 / ${STAGES} 阶段。σ = τ = 空串。`), 'info');
  }
  function row(name, arr, info) {
    const cells = arr.map((b, i) => {
      const cls = ['idx'];
      if (b) cls.push('v1');
      if (info && info.oracleKey === name && info.conv && info.queried.includes(i)) cls.push('qd');
      if (info && info.targetKey === name && i === info.n) cls.push('dg', 'new');
      if (info && info.oracleKey === name && info.conv && i >= arr.length - info.added) cls.push('new');
      return `<span class="${cls.join(' ')}" data-i="${i}">${b}</span>`;
    }).join('');
    return `<div class="rowl"><b>${name}</b><div class="cells">${cells}<span style="background:none">…</span></div></div>`;
  }
  function render(info) { $('kpStage').innerHTML = row('A', st.A, info) + '<div style="height:8px"></div>' + row('B', st.B, info); }
  function step() {
    if (s >= STAGES) return false;
    const info = kpStage(st, s);
    const req = `R${sub(s)}`;
    const T = info.targetKey, O = info.oracleKey;
    const head = `<b>${bil('Stage', '阶段')} ${s + 1}</b> · ${req}: ${T} ≠ Φ${sub(info.e)}^${O}. n = ${info.n}. `;
    let body;
    if (info.conv) body = bi(`∅′ says: yes, an extension converges. Extend ${O} (queried positions ${info.queried.join(', ')}); Φ${sub(info.e)}^${O}(${info.n}) = ${info.val}, so put ${T}(${info.n}) = ${info.bit}.`,
      `∅′ 回答：存在使计算收敛的扩张。延长 ${O}（查询了第 ${info.queried.join('、')} 位）；Φ${sub(info.e)}^${O}(${info.n}) = ${info.val}，所以令 ${T}(${info.n}) = ${info.bit}。`);
    else body = bi(`∅′ says: no extension makes Φ${sub(info.e)}^${O}(${info.n}) converge. So it diverges for every ${O} we could build; put ${T}(${info.n}) = 0. Requirement met anyway.`,
      `∅′ 回答：没有任何扩张能使 Φ${sub(info.e)}^${O}(${info.n}) 收敛。所以无论 ${O} 怎么构造它都发散；令 ${T}(${info.n}) = 0。要求照样满足。`);
    const d = document.createElement('div');
    d.className = 'fadein';
    d.innerHTML = head + body;
    $('kpLog').prepend(d);
    render(info);
    s++;
    okBox($('kpMsg'), head + body, info.conv ? 'ok' : 'warn');
    if (s >= STAGES) {
      okBox($('kpMsg'), bi(`All ${STAGES} toy requirements are met. In the real construction the stages go on forever, through every e, and A, B are the limits. Press “Verify” to re-check each requirement on the final strings.`,
        `${STAGES} 个玩具要求全部满足。真正的构造中阶段无穷无尽，遍历每个 e，A、B 是极限。点“验证”可在最终的串上重新检查每个要求。`), 'ok');
      if (timer) { clearInterval(timer); timer = null; }
    }
    return true;
  }
  function verify() {
    if (!st.witness.length) { okBox($('kpMsg'), bi('Run some stages first.', '先运行几个阶段。'), 'warn'); return; }
    const lines = st.witness.map(w => {
      const v = kpEval(st[w.oracleKey], w.n, KP_FUNS[w.e].f);
      const tv = st[w.targetKey][w.n];
      const vs = v === DIV ? '↑' : v === undefined ? '↑ (on every extension)' : v;
      const ok = v === DIV || v === undefined || v !== tv;
      return `${ok ? '✓' : '✗'} ${w.targetKey}(${w.n}) = ${tv}, Φ${sub(w.e)}^${w.oracleKey}(${w.n}) = ${vs}`;
    });
    okBox($('kpMsg'), `<div class="m" style="font-size:13px">${lines.join('<br>')}</div>` + bi('Each line: the target set and the computation disagree at the witness n (or the computation diverges). By the use principle this persists in the limit.', '每一行：目标集合与计算在见证点 n 处不一致（或者计算发散）。由使用原理，这在极限中依然成立。'), 'ok');
  }
  $('kpStep').addEventListener('click', step);
  $('kpRun').addEventListener('click', () => { if (timer) return; timer = setInterval(() => { if (!step()) { clearInterval(timer); timer = null; } }, 650); });
  $('kpReset').addEventListener('click', reset);
  $('kpVerify').addEventListener('click', verify);
  reset();
})();

/* ================= §10 truth tower ================= */
(function truthTower() {
  const S = [
    { lv: ['S', 1], f: '∃x (x·x = 49)', en: 'true', zh: '真' },
    { lv: ['P', 1], f: bil('Goldbach: ∀n>1 ∃p<2n ∃q<2n (Prime(p) ∧ Prime(q) ∧ p+q = 2n)', '哥德巴赫：∀n>1 ∃p<2n ∃q<2n (Prime(p) ∧ Prime(q) ∧ p+q = 2n)'), en: 'open', zh: '未解决' },
    { lv: ['P', 1], f: 'Con(PA): ∀s ¬Prf_PA(s, ⌜0=1⌝)', en: 'true (not provable in PA)', zh: '真（在 PA 中不可证）' },
    { lv: ['P', 2], f: bil('Euclid: ∀x ∃y (y > x ∧ Prime(y))', '欧几里得：∀x ∃y (y > x ∧ Prime(y))'), en: 'true', zh: '真' },
    { lv: ['P', 2], f: bil('Twin primes: ∀x ∃y (y > x ∧ Prime(y) ∧ Prime(y+2))', '孪生素数：∀x ∃y (y > x ∧ Prime(y) ∧ Prime(y+2))'), en: 'open', zh: '未解决' },
    { lv: ['S', 3], f: bil('“Some r.e. set is cofinite”: ∃e ∃n ∀x ∃s (x > n → x ∈ Wₑ,ₛ)', '“某个递归可枚举集余有限”：∃e ∃n ∀x ∃s (x > n → x ∈ Wₑ,ₛ)'), en: 'true (e.g. an index of ℕ)', zh: '真（例如 ℕ 的某个编号）' },
    { lv: ['P', 4], f: bil('“Every r.e. set is decidable”: ∀e (e ∈ Rec)', '“每个递归可枚举集都可判定”：∀e (e ∈ Rec)'), en: 'false (K)', zh: '假（反例 K）' },
  ];
  const svg = $('trSvg');
  function draw(n) {
    svg.innerHTML = '';
    for (let k = 1; k <= 4; k++) {
      const y = 300 - k * 62;
      const on = k <= n;
      el('rect', { x: 30, y, width: 220, height: 54, rx: 10, fill: on ? '#d3f9d8' : '#f1efe7', stroke: on ? '#2f9e44' : '#d8d3c4', 'stroke-width': 2, class: on ? 'fadein' : '' }, svg);
      svgText(svg, 46, y + 24, `Σ⁰${sub(k)} / Π⁰${sub(k)}`, { 'font-size': 14, 'font-weight': 700, fill: on ? '#1b5e20' : '#888' });
      svgText(svg, 46, y + 43, on ? `decided via Tr_Σ${sub(n)} · 可判定真假` : 'out of reach · 够不着', { 'font-size': 11, fill: on ? '#1b5e20' : '#999' });
    }
    svgText(svg, 140, 30, '⋮  TA needs all levels', { 'text-anchor': 'middle', 'font-size': 13, fill: '#c2255c', 'font-weight': 700 });
    svgText(svg, 140, 48, 'TA 需要所有层', { 'text-anchor': 'middle', 'font-size': 12, fill: '#c2255c' });
    el('line', { x1: 262, y1: 290, x2: 262, y2: 20, stroke: '#c2255c', 'stroke-width': 3, 'marker-end': 'url(#arr17)' }, svg);
    el('rect', { x: 26, y: 300 - n * 62 - 4, width: 228, height: n * 62 + 2, rx: 12, fill: 'none', stroke: '#2f9e44', 'stroke-width': 3, 'stroke-dasharray': '6 4' }, svg);
    svgText(svg, 140, 320, `Tr_Σ${sub(n)} ∈ Σ⁰${sub(n)}`, { 'text-anchor': 'middle', 'font-size': 14, 'font-weight': 800, fill: '#2f9e44' });
  }
  function render() {
    const n = +$('trN').value;
    $('trNv').textContent = n;
    draw(n);
    const inside = S.filter(c => c.lv[1] <= n).length;
    $('trSum').innerHTML = bil(`Tr_Σ${sub(n)} reaches ${inside} of ${S.length} sentences`, `Tr_Σ${sub(n)} 能处理 ${S.length} 个句子中的 ${inside} 个`);
    $('trCards').innerHTML = S.map(c => {
      const ok = c.lv[1] <= n;
      return `<div class="tcard ${ok ? 'in' : 'out'}"><span class="lv">${c.lv[0] === 'S' ? 'Σ' : 'Π'}⁰${sub(c.lv[1])}</span><div class="s"><span class="m">${c.f}</span><br><span class="muted" style="font-size:12.5px">${bil('truth value', '真值')}: ${bil(c.en, c.zh)}</span></div><span>${ok ? '✓' : '—'}</span></div>`;
    }).join('');
  }
  $('trN').addEventListener('input', render);
  render();
})();

/* ================= E1 ================= */
(function e1() {
  const OPTS = [
    ['', bi('choose…', '请选择…')], ['D1', bi('Δ⁰₁ (decidable)', 'Δ⁰₁（可判定）')], ['S1', bi('Σ⁰₁-complete', 'Σ⁰₁-完全')], ['P1', bi('Π⁰₁-complete', 'Π⁰₁-完全')],
    ['D2', bi('Δ⁰₂, neither Σ⁰₁ nor Π⁰₁', 'Δ⁰₂，既非 Σ⁰₁ 也非 Π⁰₁')], ['S2', bi('Σ⁰₂-complete', 'Σ⁰₂-完全')], ['P2', bi('Π⁰₂-complete', 'Π⁰₂-完全')],
    ['S3', bi('Σ⁰₃-complete', 'Σ⁰₃-完全')], ['P3', bi('Π⁰₃-complete', 'Π⁰₃-完全')],
  ];
  const items = [
    { s: '{e : Wₑ ≠ ∅}', a: 'S1', why: bi('∃x ∃s (x ∈ Wₑ,ₛ); K reduces to it.', '∃x ∃s (x ∈ Wₑ,ₛ)；K 可归约到它。') },
    { s: bi('{e : φₑ is total}', '{e : φₑ 是全函数}'), a: 'P2', why: bi('Tot: ∀x ∃s.', 'Tot：∀x ∃s。') },
    { s: bi('{e : Wₑ is not cofinite}', '{e : Wₑ 不是余有限集}'), a: 'P3', why: bi('Complement of the Σ⁰₃-complete set Cof.', 'Σ⁰₃-完全集 Cof 的补集。') },
    { s: bi('{⟨e,x,s⟩ : machine e halts on x within s steps}', '{⟨e,x,s⟩ : 机器 e 在 s 步内于输入 x 上停机}'), a: 'D1', why: bi('Just run s steps: Kleene’s T is decidable.', '直接运行 s 步即可：克莱尼 T 谓词可判定。') },
    { s: bi('{e : Wₑ is finite}', '{e : Wₑ 有限}'), a: 'S2', why: bi('Fin: ∃n ∀x ∀s.', 'Fin：∃n ∀x ∀s。') },
    { s: 'K ⊕ K̄', a: 'D2', why: bi('≤_T K, while both K and K̄ are ≤_m it.', '≤_T K，而 K 与 K̄ 都 ≤_m 它。') },
    { s: '{e : Wₑ = ∅}', a: 'P1', why: bi('Emp: ∀x ∀s (x ∉ Wₑ,ₛ).', 'Emp：∀x ∀s (x ∉ Wₑ,ₛ)。') },
    { s: bi('{e : Wₑ is decidable}', '{e : Wₑ 可判定}'), a: 'S3', why: bi('Rec: ∃j ∀x [Σ⁰₁ ∧ Π⁰₁].', 'Rec：∃j ∀x [Σ⁰₁ ∧ Π⁰₁]。') },
  ];
  const optHTML = OPTS.map(([v, h]) => `<option value="${v}">${h.replace(/<[^>]+>/g, '|').split('|').filter(Boolean).join(' · ')}</option>`).join('');
  $('e1List').innerHTML = items.map((it, i) => `<div class="e1row"><div class="stmt m">${String.fromCharCode(97 + i)}) ${it.s}</div><select data-i="${i}">${optHTML}</select><div class="muted why" style="flex-basis:100%;font-size:13px;display:none"></div></div>`).join('');
  const sels = [...$('e1List').querySelectorAll('select')];
  let revealed = false;
  function check(reveal) {
    if (reveal) revealed = true;
    let ok = 0;
    sels.forEach((s, i) => {
      if (reveal) s.value = items[i].a;
      s.classList.remove('right', 'wrong');
      const why = s.parentElement.querySelector('.why');
      if (s.value === items[i].a) { ok++; s.classList.add('right'); why.style.display = 'block'; why.innerHTML = items[i].why; }
      else { if (s.value) s.classList.add('wrong'); why.style.display = 'none'; }
    });
    if (ok === items.length) {
      okBox($('e1Msg'), reveal ? bi('Answers shown.', '已显示答案。') : '✓ ' + bi('All correct!', '全对！'), reveal ? 'info' : 'ok');
      if (!revealed) Progress.mark('L17E1');
    } else okBox($('e1Msg'), bi(`${ok} / ${items.length} correct. Write the defining formula, count blocks, and remember that complements swap Σ and Π.`, `答对 ${ok} / ${items.length}。先写出定义公式、数量词块，并记住取补集会互换 Σ 与 Π。`), 'warn');
  }
  $('e1Check').addEventListener('click', () => check(false));
  $('e1Show').addEventListener('click', () => check(true));
})();

/* ================= E2 ================= */
(function e2() {
  let p = [], pick = null, streak = 0, revealed = false;
  function gen() {
    const n = 3 + Math.floor(Math.random() * 4);
    do p = Array.from({ length: n }, () => 'EEAAea'[Math.floor(Math.random() * 6)]); while (classifyPrefix(p).t === 'D' && Math.random() < 0.8);
    const labels = prefixLabels(p);
    $('e2Row').innerHTML = p.map((q, i) => chipHTML(q, labels[i])).join('') + MATRIX;
    pick = null; revealed = false;
    document.querySelectorAll('[data-e2]').forEach(b => b.classList.remove('sel'));
    clearBox($('e2Msg'));
  }
  function streakTxt() { $('e2Streak').textContent = `streak ${streak} / 3`; }
  document.querySelectorAll('[data-e2]').forEach(b => b.addEventListener('click', () => { pick = b.dataset.e2; selectIn('[data-e2]', b); }));
  $('e2Check').addEventListener('click', () => {
    if (revealed) { okBox($('e2Msg'), bi('You revealed this one. Press “New prefix”.', '这题已显示答案，请点“换一题”。'), 'info'); return; }
    if (!pick) { okBox($('e2Msg'), bi('Choose Σ⁰, Π⁰ or Δ₀ first.', '先选择 Σ⁰、Π⁰ 或 Δ₀。'), 'warn'); return; }
    const c = classifyPrefix(p), n = +$('e2n').value;
    const ok = c.t === pick && (c.t === 'D' || c.n === n);
    if (ok) {
      streak++; streakTxt();
      okBox($('e2Msg'), '✓ ' + levelBadge(c) + ' ' + (streak >= 3 ? bi(' Three in a row. Solved!', ' 连对三题，完成！') : bi(' Correct. Next one…', ' 正确，下一题……')), 'ok');
      if (streak >= 3) Progress.mark('L17E2');
      setTimeout(gen, 1300);
    } else {
      streak = 0; streakTxt();
      okBox($('e2Msg'), bi('✗ Not quite. Cross out the bounded (dashed) quantifiers, merge neighbours that are alike, then count the blocks.', '✗ 不对。先划掉虚线框的有界量词，再合并相邻的同类量词，然后数块数。'), 'bad');
    }
  });
  $('e2Show').addEventListener('click', () => {
    revealed = true;
    streak = 0; streakTxt();
    const c = classifyPrefix(p);
    const ub = p.map((q, i) => [q, prefixLabels(p)[i]]).filter(([q]) => q === 'E' || q === 'A').map(x => x[1]).join(' ');
    okBox($('e2Msg'), bi(`Unbounded part: <span class="m">${ub || '(none)'}</span> → `, `无界部分：<span class="m">${ub || '（无）'}</span> → `) + levelBadge(c), 'info');
  });
  $('e2New').addEventListener('click', gen);
  streakTxt();
  gen();
})();

/* ================= E3 ================= */
(function e3() {
  const steps = [
    bi('Let B ∈ Σ⁰ₙ₊₁: x ∈ B ⟺ ∃y R(x,y) with R ∈ Π⁰ₙ.', '设 B ∈ Σ⁰ₙ₊₁：x ∈ B ⟺ ∃y R(x,y)，其中 R ∈ Π⁰ₙ。'),
    bi('The complement of R is Σ⁰ₙ, so by the induction hypothesis it is ≤_m ∅⁽ⁿ⁾ via some computable f.', 'R 的补集是 Σ⁰ₙ 的，由归纳假设，存在可计算的 f 使它 ≤_m ∅⁽ⁿ⁾。'),
    bi('Hence R ≤_T ∅⁽ⁿ⁾: to decide R(x,y), ask whether f(x,y) ∈ ∅⁽ⁿ⁾ and flip the answer.', '于是 R ≤_T ∅⁽ⁿ⁾：要判定 R(x,y)，就问 f(x,y) ∈ ∅⁽ⁿ⁾ 是否成立，再把回答取反。'),
    bi('Search y = 0, 1, 2, … with this oracle procedure and halt once R(x,y) holds: B is r.e. in ∅⁽ⁿ⁾.', '用这个谕示程序依次搜索 y = 0, 1, 2, …，一旦 R(x,y) 成立就停机：B 关于 ∅⁽ⁿ⁾ 递归可枚举。'),
    bi('So B = Wᵢ^{∅⁽ⁿ⁾} for some i, and by the jump theorem (iii) (via s-m-n) there is a computable g with x ∈ B ⟺ g(x) ∈ (∅⁽ⁿ⁾)′.', '所以对某个 i 有 B = Wᵢ^{∅⁽ⁿ⁾}，由跳跃定理 (iii)（借助 s-m-n 定理），存在可计算的 g 使 x ∈ B ⟺ g(x) ∈ (∅⁽ⁿ⁾)′。'),
    bi('Thus B ≤_m ∅⁽ⁿ⁺¹⁾. Since B was an arbitrary Σ⁰ₙ₊₁ set, every Σ⁰ₙ₊₁ set is ≤_m ∅⁽ⁿ⁺¹⁾.', '因此 B ≤_m ∅⁽ⁿ⁺¹⁾。由于 B 是任意的 Σ⁰ₙ₊₁ 集，每个 Σ⁰ₙ₊₁ 集都 ≤_m ∅⁽ⁿ⁺¹⁾。'),
  ];
  let order = [], shuffled = [], revealed = false;
  function shuffle() {
    do shuffled = steps.map((_, i) => i).sort(() => Math.random() - 0.5); while (shuffled.every((v, i) => v === i));
    order = [];
    render();
    clearBox($('e3Msg'));
  }
  function render() {
    $('e3Pool').innerHTML = `<div class="muted" style="font-size:13px">${bil('Available steps', '可选步骤')}</div>`;
    $('e3Seq').innerHTML = `<div class="muted" style="font-size:13px">${bil('Your proof', '你的证明')}</div>`;
    shuffled.filter(i => !order.includes(i)).forEach(i => {
      const d = document.createElement('div');
      d.className = 'chip fadein';
      d.innerHTML = steps[i];
      d.addEventListener('click', () => { order.push(i); render(); });
      $('e3Pool').appendChild(d);
    });
    order.forEach((i, k) => {
      const d = document.createElement('div');
      d.className = 'chip fadein';
      d.dataset.n = k + 1;
      d.innerHTML = steps[i];
      d.addEventListener('click', () => { order.splice(k, 1); render(); });
      $('e3Seq').appendChild(d);
    });
  }
  function check(reveal) {
    if (reveal) { revealed = true; order = steps.map((_, i) => i); render(); }
    const chips = [...$('e3Seq').querySelectorAll('.chip')];
    let firstBad = -1;
    chips.forEach((c, k) => { const ok = order[k] === k; c.classList.toggle('ok', ok); c.classList.toggle('no', !ok); if (!ok && firstBad < 0) firstBad = k; });
    if (order.length === steps.length && firstBad < 0) {
      okBox($('e3Msg'), reveal ? bi('This is the correct order. The induction then continues: ∅⁽ⁿ⁺¹⁾ is also in Σ⁰ₙ₊₁ (Post (a) ⟸), so it is Σ⁰ₙ₊₁-complete.', '这就是正确顺序。归纳随后继续：∅⁽ⁿ⁺¹⁾ 本身也属于 Σ⁰ₙ₊₁（波斯特定理 (a) ⟸），所以它是 Σ⁰ₙ₊₁-完全的。')
        : '✓ ' + bi('Correct! Pattern: quantifier → oracle question → search → jump.', '正确！思路：量词 → 谕示问题 → 搜索 → 跳跃。'), reveal ? 'info' : 'ok');
      if (!revealed) Progress.mark('L17E3');
    } else if (order.length < steps.length) okBox($('e3Msg'), bi(`Place all ${steps.length} steps first.`, `请先放入全部 ${steps.length} 个步骤。`), 'warn');
    else okBox($('e3Msg'), bi(`Step ${firstBad + 1} is out of place. Each step must use only what the previous ones established.`, `第 ${firstBad + 1} 步位置不对。每一步只能用到前面已经得到的结论。`), 'bad');
  }
  $('e3Check').addEventListener('click', () => check(false));
  $('e3Show').addEventListener('click', () => check(true));
  $('e3Reset').addEventListener('click', shuffle);
  shuffle();
})();

/* ================= E4 / E5: true-false lists ================= */
function tfList(boxId, items, progId, labels) {
  const solved = items.map(() => false), shown = items.map(() => false);
  const box = $(boxId);
  items.forEach((it, i) => {
    const row = document.createElement('div');
    row.className = 'tf';
    row.innerHTML = `<div class="stmt" style="font-family:var(--sans);font-size:15px">${String.fromCharCode(97 + i)}) ${it.s}</div>
      <button class="btn small" data-v="1">${labels[0]}</button>
      <button class="btn small" data-v="0">${labels[1]}</button>
      <button class="btn small ghost" data-v="show">${bil('Show answer', '显示答案')}</button>
      <div style="flex-basis:100%"><div class="msg"></div></div>`;
    box.appendChild(row);
    row.querySelectorAll('button').forEach(b => b.addEventListener('click', () => {
      const msg = row.querySelector('.msg');
      if (b.dataset.v === 'show') { shown[i] = true; okBox(msg, `<b>${it.ans ? labels[0] : labels[1]}.</b> ${it.why}`, 'info'); return; }
      if ((b.dataset.v === '1') === it.ans) {
        okBox(msg, '✓ ' + it.why, 'ok');
        if (!shown[i]) solved[i] = true;
        if (solved.every(Boolean)) Progress.mark(progId);
      } else okBox(msg, '✗ ' + bi('Not quite. Think about it again, or use “Show answer”.', '不对。再想想，或点“显示答案”。'), 'bad');
    }));
  });
}
tfList('e4List', [
  { s: bi('For every set A, A &lt;_T A′.', '对每个集合 A，都有 A &lt;_T A′。'), ans: true, why: bi('Jump theorem: A ≤_T A′ and A′ ≰_T A (relativized halting problem).', '跳跃定理：A ≤_T A′ 且 A′ ≰_T A（相对化的停机问题）。') },
  { s: bi('If A ≤_T B then A′ ≤_T B′.', '若 A ≤_T B，则 A′ ≤_T B′。'), ans: true, why: bi('Even A′ ≤_m B′. So the jump is well defined on degrees.', '甚至 A′ ≤_m B′。所以跳跃在图灵度上有良定义。') },
  { s: bi('The Turing degrees are linearly ordered.', '图灵度是线性序。'), ans: false, why: bi('Kleene–Post: there are incomparable degrees, even below 0′.', '克莱尼–波斯特：存在不可比较的度，甚至在 0′ 之下就有。') },
  { s: bi('There is an r.e. degree strictly between 0 and 0′.', '存在严格介于 0 与 0′ 之间的递归可枚举度。'), ans: true, why: bi('Friedberg–Muchnik (solution of Post’s problem).', '弗里德伯格–穆奇尼克定理（波斯特问题的解答）。') },
  { s: bi('Every set A ≤_T ∅′ is r.e.', '每个满足 A ≤_T ∅′ 的集合 A 都递归可枚举。'), ans: false, why: bi('K̄ ≤_T ∅′ is not r.e. The sets ≤_T ∅′ are the Δ⁰₂ sets.', 'K̄ ≤_T ∅′，但它不递归可枚举。≤_T ∅′ 的集合恰好是 Δ⁰₂ 集。') },
  { s: bi('∅⁽ω⁾ is arithmetical.', '∅⁽ω⁾ 是算术集。'), ans: false, why: bi('If it were Σ⁰ₙ, then ∅⁽ⁿ⁺¹⁾ ≤_m ∅⁽ω⁾ would be Σ⁰ₙ, contradicting the hierarchy theorem.', '若它是 Σ⁰ₙ 的，则 ∅⁽ⁿ⁺¹⁾ ≤_m ∅⁽ω⁾ 也是 Σ⁰ₙ 的，与层级定理矛盾。') },
  { s: bi('A ≡_T B implies A ≡_m B.', 'A ≡_T B 蕴涵 A ≡_m B。'), ans: false, why: bi('K ≡_T K̄, but K̄ ≰_m K.', 'K ≡_T K̄，但 K̄ ≰_m K。') },
], 'L17E4', [bil('True', '对'), bil('False', '错')]);
tfList('e5List', [
  { s: 'Fin ≤_m Cof', ans: true, why: bi('Fin ∈ Σ⁰₂ ⊆ Σ⁰₃ and Cof is Σ⁰₃-complete.', 'Fin ∈ Σ⁰₂ ⊆ Σ⁰₃，而 Cof 是 Σ⁰₃-完全的。') },
  { s: 'Cof ≤_T ∅″', ans: false, why: bi('≤_T ∅″ means Δ⁰₃ (Post). Cof is Σ⁰₃-complete, so Cof ∈ Δ⁰₃ would give Σ⁰₃ ⊆ Π⁰₃.', '≤_T ∅″ 即 Δ⁰₃（波斯特）。Cof 是 Σ⁰₃-完全的，若 Cof ∈ Δ⁰₃，就会得到 Σ⁰₃ ⊆ Π⁰₃。') },
  { s: 'Tot ≤_T ∅″', ans: true, why: bi('Tot ∈ Π⁰₂ ⊆ Δ⁰₃ = sets computable from ∅″.', 'Tot ∈ Π⁰₂ ⊆ Δ⁰₃ = 由 ∅″ 可计算的集合。') },
  { s: 'K̄ ≤_m Emp', ans: true, why: bi('K̄ ∈ Π⁰₁ and Emp is Π⁰₁-complete.', 'K̄ ∈ Π⁰₁，而 Emp 是 Π⁰₁-完全的。') },
  { s: 'Inf ≤_m Fin', ans: false, why: bi('Then Inf would be Σ⁰₂; since Inf is Π⁰₂-complete, Π⁰₂ ⊆ Σ⁰₂ would follow.', '那样 Inf 就是 Σ⁰₂ 集；而 Inf 是 Π⁰₂-完全的，于是 Π⁰₂ ⊆ Σ⁰₂。') },
  { s: 'Rec ≤_m Cof', ans: true, why: bi('Both are Σ⁰₃-complete, so each is ≤_m the other.', '二者都是 Σ⁰₃-完全的，所以互相 ≤_m。') },
  { s: 'Fin ≤_T Inf', ans: true, why: bi('Fin = ℕ ∖ Inf: one query, flip the answer.', 'Fin = ℕ ∖ Inf：问一次，回答取反。') },
], 'L17E5', [bil('Holds', '成立'), bil('Fails', '不成立')]);
