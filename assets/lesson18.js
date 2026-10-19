// Lesson 18 interactions: analytical hierarchy, trees, WO, recursive ordinals, Kleene's O, HYP.

/* ================= pure logic (unit-testable in node) ================= */
const L18 = (() => {
  // ---- §1 quantifier prefixes: q = 'E' | 'A', t = 'n' (number) | 'f' (function) ----
  function mergeBlocks(qs) {
    const out = [];
    qs.forEach(x => { if (!out.length || out[out.length - 1].q !== x.q) out.push({ q: x.q, t: x.t, members: [x] }); else out[out.length - 1].members.push(x); });
    return out;
  }
  function classifyPrefix(qs) {
    const fq = qs.filter(x => x.t === 'f');
    if (!fq.length) {
      const blocks = mergeBlocks(qs);
      if (!blocks.length) return { name: 'Δ⁰₁', sup: 0, k: 0, cls: 'D' };
      const k = blocks.length, cls = blocks[0].q === 'E' ? 'Σ' : 'Π';
      return { name: `${cls}⁰${'₀₁₂₃₄₅₆₇₈₉'[k] || k}`, sup: 0, k, cls };
    }
    const blocks = mergeBlocks(fq);
    const k = blocks.length, cls = blocks[0].q === 'E' ? 'Σ' : 'Π';
    return { name: `${cls}¹${'₀₁₂₃₄₅₆₇₈₉'[k] || k}`, sup: 1, k, cls };
  }
  // stages of the collapse: [original, numbers pushed right, function blocks merged]
  function collapseStages(qs) {
    const fq = qs.filter(x => x.t === 'f'), nq = qs.filter(x => x.t === 'n');
    return { pushed: { fn: fq, num: nq }, merged: mergeBlocks(fq) };
  }

  // ---- §2 trees ----
  const PI = '31415926535897932384626433832795028841971693993751058209749445923078164062862089986280348253421170679';
  function firstDev(s, f) { for (let j = 0; j < s.length; j++) if (s[j] !== f(j)) return j; return -1; }
  // A recursive tree with exactly one infinite branch f; a node first deviating at position i
  // survives up to length i + 1 + d(i, s[i]). b = branching bound (null = ω-branching).
  function hiddenTree(f, d, b = null) {
    const T = {
      omega: b === null, b, f,
      has(s) {
        if (b !== null && s.some(v => v >= b || v < 0)) return false;
        const i = firstDev(s, f);
        return i < 0 || s.length <= i + 1 + d(i, s[i]);
      },
      onBranch(s) { return firstDev(s, f) < 0; },
      height(s) { const i = firstDev(s, f); return i < 0 ? Infinity : i + 1 + d(i, s[i]) - s.length; }, // = rank
      size(s) {
        const h = T.height(s);
        if (h === Infinity) return Infinity;
        if (b === null) return h === 0 ? 1 : Infinity;
        let t = 0, p = 1;
        for (let k = 0; k <= h; k++) { t += p; p *= b; }
        return t;
      },
      infChildren(s) { return b === null && T.height(s) > 0; },
    };
    return T;
  }
  const broom = {
    omega: true, b: null,
    has(s) { return s.length === 0 || (s.slice(1).every(v => v === 0) && s.length <= s[0] + 1 && s[0] >= 0); },
    onBranch() { return false; },
    height(s) { return s.length === 0 ? 'ω' : s[0] + 1 - s.length; },
    size(s) { return s.length === 0 ? Infinity : s[0] + 2 - s.length; },
    infChildren(s) { return s.length === 0; },
  };
  const thueMorse = i => { let c = 0; while (i) { c += i & 1; i >>= 1; } return c & 1; };
  const trees = {
    A: hiddenTree(thueMorse, i => i % 3, 2),
    B: broom,
    C: hiddenTree(i => +PI[i % PI.length], (i, k) => (i + k) % 4, null),
  };
  const e2f = i => (3 * i + 1) % 10;
  const e2Tree = hiddenTree(e2f, (i, k) => 1 + ((i + k) % 3), null);

  // ---- §3 orders for the descent game. Elements: {g: group, n}. ord: [m, k] = ω·m + k ----
  const ORD = (m, k) => [m, k];
  const ordLess = (a, b) => a[0] < b[0] || (a[0] === b[0] && a[1] < b[1]);
  function ordStr(o) {
    const [m, k] = o;
    if (m === 0) return String(k);
    const head = m === 1 ? 'ω' : `ω·${m}`;
    return k ? `${head}+${k}` : head;
  }
  const orders = {
    w3: { wo: true, type: 'ω+3', ord: e => e.g === 'a' ? ORD(0, e.n) : ORD(1, e.n),
      enumN: n => n < 3 ? { g: 'b', n } : { g: 'a', n: n - 3 } },
    w2: { wo: true, type: 'ω·2', ord: e => e.g === 'a' ? ORD(0, e.n) : ORD(1, e.n),
      enumN: n => n % 2 ? { g: 'b', n: (n - 1) / 2 } : { g: 'a', n: n / 2 } },
    ww: { wo: true, type: 'ω²', ord: e => ORD(e.g, e.n),
      enumN: n => { let s = 0; while ((s + 1) * (s + 2) / 2 <= n) s++; const b = n - s * (s + 1) / 2; return { g: s - b, n: b }; } },
    Z: { wo: false, type: 'ℤ', less: (x, y) => x.n < y.n,
      enumN: n => ({ g: 'z', n: n % 2 ? -(n + 1) / 2 : n / 2 }) },
    wws: { wo: false, type: 'ω+ω*',
      less: (x, y) => (x.g === 'a' && y.g === 'c') || (x.g === 'a' && y.g === 'a' && x.n < y.n) || (x.g === 'c' && y.g === 'c' && x.n > y.n),
      enumN: n => n % 2 ? { g: 'c', n: (n - 1) / 2 } : { g: 'a', n: n / 2 } },
  };
  Object.values(orders).forEach(o => { if (o.wo) o.less = (x, y) => ordLess(o.ord(x), o.ord(y)); });
  function leq(o, x, y) { return (x.g === y.g && x.n === y.n) || o.less(x, y); }
  function codeMatrix(o, N = 8) {
    const els = Array.from({ length: N }, (_, i) => o.enumN(i));
    return els.map(x => els.map(y => leq(o, x, y) ? 1 : 0));
  }

  // ---- §5 Kleene's O (a finite fragment) ----
  function makeO() {
    let id = 0, eCount = 0;
    const nodes = [];
    const root = { id: id++, kind: 'root', m: 0, n: 0, col: 0 };
    nodes.push(root);
    const cols = [{ base: null }];
    function succ(a) {
      let s = nodes.find(x => x.kind === 'S' && x.base === a);
      if (s) return { node: s, created: false };
      s = { id: id++, kind: 'S', base: a, m: a.m, n: a.n + 1, col: a.col };
      nodes.push(s);
      return { node: s, created: true };
    }
    function limit(a, variant) {
      let l = nodes.find(x => x.kind === 'L' && x.base === a && x.variant === variant);
      if (l) return { node: l, created: false };
      eCount++;
      cols.push({ base: a });
      l = { id: id++, kind: 'L', base: a, variant, e: eCount, m: a.m + 1, n: 0, col: cols.length - 1 };
      nodes.push(l);
      return { node: l, created: true };
    }
    // b ∈ S-chain strictly above a: b = S^k(a), k ≥ 1
    function aboveInChain(b, a) { let x = b; while (x.kind === 'S') { x = x.base; if (x === a) return true; } return false; }
    function below(b, c) { // b <_O c
      if (c.kind === 'root') return false;
      if (c.kind === 'S') return b === c.base || below(b, c.base);
      return b === c.base || below(b, c.base) || aboveInChain(b, c.base);
    }
    return { nodes, root, cols, succ, limit, below };
  }
  function oOrdStr(x) { return ordStr([x.m, x.n]); }

  // ---- §7 H-ladder ----
  function hName(m, n) {
    if (m === 0) return n === 0 ? '∅' : n <= 3 ? '∅' + ['', '′', '″', '‴'][n] : `∅^(${n})`;
    return `∅^(${ordStr([m, n])})`;
  }

  // ---- E2 formula checker ----
  function checkFormula(expr, f, N = 40) {
    const s = String(expr).replace(/mod/gi, '%').replace(/×|·/g, '*').trim();
    if (!s || !/^[0-9i+\-*()%\s]+$/.test(s)) return { ok: false, err: 'syntax' };
    let g;
    try { g = new Function('i', `return (${s});`); g(0); } catch { return { ok: false, err: 'syntax' }; }
    for (let i = 0; i < N; i++) {
      const v = g(i);
      if (!Number.isFinite(v) || ((v % 10) + 10) % 10 !== f(i) || v < 0 || v > 9) return { ok: false, err: 'value', at: i, got: v };
    }
    return { ok: true };
  }

  // ---- E4 ----
  const E4_ORDER = ['uniq', 'twodef', 'tree', 'bound', 'compute'];
  const checkOrder = seq => seq.length === E4_ORDER.length && seq.every((x, i) => x === E4_ORDER[i]);

  return { classifyPrefix, collapseStages, mergeBlocks, hiddenTree, broom, trees, PI, thueMorse, e2f, e2Tree,
    orders, ordLess, ordStr, leq, codeMatrix, makeO, oOrdStr, hName, checkFormula, E4_ORDER, checkOrder };
})();
if (typeof module !== 'undefined') module.exports = L18;

/* ================= DOM ================= */
if (typeof document !== 'undefined') {
Lang.init();
Progress.paint();

const $ = id => document.getElementById(id);
const okBox = (box, html, kind = 'ok') => { box.className = 'msg ' + kind; box.innerHTML = html; };
const SUBD = '₀₁₂₃₄₅₆₇₈₉';
const subs = n => String(n).split('').map(d => SUBD[d]).join('');
const CK = 'ω₁<sup>CK</sup>';
const CKs = 'ω₁ᶜᴷ';
const C = { ink: '#1f2430', mut: '#6b7280', acc: '#3b5bdb', accS: '#e7ecff', t: '#2f9e44', tS: '#d3f9d8', f: '#e03131', fS: '#ffe3e3', m: '#ae3ec9', mS: '#f8e7fc', g: '#f08c00', gS: '#fff3bf', line: '#e3dfd3' };
function txt(parent, x, y, s, attrs = {}) {
  const t = el('text', Object.assign({ x, y, 'font-size': 13, fill: C.ink, 'text-anchor': 'middle' }, attrs), parent);
  t.textContent = s;
  return t;
}
// text with a superscript part: base^sup
function txtSup(parent, x, y, base, sup, attrs = {}) {
  const t = el('text', Object.assign({ x, y, 'font-size': 13, fill: C.ink, 'text-anchor': 'middle' }, attrs), parent);
  const a = el('tspan', {}, t); a.textContent = base;
  if (sup) { const b = el('tspan', { dy: -6, 'font-size': (+(attrs['font-size'] || 13) * 0.72).toFixed(1) }, t); b.textContent = sup; }
  return t;
}
// render "∅^(…)" style names into svg text
function txtH(parent, x, y, name, attrs = {}) {
  const m = name.match(/^(.*?)\^\((.*)\)$/);
  return m ? txtSup(parent, x, y, m[1], `(${m[2]})`, attrs) : txt(parent, x, y, name, attrs);
}
const htmlH = name => name.replace(/\^\((.*)\)$/, '<sup>($1)</sup>');
function seeded(seed) { let s = seed >>> 0; return () => ((s = (s * 1664525 + 1013904223) >>> 0) / 4294967296); }

/* ---------- generic: check-yourself ---------- */
const CY = {
  s1: { q: bi('Prefix ∀n ∃f ∀m in front of a recursive R. Which class does the collapse give?', '递归 R 前面加前缀 ∀n ∃f ∀m。化简后属于哪一类？'),
    opts: [['Π¹₁', 0], ['Σ¹₁', 1], ['Σ¹₂', 0], ['Π⁰₂', 0]],
    why: bi('Σ¹₁. Push ∀n right past ∃f: ∀n ∃f ⇔ ∃g ∀n (with f = gₙ). What is left is ∃g followed by number quantifiers only.', 'Σ¹₁。把 ∀n 越过 ∃f 推到右边：∀n ∃f ⇔ ∃g ∀n（f 取 gₙ）。剩下的是 ∃g 后面只跟数量词。') },
  s2: { q: bi('A recursive tree T ⊆ ω<sup>&lt;ω</sup> has a node at every length. Must T have an infinite branch?', '递归树 T ⊆ ω<sup>&lt;ω</sup> 在每个长度上都有结点。T 一定有无穷分支吗？'),
    opts: [[bil('Yes, always', '一定有'), 0], [bil('Not necessarily; but yes if T is finitely branching', '不一定；但若 T 有限分叉则一定有'), 1], [bil('Never', '一定没有'), 0]],
    why: bi('The broom has nodes at every length (⟨n,0,…,0⟩) but no infinite branch. For finitely branching trees, Kőnig\'s lemma applies.', '扫帚树在每个长度上都有结点（⟨n,0,…,0⟩），却没有无穷分支。对有限分叉的树，柯尼希引理适用。') },
  s3: { q: bi('x codes ω+ω*: a copy of ω followed by a reversed copy of ω. Is x ∈ WO?', 'x 编码 ω+ω*：一份 ω 后面接一份倒过来的 ω。x ∈ WO 吗？'),
    opts: [[bil('Yes', '是'), 0], [bil('No', '否'), 1], [bil('Undecidable', '不可判定'), 0]],
    why: bi('No: c₀ > c₁ > c₂ > … in the ω* part is an infinite descending sequence, i.e. a branch through the tree of descending sequences.', '否：ω* 部分里 c₀ > c₁ > c₂ > … 是无穷降链，也就是下降序列树的一条分支。') },
  s4: { q: bi('Which of these ordinals is <b>not</b> recursive?', '下列哪个序数<b>不是</b>递归序数？'),
    opts: [['ε₀', 0], ['ω^ω^ω', 0], [CK, 1], ['Γ₀', 0]],
    why: bi(`${CK} is by definition the least non-recursive ordinal. ε₀, Γ₀ and ω^ω^ω all have recursive notation systems.`, `${CK} 按定义就是最小的非递归序数。ε₀、Γ₀、ω^ω^ω 都有递归的记号系统。`) },
  s5: { q: bi('a ∈ O is a notation for ω. What is |2<sup>2<sup>a</sup></sup>|<sub>O</sub>?', 'a ∈ O 是 ω 的记号。|2<sup>2<sup>a</sup></sup>|<sub>O</sub> 等于多少？'),
    opts: [['ω+2', 1], ['ω·2', 0], ['ω', 0], ['2', 0]],
    why: bi('Each 2<sup>(·)</sup> is one successor step: ω → ω+1 → ω+2.', '每个 2<sup>(·)</sup> 是一次后继：ω → ω+1 → ω+2。') },
  s6: { q: bi('Can a (lightface) Σ¹₁ set A ⊆ WO contain a code of every recursive ordinal?', '一个（细体）Σ¹₁ 集 A ⊆ WO 能否包含每个递归序数的某个编码？'),
    opts: [[bil('Yes', '能'), 0], [bil('No', '不能'), 1]],
    why: bi(`No. Then sup{|x| : x ∈ A} ≥ ${CK}, contradicting boundedness (a).`, `不能。否则 sup{|x| : x ∈ A} ≥ ${CK}，与有界性定理 (a) 矛盾。`) },
  s7: { q: bi('Is ∅<sup>(ω)</sup> arithmetical?', '∅<sup>(ω)</sup> 是算术集吗？'),
    opts: [[bil('Yes', '是'), 0], [bil('No', '不是'), 1]],
    why: bi('No. If ∅<sup>(ω)</sup> ≤<sub>T</sub> ∅<sup>(n)</sup>, then ∅<sup>(n+1)</sup> ≤<sub>T</sub> ∅<sup>(ω)</sup> ≤<sub>T</sub> ∅<sup>(n)</sup>, which is impossible.', '不是。若 ∅<sup>(ω)</sup> ≤<sub>T</sub> ∅<sup>(n)</sup>，则 ∅<sup>(n+1)</sup> ≤<sub>T</sub> ∅<sup>(ω)</sup> ≤<sub>T</sub> ∅<sup>(n)</sup>，不可能。') },
  s8: { q: bi('Which of these is <b>not</b> Δ¹₁?', '下列哪个<b>不是</b> Δ¹₁？'),
    opts: [['∅<sup>(ω+7)</sup>', 0], ['∅‴', 0], ['O', 1], [bil('{e : φₑ total}', '{e : φₑ 全定义}'), 0]],
    why: bi('O is Π¹₁-complete, hence not Σ¹₁. The others are hyperarithmetic (∅‴ and the Π⁰₂ set {e : φₑ total} are even arithmetical).', 'O 是 Π¹₁-完全的，因此不是 Σ¹₁。其他几个都是超算术的（∅‴ 与 Π⁰₂ 集 {e : φₑ 全定义} 甚至是算术集）。') },
  s9: { q: bi('Spector–Gandy: a Π¹₁ set of numbers can be written as', 'Spector–Gandy：ω 的 Π¹₁ 子集可以写成'),
    opts: [[bil('∃Y ∈ HYP with an arithmetical matrix', '∃Y ∈ HYP 加算术母式'), 1], [bil('∀Y ∈ HYP with an arithmetical matrix', '∀Y ∈ HYP 加算术母式'), 0], [bil('∃Y recursive with an arithmetical matrix', '∃Y 递归加算术母式'), 0]],
    why: bi('∃Y ∈ HYP. (“∃Y recursive + arithmetical” only gives arithmetical sets: a number quantifier over indices.)', '∃Y ∈ HYP。（“∃Y 递归 + 算术母式”只能得到算术集：那只是对指标的数量词。）') },
  s10: { q: bi('Can forcing change the truth value of a Π¹₂ sentence?', '力迫能改变 Π¹₂ 语句的真值吗？'),
    opts: [[bil('Yes', '能'), 0], [bil('No', '不能'), 1], [bil('Only in the presence of large cardinals', '只有在存在大基数时才能'), 0]],
    why: bi('No: V is an inner model of V[G], so Shoenfield applies (the negation of a Π¹₂ sentence is Σ¹₂).', '不能：V 是 V[G] 的内模型，Shoenfield 定理适用（Π¹₂ 语句的否定是 Σ¹₂）。') },
};
document.querySelectorAll('.cy').forEach(box => {
  const d = CY[box.dataset.cy];
  box.innerHTML = `<div class="q">✎ ${bil('Check yourself', '自测')}: ${d.q}</div><div class="opts"></div><div class="toolbar"><button class="btn small ghost">${bil('Show answer', '看答案')}</button></div><div class="msg"></div>`;
  const opts = box.querySelector('.opts'), msg = box.querySelector('.msg');
  const btns = d.opts.map(([h, ok]) => {
    const b = document.createElement('button');
    b.className = 'btn small';
    b.innerHTML = h;
    b.addEventListener('click', () => {
      btns.forEach(x => x.classList.remove('right', 'wrongc'));
      b.classList.add(ok ? 'right' : 'wrongc');
      if (ok) okBox(msg, '✓ ' + d.why); else okBox(msg, bi('✗ Not quite. Look at the visual above again.', '✗ 不对。再看看上面的图。'), 'bad');
    });
    opts.appendChild(b);
    return b;
  });
  box.querySelector('.toolbar button').addEventListener('click', () => {
    btns.forEach((x, i) => { x.classList.remove('wrongc'); if (d.opts[i][1]) x.classList.add('right'); });
    okBox(msg, d.why, 'info');
  });
});

/* ---------- generic: step-by-step proofs ---------- */
document.querySelectorAll('[data-steps]').forEach(b => b.addEventListener('click', () => {
  const steps = [...$(b.dataset.steps).querySelectorAll('.step')];
  if (b.dataset.act === 'all') steps.forEach(s => s.classList.add('on'));
  else { const nx = steps.find(s => !s.classList.contains('on')); if (nx) nx.classList.add('on'); }
}));

/* ================= §1 quantifier collapse ================= */
(function quantifiers() {
  let qs = [{ q: 'A', t: 'f' }, { q: 'E', t: 'n' }];
  const names = { n: ['n', 'm', 'k', 'j', 'l', 'p'], f: ['f', 'g', 'h', 'u', 'v', 'w'] };
  const sym = x => (x.q === 'E' ? '∃' : '∀') + x.v;
  function label() { const c = { n: 0, f: 0 }; qs.forEach(x => { x.v = names[x.t][c[x.t]++ % 6]; }); }
  const pal = [['E', 'n', '∃n'], ['A', 'n', '∀n'], ['E', 'f', '∃f'], ['A', 'f', '∀f']];
  pal.forEach(([q, t, s]) => {
    const b = document.createElement('button');
    b.className = 'btn small';
    b.innerHTML = `+ <span class="m">${s}</span> ${t === 'n' ? bil('number', '数') : bil('function', '函数')}`;
    b.addEventListener('click', () => { if (qs.length < 7) { qs.push({ q, t }); render(); } });
    $('qPal').appendChild(b);
  });
  const del = document.createElement('button');
  del.className = 'btn small ghost'; del.innerHTML = bil('⌫ remove last', '⌫ 删去最后一个');
  del.addEventListener('click', () => { qs.pop(); render(); });
  $('qPal').appendChild(del);
  const go = document.createElement('button');
  go.className = 'btn primary'; go.innerHTML = bil('Collapse ▶', '化简 ▶');
  go.addEventListener('click', () => collapse());
  $('qPal').appendChild(go);
  const presets = [['∀f ∃n', 'Af En'], ['∀n ∃f ∀m', 'An Ef Am'], ['∃n ∀f ∃g', 'En Af Ef'], ['∀m ∃n', 'An En'], ['∃f ∀g ∃n', 'Ef Af En'], ['∀f ∀g ∃n ∃h', 'Af Af En Ef']];
  presets.forEach(([s, code]) => {
    const b = document.createElement('button');
    b.className = 'btn small'; b.innerHTML = `<span class="m">${s} R</span>`;
    b.addEventListener('click', () => { qs = code.split(' ').map(c => ({ q: c[0], t: c[1] === 'f' ? 'f' : 'n' })); render(); collapse(); });
    $('qPresets').appendChild(b);
  });
  const box = x => `<div class="qbox ${x.t === 'f' ? 'fn' : 'num'}">${sym(x)}<small>${x.t === 'f' ? bil('function', '函数') : bil('number', '数')}</small></div>`;
  const mat = inner => `<div class="qbox mat">${inner}<small>${bil('matrix', '母式')}</small></div>`;
  function render() {
    label();
    $('qStage').innerHTML = `<div class="qrow"><span class="lab">${bil('Your formula', '你的公式')}</span>${qs.map(box).join('')}${mat('R')}</div>`;
    $('qMsg').innerHTML = bi('Press <b>Collapse ▶</b>.', '按<b>化简 ▶</b>。');
  }
  async function collapse() {
    label();
    const st = L18.collapseStages(qs), cl = L18.classifyPrefix(qs);
    const h = `<div class="qrow"><span class="lab">${bil('Your formula', '你的公式')}</span>${qs.map(box).join('')}${mat('R')}</div>`;
    $('qStage').innerHTML = h;
    await sleep(500);
    const numPart = st.pushed.num.map(sym).join(' ');
    const row2 = st.pushed.fn.length
      ? `<div class="qrow fadein"><span class="lab">${bil('① numbers pushed right', '① 数量词右移')}</span>${st.pushed.fn.map(box).join('')}${mat(`<span>${numPart} R</span>`)}</div>`
      : `<div class="qrow fadein"><span class="lab">${bil('① no function quantifiers', '① 没有函数量词')}</span>${mat(`<span>${numPart || ''} R</span>`)}</div>`;
    $('qStage').insertAdjacentHTML('beforeend', row2);
    await sleep(700);
    if (st.pushed.fn.length) {
      const row3 = `<div class="qrow fadein"><span class="lab">${bil('② equal blocks merged', '② 同类块合并')}</span>${st.merged.map(b => `<div class="qbox fn">${b.q === 'E' ? '∃' : '∀'}${b.members.map(x => x.v).join('⊕')}<small>${b.members.length > 1 ? bil('merged', '已合并') : bil('function', '函数')}</small></div>`).join('')}${mat(bil('arithmetical', '算术'))}<span class="qres">${cl.name}</span></div>`;
      $('qStage').insertAdjacentHTML('beforeend', row3);
      okBox($('qMsg'), bi(`${cl.k} alternating block(s) of function quantifiers, starting with ${cl.cls === 'Σ' ? '∃' : '∀'}, so the formula is <b>${cl.name}</b>. Number quantifiers never count. (This is an upper bound: the set defined may be simpler.)`,
        `函数量词共 ${cl.k} 个交替块，第一块是 ${cl.cls === 'Σ' ? '∃' : '∀'}，所以公式是 <b>${cl.name}</b>。数量词从不计数。（这是上界：定义出的集合可能更简单。）`), 'info');
    } else {
      $('qStage').insertAdjacentHTML('beforeend', `<div class="qrow fadein"><span class="lab">${bil('② result', '② 结果')}</span><span class="qres">${cl.name}</span></div>`);
      okBox($('qMsg'), bi(`No function quantifiers: this is the arithmetical hierarchy of L17. ${cl.k ? `${cl.k} alternating number block(s) give <b>${cl.name}</b>` : 'No quantifiers: <b>recursive</b>'}. Every arithmetical set is Δ¹₁.`,
        `没有函数量词：这就是第 17 课的算术层级。${cl.k ? `${cl.k} 个交替的数量词块给出 <b>${cl.name}</b>` : '没有量词：<b>递归</b>'}。每个算术集都是 Δ¹₁ 的。`), 'info');
    }
  }
  render();
  collapse();
})();

/* ================= §2 / E2 tree explorer ================= */
function Explorer(svg, opts) {
  const W = 900, H = +svg.getAttribute('height');
  const st = { tree: opts.tree, path: [], offset: 0, info: false, busy: false };
  const SLOTS = 10;
  function childWindow(s, start) {
    const T = st.tree, out = [];
    if (!T.omega) { for (let k = 0; k < T.b; k++) if (T.has(s.concat([k]))) out.push(k); return { vals: out, more: false }; }
    let k = start;
    while (out.length < SLOTS && k < start + 60) { if (T.has(s.concat([k]))) out.push(k); k++; }
    return { vals: out, more: T.infChildren(s) };
  }
  function infoLabel(s) {
    if (!st.info) return '';
    const T = st.tree;
    if ((st.kind || opts.infoKind) === 'size') { const z = T.size(s); return z === Infinity ? '|·|=∞' : `|·|=${z}`; }
    const r = T.height(s);
    return r === Infinity ? 'ρ: ∞' : `ρ=${r}`;
  }
  function draw() {
    svg.innerHTML = '';
    const p = st.path, L = p.length;
    const start = Math.max(0, L - 4);
    const rowY = r => 34 + (r - start) * 62;
    const pos = {};
    // header
    const hd = txt(svg, 12, 18, `${opts.name()} · depth ${L} · 深度 ${L}`, { 'text-anchor': 'start', fill: C.mut, 'font-size': 12 });
    hd.setAttribute('font-family', 'var(--sans)');
    if (start > 0) txt(svg, W / 2, 14, '⋮', { fill: C.mut });
    const rows = [];
    for (let r = start; r <= L; r++) {
      if (r === 0) { rows.push({ r, items: [{ v: null, s: [] }] }); continue; }
      const parent = p.slice(0, r - 1), chosen = p[r - 1];
      let s0 = 0;
      if (st.tree.omega && chosen >= SLOTS) s0 = chosen - SLOTS + 2;
      const w = childWindow(parent, s0);
      if (!w.vals.includes(chosen)) w.vals.push(chosen);
      rows.push({ r, items: w.vals.map(v => ({ v, s: parent.concat([v]) })), more: w.more, s0 });
    }
    const cw = childWindow(p, st.offset);
    rows.push({ r: L + 1, items: cw.vals.map(v => ({ v, s: p.concat([v]) })), more: cw.more, kids: true, s0: st.offset });
    const xs = n => Array.from({ length: n }, (_, j) => W / 2 + (j - (n - 1) / 2) * 80);
    rows.forEach(row => {
      const n = row.items.length + (row.more ? 1 : 0) + (row.kids && st.offset > 0 ? 1 : 0);
      const X = xs(Math.max(n, 1));
      let j = row.kids && st.offset > 0 ? 1 : 0;
      row.items.forEach(it => { it.x = X[j++]; it.y = rowY(row.r); });
      if (row.more) row.moreX = X[j];
      if (row.kids && st.offset > 0) row.prevX = X[0];
    });
    // edges
    rows.forEach(row => {
      if (row.r === 0) return;
      const par = rows.find(q => q.r === row.r - 1);
      const pnode = par && par.items.find(it => it.s.length === row.r - 1 && it.s.every((v, i) => v === p[i]));
      if (!pnode) return;
      row.items.forEach(it => {
        const onPath = it.s.length <= L && it.v === p[it.s.length - 1];
        el('line', { x1: pnode.x, y1: pnode.y + 14, x2: it.x, y2: it.y - 14, stroke: onPath ? C.acc : '#c9c4b5', 'stroke-width': onPath ? 3 : 1.4 }, svg);
      });
      if (row.more) el('line', { x1: pnode.x, y1: pnode.y + 14, x2: row.moreX, y2: row.items.length ? row.items[0].y - 14 : rowY(row.r) - 14, stroke: '#c9c4b5', 'stroke-dasharray': '3 4' }, svg);
    });
    // nodes
    rows.forEach(row => {
      row.items.forEach(it => {
        const onPath = it.s.length <= L && it.s.every((v, i) => v === p[i]);
        const isCur = it.s.length === L && onPath;
        const g0 = el('g', { class: 'nd', transform: `translate(${it.x},${it.y})` }, svg);
        const g = el('g', { class: row.kids ? 'pop' : '' }, g0);
        const leafNow = !st.tree.has(it.s.concat([0])) && childWindow(it.s, 0).vals.length === 0;
        el('circle', { r: 15, fill: isCur ? C.acc : onPath ? C.accS : row.kids ? '#fff' : '#f6f4ee', stroke: onPath ? C.acc : leafNow && st.info ? C.f : '#9aa0aa', 'stroke-width': 2 }, g);
        txt(g, 0, 5, it.v === null ? '⟨⟩' : String(it.v), { 'font-size': it.v === null ? 12 : 14, 'font-weight': 700, fill: isCur ? '#fff' : C.ink });
        const il = infoLabel(it.s);
        if (il) txt(g, 0, 30, il, { 'font-size': 11, fill: il.includes('∞') ? C.m : C.mut });
        g0.addEventListener('click', () => { if (st.busy) return; st.path = it.s.slice(); st.offset = 0; update(); });
      });
      if (row.more) {
        const g = el('g', { class: 'nd', transform: `translate(${row.moreX},${rowY(row.r)})` }, svg);
        el('rect', { x: -30, y: -13, width: 60, height: 26, rx: 13, fill: C.gS, stroke: C.g }, g);
        txt(g, 0, 5, row.kids ? 'more →' : '…', { 'font-size': 12, fill: '#6b4500' });
        if (row.kids) g.addEventListener('click', () => { st.offset += SLOTS; draw(); });
      }
      if (row.kids && st.offset > 0) {
        const g = el('g', { class: 'nd', transform: `translate(${row.prevX},${rowY(row.r)})` }, svg);
        el('rect', { x: -30, y: -13, width: 60, height: 26, rx: 13, fill: C.gS, stroke: C.g }, g);
        txt(g, 0, 5, '← prev', { 'font-size': 12, fill: '#6b4500' });
        g.addEventListener('click', () => { st.offset = Math.max(0, st.offset - SLOTS); draw(); });
      }
      if (row.kids && !row.items.length && !row.more) {
        txt(svg, W / 2, rowY(row.r), '✗ ' + 'dead end (leaf) · 死胡同（叶子）', { fill: C.f, 'font-size': 14, 'font-weight': 700 });
      }
    });
  }
  function update() { draw(); opts.onMove && opts.onMove(st); }
  return {
    st, draw, update,
    setTree(T, kind) { st.tree = T; st.kind = kind; st.path = []; st.offset = 0; update(); },
    back() { st.path.pop(); st.offset = 0; update(); },
    reset() { st.path = []; st.offset = 0; update(); },
    toggleInfo() { st.info = !st.info; draw(); },
    async walk(chooser, n = 8) {
      if (st.busy) return; st.busy = true;
      for (let i = 0; i < n; i++) { const k = chooser(st.path); if (k === null) break; st.path.push(k); st.offset = 0; update(); await sleep(420); }
      st.busy = false;
    },
  };
}

(function trees() {
  const T = L18.trees;
  const defs = {
    A: { tree: T.A, infoKind: 'size', en: 'Tree A: binary (finitely branching)', zh: '树 A：二叉（有限分叉）' },
    B: { tree: T.B, infoKind: 'rank', en: 'Tree B: the broom (ω-branching)', zh: '树 B：扫帚树（ω 分叉）' },
    C: { tree: T.C, infoKind: 'rank', en: 'Tree C: ω-branching, hidden branch', zh: '树 C：ω 分叉，藏着一条分支' },
  };
  let cur = 'A';
  const names = { A: 'Tree A · 树 A', B: 'Tree B · 树 B', C: 'Tree C · 树 C' };
  const ex = Explorer($('trSvg'), { tree: T.A, infoKind: 'size', name: () => names[cur], onMove: msg });
  const btns = {};
  Object.entries(defs).forEach(([k, d]) => {
    const b = document.createElement('button');
    b.className = 'btn small' + (k === cur ? ' sel' : '');
    b.innerHTML = bi(d.en, d.zh);
    b.addEventListener('click', () => { cur = k; Object.values(btns).forEach(x => x.classList.remove('sel')); b.classList.add('sel'); ex.st.info = false; ex.setTree(d.tree, d.infoKind); });
    btns[k] = b;
    $('treePick').appendChild(b);
  });
  function msg(st) {
    const p = st.path, tr = defs[cur].tree;
    const ps = `<span class="m">⟨${p.join(',')}⟩</span>`;
    const dead = !tr.infChildren(p) && (tr.omega ? !tr.has(p.concat([0])) && !(tr.onBranch(p)) : ![0, 1].some(k => tr.has(p.concat([k]))));
    let h;
    if (cur === 'A') h = bi(`At ${ps}. Tree A is infinite and finitely branching, so by Kőnig's lemma it <b>has</b> an infinite branch. Turn on sizes: at every node on the branch, exactly one child has an infinite subtree.`,
      `当前在 ${ps}。树 A 无穷且有限分叉，由柯尼希引理，它<b>一定有</b>无穷分支。打开“子树大小”：分支上的每个结点，恰有一个子结点的子树是无穷的。`);
    else if (cur === 'B') h = bi(`At ${ps}. The broom: T = {⟨⟩} ∪ {⟨n,0,…,0⟩ of length ≤ n+1}. It has nodes at every length, yet <b>no infinite branch</b>: choosing n at the root leaves only n more steps. It is WF with rank ρ(⟨⟩) = sup(n+1) = ω.`,
      `当前在 ${ps}。扫帚树：T = {⟨⟩} ∪ {长度 ≤ n+1 的 ⟨n,0,…,0⟩}。它在每个长度都有结点，却<b>没有无穷分支</b>：在根处选了 n，就只剩 n 步可走。它是良基的，秩 ρ(⟨⟩) = sup(n+1) = ω。`);
    else h = bi(`At ${ps}. Tree C has exactly one infinite branch; every wrong turn dies within 3 steps, but there are infinitely many turns to try at each node. (Hint: a famous constant.) Ranks: “∞” marks nodes on the infinite branch, which have no ordinal rank.`,
      `当前在 ${ps}。树 C 恰有一条无穷分支；每次走错，3 步之内就会死掉，但每个结点都有无穷多个方向可试。（提示：一个著名的常数。）秩：“∞”标出无穷分支上的结点，它们没有序数秩。`);
    if (dead) h += bi(' <b>Dead end.</b> Back up and try another child.', ' <b>死胡同。</b>退回去换个子结点。');
    if (cur === 'C' && p.length >= 8 && tr.onBranch(p)) h += bi(` <b>You are on the branch: 3.14159… the digits of π.</b>`, ` <b>你在分支上：3.14159…，π 的各位数字。</b>`);
    okBox($('trMsg'), h, dead ? 'warn' : 'info');
  }
  ex.st.info = false;
  $('trBack').addEventListener('click', () => ex.back());
  $('trReset').addEventListener('click', () => ex.reset());
  $('trInfo').addEventListener('click', () => ex.toggleInfo());
  $('trKonig').addEventListener('click', () => {
    const tr = defs[cur].tree;
    if (cur !== 'A') {
      okBox($('trMsg'), cur === 'B'
        ? bi('Kőnig\'s strategy is “move to a child with infinitely many nodes above it”. At the broom\'s root <b>no</b> child qualifies, since each ⟨n⟩ has only n+1 nodes above it, even though the root has infinitely many. The pigeonhole step needs finitely many children.',
          '柯尼希策略是“走到上方有无穷多个结点的子结点”。在扫帚树的根处，<b>没有</b>这样的子结点：每个 ⟨n⟩ 上方只有 n+1 个结点，尽管根上方有无穷多个。抽屉原理那一步需要子结点只有有限个。')
        : bi('In tree C even dead nodes have infinitely many children, so “infinitely many nodes above” no longer detects the branch. In general, finding a branch of a recursive ω-branching tree can require information far beyond the arithmetical (there are recursive trees with branches but none hyperarithmetic).',
          '在树 C 中，即使是死结点也有无穷多个子结点，所以“上方有无穷多个结点”不再能识别分支。一般地，为 ω 分叉的递归树找分支所需的信息可能远超算术层级（存在有分支、却没有超算术分支的递归树）。'), 'warn');
      return;
    }
    ex.st.info = true;
    if (!tr.onBranch(ex.st.path)) { ex.st.path = []; }
    ex.walk(p => [0, 1].find(k => tr.size(p.concat([k])) === Infinity) ?? null, 8);
  });
  ex.update();
})();

/* ================= §3 descent game ================= */
(function descent() {
  const O = L18.orders;
  const svg = $('dSvg');
  const seg = (x0, x1, n, rev = false) => { const r = 0.74, t = 1 - Math.pow(r, n); return rev ? x1 - (x1 - x0) * t : x0 + (x1 - x0) * t; };
  const layouts = {
    w3: () => [...Array(13)].map((_, n) => ({ e: { g: 'a', n }, x: seg(40, 640, n) })).concat([0, 1, 2].map(n => ({ e: { g: 'b', n }, x: 700 + n * 80 }))),
    w2: () => [...Array(12)].map((_, n) => ({ e: { g: 'a', n }, x: seg(40, 430, n) })).concat([...Array(12)].map((_, n) => ({ e: { g: 'b', n }, x: seg(470, 860, n) }))),
    ww: () => { const out = []; const starts = [40, 330, 540, 690, 800]; const ends = [300, 515, 670, 785, 860];
      for (let a = 0; a < 5; a++) for (let b = 0; b < 7 - a; b++) out.push({ e: { g: a, n: b }, x: seg(starts[a], ends[a], b) }); return out; },
    Z: () => [...Array(17)].map((_, i) => ({ e: { g: 'z', n: i - 8 }, x: 450 + (i - 8) * 50 })),
    wws: () => [...Array(11)].map((_, n) => ({ e: { g: 'a', n }, x: seg(40, 440, n) })).concat([...Array(11)].map((_, n) => ({ e: { g: 'c', n }, x: seg(480, 860, n, true) }))),
  };
  const lab = (k, e) => {
    if (k === 'Z') return String(e.n);
    if (k === 'wws') return e.g === 'a' ? `a${subs(e.n)}` : `c${subs(e.n)}`;
    return L18.ordStr(O[k].ord(e));
  };
  const pick = { w3: 'ω+3', w2: 'ω·2', ww: 'ω²', Z: 'ℤ', wws: 'ω+ω*' };
  let cur = 'w3', seq = [], pts = [], token = 0;
  const btns = {};
  Object.entries(pick).forEach(([k, s]) => {
    const b = document.createElement('button');
    b.className = 'btn small' + (k === cur ? ' sel' : '');
    b.innerHTML = `<span class="m">${s}</span>`;
    b.addEventListener('click', () => { cur = k; Object.values(btns).forEach(x => x.classList.remove('sel')); b.classList.add('sel'); seq = []; token++; build(); });
    btns[k] = b;
    $('dPick').appendChild(b);
  });
  const same = (x, y) => x.g === y.g && x.n === y.n;
  function build() {
    svg.innerHTML = '';
    const o = O[cur];
    el('line', { x1: 30, x2: 875, y1: 80, y2: 80, stroke: '#c9c4b5', 'stroke-width': 2 }, svg);
    txt(svg, 450, 22, `${pick[cur]}  ·  ${o.wo ? 'well-order · 良序' : 'NOT a well-order · 不是良序'}`, { 'font-size': 14, 'font-weight': 700, fill: o.wo ? C.t : C.f });
    pts = layouts[cur]();
    pts.forEach(pt => {
      const inSeq = seq.findIndex(y => same(y, pt.e));
      const g = el('g', { class: 'nd', transform: `translate(${pt.x},80)` }, svg);
      const isLast = inSeq >= 0 && inSeq === seq.length - 1;
      const r = Math.max(4, Math.min(9, 9 - Math.abs(pt.e.n) * 0.35));
      el('circle', { r, fill: isLast ? C.m : inSeq >= 0 ? C.mS : '#fff', stroke: inSeq >= 0 ? C.m : C.ink, 'stroke-width': 2 }, g);
      el('rect', { x: -12, y: -20, width: 24, height: 40, fill: 'transparent' }, g);
      const s = lab(cur, pt.e);
      const big = (cur !== 'ww' && Math.abs(pt.e.n) < 6) || (cur === 'ww' && (inSeq >= 0 || pt.e.n === 0 || (pt.e.n === 1 && pt.e.g < 2)));
      if (big) txt(g, 0, (cur === 'ww' ? (pt.e.n === 0 ? -16 : 34) : (pts.indexOf(pt) % 2 ? 34 : -16)), s, { 'font-size': 11, fill: inSeq >= 0 ? C.m : C.mut, 'font-weight': inSeq >= 0 ? 700 : 400 });
      if (inSeq >= 0 && (inSeq < 6 || isLast)) txt(g, 0, 60, `x${subs(inSeq)}`, { 'font-size': 12, 'font-weight': 700, fill: C.m });
      g.addEventListener('click', () => click(pt.e));
    });
    // continuation marks
    const dots = { w3: [[660, 80]], w2: [[445, 80], [868, 80]], ww: [[875, 80]], Z: [[30, 80], [872, 80]], wws: [[455, 80], [465, 80]] }[cur];
    dots.forEach(([x, y]) => txt(svg, x, y - 6, '…', { fill: C.mut }));
    drawMatrix();
    msg();
  }
  function drawMatrix() {
    const m = $('dMat'); m.innerHTML = '';
    const M = L18.codeMatrix(O[cur], 8), cs = 22, x0 = 34, y0 = 34;
    txt(m, 115, 14, 'x(⟨m,n⟩) = [m ≤ n]', { 'font-size': 11, fill: C.mut });
    for (let i = 0; i < 8; i++) {
      const e = O[cur].enumN(i);
      txt(m, 16, y0 + i * cs + 15, String(i), { 'font-size': 10, fill: C.mut });
      txt(m, x0 + i * cs + 11, y0 - 4, String(i), { 'font-size': 10, fill: C.mut });
      for (let j = 0; j < 8; j++) {
        el('rect', { x: x0 + j * cs + 1, y: y0 + i * cs + 1, width: cs - 2, height: cs - 2, rx: 3, fill: M[i][j] ? C.tS : '#f3f1ea' }, m);
        txt(m, x0 + j * cs + 11, y0 + i * cs + 15, String(M[i][j]), { 'font-size': 10, fill: M[i][j] ? C.t : '#bbb' });
      }
      const t = txt(m, x0 + 8 * cs + 4, y0 + i * cs + 15, '', { 'font-size': 9, fill: C.acc, 'text-anchor': 'start' });
      t.textContent = lab(cur, e);
    }
  }
  function msg() {
    const o = O[cur];
    $('dSeq').innerHTML = seq.length ? seq.map((e, i) => `<span class="ord-chip">x${subs(i)} = ${lab(cur, e)}</span>`).join(' &gt; ') : `<span class="muted">${bil('click any point to start', '点任意一点开始')}</span>`;
    if (!seq.length) {
      okBox($('dMsg'), o.wo ? bi(`The root ⟨⟩ of the tree of descending sequences has rank ${o.type}, the order type.`, `下降序列树的根 ⟨⟩ 的秩为 ${o.type}，即序型。`)
        : bi('This order is not a well-order. Can you see an infinite descending sequence? Try <b>Auto-descend</b>.', '这个序不是良序。你能看出一条无穷降链吗？试试<b>自动下降</b>。'), 'info');
      return;
    }
    const last = seq[seq.length - 1];
    if (o.wo) {
      const r = o.ord(last);
      const zero = r[0] === 0 && r[1] === 0;
      okBox($('dMsg'), zero ? bi(`Reached the least element: the descent is over after ${seq.length} step(s). Every descent in a well-order ends, though descents can be arbitrarily long.`, `到达最小元：下降在 ${seq.length} 步后结束。良序中每次下降都会结束，尽管下降可以任意长。`)
        : bi(`Node ⟨x₀,…,x${subs(seq.length - 1)}⟩ has rank <b>${L18.ordStr(r)}</b> in the tree of descending sequences: the ranks strictly drop along a descent, so it must end.`, `结点 ⟨x₀,…,x${subs(seq.length - 1)}⟩ 在下降序列树中的秩为 <b>${L18.ordStr(r)}</b>：沿下降方向秩严格变小，所以必然终止。`), zero ? 'ok' : 'info');
    } else okBox($('dMsg'), bi('No ordinal rank here: below some points there is an infinite descending sequence, i.e. an infinite branch in the tree of descending sequences.', '这里没有序数秩：某些点下方存在无穷降链，也就是下降序列树中的无穷分支。'), 'warn');
  }
  function click(e) {
    const o = O[cur];
    if (seq.length && !o.less(e, seq[seq.length - 1])) {
      okBox($('dMsg'), bi(`✗ ${lab(cur, e)} is not below ${lab(cur, seq[seq.length - 1])}. Each new point must be strictly smaller.`, `✗ ${lab(cur, e)} 不比 ${lab(cur, seq[seq.length - 1])} 小。每个新点必须严格更小。`), 'bad');
      return;
    }
    seq.push(e);
    build();
  }
  $('dReset').addEventListener('click', () => { token++; seq = []; build(); });
  $('dAuto').addEventListener('click', async () => {
    const my = ++token, o = O[cur];
    if (o.wo) {
      seq = [];
      // greedy demo: from the top, step down by one ω-block, then count down
      const plan = { w3: [{ g: 'b', n: 2 }, { g: 'b', n: 0 }, { g: 'a', n: 5 }, { g: 'a', n: 3 }, { g: 'a', n: 1 }, { g: 'a', n: 0 }],
        w2: [{ g: 'b', n: 4 }, { g: 'b', n: 1 }, { g: 'a', n: 6 }, { g: 'a', n: 2 }, { g: 'a', n: 0 }],
        ww: [{ g: 3, n: 2 }, { g: 2, n: 4 }, { g: 1, n: 5 }, { g: 0, n: 4 }, { g: 0, n: 1 }, { g: 0, n: 0 }] }[cur];
      for (const e of plan) { if (my !== token) return; seq.push(e); build(); await sleep(500); }
      return;
    }
    seq = [];
    const plan = cur === 'Z' ? [...Array(9)].map((_, i) => ({ g: 'z', n: 2 - i })) : [...Array(11)].map((_, n) => ({ g: 'c', n }));
    for (const e of plan) { if (my !== token) return; seq.push(e); build(); await sleep(380); }
    okBox($('dMsg'), bi('…and it never stops: an infinite descending sequence f, so ∃f (∀k f(k+1) &lt;<sub>x</sub> f(k)) holds and x ∉ WO.', '……而且永远不会停：这是一条无穷降链 f，所以 ∃f (∀k f(k+1) &lt;<sub>x</sub> f(k)) 成立，x ∉ WO。'), 'bad');
  });
  build();
})();

/* ================= §4 ordinal ladder ================= */
(function ladder() {
  const svg = $('lSvg');
  const WALL = 700;
  const ticks = [
    { s: '0', x: 30, rec: 1, en: 'The empty order (field ∅).', zh: '空序（域为 ∅）。' },
    { s: '1', x: 52, rec: 1, en: 'One point.', zh: '一个点。' },
    { s: '2', x: 70, rec: 1, en: 'Two points: {0,1} with 0 &lt; 1.', zh: '两个点：{0,1}，0 &lt; 1。' },
    { s: 'ω', x: 140, rec: 1, en: 'The usual order of ℕ.', zh: 'ℕ 上的通常序。' },
    { s: 'ω+1', x: 175, rec: 1, en: 'Move 0 to the top: m ≺ n ⇔ (n = 0 ∧ m ≠ 0) ∨ (0 &lt; m &lt; n).', zh: '把 0 挪到最上面：m ≺ n ⇔ (n = 0 ∧ m ≠ 0) ∨ (0 &lt; m &lt; n)。' },
    { s: 'ω·2', x: 235, rec: 1, en: 'Evens first, then odds: m ≺ n ⇔ (m mod 2, m) &lt;<sub>lex</sub> (n mod 2, n).', zh: '先偶数后奇数：m ≺ n ⇔ (m mod 2, m) &lt;<sub>lex</sub> (n mod 2, n)。' },
    { s: 'ω²', x: 310, rec: 1, en: 'Pairs: ⟨a,b⟩ ≺ ⟨c,d⟩ ⇔ (a,b) &lt;<sub>lex</sub> (c,d).', zh: '配对：⟨a,b⟩ ≺ ⟨c,d⟩ ⇔ (a,b) &lt;<sub>lex</sub> (c,d)。' },
    { s: 'ω^ω', x: 385, rec: 1, en: 'Codes of finite non-increasing sequences (Cantor normal form exponents), compared lexicographically.', zh: '有限不增序列（康托尔范式的指数）的编码，按字典序比较。' },
    { s: 'ε₀', x: 455, rec: 1, en: 'Cantor normal form terms ω^α₁+…+ω^αₖ (α₁ ≥ … ≥ αₖ) coded by numbers; comparison is computed by recursion on the terms. (ε₀ is the proof-theoretic ordinal of PA.)', zh: '用自然数编码康托尔范式项 ω^α₁+…+ω^αₖ（α₁ ≥ … ≥ αₖ）；比较大小可沿项的结构递归计算。（ε₀ 是 PA 的证明论序数。）' },
    { s: 'Γ₀', x: 525, rec: 1, en: 'Veblen normal forms; comparison is recursive (Feferman–Schütte ordinal).', zh: 'Veblen 范式；比较是递归的（Feferman–Schütte 序数）。' },
    { s: 'BH', x: 595, rec: 1, en: 'Bachmann–Howard ordinal ψ(ε<sub>Ω+1</sub>): an ordinal collapsing notation system, still recursive.', zh: 'Bachmann–Howard 序数 ψ(ε<sub>Ω+1</sub>)：一个序数坍缩记号系统，仍是递归的。' },
    { s: CKs, x: WALL, rec: 0, wall: 1, en: `${CK}: countable (a sup of countably many countable ordinals), but no recursive well-order has this type. It is the least non-recursive ordinal.`, zh: `${CK}：可数（可数多个可数序数的上确界），但没有任何递归良序具有这个序型。它是最小的非递归序数。` },
    { s: CKs + '+1', x: 760, rec: 0, en: `Not recursive: recursive ordinals are closed downward, and ${CK} &lt; ${CK}+1.`, zh: `非递归：递归序数向下封闭，而 ${CK} &lt; ${CK}+1。` },
    { s: 'ω₁', x: 900, rec: 0, en: 'The first uncountable ordinal: not even countable. Far beyond.', zh: '第一个不可数序数：连可数都不是，远在后面。' },
  ];
  function draw() {
    svg.innerHTML = '';
    el('rect', { x: 20, y: 70, width: WALL - 20, height: 50, rx: 8, fill: C.tS, opacity: .7 }, svg);
    el('rect', { x: WALL, y: 70, width: 210, height: 50, rx: 8, fill: '#eceae3' }, svg);
    txt(svg, 360, 62, 'recursive ordinals · 递归序数', { fill: C.t, 'font-size': 12, 'font-weight': 700 });
    txt(svg, 805, 62, 'non-recursive · 非递归', { fill: C.mut, 'font-size': 12, 'font-weight': 700 });
    el('line', { x1: 20, x2: 910, y1: 95, y2: 95, stroke: C.ink, 'stroke-width': 2 }, svg);
    el('line', { x1: WALL, x2: WALL, y1: 52, y2: 140, stroke: C.f, 'stroke-width': 3, 'stroke-dasharray': '6 4' }, svg);
    txt(svg, 848, 100, '//', { fill: C.mut, 'font-size': 16 });
    ticks.forEach((t, i) => {
      const g = el('g', { class: 'nd' }, svg);
      el('line', { x1: t.x, x2: t.x, y1: 86, y2: 104, stroke: t.wall ? C.f : C.ink, 'stroke-width': 2 }, g);
      el('circle', { cx: t.x, cy: 95, r: 7, fill: t.rec ? '#fff' : t.wall ? C.fS : '#ddd', stroke: t.rec ? C.t : C.f, 'stroke-width': 2 }, g);
      const up = i % 2 === 0;
      txt(g, t.x, up ? 140 : 160, t.s, { 'font-size': 13, 'font-weight': 700, fill: t.rec ? C.ink : C.f });
      g.addEventListener('click', () => show(t));
    });
  }
  function show(t) {
    okBox($('lMsg'), `<b class="m">${t.s.replace(CKs, CK)}</b> · ${t.rec ? bil('recursive', '递归') : bil('not recursive', '非递归')}: ${bi(t.en, t.zh)}`, t.rec ? 'ok' : 'warn');
  }
  let token = 0;
  $('lClimb').addEventListener('click', async () => {
    const my = ++token;
    draw();
    const mk = el('circle', { cx: 30, cy: 95, r: 10, fill: C.m, opacity: .85 }, svg);
    mk.style.transition = 'cx .45s';
    for (const t of ticks.filter(t => t.rec)) {
      if (my !== token) return;
      mk.setAttribute('cx', t.x);
      show(t);
      await sleep(520);
    }
    for (let k = 1; k <= 14; k++) {
      if (my !== token) return;
      const x = 595 + (WALL - 595) * (1 - Math.pow(0.68, k));
      el('line', { x1: x, x2: x, y1: 89, y2: 101, stroke: C.t, 'stroke-width': 1.5, class: 'fadein' }, svg);
      mk.setAttribute('cx', x);
      await sleep(180);
    }
    okBox($('lMsg'), bi(`The climb never reaches the red wall. Each recursive α has a recursive successor α+1 (and much more), so the recursive ordinals have no largest element; their sup ${CK} is a limit ordinal that is itself not recursive. Still, ${CK} &lt; ω₁.`,
      `攀登永远到不了红墙。每个递归 α 都有递归的后继 α+1（还有更大的），所以递归序数没有最大元；它们的上确界 ${CK} 是极限序数，本身不是递归的。尽管如此，${CK} &lt; ω₁。`), 'info');
  });
  draw();
  okBox($('lMsg'), bi('Click a rung.', '点击一个刻度。'), 'info');
})();

/* ================= §5 Kleene's O ================= */
(function kleeneO() {
  const svg = $('oSvg');
  let O, sel, cmpMode = false, cmpPick = [];
  const MAXN = 4, COLW = 128;
  const X = col => 70 + col * COLW;
  const Y = (m, n) => 495 - m * 170 - n * 22;
  function notation(x) {
    if (x.kind === 'root') return '1';
    if (x.kind === 'L') return `3·5^e${subs(x.e)}`;
    const b = notation(x.base);
    const nums = { '1': '2', '2': '4', '4': '16', '16': '65536' };
    if (nums[b]) return nums[b];
    return `2^(${b})`;
  }
  function notHtml(x) {
    if (x.kind === 'root') return '1';
    if (x.kind === 'L') return `3·5<sup>e${subs(x.e)}</sup>`;
    const b = notation(x.base);
    const nums = { '1': '2', '2': '4', '4': '16', '16': '65536' };
    return nums[b] || `2<sup>${notHtml(x.base)}</sup>`;
  }
  function seqDesc(x) {
    if (x.kind !== 'L') return '';
    const a = notation(x.base);
    return x.variant === 'A'
      ? bi(`φ<sub>e${subs(x.e)}</sub>(n) = the (n+1)-th successor of ${a}: the notations of |${a}|+1, |${a}|+2, …`, `φ<sub>e${subs(x.e)}</sub>(n) = ${a} 的第 n+1 个后继：即 |${a}|+1, |${a}|+2, … 的记号`)
      : bi(`φ<sub>e${subs(x.e)}</sub>(n) = the (2n+1)-th successor of ${a}: the notations of |${a}|+1, |${a}|+3, |${a}|+5, …`, `φ<sub>e${subs(x.e)}</sub>(n) = ${a} 的第 2n+1 个后继：即 |${a}|+1, |${a}|+3, |${a}|+5, … 的记号`);
  }
  function reset() { O = L18.makeO(); sel = O.root; cmpMode = false; cmpPick = []; draw(); info(); }
  function draw() {
    svg.innerHTML = '';
    // block guides
    [0, 1, 2].forEach(m => {
      el('line', { x1: 20, x2: 880, y1: Y(m, 0) + 18, y2: Y(m, 0) + 18, stroke: '#eee' }, svg);
      txt(svg, 878, Y(m, 0) + 14, m === 0 ? '0' : m === 1 ? 'ω' : 'ω·2', { 'font-size': 11, fill: C.mut, 'text-anchor': 'end' });
    });
    // columns: successor chains + ⋮
    O.cols.forEach((c, ci) => {
      const inCol = O.nodes.filter(x => x.col === ci);
      if (!inCol.length) return;
      const top = inCol.reduce((a, b) => (b.n > a.n ? b : a));
      txt(svg, X(ci), Y(top.m, top.n) - 22, '⋮', { fill: C.mut, 'font-size': 16 });
    });
    if (O.cols.length === 1) txt(svg, 470, 200, 'select a node, then add a limit to grow O upward · 选中结点后添加极限，让 O 向上生长', { 'font-size': 12, fill: C.mut });
    O.nodes.forEach(x => {
      if (x.kind === 'S') el('line', { x1: X(x.col), y1: Y(x.m, x.n) + 12, x2: X(x.base.col), y2: Y(x.base.m, x.base.n) - 12, stroke: C.ink, 'stroke-width': 2 }, svg);
      if (x.kind === 'L') {
        const a = x.base, x1 = X(a.col), y1 = Y(a.m, MAXN) - 30, x2 = X(x.col), y2 = Y(x.m, x.n) + 12;
        el('path', { d: `M${x1},${y1} C${x1},${y1 - 28} ${x2},${y2 + 28} ${x2},${y2}`, fill: 'none', stroke: x.variant === 'A' ? C.acc : C.g, 'stroke-width': 2, 'stroke-dasharray': '6 5' }, svg);
        txt(svg, (x1 + x2) / 2, (y1 + y2) / 2 - 6, `φₑ${subs(x.e)}`, { 'font-size': 12, fill: x.variant === 'A' ? C.acc : C.g });
      }
    });
    O.nodes.forEach(x => {
      const g = el('g', { class: 'nd', transform: `translate(${X(x.col)},${Y(x.m, x.n)})` }, svg);
      const isSel = x === sel, isCmp = cmpPick.includes(x);
      el('rect', { x: -40, y: -10, width: 80, height: 20, rx: 10, fill: isCmp ? C.gS : isSel ? C.accS : '#fff', stroke: isCmp ? C.g : isSel ? C.acc : C.ink, 'stroke-width': isSel || isCmp ? 3 : 1.5 }, g);
      txt(g, 0, 4, L18.oOrdStr(x), { 'font-size': 12, 'font-weight': 700 });
      const t = el('title', {}, g); t.textContent = notation(x);
      g.addEventListener('click', () => clickNode(x));
    });
  }
  function count(x) { return O.nodes.filter(y => y.m === x.m && y.n === x.n).length; }
  function info(extra = '') {
    const x = sel;
    let h = `${bil('Selected', '选中')}: <b class="m">${notHtml(x)}</b> &nbsp; |·|<sub>O</sub> = <b>${L18.oOrdStr(x)}</b>`;
    if (x.kind === 'L') h += '<br>' + seqDesc(x);
    const k = count(x);
    h += '<br>' + (x.m === 0 ? bi('Finite ordinals have exactly one notation.', '有限序数恰有一个记号。')
      : bi(`You have built ${k} notation(s) for ${L18.oOrdStr(x)} so far; there are infinitely many.`, `到目前为止你为 ${L18.oOrdStr(x)} 造了 ${k} 个记号；实际上有无穷多个。`));
    okBox($('oMsg'), h + extra, 'info');
  }
  function clickNode(x) {
    if (cmpMode) {
      cmpPick.push(x);
      if (cmpPick.length === 2) {
        const [a, b] = cmpPick;
        let rel, en, zh;
        if (a === b) { rel = '='; en = 'the same notation'; zh = '是同一个记号'; }
        else if (O.below(a, b)) { rel = '&lt;<sub>O</sub>'; en = 'comparable'; zh = '可比较'; }
        else if (O.below(b, a)) { rel = '&gt;<sub>O</sub>'; en = 'comparable'; zh = '可比较'; }
        else { rel = '⊥'; en = '<b>incomparable</b> under &lt;<sub>O</sub>, although |·| compares them'; zh = '在 &lt;<sub>O</sub> 下<b>不可比较</b>，尽管 |·| 可以比较它们'; }
        okBox($('oMsg'), `<span class="m">${notHtml(a)} ${rel} ${notHtml(b)}</span> &nbsp; (|·| = ${L18.oOrdStr(a)}, ${L18.oOrdStr(b)}): ${bil(en, zh)}`
          + (rel === '⊥' ? bi('<br>Two different notations built from different fundamental sequences lie on different branches of the tree &lt;<sub>O</sub>.', '<br>由不同基本序列造出的两个不同记号，位于树 &lt;<sub>O</sub> 的不同分支上。') : ''), rel === '⊥' ? 'warn' : 'ok');
        cmpMode = false;
        cmpPick = [];
        draw();
        $('oCmp').classList.remove('sel');
        return;
      }
      draw();
      okBox($('oMsg'), bi('Now click the second node.', '再点第二个结点。'), 'info');
      return;
    }
    sel = x; draw(); info();
  }
  $('oSucc').addEventListener('click', () => {
    if (sel.n >= MAXN) { info(bi('<br>(Canvas limit: at most 4 successors drawn per column. The ⋮ means they go on forever.)', '<br>（画布限制：每列最多画 4 个后继，⋮ 表示还会无限延续。）')); return; }
    const r = O.succ(sel); sel = r.node; draw(); info();
  });
  function lim(v) {
    if (sel.m >= 2) { info(bi('<br>(Canvas limit: this demo stops at ω·2+n. Limits of limits give ω², …)', '<br>（画布限制：本演示只到 ω·2+n。对极限再取极限可得 ω² 等。）')); return; }
    if (O.cols.length >= 6 && !O.nodes.find(x => x.kind === 'L' && x.base === sel && x.variant === v)) { info(bi('<br>(Canvas full: press Reset.)', '<br>（画布已满，请按重置。）')); return; }
    const r = O.limit(sel, v); sel = r.node; draw(); info();
  }
  $('oLimA').addEventListener('click', () => lim('A'));
  $('oLimB').addEventListener('click', () => lim('B'));
  $('oCmp').addEventListener('click', () => { cmpMode = true; cmpPick = []; $('oCmp').classList.add('sel'); okBox($('oMsg'), bi('Compare mode: click the first node.', '比较模式：点击第一个结点。'), 'info'); });
  $('oReset').addEventListener('click', reset);
  reset();
  // pre-build the finite chain 1, 2, 4, 16, 65536
  for (let i = 0; i < 4; i++) sel = O.succ(sel).node;
  sel = O.root; draw(); info();
})();

/* ================= §6 boundedness ================= */
(function bounded() {
  const svg = $('bSvg'), WALL = 620;
  const sets = [
    { k: 'w2', en: 'WO<sub>&lt;ω²</sub> = {x ∈ WO : |x| &lt; ω²}', zh: 'WO<sub>&lt;ω²</sub> = {x ∈ WO : |x| &lt; ω²}', bound: 250, lab: 'ω²', kind: 'ok',
      men: 'Δ¹₁ (so Σ¹₁), and bounded by ω² &lt; ω₁<sup>CK</sup>, as the theorem demands. (|x| &lt; ω² iff x ∈ LO and ∃k (x embeds into a fixed recursive order of type ω·k): Σ¹₁. Being also Π¹₁, it is Δ¹₁.)',
      mzh: 'Δ¹₁（从而是 Σ¹₁），且以 ω² &lt; ω₁<sup>CK</sup> 为界，正如定理所要求。（|x| &lt; ω² 当且仅当 x ∈ LO 且 ∃k（x 能嵌入一个固定的、序型为 ω·k 的递归序）：这是 Σ¹₁ 的。它同时也是 Π¹₁ 的，所以是 Δ¹₁。）' },
    { k: 'kl', en: '{KB(T<sub>n</sub>) : n ∈ A}, A ∈ Δ¹₁', zh: '{KB(T<sub>n</sub>) : n ∈ A}，A ∈ Δ¹₁', bound: 420, lab: 'α', kind: 'ok',
      men: 'Σ¹₁ because A is Σ¹₁. So all types lie below one recursive α. This is the key step of Kleene\'s theorem (§8).',
      mzh: '因为 A 是 Σ¹₁ 的，所以它是 Σ¹₁ 的。于是所有序型都在某一个递归序数 α 之下。这是克莱尼定理（§8）的关键一步。' },
    { k: 'rec', en: '{x ∈ WO : x recursive}', zh: '{x ∈ WO : x 递归}', bound: WALL, lab: CKs, kind: 'bad',
      men: 'Its types are exactly the recursive ordinals, with sup ω₁<sup>CK</sup> not attained. By the theorem this set is <b>not Σ¹₁</b>. It is Π¹₁: x ∈ WO ∧ ∃e (x = φ<sub>e</sub>).',
      mzh: '它的序型恰好是全体递归序数，上确界 ω₁<sup>CK</sup> 取不到。由定理，这个集合<b>不是 Σ¹₁</b>的。它是 Π¹₁ 的：x ∈ WO ∧ ∃e (x = φ<sub>e</sub>)。' },
    { k: 'wo', en: 'WO', zh: 'WO', bound: 905, lab: 'ω₁', kind: 'bad',
      men: 'Types fill all of ω₁, unbounded. So WO is not even boldface Σ¹₁ (part (b)).',
      mzh: '序型填满整个 ω₁，无界。所以 WO 连粗体 Σ¹₁ 都不是（(b) 部分）。' },
  ];
  let cur = sets[0];
  const btns = [];
  sets.forEach(s => {
    const b = document.createElement('button');
    b.className = 'btn small' + (s === cur ? ' sel' : '');
    b.innerHTML = bi(s.en, s.zh);
    b.addEventListener('click', () => { cur = s; btns.forEach(x => x.classList.remove('sel')); b.classList.add('sel'); draw(); });
    btns.push(b);
    $('bPick').appendChild(b);
  });
  function draw() {
    svg.innerHTML = '';
    el('line', { x1: 20, x2: 910, y1: 90, y2: 90, stroke: C.ink, 'stroke-width': 2 }, svg);
    el('rect', { x: 20, y: 60, width: WALL - 20, height: 60, fill: C.tS, opacity: .45 }, svg);
    el('line', { x1: WALL, x2: WALL, y1: 40, y2: 135, stroke: C.f, 'stroke-width': 3, 'stroke-dasharray': '6 4' }, svg);
    txt(svg, WALL, 32, CKs, { fill: C.f, 'font-weight': 700 });
    txt(svg, 905, 32, 'ω₁', { fill: C.ink, 'font-weight': 700 });
    txt(svg, 30, 32, '0', {});
    txt(svg, 760, 108, '//', { fill: C.mut, 'font-size': 15 });
    const rnd = seeded(7 + cur.k.length);
    const N = 34;
    for (let i = 0; i < N; i++) {
      let x;
      if (cur.k === 'wo') x = 25 + 880 * rnd();
      else if (cur.k === 'rec') x = WALL - (WALL - 25) * Math.pow(rnd(), 1.8) - 2;
      else x = 25 + (cur.bound - 30) * Math.pow(rnd(), 0.8);
      const c = el('circle', { cx: x, cy: 90 + (rnd() - .5) * 34, r: 4.5, fill: cur.kind === 'ok' ? C.acc : C.m, opacity: .8, class: 'pop' }, svg);
      c.style.animationDelay = (i * 0.03) + 's';
    }
    if (cur.k !== 'wo') {
      el('line', { x1: cur.bound, x2: cur.bound, y1: 55, y2: 125, stroke: cur.kind === 'ok' ? C.acc : C.m, 'stroke-width': 2.5 }, svg);
      txt(svg, cur.bound, 150, cur.k === 'rec' ? 'sup = ω₁ᶜᴷ (not attained · 取不到)' : `sup ≤ ${cur.lab} < ω₁ᶜᴷ`, { 'font-size': 12, fill: cur.kind === 'ok' ? C.acc : C.m, 'font-weight': 700 });
    } else txt(svg, 470, 150, 'unbounded in ω₁ · 在 ω₁ 中无界', { 'font-size': 12, fill: C.m, 'font-weight': 700 });
    okBox($('bMsg'), bi(cur.men, cur.mzh), cur.kind === 'ok' ? 'ok' : 'warn');
  }
  draw();
})();

/* ================= §7 hyperarithmetic ladder ================= */
(function hyp() {
  const svg = $('hSvg');
  let hist, token = 0;
  const reset = () => { hist = [[0, 0]]; draw(); };
  function draw() {
    svg.innerHTML = '';
    const WALLX = 800;
    el('line', { x1: WALLX, x2: WALLX, y1: 20, y2: 300, stroke: C.f, 'stroke-width': 3, 'stroke-dasharray': '6 4' }, svg);
    txt(svg, WALLX, 16, CKs, { fill: C.f, 'font-weight': 700 });
    txt(svg, 850, 110, 'O', { 'font-size': 26, 'font-weight': 800, fill: C.m });
    txt(svg, 850, 132, 'Π¹₁-complete', { 'font-size': 10, fill: C.m });
    txt(svg, 850, 146, 'Π¹₁-完全', { 'font-size': 10, fill: C.m });
    txt(svg, 850, 168, '≥T all ∅⁽ᵅ⁾', { 'font-size': 10, fill: C.mut });
    const show = hist.slice(-11);
    const offset = hist.length - show.length;
    const base = 270;
    show.forEach(([m, n], j) => {
      const i = offset + j;
      const x = 30 + j * 68, h = 30 + 200 * (1 - Math.pow(0.9, i));
      const g = el('g', { class: j === show.length - 1 ? 'pop' : '' }, svg);
      const arith = m === 0;
      if (n === 0 && m > 0) {
        const K = 6;
        for (let r = 0; r < K; r++) el('rect', { x, y: base - h + r * h / K, width: 52, height: h / K - 2, rx: 2, fill: r % 2 ? C.accS : '#d7defc', stroke: C.acc, 'stroke-width': 1 }, g);
        txt(g, x + 26, base - h - 6, '⊕', { fill: C.acc, 'font-weight': 800 });
      } else el('rect', { x, y: base - h, width: 52, height: h, rx: 5, fill: arith ? C.tS : C.accS, stroke: arith ? C.t : C.acc, 'stroke-width': 1.5 }, g);
      txtH(g, x + 26, base + 20, L18.hName(m, n), { 'font-size': 13, 'font-weight': 700, fill: arith ? C.t : C.acc });
      if (j > 0) {
        const [pm, pn] = show[j - 1];
        const lim = n === 0 && m > 0;
        txt(svg, x - 8, base - 10, lim ? '⊕' : '′', { fill: C.mut, 'font-size': 14 });
        void pm; void pn;
      }
    });
    if (offset > 0) txt(svg, 14, base + 20, '…', { fill: C.mut });
    el('line', { x1: 20, x2: 790, y1: base + 30, y2: base + 30, stroke: '#ddd' }, svg);
    const cur = hist[hist.length - 1];
    describe(cur);
  }
  function describe([m, n]) {
    const name = htmlH(L18.hName(m, n));
    let h;
    if (m === 0 && n === 0) h = bi('H(1) = ∅: computable. Press <b>Jump</b>.', 'H(1) = ∅：可计算。按<b>跳跃</b>。');
    else if (m === 0) h = bi(`${name} = H(notation of ${n}) is Σ⁰${subs(n)}-complete (Post). Still <b>arithmetical</b> (green).`, `${name} = H(${n} 的记号)，是 Σ⁰${subs(n)}-完全的（波斯特定理）。仍是<b>算术集</b>（绿色）。`);
    else if (n === 0) h = bi(`${name} = ⊕ₖ ∅<sup>(${m === 1 ? '' : L18.ordStr([m - 1, 0]) + '+'}k)</sup>: row k of the stack is the k-th set below. It computes every set before it, and is <b>not arithmetical</b>. It is hyperarithmetic (Δ¹₁, Step 8).`,
      `${name} = ⊕ₖ ∅<sup>(${m === 1 ? '' : L18.ordStr([m - 1, 0]) + '+'}k)</sup>：堆叠的第 k 行就是下方第 k 个集合。它能计算之前的每个集合，且<b>不是算术集</b>。它是超算术的（Δ¹₁，第 8 步）。`);
    else h = bi(`${name}: jump of the previous set. Δ¹₁, not arithmetical.`, `${name}：前一个集合的跳跃。Δ¹₁，非算术。`);
    if (m >= 3) h += bi(` Keep going in your head: ∅<sup>(ω²)</sup>, ∅<sup>(ω^ω)</sup>, ∅<sup>(ε₀)</sup>, … one set for every α &lt; ${CK}. They never reach the wall, and O sits above all of them.`, ` 在脑子里继续：∅<sup>(ω²)</sup>、∅<sup>(ω^ω)</sup>、∅<sup>(ε₀)</sup>、……每个 α &lt; ${CK} 都对应一个集合。它们永远到不了墙，而 O 在它们所有之上。`);
    okBox($('hMsg'), h, m === 0 ? 'ok' : 'info');
  }
  const jump = () => { const [m, n] = hist[hist.length - 1]; hist.push([m, n + 1]); draw(); };
  const limit = () => { const [m] = hist[hist.length - 1]; if (m >= 5) return; hist.push([m + 1, 0]); draw(); };
  $('hJump').addEventListener('click', () => { token++; jump(); });
  $('hLim').addEventListener('click', () => { token++; limit(); });
  $('hReset').addEventListener('click', () => { token++; reset(); });
  $('hAuto').addEventListener('click', async () => {
    const my = ++token; reset();
    const plan = 'JJJJLJJLJJLJ';
    for (const c of plan) { await sleep(520); if (my !== token) return; c === 'J' ? jump() : limit(); }
  });
  reset();
})();

/* ================= §8 Venn map ================= */
(function venn() {
  const svg = $('vSvg');
  const regions = {
    ar: { x: 450, y: 250 }, d: { x: 450, y: 172 }, pi: { x: 715, y: 180 }, sig: { x: 185, y: 180 },
  };
  const items = [
    { s: '∅″', r: 'ar', en: 'Σ⁰₂-complete: arithmetical, hence Δ¹₁.', zh: 'Σ⁰₂-完全：算术集，因而是 Δ¹₁。' },
    { s: '{e : φₑ total}', r: 'ar', en: 'Π⁰₂ (∀n ∃s: φₑ(n) halts by stage s): arithmetical.', zh: 'Π⁰₂（∀n ∃s：φₑ(n) 在第 s 步前停机）：算术集。' },
    { s: '∅⁽ʷ⁾', svgs: ['∅', '(ω)'], r: 'd', en: 'Hyperarithmetic, not arithmetical.', zh: '超算术，非算术。' },
    { s: '∅⁽ᵋ⁰⁾', svgs: ['∅', '(ε₀)'], r: 'd', en: 'ε₀ is recursive, so ∅<sup>(ε₀)</sup> is hyperarithmetic, hence Δ¹₁ by Kleene.', zh: 'ε₀ 是递归序数，所以 ∅<sup>(ε₀)</sup> 是超算术的，由克莱尼定理是 Δ¹₁。' },
    { s: 'O', r: 'pi', en: 'Π¹₁-complete; not Σ¹₁ (else every Π¹₁ set would be Δ¹₁).', zh: 'Π¹₁-完全；不是 Σ¹₁（否则每个 Π¹₁ 集都会是 Δ¹₁）。' },
    { s: 'W', r: 'pi', en: 'Indices of recursive well-orders: Π¹₁-complete.', zh: '递归良序的指标集：Π¹₁-完全。' },
    { s: 'ℕ∖O', r: 'sig', en: 'Complement of a Π¹₁-complete set: Σ¹₁-complete.', zh: 'Π¹₁-完全集的补集：Σ¹₁-完全。' },
    { s: '{e : Tₑ ill-founded}', r: 'sig', en: 'Indices of recursive trees with an infinite branch: ∃f ∀m (f↾m ∈ Tₑ), Σ¹₁-complete.', zh: '有无穷分支的递归树的指标集：∃f ∀m (f↾m ∈ Tₑ)，Σ¹₁-完全。' },
  ];
  let lit = null;
  function draw() {
    svg.innerHTML = '';
    el('ellipse', { cx: 340, cy: 175, rx: 260, ry: 150, fill: 'rgba(240,140,0,.10)', stroke: C.g, 'stroke-width': 2.5 }, svg);
    el('ellipse', { cx: 560, cy: 175, rx: 260, ry: 150, fill: 'rgba(174,62,201,.10)', stroke: C.m, 'stroke-width': 2.5 }, svg);
    txt(svg, 150, 50, 'Σ¹₁', { 'font-size': 22, 'font-weight': 800, fill: C.g });
    txt(svg, 750, 50, 'Π¹₁', { 'font-size': 22, 'font-weight': 800, fill: C.m });
    txt(svg, 450, 92, 'Δ¹₁ = HYP', { 'font-size': 16, 'font-weight': 800, fill: C.acc });
    txt(svg, 450, 110, `{A : A ≤T ∅⁽ᵅ⁾, α < ${CKs}}`, { 'font-size': 11, fill: C.acc });
    el('ellipse', { cx: 450, cy: 258, rx: 118, ry: 46, fill: 'rgba(47,158,68,.15)', stroke: C.t, 'stroke-width': 2 }, svg);
    txt(svg, 450, 284, 'arithmetical · 算术', { 'font-size': 11, fill: C.t, 'font-weight': 700 });
    const counts = {};
    items.forEach(it => {
      const k = counts[it.r] = (counts[it.r] || 0) + 1;
      const base = regions[it.r];
      const x = base.x + (k === 1 ? -40 : 40) * (it.r === 'ar' ? 1 : 0.9), y = base.y + (it.r === 'ar' ? -4 : (k === 1 ? -26 : 26));
      const on = lit === it;
      const g = el('g', { class: 'nd', transform: `translate(${x},${y})` }, svg);
      el('circle', { r: 5, fill: on ? C.f : C.ink }, g);
      if (it.svgs) txtSup(g, 0, -10, it.svgs[0], it.svgs[1], { 'font-size': 12, 'font-weight': on ? 800 : 500, fill: on ? C.f : C.ink });
      else txt(g, 0, -10, it.s, { 'font-size': 12, 'font-weight': on ? 800 : 500, fill: on ? C.f : C.ink });
      g.addEventListener('click', () => pick(it));
      it.g = g;
    });
  }
  const rname = { ar: bil('arithmetical ⊆ Δ¹₁', '算术集 ⊆ Δ¹₁'), d: bil('Δ¹₁, not arithmetical', 'Δ¹₁ 但非算术'), pi: bil('Π¹₁, not Σ¹₁', 'Π¹₁ 但非 Σ¹₁'), sig: bil('Σ¹₁, not Π¹₁', 'Σ¹₁ 但非 Π¹₁') };
  function pick(it) { lit = it; draw(); okBox($('vMsg'), `<b class="m">${it.s.replace('∅⁽ʷ⁾', '∅<sup>(ω)</sup>').replace('∅⁽ᵋ⁰⁾', '∅<sup>(ε₀)</sup>')}</b>: ${rname[it.r]}. ${bi(it.en, it.zh)}`, 'info'); }
  items.forEach(it => {
    const b = document.createElement('button');
    b.className = 'btn small';
    b.innerHTML = `<span class="m">${it.s.replace('∅⁽ʷ⁾', '∅<sup>(ω)</sup>').replace('∅⁽ᵋ⁰⁾', '∅<sup>(ε₀)</sup>')}</span>`;
    b.addEventListener('click', () => pick(it));
    $('vPick').appendChild(b);
  });
  draw();
  okBox($('vMsg'), bi('Click a set (button or dot).', '点击一个集合（按钮或圆点）。'), 'info');
})();

/* ================= §9 Spector–Gandy & uniformization ================= */
(function sg() {
  const svg = $('sgSvg');
  const rnd = seeded(18);
  const dots = [...Array(170)].map(() => ({ x: 40 + 820 * rnd(), y: 40 + 140 * rnd(), hyp: false }));
  const hyp = [...Array(14)].map(() => ({ x: 70 + 120 * rnd(), y: 70 + 90 * rnd(), hyp: true }));
  let token = 0;
  function base() {
    svg.innerHTML = '';
    el('rect', { x: 20, y: 24, width: 860, height: 168, rx: 14, fill: '#fbfaf6', stroke: C.line, 'stroke-width': 2 }, svg);
    txt(svg, 450, 16, 'ω^ω: all reals (uncountable) · 全体实数（不可数）', { 'font-size': 12, fill: C.mut });
    el('ellipse', { cx: 130, cy: 115, rx: 85, ry: 58, fill: 'rgba(59,91,219,.08)', stroke: C.acc, 'stroke-dasharray': '4 4' }, svg);
    txt(svg, 130, 186, 'HYP (countable · 可数)', { 'font-size': 11, fill: C.acc, 'font-weight': 700 });
    return [...dots.filter(d => !(Math.hypot((d.x - 130) / 85, (d.y - 115) / 58) < 1.05)), ...hyp].map(d => ({ d, c: el('circle', { cx: d.x, cy: d.y, r: d.hyp ? 4.5 : 3, fill: d.hyp ? C.acc : '#b9b4a6' }, svg) }));
  }
  base();
  okBox($('sgMsg'), bi('Pick a view.', '选择一种视角。'), 'info');
  $('sgAll').addEventListener('click', async () => {
    const my = ++token; const cs = base();
    const bar = el('rect', { x: 20, y: 24, width: 6, height: 168, fill: C.m, opacity: .5 }, svg);
    for (let x = 20; x <= 880; x += 20) {
      if (my !== token) return;
      bar.setAttribute('x', x);
      cs.forEach(o => { if (o.d.x < x) o.c.setAttribute('fill', C.t); });
      await sleep(30);
    }
    okBox($('sgMsg'), bi('Π¹₁: n ∈ A ⇔ ∀y ∈ ω<sup>ω</sup> R(n, y). <b>Every</b> real must pass the arithmetical test: an uncountable check.', 'Π¹₁：n ∈ A ⇔ ∀y ∈ ω<sup>ω</sup> R(n, y)。<b>每个</b>实数都要通过算术检验：这是一次不可数的检查。'), 'info');
  });
  $('sgHyp').addEventListener('click', async () => {
    const my = ++token; const cs = base();
    const hs = cs.filter(o => o.d.hyp);
    for (let i = 0; i < hs.length; i++) {
      if (my !== token) return;
      hs[i].c.setAttribute('r', 7);
      await sleep(140);
      hs[i].c.setAttribute('r', 4.5);
      if (i === 9) { hs[i].c.setAttribute('fill', C.t); hs[i].c.setAttribute('r', 8); txt(svg, hs[i].d.x, hs[i].d.y - 12, '★ Y', { fill: C.t, 'font-weight': 800 }); break; }
    }
    okBox($('sgMsg'), bi('Spector–Gandy: n ∈ A ⇔ ∃Y ∈ HYP R′(n, Y) with R′ arithmetical. A witness from the <b>countable</b> family HYP suffices. Note: HYP itself, as a set of reals, is Π¹₁ and not Σ¹₁, so “∃Y ∈ HYP” is not a Σ¹₁ quantifier. That is how ∃ can express a Π¹₁ property.',
      'Spector–Gandy：n ∈ A ⇔ ∃Y ∈ HYP R′(n, Y)，R′ 为算术关系。只需在<b>可数</b>族 HYP 中找一个见证。注意：HYP 作为实数集本身是 Π¹₁ 而非 Σ¹₁ 的，所以“∃Y ∈ HYP”不是 Σ¹₁ 量词。这正是 ∃ 能表达 Π¹₁ 性质的原因。'), 'ok');
  });

  // uniformization cartoon
  const us = $('uSvg');
  const NX = 18, NY = 10, CW = 44, CH = 24, X0 = 60, Y0 = 20;
  let P, norm, tok = 0;
  function newP() {
    const r = seeded(Math.floor(Math.random() * 1e9));
    P = [...Array(NX)].map((_, i) => [...Array(NY)].map(() => (i % 7 === 5 ? false : r() < 0.3)));
    norm = [...Array(NX)].map(() => [...Array(NY)].map(() => Math.floor(r() * 4)));
    tok++; drawU();
    okBox($('uMsg'), bi('Click cells to toggle membership in P; numbers are norms. Columns 5 and 12 start empty: x ∉ proj(P).', '点击格子切换是否属于 P；数字是范数。第 5 列和第 12 列一开始是空的：x ∉ proj(P)。'), 'info');
  }
  function drawU(chosen = {}) {
    us.innerHTML = '';
    txt(us, 30, Y0 + NY * CH / 2, 'y', { 'font-size': 14, 'font-weight': 700, fill: C.mut });
    txt(us, X0 + NX * CW / 2, Y0 + NY * CH + 34, 'x', { 'font-size': 14, 'font-weight': 700, fill: C.mut });
    for (let i = 0; i < NX; i++) for (let j = 0; j < NY; j++) {
      const g = el('g', { class: 'nd' }, us);
      const yy = Y0 + (NY - 1 - j) * CH;
      const isC = chosen[i] === j;
      el('rect', { x: X0 + i * CW + 1, y: yy + 1, width: CW - 2, height: CH - 2, rx: 4, fill: isC ? C.t : P[i][j] ? C.mS : '#f6f4ee', stroke: isC ? C.t : P[i][j] ? C.m : '#e6e2d6' }, g);
      if (P[i][j]) txt(g, X0 + i * CW + CW / 2, yy + 16, isC ? `★${norm[i][j]}` : String(norm[i][j]), { 'font-size': 11, fill: isC ? '#fff' : C.m, 'font-weight': isC ? 800 : 500 });
      g.addEventListener('click', () => { P[i][j] = !P[i][j]; tok++; drawU(); });
    }
    for (let i = 0; i < NX; i++) txt(us, X0 + i * CW + CW / 2, Y0 + NY * CH + 14, String(i), { 'font-size': 10, fill: C.mut });
  }
  $('uNew').addEventListener('click', newP);
  $('uGo').addEventListener('click', async () => {
    const my = ++tok; const chosen = {};
    let empty = 0;
    for (let i = 0; i < NX; i++) {
      let best = null;
      for (let j = 0; j < NY; j++) if (P[i][j] && (best === null || norm[i][j] < norm[i][best])) best = j;
      if (best === null) empty++; else chosen[i] = best;
      drawU(chosen);
      await sleep(110);
      if (my !== tok) return;
    }
    okBox($('uMsg'), bi(`Done: every nonempty column now has exactly one ★ (least norm, then least y). The ★ cells form P* ⊆ P, the graph of a function on proj(P); ${empty} empty column(s) stay empty.`,
      `完成：每个非空列现在恰有一个 ★（先取范数最小，再取 y 最小）。★ 格子组成 P* ⊆ P，它是 proj(P) 上某个函数的图像；${empty} 个空列仍是空的。`), 'ok');
  });
  newP();
})();

/* ================= §10 parameters & absoluteness ================= */
(function relat() {
  const cols = [
    { h: bil('a = ∅ (lightface)', 'a = ∅（细体）') },
    { h: 'a = ∅<sup>(ω)</sup>' },
    { h: 'a = O' },
    { h: bil('boldface: some a', '粗体：某个 a') },
  ];
  const rows = [
    { h: 'O ⊆ ω', c: [bil('Π¹₁-complete, not Σ¹₁', 'Π¹₁-完全，非 Σ¹₁'), bil('still not Σ¹₁(a): a ∈ HYP gives Σ¹₁(a) = Σ¹₁', '仍非 Σ¹₁(a)：a ∈ HYP 时 Σ¹₁(a) = Σ¹₁'), bil('Δ⁰₁(a): recursive in O', 'Δ⁰₁(a)：递归于 O'), bil('boldface Δ⁰₁ (take a = O)', '粗体 Δ⁰₁（取 a = O）')] },
    { h: '∅<sup>(ω)</sup> ⊆ ω', c: [bil('Δ¹₁, not arithmetical', 'Δ¹₁，非算术'), 'Δ⁰₁(a)', bil('Δ⁰₁(a) (∅<sup>(ω)</sup> ≤<sub>T</sub> O)', 'Δ⁰₁(a)（∅<sup>(ω)</sup> ≤<sub>T</sub> O）'), bil('boldface Δ⁰₁', '粗体 Δ⁰₁')] },
    { h: 'WO ⊆ 2<sup>ω</sup>', c: [bil('Π¹₁-complete, not Σ¹₁', 'Π¹₁-完全，非 Σ¹₁'), bil('Π¹₁(a), not Σ¹₁(a)', 'Π¹₁(a)，非 Σ¹₁(a)'), bil('Π¹₁(a), not Σ¹₁(a)', 'Π¹₁(a)，非 Σ¹₁(a)'), bil('boldface Π¹₁, not boldface Σ¹₁ (no parameter helps)', '粗体 Π¹₁，非粗体 Σ¹₁（任何参数都无济于事）')] },
    { h: 'ω₁<sup>a</sup>', c: [CK, `= ${CK} (a ∈ HYP)`, `&gt; ${CK} (Spector)`, bil('sup over all a: ω₁', '对所有 a 取 sup：ω₁')] },
  ];
  let selc = 0;
  function draw() {
    let h = `<table class="ptab"><tr><th></th>${cols.map((c, i) => `<th data-c="${i}" class="${i === selc ? 'selc' : ''}">${c.h}</th>`).join('')}</tr>`;
    rows.forEach(r => { h += `<tr><th>${r.h}</th>${r.c.map((c, i) => `<td class="${i === selc ? 'selc' : ''}">${c}</td>`).join('')}</tr>`; });
    $('pTab').innerHTML = h + '</table>';
    $('pTab').querySelectorAll('th[data-c]').forEach(th => th.addEventListener('click', () => { selc = +th.dataset.c; draw(); }));
  }
  draw();

  const svg = $('abSvg');
  const sents = [
    { s: 'Con(ZFC)', cls: 'Π⁰₁', L: '?', V: '?', same: true, en: 'Arithmetical, so absolute: L and V agree. But if ZFC is consistent, ZFC proves neither Con(ZFC) nor its negation, so we write “?” for both. Absolute does not mean decided.', zh: '算术语句，因此是绝对的：L 与 V 意见一致。但若 ZFC 一致，ZFC 既不能证明 Con(ZFC) 也不能证明其否定，所以两边都写“?”。绝对不等于被判定。' },
    { s: bil('T is well-founded', 'T 良基'), p: 'T is well-founded · T 良基', cls: 'Π¹₁', L: '=', V: '=', same: true, en: 'Π¹₁ (T a recursive tree): absolute by Mostowski. Concretely: if L thinks T is WF, L has a rank function ρ : T → Ord, which is still a rank function in V, so V sees no branch either; and a branch in L is a branch in V.', zh: 'Π¹₁（T 为递归树）：由 Mostowski 绝对性定理是绝对的。具体地说：若 L 认为 T 良基，则 L 中有秩函数 ρ : T → Ord，它在 V 中仍是秩函数，所以 V 中也没有分支；而 L 中的分支在 V 中仍是分支。' },
    { s: '∃f ∀g ∃m R', cls: 'Σ¹₂', L: '=', V: '=', same: true, en: 'Shoenfield: Σ¹₂ sentences have the same truth value in L and V.', zh: 'Shoenfield：Σ¹₂ 语句在 L 与 V 中真值相同。' },
    { s: '∃x (x ∉ L)', cls: 'Σ¹₃', L: '✗', V: '✓', same: false, en: '“x ∈ L” is Σ¹₂ for reals x, so this sentence is Σ¹₃. False in L, true in V here: absoluteness fails one level up.', zh: '对实数 x，“x ∈ L”是 Σ¹₂ 的，所以这句话是 Σ¹₃ 的。在 L 中为假，在这里的 V 中为真：再往上一层，绝对性就失效了。' },
    { s: '∀x (x ∈ L)', cls: 'Π¹₃', L: '✓', V: '✗', same: false, en: 'The negation of the previous one: Π¹₃, true in L, false here in V.', zh: '上一句的否定：Π¹₃，在 L 中为真，在这里的 V 中为假。' },
  ];
  function drawU(pickI = -1) {
    svg.innerHTML = '';
    el('rect', { x: 330, y: 20, width: 550, height: 196, rx: 26, fill: 'rgba(59,91,219,.06)', stroke: C.acc, 'stroke-width': 2 }, svg);
    txt(svg, 860, 44, 'V', { 'font-size': 22, 'font-weight': 800, fill: C.acc, 'text-anchor': 'end' });
    el('rect', { x: 350, y: 50, width: 260, height: 150, rx: 22, fill: 'rgba(47,158,68,.08)', stroke: C.t, 'stroke-width': 2 }, svg);
    txt(svg, 372, 74, 'L', { 'font-size': 22, 'font-weight': 800, fill: C.t, 'text-anchor': 'start' });
    txt(svg, 745, 205, 'contains a non-constructible real · 含非可构成实数', { 'font-size': 10, fill: C.mut });
    if (pickI < 0) { txt(svg, 160, 120, '← pick a sentence · 选一句话', { 'font-size': 13, fill: C.mut }); return; }
    const s = sents[pickI];
    const card = el('g', { class: 'pop' }, svg);
    el('rect', { x: 30, y: 90, width: 270, height: 50, rx: 10, fill: '#fff', stroke: C.ink, 'stroke-width': 1.5 }, card);
    const t = txt(card, 165, 113, '', { 'font-size': 13, 'font-weight': 700 });
    t.textContent = s.p || s.s;
    txt(card, 165, 131, s.cls, { 'font-size': 12, fill: C.m, 'font-weight': 700 });
    const badge = (x, y, v) => { const g = el('g', { class: 'pop' }, svg); g.style.animationDelay = '.35s'; el('circle', { cx: x, cy: y, r: 22, fill: v === '✓' ? C.tS : v === '✗' ? C.fS : '#eee', stroke: v === '✓' ? C.t : v === '✗' ? C.f : C.mut, 'stroke-width': 2 }, g); txt(g, x, y + 7, v, { 'font-size': 20, 'font-weight': 800, fill: v === '✓' ? C.t : v === '✗' ? C.f : C.ink }); };
    badge(480, 130, s.L); badge(745, 130, s.V);
    txt(svg, 480, 175, 'in L', { 'font-size': 12, fill: C.t }); txt(svg, 745, 175, 'in V', { 'font-size': 12, fill: C.acc });
    txt(svg, 612, 136, s.same ? '⇔ same truth value · 真值相同' : '≠', { 'font-size': s.same ? 11 : 22, fill: s.same ? C.t : C.f, 'font-weight': 700 });
    okBox($('abMsg'), bi(s.en, s.zh), s.same ? 'ok' : 'warn');
  }
  sents.forEach((s, i) => {
    const b = document.createElement('button');
    b.className = 'btn small';
    b.innerHTML = `<span class="m">${s.s}</span> <span class="muted">${s.cls}</span>`;
    b.addEventListener('click', () => drawU(i));
    $('abPick').appendChild(b);
  });
  drawU();
})();

/* ================= E1 classification ================= */
(function e1() {
  const items = [
    { h: 'WO', a: 'z3', en: 'Π¹₁-complete.', zh: 'Π¹₁-完全。' },
    { h: bil('IF: codes of ill-founded trees on ω', 'IF：ω 上非良基树的编码'), a: 'z4', en: 'Σ¹₁-complete (∃ a branch).', zh: 'Σ¹₁-完全（∃ 一条分支）。' },
    { h: bil('{x ∈ 2<sup>ω</sup> : x has infinitely many 1s}', '{x ∈ 2<sup>ω</sup> : x 有无穷多个 1}'), a: 'z1', en: 'Π⁰₂: ∀n ∃m &gt; n x(m) = 1.', zh: 'Π⁰₂：∀n ∃m &gt; n x(m) = 1。' },
    { h: '∅<sup>(ω)</sup>', a: 'z2', en: 'HYP but not arithmetical.', zh: '超算术但非算术。' },
    { h: 'O', a: 'z3', en: 'Π¹₁-complete.', zh: 'Π¹₁-完全。' },
    { h: bil('LO: codes of linear orders', 'LO：线序的编码'), a: 'z1', en: 'Π⁰₁: all axioms are universal statements about x.', zh: 'Π⁰₁：线序公理都是关于 x 的全称陈述。' },
    { h: bil('codes of trees T ⊆ 2<sup>&lt;ω</sup> with an infinite branch', '有无穷分支的树 T ⊆ 2<sup>&lt;ω</sup> 的编码'), a: 'z1', en: 'Kőnig: a binary tree has a branch iff it has nodes at every level: ∀n ∃σ ∈ 2ⁿ (σ ∈ T), bounded ∃, so Π⁰₁.', zh: '柯尼希：二叉树有分支当且仅当每层都有结点：∀n ∃σ ∈ 2ⁿ (σ ∈ T)，∃ 是有界的，所以是 Π⁰₁。' },
    { h: '∅<sup>(ω·2+1)</sup>', a: 'z2', en: 'HYP (ω·2+1 is recursive), not arithmetical.', zh: '超算术（ω·2+1 是递归序数），非算术。' },
    { h: 'ℕ ∖ O', a: 'z4', en: 'Σ¹₁-complete.', zh: 'Σ¹₁-完全。' },
    { h: bil('W: indices of recursive well-orders', 'W：递归良序的指标集'), a: 'z3', en: 'Π¹₁-complete.', zh: 'Π¹₁-完全。' },
  ];
  const order = ['tray', 'z1', 'z2', 'z3', 'z4'];
  const pos = items.map(() => 'tray');
  function render() {
    ['e1Tray', 'e1z1', 'e1z2', 'e1z3', 'e1z4'].forEach(id => $(id).innerHTML = '');
    items.forEach((it, i) => {
      const d = document.createElement('div');
      d.className = 'chip';
      d.innerHTML = it.h;
      d.addEventListener('click', () => { pos[i] = order[(order.indexOf(pos[i]) + 1) % order.length]; render(); $('e1Msg').className = 'msg'; $('e1Msg').innerHTML = ''; });
      it.el = d;
      $(pos[i] === 'tray' ? 'e1Tray' : 'e1' + pos[i]).appendChild(d);
    });
  }
  render();
  let revealed = false;
  function check(reveal) {
    if (reveal) { revealed = true; items.forEach((it, i) => pos[i] = it.a); }
    render();
    let ok = 0;
    items.forEach((it, i) => { if (pos[i] === it.a) { ok++; it.el.classList.add('ok'); } else if (pos[i] !== 'tray') it.el.classList.add('no'); });
    const why = '<ul style="margin:6px 0 0">' + items.map(it => `<li>${it.h}: ${bi(it.en, it.zh)}</li>`).join('') + '</ul>';
    if (ok === items.length) {
      okBox($('e1Msg'), (reveal ? '' : '✓ ') + bi('All placed correctly.', '全部正确。') + why, reveal ? 'info' : 'ok');
      if (!revealed) Progress.mark('L18E1');
    } else okBox($('e1Msg'), bi(`${ok} / ${items.length} correct (red = wrong place). Ask: is there a real quantifier that cannot be removed? Which way does it point?`, `答对 ${ok} / ${items.length}（红色 = 放错）。想一想：有没有去不掉的实数量词？它朝哪个方向？`), 'warn');
  }
  $('e1Check').addEventListener('click', () => check(false));
  $('e1Show').addEventListener('click', () => check(true));
})();

/* ================= E2 branch hunt ================= */
(function e2() {
  let revealed = false, reached = false, formulaOk = false;
  const ex = Explorer($('e2Svg'), { tree: L18.e2Tree, infoKind: 'rank', name: () => 'E2', onMove: st => {
    const p = st.path, T = L18.e2Tree;
    if (p.length >= 10 && T.onBranch(p)) {
      reached = true;
      okBox($('e2Msg'), bi(`✓ Depth ${p.length}, and every entry of ⟨${p.join(',')}⟩ agrees with the infinite branch f: this node never dies. (Depth alone would not prove it: a node leaving f at position 6 can still reach depth 10 before dying.) Now find the formula.`, `✓ 到达深度 ${p.length}，且 ⟨${p.join(',')}⟩ 的每一项都与无穷分支 f 一致：这个结点永远不会死。（单看深度还不能说明这一点：在第 6 位离开 f 的结点在死掉之前仍可能到达深度 10。）现在找出公式。`), 'ok');
      finish();
    } else if (!T.has(p.concat([0])) && !T.onBranch(p)) okBox($('e2Msg'), bi(`Dead end at ⟨${p.join(',')}⟩. Back up.`, `在 ⟨${p.join(',')}⟩ 走进死胡同。退回去。`), 'warn');
    else okBox($('e2Msg'), bi(`At ⟨${p.join(',')}⟩, depth ${p.length}. Goal: depth 10 on the infinite branch.`, `当前 ⟨${p.join(',')}⟩，深度 ${p.length}。目标：沿无穷分支到达深度 10。`), 'info');
  } });
  function finish() { if (reached && formulaOk && !revealed) Progress.mark('L18E2'); }
  ex.update();
  $('e2Back').addEventListener('click', () => ex.back());
  $('e2Reset').addEventListener('click', () => ex.reset());
  $('e2Show').addEventListener('click', async () => {
    revealed = true;
    ex.reset();
    $('e2In').value = '(3*i + 1) mod 10';
    okBox($('e2FMsg'), bi('Answer: f(i) = (3i + 1) mod 10, i.e. 1, 4, 7, 0, 3, 6, 9, 2, 5, 8, 1, …', '答案：f(i) = (3i + 1) mod 10，即 1, 4, 7, 0, 3, 6, 9, 2, 5, 8, 1, …'), 'info');
    await ex.walk(p => L18.e2f(p.length), 11);
  });
  $('e2Go').addEventListener('click', () => {
    const r = L18.checkFormula($('e2In').value, L18.e2f);
    if (r.ok) {
      formulaOk = true;
      okBox($('e2FMsg'), bi('✓ Matches f(i) for i = 0…39. ' + (reached ? '' : 'Now also reach depth 10 in the tree.'), '✓ 对 i = 0…39 都与 f(i) 一致。' + (reached ? '' : '再在树中走到深度 10。')), 'ok');
      finish();
    } else if (r.err === 'syntax') okBox($('e2FMsg'), bi('Use only i, digits, + − * ( ) and mod (or %).', '只能使用 i、数字、+ − * ( ) 和 mod（或 %）。'), 'bad');
    else okBox($('e2FMsg'), bi(`Your formula gives ${r.got} at i = ${r.at}, but the branch has f(${r.at}) = ${L18.e2f(r.at)}.`, `你的公式在 i = ${r.at} 时给出 ${r.got}，而分支上 f(${r.at}) = ${L18.e2f(r.at)}。`), 'bad');
  });
})();

/* ================= generic true/false list ================= */
function tfList(container, items, progId) {
  const solved = items.map(() => false), shown = items.map(() => false);
  items.forEach((it, i) => {
    const row = document.createElement('div');
    row.className = 'tf';
    row.innerHTML = `<div class="stmt" style="font-family:var(--sans);font-size:15px">${String.fromCharCode(97 + i)}) ${bi(it.en, it.zh)}</div>
      <button class="btn small" data-v="1">${bil('True', '对')}</button>
      <button class="btn small" data-v="0">${bil('False', '错')}</button>
      <button class="btn small ghost" data-v="show">${bil('Show answer', '看答案')}</button>
      <div style="flex-basis:100%"><div class="msg"></div></div>`;
    container.appendChild(row);
    row.querySelectorAll('button').forEach(b => b.addEventListener('click', () => {
      const msg = row.querySelector('.msg');
      if (b.dataset.v === 'show') { shown[i] = true; okBox(msg, (it.ans ? bi('<b>True.</b> ', '<b>对。</b>') : bi('<b>False.</b> ', '<b>错。</b>')) + bi(it.wen, it.wzh), 'info'); return; }
      if ((b.dataset.v === '1') === it.ans) {
        okBox(msg, '✓ ' + bi(it.wen, it.wzh));
        if (!shown[i]) solved[i] = true;
        if (solved.every(Boolean)) Progress.mark(progId);
      } else okBox(msg, bi('✗ Not quite. Which step of the lesson is this about?', '✗ 不对。这题对应本课哪一步？'), 'bad');
    }));
  });
}

/* ================= E3 ================= */
tfList($('e3List'), [
  { ans: true, en: 'ε₀ is a recursive ordinal.', zh: 'ε₀ 是递归序数。', wen: 'Cantor normal forms give a recursive well-order of type ε₀.', wzh: '康托尔范式给出一个序型为 ε₀ 的递归良序。' },
  { ans: true, en: `${CK} is countable.`, zh: `${CK} 是可数的。`, wen: 'Countably many recursive x ∈ WO, so a countable sup of countable ordinals.', wzh: '递归的 x ∈ WO 只有可数多个，所以是可数多个可数序数的上确界。' },
  { ans: false, en: `${CK} + 1 is recursive.`, zh: `${CK} + 1 是递归序数。`, wen: `Recursive ordinals are closed downward; ${CK} itself is not recursive.`, wzh: `递归序数向下封闭，而 ${CK} 本身不是递归的。` },
  { ans: true, en: `Every α &lt; ${CK} is the order type of a recursive well-ordering of a recursive subset of ω.`, zh: `每个 α &lt; ${CK} 都是 ω 的某个递归子集上某个递归良序的序型。`, wen: 'That is what “recursive ordinal” means, and the recursive ordinals are exactly those below ω₁<sup>CK</sup>.', wzh: '这正是“递归序数”的含义，而递归序数恰好是 ω₁<sup>CK</sup> 以下的序数。' },
  { ans: false, en: 'The index set W of recursive well-orderings is arithmetical.', zh: '递归良序的指标集 W 是算术集。', wen: 'W is Π¹₁-complete; arithmetical sets are Δ¹₁, and W is not even Σ¹₁.', wzh: 'W 是 Π¹₁-完全的；算术集都是 Δ¹₁ 的，而 W 连 Σ¹₁ 都不是。' },
  { ans: false, en: 'A recursive linear order with no recursive infinite descending sequence must be a well-order.', zh: '没有递归无穷降链的递归线序一定是良序。', wen: 'Harrison\'s recursive order is ill-founded but has no hyperarithmetic (in particular no recursive) descending sequence.', wzh: 'Harrison 的递归序非良基，却没有超算术的（特别地，没有递归的）降链。' },
  { ans: true, en: `If x ∈ WO is hyperarithmetic, then |x| &lt; ${CK}.`, zh: `若 x ∈ WO 是超算术的，则 |x| &lt; ${CK}。`, wen: '{x} is Δ¹₁, so a Σ¹₁ subset of WO; apply boundedness.', wzh: '{x} 是 Δ¹₁ 的，从而是 WO 的 Σ¹₁ 子集；用有界性定理。' },
  { ans: false, en: `${CK} = ω₁.`, zh: `${CK} = ω₁。`, wen: `${CK} is countable, ω₁ is not.`, wzh: `${CK} 可数，ω₁ 不可数。` },
], 'L18E3');

/* ================= E4 order the proof ================= */
(function e4() {
  const steps = {
    uniq: bi('H(a) is the unique Y satisfying an arithmetical condition Hier(a, Y) (induction along &lt;<sub>O</sub>).', 'H(a) 是满足算术条件 Hier(a, Y) 的唯一 Y（沿 &lt;<sub>O</sub> 归纳）。'),
    twodef: bi('So n ∈ H(a) is both ∃Y- and ∀Y-definable; closing under ≤<sub>T</sub> gives HYP ⊆ Δ¹₁.', '于是 n ∈ H(a) 既可用 ∃Y 也可用 ∀Y 定义；对 ≤<sub>T</sub> 封闭得 HYP ⊆ Δ¹₁。'),
    tree: bi('For A ∈ Δ¹₁: A is Π¹₁, so n ∈ A ⇔ the recursive tree T<sub>n</sub> is well-founded.', '对 A ∈ Δ¹₁：A 是 Π¹₁ 的，所以 n ∈ A ⇔ 递归树 T<sub>n</sub> 良基。'),
    bound: bi('A is also Σ¹₁, so {KB(T<sub>n</sub>) : n ∈ A} is a Σ¹₁ subset of WO; boundedness gives one α &lt; ω₁<sup>CK</sup>.', 'A 也是 Σ¹₁ 的，所以 {KB(T<sub>n</sub>) : n ∈ A} 是 WO 的 Σ¹₁ 子集；有界性给出一个 α &lt; ω₁<sup>CK</sup>。'),
    compute: bi('n ∈ A ⇔ ρ(T<sub>n</sub>) &lt; α, which is computable from some H(b); so A ∈ HYP.', 'n ∈ A ⇔ ρ(T<sub>n</sub>) &lt; α，这可由某个 H(b) 计算；所以 A ∈ HYP。'),
  };
  const shuffled = ['bound', 'twodef', 'compute', 'uniq', 'tree'];
  let seq = [], revealed = false;
  function render(marks) {
    $('e4Pool').innerHTML = '';
    shuffled.forEach(k => {
      const b = document.createElement('button');
      b.className = 'btn' + (seq.includes(k) ? ' used' : '');
      b.innerHTML = steps[k];
      b.addEventListener('click', () => { if (!seq.includes(k)) { seq.push(k); render(); } });
      $('e4Pool').appendChild(b);
    });
    $('e4List').innerHTML = seq.map((k, i) => `<li class="${marks ? (marks[i] ? 'right' : 'wrongc') : ''}">${steps[k]}</li>`).join('');
  }
  render();
  $('e4Undo').addEventListener('click', () => { seq.pop(); render(); $('e4Msg').className = 'msg'; $('e4Msg').innerHTML = ''; });
  $('e4Check').addEventListener('click', () => {
    if (seq.length < 5) { okBox($('e4Msg'), bi('Place all five steps first.', '先把五步都排上。'), 'warn'); return; }
    const marks = seq.map((k, i) => k === L18.E4_ORDER[i]);
    render(marks);
    if (L18.checkOrder(seq)) {
      okBox($('e4Msg'), bi('✓ Correct. Note the roles: Π¹₁ gives the trees, Σ¹₁ gives the bound. Each half of Δ¹₁ is used exactly once.', '✓ 正确。注意分工：Π¹₁ 给出树，Σ¹₁ 给出界。Δ¹₁ 的两半各用了一次。'));
      if (!revealed) Progress.mark('L18E4');
    } else okBox($('e4Msg'), bi('Not yet (red = wrong position). The bound must come after the trees exist, and the computation after the bound.', '还不对（红色 = 位置错）。先有树才能谈界，先有界才能计算。'), 'bad');
  });
  $('e4Show').addEventListener('click', () => { revealed = true; seq = L18.E4_ORDER.slice(); render(seq.map(() => true)); okBox($('e4Msg'), bi('The order of §8.', '即 §8 中的顺序。'), 'info'); });
})();

/* ================= E5 notations ================= */
(function e5() {
  const qs = [
    { type: 'num', q: bi('(a) |16|<sub>O</sub> = ?', '(a) |16|<sub>O</sub> = ?'), ans: '3', why: bi('1 → 2 → 4 → 16: three successor steps (16 = 2<sup>2<sup>2<sup>1</sup></sup></sup>).', '1 → 2 → 4 → 16：三次后继（16 = 2<sup>2<sup>2<sup>1</sup></sup></sup>）。') },
    { type: 'num', q: bi('(b) How many notations in O does the ordinal 5 have?', '(b) 序数 5 在 O 中有多少个记号？'), ans: '1', why: bi('Finite ordinals have exactly one notation: 1, 2, 4, 16, 65536, 2<sup>65536</sup> for 0,…,5.', '有限序数恰有一个记号：0,…,5 分别是 1, 2, 4, 16, 65536, 2<sup>65536</sup>。') },
    { type: 'ch', q: bi('(c) |a|<sub>O</sub> = ω+1 and φ<sub>e</sub>(n) = the (n+1)-th successor of a. Then |3·5<sup>e</sup>|<sub>O</sub> =', '(c) |a|<sub>O</sub> = ω+1，φ<sub>e</sub>(n) = a 的第 n+1 个后继。则 |3·5<sup>e</sup>|<sub>O</sub> ='),
      opts: ['ω·2', 'ω+ω+1', 'ω+1', 'ω²'], ans: 0, why: bi('sup<sub>n</sub> (ω+1+n+1) = ω+ω = ω·2.', 'sup<sub>n</sub> (ω+1+n+1) = ω+ω = ω·2。') },
    { type: 'ch', q: bi('(d) 3·5<sup>e₁</sup> ≠ 3·5<sup>e₂</sup> are both notations for ω, with φ<sub>e₁</sub>, φ<sub>e₂</sub> listing finite notations. Under &lt;<sub>O</sub> they are', '(d) 3·5<sup>e₁</sup> ≠ 3·5<sup>e₂</sup> 都是 ω 的记号，φ<sub>e₁</sub>、φ<sub>e₂</sub> 列出的都是有限记号。它们在 &lt;<sub>O</sub> 下'),
      opts: [bil('equal', '相等'), bil('comparable', '可比较'), bil('incomparable', '不可比较')], ans: 2, why: bi('The &lt;<sub>O</sub>-predecessors of each are only finite notations, so neither lies below the other.', '二者的 &lt;<sub>O</sub>-前驱都只有有限记号，所以谁也不在谁下面。') },
    { type: 'ch', q: bi('(e) φ<sub>e</sub>(n) = 1 for all n (total!). Is 3·5<sup>e</sup> ∈ O?', '(e) 对所有 n，φ<sub>e</sub>(n) = 1（全定义！）。3·5<sup>e</sup> ∈ O 吗？'),
      opts: [bil('Yes, a notation for 0', '是，是 0 的记号'), bil('Yes, a notation for ω', '是，是 ω 的记号'), bil('No', '不是')], ans: 2, why: bi('The limit rule needs φ<sub>e</sub>(0) &lt;<sub>O</sub> φ<sub>e</sub>(1) &lt;<sub>O</sub> ⋯; a constant sequence is not increasing, and no other rule produces numbers of the form 3·5<sup>e</sup>.', '极限规则要求 φ<sub>e</sub>(0) &lt;<sub>O</sub> φ<sub>e</sub>(1) &lt;<sub>O</sub> ⋯；常值序列不递增，而其他规则不会产生 3·5<sup>e</sup> 形式的数。') },
  ];
  const solved = qs.map(() => false);
  let revealed = false;
  const fin = () => { if (!revealed && solved.every(Boolean)) Progress.mark('L18E5'); };
  qs.forEach((q, i) => {
    const row = document.createElement('div');
    row.className = 'tf';
    row.innerHTML = `<div class="stmt" style="font-family:var(--sans);font-size:15px">${q.q}</div><div class="ctl"></div><div style="flex-basis:100%"><div class="msg"></div></div>`;
    const ctl = row.querySelector('.ctl'), msg = row.querySelector('.msg');
    q.msg = msg;
    if (q.type === 'num') {
      ctl.innerHTML = `<input class="formula" style="min-width:80px;width:90px"> <button class="btn small">${bil('Check', '检查')}</button>`;
      const inp = ctl.querySelector('input');
      q.inp = inp;
      ctl.querySelector('button').addEventListener('click', () => {
        if (inp.value.trim() === q.ans) { okBox(msg, '✓ ' + q.why); solved[i] = true; fin(); }
        else okBox(msg, bi('✗ Try again.', '✗ 再试试。'), 'bad');
      });
    } else {
      q.btns = q.opts.map((o, j) => {
        const b = document.createElement('button');
        b.className = 'btn small'; b.innerHTML = o;
        b.addEventListener('click', () => {
          q.btns.forEach(x => x.classList.remove('right', 'wrongc'));
          if (j === q.ans) { b.classList.add('right'); okBox(msg, '✓ ' + q.why); solved[i] = true; fin(); }
          else { b.classList.add('wrongc'); okBox(msg, bi('✗ Not quite.', '✗ 不对。'), 'bad'); }
        });
        ctl.appendChild(b);
        return b;
      });
    }
    $('e5List').appendChild(row);
  });
  $('e5Show').addEventListener('click', () => {
    revealed = true;
    qs.forEach(q => {
      if (q.type === 'num') q.inp.value = q.ans; else q.btns[q.ans].classList.add('right');
      okBox(q.msg, q.why, 'info');
    });
  });
})();

/* ================= E6 ================= */
tfList($('e6List'), [
  { ans: true, en: 'Every A ⊆ ω is boldface Δ⁰₁.', zh: '每个 A ⊆ ω 都是粗体 Δ⁰₁ 的。', wen: 'A is Δ⁰₁(A): use A itself as the parameter. Boldface is only interesting for sets of reals.', wzh: 'A 是 Δ⁰₁(A) 的：把 A 本身当参数。粗体只对实数集合有意义。' },
  { ans: false, en: 'The lightface Δ¹₁ subsets of ω<sup>ω</sup> are exactly the Borel sets.', zh: 'ω<sup>ω</sup> 的细体 Δ¹₁ 子集恰好是博雷尔集。', wen: 'Boldface Δ¹₁ = Borel (Suslin). Lightface Δ¹₁ sets are the countably many effectively Borel sets.', wzh: '粗体 Δ¹₁ = 博雷尔（Suslin）。细体 Δ¹₁ 集是可数多个能行博雷尔集。' },
  { ans: false, en: 'Every nonempty lightface Σ¹₁ set of reals has a hyperarithmetic member.', zh: '每个非空的细体 Σ¹₁ 实数集都有超算术元素。', wen: 'Kleene: even a nonempty Π⁰₁ set (the branches of a recursive tree) can have no HYP member.', wzh: '克莱尼：甚至存在非空的 Π⁰₁ 集（某棵递归树的分支集）没有超算术元素。' },
  { ans: true, en: 'Every nonempty lightface Σ¹₁ set of reals has a member recursive in O.', zh: '每个非空的细体 Σ¹₁ 实数集都有一个递归于 O 的元素。', wen: 'Kleene basis theorem: follow the leftmost branch of the tree, asking O which subtrees are ill-founded.', wzh: '克莱尼基定理：沿树的最左分支走，每一步问 O 哪棵子树非良基。' },
  { ans: true, en: 'ZFC proves: every Π¹₂ sentence true in V is true in L.', zh: 'ZFC 可证：在 V 中为真的 Π¹₂ 语句在 L 中也为真。', wen: 'Shoenfield absoluteness (L is an inner model of ZF + DC).', wzh: 'Shoenfield 绝对性（L 是 ZF + DC 的内模型）。' },
  { ans: false, en: 'ZFC proves: every Σ¹₃ sentence true in V is true in L (assume ZFC is consistent).', zh: 'ZFC 可证：在 V 中为真的 Σ¹₃ 语句在 L 中也为真（假设 ZFC 一致）。', wen: '∃x (x ∉ L) is Σ¹₃; it holds after adding a Cohen real but fails in L.', wzh: '∃x (x ∉ L) 是 Σ¹₃ 的；添加 Cohen 实数后它成立，但在 L 中不成立。' },
  { ans: false, en: 'By Shoenfield, ZFC decides every Σ¹₂ sentence.', zh: '由 Shoenfield 定理，ZFC 能判定每个 Σ¹₂ 语句。', wen: 'Absoluteness is not decidability: Con(ZFC) is Π⁰₁, absolute, and undecided by ZFC (if consistent).', wzh: '绝对性不是可判定性：Con(ZFC) 是 Π⁰₁ 的，是绝对的，但（若 ZFC 一致）ZFC 判定不了它。' },
], 'L18E6');
}
