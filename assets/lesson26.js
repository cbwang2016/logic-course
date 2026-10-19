// Lesson 26 interactions: the big picture.
Lang.init();
Progress.paint();

const $ = id => document.getElementById(id);
const okBox = (box, html, kind = 'ok') => { box.className = 'msg ' + kind; box.innerHTML = html; };
const clearBox = box => { box.className = 'msg'; box.innerHTML = ''; };
const ST_LABEL = {
  thm: ['theorem', '定理'], ind: ['independent', '独立'], open: ['open', '未解决'],
  phil: ['position', '哲学立场'], hist: ['history', '史实'], prog: ['program', '研究纲领'],
};
const status = (k, extra) => {
  const [en, zh] = ST_LABEL[k];
  const cls = k === 'prog' ? 'st-open' : 'st-' + k;
  return `<span class="status ${cls}">${bi(en + (extra ? ' · ' + extra[0] : ''), zh + (extra ? ' · ' + extra[1] : ''))}</span>`;
};
const lessonChips = ls => (ls || []).map(n => `<a class="chip" href="lesson${n}.html">L${n}</a>`).join('');
const txt = (parent, attrs, s) => { const t = el('text', attrs, parent); t.textContent = s; return t; };
const shuffle = a => { for (let i = a.length - 1; i > 0; i--) { const j = Math.floor(Math.random() * (i + 1)); [a[i], a[j]] = [a[j], a[i]]; } return a; };

/* ================= check-yourself ================= */
const CY = {
  cy1: { q: ['Hilbert\'s 2nd problem asked for a proof that the axioms of arithmetic are consistent. Which two results reshaped that goal?', '希尔伯特第 2 问题要求证明算术公理的一致性。哪两个结果重塑了这一目标？'],
    o: [['Gödel 1931 and Gentzen 1936', '哥德尔 1931 与根岑 1936', 1], ['Cohen 1963 and Martin 1975', '科恩 1963 与马丁 1975', 0], ['Cantor 1891 and Russell 1901', '康托尔 1891 与罗素 1901', 0]],
    e: ['Gödel\'s second theorem (1931): a consistent, effectively axiomatized theory with enough arithmetic cannot prove its own consistency, so a finitary proof <i>inside</i> such a system is impossible. Gentzen (1936) proved Con(PA) anyway, using finitary reasoning plus transfinite induction up to ε₀, which goes beyond PA.',
      '哥德尔第二不完全性定理（1931）：一致、能行公理化且包含足够算术的理论不能证明自身的一致性，因此在这样的系统<i>内部</i>给出有穷证明是不可能的。根岑（1936）还是证明了 Con(PA)，用的是有穷推理加上直到 ε₀ 的超限归纳，而这超出了 PA 的范围。'] },
  cy2: { q: ['What did Russell\'s paradox actually show?', '罗素悖论究竟说明了什么？'],
    o: [['All of mathematics is inconsistent', '整个数学是矛盾的', 0], ['Unrestricted comprehension (e.g. Frege\'s Basic Law V) is inconsistent', '不加限制的概括原则（如弗雷格的第五基本定律）是矛盾的', 1], ['Infinite sets do not exist', '无穷集合不存在', 0]],
    e: ['The set R = {x : x ∉ x} cannot exist. Any system that lets every property define a set is inconsistent. ZF replaces this with Separation: you may only carve subsets out of an existing set.',
      '集合 R = {x : x ∉ x} 不可能存在。任何允许每个性质都定义一个集合的系统都是矛盾的。ZF 用分离公理取而代之：只能从已有集合中划分出子集。'] },
  cy3: { q: ['Which theorem is the bridge between proof theory (⊢) and model theory (⊨)?', '哪个定理是证明论（⊢）与模型论（⊨）之间的桥梁？'],
    o: [['Gödel\'s completeness theorem', '哥德尔完备性定理', 1], ['The MRDP theorem', 'MRDP 定理', 0], ['Borel determinacy', '博雷尔决定性', 0]],
    e: ['Completeness (Gödel 1929/30): T ⊢ φ ⇔ T ⊨ φ for first-order logic. MRDP connects computability with number theory; Borel determinacy lives in descriptive set theory.',
      '完备性定理（哥德尔 1929/30）：在一阶逻辑中 T ⊢ φ ⇔ T ⊨ φ。MRDP 连接可计算性与数论；博雷尔决定性属于描述集合论。'] },
  cy4: { q: ['In the halting-problem instance, what is the “flipped diagonal”?', '在停机问题的实例中，“翻转后的对角线”是什么？'],
    o: [['A program D that, on input n, halts iff Pₙ does not halt on n', '程序 D：输入 n 时，D 停机当且仅当 Pₙ 在 n 上不停机', 1], ['A program that halts on every input', '在所有输入上都停机的程序', 0], ['The list of all halting programs', '所有停机程序的列表', 0]],
    e: ['If halting were decidable, D would be a program, so D = Pₖ for some k. Then D halts on k iff Pₖ = D does not halt on k: contradiction.',
      '若停机问题可判定，D 就是一个程序，于是对某个 k 有 D = Pₖ。那么 D 在 k 上停机当且仅当 Pₖ = D 在 k 上不停机：矛盾。'] },
  cy5: { q: ['Let G be a Gödel sentence for PA. Which is correct?', '设 G 是 PA 的哥德尔语句。下列哪项正确？'],
    o: [['PA ⊨ G but PA ⊬ G, refuting completeness', 'PA ⊨ G 但 PA ⊬ G，完备性定理被推翻', 0], ['G is true in ℕ but false in some model of PA, so PA ⊭ G and PA ⊬ G', 'G 在 ℕ 中为真，但在 PA 的某个模型中为假，所以 PA ⊭ G 且 PA ⊬ G', 1], ['G is false in ℕ', 'G 在 ℕ 中为假', 0]],
    e: ['Since PA ⊬ G, by completeness PA ⊭ G: some (nonstandard) model of PA makes G false. Yet G is true in the standard model ℕ (assuming PA is consistent). No contradiction.',
      '由于 PA ⊬ G，由完备性定理得 PA ⊭ G：PA 的某个（非标准）模型使 G 为假。但 G 在标准模型 ℕ 中为真（假定 PA 一致）。并无矛盾。'] },
  cy6: { q: ['Post\'s theorem links which two ladders?', '波斯特定理连接哪两架阶梯？'],
    o: [['The arithmetical hierarchy and iterated Turing jumps', '算术层级与迭代的图灵跳跃', 1], ['The Lévy hierarchy and large cardinals', '列维层级与大基数', 0], ['Proof-theoretic ordinals and Borel classes', '证明论序数与博雷尔类', 0]],
    e: ['Post: a set is Σ⁰ₙ₊₁ iff it is computably enumerable relative to 0⁽ⁿ⁾, the n-th Turing jump of ∅.',
      '波斯特定理：一个集合是 Σ⁰ₙ₊₁ 的，当且仅当它相对于 0⁽ⁿ⁾（∅ 的第 n 次图灵跳跃）可计算枚举。'] },
  cy7: { q: ['Goodstein\'s theorem is independent of PA (Kirby–Paris 1982). What follows?', '古德斯坦定理独立于 PA（Kirby–Paris 1982）。由此可得什么？'],
    o: [['It has no truth value', '它没有真值', 0], ['It is true in ℕ and provable in ZFC', '它在 ℕ 中为真，且在 ZFC 中可证', 1], ['It is false', '它是假的', 0]],
    e: ['Goodstein\'s theorem is proved in ZFC (indeed with induction up to ε₀). Independence from PA only says PA is too weak.',
      '古德斯坦定理可在 ZFC 中证明（实际上只需直到 ε₀ 的归纳）。独立于 PA 只说明 PA 太弱。'] },
  cy8: { q: ['Which result used o-minimality as a key tool?', '哪个结果以 o-极小性为关键工具？'],
    o: [['Pila\'s proof of André–Oort for products of modular curves', '皮拉对模曲线乘积证明安德烈–奥尔特猜想', 1], ['The MRDP theorem', 'MRDP 定理', 0], ['Shelah\'s Whitehead independence', '谢拉赫关于怀特海问题的独立性', 0]],
    e: ['Pila (Annals 2011) used the Pila–Wilkie counting theorem for sets definable in the o-minimal structure ℝ_an,exp, following the Pila–Zannier strategy.',
      '皮拉（Annals 2011）沿用皮拉–扎尼尔策略，使用了针对 o-极小结构 ℝ_an,exp 中可定义集的皮拉–威尔基计数定理。'] },
  cy9: { q: ['Which position rejects the law of excluded middle as a general principle?', '哪种立场拒绝把排中律作为普遍原则？'],
    o: [['Intuitionism / constructivism', '直觉主义／构造主义', 1], ['Platonism', '柏拉图主义', 0], ['The multiverse view', '多重宇宙观', 0]],
    e: ['Intuitionists (Brouwer, Heyting) and constructivists (Bishop) accept P ∨ ¬P only when one can decide which disjunct holds.',
      '直觉主义者（布劳威尔、海廷）与构造主义者（毕晓普）只在能判定哪一支成立时才接受 P ∨ ¬P。'] },
  cy10: { q: ['What does the univalence axiom say?', '泛等公理（univalence）说的是什么？'],
    o: [['Equivalent types are equal: (A = B) ≃ (A ≃ B)', '等价的类型相等：(A = B) ≃ (A ≃ B)', 1], ['Every type has exactly one element', '每个类型恰有一个元素', 0], ['The law of excluded middle holds for all types', '排中律对所有类型成立', 0]],
    e: ['Univalence (Voevodsky) says the canonical map from identities A = B to equivalences A ≃ B is itself an equivalence. So anything provable about A transfers to any equivalent B.',
      '泛等公理（沃沃茨基）说：从恒等 A = B 到等价 A ≃ B 的典范映射本身是一个等价。于是关于 A 能证明的东西都能转移到与之等价的 B 上。'] },
  cy11: { q: ['Martin\'s conjecture is…', '马丁猜想是……'],
    o: [['a theorem of ZFC', 'ZFC 的一个定理', 0], ['an open problem about Turing-invariant functions (under AD)', '关于图灵不变函数（在 AD 下）的未解决问题', 1], ['a philosophical position', '一种哲学立场', 0]],
    e: ['Martin\'s conjecture (1970s) predicts, under AD, that Turing-invariant functions on the reals are classified by iterates of the jump. Special cases are proved; the full conjecture is open (L28).',
      '马丁猜想（1970 年代）预言：在 AD 下，实数上的图灵不变函数可以用图灵跳跃的迭代来分类。部分特例已被证明，完整猜想仍未解决（见第 28 课）。'] },
};
function buildCY(id) {
  const box = $(id), d = CY[id];
  if (!box || !d) return;
  box.innerHTML = `<div class="q">✎ ${bi('Check yourself: ' + d.q[0], '自测：' + d.q[1])}</div><div class="opts"></div><div class="msg"></div>`;
  const opts = box.querySelector('.opts'), msg = box.querySelector('.msg');
  const btns = d.o.map(o => {
    const b = document.createElement('button');
    b.className = 'btn small';
    b.innerHTML = bil(o[0], o[1]);
    b.addEventListener('click', () => {
      btns.forEach(x => x.classList.remove('right', 'wrongc'));
      b.classList.add(o[2] ? 'right' : 'wrongc');
      okBox(msg, (o[2] ? '✓ ' : '✗ ') + bi(d.e[0], d.e[1]), o[2] ? 'ok' : 'bad');
    });
    opts.appendChild(b);
    return b;
  });
  const sh = document.createElement('button');
  sh.className = 'btn small ghost';
  sh.innerHTML = bil('Show answer', '显示答案');
  sh.addEventListener('click', () => {
    btns.forEach((x, i) => x.classList.toggle('right', !!d.o[i][2]));
    okBox(msg, bi(d.e[0], d.e[1]), 'info');
  });
  opts.appendChild(sh);
}
Object.keys(CY).forEach(buildCY);

/* ================= §1 timeline ================= */
const LANES = [
  { k: 'ST', en: 'Set theory', zh: '集合论', c: '#2f9e44' },
  { k: 'MT', en: 'Model theory', zh: '模型论', c: '#3b5bdb' },
  { k: 'CT', en: 'Computability', zh: '可计算性', c: '#f08c00' },
  { k: 'PT', en: 'Proof theory', zh: '证明论', c: '#ae3ec9' },
  { k: 'FD', en: 'Foundations & philosophy', zh: '基础与哲学', c: '#0c8599' },
];
const EVENTS = [
  { y: 1874, l: 'ST', s: 'thm', d: '1874', t: ['Cantor: ℝ is uncountable', '康托尔：ℝ 不可数'],
    why: ['Cantor\'s work on trigonometric series led him to study infinite point sets, and to ask whether all infinite sets have the same size.', '康托尔对三角级数的研究使他开始研究无穷点集，并追问：所有无穷集合是否一样大？'],
    res: ['There is no bijection between ℕ and ℝ (while the algebraic numbers are countable). Infinities come in different sizes.', 'ℕ 与 ℝ 之间不存在双射（而代数数是可数的）。无穷有大小之分。'], ls: [9] },
  { y: 1878, l: 'ST', s: 'hist', d: '1878', t: ['Cantor formulates the Continuum Hypothesis', '康托尔提出连续统假设'],
    why: ['Having found two infinite sizes (ℕ and ℝ), the natural question is whether anything lies strictly between them.', '既然找到了两种无穷的大小（ℕ 与 ℝ），自然要问：两者之间是否还有别的大小？'],
    res: ['CH: every infinite set of reals is countable or has the size of ℝ. Cantor never proved it; it became Hilbert\'s 1st problem.', 'CH：每个无穷实数集要么可数，要么与 ℝ 等势。康托尔始终没能证明它；它后来成了希尔伯特第 1 问题。'], ls: [9, 16, 27] },
  { y: 1879, l: 'FD', s: 'hist', d: '1879', t: ['Frege\'s Begriffsschrift', '弗雷格《概念文字》'],
    why: ['Frege wanted to show that arithmetic is pure logic (logicism), and needed a gap-free language in which every step of a proof is explicit.', '弗雷格想证明算术就是纯逻辑（逻辑主义），为此需要一种无漏洞的语言，让证明的每一步都明明白白。'],
    res: ['The first modern logic of quantifiers (∀, ∃, nested quantifiers, relations): the ancestor of first-order logic.', '第一个现代量词逻辑（∀、∃、嵌套量词、关系），是一阶逻辑的前身。'], ls: [3] },
  { y: 1888, l: 'FD', s: 'hist', d: '1888–89', t: ['Dedekind and Peano axiomatize ℕ', '戴德金与皮亚诺将 ℕ 公理化'],
    why: ['What exactly are the natural numbers, and why is proof by induction valid?', '自然数究竟是什么？数学归纳法为什么成立？'],
    res: ['Dedekind (1888) characterizes ℕ up to isomorphism (a second-order characterization); Peano (1889) states the axioms in symbolic form.', '戴德金（1888）在同构意义下刻画了 ℕ（二阶刻画）；皮亚诺（1889）用符号形式写出了公理。'], ls: [7, 12] },
  { y: 1891, l: 'ST', s: 'thm', d: '1891', t: ['Cantor\'s diagonal method', '康托尔对角线方法'],
    why: ['Find a simpler and more general proof that some infinities are bigger than others.', '为“有的无穷比别的无穷大”找一个更简单、更一般的证明。'],
    res: ['For every set X, |X| < |P(X)|. The same pattern later powers Russell, Gödel, Turing and Tarski (§4).', '对每个集合 X 都有 |X| < |P(X)|。同一模式后来驱动了罗素、哥德尔、图灵和塔斯基的论证（见 §4）。'], ls: [1, 9] },
  { y: 1897, l: 'ST', s: 'hist', d: '1897', t: ['Burali-Forti\'s argument on ordinals', '布拉利–福尔蒂关于序数的论证'],
    why: ['Burali-Forti was studying how well-ordered types compare.', '布拉利–福尔蒂当时在研究良序型之间的比较。'],
    res: ['As later understood: the collection of all ordinals cannot be a set, since it would be well-ordered with an order type larger than every ordinal. Cantor (letters of 1897–99) already distinguished such “inconsistent multiplicities”.', '按后来的理解：全体序数不能构成集合，否则它是良序的，其序型将大于每个序数。康托尔（1897–1899 年的书信）已经区分了这种“不一致的总体”。'], ls: [8] },
  { y: 1900, l: 'FD', s: 'hist', d: '1900', t: ['Hilbert\'s problems (Paris ICM)', '希尔伯特问题（巴黎国际数学家大会）'],
    why: ['To set an agenda for 20th-century mathematics; Hilbert believed every well-posed problem has a solution.', '为 20 世纪数学定下议程；希尔伯特相信每个提法恰当的问题都有解。'],
    res: ['10 problems were presented in the talk (August 1900), 23 in print. #1: CH (and a well-ordering of ℝ); #2: consistency of the axioms of arithmetic (Hilbert meant his axioms for the real numbers); #10: an algorithm deciding whether a Diophantine equation has integer solutions.', '演讲中介绍了 10 个（1900 年 8 月），正式发表 23 个。第 1 问题：CH（以及 ℝ 的良序）；第 2 问题：算术公理的一致性（希尔伯特指的是他的实数公理）；第 10 问题：判定丢番图方程是否有整数解的算法。'], ls: [11, 12, 16] },
  { y: 1901, l: 'ST', s: 'thm', d: '1901–02', t: ['Russell\'s paradox', '罗素悖论'],
    why: ['Russell was analysing Cantor\'s proof that there is no largest cardinal, applied to the “set of all sets”.', '罗素在分析康托尔“没有最大基数”的证明，并把它用到“所有集合的集合”上。'],
    res: ['R = {x : x ∉ x} gives R ∈ R ⇔ R ∉ R. Sent to Frege in June 1902; it shows Frege\'s Basic Law V inconsistent. Zermelo found it independently but did not publish.', 'R = {x : x ∉ x} 导致 R ∈ R ⇔ R ∉ R。1902 年 6 月罗素写信告诉弗雷格；它表明弗雷格的第五基本定律是矛盾的。策梅洛曾独立发现它，但没有发表。'], ls: [6] },
  { y: 1904, l: 'ST', s: 'thm', d: '1904', t: ['Zermelo: well-ordering theorem from AC', '策梅洛：由选择公理证明良序定理'],
    why: ['Hilbert\'s 1st problem asked for a well-ordering of ℝ; Cantor believed every set can be well-ordered.', '希尔伯特第 1 问题要求给出 ℝ 的良序；康托尔相信每个集合都能良序化。'],
    res: ['Every set can be well-ordered, assuming the axiom of choice. The proof was sharply criticized (Borel, Baire, Lebesgue, Peano and others), which pushed Zermelo to state his assumptions as axioms.', '在选择公理下，每个集合都能良序化。这个证明遭到激烈批评（博雷尔、贝尔、勒贝格、皮亚诺等人），促使策梅洛把他的假设明确写成公理。'], ls: [10] },
  { y: 1908, l: 'ST', s: 'hist', d: '1908', t: ['Zermelo\'s axioms; Russell\'s type theory', '策梅洛公理；罗素类型论'],
    why: ['Defend the well-ordering proof and block the paradoxes by restricting how sets may be formed.', '为良序定理的证明辩护，并通过限制集合的构造方式来堵住悖论。'],
    res: ['Zermelo\'s set theory Z (Separation replaces unrestricted comprehension). The same year Russell published his ramified theory of types, the basis of Principia Mathematica (1910–13).', '策梅洛集合论 Z（用分离公理代替不受限制的概括原则）。同年罗素发表分支类型论，它是《数学原理》（1910–1913）的基础。'], ls: [6] },
  { y: 1915, l: 'MT', s: 'thm', d: '1915/1920', t: ['Löwenheim–Skolem theorem', '勒文海姆–斯科伦定理'],
    why: ['How large must a model of a first-order sentence (or theory) be?', '一阶语句（或理论）的模型必须有多大？'],
    res: ['A satisfiable countable first-order theory has a countable model (Löwenheim 1915, Skolem 1920). Skolem (1922) noted the “paradox”: ZF, if consistent, has a countable model even though it proves uncountable sets exist.', '可满足的可数一阶理论有可数模型（勒文海姆 1915，斯科伦 1920）。斯科伦（1922）指出了“悖论”：ZF 若一致则有可数模型，尽管它能证明存在不可数集合。'], ls: [5] },
  { y: 1921, l: 'FD', s: 'hist', d: '1920–22', t: ['The foundational debate (Grundlagenstreit)', '基础之争（Grundlagenstreit）'],
    why: ['Brouwer argued that applying excluded middle to infinite totalities is unjustified; Weyl\'s 1921 paper “On the new foundational crisis” supported him.', '布劳威尔认为把排中律用于无穷总体是没有根据的；外尔 1921 年的论文《论数学的新基础危机》支持了他。'],
    res: ['A public debate, mainly Hilbert vs Brouwer, through the 1920s. Hilbert\'s reply (1922) launched his program.', '一场公开论战，主要是希尔伯特对布劳威尔，持续整个 1920 年代。希尔伯特的回应（1922）开启了他的纲领。'], ls: [1] },
  { y: 1922, l: 'ST', s: 'hist', d: '1922', t: ['Fraenkel and Skolem: Replacement → ZF', '弗兰克尔与斯科伦：替换公理 → ZF'],
    why: ['Zermelo\'s Z cannot prove that sets like {ω, P(ω), P(P(ω)), …} exist, and his notion of “definite property” was vague.', '策梅洛的 Z 无法证明 {ω, P(ω), P(P(ω)), …} 这类集合存在，而且他的“确定性质”概念含糊。'],
    res: ['Replacement is added; Skolem proposes reading “definite property” as “first-order formula”. With Foundation (von Neumann 1925, Zermelo 1930) this becomes ZF; with choice, ZFC.', '加入替换公理；斯科伦建议把“确定性质”理解为“一阶公式”。再加上基础公理（冯·诺伊曼 1925，策梅洛 1930），就成了 ZF；加上选择公理即 ZFC。'], ls: [6, 8] },
  { y: 1924, l: 'PT', s: 'hist', d: '1921–28', t: ['Hilbert\'s program', '希尔伯特纲领'],
    why: ['Answer Brouwer and Weyl: keep classical mathematics, but formalize it and prove it consistent by finitary means.', '回应布劳威尔和外尔：保留经典数学，但把它形式化，并用有穷方法证明其一致性。'],
    res: ['Metamathematics is born (with Bernays, Ackermann, von Neumann). In 1928 Hilbert and Ackermann pose the Entscheidungsproblem and ask about completeness of first-order logic.', '元数学由此诞生（贝尔奈斯、阿克曼、冯·诺伊曼参与其中）。1928 年希尔伯特与阿克曼提出判定问题，并追问一阶逻辑的完备性。'], ls: [12] },
  { y: 1930, l: 'MT', s: 'thm', d: '1929/30', t: ['Gödel\'s completeness theorem', '哥德尔完备性定理'],
    why: ['Hilbert and Ackermann (1928) asked whether their first-order calculus proves every valid formula.', '希尔伯特与阿克曼（1928）问：他们的一阶演算能否证明每个普遍有效的公式？'],
    res: ['Yes: a first-order sentence is provable iff it is true in every model (dissertation 1929, published 1930). Compactness follows.', '能：一阶语句可证当且仅当它在所有模型中为真（1929 年博士论文，1930 年发表）。紧致性定理随之得到。'], ls: [4, 5] },
  { y: 1931, l: 'PT', s: 'thm', d: '1931', t: ['Gödel\'s incompleteness theorems', '哥德尔不完全性定理'],
    why: ['Part of Hilbert\'s program: show that formal arithmetic is complete and consistent.', '希尔伯特纲领的一部分：证明形式算术是完全的、一致的。'],
    res: ['A consistent, effectively axiomatized theory containing enough arithmetic is incomplete (1st theorem) and cannot prove its own consistency (2nd theorem). Announced September 1930, published 1931.', '一致、能行公理化且包含足够算术的理论是不完全的（第一定理），并且不能证明自身的一致性（第二定理）。1930 年 9 月宣布，1931 年发表。'], ls: [12] },
  { y: 1933, l: 'MT', s: 'thm', d: '1933', t: ['Tarski: the concept of truth', '塔斯基：真的概念'],
    why: ['Give a precise, paradox-free definition of “true sentence” for a formal language.', '为形式语言中的“真语句”给出精确且不导致悖论的定义。'],
    res: ['Truth can be defined in a stronger metalanguage, but arithmetic truth is not definable in arithmetic itself (undefinability of truth). Polish 1933, German 1935.', '真可以在更强的元语言中定义，但算术真不能在算术内部定义（真的不可定义性）。波兰文版 1933，德文版 1935。'], ls: [13] },
  { y: 1936, l: 'CT', s: 'thm', d: '1936', t: ['Church and Turing: the Entscheidungsproblem', '丘奇与图灵：判定问题'],
    why: ['Is there an algorithm that decides whether a first-order formula is valid?', '是否存在判定一阶公式是否普遍有效的算法？'],
    res: ['No. Church (λ-calculus) and Turing (machines) define computability; the halting problem is undecidable; first-order validity is undecidable. (Church–Turing thesis.)', '不存在。丘奇（λ 演算）与图灵（图灵机）定义了可计算性；停机问题不可判定；一阶有效性不可判定。（丘奇–图灵论题。）'], ls: [11] },
  { y: 1936.01, l: 'PT', s: 'thm', d: '1936', t: ['Gentzen: consistency of PA', '根岑：PA 的一致性'],
    why: ['Save as much of Hilbert\'s program as possible after Gödel.', '在哥德尔之后，尽可能挽救希尔伯特纲领。'],
    res: ['Con(PA) is proved by finitary means plus (quantifier-free) transfinite induction up to ε₀. The start of ordinal analysis.', '用有穷方法加上直到 ε₀ 的（无量词）超限归纳证明了 Con(PA)。序数分析由此开端。'], ls: [21] },
  { y: 1938, l: 'ST', s: 'thm', d: '1938/40', t: ['Gödel: the constructible universe L', '哥德尔：可构成宇宙 L'],
    why: ['Hilbert\'s 1st problem: can CH (and AC) at least never be refuted?', '希尔伯特第 1 问题：CH（以及 AC）至少是不可驳倒的吗？'],
    res: ['If ZF is consistent, so is ZFC + GCH (announced 1938, monograph 1940). L is the smallest inner model.', '若 ZF 一致，则 ZFC + GCH 也一致（1938 年宣布，1940 年出版专著）。L 是最小的内模型。'], ls: [15] },
  { y: 1956, l: 'CT', s: 'thm', d: '1956–57', t: ['Friedberg–Muchnik: Post\'s problem', '弗里德伯格–穆奇尼克：波斯特问题'],
    why: ['Post (1944) asked whether every undecidable c.e. set is as hard as the halting problem.', '波斯特（1944）问：每个不可判定的可计算枚举集是否都与停机问题一样难？'],
    res: ['No: there are c.e. degrees strictly between 0 and 0′. Found independently; they introduced the priority method.', '不是：存在严格介于 0 与 0′ 之间的可计算枚举度。两人独立得到，并创立了优先方法。'], ls: [17] },
  { y: 1963, l: 'ST', s: 'ind', d: '1963', t: ['Cohen: forcing; CH is independent', '科恩：力迫法；CH 独立'],
    why: ['Hilbert\'s 1st problem again: can ZFC prove CH? Can ZF prove AC?', '再次面对希尔伯特第 1 问题：ZFC 能证明 CH 吗？ZF 能证明 AC 吗？'],
    res: ['No: if ZF is consistent, so are ZF + ¬AC and ZFC + ¬CH. With Gödel 1938, CH is independent of ZFC. Forcing becomes the main tool for independence proofs.', '不能：若 ZF 一致，则 ZF + ¬AC 和 ZFC + ¬CH 也一致。结合哥德尔 1938，CH 独立于 ZFC。力迫法成为证明独立性的主要工具。'], ls: [16] },
  { y: 1965, l: 'MT', s: 'thm', d: '1965', t: ['Ax–Kochen (and Ershov); Morley', 'Ax–Kochen（及叶尔绍夫）；莫利'],
    why: ['Artin conjectured that p-adic forms of degree d in more than d² variables have nontrivial zeros. Ultraproducts let one transfer statements between fields.', '阿廷猜想：p 进域上 d 次、变元多于 d² 的型有非平凡零点。超积使得命题可以在不同的域之间转移。'],
    res: ['For each d, the conjecture holds for all but finitely many p (the full conjecture is false: Terjanian 1966). Same year, Morley: a countable theory categorical in one uncountable cardinal is categorical in all.', '对每个 d，猜想对除有限多个 p 以外的所有素数成立（完整猜想是错的：Terjanian 1966）。同年，莫利证明：可数理论若在某个不可数基数上范畴，则在所有不可数基数上范畴。'], ls: [5, 28] },
  { y: 1967, l: 'FD', s: 'hist', d: '1967', t: ['Bishop: Foundations of Constructive Analysis', '毕晓普《构造性分析基础》'],
    why: ['Show that real analysis can be developed with full computational meaning, without Brouwer\'s special principles.', '证明实分析可以在完全保留计算意义的前提下展开，而无需布劳威尔的特殊原则。'],
    res: ['A large body of constructive analysis whose theorems are also classically valid.', '大量构造性分析成果，其定理在经典意义下也都成立。'], ls: [10] },
  { y: 1970, l: 'CT', s: 'thm', d: '1970', t: ['Matiyasevich completes MRDP', '马季亚谢维奇完成 MRDP 定理'],
    why: ['Hilbert\'s 10th problem: find an algorithm deciding solvability of Diophantine equations.', '希尔伯特第 10 问题：找出判定丢番图方程可解性的算法。'],
    res: ['Every c.e. set is Diophantine (Davis, Putnam, Robinson 1961 + Matiyasevich 1970). Hence no such algorithm exists.', '每个可计算枚举集都是丢番图集（戴维斯、普特南、罗宾逊 1961 + 马季亚谢维奇 1970）。因此这样的算法不存在。'], ls: [11] },
  { y: 1974, l: 'PT', s: 'prog', d: '1974', t: ['Friedman: reverse mathematics', '弗里德曼：反推数学'],
    why: ['Which set-existence axioms are actually needed to prove ordinary theorems of analysis and algebra?', '证明分析与代数中的普通定理，究竟需要哪些集合存在公理？'],
    res: ['Program announced at the 1974 ICM (published 1975), developed by Simpson and others: most theorems are equivalent over RCA₀ to one of five systems (the “Big Five”).', '1974 年国际数学家大会上提出（1975 年发表），由辛普森等人发展：大多数定理在 RCA₀ 上等价于五个系统之一（“五大系统”）。'], ls: [18, 28] },
  { y: 1974, l: 'ST', s: 'ind', d: '1974', t: ['Shelah: Whitehead\'s problem is independent', '谢拉赫：怀特海问题独立'],
    why: ['Whitehead\'s problem from algebra: is every abelian group A with Ext(A, ℤ) = 0 free?', '来自代数的怀特海问题：每个满足 Ext(A, ℤ) = 0 的阿贝尔群 A 都是自由的吗？'],
    res: ['Independent of ZFC: V = L implies yes; MA + ¬CH implies no. The first major independence result in mainstream algebra.', '独立于 ZFC：V = L 推出“是”；MA + ¬CH 推出“否”。这是主流代数中第一个重大独立性结果。'], ls: [15, 16] },
  { y: 1975, l: 'ST', s: 'thm', d: '1975', t: ['Martin: Borel determinacy', '马丁：博雷尔决定性'],
    why: ['Which infinite games are determined? Friedman (1971) had shown any proof must use many iterations of the power set.', '哪些无穷博弈是决定的？弗里德曼（1971）已经证明任何证明都必须大量迭代使用幂集。'],
    res: ['ZFC proves that every Borel game on ω is determined.', 'ZFC 可以证明：ω 上的每个博雷尔博弈都是决定的。'], ls: [19, 25] },
  { y: 1977, l: 'PT', s: 'ind', d: '1977', t: ['Paris–Harrington theorem', '巴黎–哈灵顿定理'],
    why: ['Gödel sentences look artificial. Is there a natural combinatorial statement independent of PA?', '哥德尔语句看起来很人为。是否存在独立于 PA 的自然组合命题？'],
    res: ['A strengthened finite Ramsey theorem is true (provable in ZFC) but unprovable in PA.', '一个加强版的有限拉姆齐定理为真（可在 ZFC 中证明），但在 PA 中不可证。'], ls: [12, 28] },
  { y: 1978, l: 'MT', s: 'prog', d: '1970s–', t: ['Shelah: classification theory', '谢拉赫：分类理论'],
    why: ['Morley\'s question: how many models can a countable theory have in each uncountable cardinality?', '莫利的问题：一个可数理论在各个不可数基数上能有多少个模型？'],
    res: ['Stability theory and its dividing lines (book “Classification Theory”, 1978; the Main Gap in the 1980s). This became the toolkit of modern model theory.', '稳定性理论及其分界线（专著《分类理论》，1978；1980 年代证明“主间隙”定理）。它成为现代模型论的工具箱。'], ls: [28] },
  { y: 1985, l: 'ST', s: 'thm', d: '1985–89', t: ['Woodin; Martin–Steel: PD from Woodin cardinals', '伍丁；马丁–斯蒂尔：由伍丁基数得 PD'],
    why: ['Projective determinacy (PD) settles the classical questions about projective sets left open by ZFC. Which large cardinals prove it?', '投影决定性（PD）能解决 ZFC 留下的关于投影集的经典问题。哪些大基数能证明它？'],
    res: ['Martin–Steel (proved 1985, published 1989): infinitely many Woodin cardinals imply PD. Woodin: with a measurable above them, AD holds in L(ℝ).', '马丁–斯蒂尔（1985 年证明，1989 年发表）：无穷多个伍丁基数推出 PD。伍丁：若其上还有一个可测基数，则 AD 在 L(ℝ) 中成立。'], ls: [25] },
  { y: 1996, l: 'MT', s: 'thm', d: '1996', t: ['Hrushovski: Mordell–Lang for function fields', '赫鲁晓夫斯基：函数域上的莫德尔–朗猜想'],
    why: ['The Mordell–Lang conjecture for function fields, including positive characteristic, was open.', '函数域上（包括正特征情形）的莫德尔–朗猜想当时悬而未决。'],
    res: ['Proved in all characteristics using geometric stability theory: model theory solving a problem in Diophantine geometry.', '利用几何稳定性理论在所有特征下证明：模型论解决了丢番图几何中的问题。'], ls: [28] },
  { y: 2006, l: 'MT', s: 'thm', d: '2006–', t: ['Pila–Wilkie; André–Oort', '皮拉–威尔基；安德烈–奥尔特'],
    why: ['How many rational points can a set definable in an o-minimal structure have?', '在 o-极小结构中可定义的集合能有多少个有理点？'],
    res: ['Pila–Wilkie (2006): few rational points on the transcendental part. Pila (Annals 2011): André–Oort for products of modular curves. Full André–Oort: Pila–Shankar–Tsimerman (arXiv preprint 2021, substantially revised 2024; appendix by Esnault–Groechenig), completing a strategy that also relies on work of Binyamini–Schmidt–Yafaev and others.', '皮拉–威尔基（2006）：超越部分上的有理点很少。皮拉（Annals 2011）：模曲线乘积上的安德烈–奥尔特猜想。完整的安德烈–奥尔特猜想：皮拉–尚卡尔–齐默曼（arXiv 预印本，2021 年发布，2024 年大幅修订；附录由埃斯诺–格勒兴尼希撰写），这一策略还依赖比尼亚米尼–施密特–亚法耶夫等人的工作。'], ls: [28] },
  { y: 2013, l: 'FD', s: 'hist', d: '2013', t: ['The HoTT book (univalent foundations)', 'HoTT 之书（泛等基础）'],
    why: ['Voevodsky wanted a foundation suited to computer verification in which equivalent structures are literally equal.', '沃沃茨基希望有一种适合计算机验证、且等价结构真正相等的基础。'],
    res: ['Homotopy Type Theory: Univalent Foundations of Mathematics, written collaboratively during the 2012–13 IAS special year.', '《同伦类型论：数学的泛等基础》，在 2012–2013 年普林斯顿高等研究院特别年中集体写成。'], ls: [28] },
  { y: 2017, l: 'FD', s: 'hist', d: '2013–', t: ['Lean and mathlib: formalized mathematics', 'Lean 与 mathlib：形式化数学'],
    why: ['Make machine-checked proofs practical for research-level mathematics.', '让机器验证的证明在研究级数学中变得可行。'],
    res: ['Lean (de Moura, 2013); the mathlib library (from 2017); the Liquid Tensor Experiment (2020–22) verified a central theorem of Clausen–Scholze.', 'Lean（德莫拉，2013）；mathlib 库（2017 年起）；“液态张量实验”（2020–2022）验证了克劳森–肖尔策的一个核心定理。'], ls: [28] },
];
(function timeline() {
  const svg = $('tlSvg'), X0 = 150, X1 = 985, Y0 = 1870, Y1 = 2025;
  const xOf = y => X0 + (y - Y0) * (X1 - X0) / (Y1 - Y0);
  const laneY = k => 40 + LANES.findIndex(l => l.k === k) * 46;
  const hidden = new Set();
  const order = EVENTS.map((e, i) => i).sort((a, b) => EVENTS[a].y - EVENTS[b].y);
  let sel = -1, playing = null;
  // jitter close dots in a lane
  const lastX = {};
  order.forEach(i => {
    const e = EVENTS[i], x = xOf(e.y);
    e.dy = (lastX[e.l] !== undefined && x - lastX[e.l] < 15) ? 15 : 0;
    lastX[e.l] = e.dy ? -999 : x;
  });
  const leg = $('tlLegend');
  LANES.forEach(l => {
    const s = document.createElement('span');
    s.innerHTML = `<i style="background:${l.c}"></i>${bil(l.en, l.zh)}`;
    s.addEventListener('click', () => { hidden.has(l.k) ? hidden.delete(l.k) : hidden.add(l.k); s.classList.toggle('off'); draw(); });
    leg.appendChild(s);
  });
  function draw() {
    svg.innerHTML = '';
    const yr = +$('tlSlider').value;
    LANES.forEach(l => {
      const y = laneY(l.k);
      el('line', { x1: X0 - 6, x2: X1, y1: y, y2: y, stroke: hidden.has(l.k) ? '#f3f1ea' : '#e3dfd3', 'stroke-width': 2 }, svg);
      txt(svg, { x: X0 - 12, y: y - 1, 'text-anchor': 'end', 'font-size': 11.5, fill: l.c, 'font-weight': 700, class: 'lbl', opacity: hidden.has(l.k) ? .3 : 1 }, l.k === 'FD' ? 'Foundations' : l.en);
      txt(svg, { x: X0 - 12, y: y + 13, 'text-anchor': 'end', 'font-size': 11, fill: l.c, class: 'lbl', opacity: hidden.has(l.k) ? .3 : 1 }, l.zh);
    });
    const ay = 268;
    el('line', { x1: X0, x2: X1, y1: ay, y2: ay, stroke: '#999' }, svg);
    for (let t = 1870; t <= 2020; t += 10) {
      el('line', { x1: xOf(t), x2: xOf(t), y1: ay, y2: ay + 6, stroke: '#999' }, svg);
      txt(svg, { x: xOf(t), y: ay + 20, 'text-anchor': 'middle', 'font-size': 11, fill: '#777' }, t);
    }
    // eras
    [[1870, 1910, '#2f9e4412'], [1910, 1940, '#ae3ec912'], [1940, 1975, '#3b5bdb10'], [1975, 2025, '#f08c0012']].forEach(([a, b, c]) =>
      el('rect', { x: xOf(a), y: 18, width: xOf(b) - xOf(a), height: 235, fill: c }, svg));
    // now line
    const nx = xOf(Math.min(yr, Y1));
    el('rect', { x: X0, y: 18, width: Math.max(0, nx - X0), height: 4, fill: '#0c8599', opacity: .5 }, svg);
    el('line', { x1: nx, x2: nx, y1: 14, y2: ay, stroke: '#0c8599', 'stroke-width': 2, 'stroke-dasharray': '4 3' }, svg);
    order.forEach(i => {
      const e = EVENTS[i];
      if (hidden.has(e.l)) return;
      const lane = LANES.find(l => l.k === e.l);
      const past = e.y <= yr + 0.5;
      const c = el('circle', { cx: xOf(e.y), cy: laneY(e.l) + e.dy, r: i === sel ? 10 : 7, fill: past ? lane.c : '#fff', stroke: lane.c, 'stroke-width': 2, opacity: past ? 1 : .45, class: 'tl-dot' }, svg);
      const ti = el('title', {}, c); ti.textContent = `${e.d} · ${e.t[0]} · ${e.t[1]}`;
      c.addEventListener('click', () => select(i, true));
      if (i === sel) {
        const lx = Math.min(Math.max(xOf(e.y), X0 + 130), X1 - 130);
        const g = el('g', {}, svg);
        const ty = laneY(e.l) + e.dy - 16;
        const lab = txt(g, { x: lx, y: ty, 'text-anchor': 'middle', 'font-size': 12.5, 'font-weight': 700, fill: '#1f2430', class: 'lbl' }, `${e.d} · ${e.t[0]}`);
        const bb = lab.getBBox();
        el('rect', { x: bb.x - 5, y: bb.y - 2, width: bb.width + 10, height: bb.height + 4, rx: 5, fill: '#fff', stroke: lane.c, opacity: .95 }, g).parentNode.insertBefore(g.lastChild, lab);
      }
    });
  }
  function info(i) {
    const e = EVENTS[i], lane = LANES.find(l => l.k === e.l);
    $('tlInfo').innerHTML = `<div class="fadein">
      <div style="font-size:13px;color:${lane.c};font-weight:700">${bil(lane.en, lane.zh)} · <span class="m">${e.d}</span></div>
      <h3>${bi(e.t[0], e.t[1])}</h3>
      <div>${status(e.s)}</div>
      <div class="why"><b>${bil('What problem were they trying to solve?', '他们想解决什么问题？')}</b><br>${bi(e.why[0], e.why[1])}</div>
      <div><b>${bil('What was established', '得到了什么')}:</b> ${bi(e.res[0], e.res[1])}</div>
      <div class="lchips"><span class="muted" style="font-size:13px">${bil('Lessons', '相关课程')}:</span>${lessonChips(e.ls)}</div></div>`;
  }
  function select(i, setSlider) {
    sel = i;
    if (setSlider) $('tlSlider').value = Math.floor(EVENTS[i].y);
    $('tlYear').textContent = $('tlSlider').value;
    info(i);
    draw();
  }
  function fromSlider() {
    const yr = +$('tlSlider').value;
    $('tlYear').textContent = yr;
    const vis = order.filter(i => !hidden.has(EVENTS[i].l) && EVENTS[i].y <= yr + 0.5);
    if (vis.length) { sel = vis[vis.length - 1]; info(sel); }
    else { sel = -1; $('tlInfo').innerHTML = bi('<span class="muted">Drag the slider to the right, or click a dot.</span>', '<span class="muted">向右拖动滑块，或点击圆点。</span>'); }
    draw();
  }
  function stepBy(d) {
    const vis = order.filter(i => !hidden.has(EVENTS[i].l));
    let k = vis.indexOf(sel);
    k = Math.max(0, Math.min(vis.length - 1, k + d));
    if (sel === -1) k = 0;
    select(vis[k], true);
    return k < vis.length - 1;
  }
  $('tlSlider').addEventListener('input', fromSlider);
  $('tlPrev').addEventListener('click', () => stepBy(-1));
  $('tlNext').addEventListener('click', () => stepBy(1));
  $('tlPlay').addEventListener('click', () => {
    if (playing) { clearInterval(playing); playing = null; return; }
    if (sel === order[order.length - 1]) sel = -1;
    stepBy(sel === -1 ? 0 : 1);
    playing = setInterval(() => { if (!stepBy(1)) { clearInterval(playing); playing = null; } }, 1700);
  });
  select(order[0], true);
})();

/* ================= §2 crisis + motivations ================= */
(function crisis() {
  const svg = $('crisisSvg');
  const FLOORS = [
    { en: 'Logical systems: Frege\'s Basic Law V (unrestricted comprehension)', zh: '逻辑系统：弗雷格第五基本定律（不受限制的概括原则）' },
    { en: 'Cantor\'s theory of sets, ordinals and cardinals', zh: '康托尔的集合、序数与基数理论' },
    { en: 'Everyday mathematics: arithmetic, algebra, analysis (ε–δ, Dedekind cuts)', zh: '日常数学：算术、代数、分析（ε–δ、戴德金分割）' },
  ];
  const COL = { ok: ['#f1f3f5', '#adb5bd'], crack: ['#ffe3e3', '#e03131'], dispute: ['#fff3bf', '#f08c00'], fixed: ['#d3f9d8', '#2f9e44'], plan: ['#e7ecff', '#3b5bdb'] };
  const EP = [
    { b: ['1897 Burali-Forti', '1897 布拉利–福尔蒂'], st: ['ok', 'crack', 'ok'],
      en: 'The “set of all ordinals” leads to contradiction. Only the <b>middle floor</b> is hit, and only at its very top: some totalities are too big to be sets. Cantor himself (letters to Dedekind, 1899) called them “inconsistent multiplicities”.',
      zh: '“全体序数的集合”导致矛盾。受冲击的只是<b>中间层</b>，而且只是它的最顶端：有些总体太大，不能成为集合。康托尔本人（1899 年致戴德金的信）称之为“不一致的总体”。' },
    { b: ['1901–02 Russell', '1901–02 罗素'], st: ['crack', 'crack', 'ok'],
      en: 'R = {x : x ∉ x}. The <b>top floor</b> collapses: Frege\'s system, which lets every property define a set, is inconsistent (Frege acknowledged this in the appendix to vol. II of the Grundgesetze, 1903). Naive set formation on the middle floor is hit too. The ground floor is untouched: no contradiction in arithmetic or analysis was found.',
      zh: 'R = {x : x ∉ x}。<b>顶层</b>倒塌：弗雷格的系统允许每个性质定义一个集合，因此是矛盾的（弗雷格在 1903 年《算术基本规律》第二卷附录中承认了这一点）。中间层的朴素集合构造也受到冲击。底层安然无恙：算术和分析中并没有发现矛盾。' },
    { b: ['1904 Zermelo & AC', '1904 策梅洛与选择公理'], st: ['crack', 'dispute', 'ok'],
      en: 'Not a paradox, but a <b>dispute</b>: is it legitimate to make infinitely many arbitrary choices without a rule? Borel, Baire, Lebesgue and others objected. Yellow = contested method, not contradiction.',
      zh: '这不是悖论，而是<b>争议</b>：不给规则就做无穷多次任意选择，是否合法？博雷尔、贝尔、勒贝格等人表示反对。黄色 = 方法有争议，而不是矛盾。' },
    { b: ['1908–22 Repairs', '1908–22 修补'], st: ['fixed', 'fixed', 'ok'],
      en: 'Zermelo (1908) rebuilds the middle floor with axioms; Separation replaces unrestricted comprehension; Fraenkel and Skolem (1922) complete ZF. Russell replaces the top floor with type theory (1908, Principia 1910–13). Green = rebuilt with explicit rules.',
      zh: '策梅洛（1908）用公理重建中间层，用分离公理取代不受限制的概括原则；弗兰克尔与斯科伦（1922）完成了 ZF。罗素用类型论替换了顶层（1908，《数学原理》1910–1913）。绿色 = 按明确规则重建。' },
    { b: ['1920s Brouwer & Weyl', '1920 年代 布劳威尔与外尔'], st: ['fixed', 'dispute', 'dispute'],
      en: 'Brouwer and Weyl question <b>methods</b> even on the ground floor: excluded middle for infinite totalities, impredicative definitions (e.g. the least upper bound). Again: a dispute about what counts as proof, not a contradiction. Weyl\'s 1921 paper made “crisis” the slogan.',
      zh: '布劳威尔和外尔甚至对底层的<b>方法</b>也提出质疑：对无穷总体使用排中律、非直谓定义（例如上确界）。这同样是关于什么算证明的争议，而不是矛盾。外尔 1921 年的论文让“危机”成了口号。' },
    { b: ['1920s Hilbert\'s plan', '1920 年代 希尔伯特的方案'], st: ['fixed', 'plan', 'plan'],
      en: 'Hilbert\'s answer: keep everything classical, formalize it, and prove consistency by finitary means. Blue = scaffolding planned around the building.',
      zh: '希尔伯特的回答：保留全部经典数学，将其形式化，再用有穷方法证明一致性。蓝色 = 计划中围绕大楼搭起的脚手架。' },
    { b: ['1931 Gödel', '1931 哥德尔'], st: ['fixed', 'fixed', 'fixed'],
      en: 'The finitary scaffold cannot be completed from inside: a consistent system with enough arithmetic cannot prove its own consistency. The building still stands; what changed is what “secure” can mean.',
      zh: '有穷的脚手架无法从内部搭完：包含足够算术的一致系统不能证明自身的一致性。大楼依然屹立；改变的是“可靠”一词所能具有的含义。' },
    { b: ['Today', '今天'], st: ['fixed', 'fixed', 'fixed'],
      en: 'ZFC is the standard reference foundation. No contradiction has been found in it; its consistency is supported by evidence (a coherent intended picture, the cumulative hierarchy V, decades of use, relative consistency results), not by an absolute proof. Constructive and type-theoretic foundations coexist with it (§10).',
      zh: 'ZFC 是标准的参照基础。至今没有在其中发现矛盾；它的一致性靠的是证据（清晰一致的直观图景，即累积层级 V；数十年的使用；相对一致性结果），而不是绝对的证明。构造性与类型论的基础与之并存（见 §10）。' },
  ];
  let cur = 0;
  function draw(k) {
    cur = k;
    const e = EP[k];
    svg.innerHTML = '';
    // ground
    el('rect', { x: 40, y: 270, width: 820, height: 10, fill: '#ced4da' }, svg);
    FLOORS.forEach((f, i) => {
      const y = 30 + i * 80, s = e.st[i];
      const [fill, stroke] = COL[s];
      const r = el('rect', { x: 110, y, width: 680, height: 72, rx: 6, fill, stroke, 'stroke-width': 3 }, svg);
      r.classList.add('fadein');
      txt(svg, { x: 450, y: y + 30, 'text-anchor': 'middle', 'font-size': 14, 'font-weight': 700, class: 'lbl' }, f.en);
      txt(svg, { x: 450, y: y + 52, 'text-anchor': 'middle', 'font-size': 13, fill: '#555', class: 'lbl' }, f.zh);
      if (s === 'crack') {
        const cx = 700 - i * 40;
        el('polyline', { points: `${cx},${y} ${cx - 12},${y + 18} ${cx + 8},${y + 34} ${cx - 10},${y + 52} ${cx + 4},${y + 72}`, fill: 'none', stroke: '#e03131', 'stroke-width': 4, class: 'fadein' }, svg);
        txt(svg, { x: 815, y: y + 42, 'font-size': 22, fill: '#e03131' }, '✗');
      }
      if (s === 'dispute') txt(svg, { x: 812, y: y + 44, 'font-size': 24, fill: '#f08c00' }, '?');
      if (s === 'fixed') txt(svg, { x: 812, y: y + 44, 'font-size': 22, fill: '#2f9e44' }, '✓');
      if (s === 'plan') {
        el('rect', { x: 100, y: y - 4, width: 700, height: 80, rx: 8, fill: 'none', stroke: '#3b5bdb', 'stroke-width': 2, 'stroke-dasharray': '6 5' }, svg);
      }
    });
    if (k === 6) {
      el('rect', { x: 96, y: 22, width: 708, height: 244, rx: 10, fill: 'none', stroke: '#e03131', 'stroke-width': 2, 'stroke-dasharray': '3 7' }, svg);
      txt(svg, { x: 450, y: 18, 'text-anchor': 'middle', 'font-size': 12.5, fill: '#e03131', 'font-weight': 700, class: 'lbl' }, 'Finitary consistency proof from inside: impossible (Gödel II) · 内部有穷一致性证明：不可能');
    }
    // legend
    [['crack', 'contradiction', '矛盾'], ['dispute', 'disputed', '有争议'], ['fixed', 'rebuilt', '已重建'], ['plan', 'planned', '计划中']].forEach(([s, en, zh], j) => {
      const y = 40 + j * 58;
      el('rect', { x: 34, y, width: 18, height: 18, rx: 3, fill: COL[s][0], stroke: COL[s][1], 'stroke-width': 2 }, svg);
      txt(svg, { x: 43, y: y + 32, 'text-anchor': 'middle', 'font-size': 10.5, fill: '#666', class: 'lbl' }, en);
      txt(svg, { x: 43, y: y + 45, 'text-anchor': 'middle', 'font-size': 10.5, fill: '#666', class: 'lbl' }, zh);
    });
    okBox($('crisisInfo'), `<b>${bil(e.b[0], e.b[1])}</b><br>` + bi(e.en, e.zh), 'info');
    btns.forEach((b, i) => b.classList.toggle('sel', i === k));
  }
  const btns = EP.map((e, k) => {
    const b = document.createElement('button');
    b.className = 'btn small';
    b.innerHTML = bil(e.b[0], e.b[1]);
    b.addEventListener('click', () => draw(k));
    $('crisisBtns').appendChild(b);
    return b;
  });
  draw(0);

  // Venn of motivations
  const vs = $('vennSvg');
  const C = [{ x: 180, y: 175, c: '#3b5bdb', en: '1 · Security', zh: '可靠性', lx: 120, ly: 30 },
    { x: 320, y: 175, c: '#f08c00', en: '2 · Power & limits', zh: '能力与极限', lx: 385, ly: 30 },
    { x: 250, y: 295, c: '#2f9e44', en: '3 · The infinite', zh: '无穷本身', lx: 250, ly: 442 }];
  C.forEach(c => {
    el('circle', { cx: c.x, cy: c.y, r: 120, fill: c.c, 'fill-opacity': .1, stroke: c.c, 'stroke-width': 2.5 }, vs);
    txt(vs, { x: c.lx, y: c.ly, 'text-anchor': 'middle', 'font-size': 14, 'font-weight': 700, fill: c.c, class: 'lbl' }, `${c.en} · ${c.zh}`);
  });
  const pos = { S: [110, 135], L: [395, 135], I: [250, 360], SL: [250, 125], SI: [165, 265], LI: [335, 265], SLI: [250, 215] };
  const R = [
    { r: 'SI', en: 'ZF/ZFC axioms (1908–22)', zh: 'ZF/ZFC 公理（1908–22）', why: ['Secure set formation against paradoxes, and make the transfinite a precise subject.', '让集合的构造免于悖论，同时使超穷成为精确的学科。'] },
    { r: 'SL', en: 'Gödel incompleteness (1931)', zh: '哥德尔不完全性（1931）', why: ['A limit theorem that answers a security question: consistency cannot be proved from inside.', '一个回答可靠性问题的极限定理：一致性无法从内部证明。'] },
    { r: 'SLI', en: 'Gentzen: Con(PA) via ε₀ (1936)', zh: '根岑：经 ε₀ 证 Con(PA)（1936）', why: ['Security (consistency of PA), limits (exactly how much induction is needed) and the infinite (the transfinite ordinal ε₀).', '可靠性（PA 的一致性），极限（究竟需要多少归纳），无穷（超限序数 ε₀）。'] },
    { r: 'L', en: 'Halting problem (1936)', zh: '停机问题（1936）', why: ['A pure limit result: no algorithm decides halting.', '纯粹的极限结果：没有算法能判定停机。'] },
    { r: 'L', en: 'Tarski undefinability (1933)', zh: '塔斯基不可定义性（1933）', why: ['A limit on definability: arithmetic cannot define its own truth.', '可定义性的极限：算术无法定义它自己的真。'] },
    { r: 'L', en: 'Completeness theorem (1929/30)', zh: '完备性定理（1929/30）', why: ['A power result: first-order proof captures exactly first-order validity.', '能力结果：一阶证明恰好刻画一阶有效性。'] },
    { r: 'L', en: 'MRDP (1970)', zh: 'MRDP（1970）', why: ['A limit result in number theory: no algorithm for Diophantine equations.', '数论中的极限结果：丢番图方程没有通用算法。'] },
    { r: 'SL', en: 'Reverse mathematics (1974–)', zh: '反推数学（1974–）', why: ['Calibrates exactly which axioms theorems need, partly realizing a relativized Hilbert program.', '精确校准定理需要哪些公理，部分实现了相对化的希尔伯特纲领。'] },
    { r: 'SI', en: 'Gödel\'s L (1938/40)', zh: '哥德尔的 L（1938/40）', why: ['A relative consistency result (security) obtained by building a model of the transfinite.', '通过构建一个超穷模型得到的相对一致性结果（可靠性）。'] },
    { r: 'LI', en: 'Cohen forcing / CH (1963)', zh: '科恩力迫 / CH（1963）', why: ['A limit of ZFC (it cannot decide CH), obtained by building new universes of sets.', 'ZFC 的极限（它判定不了 CH），通过构造新的集合宇宙得到。'] },
    { r: 'I', en: 'Cantor\'s diagonal (1891)', zh: '康托尔对角线（1891）', why: ['The founding result of the mathematics of the infinite.', '无穷数学的奠基性结果。'] },
    { r: 'I', en: 'Large cardinals ↔ determinacy (1975–89)', zh: '大基数 ↔ 决定性（1975–89）', why: ['The structure of the infinite for its own sake: how strong axioms organize sets of reals. (Also a consistency-strength ladder, so it touches security.)', '为了无穷本身而研究其结构：强公理如何组织实数集。（它也是一架一致性强度阶梯，因而也触及可靠性。）'] },
  ];
  const dotG = el('g', {}, vs);
  const used = {};
  R.forEach((r, i) => {
    const n = used[r.r] = (used[r.r] || 0) + 1;
    const [x, y] = pos[r.r];
    r.x = x + (n - 1) * 16 - (r.r.length === 1 ? 16 : 0);
    r.y = y + (n % 2 ? 0 : 12);
    r.dot = el('circle', { cx: r.x, cy: r.y, r: 6, fill: '#1f2430', opacity: .25 }, dotG);
    const ti = el('title', {}, r.dot); ti.textContent = r.en;
    const b = document.createElement('div');
    b.className = 'chip';
    b.innerHTML = bil(r.en, r.zh);
    b.addEventListener('click', () => {
      R.forEach(q => { q.dot.setAttribute('opacity', .25); q.dot.setAttribute('r', 6); q.chip.classList.remove('ok'); });
      r.dot.setAttribute('opacity', 1); r.dot.setAttribute('r', 10); b.classList.add('ok');
      const names = r.r.split('').map(k => ({ S: bil('security', '可靠性'), L: bil('power & limits', '能力与极限'), I: bil('the infinite', '无穷') }[k])).join(' + ');
      okBox($('vennInfo'), `<b>${bi(r.en, r.zh)}</b> → ${names}<br>${bi(r.why[0], r.why[1])}`, 'info');
    });
    r.chip = b;
    $('vennChips').appendChild(b);
  });
  okBox($('vennInfo'), bi('Click a result above.', '点击上面的某个结果。'), 'info');
})();

/* ================= §3 four pillars map ================= */
const PILLARS = {
  MT: { x: 230, y: 95, c: '#3b5bdb', en: 'Model theory', zh: '模型论',
    q: ['How do theories relate to the structures that satisfy them? Which classes of structures are “tame”?', '理论与满足它的结构之间是什么关系？哪些结构类是“驯顺的”？'],
    tools: ['compactness, Löwenheim–Skolem, ultraproducts, types, quantifier elimination, stability, o-minimality', '紧致性、勒文海姆–斯科伦、超积、型、量词消去、稳定性、o-极小性'],
    flag: ['Gödel completeness (1929/30); Tarski, real closed fields decidable (1930s, publ. 1948); Morley categoricity (1965); Shelah classification (1970s–); Hrushovski, Mordell–Lang (1996); Pila–Wilkie (2006)', '哥德尔完备性（1929/30）；塔斯基，实闭域可判定（1930 年代，1948 年发表）；莫利范畴性定理（1965）；谢拉赫分类理论（1970 年代起）；赫鲁晓夫斯基，莫德尔–朗（1996）；皮拉–威尔基（2006）'],
    ls: [3, 4, 5, 13, 28] },
  PT: { x: 730, y: 95, c: '#ae3ec9', en: 'Proof theory', zh: '证明论',
    q: ['What do proofs look like, what exactly does a theory prove, and how strong is it?', '证明是什么样子的？一个理论究竟能证明什么？它有多强？'],
    tools: ['sequent calculus, cut elimination, ordinal analysis, functional interpretations, subsystems of arithmetic, reverse mathematics', '相继式演算、切消、序数分析、函数解释、算术的子系统、反推数学'],
    flag: ['Gödel incompleteness (1931); Gentzen, Con(PA) via ε₀ (1936); Paris–Harrington (1977); reverse mathematics (Friedman 1974, Simpson); proof mining (Kohlenbach)', '哥德尔不完全性（1931）；根岑，经 ε₀ 证 Con(PA)（1936）；巴黎–哈灵顿（1977）；反推数学（弗里德曼 1974，辛普森）；证明挖掘（科伦巴赫）'],
    ls: [2, 4, 12, 21, 28] },
  ST: { x: 230, y: 415, c: '#2f9e44', en: 'Set theory', zh: '集合论',
    q: ['What sets exist, what is true in the universe of all sets, and how large can infinity be?', '哪些集合存在？在全体集合构成的宇宙中什么为真？无穷能有多大？'],
    tools: ['ZFC, ordinals and cardinals, the cumulative hierarchy, inner models (L), forcing, large cardinals', 'ZFC、序数与基数、累积层级、内模型（L）、力迫法、大基数'],
    flag: ['Gödel, Con(ZFC + GCH) via L (1938/40); Cohen, independence of CH (1963); Shelah, Whitehead (1974); Martin, Borel determinacy (1975); Martin–Steel and Woodin, PD (1985–89)', '哥德尔，经 L 证 Con(ZFC + GCH)（1938/40）；科恩，CH 的独立性（1963）；谢拉赫，怀特海问题（1974）；马丁，博雷尔决定性（1975）；马丁–斯蒂尔与伍丁，PD（1985–89）'],
    ls: [6, 7, 8, 9, 10, 14, 15, 16, 20, 22, 23, 24, 25, 27] },
  CT: { x: 730, y: 415, c: '#f08c00', en: 'Computability theory', zh: '可计算性理论',
    q: ['What can be computed, and how do unsolvable problems compare in difficulty?', '什么是可计算的？不可解问题之间的难度如何比较？'],
    tools: ['Turing machines, reductions, the Turing jump, the priority method, arithmetical and analytical hierarchies', '图灵机、归约、图灵跳跃、优先方法、算术层级与分析层级'],
    flag: ['Church, Turing (1936); Kleene–Post (1954); Friedberg–Muchnik (1956–57); MRDP (1970); algorithmic randomness (1960s–)', '丘奇、图灵（1936）；克莱尼–波斯特（1954）；弗里德伯格–穆奇尼克（1956–57）；MRDP（1970）；算法随机性（1960 年代起）'],
    ls: [11, 17, 18, 28] },
  DS: { x: 480, y: 515, c: '#c2255c', small: true, en: 'Descriptive set theory', zh: '描述集合论',
    q: ['A bridge area: which definable sets of reals are well behaved (measurable, Baire property, perfect set property)?', '一个桥梁领域：哪些可定义的实数集性质良好（可测、具有贝尔性质、完美集性质）？'],
    tools: ['Borel and projective hierarchies, trees, infinite games, effective (lightface) versions', '博雷尔层级与投影层级、树、无穷博弈、能行（细体）版本'],
    flag: ['Suslin, Borel = Δ¹₁ (1917); Kleene, Δ¹₁ = hyperarithmetic (1955); Martin (1975); Harrington–Kechris–Louveau (1990)', '苏斯林，博雷尔 = Δ¹₁（1917）；克莱尼，Δ¹₁ = 超算术（1955）；马丁（1975）；哈灵顿–凯克里斯–卢沃（1990）'],
    ls: [18, 19, 25] },
};
const BRIDGES = [
  { a: 'MT', b: 'PT', p: 'M230,63 Q480,10 730,63', lx: 480, ly: 34, en: 'Completeness', zh: '完备性',
    d: ['<b>Gödel\'s completeness theorem</b> (1929/30): T ⊢ φ iff φ holds in every model of T. Proof (syntax) and truth in all models (semantics) give the same consequence relation in first-order logic. Compactness is a corollary.', '<b>哥德尔完备性定理</b>（1929/30）：T ⊢ φ 当且仅当 φ 在 T 的每个模型中成立。在一阶逻辑中，证明（语法）与在所有模型中为真（语义）给出同一个后承关系。紧致性定理是其推论。'], ls: [4] },
  { a: 'MT', b: 'ST', p: 'M170,127 Q70,255 170,383', lx: 104, ly: 245, en: 'Compactness → compact cardinals', zh: '紧致性 → 紧基数',
    d: ['<b>Compactness and ultraproducts → large cardinals.</b> Asking for which κ the infinitary logic L<sub>κ,κ</sub> is compact gives large cardinals: an uncountable κ is weakly compact iff L<sub>κ,κ</sub> satisfies compactness for sets of at most κ sentences; strongly compact cardinals satisfy full compactness. Łoś\'s ultraproducts (1955) become ultrapowers j : V → M (Scott 1961: a measurable cardinal implies V ≠ L).', '<b>紧致性与超积 → 大基数。</b>追问哪些 κ 使无穷语言 L<sub>κ,κ</sub> 满足紧致性，就得到大基数：不可数基数 κ 是弱紧的，当且仅当 L<sub>κ,κ</sub> 对至多 κ 个语句的集合满足紧致性；强紧基数满足完全的紧致性。沃希的超积（1955）变成了超幂 j : V → M（斯科特 1961：存在可测基数则 V ≠ L）。'], ls: [5, 23, 24] },
  { a: 'MT', b: 'ST', p: 'M290,127 Q390,255 290,383', lx: 330, ly: 268, en: 'Forcing ↔ Boolean-valued models', zh: '力迫 ↔ 布尔值模型',
    d: ['<b>Forcing as model theory.</b> Scott, Solovay and Vopěnka (mid-1960s) recast Cohen\'s forcing as building a Boolean-valued model V<sup>B</sup>, in which each sentence gets a truth value in a complete Boolean algebra B instead of just true/false.', '<b>力迫法即模型论。</b>斯科特、索洛韦和沃彭卡（1960 年代中期）把科恩的力迫法改写为构造布尔值模型 V<sup>B</sup>：每个语句的真值取自完备布尔代数 B，而不仅仅是真或假。'], ls: [16] },
  { a: 'PT', b: 'CT', p: 'M790,127 Q890,255 790,383', lx: 836, ly: 245, en: 'Incompleteness ↔ undecidability', zh: '不完全 ↔ 不可判定',
    d: ['<b>Incompleteness from undecidability.</b> If a consistent, effectively axiomatized theory extending a weak arithmetic were complete, its theorems would be decidable (enumerate proofs until φ or ¬φ appears). But such a theory can represent the halting problem, which is undecidable. Gödel numbering and representability are computability notions; Church (1936) also proved first-order validity undecidable.', '<b>由不可判定推出不完全。</b>若一个一致、能行公理化、扩张弱算术的理论是完全的，它的定理就可判定（枚举所有证明，直到出现 φ 或 ¬φ）。但这样的理论能表示停机问题，而停机问题不可判定。哥德尔编码与可表示性都是可计算性概念；丘奇（1936）还证明了一阶有效性不可判定。'], ls: [11, 12] },
  { a: 'PT', b: 'ST', p: 'M690,127 L270,383', lx: 610, ly: 176, en: 'Ordinal analysis', zh: '序数分析',
    d: ['<b>Ordinal analysis ↔ set-theoretic ordinals.</b> Gentzen (1936): PA\'s consistency follows from transfinite induction up to ε₀, the proof-theoretic ordinal of PA. Stronger theories need larger ordinals (Γ₀ for ATR₀, the Bachmann–Howard ordinal for KP), whose notations use “collapsing functions” borrowed from uncountable ordinals. More broadly, consistency strength orders theories all the way from PA to large cardinals.', '<b>序数分析 ↔ 集合论中的序数。</b>根岑（1936）：PA 的一致性可由直到 ε₀ 的超限归纳推出，ε₀ 是 PA 的证明论序数。更强的理论需要更大的序数（ATR₀ 对应 Γ₀，KP 对应巴赫曼–霍华德序数），其记号要借助取自不可数序数的“坍缩函数”。更广义地说，一致性强度把从 PA 到大基数的各种理论排成一列。'], ls: [21, 23] },
  { a: 'MT', b: 'CT', p: 'M270,127 L690,383', lx: 350, ly: 176, en: 'Decidable theories', zh: '可判定理论',
    d: ['<b>Decidability of theories, computable structures.</b> Tarski: the theory of real closed fields has quantifier elimination and is decidable (1930s, published 1948), while the theory of (ℕ, +, ×) is undecidable. Computable structure theory asks which structures have computable copies and how hard isomorphisms are to compute.', '<b>理论的可判定性与可计算结构。</b>塔斯基：实闭域理论可量词消去且可判定（1930 年代得到，1948 年发表），而 (ℕ, +, ×) 的理论不可判定。可计算结构理论研究哪些结构有可计算的副本，以及计算同构有多难。'], ls: [11, 28] },
  { a: 'CT', b: 'DS', p: 'M730,447 Q700,515 570,515', lx: 735, ly: 500, en: 'Effective DST', zh: '能行描述集合论',
    d: ['<b>Effective descriptive set theory.</b> Lightface classes match boldface ones: arithmetical ↔ finite Borel levels, Δ¹₁ = hyperarithmetic (Kleene 1955) ↔ Borel (Suslin 1917), Σ¹₁ ↔ analytic. Boldface = lightface relativized to a real parameter. Methods flow both ways (Moschovakis, Harrington, Kechris, Louveau and others).', '<b>能行描述集合论。</b>细体类与粗体类一一对应：算术集 ↔ 有限层博雷尔类，Δ¹₁ = 超算术集（克莱尼 1955）↔ 博雷尔集（苏斯林 1917），Σ¹₁ ↔ 解析集。粗体 = 以某个实数为参数相对化后的细体。方法在两边双向流动（莫斯科瓦基斯、哈灵顿、凯克里斯、卢沃等）。'], ls: [17, 18, 19] },
  { a: 'ST', b: 'DS', p: 'M230,447 Q260,515 390,515', lx: 225, ly: 500, en: 'Large cardinals ↔ determinacy', zh: '大基数 ↔ 决定性',
    d: ['<b>Large cardinals ↔ determinacy.</b> Martin (1970): a measurable cardinal implies Σ¹₁ (analytic) determinacy. Martin–Steel (1989): infinitely many Woodin cardinals imply projective determinacy. Woodin: ZF + AD is equiconsistent with ZFC + infinitely many Woodin cardinals. Determinacy then gives regularity properties of projective sets.', '<b>大基数 ↔ 决定性。</b>马丁（1970）：可测基数推出 Σ¹₁（解析）决定性。马丁–斯蒂尔（1989）：无穷多个伍丁基数推出投影决定性。伍丁：ZF + AD 与 ZFC +“存在无穷多个伍丁基数”等一致。决定性进而给出投影集的各种正则性质。'], ls: [19, 25] },
];
(function pillarMap() {
  const svg = $('mapSvg');
  const gE = el('g', {}, svg), gN = el('g', {}, svg), gL = el('g', {}, svg);
  txt(gE, { x: 480, y: 236, 'text-anchor': 'middle', 'font-size': 13, fill: '#868e96', 'font-style': 'italic', class: 'lbl' }, 'language ↔ structure · 语言 ↔ 结构');
  const edges = BRIDGES.map((b, i) => {
    const g = el('g', { class: 'pedge' }, gE);
    el('path', { d: b.p, fill: 'none', stroke: 'transparent', 'stroke-width': 18 }, g);
    const vis = el('path', { d: b.p, fill: 'none', stroke: '#9aa0aa', 'stroke-width': 3, class: 'vis' }, g);
    const lg = el('g', { class: 'pedge' }, gL);
    const t1 = txt(lg, { x: b.lx, y: b.ly - 2, 'text-anchor': 'middle', 'font-size': 11.5, 'font-weight': 700, fill: '#1f2430', class: 'lbl' }, b.en);
    const t2 = txt(lg, { x: b.lx, y: b.ly + 12, 'text-anchor': 'middle', 'font-size': 11, fill: '#555', class: 'lbl' }, b.zh);
    requestAnimationFrame(() => {
      const w = Math.max(t1.getBBox().width, t2.getBBox().width) + 10;
      const r = el('rect', { x: b.lx - w / 2, y: b.ly - 15, width: w, height: 32, rx: 6, fill: '#fff', stroke: '#d8d3c4', opacity: .95 });
      lg.insertBefore(r, t1);
    });
    [g, lg].forEach(x => x.addEventListener('click', () => pick('e', i)));
    return { g, lg, vis };
  });
  const nodes = {};
  Object.entries(PILLARS).forEach(([k, n]) => {
    const g = el('g', { class: 'pnode', transform: `translate(${n.x},${n.y})` }, gN);
    const w = n.small ? 180 : 210, h = n.small ? 50 : 64;
    el('rect', { x: -w / 2, y: -h / 2, width: w, height: h, rx: 14, fill: '#fff', stroke: n.c, 'stroke-width': 3 }, g);
    txt(g, { x: 0, y: -4, 'text-anchor': 'middle', 'font-size': n.small ? 13.5 : 16, 'font-weight': 800, fill: n.c, class: 'lbl' }, n.en);
    txt(g, { x: 0, y: 15, 'text-anchor': 'middle', 'font-size': n.small ? 12.5 : 14, fill: '#555', class: 'lbl' }, n.zh);
    g.addEventListener('click', () => pick('n', k));
    nodes[k] = g;
  });
  function pick(kind, key) {
    Object.values(nodes).forEach(g => g.classList.remove('sel', 'dimmed'));
    edges.forEach(e => { e.g.classList.remove('sel', 'dimmed'); e.lg.classList.remove('dimmed'); e.vis.setAttribute('stroke', '#9aa0aa'); });
    if (kind === 'n') {
      const n = PILLARS[key];
      nodes[key].classList.add('sel');
      BRIDGES.forEach((b, i) => {
        const on = b.a === key || b.b === key;
        if (on) edges[i].vis.setAttribute('stroke', n.c); else { edges[i].g.classList.add('dimmed'); edges[i].lg.classList.add('dimmed'); }
      });
      const brs = BRIDGES.filter(b => b.a === key || b.b === key).map(b => bil(b.en, b.zh)).join('; ');
      $('mapInfo').innerHTML = `<div class="fadein"><h3 style="color:${n.c}">${bi(n.en, n.zh)}</h3>
        <p><b>${bil('Core question', '核心问题')}:</b> ${bi(n.q[0], n.q[1])}</p>
        <p><b>${bil('Main tools', '主要工具')}:</b> ${bi(n.tools[0], n.tools[1])}</p>
        <p><b>${bil('Flagship theorems', '代表性定理')}:</b> ${bi(n.flag[0], n.flag[1])}</p>
        <p><b>${bil('Bridges', '桥梁')}:</b> ${brs}</p>
        <div class="lchips"><span class="muted" style="font-size:13px">${bil('Lessons', '相关课程')}:</span>${lessonChips(n.ls)}</div></div>`;
    } else {
      const b = BRIDGES[key];
      edges[key].g.classList.add('sel');
      edges[key].vis.setAttribute('stroke', '#ae3ec9');
      edges.forEach((e, i) => { if (i !== key) { e.g.classList.add('dimmed'); e.lg.classList.add('dimmed'); } });
      Object.entries(nodes).forEach(([k, g]) => g.classList.toggle('dimmed', k !== b.a && k !== b.b));
      $('mapInfo').innerHTML = `<div class="fadein"><h3>${bi(PILLARS[b.a].en + ' ↔ ' + PILLARS[b.b].en, PILLARS[b.a].zh + ' ↔ ' + PILLARS[b.b].zh)}</h3>
        <p>${status('thm')} ${bi(b.d[0], b.d[1])}</p>
        <div class="lchips"><span class="muted" style="font-size:13px">${bil('Lessons', '相关课程')}:</span>${lessonChips(b.ls)}</div></div>`;
    }
  }
  pick('n', 'ST');
})();

/* ================= §4 diagonal ================= */
(function diagonal() {
  const svg = $('diagSvg');
  const N = 6, CS = 46, X0 = 90, Y0 = 60;
  const INST = [
    { b: ['Cantor 1891', '康托尔 1891'], row: k => `f(${k})`, col: k => `${k}`, cell: ['n ∈ f(m)?', 'n ∈ f(m)？'], dname: 'D',
      text: ['<b>List:</b> any map f : ℕ → P(ℕ). Row m is the set f(m), as a 0/1 sequence. <b>Flip:</b> D = {n : n ∉ f(n)}. <b>Conclusion:</b> D differs from row n at column n, so D ≠ f(n) for all n: f is not onto. <span class="status st-thm">theorem</span> |X| &lt; |P(X)| (Cantor 1891).', '<b>列表：</b>任意映射 f : ℕ → P(ℕ)。第 m 行是集合 f(m)，写成 0/1 序列。<b>翻转：</b>D = {n : n ∉ f(n)}。<b>结论：</b>D 在第 n 列与第 n 行不同，所以对所有 n 都有 D ≠ f(n)：f 不是满射。<span class="status st-thm">定理</span> |X| &lt; |P(X)|（康托尔 1891）。'], clash: false },
    { b: ['Russell 1901', '罗素 1901'], row: k => `x${'₀₁₂₃₄₅'[k]}`, col: k => `x${'₀₁₂₃₄₅'[k]}`, cell: ['xₙ ∈ xₘ?', 'xₙ ∈ xₘ？'], dname: 'R',
      text: ['<b>List:</b> all sets (rows and columns are the same sets). <b>Flip:</b> R = {x : x ∉ x}. <b>Conclusion:</b> if R were a set it would be some row xₖ, and at the diagonal cell (k, k): R ∈ R ⇔ R ∉ R. So unrestricted comprehension is inconsistent. <span class="status st-thm">theorem</span>', '<b>列表：</b>所有集合（行与列是同一批集合）。<b>翻转：</b>R = {x : x ∉ x}。<b>结论：</b>若 R 是集合，它就是某一行 xₖ，而在对角格 (k, k) 处：R ∈ R ⇔ R ∉ R。所以不受限制的概括原则是矛盾的。<span class="status st-thm">定理</span>'], clash: true },
    { b: ['Turing 1936', '图灵 1936'], row: k => `P${'₀₁₂₃₄₅'[k]}`, col: k => `${k}`, cell: ['Pₘ halts on n?', 'Pₘ 在 n 上停机？'], dname: 'D',
      text: ['<b>List:</b> all programs P₀, P₁, …; columns are inputs. <b>Flip:</b> D(n) halts iff Pₙ(n) does not halt. <b>Conclusion:</b> if halting were decidable, D would be a program Pₖ, and cell (k, k) gives a contradiction. <span class="status st-thm">theorem</span> The halting problem is undecidable (Turing 1936).', '<b>列表：</b>所有程序 P₀, P₁, …；列是输入。<b>翻转：</b>D(n) 停机当且仅当 Pₙ(n) 不停机。<b>结论：</b>若停机问题可判定，D 就是某个程序 Pₖ，格 (k, k) 导致矛盾。<span class="status st-thm">定理</span> 停机问题不可判定（图灵 1936）。'], clash: true },
    { b: ['Gödel 1931', '哥德尔 1931'], row: k => `φ${'₀₁₂₃₄₅'[k]}(x)`, col: k => `${k}`, cell: ['PA ⊢ φₘ(n)?', 'PA ⊢ φₘ(n)？'], dname: 'ψ',
      text: ['<b>List:</b> all formulas φₘ(x) with one free variable; columns are numerals. <b>Flip:</b> ψ(n) := “φₙ(n) is not provable”, expressible because provability is arithmetically definable (Gödel numbering). <b>Conclusion:</b> ψ is itself some φₖ; the sentence G = φₖ(k) says “I am not provable”. If PA is consistent, PA ⊬ G; if PA is ω-consistent (e.g. true in ℕ), also PA ⊬ ¬G. Rosser\'s variant sentence (1936) is undecidable assuming only consistency. <span class="status st-thm">theorem</span> (Gödel 1931; Rosser 1936)', '<b>列表：</b>所有只含一个自由变元的公式 φₘ(x)；列是数码。<b>翻转：</b>ψ(n) :=“φₙ(n) 不可证”，因为可证性在算术中可定义（哥德尔编码），所以它能被表达。<b>结论：</b>ψ 本身是某个 φₖ；语句 G = φₖ(k) 说的是“我不可证”。若 PA 一致，则 PA ⊬ G；若 PA 是 ω-一致的（例如在 ℕ 中为真），则也有 PA ⊬ ¬G。罗瑟的变体语句（1936）只需假定一致性就不可判定。<span class="status st-thm">定理</span>（哥德尔 1931；罗瑟 1936）'], clash: false },
    { b: ['Tarski 1933', '塔斯基 1933'], row: k => `φ${'₀₁₂₃₄₅'[k]}(x)`, col: k => `${k}`, cell: ['ℕ ⊨ φₘ(n)?', 'ℕ ⊨ φₘ(n)？'], dname: 'ψ',
      text: ['<b>List:</b> formulas φₘ(x); entry = is φₘ(n) true in ℕ? <b>Flip:</b> suppose a formula True(x) defined arithmetic truth; set ψ(n) := ¬True(⌜φₙ(n)⌝). <b>Conclusion:</b> ψ = φₖ for some k, and φₖ(k) is true iff it is not true. So no arithmetic formula defines arithmetic truth. <span class="status st-thm">theorem</span> (Tarski 1933)', '<b>列表：</b>公式 φₘ(x)；表项 = φₘ(n) 在 ℕ 中是否为真？<b>翻转：</b>假设某个公式 True(x) 定义了算术真，令 ψ(n) := ¬True(⌜φₙ(n)⌝)。<b>结论：</b>对某个 k 有 ψ = φₖ，于是 φₖ(k) 为真当且仅当它不真。所以没有算术公式能定义算术真。<span class="status st-thm">定理</span>（塔斯基 1933）'], clash: true },
    { b: ['Forcing (cousin)', '力迫法（近亲）'], row: k => `r${'₀₁₂₃₄₅'[k]}`, col: k => `bit ${k}`, cell: ['rₘ(n)', 'rₘ(n)'], dname: 'g',
      text: ['<b>List:</b> the reals r₀, r₁, … of a countable transitive model M. <b>Build:</b> a Cohen generic real g meets every dense set of M; for each r ∈ M, D<sub>r</sub> = {p : p disagrees with r somewhere} is dense, so g ≠ r. Flipping the diagonal is the simplest way to meet these particular requirements. <b>Conclusion:</b> g ∉ M, and M[g] is a bigger model. <span class="status st-thm">theorem</span> (Cohen 1963). Analogy, not identity: genericity meets <i>all</i> dense sets of M.', '<b>列表：</b>可数传递模型 M 中的实数 r₀, r₁, …。<b>构造：</b>科恩泛型实数 g 与 M 中的每个稠密集相交；对每个 r ∈ M，D<sub>r</sub> = {p : p 在某处与 r 不同} 是稠密的，所以 g ≠ r。翻转对角线是满足这些特定要求的最简单办法。<b>结论：</b>g ∉ M，M[g] 是更大的模型。<span class="status st-thm">定理</span>（科恩 1963）。这只是类比而非等同：泛型性要求与 M 的<i>所有</i>稠密集相交。'], clash: false },
  ];
  let cur = 0, token = 0, bits = [];
  function base() {
    token++;
    const it = INST[cur];
    svg.innerHTML = '';
    bits = Array.from({ length: N }, () => Array.from({ length: N }, () => Math.random() < .5 ? 1 : 0));
    txt(svg, { x: X0 + N * CS / 2, y: 20, 'text-anchor': 'middle', 'font-size': 13, fill: '#555', class: 'lbl' }, /[\u4e00-\u9fff]/.test(it.cell[1]) ? `${it.cell[0]} · ${it.cell[1]}` : it.cell[0]);
    for (let c = 0; c < N; c++) txt(svg, { x: X0 + c * CS + CS / 2, y: Y0 - 10, 'text-anchor': 'middle', 'font-size': 13, fill: '#f08c00', 'font-weight': 700 }, it.col(c));
    for (let r = 0; r < N; r++) {
      txt(svg, { x: X0 - 10, y: Y0 + r * CS + CS / 2 + 5, 'text-anchor': 'end', 'font-size': 14, 'font-weight': 700 }, it.row(r));
      for (let c = 0; c < N; c++) {
        el('rect', { x: X0 + c * CS + 2, y: Y0 + r * CS + 2, width: CS - 4, height: CS - 4, rx: 6, fill: bits[r][c] ? '#d3f9d8' : '#ffe3e3', id: `dg${r}_${c}` }, svg);
        txt(svg, { x: X0 + c * CS + CS / 2, y: Y0 + r * CS + CS / 2 + 5, 'text-anchor': 'middle', 'font-size': 15 }, bits[r][c]);
      }
      txt(svg, { x: X0 + N * CS + 10, y: Y0 + r * CS + CS / 2 + 5, 'font-size': 14, fill: '#999' }, '…');
    }
    txt(svg, { x: X0 - 30, y: Y0 + N * CS + 14, 'font-size': 14, fill: '#999' }, '⋮');
    $('diagInfo').innerHTML = `<h3>${bi(it.b[0], it.b[1])}</h3>${bi(it.text[0], it.text[1])}`;
  }
  async function run() {
    base();
    const my = token, it = INST[cur];
    const yD = Y0 + N * CS + 24;
    txt(svg, { x: X0 - 10, y: yD + CS / 2 + 5, 'text-anchor': 'end', 'font-size': 15, 'font-weight': 800, fill: '#ae3ec9' }, it.dname);
    for (let k = 0; k < N; k++) {
      await sleep(420);
      if (my !== token) return;
      const cell = svg.querySelector(`#dg${k}_${k}`);
      cell.setAttribute('stroke', '#ae3ec9'); cell.setAttribute('stroke-width', 3);
      el('rect', { x: X0 + k * CS + 2, y: yD + 2, width: CS - 4, height: CS - 4, rx: 6, fill: '#f8e7fc', stroke: '#ae3ec9', 'stroke-width': 2, class: 'pop' }, svg);
      txt(svg, { x: X0 + k * CS + CS / 2, y: yD + CS / 2 + 5, 'text-anchor': 'middle', 'font-size': 15, 'font-weight': 800, fill: '#ae3ec9' }, 1 - bits[k][k]);
      txt(svg, { x: X0 + N * CS + 26, y: Y0 + k * CS + CS / 2 + 5, 'font-size': 12, fill: '#e03131', 'font-weight': 700 }, `≠ ${it.dname}`);
    }
    await sleep(400);
    if (my !== token) return;
    const msg = it.clash ? `${it.dname} = row k?  ⇒  cell (k,k) ⚡ contradiction · 矛盾` : `${it.dname} ≠ every row · ${it.dname} 不同于每一行`;
    txt(svg, { x: X0 - 70, y: yD + CS + 30, 'font-size': 13, fill: '#ae3ec9', 'font-weight': 700, class: 'lbl' }, msg);
  }
  const btns = INST.map((it, i) => {
    const b = document.createElement('button');
    b.className = 'btn small';
    b.innerHTML = bil(it.b[0], it.b[1]);
    b.addEventListener('click', () => { cur = i; btns.forEach((x, j) => x.classList.toggle('sel', j === i)); base(); });
    $('diagBtns').appendChild(b);
    return b;
  });
  btns[0].classList.add('sel');
  $('diagRun').addEventListener('click', run);
  base();
})();

/* ================= §5 syntax vs semantics ================= */
(function synsem() {
  const svg = $('ssSvg');
  const SET = [
    { b: ['Propositional logic', '命题逻辑'], L: 'Γ ⊢ φ', R: 'Γ ⊨ φ', sound: 1, comp: 1, dec: 1,
      en: 'Both bridges hold (sound and complete), and ⊨ is even <b>decidable</b> by truth tables (L1–L2).', zh: '两座桥都成立（可靠且完备），而且 ⊨ 甚至可以用真值表<b>判定</b>（第 1–2 课）。' },
    { b: ['First-order logic', '一阶逻辑'], L: 'T ⊢ φ', R: 'T ⊨ φ', sound: 1, comp: 1, dec: 0,
      en: 'Sound and complete (Gödel 1929/30), so validity is <b>computably enumerable</b> (list all proofs). But it is <b>not decidable</b> (Church, Turing 1936).', zh: '可靠且完备（哥德尔 1929/30），所以有效式集合是<b>可计算枚举</b>的（列出所有证明即可）。但它<b>不可判定</b>（丘奇、图灵 1936）。' },
    { b: ['Second-order logic (full semantics)', '二阶逻辑（完全语义）'], L: '⊢₂ φ', R: '⊨₂ φ', sound: 1, comp: 0, dec: 0,
      en: 'Usual proof systems are sound, but <b>no effective proof system is complete</b>: second-order PA is categorical (its only model is ℕ), so a complete system would enumerate all arithmetic truths, contradicting Gödel/Tarski. Expressive power is bought at the price of completeness.', zh: '常用的证明系统是可靠的，但<b>没有任何能行证明系统是完备的</b>：二阶 PA 是范畴的（唯一模型是 ℕ），完备的系统就能枚举所有算术真理，与哥德尔／塔斯基矛盾。表达力的代价是失去完备性。' },
    { b: ['PA vs the standard model ℕ', 'PA 与标准模型 ℕ'], L: 'PA ⊢ φ', R: 'ℕ ⊨ φ', sound: 1, comp: 0, dec: 0,
      en: 'Every theorem of PA is true in ℕ, but not every truth of ℕ is a theorem of PA (Gödel 1931): the Gödel sentence and Goodstein\'s theorem are true in ℕ yet unprovable in PA. This is <b>incompleteness</b>: a property of the <i>theory</i> PA, not of the logic.', zh: 'PA 的每条定理在 ℕ 中都为真，但 ℕ 中的真理并非都是 PA 的定理（哥德尔 1931）：哥德尔语句与古德斯坦定理在 ℕ 中为真，却在 PA 中不可证。这就是<b>不完全性</b>：它是<i>理论</i> PA 的性质，而不是逻辑的性质。' },
    { b: ['PA vs all models of PA', 'PA 与 PA 的所有模型'], L: 'PA ⊢ φ', R: 'PA ⊨ φ', sound: 1, comp: 1, dec: 0,
      en: 'Back to completeness: PA ⊢ φ iff φ is true in <b>every</b> model of PA. The Gödel sentence G is unprovable precisely because it fails in some nonstandard model. Both theorems hold at once.', zh: '回到完备性：PA ⊢ φ 当且仅当 φ 在 PA 的<b>每个</b>模型中为真。哥德尔语句 G 之所以不可证，正是因为它在某个非标准模型中不成立。两个定理同时成立。' },
  ];
  function draw(k) {
    const s = SET[k];
    svg.innerHTML = '';
    const island = (x, c, title, sub, f) => {
      el('rect', { x, y: 40, width: 230, height: 170, rx: 26, fill: c + '18', stroke: c, 'stroke-width': 3 }, svg);
      txt(svg, { x: x + 115, y: 76, 'text-anchor': 'middle', 'font-size': 16, 'font-weight': 800, fill: c, class: 'lbl' }, title);
      txt(svg, { x: x + 115, y: 98, 'text-anchor': 'middle', 'font-size': 12.5, fill: '#555', class: 'lbl' }, sub);
      txt(svg, { x: x + 115, y: 150, 'text-anchor': 'middle', 'font-size': 26, 'font-weight': 700 }, f);
    };
    island(40, '#ae3ec9', 'Syntax · 语法 (⊢)', 'finite proofs, rules · 有限证明与规则', s.L);
    island(630, '#3b5bdb', 'Semantics · 语义 (⊨)', 'truth in models · 模型中的真', s.R);
    const bridge = (y, ok, dir, en, zh) => {
      const c = ok ? '#2f9e44' : '#e03131';
      const [x1, x2] = dir > 0 ? [278, 622] : [622, 278];
      if (ok) {
        const ln = el('line', { x1, y1: y, x2, y2: y, stroke: c, 'stroke-width': 7, 'stroke-linecap': 'round', class: 'fadein' }, svg);
        ln.style.animationDuration = '.8s';
        const ax = x2, s2 = dir > 0 ? -1 : 1;
        el('polygon', { points: `${ax},${y} ${ax + s2 * 16},${y - 10} ${ax + s2 * 16},${y + 10}`, fill: c }, svg);
      } else {
        el('line', { x1, y1: y, x2: 420, y2: y, stroke: c, 'stroke-width': 7, 'stroke-linecap': 'round', 'stroke-dasharray': '2 0' }, svg);
        el('line', { x1: 480, y1: y + 14, x2, y2: y + 6, stroke: c, 'stroke-width': 7, 'stroke-linecap': 'round', opacity: .5 }, svg);
        txt(svg, { x: 450, y: y + 8, 'text-anchor': 'middle', 'font-size': 22, fill: c, 'font-weight': 800 }, '✗');
      }
      txt(svg, { x: 450, y: y - 14, 'text-anchor': 'middle', 'font-size': 13, 'font-weight': 700, fill: c, class: 'lbl' }, `${en} · ${zh}`);
    };
    bridge(100, s.sound, 1, 'Soundness ⊢ ⇒ ⊨', '可靠性');
    bridge(170, s.comp, -1, (k === 3 ? 'Truth ⇒ provability' : 'Completeness ⊨ ⇒ ⊢'), (k === 3 ? '真 ⇒ 可证' : '完备性'));
    const dc = s.dec ? '#2f9e44' : '#868e96';
    el('rect', { x: 330, y: 222, width: 240, height: 34, rx: 17, fill: s.dec ? '#d3f9d8' : '#f1f3f5', stroke: dc }, svg);
    txt(svg, { x: 450, y: 244, 'text-anchor': 'middle', 'font-size': 13, 'font-weight': 700, fill: dc, class: 'lbl' }, s.dec ? 'decidable ✓ · 可判定' : 'not decidable · 不可判定');
    okBox($('ssInfo'), bi(s.en, s.zh), 'info');
    btns.forEach((b, i) => b.classList.toggle('sel', i === k));
  }
  const btns = SET.map((s, i) => {
    const b = document.createElement('button');
    b.className = 'btn small';
    b.innerHTML = bil(s.b[0], s.b[1]);
    b.addEventListener('click', () => draw(i));
    $('ssBtns').appendChild(b);
    return b;
  });
  draw(1);
})();

/* ================= §6 ladders everywhere ================= */
(function ladders() {
  const svg = $('ladSvg');
  const COLS = [
    { en: 'Arithmetical', zh: '算术层级', l: 17, c: '#f08c00', r: ['Δ⁰₁ computable', 'Σ⁰₁', 'Σ⁰₂', 'Σ⁰₃', '⋯', 'arithmetical'] },
    { en: 'Turing jumps', zh: '图灵跳跃', l: 17, c: '#e8590c', r: ['0', '0′', '0″', '0‴', '⋯', '0⁽ω⁾'] },
    { en: 'Analytical', zh: '分析层级', l: 18, c: '#c2255c', r: ['Δ¹₁ = HYP', 'Σ¹₁', 'Σ¹₂', 'Σ¹₃', '⋯'] },
    { en: 'Borel / projective', zh: '博雷尔／投影', l: 19, c: '#ae3ec9', r: ['𝚺⁰₁ open', '𝚺⁰ₙ', 'Borel = 𝚫¹₁', '𝚺¹₁ analytic', '𝚺¹₂', 'projective'] },
    { en: 'Lévy hierarchy', zh: '列维层级', l: 20, c: '#3b5bdb', r: ['Δ₀', 'Σ₁', 'Σ₂', '⋯'] },
    { en: 'Proof-th. ordinals', zh: '证明论序数', l: 21, c: '#1098ad', r: ['ω^ω  RCA₀', 'ε₀  PA, ACA₀', 'Γ₀  ATR₀', 'BH  KP', 'ψ(Ω_ω) Π¹₁-CA₀'] },
    { en: 'Consistency strength', zh: '一致性强度', l: 23, c: '#2f9e44', r: ['PA', 'ZFC', 'inaccessible', 'weakly compact', 'measurable', 'n Woodins', '∞ Woodins', 'supercompact'] },
  ];
  const BR = [
    { b: ['Post\'s theorem', '波斯特定理'], links: [[[0, 1], [1, 0]], [[0, 2], [1, 1]], [[0, 3], [1, 2]]],
      en: 'Post: Σ⁰ₙ₊₁ sets are exactly those c.e. relative to 0⁽ⁿ⁾. Counting quantifiers = counting jumps (L17).', zh: '波斯特定理：Σ⁰ₙ₊₁ 集恰好是相对于 0⁽ⁿ⁾ 可计算枚举的集合。数量词个数 = 数跳跃次数（第 17 课）。' },
    { b: ['Lightface ↔ boldface', '细体 ↔ 粗体'], links: [[[0, 1], [3, 0]], [[2, 0], [3, 2]], [[2, 1], [3, 3]], [[2, 2], [3, 4]]],
      en: 'Effective DST: Σ⁰₁ ↔ open; Δ¹₁ = HYP (Kleene 1955) ↔ Borel = 𝚫¹₁ (Suslin 1917); Σ¹ₙ ↔ 𝚺¹ₙ. Boldface = lightface with a real parameter (L18–L19).', zh: '能行描述集合论：Σ⁰₁ ↔ 开集；Δ¹₁ = 超算术（克莱尼 1955）↔ 博雷尔 = 𝚫¹₁（苏斯林 1917）；Σ¹ₙ ↔ 𝚺¹ₙ。粗体 = 带实数参数的细体（第 18–19 课）。' },
    { b: ['Shoenfield absoluteness', '勋菲尔德绝对性'], links: [[[4, 1], [2, 2]]],
      en: 'Shoenfield (1961): Σ¹₂ statements (with real parameters) are absolute between V and any inner model containing the parameters, e.g. L. Σ¹₂ facts are Σ₁ facts about H(ω₁) in the Lévy hierarchy (L20).', zh: '勋菲尔德（1961）：（带实数参数的）Σ¹₂ 命题在 V 与包含这些参数的任一内模型（如 L）之间是绝对的。在列维层级中，Σ¹₂ 事实就是关于 H(ω₁) 的 Σ₁ 事实（第 20 课）。' },
    { b: ['Gentzen: ε₀ ↔ PA', '根岑：ε₀ ↔ PA'], links: [[[5, 1], [6, 0]]],
      en: 'Gentzen (1936): PRA + induction up to ε₀ proves Con(PA), and PA proves induction up to every α < ε₀ but not up to ε₀ itself. ε₀ is the proof-theoretic ordinal of PA (L21).', zh: '根岑（1936）：PRA 加上直到 ε₀ 的归纳可以证明 Con(PA)；PA 能证明直到任一 α < ε₀ 的归纳，却证明不了直到 ε₀ 本身的归纳。ε₀ 是 PA 的证明论序数（第 21 课）。' },
    { b: ['Large cardinals ⇒ determinacy', '大基数 ⇒ 决定性'], links: [[[6, 4], [3, 3]], [[6, 5], [3, 4]], [[6, 6], [3, 5]]],
      en: 'Martin (1970): a measurable ⇒ 𝚺¹₁-determinacy. Martin–Steel (1989): n Woodin cardinals with a measurable above ⇒ 𝚷¹ₙ₊₁-determinacy (equivalently 𝚺¹ₙ₊₁; for n = 1 this is 𝚺¹₂, the rung shown); infinitely many Woodins ⇒ projective determinacy (L25).', zh: '马丁（1970）：可测基数 ⇒ 𝚺¹₁ 决定性。马丁–斯蒂尔（1989）：n 个伍丁基数加其上一个可测基数 ⇒ 𝚷¹ₙ₊₁ 决定性（等价于 𝚺¹ₙ₊₁ 决定性；n = 1 时即图中的 𝚺¹₂）；无穷多个伍丁基数 ⇒ 投影决定性（第 25 课）。' },
  ];
  const CW = 136, X0 = 82, BASE = 440, STEP = 49, RW = 122, RH = 32;
  const pos = (c, r) => [X0 + c * CW, BASE - r * STEP];
  const gLink = el('g', {}, svg), gR = el('g', {}, svg);
  const rungs = [];
  COLS.forEach((col, ci) => {
    const [x] = pos(ci, 0);
    txt(gR, { x, y: 18, 'text-anchor': 'middle', 'font-size': 12, 'font-weight': 800, fill: col.c, class: 'lbl' }, col.en);
    txt(gR, { x, y: 34, 'text-anchor': 'middle', 'font-size': 12, fill: '#555', class: 'lbl' }, `${col.zh} · L${col.l}`);
    el('line', { x1: x - RW / 2 + 4, x2: x - RW / 2 + 4, y1: 46, y2: BASE + 16, stroke: col.c, 'stroke-width': 2, opacity: .35 }, gR);
    el('line', { x1: x + RW / 2 - 4, x2: x + RW / 2 - 4, y1: 46, y2: BASE + 16, stroke: col.c, 'stroke-width': 2, opacity: .35 }, gR);
    rungs[ci] = col.r.map((lab, ri) => {
      const [rx, ry] = pos(ci, ri);
      const a = el('a', { href: `lesson${col.l + (ci === 6 && ri >= 4 ? (ri >= 5 ? 2 : 1) : 0)}.html`, class: 'ladder-rung' }, gR);
      const rect = el('rect', { x: rx - RW / 2, y: ry - RH / 2, width: RW, height: RH, rx: 7, fill: '#fff', stroke: col.c, 'stroke-width': 1.5 }, a);
      txt(a, { x: rx, y: ry + 5, 'text-anchor': 'middle', 'font-size': lab.length > 14 ? 11 : 13, 'font-weight': 600 }, lab);
      return rect;
    });
  });
  function show(k) {
    gLink.innerHTML = '';
    rungs.flat().forEach(r => { r.setAttribute('fill', '#fff'); r.setAttribute('stroke-width', 1.5); });
    const b = BR[k];
    b.links.forEach(([[c1, r1], [c2, r2]], j) => {
      const [x1, y1] = pos(c1, r1), [x2, y2] = pos(c2, r2);
      const sx = x1 + (x2 > x1 ? RW / 2 : -RW / 2), ex = x2 + (x2 > x1 ? -RW / 2 : RW / 2);
      const mx = (sx + ex) / 2, my = Math.min(y1, y2) - 30 - Math.abs(c2 - c1) * 8;
      const p = el('path', { d: `M${sx},${y1} Q${mx},${my} ${ex},${y2}`, fill: 'none', stroke: '#1f2430', 'stroke-width': 3, 'stroke-dasharray': '6 4', class: 'fadein' }, gLink);
      p.style.animationDelay = (j * .15) + 's';
      [[c1, r1], [c2, r2]].forEach(([c, r]) => { rungs[c][r].setAttribute('fill', '#fff3bf'); rungs[c][r].setAttribute('stroke-width', 3.5); });
    });
    okBox($('ladInfo'), `<b>${bil(b.b[0], b.b[1])}</b> ${status('thm')}<br>` + bi(b.en, b.zh), 'info');
    btns.forEach((x, i) => x.classList.toggle('sel', i === k));
  }
  const btns = BR.map((b, i) => {
    const x = document.createElement('button');
    x.className = 'btn small';
    x.innerHTML = bil(b.b[0], b.b[1]);
    x.addEventListener('click', () => show(i));
    $('ladBtns').appendChild(x);
    return x;
  });
  show(0);
})();

/* ================= §7 independence matrix ================= */
(function independence() {
  const THS = [['PA', 'PA'], ['ZFC', 'ZFC'], ['ZFC + ∞ Woodin cardinals', 'ZFC + 无穷多个伍丁基数']];
  const LAB = { prov: ['provable', '可证'], ind: ['independent', '独立'], open: ['open', '未知'], na: ['not expressible', '无法表达'] };
  const ROWS = [
    { s: ['Goodstein\'s theorem', '古德斯坦定理'], c: [
      ['ind', 'Kirby–Paris (1982): unprovable in PA, although true in ℕ. PA ⊬ ¬Goodstein since PA proves only truths.', 'Kirby–Paris（1982）：在 PA 中不可证，尽管它在 ℕ 中为真。PA 也证明不了它的否定，因为 PA 只证明真命题。'],
      ['prov', 'Goodstein (1944): provable using ordinals below ε₀ and their well-foundedness, which ZFC proves.', '古德斯坦（1944）：借助小于 ε₀ 的序数及其良基性即可证明，而 ZFC 能证明这些。'],
      ['prov', 'Stronger than ZFC, so still provable.', '比 ZFC 更强，当然仍可证。']] },
    { s: ['Con(PA)', 'Con(PA)'], c: [
      ['ind', 'Gödel\'s second theorem: PA ⊬ Con(PA). And PA ⊬ ¬Con(PA), because ¬Con(PA) is false in ℕ and PA proves only truths.', '哥德尔第二定理：PA ⊬ Con(PA)。而且 PA ⊬ ¬Con(PA)，因为 ¬Con(PA) 在 ℕ 中为假，PA 只证明真命题。'],
      ['prov', 'In ZFC, ℕ is a set and a model of PA, so PA is consistent.', '在 ZFC 中，ℕ 是一个集合，且是 PA 的模型，所以 PA 是一致的。'],
      ['prov', 'Stronger than ZFC, so still provable.', '比 ZFC 更强，当然仍可证。']] },
    { s: ['Con(ZFC)', 'Con(ZFC)'], c: [
      ['ind', 'Assuming ZFC is consistent: PA ⊬ Con(ZFC) (else ZFC ⊢ Con(ZFC), contradicting Gödel II), and PA ⊬ ¬Con(ZFC) since that would be a false sentence.', '假定 ZFC 一致：PA ⊬ Con(ZFC)（否则 ZFC ⊢ Con(ZFC)，与哥德尔第二定理矛盾）；PA ⊬ ¬Con(ZFC)，因为那是一个假语句。'],
      ['ind', 'Gödel II: ZFC ⊬ Con(ZFC) if ZFC is consistent. ZFC ⊬ ¬Con(ZFC) under the standard assumption that ZFC proves no false arithmetic sentences.', '哥德尔第二定理：若 ZFC 一致，则 ZFC ⊬ Con(ZFC)。在“ZFC 不证明假的算术语句”这一标准假设下，ZFC ⊬ ¬Con(ZFC)。'],
      ['prov', 'A Woodin cardinal δ is inaccessible, so V_δ is a model of ZFC.', '伍丁基数 δ 是不可达基数，所以 V_δ 是 ZFC 的模型。']] },
    { s: ['CH', 'CH'], c: [
      ['na', 'CH quantifies over arbitrary sets of reals; it is not a statement of first-order arithmetic.', 'CH 量化的是任意实数集合，它不是一阶算术中的命题。'],
      ['ind', 'Gödel (1938/40): Con(ZFC) ⇒ Con(ZFC + CH). Cohen (1963): Con(ZFC) ⇒ Con(ZFC + ¬CH).', '哥德尔（1938/40）：Con(ZFC) ⇒ Con(ZFC + CH)。科恩（1963）：Con(ZFC) ⇒ Con(ZFC + ¬CH)。'],
      ['ind', 'Lévy–Solovay (1967): “small” forcing preserves large cardinals, and CH can be forced true or false by small forcing. So the known large cardinals do not decide CH (assuming they are consistent). See L27.', '列维–索洛韦（1967）：“小”力迫保持大基数，而用小力迫就能使 CH 为真或为假。所以已知的大基数都判定不了 CH（假定它们一致）。见第 27 课。']] },
    { s: ['PD (projective determinacy)', 'PD（投影决定性）'], c: [
      ['na', 'PD is about games on reals; not a statement of first-order arithmetic.', 'PD 讨论的是实数上的博弈，不是一阶算术命题。'],
      ['ind', 'ZFC ⊬ PD: PD implies Con(ZFC) (it gives 0#), so Gödel II applies. ZFC ⊬ ¬PD assuming Con(ZFC + ∞ Woodins). In L, PD fails.', 'ZFC ⊬ PD：PD 推出 Con(ZFC)（它给出 0#），所以哥德尔第二定理适用。假定 Con(ZFC + 无穷多个伍丁基数)，则 ZFC ⊬ ¬PD。在 L 中 PD 不成立。'],
      ['prov', 'Martin–Steel (1989): infinitely many Woodin cardinals imply PD.', '马丁–斯蒂尔（1989）：无穷多个伍丁基数推出 PD。']] },
    { s: ['Goldbach\'s conjecture', '哥德巴赫猜想'], c: [
      ['open', 'Open. It is Π⁰₁: if it were false, a counterexample could be checked, and PA would prove it false. So if Goldbach were independent of PA, it would be <b>true</b>.', '未知。它是 Π⁰₁ 语句：如果它为假，反例可以被验证，PA 就能证明它为假。所以若哥德巴赫猜想独立于 PA，它必然<b>为真</b>。'],
      ['open', 'Open; same Π⁰₁ remark applies to ZFC.', '未知；同样的 Π⁰₁ 论证对 ZFC 也成立。'],
      ['open', 'Open. Nobody expects large cardinals to matter here, but nobody knows.', '未知。没人认为大基数会对它有影响，但也没人知道。']] },
  ];
  const tab = $('indTab');
  const shown = ROWS.map(() => [false, false, false]);
  let h = `<tr><th></th>${THS.map(t => `<th>${t[0] === t[1] ? t[0] : bi(t[0], t[1])}</th>`).join('')}</tr>`;
  ROWS.forEach((r, i) => {
    h += `<tr><td class="st">${r.s[0] === r.s[1] ? r.s[0] : bi(r.s[0], r.s[1])}</td>`;
    r.c.forEach((c, j) => { h += `<td class="cell c-hid" data-i="${i}" data-j="${j}">?</td>`; });
    h += '</tr>';
  });
  tab.innerHTML = h;
  const cellOf = (i, j) => tab.querySelector(`td[data-i="${i}"][data-j="${j}"]`);
  function reveal(i, j) {
    shown[i][j] = true;
    const [k] = ROWS[i].c[j], td = cellOf(i, j);
    td.className = `cell c-${k} pop`;
    td.innerHTML = bi(LAB[k][0], LAB[k][1]);
  }
  function explain(i, j) {
    tab.querySelectorAll('td.cell').forEach(x => x.classList.remove('sel'));
    cellOf(i, j).classList.add('sel');
    const [, en, zh] = ROWS[i].c[j];
    okBox($('indInfo'), `<b>${bi(ROWS[i].s[0], ROWS[i].s[1])} / ${bi(THS[j][0], THS[j][1])}:</b> ${bi(en, zh)}`, 'info');
  }
  tab.querySelectorAll('td.cell').forEach(td => td.addEventListener('click', () => {
    const i = +td.dataset.i, j = +td.dataset.j;
    if (!shown[i][j]) reveal(i, j);
    explain(i, j);
  }));
  const B = [
    [['Reveal PA column', '揭晓 PA 列'], () => ROWS.forEach((_, i) => reveal(i, 0))],
    [['Reveal ZFC column', '揭晓 ZFC 列'], () => ROWS.forEach((_, i) => reveal(i, 1))],
    [['Reveal large-cardinal column', '揭晓大基数列'], () => ROWS.forEach((_, i) => reveal(i, 2))],
    [['Hide all', '全部隐藏'], () => { ROWS.forEach((_, i) => [0, 1, 2].forEach(j => { shown[i][j] = false; const td = cellOf(i, j); td.className = 'cell c-hid'; td.textContent = '?'; })); clearBox($('indInfo')); }],
  ];
  B.forEach(([t, f]) => { const b = document.createElement('button'); b.className = 'btn small'; b.innerHTML = bil(t[0], t[1]); b.addEventListener('click', f); $('indBtns').appendChild(b); });
  okBox($('indInfo'), bi('Read across a row: what happens to the statement as the theory gets stronger?', '横着读一行：理论越来越强时，这个命题会怎样？'), 'info');
})();

/* ================= §8 mainstream math ================= */
(function mainstream() {
  const TAGS = { MT: ['Model theory', '模型论', '#3b5bdb'], ST: ['Set theory', '集合论', '#2f9e44'], CT: ['Computability', '可计算性', '#f08c00'], PT: ['Proof theory', '证明论', '#ae3ec9'] };
  const CARDS = [
    { t: 'MT', h: ['Ax–Kochen: p-adic forms', 'Ax–Kochen：p 进型'], who: 'Ax–Kochen, Ershov · 1965', s: 'thm',
      m: ['For each degree d, for all but finitely many primes p, every form of degree d over ℚₚ in more than d² variables has a nontrivial zero. Proof: compare ultraproducts of the ℚₚ with ultraproducts of 𝔽ₚ((t)), where the analogue is known (Lang), and transfer. Artin\'s full conjecture is false (Terjanian 1966).', '对每个次数 d，除有限多个素数 p 外，ℚₚ 上变元个数多于 d² 的 d 次型都有非平凡零点。证明：比较各 ℚₚ 的超积与各 𝔽ₚ((t)) 的超积（后者上的类似结论已知，属于朗），再进行转移。阿廷的完整猜想是错的（Terjanian 1966）。'] },
    { t: 'MT', h: ['Mordell–Lang for function fields', '函数域上的莫德尔–朗猜想'], who: 'Hrushovski · 1996', s: 'thm',
      m: ['Hrushovski proved the function-field Mordell–Lang conjecture in all characteristics using geometric stability theory (Zariski geometries, with Zilber). A landmark: model theory resolving an open problem in Diophantine geometry.', '赫鲁晓夫斯基利用几何稳定性理论（与齐尔伯合作的扎里斯基几何）在所有特征下证明了函数域上的莫德尔–朗猜想。这是一个里程碑：模型论解决了丢番图几何中的公开问题。'] },
    { t: 'MT', h: ['o-minimality, Pila–Wilkie, André–Oort', 'o-极小性、皮拉–威尔基、安德烈–奥尔特'], who: 'Pila–Wilkie 2006; Pila 2011; Pila–Shankar–Tsimerman 2021', s: 'thm',
      m: ['o-minimal structures (van den Dries, Pillay–Steinhorn, Knight) have tame definable sets. Pila–Wilkie: the transcendental part of a definable set has few rational points. With the Pila–Zannier strategy this gave André–Oort for products of modular curves (Pila, Annals 2011) and, with other deep inputs, the full André–Oort conjecture (Pila–Shankar–Tsimerman, arXiv preprint 2021, substantially revised 2024).', 'o-极小结构（范登德里斯、皮雷–斯坦霍恩、奈特）中的可定义集性质驯顺。皮拉–威尔基：可定义集的超越部分上有理点很少。借助皮拉–扎尼尔策略，这给出了模曲线乘积上的安德烈–奥尔特猜想（皮拉，Annals 2011），再结合其他深刻工具，得到了完整的安德烈–奥尔特猜想（皮拉–尚卡尔–齐默曼，arXiv 预印本，2021 年发布，2024 年大幅修订）。'] },
    { t: 'MT', h: ['Nonstandard analysis', '非标准分析'], who: 'A. Robinson · 1961/66', s: 'thm',
      m: ['Using compactness, build ordered fields with infinitesimals that satisfy the same first-order statements as ℝ (transfer principle). This makes Leibniz-style infinitesimal reasoning rigorous.', '利用紧致性构造含无穷小的有序域，它与 ℝ 满足相同的一阶命题（转移原理）。这让莱布尼茨式的无穷小推理变得严格。'] },
    { t: 'ST', h: ['Whitehead\'s problem', '怀特海问题'], who: 'Shelah · 1974', s: 'ind',
      m: ['Is every abelian group A with Ext(A, ℤ) = 0 free? Independent of ZFC: V = L implies yes, MA + ¬CH implies no. Algebraists learned that some natural questions need set theory.', '每个满足 Ext(A, ℤ) = 0 的阿贝尔群 A 都是自由的吗？此问题独立于 ZFC：V = L 推出“是”，MA + ¬CH 推出“否”。代数学家由此认识到，有些自然的问题需要集合论。'] },
    { t: 'ST', h: ['Classification problems & Borel equivalence relations', '分类问题与博雷尔等价关系'], who: 'Harrington–Kechris–Louveau 1990; Foreman–Rudolph–Weiss 2011', s: 'thm',
      m: ['Descriptive set theory measures how hard it is to classify objects up to isomorphism. Glimm–Effros dichotomy for Borel equivalence relations (Harrington–Kechris–Louveau 1990). Foreman–Rudolph–Weiss (2011): isomorphism of ergodic measure-preserving transformations is not Borel, so no “reasonable” complete invariants exist.', '描述集合论度量在同构意义下分类对象有多难。博雷尔等价关系的 Glimm–Effros 二分定理（哈灵顿–凯克里斯–卢沃 1990）。福尔曼–鲁道夫–韦斯（2011）：遍历保测变换的同构关系不是博雷尔的，因此不存在“合理的”完全不变量。'] },
    { t: 'CT', h: ['Hilbert\'s 10th problem (MRDP)', '希尔伯特第十问题（MRDP）'], who: 'Davis, Putnam, Robinson 1961; Matiyasevich 1970', s: 'thm',
      m: ['Every c.e. set is Diophantine, so there is no algorithm deciding whether a polynomial equation has integer solutions. Side effect: statements like Con(ZFC) are equivalent to the unsolvability of one specific Diophantine equation.', '每个可计算枚举集都是丢番图集，所以不存在判定多项式方程是否有整数解的算法。副产品：像 Con(ZFC) 这样的命题等价于某个特定丢番图方程无解。'] },
    { t: 'CT', h: ['Computability in analysis & dynamics', '分析与动力系统中的可计算性'], who: 'Pour-El–Richards 1981; Braverman–Yampolsky 2006', s: 'thm',
      m: ['The 3D wave equation has computable initial data whose solution at a later time is not computable (Pour-El–Richards). Some quadratic Julia sets with computable parameters are not computable (Braverman–Yampolsky). Logic tells numerical analysts what no algorithm can do.', '三维波动方程存在可计算的初值，其在之后某时刻的解却不可计算（Pour-El–Richards）。某些参数可计算的二次朱利亚集本身不可计算（Braverman–Yampolsky）。逻辑告诉数值分析学家：哪些事情任何算法都做不到。'] },
    { t: 'PT', h: ['Reverse mathematics', '反推数学'], who: 'Friedman 1974; Simpson', s: 'thm',
      m: ['Over the weak base RCA₀: Heine–Borel ⇔ WKL₀; Bolzano–Weierstrass ⇔ ACA₀; Cantor–Bendixson ⇔ Π¹₁-CA₀. A precise answer to “which axioms does this theorem need?”.', '在弱基础系统 RCA₀ 上：海涅–博雷尔 ⇔ WKL₀；波尔查诺–魏尔斯特拉斯 ⇔ ACA₀；康托尔–本迪克松 ⇔ Π¹₁-CA₀。这精确回答了“这条定理需要哪些公理”。'] },
    { t: 'PT', h: ['Proof mining', '证明挖掘'], who: 'Kreisel (1950s); Kohlenbach (1990s–)', s: 'thm',
      m: ['Proof-theoretic interpretations extract explicit bounds and rates from non-constructive proofs in analysis: e.g. rates of metastability for ergodic averages (Avigad–Gerhardy–Towsner 2010) and many results in fixed-point theory and convex optimization.', '证明论的解释方法可以从分析中的非构造性证明里提取出显式的界和速率：例如遍历平均的亚稳定性速率（Avigad–Gerhardy–Towsner 2010），以及不动点理论和凸优化中的大量结果。'] },
    { t: 'PT', h: ['Formal verification', '形式化验证'], who: 'Coq 2005, 2012; Flyspeck 2014; Lean 2022', s: 'hist',
      m: ['Machine-checked proofs of the Four Colour Theorem (Gonthier, Coq, 2005), Feit–Thompson (Coq, 2012), the Kepler conjecture (Flyspeck, 2014), and a key theorem of condensed mathematics (Liquid Tensor Experiment, Lean, 2022). Logic supplies the formal systems these tools implement.', '四色定理（Gonthier，Coq，2005）、费特–汤普森定理（Coq，2012）、开普勒猜想（Flyspeck，2014）以及凝聚数学的一个关键定理（液态张量实验，Lean，2022）都已得到机器验证。这些工具所实现的形式系统正是由逻辑提供的。'] },
  ];
  let filter = null;
  const box = $('appCards');
  CARDS.forEach(c => {
    const d = document.createElement('div');
    const [en, zh, col] = TAGS[c.t];
    d.className = 'ocard';
    d.style.borderTop = `4px solid ${col}`;
    d.innerHTML = `<div class="sub" style="color:${col};font-weight:700">${bil(en, zh)}</div><div class="hd">${bi(c.h[0], c.h[1])}</div>
      <div class="sub">${c.who}</div><div class="more">${status(c.s)} ${bi(c.m[0], c.m[1])}</div>`;
    d.addEventListener('click', () => d.classList.toggle('open'));
    c.el = d;
    box.appendChild(d);
  });
  const fb = [];
  [[null, ['All', '全部']], ...Object.entries(TAGS).map(([k, v]) => [k, v])].forEach(([k, v]) => {
    const b = document.createElement('button');
    b.className = 'btn small' + (k === null ? ' sel' : '');
    b.innerHTML = bil(v[0], v[1]);
    b.addEventListener('click', () => {
      filter = k;
      fb.forEach(x => x.classList.toggle('sel', x === b));
      CARDS.forEach(c => c.el.classList.toggle('hide', filter !== null && c.t !== filter));
    });
    fb.push(b);
    $('appBtns').appendChild(b);
  });
})();

/* ================= §9 philosophy quiz ================= */
(function philosophy() {
  const POS = {
    P: { en: 'Platonism / realism', zh: '柏拉图主义／实在论', who: 'Gödel; many set theorists',
      core: ['Mathematical objects exist independently of us, and mathematical statements (including CH) have determinate truth values.', '数学对象独立于我们而存在，数学命题（包括 CH）都有确定的真值。'],
      ch: ['CH is true or false; we should look for well-justified new axioms to decide it (Gödel thought it false).', 'CH 非真即假；应当寻找有充分理由的新公理来判定它（哥德尔认为它是假的）。'],
      obj: ['How can we know about abstract objects we cannot causally interact with? (Benacerraf 1973)', '我们如何认识那些无法与之发生因果作用的抽象对象？（贝纳塞拉夫 1973）'] },
    F: { en: 'Formalism', zh: '形式主义', who: 'Hilbert (in a nuanced form), Curry',
      core: ['Mathematics is (at least largely) the study of formal systems and derivations. Hilbert himself treated finitary arithmetic as contentful and the rest as “ideal elements”.', '数学（至少在很大程度上）是对形式系统与推导的研究。希尔伯特本人把有穷算术看作有内容的，把其余部分看作“理想元素”。'],
      ch: ['CH is provable in some systems, refutable in others, and that is all there is to say.', 'CH 在某些系统中可证，在另一些系统中可驳，此外再无可说。'],
      obj: ['Gödel: no single system captures arithmetic. Why then does Con(PA) seem to have a definite truth value?', '哥德尔：没有哪个单一系统能把握算术。那为什么 Con(PA) 看起来有确定的真值？'] },
    I: { en: 'Intuitionism / constructivism', zh: '直觉主义／构造主义', who: 'Brouwer, Heyting, Bishop',
      core: ['Mathematics is mental construction. To prove ∃x P(x) you must construct x; excluded middle is not valid in general.', '数学是心智的构造。要证明 ∃x P(x)，必须构造出 x；排中律一般不成立。'],
      ch: ['CH, quantifying over arbitrary sets of reals, is not meaningful as a classical statement; constructive analogues can be studied.', 'CH 量化的是任意实数集合，作为经典命题它没有意义；可以研究它的构造性类比。'],
      obj: ['Some classical theorems must be weakened or reformulated. In return, proofs carry computational content.', '有些经典定理必须减弱或重新表述。作为回报，证明带有计算内容。'] },
    S: { en: 'Structuralism', zh: '结构主义', who: 'Benacerraf (1965), Resnik, Shapiro',
      core: ['Mathematics studies structures; objects are just positions in structures. “Is 2 = {∅, {∅}}?” is a bad question.', '数学研究的是结构；对象只是结构中的位置。“2 = {∅, {∅}} 吗？”是个不恰当的问题。'],
      ch: ['Depends on whether the structure of “all sets” is determinate. Zermelo (1930) showed second-order ZF determines its models up to the height of the universe.', '取决于“全体集合”的结构是否确定。策梅洛（1930）证明二阶 ZF 在宇宙“高度”之外唯一确定其模型。'],
      obj: ['What exactly is a structure, and does set theory itself have one intended structure?', '结构究竟是什么？集合论本身是否有唯一的预期结构？'] },
    M: { en: 'Multiverse view', zh: '多重宇宙观', who: 'Hamkins (2012)',
      core: ['There are many legitimate concepts of set, each realized in its own universe; forcing extensions are as real as the original.', '存在许多合法的集合概念，各自在其宇宙中实现；力迫扩张与原宇宙同样真实。'],
      ch: ['CH is “settled” in the sense that we know exactly how it behaves: it holds in some universes and fails in others.', 'CH 在这个意义上已“解决”：我们清楚它的表现，它在某些宇宙中成立，在另一些中不成立。'],
      obj: ['If set-theoretic truth varies, does arithmetic truth vary too? Critics worry about losing determinacy altogether.', '如果集合论的真会变化，算术的真是否也会变？批评者担心确定性会全面丧失。'] },
    N: { en: 'Naturalism', zh: '自然主义', who: 'Maddy (1997, 2011)',
      core: ['Mathematical methods are justified by mathematical practice and goals, not by external philosophy.', '数学方法由数学实践及其目标来辩护，而不靠外在的哲学。'],
      ch: ['Adopt axioms that best serve set theory\'s goals (unify, maximize, decide); then see what they say about CH.', '采用最能服务于集合论目标（统一、最大化、判定）的公理，然后看它们对 CH 怎么说。'],
      obj: ['Which goals count, and do they single out one answer to CH?', '哪些目标算数？它们能否挑出 CH 的唯一答案？'] },
  };
  const Q = [
    { q: ['Does CH have a definite truth value, even though ZFC cannot decide it?', '尽管 ZFC 判定不了 CH，CH 是否有确定的真值？'], o: [
      ['Yes: there is one universe of sets, and CH is true or false in it.', '有：只有一个集合宇宙，CH 在其中非真即假。', { P: 2 }],
      ['It depends on which universe of sets you are in; many are equally legitimate.', '这取决于你身处哪个集合宇宙；许多宇宙同样合法。', { M: 2 }],
      ['“True” only makes sense relative to a chosen formal system.', '“真”只有相对于选定的形式系统才有意义。', { F: 2 }],
      ['CH quantifies over arbitrary sets of reals, which cannot be surveyed constructively; the question is not well-posed as stated.', 'CH 量化的是任意实数集合，无法构造性地遍历；照原样提出这个问题并不恰当。', { I: 2 }],
      ['Let set-theoretic practice decide: adopt the axioms that best serve mathematics and see what they say.', '让集合论实践来决定：采用最有益于数学的公理，看它们怎么说。', { N: 2 }]] },
    { q: ['What is the number 3?', '数 3 是什么？'], o: [
      ['An abstract object that exists independently of us.', '一个独立于我们存在的抽象对象。', { P: 2 }],
      ['A position: whatever plays the role of “third successor of 0” in an ω-sequence.', '一个位置：在任何 ω-序列中扮演“0 的第三个后继”的那个东西。', { S: 2 }],
      ['The term SSS0, manipulated by formal rules.', '项 SSS0，按形式规则操作。', { F: 2 }],
      ['A mental construction: counting three times.', '一种心智构造：数三次。', { I: 2 }],
      ['It does not matter for doing mathematics; what matters is the role numbers play.', '这对做数学无关紧要；要紧的是数所扮演的角色。', { N: 1, S: 1 }]] },
    { q: ['You prove ∃x P(x) by contradiction, with no way to find x. Is that a proof of existence?', '你用反证法证明了 ∃x P(x)，但没有办法找到 x。这算存在性证明吗？'], o: [
      ['Yes, fully.', '算，完全算。', { P: 1, F: 1, S: 1, M: 1, N: 1 }],
      ['No: it proves ¬∀x ¬P(x), which is weaker; real existence needs a construction.', '不算：它只证明了 ¬∀x ¬P(x)，这更弱；真正的存在需要构造。', { I: 2 }]] },
    { q: ['How should a new axiom like “there is a measurable cardinal” be justified?', '像“存在可测基数”这样的新公理应当如何辩护？'], o: [
      ['By insight into the concept of set: it should be true of V.', '靠对集合概念的洞察：它应当在 V 中为真。', { P: 2 }],
      ['By its fruits: what it explains, unifies and lets us prove.', '靠它的成果：它能解释、统一、证明什么。', { N: 2, P: 1 }],
      ['No need to pick: explore the universes where it holds and where it fails.', '不必挑选：去探索它成立和不成立的各个宇宙。', { M: 2 }],
      ['As a rule of a game: it only needs to be consistent (which we cannot even prove).', '把它当作游戏规则：只要一致就行（而我们甚至无法证明这一点）。', { F: 2 }],
      ['It goes far beyond anything constructible, so it is not justified.', '它远远超出了任何可构造的东西，所以没有道理。', { I: 2 }]] },
    { q: ['Two structures are isomorphic. Are they “the same” mathematical object?', '两个结构同构。它们是“同一个”数学对象吗？'], o: [
      ['For all mathematical purposes, yes: mathematics is about structure.', '就一切数学目的而言，是的：数学研究的是结构。', { S: 2 }],
      ['No: e.g. {∅, {∅}} and {{∅}} are different sets, even if both can play the role of 2.', '不是：例如 {∅, {∅}} 与 {{∅}} 是不同的集合，尽管它们都能扮演 2 的角色。', { P: 1, F: 1 }],
      ['A good foundation should make equivalent things literally equal (as univalence does).', '好的基础应当让等价的东西真正相等（如泛等公理那样）。', { S: 1, I: 1 }]] },
  ];
  const MAX = {};
  Q.forEach(q => Object.keys(POS).forEach(k => { MAX[k] = (MAX[k] || 0) + Math.max(...q.o.map(o => o[2][k] || 0)); }));
  const ans = Q.map(() => null);
  const box = $('quiz');
  Q.forEach((q, i) => {
    const d = document.createElement('div');
    d.className = 'quizq';
    d.innerHTML = `<b>${i + 1}.</b> ${bil(q.q[0], q.q[1])}<div class="opts"></div>`;
    const bs = q.o.map((o, j) => {
      const b = document.createElement('button');
      b.className = 'btn small';
      b.innerHTML = bil(o[0], o[1]);
      b.addEventListener('click', () => { ans[i] = j; bs.forEach(x => x.classList.toggle('sel', x === b)); });
      d.querySelector('.opts').appendChild(b);
      return b;
    });
    q.bs = bs;
    box.appendChild(d);
  });
  function bars(score) {
    let h = '';
    Object.entries(POS).forEach(([k, p]) => {
      const pct = score ? Math.round(100 * (score[k] || 0) / MAX[k]) : 0;
      h += `<div>${bil(p.en, p.zh)}</div><div class="trk"><div class="bar" data-w="${pct}" style="width:0%"></div></div><div class="m">${score ? pct + '%' : ''}</div>`;
    });
    $('quizBars').innerHTML = h;
    requestAnimationFrame(() => requestAnimationFrame(() => $('quizBars').querySelectorAll('.bar').forEach(b => b.style.width = b.dataset.w + '%')));
  }
  $('quizGo').addEventListener('click', () => {
    const n = ans.filter(a => a !== null).length;
    if (n < Q.length) { okBox($('quizMsg'), bi(`Answer all questions first (${n}/${Q.length}).`, `请先回答全部问题（${n}/${Q.length}）。`), 'warn'); return; }
    const sc = {};
    ans.forEach((a, i) => Object.entries(Q[i].o[a][2]).forEach(([k, v]) => sc[k] = (sc[k] || 0) + v));
    bars(sc);
    const best = Object.keys(POS).sort((a, b) => (sc[b] || 0) / MAX[b] - (sc[a] || 0) / MAX[a])[0];
    okBox($('quizMsg'), bi(`Closest match: <b>${POS[best].en}</b>. Percentages are relative to the maximum each position can score. Real views are mixtures; read all six cards below, including the main objection to your own view.`,
      `最接近的立场：<b>${POS[best].zh}</b>。百分比是相对于每种立场可得的最高分计算的。真实的观点往往是混合的；请读完下面六张卡片，包括针对你自己立场的主要质疑。`), 'info');
    posCards.forEach(([k, el]) => el.classList.toggle('open', k === best));
  });
  $('quizReset').addEventListener('click', () => { ans.fill(null); Q.forEach(q => q.bs.forEach(b => b.classList.remove('sel'))); bars(null); clearBox($('quizMsg')); });
  bars(null);
  const posCards = Object.entries(POS).map(([k, p]) => {
    const d = document.createElement('div');
    d.className = 'ocard';
    d.innerHTML = `<div class="hd">${bi(p.en, p.zh)}</div><div class="sub">${p.who}</div>
      <div class="more">${status('phil')}<br><b>${bil('Core claim', '核心主张')}:</b> ${bi(p.core[0], p.core[1])}
      <br><b>${bil('On CH', '对 CH 的看法')}:</b> ${bi(p.ch[0], p.ch[1])}
      <br><b>${bil('Main challenge', '主要质疑')}:</b> ${bi(p.obj[0], p.obj[1])}</div>`;
    d.addEventListener('click', () => d.classList.toggle('open'));
    $('posCards').appendChild(d);
    return [k, d];
  });
})();

/* ================= §10 alternative foundations ================= */
(function alternatives() {
  const COLS = [
    ['Primitive notion', '原始概念'], ['Logic', '逻辑'], ['Motivation', '动机'], ['Equality', '相等'], ['Strength vs ZFC', '相对 ZFC 的强度'], ['In practice', '实际使用'],
  ];
  const ROWS = [
    { n: ['ZFC', 'ZFC'], c: [
      ['sets and ∈', '集合与 ∈'], ['classical first-order', '经典一阶逻辑'],
      ['block the paradoxes; one universe in which all mathematics can be encoded (Zermelo 1908; Fraenkel, Skolem 1922)', '堵住悖论；提供一个能编码全部数学的宇宙（策梅洛 1908；弗兰克尔、斯科伦 1922）'],
      ['extensional: same elements ⇒ same set', '外延的：元素相同 ⇒ 集合相同'],
      ['the reference point; extended by large cardinals', '参照基准；可用大基数加强'],
      ['standard reference for consistency questions; Mizar (Tarski–Grothendieck set theory)', '一致性问题的标准参照；Mizar（塔斯基–格罗滕迪克集合论）']] },
    { n: ['Type theory (simple; Martin-Löf; CIC)', '类型论（简单类型论；马丁–洛夫；CIC）'], c: [
      ['types and terms; every object has a type', '类型与项；每个对象都有类型'],
      ['Church\'s simple type theory (1940): classical higher-order; Martin-Löf (1970s): intuitionistic, propositions as types', '丘奇简单类型论（1940）：经典高阶逻辑；马丁–洛夫（1970 年代）：直觉主义，命题即类型'],
      ['avoid paradoxes by typing (Russell 1908); proofs as programs (Curry–Howard)', '用类型避免悖论（罗素 1908）；证明即程序（柯里–霍华德）'],
      ['identity types (intensional) or definitional equality', '恒等类型（内涵的）或定义相等'],
      ['higher-order logic is weaker than ZFC (Zermelo-like); Carneiro (2019, for Lean 3) argued that Lean\'s type theory is consistent relative to ZFC + “there are n inaccessible cardinals” for every n (optimal, since Lean interprets each of these); an error was later found in that thesis (see Tao, Oct 2026); Carneiro has described an alternative route that avoids it, but it has not yet been written out in full, and the related Con-Leche project formally verifies a closely related consistency claim', '高阶逻辑比 ZFC 弱（与策梅洛式集合论相当）；卡内罗（2019，针对 Lean 3）论证了 Lean 的类型论相对于“ZFC + 存在 n 个不可达基数”（对每个 n）一致，且这是最优的（Lean 能解释其中每一个理论）；后来该论文被发现有一处错误（见陶哲轩 2026 年 10 月的博文）；卡内罗称存在绕开该错误的另一条论证路线，但尚未完整成文；相关的 Con-Leche 项目则对一个密切相关的一致性命题做了形式化验证'],
      ['Isabelle/HOL, HOL Light; Coq/Rocq, Lean, Agda', 'Isabelle/HOL、HOL Light；Coq/Rocq、Lean、Agda']] },
    { n: ['Category-theoretic (ETCS, topoi)', '范畴论基础（ETCS、拓扑斯）'], c: [
      ['objects and morphisms (functions)', '对象与态射（函数）'],
      ['ETCS classical; a general elementary topos has intuitionistic internal logic', 'ETCS 是经典的；一般的初等拓扑斯具有直觉主义的内部逻辑'],
      ['mathematics is about structure and maps (Lawvere, ETCS 1964); topoi (Grothendieck; Lawvere–Tierney c. 1970) unify sets, sheaves and forcing-style models', '数学研究结构与映射（劳维尔，ETCS 1964）；拓扑斯（格罗滕迪克；劳维尔–蒂尔尼 约 1970）统一了集合、层与力迫式模型'],
      ['isomorphism-invariant practice; elements have no internal ∈-structure', '同构不变的实践；元素没有内部的 ∈ 结构'],
      ['ETCS ≈ bounded Zermelo set theory with choice; ETCS + a replacement axiom ≈ ZFC', 'ETCS ≈ 带选择的有界策梅洛集合论；ETCS + 替换公理 ≈ ZFC'],
      ['working framework in algebraic geometry and topology; categorical logic', '代数几何与拓扑中的工作框架；范畴逻辑']] },
    { n: ['HoTT / univalent foundations', 'HoTT／泛等基础'], c: [
      ['types as homotopy types (spaces); identities as paths', '类型即同伦类型（空间）；恒等即道路'],
      ['intuitionistic core; excluded middle and choice for propositions can be added consistently', '直觉主义内核；可一致地加入针对命题的排中律与选择公理'],
      ['equivalent structures should be equal; reliable computer formalization (Voevodsky)', '等价的结构应当相等；可靠的计算机形式化（沃沃茨基）'],
      ['univalence: (A = B) ≃ (A ≃ B)', '泛等公理：(A = B) ≃ (A ≃ B)'],
      ['simplicial-set model in ZFC plus inaccessible cardinals (Voevodsky; Kapulkin–Lumsdaine)', '在 ZFC 加不可达基数中有单纯集模型（沃沃茨基；Kapulkin–Lumsdaine）'],
      ['Coq UniMath, Agda (cubical), the HoTT book (2013)', 'Coq UniMath、Agda（立方类型论）、HoTT 之书（2013）']] },
    { n: ['Bishop-style constructive mathematics', '毕晓普式构造性数学'], c: [
      ['constructions / algorithms (informal)', '构造／算法（非形式）'],
      ['intuitionistic', '直觉主义逻辑'],
      ['every theorem should have computational content (Bishop 1967)', '每个定理都应当有计算内容（毕晓普 1967）'],
      ['each set comes with its own equality relation', '每个集合自带其相等关系'],
      ['formalizable in weak systems (e.g. Aczel\'s CZF, Martin-Löf type theory); all theorems classically valid', '可在弱系统中形式化（如阿克泽尔的 CZF、马丁–洛夫类型论）；所有定理在经典意义下成立'],
      ['constructive analysis, program extraction', '构造性分析、程序提取']] },
  ];
  let rowSel = -1, colSel = -1;
  const tab = $('altTab');
  function render() {
    let h = `<tr><th>${bil('Foundation', '基础')}</th>${COLS.map((c, j) => `<th style="${j === colSel ? 'background:#e7ecff' : ''}">${bi(c[0], c[1])}</th>`).join('')}</tr>`;
    ROWS.forEach((r, i) => {
      h += `<tr class="${i === rowSel ? 'hl' : ''}"><td class="rowh" data-r="${i}" style="cursor:pointer">${r.n[0] === r.n[1] ? r.n[0] : bi(r.n[0], r.n[1])}</td>`;
      r.c.forEach((c, j) => { h += `<td style="${j === colSel ? 'background:#e7ecff' : ''}">${bi(c[0], c[1])}</td>`; });
      h += '</tr>';
    });
    tab.innerHTML = h;
    tab.querySelectorAll('td.rowh').forEach(td => td.addEventListener('click', () => { rowSel = +td.dataset.r === rowSel ? -1 : +td.dataset.r; render(); }));
  }
  const NOTES = [
    ['Primitive notion: what the foundation takes as basic. ZFC builds everything (functions, numbers, spaces) out of sets; type theory and category theory take functions or typed terms as basic.', '原始概念：基础把什么当作最基本的东西。ZFC 用集合构造一切（函数、数、空间）；类型论与范畴论则以函数或带类型的项为基本概念。'],
    ['Logic: classical vs intuitionistic. Intuitionistic foundations do not assume P ∨ ¬P in general, which is why proofs there carry algorithms.', '逻辑：经典的还是直觉主义的。直觉主义基础一般不假定 P ∨ ¬P，所以其中的证明带有算法。'],
    ['Motivation: each foundation answers a different worry: paradoxes (ZFC, types), structure (categories), invariance and formalization (HoTT), computation (Bishop).', '动机：每种基础回应的担忧不同：悖论（ZFC、类型论）、结构（范畴论）、不变性与形式化（HoTT）、计算（毕晓普）。'],
    ['Equality: in ZFC, equality is extensional; in HoTT, equality of types is equivalence, so isomorphism invariance is built in.', '相等：在 ZFC 中相等是外延的；在 HoTT 中类型的相等就是等价，同构不变性因此是内建的。'],
    ['Strength: these foundations are compared by mutual interpretations and consistency strength. None is “more correct”; they differ in strength and convenience.', '强度：这些基础通过相互解释与一致性强度来比较。没有哪个“更正确”；它们的差别在于强度与便利性。'],
    ['Practice: everyday mathematicians rarely notice the foundation; proof assistants force a choice, which revived interest in type theory.', '实践：日常做数学的人很少察觉到基础的存在；证明助手却必须做出选择，这使人们重新关注类型论。'],
  ];
  COLS.forEach((c, j) => {
    const b = document.createElement('button');
    b.className = 'btn small';
    b.innerHTML = bil(c[0], c[1]);
    b.addEventListener('click', () => { colSel = colSel === j ? -1 : j; $('altCols').querySelectorAll('.btn').forEach((x, k) => x.classList.toggle('sel', k === colSel)); render(); if (colSel >= 0) okBox($('altInfo'), bi(NOTES[j][0], NOTES[j][1]), 'info'); else clearBox($('altInfo')); });
    $('altCols').appendChild(b);
  });
  render();
})();

/* ================= §11 frontier ================= */
(function frontier() {
  const F = [
    { h: ['Set theory → L27', '集合论 → 第 27 课'], c: '#2f9e44', q: [
      ['Which well-justified axioms decide 2^ℵ₀?', '哪些有充分理由的公理能判定 2^ℵ₀？', 'open', 'Forcing axioms (MM, PFA) imply 2^ℵ₀ = ℵ₂ (Foreman–Magidor–Shelah 1988; Todorcevic, Veličković); Woodin\'s Ultimate L program points towards CH.', '力迫公理（MM、PFA）推出 2^ℵ₀ = ℵ₂（福尔曼–马吉多尔–谢拉赫 1988；托多尔切维奇、韦利奇科维奇）；伍丁的终极 L 纲领则指向 CH 成立。'],
      ['Ultimate L conjecture', '终极 L 猜想', 'open', 'Woodin: there should be an L-like inner model compatible with all large cardinals (a precise conjecture formulated around 2010).', '伍丁：应当存在一个与所有大基数相容的、类似 L 的内模型（约 2010 年提出精确的猜想）。'],
      ['HOD conjecture', 'HOD 猜想', 'open', 'Woodin proved the HOD dichotomy (a theorem): above an extendible cardinal, HOD is either very close to V or very far from it. The (open) HOD conjecture says “close”.', '伍丁证明了 HOD 二分定理（已证定理）：在可扩基数之上，HOD 要么非常接近 V，要么离 V 非常远。（未解决的）HOD 猜想断言是“接近”。'],
      ['Inner models for supercompact cardinals', '超紧基数的内模型', 'prog', 'The inner model program has canonical models up to roughly Woodin limits of Woodin cardinals; supercompacts remain the big target.', '内模型纲领已经构造出大约到“伍丁基数的伍丁极限”的典范模型；超紧基数仍是重大目标。'],
      ['pcf: Shelah\'s bound on 2^ℵ_ω', 'pcf：谢拉赫对 2^ℵ_ω 的上界', 'open', 'If ℵ_ω is a strong limit, 2^ℵ_ω < ℵ_{ω₄} (Shelah). Can ω₄ be lowered to ω₁?', '若 ℵ_ω 是强极限，则 2^ℵ_ω < ℵ_{ω₄}（谢拉赫）。ω₄ 能否降到 ω₁？']] },
    { h: ['Model theory → L28', '模型论 → 第 28 课'], c: '#3b5bdb', q: [
      ['Classification beyond stability (NIP, simple, NTP₂)', '稳定性之外的分类（NIP、简单、NTP₂）', 'prog', '“Neostability”: extend Shelah\'s dividing lines to wider classes, with applications in combinatorics and valued fields.', '“新稳定性”：把谢拉赫的分界线推广到更广的理论类，并应用于组合学与赋值域。'],
      ['Zilber\'s quasiminimality conjecture', '齐尔伯拟极小性猜想', 'open', 'Is every subset of ℂ definable in (ℂ, +, ×, exp) countable or co-countable?', '在 (ℂ, +, ×, exp) 中可定义的 ℂ 的子集是否都可数或余可数？'],
      ['Decidability of the real exponential field', '实指数域的可判定性', 'open', 'Macintyre–Wilkie (1996): decidable if Schanuel\'s conjecture holds. Unconditionally open.', 'Macintyre–Wilkie（1996）：若 Schanuel 猜想成立则可判定。无条件情形未解决。'],
      ['Unlikely intersections (Zilber–Pink)', '非预期相交（齐尔伯–平克）', 'open', 'A vast generalization of André–Oort; o-minimal counting is a key tool.', '安德烈–奥尔特猜想的宏大推广；o-极小计数是关键工具。']] },
    { h: ['Computability → L28', '可计算性 → 第 28 课'], c: '#f08c00', q: [
      ['Martin\'s conjecture', '马丁猜想', 'open', 'Under AD, Turing-invariant functions should be classified by iterates of the jump; special cases are proved.', '在 AD 下，图灵不变函数应当可由跳跃的迭代分类；部分特例已被证明。'],
      ['Rigidity of the Turing degrees', '图灵度的刚性', 'open', 'Does the partial order of all Turing degrees have a nontrivial automorphism?', '全体图灵度构成的偏序是否有非平凡自同构？'],
      ['Reverse mathematics of combinatorics', '组合学的反推数学', 'prog', 'Ramsey\'s theorem for pairs and its relatives have surprising strengths (Seetapun 1995; Cholak–Jockusch–Slaman 2001; Liu 2012).', '二元拉姆齐定理及其变体有出人意料的强度（Seetapun 1995；Cholak–Jockusch–Slaman 2001；刘路 2012）。'],
      ['Algorithmic randomness and geometry', '算法随机性与几何', 'prog', 'The point-to-set principle (J. Lutz–N. Lutz 2018) turns Hausdorff dimension into Kolmogorov complexity, yielding new results in fractal geometry.', '点到集原理（J. Lutz–N. Lutz 2018）把豪斯多夫维数转化为柯尔莫哥洛夫复杂度，在分形几何中得到了新结果。']] },
    { h: ['Proof theory → L28', '证明论 → 第 28 课'], c: '#ae3ec9', q: [
      ['Ordinal analysis of stronger theories', '更强理论的序数分析', 'prog', 'Ordinal analyses reach somewhat beyond Π¹₁-CA₀; full second-order arithmetic (let alone ZFC) remains out of reach.', '序数分析已经稍稍超出 Π¹₁-CA₀；完整的二阶算术（更不用说 ZFC）仍遥不可及。'],
      ['Proof complexity and NP vs coNP', '证明复杂度与 NP 对 coNP', 'open', 'Cook–Reckhow (1979): NP = coNP iff some propositional proof system has polynomial-size proofs of all tautologies.', 'Cook–Reckhow（1979）：NP = coNP 当且仅当存在某个命题证明系统，所有重言式在其中都有多项式长度的证明。'],
      ['Proof mining & formalization at scale', '大规模证明挖掘与形式化', 'prog', 'Extracting bounds systematically, and making large formal libraries and automated provers reliable.', '系统地提取界，并让大型形式化库与自动证明器可靠可用。']] },
    { h: ['Foundations & type theory → L28', '基础与类型论 → 第 28 课'], c: '#0c8599', q: [
      ['Computational univalence', '泛等公理的计算解释', 'thm', 'Cubical type theory (Cohen–Coquand–Huber–Mörtberg, 2015/18) gives univalence computational meaning.', '立方类型论（Cohen–Coquand–Huber–Mörtberg，2015/18）赋予泛等公理以计算意义。'],
      ['Semi-simplicial types in book HoTT', 'HoTT 中的半单纯类型', 'open', 'Can the infinite tower of semi-simplicial types be defined internally? A well-known open problem.', '半单纯类型的无穷塔能否在内部定义？一个著名的未解决问题。'],
      ['Is ZFC consistent?', 'ZFC 是一致的吗？', 'phil', 'Unprovable in ZFC if true (Gödel II); belief rests on evidence. Separate from all the mathematical problems above.', '若为真，则在 ZFC 中不可证（哥德尔第二定理）；人们的信念基于证据。它与上面所有数学问题性质不同。']] },
  ];
  const box = $('frontier');
  F.forEach(f => {
    const d = document.createElement('div');
    d.className = 'fcol';
    d.style.borderColor = f.c;
    d.innerHTML = `<h4 style="color:${f.c}">${bi(f.h[0], f.h[1])}</h4>`;
    f.q.forEach(q => {
      const x = document.createElement('div');
      x.className = 'fq';
      x.innerHTML = `${status(q[2])} ${bil(q[0], q[1])}<div class="more">${bi(q[3], q[4])}</div>`;
      x.addEventListener('click', () => x.classList.toggle('open'));
      d.appendChild(x);
    });
    box.appendChild(d);
  });
})();

/* ================= exercises: shared match helper ================= */
function matchExercise({ list, items, options, check, show, msg, prog, okText, hint }) {
  let revealed = false;
  const sels = items.map(it => {
    const row = document.createElement('div');
    row.className = 'matchrow';
    row.innerHTML = `<div class="cond">${it.h}</div>`;
    const s = document.createElement('select');
    s.innerHTML = `<option value="">— choose / 请选择 —</option>` +
      options.map((o, j) => `<option value="${j}">${o}</option>`).join('');
    s.addEventListener('change', () => { s.classList.remove('right', 'wrong'); });
    row.appendChild(s);
    $(list).appendChild(row);
    return s;
  });
  $(check).addEventListener('click', () => {
    let ok = 0;
    sels.forEach((s, i) => {
      s.classList.remove('right', 'wrong');
      if (s.value === '') return;
      if (+s.value === items[i].a) { ok++; s.classList.add('right'); } else s.classList.add('wrong');
    });
    if (ok === items.length) {
      if (revealed) { okBox($(msg), bi('All correct, but the answers were shown earlier in this session, so this is not counted. Reload the page to try again from scratch.', '全对，但本次访问中已经显示过答案，所以不计入。刷新页面后可重新作答。') + ' ' + okText, 'info'); return; }
      okBox($(msg), '✓ ' + okText); Progress.mark(prog);
    }
    else okBox($(msg), bi(`${ok} / ${items.length} correct. Red ones are wrong. `, `答对 ${ok} / ${items.length}，红色的不对。`) + (hint || ''), 'warn');
  });
  $(show).addEventListener('click', () => {
    revealed = true;
    sels.forEach((s, i) => { s.value = items[i].a; s.classList.remove('wrong'); s.classList.add('right'); });
    okBox($(msg), bi('Answers filled in (this does not count as solved). ', '已填入答案（不计为完成）。') + okText, 'info');
  });
}
// <option> cannot contain HTML; use "English / 中文".
const opt = (en, zh) => `${en} / ${zh}`;

/* E1 people */
(function e1() {
  const O = [
    opt('diagonal method, |X| < |P(X)| (1891)', '对角线方法 |X| < |P(X)|（1891）'),
    opt('well-ordering theorem from AC (1904)', '由选择公理证明良序定理（1904）'),
    opt('incompleteness theorems (1931)', '不完全性定理（1931）'),
    opt('consistency of PA via ε₀ (1936)', '经 ε₀ 证明 PA 的一致性（1936）'),
    opt('halting problem undecidable (1936)', '停机问题不可判定（1936）'),
    opt('undefinability of truth (1933)', '真的不可定义性（1933）'),
    opt('forcing; CH independent of ZFC (1963)', '力迫法；CH 独立于 ZFC（1963）'),
    opt('Hilbert\'s 10th problem unsolvable (1970)', '希尔伯特第十问题不可解（1970）'),
    opt('Borel determinacy (1975)', '博雷尔决定性（1975）'),
    opt('Whitehead\'s problem independent (1974)', '怀特海问题独立（1974）'),
    opt('CH independent of ZFC (1938)', 'CH 独立于 ZFC（1938）'),
    opt('Borel determinacy (1963)', '博雷尔决定性（1963）'),
  ];
  const P = [['Cantor', '康托尔', 0], ['Zermelo', '策梅洛', 1], ['Gödel', '哥德尔', 2], ['Gentzen', '根岑', 3], ['Turing', '图灵', 4], ['Tarski', '塔斯基', 5], ['Cohen', '科恩', 6], ['Matiyasevich', '马季亚谢维奇', 7], ['D. A. Martin', 'D. A. 马丁', 8], ['Shelah', '谢拉赫', 9]];
  matchExercise({ list: 'e1List', items: P.map(p => ({ h: bil(p[0], p[1]), a: p[2] })), options: O, check: 'e1Check', show: 'e1Show', msg: 'e1Msg', prog: 'L26E1',
    okText: bi('Note the traps: Gödel (1938) proved only that CH is <i>consistent</i>; independence needed Cohen (1963). Martin\'s Borel determinacy is 1975.', '注意陷阱：哥德尔（1938）只证明了 CH 是<i>一致的</i>；独立性要等到科恩（1963）。马丁的博雷尔决定性是 1975 年。'),
    hint: bi('Watch the dates: two options are deliberate traps.', '留意年代：有两个选项是故意设置的陷阱。') });
})();

/* E2 order */
(function e2() {
  const EV = [
    [1891, 'Cantor\'s diagonal argument', '康托尔对角线论证'],
    [1901, 'Russell\'s paradox', '罗素悖论'],
    [1908, 'Zermelo\'s axioms', '策梅洛公理'],
    [1931, 'Gödel\'s incompleteness theorems', '哥德尔不完全性定理'],
    [1936, 'Turing: the halting problem', '图灵：停机问题'],
    [1938, 'Gödel\'s constructible universe L', '哥德尔可构成宇宙 L'],
    [1963, 'Cohen\'s forcing', '科恩力迫法'],
    [1970, 'Matiyasevich completes MRDP', '马季亚谢维奇完成 MRDP'],
    [1975, 'Martin: Borel determinacy', '马丁：博雷尔决定性'],
    [2013, 'The HoTT book', 'HoTT 之书'],
  ];
  let cur = shuffle(EV.map((_, i) => i));
  let revealed = false;
  function render() {
    const box = $('e2List');
    box.innerHTML = '';
    cur.forEach((k, pos) => {
      const d = document.createElement('div');
      d.className = 'chip';
      d.innerHTML = `<span class="num">${pos + 1}</span><span class="sp">${bil(EV[k][1], EV[k][2])}${revealed ? ` <span class="m muted">(${EV[k][0]})</span>` : ''}</span>`;
      const up = document.createElement('button'); up.textContent = '▲';
      const dn = document.createElement('button'); dn.textContent = '▼';
      up.addEventListener('click', () => { if (pos > 0) { [cur[pos - 1], cur[pos]] = [cur[pos], cur[pos - 1]]; render(); } });
      dn.addEventListener('click', () => { if (pos < cur.length - 1) { [cur[pos + 1], cur[pos]] = [cur[pos], cur[pos + 1]]; render(); } });
      d.append(up, dn);
      box.appendChild(d);
    });
  }
  $('e2Check').addEventListener('click', () => {
    const chips = $('e2List').querySelectorAll('.chip');
    let ok = 0;
    cur.forEach((k, pos) => { const r = k === pos; if (r) ok++; chips[pos].classList.toggle('ok', r); chips[pos].classList.toggle('no', !r); });
    if (ok === EV.length) {
      if (revealed) { okBox($('e2Msg'), bi('Correct order, but the answer was shown earlier in this session, so it is not counted. Reload the page to try again from scratch.', '顺序正确，但本次访问中已经显示过答案，所以不计入。刷新页面后可重新作答。'), 'info'); return; }
      Progress.mark('L26E2');
      okBox($('e2Msg'), bi('✓ Correct order. Notice the rhythm: paradox (1901) → axioms (1908) → limits (1931, 1936) → independence (1938, 1963).', '✓ 顺序正确。注意节奏：悖论（1901）→ 公理（1908）→ 极限（1931、1936）→ 独立性（1938、1963）。'));
    } else okBox($('e2Msg'), bi(`${ok} / ${EV.length} in the right position (green).`, `${ok} / ${EV.length} 个位置正确（绿色）。`), 'warn');
  });
  $('e2Shuffle').addEventListener('click', () => { cur = shuffle(cur); clearBox($('e2Msg')); render(); });
  $('e2Show').addEventListener('click', () => {
    revealed = true; cur = EV.map((_, i) => i); render();
    okBox($('e2Msg'), bi('Correct order shown with years (not counted as solved in this session).', '已显示正确顺序及年代（本次访问中不再计为完成）。'), 'info');
  });
  render();
})();

/* E3 bridges */
(function e3() {
  const O = [
    opt('Proof theory ↔ Model theory', '证明论 ↔ 模型论'),
    opt('Model theory ↔ Set theory', '模型论 ↔ 集合论'),
    opt('Proof theory ↔ Computability', '证明论 ↔ 可计算性'),
    opt('Proof theory ↔ Set theory (ordinals)', '证明论 ↔ 集合论（序数）'),
    opt('Computability ↔ Set theory (descriptive)', '可计算性 ↔ 集合论（描述集合论）'),
    opt('Model theory ↔ Computability', '模型论 ↔ 可计算性'),
  ];
  const I = [
    ['Gödel\'s completeness theorem', '哥德尔完备性定理', 0],
    ['Forcing recast as Boolean-valued models', '把力迫法改写为布尔值模型', 1],
    ['A complete, consistent, effectively axiomatized extension of arithmetic would decide the halting problem', '算术的一个完全、一致、能行公理化的扩张将能判定停机问题', 2],
    ['The proof-theoretic ordinal of PA is ε₀', 'PA 的证明论序数是 ε₀', 3],
    ['Δ¹₁ = hyperarithmetic (Kleene), whose boldface version is the Borel sets', 'Δ¹₁ = 超算术集（克莱尼），其粗体版本就是博雷尔集', 4],
    ['Real closed fields: quantifier elimination and decidability (Tarski)', '实闭域：量词消去与可判定性（塔斯基）', 5],
    ['Weakly compact cardinals characterized by compactness of L_{κ,κ}', '用 L_{κ,κ} 的紧致性刻画弱紧基数', 1],
  ];
  matchExercise({ list: 'e3List', items: I.map(x => ({ h: bil(x[0], x[1]), a: x[2] })), options: O, check: 'e3Check', show: 'e3Show', msg: 'e3Msg', prog: 'L26E3',
    okText: bi('Revisit §3: each of these is an edge of the pillar map.', '回看 §3：这些都是支柱图上的连线。'),
    hint: bi('Ask: which two kinds of objects does the theorem relate (proofs, models, algorithms, sets/ordinals, definable sets of reals)?', '问自己：这个定理把哪两类对象联系起来（证明、模型、算法、集合／序数、可定义实数集）？') });
})();

/* E4 misconceptions */
(function e4() {
  const S = [
    ['Gödel showed that mathematics is inconsistent.', '哥德尔证明了数学是矛盾的。', false, 'He showed a consistent system (with enough arithmetic, effectively axiomatized) cannot prove its own consistency, and is incomplete. Nothing about inconsistency.', '他证明的是：一致的系统（能行公理化且含足够算术）不能证明自身一致，而且是不完全的。与“矛盾”毫无关系。'],
    ['Gödel\'s theorem shows some true statements can never be proved by any means.', '哥德尔定理表明，有些真命题用任何方法都永远证明不了。', false, 'Unprovability is relative to a fixed theory T. The Gödel sentence of PA is provable in ZFC; ZFC has its own Gödel sentence, provable in a stronger theory, and so on.', '不可证是相对于某个固定理论 T 而言的。PA 的哥德尔语句在 ZFC 中可证；ZFC 也有自己的哥德尔语句，可在更强的理论中证明，依此类推。'],
    ['Since CH is independent of ZFC, CH is meaningless.', '既然 CH 独立于 ZFC，CH 就没有意义。', false, 'Independence is a theorem about ZFC. Whether CH is meaningful is a philosophical position (§9); many set theorists think it has a definite answer.', '独立性是关于 ZFC 的定理。CH 是否有意义是哲学立场问题（§9）；许多集合论学家认为它有确定的答案。'],
    ['The completeness and the first incompleteness theorem contradict each other.', '完备性定理与第一不完全性定理相互矛盾。', false, '“Complete logic” (⊢ = ⊨) vs “complete theory” (decides every sentence). A Gödel sentence is true in some models of PA and false in others.', '“逻辑完备”（⊢ = ⊨）与“理论完全”（判定每个语句）是两回事。哥德尔语句在 PA 的某些模型中为真，在另一些中为假。'],
    ['Russell\'s paradox shows that unrestricted comprehension is inconsistent.', '罗素悖论表明不受限制的概括原则是矛盾的。', true, 'Yes: {x : x ∉ x} cannot be a set. ZF uses Separation instead.', '对：{x : x ∉ x} 不能是集合。ZF 改用分离公理。'],
    ['Cohen proved that CH is false.', '科恩证明了 CH 是假的。', false, 'Cohen proved ¬CH is consistent with ZFC (if ZFC is consistent). Together with Gödel, CH is independent.', '科恩证明的是 ¬CH 与 ZFC 一致（若 ZFC 一致）。结合哥德尔的结果，CH 是独立的。'],
    ['Goodstein\'s theorem is independent of PA but provable in ZFC.', '古德斯坦定理独立于 PA，但在 ZFC 中可证。', true, 'Kirby–Paris (1982); the ZFC proof uses ordinals below ε₀.', 'Kirby–Paris（1982）；ZFC 中的证明用到小于 ε₀ 的序数。'],
    ['The large cardinal axioms known today settle CH.', '如今已知的大基数公理能判定 CH。', false, 'Lévy–Solovay (1967): small forcing preserves them and can make CH true or false.', '列维–索洛韦（1967）：小力迫保持这些大基数，同时能使 CH 为真或为假。'],
    ['There is no algorithm deciding whether a Diophantine equation has an integer solution.', '不存在判定丢番图方程是否有整数解的算法。', true, 'MRDP (Davis, Putnam, Robinson, Matiyasevich 1970).', 'MRDP 定理（戴维斯、普特南、罗宾逊、马季亚谢维奇 1970）。'],
    ['Bishop-style constructive mathematics proves theorems that are false classically.', '毕晓普式构造性数学证明了一些在经典意义下为假的定理。', false, 'Bishop\'s mathematics is compatible with classical mathematics; Brouwer\'s intuitionism (with continuity principles) is the one that contradicts it.', '毕晓普的数学与经典数学相容；与经典数学矛盾的是（带连续性原则的）布劳威尔直觉主义。'],
  ];
  const solved = S.map(() => false);
  let revealed = false;
  S.forEach((s, i) => {
    const row = document.createElement('div');
    row.className = 'tfrow';
    row.innerHTML = `<div class="stmt">${bil(s[0], s[1])}</div>`;
    const m = document.createElement('div');
    m.className = 'msg';
    const mk = (v, en, zh) => {
      const b = document.createElement('button');
      b.className = 'btn small';
      b.innerHTML = bil(en, zh);
      b.addEventListener('click', () => {
        const ok = v === s[2];
        tb.classList.remove('right', 'wrongc'); fb.classList.remove('right', 'wrongc');
        b.classList.add(ok ? 'right' : 'wrongc');
        okBox(m, (ok ? '✓ ' : '✗ ') + bi(s[3], s[4]), ok ? 'ok' : 'bad');
        if (ok && !revealed) { solved[i] = true; if (solved.every(Boolean)) { Progress.mark('L26E4'); okBox($('e4Msg'), bi('✓ All ten answered correctly.', '✓ 十题全部答对。')); } }
      });
      return b;
    };
    const tb = mk(true, 'True', '对'), fb = mk(false, 'False', '错');
    row.append(tb, fb, m);
    s.show = () => { (s[2] ? tb : fb).classList.add('right'); okBox(m, bi((s[2] ? '<b>True.</b> ' : '<b>False.</b> ') + s[3], (s[2] ? '<b>对。</b>' : '<b>错。</b>') + s[4]), 'info'); };
    $('e4List').appendChild(row);
  });
  $('e4Show').addEventListener('click', () => { revealed = true; S.forEach(s => s.show()); okBox($('e4Msg'), bi('All answers shown (not counted as solved).', '已显示全部答案（不计为完成）。'), 'info'); });
})();

/* E5 status */
(function e5() {
  const O = [opt('theorem (proved)', '定理（已证明）'), opt('independent of the stated theory', '独立于所给理论'), opt('open problem', '未解决问题'), opt('philosophical position', '哲学立场')];
  const I = [
    ['ZFC proves every Borel game on ω is determined.', 'ZFC 证明 ω 上每个博雷尔博弈都是决定的。', 0],
    ['CH, relative to ZFC.', 'CH，相对于 ZFC。', 1],
    ['CH has a determinate truth value.', 'CH 有确定的真值。', 3],
    ['Martin\'s conjecture on Turing-invariant functions.', '关于图灵不变函数的马丁猜想。', 2],
    ['PA does not prove Con(PA).', 'PA 不能证明 Con(PA)。', 0],
    ['PD, relative to ZFC (assuming large cardinals are consistent).', 'PD，相对于 ZFC（假定大基数一致）。', 1],
    ['Mathematics is about structures, not objects.', '数学研究的是结构，而不是对象。', 3],
    ['Zilber\'s quasiminimality conjecture for (ℂ, +, ×, exp).', '关于 (ℂ, +, ×, exp) 的齐尔伯拟极小性猜想。', 2],
    ['The axiom of choice, relative to ZF.', '选择公理，相对于 ZF。', 1],
    ['The Ultimate L conjecture.', '终极 L 猜想。', 2],
  ];
  matchExercise({ list: 'e5List', items: I.map(x => ({ h: bil(x[0], x[1]), a: x[2] })), options: O, check: 'e5Check', show: 'e5Show', msg: 'e5Msg', prog: 'L26E5',
    okText: bi('Keep the four labels apart: a theorem is proved; independence is a <i>proved</i> fact about a theory; open means nobody knows; a position is philosophy.', '把四种标签分清：定理是已证明的；独立性是关于某个理论的<i>已证明</i>事实；未解决意味着无人知道；立场属于哲学。'),
    hint: bi('“Independent” is itself a theorem about a theory, so it is not the same as “open”.', '“独立”本身就是关于某个理论的定理，所以它不同于“未解决”。') });
})();

/* E6 subfield */
(function e6() {
  const O = [opt('Set theory', '集合论'), opt('Model theory', '模型论'), opt('Computability theory', '可计算性理论'), opt('Proof theory', '证明论'), opt('Type theory / foundations', '类型论／基础')];
  const I = [
    ['Is 2^ℵ₀ = ℵ₂ under the right new axioms?', '在合适的新公理下 2^ℵ₀ = ℵ₂ 吗？', 0],
    ['Classify the theories without the independence property (NIP).', '对没有独立性质的理论（NIP）进行分类。', 1],
    ['Does the partial order of Turing degrees have a nontrivial automorphism?', '图灵度构成的偏序是否有非平凡自同构？', 2],
    ['What is the proof-theoretic ordinal of a stronger subsystem of second-order arithmetic?', '二阶算术中某个更强子系统的证明论序数是什么？', 3],
    ['Give univalence a computational interpretation.', '为泛等公理给出计算解释。', 4],
    ['Is the real exponential field decidable, unconditionally?', '实指数域是否（无条件地）可判定？', 1],
    ['Is there a canonical inner model with a supercompact cardinal?', '是否存在含超紧基数的典范内模型？', 0],
    ['Extract an explicit convergence rate from a non-constructive proof in analysis.', '从分析中的非构造性证明里提取显式的收敛速率。', 3],
  ];
  matchExercise({ list: 'e6List', items: I.map(x => ({ h: bil(x[0], x[1]), a: x[2] })), options: O, check: 'e6Check', show: 'e6Show', msg: 'e6Msg', prog: 'L26E6',
    okText: bi('These are exactly the questions L27 and L28 unpack.', '这些正是第 27、28 课要展开的问题。'),
    hint: bi('Decidability of a specific structure\'s theory is model theory; proof mining is proof theory.', '某个具体结构的理论是否可判定属于模型论；证明挖掘属于证明论。') });
})();
