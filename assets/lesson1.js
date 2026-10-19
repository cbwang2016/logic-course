// Lesson 1 interactions.
Lang.init();
Progress.paint();

const $ = id => document.getElementById(id);
const errBox = (box, e) => { box.className = 'msg bad'; box.innerHTML = e instanceof ParseError ? e.html() : String(e); };
const okBox = (box, html, kind = 'ok') => { box.className = 'msg ' + kind; box.innerHTML = html; };
const clearBox = box => { box.className = 'msg'; box.innerHTML = ''; };
const SUB = '₀₁₂₃₄₅₆₇₈₉';
const sub = n => String(n).split('').map(d => SUB[d]).join('');

/* ================= §1 sorting game ================= */
(function sorting() {
  const cards = [
    { h: '<span class="m">(p → q)</span>', a: 'obj' },
    { h: '<span class="m">¬(p ∧ ¬p)</span>', a: 'obj' },
    { h: '<span class="m">¬¬r</span>', a: 'obj' },
    { h: '<span class="m">((p ∨ q) ↔ r)</span>', a: 'obj' },
    { h: bil('<span class="m">φ</span> is a tautology', '<span class="m">φ</span> 是重言式'), a: 'meta' },
    { h: '<span class="m">Γ ⊨ φ</span>', a: 'meta' },
    { h: bil('<span class="m">(p → q)</span> has 5 symbols', '<span class="m">(p → q)</span> 含 5 个符号'), a: 'meta' },
    { h: '<span class="m">v(p) = 1</span>', a: 'meta' },
    { h: bil('every formula has balanced parentheses', '每个公式的括号都配对'), a: 'meta' },
  ];
  const pos = cards.map(() => 'tray');
  const order = ['tray', 'obj', 'meta'];
  function render() {
    ['tray', 'zobj', 'zmeta'].forEach(id => $(id).innerHTML = '');
    cards.forEach((c, i) => {
      const d = document.createElement('div');
      d.className = 'chip';
      d.innerHTML = c.h;
      d.addEventListener('click', () => {
        pos[i] = order[(order.indexOf(pos[i]) + 1) % 3];
        render();
        clearBox($('sortMsg'));
      });
      c.el = d;
      $({ tray: 'tray', obj: 'zobj', meta: 'zmeta' }[pos[i]]).appendChild(d);
    });
  }
  render();
  $('sortCheck').addEventListener('click', () => {
    let right = 0, placed = 0;
    cards.forEach((c, i) => {
      c.el.classList.remove('ok', 'no');
      if (pos[i] === 'tray') return;
      placed++;
      if (pos[i] === c.a) { right++; c.el.classList.add('ok'); } else c.el.classList.add('no');
    });
    if (right === cards.length) {
      okBox($('sortMsg'), bi(
        'All correct! Note the sneaky ones: <span class="m">⊨</span> and <span class="m">v(p) = 1</span> are statements <i>about</i> formulas, so they are metalanguage. The Greek letter <span class="m">φ</span> is a <b>metavariable</b>: a name we use for some formula, never a symbol inside the box.',
        '全对！注意几个容易混的：<span class="m">⊨</span> 和 <span class="m">v(p) = 1</span> 都是<i>关于</i>公式的断言，属于元语言。希腊字母 <span class="m">φ</span> 是<b>元变元</b>，是我们给某个公式起的名字，它本身从不出现在箱子里。'));
    } else {
      okBox($('sortMsg'), bi(`${right} / ${cards.length} correct${placed < cards.length ? ' (some cards are still in the tray)' : ''}. Red cards are in the wrong place. Ask yourself: is this a string <i>inside</i> the system, or a claim <i>about</i> it?`,
        `答对 ${right} / ${cards.length}${placed < cards.length ? '（还有卡片没分类）' : ''}。红色卡片放错了。问问自己：这是系统<i>内部</i>的一串符号，还是<i>关于</i>系统的一句断言？`), 'warn');
    }
  });
})();

/* ================= §2 formula factory ================= */
(function factory() {
  const svg = $('factory');
  const CX = 360, CY = 260;
  const R = [26, 105, 175, 240];
  const FONT = [18, 13, 11, 9.5];
  const SAMPLES = [2, 14, 16, 18];
  const counts = [2n];
  for (let k = 0; k < 4; k++) { const d = counts[k]; counts.push(2n + d + 4n * d * d); }
  let level = -1;

  function exactDepth(k) {
    if (k === 0) return { type: 'atom', name: Math.random() < .5 ? 'p' : 'q' };
    const op = ['not', 'and', 'or', 'imp', 'iff'][Math.floor(Math.random() * 5)];
    if (op === 'not') return { type: 'not', a: exactDepth(k - 1) };
    const deep = exactDepth(k - 1), other = randomFormula(['p', 'q'], k - 1);
    return Math.random() < .5 ? { type: 'bin', op, a: deep, b: other } : { type: 'bin', op, a: other, b: deep };
  }
  function samplesFor(k) {
    if (k === 0) return ['p', 'q'];
    const seen = new Set(), out = [];
    let guard = 0;
    while (out.length < SAMPLES[k] && guard++ < 500) {
      const s = tight(exactDepth(k));
      if (k >= 2 && s.length > 24) continue;
      if (!seen.has(s)) { seen.add(s); out.push(s); }
    }
    return out;
  }
  function reset() {
    svg.innerHTML = '';
    const garbage = [[')p(', 60, 40], ['p∧', 660, 40], ['¬', 60, 490], ['(p)', 660, 490], ['pq', 40, 260], ['∧∧q', 680, 260]];
    garbage.forEach(([s, x, y]) => {
      const t = el('text', { x, y, 'text-anchor': 'middle', fill: '#c0bcb0', 'font-size': 15 }, svg);
      t.textContent = s + ' ✗';
    });
    level = -1;
    $('facNext').disabled = false;
    step();
  }
  function step() {
    if (level >= 3) return;
    level++;
    const k = level;
    if (k > 0) {
      const c = el('circle', { cx: CX, cy: CY, r: R[k], fill: 'none', stroke: '#3b5bdb', 'stroke-dasharray': '4 6', opacity: .5 }, svg);
      c.classList.add('fadein');
      const lab = el('text', { x: CX + R[k] * 0.72, y: CY - R[k] * 0.72 - 4, fill: '#3b5bdb', 'font-size': 12, 'font-weight': 700 }, svg);
      lab.textContent = `F${sub(k)}`;
    }
    const items = samplesFor(k);
    items.forEach((s, i) => {
      const ang = (i / items.length) * Math.PI * 2 + k * 0.4 - Math.PI / 2;
      const x = CX + R[k] * Math.cos(ang), y = CY + R[k] * Math.sin(ang);
      const g = el('g', {}, svg);
      g.style.transition = 'transform .9s cubic-bezier(.2,.9,.3,1), opacity .9s';
      g.style.transform = `translate(${CX}px, ${CY}px)`;
      g.style.opacity = 0;
      const t = el('text', { 'text-anchor': 'middle', 'dominant-baseline': 'central', 'font-size': FONT[k], fill: k === 0 ? '#f08c00' : '#1f2430', 'font-weight': k === 0 ? 700 : 500 }, g);
      t.textContent = s;
      requestAnimationFrame(() => requestAnimationFrame(() => {
        setTimeout(() => { g.style.transform = `translate(${x}px, ${y}px)`; g.style.opacity = 1; }, i * 45);
      }));
    });
    const fmt = n => n.toLocaleString('en-US');
    const lines = [];
    for (let j = 0; j <= k; j++) lines.push(`|F${sub(j)}| = ${fmt(counts[j])}`);
    let extra = '';
    if (k === 3) {
      $('facNext').disabled = true;
      extra = bi(`<br>Next round, F₄, would have ${fmt(counts[4])} formulas, about 4.4 × 10¹⁴. Each round is finite, and Form = F₀ ∪ F₁ ∪ F₂ ∪ … is a <b>countable union of finite sets</b>, each of which we can list explicitly, so it is countable (no Axiom of Choice needed).`,
        `<br>再转一轮，F₄ 会有 ${fmt(counts[4])} 个公式，约 4.4 × 10¹⁴。每一轮都是有限的，而 Form = F₀ ∪ F₁ ∪ F₂ ∪ … 是<b>可数个有限集之并</b>，而且每个有限集都能明确地列出来，所以可数（无需选择公理）。`);
    }
    $('facInfo').innerHTML = `<span class="m">${lines.join(' &nbsp; ')}</span>` + bi(
      `<br>Rings show a sample of the <i>new</i> formulas made in each round (depth exactly k). The grey strings in the corners can <b>never</b> come out of the factory. Minimality is what keeps them out.`,
      `<br>每圈只展示该轮<i>新</i>造出的一部分公式（深度恰为 k）。四角的灰色字符串<b>永远</b>造不出来，正是“最小性”把它们挡在门外。`) + extra;
  }
  $('facNext').addEventListener('click', step);
  $('facReset').addEventListener('click', reset);
  reset();

  // strict checker
  const inp = $('strictIn');
  attachKeys($('strictKeys'), inp);
  function check() {
    const out = $('strictOut');
    try {
      const ast = strictParse(inp.value);
      const seq = subformulas(ast);
      const idx = new Map(seq.map((s, i) => [tight(s), i + 1]));
      let h = `<div class="msg ok">${bi('✓ A formula! Formation sequence (each line built from earlier lines by one rule):', '✓ 是公式！构造序列（每一行都由前面的行经一条规则得到）：')}</div><ol class="m" style="font-size:16px">`;
      seq.forEach((s, i) => {
        let why;
        if (s.type === 'atom') why = bil('rule 1: atom', '规则 1：原子');
        else if (s.type === 'not') why = bil(`rule 2 applied to #${idx.get(tight(s.a))}`, `对第 ${idx.get(tight(s.a))} 行用规则 2`);
        else why = bil(`rule 3 (${SYM[s.op]}) applied to #${idx.get(tight(s.a))}, #${idx.get(tight(s.b))}`, `对第 ${idx.get(tight(s.a))}、${idx.get(tight(s.b))} 行用规则 3（${SYM[s.op]}）`);
        h += `<li class="fadein" style="animation-delay:${i * .12}s"><b>${tight(s)}</b> &nbsp;<span class="muted" style="font-family:var(--sans);font-size:13px">${why}</span></li>`;
      });
      out.innerHTML = h + '</ol>';
    } catch (e) {
      let h = `<div class="msg bad">✗ ${bi('Not a formula: ', '不是公式：')}${e instanceof ParseError ? e.html() : e}</div>`;
      try {
        const loose = parse(inp.value);
        h += `<div class="msg info">${bi(`Under the friendly reading conventions it would mean <span class="m">${show(loose)}</span>, but the official definition is strict.`,
          `按宽松约定它可以理解为 <span class="m">${show(loose)}</span>，但官方定义是严格的。`)}</div>`;
      } catch { /* not even loosely a formula */ }
      out.innerHTML = h;
    }
  }
  inp.addEventListener('input', check);
  document.querySelectorAll('[data-try]').forEach(b => b.addEventListener('click', () => { inp.value = b.dataset.try; check(); }));
  check();
})();

/* ================= parenthesis mountain (shared by §3 and E3) ================= */
let mtnToken = 0;
async function mountain(container, str, opts = {}) {
  const my = ++mtnToken;
  container.innerHTML = '';
  const chars = [...str];
  const CW = Math.max(14, Math.min(26, 760 / chars.length)), LH = 26;
  let d = 0, maxD = 0;
  const info = chars.map(c => {
    if (c === '(') d++;
    const rec = { c, d };
    if (c === ')') d--;
    maxD = Math.max(maxD, rec.d);
    return rec;
  });
  const W = Math.max(chars.length * CW + 40, 280), H = (maxD + 1) * LH + 70;
  const svg = el('svg', { viewBox: `0 0 ${W} ${H}`, width: W, height: H }, container);
  const base = H - 40;
  el('line', { x1: 10, x2: W - 10, y1: base, y2: base, stroke: '#ccc' }, svg);
  for (let k = 1; k <= maxD; k++) {
    const t = el('text', { x: 4, y: base - k * LH + 4, 'font-size': 10, fill: '#aaa' }, svg);
    t.textContent = k;
    el('line', { x1: 16, x2: W - 10, y1: base - k * LH, y2: base - k * LH, stroke: '#eee' }, svg);
  }
  const isBin = c => '∧∨→↔'.includes(c);
  const mainIdx = str[0] === '(' ? info.findIndex(r => isBin(r.c) && r.d === 1) : -1;
  let L = 0, R = 0;
  const counter = el('text', { x: W - 12, y: 18, 'text-anchor': 'end', 'font-size': 14, 'font-weight': 700 }, svg);
  let prev = { x: 20, y: base };
  for (let i = 0; i < chars.length; i++) {
    if (my !== mtnToken) return;
    const { c, d: dd } = info[i];
    const x = 20 + i * CW + CW / 2;
    const after = c === ')' ? dd - 1 : dd;
    const y = base - after * LH;
    el('line', { x1: prev.x, y1: prev.y, x2: x - CW / 2, y2: prev.y, stroke: '#3b5bdb', 'stroke-width': 3 }, svg);
    el('line', { x1: x - CW / 2, y1: prev.y, x2: x - CW / 2, y2: y, stroke: '#3b5bdb', 'stroke-width': 3 }, svg);
    prev = { x: x - CW / 2, y };
    const isMain = i === mainIdx || (mainIdx === -1 && i === 0 && c === '¬');
    if (isMain) el('rect', { x: x - CW / 2, y: base + 4, width: CW, height: 26, rx: 5, fill: '#ae3ec9' }, svg);
    const t = el('text', { x, y: base + 22, 'text-anchor': 'middle', 'font-size': Math.min(17, CW * 0.8),
      fill: isMain ? '#fff' : c === '(' || c === ')' ? '#3b5bdb' : isBin(c) ? '#1f2430' : '#f08c00', 'font-weight': 700 }, svg);
    t.textContent = c;
    if (isBin(c) || c === '¬') {
      const dot = el('circle', { cx: x, cy: base - dd * LH, r: isMain ? 7 : 4, fill: isMain ? '#ae3ec9' : '#999' }, svg);
      dot.classList.add('pop');
    }
    if (c === '(') L++;
    if (c === ')') R++;
    counter.textContent = `( : ${L}   ) : ${R}`;
    counter.setAttribute('fill', L === R ? '#2f9e44' : '#1f2430');
    await sleep(opts.speed ?? 140);
  }
  el('line', { x1: prev.x, y1: prev.y, x2: W - 10, y2: prev.y, stroke: '#3b5bdb', 'stroke-width': 3 }, svg);
  return { L, R, main: mainIdx };
}

/* ================= §3 parse tree ================= */
let treeAst = null;
(function trees() {
  const inp = $('treeIn');
  attachKeys($('treeKeys'), inp);
  function grow() {
    try {
      treeAst = parse(inp.value);
      clearBox($('treeErr'));
      TreeView($('treeStage'), treeAst, {
        markMain: true,
        onHover: a => $('treeSub').innerHTML = a ? `${bil('subformula', '子公式')}: <b>${pretty(a)}</b>` : '',
      });
      const mc = treeAst.type === 'atom' ? bil('none (it is an atom)', '无（它是原子）') : treeAst.type === 'not' ? '¬' : SYM[treeAst.op];
      $('treeSub').innerHTML = `${bil('Main connective (purple ring)', '主联结词（紫圈）')}: <b>${mc}</b> &nbsp;·&nbsp; ${bil('official form', '官方写法')}: <b>${show(treeAst)}</b>`;
      $('mtnStage').innerHTML = '';
    } catch (e) { errBox($('treeErr'), e); }
  }
  $('treeGo').addEventListener('click', grow);
  inp.addEventListener('keydown', e => e.key === 'Enter' && grow());
  $('mtnGo').addEventListener('click', () => { if (treeAst) mountain($('mtnStage'), tight(treeAst)); });
  grow();

  // ambiguity
  const t1 = { type: 'bin', op: 'or', a: { type: 'bin', op: 'and', a: { type: 'atom', name: 'p' }, b: { type: 'atom', name: 'q' } }, b: { type: 'atom', name: 'r' } };
  const t2 = { type: 'bin', op: 'and', a: { type: 'atom', name: 'p' }, b: { type: 'bin', op: 'or', a: { type: 'atom', name: 'q' }, b: { type: 'atom', name: 'r' } } };
  const v1 = TreeView($('amb1'), t1, { gx: 58, gy: 60 });
  const v2 = TreeView($('amb2'), t2, { gx: 58, gy: 60 });
  const v = { p: 1, q: 1, r: 1 };
  async function run() {
    const [a, b] = await Promise.all([v1.evaluate(v, 160), v2.evaluate(v, 160)]);
    if (a !== b) okBox($('ambMsg'), bi(`Found it! Same string, same valuation, different truth values (${a} vs ${b}). Without parentheses, “the value of p ∧ q ∨ r” is not even well-defined.`,
      `找到了！同一个字符串、同一个赋值，真值却不同（${a} 对 ${b}）。没有括号，“p ∧ q ∨ r 的真值”根本就没有良定义。`));
    else okBox($('ambMsg'), bi(`Both trees give ${a}. Keep flipping: some valuation makes them disagree.`, `两棵树都得 ${a}。继续拨：总有某个赋值让它们分道扬镳。`), 'info');
  }
  Switches($('ambSw'), ['p', 'q', 'r'], v, run);
  setTimeout(run, 900);
})();

/* ================= §4 valuations ================= */
(function valuations() {
  const v = {};
  let tv = null, ast = null;
  async function run() {
    const val = await tv.evaluate(v);
    if (val === undefined) return;
    okBox($('valOut'), `<span class="m">v̄(${pretty(ast)}) = ${val}</span>`, val ? 'ok' : 'bad');
  }
  function load() {
    try {
      ast = parse($('valIn').value);
      clearBox($('valErr'));
      const atoms = sortAtoms(atomsOf(ast));
      tv = TreeView($('valStage'), ast);
      Switches($('valSw'), atoms, v, run);
      setTimeout(run, 600);
    } catch (e) { errBox($('valErr'), e); }
  }
  $('valGo').addEventListener('click', load);
  $('valIn').addEventListener('keydown', e => e.key === 'Enter' && load());
  load();
})();

/* ================= §5 truth tables ================= */
(function tables() {
  let ast = null;
  function build() {
    try {
      ast = parse($('ttIn').value);
      clearBox($('ttErr'));
      render();
    } catch (e) { errBox($('ttErr'), e); }
  }
  function render() {
    TruthTable($('ttStage'), ast);
    const c = classify(ast);
    if (c.atoms.length > 5) return;
    $('ttKind').innerHTML = KIND_HTML[c.kind];
    $('ttStrip').innerHTML = c.vals.map((x, i) => `<span class="s${x} pop" style="animation-delay:${i * .05}s" title="row ${i + 1}"></span>`).join('');
  }
  $('ttGo').addEventListener('click', build);
  $('ttIn').addEventListener('keydown', e => e.key === 'Enter' && build());
  $('ttNeg').addEventListener('click', () => {
    if (!ast) return;
    ast = { type: 'not', a: ast };
    $('ttIn').value = pretty(ast);
    render();
  });
  document.querySelectorAll('[data-tt]').forEach(b => b.addEventListener('click', () => { $('ttIn').value = b.dataset.tt; build(); }));
  build();
})();

/* ================= §6 consequence ================= */
function drawVenn(svg, res) {
  svg.innerHTML = '';
  el('rect', { x: 4, y: 4, width: 352, height: 192, rx: 14, fill: '#f1efe7', stroke: '#d8d3c4' }, svg);
  const tl = el('text', { x: 14, y: 22, 'font-size': 12, fill: '#777' }, svg);
  tl.textContent = `${res.total} valuations · ${res.total} 个赋值`;
  const nPhi = res.tiles.filter(t => t.f).length;
  const label = (x, y, s, fill = '#1f2430', size = 13) => { const t = el('text', { x, y, 'text-anchor': 'middle', 'font-size': size, fill, 'font-weight': 700 }, svg); t.textContent = s; };
  // Mod(φ)
  el('circle', { cx: 200, cy: 108, r: 72, fill: 'rgba(47,158,68,.18)', stroke: '#2f9e44', 'stroke-width': 2 }, svg);
  label(200, 30, `Mod(φ): ${nPhi}`, '#2f9e44');
  if (res.inG === 0) {
    el('circle', { cx: 90, cy: 110, r: 26, fill: 'none', stroke: '#3b5bdb', 'stroke-width': 2, 'stroke-dasharray': '4 4' }, svg);
    label(90, 114, '∅', '#3b5bdb', 18);
    label(90, 160, 'Mod(Γ) = ∅', '#3b5bdb', 12);
  } else if (res.holds) {
    el('circle', { cx: 200, cy: 118, r: 46, fill: 'rgba(59,91,219,.15)', stroke: '#3b5bdb', 'stroke-width': 3 }, svg);
    label(200, 122, `Mod(Γ): ${res.inG}`, '#3b5bdb', 11);
  } else {
    el('circle', { cx: 120, cy: 112, r: 52, fill: 'rgba(59,91,219,.1)', stroke: '#3b5bdb', 'stroke-width': 3 }, svg);
    label(98, 64, `Mod(Γ): ${res.inG}`, '#3b5bdb', 12);
    label(96, 118, `✗ ${res.counter}`, '#e03131', 16);
  }
}
(function consequence() {
  function run() {
    try {
      const prem = $('cqG').value.split(';').map(s => s.trim()).filter(Boolean).map(parse);
      const concl = parse($('cqF').value);
      clearBox($('cqErr'));
      const res = ConsequenceView($('cqStage'), prem, concl);
      if (!res) return;
      drawVenn($('venn'), res);
      const G = prem.length ? '{' + prem.map(pretty).join(', ') + '}' : '∅';
      const rel = `<span class="m">${G} ${res.holds ? '⊨' : '⊭'} ${pretty(concl)}</span>`;
      if (res.holds && res.inG === 0) okBox($('cqOut'), rel + bi('<br>Holds <b>vacuously</b>: no world makes all the premises true, so no world can be a counterexample.', '<br><b>空真</b>成立：没有任何世界让前提全真，自然也就没有反例。'));
      else if (res.holds) okBox($('cqOut'), rel + bi(`<br>Every blue-framed tile is green (${res.inG} of ${res.inG}).`, `<br>所有蓝框砖都是绿的（${res.inG}/${res.inG}）。`));
      else okBox($('cqOut'), rel + bi(`<br>${res.counter} counterexample(s), shown as red tiles: premises all true, conclusion false.`, `<br>有 ${res.counter} 个反例（红砖）：前提全真，结论为假。`), 'bad');
    } catch (e) { errBox($('cqErr'), e); }
  }
  $('cqGo').addEventListener('click', run);
  [$('cqG'), $('cqF')].forEach(i => i.addEventListener('keydown', e => e.key === 'Enter' && run()));
  document.querySelectorAll('[data-cq]').forEach(b => b.addEventListener('click', () => {
    const [g, f] = b.dataset.cq.split('⊢');
    $('cqG').value = g.trim();
    $('cqF').value = f.trim();
    run();
  }));
  run();
})();

/* ================= §7 promise ================= */
(function promise() {
  const box = $('promise');
  const cells = [
    { p: 1, q: 1, emo: '💯 🍽️', v: 1, en: 'Promise kept', zh: '说到做到' },
    { p: 1, q: 0, emo: '💯 🙅', v: 0, en: 'Promise broken!', zh: '食言了！' },
    { p: 0, q: 1, emo: '📝 🍽️', v: 1, en: 'Not broken: a bonus dinner', zh: '没食言，白赚一顿' },
    { p: 0, q: 0, emo: '📝 🏠', v: 1, en: 'Not broken: never triggered', zh: '没食言，承诺没被触发' },
  ];
  let h = `<div></div><div class="hd">${bi('🍽️ dinner (q = 1)', '🍽️ 请客了（q = 1）')}</div><div class="hd">${bi('🏠 no dinner (q = 0)', '🏠 没请（q = 0）')}</div>`;
  [1, 0].forEach(p => {
    h += `<div class="hd">${p ? bi('💯 aced it (p = 1)', '💯 考了满分（p = 1）') : bi('📝 didn\'t (p = 0)', '📝 没考满分（p = 0）')}</div>`;
    cells.filter(c => c.p === p).forEach(c => {
      h += `<div class="pcard ${c.v ? 't' : 'f'}"><div class="emo">${c.emo}</div><div class="m">${c.p} → ${c.q} = ?</div>
        <div class="verdict">${bi(c.en, c.zh)}<div class="m">${c.p} → ${c.q} = ${c.v}</div></div></div>`;
    });
  });
  box.innerHTML = h;
  box.querySelectorAll('.pcard').forEach(c => c.addEventListener('click', () => c.classList.add('shown')));
})();

/* ================= §8 Cantor ================= */
(function cantor() {
  // enumeration of formulas over p₀, p₁ by length then lexicographic order
  const atoms = ['p₀', 'p₁'];
  let pool = atoms.map(a => ({ type: 'atom', name: a }));
  for (let r = 0; r < 2; r++) {
    const next = [...pool];
    pool.forEach(a => next.push({ type: 'not', a }));
    pool.forEach(a => pool.forEach(b => OPS.forEach(op => next.push({ type: 'bin', op, a, b }))));
    pool = next;
  }
  const strs = [...new Set(pool.map(tight))].sort((x, y) => x.length - y.length || x.localeCompare(y));
  const list = $('enumList');
  let idx = 0;
  setInterval(() => {
    if (idx >= strs.length) return;
    const d = document.createElement('div');
    d.className = 'fadein';
    d.innerHTML = `<span class="muted">φ${sub(idx)} =</span> ${strs[idx]}`;
    list.appendChild(d);
    if (list.children.length > 13) list.removeChild(list.firstChild);
    idx++;
  }, 650);

  // diagonal
  const svg = $('diag');
  const N = 8, CS = 40, X0 = 70, Y0 = 36;
  let bits = [], running = 0;
  function draw() {
    running++;
    svg.innerHTML = '';
    bits = Array.from({ length: N }, () => Array.from({ length: N }, () => Math.random() < .5 ? 1 : 0));
    for (let c = 0; c < N; c++) {
      const t = el('text', { x: X0 + c * CS + CS / 2, y: Y0 - 12, 'text-anchor': 'middle', 'font-size': 14, fill: '#f08c00', 'font-weight': 700 }, svg);
      t.textContent = 'p' + sub(c);
    }
    const dots = el('text', { x: X0 + N * CS + 16, y: Y0 - 12, 'font-size': 14, fill: '#999' }, svg);
    dots.textContent = '…';
    for (let r = 0; r < N; r++) {
      const t = el('text', { x: X0 - 12, y: Y0 + r * CS + CS / 2 + 5, 'text-anchor': 'end', 'font-size': 14, 'font-weight': 700 }, svg);
      t.textContent = 'v' + sub(r);
      for (let c = 0; c < N; c++) {
        el('rect', { x: X0 + c * CS + 2, y: Y0 + r * CS + 2, width: CS - 4, height: CS - 4, rx: 6, fill: bits[r][c] ? '#d3f9d8' : '#ffe3e3', id: `dc${r}_${c}` }, svg);
        const b = el('text', { x: X0 + c * CS + CS / 2, y: Y0 + r * CS + CS / 2 + 5, 'text-anchor': 'middle', 'font-size': 15 }, svg);
        b.textContent = bits[r][c];
      }
      const more = el('text', { x: X0 + N * CS + 16, y: Y0 + r * CS + CS / 2 + 5, 'font-size': 14, fill: '#999' }, svg);
      more.textContent = '…';
    }
    const vd = el('text', { x: 4, y: Y0 + N * CS + CS / 2 + 24, 'font-size': 12, fill: '#999' }, svg);
    vd.textContent = '⋮';
  }
  async function run() {
    draw();
    const my = running;
    const yD = Y0 + N * CS + 20;
    const lab = el('text', { x: X0 - 12, y: yD + CS / 2 + 5, 'text-anchor': 'end', 'font-size': 15, 'font-weight': 800, fill: '#ae3ec9' }, svg);
    lab.textContent = 'd';
    for (let k = 0; k < N; k++) {
      await sleep(450);
      if (my !== running) return;
      const cell = svg.querySelector(`#dc${k}_${k}`);
      cell.setAttribute('stroke', '#ae3ec9');
      cell.setAttribute('stroke-width', 3);
      const nb = 1 - bits[k][k];
      el('rect', { x: X0 + k * CS + 2, y: yD + 2, width: CS - 4, height: CS - 4, rx: 6, fill: '#f8e7fc', stroke: '#ae3ec9', 'stroke-width': 2, class: 'pop' }, svg);
      const t = el('text', { x: X0 + k * CS + CS / 2, y: yD + CS / 2 + 5, 'text-anchor': 'middle', 'font-size': 15, 'font-weight': 800, fill: '#ae3ec9' }, svg);
      t.textContent = nb;
      const x = el('text', { x: X0 + N * CS + 34, y: Y0 + k * CS + CS / 2 + 5, 'font-size': 13, fill: '#e03131', 'font-weight': 700 }, svg);
      x.textContent = `d ≠ v${sub(k)}`;
    }
    await sleep(400);
    if (my !== running) return;
    const msg = el('text', { x: X0, y: yD + CS + 28, 'font-size': 13, fill: '#ae3ec9', 'font-weight': 700 }, svg);
    msg.textContent = 'd(pₖ) = 1 − vₖ(pₖ)  ⇒  d ∉ list / d 不在清单里';
  }
  $('diagGo').addEventListener('click', run);
  $('diagNew').addEventListener('click', draw);
  draw();
})();

/* ================= E1 ================= */
(function e1() {
  const p = { type: 'atom', name: 'p' }, q = { type: 'atom', name: 'q' };
  const pq = { type: 'bin', op: 'imp', a: p, b: q };
  const pqp = { type: 'bin', op: 'imp', a: pq, b: p };
  const peirce = { type: 'bin', op: 'imp', a: pqp, b: p };
  const cols = [pq, pqp, peirce];
  const rows = allValuations(['p', 'q']);
  const user = rows.map(() => cols.map(() => null));
  let h = '<table class="tt"><thead><tr><th>p</th><th>q</th>';
  cols.forEach((c, k) => h += `<th class="${k ? '' : 'sep'}">${pretty(c)}</th>`);
  h += '</tr></thead><tbody>';
  rows.forEach((v, r) => {
    h += `<tr><td class="c${v.p}">${v.p}</td><td class="c${v.q}">${v.q}</td>`;
    cols.forEach((c, k) => h += `<td class="click${k ? '' : ' sep'}" data-r="${r}" data-k="${k}"></td>`);
    h += '</tr>';
  });
  $('e1Table').innerHTML = h + '</tbody></table>';
  $('e1Table').querySelectorAll('td.click').forEach(td => td.addEventListener('click', () => {
    const r = +td.dataset.r, k = +td.dataset.k;
    user[r][k] = user[r][k] === null ? 1 : user[r][k] === 1 ? 0 : null;
    td.textContent = user[r][k] ?? '';
    td.className = `click${k ? '' : ' sep'}` + (user[r][k] === null ? '' : ` c${user[r][k]}`);
  }));
  let revealed = false;
  function check(reveal) {
    if (reveal) revealed = true;
    let ok = 0;
    $('e1Table').querySelectorAll('td.click').forEach(td => {
      const r = +td.dataset.r, k = +td.dataset.k;
      const want = evalF(cols[k], rows[r]);
      if (reveal) { user[r][k] = want; td.textContent = want; }
      td.classList.remove('right', 'wrong');
      void td.offsetWidth;
      if (user[r][k] === want) { ok++; td.classList.add('right'); } else if (user[r][k] !== null) td.classList.add('wrong');
    });
    if (ok === 12) {
      okBox($('e1Msg'), bi('✓ Last column is all 1s, so Peirce\'s law <b>is a tautology</b>. Fun fact: it can\'t be proved in <i>intuitionistic</i> logic. Classical logic is stronger than it looks.',
        '✓ 最后一列全是 1，所以皮尔士定律<b>是重言式</b>。趣闻：它在<i>直觉主义逻辑</i>中证不出来，经典逻辑比看上去更“强”。'));
      if (!revealed) Progress.mark('L1E1');
    } else okBox($('e1Msg'), bi(`${ok} / 12 cells correct. Red = wrong. Compute the middle columns first.`, `${ok} / 12 格正确，红色为错。先算中间几列。`), 'warn');
  }
  $('e1Check').addEventListener('click', () => check(false));
  $('e1Show').addEventListener('click', () => check(true));
})();

/* ================= E2 ================= */
(function e2() {
  const items = [
    { s: '(a) &nbsp; p ⊨ (q → p)', ans: true, G: ['p'], F: 'q → p',
      en: 'True. Whenever p = 1, q → p has a true consequent, so it is 1.', zh: '对。只要 p = 1，q → p 的后件为真，整体就是 1。' },
    { s: '(b) &nbsp; (q → p) ⊨ p', ans: false, G: ['q → p'], F: 'p',
      en: 'False. Counterexample p = 0, q = 0: the premise 0 → 0 = 1, but the conclusion is 0.', zh: '错。反例 p = 0, q = 0：前提 0 → 0 = 1，结论却是 0。' },
    { s: bil('(c) &nbsp; ∅ ⊨ φ  means  “φ is a tautology”', '(c) &nbsp; ∅ ⊨ φ 即“φ 是重言式”'), ans: true, G: [], F: 'p ∨ ¬p',
      en: 'True. With no premises, every valuation satisfies “all premises”, so every tile is framed. φ must then be true everywhere.', zh: '对。没有前提时，“前提全真”对每个赋值都成立，所有砖都有蓝框，于是 φ 必须处处为真。' },
    { s: bil('(d) &nbsp; Γ unsatisfiable ⇒ Γ ⊨ φ for every φ', '(d) &nbsp; Γ 不可满足 ⇒ 对任意 φ 都有 Γ ⊨ φ'), ans: true, G: ['p', '¬p'], F: 'q',
      en: 'True, vacuously. No tile is framed, so there is nothing to check (Mod(Γ) = ∅ ⊆ anything). This is the principle of explosion.', zh: '对，空真。没有一块砖带蓝框，也就无可检查（Mod(Γ) = ∅ ⊆ 任何集合）。这就是“爆炸原理”。' },
  ];
  const solved = items.map(() => false);
  const revealed = items.map(() => false);
  const box = $('e2List');
  items.forEach((it, i) => {
    const row = document.createElement('div');
    row.className = 'tf';
    row.innerHTML = `<div class="stmt">${it.s}</div>
      <button class="btn small" data-v="1">${bil('True', '对')}</button>
      <button class="btn small" data-v="0">${bil('False', '错')}</button>
      <button class="btn small ghost" data-v="show">${bil('Show answer', '看答案')}</button>
      <div style="flex-basis:100%"><div class="msg"></div><div class="grid"></div></div>`;
    box.appendChild(row);
    row.querySelectorAll('button').forEach(b => b.addEventListener('click', () => {
      const show = b.dataset.v === 'show';
      if (show) revealed[i] = true;
      const guess = show ? it.ans : b.dataset.v === '1';
      const msg = row.querySelector('.msg');
      if (guess === it.ans) {
        okBox(msg, (show ? (it.ans ? bi('<b>True.</b> ', '<b>对。</b>') : bi('<b>False.</b> ', '<b>错。</b>')) : '✓ ') + bi(it.en, it.zh), show ? 'info' : 'ok');
        ConsequenceView(row.querySelector('.grid'), it.G.map(parse), parse(it.F), { small: true, noLegend: true });
        if (show || revealed[i]) return;
        solved[i] = true;
        if (solved.every(Boolean)) Progress.mark('L1E2');
      } else {
        okBox(msg, bi('✗ Not quite. Picture the tile grid: is there a red tile (premises true, conclusion false)?', '✗ 不对。想象一下格子图：有没有红砖（前提全真、结论为假）？'), 'bad');
        row.querySelector('.grid').innerHTML = '';
      }
    }));
  });
})();

/* ================= E3 ================= */
(function e3() {
  async function rand() {
    let f;
    do f = randomFormula(['p', 'q', 'r'], 4); while (tight(f).split('(').length < 3);
    await mountain($('e3Mtn'), tight(f), { speed: 90 });
  }
  $('e3Rand').addEventListener('click', rand);
  rand();
  const steps = [...document.querySelectorAll('#e3Steps .step')];
  let k = 0;
  $('e3Next').addEventListener('click', () => {
    if (k < steps.length) steps[k++].classList.add('on');
    if (k === steps.length) { $('e3Next').disabled = true; Progress.mark('L1E3'); }
  });
  $('e3All').addEventListener('click', () => {
    steps.forEach(st => st.classList.add('on'));
    k = steps.length;
    $('e3Next').disabled = true;
  });
})();

/* ================= E4 ================= */
(function e4() {
  attachKeys($('e4Keys'), $('e4Or'));
  const targets = {
    Or: { f: (p, q) => p | q, name: 'p ∨ q',
      hint: bi('p ∨ q says: “if p fails, then q must hold”.', 'p ∨ q 的意思是：“p 不成立的话，q 就得成立”。') },
    And: { f: (p, q) => p & q, name: 'p ∧ q',
      hint: bi('p ∧ q is false exactly when “p → ¬q” is true. So negate that.', 'p ∧ q 为假，恰好是“p → ¬q”为真的时候。把它否定掉就行。') },
  };
  const done = { Or: false, And: false };
  let revealing = false, revealed = false;
  $('e4Show').addEventListener('click', () => {
    revealing = true;
    revealed = true;
    $('e4Or').value = '¬p → q';
    $('e4And').value = '¬(p → ¬q)';
    $('e4Or').dispatchEvent(new Event('input'));
    $('e4And').dispatchEvent(new Event('input'));
    revealing = false;
  });
  for (const key of ['Or', 'And']) {
    const inp = $('e4' + key), msg = $(`e4${key}Msg`), tt = $(`e4${key}TT`);
    inp.addEventListener('focus', () => { $('e4Keys').innerHTML = ''; attachKeys($('e4Keys'), inp); });
    $(`e4${key}Hint`).addEventListener('click', () => okBox(msg, targets[key].hint, 'info'));
    inp.addEventListener('input', () => {
      tt.innerHTML = '';
      if (!inp.value.trim()) { clearBox(msg); return; }
      let ast;
      try { ast = parse(inp.value); } catch (e) { errBox(msg, e); return; }
      const bad = [...opsOf(ast)].filter(o => o !== 'not' && o !== 'imp');
      const badAtoms = [...atomsOf(ast)].filter(a => a !== 'p' && a !== 'q');
      if (bad.length) { okBox(msg, bi(`Uses forbidden ${bad.map(o => SYM[o]).join(' ')}: only ¬ and → allowed.`, `用了禁用的 ${bad.map(o => SYM[o]).join(' ')}：只准用 ¬ 和 →。`), 'bad'); return; }
      if (badAtoms.length) { okBox(msg, bi('Only atoms p and q, please.', '原子只能用 p 和 q。'), 'bad'); return; }
      const rows = allValuations(['p', 'q']);
      let all = true;
      let h = `<table class="tt"><tr><th>p</th><th>q</th><th class="sep">${targets[key].name}</th><th>${bil('yours', '你的')}</th></tr>`;
      rows.forEach(v => {
        const want = targets[key].f(v.p, v.q), got = evalF(ast, v);
        if (want !== got) all = false;
        h += `<tr><td>${v.p}</td><td>${v.q}</td><td class="sep c${want}">${want}</td><td class="c${got} ${want === got ? 'right' : 'wrong'}">${got}</td></tr>`;
      });
      tt.innerHTML = h + '</table>';
      if (all) {
        okBox(msg, '✓ ' + bi(`Equivalent to ${targets[key].name}.`, `与 ${targets[key].name} 逻辑等价。`));
        if (revealing || revealed) return;
        done[key] = true;
        if (done.Or && done.And) Progress.mark('L1E4');
      } else okBox(msg, bi('Truth tables differ (red rows).', '真值表对不上（见红格）。'), 'warn');
    });
  }
})();

/* ================= E5 ================= */
(function e5() {
  const solved = { a: false, b: false };
  let revealed = false;
  const finish = () => !revealed && solved.a && solved.b && Progress.mark('L1E5');
  function strips() {
    const n = +$('e5n').value;
    $('e5nv').textContent = n;
    const rows = 1 << n, fns = 1 << rows;
    $('e5count').innerHTML = `&nbsp; 2ⁿ = ${rows} ${bil('rows', '行')} &nbsp;⇒&nbsp; 2^(2ⁿ) = <b>${fns}</b> ${bil('truth functions', '个真值函数')}`;
    const sz = n === 3 ? 7 : 16;
    let h = '<div style="display:flex;flex-wrap:wrap;gap:6px">';
    for (let f = 0; f < fns; f++) {
      h += `<div class="pop" style="display:flex;gap:1px;padding:2px;border:1px solid #e3dfd3;border-radius:4px;animation-delay:${Math.min(f * 8, 900)}ms">`;
      for (let r = 0; r < rows; r++) {
        const b = (f >> (rows - 1 - r)) & 1;
        h += `<span style="width:${sz}px;height:${sz}px;border-radius:2px;background:${b ? 'var(--true)' : 'var(--false)'}"></span>`;
      }
      h += '</div>';
    }
    $('e5Strips').innerHTML = h + '</div>';
  }
  $('e5n').addEventListener('input', strips);
  strips();
  $('e5aGo').addEventListener('click', () => {
    const v = $('e5a').value.replace(/[,\s]/g, '');
    if (v === '65536' || v === '2^16' || v === '2^(2^4)') {
      okBox($('e5aMsg'), bi('✓ 2^(2⁴) = 2¹⁶ = 65,536. Each truth function = one way to fill a 16-row output column.', '✓ 2^(2⁴) = 2¹⁶ = 65536。每个真值函数就是 16 行输出列的一种填法。'));
      solved.a = true; finish();
    } else okBox($('e5aMsg'), bi('Not yet. How many rows does a 4-variable table have? Each row\'s output is 0 or 1, independently.', '还不对。4 元真值表有几行？每行输出可以独立地取 0 或 1。'), 'bad');
  });
  const opts = [
    { ok: false, en: 'Yes, a real contradiction: one of the two counts must be wrong.', zh: '矛盾，两个结论必有一个算错了。' },
    { ok: true, en: 'No. A finitary truth function is a finite object (a finite table); listing the finitely many tables for n = 0, 1, 2, … in turn shows there are countably many (no choice needed, since each finite batch has an explicit order). An element of {0,1}^ℕ is an infinite sequence, a different kind of object, so the two sets simply aren\'t the same.', zh: '不矛盾。有限元真值函数是有限对象（一张有限的表）；按 n = 0, 1, 2, … 依次列出每一批有限多张表，就知道它们只有可数多个（每批都有明确的顺序，无需选择公理）；而 {0,1}^ℕ 的元素是无穷序列，是另一类东西，两个集合本来就不是一回事。' },
    { ok: false, en: 'No contradiction, but only because of the Axiom of Choice.', zh: '不矛盾，但这要靠选择公理才能保证。' },
  ];
  const box = $('e5b');
  $('e5Show').addEventListener('click', () => {
    revealed = true;
    okBox($('e5aMsg'), bi('(a) 2^(2⁴) = 2¹⁶ = 65,536: a 4-variable table has 16 rows, and each row\'s output is chosen independently.', '(a) 2^(2⁴) = 2¹⁶ = 65536：4 元真值表有 16 行，每行输出独立地取 0 或 1。'), 'info');
    box.querySelectorAll('.choice')[1].classList.add('right');
    okBox($('e5bMsg'), bi('(b) No contradiction: finitary truth functions are finite tables (countably many), while elements of {0,1}^ℕ are infinite sequences, a different kind of object.', '(b) 不矛盾：有限元真值函数是有限的表（可数多个），而 {0,1}^ℕ 的元素是无穷序列，是另一类东西。'), 'info');
  });
  opts.forEach(o => {
    const b = document.createElement('button');
    b.className = 'btn choice';
    b.innerHTML = bi(o.en, o.zh);
    b.addEventListener('click', () => {
      box.querySelectorAll('.choice').forEach(x => x.classList.remove('right', 'wrongc'));
      b.classList.add(o.ok ? 'right' : 'wrongc');
      if (o.ok) {
        okBox($('e5bMsg'), bi('✓ Exactly. Keep this in mind: “a finite description” vs “an infinite object” is the same gap that will make <i>definability</i> and <i>incompleteness</i> work later.', '✓ 正是如此。记住“有限描述”与“无穷对象”之间的这道鸿沟，后面讲<i>可定义性</i>和<i>不完全性</i>时还会用到。'));
        solved.b = true; finish();
      } else okBox($('e5bMsg'), bi('✗ Look again: are a truth function and an infinite 0/1 sequence even the same kind of thing?', '✗ 再想想：真值函数和无穷 0/1 序列是同一类东西吗？'), 'bad');
    });
    box.appendChild(b);
  });
})();

/* ================= E6 ================= */
(function e6() {
  function test() {
    let ast;
    try { ast = parse($('e6In').value); } catch (e) { errBox($('e6Out'), e); return; }
    const bad = [...opsOf(ast)].filter(o => o !== 'and' && o !== 'or');
    if (bad.length) { okBox($('e6Out'), bi(`Contains ${bad.map(o => o === 'not' ? '¬' : SYM[o]).join(' ')}: only ∧ and ∨ allowed in this challenge.`, `含有 ${bad.map(o => o === 'not' ? '¬' : SYM[o]).join(' ')}：本题只准用 ∧ 和 ∨。`), 'bad'); return; }
    const atoms = sortAtoms(atomsOf(ast));
    const one = Object.fromEntries(atoms.map(a => [a, 1])), zero = Object.fromEntries(atoms.map(a => [a, 0]));
    const c = classify(ast);
    okBox($('e6Out'), `${KIND_HTML[c.kind]}<br><span class="m">${bil('all-1 valuation', '全 1 赋值')} 𝟙 ⇒ ${evalF(ast, one)} &nbsp;·&nbsp; ${bil('all-0 valuation', '全 0 赋值')} 𝟘 ⇒ ${evalF(ast, zero)}</span>`, 'info');
  }
  $('e6Go').addEventListener('click', test);
  let revealed = false;
  $('e6Show').addEventListener('click', () => {
    revealed = true;
    $('e6Choice').querySelectorAll('.choice')[0].classList.add('right');
    document.querySelector('#e6Proof .step').classList.add('on');
  });
  $('e6In').addEventListener('keydown', e => e.key === 'Enter' && test());
  test();
  const opts = [
    { ok: true, en: 'The claim is true.', zh: '命题成立。' },
    { ok: false, en: 'The claim is flawed: some ∧∨-formula is a tautology or unsatisfiable.', zh: '命题有漏洞：存在某个 ∧∨ 公式是重言式或矛盾式。' },
  ];
  opts.forEach(o => {
    const b = document.createElement('button');
    b.className = 'btn choice';
    b.innerHTML = bi(o.en, o.zh);
    b.addEventListener('click', () => {
      $('e6Choice').querySelectorAll('.choice').forEach(x => x.classList.remove('right', 'wrongc'));
      b.classList.add(o.ok ? 'right' : 'wrongc');
      if (o.ok) {
        okBox($('e6Msg'), bi('✓ Right. Look at the two valuations the tester keeps showing you. Proof:', '✓ 对。注意测试器一直显示的那两个赋值。证明如下：'));
        document.querySelector('#e6Proof .step').classList.add('on');
        if (!revealed) Progress.mark('L1E6');
      } else okBox($('e6Msg'), bi('✗ Try to produce such a formula in the tester above. Watch what the all-1 and all-0 valuations always do.', '✗ 先在上面测试器里造一个这样的公式试试。留意全 1 和全 0 赋值总是给出什么。'), 'bad');
    });
    $('e6Choice').appendChild(b);
  });
})();
