// Lesson 6 interactions: Russell's paradox and the ZF axioms.
Lang.init();
Progress.paint();

const $ = id => document.getElementById(id);
const okBox = (box, html, kind = 'ok') => { box.className = 'msg ' + kind; box.innerHTML = html; };
const clearBox = box => { box.className = 'msg'; box.innerHTML = ''; };
const errBox = (box, e) => okBox(box, e instanceof ParseError ? e.html() : String(e), 'bad');
const SUB = '₀₁₂₃₄₅₆₇₈₉';
const sub = n => String(n).split('').map(d => SUB[d]).join('');
const esc = s => String(s).replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;');
function svgText(parent, x, y, str, attrs = {}) {
  const t = el('text', { x, y, ...attrs }, parent);
  t.textContent = str;
  return t;
}

/* ================= hereditarily finite sets (pure, testable) ================= */
// HF-START
const HF = (() => {
  const pool = new Map();
  const cmp = (a, b) => a.rank - b.rank || a.m.length - b.m.length || (a.k < b.k ? -1 : a.k > b.k ? 1 : 0);
  // Canonical, interned set: equal sets are the same JS object (Extensionality).
  function mk(members) {
    const seen = new Map();
    for (const x of members) seen.set(x.k, x);
    const m = [...seen.values()].sort(cmp);
    const k = '{' + m.map(x => x.k).join(',') + '}';
    let s = pool.get(k);
    if (!s) {
      s = { k, m, rank: m.length ? 1 + Math.max(...m.map(x => x.rank)) : 0, size: 1 + m.reduce((t, x) => t + x.size, 0) };
      pool.set(k, s);
    }
    return s;
  }
  const E = mk([]);
  const has = (A, x) => A.m.includes(x);
  const union = A => mk(A.m.flatMap(x => x.m));
  const cup = (a, b) => mk([...a.m, ...b.m]);
  const cap = (a, b) => mk(a.m.filter(x => has(b, x)));
  const subset = (a, b) => a.m.every(x => has(b, x));
  function power(A) {
    const n = A.m.length, out = [];
    for (let mask = 0; mask < (1 << n); mask++) out.push(mk(A.m.filter((_, i) => (mask >> i) & 1)));
    return mk(out);
  }
  const succ = x => mk([...x.m, x]);
  const nats = [E];
  function nat(n) { while (nats.length <= n) nats.push(succ(nats[nats.length - 1])); return nats[n]; }
  function natOf(s) { const n = s.m.length; return n <= 12 && nat(n) === s ? n : -1; }
  function show(s, nums = false) {
    if (nums) { const n = natOf(s); if (n >= 0) return String(n); }
    if (!s.m.length) return '∅';
    return '{' + s.m.map(x => show(x, nums)).join(', ') + '}';
  }
  // Parser. Returns { set, raw } where raw keeps the order/duplicates as typed.
  function parse(str, nums = true) {
    const s = String(str).replace(/｛/g, '{').replace(/｝/g, '}').replace(/，/g, ',').replace(/\s+/g, '');
    let i = 0;
    function S() {
      const c = s[i];
      if (c === undefined) throw new ParseError('Input ends too early', '输入不完整，结尾缺少内容');
      if ('∅Øø⌀'.includes(c)) { i++; return { kids: [], set: E }; }
      if (/\d/.test(c)) {
        if (!nums) throw new ParseError('Digits are not allowed here: use ∅ and braces', '这里不能用数字，请只用 ∅ 和花括号');
        let j = i;
        while (j < s.length && /\d/.test(s[j])) j++;
        const n = +s.slice(i, j);
        if (n > 8) throw new ParseError('Numerals above 8 are too big to draw', '大于 8 的数字太大，画不下');
        i = j;
        return { num: n, set: nat(n) };
      }
      if (c === '{') {
        i++;
        const kids = [];
        if (s[i] === '}') { i++; return { kids, set: E }; }
        for (;;) {
          kids.push(S());
          if (s[i] === ',') { i++; continue; }
          if (s[i] === '}') { i++; break; }
          if (s[i] === undefined) throw new ParseError('Missing “}”', '缺少右花括号“}”');
          throw new ParseError(`Expected “,” or “}” but found “${s[i]}”`, `此处应为“,”或“}”，却出现了“${s[i]}”`);
        }
        return { kids, set: mk(kids.map(k => k.set)) };
      }
      throw new ParseError(`Unexpected “${c}”`, `此处不应出现“${c}”`);
    }
    if (!s.length) throw new ParseError('Empty input', '输入为空');
    const r = S();
    if (i < s.length) throw new ParseError('Extra symbols after the set', '集合后面多出了符号');
    return r;
  }
  return { mk, E, has, union, cup, cap, subset, power, succ, nat, natOf, show, parse, cmp };
})();
// HF-END

/* ================= drawing helpers ================= */
function boxes(s, o = {}, d = 0) {
  if (o.nums && (d > 0 || o.numRoot)) {
    const n = HF.natOf(s);
    if (n >= 0) return `<span class="nb num" title="${n}">${n}</span>`;
  }
  if (!s.m.length) return `<span class="nb e d${d % 6}" title="∅"></span>`;
  return `<span class="nb d${d % 6}" title="${esc(HF.show(s, true))}">${s.m.map(x => boxes(x, o, d + 1)).join('')}</span>`;
}
function rawBoxes(r, d = 0) {
  if (r.num !== undefined) return boxes(r.set, {}, d);
  if (!r.kids.length) return `<span class="nb e d${d % 6}" title="∅"></span>`;
  return `<span class="nb d${d % 6}">${r.kids.map(k => rawBoxes(k, d + 1)).join('')}</span>`;
}
function treeSVG(container, s, o = {}) {
  container.innerHTML = '';
  if (s.size > 90) {
    container.innerHTML = `<div class="msg warn">${bi(`This tree has ${s.size} nodes, too many to draw.`, `这棵树有 ${s.size} 个结点，太多了，画不下。`)}</div>`;
    return;
  }
  let leaf = 0, maxD = 0;
  const nodes = [];
  function walk(x, d) {
    maxD = Math.max(maxD, d);
    const n = { s: x, d, ch: [] };
    nodes.push(n);
    if (!x.m.length) n.x = leaf++;
    else { n.ch = x.m.map(y => walk(y, d + 1)); n.x = (n.ch[0].x + n.ch[n.ch.length - 1].x) / 2; }
    return n;
  }
  walk(s, 0);
  const GX = o.gx || 38, GY = o.gy || 54;
  const W = Math.max(leaf * GX + 20, 140), H = (maxD + 1) * GY + 10;
  const svg = el('svg', { viewBox: `0 0 ${W} ${H}`, width: W, height: H }, container);
  const px = n => 10 + GX / 2 + n.x * GX, py = n => 22 + n.d * GY;
  nodes.forEach(n => n.ch.forEach(c => {
    const ln = el('line', { x1: px(n), y1: py(n), x2: px(c), y2: py(c), class: 'tedge fadein' }, svg);
    ln.style.animationDelay = (c.d * 0.15) + 's';
  }));
  const COLORS = ['#3b5bdb', '#2f9e44', '#f08c00', '#ae3ec9', '#0c8599', '#e03131'];
  nodes.forEach(n => {
    const g = el('g', { transform: `translate(${px(n)},${py(n)})` }, svg);
    const inner = el('g', { class: 'pop' }, g);
    inner.style.animationDelay = (n.d * 0.15) + 's';
    const empty = !n.s.m.length;
    el('circle', { r: 12, fill: empty ? '#fff' : '#fff', stroke: COLORS[n.d % 6], 'stroke-width': 2.5 }, inner);
    const nm = HF.natOf(n.s);
    const lab = empty ? '∅' : (o.nums && nm >= 0 ? String(nm) : '');
    if (lab) svgText(inner, 0, 1, lab, { 'text-anchor': 'middle', 'dominant-baseline': 'central', 'font-size': 13, 'font-weight': 700 });
    else el('circle', { r: 3, fill: COLORS[n.d % 6] }, inner);
    const t = el('title', {}, g);
    t.textContent = HF.show(n.s);
  });
}
// Step-by-step reveal. onDone fires only when the user reveals the last step themselves.
function stepper(stepsEl, nextBtn, allBtn, onDone) {
  const steps = [...stepsEl.querySelectorAll('.step')];
  let k = 0;
  nextBtn.addEventListener('click', () => {
    if (k < steps.length) steps[k++].classList.add('on');
    if (k === steps.length) { nextBtn.disabled = true; onDone && onDone(); }
  });
  allBtn.addEventListener('click', () => { steps.forEach(s => s.classList.add('on')); k = steps.length; nextBtn.disabled = true; });
}
// Multiple-choice block.
function choice(box, opts, msg, onRight) {
  let revealed = false; // after reveal(), a correct click no longer earns progress this session
  const btns = opts.map(o => {
    const b = document.createElement('button');
    b.className = 'btn choice';
    b.innerHTML = o.en === o.zh ? `<span class="m">${o.en}</span>` : bi(o.en, o.zh);
    b.addEventListener('click', () => {
      btns.forEach(x => x.classList.remove('right', 'wrongc'));
      b.classList.add(o.ok ? 'right' : 'wrongc');
      okBox(msg, bi(o.fen, o.fzh), o.ok ? 'ok' : 'bad');
      if (o.ok && onRight && !revealed) onRight();
    });
    box.appendChild(b);
    return b;
  });
  return { reveal() { revealed = true; const i = opts.findIndex(o => o.ok); btns[i].classList.add('right'); okBox(msg, bi(opts[i].fen, opts[i].fzh), 'info'); } };
}
let lastSetInput = null;

/* ================= §1 Russell flip-flop ================= */
(function russell() {
  const svg = $('russell');
  const CW = 160, CH = 34;
  const cands = [
    { lab: '∅', self: false, en: '∅ has no members at all, so certainly ∅ ∉ ∅. Admitted: ∅ ∈ R.', zh: '∅ 没有任何元素，当然 ∅ ∉ ∅。放行：∅ ∈ R。' },
    { lab: '{∅}', self: false, en: 'The only member of {∅} is ∅, and ∅ ≠ {∅}. So {∅} ∉ {∅}. Admitted.', zh: '{∅} 唯一的元素是 ∅，而 ∅ ≠ {∅}，所以 {∅} ∉ {∅}。放行。' },
    { lab: 'ℕ', self: false, en: 'ℕ is not a natural number, so ℕ ∉ ℕ. Admitted.', zh: 'ℕ 本身不是自然数，所以 ℕ ∉ ℕ。放行。' },
    { lab: 'V: all sets · 全集', self: true, en: 'Naively, the set V of all sets is a set, so V ∈ V. Rejected at the door.', zh: '按朴素的想法，全体集合之集 V 自己也是集合，所以 V ∈ V。被门卫拦下。' },
    { lab: 'W: ∞ sets · 无穷集', self: true, en: 'W = the set of all infinite sets. W is itself infinite, so W ∈ W. Rejected.', zh: 'W ＝ 全体无穷集组成的集合。W 自己也是无穷的，所以 W ∈ W。被拦下。' },
    { lab: 'R', self: null },
  ];
  const trayPos = i => i === 5 ? [95, 228] : [18 + (i % 2) * 168, 62 + Math.floor(i / 2) * 52];
  const INSIDE_R = [520, 190], BORDER = [262, 190];
  let token = 0, inCount = 0;
  let status;
  function setStatus(txt, color) { status.textContent = txt; status.setAttribute('fill', color); }
  function move(c, [x, y]) { c.g.style.transform = `translate(${x}px, ${y}px)`; }
  function draw() {
    token++;
    inCount = 0;
    svg.innerHTML = '';
    el('rect', { x: 8, y: 30, width: 338, height: 250, rx: 14, fill: '#f1efe7', stroke: '#d8d3c4', 'stroke-dasharray': '5 5' }, svg);
    svgText(svg, 20, 50, 'candidates · 候选者', { 'font-size': 13, fill: '#888' });
    el('rect', { x: 362, y: 30, width: 410, height: 250, rx: 14, fill: '#eef2ff', stroke: '#3b5bdb', 'stroke-width': 3 }, svg);
    svgText(svg, 378, 52, 'R = {x : x ∉ x}', { 'font-size': 17, 'font-weight': 700, fill: '#3b5bdb' });
    svgText(svg, 352, 168, '🚪', { 'font-size': 22, 'text-anchor': 'middle' });
    status = svgText(svg, 390, 312, '', { 'font-size': 17, 'font-weight': 800 });
    cands.forEach((c, i) => {
      c.state = 'tray';
      const g = el('g', { style: 'cursor:pointer;transition:transform .8s cubic-bezier(.3,1.2,.4,1)' }, svg);
      c.rect = el('rect', { width: CW, height: CH, rx: 10, fill: i === 5 ? '#f8e7fc' : '#fff', stroke: i === 5 ? '#ae3ec9' : '#868e96', 'stroke-width': 2 }, g);
      c.text = svgText(g, CW / 2, CH / 2 + 5, c.lab, { 'text-anchor': 'middle', 'font-size': i === 5 ? 18 : 13, 'font-weight': 700, fill: i === 5 ? '#ae3ec9' : '#1f2430' });
      c.g = g;
      move(c, trayPos(i));
      g.addEventListener('click', () => click(c, i));
    });
    $('rFormal').style.display = 'none';
    okBox($('rMsg'), bi('Click the candidates. Which ones belong in R?', '点击候选者。哪些该进 R？'), 'info');
  }
  async function click(c, i) {
    if (c.state !== 'tray') return;
    if (i < 5) {
      if (c.self) {
        c.state = 'rejected';
        move(c, [INSIDE_R[0] - 260, trayPos(i)[1]]);
        await sleep(450);
        move(c, trayPos(i));
        c.rect.setAttribute('stroke', '#e03131');
        c.rect.setAttribute('fill', '#ffe3e3');
        c.text.textContent = c.lab + ' ✗';
        c.text.setAttribute('font-size', 11.5);
        okBox($('rMsg'), bi(c.en, c.zh), 'bad');
      } else {
        c.state = 'in';
        const k = inCount++;
        move(c, [380 + (k % 2) * 190, 70 + Math.floor(k / 2) * 46]);
        c.rect.setAttribute('stroke', '#2f9e44');
        c.rect.setAttribute('fill', '#d3f9d8');
        okBox($('rMsg'), bi(c.en, c.zh), 'ok');
      }
      return;
    }
    // R itself: the flip-flop
    c.state = 'running';
    const my = token;
    for (let round = 0; round < 3; round++) {
      move(c, INSIDE_R);
      setStatus('R ∈ R ?  → suppose YES · 假设“是”', '#2f9e44');
      okBox($('rMsg'), bi('Suppose <b>R ∈ R</b>. Members of R satisfy x ∉ x, so R ∉ R. The doorkeeper throws it out!',
        '假设 <b>R ∈ R</b>。R 的元素都满足 x ∉ x，于是 R ∉ R。门卫把它赶了出去！'), 'warn');
      await sleep(1700);
      if (my !== token) return;
      move(c, trayPos(5));
      setStatus('R ∈ R ?  → then NO · 那么“否”', '#e03131');
      okBox($('rMsg'), bi('So <b>R ∉ R</b>. But then R satisfies x ∉ x, which is exactly the entry condition, so R ∈ R. Back in it goes!',
        '于是 <b>R ∉ R</b>。可这样一来 R 恰好满足入场条件 x ∉ x，所以 R ∈ R。又被拉了回去！'), 'warn');
      await sleep(1700);
      if (my !== token) return;
    }
    move(c, BORDER);
    c.rect.setAttribute('stroke', '#e03131');
    c.rect.setAttribute('fill', '#ffe3e3');
    setStatus('R ∈ R  ⇔  R ∉ R   ⚡', '#e03131');
    okBox($('rMsg'), bi('<b>Contradiction:</b> R ∈ R ⇔ R ∉ R. R can be neither inside nor outside, so R does not exist and naive comprehension is <b>inconsistent</b>.',
      '<b>矛盾：</b>R ∈ R ⇔ R ∉ R。R 既不能在里面，也不能在外面，所以 R 不存在，朴素概括原则是<b>不一致</b>的。'), 'bad');
    $('rFormal').style.display = '';
  }
  $('rReset').addEventListener('click', draw);
  draw();
})();

/* ================= §2 membership matrix ================= */
(function matrix() {
  const svg = $('mx');
  const N = 6, CS = 40, X0 = 70, Y0 = 62, DX = X0 + N * CS + 22;
  let M = [
    [0, 1, 1, 0, 1, 0], [0, 1, 0, 1, 0, 0], [0, 0, 0, 1, 1, 1],
    [1, 0, 0, 0, 1, 0], [0, 0, 1, 0, 1, 0], [1, 1, 0, 0, 0, 0],
  ];
  let hover = -1;
  function draw() {
    svg.innerHTML = '';
    svgText(svg, X0 + N * CS / 2, 16, 'y (as a set · 作为集合)', { 'text-anchor': 'middle', 'font-size': 12, fill: '#888' });
    svgText(svg, 6, Y0 - 8, 'x ∈ y ?', { 'font-size': 12, fill: '#888' });
    for (let j = 0; j < N; j++) svgText(svg, X0 + j * CS + CS / 2, Y0 - 10, 'x' + sub(j), { 'text-anchor': 'middle', 'font-size': 14, 'font-weight': 700, fill: '#3b5bdb' });
    svgText(svg, DX + CS / 2, Y0 - 10, 'd', { 'text-anchor': 'middle', 'font-size': 16, 'font-weight': 800, fill: '#ae3ec9' });
    for (let i = 0; i < N; i++) {
      svgText(svg, X0 - 12, Y0 + i * CS + CS / 2 + 5, 'x' + sub(i), { 'text-anchor': 'end', 'font-size': 14, 'font-weight': 700 });
      for (let j = 0; j < N; j++) {
        const hl = hover === j;
        const r = el('rect', { x: X0 + j * CS + 2, y: Y0 + i * CS + 2, width: CS - 4, height: CS - 4, rx: 6,
          fill: M[i][j] ? '#d3f9d8' : '#ffe3e3', stroke: i === j ? '#f08c00' : hl ? '#3b5bdb' : 'none', 'stroke-width': i === j ? 3 : 2, style: 'cursor:pointer' }, svg);
        if (hl && i === j) { r.setAttribute('stroke', '#ae3ec9'); r.setAttribute('stroke-width', 4); }
        const t = svgText(svg, X0 + j * CS + CS / 2, Y0 + i * CS + CS / 2 + 5, M[i][j], { 'text-anchor': 'middle', 'font-size': 15, 'pointer-events': 'none' });
        if (i === j) t.setAttribute('font-weight', 800);
        r.addEventListener('click', () => { M[i][j] ^= 1; draw(); });
        r.addEventListener('mouseenter', () => { if (hover !== j) { hover = j; draw(); } });
      }
      const dv = 1 - M[i][i];
      el('rect', { x: DX + 2, y: Y0 + i * CS + 2, width: CS - 4, height: CS - 4, rx: 6, fill: '#f8e7fc',
        stroke: hover === i ? '#ae3ec9' : '#d0a8dc', 'stroke-width': hover === i ? 4 : 1.5 }, svg);
      svgText(svg, DX + CS / 2, Y0 + i * CS + CS / 2 + 5, dv, { 'text-anchor': 'middle', 'font-size': 15, 'font-weight': 800, fill: '#ae3ec9' });
    }
    if (hover >= 0) {
      const y = Y0 + hover * CS + CS / 2;
      el('line', { x1: X0 + hover * CS + CS - 2, y1: y, x2: DX + 2, y2: y, stroke: '#ae3ec9', 'stroke-width': 2, 'stroke-dasharray': '4 3' }, svg);
    }
    svgText(svg, X0, Y0 + N * CS + 26, 'd(xᵢ) = 1 − M(xᵢ, xᵢ)  ⇒  d ≠ every column · d 与每一列都不同', { 'font-size': 12.5, fill: '#ae3ec9', 'font-weight': 700 });
    const j = hover;
    if (j >= 0) okBox($('mxMsg'), bi(`Column <b>x${sub(j)}</b> vs <b>d</b>: in row x${sub(j)} the column says x${sub(j)} ${M[j][j] ? '∈' : '∉'} x${sub(j)}, while d says x${sub(j)} ${M[j][j] ? '∉' : '∈'} d. They differ, so <b>d ≠ x${sub(j)}</b>. This works for every column, whatever you click.`,
      `比较第 <b>x${sub(j)}</b> 列和 <b>d</b>：在 x${sub(j)} 这一行，该列给出 x${sub(j)} ${M[j][j] ? '∈' : '∉'} x${sub(j)}，而 d 给出 x${sub(j)} ${M[j][j] ? '∉' : '∈'} d。两者不同，所以 <b>d ≠ x${sub(j)}</b>。无论你怎么改格子，每一列都逃不掉。`), 'info');
    else okBox($('mxMsg'), bi('Hover a column to compare it with d.', '把鼠标移到某一列上，与 d 比较。'), 'info');
  }
  svg.addEventListener('mouseleave', () => { hover = -1; draw(); });
  $('mxRand').addEventListener('click', () => { M = M.map(r => r.map(() => Math.random() < 0.4 ? 1 : 0)); draw(); });
  $('mxClear').addEventListener('click', () => { M = M.map(r => r.map(() => 0)); draw(); });
  draw();
})();

/* ================= §3 viewer + extensionality ================= */
(function viewer() {
  const presets = ['∅', '{∅}', '{{∅}}', '{∅, {∅}}', '{∅, {∅}, {{∅}}}', '{{∅, {∅}}}', '{{{{∅}}}}', '3'];
  presets.forEach(p => {
    const b = document.createElement('button');
    b.className = 'btn small';
    b.innerHTML = `<span class="m">${p}</span>`;
    b.addEventListener('click', () => { $('hfIn').value = p; go(); });
    $('hfPresets').appendChild(b);
  });
  function go() {
    let r;
    try { r = HF.parse($('hfIn').value); } catch (e) { errBox($('hfErr'), e); return; }
    clearBox($('hfErr'));
    const s = r.set;
    $('hfBoxes').innerHTML = `<div class="pop" style="display:inline-block">${boxes(s)}</div><div class="bigtext" style="margin-top:8px">${HF.show(s)}</div>`;
    treeSVG($('hfTree'), s);
    const trans = s.m.every(x => HF.subset(x, s));
    $('hfStats').innerHTML = `<span class="stat">|A| = ${s.m.length}</span><span class="stat">${bil('rank', '秩')} = ${s.rank}</span>` +
      `<span class="stat">${bil('brace pairs', '花括号对数')} = ${s.size}</span>` +
      `<span class="stat">${trans ? bil('transitive ✓', '传递集 ✓') : bil('not transitive', '非传递集')}</span>` +
      (HF.natOf(s) >= 0 ? `<span class="stat">= ${HF.natOf(s)} ${bil('(von Neumann)', '（冯·诺伊曼）')}</span>` : '');
  }
  $('hfGo').addEventListener('click', go);
  $('hfIn').addEventListener('keydown', e => e.key === 'Enter' && go());
  go();

  function compare() {
    let a, b;
    const out = $('exOut');
    try { a = HF.parse($('exA').value); $('exAraw').innerHTML = rawBoxes(a); } catch (e) { $('exAraw').innerHTML = `<div class="msg bad">${e.html ? e.html() : e}</div>`; out.innerHTML = ''; return; }
    try { b = HF.parse($('exB').value); $('exBraw').innerHTML = rawBoxes(b); } catch (e) { $('exBraw').innerHTML = `<div class="msg bad">${e.html ? e.html() : e}</div>`; out.innerHTML = ''; return; }
    const A = a.set, B = b.set;
    const row = (X, Y, nm) => X.m.map(x => `<div class="m" style="font-size:14px">${HF.has(Y, x) ? '<span style="color:var(--true)">✓</span>' : '<span style="color:var(--false)">✗</span>'} ${HF.show(x)} ${HF.has(Y, x) ? '∈' : '∉'} ${nm}</div>`).join('');
    let h = `<div class="row" style="margin-top:8px"><div class="col panel"><h4>${bil('members of the left set, looked up on the right', '左边集合的元素，到右边查找')}</h4>${row(A, B, 'B')}</div>
      <div class="col panel"><h4>${bil('members of the right set, looked up on the left', '右边集合的元素，到左边查找')}</h4>${row(B, A, 'A')}</div></div>`;
    if (A === B) h += `<div class="msg ok">${bi(`Same members, so by Extensionality they are <b>the same set</b>: ${HF.show(A)}. The drawings differ only in order and repetition. Here is the canonical drawing:`, `元素完全相同，由外延公理它们是<b>同一个集合</b>：${HF.show(A)}。两幅图只是次序和重复不同。下面是规范画法：`)}<div style="margin-top:6px" class="pop">${boxes(A)}</div></div>`;
    else h += `<div class="msg bad">${bi('Some member (✗) is missing on the other side, so these are <b>different sets</b>.', '有元素（✗）在另一边找不到，所以它们是<b>不同的集合</b>。')}</div>`;
    out.innerHTML = h;
  }
  $('exGo').addEventListener('click', compare);
  [$('exA'), $('exB')].forEach(i => i.addEventListener('keydown', e => e.key === 'Enter' && compare()));
  document.querySelectorAll('[data-ex]').forEach(b => b.addEventListener('click', () => {
    const [x, y] = b.dataset.ex.split('|');
    $('exA').value = x; $('exB').value = y; compare();
  }));
  compare();
})();

/* ================= §4 unfolding abbreviations ================= */
(function unfold() {
  const pair = (p, a, b, w = 'w', u = 'u') => `∀${w} (${w} ∈ ${p} ↔ (∀${u} (${u} ∈ ${w} ↔ ${u} = ${a}) ∨ ∀${u} (${u} ∈ ${w} ↔ (${u} = ${a} ∨ ${u} = ${b}))))`;
  const items = [
    { n: 'x ⊆ y', L: ['[[x ⊆ y]]', '∀z (z ∈ x → z ∈ y)'] },
    { n: 'z = ∅', L: ['[[z = ∅]]', '∀w ¬(w ∈ z)'] },
    { n: 'z = {x, y}', L: ['[[z = {x, y}]]', '∀w (w ∈ z ↔ (w = x ∨ w = y))'] },
    { n: 'z = x ∪ y', L: ['[[z = x ∪ y]]', '∀w (w ∈ z ↔ (w ∈ x ∨ w ∈ y))'] },
    { n: 'z = ⋃x', L: ['[[z = ⋃x]]', '∀w (w ∈ z ↔ ∃u (u ∈ x ∧ w ∈ u))'] },
    { n: 'z = 𝒫(x)', L: ['[[z = 𝒫(x)]]', '∀w (w ∈ z ↔ [[w ⊆ x]])', '∀w (w ∈ z ↔ ∀u (u ∈ w → u ∈ x))'] },
    { n: 'p = (a, b)', L: ['[[p = (a, b)]]', '[[p = {{a}, {a, b}}]]', '∀w (w ∈ p ↔ ([[w = {a}]] ∨ [[w = {a, b}]]))', pair('p', 'a', 'b')] },
    { n: bil('f is a function', 'f 是函数'), L: [
      '[[Fun(f)]]',
      '∀p (p ∈ f → ∃a ∃b [[p = (a, b)]]) ∧ ∀a ∀b ∀c (([[(a, b) ∈ f]] ∧ [[(a, c) ∈ f]]) → b = c)',
      '∀p (p ∈ f → ∃a ∃b [[p = (a, b)]]) ∧ ∀a ∀b ∀c ((∃p (p ∈ f ∧ [[p = (a, b)]]) ∧ ∃q (q ∈ f ∧ [[q = (a, c)]])) → b = c)',
      `∀p (p ∈ f → ∃a ∃b ${pair('p', 'a', 'b')}) ∧ ∀a ∀b ∀c ((∃p (p ∈ f ∧ ${pair('p', 'a', 'b')}) ∧ ∃q (q ∈ f ∧ ${pair('q', 'a', 'c')})) → b = c)`] },
  ];
  const box = $('unfold');
  const MAXLEN = Math.max(...items.map(it => it.L[it.L.length - 1].length));
  items.forEach(it => {
    it.lv = 0;
    const row = document.createElement('div');
    row.className = 'unf';
    row.innerHTML = `<div><b class="m">${it.n}</b></div><div><div class="fm"></div><div class="bar"></div><div class="muted cnt" style="font-size:12px"></div></div>
      <div style="white-space:nowrap"><button class="btn small" data-a="-">◂</button> <button class="btn small" data-a="+">${bil('unfold ▸', '展开 ▸')}</button></div>`;
    box.appendChild(row);
    it.render = () => {
      const raw = it.L[it.lv];
      const plain = raw.replace(/\[\[|\]\]/g, '');
      const abs = (raw.match(/\[\[/g) || []).length;
      const html = esc(raw).replace(/∈/g, '<span class="in">∈</span>').replace(/\[\[(.*?)\]\]/g, '<span class="ab">$1</span>');
      row.querySelector('.fm').innerHTML = `<span class="fadein">${html}</span>`;
      row.querySelector('.bar').style.width = Math.max(3, 100 * plain.length / MAXLEN) + '%';
      const nsym = plain.replace(/\s/g, '').length;
      row.querySelector('.cnt').innerHTML = bil(`${nsym} symbols`, `${nsym} 个符号`) + ' · ' +
        (abs ? bil(`${abs} abbreviation(s) left`, `还有 ${abs} 处缩写待展开`) : `<span style="color:var(--true)">${bil('pure ∈ / = formula ✓', '纯 ∈ / = 公式 ✓')}</span>`);
      row.querySelector('[data-a="+"]').disabled = it.lv === it.L.length - 1;
      row.querySelector('[data-a="-"]').disabled = it.lv === 0;
    };
    row.querySelector('[data-a="+"]').addEventListener('click', () => { it.lv = Math.min(it.L.length - 1, it.lv + 1); it.render(); });
    row.querySelector('[data-a="-"]').addEventListener('click', () => { it.lv = Math.max(0, it.lv - 1); it.render(); });
    it.render();
  });
  $('unfAll').addEventListener('click', () => items.forEach(it => { it.lv = it.L.length - 1; it.render(); }));
  $('unfNone').addEventListener('click', () => items.forEach(it => { it.lv = 0; it.render(); }));
})();

/* ================= §5 axioms + workshop + Hasse ================= */
const AXIOMS = [
  { en: 'Extensionality', zh: '外延公理', f: '∀x ∀y (∀z (z ∈ x ↔ z ∈ y) → x = y)', men: 'Sets with the same members are equal.', mzh: '元素相同的集合相等。', at: '#s3' },
  { en: 'Empty set', zh: '空集公理', f: '∃x ∀y ¬(y ∈ x)', men: 'There is a set with no members; by Extensionality it is unique, called ∅.', mzh: '存在一个没有元素的集合；由外延公理它唯一，记作 ∅。', at: '#s5' },
  { en: 'Pairing', zh: '配对公理', f: '∀a ∀b ∃c ∀x (x ∈ c ↔ (x = a ∨ x = b))', men: 'For any a, b the set {a, b} exists. With a = b this gives {a}.', mzh: '对任意 a、b，集合 {a, b} 存在。取 a = b 便得 {a}。', at: '#s5' },
  { en: 'Union', zh: '并集公理', f: '∀A ∃U ∀x (x ∈ U ↔ ∃Y (Y ∈ A ∧ x ∈ Y))', men: '⋃A, the set of members of members of A, exists. Then a ∪ b = ⋃{a, b}.', mzh: '⋃A（A 的元素的元素全体）存在。于是 a ∪ b = ⋃{a, b}。', at: '#s5' },
  { en: 'Power set', zh: '幂集公理', f: '∀A ∃P ∀x (x ∈ P ↔ ∀z (z ∈ x → z ∈ A))', men: '𝒫(A), the set of all subsets of A, exists.', mzh: '𝒫(A)，即 A 的全体子集组成的集合，存在。', at: '#s5' },
  { en: 'Separation (schema)', zh: '分离公理模式', f: '∀p₁…∀pₙ ∀A ∃y ∀x (x ∈ y ↔ (x ∈ A ∧ φ(x, p₁, …, pₙ)))', men: 'You may carve a subset {x ∈ A : φ(x)} out of an existing set A, for any formula φ.', mzh: '对任意公式 φ，可以从已有集合 A 中切出子集 {x ∈ A : φ(x)}。', at: '#s6' },
  { en: 'Replacement (schema)', zh: '替换公理模式', f: '∀p₁…∀pₙ ∀A [∀x∈A ∃!y φ(x,y,p₁…pₙ) → ∃B ∀y (y ∈ B ↔ ∃x∈A φ(x,y,p₁…pₙ))]', men: 'The image of a set under a definable function is a set.', mzh: '集合在可定义函数下的像是集合。', at: '#s7' },
  { en: 'Infinity', zh: '无穷公理', f: '∃I (∅ ∈ I ∧ ∀x (x ∈ I → x ∪ {x} ∈ I))', men: 'There is an inductive set.', mzh: '存在归纳集。', at: '#s8' },
  { en: 'Foundation', zh: '正则公理（基础公理）', f: '∀x (x ≠ ∅ → ∃y (y ∈ x ∧ y ∩ x = ∅))', men: 'Every nonempty set has an ∈-minimal member.', mzh: '每个非空集合都有 ∈-极小元。', at: '#s9' },
  { en: 'Choice (ZFC)', zh: '选择公理（ZFC）', f: '∀F (∅ ∉ F → ∃f (f : F → ⋃F ∧ ∀X ∈ F f(X) ∈ X))', men: 'Every family of nonempty sets has a choice function. Lesson 10.', mzh: '每个非空集合族都有选择函数。见第 10 课。', at: '#s9' },
];
(function axiomChips() {
  const btns = AXIOMS.map((a, i) => {
    const b = document.createElement('button');
    b.className = 'btn small';
    b.innerHTML = `${i + 1}. ${bil(a.en, a.zh)}`;
    b.addEventListener('click', () => showAx(i));
    $('axChips').appendChild(b);
    return b;
  });
  function showAx(i) {
    const a = AXIOMS[i];
    btns.forEach((b, j) => b.classList.toggle('sel', i === j));
    $('axCard').innerHTML = `<b>${bil(a.en, a.zh)}</b><div class="formal">${a.f}</div>${bi(a.men, a.mzh)} <a href="${a.at}" style="font-size:13px">${bil('see the visual', '去看图示')} ${a.at.replace('#s', '§')}</a>`;
  }
  showAx(0);
})();

const PREDS = [
  { f: 'x ≠ ∅', en: 'x ≠ ∅', test: x => x.m.length > 0 },
  { f: '∅ ∈ x', en: '∅ ∈ x', test: x => HF.has(x, HF.E) },
  { f: '∅ ∉ x', en: '∅ ∉ x', test: x => !HF.has(x, HF.E) },
  { f: '|x| = 1', en: 'x is a singleton', zh: 'x 是单元素集', test: x => x.m.length === 1 },
  { f: 'x ∉ x', en: 'x ∉ x', test: x => !HF.has(x, x) },
];
(function workshop() {
  const sel = $('sepPred');
  PREDS.forEach((p, i) => { const o = document.createElement('option'); o.value = i; o.textContent = 'φ(x): ' + p.f; sel.appendChild(o); });
  const targets = ['{∅}', '{{∅}}', '{∅, {∅}}', '{{∅}, {{∅}}}', '{∅, {∅}, {{∅}}}', '{∅, {∅}, {∅, {∅}}}'].map(t => ({ t, s: HF.parse(t).set }));
  let cards = [], picked = [], counter = 0;
  function add(s, how, fromIdx) {
    const ex = cards.findIndex(c => c.s === s);
    if (ex >= 0) {
      okBox($('wsMsg'), bi(`You already have this set: it is <b>${cards[ex].name}</b>. By Extensionality, same members means same set, so nothing new is created.`,
        `这个集合已经有了，就是 <b>${cards[ex].name}</b>。由外延公理，元素相同即为同一集合，不会产生新东西。`), 'warn');
      render(ex);
      return;
    }
    if (s.size > 140) { okBox($('wsMsg'), bi(`The axiom guarantees this set exists, but it has ${s.size} nested boxes, too many to draw here.`, `公理保证这个集合存在，但它有 ${s.size} 层嵌套盒子，这里画不下。`), 'warn'); return; }
    if (cards.length >= 16) cards.shift();
    cards.push({ s, name: 's' + sub(counter++), how });
    okBox($('wsMsg'), bi(`New set: <b>${cards[cards.length - 1].name}</b> ${how.en}.`, `新集合 <b>${cards[cards.length - 1].name}</b> ${how.zh}。`), 'ok');
    picked = [];
    render(cards.length - 1);
  }
  function render(flash = -1) {
    const ws = $('ws');
    ws.innerHTML = '';
    cards.forEach((c, i) => {
      const d = document.createElement('div');
      d.className = 'wcard' + (picked.includes(i) ? ' sel' : '') + (i === flash ? ' pop' : '');
      d.innerHTML = `<span class="nm">${c.name} <small>${bil(c.how.en, c.how.zh)}</small></span><div>${boxes(c.s)}</div><div class="tx">${HF.show(c.s)}</div>` + (i ? '<span class="x" title="remove · 删除">✕</span>' : '');
      d.addEventListener('click', e => {
        if (e.target.classList.contains('x')) { cards.splice(i, 1); picked = []; render(); return; }
        if (picked.includes(i)) picked = picked.filter(j => j !== i);
        else { picked.push(i); if (picked.length > 2) picked.shift(); }
        render();
      });
      ws.appendChild(d);
    });
    $('targets').innerHTML = `<b style="font-size:13px">${bil('Targets', '目标')}:</b>` + targets.map(t => `<span class="${cards.some(c => c.s === t.s) ? 'got' : ''}">${t.t}${cards.some(c => c.s === t.s) ? ' ✓' : ''}</span>`).join('');
  }
  const need = (n, en, zh) => {
    if (picked.length === n || (n === 12 && picked.length >= 1)) return true;
    okBox($('wsMsg'), bi(en, zh), 'warn');
    return false;
  };
  const nm = i => cards[i].name;
  $('opPair').addEventListener('click', () => {
    if (!need(12, 'Select one or two cards first.', '请先选中一两张卡片。')) return;
    const [i, j = picked[0]] = picked;
    add(HF.mk([cards[i].s, cards[j].s]), { en: `= {${nm(i)}, ${nm(j)}} by Pairing`, zh: `= {${nm(i)}, ${nm(j)}}，由配对公理` });
  });
  $('opUnion').addEventListener('click', () => {
    if (!need(1, 'Select exactly one card.', '请恰好选中一张卡片。')) return;
    const i = picked[0];
    add(HF.union(cards[i].s), { en: `= ⋃${nm(i)} by Union`, zh: `= ⋃${nm(i)}，由并集公理` });
  });
  $('opCup').addEventListener('click', () => {
    if (!need(2, 'Select exactly two cards.', '请恰好选中两张卡片。')) return;
    const [i, j] = picked;
    add(HF.cup(cards[i].s, cards[j].s), { en: `= ${nm(i)} ∪ ${nm(j)} by Pairing + Union`, zh: `= ${nm(i)} ∪ ${nm(j)}，由配对 + 并集公理` });
  });
  $('opPow').addEventListener('click', () => {
    if (!need(1, 'Select exactly one card.', '请恰好选中一张卡片。')) return;
    const i = picked[0];
    if (cards[i].s.m.length > 4) { okBox($('wsMsg'), bi('That power set would have more than 16 members. It exists, but let us keep the drawing small: pick a set with ≤ 4 members.', '这个幂集会有 16 个以上的元素。它当然存在，但为了画得下，请选元素不超过 4 个的集合。'), 'warn'); return; }
    add(HF.power(cards[i].s), { en: `= 𝒫(${nm(i)}) by Power set`, zh: `= 𝒫(${nm(i)})，由幂集公理` });
  });
  $('opSep').addEventListener('click', () => {
    if (!need(1, 'Select exactly one card (the set to filter).', '请恰好选中一张卡片（被筛选的集合）。')) return;
    const i = picked[0], p = PREDS[+sel.value];
    add(HF.mk(cards[i].s.m.filter(p.test)), { en: `= {x ∈ ${nm(i)} : ${p.f}} by Separation`, zh: `= {x ∈ ${nm(i)} : ${p.f}}，由分离公理` });
  });
  function reset() {
    cards = [{ s: HF.E, name: 's₀', how: { en: '= ∅ by Empty set', zh: '= ∅，由空集公理' } }];
    counter = 1; picked = [];
    clearBox($('wsMsg'));
    render();
  }
  $('wsReset').addEventListener('click', reset);
  reset();
})();

(function hasse() {
  const svg = $('hasse');
  const names = ['a', 'b', 'c', 'd'];
  let selMask = -1;
  const pc = m => { let c = 0; while (m) { c += m & 1; m >>= 1; } return c; };
  function draw() {
    const n = +$('hsN').value;
    $('hsNv').textContent = n;
    $('hsCount').innerHTML = `&nbsp; |𝒫(A)| = 2<sup>${n}</sup> = <b>${1 << n}</b>`;
    svg.innerHTML = '';
    const levels = Array.from({ length: n + 1 }, () => []);
    for (let m = 0; m < (1 << n); m++) levels[pc(m)].push(m);
    const pos = {};
    levels.forEach((L, k) => {
      const sp = Math.min(118, 660 / L.length);
      L.forEach((m, i) => { pos[m] = [350 + (i - (L.length - 1) / 2) * sp, 300 - k * (270 / n)]; });
    });
    const rel = m => selMask < 0 ? '' : m === selMask ? 'self' : (m & selMask) === m ? 'sub' : (m & selMask) === selMask ? 'sup' : '';
    for (let m = 0; m < (1 << n); m++) for (let b = 0; b < n; b++) if (!(m & (1 << b))) {
      const m2 = m | (1 << b);
      const r1 = rel(m), r2 = rel(m2);
      const on = (r1 === 'sub' || r1 === 'self') && (r2 === 'sub' || r2 === 'self') ? '#2f9e44' : (r1 === 'sup' || r1 === 'self') && (r2 === 'sup' || r2 === 'self') ? '#3b5bdb' : '#d0ccc0';
      el('line', { x1: pos[m][0], y1: pos[m][1], x2: pos[m2][0], y2: pos[m2][1], stroke: on, 'stroke-width': on === '#d0ccc0' ? 1.5 : 3 }, svg);
    }
    for (let m = 0; m < (1 << n); m++) {
      const lab = m ? '{' + names.filter((_, b) => m & (1 << b)).join(',') + '}' : '∅';
      const w = Math.max(30, lab.length * 9 + 12);
      const r = rel(m);
      const g = el('g', { class: 'pop', style: 'cursor:pointer' }, svg);
      g.style.animationDelay = (pc(m) * 0.08) + 's';
      el('rect', { x: pos[m][0] - w / 2, y: pos[m][1] - 13, width: w, height: 26, rx: 8,
        fill: r === 'self' ? '#1f2430' : r === 'sub' ? '#d3f9d8' : r === 'sup' ? '#e7ecff' : '#fff',
        stroke: r === 'sub' ? '#2f9e44' : r === 'sup' ? '#3b5bdb' : '#1f2430', 'stroke-width': 1.5 }, g);
      svgText(g, pos[m][0], pos[m][1] + 5, lab, { 'text-anchor': 'middle', 'font-size': 14, fill: r === 'self' ? '#fff' : '#1f2430' });
      g.addEventListener('click', () => { selMask = selMask === m ? -1 : m; draw(); });
    }
    svgText(svg, 10, 20, 'A = {' + names.slice(0, n).join(', ') + '}', { 'font-size': 14, 'font-weight': 700, fill: '#3b5bdb' });
  }
  $('hsN').addEventListener('input', () => { selMask = -1; draw(); });
  draw();
})();

/* ================= §6 Separation sieve ================= */
(function sieve() {
  const As = ['{∅, {∅}, {{∅}}, {∅, {∅}}}', '{∅, {∅}, {∅, {∅}}}', '{{∅}, {{∅}}, {∅, {{∅}}}, {{∅}, {{∅}}}}'];
  As.forEach((a, i) => { const o = document.createElement('option'); o.value = i; o.textContent = a; $('svA').appendChild(o); });
  PREDS.forEach((p, i) => { const o = document.createElement('option'); o.value = i; o.textContent = p.f; $('svP').appendChild(o); });
  let token = 0;
  function setup() {
    token++;
    const A = HF.parse(As[+$('svA').value]).set;
    const p = PREDS[+$('svP').value];
    $('svTop').innerHTML = `<b class="m" style="margin-right:6px">A =</b>` + A.m.map((x, i) => `<div class="mem" id="svm${i}">${boxes(x, {}, 1)}<div class="m" style="font-size:12px;text-align:center">${HF.show(x)}</div></div>`).join('');
    $('svLine').textContent = `▼ ▼ ▼  φ(x) ≡ ${p.f}  ▼ ▼ ▼`;
    $('svBot').innerHTML = `<b class="m" style="margin-right:6px">{x ∈ A : ${p.f}} =</b>`;
    clearBox($('svMsg'));
    return { A, p };
  }
  async function run() {
    const { A, p } = setup();
    const my = token;
    const kept = [];
    for (let i = 0; i < A.m.length; i++) {
      const x = A.m[i], node = $('svm' + i);
      node.classList.add('look');
      await sleep(650);
      if (my !== token) return;
      node.classList.remove('look');
      if (p.test(x)) {
        node.classList.add('pass');
        kept.push(x);
        const d = document.createElement('div');
        d.className = 'mem pop';
        d.innerHTML = `${boxes(x, {}, 1)}<div class="m" style="font-size:12px;text-align:center">${HF.show(x)}</div>`;
        $('svBot').appendChild(d);
      } else node.classList.add('out');
    }
    const res = HF.mk(kept);
    let extra = '';
    if (p.f === 'x ∉ x') extra = bi('<br>Every member passed: with Foundation (§9) no set is a member of itself, so here <span class="m">R<sub>A</sub> = A</span>. And indeed <span class="m">A ∉ A</span>, as the theorem of §2 predicts.',
      '<br>所有元素都通过了：有了正则公理（§9），没有集合属于自身，所以这里 <span class="m">R<sub>A</sub> = A</span>。而 <span class="m">A ∉ A</span>，正如 §2 的定理所说。');
    okBox($('svMsg'), bi(`Result: <span class="m">${HF.show(res)}</span>, a subset of A, guaranteed to exist by Separation.`, `结果：<span class="m">${HF.show(res)}</span>，它是 A 的子集，由分离公理保证存在。`) + extra, 'ok');
  }
  $('svGo').addEventListener('click', run);
  $('svA').addEventListener('change', setup);
  $('svP').addEventListener('change', setup);
  $('svP').value = 4;
  run();

  // static comparison picture
  const svg = $('cmpSvg');
  const col = (x0, title, zh, ok) => {
    svgText(svg, x0 + 75, 18, title, { 'text-anchor': 'middle', 'font-size': 13, 'font-weight': 700, fill: ok ? '#2f9e44' : '#e03131' });
    svgText(svg, x0 + 75, 34, zh, { 'text-anchor': 'middle', 'font-size': 12, fill: '#666' });
    if (ok) {
      el('rect', { x: x0 + 35, y: 44, width: 80, height: 34, rx: 8, fill: '#e7ecff', stroke: '#3b5bdb', 'stroke-width': 2 }, svg);
      svgText(svg, x0 + 75, 66, 'A', { 'text-anchor': 'middle', 'font-size': 16, 'font-weight': 700, fill: '#3b5bdb' });
    } else {
      el('ellipse', { cx: x0 + 75, cy: 61, rx: 66, ry: 18, fill: '#f1efe7', stroke: '#999', 'stroke-dasharray': '4 4' }, svg);
      svgText(svg, x0 + 75, 66, 'everything? · 一切?', { 'text-anchor': 'middle', 'font-size': 11, fill: '#666' });
    }
    el('path', { d: `M${x0 + 35} 90 L${x0 + 115} 90 L${x0 + 85} 122 L${x0 + 85} 136 L${x0 + 65} 136 L${x0 + 65} 122 Z`, fill: '#fff4e6', stroke: '#f08c00', 'stroke-width': 2 }, svg);
    svgText(svg, x0 + 75, 108, 'φ', { 'text-anchor': 'middle', 'font-size': 14, 'font-weight': 700, fill: '#f08c00' });
    el('rect', { x: x0 + 30, y: 148, width: 90, height: 34, rx: 8, fill: ok ? '#d3f9d8' : '#ffe3e3', stroke: ok ? '#2f9e44' : '#e03131', 'stroke-width': 2 }, svg);
    svgText(svg, x0 + 75, 170, ok ? '{x∈A : φ} ✓' : '{x : φ} ✗', { 'text-anchor': 'middle', 'font-size': 13, 'font-weight': 700, fill: ok ? '#2f9e44' : '#e03131' });
    svgText(svg, x0 + 75, 200, ok ? 'a subset of A · A 的子集' : 'Russell! · 罗素悖论!', { 'text-anchor': 'middle', 'font-size': 11, fill: ok ? '#2f9e44' : '#e03131' });
  };
  col(0, 'Comprehension', '概括原则', false);
  col(165, 'Separation', '分离公理', true);
})();

/* ================= §7 Replacement ================= */
(function replacement() {
  const doms = ['{0, 1, 2, 3}', '{1, {1}, 2, {2}}', '{∅, {∅}, {{∅}}, {{{∅}}}}'];
  const fns = [
    { f: '{x}', g: x => HF.mk([x]) },
    { f: 'x ∪ {x}', g: x => HF.succ(x) },
    { f: '⋃x', g: x => HF.union(x) },
    { f: '𝒫(x)', g: x => HF.power(x) },
    { f: '|x|', g: x => HF.nat(x.m.length) },
    { f: '∅', g: () => HF.E },
  ];
  doms.forEach((d, i) => { const o = document.createElement('option'); o.value = i; o.textContent = d; $('rpA').appendChild(o); });
  fns.forEach((f, i) => { const o = document.createElement('option'); o.value = i; o.textContent = f.f; $('rpF').appendChild(o); });
  const svg = $('rp');
  async function run() {
    const A = HF.parse(doms[+$('rpA').value]).set;
    const F = fns[+$('rpF').value];
    svg.innerHTML = '';
    el('defs', {}, svg).innerHTML = '<marker id="rpArr" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto"><path d="M0,0 L10,5 L0,10 z" fill="#ae3ec9"/></marker>';
    svgText(svg, 90, 22, 'A', { 'text-anchor': 'middle', 'font-size': 16, 'font-weight': 800, fill: '#3b5bdb' });
    svgText(svg, 470, 22, `F[A],  F(x) = ${F.f}`, { 'font-size': 15, 'font-weight': 800, fill: '#2f9e44' });
    const imgs = [];
    const ys = A.m.map((_, i) => 60 + i * 55);
    A.m.forEach(x => { const y = F.g(x); if (!imgs.includes(y)) imgs.push(y); });
    const iy = imgs.map((_, i) => 60 + i * (imgs.length > 1 ? (ys[ys.length - 1] - 60) / (imgs.length - 1) : 0) + (imgs.length === 1 ? (ys[ys.length - 1] - 60) / 2 : 0));
    el('rect', { x: 20, y: 34, width: 150, height: ys[ys.length - 1] - 20, rx: 12, fill: '#eef2ff', stroke: '#3b5bdb', 'stroke-width': 2 }, svg);
    el('rect', { x: 460, y: 34, width: 310, height: ys[ys.length - 1] - 20, rx: 12, fill: '#ebfbee', stroke: '#2f9e44', 'stroke-width': 2 }, svg);
    A.m.forEach((x, i) => svgText(svg, 95, ys[i] + 5, HF.show(x, true), { 'text-anchor': 'middle', 'font-size': 14, 'font-weight': 700 }));
    imgs.forEach((y, i) => {
      const t = svgText(svg, 475, iy[i] + 5, HF.show(y, true), { 'font-size': 13, 'font-weight': 700, opacity: 0 });
      t.style.transition = 'opacity .4s';
      imgs[i] = { s: y, t };
    });
    const token = (run.tok = (run.tok || 0) + 1);
    for (let i = 0; i < A.m.length; i++) {
      const j = imgs.findIndex(o => o.s === F.g(A.m[i]));
      const p = el('path', { d: `M170 ${ys[i]} C 300 ${ys[i]}, 330 ${iy[j]}, 462 ${iy[j]}`, fill: 'none', stroke: '#ae3ec9', 'stroke-width': 2.5, 'marker-end': 'url(#rpArr)' }, svg);
      const L = p.getTotalLength();
      p.style.strokeDasharray = L;
      p.style.strokeDashoffset = L;
      p.style.transition = 'stroke-dashoffset .6s ease';
      requestAnimationFrame(() => requestAnimationFrame(() => { p.style.strokeDashoffset = 0; }));
      await sleep(350);
      if (token !== run.tok) return;
      imgs[j].t.setAttribute('opacity', 1);
      await sleep(300);
    }
    const img = HF.mk(imgs.map(o => o.s));
    svgText(svg, 20, 290, `F[A] = ${HF.show(img, true)}`, { 'font-size': 14, 'font-weight': 700, fill: '#2f9e44' });
    okBox($('rpMsg'), bi(`|A| = ${A.m.length}, |F[A]| = ${img.m.length}. ${img.m.length < A.m.length ? 'Several arrows hit the same value, and the image keeps it only once.' : 'F is injective on A here.'} Replacement says this image is a set no matter how large A is.`,
      `|A| = ${A.m.length}，|F[A]| = ${img.m.length}。${img.m.length < A.m.length ? '有几支箭射中了同一个值，像集里只保留一次。' : '这里 F 在 A 上是单射。'}替换公理断言：无论 A 多大，这个像都是集合。`), 'info');
  }
  $('rpGo').addEventListener('click', run);
  $('rpA').addEventListener('change', run);
  $('rpF').addEventListener('change', run);
  run();
})();

/* ================= §8 Infinity ================= */
(function infinity() {
  let k = 0, playing = false;
  const mode = () => document.querySelector('input[name=infMode]:checked').value;
  const MAX = { vn: 5, z: 7 };
  const stage = j => { let s = HF.E; for (let t = 0; t < j; t++) s = mode() === 'vn' ? HF.succ(s) : HF.mk([s]); return s; };
  function render(animLast) {
    const row = $('infRow');
    row.innerHTML = '';
    for (let j = 0; j <= k; j++) {
      const d = document.createElement('div');
      d.style.textAlign = 'center';
      if (animLast && j === k) d.className = 'pop';
      d.innerHTML = `${boxes(stage(j))}<div class="m" style="font-size:13px;margin-top:4px">${j === 0 ? '∅' : 'S' + (j > 1 ? '<sup>' + j + '</sup>' : '') + '(∅)'}${mode() === 'vn' ? ' = ' + j : ''}</div>`;
      row.appendChild(d);
    }
    const dots = document.createElement('div');
    dots.innerHTML = '<span class="m" style="font-size:22px;color:#aaa">⋯ ∈ I</span>';
    row.appendChild(dots);
    // staircase: stage j is a column of its members
    const svg = $('infStairs');
    svg.innerHTML = '';
    const BW = 70, U = 16;
    for (let j = 0; j <= k; j++) {
      const s = stage(j), x = 20 + j * (BW + 16);
      el('line', { x1: x, y1: 100, x2: x + BW, y2: 100, stroke: '#999' }, svg);
      s.m.forEach((m, t) => {
        el('rect', { x: x + 4, y: 100 - (t + 1) * U, width: BW - 8, height: U - 2, rx: 3, fill: '#e7ecff', stroke: '#3b5bdb' }, svg);
        svgText(svg, x + BW / 2, 100 - t * U - 4, HF.show(m, mode() === 'vn'), { 'text-anchor': 'middle', 'font-size': 10 });
      });
      svgText(svg, x + BW / 2, 115, `|·| = ${s.m.length}`, { 'text-anchor': 'middle', 'font-size': 11, fill: '#666' });
    }
    const list = Array.from({ length: k + 1 }, (_, j) => mode() === 'vn' ? j : HF.show(stage(j))).join(', ');
    okBox($('infMsg'), bi(`Any inductive set I must contain: <span class="m">${list}, …</span>` + (mode() === 'vn' ? '. Each stage n has exactly n members, namely all earlier stages: n = {0, 1, …, n−1}.' : '. With x ↦ {x}, each stage has exactly one member, the previous stage.'),
      `任何归纳集 I 都必须包含：<span class="m">${list}, …</span>` + (mode() === 'vn' ? '。第 n 个阶段恰有 n 个元素，就是之前的所有阶段：n = {0, 1, …, n−1}。' : '。用 x ↦ {x} 时，每个阶段只有一个元素，即前一个阶段。')), 'info');
  }
  function step() { if (k < MAX[mode()]) { k++; render(true); } }
  $('infStep').addEventListener('click', step);
  $('infPlay').addEventListener('click', async () => {
    if (playing) return;
    playing = true;
    if (k >= MAX[mode()]) { k = 0; render(); }
    while (k < MAX[mode()]) { await sleep(700); step(); }
    playing = false;
  });
  $('infReset').addEventListener('click', () => { k = 0; render(); });
  document.querySelectorAll('input[name=infMode]').forEach(r => r.addEventListener('change', () => { k = Math.min(k, MAX[mode()]); render(); }));
  k = 3;
  render();
})();

/* ================= ∈-graph drawing (shared by §9 and E5) ================= */
function onCycle(n, edges) {
  // node i is on a cycle iff i reaches itself
  const adj = Array.from({ length: n }, () => []);
  edges.forEach(([u, v]) => adj[u].push(v));
  const reach = (s, t) => { const seen = new Set(), st = [...adj[s]]; while (st.length) { const x = st.pop(); if (x === t) return true; if (!seen.has(x)) { seen.add(x); st.push(...adj[x]); } } return false; };
  const nodes = Array.from({ length: n }, (_, i) => reach(i, i));
  const edgeCyc = edges.map(([u, v]) => u === v || reach(v, u));
  return { nodes, edgeCyc };
}
function drawGraph(svg, pos, names, edges, opts = {}) {
  svg.innerHTML = '';
  const R = opts.r || 20;
  const id = 'ar' + Math.random().toString(36).slice(2, 7);
  el('defs', {}, svg).innerHTML = `<marker id="${id}" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto"><path d="M0,0 L10,5 L0,10 z" fill="#868e96"/></marker>
    <marker id="${id}r" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto"><path d="M0,0 L10,5 L0,10 z" fill="#e03131"/></marker>`;
  const cyc = onCycle(names.length, edges);
  const has = (u, v) => edges.some(([a, b]) => a === u && b === v);
  edges.forEach(([u, v], k) => {
    const red = opts.color !== false && cyc.edgeCyc[k];
    const attrs = { class: 'gedge' + (red ? ' cyc' : ''), 'marker-end': `url(#${id}${red ? 'r' : ''})` };
    const [x1, y1] = pos[u], [x2, y2] = pos[v];
    if (u === v) {
      attrs.d = `M${x1 - 8} ${y1 - R + 2} C ${x1 - 30} ${y1 - R - 40}, ${x1 + 30} ${y1 - R - 40}, ${x1 + 8} ${y1 - R + 2}`;
    } else {
      const dx = x2 - x1, dy = y2 - y1, L = Math.hypot(dx, dy), ux = dx / L, uy = dy / L;
      const off = has(v, u) ? 16 : 0;
      const sx = x1 + ux * R, sy = y1 + uy * R, ex = x2 - ux * (R + 2), ey = y2 - uy * (R + 2);
      const mx = (sx + ex) / 2 - uy * off * 1.6, my = (sy + ey) / 2 + ux * off * 1.6;
      attrs.d = `M${sx} ${sy} Q ${mx} ${my} ${ex} ${ey}`;
    }
    el('path', attrs, svg);
  });
  const incoming = names.map((_, i) => edges.some(([, v]) => v === i));
  return names.map((nm, i) => {
    const cls = ['gnode'];
    if (opts.color !== false && cyc.nodes[i]) cls.push('cyc');
    else if (opts.color !== false && !incoming[i]) cls.push('min');
    if (opts.picked === i) cls.push('pick');
    const g = el('g', { class: cls.join(' '), transform: `translate(${pos[i][0]},${pos[i][1]})` }, svg);
    el('circle', { r: R }, g);
    svgText(g, 0, 0, nm);
    return g;
  });
}

/* ================= §9 Foundation editor + Choice ================= */
(function foundation() {
  const names = ['a', 'b', 'c', 'd', 'e'];
  const pos = names.map((_, i) => [230 + 120 * Math.cos(-Math.PI / 2 + i * 2 * Math.PI / 5), 168 + 120 * Math.sin(-Math.PI / 2 + i * 2 * Math.PI / 5)]);
  let edges = [], picked = -1;
  const presets = [
    { en: 'von Neumann 0,1,2,3', zh: '冯·诺伊曼 0,1,2,3', e: [[0, 1], [0, 2], [1, 2], [0, 3], [1, 3], [2, 3]] },
    { en: 'a ∈ a', zh: 'a ∈ a', e: [[0, 0]] },
    { en: 'a ∈ b ∈ a', zh: 'a ∈ b ∈ a', e: [[0, 1], [1, 0]] },
    { en: '3-cycle + tail', zh: '三元环加一条尾巴', e: [[0, 1], [1, 2], [2, 0], [3, 0], [4, 3]] },
    { en: 'Clear', zh: '清空', e: [] },
  ];
  presets.forEach(p => {
    const b = document.createElement('button');
    b.className = 'btn small';
    b.innerHTML = bil(p.en, p.zh);
    b.addEventListener('click', () => { edges = p.e.map(x => [...x]); picked = -1; draw(); });
    $('fdPresets').appendChild(b);
  });
  function draw() {
    const svg = $('fd');
    const gs = drawGraph(svg, pos, names, edges, { picked, r: 22 });
    gs.forEach((g, i) => g.addEventListener('click', () => {
      if (picked < 0) picked = i;
      else {
        const k = edges.findIndex(([u, v]) => u === picked && v === i);
        if (k >= 0) edges.splice(k, 1); else edges.push([picked, i]);
        picked = -1;
      }
      draw();
    }));
    const cyc = onCycle(5, edges);
    const cnodes = names.filter((_, i) => cyc.nodes[i]);
    const mins = names.filter((_, i) => !edges.some(([, v]) => v === i));
    const hint = picked >= 0 ? bi(`Now click the set that <b>${names[picked]}</b> should belong to.`, `再点击 <b>${names[picked]}</b> 要属于的那个集合。`) + '<br>' : '';
    if (cnodes.length) okBox($('fdMsg'), hint + bi(`✗ <b>Violates Foundation.</b> The set <span class="m">{${cnodes.join(', ')}}</span> has no ∈-minimal member: each of its members has a member inside the set (follow the red arrows backwards).`,
      `✗ <b>违反正则公理.</b> 集合 <span class="m">{${cnodes.join(', ')}}</span> 没有 ∈-极小元：它的每个元素都有一个元素仍在这个集合里（逆着红色箭头走就看到了）。`), 'bad');
    else okBox($('fdMsg'), hint + bi(`✓ <b>Well-founded.</b> No cycles. ∈-minimal nodes (green): <span class="m">${mins.join(', ')}</span>. Any nonempty set S of nodes has one: walk backwards along arrows inside S; with no cycles the walk must stop.`,
      `✓ <b>良基.</b> 没有环。∈-极小结点（绿色）：<span class="m">${mins.join(', ')}</span>。任取非空结点集 S，在 S 内逆着箭头走；没有环，这条路必然走到头，终点就是极小元。`), 'ok');
  }
  edges = presets[0].e.map(x => [...x]);
  draw();

  // Choice preview
  const fam = [
    { n: 'X₁', c: '#3b5bdb', els: ['1', '2'] },
    { n: 'X₂', c: '#2f9e44', els: ['a', 'b', 'c'] },
    { n: 'X₃', c: '#f08c00', els: ['∅'] },
    { n: 'X₄', c: '#ae3ec9', els: ['p', 'q', 'r', 's'] },
  ];
  const chosen = fam.map(() => -1);
  function drawFam() {
    const box = $('fam');
    box.innerHTML = '';
    fam.forEach((X, i) => {
      const d = document.createElement('div');
      d.className = 'fbox';
      d.style.borderColor = X.c;
      d.innerHTML = `<span class="lb" style="color:${X.c}">${X.n}</span>` + X.els.map((e, j) => `<span class="dot${chosen[i] === j ? ' ch' : ''}" style="background:${X.c}" data-j="${j}">${e}</span>`).join('');
      d.querySelectorAll('.dot').forEach(dot => dot.addEventListener('click', () => { chosen[i] = +dot.dataset.j; drawFam(); }));
      box.appendChild(d);
    });
    const f = fam.map((X, i) => `f(${X.n}) = ${chosen[i] < 0 ? '?' : X.els[chosen[i]]}`).join(', ');
    if (chosen.every(c => c >= 0)) okBox($('famMsg'), `<span class="m">${f}</span><br>` + bi('✓ A choice function. Four boxes, four clicks: finitely many choices need no axiom.', '✓ 这是一个选择函数。四个盒子点四下：有限次选择不需要任何公理。'), 'ok');
    else okBox($('famMsg'), `<span class="m">${f}</span>`, 'info');
  }
  drawFam();
  function socks(kind) {
    const svg = $('socks');
    svg.innerHTML = '';
    for (let i = 0; i < 9; i++) {
      const x = 14 + i * 80;
      el('rect', { x, y: 20, width: 68, height: 64, rx: 10, fill: '#fff', stroke: '#ccc', 'stroke-dasharray': '3 3' }, svg);
      for (let s = 0; s < 2; s++) {
        const cx = x + 18 + s * 32;
        const pick = kind === 'shoes' && s === 0;
        const lab = kind === 'shoes' ? (s ? 'R' : 'L') : kind === 'socks' ? '?' : '';
        const g = el('g', { class: 'pop' }, svg);
        g.style.animationDelay = (i * 0.07) + 's';
        el('ellipse', { cx, cy: 52, rx: 12, ry: 22, fill: pick ? '#d3f9d8' : '#f1f3f5', stroke: pick ? '#2f9e44' : '#868e96', 'stroke-width': pick ? 3 : 1.5 }, g);
        svgText(g, cx, 57, lab, { 'text-anchor': 'middle', 'font-size': 13, 'font-weight': 700, fill: kind === 'shoes' ? '#1f2430' : '#e03131' });
      }
    }
    svgText(svg, 740, 58, '⋯', { 'font-size': 22, fill: '#999', 'text-anchor': 'middle' });
    if (kind === 'none') return;
    if (kind === 'shoes') okBox($('famMsg'), bi('<b>Shoes:</b> “take the left one” is a rule, a formula. Replacement then gives the choice function outright, with no AC needed.', '<b>鞋子：</b>“取左脚那只”是一条规则，即一个公式。由替换公理直接得到选择函数，无需选择公理。'), 'ok');
    else okBox($('famMsg'), bi('<b>Socks:</b> the two socks of a pair are indistinguishable, so no formula picks one. Choosing from infinitely many pairs at once is exactly what <b>AC</b> postulates. (If ZF is consistent, so is ZF + “such a choice is impossible”.)', '<b>袜子：</b>一双袜子的两只无法区分，没有公式能挑出其中一只。从无穷多双里同时各挑一只，恰恰是<b>选择公理</b>所断言的。（若 ZF 一致，则 ZF 加上“这种选择做不到”也一致。）'), 'warn');
  }
  $('famShoes').addEventListener('click', () => socks('shoes'));
  $('famSocks').addEventListener('click', () => socks('socks'));
  $('famReset').addEventListener('click', () => { chosen.fill(-1); socks('none'); drawFam(); });
  socks('none');
})();

/* ================= exercises: set-input rows ================= */
(function keys() {
  ['∅', '{', '}', ','].forEach(s => {
    const b = document.createElement('button');
    b.type = 'button';
    b.textContent = s;
    b.addEventListener('click', () => {
      const input = lastSetInput;
      if (!input) return;
      const st = input.selectionStart ?? input.value.length, en = input.selectionEnd ?? input.value.length;
      input.value = input.value.slice(0, st) + s + input.value.slice(en);
      input.focus();
      input.setSelectionRange(st + s.length, st + s.length);
      input.dispatchEvent(new Event('input'));
    });
    $('setKeys').appendChild(b);
  });
})();
// q: question html; ans: HF set (or number when num); returns row controller
function setRow(box, item, onSolve) {
  const row = document.createElement('div');
  row.className = 'tf';
  row.innerHTML = `<div style="flex:1 1 100%">${item.q}</div>
    <input class="formula" style="flex:1 1 260px" placeholder="${item.num ? '?' : '{ … }'}">
    <button class="btn small primary" data-a="c">${bil('Check', '检查')}</button>
    <button class="btn small ghost" data-a="s">${bil('Show answer', '看答案')}</button>
    <div style="flex-basis:100%"><div class="prev"></div><div class="msg"></div></div>`;
  box.appendChild(row);
  const inp = row.querySelector('input'), msg = row.querySelector('.msg'), prev = row.querySelector('.prev');
  let revealed = false; // after "Show answer", Check no longer earns progress for the rest of this page session
  const solve = () => { if (!revealed) onSolve(); };
  inp.addEventListener('focus', () => { lastSetInput = inp; });
  inp.addEventListener('input', () => {
    if (item.num) return;
    try { const r = HF.parse(inp.value); prev.innerHTML = rawBoxes(r); } catch { prev.innerHTML = ''; }
  });
  const check = () => {
    if (item.num) {
      if (+inp.value.trim() === item.ans) { okBox(msg, '✓ ' + bi(item.en, item.zh)); solve(); }
      else okBox(msg, bi(item.wen || 'Not yet. Count again.', item.wzh || '还不对，再数一数。'), 'bad');
      return;
    }
    let r;
    try { r = HF.parse(inp.value); } catch (e) { errBox(msg, e); return; }
    if (r.set === item.ans) { okBox(msg, '✓ ' + bi(`Correct: ${HF.show(item.ans)}. ${item.en || ''}`, `正确：${HF.show(item.ans)}。${item.zh || ''}`)); solve(); }
    else {
      const miss = item.ans.m.filter(x => !HF.has(r.set, x)).length, extra = r.set.m.filter(x => !HF.has(item.ans, x)).length;
      okBox(msg, bi(`Not equal. Your set is missing ${miss} member(s) and has ${extra} extra one(s).`, `不相等。你的集合少了 ${miss} 个元素，多了 ${extra} 个元素。`), 'bad');
    }
  };
  row.querySelector('[data-a=c]').addEventListener('click', check);
  inp.addEventListener('keydown', e => e.key === 'Enter' && check());
  row.querySelector('[data-a=s]').addEventListener('click', () => {
    revealed = true;
    if (item.num) { inp.value = item.ans; okBox(msg, bi(item.en, item.zh), 'info'); return; }
    inp.value = HF.show(item.ans);
    prev.innerHTML = boxes(item.ans);
    okBox(msg, bi(`Answer: ${HF.show(item.ans)}. ${item.en || ''}`, `答案：${HF.show(item.ans)}。${item.zh || ''}`), 'info');
  });
}

/* ================= E1, E2 ================= */
(function e1() {
  const P = s => HF.parse(s).set;
  const items = [
    { A: '{{∅}, {{∅}}}', ans: P('{∅, {∅}}'), en: 'Open {∅} to get ∅, open {{∅}} to get {∅}.', zh: '打开 {∅} 得到 ∅，打开 {{∅}} 得到 {∅}。' },
    { A: '{∅}', ans: HF.E, en: 'The only box inside is empty, so nothing comes out: ⋃{∅} = ∅.', zh: '里面唯一的盒子是空的，倒不出任何东西：⋃{∅} = ∅。' },
    { A: '{{∅, {∅}}, {{{∅}}}}', ans: P('{∅, {∅}, {{∅}}}'), en: '', zh: '' },
    { A: '{∅, {∅}, {∅, {∅}}}', ans: P('{∅, {∅}}'), en: 'This A is the numeral 3, and ⋃3 = 2. In general ⋃(n+1) = n.', zh: '这个 A 就是自然数 3，而 ⋃3 = 2。一般地，⋃(n+1) = n。' },
  ];
  const solved = items.map(() => false);
  items.forEach((it, i) => setRow($('e1List'), {
    q: `<b>(${'abcd'[i]})</b> <span class="m">A = ${it.A}</span> &nbsp; ${boxes(HF.parse(it.A).set)} &nbsp; <span class="m">⋃A = ?</span>`, ans: it.ans, en: it.en, zh: it.zh,
  }, () => { solved[i] = true; if (solved.every(Boolean)) Progress.mark('L6E1'); }));
})();
(function e2() {
  const items = [
    { q: '<b>(a)</b> <span class="m">𝒫({∅, {∅}}) = ?</span>', ans: HF.power(HF.parse('{∅,{∅}}').set),
      en: 'Four subsets: ∅, {∅}, {{∅}}, and the whole set.', zh: '四个子集：∅、{∅}、{{∅}} 和整个集合。' },
    { q: '<b>(b)</b> <span class="m">𝒫(𝒫(∅)) = ?</span>', ans: HF.power(HF.power(HF.E)),
      en: '𝒫(∅) = {∅} (∅ is a subset of everything), and 𝒫({∅}) = {∅, {∅}}.', zh: '𝒫(∅) = {∅}（∅ 是任何集合的子集），而 𝒫({∅}) = {∅, {∅}}。' },
    { q: bi('<b>(c)</b> How many members does <span class="m">𝒫(𝒫(𝒫(𝒫(∅))))</span> have?', '<b>(c)</b> <span class="m">𝒫(𝒫(𝒫(𝒫(∅))))</span> 有多少个元素？'), num: true, ans: 16,
      en: 'Sizes go 0 → 1 → 2 → 4 → 16, since |𝒫(X)| = 2^|X|. One more step gives 65 536. These are the levels V₀ ⊆ V₁ ⊆ ⋯ of the cumulative hierarchy (Lesson 14).',
      zh: '元素个数依次为 0 → 1 → 2 → 4 → 16，因为 |𝒫(X)| = 2^|X|。再来一次就是 65536。这正是累积层级 V₀ ⊆ V₁ ⊆ ⋯ 的前几层（第 14 课）。',
      wen: 'Not yet. Use |𝒫(X)| = 2^|X| four times, starting from |∅| = 0.', wzh: '还不对。从 |∅| = 0 出发，连用四次 |𝒫(X)| = 2^|X|。' },
  ];
  const solved = items.map(() => false);
  items.forEach((it, i) => setRow($('e2List'), it, () => { solved[i] = true; if (solved.every(Boolean)) Progress.mark('L6E2'); }));
})();

/* ================= E3 which axiom ================= */
(function e3() {
  const facts = [
    { en: 'The set {x ∈ A : x ≠ ∅} exists.', zh: '集合 {x ∈ A : x ≠ ∅} 存在。', a: 5 },
    { en: 'If A and B have exactly the same members, then A = B.', zh: '若 A 与 B 的元素完全相同，则 A = B。', a: 0 },
    { en: 'For any set a, the singleton {a} exists.', zh: '对任意集合 a，单元素集 {a} 存在。', a: 2 },
    { en: 'The set of all members of members of A exists.', zh: 'A 的元素的元素全体构成集合。', a: 3 },
    { en: 'There is a set containing ∅, {∅}, {∅, {∅}}, … (all of them).', zh: '存在一个集合，包含 ∅、{∅}、{∅, {∅}}、……（全部）。', a: 7 },
    { en: '{ω, 𝒫(ω), 𝒫(𝒫(ω)), …} is a set.', zh: '{ω, 𝒫(ω), 𝒫(𝒫(ω)), …} 是集合。', a: 6 },
    { en: 'No set is a member of itself.', zh: '没有集合属于它自身。', a: 8 },
    { en: 'The collection of all subsets of A is a set.', zh: 'A 的全体子集构成集合。', a: 4 },
    { en: 'Every family of nonempty sets has a choice function.', zh: '每个非空集合族都有选择函数。', a: 9 },
  ];
  const sels = facts.map((f, i) => {
    const row = document.createElement('div');
    row.className = 'tf';
    row.innerHTML = `<div class="stmt" style="font-family:var(--sans);font-size:15px">${i + 1}. ${bi(f.en, f.zh)}</div><select class="sel"><option value="-1">—</option>${AXIOMS.map((a, j) => `<option value="${j}">${a.en} · ${a.zh}</option>`).join('')}</select><span class="chk"></span>`;
    $('e3List').appendChild(row);
    return row;
  });
  let revealed = false;
  function check(reveal) {
    let ok = 0;
    facts.forEach((f, i) => {
      const s = sels[i].querySelector('select'), c = sels[i].querySelector('.chk');
      if (reveal) s.value = f.a;
      const good = +s.value === f.a;
      if (good) ok++;
      c.textContent = +s.value < 0 ? '' : good ? '✓' : '✗';
      c.style.color = good ? 'var(--true)' : 'var(--false)';
    });
    if (reveal) { revealed = true; okBox($('e3Msg'), bi('Answers filled in. Note #6: Zermelo set theory Z, which lacks Replacement, cannot prove it.', '答案已填好。注意第 6 条：没有替换公理的策梅洛集合论 Z 证明不了它。'), 'info'); return; }
    if (ok === facts.length) { okBox($('e3Msg'), bi('✓ All correct. Note #6: Zermelo set theory Z, which lacks Replacement, cannot prove it.', '✓ 全对。注意第 6 条：没有替换公理的策梅洛集合论 Z 证明不了它。')); if (!revealed) Progress.mark('L6E3'); }
    else okBox($('e3Msg'), bi(`${ok} / ${facts.length} correct.`, `答对 ${ok} / ${facts.length}。`), 'warn');
  }
  $('e3Check').addEventListener('click', () => check(false));
  $('e3Show').addEventListener('click', () => check(true));
})();

/* ================= E4 no universal set ================= */
(function e4() {
  stepper($('e4Steps'), $('e4Next'), $('e4All'));
  const c = choice($('e4Choice'), [
    { ok: false, en: 'Because Separation does not allow the formula x ∉ x.', zh: '因为分离公理不允许使用公式 x ∉ x。',
      fen: '✗ It does allow it: x ∉ x is a perfectly good formula of the language {∈}. Look at what we actually conclude.', fzh: '✗ 允许的：x ∉ x 是语言 {∈} 中完全合法的公式。看看我们实际推出了什么。' },
    { ok: true, en: 'Because without “R<sub>A</sub> ∈ A” there is no contradiction: we only learn that R<sub>A</sub> lies outside A.', zh: '因为少了“R<sub>A</sub> ∈ A”就没有矛盾：我们只是得知 R<sub>A</sub> 落在 A 之外。',
      fen: '✓ Right. Step 3 needed R ∈ V, which only a universal V provides. For an arbitrary A the argument proves the harmless theorem R<sub>A</sub> ∉ A.', fzh: '✓ 对。第 3 步要用到 R ∈ V，而这只有“全集” V 才能保证。对任意的 A，这个论证只证出一条无害的定理：R<sub>A</sub> ∉ A。' },
    { ok: false, en: 'Because Foundation makes R<sub>A</sub> empty.', zh: '因为正则公理使 R<sub>A</sub> 为空。',
      fen: '✗ Quite the opposite: with Foundation no x has x ∈ x, so R<sub>A</sub> = A. And the proof never used Foundation anyway.', fzh: '✗ 恰恰相反：有了正则公理，没有 x 满足 x ∈ x，所以 R<sub>A</sub> = A。况且这个证明根本没用到正则公理。' },
  ], $('e4Msg'), () => Progress.mark('L6E4'));
  $('e4Show').addEventListener('click', () => { c.reveal(); $('e4All').click(); });
})();

/* ================= E5 foundation check ================= */
(function e5() {
  const graphs = [
    { n: ['a', 'b', 'c'], p: [[40, 110], [150, 110], [95, 30]], e: [[0, 1], [0, 2], [1, 2]], ok: true },
    { n: ['a', 'b'], p: [[60, 90], [140, 90]], e: [[0, 0], [0, 1]], ok: false },
    { n: ['a', 'b', 'c'], p: [[40, 110], [150, 110], [95, 30]], e: [[0, 1], [1, 2], [2, 0]], ok: false },
    { n: ['a', 'b', 'c', 'd'], p: [[35, 35], [155, 35], [155, 120], [35, 120]], e: [[0, 1], [2, 1], [0, 2], [3, 2], [3, 0]], ok: true },
    { n: ['a', 'b', 'c', 'd'], p: [[35, 35], [155, 35], [155, 120], [35, 120]], e: [[0, 1], [1, 2], [2, 3], [3, 1]], ok: false },
  ];
  const solved = graphs.map(() => false);
  let revealed = false;
  const cards = graphs.map((g, i) => {
    const d = document.createElement('div');
    d.className = 'g';
    d.innerHTML = `<b>G${sub(i + 1)}</b>`;
    const svg = el('svg', { viewBox: '0 0 190 150', width: 190, height: 150, style: 'margin:0 auto' }, d);
    drawGraph(svg, g.p, g.n, g.e, { color: false, r: 15 });
    g.svg = svg;
    const bar = document.createElement('div');
    bar.innerHTML = `<button class="btn small" data-v="1">${bil('obeys', '满足')}</button> <button class="btn small" data-v="0">${bil('violates', '违反')}</button>`;
    d.appendChild(bar);
    bar.querySelectorAll('button').forEach(b => b.addEventListener('click', () => {
      const good = (b.dataset.v === '1') === g.ok;
      d.classList.remove('right', 'wrong');
      void d.offsetWidth;
      d.classList.add(good ? 'right' : 'wrong');
      if (good) {
        drawGraph(svg, g.p, g.n, g.e, { r: 15 });
        if (!revealed) solved[i] = true;
        if (solved.every(Boolean)) { okBox($('e5Msg'), bi('✓ All five right. G₄ looks busy but has no cycle: d is ∈-minimal.', '✓ 五个全对。G₄ 看着热闹，其实没有环：d 是 ∈-极小元。')); Progress.mark('L6E5'); }
      } else okBox($('e5Msg'), bi('✗ Look for a closed loop of arrows (including a loop on one node).', '✗ 找一找有没有首尾相接的箭头环（包括单个结点上的自环）。'), 'bad');
    }));
    $('e5Graphs').appendChild(d);
    return d;
  });
  $('e5Show').addEventListener('click', () => {
    revealed = true;
    graphs.forEach((g, i) => { drawGraph(g.svg, g.p, g.n, g.e, { r: 15 }); cards[i].classList.remove('right', 'wrong'); cards[i].classList.add(g.ok ? 'right' : 'wrong'); });
    okBox($('e5Msg'), bi('Green cards obey Foundation, red ones violate it: G₂ has a ∈ a, G₃ a 3-cycle, G₅ the cycle b → c → d → b. G₄ has no cycle.', '绿色的满足正则公理，红色的违反：G₂ 有 a ∈ a，G₃ 有三元环，G₅ 有环 b → c → d → b。G₄ 没有环。'), 'info');
  });
})();

/* ================= E6 x ∉ x ================= */
(function e6() {
  const solved = { a: false, b: false };
  const fin = () => { if (solved.a && solved.b) { document.querySelector('#e6Proof .step').classList.add('on'); Progress.mark('L6E6'); } };
  const ca = choice($('e6a'), [
    { ok: false, en: 'x itself', zh: 'x 本身', fen: '✗ Foundation gives some y ∈ x with y ∩ x = ∅, but that y need not be x, so no contradiction.', fzh: '✗ 正则公理给出某个 y ∈ x 且 y ∩ x = ∅，但这个 y 未必是 x，推不出矛盾。' },
    { ok: true, en: '{x}', zh: '{x}', fen: '✓ Its only member is x, so x must be disjoint from {x}, i.e. x ∉ x.', fzh: '✓ 它唯一的元素是 x，所以 x 与 {x} 不交，即 x ∉ x。' },
    { ok: false, en: '𝒫(x)', zh: '𝒫(x)', fen: '✗ ∅ ∈ 𝒫(x) is always a disjoint member, so this tells you nothing.', fzh: '✗ ∅ ∈ 𝒫(x) 总是一个不交的元素，什么也推不出来。' },
    { ok: false, en: '⋃x', zh: '⋃x', fen: '✗ ⋃x might even be empty. Choose a set whose only member is x.', fzh: '✗ ⋃x 甚至可能是空集。挑一个唯一元素就是 x 的集合。' },
  ], $('e6aMsg'), () => { solved.a = true; fin(); });
  const cb = choice($('e6b'), [
    { ok: false, en: '{x}', zh: '{x}', fen: '✗ x ∩ {x} = ∅ is perfectly possible when x ∈ y ∈ x (and y ≠ x). Include both.', fzh: '✗ 当 x ∈ y ∈ x（且 y ≠ x）时，x ∩ {x} = ∅ 完全可能。把两者都放进去。' },
    { ok: false, en: 'x ∩ y', zh: 'x ∩ y', fen: '✗ That might be empty. You need a set containing both x and y.', fzh: '✗ 它可能是空集。需要一个同时含有 x 和 y 的集合。' },
    { ok: true, en: '{x, y}', zh: '{x, y}', fen: '✓ x is not disjoint from it (y ∈ x), and y is not (x ∈ y). No ∈-minimal member exists.', fzh: '✓ x 与它不交吗？不，y ∈ x；y 呢？也不，x ∈ y。于是没有 ∈-极小元。' },
    { ok: false, en: 'x ∪ y', zh: 'x ∪ y', fen: '✗ Its members are the members of x and y, not x and y themselves.', fzh: '✗ 它的元素是 x 和 y 的元素，而不是 x、y 本身。' },
  ], $('e6bMsg'), () => { solved.b = true; fin(); });
  $('e6Show').addEventListener('click', () => { ca.reveal(); cb.reveal(); document.querySelector('#e6Proof .step').classList.add('on'); });
})();
