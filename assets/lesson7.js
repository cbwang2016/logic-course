// Lesson 7 interactions: building N, Z, Q, R from sets.
// The helpers below (HF sets, box drawings, stepper, choice) are shared verbatim with lesson6.js.
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
  const btns = opts.map(o => {
    const b = document.createElement('button');
    b.className = 'btn choice';
    b.innerHTML = o.en === o.zh ? `<span class="m">${o.en}</span>` : bi(o.en, o.zh);
    b.addEventListener('click', () => {
      btns.forEach(x => x.classList.remove('right', 'wrongc'));
      b.classList.add(o.ok ? 'right' : 'wrongc');
      okBox(msg, bi(o.fen, o.fzh), o.ok ? 'ok' : 'bad');
      if (o.ok && onRight) onRight();
    });
    box.appendChild(b);
    return b;
  });
  return { reveal() { const i = opts.findIndex(o => o.ok); btns[i].classList.add('right'); okBox(msg, bi(opts[i].fen, opts[i].fzh), 'info'); } };
}
let lastSetInput = null;

const kp = (a, b) => HF.mk([HF.mk([a]), HF.mk([a, b])]);
const gcd = (a, b) => { a = Math.abs(a); b = Math.abs(b); while (b) [a, b] = [b, a % b]; return a; };

/* ================= hero ladder ================= */
(function ladder() {
  const svg = $('ladder');
  const nodes = [['∅', '#s1'], ['ω', '#s2'], ['ℤ', '#s5'], ['ℚ', '#s6'], ['ℝ', '#s7']];
  const links = [['Infinity + Separation', '无穷 + 分离'], ['(ω×ω)/~', '数对/等价'], ['(ℤ×ℤ*)/~', '分数/等价'], ['cuts ⊆ 𝒫(ℚ)', '戴德金分割']];
  nodes.forEach(([t, href], i) => {
    const x = 50 + i * 200;
    if (i < 4) {
      el('line', { x1: x + 28, y1: 40, x2: x + 172, y2: 40, stroke: '#aaa', 'stroke-width': 2, 'stroke-dasharray': '5 4' }, svg);
      svgText(svg, x + 100, 30, links[i][0], { 'text-anchor': 'middle', 'font-size': 10.5, fill: '#666' });
      svgText(svg, x + 100, 60, links[i][1], { 'text-anchor': 'middle', 'font-size': 12, fill: '#888' });
    }
    const a = el('a', { href }, svg);
    const g = el('g', { class: 'pop' }, a);
    g.style.animationDelay = (i * 0.15) + 's';
    el('circle', { cx: x, cy: 40, r: 26, fill: '#fff', stroke: '#2f9e44', 'stroke-width': 3 }, g);
    svgText(g, x, 48, t, { 'text-anchor': 'middle', 'font-size': 22, 'font-weight': 700, fill: '#2f9e44' });
  });
})();

/* ================= §1 Kuratowski ================= */
(function kuratowski() {
  const opts = ['0', '1', '2', '3', '{1}', '{0, 2}'];
  const sets = opts.map(o => HF.parse(o).set);
  ['kpA', 'kpB', 'kpC', 'kpD'].forEach((id, k) => {
    opts.forEach((o, i) => { const op = document.createElement('option'); op.value = i; op.textContent = o; $(id).appendChild(op); });
    $(id).value = [0, 1, 1, 0][k];
    $(id).addEventListener('change', render);
  });
  $('kpNums').addEventListener('change', render);
  function pane(box, a, b, la, lb) {
    const nums = $('kpNums').checked;
    const p = kp(a, b);
    const degenerate = a === b;
    box.innerHTML = `<div class="m" style="font-size:15px">(${la}, ${lb}) = {{${la}}, {${la}, ${lb}}}${degenerate ? ` = {{${la}}}` : ''}</div>
      <div style="margin:6px 0" class="pop">${boxes(p, { nums })}</div>
      <div class="bigtext">= ${HF.show(p, nums)}</div>` +
      (degenerate ? `<div class="msg warn" style="margin:6px 0 0">${bi('Degenerate case a = b: {a, a} = {a}, so the pair has only <b>one</b> member.', '退化情形 a = b：{a, a} = {a}，所以这个有序对只有<b>一个</b>元素。')}</div>` : '');
    return p;
  }
  function render() {
    const [a, b, c, d] = ['kpA', 'kpB', 'kpC', 'kpD'].map(id => sets[+$(id).value]);
    const [la, lb, lc, ld] = ['kpA', 'kpB', 'kpC', 'kpD'].map(id => opts[+$(id).value]);
    const p = pane($('kpBox1'), a, b, la, lb), q = pane($('kpBox2'), c, d, lc, ld);
    const yn = v => v ? `<span class="yes">${bil('yes', '是')}</span>` : `<span class="no">${bil('no', '否')}</span>`;
    const naive1 = HF.mk([a, b]), naive2 = HF.mk([c, d]);
    let h = `<table class="tt verdict"><tr><th>a = c ?</th><th>b = d ?</th><th>(a,b) = (c,d) ?</th><th>${bil('naive', '天真写法')} {a,b} = {c,d} ?</th></tr>
      <tr><td>${yn(a === c)}</td><td>${yn(b === d)}</td><td>${yn(p === q)}</td><td>${yn(naive1 === naive2)}</td></tr></table>`;
    if (naive1 === naive2 && p !== q) h += `<div class="msg warn">${bi('The naive pair {a, b} cannot tell these apart: it forgets the order. Kuratowski\'s pair can.', '天真的 {a, b} 分不清这两者：它丢掉了次序。库拉托夫斯基有序对分得清。')}</div>`;
    else if (p === q) h += `<div class="msg ok">${bi('Same set, and indeed a = c and b = d. The characteristic property never fails.', '是同一个集合，而且确实 a = c、b = d。基本性质从不失效。')}</div>`;
    else h += `<div class="msg info">${bi('Different pairs, different sets.', '不同的有序对，不同的集合。')}</div>`;
    if (p === HF.parse('{1,2}').set) h += `<div class="msg info">${bi('Fun fact: (0, 1) = {{0}, {0, 1}} = {1, 2}. From the outside a pair is just a set like any other. Only the characteristic property matters.', '趣闻：(0, 1) = {{0}, {0, 1}} = {1, 2}。从外面看，有序对不过是个普通集合，要紧的只是那条基本性质。')}</div>`;
    $('kpVerdict').innerHTML = h;
    // decode p
    const nums = $('kpNums').checked;
    const S = x => HF.show(x, nums);
    const inter = p.m.reduce((acc, x) => HF.cap(acc, x));
    const uni = HF.union(p);
    const first = inter.m[0];
    const rest = uni.m.filter(x => !HF.has(inter, x));
    $('kpDecode').innerHTML = `<div>p = ${S(p)}</div><div>⋂p = ${S(inter)} &nbsp;⇒&nbsp; ${bil('first', '第一分量')} = <b>${S(first)}</b></div><div>⋃p = ${S(uni)}</div>` +
      (rest.length ? `<div>⋃p ∖ ⋂p = {${rest.map(S).join(', ')}} &nbsp;⇒&nbsp; ${bil('second', '第二分量')} = <b>${S(rest[0])}</b></div>`
        : `<div>⋃p = ⋂p &nbsp;⇒&nbsp; ${bil('second = first', '第二分量 = 第一分量')} = <b>${S(first)}</b></div>`);
  }
  render();
  stepper($('kpProof'), $('kpNext'), $('kpAll'));
})();

/* ================= §2 von Neumann ================= */
(function vonNeumann() {
  function render() {
    const n = +$('vnN').value, abbr = $('vnAbbr').checked;
    $('vnNv').textContent = n;
    const s = HF.nat(n);
    $('vnBoxes').innerHTML = `<div class="pop" style="display:inline-block">${boxes(s, { nums: abbr })}</div>`;
    const full = HF.show(s);
    $('vnText').innerHTML = `${n} = ${n ? '{' + Array.from({ length: n }, (_, k) => k).join(', ') + '}' : '∅'}<br><span class="muted" style="font-size:13px">= ${full}</span>`;
    $('vnStats').innerHTML = `<span class="stat">|${n}| = ${n}</span><span class="stat">${bil('brace pairs', '花括号对数')} (∅ = {}) = ${s.size}</span><span class="stat">${bil('rank', '秩')} = ${s.rank}</span>`;
    const svg = $('vnStairs');
    svg.innerHTML = '';
    const W = 48, U = 26, base = 190;
    for (let k = 0; k <= n; k++) {
      const x = 14 + k * W;
      const inN = k < n;
      const g = el('g', { class: 'pop' }, svg);
      g.style.animationDelay = (k * 0.08) + 's';
      el('rect', { x, y: base - (k + 1) * U, width: W - 4, height: (k + 1) * U, rx: 4, fill: inN ? '#e7ecff' : '#f8e7fc', stroke: inN ? '#3b5bdb' : '#ae3ec9', 'stroke-width': inN ? 1.5 : 3 }, g);
      svgText(g, x + (W - 4) / 2, base - (k + 1) * U + 18, k, { 'text-anchor': 'middle', 'font-size': 15, 'font-weight': 700, fill: inN ? '#3b5bdb' : '#ae3ec9' });
    }
    if (n > 0) {
      el('path', { d: `M14 ${base + 6} L14 ${base + 12} L${14 + n * W - 4} ${base + 12} L${14 + n * W - 4} ${base + 6}`, fill: 'none', stroke: '#ae3ec9', 'stroke-width': 2 }, svg);
    }
    svgText(svg, 14, 16, `${n} = { ${n ? Array.from({ length: n }, (_, k) => k).join(', ') : ''} }`, { 'font-size': 14, 'font-weight': 700, fill: '#ae3ec9' });
  }
  $('vnN').addEventListener('input', render);
  $('vnAbbr').addEventListener('change', render);
  render();

  const svg = $('vnMx');
  const N = 8, CS = 38, X0 = 52, Y0 = 44;
  let sel = [2, 5];
  function mx() {
    svg.innerHTML = '';
    svgText(svg, X0 + N * CS / 2, 14, 'n', { 'text-anchor': 'middle', 'font-size': 13, fill: '#888' });
    svgText(svg, 10, Y0 + N * CS / 2, 'm', { 'font-size': 13, fill: '#888' });
    for (let j = 0; j < N; j++) svgText(svg, X0 + j * CS + CS / 2, Y0 - 8, j, { 'text-anchor': 'middle', 'font-size': 14, 'font-weight': 700, fill: '#3b5bdb' });
    for (let i = 0; i < N; i++) {
      svgText(svg, X0 - 10, Y0 + i * CS + CS / 2 + 5, i, { 'text-anchor': 'end', 'font-size': 14, 'font-weight': 700 });
      for (let j = 0; j < N; j++) {
        const on = i < j, me = sel[0] === i && sel[1] === j;
        const r = el('rect', { x: X0 + j * CS + 2, y: Y0 + i * CS + 2, width: CS - 4, height: CS - 4, rx: 5, fill: on ? '#3b5bdb' : i === j ? '#fff' : '#f1efe7',
          stroke: me ? '#f08c00' : i === j ? '#d0ccc0' : 'none', 'stroke-width': me ? 4 : 1, style: 'cursor:pointer' }, svg);
        if (on) svgText(svg, X0 + j * CS + CS / 2, Y0 + i * CS + CS / 2 + 5, '∈', { 'text-anchor': 'middle', 'font-size': 14, fill: '#fff', 'pointer-events': 'none' });
        r.addEventListener('click', () => { sel = [i, j]; mx(); });
      }
    }
    const [m, n] = sel;
    okBox($('vnMxMsg'), bi(`<span class="m">${m} ${m < n ? '∈' : '∉'} ${n}</span> because ${n} = {${Array.from({ length: n }, (_, k) => k).join(', ')}}${m < n ? ' lists ' + m : ' does not list ' + m}. So <span class="m">${m} ${m < n ? '&lt;' : '≮'} ${n}</span>. Also <span class="m">${m} ${m <= n ? '⊆' : '⊈'} ${n}</span>.`,
      `<span class="m">${m} ${m < n ? '∈' : '∉'} ${n}</span>，因为 ${n} = {${Array.from({ length: n }, (_, k) => k).join(', ')}}${m < n ? ' 中有 ' + m : ' 中没有 ' + m}。所以 <span class="m">${m} ${m < n ? '&lt;' : '≮'} ${n}</span>。同时 <span class="m">${m} ${m <= n ? '⊆' : '⊈'} ${n}</span>。`), m < n ? 'ok' : 'info');
  }
  mx();
})();

/* ================= §3 ω as intersection, induction ================= */
(function omega() {
  const svg = $('omSvg');
  function draw(intersected) {
    svg.innerHTML = '';
    const r1 = el('rect', { x: 14, y: 14, width: 792, height: 150, rx: 40, fill: 'rgba(59,91,219,.10)', stroke: '#3b5bdb', 'stroke-width': 2 }, svg);
    const r2 = el('rect', { x: 14, y: 86, width: 792, height: 150, rx: 40, fill: 'rgba(47,158,68,.10)', stroke: '#2f9e44', 'stroke-width': 2 }, svg);
    const t1 = svgText(svg, 30, 36, 'I₁ inductive · 归纳集', { 'font-size': 13, 'font-weight': 700, fill: '#3b5bdb' });
    const t2 = svgText(svg, 30, 228, 'I₂ inductive · 归纳集', { 'font-size': 13, 'font-weight': 700, fill: '#2f9e44' });
    const junk = [];
    const chain = (labels, y, x0, color) => labels.forEach((lab, k) => {
      const x = x0 + k * 82;
      if (k < labels.length - 1) junk.push(el('line', { x1: x + 22, y1: y, x2: x + 60, y2: y, stroke: color, 'stroke-width': 1.5, 'marker-end': '' }, svg));
      const c = el('circle', { cx: x, cy: y, r: 20, fill: '#fff', stroke: color, 'stroke-width': 2 }, svg);
      const t = svgText(svg, x, y + 5, lab, { 'text-anchor': 'middle', 'font-size': 12, 'font-weight': 700, fill: color });
      junk.push(c, t);
    });
    chain(['ω', 'S(ω)', 'S²(ω)', '⋯'], 52, 520, '#3b5bdb');
    chain(['a', 'S(a)', 'S²(a)', '⋯'], 198, 520, '#2f9e44');
    for (let k = 0; k <= 6; k++) {
      const x = 60 + k * 62;
      if (k < 6) el('line', { x1: x + 18, y1: 125, x2: x + 44, y2: 125, stroke: '#888', 'stroke-width': 1.5 }, svg);
      el('circle', { cx: x, cy: 125, r: 18, fill: intersected ? '#fff3bf' : '#fff', stroke: intersected ? '#f08c00' : '#1f2430', 'stroke-width': 2 }, svg);
      svgText(svg, x, 130, k === 6 ? '⋯' : k, { 'text-anchor': 'middle', 'font-size': 14, 'font-weight': 700 });
    }
    if (intersected) {
      junk.forEach(j => { j.style.transition = 'opacity .8s'; requestAnimationFrame(() => requestAnimationFrame(() => { j.style.opacity = 0.12; })); });
      [r1, r2, t1, t2].forEach(j => { j.style.transition = 'opacity .8s'; j.style.opacity = 0.35; });
      el('rect', { x: 30, y: 94, width: 440, height: 62, rx: 30, fill: 'none', stroke: '#f08c00', 'stroke-width': 3, class: 'fadein' }, svg);
      svgText(svg, 480, 130, 'ω = ⋂{ I : I inductive } · 一切归纳集之交', { 'font-size': 13, 'font-weight': 800, fill: '#f08c00', class: 'fadein' });
    }
  }
  $('omInt').addEventListener('click', () => draw(true));
  $('omReset').addEventListener('click', () => draw(false));
  draw(false);

  // induction toggles
  const N = 16;
  let S = new Set(Array.from({ length: N }, (_, k) => k).filter(k => k !== 7));
  const isvg = $('indSvg');
  const cx = k => 26 + k * 48;
  function render() {
    isvg.innerHTML = '';
    el('defs', {}, isvg).innerHTML = '<marker id="indA" viewBox="0 0 10 10" refX="8" refY="5" markerWidth="6" markerHeight="6" orient="auto"><path d="M0,0 L10,5 L0,10 z" fill="context-stroke"/></marker>';
    for (let k = 0; k < N - 1; k++) {
      const a = S.has(k), b = S.has(k + 1);
      const col = a && b ? '#2f9e44' : a && !b ? '#e03131' : '#ccc';
      el('path', { d: `M${cx(k) + 6} 40 Q ${cx(k) + 24} 14 ${cx(k + 1) - 6} 40`, fill: 'none', stroke: col, 'stroke-width': a && !b ? 3 : 2, 'marker-end': 'url(#indA)' }, isvg);
      if (a && !b) svgText(isvg, cx(k) + 24, 12, '✗', { 'text-anchor': 'middle', 'font-size': 14, fill: '#e03131', 'font-weight': 800 });
    }
    for (let k = 0; k < N; k++) {
      const on = S.has(k);
      const g = el('g', { style: 'cursor:pointer' }, isvg);
      el('circle', { cx: cx(k), cy: 62, r: 17, fill: on ? '#3b5bdb' : '#fff', stroke: on ? '#3b5bdb' : (k === 0 ? '#e03131' : '#bbb'), 'stroke-width': 2 }, g);
      svgText(g, cx(k), 67, k, { 'text-anchor': 'middle', 'font-size': 14, 'font-weight': 700, fill: on ? '#fff' : '#555' });
      g.addEventListener('click', () => { if (S.has(k)) S.delete(k); else S.add(k); render(); });
    }
    svgText(isvg, cx(N - 1) + 26, 67, '⋯', { 'font-size': 18, fill: '#999' });
    svgText(isvg, 6, 96, 'S = blue · 蓝色为 S', { 'font-size': 11, fill: '#888' });
    let miss = -1;
    for (let k = 0; k < N; k++) if (!S.has(k)) { miss = k; break; }
    if (miss < 0) okBox($('indMsg'), bi('0 ∈ S and every arrow is green: S is inductive, so S = ω (imagine all later numbers in S too).', '0 ∈ S 且每支箭都是绿的：S 是归纳集，所以 S = ω（假想后面的数也都在 S 里）。'), 'ok');
    else if (miss === 0) okBox($('indMsg'), bi('<b>0 ∉ S</b>: the base case fails, so S is not inductive. Induction says nothing about S.', '<b>0 ∉ S</b>：奠基不成立，S 不是归纳集，归纳原理对它无话可说。'), 'bad');
    else okBox($('indMsg'), bi(`The least number missing from S is <b>${miss}</b>. Then ${miss - 1} ∈ S but ${miss} ∉ S: the step <span class="m">n ∈ S ⇒ n+1 ∈ S</span> fails at n = ${miss - 1} (red arrow). A gap always produces such a break: this is the <b>least number principle</b>, equivalent to induction.`,
      `S 中缺的最小的数是 <b>${miss}</b>。于是 ${miss - 1} ∈ S 而 ${miss} ∉ S：归纳步 <span class="m">n ∈ S ⇒ n+1 ∈ S</span> 在 n = ${miss - 1} 处断了（红箭头）。有缺口就必然有这样的断点：这就是<b>最小数原理</b>，它与归纳法等价。`), 'warn');
  }
  $('indAll').addEventListener('click', () => { S = new Set(Array.from({ length: N }, (_, k) => k)); render(); });
  $('indEven').addEventListener('click', () => { S = new Set(Array.from({ length: N }, (_, k) => k).filter(k => k % 2 === 0)); render(); });
  $('indGap').addEventListener('click', () => { S = new Set(Array.from({ length: N }, (_, k) => k).filter(k => k !== 7)); render(); });
  $('indNo0').addEventListener('click', () => { S = new Set(Array.from({ length: N - 1 }, (_, k) => k + 1)); render(); });
  render();
})();

/* ================= §4 recursion ================= */
(function recursion() {
  let tok = 0;
  const sync = () => { $('rcMv').textContent = $('rcM').value; $('rcNv').textContent = $('rcN').value; };
  async function run() {
    sync();
    const my = ++tok;
    const m = +$('rcM').value, n = +$('rcN').value, op = $('rcOp').value;
    const svg = $('rcSvg'), tr = $('rcTrace');
    svg.innerHTML = '';
    tr.innerHTML = '';
    const B = 26;
    const line = html => { const d = document.createElement('div'); d.innerHTML = html; tr.appendChild(d); };
    const block = (x, y, fill, stroke) => { const r = el('rect', { x, y, width: B - 3, height: B - 3, rx: 4, fill, stroke, class: 'pop' }, svg); return r; };
    if (op === '+') {
      svgText(svg, 10, 20, `h(k) = ${m} + k`, { 'font-size': 14, 'font-weight': 700, fill: '#3b5bdb' });
      for (let i = 0; i < m; i++) block(10 + i * B, 120, '#e7ecff', '#3b5bdb');
      line(`${m} + 0 = <b>${m}</b> <span class="muted">${bil('(base: h(0) = a = m)', '（奠基：h(0) = a = m）')}</span>`);
      for (let k = 0; k < n; k++) {
        await sleep(750);
        if (my !== tok) return;
        block(10 + (m + k) * B, 120, '#d3f9d8', '#2f9e44');
        line(`${m} + ${k + 1} = S(${m} + ${k}) = S(${m + k}) = <b>${m + k + 1}</b>`);
      }
      svgText(svg, 10, 180, `${m} + ${n} = ${m + n}`, { 'font-size': 18, 'font-weight': 800, fill: '#2f9e44', class: 'fadein' });
    } else {
      svgText(svg, 10, 20, `h(k) = ${m} · k`, { 'font-size': 14, 'font-weight': 700, fill: '#3b5bdb' });
      line(`${m} · 0 = <b>0</b> <span class="muted">${bil('(base: h(0) = 0)', '（奠基：h(0) = 0）')}</span>`);
      for (let k = 0; k < n; k++) {
        await sleep(750);
        if (my !== tok) return;
        for (let i = 0; i < m; i++) block(10 + i * B, 36 + k * B, k % 2 ? '#d3f9d8' : '#e7ecff', k % 2 ? '#2f9e44' : '#3b5bdb');
        line(`${m} · ${k + 1} = ${m} · ${k} + ${m} = ${m * k} + ${m} = <b>${m * (k + 1)}</b>`);
      }
      svgText(svg, 200, 260, `${m} · ${n} = ${m * n}`, { 'font-size': 18, 'font-weight': 800, fill: '#2f9e44', class: 'fadein' });
    }
  }
  ['rcM', 'rcN'].forEach(id => $(id).addEventListener('input', sync));
  $('rcOp').addEventListener('change', run);
  $('rcGo').addEventListener('click', run);
  run();
  stepper($('rcProof'), $('rcPNext'), $('rcPAll'));
})();

/* ================= §5 ℤ grid ================= */
(function integers() {
  const svg = $('zSvg');
  const M = 12, SP = 34, X0 = 40, Y0 = 440;
  const X = a => X0 + a * SP, Y = b => Y0 - b * SP;
  let mode = 'class', sel = [5, 2], P = null, Q = null;
  const fmt = k => (k > 0 ? '+' : '') + k;
  function classLine(k, color, w) {
    const a0 = Math.max(0, k), a1 = Math.min(M, M + k);
    if (a0 > a1) return;
    el('line', { x1: X(a0), y1: Y(a0 - k), x2: X(a1), y2: Y(a1 - k), stroke: color, 'stroke-width': w, 'stroke-linecap': 'round' }, svg);
  }
  function draw() {
    svg.innerHTML = '';
    for (let k = -M; k <= M; k++) {
      classLine(k, k === 0 ? '#c9c4b5' : '#ebe7dc', k === 0 ? 3 : 1.5);
      const a1 = Math.min(M, M + k);
      if (k >= -M + 1 && k <= M - 1 && Math.abs(k) % 2 === 0) svgText(svg, X(a1) + (k <= 0 ? 0 : 10), Y(a1 - k) - (k <= 0 ? 10 : -4), fmt(k), { 'text-anchor': 'middle', 'font-size': 10, fill: '#aaa' });
    }
    svgText(svg, X(M) + 6, Y0 + 26, 'a', { 'font-size': 14, 'font-weight': 700, fill: '#666' });
    svgText(svg, X0 - 26, Y(M) - 6, 'b', { 'font-size': 14, 'font-weight': 700, fill: '#666' });
    for (let i = 0; i <= M; i += 2) { svgText(svg, X(i), Y0 + 18, i, { 'text-anchor': 'middle', 'font-size': 10, fill: '#999' }); svgText(svg, X0 - 14, Y(i) + 4, i, { 'text-anchor': 'middle', 'font-size': 10, fill: '#999' }); }
    const hl = new Map();
    if (mode === 'class' && sel) {
      const k = sel[0] - sel[1];
      classLine(k, '#f08c00', 6);
      for (let a = 0; a <= M; a++) if (a - k >= 0 && a - k <= M) hl.set(a + ',' + (a - k), '#f08c00');
      hl.set(sel.join(','), '#1f2430');
    }
    if (mode === 'add') {
      if (P) { classLine(P[0] - P[1], 'rgba(59,91,219,.35)', 5); hl.set(P.join(','), '#3b5bdb'); }
      if (Q) { classLine(Q[0] - Q[1], 'rgba(47,158,68,.35)', 5); hl.set(Q.join(','), '#2f9e44'); }
      if (P && Q) {
        const s = [P[0] + Q[0], P[1] + Q[1]];
        classLine(s[0] - s[1], 'rgba(174,62,201,.45)', 6);
        if (s[0] <= M && s[1] <= M) {
          hl.set(s.join(','), '#ae3ec9');
          el('line', { x1: X(0), y1: Y(0), x2: X(P[0]), y2: Y(P[1]), stroke: '#3b5bdb', 'stroke-width': 2, 'stroke-dasharray': '4 3' }, svg);
          el('line', { x1: X(P[0]), y1: Y(P[1]), x2: X(s[0]), y2: Y(s[1]), stroke: '#2f9e44', 'stroke-width': 2, 'stroke-dasharray': '4 3' }, svg);
        }
      }
    }
    for (let a = 0; a <= M; a++) for (let b = 0; b <= M; b++) {
      const c = hl.get(a + ',' + b);
      const pt = el('circle', { cx: X(a), cy: Y(b), r: c ? 7 : 4, fill: c || '#9aa0aa', class: 'gridpt' }, svg);
      const hit = el('circle', { cx: X(a), cy: Y(b), r: 14, fill: 'transparent', class: 'gridpt' }, svg);
      hit.addEventListener('click', () => click(a, b));
      const t = el('title', {}, hit); t.textContent = `(${a}, ${b})`;
      void pt;
    }
    message();
  }
  function click(a, b) {
    if (mode === 'class') sel = [a, b];
    else if (!P || (P && Q)) { P = [a, b]; Q = null; }
    else Q = [a, b];
    draw();
  }
  function message() {
    if (mode === 'class') {
      const [a, b] = sel, k = a - b;
      const reps = [];
      for (let x = Math.max(0, k); x <= Math.min(M, M + k) && reps.length < 6; x++) reps.push(`(${x},${x - k})`);
      okBox($('zMsg'), bi(`Class of <span class="m">(${a}, ${b})</span>: all <span class="m">(c, d)</span> with <span class="m">${a} + d = ${b} + c</span>:<br><span class="m">${reps.join(' ~ ')} ~ …</span><br>This class <b>is</b> the integer <b>${k}</b>${k >= 0 ? ` = [(${k}, 0)], the copy of the natural number ${k}` : ` = [(0, ${-k})], the negative of ${-k}`}.`,
        `<span class="m">(${a}, ${b})</span> 的等价类：所有满足 <span class="m">${a} + d = ${b} + c</span> 的 <span class="m">(c, d)</span>：<br><span class="m">${reps.join(' ~ ')} ~ …</span><br>这个类<b>就是</b>整数 <b>${k}</b>${k >= 0 ? ` = [(${k}, 0)]，即自然数 ${k} 的副本` : ` = [(0, ${-k})]，即 ${-k} 的相反数`}。`), 'info');
    } else if (!P) okBox($('zMsg'), bi('Click a first point (blue).', '点第一个点（蓝色）。'), 'info');
    else if (!Q) okBox($('zMsg'), bi(`First: (${P[0]}, ${P[1]}), which represents ${P[0] - P[1]}. Now click a second point (green).`, `第一个点：(${P[0]}, ${P[1]})，代表 ${P[0] - P[1]}。再点第二个点（绿色）。`), 'info');
    else {
      const s = [P[0] + Q[0], P[1] + Q[1]];
      okBox($('zMsg'), `<span class="m">(${P[0]},${P[1]}) + (${Q[0]},${Q[1]}) = (${s[0]},${s[1]})</span><br>` + bi(`${P[0] - P[1]} + ${Q[0] - Q[1]} = <b>${s[0] - s[1]}</b> (purple line). ${s[0] > M || s[1] > M ? 'The sum lies off the grid, but its class line is drawn. ' : ''}Press “Other representatives”: the points move along their lines, and the sum stays on the same purple line. That is well-definedness.`,
        `${P[0] - P[1]} + ${Q[0] - Q[1]} = <b>${s[0] - s[1]}</b>（紫线）。${s[0] > M || s[1] > M ? '和落在格子外面，但它所在的类线已画出。' : ''}按“换代表元”：两个点沿各自的斜线移动，而和始终落在同一条紫线上。这就是良定义。`), 'ok');
    }
  }
  const rerep = ([a, b]) => { const k = a - b, lo = Math.max(0, k), hi = Math.min(6, 6 + k); const x = lo + Math.floor(Math.random() * Math.max(1, hi - lo + 1)); return [x, x - k]; };
  $('zMode1').addEventListener('click', () => { mode = 'class'; $('zMode1').classList.add('sel'); $('zMode2').classList.remove('sel'); draw(); });
  $('zMode2').addEventListener('click', () => { mode = 'add'; P = [2, 5]; Q = [4, 1]; $('zMode2').classList.add('sel'); $('zMode1').classList.remove('sel'); draw(); });
  $('zShuffle').addEventListener('click', () => {
    if (mode === 'class') { sel = rerep(sel); draw(); return; }
    if (P && Q) { P = rerep(P); Q = rerep(Q); draw(); }
  });
  $('zNeg').addEventListener('click', () => {
    if (mode !== 'class') { mode = 'class'; $('zMode1').classList.add('sel'); $('zMode2').classList.remove('sel'); }
    sel = [sel[1], sel[0]];
    draw();
  });
  draw();
})();

/* ================= §6 ℚ grid ================= */
(function rationals() {
  const svg = $('qSvg');
  const A = 8, Bm = 6, SP = 30, CX = 275, CY = 210;
  const X = a => CX + a * SP, Y = b => CY - b * SP;
  let sel = [2, 3];
  function draw() {
    svg.innerHTML = '';
    el('line', { x1: X(-A) - 10, y1: CY, x2: X(A) + 10, y2: CY, stroke: '#e03131', 'stroke-width': 1, 'stroke-dasharray': '4 4' }, svg);
    el('line', { x1: CX, y1: Y(Bm) - 10, x2: CX, y2: Y(-Bm) + 10, stroke: '#ccc' }, svg);
    svgText(svg, X(A) + 12, CY + 4, 'a', { 'font-size': 13, 'font-weight': 700, fill: '#666' });
    svgText(svg, CX + 6, Y(Bm) - 12, 'b', { 'font-size': 13, 'font-weight': 700, fill: '#666' });
    svgText(svg, X(-A), CY + 20, 'b = 0: forbidden · 禁止', { 'font-size': 11, fill: '#e03131' });
    const [a, b] = sel;
    // line through origin and (a, b), clipped to the grid box
    const t = Math.min(Math.abs(a) ? (A + 0.4) / Math.abs(a) : Infinity, (Bm + 0.4) / Math.abs(b));
    el('line', { x1: X(-a * t), y1: Y(-b * t), x2: X(a * t), y2: Y(b * t), stroke: '#f08c00', 'stroke-width': 4, 'stroke-linecap': 'round', opacity: 0.8 }, svg);
    const onLine = (x, y) => y !== 0 && x * b === y * a;
    for (let x = -A; x <= A; x++) for (let y = -Bm; y <= Bm; y++) {
      if (y === 0) { svgText(svg, X(x), Y(0) + 4, '×', { 'text-anchor': 'middle', 'font-size': 11, fill: '#e8a0a0' }); continue; }
      const on = onLine(x, y), me = x === a && y === b;
      el('circle', { cx: X(x), cy: Y(y), r: me ? 8 : on ? 6 : 3.5, fill: me ? '#1f2430' : on ? '#f08c00' : '#9aa0aa' }, svg);
      const hit = el('circle', { cx: X(x), cy: Y(y), r: 13, fill: 'transparent', class: 'gridpt' }, svg);
      hit.addEventListener('click', () => { sel = [x, y]; draw(); });
      const tt = el('title', {}, hit); tt.textContent = `(${x}, ${y})`;
    }
    const g = gcd(a, b), s = b < 0 ? -1 : 1;
    const p = s * a / g, q = s * b / g;
    const reps = [];
    for (let y = -Bm; y <= Bm; y++) for (let x = -A; x <= A; x++) if (onLine(x, y)) reps.push(`(${x},${y})`);
    svgText(svg, X(A) - 4, Y(Bm) + 4, q === 1 ? `${p}` : `${p}/${q}`, { 'text-anchor': 'end', 'font-size': 20, 'font-weight': 800, fill: '#f08c00' });
    okBox($('qMsg'), bi(`Class of <span class="m">(${a}, ${b})</span> = the rational <b>${q === 1 ? p : p + '/' + q}</b> ≈ ${(a / b).toFixed(4)}. Visible representatives: <span class="m">${reps.join(', ')}</span>. Each satisfies <span class="m">x·${b} = y·${a}</span>.`,
      `<span class="m">(${a}, ${b})</span> 的等价类 = 有理数 <b>${q === 1 ? p : p + '/' + q}</b> ≈ ${(a / b).toFixed(4)}。图中可见的代表元：<span class="m">${reps.join(', ')}</span>。它们都满足 <span class="m">x·${b} = y·${a}</span>。`), 'info');
  }
  draw();
})();

/* ================= §7 Dedekind cuts ================= */
(function dedekind() {
  const svg = $('ddSvg');
  const XL = 40, XR = 820, LY = 112;
  const SQ2 = Math.SQRT2;
  let lo = -1, hi = 3, mode = 'free', x = 1.25, dragging = false, zooming = 0;
  const toPx = v => XL + (v - lo) / (hi - lo) * (XR - XL);
  const toV = px => lo + (px - XL) / (XR - XL) * (hi - lo);
  // exact test for the √2 cut on a tick k·10^-e or p/q
  const inSqrt2 = (p, q) => p < 0n || p * p < 2n * q * q;
  function ticks() {
    const w = hi - lo, out = [];
    if (w > 0.6) {
      const seen = new Set();
      for (let q = 1; q <= 6; q++) for (let p = Math.ceil(lo * q); p <= Math.floor(hi * q); p++) {
        const g = gcd(p, q); const key = (p / g) + '/' + (q / g);
        if (seen.has(key)) continue;
        seen.add(key);
        out.push({ v: p / q, P: BigInt(p / g), Q: BigInt(q / g), h: q === 1 ? 18 : 12 - q, lab: q === 1 ? String(p) : null });
      }
    } else {
      // 1-2-5 tick step close to w/40; tick values are exact fractions N / 10^E
      const target = w / 40, E = -Math.floor(Math.log10(target) + 1e-12);
      const pow = 10 ** -E, m = [1, 2, 5, 10].find(x => x * pow >= target * (1 - 1e-9));
      const Q = 10n ** BigInt(E);
      const j0 = Math.ceil(lo / (m * pow)), j1 = Math.floor(hi / (m * pow));
      for (let j = j0; j <= j1; j++) {
        const major = j % 5 === 0, N = j * m;
        out.push({ v: N * pow, P: BigInt(N), Q, h: major ? 16 : 9, lab: major ? (N * pow).toFixed(Math.max(0, E)) : null });
      }
    }
    return out;
  }
  const inL = t => mode === 'sqrt2' ? inSqrt2(t.P, t.Q) : t.v < x - 1e-12;
  function snapRational(v) {
    for (let q = 1; q <= 6; q++) { const p = Math.round(v * q); if (Math.abs(p / q - v) < 0.012 * (hi - lo) / 4) return [p, q]; }
    return null;
  }
  function draw() {
    svg.innerHTML = '';
    const cutV = mode === 'sqrt2' ? SQ2 : x;
    const cp = Math.max(XL, Math.min(XR, toPx(cutV)));
    el('rect', { x: XL, y: LY - 16, width: cp - XL, height: 32, fill: 'rgba(59,91,219,.13)' }, svg);
    el('line', { x1: XL - 10, y1: LY, x2: XR + 10, y2: LY, stroke: '#1f2430', 'stroke-width': 1.5 }, svg);
    ticks().forEach(t => {
      const px = toPx(t.v), blue = inL(t);
      el('line', { x1: px, y1: LY - t.h / 2, x2: px, y2: LY + t.h / 2, stroke: blue ? '#3b5bdb' : '#f08c00', 'stroke-width': t.lab ? 2.2 : 1.3 }, svg);
      if (t.lab) svgText(svg, px, LY + 32, t.lab, { 'text-anchor': 'middle', 'font-size': 12, fill: '#555' });
    });
    // knife
    el('line', { x1: cp, y1: 40, x2: cp, y2: LY + 20, stroke: '#ae3ec9', 'stroke-width': 2.5 }, svg);
    const h = el('g', { style: 'cursor:ew-resize' }, svg);
    el('circle', { cx: cp, cy: 34, r: 12, fill: '#ae3ec9' }, h);
    svgText(h, cp, 39, '✂', { 'text-anchor': 'middle', 'font-size': 13, fill: '#fff' });
    svgText(svg, XL, 22, 'L (blue · 蓝)', { 'font-size': 13, 'font-weight': 700, fill: '#3b5bdb' });
    svgText(svg, XR, 22, 'ℚ ∖ L (orange · 橙)', { 'text-anchor': 'end', 'font-size': 13, 'font-weight': 700, fill: '#f08c00' });
    const mag = 4 / (hi - lo);
    if (mag > 1.5) svgText(svg, XR, 186, `×${mag >= 1000 ? '10^' + Math.round(Math.log10(mag)) : Math.round(mag)}`, { 'text-anchor': 'end', 'font-size': 14, 'font-weight': 800, fill: '#ae3ec9' });
    if (mode === 'sqrt2') svgText(svg, cp + 8, 56, '√2', { 'font-size': 15, 'font-weight': 800, fill: '#ae3ec9' });
    message();
  }
  function message() {
    if (zooming) return;
    if (mode === 'sqrt2') {
      const w = hi - lo;
      okBox($('ddMsg'), bi(`<span class="m">L = {q ∈ ℚ : q &lt; 0 ∨ q² &lt; 2}</span>, defined without mentioning √2. Membership of every tick is decided exactly, with integer arithmetic. ${w < 0.01 ? 'Even at this magnification, blue ticks never reach the knife from below and orange ones never reach it from above: L has no maximum and ℚ ∖ L has no minimum.' : 'Press “Zoom” to look closely at the gap.'}`,
        `<span class="m">L = {q ∈ ℚ : q &lt; 0 ∨ q² &lt; 2}</span>，定义中根本没提到 √2。每个刻度属不属于 L 都用整数运算精确判定。${w < 0.01 ? '放大到这个程度，蓝色刻度从下方始终够不到刀口，橙色刻度从上方也够不到：L 没有最大元，ℚ ∖ L 也没有最小元。' : '按“放大”仔细看看这个缺口。'}`), 'info');
      return;
    }
    const r = snapRational(x);
    if (r) {
      const [p, q] = r, s = q === 1 ? String(p) : `${p}/${q}`;
      okBox($('ddMsg'), bi(`Knife at the rational <b>${s}</b>: <span class="m">L = {q ∈ ℚ : q &lt; ${s}}</span>. The point ${s} itself goes to the orange side, so L has no greatest element (condition iii). Putting ${s} into L would create a maximum, so that set is not a cut.`,
        `刀口落在有理数 <b>${s}</b>：<span class="m">L = {q ∈ ℚ : q &lt; ${s}}</span>。${s} 本身归到橙色一侧，所以 L 没有最大元（条件 iii）。若把 ${s} 也放进 L，就会出现最大元，那样的集合就不是分割了。`), 'info');
    } else okBox($('ddMsg'), bi(`Knife at ≈ ${x.toFixed(3)}. L is every rational to the left. Drag it onto a fraction with a small denominator, or press √2.`, `刀口约在 ${x.toFixed(3)}。L 由它左边的全体有理数组成。把它拖到某个小分母的分数上，或者按 √2。`), 'info');
  }
  function evV(e) {
    const pt = svg.createSVGPoint();
    pt.x = e.clientX; pt.y = e.clientY;
    return toV(pt.matrixTransform(svg.getScreenCTM().inverse()).x);
  }
  svg.addEventListener('pointerdown', e => {
    if (zooming) return;
    dragging = true;
    svg.setPointerCapture(e.pointerId);
    if (hi - lo < 3.9) { lo = -1; hi = 3; }
    mode = 'free';
    x = Math.max(lo, Math.min(hi, evV(e)));
    const r = snapRational(x); if (r) x = r[0] / r[1];
    draw();
  });
  svg.addEventListener('pointermove', e => {
    if (!dragging) return;
    x = Math.max(lo, Math.min(hi, evV(e)));
    const r = snapRational(x); if (r) x = r[0] / r[1];
    draw();
  });
  svg.addEventListener('pointerup', () => { dragging = false; });
  $('ddS2').addEventListener('click', () => { zooming = 0; mode = 'sqrt2'; lo = -1; hi = 3; draw(); });
  $('ddReset').addEventListener('click', () => { zooming = 0; lo = -1; hi = 3; draw(); });
  $('ddZoom').addEventListener('click', () => {
    mode = 'sqrt2';
    const my = ++zooming;
    const w0 = Math.log10(4), w1 = Math.log10(4e-7), T = 7000;
    const c0 = 1, t0 = performance.now();
    okBox($('ddMsg'), bi('Zooming in on the cut, 10× per second…', '正在放大切口，每秒放大 10 倍……'), 'info');
    function frame(now) {
      if (my !== zooming) return;
      const u = Math.min(1, (now - t0) / T);
      const w = 10 ** (w0 + (w1 - w0) * u);
      const c = c0 + (SQ2 - c0) * Math.min(1, u * 4);
      lo = c - w / 2; hi = c + w / 2;
      draw();
      if (u < 1) requestAnimationFrame(frame);
      else { zooming = 0; message(); }
    }
    requestAnimationFrame(frame);
  });
  draw();

  // least upper bound bands
  const lsvg = $('lubSvg');
  const vals = ['1', '1.4', '1.41', '1.414', '1.4142', '1.41421'];
  let shown = 0;
  const LX = v => 30 + (v + 0.5) / 2.3 * 560;
  function lub() {
    lsvg.innerHTML = '';
    el('line', { x1: LX(-0.5), y1: 214, x2: LX(1.8), y2: 214, stroke: '#1f2430' }, lsvg);
    [-0.5, 0, 0.5, 1, 1.5].forEach(v => { el('line', { x1: LX(v), y1: 209, x2: LX(v), y2: 219, stroke: '#1f2430' }, lsvg); svgText(lsvg, LX(v), 234, v, { 'text-anchor': 'middle', 'font-size': 11, fill: '#666' }); });
    el('line', { x1: LX(SQ2), y1: 8, x2: LX(SQ2), y2: 214, stroke: '#ae3ec9', 'stroke-dasharray': '4 4' }, lsvg);
    svgText(lsvg, LX(SQ2) + 4, 18, '√2', { 'font-size': 13, 'font-weight': 700, fill: '#ae3ec9' });
    for (let i = 0; i < shown; i++) {
      const v = +vals[i], y = 26 + i * 22;
      const r = el('rect', { x: LX(-0.5), y, width: LX(v) - LX(-0.5), height: 15, rx: 3, fill: 'rgba(59,91,219,.25)', stroke: '#3b5bdb', class: 'fadein' }, lsvg);
      void r;
      svgText(lsvg, 640, y + 12, `L${sub(i + 1)} = {q : q < ${vals[i]}}`, { 'font-size': 12, fill: '#3b5bdb' });
    }
    const y = 26 + 6 * 22 + 6;
    el('rect', { x: LX(-0.5), y, width: LX(SQ2) - LX(-0.5), height: 18, rx: 3, fill: shown === 6 ? 'rgba(240,140,0,.35)' : 'rgba(240,140,0,.12)', stroke: '#f08c00', 'stroke-dasharray': shown === 6 ? '' : '5 4' }, lsvg);
    svgText(lsvg, 640, y + 14, '⋃ₖ Lₖ = {q : q < 0 ∨ q² < 2}', { 'font-size': 12, 'font-weight': 700, fill: '#c46e00' });
    if (shown) { svgText(lsvg, 640, y + 32, shown < 6 ? `${shown} of ∞ many added so far` : '… and so on forever', { 'font-size': 11, fill: '#888' }); svgText(lsvg, 640, y + 47, shown < 6 ? `已加入 ${shown} 个，共无穷多个` : '以此类推，直至无穷', { 'font-size': 11, fill: '#888' }); }
  }
  $('lubAdd').addEventListener('click', () => { if (shown < 6) shown++; lub(); });
  $('lubReset').addEventListener('click', () => { shown = 0; lub(); });
  shown = 2;
  lub();
})();

/* ================= §8 Cauchy ================= */
(function cauchy() {
  const svg = $('cySvg');
  const T = 8;
  const dec = Array.from({ length: 14 }, (_, n) => Math.floor(Math.SQRT2 * 10 ** n) / 10 ** n);
  const newt = [1];
  for (let n = 1; n < 14; n++) newt.push(newt[n - 1] / 2 + 1 / newt[n - 1]);
  const VX = v => 70 + (v - 0.98) / (1.56 - 0.98) * 560;
  const firstN = (seq, eps) => { for (let N = 0; N < 12; N++) { let ok = true; for (let m = N; m < 14 && ok; m++) for (let k = N; k < 14; k++) if (Math.abs(seq[m] - seq[k]) >= eps) { ok = false; break; } if (ok) return N; } return 12; };
  function draw() {
    const e = +$('cyE').value;
    $('cyEv').textContent = e;
    const eps = 10 ** -e;
    const Nd = firstN(dec, eps), Nn = firstN(newt, eps);
    svg.innerHTML = '';
    svgText(svg, 6, 16, 'n', { 'font-size': 12, fill: '#888' });
    svgText(svg, 680, 16, '|dₙ − rₙ|', { 'font-size': 13, 'font-weight': 700, fill: '#ae3ec9' });
    el('line', { x1: VX(Math.SQRT2), y1: 22, x2: VX(Math.SQRT2), y2: 236, stroke: '#ae3ec9', 'stroke-dasharray': '5 4' }, svg);
    svgText(svg, VX(Math.SQRT2), 272, '√2 ∉ ℚ: gap · 缺口', { 'text-anchor': 'middle', 'font-size': 12, fill: '#ae3ec9' });
    [1, 1.1, 1.2, 1.3, 1.4, 1.5].forEach(v => svgText(svg, VX(v), 252, v.toFixed(1), { 'text-anchor': 'middle', 'font-size': 11, fill: '#888' }));
    for (let n = 0; n < T; n++) {
      const y = 34 + n * 26;
      if (n >= Nd) el('rect', { x: 60, y: y - 12, width: 580, height: 11, fill: 'rgba(59,91,219,.10)' }, svg);
      if (n >= Nn) el('rect', { x: 60, y: y - 1, width: 580, height: 11, fill: 'rgba(47,158,68,.10)' }, svg);
      svgText(svg, 10, y + 4, n, { 'font-size': 12, fill: '#666' });
      el('line', { x1: 60, y1: y, x2: 640, y2: y, stroke: '#eee' }, svg);
      el('circle', { cx: VX(dec[n]), cy: y - 5, r: 5, fill: '#3b5bdb' }, svg);
      el('circle', { cx: VX(newt[n]), cy: y + 5, r: 5, fill: '#2f9e44' }, svg);
      const d = Math.abs(dec[n] - newt[n]);
      svgText(svg, 680, y + 4, d === 0 ? '0' : d.toExponential(1), { 'font-size': 12, fill: '#ae3ec9' });
    }
    svgText(svg, 70, 16, '● dₙ decimals · 十进制截断', { 'font-size': 12, fill: '#3b5bdb' });
    svgText(svg, 300, 16, '● rₙ Newton · 牛顿迭代', { 'font-size': 12, fill: '#2f9e44' });
    okBox($('cyMsg'), bi(`ε = 10<sup>−${e}</sup>: the decimals stay within ε of each other from <b>N = ${Nd}</b> on (blue rows), Newton's sequence from <b>N = ${Nn}</b> on (green rows). It converges quadratically. Both are Cauchy, their difference tends to 0, so they define the <b>same</b> real number, even though neither has a limit in ℚ.`,
      `ε = 10<sup>−${e}</sup>：十进制截断从 <b>N = ${Nd}</b> 起两两相差小于 ε（蓝色行），牛顿数列从 <b>N = ${Nn}</b> 起即可（绿色行），它是平方收敛的。两者都是柯西列，差趋于 0，所以它们代表<b>同一个</b>实数，尽管在 ℚ 中谁都没有极限。`), 'info');
  }
  $('cyE').addEventListener('input', draw);
  draw();
})();

/* ================= §9 cardinalities ================= */
(function cardinals() {
  const svg = $('cdSvg');
  let tok = 0;
  async function zig() {
    const my = ++tok;
    svg.innerHTML = '';
    const X = k => 430 + k * 55, Y = 170;
    el('line', { x1: 20, y1: Y, x2: 840, y2: Y, stroke: '#1f2430' }, svg);
    for (let k = -7; k <= 7; k++) { el('circle', { cx: X(k), cy: Y, r: 5, fill: '#9aa0aa' }, svg); svgText(svg, X(k), Y + 24, k, { 'text-anchor': 'middle', 'font-size': 13 }); }
    svgText(svg, 20, 30, 'f(n) = (n+1)/2 (n odd),  −n/2 (n even)', { 'font-size': 13, fill: '#ae3ec9', 'font-weight': 700 });
    // f(0)=0, f(1)=-1? Use 0, 1, -1, 2, -2, ...
    let prev = null;
    for (let i = 0; i <= 14; i++) {
      const z = i % 2 ? (i + 1) / 2 : -i / 2;
      const zz = i === 0 ? 0 : z;
      if (prev !== null) {
        const up = i % 2;
        el('path', { d: `M${X(prev)} ${Y - 6} Q ${(X(prev) + X(zz)) / 2} ${Y - 30 - Math.abs(zz - prev) * 9} ${X(zz)} ${Y - 6}`, fill: 'none', stroke: up ? '#3b5bdb' : '#2f9e44', 'stroke-width': 2, class: 'fadein' }, svg);
      }
      el('circle', { cx: X(zz), cy: Y, r: 9, fill: '#ae3ec9', class: 'pop' }, svg);
      svgText(svg, X(zz), Y + 50, 'n=' + i, { 'text-anchor': 'middle', 'font-size': 11, fill: '#ae3ec9', 'font-weight': 700, class: 'fadein' });
      prev = zz;
      await sleep(350);
      if (my !== tok) return;
    }
  }
  async function grid() {
    const my = ++tok;
    svg.innerHTML = '';
    const P = 8, Q = 6, CW = 90, CH = 46, X0 = 60, Y0 = 40;
    const cell = (p, q) => [X0 + (p - 1) * CW + CW / 2, Y0 + (q - 1) * CH + CH / 2];
    svgText(svg, X0, 22, 'p →', { 'font-size': 12, fill: '#888' });
    svgText(svg, 12, Y0 + 20, 'q ↓', { 'font-size': 12, fill: '#888' });
    const lab = {};
    for (let p = 1; p <= P; p++) for (let q = 1; q <= Q; q++) {
      const [x, y] = cell(p, q);
      lab[p + ',' + q] = svgText(svg, x, y + 5, `${p}/${q}`, { 'text-anchor': 'middle', 'font-size': 14, fill: '#bbb' });
    }
    let n = 0, prev = null;
    for (let s = 2; s <= P + Q && n < 30; s++) for (let p = 1; p < s; p++) {
      const q = s - p;
      if (p > P || q > Q) continue;
      const [x, y] = cell(p, q);
      if (prev) el('line', { x1: prev[0], y1: prev[1], x2: x, y2: y, stroke: '#d0ccc0', 'stroke-width': 1.5 }, svg);
      prev = [x, y];
      const t = lab[p + ',' + q];
      if (gcd(p, q) > 1) { t.setAttribute('fill', '#e03131'); t.setAttribute('text-decoration', 'line-through'); }
      else {
        t.setAttribute('fill', '#1f2430'); t.setAttribute('font-weight', 700);
        svgText(svg, x + 22, y - 8, n++, { 'font-size': 11, fill: '#ae3ec9', 'font-weight': 800, class: 'pop' });
      }
      svg.appendChild(t);
      await sleep(160);
      if (my !== tok) return;
    }
  }
  async function diag() {
    const my = ++tok;
    svg.innerHTML = '';
    const R = 7, D = 9;
    const rows = Array.from({ length: R }, () => Array.from({ length: D }, () => Math.floor(Math.random() * 10)));
    const X0 = 120, CW = 34, Y0 = 40, RH = 34;
    for (let i = 0; i < R; i++) {
      svgText(svg, 20, Y0 + i * RH + 22, `x${sub(i)} = 0.`, { 'font-size': 15, 'font-weight': 700 });
      for (let j = 0; j < D; j++) {
        const t = svgText(svg, X0 + j * CW, Y0 + i * RH + 22, rows[i][j], { 'text-anchor': 'middle', 'font-size': 16, id: `dg${i}_${j}` });
        void t;
      }
      svgText(svg, X0 + D * CW, Y0 + i * RH + 22, '…', { 'font-size': 15, fill: '#999' });
    }
    svgText(svg, 20, Y0 + R * RH + 14, '⋮', { 'font-size': 16, fill: '#999' });
    const yd = Y0 + R * RH + 46;
    svgText(svg, 20, yd, 'd = 0.', { 'font-size': 15, 'font-weight': 800, fill: '#ae3ec9' });
    for (let i = 0; i < R; i++) {
      await sleep(450);
      if (my !== tok) return;
      el('rect', { x: X0 + i * CW - 13, y: Y0 + i * RH + 2, width: 26, height: 28, rx: 6, fill: 'none', stroke: '#ae3ec9', 'stroke-width': 2.5, class: 'pop' }, svg);
      const nd = rows[i][i] === 5 ? 4 : 5;
      svgText(svg, X0 + i * CW, yd, nd, { 'text-anchor': 'middle', 'font-size': 16, 'font-weight': 800, fill: '#ae3ec9', class: 'pop' });
      svgText(svg, X0 + D * CW + 40, Y0 + i * RH + 22, `d ≠ x${sub(i)}: digit ${i + 1} · 第 ${i + 1} 位 ${nd} ≠ ${rows[i][i]}`, { 'font-size': 12, fill: '#e03131', class: 'fadein' });
    }
    svgText(svg, X0 + R * CW, yd, '…', { 'font-size': 15, fill: '#ae3ec9' });
  }
  const msgs = {
    z: bi('0, 1, −1, 2, −2, …: every integer is hit exactly once, so <span class="m">|ℤ| = ℵ₀</span>.', '0, 1, −1, 2, −2, …：每个整数恰好被数到一次，所以 <span class="m">|ℤ| = ℵ₀</span>。'),
    q: bi('Walk the anti-diagonals p + q = 2, 3, 4, …, skipping fractions not in lowest terms (red), since they name a class already counted. This lists ℚ⁺. Then 0, q₀, −q₀, q₁, −q₁, … lists ℚ, so <span class="m">|ℚ| = ℵ₀</span>.',
      '沿反对角线 p + q = 2, 3, 4, … 依次走，跳过非既约分数（红色），因为它们代表的类已经数过了。这样就列出了 ℚ⁺。再按 0, q₀, −q₀, q₁, −q₁, … 排列就列出了 ℚ，所以 <span class="m">|ℚ| = ℵ₀</span>。'),
    r: bi('Given any list of reals in (0, 1), build d digit by digit: 5 where the diagonal digit isn\'t 5, else 4. d uses no 0s or 9s, so its decimal expansion is unique, and it differs from xᵢ at digit i + 1. No list is complete: <span class="m">|ℝ| &gt; ℵ₀</span>. Click the tab again for a new list.',
      '任给 (0, 1) 中实数的一张清单，逐位构造 d：对角线数字不是 5 就取 5，是 5 就取 4。d 不含 0 和 9，所以十进制展开唯一，并且它在第 i + 1 位与 xᵢ 不同。任何清单都不完整：<span class="m">|ℝ| &gt; ℵ₀</span>。再点一次标签可换一张清单。'),
  };
  const run = { z: zig, q: grid, r: diag };
  document.querySelectorAll('[data-cd]').forEach(b => b.addEventListener('click', () => {
    document.querySelectorAll('[data-cd]').forEach(x => x.classList.toggle('sel', x === b));
    okBox($('cdMsg'), msgs[b.dataset.cd], 'info');
    run[b.dataset.cd]();
  }));
  okBox($('cdMsg'), msgs.z, 'info');
  zig();
})();

/* ================= exercises ================= */
(function keys() {
  ['∅', '{', '}', ',', '(', ')'].forEach(s => {
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
// Generic answer row. item: { q, placeholder, check(str) -> {ok, en, zh} | ParseError thrown, answer, en, zh, preview(str) -> html }
function answerRow(box, item, onSolve) {
  const row = document.createElement('div');
  row.className = 'tf';
  row.innerHTML = `<div style="flex:1 1 100%">${item.q}</div>
    <input class="formula" style="flex:1 1 260px" placeholder="${item.placeholder || ''}">
    <button class="btn small primary" data-a="c">${bil('Check', '检查')}</button>
    <button class="btn small ghost" data-a="s">${bil('Show answer', '看答案')}</button>
    <div style="flex-basis:100%"><div class="prev"></div><div class="msg"></div></div>`;
  box.appendChild(row);
  const inp = row.querySelector('input'), msg = row.querySelector('.msg'), prev = row.querySelector('.prev');
  let revealed = false; // after "Show answer", Check never earns progress again during this page session
  inp.addEventListener('focus', () => { lastSetInput = inp; });
  inp.addEventListener('input', () => { if (item.preview) { try { prev.innerHTML = item.preview(inp.value); } catch { prev.innerHTML = ''; } } });
  const check = () => {
    let r;
    try { r = item.check(inp.value); } catch (e) { errBox(msg, e); return; }
    if (r.ok) { okBox(msg, '✓ ' + bi(item.en, item.zh)); if (!revealed) onSolve(); }
    else okBox(msg, bi(r.en, r.zh), 'bad');
  };
  row.querySelector('[data-a=c]').addEventListener('click', check);
  inp.addEventListener('keydown', e => e.key === 'Enter' && check());
  row.querySelector('[data-a=s]').addEventListener('click', () => {
    revealed = true;
    inp.value = item.answer;
    inp.dispatchEvent(new Event('input'));
    okBox(msg, bi(`Answer: <span class="m">${item.answer}</span>. ${item.en}`, `答案：<span class="m">${item.answer}</span>。${item.zh}`), 'info');
  });
}
function parsePair(str) {
  const s = String(str).replace(/（/g, '(').replace(/）/g, ')').replace(/，/g, ',').trim();
  if (!s.startsWith('(') || !s.endsWith(')')) throw new ParseError('Write the pair as (x, y)', '请把有序对写成 (x, y)');
  const inner = s.slice(1, -1);
  let depth = 0, cut = -1;
  for (let i = 0; i < inner.length; i++) {
    const c = inner[i];
    if (c === '{' || c === '｛') depth++;
    else if (c === '}' || c === '｝') depth--;
    else if (c === ',' && depth === 0) { if (cut >= 0) throw new ParseError('A pair has exactly two coordinates', '有序对恰好有两个分量'); cut = i; }
  }
  if (cut < 0) throw new ParseError('Missing the comma between the coordinates', '两个分量之间缺少逗号');
  return [HF.parse(inner.slice(0, cut)).set, HF.parse(inner.slice(cut + 1)).set];
}
function tfRows(box, items, onAll, showBtn) {
  const solved = items.map(() => false);
  let revealed = false; // after "Show answer(s)", correct clicks no longer earn progress
  const rows = items.map((it, i) => {
    const row = document.createElement('div');
    row.className = 'tf';
    row.innerHTML = `<div class="stmt">${it.s}</div>
      <button class="btn small" data-v="1">${bil(it.yes || 'True', it.yesz || '对')}</button>
      <button class="btn small" data-v="0">${bil(it.no || 'False', it.noz || '错')}</button>
      <div style="flex-basis:100%"><div class="msg"></div></div>`;
    box.appendChild(row);
    const msg = row.querySelector('.msg');
    row.querySelectorAll('button').forEach(b => b.addEventListener('click', () => {
      if ((b.dataset.v === '1') === it.ans) {
        okBox(msg, '✓ ' + bi(it.en, it.zh));
        solved[i] = true;
        if (solved.every(Boolean) && !revealed) onAll();
      } else okBox(msg, bi('✗ Not quite. Check the definitions again.', '✗ 不对，再对照一下定义。'), 'bad');
    }));
    return msg;
  });
  if (showBtn) showBtn.addEventListener('click', () => (revealed = true) && items.forEach((it, i) => okBox(rows[i], bi(`<b>${it.ans ? (it.yes || 'True') : (it.no || 'False')}.</b> ${it.en}`, `<b>${it.ans ? (it.yesz || '对') : (it.noz || '错')}。</b>${it.zh}`), 'info')));
  return rows;
}

/* E1 */
(function e1() {
  const P = s => HF.parse(s).set;
  const solved = [false, false, false, false];
  const fin = () => solved.every(Boolean) && Progress.mark('L7E1');
  const decode = (q, want, answer, en, zh, k) => answerRow($('e1List'), {
    q, placeholder: '(x, y)', answer, en, zh,
    check: s => { const [x, y] = parsePair(s); return x === want[0] && y === want[1] ? { ok: true } : { ok: false, en: `(${HF.show(x, true)}, ${HF.show(y, true)}) encodes ${HF.show(kp(x, y))}, a different set.`, zh: `(${HF.show(x, true)}, ${HF.show(y, true)}) 编码出的是 ${HF.show(kp(x, y))}，不是同一个集合。` }; },
  }, () => { solved[k] = true; fin(); });
  decode(`<b>(a)</b> ${bil('Decode', '解码')} <span class="m">p = {{∅}, {∅, {∅}}}</span> &nbsp; ${boxes(P('{{∅},{∅,{∅}}}'))}`, [HF.nat(0), HF.nat(1)], '(0, 1)',
    '{∅} = {0} is the singleton, so the first coordinate is 0; the other element of {∅, {∅}} is {∅} = 1.', '{∅} = {0} 是单元素集，所以第一分量是 0；{∅, {∅}} 中另一个元素是 {∅} = 1。', 0);
  decode(`<b>(b)</b> ${bil('Decode', '解码')} <span class="m">p = {{{∅}}}</span> &nbsp; ${boxes(P('{{{∅}}}'))}`, [HF.nat(1), HF.nat(1)], '(1, 1)',
    'Only one member, {{∅}} = {1}: the degenerate case, (1, 1) = {{1}}.', '只有一个元素 {{∅}} = {1}：这是退化情形，(1, 1) = {{1}}。', 1);
  answerRow($('e1List'), {
    q: `<b>(c)</b> ${bil('Encode <span class="m">(1, 0)</span> using only ∅, braces and commas.', '只用 ∅、花括号和逗号写出 <span class="m">(1, 0)</span>。')}`, placeholder: '{ … }',
    answer: HF.show(kp(HF.nat(1), HF.nat(0))), en: '(1, 0) = {{1}, {1, 0}} = {{{∅}}, {∅, {∅}}}. Note it differs from (0, 1) = {{∅}, {∅, {∅}}}.', zh: '(1, 0) = {{1}, {1, 0}} = {{{∅}}, {∅, {∅}}}。注意它与 (0, 1) = {{∅}, {∅, {∅}}} 不同。',
    preview: s => rawBoxes(HF.parse(s, false)),
    check: s => { const r = HF.parse(s, false).set; return r === kp(HF.nat(1), HF.nat(0)) ? { ok: true } : { ok: false, en: 'Not the same set as {{1}, {1, 0}}. Build {1} = {{∅}} and {1, 0} first.', zh: '与 {{1}, {1, 0}} 不是同一个集合。先写出 {1} = {{∅}} 和 {1, 0}。' }; },
  }, () => { solved[2] = true; fin(); });
  const dmsg = $('e1dMsg');
  let revealedD = false;
  const dExp = bi('{{∅, {∅}}} = {2}. Every pair (a, b) contains the singleton {a}, but the only member here, {∅, {∅}}, has two elements. So it is <b>not</b> a pair.', '{{∅, {∅}}} = {2}。每个有序对 (a, b) 都含有单元素集 {a}，而这里唯一的元素 {∅, {∅}} 有两个元素。所以它<b>不是</b>有序对。');
  document.querySelectorAll('#e1 [data-d]').forEach(b => b.addEventListener('click', () => {
    if (b.dataset.d === 's') { revealedD = true; okBox(dmsg, dExp, 'info'); return; }
    if (b.dataset.d === '0') { okBox(dmsg, '✓ ' + dExp); if (!revealedD) { solved[3] = true; fin(); } }
    else okBox(dmsg, bi('✗ Which member would be the singleton {a}?', '✗ 哪个元素能充当单元素集 {a}？'), 'bad');
  }));
})();

/* E2 */
(function e2() {
  const solved = { a: false, b: false, c: false };
  const fin = () => solved.a && solved.b && solved.c && Progress.mark('L7E2');
  answerRow($('e2List'), {
    q: `<b>(a)</b> ${bil('Write 3 using only ∅, braces and commas.', '只用 ∅、花括号和逗号写出 3。')}`, placeholder: '{ … }',
    answer: HF.show(HF.nat(3)), en: '3 = {0, 1, 2} = {∅, {∅}, {∅, {∅}}}.', zh: '3 = {0, 1, 2} = {∅, {∅}, {∅, {∅}}}。',
    preview: s => rawBoxes(HF.parse(s, false)),
    check: s => { const r = HF.parse(s, false).set; return r === HF.nat(3) ? { ok: true } : { ok: false, en: `That set has ${r.m.length} member(s) but is not 3. Remember 3 = {0, 1, 2}.`, zh: `这个集合有 ${r.m.length} 个元素，但不是 3。记住 3 = {0, 1, 2}。` }; },
  }, () => { solved.a = true; fin(); });
  answerRow($('e2List'), {
    q: `<b>(b)</b> ${bil('Writing ∅ as {}, how many pairs of braces does the numeral 5 contain? (Use the “brace pairs” counter in §2 to spot the pattern for 0–4.)', '把 ∅ 写成 {}，自然数 5 一共含有多少对花括号？（可以借助 §2 的“花括号对数”找出 0–4 的规律。）')}`, placeholder: '?',
    answer: '32', en: 'b(0) = 1 and b(n) = 1 + b(0) + ⋯ + b(n−1), so b(n) = 2ⁿ and b(5) = 32.', zh: 'b(0) = 1，b(n) = 1 + b(0) + ⋯ + b(n−1)，所以 b(n) = 2ⁿ，b(5) = 32。',
    check: s => (+s.trim() === 32 ? { ok: true } : { ok: false, en: 'Not yet. One pair for the outer braces, plus all the pairs inside 0, 1, 2, 3 and 4.', zh: '还不对。最外层一对，再加上 0、1、2、3、4 各自内部的所有括号。' }),
  }, () => { solved.b = true; fin(); });
  tfRows($('e2TF'), [
    { s: '2 ∈ 5', ans: true, en: '5 = {0, 1, 2, 3, 4}.', zh: '5 = {0, 1, 2, 3, 4}。' },
    { s: '2 ⊆ 5', ans: true, en: '2 = {0, 1} and both 0, 1 ∈ 5. Natural numbers are transitive sets.', zh: '2 = {0, 1}，而 0、1 都属于 5。自然数都是传递集。' },
    { s: '5 ∈ 2', ans: false, en: '2 = {0, 1} has no member 5.', zh: '2 = {0, 1} 中没有 5。' },
    { s: '⋃5 = 4', ans: true, en: '⋃(n+1) = n ∪ ⋃n = n, since ⋃n ⊆ n.', zh: '⋃(n+1) = n ∪ ⋃n = n，因为 ⋃n ⊆ n。' },
    { s: '{2} ∈ 5', ans: false, en: '{2} = {{0, 1}} is not a natural number (1 is the only natural number with exactly one member, and 1 = {0} ≠ {2}).', zh: '{2} = {{0, 1}} 不是自然数（恰有一个元素的自然数只有 1，而 1 = {0} ≠ {2}）。' },
  ], () => { solved.c = true; fin(); }, $('e2Show'));
})();

/* E3 */
(function e3() {
  const svg = $('e3Svg');
  const M = 8, SP = 34, X0 = 30, Y0 = 300;
  const picked = new Set();
  let revealedA = false, revealedB = false;
  const want = new Set(Array.from({ length: 6 }, (_, a) => a + ',' + (a + 3)));
  let marks = {};
  function draw() {
    svg.innerHTML = '';
    for (let i = 0; i <= M; i++) {
      svgText(svg, X0 + i * SP, Y0 + 20, i, { 'text-anchor': 'middle', 'font-size': 10, fill: '#999' });
      svgText(svg, X0 - 16, Y0 - i * SP + 4, i, { 'text-anchor': 'middle', 'font-size': 10, fill: '#999' });
    }
    svgText(svg, X0 + M * SP + 10, Y0 + 20, 'a', { 'font-size': 12, fill: '#666' });
    svgText(svg, X0 - 20, Y0 - M * SP - 10, 'b', { 'font-size': 12, fill: '#666' });
    for (let a = 0; a <= M; a++) for (let b = 0; b <= M; b++) {
      const k = a + ',' + b, on = picked.has(k);
      el('circle', { cx: X0 + a * SP, cy: Y0 - b * SP, r: on ? 8 : 4.5, fill: marks[k] === 'bad' ? '#e03131' : marks[k] === 'miss' ? '#f08c00' : on ? '#3b5bdb' : '#9aa0aa' }, svg);
      const hit = el('circle', { cx: X0 + a * SP, cy: Y0 - b * SP, r: 14, fill: 'transparent', class: 'gridpt' }, svg);
      hit.addEventListener('click', () => { if (picked.has(k)) picked.delete(k); else picked.add(k); marks = {}; draw(); });
    }
  }
  draw();
  $('e3aCheck').addEventListener('click', () => {
    marks = {};
    let bad = 0, miss = 0;
    picked.forEach(k => { if (!want.has(k)) { marks[k] = 'bad'; bad++; } });
    want.forEach(k => { if (!picked.has(k)) miss++; });
    draw();
    if (!bad && !miss) { okBox($('e3aMsg'), '✓ ' + bi('The six points (0,3), (1,4), …, (5,8): exactly those with a + 3 = b, i.e. (a, b) ~ (0, 3).', '这六个点 (0,3)、(1,4)、…、(5,8)：恰好是满足 a + 3 = b 的点，即 (a, b) ~ (0, 3)。')); if (!revealedA) { done.a = true; fin(); } }
    else okBox($('e3aMsg'), bi(`${bad} wrong point(s) (red)${miss ? `, and ${miss} point(s) still missing` : ''}. (a, b) represents −3 exactly when a + 3 = b.`, `有 ${bad} 个点选错了（红色）${miss ? `，还漏了 ${miss} 个点` : ''}。(a, b) 代表 −3 当且仅当 a + 3 = b。`), 'bad');
  });
  $('e3aShow').addEventListener('click', () => {
    revealedA = true; picked.clear(); want.forEach(k => picked.add(k)); marks = {}; draw();
    okBox($('e3aMsg'), bi('Answer: (0,3), (1,4), (2,5), (3,6), (4,7), (5,8), the diagonal b = a + 3.', '答案：(0,3)、(1,4)、(2,5)、(3,6)、(4,7)、(5,8)，即斜线 b = a + 3。'), 'info');
  });
  const done = { a: false, b: false };
  const fin = () => done.a && done.b && Progress.mark('L7E3');
  [$('e3bX'), $('e3bY')].forEach(i => { i.addEventListener('keydown', e => e.key === 'Enter' && $('e3bCheck').click()); });
  $('e3bCheck').addEventListener('click', () => {
    const x = $('e3bX').value.trim(), y = $('e3bY').value.trim();
    if (!/^\d+$/.test(x) || !/^\d+$/.test(y)) { okBox($('e3bMsg'), bi('Enter two natural numbers.', '请填两个自然数。'), 'bad'); return; }
    if (+x - +y === -9) { okBox($('e3bMsg'), '✓ ' + bi(`(${x}, ${y}) represents −9. The rule gives (2·4 + 5·1, 2·1 + 5·4) = (13, 22), and indeed (−3)·3 = −9.`, `(${x}, ${y}) 代表 −9。按规则得 (2·4 + 5·1, 2·1 + 5·4) = (13, 22)，确实 (−3)·3 = −9。`)); if (!revealedB) { done.b = true; fin(); } }
    else okBox($('e3bMsg'), bi(`(${x}, ${y}) represents ${x - y}, not the product. Compute (ac + bd, ad + bc) with a=2, b=5, c=4, d=1.`, `(${x}, ${y}) 代表 ${x - y}，不是这个乘积。用 a=2, b=5, c=4, d=1 计算 (ac + bd, ad + bc)。`), 'bad');
  });
  $('e3bShow').addEventListener('click', () => { revealedB = true; $('e3bX').value = 13; $('e3bY').value = 22; okBox($('e3bMsg'), bi('(2·4 + 5·1, 2·1 + 5·4) = (13, 22), which represents −9 = (−3)·3. Any (x, y) with y = x + 9 is also correct.', '(2·4 + 5·1, 2·1 + 5·4) = (13, 22)，代表 −9 = (−3)·3。任何满足 y = x + 9 的 (x, y) 也都对。'), 'info'); });
})();

/* E4 */
(function e4() {
  const yes = { yes: 'Cut', yesz: '是分割', no: 'Not a cut', noz: '不是分割' };
  tfRows($('e4List'), [
    { s: '{q ∈ ℚ : q < 1/2}', ans: true, en: 'The cut of the rational 1/2.', zh: '这是有理数 1/2 对应的分割。' },
    { s: '{q ∈ ℚ : q ≤ 1/2}', ans: false, en: 'It has a greatest element, 1/2. Condition (iii) fails.', zh: '它有最大元 1/2，条件 (iii) 不成立。' },
    { s: '{q ∈ ℚ : q² < 2}', ans: false, en: 'Not downward closed: 0 is in it, but −5 < 0 and (−5)² = 25 > 2.', zh: '不向下封闭：0 属于它，而 −5 < 0 且 (−5)² = 25 > 2。' },
    { s: '{q ∈ ℚ : q < 0 ∨ q² < 3}', ans: true, en: 'This is √3: nonempty (0 is in it), not all of ℚ (2 is not), downward closed, and no maximum, because the inequality is strict: if q² < 3 (with q ≥ 0), a slightly larger rational still has square < 3, and every q < 0 is below 0.', zh: '这就是 √3：非空（含 0），不等于 ℚ（不含 2），向下封闭，并且没有最大元，因为不等式是严格的：若 q ≥ 0 且 q² < 3，稍大一点的有理数平方仍小于 3；而每个 q < 0 都小于 0。' },
    { s: '{q ∈ ℚ : q³ < 2}', ans: true, en: 'q ↦ q³ is strictly increasing on all of ℚ, so this is downward closed; it contains 1 but not 2; and since the inequality is strict, if q³ < 2 a slightly larger rational still has cube < 2, so there is no maximum. It is ∛2. (Irrationality of ∛2 is what makes the complement have no minimum, not what (iii) needs.)', zh: 'q ↦ q³ 在整个 ℚ 上严格递增，所以向下封闭；它含 1 而不含 2；又因不等式是严格的，若 q³ < 2，稍大一点的有理数立方仍小于 2，所以没有最大元。它就是 ∛2。（∛2 是无理数，保证的是补集没有最小元，而不是条件 (iii)。）' },
    { s: '∅', ans: false, en: 'A cut must be nonempty.', zh: '分割必须非空。' },
    { s: '{q ∈ ℚ : q < 0 ∨ q² ≤ 4}', ans: false, en: 'This is {q : q ≤ 2}, with greatest element 2.', zh: '这就是 {q : q ≤ 2}，有最大元 2。' },
    { s: '{q ∈ ℚ : ∃n ≥ 1, q < 1 − 1/n}', ans: true, en: 'It equals {q : q < 1}, the cut of 1. Each q < 1 is below some 1 − 1/n, and nothing ≥ 1 is.', zh: '它等于 {q : q < 1}，即 1 对应的分割。每个 q < 1 都小于某个 1 − 1/n，而 ≥ 1 的数都不满足。' },
  ].map(x => ({ ...x, ...yes })), () => { okBox($('e4Msg'), '✓ ' + bi('All eight right.', '八道全对。')); Progress.mark('L7E4'); }, $('e4Show'));
})();

/* E5 */
(function e5() {
  stepper($('e5Steps'), $('e5Next'), $('e5All'));
  let revealed = false;
  const c = choice($('e5Choice'), [
    { ok: false, en: '𝒞 is nonempty', zh: '𝒞 非空', fen: '✗ Nonemptiness of 𝒞 is what makes U ≠ ∅.', fzh: '✗ 𝒞 非空是用来保证 U ≠ ∅ 的。' },
    { ok: true, en: '𝒞 is bounded above by a cut B', zh: '𝒞 有上界分割 B', fen: '✓ Right. Without a bound, e.g. 𝒞 = {all cuts of integers n}, the union is all of ℚ, which is not a cut.', fzh: '✓ 对。没有上界的话，比如 𝒞 = {所有整数 n 对应的分割}，并集就是整个 ℚ，不是分割。' },
    { ok: false, en: 'each L ∈ 𝒞 is downward closed', zh: '每个 L ∈ 𝒞 都向下封闭', fen: '✗ That is used for (ii).', fzh: '✗ 那是用于证明 (ii) 的。' },
    { ok: false, en: '𝒞 is a chain under ⊆', zh: '𝒞 在 ⊆ 下是一条链', fen: '✗ Never assumed, and not needed. (Any two cuts are comparable anyway.)', fzh: '✗ 从未假设，也不需要。（反正任意两个分割都可以比较。）' },
  ], $('e5Msg'), () => { if (!revealed) Progress.mark('L7E5'); });
  $('e5Show').addEventListener('click', () => { revealed = true; c.reveal(); $('e5All').click(); });
})();

/* E6 */
(function e6() {
  const ids = ['e6a', 'e6b', 'e6a2', 'e6b2', 'e6c', 'e6d', 'e6c2', 'e6d2'];
  const init = [1, 0, 1, 0, 1, 0, 1, 0];
  let revealed = false;
  ids.forEach((id, i) => { $(id).value = init[i]; });
  const eq = (a, b, c, d) => a + d === b + c;
  $('e6Check').addEventListener('click', () => {
    const v = ids.map(id => $(id).value.trim());
    if (!v.every(s => /^\d+$/.test(s))) { okBox($('e6Msg'), bi('All eight entries must be natural numbers.', '八个格子都要填自然数。'), 'bad'); return; }
    const [a, b, a2, b2, c, d, c2, d2] = v.map(Number);
    if (!eq(a, b, a2, b2)) { okBox($('e6Msg'), bi(`(${a},${b}) ≁ (${a2},${b2}): they represent ${a - b} and ${a2 - b2}. Pick equivalent representatives.`, `(${a},${b}) ≁ (${a2},${b2})：它们分别代表 ${a - b} 和 ${a2 - b2}。请选等价的代表元。`), 'bad'); return; }
    if (!eq(c, d, c2, d2)) { okBox($('e6Msg'), bi(`(${c},${d}) ≁ (${c2},${d2}): they represent ${c - d} and ${c2 - d2}.`, `(${c},${d}) ≁ (${c2},${d2})：它们分别代表 ${c - d} 和 ${c2 - d2}。`), 'bad'); return; }
    const r1 = [a * c, b * d], r2 = [a2 * c2, b2 * d2];
    const line = `<span class="m">(${a},${b}) ⋆ (${c},${d}) = (${r1})  ↦ ${r1[0] - r1[1]} &nbsp; | &nbsp; (${a2},${b2}) ⋆ (${c2},${d2}) = (${r2}) ↦ ${r2[0] - r2[1]}</span><br>`;
    if (eq(r1[0], r1[1], r2[0], r2[1])) okBox($('e6Msg'), line + bi('Same class this time. Keep hunting: try changing one representative by adding 1 to both coordinates.', '这次落在同一个类里。继续找：试着把某个代表元的两个坐标同时加 1。'), 'warn');
    else { okBox($('e6Msg'), line + '✓ ' + bi('Same inputs (as integers), different outputs: ⋆ is <b>not well-defined</b>. The correct product [(ac + bd, ad + bc)] passes this test for all representatives.', '输入（作为整数）相同，输出却不同：⋆ <b>不是良定义的</b>。正确的乘法 [(ac + bd, ad + bc)] 对所有代表元都能通过这个检验。')); if (!revealed) Progress.mark('L7E6'); }
  });
  $('e6Show').addEventListener('click', () => {
    revealed = true;
    [1, 0, 2, 1, 1, 0, 1, 0].forEach((x, i) => { $(ids[i]).value = x; });
    okBox($('e6Msg'), bi('Example: (1,0) ~ (2,1) both represent 1, and (c,d) = (c′,d′) = (1,0). Then (1,0) ⋆ (1,0) = (1,0) ↦ 1, but (2,1) ⋆ (1,0) = (2,0) ↦ 2.', '例如 (1,0) ~ (2,1) 都代表 1，取 (c,d) = (c′,d′) = (1,0)。于是 (1,0) ⋆ (1,0) = (1,0) ↦ 1，而 (2,1) ⋆ (1,0) = (2,0) ↦ 2。'), 'info');
  });
})();
