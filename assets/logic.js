// Shared engine: language toggle, formula parsing, evaluation, and SVG/HTML renderers.

/* ================= language ================= */
const Lang = {
  init() {
    const mode = localStorage.getItem('lang') || 'both';
    this.set(mode);
    document.querySelectorAll('.lang-switch button').forEach(b =>
      b.addEventListener('click', () => this.set(b.dataset.lang)));
  },
  set(mode) {
    document.body.classList.remove('lang-en', 'lang-zh', 'lang-both');
    document.body.classList.add('lang-' + mode);
    localStorage.setItem('lang', mode);
    document.querySelectorAll('.lang-switch button').forEach(b =>
      b.classList.toggle('active', b.dataset.lang === mode));
  },
};
// block-level bilingual text
const bi = (en, zh) => `<span class="en">${en}</span><span class="zh">${zh}</span>`;
// inline bilingual text
const bil = (en, zh) => `<span class="il">${bi(en, zh)}</span>`;

/* ================= syntax ================= */
const SYM = { and: '∧', or: '∨', imp: '→', iff: '↔' };
const OPS = ['and', 'or', 'imp', 'iff'];

class ParseError extends Error {
  constructor(en, zh) { super(en); this.en = en; this.zh = zh; }
  html() { return bi(this.en, this.zh); }
}

function tokenize(s) {
  const out = [];
  let i = 0;
  while (i < s.length) {
    const c = s[i];
    if (/\s/.test(c)) { i++; continue; }
    const rest = s.slice(i);
    if (rest.startsWith('<->') || rest.startsWith('<=>')) { out.push({ t: 'iff', pos: i }); i += 3; continue; }
    if (rest.startsWith('->') || rest.startsWith('=>')) { out.push({ t: 'imp', pos: i }); i += 2; continue; }
    if (c === '↔') { out.push({ t: 'iff', pos: i }); i++; continue; }
    if (c === '→') { out.push({ t: 'imp', pos: i }); i++; continue; }
    if ('∧&^'.includes(c)) { out.push({ t: 'and', pos: i }); i++; continue; }
    if ('∨|'.includes(c)) { out.push({ t: 'or', pos: i }); i++; continue; }
    if ('¬~!'.includes(c)) { out.push({ t: 'not', pos: i }); i++; continue; }
    if (c === '(' || c === ')') { out.push({ t: c, pos: i }); i++; continue; }
    if (/[A-Za-zα-ω]/.test(c)) {
      let j = i + 1;
      while (j < s.length && /[0-9₀-₉']/.test(s[j])) j++;
      out.push({ t: 'atom', v: s.slice(i, j), pos: i });
      i = j;
      continue;
    }
    throw new ParseError(`Unknown symbol “${c}” at position ${i + 1}`, `第 ${i + 1} 个位置出现了无法识别的符号“${c}”`);
  }
  return out;
}

// Friendly parser: standard precedence ¬ > ∧ > ∨ > → > ↔, → is right-associative, outer parentheses optional.
function parse(s) {
  const toks = tokenize(s);
  if (!toks.length) throw new ParseError('Empty input', '输入为空');
  let i = 0;
  const peek = () => toks[i];
  const fail = (en, zh) => { throw new ParseError(en, zh); };
  function pIff() {
    let a = pImp();
    while (peek() && peek().t === 'iff') { i++; a = { type: 'bin', op: 'iff', a, b: pImp() }; }
    return a;
  }
  function pImp() {
    const a = pOr();
    if (peek() && peek().t === 'imp') { i++; return { type: 'bin', op: 'imp', a, b: pImp() }; }
    return a;
  }
  function pOr() {
    let a = pAnd();
    while (peek() && peek().t === 'or') { i++; a = { type: 'bin', op: 'or', a, b: pAnd() }; }
    return a;
  }
  function pAnd() {
    let a = pNot();
    while (peek() && peek().t === 'and') { i++; a = { type: 'bin', op: 'and', a, b: pNot() }; }
    return a;
  }
  function pNot() {
    if (peek() && peek().t === 'not') { i++; return { type: 'not', a: pNot() }; }
    return pAtom();
  }
  function pAtom() {
    const tk = peek();
    if (!tk) fail('Formula ends too early', '公式不完整，结尾缺少内容');
    if (tk.t === 'atom') { i++; return { type: 'atom', name: tk.v }; }
    if (tk.t === '(') {
      i++;
      const a = pIff();
      if (!peek() || peek().t !== ')') fail('Missing “)”', '缺少右括号“)”');
      i++;
      return a;
    }
    fail(`Unexpected “${tk.t === ')' ? ')' : SYM[tk.t] || '¬'}”`, `此处不应出现“${tk.t === ')' ? ')' : SYM[tk.t] || '¬'}”`);
  }
  const r = pIff();
  if (i < toks.length) fail('Extra symbols after the formula', '公式后面多出了符号');
  return r;
}

// Strict parser: exactly the official inductive definition (every binary connective wrapped in parentheses).
function strictParse(s) {
  const toks = tokenize(s);
  if (!toks.length) throw new ParseError('Empty string is not a formula', '空串不是公式');
  let i = 0;
  const peek = () => toks[i];
  function F() {
    const tk = peek();
    if (!tk) throw new ParseError('String ends where a formula was expected', '此处需要一个公式，但字符串已经结束');
    if (tk.t === 'atom') { i++; return { type: 'atom', name: tk.v }; }
    if (tk.t === 'not') { i++; return { type: 'not', a: F() }; }
    if (tk.t === '(') {
      i++;
      const a = F();
      const op = peek();
      if (!op || !OPS.includes(op.t)) throw new ParseError('After “(φ” the rules demand a binary connective', '规则要求“(φ”之后紧跟一个二元联结词');
      i++;
      const b = F();
      if (!peek() || peek().t !== ')') throw new ParseError('Missing “)” — rule 3 always closes the parenthesis', '缺少“)”——规则 3 生成的公式一定带右括号');
      i++;
      return { type: 'bin', op: op.t, a, b };
    }
    throw new ParseError('No rule produces a formula starting here', '没有任何规则能生成从这里开始的公式');
  }
  const r = F();
  if (i < toks.length) throw new ParseError('Extra symbols left over — no rule produces them', '有多余符号，任何规则都生成不了');
  return r;
}

// Fully parenthesised official form.
function show(n, outer = true) {
  if (n.type === 'atom') return n.name;
  if (n.type === 'not') return '¬' + show(n.a, true);
  return '(' + show(n.a, true) + ' ' + SYM[n.op] + ' ' + show(n.b, true) + ')';
}
// Official form without spaces (for symbol counting).
function tight(n) {
  if (n.type === 'atom') return n.name;
  if (n.type === 'not') return '¬' + tight(n.a);
  return '(' + tight(n.a) + SYM[n.op] + tight(n.b) + ')';
}
// Readable form: drop outermost parentheses only.
function pretty(n) {
  const s = show(n);
  return n.type === 'bin' ? s.slice(1, -1) : s;
}

function atomsOf(n, acc = new Set()) {
  if (n.type === 'atom') acc.add(n.name);
  else if (n.type === 'not') atomsOf(n.a, acc);
  else { atomsOf(n.a, acc); atomsOf(n.b, acc); }
  return acc;
}
function sortAtoms(set) {
  return [...set].sort((x, y) => x.localeCompare(y, 'en', { numeric: true }));
}
function opsOf(n, acc = new Set()) {
  if (n.type === 'not') { acc.add('not'); opsOf(n.a, acc); }
  else if (n.type === 'bin') { acc.add(n.op); opsOf(n.a, acc); opsOf(n.b, acc); }
  return acc;
}
function evalF(n, v) {
  switch (n.type) {
    case 'atom': return v[n.name] ? 1 : 0;
    case 'not': return 1 - evalF(n.a, v);
    default: {
      const a = evalF(n.a, v), b = evalF(n.b, v);
      if (n.op === 'and') return a & b;
      if (n.op === 'or') return a | b;
      if (n.op === 'imp') return (!a || b) ? 1 : 0;
      return a === b ? 1 : 0;
    }
  }
}
// Distinct subformulas in post-order (children before parents).
function subformulas(n, acc = [], seen = new Set()) {
  if (n.type === 'not') subformulas(n.a, acc, seen);
  if (n.type === 'bin') { subformulas(n.a, acc, seen); subformulas(n.b, acc, seen); }
  const k = show(n);
  if (!seen.has(k)) { seen.add(k); acc.push(n); }
  return acc;
}
function allValuations(atoms) {
  const rows = [];
  const n = atoms.length;
  for (let m = 0; m < (1 << n); m++) {
    const v = {};
    atoms.forEach((a, k) => { v[a] = (m >> (n - 1 - k)) & 1; });
    rows.push(v);
  }
  return rows;
}
function classify(n) {
  const atoms = sortAtoms(atomsOf(n));
  const vals = allValuations(atoms).map(v => evalF(n, v));
  const ones = vals.filter(x => x).length;
  return { atoms, vals, kind: ones === vals.length ? 'taut' : ones === 0 ? 'unsat' : 'cont' };
}
const KIND_HTML = {
  taut: `<span class="badge-big taut">${bi('Tautology', '重言式（永真）')}</span>`,
  cont: `<span class="badge-big cont">${bi('Contingent: satisfiable, not a tautology', '可满足式（非永真）')}</span>`,
  unsat: `<span class="badge-big unsat">${bi('Unsatisfiable (contradiction)', '矛盾式（永假，不可满足）')}</span>`,
};

// Random formula generator over given atoms, max depth d.
function randomFormula(atoms, d, ops = ['not', ...OPS]) {
  if (d === 0 || Math.random() < 0.2) return { type: 'atom', name: atoms[Math.floor(Math.random() * atoms.length)] };
  const op = ops[Math.floor(Math.random() * ops.length)];
  if (op === 'not') return { type: 'not', a: randomFormula(atoms, d - 1, ops) };
  return { type: 'bin', op, a: randomFormula(atoms, d - 1, ops), b: randomFormula(atoms, d - 1, ops) };
}

/* ================= SVG helpers ================= */
const NS = 'http://www.w3.org/2000/svg';
function el(tag, attrs = {}, parent) {
  const e = document.createElementNS(NS, tag);
  for (const k in attrs) e.setAttribute(k, attrs[k]);
  if (parent) parent.appendChild(e);
  return e;
}
const sleep = ms => new Promise(r => setTimeout(r, ms));

/* ================= parse tree ================= */
// Renders an animated parse tree. Returns a controller with evaluate(valuation).
function TreeView(container, ast, opts = {}) {
  container.innerHTML = '';
  const GX = opts.gx || 64, GY = opts.gy || 70, R = 21;
  let leaf = 0, maxDepth = 0;
  const nodes = [];
  function walk(n, depth) {
    maxDepth = Math.max(maxDepth, depth);
    const node = { ast: n, depth, children: [] };
    nodes.push(node);
    if (n.type === 'atom') { node.x = leaf++; node.label = n.name; }
    else if (n.type === 'not') { node.children = [walk(n.a, depth + 1)]; node.x = node.children[0].x; node.label = '¬'; }
    else {
      node.children = [walk(n.a, depth + 1), walk(n.b, depth + 1)];
      node.x = (node.children[0].x + node.children[1].x) / 2;
      node.label = SYM[n.op];
    }
    return node;
  }
  const root = walk(ast, 0);
  // Push a lone ¬ chain sideways a bit so stacked nodes stay readable.
  const W = Math.max(leaf * GX + 40, 160), H = (maxDepth + 1) * GY + 30;
  const svg = el('svg', { viewBox: `0 0 ${W} ${H}`, width: W, height: H }, container);
  const px = n => 20 + GX / 2 + n.x * GX + (W - 40 - leaf * GX) / 2;
  const py = n => 34 + n.depth * GY;
  const gE = el('g', {}, svg), gN = el('g', {}, svg);
  nodes.forEach(n => {
    n.edges = n.children.map(c => {
      const ln = el('line', { x1: px(n), y1: py(n), x2: px(c), y2: py(c), class: 'tedge' }, gE);
      ln.classList.add('fadein');
      ln.style.animationDelay = (c.depth * 0.18) + 's';
      c.upEdge = ln;
      return ln;
    });
  });
  nodes.forEach(n => {
    const g = el('g', { class: 'tnode' + (n.ast.type === 'atom' ? ' atom' : ''), transform: `translate(${px(n)},${py(n)})` }, gN);
    const inner = el('g', { class: 'pop' }, g);
    inner.style.animationDelay = (n.depth * 0.18) + 's';
    el('circle', { r: R }, inner);
    const t = el('text', { class: 'lab' }, inner);
    t.textContent = n.label;
    const title = el('title', {}, g);
    title.textContent = pretty(n.ast);
    const bd = el('g', { class: 'badge', transform: `translate(${R - 2},${-R + 2})` }, inner);
    el('circle', { r: 10 }, bd);
    n.badgeText = el('text', {}, bd);
    n.g = g;
    if (opts.onHover) {
      g.style.cursor = 'pointer';
      g.addEventListener('mouseenter', () => opts.onHover(n.ast));
      g.addEventListener('mouseleave', () => opts.onHover(null));
    }
  });
  if (opts.markMain && ast.type !== 'atom') root.g.classList.add('main');

  let token = 0;
  async function evaluate(v, speed = 380) {
    const my = ++token;
    nodes.forEach(n => { n.g.classList.remove('v0', 'v1', 'active'); n.upEdge && n.upEdge.classList.remove('lit0', 'lit1'); });
    const order = [];
    (function post(n) { n.children.forEach(post); order.push(n); })(root);
    for (const n of order) {
      if (my !== token) return;
      const val = evalF(n.ast, v);
      n.g.classList.add('active', 'v' + val);
      n.badgeText.textContent = val;
      if (n.upEdge) n.upEdge.classList.add('lit' + val);
      if (speed) await sleep(speed);
      n.g.classList.remove('active');
    }
    return evalF(ast, v);
  }
  function clear() {
    token++;
    nodes.forEach(n => { n.g.classList.remove('v0', 'v1', 'active'); n.upEdge && n.upEdge.classList.remove('lit0', 'lit1'); });
  }
  return { evaluate, clear, root, nodes, svg };
}

/* ================= switches ================= */
function Switches(container, atoms, v, onChange) {
  container.innerHTML = '';
  atoms.forEach(a => {
    if (!(a in v)) v[a] = 1;
    const sw = document.createElement('div');
    sw.className = 'sw' + (v[a] ? ' on' : '');
    sw.innerHTML = `<span>${a}</span><span class="track"><span class="knob"></span></span><span class="val">${v[a]}</span>`;
    sw.addEventListener('click', () => {
      v[a] = 1 - v[a];
      sw.classList.toggle('on', !!v[a]);
      sw.querySelector('.val').textContent = v[a];
      onChange && onChange(v);
    });
    container.appendChild(sw);
  });
}

/* ================= truth table ================= */
function TruthTable(container, ast, opts = {}) {
  const atoms = sortAtoms(atomsOf(ast));
  if (atoms.length > 5) {
    container.innerHTML = `<div class="msg warn">${bi('Too many atoms for a table (max 5).', '原子命题太多（最多 5 个），真值表放不下。')}</div>`;
    return;
  }
  const subs = opts.subs === false ? [ast] : subformulas(ast).filter(s => s.type !== 'atom');
  const rows = allValuations(atoms);
  let h = '<table class="tt"><thead><tr>';
  atoms.forEach(a => h += `<th>${a}</th>`);
  subs.forEach((s, k) => h += `<th class="${k === 0 ? 'sep' : ''}">${pretty(s)}</th>`);
  h += '</tr></thead><tbody>';
  rows.forEach((v, r) => {
    h += `<tr class="row-in" style="animation-delay:${r * (opts.delay ?? 0.07)}s">`;
    atoms.forEach(a => h += `<td class="c${v[a]}">${v[a]}</td>`);
    subs.forEach((s, k) => {
      const val = evalF(s, v);
      const fin = k === subs.length - 1;
      h += `<td class="c${val}${k === 0 ? ' sep' : ''}${fin ? ' final' : ''}">${val}</td>`;
    });
    h += '</tr>';
  });
  h += '</tbody></table>';
  container.innerHTML = h;
}

/* ================= valuation space / consequence ================= */
// premises: array of ASTs; concl: AST. Renders tiles = valuations.
function ConsequenceView(container, premises, concl, opts = {}) {
  const set = new Set();
  premises.forEach(p => atomsOf(p, set));
  atomsOf(concl, set);
  const atoms = sortAtoms(set);
  if (atoms.length > 5) {
    container.innerHTML = `<div class="msg warn">${bi('Max 5 atoms here.', '这里最多支持 5 个原子命题。')}</div>`;
    return null;
  }
  const rows = allValuations(atoms);
  const cols = atoms.length <= 2 ? rows.length : atoms.length === 3 ? 4 : atoms.length === 4 ? 4 : 8;
  let inG = 0, counter = 0;
  const tiles = rows.map(v => {
    const g = premises.every(p => evalF(p, v));
    const f = evalF(concl, v);
    if (g) inG++;
    if (g && !f) counter++;
    return { v, g, f };
  });
  const tileW = opts.small ? 62 : 86;
  let h = `<div class="vgrid" style="grid-template-columns:repeat(${cols}, ${tileW}px)">`;
  tiles.forEach((t, k) => {
    const cls = ['tile', 'hidden'];
    if (t.f) cls.push('phi');
    if (t.g) cls.push('gamma');
    if (t.g && !t.f) cls.push('counter');
    const bits = atoms.map(a => `${a}=${t.v[a]}`).join(' ');
    h += `<div class="${cls.join(' ')}" data-k="${k}" title="${atoms.map(a => a + '=' + t.v[a]).join(', ')}">
            <div class="bits">${bits}</div><div class="mark">${t.f ? '✓' : '✗'}</div></div>`;
  });
  h += '</div>';
  if (!opts.noLegend) {
    h += `<div class="legend">
      <span><i style="border:3px solid var(--accent)"></i>${bil('blue frame = all premises true', '蓝框＝前提全真')}</span>
      <span><i style="background:var(--true-soft)"></i>${bil('green ✓ = conclusion true', '绿色 ✓＝结论为真')}</span>
      <span><i style="background:var(--false-soft);border:2px solid var(--false)"></i>${bil('red = counterexample', '红色＝反例')}</span></div>`;
  }
  container.innerHTML = h;
  container.querySelectorAll('.tile').forEach((t, k) => setTimeout(() => t.classList.remove('hidden'), 40 + k * (opts.small ? 25 : 55)));
  return { atoms, inG, counter, total: rows.length, holds: counter === 0, tiles };
}

/* ================= progress ================= */
const Progress = {
  key: 'logic-progress',
  get() { try { return JSON.parse(localStorage.getItem(this.key)) || {}; } catch { return {}; } },
  mark(id) {
    const p = this.get(); p[id] = true;
    localStorage.setItem(this.key, JSON.stringify(p));
    this.paint();
  },
  paint() {
    const p = this.get();
    document.querySelectorAll('[data-prog]').forEach(e => e.classList.toggle('done', !!p[e.dataset.prog]));
  },
};

// Insert-symbol keyboard for formula inputs.
function attachKeys(container, input) {
  ['¬', '∧', '∨', '→', '↔', '(', ')', 'p', 'q', 'r'].forEach(s => {
    const b = document.createElement('button');
    b.type = 'button';
    b.textContent = s;
    b.addEventListener('click', () => {
      const st = input.selectionStart ?? input.value.length, en = input.selectionEnd ?? input.value.length;
      input.value = input.value.slice(0, st) + s + input.value.slice(en);
      input.focus();
      input.setSelectionRange(st + s.length, st + s.length);
      input.dispatchEvent(new Event('input'));
    });
    container.appendChild(b);
  });
}
