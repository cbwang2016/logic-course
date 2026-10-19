// Lesson 4 interactions: first-order proofs and Gödel's completeness theorem.
Lang.init();
Progress.paint();

const $ = id => document.getElementById(id);
const errBox = (box, e) => { box.className = 'msg bad'; box.innerHTML = e instanceof ParseError ? e.html() : String(e); };
const okBox = (box, html, kind = 'ok') => { box.className = 'msg ' + kind; box.innerHTML = html; };
const clearBox = box => { box.className = 'msg'; box.innerHTML = ''; };
const SUB = '₀₁₂₃₄₅₆₇₈₉';
const sub = n => String(n).split('').map(d => SUB[d]).join('');
const pick = a => a[Math.floor(Math.random() * a.length)];
const shuffle = a => { const b = [...a]; for (let i = b.length - 1; i > 0; i--) { const j = Math.floor(Math.random() * (i + 1)); [b[i], b[j]] = [b[j], b[i]]; } return b; };

// Re-run layout-dependent drawings when the language (and so the text height) changes.
const redrawers = [];
document.querySelectorAll('.lang-switch button').forEach(b => b.addEventListener('click', () => setTimeout(() => redrawers.forEach(f => f()), 40)));
window.addEventListener('resize', () => redrawers.forEach(f => f()));

// Bilingual SVG text: English line at y, Chinese line at y + gap (the CSS language switch hides one of them).
function svgBi(parent, x, y, en, zh, attrs = {}, gap = 16) {
  const size = attrs.size || 13;
  const common = { x, 'text-anchor': attrs.anchor || 'middle', fill: attrs.fill || '#1f2430', 'font-weight': attrs.weight || 400 };
  const a = el('text', { ...common, y, class: 'en' }, parent);
  a.style.fontSize = size + 'px';
  a.textContent = en;
  const b = el('text', { ...common, y: y + gap, class: 'zh' }, parent);
  b.style.fontSize = (size - 1) + 'px';
  b.style.fontFamily = 'var(--sans)';
  b.textContent = zh;
  return [a, b];
}
function svgText(parent, x, y, s, attrs = {}) {
  const t = el('text', { x, y, 'text-anchor': 'middle', 'font-size': 13, fill: '#1f2430', ...attrs }, parent);
  t.textContent = s;
  return t;
}
let markerUid = 0;
function marker(svg, color) {
  const id = 'mk' + (markerUid++);
  let defs = svg.querySelector('defs');
  if (!defs) defs = el('defs', {}, svg);
  const m = el('marker', { id, viewBox: '0 0 10 10', refX: 9, refY: 5, markerWidth: 7, markerHeight: 7, orient: 'auto-start-reverse' }, defs);
  el('path', { d: 'M0,0 L10,5 L0,10 z', fill: color }, m);
  return `url(#${id})`;
}

/* =====================================================================
   First-order engine: parse, print (with binding info), substitute, evaluate
   ===================================================================== */
const VAR_RE = /^[uvwxyz][0-9₀-₉']*$/;
const ARITY = { P: 1, Q: 1, R: 2, S: 2, f: 1, h: 1, g: 2 };
const CONSTS = ['a', 'b', 'c', 'd', 'e', '0', '1'];

function foTokenize(s) {
  const out = [];
  let i = 0;
  const single = { '↔': 'iff', '→': 'imp', '∧': 'and', '&': 'and', '∨': 'or', '|': 'or', '¬': 'not', '~': 'not', '!': 'not',
    '(': '(', ')': ')', ',': ',', '=': 'eq', '≠': 'neq', '∀': 'all', '∃': 'ex', '⊥': 'bot' };
  while (i < s.length) {
    const c = s[i];
    if (/\s/.test(c)) { i++; continue; }
    const rest = s.slice(i);
    if (rest.startsWith('<->')) { out.push({ t: 'iff' }); i += 3; continue; }
    if (rest.startsWith('->')) { out.push({ t: 'imp' }); i += 2; continue; }
    if (rest.startsWith('!=')) { out.push({ t: 'neq' }); i += 2; continue; }
    if (single[c]) { out.push({ t: single[c] }); i++; continue; }
    if (/[A-Za-z0-9]/.test(c)) {
      let j = i + 1;
      while (j < s.length && /[0-9₀-₉']/.test(s[j]) && !/[0-9]/.test(c)) j++;
      out.push({ t: 'id', v: s.slice(i, j) });
      i = j;
      continue;
    }
    throw new ParseError(`Unknown symbol “${c}”`, `无法识别的符号“${c}”`);
  }
  return out;
}

function foParse(s) {
  const tk = foTokenize(s);
  if (!tk.length) throw new ParseError('Empty input', '输入为空');
  let i = 0;
  const peek = () => tk[i];
  const fail = (en, zh) => { throw new ParseError(en, zh); };
  const expect = t => { if (!peek() || peek().t !== t) fail(`Expected “${t}”`, `此处应为“${t}”`); i++; };
  function term() {
    const k = peek();
    if (!k || k.t !== 'id') fail('Expected a term here', '此处应为一个项');
    if (/^[A-Z]/.test(k.v)) fail(`“${k.v}” is a predicate symbol, not a term`, `“${k.v}”是谓词符号，不是项`);
    i++;
    if (peek() && peek().t === '(') {
      i++;
      const args = [term()];
      while (peek() && peek().t === ',') { i++; args.push(term()); }
      expect(')');
      return { t: 'fn', f: k.v, args };
    }
    if (VAR_RE.test(k.v)) return { t: 'var', n: k.v };
    return { t: 'const', n: k.v };
  }
  function atom() {
    const k = peek();
    if (!k) fail('Formula ends too early', '公式不完整，结尾缺少内容');
    if (k.t === 'bot') { i++; return { type: 'bot' }; }
    if (k.t === 'id' && /^[A-Z]/.test(k.v)) {
      i++;
      const args = [];
      if (peek() && peek().t === '(') {
        i++;
        args.push(term());
        while (peek() && peek().t === ',') { i++; args.push(term()); }
        expect(')');
      }
      return { type: 'pred', p: k.v, args };
    }
    const a = term();
    const op = peek();
    if (!op || (op.t !== 'eq' && op.t !== 'neq')) fail('After a term, expected “=” or “≠”', '项后面应为“=”或“≠”');
    i++;
    const e = { type: 'eq', a, b: term() };
    return op.t === 'eq' ? e : { type: 'not', a: e };
  }
  function un() {
    const k = peek();
    if (k && k.t === 'not') { i++; return { type: 'not', a: un() }; }
    if (k && (k.t === 'all' || k.t === 'ex')) {
      i++;
      const v = peek();
      if (!v || v.t !== 'id' || !VAR_RE.test(v.v)) fail('A quantifier must be followed by a variable (u, v, w, x, y, z)', '量词后面必须紧跟一个变元（u, v, w, x, y, z）');
      i++;
      return { type: 'q', q: k.t, v: v.v, a: un() };
    }
    if (k && k.t === '(') { i++; const a = iff(); expect(')'); return a; }
    return atom();
  }
  function and() { let a = un(); while (peek() && peek().t === 'and') { i++; a = { type: 'bin', op: 'and', a, b: un() }; } return a; }
  function or() { let a = and(); while (peek() && peek().t === 'or') { i++; a = { type: 'bin', op: 'or', a, b: and() }; } return a; }
  function imp() { const a = or(); if (peek() && peek().t === 'imp') { i++; return { type: 'bin', op: 'imp', a, b: imp() }; } return a; }
  function iff() { let a = imp(); while (peek() && peek().t === 'iff') { i++; a = { type: 'bin', op: 'iff', a, b: imp() }; } return a; }
  const r = iff();
  if (i < tk.length) fail('Extra symbols after the formula', '公式后面多出了符号');
  return r;
}
function foParseTerm(s) {
  const f = foParse(s + ' = ' + s);
  return f.a;
}

// Check symbols against the fixed signature used by the random-structure tester.
function sigCheck(n) {
  const bad = (en, zh) => { throw new ParseError(en, zh); };
  function T(t) {
    if (t.t === 'const' && !CONSTS.includes(t.n)) bad(`Unknown constant “${t.n}” (use a, b, c, d, e, 0, 1)`, `未知常元“${t.n}”（可用 a, b, c, d, e, 0, 1）`);
    if (t.t === 'fn') {
      if (!(t.f in ARITY) || /[A-Z]/.test(t.f)) bad(`Unknown function symbol “${t.f}” (use f, h unary; g binary)`, `未知函数符号“${t.f}”（一元用 f, h；二元用 g）`);
      if (ARITY[t.f] !== t.args.length) bad(`“${t.f}” takes ${ARITY[t.f]} argument(s)`, `“${t.f}”是 ${ARITY[t.f]} 元函数`);
      t.args.forEach(T);
    }
  }
  (function F(n) {
    if (n.type === 'pred') {
      if (!(n.p in ARITY)) bad(`Unknown predicate “${n.p}” (use P, Q unary; R, S binary)`, `未知谓词“${n.p}”（一元用 P, Q；二元用 R, S）`);
      if (ARITY[n.p] !== n.args.length) bad(`“${n.p}” takes ${ARITY[n.p]} argument(s)`, `“${n.p}”是 ${ARITY[n.p]} 元谓词`);
      n.args.forEach(T);
    } else if (n.type === 'eq') { T(n.a); T(n.b); }
    else if (n.type === 'not' || n.type === 'q') F(n.a);
    else if (n.type === 'bin') { F(n.a); F(n.b); }
  })(n);
}

const PREC = { iff: 1, imp: 2, or: 3, and: 4 };
// Print a formula as a token list. Each variable token knows its binder (or null = free).
function foEmit(root) {
  const out = [], stack = [], qs = [];
  let qid = 0;
  const push = (s, k, extra = {}) => out.push({ s, k, ...extra });
  function term(t) {
    const sb = !!t.sub;
    if (t.t === 'var') {
      const b = [...stack].reverse().find(q => q.v === t.n);
      push(t.n, 'var', { n: t.n, binder: b ? b.id : null, sub: sb });
    } else if (t.t === 'const') push(t.n, 'const', { sub: sb });
    else {
      push(t.f, 'fn', { sub: sb });
      push('(', 'p', { sub: sb });
      t.args.forEach((a, i) => { if (i) push(',', 'p', { sub: sb }); term(a); });
      push(')', 'p', { sub: sb });
    }
  }
  const prec = n => n.type === 'bin' ? PREC[n.op] : ((n.type === 'not' && n.a.type !== 'eq') || n.type === 'q') ? 5 : 6;
  function f(n, ctx) {
    const wrap = prec(n) < ctx;
    if (wrap) push('(', 'p');
    switch (n.type) {
      case 'bot': push('⊥', 'op'); break;
      case 'pred':
        push(n.p, 'pred');
        if (n.args.length) { push('(', 'p'); n.args.forEach((a, i) => { if (i) push(',', 'p'); term(a); }); push(')', 'p'); }
        break;
      case 'eq': term(n.a); push(' = ', 'op'); term(n.b); break;
      case 'not':
        if (n.a.type === 'eq') { term(n.a.a); push(' ≠ ', 'op'); term(n.a.b); }
        else { push('¬', 'op'); f(n.a, n.a.type === 'not' && n.a.a.type === 'eq' ? 7 : 5); }
        break;
      case 'q': {
        const q = { id: qid++, v: n.v, q: n.q, start: out.length, depth: stack.length };
        qs.push(q);
        push((n.q === 'all' ? '∀' : '∃') + n.v, 'q', { qid: q.id });
        stack.push(q);
        f(n.a, n.a.type === 'eq' || (n.a.type === 'not' && n.a.a.type === 'eq') ? 7 : 5);
        stack.pop();
        q.end = out.length - 1;
        break;
      }
      case 'bin': {
        const p = PREC[n.op];
        if (n.op === 'imp') { f(n.a, p + 1); push(' → ', 'op'); f(n.b, p); }
        else { f(n.a, p); push(' ' + SYM[n.op] + ' ', 'op'); f(n.b, p + 1); }
        break;
      }
    }
    if (wrap) push(')', 'p');
  }
  f(root, 0);
  return { toks: out, qs };
}
const foShow = n => foEmit(n).toks.map(t => t.s).join('');
const fo = s => foShow(foParse(s)); // normalise a formula string

function termVars(t, acc = new Set()) {
  if (t.t === 'var') acc.add(t.n);
  else if (t.t === 'fn') t.args.forEach(a => termVars(a, acc));
  return acc;
}
function freeVars(n, acc = new Set(), bound = new Set()) {
  const T = t => termVars(t).forEach(v => { if (!bound.has(v)) acc.add(v); });
  if (n.type === 'pred') n.args.forEach(T);
  else if (n.type === 'eq') { T(n.a); T(n.b); }
  else if (n.type === 'not') freeVars(n.a, acc, bound);
  else if (n.type === 'bin') { freeVars(n.a, acc, bound); freeVars(n.b, acc, bound); }
  else if (n.type === 'q') freeVars(n.a, acc, new Set([...bound, n.v]));
  return acc;
}
// Quantifiers that would capture a variable of t when t replaces the free occurrences of x.
function captures(n, x, t) {
  const tv = termVars(t), acc = new Set();
  (function go(n, stack) {
    const hit = ts => ts.some(s => termVars(s).has(x));
    if ((n.type === 'pred' && hit(n.args)) || (n.type === 'eq' && hit([n.a, n.b]))) {
      if (!stack.some(q => q.v === x)) stack.filter(q => tv.has(q.v)).forEach(q => acc.add(q.q + q.v));
    } else if (n.type === 'not') go(n.a, stack);
    else if (n.type === 'bin') { go(n.a, stack); go(n.b, stack); }
    else if (n.type === 'q') go(n.a, [...stack, { v: n.v, q: n.q === 'all' ? '∀' : '∃' }]);
  })(n, []);
  return [...acc];
}
const substitutable = (n, x, t) => captures(n, x, t).length === 0;
function markSub(t) {
  if (t.t === 'fn') return { ...t, sub: true, args: t.args.map(markSub) };
  return { ...t, sub: true };
}
function substT(s, x, t) {
  if (s.t === 'var') return s.n === x ? t : s;
  if (s.t === 'fn') return { ...s, args: s.args.map(a => substT(a, x, t)) };
  return s;
}
function substF(n, x, t) {
  switch (n.type) {
    case 'pred': return { ...n, args: n.args.map(a => substT(a, x, t)) };
    case 'eq': return { type: 'eq', a: substT(n.a, x, t), b: substT(n.b, x, t) };
    case 'not': return { type: 'not', a: substF(n.a, x, t) };
    case 'bin': return { ...n, a: substF(n.a, x, t), b: substF(n.b, x, t) };
    case 'q': return n.v === x ? n : { ...n, a: substF(n.a, x, t) };
    default: return n;
  }
}

/* ---------- semantics over small finite structures ---------- */
// M = { n, P:[bool], Q:[bool], R:[[bool]], S:[[bool]], f:[int], h:[int], g:[[int]], k:{c: int, ...} }
function evalTerm(t, M, s) {
  if (t.t === 'var') { if (!(t.n in s)) throw new Error('unassigned ' + t.n); return s[t.n]; }
  if (t.t === 'const') return M.k[t.n];
  const a = t.args.map(x => evalTerm(x, M, s));
  return t.args.length === 1 ? M[t.f][a[0]] : M[t.f][a[0]][a[1]];
}
function sat(n, M, s = {}) {
  switch (n.type) {
    case 'bot': return false;
    case 'pred': {
      const a = n.args.map(x => evalTerm(x, M, s));
      return a.length === 1 ? !!M[n.p][a[0]] : !!M[n.p][a[0]][a[1]];
    }
    case 'eq': return evalTerm(n.a, M, s) === evalTerm(n.b, M, s);
    case 'not': return !sat(n.a, M, s);
    case 'bin': {
      const a = sat(n.a, M, s), b = sat(n.b, M, s);
      return n.op === 'and' ? a && b : n.op === 'or' ? a || b : n.op === 'imp' ? (!a || b) : a === b;
    }
    case 'q': {
      for (let d = 0; d < M.n; d++) {
        const v = sat(n.a, M, { ...s, [n.v]: d });
        if (n.q === 'all' && !v) return false;
        if (n.q === 'ex' && v) return true;
      }
      return n.q === 'all';
    }
  }
}
// All assignments of the free variables; returns a falsifying assignment or null.
function counterAssignment(n, M) {
  const fv = [...freeVars(n)];
  const total = Math.pow(M.n, fv.length);
  for (let m = 0; m < total; m++) {
    const s = {};
    let r = m;
    fv.forEach(v => { s[v] = r % M.n; r = Math.floor(r / M.n); });
    if (!sat(n, M, s)) return s;
  }
  return null;
}
function randStructure(n) {
  n = n || pick([1, 2, 2, 3, 3, 3]);
  const ri = () => Math.floor(Math.random() * n), rb = () => Math.random() < 0.5;
  const M = { n, P: [], Q: [], R: [], S: [], f: [], h: [], g: [], k: {} };
  for (let i = 0; i < n; i++) {
    M.P.push(rb()); M.Q.push(rb()); M.f.push(ri()); M.h.push(ri());
    M.R.push(Array.from({ length: n }, rb)); M.S.push(Array.from({ length: n }, rb)); M.g.push(Array.from({ length: n }, ri));
  }
  CONSTS.forEach(c => M.k[c] = ri());
  return M;
}
function emptyStructure(n) {
  const M = { n, P: [], Q: [], R: [], S: [], f: [], h: [], g: [], k: {} };
  for (let i = 0; i < n; i++) {
    M.P.push(false); M.Q.push(false); M.f.push(i); M.h.push(i);
    M.R.push(Array(n).fill(false)); M.S.push(Array(n).fill(false)); M.g.push(Array(n).fill(0));
  }
  CONSTS.forEach(c => M.k[c] = 0);
  return M;
}
// Which signature symbols occur in a formula (for drawing only what matters).
function symbolsOf(n, acc = new Set()) {
  const T = t => { if (t.t === 'const') acc.add(t.n); if (t.t === 'fn') { acc.add(t.f); t.args.forEach(T); } };
  if (n.type === 'pred') { acc.add(n.p); n.args.forEach(T); }
  else if (n.type === 'eq') { T(n.a); T(n.b); }
  else if (n.type === 'not' || n.type === 'q') symbolsOf(n.a, acc);
  else if (n.type === 'bin') { symbolsOf(n.a, acc); symbolsOf(n.b, acc); }
  return acc;
}
function describeStructure(M, syms, s = {}) {
  const parts = [`|M| = {${[...Array(M.n).keys()].join(', ')}}`];
  const set1 = a => '{' + a.map((b, i) => b ? i : null).filter(x => x !== null).join(', ') + '}';
  const set2 = A => '{' + A.flatMap((row, i) => row.map((b, j) => b ? `(${i},${j})` : null)).filter(Boolean).join(', ') + '}';
  ['P', 'Q'].forEach(p => syms.has(p) && parts.push(`${p} = ${set1(M[p])}`));
  ['R', 'S'].forEach(p => syms.has(p) && parts.push(`${p} = ${set2(M[p])}`));
  ['f', 'h'].forEach(f => syms.has(f) && parts.push(`${f} = [${M[f].map((v, i) => `${i}↦${v}`).join(', ')}]`));
  if (syms.has('g')) parts.push(`g = [${M.g.flatMap((r, i) => r.map((v, j) => `(${i},${j})↦${v}`)).join(', ')}]`);
  CONSTS.forEach(c => syms.has(c) && parts.push(`${c} = ${M.k[c]}`));
  const sa = Object.keys(s).map(v => `${v} ↦ ${s[v]}`);
  if (sa.length) parts.push('s: ' + sa.join(', '));
  return parts.join(' ; ');
}

/* ---------- drawing a small structure ---------- */
// Elements on a circle. P = gold fill, Q = thick green ring, R = blue arrows, f = purple dashed arrows,
// constants = purple labels below, assignment = blue tags above.
function StructView(svg, M, opts = {}) {
  svg.innerHTML = '';
  const W = opts.W || 300, H = opts.H || 220, show = opts.show || new Set(['P', 'Q', 'R']);
  svg.setAttribute('viewBox', `0 0 ${W} ${H}`);
  svg.setAttribute('width', W);
  svg.setAttribute('height', H);
  const cx = W / 2, cy = H / 2 + 4, rad = M.n === 1 ? 0 : Math.min(W, H) / 2 - 44, NR = 17;
  const pos = [...Array(M.n).keys()].map(i => {
    const a = -Math.PI / 2 + (M.n === 2 ? Math.PI / 2 : 0) + 2 * Math.PI * i / M.n;
    return [cx + rad * Math.cos(a), cy + rad * Math.sin(a)];
  });
  const mR = marker(svg, '#3b5bdb'), mF = marker(svg, '#ae3ec9');
  const edge = (i, j, color, mk, dash, bend) => {
    const [x1, y1] = pos[i], [x2, y2] = pos[j];
    if (i === j) {
      const dx = x1 - cx, dy = y1 - cy, L = Math.hypot(dx, dy) || 1;
      const ux = M.n === 1 ? 0 : dx / L, uy = M.n === 1 ? -1 : dy / L;
      const off = dash ? 0.5 : 0;
      const bx = x1 + ux * NR, by = y1 + uy * NR;
      const px = -uy, py = ux;
      const r = 26 + off * 14;
      el('path', { d: `M${bx + px * 7},${by + py * 7} C${bx + ux * r + px * 22},${by + uy * r + py * 22} ${bx + ux * r - px * 22},${by + uy * r - py * 22} ${bx - px * 7},${by - py * 7}`,
        fill: 'none', stroke: color, 'stroke-width': 2, 'marker-end': mk, 'stroke-dasharray': dash ? '5 4' : '' }, svg);
      return;
    }
    const dx = x2 - x1, dy = y2 - y1, L = Math.hypot(dx, dy);
    const ux = dx / L, uy = dy / L, nx = -uy, ny = ux;
    const sx = x1 + ux * NR, sy = y1 + uy * NR, ex = x2 - ux * (NR + 2), ey = y2 - uy * (NR + 2);
    const mx = (sx + ex) / 2 + nx * bend, my = (sy + ey) / 2 + ny * bend;
    el('path', { d: `M${sx},${sy} Q${mx},${my} ${ex},${ey}`, fill: 'none', stroke: color, 'stroke-width': 2, 'marker-end': mk, 'stroke-dasharray': dash ? '5 4' : '' }, svg);
  };
  ['R', 'S'].forEach((r, ri) => {
    if (!show.has(r)) return;
    for (let i = 0; i < M.n; i++) for (let j = 0; j < M.n; j++) if (M[r][i][j]) edge(i, j, ri ? '#0c8599' : '#3b5bdb', mR, false, 12);
  });
  ['f', 'h'].forEach(f => { if (show.has(f)) for (let i = 0; i < M.n; i++) edge(i, M[f][i], '#ae3ec9', mF, true, -16); });
  for (let i = 0; i < M.n; i++) {
    const [x, y] = pos[i];
    const g = el('g', { class: 'snode' }, svg);
    if (opts.onClick) { g.style.cursor = 'pointer'; g.addEventListener('click', () => opts.onClick(i)); }
    const hi = opts.highlight && opts.highlight.includes(i);
    el('circle', { cx: x, cy: y, r: NR, fill: show.has('P') && M.P[i] ? '#ffe8a3' : '#fff',
      stroke: show.has('Q') && M.Q[i] ? '#2f9e44' : hi ? '#e03131' : '#1f2430', 'stroke-width': show.has('Q') && M.Q[i] ? 5 : hi ? 3 : 1.6 }, g);
    svgText(g, x, y + 5, String(i), { 'font-size': 15, 'font-weight': 700 });
    const ks = CONSTS.filter(c => show.has(c) && M.k[c] === i);
    if (ks.length) svgText(svg, x, y + NR + 15, ks.join(','), { fill: '#ae3ec9', 'font-weight': 700 });
    const vs = Object.keys(opts.assign || {}).filter(v => opts.assign[v] === i);
    if (vs.length) {
      const tg = el('g', {}, svg);
      el('rect', { x: x - 7 - vs.length * 9, y: y - NR - 22, width: 14 + vs.length * 18, height: 18, rx: 6, fill: '#3b5bdb' }, tg);
      svgText(tg, x, y - NR - 9, vs.join(','), { fill: '#fff', 'font-weight': 700 });
    }
  }
  return pos;
}
function structLegend(syms) {
  const items = [];
  if (syms.has('P')) items.push(`<span><i style="background:#ffe8a3;border:1px solid #1f2430"></i>${bil('P (gold fill)', 'P（金色填充）')}</span>`);
  if (syms.has('Q')) items.push(`<span><i style="border:3px solid #2f9e44"></i>${bil('Q (green ring)', 'Q（绿色粗环）')}</span>`);
  if (syms.has('R')) items.push(`<span><i style="background:#3b5bdb;height:3px;vertical-align:4px"></i>${bil('R: arrow a → b means R(a,b)', 'R：箭头 a → b 表示 R(a,b)')}</span>`);
  if (syms.has('f')) items.push(`<span><i style="border-top:2px dashed #ae3ec9;height:0;vertical-align:4px"></i>${bil('f (dashed)', 'f（虚线）')}</span>`);
  return `<div class="legend">${items.join('')}</div>`;
}

/* ---------- symbol keypad for first-order inputs ---------- */
function foKeys(container, input) {
  container.innerHTML = '';
  ['∀', '∃', '¬', '∧', '∨', '→', '↔', '=', '≠', '(', ')', ','].forEach(s => {
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

/* ---------- proof display with dependency arrows ---------- */
// lines: [{ f, j (html), cites: [indices], depth }]
function ProofView(box, lines, opts = {}) {
  box.innerHTML = '';
  box.classList.add('proof');
  const svg = el('svg', { class: 'pgut' }, box);
  const mk = marker(svg, '#3b5bdb');
  const mkOld = marker(svg, '#b8c2e8');
  const rows = lines.map((L, i) => {
    const d = document.createElement('div');
    d.className = 'pline' + (L.depth ? ' inner' : '');
    d.style.marginLeft = (60 + (L.depth || 0) * 24) + 'px';
    d.innerHTML = `<span class="pn">${opts.numFrom0 ? i : i + 1}.</span><span class="pf m">${L.f}</span><span class="pj">${L.j}</span><span class="pb"></span>`;
    if (opts.onRow) { d.style.cursor = 'pointer'; d.addEventListener('click', () => opts.onRow(i, d)); }
    box.appendChild(d);
    return d;
  });
  let shown = opts.allShown ? lines.length : 0, focus = -1;
  function draw() {
    svg.querySelectorAll('path.arr').forEach(p => p.remove());
    svg.setAttribute('height', box.scrollHeight);
    svg.setAttribute('width', 62);
    const mid = r => r.offsetTop + r.offsetHeight / 2;
    for (let k = 0; k < shown; k++) {
      (lines[k].cites || []).forEach(c => {
        const y1 = mid(rows[c]), y2 = mid(rows[k]);
        const cur = k === focus;
        const bulge = Math.min(54, 14 + (k - c) * 7);
        el('path', { class: 'arr', d: `M58,${y1} C${58 - bulge},${y1} ${58 - bulge},${y2} 56,${y2}`, fill: 'none',
          stroke: cur ? '#3b5bdb' : '#b8c2e8', 'stroke-width': cur ? 2.4 : 1.4, 'marker-end': cur ? mk : mkOld }, svg);
      });
    }
  }
  function sync() {
    rows.forEach((r, i) => {
      r.classList.toggle('on', i < shown);
      r.classList.toggle('cur', i === focus);
      r.classList.toggle('cited', focus >= 0 && (lines[focus].cites || []).includes(i));
    });
    draw();
  }
  redrawers.push(draw);
  sync();
  return {
    rows,
    next() { if (shown < lines.length) { focus = shown; shown++; sync(); } return shown; },
    all() { shown = lines.length; focus = -1; sync(); },
    reset() { shown = 0; focus = -1; sync(); },
    focus(k) { focus = k; shown = Math.max(shown, k + 1); sync(); },
    get shown() { return shown; },
    badge(i, html, cls) { const b = rows[i].querySelector('.pb'); b.innerHTML = html; b.className = 'pb ' + (cls || ''); },
    redraw: draw,
  };
}

/* =====================================================================
   §1 Substitution and variable capture
   ===================================================================== */
const QCOL = ['#ae3ec9', '#3b5bdb', '#f08c00', '#0c8599', '#c2255c'];
function drawSubLab(svg, phi, x, t) {
  svg.innerHTML = '';
  const CW = 11.2, X0 = 118;
  const A = foEmit(phi);
  const res = substF(phi, x, markSub(t));
  const B = foEmit(res);
  const layout = toks => { let p = X0; return toks.map(tk => { const w = [...tk.s].length * CW; const r = { x: p, w, c: p + w / 2 }; p += w; return r; }); };
  const LA = layout(A.toks), LB = layout(B.toks);
  const endOf = L => L.length ? L[L.length - 1].x + L[L.length - 1].w : 0;
  const width = Math.max(720, Math.max(endOf(LA), endOf(LB)) + 30);
  const Y1 = 74, Y2 = 214, H = 280;
  svg.setAttribute('viewBox', `0 0 ${width} ${H}`);
  svg.setAttribute('width', width);
  svg.setAttribute('height', H);
  const mkCap = marker(svg, '#e03131');
  function row(E, L, Y, isB) {
    const g = el('g', {}, svg);
    let labelled = false;
    // scope brackets
    E.qs.forEach(q => {
      const col = QCOL[q.id % QCOL.length];
      const xs = L[q.start].x + 2, xe = L[q.end].x + L[q.end].w - 2, yb = Y + 12 + q.depth * 8;
      el('path', { d: `M${xs},${yb - 5} L${xs},${yb} L${xe},${yb} L${xe},${yb - 5}`, fill: 'none', stroke: col, 'stroke-width': 2, opacity: .75 }, g);
    });
    // token backgrounds
    E.toks.forEach((tk, i) => {
      const P = L[i];
      if (!isB && tk.k === 'var' && tk.n === x && tk.binder === null)
        el('rect', { x: P.x - 1, y: Y - 19, width: P.w + 2, height: 26, rx: 5, fill: '#ffe8a3', stroke: '#f08c00' }, g);
      if (isB && tk.sub) el('rect', { x: P.x - 0.5, y: Y - 19, width: P.w + 1, height: 26, fill: '#e7ecff' }, g);
      if (isB && tk.sub && tk.k === 'var' && tk.binder !== null)
        el('rect', { x: P.x - 1, y: Y - 19, width: P.w + 2, height: 26, rx: 5, fill: '#ffe3e3', stroke: '#e03131', 'stroke-width': 2, class: 'capflash' }, g);
    });
    // binding arcs
    E.toks.forEach((tk, i) => {
      if (tk.k !== 'var' || tk.binder === null) return;
      const q = E.qs[tk.binder], qt = L[q.start];
      const bx = qt.x + qt.w * 0.72, cx = L[i].c;
      const cap = isB && tk.sub;
      const hgt = 16 + Math.min(30, Math.abs(cx - bx) * 0.12);
      el('path', { d: `M${cx},${Y - 21} Q${(cx + bx) / 2},${Y - 21 - hgt * 2} ${bx},${Y - 23}`, fill: 'none',
        stroke: cap ? '#e03131' : QCOL[q.id % QCOL.length], 'stroke-width': cap ? 2.6 : 1.4, opacity: cap ? 1 : .6,
        'marker-end': cap ? mkCap : '' , 'stroke-dasharray': cap ? '' : '3 3' }, g);
      if (cap && !labelled) { labelled = true; svgText(g, cx, Y + 50, '↑ captured! · 被捕获！', { fill: '#e03131', 'font-weight': 700, 'font-size': 13 }); }
    });
    // tokens
    E.toks.forEach((tk, i) => {
      const P = L[i];
      const fill = tk.k === 'q' ? QCOL[tk.qid % QCOL.length] : tk.k === 'var' && tk.binder === null && !tk.sub ? (tk.n === x && !isB ? '#b35c00' : '#1f2430') : tk.k === 'op' ? '#555' : '#1f2430';
      svgText(g, P.c, Y, tk.s.trim(), { 'font-size': 18, fill, 'font-weight': tk.k === 'q' || (tk.k === 'var' && tk.n === x && tk.binder === null && !isB) ? 700 : 500 });
    });
    return g;
  }
  svgText(svg, 8, Y1, 'φ', { 'text-anchor': 'start', 'font-size': 18, 'font-weight': 700, fill: '#ae3ec9' });
  svgText(svg, 8, Y2, `φ[${foShowTerm(t)}/${x}]`, { 'text-anchor': 'start', 'font-size': 14, 'font-weight': 700, fill: '#ae3ec9' });
  row(A, LA, Y1, false);
  // connectors: k-th free x  ->  k-th substituted run
  const frees = A.toks.map((tk, i) => tk.k === 'var' && tk.n === x && tk.binder === null ? i : -1).filter(i => i >= 0);
  const runs = [];
  B.toks.forEach((tk, i) => { if (tk.sub && (i === 0 || !B.toks[i - 1].sub)) runs.push([i, i]); else if (tk.sub) runs[runs.length - 1][1] = i; });
  // a substituted term that is itself a single run may touch a neighbouring run (e.g. "x,x"): split by count
  frees.forEach((fi, k) => {
    const r = runs[k];
    if (!r) return;
    const x1 = LA[fi].c, x2 = (LB[r[0]].x + LB[r[1]].x + LB[r[1]].w) / 2;
    const ln = el('path', { d: `M${x1},${Y1 + 34} C${x1},${Y1 + 80} ${x2},${Y2 - 110} ${x2},${Y2 - 64}`, fill: 'none', stroke: '#f08c00', 'stroke-width': 1.6, 'stroke-dasharray': '4 4', class: 'fadein' }, svg);
    ln.style.animationDelay = (k * 0.15) + 's';
  });
  const g2 = row(B, LB, Y2, true);
  g2.classList.add('fadein');
  return { res, frees: frees.length, caps: captures(phi, x, t) };
}
function foShowTerm(t) { return t.t === 'fn' ? `${t.f}(${t.args.map(foShowTerm).join(',')})` : t.n; }

(function subLab() {
  const phiIn = $('subPhi'), tIn = $('subT'), xSel = $('subX');
  foKeys($('subKeys'), phiIn);
  let cur = null;
  function run() {
    const msg = $('subMsg');
    clearBox($('subTest'));
    try {
      const phi = foParse(phiIn.value), t = foParseTerm(tIn.value), x = xSel.value;
      const r = drawSubLab($('subSvg'), phi, x, t);
      cur = { phi, t, x };
      const ts = foShowTerm(t);
      if (!r.frees) okBox(msg, bi(`<span class="m">${x}</span> has <b>no free occurrence</b> in φ, so <span class="m">φ[${ts}/${x}] = φ</span>: nothing happens, and ${ts} is trivially substitutable.`,
        `<span class="m">${x}</span> 在 φ 中<b>没有自由出现</b>，所以 <span class="m">φ[${ts}/${x}] = φ</span>，什么都不变，${ts} 当然可代入。`), 'info');
      else if (r.caps.length) okBox(msg, bi(`✗ <b>Not substitutable.</b> A variable of <span class="m">${ts}</span> lands inside the scope of <span class="m">${r.caps.join(', ')}</span> and gets <b>captured</b> (red). The formula now says something different, so <span class="m">∀${x}φ → φ[${ts}/${x}]</span> is <b>not</b> an axiom.`,
        `✗ <b>不可代入。</b><span class="m">${ts}</span> 中的变元落进了 <span class="m">${r.caps.join('、')}</span> 的辖域，被<b>捕获</b>了（红色）。公式的意思变了，所以 <span class="m">∀${x}φ → φ[${ts}/${x}]</span> <b>不是</b>公理。`), 'bad');
      else okBox(msg, bi(`✓ <b>Substitutable.</b> Every free <span class="m">${x}</span> (gold) is replaced by <span class="m">${ts}</span> (blue), and no variable of <span class="m">${ts}</span> falls under a quantifier binding it. So <span class="m">∀${x}φ → φ[${ts}/${x}]</span> is an instance of axiom Q1.`,
        `✓ <b>可代入。</b>每个自由的 <span class="m">${x}</span>（金色）都换成了 <span class="m">${ts}</span>（蓝色），<span class="m">${ts}</span> 中没有变元落入约束它的量词辖域。所以 <span class="m">∀${x}φ → φ[${ts}/${x}]</span> 是公理 Q1 的一个实例。`));
    } catch (e) { errBox(msg, e); cur = null; }
  }
  $('subGo').addEventListener('click', run);
  [phiIn, tIn].forEach(i => i.addEventListener('keydown', e => e.key === 'Enter' && run()));
  xSel.addEventListener('change', run);
  document.querySelectorAll('[data-sub]').forEach(b => b.addEventListener('click', () => {
    const [p, x, t] = b.dataset.sub.split('|');
    phiIn.value = p; xSel.value = x; tIn.value = t;
    run();
  }));
  $('subTestGo').addEventListener('click', () => {
    if (!cur) return;
    const box = $('subTest');
    try {
      const inst = { type: 'bin', op: 'imp', a: { type: 'q', q: 'all', v: cur.x, a: cur.phi }, b: substF(cur.phi, cur.x, cur.t) };
      sigCheck(inst);
      for (let k = 0; k < 400; k++) {
        const M = randStructure();
        const s = counterAssignment(inst, M);
        if (s) {
          okBox(box, bi(`Counterexample found after ${k + 1} random structures to <span class="m">${foShow(inst)}</span>:<br><span class="m" style="font-size:13px">${describeStructure(M, symbolsOf(inst), s)}</span><br>The antecedent is true there, the consequent false. An “axiom” that can be false would make the proof system unsound.`,
            `随机试到第 ${k + 1} 个结构，找到 <span class="m">${foShow(inst)}</span> 的反例：<br><span class="m" style="font-size:13px">${describeStructure(M, symbolsOf(inst), s)}</span><br>前件为真、后件为假。如果“公理”能为假，证明系统就不可靠了。`), 'bad');
          return;
        }
      }
      if (substitutable(cur.phi, cur.x, cur.t)) okBox(box, bi(`No counterexample in 400 random structures of size ≤ 3 (all assignments checked) for <span class="m">${foShow(inst)}</span>. That is expected: when t is substitutable, <span class="m">∀xφ → φ[t/x]</span> is valid (substitution lemma).`,
        `对 <span class="m">${foShow(inst)}</span> 随机检查了 400 个规模 ≤ 3 的结构（每个都穷举所有赋值），没有反例。这在意料之中：t 可代入时，<span class="m">∀xφ → φ[t/x]</span> 是普遍有效的（代入引理）。`));
      else okBox(box, bi(`No counterexample in 400 random structures of size ≤ 3 for <span class="m">${foShow(inst)}</span>. Random search can miss, and sometimes a particular capture happens not to change the meaning; either way, since t is not substitutable this formula is <b>not</b> a Q1 axiom.`,
        `对 <span class="m">${foShow(inst)}</span> 随机检查了 400 个规模 ≤ 3 的结构，没有找到反例。随机搜索可能漏掉反例，有时某次捕获也恰好不改变意思；无论如何，t 不可代入，这个公式<b>不是</b> Q1 公理。`), 'warn');
    } catch (e) { errBox(box, e); }
  });
  run();
})();

/* =====================================================================
   §2 Generalization and its restriction
   ===================================================================== */
(function genDemo() {
  const M = emptyStructure(5);
  M.P = [true, true, false, true, false];
  let sx = 0;
  const show = new Set(['P']);
  function render() {
    StructView($('genSvg'), M, { W: 330, H: 230, show, assign: { x: sx }, onClick: i => { M.P[i] = !M.P[i]; render(); } });
    $('genX').innerHTML = [...Array(M.n).keys()].map(i => `<button class="btn small ${i === sx ? 'sel' : ''}" data-gx="${i}">x ↦ ${i}</button>`).join(' ');
    $('genX').querySelectorAll('[data-gx]').forEach(b => b.addEventListener('click', () => { sx = +b.dataset.gx; render(); }));
    const px = M.P[sx], all = M.P.every(Boolean);
    $('genVals').innerHTML = `<div class="evrow"><span class="m">𝔐 ⊨ P(x)[s]</span> <b class="${px ? 'tv1' : 'tv0'}">${px ? bil('true', '真') : bil('false', '假')}</b></div>
      <div class="evrow"><span class="m">𝔐 ⊨ ∀xP(x)</span> <b class="${all ? 'tv1' : 'tv0'}">${all ? bil('true', '真') : bil('false', '假')}</b></div>`;
    if (px && !all) okBox($('genMsg'), bi(`Here the hypothesis <span class="m">P(x)</span> is true under s, yet <span class="m">∀xP(x)</span> is false. So <span class="m">P(x) ⊭ ∀xP(x)</span>: generalizing on <span class="m">x</span> while <span class="m">x</span> is free in a hypothesis would be unsound.`,
      `此处假设 <span class="m">P(x)</span> 在赋值 s 下为真，<span class="m">∀xP(x)</span> 却为假。所以 <span class="m">P(x) ⊭ ∀xP(x)</span>：若 <span class="m">x</span> 在假设中自由出现，还对 <span class="m">x</span> 做概括，就不可靠了。`), 'bad');
    else if (!px) okBox($('genMsg'), bi('Under this assignment the hypothesis P(x) is false, so it tells us nothing. Move x to a gold element.', '在这个赋值下假设 P(x) 本身为假，说明不了问题。把 x 移到一个金色元素上。'), 'info');
    else okBox($('genMsg'), bi('Every element is in P, so here both are true. Click an element to remove it from P and see the problem.', '每个元素都在 P 中，所以两者都真。点击某个元素把它移出 P，看看问题出在哪。'), 'info');
  }
  render();
})();

/* =====================================================================
   §3 Step-through proofs and the counterexample to the converse
   ===================================================================== */
const PROOFS = {
  swap: {
    goal: '∀x∀yR(x,y) ⊢ ∀y∀xR(x,y)',
    lines: [
      { f: '∀x∀yR(x,y)', j: bil('hypothesis', '假设'), cites: [] },
      { f: '∀x∀yR(x,y) → ∀yR(x,y)', j: bil('Q1 with t = x (trivially substitutable)', 'Q1，取 t = x（显然可代入）'), cites: [] },
      { f: '∀yR(x,y)', j: bil('MP 1, 2', 'MP 1, 2'), cites: [0, 1] },
      { f: '∀yR(x,y) → R(x,y)', j: bil('Q1 with t = y', 'Q1，取 t = y'), cites: [] },
      { f: 'R(x,y)', j: bil('MP 3, 4', 'MP 3, 4'), cites: [2, 3] },
      { f: '∀xR(x,y)', j: bil('Gen on x: x is not free in the hypothesis ✓', '对 x 概括：x 在假设中不自由出现 ✓'), cites: [4] },
      { f: '∀y∀xR(x,y)', j: bil('Gen on y: y is not free in the hypothesis ✓', '对 y 概括：y 在假设中不自由出现 ✓'), cites: [5] },
    ],
  },
  exall: {
    goal: '∃x∀yR(x,y) ⊢ ∀y∃xR(x,y)',
    lines: [
      { f: '∃x∀yR(x,y)', j: bil('hypothesis', '假设'), cites: [] },
      { f: '∀yR(x,y)', j: bil('temporary assumption: “let x be such a witness”', '临时假设：“设 x 就是这样一个见证”'), cites: [], depth: 1 },
      { f: '∀yR(x,y) → R(x,y)', j: bil('Q1 with t = y', 'Q1，取 t = y'), cites: [], depth: 1 },
      { f: 'R(x,y)', j: bil('MP 2, 3', 'MP 2, 3'), cites: [1, 2], depth: 1 },
      { f: 'R(x,y) → ∃xR(x,y)', j: bil('∃-introduction axiom φ[t/x] → ∃xφ (t = x)', '∃ 引入公理 φ[t/x] → ∃xφ（t = x）'), cites: [], depth: 1 },
      { f: '∃xR(x,y)', j: bil('MP 4, 5', 'MP 4, 5'), cites: [3, 4], depth: 1 },
      { f: '∀y∃xR(x,y)', j: bil('Gen on y: y is free in neither line 1 nor line 2 ✓', '对 y 概括：y 在第 1、2 行都不自由出现 ✓'), cites: [5], depth: 1 },
      { f: '∀y∃xR(x,y)', j: bil('∃-elimination on 1 and 2–7: x is not free in the conclusion or in line 1 ✓', '∃ 消去（第 1 行与 2–7 行）：x 在结论和第 1 行中都不自由出现 ✓'), cites: [0, 6] },
    ],
  },
};
(function proofs() {
  let which = 'swap', pv = null;
  function load() {
    pv = ProofView($('pfBox'), PROOFS[which].lines);
    pv.next();
    $('pfGoal').innerHTML = `<span class="m">${PROOFS[which].goal}</span>`;
    document.querySelectorAll('[data-pf]').forEach(b => b.classList.toggle('sel', b.dataset.pf === which));
    clearBox($('pfMsg'));
  }
  document.querySelectorAll('[data-pf]').forEach(b => b.addEventListener('click', () => { which = b.dataset.pf; load(); }));
  $('pfNext').addEventListener('click', () => {
    const k = pv.next();
    if (k === PROOFS[which].lines.length) okBox($('pfMsg'), which === 'swap'
      ? bi('∎ Done. The trick: strip both quantifiers with Q1, then put them back in the other order with Gen. Both Gen steps are legal because the hypothesis is a <i>sentence</i>.', '∎ 证毕。诀窍：先用 Q1 把两个量词剥掉，再用 Gen 按相反顺序装回去。两次 Gen 都合法，因为假设是<i>语句</i>（没有自由变元）。')
      : bi('∎ Done. ∃-elimination is the formal version of “pick a witness x and argue about it”; its side condition (x not free in the conclusion) is exactly the condition that the argument did not depend on <i>which</i> witness was picked.', '∎ 证毕。∃ 消去就是“任取一个见证 x 来论证”的形式化；它的附加条件（x 在结论中不自由出现）正好保证论证不依赖于取的是<i>哪一个</i>见证。'));
  });
  $('pfAll').addEventListener('click', () => pv.all());
  $('pfReset').addEventListener('click', () => { pv.reset(); pv.next(); clearBox($('pfMsg')); });
  load();
})();

(function converse() {
  let M = emptyStructure(3);
  M.R = [[false, true, false], [false, false, true], [false, false, false]];
  const A = foParse('∃x∀yR(x,y)'), B = foParse('∀y∃xR(x,y)');
  function setN(n) {
    const old = M;
    M = emptyStructure(n);
    for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) M.R[i][j] = i < old.n && j < old.n ? old.R[i][j] : false;
    render();
  }
  function render() {
    const hubs = [...Array(M.n).keys()].filter(i => M.R[i].every(Boolean));
    StructView($('cvSvg'), M, { W: 300, H: 230, show: new Set(['R']), highlight: hubs });
    let h = '<table class="tt rmat"><tr><th>R</th>' + [...Array(M.n).keys()].map(j => `<th>${j}</th>`).join('') + '</tr>';
    for (let i = 0; i < M.n; i++) {
      h += `<tr><th>${i}</th>` + [...Array(M.n).keys()].map(j => `<td class="click ${M.R[i][j] ? 'c1' : 'c0'}" data-i="${i}" data-j="${j}">${M.R[i][j] ? 1 : 0}</td>`).join('') + '</tr>';
    }
    $('cvMat').innerHTML = h + '</table>';
    $('cvMat').querySelectorAll('td.click').forEach(td => td.addEventListener('click', () => { M.R[+td.dataset.i][+td.dataset.j] = !M.R[+td.dataset.i][+td.dataset.j]; render(); }));
    const a = sat(A, M), b = sat(B, M);
    const noIn = [...Array(M.n).keys()].filter(j => ![...Array(M.n).keys()].some(i => M.R[i][j]));
    $('cvVals').innerHTML = `<div class="evrow"><span class="m">∃x∀yR(x,y)</span> <b class="${a ? 'tv1' : 'tv0'}">${a ? bil('true', '真') : bil('false', '假')}</b>
      <span class="muted" style="font-size:13px">${a ? bil(`witness: ${hubs.join(', ')} points to everything (red ring)`, `见证：${hubs.join('、')} 指向所有元素（红圈）`) : bil('no element points to every element', '没有哪个元素指向全部元素')}</span></div>
      <div class="evrow"><span class="m">∀y∃xR(x,y)</span> <b class="${b ? 'tv1' : 'tv0'}">${b ? bil('true', '真') : bil('false', '假')}</b>
      <span class="muted" style="font-size:13px">${b ? bil('every element receives an arrow', '每个元素都有箭头指入') : bil(`no arrow into: ${noIn.join(', ')}`, `没有箭头指入：${noIn.join('、')}`)}</span></div>`;
    if (b && !a) okBox($('cvMsg'), bi('Counterexample to the converse: <span class="m">∀y∃xR(x,y) ⊭ ∃x∀yR(x,y)</span>. Each y has its own x, but no single x works for all y. By soundness, no proof of the converse can exist.', '逆命题的反例：<span class="m">∀y∃xR(x,y) ⊭ ∃x∀yR(x,y)</span>。每个 y 都有各自的 x，却没有一个 x 对所有 y 都管用。由可靠性定理，逆命题不可能有证明。'));
    else if (a && !b) okBox($('cvMsg'), bi('Impossible! (We just proved ∃∀ ⊢ ∀∃.) Check again… this message should never appear.', '不可能出现！（我们刚证明了 ∃∀ ⊢ ∀∃。）这条消息本不应出现。'), 'bad');
    else okBox($('cvMsg'), bi('Not a counterexample yet: you need ∀y∃x true and ∃x∀y false. Click matrix cells to toggle arrows.', '还不是反例：需要 ∀y∃x 为真而 ∃x∀y 为假。点击矩阵格子增删箭头。'), 'info');
  }
  document.querySelectorAll('[data-cvn]').forEach(b => b.addEventListener('click', () => setN(+b.dataset.cvn)));
  render();
})();

/* =====================================================================
   §4 Soundness
   ===================================================================== */
(function soundness() {
  const G = ['∀x(P(x) → Q(x))', 'P(c)'].map(foParse);
  const lines = [
    { f: '∀x(P(x) → Q(x))', kind: 'hyp', j: bil('hypothesis', '假设'), cites: [] },
    { f: '∀x(P(x) → Q(x)) → (P(c) → Q(c))', kind: 'ax', j: bil('Q1, t = c', 'Q1，t = c'), cites: [] },
    { f: 'P(c) → Q(c)', kind: 'mp', j: 'MP 1, 2', cites: [0, 1] },
    { f: 'P(c)', kind: 'hyp', j: bil('hypothesis', '假设'), cites: [] },
    { f: 'Q(c)', kind: 'mp', j: 'MP 3, 4', cites: [2, 3] },
    { f: 'Q(c) → ∃xQ(x)', kind: 'ax', j: bil('∃-introduction axiom', '∃ 引入公理'), cites: [] },
    { f: '∃xQ(x)', kind: 'mp', j: 'MP 5, 6', cites: [4, 5] },
  ];
  const asts = lines.map(l => foParse(l.f));
  let M = null, pv = null, token = 0;
  const show = new Set(['P', 'Q', 'c']);
  function newM(model) {
    for (let k = 0; k < 500; k++) {
      const N = randStructure(pick([2, 3, 4]));
      const isModel = G.every(g => sat(g, N));
      if (model === isModel) return N;
    }
    return randStructure(3);
  }
  async function run(model) {
    const my = ++token;
    M = newM(model);
    StructView($('sdSvg'), M, { W: 300, H: 230, show });
    $('sdLegend').innerHTML = structLegend(show) + `<div class="legend"><span>${bil('c = purple label', 'c＝紫色标签')}</span></div>`;
    const isModel = G.every(g => sat(g, M));
    $('sdModel').innerHTML = isModel ? `<span class="badge-big taut">${bi('𝔐 ⊨ Γ', '𝔐 ⊨ Γ')}</span>` : `<span class="badge-big unsat">${bi('𝔐 ⊭ Γ', '𝔐 ⊭ Γ')}</span>`;
    pv = ProofView($('sdBox'), lines);
    for (let i = 0; i < lines.length; i++) {
      await sleep(i ? 650 : 200);
      if (my !== token) return;
      pv.next();
      const v = sat(asts[i], M), L = lines[i];
      let why;
      if (L.kind === 'ax') why = bil('axiom: valid, true in every structure', '公理：普遍有效，在任何结构中都真');
      else if (L.kind === 'hyp') why = v ? bil('hypothesis: true because 𝔐 ⊨ Γ', '假设：因为 𝔐 ⊨ Γ，所以为真') : bil('hypothesis fails: 𝔐 is not a model of Γ', '假设不成立：𝔐 不是 Γ 的模型');
      else why = v ? bil(`MP: lines ${L.cites[0] + 1} and ${L.cites[1] + 1} are true, hence so is this`, `MP：第 ${L.cites[0] + 1}、${L.cites[1] + 1} 行为真，所以本行也为真`) : bil('MP from a false line: no guarantee', '由假的行做 MP：没有任何保证');
      pv.badge(i, `${v ? '✓' : '✗'} <span class="pwhy">${why}</span>`, v ? 'b1' : 'b0');
    }
    if (isModel) okBox($('sdMsg'), bi('Truth flowed all the way down: every line, in particular the conclusion <span class="m">∃xQ(x)</span>, holds in this model of Γ. Soundness is exactly this, proved by induction on the length of the derivation.', '真值一路向下传递：每一行，特别是结论 <span class="m">∃xQ(x)</span>，在这个 Γ 的模型里都成立。可靠性定理说的正是这件事，对推导长度归纳即可证明。'));
    else okBox($('sdMsg'), bi('𝔐 is not a model of Γ, so soundness promises nothing about the hypotheses and what follows from them. The axiom lines are still true: axioms are valid.', '𝔐 不是 Γ 的模型，可靠性定理对假设及其推论不作任何保证。但公理行依然为真：公理是普遍有效的。'), 'warn');
  }
  $('sdGo').addEventListener('click', () => run(true));
  $('sdAny').addEventListener('click', () => run(false));
  run(true);
})();

(function axiomTester() {
  const items = [
    { s: '∀xR(x,y) → R(f(y),y)', ok: true, en: 'Q1 with t = f(y): substitutable', zh: 'Q1，t = f(y)：可代入' },
    { s: '∀x(P(c) → Q(x)) → (P(c) → ∀xQ(x))', ok: true, en: 'Q2: x not free in P(c)', zh: 'Q2：x 在 P(c) 中不自由' },
    { s: 'x = y → (R(x,x) → R(x,y))', ok: true, en: 'equality axiom E2', zh: '等词公理 E2' },
    { s: '∀x∃y(y ≠ x) → ∃y(y ≠ y)', ok: false, en: 'fake Q1: y is captured', zh: '假 Q1：y 被捕获' },
    { s: '∀x(P(x) → Q(x)) → (P(x) → ∀xQ(x))', ok: false, en: 'fake Q2: x is free in P(x)', zh: '假 Q2：x 在 P(x) 中自由' },
    { s: 'P(x) → ∀xP(x)', ok: false, en: 'unrestricted Gen as an axiom', zh: '无限制的 Gen 当公理' },
  ];
  let token = 0;
  const box = $('axBtns');
  items.forEach((it, i) => {
    const b = document.createElement('button');
    b.className = 'btn small';
    b.innerHTML = `<span class="m">${it.s}</span>`;
    b.title = it.en + ' / ' + it.zh;
    b.addEventListener('click', () => test(i));
    box.appendChild(b);
  });
  async function test(i) {
    const my = ++token;
    box.querySelectorAll('button').forEach((b, k) => b.classList.toggle('sel', k === i));
    const it = items[i], f = foParse(it.s), syms = symbolsOf(f);
    $('axGrid').innerHTML = '';
    $('axDetail').innerHTML = '';
    clearBox($('axMsg'));
    let bad = 0;
    for (let k = 0; k < 40; k++) {
      const M = randStructure();
      const s = counterAssignment(f, M);
      const d = document.createElement('div');
      d.className = 'stile pop ' + (s ? 'bad' : 'good');
      d.textContent = s ? '✗' : '✓';
      d.title = `|M| = ${M.n}`;
      if (s) {
        bad++;
        d.addEventListener('click', () => {
          $('axDetail').innerHTML = `<div class="row" style="align-items:center"><svg id="axSv"></svg><div class="col">${structLegend(syms)}
            <p class="m" style="font-size:13px">${describeStructure(M, syms, s)}</p>
            <p>${bi(`Under this assignment the antecedent is true and the consequent false.`, `在这个赋值下前件真、后件假。`)}</p></div></div>`;
          StructView($('axSv'), M, { W: 260, H: 210, show: syms, assign: s });
        });
      }
      $('axGrid').appendChild(d);
      await sleep(35);
      if (my !== token) return;
    }
    if (bad) okBox($('axMsg'), bi(`<b>${it.en}.</b> ${bad} of 40 random structures falsify it (red). Click a red tile to see the counterexample. This formula cannot be an axiom of a sound system.`,
      `<b>${it.zh}。</b>40 个随机结构中有 ${bad} 个使它为假（红色）。点击红块查看反例。这样的公式不能当可靠系统的公理。`), 'bad');
    else okBox($('axMsg'), bi(`<b>${it.en}.</b> True in all 40 random structures under every assignment. Of course random testing proves nothing; the real proof is a short argument for each axiom scheme, valid in <i>every</i> structure.`,
      `<b>${it.zh}。</b>在 40 个随机结构、所有赋值下都为真。当然随机测试不算证明；真正的证明是对每条公理模式给出简短论证，说明它在<i>每个</i>结构中都成立。`));
  }
  test(3);
})();

/* =====================================================================
   §5 Completeness: the road map
   ===================================================================== */
(function roadmap() {
  const svg = $('roadSvg');
  const boxes = [
    { en: 'Γ consistent', zh: 'Γ 一致', f: 'Γ ⊬ ⊥', sec: null,
      den: 'Start: Γ is a consistent set of L-sentences (no derivation of ⊥). Goal: produce a structure 𝔄 with 𝔄 ⊨ Γ.',
      dzh: '出发点：Γ 是一致的 L 语句集（推不出 ⊥）。目标：造出一个结构 𝔄，使 𝔄 ⊨ Γ。' },
    { en: 'add witnesses', zh: '添加见证常元', f: '∃xφ → φ(c_φ)', sec: 's6',
      den: 'Add a new constant c_φ for every sentence ∃xφ (φ has at most x free), together with the Henkin axiom ∃xφ → φ(c_φ). Repeat ω times. Consistency is preserved.',
      dzh: '对每个语句 ∃xφ（φ 中至多 x 自由出现）引入新常元 c_φ，并加入亨金公理 ∃xφ → φ(c_φ)。重复 ω 轮。一致性保持不变。' },
    { en: 'Lindenbaum', zh: '林登鲍姆引理', f: 'Γ* ⊇ Γ_H', sec: 's6',
      den: 'Extend to a maximal consistent Γ*: for each sentence σ, exactly one of σ, ¬σ lies in Γ*. The Henkin axioms come along.',
      dzh: '扩张成极大一致集 Γ*：对每个语句 σ，σ 与 ¬σ 恰有一个属于 Γ*。亨金公理也一并带上。' },
    { en: 'term model', zh: '项模型', f: '𝔄 = Terms / ∼', sec: 's7',
      den: 'Universe: closed terms modulo t ∼ s ⇔ (t = s) ∈ Γ*. Symbols are interpreted “syntactically”.',
      dzh: '论域：闭项按 t ∼ s ⇔ (t = s) ∈ Γ* 取商。各符号都按“语法本身”来解释。' },
    { en: 'truth lemma', zh: '真引理', f: '𝔄 ⊨ σ ⇔ σ ∈ Γ*', sec: 's7',
      den: 'By induction on σ. The ∃-step needs the witnesses, the ¬ and → steps need maximality. Since Γ ⊆ Γ*, 𝔄 ⊨ Γ. ∎',
      dzh: '对 σ 归纳。∃ 的情形要用见证常元，¬ 与 → 的情形要用极大性。由于 Γ ⊆ Γ*，得 𝔄 ⊨ Γ。∎' },
  ];
  const BW = 172, GAP = 30, X0 = 12, Y0 = 26, BH = 104;
  const mk = marker(svg, '#9aa0aa');
  const gs = boxes.map((b, i) => {
    const x = X0 + i * (BW + GAP);
    if (i) el('line', { x1: x - GAP + 2, y1: Y0 + BH / 2, x2: x - 4, y2: Y0 + BH / 2, stroke: '#9aa0aa', 'stroke-width': 2.5, 'marker-end': mk }, svg);
    const g = el('g', { class: 'rbox' }, svg);
    g.style.cursor = 'pointer';
    el('rect', { x, y: Y0, width: BW, height: BH, rx: 14, fill: '#fff', stroke: '#c9c4b5', 'stroke-width': 2 }, g);
    svgText(g, x + 18, Y0 + 22, String(i + 1), { 'font-size': 13, 'font-weight': 800, fill: '#3b5bdb' });
    svgBi(g, x + BW / 2, Y0 + 32, b.en, b.zh, { size: 16, weight: 700 }, 20);
    const ft = svgText(g, x + BW / 2, Y0 + 84, b.f, { 'font-size': 15, fill: '#ae3ec9', 'font-weight': 700 });
    ft.style.fontFamily = 'var(--sans)';
    g.addEventListener('click', () => select(i));
    return g;
  });
  const tokenDot = el('circle', { cx: X0 + BW / 2, cy: Y0 + BH + 16, r: 8, fill: '#3b5bdb' }, svg);
  tokenDot.style.transition = 'cx .5s ease';
  function select(i) {
    gs.forEach((g, k) => g.classList.toggle('on', k <= i));
    tokenDot.setAttribute('cx', X0 + i * (BW + GAP) + BW / 2);
    const b = boxes[i];
    $('roadInfo').innerHTML = `<b>${i + 1}.</b> ` + bi(b.den, b.dzh) + (b.sec ? ` <a href="#${b.sec}">${bil('→ see the animation below', '→ 看下面的动画')}</a>` : '');
    $('roadInfo').className = 'msg info';
  }
  let playing = 0;
  $('roadPlay').addEventListener('click', async () => {
    const my = ++playing;
    for (let i = 0; i < boxes.length; i++) { select(i); await sleep(1300); if (my !== playing) return; }
  });
  select(0);
  const steps = [...document.querySelectorAll('#redSteps .step')];
  let k = 0;
  $('redNext').addEventListener('click', () => { if (k < steps.length) steps[k++].classList.add('on'); });
  $('redAll').addEventListener('click', () => { steps.forEach(s => s.classList.add('on')); k = steps.length; });
})();

/* =====================================================================
   §6 Henkin witnesses and Lindenbaum's lemma
   ===================================================================== */
(function witnesses() {
  const svg = $('wSvg');
  const A = [
    ['∃xP(x)', 'P(c₁)'], ['∃xR(c,x)', 'R(c,c₂)'], ['∃x¬P(x)', '¬P(c₃)'], ['∃x(P(x) ∧ R(x,c))', 'P(c₄) ∧ R(c₄,c)'],
  ];
  const C = [
    ['∃xR(c₂,x)', 'R(c₂,c₅)', 1], ['∃x(R(x,c₁) ∧ P(x))', 'R(c₆,c₁) ∧ P(c₆)', 0], ['∃x(x ≠ c₃)', 'c₇ ≠ c₃', 2],
  ];
  const RY = i => 92 + i * 52;
  let step = 1;
  function base() {
    svg.innerHTML = '';
    el('rect', { x: 6, y: 30, width: 300, height: 270, rx: 14, fill: '#fffaf0', stroke: '#f0d9a8' }, svg);
    el('rect', { x: 318, y: 30, width: 90, height: 270, rx: 14, fill: '#f3f0ff', stroke: '#d0c6f5' }, svg);
    el('rect', { x: 452, y: 30, width: 330, height: 270, rx: 14, fill: '#fffaf0', stroke: '#f0d9a8' }, svg);
    el('rect', { x: 794, y: 30, width: 90, height: 270, rx: 14, fill: '#f3f0ff', stroke: '#d0c6f5' }, svg);
    svgBi(svg, 156, 52, '∃-formulas of L₀ = {P, R, c}', 'L₀ = {P, R, c} 中的 ∃ 公式', { size: 13, weight: 700, fill: '#b35c00' }, 16);
    svgBi(svg, 363, 52, 'new in L₁', 'L₁ 新增', { size: 12, weight: 700, fill: '#5f3dc4' }, 16);
    svgBi(svg, 617, 52, 'new ∃-formulas of L₁', 'L₁ 中新出现的 ∃ 公式', { size: 13, weight: 700, fill: '#b35c00' }, 16);
    svgBi(svg, 839, 52, 'new in L₂', 'L₂ 新增', { size: 12, weight: 700, fill: '#5f3dc4' }, 16);
    A.forEach((a, i) => svgText(svg, 156, RY(i) + 5, fo(a[0]), { 'font-size': 15 }));
    svgText(svg, 156, RY(4) + 5, '⋮', { 'font-size': 16, fill: '#999' });
    svgText(svg, 363, RY(4) + 5, '⋮', { 'font-size': 16, fill: '#999' });
  }
  function render() {
    base();
    const mk = marker(svg, '#7048e8');
    const axioms = [];
    A.forEach((a, i) => {
      if (step <= i) return;
      const p = el('path', { d: `M${156 + fo(a[0]).length * 4.6 + 4},${RY(i)} C 300,${RY(i)} 300,${RY(i)} 338,${RY(i)}`, fill: 'none', stroke: '#7048e8', 'stroke-width': 2, 'marker-end': mk }, svg);
      p.classList.add('fadein');
      const g = el('g', { class: 'pop' }, svg);
      el('rect', { x: 340, y: RY(i) - 15, width: 46, height: 28, rx: 9, fill: '#7048e8' }, g);
      svgText(g, 363, RY(i) + 5, 'c' + sub(i + 1), { fill: '#fff', 'font-size': 15, 'font-weight': 700 });
      axioms.push(`${fo(a[0])} → ${a[1]}`);
    });
    C.forEach((c, i) => {
      if (step <= 4 + i) return;
      const y = RY(i);
      const from = RY(c[2]);
      const dl = el('path', { d: `M386,${from} C 420,${from} 430,${y} 470,${y}`, fill: 'none', stroke: '#b197fc', 'stroke-width': 1.5, 'stroke-dasharray': '4 3' }, svg);
      dl.classList.add('fadein');
      const t = svgText(svg, 617, y + 5, fo(c[0]), { 'font-size': 15 });
      t.classList.add('fadein');
      const p = el('path', { d: `M${617 + fo(c[0]).length * 4.6 + 4},${y} C 780,${y} 780,${y} 814,${y}`, fill: 'none', stroke: '#7048e8', 'stroke-width': 2, 'marker-end': mk }, svg);
      p.classList.add('fadein');
      const g = el('g', { class: 'pop' }, svg);
      el('rect', { x: 816, y: y - 15, width: 46, height: 28, rx: 9, fill: '#7048e8' }, g);
      svgText(g, 839, y + 5, 'c' + sub(i + 5), { fill: '#fff', 'font-size': 15, 'font-weight': 700 });
      axioms.push(`${fo(c[0])} → ${c[1]}`);
    });
    if (step > 4) { svgText(svg, 617, RY(3) + 5, '⋮', { 'font-size': 16, fill: '#999' }); svgText(svg, 839, RY(3) + 5, '⋮', { 'font-size': 16, fill: '#999' }); }
    if (step === 4) svgBi(svg, 617, RY(1), 'L₁ = L₀ ∪ {c₁, c₂, …} has new ∃-formulas →', 'L₁ = L₀ ∪ {c₁, c₂, …} 又有了新的 ∃ 公式 →', { size: 12, fill: '#999' }, 16);
    if (step >= 8) {
      const g = el('g', { class: 'fadein' }, svg);
      el('rect', { x: 150, y: 312, width: 600, height: 34, rx: 10, fill: '#1f2430' }, g);
      svgText(g, 450, 334, 'L_ω = L₀ ∪ L₁ ∪ L₂ ∪ ⋯  ·  |L_ω| = |L| + ℵ₀', { fill: '#fff', 'font-size': 15, 'font-weight': 700 });
    }
    $('wAx').innerHTML = axioms.length ? axioms.map((a, i) => `<div class="fadein m">${bil('Henkin axiom', '亨金公理')}: ${a}</div>`).join('') : `<span class="muted">${bil('(Henkin axioms will appear here)', '（亨金公理将出现在这里）')}</span>`;
    $('wNext').disabled = step >= 8;
    const msgs = [
      bi('Each ∃-sentence ∃xφ (φ has at most the free variable x) gets its own brand-new constant: its <b>witness</b>.', '每个 ∃ 语句 ∃xφ（φ 中至多 x 自由出现）都分到一个全新的常元，即它的<b>见证常元</b>。'),
      bi('c₁ is a name for “some P-thing, if there is one”. The Henkin axiom says exactly that.', 'c₁ 是“某个具有 P 性质的东西（如果有的话）”的名字，亨金公理说的正是这个意思。'),
      bi('Witnesses for formulas that mention old constants: c₂ is “some R-successor of c”.', '涉及旧常元的公式也要见证：c₂ 是“c 的某个 R-后继”。'),
      bi('Note: the Henkin axiom is an <i>implication</i>. We do not claim ∃x¬P(x) is true, only that <i>if</i> it is, c₃ is an example.', '注意：亨金公理是一个<i>蕴涵式</i>。我们并不断言 ∃x¬P(x) 为真，只是说<i>如果</i>它真，c₃ 就是一个例子。'),
      bi('Layer 0 done. But now L₁ contains new formulas such as ∃xR(c₂,x), which have no witness yet!', '第 0 层完成。可 L₁ 里又出现了 ∃xR(c₂,x) 这类新公式，它们还没有见证！'),
      bi('So we repeat: every new ∃-formula of L₁ gets a witness in L₂.', '所以再来一轮：L₁ 中每个新的 ∃ 公式都在 L₂ 里得到见证。'),
      bi('Formulas can mix old and new constants freely.', '公式里新旧常元可以随意混用。'),
      bi('One more round… and another… ω rounds in total.', '再一轮……再一轮……一共 ω 轮。'),
      bi('Take the union. Every ∃-formula of L_ω lives in some L_n, so it has a witness in L_{n+1}. Only countably many new constants were added per round, so the size stays |L| + ℵ₀.', '取并集。L_ω 中每个 ∃ 公式都属于某个 L_n，因而在 L_{n+1} 中有见证。每轮只加可数多个新常元，所以规模仍是 |L| + ℵ₀。'),
    ];
    $('wInfo').innerHTML = msgs[step];
    $('wInfo').className = 'msg info';
  }
  $('wNext').addEventListener('click', () => { if (step < 8) step++; render(); });
  $('wAll').addEventListener('click', () => { step = 8; render(); });
  $('wReset').addEventListener('click', () => { step = 0; render(); });
  render();
  const steps = [...document.querySelectorAll('#hkSteps .step')];
  let k = 0;
  $('hkNext').addEventListener('click', () => { if (k < steps.length) steps[k++].classList.add('on'); });
  $('hkAll').addEventListener('click', () => { steps.forEach(s => s.classList.add('on')); k = steps.length; });
})();

(function lindenbaum() {
  const svg = $('lbSvg');
  const T0 = ['∀x(P(x) → Q(x))', 'P(c)'];
  const S = [
    { s: 'Q(c)', take: 0, altBad: true,
      en: 'T₀ ⊢ Q(c) (Q1 + MP), so T₀ ∪ {¬Q(c)} is inconsistent. Add σ₀.', zh: 'T₀ ⊢ Q(c)（Q1 + MP），所以 T₀ ∪ {¬Q(c)} 不一致。加入 σ₀。' },
    { s: 'P(d)', take: 0, altBad: false,
      en: 'Both P(d) and ¬P(d) are consistent with T₁. The rule says: add σ₁ whenever that is consistent.', zh: 'P(d) 和 ¬P(d) 都与 T₁ 一致。规则：只要加 σ₁ 仍一致，就加 σ₁。' },
    { s: '¬Q(d)', take: 1, altBad: true,
      en: 'T₂ ⊢ Q(d) (since P(d) is now in), so adding ¬Q(d) is inconsistent. Add ¬σ₂ = ¬¬Q(d) instead.', zh: 'T₂ ⊢ Q(d)（因为 P(d) 已经加入），所以加 ¬Q(d) 会不一致。改加 ¬σ₂ = ¬¬Q(d)。' },
    { s: 'c = d', take: 0, altBad: false,
      en: 'Consistent either way; add c = d. (Γ* now identifies c and d: they will be one element of the term model.)', zh: '两种选择都一致；加入 c = d。（Γ* 由此把 c 与 d 等同：它们将是项模型中的同一个元素。）' },
    { s: '∃x¬P(x)', take: 0, altBad: false,
      en: 'Consistent: add it. Its Henkin axiom ∃x¬P(x) → ¬P(c_¬P) is already in Γ_H, so now T₅ ⊢ ¬P(c_¬P): the witness is forced.', zh: '一致，加入。它的亨金公理 ∃x¬P(x) → ¬P(c_¬P) 早已在 Γ_H 中，于是 T₅ ⊢ ¬P(c_¬P)：见证自动就位。' },
  ];
  const D = S.length, W = 940, LH = 56, Y0 = 34;
  let step = 0;
  const nodeX = (lvl, idx) => 20 + (idx + 0.5) * (W - 40) / Math.pow(2, lvl);
  function render() {
    svg.innerHTML = '';
    // the whole tree, faint
    for (let l = 0; l <= D; l++) for (let i = 0; i < Math.pow(2, l); i++) {
      const x = nodeX(l, i), y = Y0 + l * LH;
      if (l < D) [0, 1].forEach(b => el('line', { x1: x, y1: y, x2: nodeX(l + 1, 2 * i + b), y2: y + LH, stroke: '#e6e2d6', 'stroke-width': 1 }, svg));
      el('circle', { cx: x, cy: y, r: 3, fill: '#d8d3c4' }, svg);
    }
    for (let l = 0; l < D; l++) {
      svgText(svg, 6, Y0 + l * LH + LH / 2 + 4, 'σ' + sub(l), { 'text-anchor': 'start', fill: '#999', 'font-size': 12 });
    }
    let idx = 0;
    for (let l = 0; l < step; l++) {
      const x = nodeX(l, idx), y = Y0 + l * LH, st = S[l];
      const good = 2 * idx + st.take, alt = 2 * idx + 1 - st.take;
      const gx = nodeX(l + 1, good), ax = nodeX(l + 1, alt);
      el('line', { x1: x, y1: y, x2: ax, y2: y + LH, stroke: st.altBad ? '#e03131' : '#adb5bd', 'stroke-width': 2, 'stroke-dasharray': '5 4' }, svg);
      if (st.altBad) svgText(svg, ax, y + LH + 5, '✗', { fill: '#e03131', 'font-size': 18, 'font-weight': 800 });
      else el('circle', { cx: ax, cy: y + LH, r: 5, fill: '#fff', stroke: '#adb5bd', 'stroke-width': 2 }, svg);
      const ln = el('line', { x1: x, y1: y, x2: gx, y2: y + LH, stroke: '#2f9e44', 'stroke-width': 4, class: 'fadein' }, svg);
      const lab = st.take ? '¬' + st.s : st.s, altLab = st.take ? st.s : '¬' + st.s;
      const lx = (x + gx) / 2, ly = y + LH / 2;
      svgText(svg, lx + (gx > x ? 8 : -8), ly, lab, { 'text-anchor': gx > x ? 'start' : 'end', fill: '#2f9e44', 'font-size': 12, 'font-weight': 700 });
      svgText(svg, (x + ax) / 2 + (ax > x ? 8 : -8), ly, altLab, { 'text-anchor': ax > x ? 'start' : 'end', fill: st.altBad ? '#e03131' : '#999', 'font-size': 11 });
      idx = good;
    }
    // path nodes
    let id2 = 0;
    for (let l = 0; l <= step; l++) {
      el('circle', { cx: nodeX(l, id2), cy: Y0 + l * LH, r: l === step ? 9 : 6, fill: l === step ? '#2f9e44' : '#d3f9d8', stroke: '#2f9e44', 'stroke-width': 2, class: l === step ? 'pop' : '' }, svg);
      if (l < step) id2 = 2 * id2 + S[l].take;
    }
    if (step === D) svgText(svg, nodeX(D, id2), Y0 + D * LH + 26, '⋮  Γ* = ⋃ Tₙ', { fill: '#2f9e44', 'font-weight': 700, 'font-size': 14 });
    // current theory
    const T = [...T0];
    for (let l = 0; l < step; l++) T.push(S[l].take ? '¬' + S[l].s : S[l].s);
    $('lbT').innerHTML = `<span class="m">T${sub(step)} = Γ_H ∪ {${T.join(', ')}}</span>`;
    $('lbInfo').innerHTML = step ? bi(`<b>σ${sub(step - 1)} = <span class="m">${S[step - 1].s}</span>.</b> ${S[step - 1].en}`, `<b>σ${sub(step - 1)} = <span class="m">${S[step - 1].s}</span>。</b>${S[step - 1].zh}`)
      : bi('Enumerate all sentences σ₀, σ₁, σ₂, … of L_ω. Walk down the tree: at level n go left (add σₙ) if that stays consistent, otherwise go right (add ¬σₙ). Red ✗ = that branch would be inconsistent.',
        '把 L_ω 的所有语句排成 σ₀, σ₁, σ₂, …。沿树往下走：第 n 层若加 σₙ 仍一致就往左（加 σₙ），否则往右（加 ¬σₙ）。红色 ✗ 表示那一支会不一致。');
    $('lbInfo').className = 'msg info';
    $('lbNext').disabled = step >= D;
  }
  $('lbNext').addEventListener('click', () => { if (step < D) step++; render(); });
  $('lbAll').addEventListener('click', () => { step = D; render(); });
  $('lbReset').addEventListener('click', () => { step = 0; render(); });
  render();
})();

/* =====================================================================
   §7 Term model: closed terms modulo provable equality
   ===================================================================== */
// Terms are f^n(c) or f^n(d), n <= DMAX. Γ is a set of closed equations; Γ ⊢ t = s iff t, s are
// congruent in the congruence closure (ground equational logic), which we compute by union–find.
const DMAX = 14;
function termName(g, n, short) {
  if (n === 0) return g;
  if (n === 1) return `f(${g})`;
  if (n === 2 && !short) return `f(f(${g}))`;
  return `f${String(n).split('').map(d => '⁰¹²³⁴⁵⁶⁷⁸⁹'[d]).join('')}(${g})`;
}
function congruence(eqs) {
  const N = 2 * (DMAX + 1), id = (g, n) => (g === 'c' ? 0 : DMAX + 1) + n;
  const par = [...Array(N).keys()];
  const find = a => { while (par[a] !== a) { par[a] = par[par[a]]; a = par[a]; } return a; };
  const union = (a, b) => { a = find(a); b = find(b); if (a === b) return false; par[Math.max(a, b)] = Math.min(a, b); return true; };
  eqs.forEach(([g1, n1, g2, n2]) => union(id(g1, n1), id(g2, n2)));
  let changed = true;
  while (changed) {
    changed = false;
    for (let a = 0; a < N; a++) for (let b = a + 1; b < N; b++) {
      const na = a % (DMAX + 1), nb = b % (DMAX + 1);
      if (na < DMAX && nb < DMAX && find(a) === find(b) && union(a + 1, b + 1)) changed = true;
    }
  }
  const cls = (g, n) => find(id(g, n));
  // finite iff both chains are eventually periodic (checked up to DMAX, ample for the small equations used here)
  const periodic = g => { for (let m = 0; m < DMAX; m++) for (let n = m + 1; n <= DMAX; n++) if (cls(g, m) === cls(g, n)) return true; return false; };
  const finite = periodic('c') && periodic('d');
  const all = new Set();
  for (let n = 0; n <= DMAX; n++) { all.add(cls('c', n)); all.add(cls('d', n)); }
  return { cls, finite, size: finite ? all.size : Infinity, id };
}
const TM_COL = ['#3b5bdb', '#e8590c', '#2f9e44', '#ae3ec9', '#c2255c', '#0c8599', '#f08c00', '#5c940d'];
function drawTermModel(svgT, svgM, eqs) {
  const C = congruence(eqs);
  const SHOW = 4;
  const colorOf = new Map();
  ['c', 'd'].forEach(g => { for (let n = 0; n <= SHOW; n++) { const k = C.cls(g, n); if (!colorOf.has(k)) colorOf.set(k, TM_COL[colorOf.size % TM_COL.length]); } });
  const members = new Map();
  ['c', 'd'].forEach((g, gi) => { for (let n = 0; n <= SHOW; n++) { const k = C.cls(g, n); if (!members.has(k)) members.set(k, []); members.get(k).push([gi, n]); } });
  // left: the grid of closed terms; same class = same colour, joined by a band
  svgT.innerHTML = '';
  svgT.setAttribute('viewBox', '0 0 700 280');
  const px = n => 54 + n * 118, py = gi => 84 + gi * 120;
  members.forEach((ms, k) => {
    if (ms.length < 2) return;
    const col = colorOf.get(k);
    for (let i = 0; i + 1 < ms.length; i++) {
      const [g1, n1] = ms[i], [g2, n2] = ms[i + 1];
      const x1 = px(n1), y1 = py(g1), x2 = px(n2), y2 = py(g2);
      const up = 44 + (n2 - n1) * 6;
      const d = g1 === g2 ? `M${x1},${y1 - 16} C${x1},${y1 - 16 - up} ${x2},${y2 - 16 - up} ${x2},${y2 - 16}` : `M${x1},${y1 + 16} C${x1},${(y1 + y2) / 2} ${x2},${(y1 + y2) / 2} ${x2},${y2 - 16}`;
      const p = el('path', { d, fill: 'none', stroke: col, 'stroke-width': 6, opacity: .4, 'stroke-linecap': 'round', class: 'fadein' }, svgT);
      p.style.animationDelay = (i * 0.12) + 's';
    }
  });
  ['c', 'd'].forEach((g, gi) => {
    for (let n = 0; n <= SHOW; n++) {
      const k = C.cls(g, n), col = colorOf.get(k), multi = members.get(k).length > 1;
      const gg = el('g', { class: 'pop' }, svgT);
      gg.style.animationDelay = (n * 0.05) + 's';
      el('rect', { x: px(n) - 44, y: py(gi) - 16, width: 88, height: 32, rx: 10, fill: multi ? col : '#fff', 'fill-opacity': multi ? .18 : 1, stroke: col, 'stroke-width': 2 }, gg);
      svgText(gg, px(n), py(gi) + 5, termName(g, n), { 'font-size': 14, 'font-weight': 700 });
      if (n < SHOW) el('line', { x1: px(n) + 46, y1: py(gi), x2: px(n + 1) - 46, y2: py(gi), stroke: '#ddd', 'stroke-width': 1.5 }, svgT);
    }
    svgText(svgT, px(SHOW) + 62, py(gi) + 5, '…', { 'font-size': 16, fill: '#999' });
  });
  svgBi(svgT, 20, 252, 'closed terms (depth ≤ 4 shown); same colour = same class', '闭项（只画深度 ≤ 4）；同色 = 同一等价类', { anchor: 'start', size: 13, weight: 700, fill: '#6b7280' }, 17);
  // right: the quotient structure
  svgM.innerHTML = '';
  svgM.setAttribute('viewBox', '0 0 520 300');
  const mk = marker(svgM, '#ae3ec9');
  const placed = new Map(), edges = [], ROWY = [92, 196], used = [0, 0];
  ['c', 'd'].forEach((g, gi) => {
    let prev = null;
    for (let n = 0; n <= DMAX; n++) {
      const k = C.cls(g, n);
      if (placed.has(k)) { if (prev !== null) edges.push([prev, k]); break; }
      if (used[gi] >= 5) { placed.set('more' + gi, { x: 46 + used[gi] * 84 - 20, y: ROWY[gi], more: true }); edges.push([prev, 'more' + gi]); break; }
      placed.set(k, { x: 46 + used[gi] * 84, y: ROWY[gi], k, label: termName(g, n, true) });
      used[gi]++;
      if (prev !== null) edges.push([prev, k]);
      prev = k;
    }
  });
  edges.forEach(([a, b]) => {
    const A = placed.get(a), B = placed.get(b);
    if (a === b) {
      el('path', { d: `M${A.x - 10},${A.y - 24} C${A.x - 34},${A.y - 72} ${A.x + 34},${A.y - 72} ${A.x + 10},${A.y - 24}`, fill: 'none', stroke: '#ae3ec9', 'stroke-width': 2, 'marker-end': mk }, svgM);
      return;
    }
    let d;
    if (A.y === B.y && B.x > A.x) d = `M${A.x + 27},${A.y} L${B.x - (B.more ? 14 : 29)},${B.y}`;
    else if (A.y === B.y) {
      const dir = A.y === ROWY[0] ? -1 : 1;
      d = `M${A.x},${A.y + dir * 27} C${A.x},${A.y + dir * 80} ${B.x},${B.y + dir * 80} ${B.x + 4},${B.y + dir * 29}`;
    } else {
      const dx = B.x - A.x, dy = B.y - A.y, L = Math.hypot(dx, dy), ux = dx / L, uy = dy / L;
      d = `M${A.x + ux * 27},${A.y + uy * 27} L${B.x - ux * 30},${B.y - uy * 30}`;
    }
    el('path', { d, fill: 'none', stroke: '#ae3ec9', 'stroke-width': 2, 'marker-end': mk }, svgM);
  });
  placed.forEach(P => {
    const g = el('g', { class: 'pop' }, svgM);
    if (P.more) { svgText(g, P.x, P.y + 6, '⋯', { 'font-size': 22, fill: '#999' }); return; }
    const col = colorOf.get(P.k) || '#999';
    el('circle', { cx: P.x, cy: P.y, r: 26, fill: col, 'fill-opacity': .18, stroke: col, 'stroke-width': 2.5 }, g);
    svgText(g, P.x, P.y + 5, `[${P.label}]`, { 'font-size': P.label.length > 4 ? 12 : 13, 'font-weight': 700 });
  });
  svgBi(svgM, 16, 268, `term model 𝔄: ${C.finite ? C.size + ' element' + (C.size > 1 ? 's' : '') : 'infinite (ℵ₀ elements)'} · arrows = f^𝔄`, `项模型 𝔄：${C.finite ? C.size + ' 个元素' : '无穷（ℵ₀ 个元素）'} · 箭头 = f^𝔄`, { anchor: 'start', size: 13, weight: 700, fill: '#6b7280' }, 17);
  return C;
}
const TM_EQS = {
  e1: ['f(c) = d', ['c', 1, 'd', 0]],
  e2: ['f(f(c)) = c', ['c', 2, 'c', 0]],
  e3: ['f(d) = d', ['d', 1, 'd', 0]],
  e4: ['c = d', ['c', 0, 'd', 0]],
  e5: ['f³(d) = f(d)', ['d', 3, 'd', 1]],
};
(function termModel() {
  const on = new Set(['e2']);
  const box = $('tmEqs');
  Object.keys(TM_EQS).forEach(k => {
    const b = document.createElement('button');
    b.className = 'btn small';
    b.innerHTML = `<span class="m">${TM_EQS[k][0]}</span>`;
    b.addEventListener('click', () => { on.has(k) ? on.delete(k) : on.add(k); render(); });
    b.dataset.k = k;
    box.appendChild(b);
  });
  function render() {
    box.querySelectorAll('button').forEach(b => b.classList.toggle('sel', on.has(b.dataset.k)));
    const eqs = [...on].map(k => TM_EQS[k][1]);
    const C = drawTermModel($('tmTerms'), $('tmModel'), eqs);
    const G = [...on].map(k => TM_EQS[k][0]);
    $('tmInfo').innerHTML = bi(`Γ = {${G.join(', ')}}. Same colour = provably equal from Γ (the equality axioms make ∼ an equivalence relation and a <b>congruence</b>: if t ∼ s then f(t) ∼ f(s)). The term model has <b>${C.finite ? C.size : 'infinitely many (ℵ₀)'}</b> element${C.size === 1 ? '' : 's'}.`,
      `Γ = {${G.join(', ')}}。同色 = 由 Γ 可证相等（等词公理保证 ∼ 是等价关系，而且是<b>同余关系</b>：若 t ∼ s 则 f(t) ∼ f(s)）。项模型有 <b>${C.finite ? C.size : '无穷多（ℵ₀）'}</b> 个元素。`);
    $('tmInfo').className = 'msg info';
  }
  render();
  const steps = [...document.querySelectorAll('#tlSteps .step')];
  let k = 0;
  $('tlNext').addEventListener('click', () => { if (k < steps.length) steps[k++].classList.add('on'); });
  $('tlAll').addEventListener('click', () => { steps.forEach(s => s.classList.add('on')); k = steps.length; });
})();

/* =====================================================================
   §8 Corollaries: compactness and recursive enumerability
   ===================================================================== */
(function compactMini() {
  const svg = $('cpSvg');
  const N = 12, X0 = 40, DX = 66;
  function base() {
    svg.innerHTML = '';
    for (let i = 0; i < N; i++) {
      const g = el('g', { id: 'cpg' + i }, svg);
      el('rect', { x: X0 + i * DX - 26, y: 20, width: 52, height: 30, rx: 9, fill: '#e7ecff', stroke: '#3b5bdb' }, g);
      svgText(g, X0 + i * DX, 40, 'γ' + sub(i), { 'font-size': 15, 'font-weight': 700 });
    }
    svgText(svg, X0 + N * DX - 12, 40, '⋯', { 'font-size': 20, fill: '#999' });
  }
  base();
  let busy = 0;
  $('cpGo').addEventListener('click', async () => {
    const my = ++busy;
    base();
    const used = shuffle([...Array(N).keys()]).slice(0, 3).sort((a, b) => a - b);
    const tx = 430, ty = 160;
    const tri = el('path', { d: `M${tx},${ty - 46} L${tx - 190},${ty + 50} L${tx + 190},${ty + 50} Z`, fill: '#f8e7fc', stroke: '#ae3ec9', 'stroke-width': 2, class: 'fadein' }, svg);
    svgBi(svg, tx, ty + 18, 'a derivation (finite!)', '一个推导（有限长！）', { size: 14, fill: '#ae3ec9', weight: 700 }, 17);
    svgText(svg, tx, ty + 76, '⊥', { 'font-size': 22, 'font-weight': 800, fill: '#e03131' });
    for (const i of used) {
      await sleep(450);
      if (my !== busy) return;
      svg.querySelector('#cpg' + i + ' rect').setAttribute('fill', '#ffe8a3');
      svg.querySelector('#cpg' + i + ' rect').setAttribute('stroke', '#f08c00');
      const p = el('path', { d: `M${X0 + i * DX},52 C${X0 + i * DX},110 ${tx},70 ${tx},${ty - 48}`, fill: 'none', stroke: '#f08c00', 'stroke-width': 2, class: 'fadein' }, svg);
      p.setAttribute('stroke-dasharray', '5 4');
    }
    void tri;
    okBox($('cpMsg'), bi(`Suppose Γ has no model. By completeness Γ ⊢ ⊥. A derivation is a <b>finite</b> list, so it cites only finitely many hypotheses, here Γ₀ = {${used.map(i => 'γ' + sub(i)).join(', ')}}. So Γ₀ ⊢ ⊥, and by soundness Γ₀ has no model. Contrapositive: <b>if every finite subset of Γ has a model, so does Γ.</b> Lesson 5 is all about the consequences.`,
      `设 Γ 没有模型。由完备性定理 Γ ⊢ ⊥。推导是<b>有限</b>的序列，只引用了有限多个前提，这里是 Γ₀ = {${used.map(i => 'γ' + sub(i)).join(', ')}}。于是 Γ₀ ⊢ ⊥，由可靠性定理 Γ₀ 没有模型。逆否过来：<b>若 Γ 的每个有限子集都有模型，则 Γ 有模型。</b>第 5 课专门讲它的种种推论。`), 'info');
  });
  setTimeout(() => $('cpGo').click(), 300);
})();

(function conveyor() {
  const POOL = [
    { f: '∀xP(x) → P(c)', ax: true, en: 'Q1 instance', zh: 'Q1 实例' },
    { f: '(∀xP(x) → P(c)) → (¬P(c) → ¬∀xP(x))', ax: true, en: 'tautology instance', zh: '重言式实例' },
    { f: '¬P(c) → ¬∀xP(x)', ax: false, en: 'not an axiom', zh: '不是公理' },
    { f: 'x = x', ax: true, en: 'equality axiom E1', zh: '等词公理 E1' },
    { f: 'P(c)', ax: false, en: 'not an axiom', zh: '不是公理' },
    { f: '∀xP(x)', ax: false, en: 'not an axiom', zh: '不是公理' },
  ];
  const nm = i => 'F' + sub(i + 1);
  $('beltPool').innerHTML = POOL.map((p, i) => `<div><b class="m">${nm(i)}</b> <span class="m">${p.f}</span> <span class="muted" style="font-size:12px">${bil(p.en, p.zh)}</span></div>`).join('');
  // candidate n -> sequence over POOL (shortlex)
  function nth(n) {
    let len = 1, cnt = POOL.length;
    while (n >= cnt) { n -= cnt; len++; cnt *= POOL.length; }
    const seq = [];
    for (let i = 0; i < len; i++) { seq.unshift(n % POOL.length); n = Math.floor(n / POOL.length); }
    return seq;
  }
  // a genuine (tiny) proof checker: each line is an axiom or follows by MP from two earlier lines
  function check(seq) {
    const lines = seq.map(i => POOL[i].f);
    for (let k = 0; k < seq.length; k++) {
      if (POOL[seq[k]].ax) continue;
      const B = lines[k];
      let ok = false;
      for (let i = 0; i < k && !ok; i++) for (let j = 0; j < k && !ok; j++) if (lines[j] === `(${lines[i]}) → (${B})` || lines[j] === `${lines[i]} → ${B}` || lines[j] === `(${lines[i]}) → ${B}`) ok = true;
      if (!ok) return { ok: false, bad: k };
    }
    return { ok: true };
  }
  const svg = $('belt');
  let n = 0, found = new Map();
  function frame() {
    svg.innerHTML = '';
    el('rect', { x: 0, y: 118, width: 900, height: 14, fill: '#d8d3c4' }, svg);
    for (let x = 6; x < 900; x += 26) el('circle', { cx: x, cy: 125, r: 3, fill: '#bdb6a3' }, svg);
    el('rect', { x: 560, y: 30, width: 120, height: 86, rx: 12, fill: '#1f2430' }, svg);
    svgBi(svg, 620, 62, 'proof checker', '证明检查器', { size: 13, fill: '#fff', weight: 700 }, 18);
    el('rect', { x: 740, y: 150, width: 150, height: 80, rx: 12, fill: '#d3f9d8', stroke: '#2f9e44' }, svg);
    svgBi(svg, 815, 178, 'theorems ⊢ σ', '定理 ⊢ σ', { size: 13, fill: '#1b5e20', weight: 700 }, 18);
    el('rect', { x: 740, y: 30, width: 150, height: 80, rx: 12, fill: '#f1efe7', stroke: '#c9c4b5' }, svg);
    svgBi(svg, 815, 62, 'rejected', '不合格', { size: 13, fill: '#6b7280', weight: 700 }, 18);
    svgText(svg, 20, 24, `#${n}`, { 'text-anchor': 'start', 'font-size': 13, fill: '#6b7280' });
    for (let q = 1; q <= 3; q++) card(nth(n + q), 470 - q * 140, 'queued');
    return card(nth(n), 470);
  }
  function card(seq, x, cls) {
    const g = el('g', { class: 'bcard ' + (cls || '') }, svg);
    const w = 22 + seq.length * 34;
    el('rect', { x: -w / 2, y: -20, width: w, height: 40, rx: 8, fill: '#fff', stroke: '#1f2430', 'stroke-width': 1.5 }, g);
    svgText(g, 0, 6, seq.map(nm).join(' '), { 'font-size': 14, 'font-weight': 700 });
    g.style.transform = `translate(${x}px,96px)`;
    return g;
  }
  async function stepOnce(fast) {
    const seq = nth(n);
    const c = frame();
    const res = check(seq);
    await sleep(fast ? 60 : 350);
    c.style.transition = `transform ${fast ? .15 : .45}s ease`;
    c.style.transform = 'translate(620px,96px)';
    await sleep(fast ? 170 : 500);
    const stamp = svgText(svg, 620, 150, res.ok ? '✓' : '✗', { 'font-size': 30, 'font-weight': 800, fill: res.ok ? '#2f9e44' : '#e03131', class: 'pop' });
    void stamp;
    await sleep(fast ? 60 : 300);
    c.style.transform = res.ok ? 'translate(815px,206px) scale(.7)' : 'translate(815px,86px) scale(.7)';
    if (res.ok) {
      const concl = POOL[seq[seq.length - 1]].f;
      if (!found.has(concl)) {
        found.set(concl, n);
        $('beltBin').innerHTML = [...found].map(([f, k]) => `<div class="fadein"><span class="m">⊢ ${f}</span> <span class="muted" style="font-size:12px">${bil(`(candidate #${k})`, `（第 ${k} 号候选）`)}</span></div>`).join('');
      }
    }
    const why = res.ok ? bi(`#${n}: ${seq.map(nm).join(', ')} is a correct derivation; its last line goes to the theorem bin.`, `#${n}：${seq.map(nm).join(', ')} 是正确的推导，最后一行进入定理箱。`)
      : bi(`#${n}: line ${res.bad + 1} (${nm(seq[res.bad])}) is neither an axiom nor obtained by MP from earlier lines.`, `#${n}：第 ${res.bad + 1} 行（${nm(seq[res.bad])}）既不是公理，也不能由前面的行用 MP 得到。`);
    $('beltMsg').innerHTML = why;
    $('beltMsg').className = 'msg ' + (res.ok ? 'ok' : 'info');
    n++;
  }
  let running = false;
  async function loop() {
    while (running) {
      await stepOnce($('beltFast').checked);
      await sleep($('beltFast').checked ? 40 : 400);
      if (n > 258) { running = false; $('beltGo').innerHTML = bi('Run ▶', '运行 ▶'); }
    }
  }
  $('beltGo').addEventListener('click', () => {
    running = !running;
    $('beltGo').innerHTML = running ? bi('Pause ❚❚', '暂停 ❚❚') : bi('Run ▶', '运行 ▶');
    if (running) loop();
  });
  $('beltStep').addEventListener('click', () => { if (!running) stepOnce(false); });
  $('beltReset').addEventListener('click', () => { running = false; $('beltGo').innerHTML = bi('Run ▶', '运行 ▶'); n = 0; found = new Map(); $('beltBin').innerHTML = ''; clearBox($('beltMsg')); frame(); });
  frame();
})();

/* =====================================================================
   §9 Complete theory vs completeness theorem
   ===================================================================== */
function drawOrder(svg, kind) {
  svg.innerHTML = '';
  svg.setAttribute('viewBox', '0 0 230 44');
  svg.setAttribute('width', 230);
  svg.setAttribute('height', 44);
  el('line', { x1: 10, x2: 220, y1: 22, y2: 22, stroke: '#ccc' }, svg);
  const dot = (x, big) => el('circle', { cx: x, cy: 22, r: big ? 6 : 4.5, fill: big ? '#e03131' : '#1f2430' }, svg);
  if (kind === 'N') { for (let i = 0; i < 8; i++) dot(24 + i * 24, i === 0); svgText(svg, 214, 27, '…', { fill: '#999' }); svgText(svg, 24, 42, 'ℕ', { 'font-size': 11, fill: '#999' }); }
  if (kind === 'Z') { svgText(svg, 16, 27, '…', { fill: '#999' }); for (let i = 0; i < 8; i++) dot(36 + i * 23); svgText(svg, 214, 27, '…', { fill: '#999' }); svgText(svg, 115, 42, 'ℤ', { 'font-size': 11, fill: '#999' }); }
  if (kind === 'Q') { svgText(svg, 16, 27, '…', { fill: '#999' }); for (let i = 0; i < 60; i++) el('line', { x1: 32 + i * 2.8 + (i % 3) * 0.4, x2: 32 + i * 2.8 + (i % 3) * 0.4, y1: 16, y2: 28, stroke: '#3b5bdb', 'stroke-width': 1 }, svg); svgText(svg, 214, 27, '…', { fill: '#999' }); svgText(svg, 115, 42, 'ℚ', { 'font-size': 11, fill: '#999' }); }
  if (kind === 'one') { dot(115, true); svgText(svg, 115, 42, '{0}', { 'font-size': 11, fill: '#999' }); }
}
(function completeTheories() {
  const sents = [
    { s: '∃x∀y(x ≤ y)', en: 'has a least element', zh: '有最小元' },
    { s: '∀x∀y(x < y → ∃z(x < z ∧ z < y))', en: 'dense', zh: '稠密' },
    { s: '∀x∃y(x < y)', en: 'no greatest element', zh: '无最大元' },
    { s: '∃x∃y(x ≠ y)', en: 'at least 2 elements', zh: '至少 2 个元素' },
  ];
  // per theory: for each sentence: 'T' (proves), 'F' (refutes), or [modelTrue, modelFalse]
  const th = [
    { n: 'LO', en: 'linear orders', zh: '线序理论', c: [['N', 'Z'], ['Q', 'Z'], ['N', 'one'], ['N', 'one']] },
    { n: 'DLO', en: 'dense linear orders without endpoints (nonempty)', zh: '无端点稠密线序（非空）', c: ['F', 'T', 'T', 'T'] },
    { n: 'Th(ℕ,<)', en: 'all sentences true in (ℕ,<)', zh: '(ℕ,<) 中所有真语句', c: ['T', 'F', 'T', 'T'] },
  ];
  const revealed = new Set();
  function render() {
    let h = `<table class="tt ctab"><colgroup><col style="width:21%">${sents.map(() => '<col style="width:17%">').join('')}<col style="width:11%"></colgroup><tr><th></th>${sents.map(s => `<th><span class="m">${s.s}</span><div style="font-weight:400;font-size:12px">${bil(s.en, s.zh)}</div></th>`).join('')}<th>${bil('complete?', '完全？')}</th></tr>`;
    th.forEach((t, i) => {
      h += `<tr><th style="text-align:left"><span class="m">${t.n}</span><div style="font-weight:400;font-size:12px">${bil(t.en, t.zh)}</div></th>`;
      t.c.forEach((c, j) => {
        const key = i + ',' + j;
        if (!revealed.has(key)) { h += `<td class="click ccell" data-k="${key}">?</td>`; return; }
        const txt = c === 'T' ? `<b class="tv1">T ⊢ σ</b>` : c === 'F' ? `<b class="tv0">T ⊢ ¬σ</b>` : `<b style="color:var(--gold)">${bil('neither', '都不')}</b>`;
        h += `<td class="ccell shown" data-k="${key}">${txt}</td>`;
      });
      const allRev = t.c.every((_, j) => revealed.has(i + ',' + j));
      const complete = t.c.every(c => typeof c === 'string');
      h += `<td>${allRev ? (complete ? `<b class="tv1">✓ ${bil('complete', '完全')}</b>` : `<b class="tv0">✗ ${bil('incomplete', '不完全')}</b>`) : ''}</td></tr>`;
    });
    $('ctGrid').innerHTML = h + '</table>';
    $('ctGrid').querySelectorAll('.ccell').forEach(td => td.addEventListener('click', () => { revealed.add(td.dataset.k); render(); detail(td.dataset.k); }));
  }
  function detail(key) {
    const [i, j] = key.split(',').map(Number), t = th[i], c = t.c[j], s = sents[j];
    const box = $('ctDetail');
    if (typeof c === 'string') {
      box.innerHTML = bi(`<b>${t.n}</b> ${c === 'T' ? 'proves' : 'refutes'} <span class="m">${s.s}</span>: every model of ${t.n} ${c === 'T' ? 'satisfies' : 'falsifies'} it, so by the completeness theorem there is a derivation of ${c === 'T' ? 'σ' : '¬σ'}.`,
        `<b>${t.n}</b> ${c === 'T' ? '证明' : '否证'}了 <span class="m">${s.s}</span>：${t.n} 的每个模型都使它${c === 'T' ? '为真' : '为假'}，由完备性定理，存在 ${c === 'T' ? 'σ' : '¬σ'} 的推导。`);
      box.className = 'msg ok';
      return;
    }
    box.className = 'msg warn';
    box.innerHTML = bi(`<b>${t.n}</b> decides nothing about “${s.en}”: here are two models of ${t.n}, one where it holds and one where it fails. By <b>soundness</b>, neither σ nor ¬σ is provable.`,
      `<b>${t.n}</b> 对“${s.zh}”无法判定：下面是 ${t.n} 的两个模型，一个使它成立，一个使它不成立。由<b>可靠性定理</b>，σ 与 ¬σ 都不可证。`) +
      `<div class="row" style="margin-top:8px"><div><b class="tv1">⊨ σ</b><svg id="ctA"></svg></div><div><b class="tv0">⊭ σ</b><svg id="ctB"></svg></div></div>`;
    drawOrder($('ctA'), c[0]);
    drawOrder($('ctB'), c[1]);
  }
  $('ctAll').addEventListener('click', () => { th.forEach((t, i) => t.c.forEach((_, j) => revealed.add(i + ',' + j))); render(); });
  render();
})();

/* =====================================================================
   Exercises
   ===================================================================== */
/* ---------- E1 substitutable? ---------- */
(function e1() {
  const items = [
    ['∀yR(x,y)', 'x', 'f(y)'],
    ['∀yR(x,y)', 'x', 'f(z)'],
    ['∃xP(x) ∧ Q(x)', 'x', 'y'],
    ['∀z(P(z) → ∃yR(y,x))', 'x', 'g(y,z)'],
    ['∀xR(x,y)', 'y', 'x'],
    ['∀y(P(y) → P(x))', 'y', 'x'],
    ['∃y(x = y)', 'x', 'c'],
  ];
  const solved = items.map(() => false), revealed = items.map(() => false);
  const box = $('e1List');
  items.forEach((it, i) => {
    const phi = foParse(it[0]), t = foParseTerm(it[2]);
    const caps = captures(phi, it[1], t), ok = caps.length === 0;
    const res = foShow(substF(phi, it[1], t));
    const hasFree = freeVars(phi).has(it[1]);
    const row = document.createElement('div');
    row.className = 'tf';
    row.innerHTML = `<div class="stmt">(${'abcdefg'[i]}) &nbsp; φ = ${foShow(phi)} &nbsp;&nbsp; [${it[2]}/${it[1]}] ?</div>
      <button class="btn small" data-v="1">${bil('substitutable', '可代入')}</button>
      <button class="btn small" data-v="0">${bil('capture!', '会被捕获')}</button>
      <button class="btn small ghost" data-v="show">${bil('Show answer', '看答案')}</button>
      <div style="flex-basis:100%"><div class="msg"></div></div>`;
    box.appendChild(row);
    const explain = () => ok
      ? (hasFree ? bi(`Substitutable. φ[t/${it[1]}] = <span class="m">${res}</span>.`, `可代入。φ[t/${it[1]}] = <span class="m">${res}</span>。`)
        : bi(`Substitutable, trivially: ${it[1]} has no free occurrence in φ (it is bound everywhere or absent), so φ[t/${it[1]}] = φ.`, `可代入，而且是平凡的：${it[1]} 在 φ 中没有自由出现，所以 φ[t/${it[1]}] = φ。`))
      : bi(`Capture by <span class="m">${caps.join(', ')}</span>: the naive result <span class="m">${res}</span> binds a variable of t that was meant to stay free.`, `被 <span class="m">${caps.join('、')}</span> 捕获：直接替换得到 <span class="m">${res}</span>，t 中本应自由的变元被约束了。`);
    row.querySelectorAll('button').forEach(b => b.addEventListener('click', () => {
      const msg = row.querySelector('.msg');
      if (b.dataset.v === 'show') { revealed[i] = true; okBox(msg, explain(), 'info'); return; }
      if ((b.dataset.v === '1') === ok) {
        okBox(msg, '✓ ' + explain());
        if (!revealed[i]) solved[i] = true;
        if (solved.every(Boolean)) Progress.mark('L4E1');
      } else okBox(msg, bi('✗ Look again: find each <i>free</i> occurrence of the variable, then list the quantifiers above it. Does one of them bind a variable of t?', '✗ 再看看：找出该变元的每个<i>自由</i>出现，再看它头上有哪些量词。其中有没有约束 t 中变元的？'), 'bad');
    }));
  });
  $('e1All').addEventListener('click', () => box.querySelectorAll('[data-v="show"]').forEach(b => b.click()));
})();

/* ---------- E2 counterexample builder ---------- */
(function e2() {
  const tasks = [
    { p: ['∀x(P(x) ∨ Q(x))'], c: '∀xP(x) ∨ ∀xQ(x)', show: ['P', 'Q'], ans: () => { const M = emptyStructure(2); M.P = [true, false]; M.Q = [false, true]; return M; } },
    { p: ['∃xP(x)', '∃xQ(x)'], c: '∃x(P(x) ∧ Q(x))', show: ['P', 'Q'], ans: () => { const M = emptyStructure(2); M.P = [true, false]; M.Q = [false, true]; return M; } },
    { p: ['∀x∃yR(x,y)'], c: '∃y∀xR(x,y)', show: ['R'], ans: () => { const M = emptyStructure(2); M.R = [[true, false], [false, true]]; return M; } },
  ];
  const solved = tasks.map(() => false), revealed = tasks.map(() => false);
  let cur = 0, M = emptyStructure(3);
  function tabs() {
    $('e2Tabs').innerHTML = tasks.map((t, i) => `<button class="btn small ${i === cur ? 'sel' : ''}" data-t="${i}">(${'abc'[i]}) ${solved[i] ? '✓' : ''}</button>`).join(' ');
    $('e2Tabs').querySelectorAll('[data-t]').forEach(b => b.addEventListener('click', () => { if (cur !== +b.dataset.t) { cur = +b.dataset.t; M = emptyStructure(3); } render(true); }));
  }
  function render(fromAnswer) {
    tabs();
    const t = tasks[cur], show = new Set(t.show);
    $('e2Goal').innerHTML = `<span class="m" style="font-size:18px">${t.p.map(fo).join(', ')} &nbsp;⊭?&nbsp; ${fo(t.c)}</span>`;
    StructView($('e2Svg'), M, { W: 300, H: 230, show });
    $('e2Legend').innerHTML = structLegend(show);
    // controls
    let h = `<div class="toolbar">${bil('size', '规模')}: ${[1, 2, 3, 4].map(n => `<button class="btn small ${n === M.n ? 'sel' : ''}" data-n="${n}">${n}</button>`).join('')}</div>`;
    h += '<table class="tt rmat"><tr><th></th>';
    if (show.has('P')) h += '<th>P</th>';
    if (show.has('Q')) h += '<th>Q</th>';
    if (show.has('R')) for (let j = 0; j < M.n; j++) h += `<th>R(·,${j})</th>`;
    h += '</tr>';
    for (let i = 0; i < M.n; i++) {
      h += `<tr><th>${i}</th>`;
      ['P', 'Q'].forEach(p => { if (show.has(p)) h += `<td class="click ${M[p][i] ? 'c1' : 'c0'}" data-p="${p}" data-i="${i}">${M[p][i] ? 1 : 0}</td>`; });
      if (show.has('R')) for (let j = 0; j < M.n; j++) h += `<td class="click ${M.R[i][j] ? 'c1' : 'c0'}" data-p="R" data-i="${i}" data-j="${j}">${M.R[i][j] ? 1 : 0}</td>`;
      h += '</tr>';
    }
    $('e2Ctl').innerHTML = h + '</table>';
    $('e2Ctl').querySelectorAll('[data-n]').forEach(b => b.addEventListener('click', () => {
      const old = M; M = emptyStructure(+b.dataset.n);
      for (let i = 0; i < M.n; i++) { if (i < old.n) { M.P[i] = old.P[i]; M.Q[i] = old.Q[i]; for (let j = 0; j < M.n; j++) M.R[i][j] = j < old.n ? old.R[i][j] : false; } }
      render(false);
    }));
    $('e2Ctl').querySelectorAll('td.click').forEach(td => td.addEventListener('click', () => {
      const p = td.dataset.p, i = +td.dataset.i;
      if (p === 'R') M.R[i][+td.dataset.j] = !M.R[i][+td.dataset.j]; else M[p][i] = !M[p][i];
      render(false);
    }));
    const prem = t.p.map(s => sat(foParse(s), M)), concl = sat(foParse(t.c), M);
    $('e2Vals').innerHTML = t.p.map((s, i) => `<div class="evrow"><span class="m">${fo(s)}</span> <b class="${prem[i] ? 'tv1' : 'tv0'}">${prem[i] ? bil('true', '真') : bil('false', '假')}</b></div>`).join('') +
      `<div class="evrow"><span class="m">${fo(t.c)}</span> <b class="${concl ? 'tv1' : 'tv0'}">${concl ? bil('true', '真') : bil('false', '假')}</b></div>`;
    if (prem.every(Boolean) && !concl) {
      okBox($('e2Msg'), bi('✓ Counterexample! All premises true, conclusion false. By soundness, the inference is not derivable either.', '✓ 反例！前提全真、结论为假。由可靠性定理，这个推理也不可推导。'));
      if (fromAnswer === false && !revealed[cur] && !solved[cur]) { solved[cur] = true; tabs(); if (solved.every(Boolean)) Progress.mark('L4E2'); }
    } else okBox($('e2Msg'), bi('Not yet a counterexample: make every premise true and the conclusion false.', '还不是反例：要让每个前提为真、结论为假。'), 'info');
  }
  $('e2Show').addEventListener('click', () => { revealed[cur] = true; M = tasks[cur].ans(); render(true); });
  render(true);
})();

/* ---------- E3 order the Henkin proof ---------- */
(function e3() {
  const steps = [
    { en: 'Assume Γ is consistent; we must build a model.', zh: '设 Γ 一致；要造出一个模型。' },
    { en: 'Add a witness constant c_φ and the Henkin axiom ∃xφ → φ(c_φ) for every ∃xφ, iterating ω times. Still consistent.', zh: '对每个 ∃xφ 加见证常元 c_φ 和亨金公理 ∃xφ → φ(c_φ)，迭代 ω 轮，仍然一致。' },
    { en: 'Extend to a maximal consistent set Γ* (Lindenbaum).', zh: '扩张成极大一致集 Γ*（林登鲍姆引理）。' },
    { en: 'Form the term model: closed terms modulo t ∼ s ⇔ (t = s) ∈ Γ*.', zh: '构造项模型：闭项按 t ∼ s ⇔ (t = s) ∈ Γ* 取商。' },
    { en: 'Prove the truth lemma 𝔄 ⊨ σ ⇔ σ ∈ Γ* by induction on σ.', zh: '对 σ 归纳证明真引理：𝔄 ⊨ σ ⇔ σ ∈ Γ*。' },
    { en: 'Conclude: the reduct of 𝔄 to L is a model of Γ.', zh: '结论：𝔄 在 L 上的约化是 Γ 的模型。' },
  ];
  let order = [], revealed = false;
  const perm = shuffle([...steps.keys()]);
  function render() {
    $('e3Pool').innerHTML = '';
    perm.forEach(i => {
      if (order.includes(i)) return;
      const d = document.createElement('div');
      d.className = 'chip';
      d.innerHTML = bi(steps[i].en, steps[i].zh);
      d.addEventListener('click', () => { order.push(i); render(); });
      $('e3Pool').appendChild(d);
    });
    $('e3Seq').innerHTML = order.length ? order.map((i, k) => `<div class="chip seqchip" data-k="${k}"><b>${k + 1}.</b> ${bil(steps[i].en, steps[i].zh)}</div>`).join('') : `<span class="muted">${bil('Click the cards in the right order.', '按正确顺序点击卡片。')}</span>`;
    $('e3Seq').querySelectorAll('.seqchip').forEach(c => c.addEventListener('click', () => { order.splice(+c.dataset.k, 1); render(); }));
  }
  $('e3Check').addEventListener('click', () => {
    const chips = $('e3Seq').querySelectorAll('.seqchip');
    chips.forEach((c, k) => c.classList.add(order[k] === k ? 'ok' : 'no'));
    if (order.length === steps.length && order.every((v, k) => v === k)) {
      okBox($('e3Msg'), bi('✓ Exactly the Henkin proof. Witnesses must come <i>before</i> Lindenbaum so that Γ* contains the Henkin axioms; the term model needs Γ* to decide every equation.', '✓ 这正是亨金的证明。见证常元必须在林登鲍姆<i>之前</i>加入，这样 Γ* 才包含亨金公理；项模型需要 Γ* 判定每个等式。'));
      if (!revealed) Progress.mark('L4E3');
    } else okBox($('e3Msg'), bi(`${order.filter((v, k) => v === k).length} of ${steps.length} in the right place. Click a card in your sequence to take it back.`, `${order.filter((v, k) => v === k).length}/${steps.length} 个位置正确。点击序列中的卡片可以撤回。`), 'warn');
  });
  $('e3Reset').addEventListener('click', () => { order = []; render(); clearBox($('e3Msg')); });
  $('e3Show').addEventListener('click', () => { revealed = true; order = [...steps.keys()]; render(); okBox($('e3Msg'), bi('The correct order is shown above.', '上面显示的就是正确顺序。'), 'info'); });
  render();
})();

/* ---------- E4 size of term models ---------- */
(function e4() {
  const qs = [
    { eqs: [['c', 1, 'd', 0], ['d', 1, 'c', 0]], g: 'f(c) = d, f(d) = c', ans: 2 },
    { eqs: [['c', 1, 'c', 0]], g: 'f(c) = c', ans: Infinity },
    { eqs: [['c', 3, 'c', 0], ['d', 1, 'c', 0]], g: 'f³(c) = c, f(d) = c', ans: 4 },
  ];
  const solved = qs.map(() => false), revealed = qs.map(() => false);
  const box = $('e4List');
  qs.forEach((q, i) => {
    const C = congruence(q.eqs);
    if (C.size !== q.ans) console.warn('E4 answer mismatch', i);
    const row = document.createElement('div');
    row.className = 'tf';
    row.innerHTML = `<div class="stmt">(${'abc'[i]}) &nbsp; Γ = {${q.g}}</div>
      <input class="formula" style="min-width:90px;width:110px" placeholder="3, ∞ …">
      <button class="btn small" data-a="check">${bil('Check', '检查')}</button>
      <button class="btn small ghost" data-a="show">${bil('Show answer', '看答案')}</button>
      <div style="flex-basis:100%"><div class="msg"></div><div class="row tmmini" style="display:none"><svg width="560" height="224"></svg><svg width="416" height="240"></svg></div></div>`;
    box.appendChild(row);
    const msg = row.querySelector('.msg'), mini = row.querySelector('.tmmini');
    const reveal = () => { mini.style.display = 'flex'; const [a, b] = mini.querySelectorAll('svg'); drawTermModel(a, b, q.eqs); };
    const ansTxt = q.ans === Infinity ? bi('infinitely many (ℵ₀): the d-chain d, f(d), f(f(d)), … never repeats.', '无穷多（ℵ₀）：d 链 d, f(d), f(f(d)), … 永不重复。') : bi(`${q.ans} elements.`, `${q.ans} 个元素。`);
    row.querySelector('[data-a="show"]').addEventListener('click', () => { revealed[i] = true; okBox(msg, ansTxt, 'info'); reveal(); });
    row.querySelector('[data-a="check"]').addEventListener('click', () => {
      const v = row.querySelector('input').value.trim().toLowerCase();
      const inf = ['∞', 'inf', 'infinite', 'infinity', 'ℵ0', 'ℵ₀', 'aleph0', 'aleph_0', 'omega', 'ω', '无穷'].includes(v);
      const got = inf ? Infinity : parseInt(v, 10);
      if (got === q.ans) { okBox(msg, '✓ ' + ansTxt); reveal(); if (!revealed[i]) solved[i] = true; if (solved.every(Boolean)) Progress.mark('L4E4'); }
      else okBox(msg, bi('✗ Not quite. Follow each chain c, f(c), f(f(c)), … and d, f(d), …: when does it come back to an earlier class? Remember congruence: t ∼ s ⇒ f(t) ∼ f(s).', '✗ 不对。沿着 c, f(c), f(f(c)), … 和 d, f(d), … 两条链走：什么时候回到以前的类？别忘了同余性：t ∼ s ⇒ f(t) ∼ f(s)。'), 'bad');
    });
  });
})();

/* ---------- E5 complete vs completeness ---------- */
(function e5() {
  const items = [
    { s: bil('Gödel\'s completeness theorem says every consistent theory is complete.', '哥德尔完备性定理说：每个一致的理论都是完全的。'), ans: false,
      en: 'False. It says every consistent theory has a model (equivalently ⊨ = ⊢). Completeness of a theory means deciding every sentence, a different notion.', zh: '错。它说的是每个一致理论都有模型（等价地 ⊨ = ⊢）。理论的完全性是指判定每个语句，是另一个概念。' },
    { s: bil('Th(𝔐) is complete for every structure 𝔐.', '对任意结构 𝔐，Th(𝔐) 都是完全的。'), ans: true,
      en: 'True. For each σ, either 𝔐 ⊨ σ or 𝔐 ⊨ ¬σ, and Th(𝔐) contains whichever holds.', zh: '对。对每个 σ，要么 𝔐 ⊨ σ，要么 𝔐 ⊨ ¬σ，成立的那个就在 Th(𝔐) 中。' },
    { s: bil('The theory of groups is complete.', '群论是完全理论。'), ans: false,
      en: 'False. ∀x∀y(x·y = y·x) holds in ℤ but fails in S₃, so neither it nor its negation is provable.', zh: '错。∀x∀y(x·y = y·x) 在 ℤ 中成立而在 S₃ 中不成立，所以它和它的否定都不可证。' },
    { s: bil('If T is complete and consistent, any two models of T satisfy exactly the same sentences.', '若 T 完全且一致，则 T 的任意两个模型满足完全相同的语句。'), ans: true,
      en: 'True. If T ⊢ σ both models satisfy σ; if T ⊢ ¬σ neither does (soundness).', zh: '对。若 T ⊢ σ，两个模型都满足 σ；若 T ⊢ ¬σ，都不满足（可靠性）。' },
    { s: bil('Gödel\'s incompleteness theorem contradicts his completeness theorem.', '哥德尔不完全性定理与他的完备性定理相矛盾。'), ans: false,
      en: 'False. Incompleteness: PA (assumed consistent) is not a complete theory (some σ is undecided). Completeness theorem: then PA has models of σ and of ¬σ. They fit together perfectly.', zh: '错。不完全性定理：（假定 PA 一致）PA 不是完全理论（有不可判定的 σ）。完备性定理：于是 PA 既有使 σ 真的模型，也有使 ¬σ 真的模型。两者完全相容。' },
    { s: bil('If T ⊬ σ and T ⊬ ¬σ, then T has a model of σ and a model of ¬σ.', '若 T ⊬ σ 且 T ⊬ ¬σ，则 T 既有满足 σ 的模型，也有满足 ¬σ 的模型。'), ans: true,
      en: 'True. T ⊬ σ ⇒ T ∪ {¬σ} consistent ⇒ (completeness) it has a model. Same for ¬σ.', zh: '对。T ⊬ σ ⇒ T ∪ {¬σ} 一致 ⇒（完备性定理）它有模型。¬σ 同理。' },
  ];
  const solved = items.map(() => false), revealed = items.map(() => false);
  const box = $('e5List');
  items.forEach((it, i) => {
    const row = document.createElement('div');
    row.className = 'tf';
    row.innerHTML = `<div class="stmt" style="font-family:var(--sans)">(${'abcdef'[i]}) ${it.s}</div>
      <button class="btn small" data-v="1">${bil('True', '对')}</button>
      <button class="btn small" data-v="0">${bil('False', '错')}</button>
      <button class="btn small ghost" data-v="show">${bil('Show answer', '看答案')}</button>
      <div style="flex-basis:100%"><div class="msg"></div></div>`;
    box.appendChild(row);
    row.querySelectorAll('button').forEach(b => b.addEventListener('click', () => {
      const msg = row.querySelector('.msg');
      if (b.dataset.v === 'show') { revealed[i] = true; okBox(msg, bi(it.en, it.zh), 'info'); return; }
      if ((b.dataset.v === '1') === it.ans) {
        okBox(msg, '✓ ' + bi(it.en, it.zh));
        if (!revealed[i]) solved[i] = true;
        if (solved.every(Boolean)) Progress.mark('L4E5');
      } else okBox(msg, bi('✗ Not quite. Keep the two words apart: a <i>theory</i> can be complete; the <i>proof system</i> is complete.', '✗ 不对。把两个词分开：<i>理论</i>可以是完全的；<i>证明系统</i>是完备的。'), 'bad');
    }));
  });
})();

/* ---------- E6 find the bug ---------- */
(function e6() {
  const bugs = [
    { goal: '∀x∃y(y ≠ x) ⊢ ∃y(y ≠ y) ???', bad: 1, lines: [
      { f: '∀x∃y(y ≠ x)', j: bil('hypothesis', '假设'), cites: [] },
      { f: '∀x∃y(y ≠ x) → ∃y(y ≠ y)', j: bil('Q1 with t = y', 'Q1，取 t = y'), cites: [] },
      { f: '∃y(y ≠ y)', j: 'MP 1, 2', cites: [0, 1] },
    ], en: 'Line 2: y is not substitutable for x in ∃y(y ≠ x): the new y is captured by ∃y. In a 2-element structure the hypothesis is true and the “conclusion” false.',
      zh: '第 2 行：在 ∃y(y ≠ x) 中 y 对 x 不可代入，新的 y 被 ∃y 捕获。在 2 元结构中假设为真而“结论”为假。' },
    { goal: '∀x(P(x) → Q(x)), P(x) ⊢ ∀xQ(x) ???', bad: 5, lines: [
      { f: '∀x(P(x) → Q(x))', j: bil('hypothesis', '假设'), cites: [] },
      { f: '∀x(P(x) → Q(x)) → (P(x) → Q(x))', j: bil('Q1 with t = x', 'Q1，取 t = x'), cites: [] },
      { f: 'P(x) → Q(x)', j: 'MP 1, 2', cites: [0, 1] },
      { f: 'P(x)', j: bil('hypothesis', '假设'), cites: [] },
      { f: 'Q(x)', j: 'MP 3, 4', cites: [2, 3] },
      { f: '∀xQ(x)', j: 'Gen 5', cites: [4] },
    ], en: 'Line 6: Gen on x, but x is free in the hypothesis P(x). Counterexample: P = Q = {0} in {0,1} with s(x) = 0.',
      zh: '第 6 行：对 x 概括，可 x 在假设 P(x) 中自由出现。反例：论域 {0,1}，P = Q = {0}，s(x) = 0。' },
    { goal: '∀x(P(x) → Q(x)) ⊢ P(x) → ∀xQ(x) ???', bad: 1, lines: [
      { f: '∀x(P(x) → Q(x))', j: bil('hypothesis', '假设'), cites: [] },
      { f: '∀x(P(x) → Q(x)) → (P(x) → ∀xQ(x))', j: 'Q2', cites: [] },
      { f: 'P(x) → ∀xQ(x)', j: 'MP 1, 2', cites: [0, 1] },
    ], en: 'Line 2: Q2 requires x not free in the antecedent φ, but φ = P(x). Counterexample: P = Q = {0} in {0,1}, s(x) = 0.',
      zh: '第 2 行：Q2 要求 x 在前件 φ 中不自由出现，但这里 φ = P(x)。反例：论域 {0,1}，P = Q = {0}，s(x) = 0。' },
  ];
  const solved = bugs.map(() => false), revealed = bugs.map(() => false);
  bugs.forEach((B, i) => {
    const wrap = document.createElement('div');
    wrap.className = 'bugbox';
    wrap.innerHTML = `<div class="m" style="font-weight:700;margin:6px 0">(${'abc'[i]}) ${B.goal}</div><div class="pbox"></div>
      <div class="toolbar"><button class="btn small ghost">${bil('Show answer', '看答案')}</button></div><div class="msg"></div>`;
    $('e6List').appendChild(wrap);
    const msg = wrap.querySelector('.msg');
    let pv;
    pv = ProofView(wrap.querySelector('.pbox'), B.lines, {
      allShown: true,
      onRow: (k, row) => {
        pv.rows.forEach(r => r.classList.remove('bugpick', 'okpick'));
        if (k === B.bad) {
          row.classList.add('bugpick');
          okBox(msg, '✓ ' + bi(B.en, B.zh));
          if (!revealed[i]) solved[i] = true;
          if (solved.every(Boolean)) Progress.mark('L4E6');
        } else {
          row.classList.add('okpick');
          okBox(msg, bi(`Line ${k + 1} is fine. Check the side conditions of Q1, Q2 and Gen.`, `第 ${k + 1} 行没问题。检查 Q1、Q2 和 Gen 的附加条件。`), 'bad');
        }
      },
    });
    wrap.querySelector('button').addEventListener('click', () => {
      revealed[i] = true;
      pv.rows.forEach(r => r.classList.remove('bugpick', 'okpick'));
      pv.rows[B.bad].classList.add('bugpick');
      okBox(msg, bi(B.en, B.zh), 'info');
    });
  });
})();
