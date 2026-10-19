// Lesson 15: Gödel's constructible universe L.
// Pure part first (hereditarily finite sets and a small first-order evaluator, shared in spirit with lesson14.js,
// plus Def(X) and the toy <_L ladder); exported for node unit tests. DOM code runs only in the browser.

/* ===================================================================== */
/* ======================  pure: hereditarily finite sets  ============== */
/* ===================================================================== */
class HFError extends Error {
  constructor(en, zh) { super(en); this.en = en; this.zh = zh; }
  html() { return bi(this.en, this.zh); }
}

const HF = (() => {
  const pool = new Map();       // canonical key -> node {k, e (sorted elements), r (rank)}
  const codeCache = new Map();
  // Ackermann code (BigInt): code(x) = Σ_{y∈x} 2^code(y). Defined for rank ≤ 5 only.
  function code(x) {
    if (x.r > 5) return null;
    if (codeCache.has(x.k)) return codeCache.get(x.k);
    let c = 0n;
    for (const y of x.e) c += 1n << code(y);
    codeCache.set(x.k, c);
    return c;
  }
  function cmp(a, b) {
    if (a.r !== b.r) return a.r - b.r;
    if (a.r <= 5) { const ca = code(a), cb = code(b); return ca < cb ? -1 : ca > cb ? 1 : 0; }
    return a.k < b.k ? -1 : a.k > b.k ? 1 : 0;
  }
  function mk(els) {
    const u = new Map();
    for (const e of els) u.set(e.k, e);
    const arr = [...u.values()].sort(cmp);
    const k = '{' + arr.map(e => e.k).join(',') + '}';
    let n = pool.get(k);
    if (!n) {
      n = { k, e: arr, r: arr.reduce((m, y) => Math.max(m, y.r + 1), 0) };
      pool.set(k, n);
    }
    return n;
  }
  const EMPTY = mk([]);
  const ords = [EMPTY];
  function ord(n) { while (ords.length <= n) ords.push(mk(ords.slice())); return ords[n]; }
  const isOrd = x => x === ord(x.r);           // an HF ordinal of rank n is exactly n
  const mem = (y, x) => x.e.includes(y);        // y ∈ x  (nodes are interned)
  function show(x, num = false) {
    if (x === EMPTY) return '∅';
    if (num && isOrd(x)) return String(x.r);
    return '{' + x.e.map(y => show(y, num)).join(', ') + '}';
  }
  // Parser: ∅ | Ø | {} | digit(s) n (von Neumann ordinal, n ≤ 7) | { set, set, ... }
  function parse(s) {
    let i = 0;
    const ws = () => { while (i < s.length && /\s/.test(s[i])) i++; };
    function set(depth) {
      ws();
      if (depth > 14) throw new HFError('Nested too deeply', '嵌套层数太多');
      if (i >= s.length) throw new HFError('Input ends too early: a set is missing', '输入提前结束：缺少一个集合');
      const c = s[i];
      if (c === '∅' || c === 'Ø') { i++; return EMPTY; }
      if (/[0-9]/.test(c)) {
        let j = i;
        while (j < s.length && /[0-9]/.test(s[j])) j++;
        const n = +s.slice(i, j);
        if (n > 7) throw new HFError(`Ordinal ${n} is too big for this tool (max 7)`, `序数 ${n} 太大（本工具最多到 7）`);
        i = j;
        return ord(n);
      }
      if (c === '{') {
        i++; ws();
        const els = [];
        if (s[i] === '}') { i++; return EMPTY; }
        for (;;) {
          els.push(set(depth + 1));
          ws();
          if (s[i] === ',') { i++; continue; }
          if (s[i] === '}') { i++; break; }
          if (i >= s.length) throw new HFError('Missing “}”', '缺少右花括号“}”');
          throw new HFError(`Unexpected “${s[i]}”: expected “,” or “}”`, `此处不应出现“${s[i]}”：应为“,”或“}”`);
        }
        return mk(els);
      }
      throw new HFError(`Unexpected “${c}”: use ∅, digits, braces and commas`, `无法识别“${c}”：只能用 ∅、数字、花括号和逗号`);
    }
    const x = set(0);
    ws();
    if (i < s.length) throw new HFError('Extra symbols after the set', '集合后面多出了符号');
    return x;
  }
  // V_n as a sorted list (n ≤ 5)
  function V(n) {
    if (n > 5) throw new Error('V(n) only for n ≤ 5');
    let cur = [];
    for (let k = 0; k < n; k++) {
      const m = cur.length, next = [];
      for (let mask = 0; mask < 2 ** m; mask++) next.push(mk(cur.filter((_, j) => Math.floor(mask / 2 ** j) % 2)));
      cur = next.sort(cmp);
    }
    return cur;
  }
  // {x} ∪ TC(x), sorted by rank
  function tc(x) {
    const seen = new Map();
    (function go(y) { if (seen.has(y.k)) return; seen.set(y.k, y); y.e.forEach(go); })(x);
    return [...seen.values()].sort(cmp);
  }
  // a longest ∈-chain  x ∋ y₁ ∋ … ∋ ∅
  function chain(x) {
    const out = [x];
    let y = x;
    while (y.r > 0) { const r = y.r; y = y.e.find(z => z.r === r - 1); out.push(y); }
    return out;
  }
  const pair = (a, b) => mk([a, b]);
  const union = a => mk(a.e.flatMap(y => y.e));
  const cup = (a, b) => mk([...a.e, ...b.e]);
  const succ = a => mk([...a.e, a]);
  function power(a) {
    if (a.e.length > 6) return null;
    const out = [], m = a.e.length;
    for (let mask = 0; mask < 2 ** m; mask++) out.push(mk(a.e.filter((_, j) => Math.floor(mask / 2 ** j) % 2)));
    return mk(out);
  }
  const transitive = (M) => { const S = new Set(M); return M.every(y => y.e.every(z => S.has(z))); };
  return { mk, EMPTY, ord, isOrd, mem, show, parse, V, tc, chain, code, cmp, pair, union, cup, succ, power, transitive };
})();

/* ===================================================================== */
/* ======== pure: first-order formulas in the language {∈} ============= */
/* ===================================================================== */
const FO = (() => {
  const VARS = 'uvwxyz';
  function lex(s) {
    const out = [];
    let i = 0;
    while (i < s.length) {
      const c = s[i];
      if (/\s/.test(c)) { i++; continue; }
      const r = s.slice(i);
      const push = (t, n) => { out.push({ t }); i += n; };
      if (r.startsWith('<->') || r.startsWith('<=>')) { push('iff', 3); continue; }
      if (r.startsWith('->') || r.startsWith('=>')) { push('imp', 2); continue; }
      if (r.startsWith('!=')) { push('ne', 2); continue; }
      if (r.startsWith('notin')) { push('nin', 5); continue; }
      if (r.startsWith('in') && !/[a-z]/.test(r[2] || '')) { push('mem', 2); continue; }
      const single = { '↔': 'iff', '→': 'imp', '∧': 'and', '&': 'and', '∨': 'or', '|': 'or', '¬': 'not', '~': 'not', '!': 'not',
        '∀': 'all', 'A': 'all', '∃': 'ex', 'E': 'ex', '∈': 'mem', '∉': 'nin', '=': 'eq', '≠': 'ne', '(': '(', ')': ')' };
      if (single[c]) { push(single[c], 1); continue; }
      if (VARS.includes(c)) { out.push({ t: 'var', v: c }); i++; continue; }
      if (c === '∅' || c === 'Ø' || /[0-9]/.test(c) || c === '{') {
        let j = i;
        if (c === '{') {
          let d = 0;
          for (; j < s.length; j++) { if (s[j] === '{') d++; if (s[j] === '}') { d--; if (d === 0) { j++; break; } } }
          if (d !== 0) throw new HFError('Unbalanced braces in a set constant', '集合常元的花括号不配对');
        } else if (/[0-9]/.test(c)) { while (j < s.length && /[0-9]/.test(s[j])) j++; } else j++;
        out.push({ t: 'lit', v: HF.parse(s.slice(i, j)), src: s.slice(i, j) });
        i = j;
        continue;
      }
      throw new HFError(`Unknown symbol “${c}”. Variables are u, v, w, x, y, z.`, `无法识别的符号“${c}”。变元只能用 u, v, w, x, y, z。`);
    }
    return out;
  }
  function parse(s) {
    const T = lex(s);
    if (!T.length) throw new HFError('Empty formula', '公式为空');
    let i = 0;
    const peek = () => T[i];
    const fail = (en, zh) => { throw new HFError(en, zh); };
    function F() { let a = Imp(); while (peek() && peek().t === 'iff') { i++; a = { t: 'bin', op: 'iff', a, b: Imp() }; } return a; }
    function Imp() { const a = Or(); if (peek() && peek().t === 'imp') { i++; return { t: 'bin', op: 'imp', a, b: Imp() }; } return a; }
    function Or() { let a = And(); while (peek() && peek().t === 'or') { i++; a = { t: 'bin', op: 'or', a, b: And() }; } return a; }
    function And() { let a = Un(); while (peek() && peek().t === 'and') { i++; a = { t: 'bin', op: 'and', a, b: Un() }; } return a; }
    function Term() {
      const tk = peek();
      if (tk && tk.t === 'var') { i++; return { v: tk.v }; }
      if (tk && tk.t === 'lit') { i++; return { c: tk.v }; }
      fail('Expected a variable or a set here', '这里应当是变元或集合');
    }
    function Un() {
      const tk = peek();
      if (!tk) fail('Formula ends too early', '公式不完整，结尾缺少内容');
      if (tk.t === 'not') { i++; return { t: 'not', a: Un() }; }
      if (tk.t === 'all' || tk.t === 'ex') {
        i++;
        const v = peek();
        if (!v || v.t !== 'var') fail('A quantifier must be followed by a variable (u, v, w, x, y, z)', '量词后面必须紧跟一个变元（u, v, w, x, y, z）');
        i++;
        let bound = null;
        if (peek() && peek().t === 'mem') { i++; bound = Term(); }
        return { t: 'q', q: tk.t, v: v.v, bound, a: Un() };
      }
      if (tk.t === '(') {
        i++;
        const a = F();
        if (!peek() || peek().t !== ')') fail('Missing “)”', '缺少右括号“)”');
        i++;
        return a;
      }
      const l = Term();
      const r = peek();
      if (!r || !['mem', 'nin', 'eq', 'ne'].includes(r.t)) fail('Expected ∈, ∉, = or ≠ here', '这里应当是 ∈、∉、= 或 ≠');
      i++;
      const rt = Term();
      const at = { t: r.t === 'mem' || r.t === 'nin' ? 'mem' : 'eq', a: l, b: rt };
      return r.t === 'nin' || r.t === 'ne' ? { t: 'not', a: at, sugar: true } : at;
    }
    const f = F();
    if (i < T.length) fail('Extra symbols after the formula', '公式后面多出了符号');
    return f;
  }
  function free(f, bound = new Set(), acc = new Set()) {
    const tm = t => { if (t.v && !bound.has(t.v)) acc.add(t.v); };
    if (f.t === 'mem' || f.t === 'eq') { tm(f.a); tm(f.b); }
    else if (f.t === 'not') free(f.a, bound, acc);
    else if (f.t === 'bin') { free(f.a, bound, acc); free(f.b, bound, acc); }
    else { if (f.bound) tm(f.bound); const nb = new Set(bound); nb.add(f.v); free(f.a, nb, acc); }
    return acc;
  }
  function consts(f, acc = []) {
    const tm = t => { if (t.c) acc.push(t.c); };
    if (f.t === 'mem' || f.t === 'eq') { tm(f.a); tm(f.b); }
    else if (f.t === 'not') consts(f.a, acc);
    else if (f.t === 'bin') { consts(f.a, acc); consts(f.b, acc); }
    else { if (f.bound) tm(f.bound); consts(f.a, acc); }
    return acc;
  }
  const isDelta0 = f => f.t === 'q' ? !!f.bound && isDelta0(f.a) : f.t === 'not' ? isDelta0(f.a) : f.t === 'bin' ? isDelta0(f.a) && isDelta0(f.b) : true;
  // (dom, ∈) ⊨ f[env]; quantifiers range over dom, bounded ones over dom ∩ bound.
  function sat(f, dom, env) {
    const val = t => (t.v ? env[t.v] : t.c);
    switch (f.t) {
      case 'mem': return HF.mem(val(f.a), val(f.b));
      case 'eq': return val(f.a) === val(f.b);
      case 'not': return !sat(f.a, dom, env);
      case 'bin': {
        const a = sat(f.a, dom, env);
        if (f.op === 'and') return a && sat(f.b, dom, env);
        if (f.op === 'or') return a || sat(f.b, dom, env);
        if (f.op === 'imp') return !a || sat(f.b, dom, env);
        return a === sat(f.b, dom, env);
      }
      default: {
        const range = f.bound ? dom.filter(z => HF.mem(z, val(f.bound))) : dom;
        const test = z => sat(f.a, dom, Object.assign({}, env, { [f.v]: z }));
        return f.q === 'all' ? range.every(test) : range.some(test);
      }
    }
  }
  const OPS = { iff: '↔', imp: '→', or: '∨', and: '∧' };
  // HTML pretty printer; quantifiers colored green (bounded) / red (unbounded)
  function fmt(f, html = true, top = true) {
    const tm = t => (t.v ? t.v : HF.show(t.c, true));
    switch (f.t) {
      case 'mem': return `${tm(f.a)} ∈ ${tm(f.b)}`;
      case 'eq': return `${tm(f.a)} = ${tm(f.b)}`;
      case 'not':
        if (f.sugar) return f.a.t === 'mem' ? `${tm(f.a.a)} ∉ ${tm(f.a.b)}` : `${tm(f.a.a)} ≠ ${tm(f.a.b)}`;
        return '¬' + fmt(f.a, html, false);
      case 'bin': {
        const s = `${fmt(f.a, html, false)} ${OPS[f.op]} ${fmt(f.b, html, false)}`;
        return top ? s : `(${s})`;
      }
      default: {
        const qs = (f.q === 'all' ? '∀' : '∃') + f.v + (f.bound ? '∈' + tm(f.bound) : '');
        const q = html ? `<span class="q ${f.bound ? 'bd' : 'ub'}">${qs}</span>` : qs;
        return q + ' ' + fmt(f.a, html, false);
      }
    }
  }
  return { parse, free, consts, isDelta0, sat, fmt };
})();

/* ===================================================================== */
/* ===================  pure: lesson 15 helpers  ======================== */
/* ===================================================================== */
// {x ∈ X : (X, ∈) ⊨ f[x]}
function defSubset(f, X) { return X.filter(x => FO.sat(f, X, { x })); }

// Toy <_L on L_n = V_n (n ≤ 4): stage first, then formula code k = |x| for
// "v = p1 ∨ … ∨ v = pk" (code 0 = "v ≠ v"), then parameter tuple p1 <_L … <_L pk lexicographically.
function ladderOrder(n) {
  const list = [];
  const lex = (a, b) => { for (let i = 0; i < Math.min(a.length, b.length); i++) if (a[i] !== b[i]) return a[i] - b[i]; return a.length - b.length; };
  for (let st = 0; st < n; st++) {
    const idx = new Map(list.map((it, i) => [it.x, i]));
    const fresh = HF.V(st + 1).filter(x => x.r === st).map(x => ({ x, stage: st + 1, code: x.e.length, params: x.e.map(y => idx.get(y)).sort((a, b) => a - b) }));
    fresh.sort((a, b) => a.code - b.code || lex(a.params, b.params));
    list.push(...fresh);
  }
  return list;
}

// cardinalities of L_α and V_α (provable in ZFC; no GCH)
const SIZES = [
  ['0', '0', '0'], ['1', '1', '1'], ['2', '2', '2'], ['3', '4', '4'], ['4', '16', '16'], ['5', '65 536', '65 536'],
  ['ω', 'ℵ₀', 'ℵ₀'], ['ω+1', 'ℵ₀', '2^ℵ₀'], ['ω+2', 'ℵ₀', '2^(2^ℵ₀)'], ['ω+ω', 'ℵ₀', 'ℶ_ω'], ['ω₁', 'ℵ₁', 'ℶ_ω₁'], ['ω₁+1', 'ℵ₁', 'ℶ_ω₁+1'],
];

if (typeof module !== 'undefined' && module.exports) module.exports = { HF, FO, defSubset, ladderOrder, SIZES, HFError };

/* ===================================================================== */
/* ============================  browser  =============================== */
/* ===================================================================== */
function lesson15Main() {
  Lang.init();
  Progress.paint();

  const $ = id => document.getElementById(id);
  const okBox = (box, html, kind = 'ok') => { box.className = 'msg ' + kind; box.innerHTML = html; };
  const clearBox = box => { box.className = 'msg'; box.innerHTML = ''; };
  const errBox = (box, e) => { box.className = 'msg bad'; box.innerHTML = e instanceof HFError ? e.html() : String(e.message || e); };
  const SUBD = '₀₁₂₃₄₅₆₇₈₉';
  const sub = n => String(n).split('').map(d => SUBD[d] || d).join('');
  const txt = (parent, x, y, s, attrs = {}) => { const t = el('text', Object.assign({ x, y }, attrs), parent); t.textContent = s; return t; };
  const S = x => HF.show(x, true);
  const setStr = arr => arr.length ? '{' + arr.map(S).join(', ') + '}' : '∅';

  function stepper(stepsId, nextId, allId, onStep) {
    const steps = [...document.querySelectorAll('#' + stepsId + ' .step')];
    let k = 1;
    steps[0].classList.add('on');
    if (onStep) onStep(0, false);
    $(nextId).addEventListener('click', () => {
      if (k < steps.length) { steps[k].classList.add('on'); if (onStep) onStep(k, false); k++; }
      if (k >= steps.length) $(nextId).disabled = true;
    });
    $(allId).addEventListener('click', () => { steps.forEach(s => s.classList.add('on')); k = steps.length; $(nextId).disabled = true; if (onStep) onStep(steps.length - 1, true); });
    return {
      reset() { steps.forEach((s, i) => s.classList.toggle('on', i === 0)); k = 1; $(nextId).disabled = false; if (onStep) onStep(0, false); },
    };
  }
  function symKeys(container, input, syms) {
    syms.forEach(s => {
      const b = document.createElement('button');
      b.type = 'button';
      b.textContent = s;
      b.addEventListener('click', () => {
        const target = container._target || input;
        const st = target.selectionStart ?? target.value.length, en = target.selectionEnd ?? target.value.length;
        target.value = target.value.slice(0, st) + s + target.value.slice(en);
        target.focus();
        target.setSelectionRange(st + s.length, st + s.length);
        target.dispatchEvent(new Event('input'));
      });
      container.appendChild(b);
    });
  }
  function arrowDefs(svg, id) {
    const defs = el('defs', {}, svg);
    [['g', '#868e96'], ['p', '#ae3ec9'], ['b', '#3b5bdb'], ['o', '#f08c00']].forEach(([s, c]) => {
      const m = el('marker', { id: `${id}-${s}`, viewBox: '0 0 10 10', refX: 9, refY: 5, markerUnits: 'userSpaceOnUse', markerWidth: 10, markerHeight: 10, orient: 'auto-start-reverse' }, defs);
      el('path', { d: 'M0,0 L10,5 L0,10 z', fill: c }, m);
    });
  }
  function onVisible(node, fn) {
    if (!('IntersectionObserver' in window)) { fn(); return; }
    const io = new IntersectionObserver(es => { if (es.some(e => e.isIntersecting)) { io.disconnect(); fn(); } }, { threshold: 0.3 });
    io.observe(node);
  }
  const FORMULA_KEYS = ['∀', '∃', '∈', '∉', '=', '≠', '¬', '∧', '∨', '→', '(', ')', 'x', 'y', 'z'];

  /* ================= §1 Def(X) ================= */
  (function defX() {
    const XS = {
      3: () => [0, 1, 2].map(HF.ord),
      V3: () => HF.V(3),
      odd: () => ['1', '{1}', '3'].map(HF.parse),
    };
    const PRE = {
      3: [['x = x', 'everything', '全体'], ['x ≠ x', 'nothing', '空集'], ['∃y∈x (y = y)', 'nonempty', '非空'], ['∃y∈x ∃z∈y (z = z)', '∋ a nonempty set', '含非空元素'], ['∀y (x ∉ y)', '∈-maximal', '∈-极大'], ['x = 0 ∨ x = 2', 'with parameters', '带参数']],
      V3: [['∃y∈x (y = y)', 'nonempty', '非空'], ['∀y∈x ∀z∈y (z ∈ x)', 'transitive', '传递'], ['∃y (x ∈ y)', 'belongs to something', '属于某元素'], ['x ∈ 2', 'x ∈ 2', 'x ∈ 2'], ['x = {1} ∨ x = 0', 'with parameters', '带参数']],
      odd: [['∃y (y ∈ x)', 'has a member in X', '在 X 中有元素'], ['∃y (x ∈ y)', 'is a member of something in X', '属于 X 中某元素'], ['∀y (y ∉ x)', 'looks empty from inside X', '在 X 内部看是空的'], ['x = 3', 'x = 3', 'x = 3']],
    };
    let key = '3', X = [], found = new Map(), tok = 0;
    const svg = $('dxSvg');
    function allSubsets() {
      const out = [];
      for (let m = 0; m < 2 ** X.length; m++) out.push(X.filter((_, j) => Math.floor(m / 2 ** j) % 2));
      return out.sort((a, b) => a.length - b.length || a.map(x => X.indexOf(x)).join() .localeCompare(b.map(x => X.indexOf(x)).join()));
    }
    const sk = arr => arr.map(x => x.k).sort().join('|');
    function drawGraph(inSet) {
      svg.innerHTML = '';
      arrowDefs(svg, 'dx');
      const layers = [];
      X.forEach(x => (layers[x.r] = layers[x.r] || []).push(x));
      const pos = new Map();
      const ranks = layers.map((L, r) => r).filter(r => layers[r]);
      ranks.forEach((r, li) => layers[r].forEach((x, i) => pos.set(x, { x: 165 + (i - (layers[r].length - 1) / 2) * 110, y: 220 - li * (180 / Math.max(1, ranks.length - 1)) })));
      X.forEach(b => b.e.forEach(a => {
        if (!pos.has(a)) return;
        const A = pos.get(a), B = pos.get(b), dx = B.x - A.x, dy = B.y - A.y, L = Math.hypot(dx, dy);
        el('line', { x1: A.x + dx / L * 22, y1: A.y + dy / L * 22, x2: B.x - dx / L * 25, y2: B.y - dy / L * 25, stroke: '#868e96', 'stroke-width': 1.8, 'marker-end': 'url(#dx-g)' }, svg);
      }));
      X.forEach(x => {
        const P = pos.get(x);
        const g = el('g', { class: 'gnode' + (inSet && inSet.includes(x) ? ' in' : ''), transform: `translate(${P.x},${P.y})` }, svg);
        el('circle', { r: 21 }, g);
        txt(g, 0, 0, S(x));
        const t = el('title', {}, g); t.textContent = HF.show(x);
      });
    }
    function tiles(now) {
      const subs = allSubsets();
      $('dxTiles').innerHTML = subs.map(s => {
        const f = found.get(sk(s));
        return `<div class="ptile${f ? ' found' : ''}${now && sk(now) === sk(s) ? ' now' : ''}">${setStr(s)}${f ? `<small>${f}</small>` : '<small>?</small>'}</div>`;
      }).join('');
      $('dxCount').innerHTML = bil(`collected ${found.size} / ${subs.length}`, `已收集 ${found.size} / ${subs.length}`);
    }
    function load(k) {
      key = k; X = XS[k](); found = new Map(); tok++;
      document.querySelectorAll('[data-x]').forEach(b => b.classList.toggle('sel', b.dataset.x === k));
      $('dxPresets').innerHTML = '';
      PRE[k].forEach(([f, en, zh]) => {
        const b = document.createElement('button');
        b.className = 'btn small';
        b.innerHTML = `<span class="m">${f}</span>`;
        b.title = en + ' · ' + zh;
        b.addEventListener('click', () => { $('dxIn').value = f; run(); });
        $('dxPresets').appendChild(b);
      });
      $('dxIn').value = PRE[k][0][0];
      run();
    }
    function run() {
      let f;
      try { f = FO.parse($('dxIn').value); } catch (e) { errBox($('dxOut'), e); drawGraph(null); return; }
      const fv = [...FO.free(f)];
      if (fv.some(v => v !== 'x')) { okBox($('dxOut'), bi(`Only x may be free (found ${fv.join(', ')}).`, `只允许 x 自由出现（现在有 ${fv.join(', ')}）。`), 'bad'); return; }
      const bad = FO.consts(f).filter(c => !X.includes(c));
      if (bad.length) { okBox($('dxOut'), bi(`Parameter ${S(bad[0])} is not an element of X. Parameters must come from X.`, `参数 ${S(bad[0])} 不是 X 的元素。参数必须取自 X。`), 'bad'); return; }
      const S1 = defSubset(f, X);
      const pf = FO.consts(f).length === 0;
      const isNew = !found.has(sk(S1));
      if (isNew) found.set(sk(S1), FO.fmt(f, false));
      drawGraph(S1);
      tiles(S1);
      okBox($('dxOut'), `<span class="m">{x ∈ X : ${FO.fmt(f)}} = <b>${setStr(S1)}</b></span><br>` +
        (pf ? bi('Parameter-free definition.', '不带参数的定义。') : bi('Uses parameters from X.', '用到了 X 中的参数。')) + ' ' +
        (isNew ? bi('New subset collected!', '收集到一个新子集！') : bi('Already collected.', '这个子集已经收集过了。')), isNew ? 'ok' : 'info');
    }
    $('dxGo').addEventListener('click', run);
    $('dxIn').addEventListener('keydown', e => e.key === 'Enter' && run());
    symKeys($('dxKeys'), $('dxIn'), FORMULA_KEYS);
    document.querySelectorAll('[data-x]').forEach(b => b.addEventListener('click', () => load(b.dataset.x)));
    $('dxReset').addEventListener('click', () => { found = new Map(); tiles(); });
    $('dxAll').addEventListener('click', async () => {
      const my = ++tok;
      for (const s of allSubsets()) {
        if (my !== tok) return;
        if (found.has(sk(s))) continue;
        const f = s.length ? s.map(x => `x = ${S(x)}`).join(' ∨ ') : 'x ≠ x';
        $('dxIn').value = f;
        found.set(sk(s), f);
        drawGraph(s);
        tiles(s);
        await sleep(260);
      }
      okBox($('dxOut'), bi(`All ${found.size} subsets are definable: Def(X) = 𝒫(X) for finite X.`, `全部 ${found.size} 个子集都可定义：X 有限时 Def(X) = 𝒫(X)。`));
    });
    load('3');
  })();

  /* ================= §2 sizes ================= */
  const card = s => ({ '2^ℵ₀': '2<sup>ℵ₀</sup>', '2^(2^ℵ₀)': '2<sup>2<sup>ℵ₀</sup></sup>', 'ℶ_ω': 'ℶ<sub>ω</sub>', 'ℶ_ω₁': 'ℶ<sub>ω₁</sub>', 'ℶ_ω₁+1': 'ℶ<sub>ω₁+1</sub>' }[s] || s);
  (function sizes() {
    const svg = $('szSvg');
    const H = { '0': 0, '1': 8, '2': 16, '4': 26, '16': 40, '65 536': 62, 'ℵ₀': 105, 'ℵ₁': 130, '2^ℵ₀': 150, '2^(2^ℵ₀)': 182, 'ℶ_ω': 220, 'ℶ_ω₁': 245, 'ℶ_ω₁+1': 258 };
    const msgs = {
      fin: (a, n) => bi(`<b>L${sub(a)} = V${sub(a)}</b>, both with ${n} elements: over a finite set every subset is definable (§1).`, `<b>L${sub(a)} = V${sub(a)}</b>，都有 ${n} 个元素：有限集上每个子集都可定义（§1）。`),
      'ω': bi('<b>L<sub>ω</sub> = V<sub>ω</sub></b>: the hereditarily finite sets. Up to here, nothing is lost.', '<b>L<sub>ω</sub> = V<sub>ω</sub></b>：全体遗传有限集。到这里为止，什么也没丢。'),
      'ω+1': bi('<b>The split.</b> L<sub>ω+1</sub> = Def(V<sub>ω</sub>) is countable: countably many names. V<sub>ω+1</sub> = 𝒫(V<sub>ω</sub>) has 2<sup>ℵ₀</sup> elements. This is provable in ZF, so L<sub>ω+1</sub> ⊊ V<sub>ω+1</sub> no matter what.', '<b>分岔点.</b> L<sub>ω+1</sub> = Def(V<sub>ω</sub>) 可数：名字只有可数个。V<sub>ω+1</sub> = 𝒫(V<sub>ω</sub>) 有 2<sup>ℵ₀</sup> 个元素。这在 ZF 中可证，所以无论如何 L<sub>ω+1</sub> ⊊ V<sub>ω+1</sub>。'),
      'ω+2': bi('L keeps the size |α| = ℵ₀; V has already taken two power sets.', 'L 的大小仍是 |α| = ℵ₀；V 已经取了两次幂集。'),
      'ω+ω': bi('|L<sub>ω+ω</sub>| = ℵ₀, while |V<sub>ω+ω</sub>| = ℶ<sub>ω</sub> = sup ℶ<sub>n</sub>.', '|L<sub>ω+ω</sub>| = ℵ₀，而 |V<sub>ω+ω</sub>| = ℶ<sub>ω</sub> = sup ℶ<sub>n</sub>。'),
      'ω₁': bi('|L<sub>ω₁</sub>| = ℵ₁: in general |L<sub>α</sub>| = |α| for infinite α, by induction (|Def(X)| = |X| for infinite X).', '|L<sub>ω₁</sub>| = ℵ₁：一般地，α 无穷时 |L<sub>α</sub>| = |α|，对 α 归纳即得（无穷 X 有 |Def(X)| = |X|）。'),
      'ω₁+1': bi('|L<sub>ω₁+1</sub>| = ℵ₁ but |V<sub>ω₁+1</sub>| = 2<sup>ℶ<sub>ω₁</sub></sup>. L grows as slowly as possible: one ordinal at a time, cardinality-wise.', '|L<sub>ω₁+1</sub>| = ℵ₁，而 |V<sub>ω₁+1</sub>| = 2<sup>ℶ<sub>ω₁</sub></sup>。L 的增长慢到极致：就基数而言，一次只多一个序数。'),
    };
    function draw() {
      const i = +$('szR').value, [a, l, v] = SIZES[i];
      $('szA').textContent = a;
      svg.innerHTML = '';
      const X0 = 50, Y0 = 270, GW = (540 - X0) / SIZES.length;
      el('line', { x1: X0 - 6, x2: 552, y1: Y0, y2: Y0, stroke: '#999' }, svg);
      txt(svg, 8, 18, 'size (not to scale) · 大小（非等比例）', { 'font-size': 11, fill: '#888' });
      SIZES.forEach(([aa, ll, vv], k) => {
        const x = X0 + k * GW, cur = k === i;
        el('rect', { x: x + 3, y: Y0 - H[vv], width: GW / 2 - 4, height: H[vv], fill: '#3b5bdb', opacity: cur ? 1 : 0.25, rx: 2 }, svg);
        el('rect', { x: x + GW / 2, y: Y0 - H[ll], width: GW / 2 - 4, height: H[ll], fill: '#2f9e44', opacity: cur ? 1 : 0.25, rx: 2 }, svg);
        txt(svg, x + GW / 2, Y0 + 16, aa, { 'font-size': cur ? 13 : 11, 'text-anchor': 'middle', 'font-weight': cur ? 700 : 400 });
        if (cur) {
          txt(svg, x + GW / 4, Y0 - H[vv] - 8, vv, { 'font-size': 12, 'text-anchor': 'end', fill: '#3b5bdb', 'font-weight': 700 });
          txt(svg, x + 3 * GW / 4, Y0 - H[ll] - 22, ll, { 'font-size': 12, 'text-anchor': 'start', fill: '#2f9e44', 'font-weight': 700 });
        }
      });
      el('rect', { x: X0, y: 28, width: 12, height: 12, fill: '#3b5bdb' }, svg); txt(svg, X0 + 16, 39, '|V_α|', { 'font-size': 12 });
      el('rect', { x: X0 + 70, y: 28, width: 12, height: 12, fill: '#2f9e44' }, svg); txt(svg, X0 + 86, 39, '|L_α|', { 'font-size': 12 });
      $('szMsg').innerHTML = `<div class="m" style="font-size:15px;margin-bottom:6px">|L<sub>${a}</sub>| = ${card(l)} &nbsp; · &nbsp; |V<sub>${a}</sub>| = ${card(v)}</div>` + (i <= 5 ? msgs.fin(a, l) : msgs[a]);
    }
    $('szR').addEventListener('input', draw);
    draw();
  })();

  (function names() {
    const svg = $('nmSvg');
    const NB = 28;
    const isPrime = n => { if (n < 2) return false; for (let d = 2; d * d <= n; d++) if (n % d === 0) return false; return true; };
    const NAMES = [
      ['x ∈ 5', '(param 5)', n => n < 5],
      ['∃y∈ω (x = y + y)', 'even · 偶数', n => n % 2 === 0],
      ['x is prime', '素数', isPrime],
      ['∃y∈ω (x = y · y)', 'square · 平方数', n => Number.isInteger(Math.sqrt(n))],
      ['x = 7 ∨ x = 12', '(params 7, 12)', n => n === 7 || n === 12],
      ['∃y∈ω (x = 3y + 1)', '≡ 1 mod 3', n => n % 3 === 1],
      ['x is a power of 2', '2 的幂', n => n > 0 && (n & (n - 1)) === 0],
      ['∃y∈x (x = y + 20)', 'x ≥ 20', n => n >= 20],
    ];
    let shown = 0, diag = false, tok = 0;
    function draw() {
      svg.innerHTML = '';
      txt(svg, 12, 22, 'name · 名字', { 'font-size': 12, fill: '#6b7280' });
      txt(svg, 300, 22, 'the subset of ω it defines · 它定义的 ω 的子集', { 'font-size': 12, fill: '#6b7280' });
      for (let j = 0; j < NB; j++) txt(svg, 300 + j * 16 + 7, 40, String(j), { 'font-size': 9, 'text-anchor': 'middle', fill: '#999' });
      for (let k = 0; k < shown; k++) {
        const [f, note, p] = NAMES[k], y = 62 + k * 29;
        const g = el('g', { class: k === shown - 1 && !diag ? 'fadein' : '' }, svg);
        txt(g, 12, y + 4, `n${sub(k)}: ${f}`, { 'font-size': 12.5, 'font-weight': 700 });
        txt(g, 12, y + 17, note, { 'font-size': 10, fill: '#888' });
        for (let j = 0; j < NB; j++) {
          const on = p(j), d = diag && j === k;
          el('rect', { x: 300 + j * 16, y: y - 9, width: 14, height: 18, rx: 3, fill: on ? '#2f9e44' : '#e9ecef', stroke: d ? '#ae3ec9' : 'none', 'stroke-width': 3 }, g);
        }
      }
      if (shown < NAMES.length) txt(svg, 12, 62 + shown * 29 + 4, '⋮', { 'font-size': 14, fill: '#999' });
      if (diag) {
        const y = 62 + NAMES.length * 29 + 6;
        txt(svg, 12, y + 4, 'd = {k : k ∉ set named nₖ}', { 'font-size': 12.5, 'font-weight': 700, fill: '#ae3ec9' });
        for (let j = 0; j < Math.min(shown, NB); j++) {
          const r = el('rect', { x: 300 + j * 16, y: y - 9, width: 14, height: 18, rx: 3, fill: NAMES[j][2](j) ? '#e9ecef' : '#ae3ec9', class: 'pop' }, svg);
          r.style.animationDelay = (j * 0.12) + 's';
        }
        txt(svg, 300 + shown * 16 + 8, y + 4, '… differs from every name', { 'font-size': 11, fill: '#ae3ec9' });
      }
    }
    async function nameOne() {
      if (shown >= NAMES.length) { $('nmMsg').innerHTML = bi('In reality the list goes on forever, but only countably: formulas are finite strings, and parameters are finite tuples from the countable set L<sub>ω</sub>.', '实际上名字无穷无尽，但只有可数多个：公式是有限串，参数是可数集 L<sub>ω</sub> 中的有限元组。'); return; }
      shown++; diag = false; draw();
      $('nmMsg').innerHTML = bi(`Name n${sub(shown - 1)} defines a subset of ω over (L<sub>ω</sub>, ∈). Arithmetic (+, ·) is itself definable over V<sub>ω</sub>, so these are all legitimate.`, `名字 n${sub(shown - 1)} 在 (L<sub>ω</sub>, ∈) 上定义了 ω 的一个子集。加法和乘法本身在 V<sub>ω</sub> 上可定义，所以这些都合法。`);
    }
    $('nmGo').addEventListener('click', nameOne);
    $('nmDiag').addEventListener('click', () => {
      if (!shown) shown = NAMES.length;
      diag = true; draw();
      $('nmMsg').innerHTML = bi('Purple marks the diagonal. d differs from the k-th named set at k. Run this against the list of <b>all</b> names and d is a subset of ω that no name defines: <b>d ∈ V<sub>ω+1</sub> \\ L<sub>ω+1</sub></b>. Cantor beats Def. (Since satisfaction over L<sub>ω</sub> is definable over L<sub>ω+1</sub>, d does turn up one stage later, in L<sub>ω+2</sub>.)',
        '紫色标出对角线。d 在第 k 位与第 k 个名字定义的集合不同。若对<b>全体</b>名字做这件事，d 就是任何名字都定义不了的 ω 子集：<b>d ∈ V<sub>ω+1</sub> \\ L<sub>ω+1</sub></b>。康托尔胜过了 Def。（由于 L<sub>ω</sub> 上的满足关系在 L<sub>ω+1</sub> 上可定义，d 会在下一层 L<sub>ω+2</sub> 中出现。）');
    });
    $('nmReset').addEventListener('click', () => { tok++; shown = 0; diag = false; draw(); $('nmMsg').innerHTML = bi('Press “Name a set”.', '按“取一个名字”。'); });
    draw();
    $('nmMsg').innerHTML = bi('Press “Name a set”.', '按“取一个名字”。');
    onVisible(svg, async () => { const my = ++tok; for (let k = 0; k < 4; k++) { if (my !== tok) return; await nameOne(); await sleep(500); } });
  })();

  /* ================= §3 two cones ================= */
  (function cones() {
    const svg = $('ccSvg');
    const AX = 230, AY = 415, hwV = y => (AY - y) * 0.55, YW = 300;
    const LV = [['3', 365], ['ω', YW], ['ω+1', 268], ['ω+2', 240], ['ω+ω', 195], ['ω₁', 125], ['ω₂', 60]];
    let VL = false;
    const hwL = y => {
      if (y >= YW) return hwV(y);
      const base = hwV(YW) + (YW - y) * 0.13;
      if (!VL) return base;
      const t = Math.min(1, Math.max(0, (YW - y) / (YW - 125)));
      return base + (hwV(y) - base) * Math.pow(t, 1.6) * 0.92;
    };
    const MSG = [
      bi('L₃ = V₃ = {0, 1, {1}, 2}.', 'L₃ = V₃ = {0, 1, {1}, 2}。'),
      bi('L<sub>ω</sub> = V<sub>ω</sub>: the cones coincide below ω.', 'L<sub>ω</sub> = V<sub>ω</sub>：在 ω 以下两个锥完全重合。'),
      bi('L<sub>ω+1</sub> is countable, V<sub>ω+1</sub> is not: L becomes thin, provably in ZF.', 'L<sub>ω+1</sub> 可数，V<sub>ω+1</sub> 不可数：从这里起 L 变细，这在 ZF 中可证。'),
      bi('|L<sub>ω+2</sub>| = ℵ₀ &lt; |V<sub>ω+2</sub>|.', '|L<sub>ω+2</sub>| = ℵ₀ &lt; |V<sub>ω+2</sub>|。'),
      bi('L<sub>ω+ω</sub> ⊊ V<sub>ω+ω</sub>; L<sub>α</sub> ∩ Ord = α = V<sub>α</sub> ∩ Ord: both have the same ordinals at every stage.', 'L<sub>ω+ω</sub> ⊊ V<sub>ω+ω</sub>；L<sub>α</sub> ∩ Ord = α = V<sub>α</sub> ∩ Ord：每一层两者含有的序数都相同。'),
      bi('|L<sub>ω₁</sub>| = ℵ₁. If V = L, every real is already in L<sub>ω₁</sub> (§6).', '|L<sub>ω₁</sub>| = ℵ₁。若 V = L，每个实数都已在 L<sub>ω₁</sub> 中（§6）。'),
      bi('|L<sub>ω₂</sub>| = ℵ₂. If V = L, every subset of ω₁ is in L<sub>ω₂</sub>.', '|L<sub>ω₂</sub>| = ℵ₂。若 V = L，ω₁ 的每个子集都在 L<sub>ω₂</sub> 中。'),
    ];
    function poly(hw, fill, stroke) {
      const ys = []; for (let y = 20; y <= AY; y += 5) ys.push(y);
      const pts = ys.map(y => [AX + hw(y), y]).concat(ys.slice().reverse().map(y => [AX - hw(y), y]));
      return el('polygon', { points: pts.map(p => p.join(',')).join(' '), fill, stroke, 'stroke-width': 1.5 }, svg);
    }
    function draw() {
      const i = +$('ccR').value;
      $('ccA').textContent = LV[i][0];
      svg.innerHTML = '';
      arrowDefs(svg, 'cc');
      poly(hwV, '#e7ecff', '#3b5bdb');
      poly(hwL, 'rgba(47,158,68,.28)', '#2f9e44');
      el('line', { x1: AX, x2: AX, y1: AY, y2: 20, stroke: '#1f2430', 'stroke-dasharray': '3 3' }, svg);
      txt(svg, AX + 4, 16, 'Ord', { 'font-size': 11, fill: '#555' });
      txt(svg, AX - hwV(30) + 6, 46, 'V', { 'font-size': 18, 'font-weight': 800, fill: '#3b5bdb' });
      txt(svg, AX - 10, 46, 'L', { 'font-size': 18, 'font-weight': 800, fill: '#2f9e44', 'text-anchor': 'end' });
      LV.forEach(([lab, y], k) => {
        const cur = k === i;
        el('line', { x1: AX - hwV(y), x2: AX + hwV(y), y1: y, y2: y, stroke: cur ? '#ae3ec9' : '#adb5bd', 'stroke-width': cur ? 3 : 1, 'stroke-dasharray': cur ? '' : '3 4' }, svg);
        el('circle', { cx: AX, cy: y, r: cur ? 5 : 3, fill: '#1f2430' }, svg);
        txt(svg, AX + hwV(y) + 6, y + 4, lab, { 'font-size': cur ? 14 : 12, 'font-weight': cur ? 700 : 400, fill: cur ? '#ae3ec9' : '#555' });
      });
      // the real r
      const ry = 280, rx = AX - (hwV(ry) + hwL(ry)) / 2;
      el('circle', { cx: rx, cy: ry, r: 5, fill: '#f08c00', stroke: '#fff', 'stroke-width': 1.5 }, svg);
      el('line', { x1: rx - 6, y1: ry + 2, x2: rx - 50, y2: ry + 24, stroke: '#f08c00', 'stroke-width': 1.2 }, svg);
      txt(svg, rx - 54, ry + 30, 'r ⊆ ω, rank ω', { 'font-size': 12, fill: '#b35c00', 'font-weight': 700, 'text-anchor': 'end' });
      if (VL) {
        const ty = 150, tx = AX - hwL(ty) * 0.6;
        const p = el('path', { d: `M${rx},${ry - 7} C${rx - 10},${ry - 80} ${tx - 30},${ty + 40} ${tx - 4},${ty + 8}`, stroke: '#f08c00', 'stroke-width': 2, fill: 'none', 'stroke-dasharray': '5 4', 'marker-end': 'url(#cc-o)' }, svg);
        p.classList.add('fadein');
        el('circle', { cx: tx, cy: ty, r: 6, fill: '#f08c00' }, svg);
        txt(svg, tx + 10, ty - 8, 'r ∈ L_β+1, β < ω₁', { 'font-size': 11, fill: '#b35c00', 'font-weight': 700 });
      }
      $('ccMsg').innerHTML = MSG[i];
    }
    function setVL(v) {
      VL = v;
      $('ccVL').classList.toggle('sel', v); $('ccNo').classList.toggle('sel', !v);
      draw();
      $('ccR2').className = 'msg ' + (v ? 'ok' : 'warn');
      $('ccR2').innerHTML = v
        ? bi('<b>V = L</b> does <i>not</i> say L<sub>α</sub> = V<sub>α</sub>; that already fails at ω+1. It says every set shows up in L <i>eventually</i>. The real r has rank ω, but it enters L only at some countable stage β+1, which may be far above ω+1. The union of the thin layers is still all of V.',
          '<b>V = L</b> 并<i>不是</i>说 L<sub>α</sub> = V<sub>α</sub>（这在 ω+1 处就已不成立），而是说每个集合<i>迟早</i>会在 L 中出现。实数 r 的秩是 ω，但它要到某个可数阶段 β+1 才进入 L，β 可能远高于 ω+1。这些细层的并仍是整个 V。')
        : bi('Without V = L, r may never enter L. For example, if 0<sup>♯</sup> exists (§8), only countably many reals are constructible.',
          '不假设 V = L 时，r 可能永远进不了 L。例如若 0<sup>♯</sup> 存在（§8），可构成的实数只有可数多个。');
    }
    $('ccR').addEventListener('input', draw);
    $('ccVL').addEventListener('click', () => setVL(true));
    $('ccNo').addEventListener('click', () => setVL(false));
    setVL(false);
  })();

  /* ================= §4 axioms + inner model ================= */
  (function axioms() {
    const AX = [
      ['Extensionality', '外延公理', 'L is transitive, and Extensionality holds in every transitive class.', 'L 是传递类，而外延公理在任何传递类中都成立。'],
      ['Foundation', '正则公理', 'Holds in every transitive class: ∈ is well-founded in V, and a ∈-minimal element of x ∈ L is found among x\'s members, which are in L.', '在任何传递类中都成立：∈ 在 V 中良基，x ∈ L 的 ∈-极小元就在 x 的元素中找，而它们都在 L 里。'],
      ['Pairing', '配对公理', 'If a, b ∈ L<sub>α</sub>, then {a, b} = {x ∈ L<sub>α</sub> : x = a ∨ x = b} ∈ Def(L<sub>α</sub>) = L<sub>α+1</sub>.', '若 a, b ∈ L<sub>α</sub>，则 {a, b} = {x ∈ L<sub>α</sub> : x = a ∨ x = b} ∈ Def(L<sub>α</sub>) = L<sub>α+1</sub>。'],
      ['Union', '并集公理', 'If a ∈ L<sub>α</sub>, then ⋃a ⊆ L<sub>α</sub> by transitivity, and ⋃a = {x ∈ L<sub>α</sub> : ∃y∈a (x ∈ y)} ∈ L<sub>α+1</sub>.', '若 a ∈ L<sub>α</sub>，由传递性 ⋃a ⊆ L<sub>α</sub>，且 ⋃a = {x ∈ L<sub>α</sub> : ∃y∈a (x ∈ y)} ∈ L<sub>α+1</sub>。'],
      ['Infinity', '无穷公理', 'ω = {x ∈ L<sub>ω</sub> : x is an ordinal} ∈ L<sub>ω+1</sub>.', 'ω = {x ∈ L<sub>ω</sub> : x 是序数} ∈ L<sub>ω+1</sub>。'],
      ['Separation', '分离公理', 'Given a ∈ L and φ, use reflection (Lesson 14 §8) inside the L-hierarchy: pick β with a ∈ L<sub>β</sub> and φ absolute between L<sub>β</sub> and L. Then {x ∈ a : φ<sup>L</sup>(x)} = {x ∈ L<sub>β</sub> : x ∈ a ∧ φ<sup>L<sub>β</sub></sup>(x)} ∈ L<sub>β+1</sub>.', '给定 a ∈ L 和 φ，在 L 层级内部用反射原理（第 14 课 §8）：取 β 使 a ∈ L<sub>β</sub> 且 φ 在 L<sub>β</sub> 与 L 之间绝对。则 {x ∈ a : φ<sup>L</sup>(x)} = {x ∈ L<sub>β</sub> : x ∈ a ∧ φ<sup>L<sub>β</sub></sup>(x)} ∈ L<sub>β+1</sub>。'],
      ['Replacement', '替换公理', 'If F maps a ∈ L into L, Replacement in V bounds the stages at which the values F(y) first appear by some β, so F[a] ⊆ L<sub>β</sub>. Then F[a] is cut out of L<sub>β</sub> by Separation in L.', '若 F 把 a ∈ L 映入 L，在 V 中用替换公理可知各个 F(y) 首次出现的阶段有上界 β，于是 F[a] ⊆ L<sub>β</sub>，再用 L 中的分离公理从 L<sub>β</sub> 里把 F[a] 切出来。'],
      ['Power Set', '幂集公理', 'For a ∈ L, Replacement in V bounds the stages of all constructible subsets of a by some β. Then 𝒫(a)<sup>L</sup> = {x ∈ L<sub>β</sub> : x ⊆ a} ∈ L<sub>β+1</sub>. Note that it is 𝒫(a) ∩ L, not 𝒫(a).', '对 a ∈ L，在 V 中用替换公理可知 a 的所有可构成子集出现的阶段有上界 β。于是 𝒫(a)<sup>L</sup> = {x ∈ L<sub>β</sub> : x ⊆ a} ∈ L<sub>β+1</sub>。注意它是 𝒫(a) ∩ L，而不是 𝒫(a)。'],
    ];
    $('axCards').innerHTML = AX.map(a => `<div class="acard"><div class="ttl">${bil(a[0], a[1])}</div><div class="why">${bi(a[2], a[3])}</div></div>`).join('');
    document.querySelectorAll('#axCards .acard').forEach(c => c.addEventListener('click', () => c.classList.toggle('open')));
    const svg = $('imSvg');
    const AXc = 210, AY = 315, hw = k => y => (AY - y) * k;
    function base() {
      svg.innerHTML = '';
      [[0.62, '#e7ecff', '#3b5bdb', 'V'], [0.36, '#fff3bf', '#f08c00', 'M'], [0.16, 'rgba(47,158,68,.25)', '#2f9e44', 'L']].forEach(([k, f, s, lab], i) => {
        const w = hw(k)(15);
        el('path', { d: `M${AXc - w},15 L${AXc},${AY} L${AXc + w},15 Z`, fill: f, stroke: s, 'stroke-width': 2 }, svg);
        txt(svg, AXc - w + 8 + (i === 2 ? -4 : 0), 34 + i * 18, lab, { 'font-size': 15, 'font-weight': 800, fill: s });
      });
      txt(svg, 8, 326, 'Ord ⊆ L ⊆ M ⊆ V', { 'font-size': 11, fill: '#555' });
    }
    let tok = 0;
    async function build() {
      const my = ++tok;
      base();
      const ys = [280, 240, 195, 150, 105, 60];
      const labs = ['L₁', 'L₂', 'L_ω', 'L_ω+1', 'L_α', 'L_β'];
      for (let k = 0; k < ys.length; k++) {
        if (my !== tok) return;
        const y = ys[k], wM = hw(0.36)(y), wL = hw(0.16)(y);
        const d = el('line', { x1: AXc - wM, x2: AXc + wM, y1: y, y2: y, stroke: '#f08c00', 'stroke-width': 2, 'stroke-dasharray': '5 4' }, svg);
        d.classList.add('fadein');
        txt(svg, AXc + wM + 4, y - 2, labs[k] + 'ᴹ', { 'font-size': 11, fill: '#b35c00' });
        await sleep(350);
        if (my !== tok) return;
        d.setAttribute('x1', AXc - wL); d.setAttribute('x2', AXc + wL); d.setAttribute('stroke', '#2f9e44'); d.setAttribute('stroke-dasharray', '');
        txt(svg, AXc + wM + 4, y + 11, '= ' + labs[k] + ' ✓', { 'font-size': 11, fill: '#2f9e44', 'font-weight': 700 });
        await sleep(300);
      }
      if (my !== tok) return;
      const t = txt(svg, 410, 326, 'Lᴹ = L ✓', { 'font-size': 14, 'text-anchor': 'end', 'font-weight': 800, fill: '#2f9e44' });
      t.classList.add('fadein');
    }
    base();
    $('imGo').addEventListener('click', build);
    onVisible(svg, build);
    stepper('imSteps', 'imNext', 'imAll');
  })();

  /* ================= §5 the <_L ladder ================= */
  (function ladder() {
    const svg = $('ldSvg');
    const order = ladderOrder(4);
    const colors = ['#3b5bdb', '#f08c00', '#2f9e44', '#ae3ec9'];
    const RY = i => 22 + i * 33.5;
    const A = new Set();
    let sorted = false;
    svg.innerHTML = '';
    for (let i = 0; i < order.length; i++) {
      el('line', { x1: 34, x2: 620, y1: RY(i) + 14, y2: RY(i) + 14, stroke: '#eee' }, svg);
      txt(svg, 28, RY(i) + 4, String(i + 1), { 'font-size': 11, 'text-anchor': 'end', fill: '#999' });
    }
    el('line', { x1: 34, x2: 34, y1: 8, y2: RY(order.length - 1) + 14, stroke: '#c9c3b3', 'stroke-width': 3 }, svg);
    const groups = order.map((it, i) => {
      const g = el('g', {}, svg);
      g.style.transition = 'transform .9s cubic-bezier(.2,.8,.3,1)';
      const lab = S(it.x);
      const w = Math.max(40, lab.length * 7.6 + 16);
      it.rect = el('rect', { x: 0, y: -12, width: w, height: 26, rx: 8, fill: '#fff', stroke: colors[it.stage - 1], 'stroke-width': 2.5 }, g);
      txt(g, w / 2, 5, lab, { 'font-size': 12.5, 'text-anchor': 'middle', 'font-weight': 700 });
      const cert = it.code === 0 ? `L${sub(it.stage)} · φ₀: x ≠ x` : `L${sub(it.stage)} · φ${sub(it.code)} · (${it.params.map(p => '#' + (p + 1)).join(', ')})`;
      it.cert = txt(g, w + 12, 5, cert, { 'font-size': 11.5, fill: colors[it.stage - 1] });
      it.g = g; it.i = i;
      return g;
    });
    function place(shuffle) {
      const perm = order.map((_, i) => i);
      if (shuffle) for (let i = perm.length - 1; i > 0; i--) { const j = Math.floor(Math.random() * (i + 1)); [perm[i], perm[j]] = [perm[j], perm[i]]; }
      order.forEach((it, i) => {
        const r = perm[i];
        it.g.style.transform = shuffle ? `translate(${60 + Math.random() * 200}px, ${RY(r)}px)` : `translate(46px, ${RY(i)}px)`;
        it.cert.style.opacity = shuffle ? 0 : 1;
      });
      sorted = !shuffle;
      paintA();
    }
    function paintA() {
      const arr = order.filter(it => A.has(it.x));
      order.forEach(it => { it.rect.setAttribute('fill', A.has(it.x) ? '#e7ecff' : '#fff'); });
      if (!arr.length) { okBox($('ldMsg'), bi('Pick some elements to form A.', '选一些元素组成 A。'), 'info'); return; }
      const least = arr[0];
      least.rect.setAttribute('fill', '#ffd43b');
      okBox($('ldMsg'), bi(`F(A) = <b class="m">${S(least.x)}</b>, the &lt;<sub>L</sub>-least element of A (rung #${least.i + 1}). F is defined by a formula, so this choice function exists in L without any appeal to AC.`,
        `F(A) = <b class="m">${S(least.x)}</b>，即 A 的 &lt;<sub>L</sub>-最小元（第 ${least.i + 1} 级）。F 由公式定义，所以这个选择函数在 L 中存在，不需要借助 AC。`) + (sorted ? '' : bi(' (Sort the ladder to see it.)', '（排好序就能看清。）')));
    }
    $('ldChips').innerHTML = order.slice().sort((a, b) => HF.cmp(a.x, b.x)).map(it => `<span class="pick" data-k="${order.indexOf(it)}">${S(it.x)}</span>`).join('');
    document.querySelectorAll('#ldChips .pick').forEach(c => c.addEventListener('click', () => {
      const it = order[+c.dataset.k];
      if (A.has(it.x)) A.delete(it.x); else A.add(it.x);
      c.classList.toggle('on', A.has(it.x));
      paintA();
    }));
    [5, 9, 13].forEach(k => { A.add(order[k].x); document.querySelector(`#ldChips .pick[data-k="${k}"]`).classList.add('on'); });
    place(true);
    $('ldSort').addEventListener('click', () => place(false));
    $('ldShuffle').addEventListener('click', () => place(true));
    onVisible(svg, () => setTimeout(() => place(false), 600));
  })();

  /* ================= §6 condensation ================= */
  (function condensation() {
    const svg = $('gcSvg');
    const AX = 215, AY = 405, hw = y => (AY - y) * 0.5;
    const yK = 355, yK1 = 262, yD = 55;
    const rnd = (() => { let s = 7; return () => (s = (s * 9301 + 49297) % 233280) / 233280; })();
    const high = Array.from({ length: 22 }, () => { const y = yD + 10 + rnd() * (yK1 - yD - 20); return { y, x: AX + (rnd() * 2 - 1) * hw(y) * 0.85 }; });
    const midPts = Array.from({ length: 6 }, () => { const y = yK1 + 6 + rnd() * (yK - yK1 - 12); return { y, x: AX + (rnd() * 2 - 1) * hw(y) * 0.8 }; });
    const low = Array.from({ length: 9 }, (_, i) => ({ y: yK + 8 + (i % 3) * 14, x: AX + (Math.floor(i / 3) - 1) * 22 + (i % 3 - 1) * 6 }));
    const Apos = { x: AX + 40, y: 95 };
    const collapsedY = (y) => yK1 + 8 + (y - yD) / (yK - yD) * (yK - yK1 - 16);
    function line(y, lab, c, w = 1.5) {
      el('line', { x1: AX - hw(y) - 10, x2: AX + hw(y) + 10, y1: y, y2: y, stroke: c, 'stroke-width': w }, svg);
      txt(svg, AX + hw(y) + 14, y + 4, lab, { 'font-size': 13, fill: c, 'font-weight': 700 });
    }
    function dot(p, fill, r = 4) {
      const c = el('circle', { cx: 0, cy: 0, r, fill }, svg);
      c.style.transition = 'transform 1.2s cubic-bezier(.3,.8,.3,1)';
      c.style.transform = `translate(${p.x}px, ${p.y}px)`;
      return c;
    }
    function draw(step, instant) {
      svg.innerHTML = '';
      el('path', { d: `M${AX - hw(20)},20 L${AX},${AY} L${AX + hw(20)},20 Z`, fill: '#f4fbf5', stroke: '#2f9e44', 'stroke-width': 1.5 }, svg);
      txt(svg, AX - hw(20) + 10, 40, 'L', { 'font-size': 18, 'font-weight': 800, fill: '#2f9e44' });
      el('path', { d: `M${AX - hw(yK)},${yK} L${AX},${AY} L${AX + hw(yK)},${yK} Z`, fill: '#e7ecff', stroke: 'none' }, svg);
      line(yK, 'κ', '#3b5bdb', 2);
      line(yK1, 'κ⁺', '#ae3ec9', 2);
      line(yD, 'δ', '#868e96');
      if (step >= 4) {
        const yg = yK1 + 4;
        el('path', { d: `M${AX - hw(yg)},${yg} L${AX},${AY} L${AX + hw(yg)},${yg} Z`, fill: 'rgba(47,158,68,.18)', stroke: '#2f9e44', 'stroke-width': 2, 'stroke-dasharray': '6 3' }, svg);
        txt(svg, 12, yg - 6, 'M = L_γ, γ < κ⁺', { 'font-size': 12.5, fill: '#2f9e44', 'font-weight': 700 });
      }
      const fall = step >= 2;
      if (step >= 1) {
        const ds = high.map(p => dot(p, '#3b5bdb'));
        const ms = midPts.map(p => dot(p, '#3b5bdb'));
        low.forEach(p => dot(p, step >= 3 ? '#2f9e44' : '#3b5bdb', 4.5));
        if (step === 1) txt(svg, 12, 76, 'X ≺ L_δ, |X| = κ', { 'font-size': 13, fill: '#3b5bdb', 'font-weight': 700 });
        if (fall) {
          const go = () => {
            ds.forEach((c, i) => { c.style.transform = `translate(${AX + (high[i].x - AX) * 0.55}px, ${collapsedY(high[i].y)}px)`; });
            ms.forEach((c, i) => { c.style.transform = `translate(${AX + (midPts[i].x - AX) * 0.5}px, ${collapsedY(midPts[i].y) + 6}px)`; });
          };
          if (instant || step > 2) { ds.forEach(c => c.style.transition = 'none'); ms.forEach(c => c.style.transition = 'none'); go(); }
          else requestAnimationFrame(() => requestAnimationFrame(go));
          if (step === 2) txt(svg, 12, 76, 'π : X ≅ M (collapse · 坍塌)', { 'font-size': 13, fill: '#3b5bdb', 'font-weight': 700 });
        }
      }
      const Ad = dot(Apos, '#f08c00', 7);
      const Atarget = { x: AX + 34, y: collapsedY(Apos.y) };
      if (fall) {
        if (instant || step > 2) { Ad.style.transition = 'none'; Ad.style.transform = `translate(${Atarget.x}px, ${Atarget.y}px)`; }
        else requestAnimationFrame(() => requestAnimationFrame(() => { Ad.style.transform = `translate(${Atarget.x}px, ${Atarget.y}px)`; }));
      }
      if (fall) {
        const lx = AX + hw(Atarget.y + 18) + 12, ly = Atarget.y + 22;
        el('line', { x1: Atarget.x + 7, y1: Atarget.y + 3, x2: lx - 2, y2: ly - 4, stroke: '#f08c00', 'stroke-width': 1.2 }, svg);
        txt(svg, lx, ly, step >= 3 ? 'π(A) = A' : 'π(A)', { 'font-size': 13, fill: '#b35c00', 'font-weight': 800 });
      } else txt(svg, Apos.x + 12, Apos.y + 4, 'A', { 'font-size': 13, fill: '#b35c00', 'font-weight': 800 });
      if (step >= 3) txt(svg, 12, yK + 30, 'π↾κ = id', { 'font-size': 12.5, fill: '#2f9e44', 'font-weight': 700 });
      if (step >= 5) txt(svg, 12, 76, '𝒫(κ) ⊆ L_κ⁺ ⇒ 2^κ = κ⁺', { 'font-size': 14, fill: '#ae3ec9', 'font-weight': 800 });
      if (step === 0) txt(svg, Apos.x + 12, Apos.y + 22, 'A ⊆ κ, A ∈ L_δ', { 'font-size': 12, fill: '#b35c00' });
    }
    const st = stepper('gcSteps', 'gcNext', 'gcAll', (k, instant) => draw(k, instant));
    $('gcReset').addEventListener('click', () => st.reset());
  })();

  /* ================= §7 flow + board ================= */
  (function flow() {
    const B = [
      ['Suppose ZFC + GCH + V = L ⊢ ⊥', '(a finite proof)', '设 ZFC + GCH + V = L ⊢ ⊥', '（一个有限证明）'],
      ['ZF ⊢ σᴸ for each', 'axiom σ of ZF (§4)', '对 ZF 的每条公理 σ', '有 ZF ⊢ σᴸ（§4）'],
      ['ZF ⊢ (V = L)ᴸ', '(§4)', 'ZF ⊢ (V = L)ᴸ', '（§4）'],
      ['ZF ⊢ (AC ∧ GCH)ᴸ', '(§5, §6 inside L)', 'ZF ⊢ (AC ∧ GCH)ᴸ', '（在 L 内用 §5、§6）'],
      ['Relativize the proof', 'of ⊥ to L: ZF ⊢ ⊥', '把推出 ⊥ 的证明', '相对化到 L：ZF ⊢ ⊥'],
      ['Con(ZF) ⇒ Con(ZFC +', 'GCH + V = L)', 'Con(ZF) ⇒ Con(ZFC +', 'GCH + V = L)'],
    ];
    const N = [
      ['Toward a contradiction. The proof uses finitely many axioms.', '用反证法。证明只用到有限条公理。'],
      ['Each σᴸ is a separate theorem of ZF, a scheme. We never claim “L is a model of ZF” as a single statement, which would give Con(ZF).', '每个 σᴸ 都是 ZF 的一个独立定理，构成定理模式。我们从不把“L 是 ZF 的模型”当作单个命题来断言，否则就推出了 Con(ZF)。'],
      ['By absoluteness of the L-hierarchy: Lᴸ = L.', '由 L 层级的绝对性：Lᴸ = L。'],
      ['ZF ⊢ “V = L → AC ∧ GCH” (the well-order &lt;<sub>L</sub> and condensation). Relativize this theorem to L and combine it with the previous box.', 'ZF ⊢ “V = L → AC ∧ GCH”（良序 &lt;<sub>L</sub> 与凝聚引理）。把这条定理相对化到 L，再与上一框结合。'],
      ['Every axiom used has been proved in ZF relativized to L, and relativization respects logical rules, so ⊥ᴸ, which is just ⊥, is a theorem of ZF.', '用到的每条公理都已在 ZF 中被证明（相对化到 L 后），而相对化保持逻辑规则，于是 ⊥ᴸ（就是 ⊥）是 ZF 的定理。'],
      ['Gödel 1938. Since ZFC + CH is consistent if ZF is, ZFC cannot prove ¬CH (assuming ZF is consistent). The argument is finitary, and no model of ZF is assumed.', '哥德尔 1938。既然 ZF 一致蕴涵 ZFC + CH 一致，ZFC 就证明不了 ¬CH（假设 ZF 一致）。整个论证是有穷的，没有假设 ZF 有模型。'],
    ];
    const svg = $('flSvg');
    let tok = 0;
    function layout(n) {
      const per = Math.ceil(n / 2), W = (720 - (per - 1) * 24) / per;
      return Array.from({ length: n }, (_, i) => { const row = i < per ? 0 : 1, col = row ? per - 1 - (i - per) : i; return { x: 20 + col * (W + 24), y: row ? 200 : 30, w: W, h: 96 }; });
    }
    function draw(lit = -1) {
      svg.innerHTML = '';
      arrowDefs(svg, 'fl');
      const P = layout(B.length);
      for (let i = 0; i + 1 < B.length; i++) {
        const a = P[i], b = P[i + 1];
        let x1, y1, x2, y2;
        if (a.y === b.y) { const dir = b.x > a.x ? 1 : -1; x1 = dir > 0 ? a.x + a.w : a.x; x2 = dir > 0 ? b.x : b.x + b.w; y1 = y2 = a.y + a.h / 2; }
        else { x1 = a.x + a.w / 2; x2 = b.x + b.w / 2; y1 = a.y + a.h; y2 = b.y; }
        el('line', { x1, y1, x2: x2 - Math.sign(x2 - x1) * 3, y2: y2 - Math.sign(y2 - y1) * 3, class: 'farrow', 'marker-end': 'url(#fl-g)' }, svg);
      }
      B.forEach((b, i) => {
        const p = P[i];
        const g = el('g', { class: 'fbox' + (i < lit ? ' done' : i === lit ? ' on' : ''), style: 'cursor:pointer' }, svg);
        el('rect', { x: p.x, y: p.y, width: p.w, height: p.h, rx: 12 }, g);
        const cx = p.x + p.w / 2;
        txt(g, cx, p.y + 22, b[0], { class: 'en', style: 'font-size:12.5px', 'font-weight': 700 });
        txt(g, cx, p.y + 38, b[1], { class: 'en', style: 'font-size:12px' });
        txt(g, cx, p.y + 62, b[2], { class: 'zh', style: 'font-size:12.5px', fill: '#4a5568' });
        txt(g, cx, p.y + 78, b[3], { class: 'zh', style: 'font-size:12px', fill: '#4a5568' });
        g.addEventListener('click', () => { tok++; draw(i); note(i); });
      });
    }
    const note = i => { $('flMsg').innerHTML = `<b>${i + 1}.</b> ` + bi(N[i][0], N[i][1]); };
    $('flRun').addEventListener('click', async () => {
      const my = ++tok;
      for (let i = 0; i < B.length; i++) { if (my !== tok) return; draw(i); note(i); await sleep(1600); }
      if (my === tok) draw(99);
    });
    $('flAll').addEventListener('click', () => { tok++; draw(99); $('flMsg').innerHTML = N.map((n, i) => `<b>${i + 1}.</b> ` + bi(n[0], n[1])).join(''); });
    draw();
    $('flMsg').innerHTML = bi('Press Run, or click any box.', '按“运行”，或点击任意方框。');

    const rows = [
      ['CH', 'CH', ['Con(ZF) ⇒ Con(ZFC + CH)', 'Gödel 1938, via L (this lesson). Hence ZFC ⊬ ¬CH.', '哥德尔 1938，借助 L（本课）。因此 ZFC ⊬ ¬CH。'], ['Con(ZF) ⇒ Con(ZFC + ¬CH)', 'Cohen 1963, forcing: add ℵ₂ Cohen reals to a ctm (Lesson 16). Hence ZFC ⊬ CH.', '科恩 1963，力迫法：向可数传递模型添加 ℵ₂ 个科恩实数（第 16 课）。因此 ZFC ⊬ CH。']],
      ['AC', 'AC', ['Con(ZF) ⇒ Con(ZF + AC)', 'Gödel 1938: L ⊨ AC (§5).', '哥德尔 1938：L ⊨ AC（§5）。'], ['Con(ZF) ⇒ Con(ZF + ¬AC)', 'Cohen 1963: a symmetric submodel of a forcing extension.', '科恩 1963：力迫扩张的对称子模型。']],
      ['V = L', 'V = L', ['Con(ZF) ⇒ Con(ZF + V = L)', 'Gödel: L ⊨ V = L (§4).', '哥德尔：L ⊨ V = L（§4）。'], ['Con(ZF) ⇒ Con(ZFC + V ≠ L)', 'Cohen: adding a single Cohen real already makes V ≠ L.', '科恩：只添加一个科恩实数就已使 V ≠ L。']],
    ];
    let h = `<div class="hd">${bil('statement X', '命题 X')}</div><div class="hd">${bil('X consistent', 'X 一致')}</div><div class="hd">${bil('¬X consistent', '¬X 一致')}</div>`;
    rows.forEach((r, i) => {
      h += `<div class="hd m">${r[0]}</div>`;
      h += `<div class="cell yes" data-b="${i}-0"><div class="stamp" style="color:var(--true)">✓ ${bil('Gödel', '哥德尔')}</div><div class="m" style="font-size:12px">${r[2][0]}</div></div>`;
      h += `<div class="cell todo" data-b="${i}-1"><div class="stamp" style="color:var(--meta)">→ L16 ${bil('Cohen', '科恩')}</div><div class="m" style="font-size:12px">${r[3][0]}</div></div>`;
    });
    $('board').innerHTML = h;
    document.querySelectorAll('#board [data-b]').forEach(c => c.addEventListener('click', () => {
      const [i, j] = c.dataset.b.split('-').map(Number);
      const r = rows[i][2 + j];
      $('boardMsg').innerHTML = `<b class="m">${r[0]}</b><br>` + bi(r[1], r[2]);
    }));
    $('boardMsg').innerHTML = bi('Green: proved in this lesson. Purple: needs forcing (Lesson 16). Together: CH is independent of ZFC.', '绿色：本课已证。紫色：需要力迫法（第 16 课）。两者合起来：CH 独立于 ZFC。');
  })();

  /* ================= §8 V = L consequences, 0# ================= */
  (function beyond() {
    const C = [
      ['GCH', 'GCH', '2<sup>κ</sup> = κ⁺ for every infinite κ (§6).', '对每个无穷基数 κ 有 2<sup>κ</sup> = κ⁺（§6）。'],
      ['◇ (diamond)', '◇（菱形原理）', 'Jensen: V = L implies ◇, a guessing principle on ω₁. ◇ implies CH and the existence of a Suslin tree, so Suslin\'s Hypothesis fails in L.', '詹森：V = L 蕴涵 ◇，这是 ω₁ 上的一种“猜测”原理。◇ 蕴涵 CH，并蕴涵苏斯林树存在，所以苏斯林假设在 L 中不成立。'],
      ['A definable well-order of ℝ', 'ℝ 的可定义良序', '&lt;<sub>L</sub> restricted to the reals is Δ¹₂. Consequently there is a Δ¹₂ set of reals that is not Lebesgue measurable: L is a world where “nice” projective sets can be pathological.', '&lt;<sub>L</sub> 限制在实数上是 Δ¹₂ 的。由此存在一个不是勒贝格可测的 Δ¹₂ 实数集：在 L 中，“好看”的投影集也可能很病态。'],
      ['No measurable cardinal (Scott 1961)', '没有可测基数（斯科特 1961）', 'Suppose V = L and κ is the least measurable. The ultrapower gives an elementary j : V → M with M transitive and j(κ) &gt; κ. By minimality M = L = V, so by elementarity j(κ) is the least measurable of V, which is κ. Contradiction.', '设 V = L，κ 为最小的可测基数。超幂给出初等嵌入 j : V → M，M 传递且 j(κ) &gt; κ。由最小性 M = L = V，再由初等性，j(κ) 是 V 中最小的可测基数，即 κ。矛盾。'],
      ['Inaccessibles are fine', '不可达基数不受影响', 'If κ is inaccessible in V, it is inaccessible in L: regularity goes down to L, and GCH<sup>L</sup> turns “limit cardinal” into “strong limit”. So V = L is compatible with inaccessibles.', '若 κ 在 V 中不可达，则它在 L 中也不可达：正则性向下传递到 L，而 GCH<sup>L</sup> 把“极限基数”变成“强极限”。所以 V = L 与不可达基数相容。'],
      ['Absoluteness of L', 'L 的绝对性', 'Every transitive model of ZF with all the ordinals contains the same L. So V = L is the most “economical” universe, and it settles CH, but at the cost of large cardinals.', '凡是包含全体序数的 ZF 传递模型，都含有同一个 L。所以 V = L 是最“节俭”的宇宙，它判定了 CH，代价是失去大基数。'],
    ];
    $('vlCards').innerHTML = C.map(c => `<div class="acard"><div class="ttl">${bil(c[0], c[1])}</div><div class="why">${bi(c[2], c[3])}</div></div>`).join('');
    document.querySelectorAll('#vlCards .acard').forEach(c => c.addEventListener('click', () => c.classList.toggle('open')));
    const svg = $('zsSvg');
    const AX = 210, AY = 315, hw = y => (AY - y) * 0.62;
    function draw(sharp) {
      svg.innerHTML = '';
      el('path', { d: `M${AX - hw(15)},15 L${AX},${AY} L${AX + hw(15)},15 Z`, fill: '#e7ecff', stroke: '#3b5bdb', 'stroke-width': 2 }, svg);
      txt(svg, AX - hw(15) + 10, 36, 'V', { 'font-size': 17, 'font-weight': 800, fill: '#3b5bdb' });
      const k = sharp ? 0.07 : 0.5;
      const p = el('path', { d: `M${AX - (AY - 15) * k},15 L${AX},${AY} L${AX + (AY - 15) * k},15 Z`, fill: 'rgba(47,158,68,.3)', stroke: '#2f9e44', 'stroke-width': 2 }, svg);
      p.classList.add('fadein');
      txt(svg, AX + (AY - 15) * k + 6, 36, 'L', { 'font-size': 17, 'font-weight': 800, fill: '#2f9e44' });
      el('line', { x1: AX, x2: AX, y1: AY, y2: 15, stroke: '#1f2430', 'stroke-dasharray': '3 3' }, svg);
      if (sharp) {
        [[240, 'ω₁'], [180, 'ω₂'], [120, 'ℵ_ω₊₁'], [60, 'κ']].forEach(([y, lab]) => {
          el('circle', { cx: AX, cy: y, r: 5, fill: '#ae3ec9' }, svg);
          txt(svg, AX - 12, y + 4, lab, { 'font-size': 12, 'text-anchor': 'end', fill: '#ae3ec9', 'font-weight': 700 });
        });
        txt(svg, AX + 22, 244, 'inaccessible in L · 在 L 中不可达', { 'font-size': 11, fill: '#ae3ec9' });
        txt(svg, 8, AY + 10, 'ℝ ∩ L is countable · ℝ ∩ L 可数', { 'font-size': 11.5, fill: '#2f9e44', 'font-weight': 700 });
      } else {
        el('ellipse', { cx: AX + 70, cy: 150, rx: 40, ry: 22, fill: 'none', stroke: '#f08c00', 'stroke-width': 2, 'stroke-dasharray': '4 3' }, svg);
        txt(svg, AX + 70, 154, 'X', { 'font-size': 13, 'text-anchor': 'middle', fill: '#b35c00', 'font-weight': 700 });
        el('ellipse', { cx: AX + 70, cy: 150, rx: 56, ry: 34, fill: 'none', stroke: '#2f9e44', 'stroke-width': 2 }, svg);
        txt(svg, AX + 70, 200, 'Y ∈ L, |Y| = |X|', { 'font-size': 12, 'text-anchor': 'middle', fill: '#2f9e44', 'font-weight': 700 });
        txt(svg, 8, AY + 10, 'covering · 覆盖引理', { 'font-size': 11.5, fill: '#2f9e44', 'font-weight': 700 });
      }
      $('zsNo').classList.toggle('sel', !sharp); $('zsYes').classList.toggle('sel', sharp);
      $('zsMsg').innerHTML = sharp
        ? bi('<b>If 0<sup>♯</sup> exists</b>, L is extremely thin. Every uncountable cardinal of V is inaccessible (indeed much more) in L, ω₁ in particular, so ℝ ∩ L is countable. 0<sup>♯</sup> follows from a measurable cardinal, so large cardinals make V far from L.',
          '<b>若 0<sup>♯</sup> 存在</b>，L 就极其“瘦”：V 中每个不可数基数在 L 中都是不可达的（实际上远不止于此），特别是 ω₁，因而 ℝ ∩ L 可数。可测基数蕴涵 0<sup>♯</sup> 存在，所以大基数让 V 远离 L。')
        : bi('<b>If 0<sup>♯</sup> does not exist</b>, Jensen\'s <b>Covering Lemma</b> says L is close to V: every uncountable set of ordinals X is covered by some Y ∈ L with |Y| = |X|. Consequently every singular cardinal κ is singular in L, and κ⁺ is computed correctly by L.',
          '<b>若 0<sup>♯</sup> 不存在</b>，詹森的<b>覆盖引理</b>说 L 与 V 很接近：每个不可数序数集 X 都能被某个 Y ∈ L 覆盖，且 |Y| = |X|。由此每个奇异基数 κ 在 L 中仍然奇异，并且 L 正确地算出 κ⁺。');
    }
    $('zsNo').addEventListener('click', () => draw(false));
    $('zsYes').addEventListener('click', () => draw(true));
    draw(false);
  })();

  /* ================= E1 parameter-free Def(3) ================= */
  (function e1() {
    const X = [0, 1, 2].map(HF.ord);
    const T = [
      { t: [0], a: '¬∃y∈x (y = y)' },
      { t: [1, 2], a: '∃y∈x (y = y)' },
      { t: [2], a: '∃y∈x ∃z∈y (z = z)' },
      { t: [1], a: '∃y∈x (y = y) ∧ ¬∃y∈x ∃z∈y (z = z)' },
    ].map(o => ({ ...o, target: o.t.map(HF.ord) }));
    const solved = T.map(() => false);
    let revealed = false;
    $('e1List').innerHTML = T.map((o, i) => `<div class="tf"><div class="stmt" style="flex:0 0 150px">${setStr(o.target)} =</div>
      <span class="m">{x ∈ 3 :</span><input class="formula" data-i="${i}" style="min-width:300px"><span class="m">}</span><span data-r="${i}" style="flex-basis:100%;font-size:14px"></span></div>`).join('');
    const inputs = [...document.querySelectorAll('#e1List input')];
    symKeys($('e1Keys'), inputs[0], FORMULA_KEYS);
    inputs.forEach(inp => inp.addEventListener('focus', () => { $('e1Keys')._target = inp; }));
    function check(i) {
      const inp = inputs[i], out = document.querySelector(`#e1List [data-r="${i}"]`);
      if (!inp.value.trim()) { out.innerHTML = ''; return; }
      let f;
      try { f = FO.parse(inp.value); } catch (e) { out.innerHTML = `<span style="color:var(--false)">${e.html ? e.html() : e.message}</span>`; return; }
      const fv = [...FO.free(f)];
      if (fv.some(v => v !== 'x')) { out.innerHTML = `<span style="color:var(--false)">${bil('only x may be free', '只允许 x 自由出现')}</span>`; return; }
      if (FO.consts(f).length) { out.innerHTML = `<span style="color:var(--false)">${bil('no parameters allowed here', '这里不允许用参数')}</span>`; return; }
      const got = defSubset(f, X);
      const ok = got.length === T[i].target.length && got.every(x => T[i].target.includes(x));
      out.innerHTML = ok ? `<span style="color:var(--true)">✓ ${bil('defines', '定义出')} ${setStr(got)}</span>` : `<span style="color:var(--false)">✗ ${bil('defines', '定义出')} ${setStr(got)}</span>`;
      if (ok && !revealed) { solved[i] = true; if (solved.every(Boolean)) { okBox($('e1Msg'), bi('✓ All four, without parameters. In fact every element of a finite transitive set is definable without parameters, because (X, ∈) has no nontrivial automorphisms.', '✓ 四个都不带参数地定义出来了。事实上，有限传递集的每个元素都不带参数可定义，因为 (X, ∈) 没有非平凡自同构。')); Progress.mark('L15E1'); } }
    }
    inputs.forEach((inp, i) => inp.addEventListener('input', () => check(i)));
    $('e1Show').addEventListener('click', () => {
      revealed = true;
      inputs.forEach((inp, i) => { inp.value = T[i].a; check(i); });
      okBox($('e1Msg'), bi('Idea: 0 is the empty element, 1 and 2 are nonempty, and 2 is the only one with a nonempty member (namely 1).', '思路：0 是空的；1 和 2 非空；只有 2 含有非空的元素（即 1）。'), 'info');
    });
  })();

  /* ================= E2 sizes ================= */
  (function e2() {
    const OPTS = ['16', '65 536', 'ℵ₀', 'ℵ₁', '2^ℵ₀', '2^(2^ℵ₀)', 'ℶ_ω₁'];
    const R = [['4', '16', '16'], ['ω', 'ℵ₀', 'ℵ₀'], ['ω+1', 'ℵ₀', '2^ℵ₀'], ['ω+2', 'ℵ₀', '2^(2^ℵ₀)'], ['ω₁', 'ℵ₁', 'ℶ_ω₁']];
    let revealed = false;
    const sel = c => `<select data-c="${c}"><option value="">?</option>${OPTS.map(o => `<option>${o}</option>`).join('')}</select>`;
    $('e2Table').innerHTML = `<table class="abs"><tr><th>α</th><th>|L<sub>α</sub>|</th><th>|V<sub>α</sub>|</th></tr>${R.map((r, i) => `<tr><td class="m">${r[0]}</td><td>${sel(i + '-1')}</td><td>${sel(i + '-2')}</td></tr>`).join('')}</table>`;
    const sels = [...document.querySelectorAll('#e2Table select')];
    function check(rev) {
      let ok = 0;
      sels.forEach(s => {
        const [i, j] = s.dataset.c.split('-').map(Number);
        if (rev) s.value = R[i][j];
        s.classList.remove('right', 'wrong');
        if (s.value === R[i][j]) { ok++; s.classList.add('right'); } else if (s.value) s.classList.add('wrong');
      });
      if (rev) { okBox($('e2Msg'), bi('L: |L<sub>α</sub>| = |α| for infinite α. V: |V<sub>ω+α</sub>| = ℶ<sub>α</sub>, and ω + ω₁ = ω₁. Without GCH we cannot simplify 2<sup>ℵ₀</sup> to ℵ₁.', 'L：α 无穷时 |L<sub>α</sub>| = |α|。V：|V<sub>ω+α</sub>| = ℶ<sub>α</sub>，且 ω + ω₁ = ω₁。不假设 GCH 时，2<sup>ℵ₀</sup> 不能化简为 ℵ₁。'), 'info'); return; }
      if (ok === sels.length) { okBox($('e2Msg'), bi('✓ All 10 correct.', '✓ 10 格全对。')); if (!revealed) Progress.mark('L15E2'); }
      else okBox($('e2Msg'), bi(`${ok} / 10 correct. Hint: |L<sub>α</sub>| = |α| for infinite α, and |V<sub>ω+α</sub>| = ℶ<sub>α</sub>.`, `答对 ${ok} / 10。提示：α 无穷时 |L<sub>α</sub>| = |α|，且 |V<sub>ω+α</sub>| = ℶ<sub>α</sub>。`), 'warn');
    }
    $('e2Check').addEventListener('click', () => check(false));
    $('e2Show').addEventListener('click', () => { revealed = true; check(true); });
  })();

  /* ================= E3 order the proof ================= */
  (function e3() {
    const steps = [
      ['Let A ⊆ κ. By V = L, A ∈ L<sub>δ</sub> for some limit δ > κ.', '设 A ⊆ κ。由 V = L，存在极限序数 δ > κ 使 A ∈ L<sub>δ</sub>。'],
      ['Take X ≺ L<sub>δ</sub> with κ ∪ {A} ⊆ X and |X| = κ (Löwenheim–Skolem).', '取 X ≺ L<sub>δ</sub>，使 κ ∪ {A} ⊆ X 且 |X| = κ（勒文海姆–斯科伦）。'],
      ['Collapse: π : (X, ∈) ≅ (M, ∈) with M transitive (Mostowski).', '坍塌：π : (X, ∈) ≅ (M, ∈)，M 传递（莫斯托夫斯基）。'],
      ['π↾κ = id, so π(A) = A ∈ M.', 'π↾κ = id，故 π(A) = A ∈ M。'],
      ['Condensation: M = L<sub>γ</sub>, and |γ| = κ gives γ &lt; κ⁺.', '凝聚引理：M = L<sub>γ</sub>，由 |γ| = κ 得 γ &lt; κ⁺。'],
      ['So 𝒫(κ) ⊆ L<sub>κ⁺</sub>, and 2<sup>κ</sup> = κ⁺.', '所以 𝒫(κ) ⊆ L<sub>κ⁺</sub>，从而 2<sup>κ</sup> = κ⁺。'],
    ];
    const shuffled = [3, 5, 0, 4, 2, 1];
    let seq = [], revealed = false;
    function render() {
      $('e3Pool').innerHTML = '';
      $('e3Seq').innerHTML = '';
      shuffled.forEach(i => {
        const d = document.createElement('div');
        d.className = 'chip' + (seq.includes(i) ? ' used' : '');
        d.innerHTML = bi(steps[i][0], steps[i][1]);
        d.addEventListener('click', () => { if (seq.includes(i)) return; seq.push(i); render(); clearBox($('e3Msg')); });
        $('e3Pool').appendChild(d);
      });
      seq.forEach((i, k) => {
        const d = document.createElement('div');
        d.className = 'chip';
        d.innerHTML = `<b>${k + 1}.</b> ` + bi(steps[i][0], steps[i][1]);
        d.addEventListener('click', () => { seq.splice(k, 1); render(); });
        $('e3Seq').appendChild(d);
      });
    }
    render();
    $('e3Check').addEventListener('click', () => {
      const s = seq.join(',');
      if (s === '0,1,2,3,4,5' || s === '0,1,2,4,3,5') {
        okBox($('e3Msg'), bi('✓ Correct. (Steps 4 and 5 may be swapped: both only use the collapse.)', '✓ 正确。（第 4、5 步可以互换：两者都只用到坍塌。）'));
        if (!revealed) Progress.mark('L15E3');
      } else if (seq.length < steps.length) okBox($('e3Msg'), bi(`Place all ${steps.length} steps first.`, `请先把 ${steps.length} 步全部排上。`), 'warn');
      else {
        const k = seq.findIndex((v, i) => v !== [0, 1, 2, 3, 4, 5][i] && !(i === 3 && v === 4) && !(i === 4 && v === 3));
        okBox($('e3Msg'), bi(`Step ${k + 1} is out of place. Ask: what does this step need that only an earlier step provides?`, `第 ${k + 1} 步的位置不对。问问自己：这一步需要什么，而那是哪一步才提供的？`), 'bad');
      }
    });
    $('e3Show').addEventListener('click', () => { revealed = true; seq = [0, 1, 2, 3, 4, 5]; render(); okBox($('e3Msg'), bi('Find A, shrink to X (LS), collapse (Mostowski), observe that κ and A are fixed, apply condensation, count.', '找到 A，缩小成 X（LS），坍塌（莫斯托夫斯基），注意 κ 与 A 不动，用凝聚引理，最后计数。'), 'info'); });
  })();

  /* ================= E4 what holds in L ================= */
  (function e4() {
    const items = [
      ['AC', 'AC', true, 'The definable well-order &lt;<sub>L</sub> (§5).', '可定义良序 &lt;<sub>L</sub>（§5）。'],
      ['GCH', 'GCH', true, 'Condensation (§6).', '凝聚引理（§6）。'],
      ['Every subset of ω is constructible.', 'ω 的每个子集都可构成。', true, 'L ⊨ V = L, so in L every set, in particular every real, is constructible.', 'L ⊨ V = L，所以在 L 中每个集合（特别是每个实数）都可构成。'],
      ['2<sup>ℵ₀</sup> = ℵ₂', '2<sup>ℵ₀</sup> = ℵ₂', false, 'L ⊨ CH, i.e. 2<sup>ℵ₀</sup> = ℵ₁.', 'L ⊨ CH，即 2<sup>ℵ₀</sup> = ℵ₁。'],
      ['There is a measurable cardinal.', '存在可测基数。', false, 'Scott: V = L refutes measurables, and L ⊨ V = L.', '斯科特：V = L 否定可测基数的存在，而 L ⊨ V = L。'],
      ['0<sup>♯</sup> exists.', '0<sup>♯</sup> 存在。', false, '0<sup>♯</sup> is not constructible; L ⊨ “0<sup>♯</sup> does not exist”.', '0<sup>♯</sup> 不可构成；L ⊨ “0<sup>♯</sup> 不存在”。'],
      ['There is a Suslin tree.', '存在苏斯林树。', true, 'L ⊨ ◇, and ◇ yields a Suslin tree.', 'L ⊨ ◇，而 ◇ 可造出苏斯林树。'],
      ['ω₁ is inaccessible.', 'ω₁ 是不可达基数。', false, 'ω₁ is a successor cardinal in any model. (But ω₁<sup>V</sup> may be inaccessible <i>in L</i> if 0<sup>♯</sup> exists. That is a different statement!)', 'ω₁ 在任何模型中都是后继基数。（但若 0<sup>♯</sup> 存在，ω₁<sup>V</sup> 可能<i>在 L 中</i>是不可达的，那是另一回事！）'],
    ];
    const solved = items.map(() => false), shown = items.map(() => false);
    items.forEach((it, i) => {
      const row = document.createElement('div');
      row.className = 'tf';
      row.innerHTML = `<div class="stmt" style="font-family:var(--sans);font-size:15px">σ = ${it[0] === it[1] ? `<span class="m">${it[0]}</span>` : bi(it[0], it[1])}</div>
        <button class="btn small" data-v="1">ZF ⊢ σ<sup>L</sup></button>
        <button class="btn small" data-v="0">ZF ⊢ ¬σ<sup>L</sup></button>
        <button class="btn small ghost" data-v="show">${bil('Show answer', '看答案')}</button>
        <div style="flex-basis:100%"><div class="msg"></div></div>`;
      $('e4List').appendChild(row);
      row.querySelectorAll('button').forEach(b => b.addEventListener('click', () => {
        const msg = row.querySelector('.msg');
        if (b.dataset.v === 'show') { shown[i] = true; okBox(msg, (it[2] ? 'σ<sup>L</sup>. ' : '¬σ<sup>L</sup>. ') + bi(it[3], it[4]), 'info'); return; }
        if ((b.dataset.v === '1') === it[2]) {
          okBox(msg, '✓ ' + bi(it[3], it[4]));
          if (!shown[i]) solved[i] = true;
          if (solved.every(Boolean)) Progress.mark('L15E4');
        } else okBox(msg, bi('✗ Remember that L ⊨ V = L, and think about what V = L implies.', '✗ 记住 L ⊨ V = L，再想想 V = L 蕴涵什么。'), 'bad');
      }));
    });
  })();

  /* ================= E5 first stage ================= */
  (function e5() {
    const R = [['3', '4'], ['ω', 'ω+1'], ['{ω}', 'ω+2'], ['{∅, ω}', 'ω+2'], ['ω+ω', 'ω+ω+1'], ['ω₁', 'ω₁+1']];
    let revealed = false;
    $('e5List').innerHTML = R.map((r, i) => `<div class="tf"><div class="stmt">min{ α : ${r[0]} ∈ L<sub>α</sub> } =</div><input class="formula short" data-i="${i}"><span data-r="${i}"></span></div>`).join('');
    const norm = s => s.toLowerCase().replace(/\s/g, '').replace(/omega/g, 'ω').replace(/w/g, 'ω').replace(/ω1/g, 'ω₁');
    function check(rev) {
      let ok = 0;
      R.forEach((r, i) => {
        const inp = document.querySelector(`#e5List input[data-i="${i}"]`);
        if (rev) inp.value = r[1];
        const good = norm(inp.value) === r[1];
        if (good) ok++;
        document.querySelector(`#e5List [data-r="${i}"]`).innerHTML = inp.value ? (good ? ' <span style="color:var(--true)">✓</span>' : ' <span style="color:var(--false)">✗</span>') : '';
      });
      if (rev) { okBox($('e5Msg'), bi('Rule: an ordinal α first appears in L<sub>α+1</sub>, since α ⊆ L<sub>α</sub> but α ∉ L<sub>α</sub> (L<sub>α</sub> ∩ Ord = α). {ω} and {∅, ω} are subsets of L<sub>ω+1</sub>, definable there with parameter ω, and they have rank ω+1, so they first appear in L<sub>ω+2</sub>.', '规律：序数 α 首次出现在 L<sub>α+1</sub>，因为 α ⊆ L<sub>α</sub> 而 α ∉ L<sub>α</sub>（L<sub>α</sub> ∩ Ord = α）。{ω} 与 {∅, ω} 是 L<sub>ω+1</sub> 的子集，在其上以 ω 为参数可定义，而它们的秩为 ω+1，所以首次出现在 L<sub>ω+2</sub>。'), 'info'); return; }
      if (ok === R.length) { okBox($('e5Msg'), bi('✓ All correct: α ∈ L<sub>α+1</sub> \\ L<sub>α</sub> for every ordinal α.', '✓ 全对：对每个序数 α 都有 α ∈ L<sub>α+1</sub> \\ L<sub>α</sub>。')); if (!revealed) Progress.mark('L15E5'); }
      else okBox($('e5Msg'), bi(`${ok} / ${R.length} correct. Use L<sub>α</sub> ∩ Ord = α, and that x ∈ L<sub>β+1</sub> requires x ⊆ L<sub>β</sub>.`, `答对 ${ok} / ${R.length}。利用 L<sub>α</sub> ∩ Ord = α，以及 x ∈ L<sub>β+1</sub> 要求 x ⊆ L<sub>β</sub>。`), 'warn');
    }
    $('e5Check').addEventListener('click', () => check(false));
    $('e5Show').addEventListener('click', () => { revealed = true; check(true); });
  })();

  /* ================= E6 why not ¬CH ================= */
  (function e6() {
    const opts = [
      [false, 'Because ZF cannot prove that L satisfies the axioms of ZF.', '因为 ZF 证明不了 L 满足 ZF 的公理。', 'No: ZF ⊢ σᴸ for every axiom σ (§4).', '不对：对每条公理 σ 都有 ZF ⊢ σᴸ（§4）。'],
      [true, 'Because L ⊨ CH, and inner models only shrink the universe: if V = L, every inner model containing all ordinals equals L, so none can satisfy ¬CH.', '因为 L ⊨ CH，而内模型只会让宇宙变小：若 V = L，每个包含全体序数的内模型都等于 L，所以没有一个能满足 ¬CH。', 'Exactly. One must enlarge the universe instead: forcing.', '正是如此。必须改为扩大宇宙：力迫法。'],
      [false, 'Because CH is actually provable in ZFC.', '因为 CH 其实在 ZFC 中可证。', 'No: that is exactly what Lesson 16 refutes, assuming ZF is consistent.', '不对：第 16 课恰好会否定这一点（假设 ZF 一致）。'],
      [false, 'Because Gödel\'s second incompleteness theorem forbids all relative consistency proofs.', '因为哥德尔第二不完全性定理禁止一切相对一致性证明。', 'No: Gödel 2 forbids proving Con(ZF) in ZF, not Con(ZF) ⇒ Con(ZF + X).', '不对：哥德尔第二定理禁止的是在 ZF 中证明 Con(ZF)，而不是 Con(ZF) ⇒ Con(ZF + X)。'],
    ];
    let shown = false;
    opts.forEach(o => {
      const b = document.createElement('button');
      b.className = 'btn choice';
      b.innerHTML = bi(o[1], o[2]);
      b.addEventListener('click', () => {
        $('e6Choices').querySelectorAll('.choice').forEach(x => x.classList.remove('right', 'wrongc'));
        b.classList.add(o[0] ? 'right' : 'wrongc');
        okBox($('e6Msg'), (o[0] ? '✓ ' : '✗ ') + bi(o[3], o[4]), o[0] ? 'ok' : 'bad');
        if (o[0] && !shown) Progress.mark('L15E6');
      });
      $('e6Choices').appendChild(b);
    });
    $('e6Show').addEventListener('click', () => {
      shown = true;
      $('e6Choices').querySelectorAll('.choice')[1].classList.add('right');
      okBox($('e6Msg'), bi(opts[1][3] + ' (Shepherdson 1953 showed that inner-model methods cannot give Con(ZF + ¬CH).)', opts[1][4] + '（谢泼德森 1953 年证明了内模型方法给不出 Con(ZF + ¬CH)。）'), 'info');
    });
  })();
}

if (typeof document !== 'undefined') lesson15Main();
