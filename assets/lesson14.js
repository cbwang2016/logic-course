// Lesson 14: Models of ZFC and the cumulative hierarchy V.
// Pure part first (hereditarily finite sets, a small first-order evaluator, Mostowski collapse);
// it is exported for node unit tests. DOM code runs only in the browser.

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
/* ====================  pure: Mostowski collapse  ====================== */
/* ===================================================================== */
// ids: node ids; edges: [a, b] meaning a E b.  π(b) = { π(a) : a E b } on the well-founded part.
function mostowski(ids, edges) {
  const preds = new Map(ids.map(v => [v, []]));
  edges.forEach(([a, b]) => { if (preds.has(b) && preds.has(a) && !preds.get(b).includes(a)) preds.get(b).push(a); });
  const val = new Map();
  let changed = true;
  while (changed) {
    changed = false;
    for (const v of ids) {
      if (!val.has(v) && preds.get(v).every(u => val.has(u))) {
        val.set(v, HF.mk(preds.get(v).map(u => val.get(u))));
        changed = true;
      }
    }
  }
  const ill = ids.filter(v => !val.has(v));
  const order = ids.filter(v => val.has(v)).sort((a, b) => val.get(a).r - val.get(b).r);
  const sig = v => [...preds.get(v)].sort().join(',');
  const clashes = [];
  for (let i = 0; i < ids.length; i++) for (let j = i + 1; j < ids.length; j++) if (sig(ids[i]) === sig(ids[j])) clashes.push([ids[i], ids[j]]);
  const image = HF.mk(order.map(v => val.get(v)));
  return { val, order, ill, wf: ill.length === 0, clashes, ext: clashes.length === 0, preds, image };
}

if (typeof module !== 'undefined' && module.exports) module.exports = { HF, FO, mostowski, HFError };

/* ===================================================================== */
/* ============================  browser  =============================== */
/* ===================================================================== */
function lesson14Main() {
  Lang.init();
  Progress.paint();

  const $ = id => document.getElementById(id);
  const okBox = (box, html, kind = 'ok') => { box.className = 'msg ' + kind; box.innerHTML = html; };
  const clearBox = box => { box.className = 'msg'; box.innerHTML = ''; };
  const errBox = (box, e) => { box.className = 'msg bad'; box.innerHTML = e instanceof HFError ? e.html() : String(e.message || e); };
  const SUBD = '₀₁₂₃₄₅₆₇₈₉';
  const sub = n => String(n).split('').map(d => SUBD[d] || d).join('');
  const txt = (parent, x, y, s, attrs = {}) => { const t = el('text', Object.assign({ x, y }, attrs), parent); t.textContent = s; return t; };
  const boxHTML = (x, d = 0) => `<span class="nb d${d % 4}">${x.e.map(y => boxHTML(y, d + 1)).join('')}</span>`;
  const S = (x) => HF.show(x, true);

  function stepper(stepsId, nextId, allId) {
    const steps = [...document.querySelectorAll('#' + stepsId + ' .step')];
    let k = 1;
    steps[0].classList.add('on');
    $(nextId).addEventListener('click', () => {
      if (k < steps.length) steps[k++].classList.add('on');
      if (k >= steps.length) $(nextId).disabled = true;
    });
    $(allId).addEventListener('click', () => { steps.forEach(s => s.classList.add('on')); k = steps.length; $(nextId).disabled = true; });
  }
  function symKeys(container, input, syms) {
    syms.forEach(s => {
      const b = document.createElement('button');
      b.type = 'button';
      b.textContent = s;
      b.addEventListener('click', () => {
        const st = input.selectionStart ?? input.value.length, en = input.selectionEnd ?? input.value.length;
        input.value = input.value.slice(0, st) + s + input.value.slice(en);
        input.focus();
        input.setSelectionRange(st + s.length, st + s.length);
      });
      container.appendChild(b);
    });
  }
  function arrowDefs(svg, id) {
    const defs = el('defs', {}, svg);
    [['g', '#868e96'], ['p', '#ae3ec9'], ['r', '#e03131'], ['b', '#3b5bdb']].forEach(([s, c]) => {
      const m = el('marker', { id: `${id}-${s}`, viewBox: '0 0 10 10', refX: 9, refY: 5, markerUnits: 'userSpaceOnUse', markerWidth: 11, markerHeight: 11, orient: 'auto-start-reverse' }, defs);
      el('path', { d: 'M0,0 L10,5 L0,10 z', fill: c }, m);
    });
  }
  // directed edge between two circles of radius R; returns the path
  function edgePath(parent, A, B, R, cls, marker, bend = 0) {
    if (A === B) {
      return el('path', { d: `M${A.x - 9},${A.y - R + 2} C${A.x - 45},${A.y - R - 50} ${A.x + 45},${A.y - R - 50} ${A.x + 9},${A.y - R + 2}`, class: cls, 'marker-end': `url(#${marker})` }, parent);
    }
    const dx = B.x - A.x, dy = B.y - A.y, len = Math.hypot(dx, dy) || 1, ux = dx / len, uy = dy / len;
    const px = -uy * bend, py = ux * bend;
    const x1 = A.x + ux * R + px * 0.5, y1 = A.y + uy * R + py * 0.5, x2 = B.x - ux * (R + 3) + px * 0.5, y2 = B.y - uy * (R + 3) + py * 0.5;
    const mx = (x1 + x2) / 2 + px, my = (y1 + y2) / 2 + py;
    return el('path', { d: `M${x1},${y1} Q${mx},${my} ${x2},${y2}`, class: cls, 'marker-end': `url(#${marker})` }, parent);
  }

  function onVisible(node, fn) {
    if (!('IntersectionObserver' in window)) { fn(); return; }
    const io = new IntersectionObserver(es => { if (es.some(e => e.isIntersecting)) { io.disconnect(); fn(); } }, { threshold: 0.3 });
    io.observe(node);
  }

  /* ================= §1 the cone ================= */
  (function cone() {
    const svg = $('cone');
    const AX = 210, AY = 440;
    const hw = y => (AY - y) * 0.4;
    const LV = [
      { key: 0, lab: 'V₀', y: 440, size: '0' },
      { key: 1, lab: 'V₁', y: 405, size: '1' },
      { key: 2, lab: 'V₂', y: 365, size: '2' },
      { key: 3, lab: 'V₃', y: 318, size: '4' },
      { key: 4, lab: 'V₄', y: 262, size: '16' },
      { key: 5, lab: 'V₅', y: 200, size: '65 536' },
      { key: 'w', lab: 'V_ω', y: 125, size: 'ℵ₀' },
      { key: 'w1', lab: 'V_ω+1', y: 85, size: '2^ℵ₀' },
      { key: 'all', lab: 'V = ⋃V_α', y: 28, size: '' },
    ];
    const fills = ['#e7ecff', '#fff3bf', '#d3f9d8', '#f8e7fc'];
    let shown = 4, selected = 3;
    function draw(fadeFrom = 99) {
      svg.innerHTML = '';
      el('path', { d: `M${AX - hw(20)},20 L${AX},${AY} L${AX + hw(20)},20`, fill: 'none', stroke: '#d8d3c4', 'stroke-dasharray': '4 5' }, svg);
      for (let k = 1; k <= shown; k++) {
        const lo = LV[k - 1], hi = LV[k];
        const pts = [[AX - hw(lo.y), lo.y], [AX + hw(lo.y), lo.y], [AX + hw(hi.y), hi.y], [AX - hw(hi.y), hi.y]];
        const poly = el('polygon', { points: pts.map(p => p.join(',')).join(' '), fill: fills[(k - 1) % 4], stroke: '#9aa0aa', 'stroke-width': 1, style: 'cursor:pointer' }, svg);
        if (k === selected) { poly.setAttribute('stroke', '#3b5bdb'); poly.setAttribute('stroke-width', 3); }
        if (k >= fadeFrom) poly.classList.add('fadein');
        poly.addEventListener('click', () => open(k));
        if (k === 6 || k === 8) txt(svg, AX + 40, (lo.y + hi.y) / 2 + 5, '⋮', { 'font-size': 18, fill: '#888', 'text-anchor': 'middle' });
      }
      // ordinal spine
      el('line', { x1: AX, y1: AY, x2: AX, y2: LV[shown].y, stroke: '#1f2430', 'stroke-width': 1.5, 'stroke-dasharray': '3 3' }, svg);
      for (let n = 0; n < Math.min(shown, 5); n++) {
        const y = (LV[n].y + LV[n + 1].y) / 2;
        el('circle', { cx: AX, cy: y, r: 4, fill: '#1f2430' }, svg);
        txt(svg, AX - 9, y + 4, String(n), { 'font-size': 11, 'text-anchor': 'end', fill: '#1f2430' });
      }
      if (shown >= 7) {
        const y = (LV[6].y + LV[7].y) / 2;
        el('circle', { cx: AX, cy: y, r: 4, fill: '#1f2430' }, svg);
        txt(svg, AX - 9, y + 4, 'ω', { 'font-size': 12, 'text-anchor': 'end' });
      }
      if (shown >= 8) txt(svg, AX, 14, 'Ord · 序数', { 'font-size': 11, 'text-anchor': 'middle', fill: '#555' });
      for (let k = 0; k <= shown; k++) {
        const L = LV[k];
        const g = el('g', { style: 'cursor:pointer' }, svg);
        const x = AX + hw(L.y) + 10;
        const t = txt(g, x, L.y + 4, L.lab, { 'font-size': 14, 'font-weight': 700, fill: k === selected ? '#3b5bdb' : '#1f2430' });
        if (L.size) txt(g, x + t.getComputedTextLength() + 8, L.y + 4, '· ' + L.size, { 'font-size': 12, fill: '#6b7280' });
        el('line', { x1: AX - hw(L.y), x2: AX + hw(L.y), y1: L.y, y2: L.y, stroke: '#6b7280', 'stroke-width': 1 }, g);
        g.addEventListener('click', () => open(k));
      }
      txt(svg, 12, 452, 'rank 0 at the bottom · 底部秩为 0', { 'font-size': 11, fill: '#999' });
    }
    function open(k) {
      selected = k;
      draw();
      const L = LV[k], box = $('vlist');
      box.innerHTML = '';
      if (typeof L.key === 'number' && L.key <= 4) {
        const els = HF.V(L.key);
        const nNew = els.filter(x => x.r === L.key - 1).length;
        $('coneInfo').innerHTML = L.key === 0
          ? bi('V₀ = ∅: nothing at all. Every set is built from here.', 'V₀ = ∅：什么都没有。一切集合都从这里建起。')
          : bi(`<b>${L.lab} = 𝒫(V${sub(L.key - 1)})</b> has ${els.length} elements, ${nNew} of them new (gold, rank ${L.key - 1}).`,
            `<b>${L.lab} = 𝒫(V${sub(L.key - 1)})</b> 共有 ${els.length} 个元素，其中 ${nNew} 个是新的（金色框，秩为 ${L.key - 1}）。`);
        els.forEach((x, i) => {
          const d = document.createElement('div');
          d.className = 'vel pop' + (x.r === L.key - 1 ? ' new' : '');
          d.style.animationDelay = (i * 0.04) + 's';
          d.innerHTML = `<div>${boxHTML(x)}</div><div class="m">${HF.show(x)}</div><div class="rk">rank ${x.r} · #${HF.code(x)}</div>`;
          box.appendChild(d);
        });
      } else if (L.key === 5) {
        const V4 = HF.V(4), deep = V4.filter(x => x.r === 3);
        const seen = new Set();
        for (let t = 0; t < 40 && seen.size < 6; t++) {
          const pick = V4.filter(() => Math.random() < 0.22);
          pick.push(deep[Math.floor(Math.random() * deep.length)]);
          const x = HF.mk(pick);
          if (seen.has(x.k) || x.e.length > 6) continue;
          seen.add(x.k);
          const d = document.createElement('div');
          d.className = 'vel new pop';
          d.innerHTML = `<div>${boxHTML(x)}</div><div class="m">${S(x)}</div><div class="rk">rank 4</div>`;
          box.appendChild(d);
        }
        $('coneInfo').innerHTML = bi('<b>V₅ = 𝒫(V₄)</b> has 2¹⁶ = 65 536 elements, of which 65 536 − 16 = 65 520 are new. A few random new ones (digits abbreviate ordinals):',
          '<b>V₅ = 𝒫(V₄)</b> 有 2¹⁶ = 65 536 个元素，其中 65 536 − 16 = 65 520 个是新的。随机展示几个新元素（数字是序数的缩写）：');
      } else if (L.key === 'w') {
        $('coneInfo').innerHTML = bi('<b>V<sub>ω</sub> = ⋃<sub>n</sub> V<sub>n</sub></b>, the hereditarily finite sets. A countable union of finite sets, so countable. It contains every natural number n (rank n) but <b>not ω</b>, whose rank is ω.',
          '<b>V<sub>ω</sub> = ⋃<sub>n</sub> V<sub>n</sub></b>，即全体遗传有限集。它是可数个有限集之并，因而可数。它含有每个自然数 n（秩为 n），却<b>不含 ω</b>，因为 ω 的秩是 ω。');
      } else if (L.key === 'w1') {
        $('coneInfo').innerHTML = bi('<b>V<sub>ω+1</sub> = 𝒫(V<sub>ω</sub>)</b> already has size 2<sup>ℵ₀</sup> by Cantor. Here ω itself first appears, along with every subset of ω. The reals (coded as subsets of ω) live just above, in V<sub>ω+1</sub> and V<sub>ω+2</sub>.',
          '<b>V<sub>ω+1</sub> = 𝒫(V<sub>ω</sub>)</b> 由康托尔定理已有 2<sup>ℵ₀</sup> 个元素。ω 本身以及 ω 的所有子集都在这一层首次出现。实数（编码为 ω 的子集）就住在 V<sub>ω+1</sub>、V<sub>ω+2</sub> 这一带。');
      } else if (L.key === 'all') {
        $('coneInfo').innerHTML = bi('<b>V = ⋃<sub>α∈Ord</sub> V<sub>α</sub></b> is a proper class. Its spine is the class of ordinals: rank(α) = α. Under Foundation <b>every</b> set lies in some V<sub>α</sub> (§3).',
          '<b>V = ⋃<sub>α∈Ord</sub> V<sub>α</sub></b> 是真类，它的“脊柱”是全体序数：rank(α) = α。在正则公理下，<b>每个</b>集合都属于某个 V<sub>α</sub>（§3）。');
      }
    }
    $('coneGrow').addEventListener('click', () => { if (shown < LV.length - 1) { shown++; draw(shown); open(shown); } });
    $('coneAll').addEventListener('click', () => { const f = shown + 1; shown = LV.length - 1; draw(f); });
    $('coneReset').addEventListener('click', () => { shown = 1; open(1); });
    draw(1);
    open(3);
  })();

  /* ================= §2 rank ================= */
  function drawRankDag(stage, x) {
    stage.innerHTML = '';
    const nodes = HF.tc(x);
    const R = x.r;
    const layers = [];
    nodes.forEach(n => (layers[n.r] = layers[n.r] || []).push(n));
    const W = 760, GY = 64, H = (R + 1) * GY + 30;
    const svg = el('svg', { viewBox: `0 0 ${W} ${H}`, width: W, height: H, class: 'bigsvg' }, stage);
    arrowDefs(svg, 'rk');
    const pos = new Map();
    const legend = [];
    layers.forEach((L, r) => L.forEach((n, i) => {
      pos.set(n.k, { x: 110 + (i + 0.5) * (W - 130) / L.length, y: 26 + (R - r) * GY });
    }));
    const chain = HF.chain(x);
    const chainEdges = new Set(chain.slice(1).map((y, i) => y.k + '>' + chain[i].k));
    for (let r = 0; r <= R; r++) {
      const y = 26 + (R - r) * GY;
      el('line', { x1: 70, x2: W - 6, y1: y, y2: y, stroke: '#eee' }, svg);
      txt(svg, 8, y + 4, `rank ${r}`, { 'font-size': 12, fill: '#888' });
    }
    const gE = el('g', {}, svg), gN = el('g', {}, svg);
    nodes.forEach(n => n.e.forEach(y => {
      const A = pos.get(y.k), B = pos.get(n.k), ch = chainEdges.has(y.k + '>' + n.k);
      const skip = n.r - y.r - 1, side = (y.r % 2 ? 1 : -1);
      const cx = (A.x + B.x) / 2 + side * skip * 46, cy = (A.y + B.y) / 2;
      const p = el('path', { d: `M${A.x},${A.y - 13} Q${cx},${cy} ${B.x},${B.y + 15}`, fill: 'none', stroke: ch ? '#ae3ec9' : '#bbb', 'stroke-width': ch ? 4 : 1.5, 'marker-end': `url(#rk-${ch ? 'p' : 'g'})` }, gE);
      p.classList.add('fadein');
      p.style.animationDelay = (y.r * 0.25 + 0.1) + 's';
    }));
    const onChain = new Set(chain.map(c => c.k));
    nodes.forEach(n => {
      const P = pos.get(n.k);
      let lab = S(n);
      if (lab.length > 15) { lab = String.fromCharCode(65 + legend.length); legend.push([lab, n]); }
      const g = el('g', { transform: `translate(${P.x},${P.y})` }, gN);
      const inner = el('g', { class: 'pop' }, g);
      inner.style.animationDelay = (n.r * 0.25) + 's';
      const w = Math.max(30, lab.length * 8.5 + 14);
      el('rect', { x: -w / 2, y: -13, width: w, height: 26, rx: 8, fill: n === x ? '#e7ecff' : '#fff', stroke: onChain.has(n.k) ? '#ae3ec9' : '#9aa0aa', 'stroke-width': onChain.has(n.k) ? 3 : 1.5 }, inner);
      txt(inner, 0, 5, lab, { 'font-size': 13, 'text-anchor': 'middle', 'font-weight': 700 });
      const tt = el('title', {}, g); tt.textContent = HF.show(n);
    });
    return { chain, legend, nodes };
  }
  (function rank() {
    const inp = $('rkIn');
    function go() {
      let x;
      try { x = HF.parse(inp.value); clearBox($('rkErr')); } catch (e) { errBox($('rkErr'), e); return; }
      const { chain, legend, nodes } = drawRankDag($('rkStage'), x);
      const lines = nodes.slice().reverse().filter(n => n.r > 0).slice(0, 8).map(n =>
        `rank(${S(n)}) = max{${n.e.map(y => y.r).join(', ')}} + 1 = ${n.r}`);
      const leg = legend.length ? '<br>' + legend.map(([l, n]) => `<b>${l}</b> = ${S(n)}`).join(' &nbsp; ') : '';
      okBox($('rkOut'), `<span class="m"><b>rank(${S(x)}) = ${x.r}</b> &nbsp;⇒&nbsp; x ∈ V${sub(x.r + 1)} \\ V${sub(x.r)}</span><br>` +
        bi('Longest ∈-chain (purple): ', '最长 ∈-链（紫色）：') + `<span class="m">${chain.map(S).join(' ∋ ')}</span>` +
        `<br><span class="m" style="font-size:13px">${lines.join('<br>')}</span>` + leg + `<br><span class="muted" style="font-size:12px">${bi('Digits abbreviate von Neumann ordinals. Hover a node for its full form.', '数字是冯·诺伊曼序数的缩写，鼠标悬停可看完整写法。')}</span>`, 'info');
    }
    $('rkGo').addEventListener('click', go);
    $('rkEmpty').addEventListener('click', () => { const st = inp.selectionStart ?? inp.value.length; inp.value = inp.value.slice(0, st) + '∅' + inp.value.slice(inp.selectionEnd ?? st); inp.focus(); });
    inp.addEventListener('keydown', e => e.key === 'Enter' && go());
    document.querySelectorAll('[data-rk]').forEach(b => b.addEventListener('click', () => { inp.value = b.dataset.rk; go(); }));
    go();
  })();

  /* ================= §3 foundation ================= */
  (function foundation() {
    const svg = $('fdSvg');
    const presets = [
      { s: '{1, 2, 3}' }, { s: '{2, {1}, {{2}}, 4}' }, { s: '{3, {3}, {2, {3}}}' }, { s: '{{1}, {{1}}, {{{1}}}}' },
      { omega: true },
    ];
    let cur = null;
    presets.forEach((p, i) => {
      const b = document.createElement('button');
      b.className = 'btn small';
      b.innerHTML = p.omega ? bil('Ω = {Ω} (no Foundation)', 'Ω = {Ω}（无正则公理）') : `x = <span class="m">${p.s}</span>`;
      b.addEventListener('click', () => load(i));
      $('fdPresets').appendChild(b);
    });
    const Y = r => 300 - r * 50;
    function load(i) {
      const p = presets[i];
      svg.innerHTML = '';
      arrowDefs(svg, 'fd');
      if (p.omega) { cur = null; drawOmega(); return; }
      const x = HF.parse(p.s);
      const els = x.e.slice();
      const maxR = Math.max(...els.map(e => e.r));
      for (let r = 0; r <= maxR; r++) {
        el('line', { x1: 70, x2: 750, y1: Y(r), y2: Y(r), stroke: '#eee' }, svg);
        txt(svg, 6, Y(r) + 4, `rank ${r}`, { 'font-size': 12, fill: '#999' });
      }
      txt(svg, 750, 20, `x = ${S(x)}`, { 'font-size': 14, 'text-anchor': 'end', 'font-weight': 700, fill: '#3b5bdb' });
      const pos = new Map();
      els.forEach((e, j) => pos.set(e.k, { x: els.length === 1 ? 410 : 150 + j * 540 / (els.length - 1), y: Y(e.r) }));
      cur = { x, els, pos, layer: el('g', {}, svg), nodes: el('g', {}, svg) };
      els.forEach(e => {
        const P = pos.get(e.k);
        const g = el('g', { transform: `translate(${P.x},${P.y})`, style: 'cursor:pointer' }, cur.nodes);
        const lab = S(e), w = Math.max(34, lab.length * 9 + 16);
        e._rect = el('rect', { x: -w / 2, y: -15, width: w, height: 30, rx: 9, fill: '#e7ecff', stroke: '#3b5bdb', 'stroke-width': 2 }, g);
        txt(g, 0, 5, lab, { 'font-size': 14, 'text-anchor': 'middle', 'font-weight': 700 });
        g.addEventListener('click', () => test(e));
      });
      const minR = Math.min(...els.map(e => e.r));
      test(els.find(e => e.r === minR));
    }
    function test(m) {
      const { x, els, pos, layer } = cur;
      layer.innerHTML = '';
      els.forEach(e => e._rect.setAttribute('fill', '#e7ecff'));
      const P = pos.get(m.k);
      const ghosts = m.e.filter(y => !HF.mem(y, x));
      const inX = m.e.filter(y => HF.mem(y, x));
      ghosts.slice(0, 7).forEach((y, j) => {
        const gx = P.x + (j - (Math.min(ghosts.length, 7) - 1) / 2) * 44, gy = Y(y.r);
        el('line', { x1: gx, y1: gy - 10, x2: P.x, y2: P.y + 15, stroke: '#adb5bd', 'stroke-width': 1.5, 'stroke-dasharray': '4 3', 'marker-end': 'url(#fd-g)' }, layer);
        el('circle', { cx: gx, cy: gy, r: 11, fill: '#f1f3f5', stroke: '#adb5bd' }, layer);
        txt(layer, gx, gy + 4, S(y).length > 4 ? '·' : S(y), { 'font-size': 11, 'text-anchor': 'middle', fill: '#666' });
      });
      inX.forEach(y => {
        const Q = pos.get(y.k);
        edgePath(layer, { x: Q.x, y: Q.y }, { x: P.x, y: P.y }, 18, '', 'fd-r', 30).setAttribute('style', 'stroke:#e03131;stroke-width:3;fill:none');
        y._rect.setAttribute('fill', '#ffe3e3');
      });
      m._rect.setAttribute('fill', inX.length ? '#ffe3e3' : '#d3f9d8');
      const minR = Math.min(...els.map(e => e.r));
      if (!inX.length) okBox($('fdMsg'), `<span class="m">m = ${S(m)}: m ∩ x = ∅</span> ✓ ` + bi(`∈-minimal. Its members (grey) all have rank &lt; ${m.r}${m.r === minR ? ', below every element of x.' : '. It is not of least rank, but still minimal: minimal elements need not be unique.'}`,
        `是 ∈-极小元。它的元素（灰色）秩都小于 ${m.r}${m.r === minR ? '，比 x 的所有元素都低。' : '。它的秩并非最小，但仍是极小元：极小元未必唯一。'}`));
      else okBox($('fdMsg'), `<span class="m">m = ${S(m)}: m ∩ x = {${inX.map(S).join(', ')}} ≠ ∅</span> ✗ ` + bi('Not minimal: the red arrows show members of m that are also in x. Try the element of least rank.', '不是极小元：红色箭头指出 m 中同时属于 x 的元素。试试秩最小的那个。'), 'warn');
    }
    function drawOmega() {
      const g = el('g', {}, svg);
      el('circle', { cx: 380, cy: 190, r: 26, fill: '#ffe3e3', stroke: '#e03131', 'stroke-width': 3 }, g);
      txt(g, 380, 197, 'Ω', { 'font-size': 20, 'text-anchor': 'middle', 'font-weight': 700 });
      edgePath(g, { x: 380, y: 190 }, { x: 380, y: 190 }, 26, '', 'fd-r').setAttribute('style', 'stroke:#e03131;stroke-width:3;fill:none');
      txt(g, 380, 250, 'Ω ∈ Ω ∈ Ω ∈ …  rank(Ω) = ?', { 'font-size': 15, 'text-anchor': 'middle', fill: '#e03131' });
      txt(g, 380, 280, 'x = {Ω}: Ω ∩ x = {Ω} ≠ ∅', { 'font-size': 14, 'text-anchor': 'middle' });
      okBox($('fdMsg'), bi('Without Foundation, a “Quine atom” Ω = {Ω} is consistent with the other axioms. Then x = {Ω} has <b>no</b> ∈-minimal element, Ω has no rank, and Ω lies in no V<sub>α</sub>. Foundation is exactly what rules this out.',
        '去掉正则公理后，“奎因原子” Ω = {Ω} 与其余公理是相容的。此时 x = {Ω} <b>没有</b> ∈-极小元，Ω 没有秩，也不属于任何 V<sub>α</sub>。正则公理排除的正是这种情形。'), 'bad');
    }
    load(1);
    stepper('fdSteps', 'fdNext', 'fdAll');
  })();

  /* ================= §4 Mostowski collapse (editable graph) ================= */
  const GRAPH_PRESETS = {
    ord: { nodes: [['a', 320, 320], ['b', 220, 220], ['c', 380, 110]], edges: [['a', 'b'], ['a', 'c'], ['b', 'c']] },
    nontrans: { nodes: [['a', 200, 320], ['b', 120, 210], ['c', 160, 90], ['d', 380, 160], ['e', 520, 230]], edges: [['a', 'b'], ['b', 'c'], ['a', 'd'], ['c', 'd'], ['b', 'e'], ['d', 'e']] },
    noext: { nodes: [['a', 320, 320], ['b', 200, 200], ['c', 440, 200], ['d', 320, 80]], edges: [['a', 'b'], ['a', 'c'], ['b', 'd'], ['c', 'd']] },
    cycle: { nodes: [['a', 220, 160], ['b', 420, 160], ['c', 320, 320]], edges: [['a', 'b'], ['b', 'a'], ['c', 'a']] },
    clear: { nodes: [], edges: [] },
  };
  (function graph() {
    const svg = $('gSvg');
    let nodes = [], edges = [], sel = null, vals = null, status = null, token = 0;
    const R = 22;
    function load(name) {
      const p = GRAPH_PRESETS[name];
      nodes = p.nodes.map(([id, x, y]) => ({ id, x, y }));
      edges = p.edges.map(e => e.slice());
      sel = null; vals = null; status = null; token++;
      render();
      clearBox($('gMsg'));
      $('gSide').innerHTML = '';
    }
    function render() {
      svg.innerHTML = '';
      arrowDefs(svg, 'gm');
      el('rect', { x: 0, y: 0, width: 640, height: 380, fill: 'transparent', class: 'bg' }, svg);
      const pos = new Map(nodes.map(n => [n.id, n]));
      const gE = el('g', {}, svg), gN = el('g', {}, svg);
      edges.forEach(([a, b]) => {
        const rev = a !== b && edges.some(([c, d]) => c === b && d === a);
        edgePath(gE, pos.get(a), pos.get(b), R, 'gedge', 'gm-g', rev ? 22 : 0);
      });
      nodes.forEach(n => {
        let cls = 'gnode';
        if (sel === n.id) cls += ' sel';
        if (status) {
          if (status.ill.includes(n.id)) cls += ' ill';
          else if (status.clashIds.has(n.id)) cls += ' clash';
          else if (vals && vals.has(n.id)) cls += ' done';
        }
        const g = el('g', { class: cls, transform: `translate(${n.x},${n.y})`, style: 'cursor:grab' }, gN);
        el('circle', { r: R }, g);
        txt(g, 0, 0, n.id);
        if (vals && vals.has(n.id)) {
          let s = HF.show(vals.get(n.id));
          if (s.length > 20) s = S(vals.get(n.id));
          if (s.length > 22) s = s.slice(0, 20) + '…';
          const t = txt(g, 0, R + 16, s, { class: 'glabel', 'text-anchor': 'middle' });
          t.classList.add('fadein');
        }
        g.addEventListener('pointerdown', ev => {
          ev.stopPropagation();
          drag = { id: n.id, x0: ev.clientX, y0: ev.clientY, moved: false };
          svg.setPointerCapture(ev.pointerId);
        });
      });
      txt(svg, 8, 372, 'arrow a → b means a E b · 箭头 a → b 表示 a E b', { 'font-size': 11, fill: '#999' });
    }
    let drag = null;
    const toSvg = ev => { const p = svg.createSVGPoint(); p.x = ev.clientX; p.y = ev.clientY; return p.matrixTransform(svg.getScreenCTM().inverse()); };
    svg.addEventListener('pointermove', ev => {
      if (!drag) return;
      if (Math.hypot(ev.clientX - drag.x0, ev.clientY - drag.y0) > 4) drag.moved = true;
      if (!drag.moved) return;
      const p = toSvg(ev), n = nodes.find(m => m.id === drag.id);
      n.x = Math.max(R + 2, Math.min(640 - R - 2, p.x));
      n.y = Math.max(R + 40, Math.min(380 - R - 24, p.y));
      render();
    });
    svg.addEventListener('pointerup', () => {
      if (drag && !drag.moved) clickNode(drag.id);
      drag = null;
    });
    svg.addEventListener('pointerdown', () => { if (!drag) { sel = null; render(); } });
    function invalidate() { vals = null; status = null; token++; $('gSide').innerHTML = ''; clearBox($('gMsg')); }
    function clickNode(id) {
      if (sel === null) sel = id;
      else if (sel === id) sel = null;
      else {
        const k = edges.findIndex(([a, b]) => a === sel && b === id);
        if (k >= 0) edges.splice(k, 1); else edges.push([sel, id]);
        invalidate();
      }
      render();
    }
    $('gAdd').addEventListener('click', () => {
      const used = new Set(nodes.map(n => n.id));
      const id = 'abcdefghijklmnopq'.split('').find(c => !used.has(c));
      if (!id) return;
      nodes.push({ id, x: 60 + Math.random() * 520, y: 80 + Math.random() * 240 });
      invalidate(); render();
    });
    $('gDel').addEventListener('click', () => {
      if (sel === null) return;
      nodes = nodes.filter(n => n.id !== sel);
      edges = edges.filter(([a, b]) => a !== sel && b !== sel);
      sel = null; invalidate(); render();
    });
    document.querySelectorAll('[data-gp]').forEach(b => b.addEventListener('click', () => load(b.dataset.gp)));
    $('gUndo').addEventListener('click', () => { invalidate(); render(); });
    $('gCollapse').addEventListener('click', async () => {
      const my = ++token;
      sel = null;
      const res = mostowski(nodes.map(n => n.id), edges);
      vals = new Map();
      status = null;
      render();
      for (const v of res.order) {
        await sleep(450);
        if (my !== token) return;
        vals.set(v, res.val.get(v));
        render();
      }
      status = { ill: res.ill, clashIds: new Set(res.clashes.flat()) };
      render();
      let side = `<table class="abs"><tr><th>v</th><th>π(v)</th><th>rank</th></tr>`;
      nodes.slice().sort((a, b) => a.id.localeCompare(b.id)).forEach(n => {
        const x = res.val.get(n.id);
        side += `<tr><td class="m"><b>${n.id}</b></td><td class="m">${x ? HF.show(x) : '<span style="color:var(--false)">—</span>'}</td><td>${x ? x.r : '?'}</td></tr>`;
      });
      side += '</table>';
      if (res.wf && nodes.length) side += `<div class="m" style="font-size:13px">π[M] = ${HF.show(res.image)}</div>`;
      $('gSide').innerHTML = side;
      if (!nodes.length) { okBox($('gMsg'), bi('The empty model collapses to ∅.', '空模型坍塌为 ∅。'), 'info'); return; }
      if (!res.wf) {
        okBox($('gMsg'), bi(`<b>Not well-founded:</b> nodes ${res.ill.join(', ')} (red) sit on or above an infinite descending E-chain (a cycle). The recursion π(b) = {π(a) : a E b} never bottoms out there, so no collapse exists. Real ∈ is well-founded by Foundation.`,
          `<b>非良基：</b>节点 ${res.ill.join('、')}（红色）位于一条无穷下降 E-链（一个圈）之上或其中。递归 π(b) = {π(a) : a E b} 在那里永远落不了底，所以坍塌不存在。而真正的 ∈ 由正则公理保证是良基的。`), 'bad');
      } else if (!res.ext) {
        const pairs = res.clashes.map(([u, v]) => `${u}, ${v}`).join('; ');
        okBox($('gMsg'), bi(`<b>Not extensional:</b> (${pairs}) have exactly the same E-predecessors, so π sends them to the same set (gold). π is onto a transitive set but <b>not injective</b>, hence not an isomorphism: (M, E) ⊭ Extensionality.`,
          `<b>不满足外延性：</b>（${pairs}）的 E-前驱完全相同，于是 π 把它们送到同一个集合（金色）。π 映满一个传递集，但<b>不是单射</b>，因此不是同构：(M, E) ⊭ 外延公理。`), 'warn');
      } else {
        okBox($('gMsg'), bi(`<b>Well-founded and extensional:</b> π is an isomorphism onto the <b>transitive</b> set π[M] (every element of a member is a member). E has become the real ∈.`,
          `<b>良基且外延：</b>π 是到<b>传递</b>集 π[M] 上的同构（成员的元素仍是成员）。E 变成了真正的 ∈。`));
      }
    });
    load('nontrans');
  })();

  /* ================= §5 absoluteness lab ================= */
  (function absLab() {
    const V4 = HF.V(4);
    let M = new Set(HF.V(3));
    const chips = $('mChips');
    function drawChips() {
      chips.innerHTML = `<div class="muted" style="font-size:13px">${bi('Elements of N = V₄; click to put into / take out of M (blue = in M). Digits abbreviate ordinals.', 'N = V₄ 的元素；点击放入或移出 M（蓝色 = 在 M 中）。数字是序数的缩写。')}</div>`;
      V4.forEach(x => {
        const s = document.createElement('span');
        s.className = 'pick' + (M.has(x) ? ' on' : '');
        s.textContent = S(x);
        s.title = HF.show(x);
        s.addEventListener('click', () => { if (M.has(x)) M.delete(x); else M.add(x); drawChips(); run(); });
        chips.appendChild(s);
      });
      const arr = [...M];
      const bad = arr.flatMap(y => y.e.filter(z => !M.has(z)).map(z => [y, z]));
      if (!bad.length) okBox($('mTrans'), bi(`M has ${arr.length} elements and is <b>transitive</b>.`, `M 有 ${arr.length} 个元素，是<b>传递</b>的。`));
      else okBox($('mTrans'), bi(`M is <b>not transitive</b>: e.g. ${S(bad[0][1])} ∈ ${S(bad[0][0])} ∈ M but ${S(bad[0][1])} ∉ M.`, `M <b>不是传递的</b>：例如 ${S(bad[0][1])} ∈ ${S(bad[0][0])} ∈ M，但 ${S(bad[0][1])} ∉ M。`), 'warn');
    }
    const presetsM = { V3: () => HF.V(3), ord: () => [0, 1, 2, 3].map(HF.ord), bad: () => ['∅', '{{∅}}', '{{{∅}}}'].map(HF.parse) };
    document.querySelectorAll('[data-mp]').forEach(b => b.addEventListener('click', () => { M = new Set(presetsM[b.dataset.mp]()); drawChips(); run(); }));
    const fPresets = [
      ['∃z∈y (z = z)', 'y ≠ ∅', 'y 非空'],
      ['∀z∈y ∀w∈z (w ∈ y)', 'y is transitive', 'y 是传递集'],
      ['∀z∈y ∀w∈z (w ∈ y) ∧ ∀z∈y ∀w∈y (z ∈ w ∨ z = w ∨ w ∈ z)', 'y is an ordinal', 'y 是序数'],
      ['∃z (y ∈ z)', 'y is an element of something', 'y 属于某个集合'],
      ['∃u ∀z (z ∈ y ↔ ∀w∈z (w ∈ u))', 'y = 𝒫(u) for some u', 'y 是某个 u 的幂集'],
    ];
    fPresets.forEach(([f, en, zh]) => {
      const b = document.createElement('button');
      b.className = 'btn small';
      b.innerHTML = bil(en, zh);
      b.addEventListener('click', () => { $('absIn').value = f; run(); });
      $('absPresets').appendChild(b);
    });
    symKeys($('absKeys'), $('absIn'), ['∀', '∃', '∈', '∉', '=', '≠', '¬', '∧', '∨', '→', '↔', '(', ')', '∅', 'y', 'z', 'w']);
    function run() {
      let f;
      try { f = FO.parse($('absIn').value); clearBox($('absErr')); } catch (e) { errBox($('absErr'), e); $('absOut').innerHTML = ''; return; }
      const fv = [...FO.free(f)];
      if (fv.some(v => v !== 'y')) { okBox($('absErr'), bi(`Only y may be free here; free: ${fv.join(', ')}.`, `这里只允许 y 自由出现；目前自由变元有：${fv.join(', ')}。`), 'bad'); $('absOut').innerHTML = ''; return; }
      const Marr = [...M].sort(HF.cmp);
      const badC = FO.consts(f).filter(c => !M.has(c));
      if (badC.length) { okBox($('absErr'), bi(`Parameter ${S(badC[0])} is not in M.`, `参数 ${S(badC[0])} 不在 M 中。`), 'bad'); $('absOut').innerHTML = ''; return; }
      const d0 = FO.isDelta0(f), trans = HF.transitive(Marr);
      const rows = fv.length ? Marr : [null];
      let mism = 0;
      let h = `<div class="m" style="font-size:16px;margin:8px 0">φ(y) = ${FO.fmt(f)} &nbsp; ${d0 ? '<span class="q bd">Δ₀</span>' : `<span class="q ub">${bil('not Δ₀', '非 Δ₀')}</span>`}</div>`;
      h += `<table class="abs"><tr><th>y</th><th>N = V₄ ⊨ φ[y]</th><th>M ⊨ φ[y]</th><th></th></tr>`;
      rows.forEach((y, i) => {
        const env = y ? { y } : {};
        const a = FO.sat(f, V4, env), b = FO.sat(f, Marr, env);
        if (a !== b) mism++;
        h += `<tr class="row-in${a !== b ? ' flip' : ''}" style="animation-delay:${i * 0.05}s"><td class="m">${y ? S(y) : '—'}</td><td class="v${+a}">${a ? '✓ true' : '✗ false'}</td><td class="v${+b}">${b ? '✓ true' : '✗ false'}</td><td>${a !== b ? bil('differs!', '不一致！') : ''}</td></tr>`;
      });
      h += '</table>';
      let verdict;
      if (d0 && trans) verdict = `<div class="msg ok">${bi('Δ₀ formula + transitive M ⇒ the theorem guarantees agreement, and indeed every row agrees.', 'Δ₀ 公式 + 传递的 M ⇒ 定理保证结果一致，果然每一行都一致。')}</div>`;
      else if (mism) verdict = `<div class="msg warn">${d0 ? bi(`${mism} row(s) differ even though φ is Δ₀, because M is <b>not transitive</b>: a bounded quantifier ∃z∈y searches y ∩ M, which can be smaller than y.`, `尽管 φ 是 Δ₀ 的，仍有 ${mism} 行不一致，因为 M <b>不是传递的</b>：有界量词 ∃z∈y 在 M 中只搜索 y ∩ M，它可能比 y 小。`)
        : bi(`${mism} row(s) differ: φ has an <b>unbounded</b> quantifier, whose witness lives in N but not in M.`, `有 ${mism} 行不一致：φ 含<b>无界</b>量词，它的证据在 N 里有，在 M 里没有。`)}</div>`;
      else verdict = `<div class="msg info">${bi('All rows agree this time, but nothing guarantees it. Try other M.', '这次每行都一致，但并没有定理保证。换个 M 试试。')}</div>`;
      $('absOut').innerHTML = h + verdict;
    }
    $('absGo').addEventListener('click', run);
    $('absIn').addEventListener('keydown', e => e.key === 'Enter' && run());
    drawChips();
    run();
    stepper('absSteps', 'absNext', 'absAll');

    // catalogue
    const cat = [
      ['x ⊆ y', '∀z∈x (z ∈ y)', 1, 1, '', ''],
      ['x = ∅', '∀z∈x (z ≠ z)', 1, 1, '', ''],
      ['z = {x, y}', 'x ∈ z ∧ y ∈ z ∧ ∀w∈z (w = x ∨ w = y)', 1, 1, '', ''],
      ['y = ⋃x', '∀z∈y ∃w∈x (z ∈ w) ∧ ∀w∈x ∀z∈w (z ∈ y)', 1, 1, '', ''],
      ['x is transitive · x 是传递集', '∀y∈x ∀z∈y (z ∈ x)', 1, 1, '', ''],
      ['x is an ordinal · x 是序数', 'trans(x) ∧ ∀y∈x ∀z∈x (y ∈ z ∨ y = z ∨ z ∈ y)', 1, 1,
        'Uses Foundation: in ZF an ordinal is a transitive set linearly ordered by ∈; well-foundedness comes for free.', '用到正则公理：在 ZF 中，序数就是被 ∈ 线性序化的传递集，良基性自动成立。'],
      ['x = ω', 'x is a limit ordinal ∧ x ≠ ∅ ∧ ∀y∈x (y = ∅ ∨ ∃z∈y (y = z ∪ {z}))', 1, 1,
        'So every transitive model containing ω computes ω correctly: ω^M = ω.', '因此凡是含 ω 的传递模型都正确地算出 ω：ω^M = ω。'],
      ['x is finite · x 有限', '∃n∈ω ∃f (f : n → x bijective)', 0, 1,
        'Not Δ₀ as written, but ZF proves it equivalent to a Π₁ formula too (Δ₁^ZF), so it is absolute for transitive models of ZF.', '按字面不是 Δ₀，但 ZF 能证明它也等价于一个 Π₁ 公式（Δ₁^ZF），因此对 ZF 的传递模型绝对。'],
      ['y = 𝒫(x)', '∀z (z ⊆ x → z ∈ y) ∧ ∀z∈y (z ⊆ x)', 0, 0,
        'Π₁, so only downward absolute: 𝒫(x)^M = 𝒫(x) ∩ M. You saw this in the lab: M = 4 thinks 3 = 𝒫(2).', 'Π₁ 公式，只向下绝对：𝒫(x)^M = 𝒫(x) ∩ M。实验室里已经见过：M = 4 认为 3 = 𝒫(2)。'],
      ['x is countable · x 可数', '∃f (f : ω → x onto)', 0, 0,
        'Σ₁, upward absolute only: countable in M ⇒ countable in V, but not conversely (Skolem, §6).', 'Σ₁ 公式，只向上绝对：在 M 中可数 ⇒ 在 V 中可数，反之不然（斯科伦，§6）。'],
      ['κ is a cardinal · κ 是基数', 'κ is an ordinal ∧ ∀α∈κ ∀f ¬(f : α → κ onto)', 0, 0,
        'Π₁, downward absolute only: a cardinal of V is a cardinal of M, but ω₁^M may be countable in V.', 'Π₁ 公式，只向下绝对：V 中的基数在 M 中仍是基数，但 ω₁^M 在 V 中可能可数。'],
    ];
    const color = s => s.replace(/([∀∃])([a-zα-ωκ])(∈[a-zA-Zωκα-ω]+)?/g, (m, q, v, b) => `<span class="q ${b ? 'bd' : 'ub'}">${m}</span>`);
    let h = `<table class="abs"><tr><th>${bil('notion', '概念')}</th><th>${bil('defining formula', '定义公式')}</th><th>Δ₀?</th><th>${bil('absolute for transitive M ⊨ ZF?', '对 ZF 的传递模型绝对？')}</th></tr>`;
    cat.forEach((c, i) => {
      h += `<tr data-cat="${i}" style="cursor:pointer"><td>${c[0]}</td><td class="m">${color(c[1])}</td><td class="v${c[2]}">${c[2] ? '✓' : '✗'}</td><td class="v${c[3]}">${c[3] ? '✓' : '✗'}</td></tr>`;
    });
    $('catTable').innerHTML = h + '</table>';
    document.querySelectorAll('[data-cat]').forEach(tr => tr.addEventListener('click', () => {
      const c = cat[+tr.dataset.cat];
      $('catOut').innerHTML = `<b class="m">${c[0]}</b>: <span class="m">${color(c[1])}</span><br>` +
        (c[4] ? bi(c[4], c[5]) : bi('Every quantifier is bounded, so it is Δ₀ and absolute for all transitive classes.', '所有量词都有界，所以是 Δ₀ 公式，对一切传递类绝对。'));
    }));
    $('catOut').innerHTML = bi('Click a row.', '点击某一行。');
  })();

  /* ================= §6 Skolem ================= */
  (function skolem() {
    const svg = $('skSvg');
    const N = 8, B = 14;
    let rows = [], view = 'V', diag = false;
    function newRows() { rows = Array.from({ length: N }, () => Array.from({ length: B }, () => Math.random() < 0.5 ? 1 : 0)); }
    function draw() {
      svg.innerHTML = '';
      arrowDefs(svg, 'sk');
      el('rect', { x: 4, y: 4, width: 752, height: 372, rx: 18, fill: view === 'V' ? '#fbfaf6' : '#f1f3f5', stroke: '#d8d3c4' }, svg);
      txt(svg, 20, 28, 'V', { 'font-size': 20, 'font-weight': 800, fill: view === 'V' ? '#1f2430' : '#bbb' });
      el('rect', { x: 150, y: 24, width: 480, height: 300, rx: 22, fill: '#fff', stroke: '#2f9e44', 'stroke-width': 3 }, svg);
      txt(svg, 166, 48, 'M  (countable transitive · 可数传递模型)', { 'font-size': 14, 'font-weight': 700, fill: '#2f9e44' });
      txt(svg, 205, 74, 'ω', { 'font-size': 15, 'font-weight': 700, 'text-anchor': 'middle' });
      txt(svg, 470, 74, '𝒫(ω)^M', { 'font-size': 15, 'font-weight': 700, 'text-anchor': 'middle' });
      for (let k = 0; k < N; k++) {
        const y = 100 + k * 26;
        el('circle', { cx: 205, cy: y - 4, r: 9, fill: '#e7ecff', stroke: '#3b5bdb' }, svg);
        txt(svg, 205, y, String(k), { 'font-size': 11, 'text-anchor': 'middle' });
        for (let j = 0; j < B; j++) {
          const on = diag && j === k;
          el('rect', { x: 360 + j * 16, y: y - 15, width: 14, height: 18, rx: 3, fill: rows[k][j] ? '#d3f9d8' : '#ffe3e3', stroke: on ? '#ae3ec9' : 'none', 'stroke-width': 2.5 }, svg);
          txt(svg, 367 + j * 16, y - 2, String(rows[k][j]), { 'font-size': 11, 'text-anchor': 'middle' });
        }
        txt(svg, 360 + B * 16 + 4, y - 2, '…', { 'font-size': 12, fill: '#999' });
        if (view === 'V') {
          const p = el('path', { d: `M216,${y - 4} C270,${y - 4} 300,${y - 6} 354,${y - 6}`, stroke: '#ae3ec9', 'stroke-width': 2, fill: 'none', 'stroke-dasharray': '5 3', 'marker-end': 'url(#sk-p)' }, svg);
          p.classList.add('fadein');
        }
      }
      txt(svg, 205, 100 + N * 26, '⋮', { 'font-size': 16, 'text-anchor': 'middle', fill: '#999' });
      txt(svg, 470, 100 + N * 26, '⋮', { 'font-size': 16, 'text-anchor': 'middle', fill: '#999' });
      if (view === 'V') {
        txt(svg, 282, 92, 'f ∈ V \\ M', { 'font-size': 13, fill: '#ae3ec9', 'font-weight': 700, 'text-anchor': 'middle' });
        txt(svg, 640, 360, 'V sees: 𝒫(ω)^M is countable · V 看来：𝒫(ω)^M 可数', { 'font-size': 13, 'text-anchor': 'end', fill: '#ae3ec9' });
      } else {
        txt(svg, 282, 92, 'f ∉ M', { 'font-size': 13, fill: '#bbb', 'font-weight': 700, 'text-anchor': 'middle' });
        txt(svg, 620, 314, 'M ⊨ “𝒫(ω) is uncountable” · M 认为 𝒫(ω) 不可数', { 'font-size': 13, 'text-anchor': 'end', fill: '#2f9e44', 'font-weight': 700 });
      }
      if (diag) {
        const y = 352;
        txt(svg, 344, y, 'd', { 'font-size': 15, 'font-weight': 800, fill: '#ae3ec9', 'text-anchor': 'end' });
        for (let j = 0; j < N; j++) {
          const g = el('g', { class: 'pop' }, svg);
          g.style.animationDelay = (j * 0.12) + 's';
          el('rect', { x: 360 + j * 16, y: y - 15, width: 14, height: 18, rx: 3, fill: '#f8e7fc', stroke: '#ae3ec9' }, g);
          txt(g, 367 + j * 16, y - 2, String(1 - rows[j][j]), { 'font-size': 11, 'text-anchor': 'middle', 'font-weight': 700 });
        }
        txt(svg, 360 + N * 16 + 8, y - 2, view === 'V' ? 'd ∉ M (outside the green box) · d 在 M 之外' : '', { 'font-size': 12, fill: '#ae3ec9' });
      }
    }
    function setView(v) {
      view = v;
      $('skV').classList.toggle('sel', v === 'V');
      $('skM').classList.toggle('sel', v === 'M');
      draw();
      msg();
    }
    function msg() {
      if (view === 'V') $('skMsg').innerHTML = bi('From outside, M is countable, so its subsets of ω can be listed as r₀, r₁, r₂, … by a function f. But f is <b>not an element of M</b>. ' + (diag ? 'The diagonal d differs from every rₖ, so d is a real of V that M lacks.' : ''),
        '从外面看，M 可数，所以它的 ω 子集可以由某个函数 f 排成 r₀, r₁, r₂, …。但 f <b>不是 M 的元素</b>。' + (diag ? '对角线 d 与每个 rₖ 都不同，所以 d 是 V 中有而 M 中没有的实数。' : ''));
      else $('skMsg').innerHTML = bi('Inside M there is no f at all: M ⊨ “no function from ω onto 𝒫(ω)”. ' + (diag ? 'M can run Cantor\'s argument against any list g that <i>belongs to M</i>; the diagonal then lies in M but not in the list. M\'s Cantor theorem is perfectly correct, about M\'s own functions.' : ''),
        '在 M 内部根本没有 f：M ⊨ “不存在从 ω 到 𝒫(ω) 的满射”。' + (diag ? 'M 可以对任何<i>属于 M</i> 的列表 g 做康托尔论证，得到的对角线在 M 里却不在 g 的值域里。M 的康托尔定理完全正确，只是它谈论的是 M 自己的函数。' : ''));
    }
    $('skV').addEventListener('click', () => setView('V'));
    $('skM').addEventListener('click', () => setView('M'));
    $('skDiag').addEventListener('click', () => { diag = true; draw(); msg(); });
    newRows();
    setView('V');

    // V/M table
    const T = [
      ['ω is an ordinal', 'ω 是序数', 'Δ₀', 1, 1],
      ['x = ω (for x = ω)', 'x = ω（取 x = ω）', 'Δ₀', 1, 1],
      ['{0, 1} ⊆ ω', '{0, 1} ⊆ ω', 'Δ₀', 1, 1],
      ['7 is finite', '7 是有限集', 'Δ₁<sup>ZF</sup>', 1, 1],
      ['P = 𝒫(ω), where P = 𝒫(ω)<sup>M</sup>', 'P = 𝒫(ω)，其中 P = 𝒫(ω)<sup>M</sup>', 'Π₁', 0, 1],
      ['P is uncountable', 'P 不可数', 'Π₁', 0, 1],
      ['ω₁<sup>M</sup> is an ordinal', 'ω₁<sup>M</sup> 是序数', 'Δ₀', 1, 1],
      ['ω₁<sup>M</sup> is a cardinal (uncountable)', 'ω₁<sup>M</sup> 是（不可数）基数', 'Π₁', 0, 1],
      ['there is a bijection ω → P', '存在双射 ω → P', 'Σ₁', 1, 0],
    ];
    let where = 'V';
    function table() {
      let h = `<table class="abs"><tr><th>${bil('statement', '命题')}</th><th>${bil('form', '复杂度')}</th><th>${where === 'V' ? bil('true in V?', '在 V 中成立？') : bil('true in M?', '在 M 中成立？')}</th></tr>`;
      T.forEach(r => {
        const v = where === 'V' ? r[3] : r[4];
        h += `<tr class="${r[3] !== r[4] ? 'flip' : ''}"><td>${bi(r[0], r[1])}</td><td class="m">${r[2]}</td><td class="v${v} pop" style="font-size:16px">${v ? '✓' : '✗'}</td></tr>`;
      });
      $('vmTable').innerHTML = h + `</table><div class="muted" style="font-size:13px">${bi('Gold rows are the ones that flip. None of them is Δ₀.', '金色行是翻转的那些，没有一个是 Δ₀ 的。')}</div>`;
    }
    $('tV').addEventListener('click', () => { where = 'V'; $('tV').classList.add('sel'); $('tM').classList.remove('sel'); table(); });
    $('tM').addEventListener('click', () => { where = 'M'; $('tM').classList.add('sel'); $('tV').classList.remove('sel'); table(); });
    table();
  })();

  /* ================= §7 V_α models ================= */
  (function closure() {
    let palette = ['∅', '1', '2', '{1}', '3', '{∅,{∅},{{∅}},{∅,{∅}}}'].map(HF.parse);
    let a = palette[2], b = palette[3], result = null;
    function drawPalette() {
      let h = '';
      ['a', 'b'].forEach(which => {
        h += `<div style="margin:4px 0"><b class="m">${which} =</b> `;
        palette.forEach((x, i) => {
          const on = (which === 'a' ? a : b) === x;
          h += `<span class="pick ${on ? (which === 'a' ? 'on' : 'on2') : ''}" data-w="${which}" data-i="${i}" title="${HF.show(x)}">${S(x)}</span>`;
        });
        h += '</div>';
      });
      $('cmPalette').innerHTML = h;
      document.querySelectorAll('#cmPalette .pick').forEach(s => s.addEventListener('click', () => {
        if (s.dataset.w === 'a') a = palette[+s.dataset.i]; else b = palette[+s.dataset.i];
        drawPalette();
      }));
    }
    function bars(items, omegaMode) {
      const svg = $('cmSvg');
      svg.innerHTML = '';
      el('line', { x1: 30, x2: 350, y1: 190, y2: 190, stroke: '#999' }, svg);
      el('line', { x1: 30, x2: 350, y1: 22, y2: 22, stroke: '#e03131', 'stroke-dasharray': '6 4' }, svg);
      txt(svg, 34, 16, 'rank ω: never reached · 永远到不了', { 'font-size': 11, fill: '#e03131' });
      const maxR = Math.max(8, ...items.map(it => it.r));
      const w = Math.min(60, 300 / items.length - 8);
      items.forEach((it, i) => {
        const h = (it.r / maxR) * 150;
        const x = 40 + i * (w + 8);
        const r = el('rect', { x, y: 190 - h, width: w, height: h, fill: it.c, rx: 4 }, svg);
        r.classList.add('fadein');
        txt(svg, x + w / 2, 186 - h, String(it.r), { 'font-size': 12, 'text-anchor': 'middle', 'font-weight': 700 });
        txt(svg, x + w / 2, 206, it.lab, { 'font-size': omegaMode ? 11 : 12, 'text-anchor': 'middle' });
      });
    }
    function apply(op) {
      const names = { pair: '{a, b}', union: '⋃a', power: '𝒫(a)', cup: 'a ∪ b', succ: 'a ∪ {a}' };
      if (op === 'power' && a.e.length > 4) { okBox($('cmMsg'), bi(`𝒫(a) would have 2^${a.e.length} elements, too many to draw here, but its rank is still rank(a) + 1 = ${a.r + 1}: finite.`, `𝒫(a) 有 2^${a.e.length} 个元素，太多画不下，但它的秩仍是 rank(a) + 1 = ${a.r + 1}，有限。`), 'info'); return; }
      result = { pair: () => HF.pair(a, b), union: () => HF.union(a), power: () => HF.power(a), cup: () => HF.cup(a, b), succ: () => HF.succ(a) }[op]();
      const two = op === 'pair' || op === 'cup';
      $('cmOut').innerHTML = `<div class="m" style="margin-bottom:6px">${names[op]} = ${S(result)}</div><div>${boxHTML(result)}</div>`;
      const items = [{ r: a.r, c: '#3b5bdb', lab: 'a' }];
      if (two) items.push({ r: b.r, c: '#f08c00', lab: 'b' });
      items.push({ r: result.r, c: '#2f9e44', lab: names[op] });
      bars(items);
      const rule = { pair: 'max(rank a, rank b) + 1', union: '≤ rank a', power: 'rank a + 1', cup: 'max(rank a, rank b)', succ: 'rank a + 1' }[op];
      okBox($('cmMsg'), `<span class="m">rank = ${result.r} (${rule})</span> · ` + bi('still finite, so the result is in V<sub>ω</sub>. Click the result chip below to reuse it.', '仍然有限，所以结果在 V<sub>ω</sub> 中。可以点下方芯片继续使用这个结果。'));
      if (!palette.includes(result) && result.e.length <= 16) { palette.push(result); if (palette.length > 12) palette.splice(6, 1); }
      drawPalette();
    }
    document.querySelectorAll('[data-op]').forEach(bn => bn.addEventListener('click', () => apply(bn.dataset.op)));
    let tok = 0;
    $('cmOmega').addEventListener('click', async () => {
      const my = ++tok;
      let x = HF.EMPTY;
      const items = [];
      for (let n = 0; n <= 7; n++) {
        if (my !== tok) return;
        items.push({ r: n, c: '#3b5bdb', lab: String(n) });
        bars(items, true);
        $('cmOut').innerHTML = `<div class="m">${n} = ${HF.show(x).length < 60 ? HF.show(x) : S(x)}</div><div>${boxHTML(x)}</div>`;
        x = HF.succ(x);
        await sleep(380);
      }
      okBox($('cmMsg'), bi('Each n ∈ V<sub>ω</sub>, with rank n. But ω = {0, 1, 2, …} would have rank sup(n + 1) = ω, so <b>ω ∉ V<sub>ω</sub></b>, and in fact no inductive set lies in V<sub>ω</sub>. V<sub>ω</sub> ⊨ ¬Infinity.',
        '每个 n 都在 V<sub>ω</sub> 中，秩为 n。但 ω = {0, 1, 2, …} 的秩是 sup(n + 1) = ω，所以 <b>ω ∉ V<sub>ω</sub></b>；事实上 V<sub>ω</sub> 中没有任何归纳集。V<sub>ω</sub> ⊨ ¬无穷公理。'), 'warn');
    });
    drawPalette();
    apply('pair');
  })();

  (function replacement() {
    const svg = $('repSvg');
    let tok = 0;
    function base() {
      svg.innerHTML = '';
      arrowDefs(svg, 'rp');
      el('rect', { x: 20, y: 60, width: 720, height: 190, rx: 12, fill: '#f4f6ff', stroke: '#3b5bdb' }, svg);
      txt(svg, 30, 78, 'V_ω+ω', { 'font-size': 13, 'font-weight': 700, fill: '#3b5bdb' });
      el('line', { x1: 20, x2: 740, y1: 60, y2: 60, stroke: '#3b5bdb', 'stroke-width': 3 }, svg);
      txt(svg, 736, 54, 'rank ω+ω', { 'font-size': 12, 'text-anchor': 'end', fill: '#3b5bdb' });
      txt(svg, 30, 226, 'ω = {0, 1, 2, …}', { 'font-size': 12, fill: '#555' });
    }
    const X = n => 200 + n * 58;
    const Yt = n => 72 + 120 * Math.pow(0.78, n);
    async function run() {
      const my = ++tok;
      base();
      for (let n = 0; n < 9; n++) {
        el('circle', { cx: X(n), cy: 222, r: 11, fill: '#fff', stroke: '#1f2430' }, svg);
        txt(svg, X(n), 226, String(n), { 'font-size': 11, 'text-anchor': 'middle' });
      }
      txt(svg, X(9), 226, '…', { 'font-size': 14 });
      for (let n = 0; n < 9; n++) {
        await sleep(260);
        if (my !== tok) return;
        const p = el('line', { x1: X(n), y1: 210, x2: X(n) + 20, y2: Yt(n) + 12, stroke: '#ae3ec9', 'stroke-width': 1.6, 'marker-end': 'url(#rp-p)' }, svg);
        p.classList.add('fadein');
        const g = el('g', { class: 'pop' }, svg);
        el('circle', { cx: X(n) + 22, cy: Yt(n), r: 10, fill: '#f8e7fc', stroke: '#ae3ec9' }, g);
        txt(g, X(n) + 22, Yt(n) - 14, n ? `ω+${n}` : 'ω', { 'font-size': 10, 'text-anchor': 'middle', fill: '#ae3ec9' });
      }
      await sleep(500);
      if (my !== tok) return;
      const g = el('g', { class: 'pop' }, svg);
      el('rect', { x: 230, y: 8, width: 300, height: 34, rx: 10, fill: '#ffe3e3', stroke: '#e03131', 'stroke-width': 2 }, g);
      txt(g, 380, 30, '{ω+n : n ∈ ω} has rank ω+ω ∉ V_ω+ω', { 'font-size': 13, 'text-anchor': 'middle', 'font-weight': 700, fill: '#8a1c1c' });
      txt(svg, 380, 56, '像集的秩为 ω+ω，跳出了 V_ω+ω', { 'font-size': 12, 'text-anchor': 'middle', fill: '#8a1c1c' });
    }
    base();
    $('repGo').addEventListener('click', run);
    onVisible(svg, run);
  })();

  (function ladder() {
    const svg = $('ladder');
    const rungs = [
      ['ZFC', 'ZFC', 'Proves Con(Φ) for each finite Φ ⊆ ZFC (via reflection, §8), but not Con(ZFC) itself (Gödel 2).', '对每个有限 Φ ⊆ ZFC 都能证明 Con(Φ)（借助反射原理，§8），但证明不了 Con(ZFC) 本身（哥德尔第二定理）。'],
      ['ZFC + Con(ZFC)', 'ZFC + Con(ZFC)', 'Proves Con(ZFC) by fiat. A model it provides may be ill-founded, with nonstandard integers.', '直接把 Con(ZFC) 作为公理。由它得到的模型可能非良基，带有非标准自然数。'],
      ['ZFC + ∃ transitive model of ZFC', 'ZFC + 存在 ZFC 的传递模型', 'Strictly stronger than Con(ZFC): it proves Con(ZFC + Con(ZFC)). By LS + collapse it gives a countable transitive model of ZFC.', '比 Con(ZFC) 严格更强：它能证明 Con(ZFC + Con(ZFC))。借助 LS 定理与坍塌，可得到 ZFC 的可数传递模型。'],
      ['ZFC + ∃ inaccessible κ', 'ZFC + 存在不可达基数 κ', 'V<sub>κ</sub> ⊨ ZFC; moreover V<sub>α</sub> ≺ V<sub>κ</sub> for many α &lt; κ, and these V<sub>α</sub> ∈ V<sub>κ</sub>, so V<sub>κ</sub> ⊨ “there is a transitive model of ZFC”.', 'V<sub>κ</sub> ⊨ ZFC；而且对许多 α &lt; κ 有 V<sub>α</sub> ≺ V<sub>κ</sub> 且 V<sub>α</sub> ∈ V<sub>κ</sub>，所以 V<sub>κ</sub> ⊨ “存在 ZFC 的传递模型”。'],
      ['ZFC + ∃ two inaccessibles', 'ZFC + 存在两个不可达基数', 'If κ₁ &lt; κ₂ are inaccessible, V<sub>κ₂</sub> ⊨ ZFC + IC.', '若 κ₁ &lt; κ₂ 都不可达，则 V<sub>κ₂</sub> ⊨ ZFC + IC。'],
      ['ZFC + ∃ measurable', 'ZFC + 存在可测基数', 'A measurable κ is the κ-th inaccessible, and much more. Its existence contradicts V = L (Scott, Lesson 15).', '可测基数 κ 是第 κ 个不可达基数，而且远不止于此。它的存在与 V = L 矛盾（斯科特，见第 15 课）。'],
    ];
    rungs.forEach((r, i) => {
      const y = 290 - i * 52;
      const g = el('g', { class: 'rung' }, svg);
      el('rect', { x: 30, y, width: 360, height: 38, rx: 10, fill: '#fff', stroke: '#c9c3b3', 'stroke-width': 2 }, g);
      txt(g, 210, y + 16, r[0], { 'font-size': 12.5, 'text-anchor': 'middle', 'font-weight': 700 });
      txt(g, 210, y + 31, r[1], { 'font-size': 11, 'text-anchor': 'middle', fill: '#555' });
      if (i) el('line', { x1: 14, x2: 14, y1: y + 52 + 30, y2: y + 14, stroke: '#ae3ec9', 'stroke-width': 2, 'marker-end': 'url(#ld-p)' }, svg);
      g.addEventListener('click', () => {
        svg.querySelectorAll('.rung').forEach(x => x.classList.remove('on'));
        g.classList.add('on');
        $('ladMsg').innerHTML = `<b>${bi(r[0], r[1])}</b>` + bi(r[2], r[3]);
      });
    });
    arrowDefs(svg, 'ld');
    txt(svg, 6, 14, 'stronger ↑ · 更强', { 'font-size': 11, fill: '#ae3ec9' });
    svg.querySelectorAll('.rung')[3].dispatchEvent(new Event('click'));
    stepper('incSteps', 'incNext', 'incAll');
  })();

  /* ================= §8 reflection ================= */
  (function reflection() {
    const svg = $('rfSvg');
    const AX = 190, AY = 340, hw = y => (AY - y) * 0.42;
    const axioms = [['Extensionality', '外延'], ['Pairing', '配对'], ['Union', '并集'], ['Power Set', '幂集'], ['Infinity', '无穷'], ['Replacement for one F', '某一条替换实例'], ['Choice', '选择']];
    const checks = axioms.map((a, i) => i < 4);
    axioms.forEach((a, i) => {
      const s = document.createElement('span');
      s.className = 'pick' + (checks[i] ? ' on' : '');
      s.innerHTML = bil(a[0], a[1]);
      s.addEventListener('click', () => { checks[i] = !checks[i]; s.classList.toggle('on', checks[i]); });
      $('rfChecks').appendChild(s);
    });
    let tok = 0, reflected = false;
    function base() {
      svg.innerHTML = '';
      arrowDefs(svg, 'rf');
      el('path', { d: `M${AX - hw(20)},20 L${AX},${AY} L${AX + hw(20)},20 Z`, fill: '#f4f6ff', stroke: '#9aa0aa' }, svg);
      txt(svg, AX, 40, 'V', { 'font-size': 18, 'font-weight': 800, 'text-anchor': 'middle' });
      el('line', { x1: 400, x2: 400, y1: 10, y2: 350, stroke: '#eee' }, svg);
    }
    async function reflect() {
      const my = ++tok;
      base();
      const n = checks.filter(Boolean).length;
      if (!n) { $('rfMsg').innerHTML = bi('Pick at least one formula.', '至少勾选一个公式。'); return; }
      const ys = [300, 240, 196, 164, 141, 125];
      for (let k = 0; k < ys.length; k++) {
        if (my !== tok) return;
        const y = ys[k];
        const ln = el('line', { x1: AX - hw(y), x2: AX + hw(y), y1: y, y2: y, stroke: '#3b5bdb', 'stroke-width': 1.5 }, svg);
        ln.classList.add('fadein');
        txt(svg, AX + hw(y) + 6, y + 4, `α${sub(k)}`, { 'font-size': 12, fill: '#3b5bdb' });
        if (k > 0) {
          for (let j = 0; j < Math.min(n, 5); j++) {
            const x0 = AX - hw(ys[k - 1]) * 0.7 + j * hw(ys[k - 1]) * 0.35;
            const x1 = x0 + 8;
            const p = el('line', { x1: x0, y1: ys[k - 1] - 2, x2: x1, y2: y + 6, stroke: '#f08c00', 'stroke-width': 1.3, 'marker-end': 'url(#rf-g)' }, svg);
            p.classList.add('fadein');
            el('circle', { cx: x1, cy: y + 4, r: 3, fill: '#f08c00' }, svg);
          }
        }
        $('rfMsg').innerHTML = k === 0 ? bi('Start anywhere: α₀.', '从任意 α₀ 出发。')
          : bi(`α${sub(k)}: for each of the ${n} chosen formulas and each existential subformula with parameters in V<sub>α${sub(k - 1)}</sub>, if V has a witness, put one below α${sub(k)} (orange).`,
            `α${sub(k)}：对所选 ${n} 个公式的每个存在型子公式，以及参数取自 V<sub>α${sub(k - 1)}</sub> 的每种情形，只要 V 中有证据，就在 α${sub(k)} 以下放一个（橙色）。`);
        await sleep(650);
      }
      if (my !== tok) return;
      txt(svg, AX, 112, '⋮', { 'font-size': 14, 'text-anchor': 'middle', fill: '#3b5bdb' });
      const y = 96;
      const ln = el('line', { x1: AX - hw(y), x2: AX + hw(y), y1: y, y2: y, stroke: '#ae3ec9', 'stroke-width': 4 }, svg);
      ln.classList.add('fadein');
      txt(svg, AX + hw(y) + 6, y + 4, 'α = sup αₖ', { 'font-size': 13, fill: '#ae3ec9', 'font-weight': 700 });
      el('path', { d: `M${AX - hw(y)},${y} L${AX},${AY} L${AX + hw(y)},${y} Z`, fill: 'rgba(174,62,201,.10)', stroke: 'none' }, svg);
      reflected = true;
      $('rfMsg').innerHTML = bi(`<b>V<sub>α</sub> reflects the ${n} chosen formulas:</b> each is true in V<sub>α</sub> iff it is true in V. Since they are axioms (true in V), V<sub>α</sub> ⊨ all of them. Only finitely many formulas: with infinitely many we would need a truth predicate for V (Tarski, Lesson 13).`,
        `<b>V<sub>α</sub> 反射了所选的 ${n} 个公式：</b>每个公式在 V<sub>α</sub> 中成立当且仅当它在 V 中成立。它们都是公理（在 V 中成立），所以 V<sub>α</sub> 满足它们全体。只能是有限个公式：若要无穷多个，就需要 V 的真谓词（塔斯基，第 13 课）。`);
    }
    async function ctm() {
      if (!reflected) await reflect();
      const my = ++tok;
      const boxes = [
        [420, 20, 'V_α  (huge · 巨大)', '#ae3ec9'],
        [420, 130, 'X ≺ V_α, |X| = ℵ₀  (LS)', '#3b5bdb'],
        [420, 240, 'M = π[X], transitive · 传递', '#2f9e44'],
      ];
      for (let k = 0; k < 3; k++) {
        if (my !== tok) return;
        const [x, y, lab, c] = boxes[k];
        const g = el('g', { class: 'fadein' }, svg);
        el('rect', { x, y, width: 320, height: 90, rx: 14, fill: '#fff', stroke: c, 'stroke-width': 2.5 }, g);
        txt(g, x + 12, y + 20, lab, { 'font-size': 13, 'font-weight': 700, fill: c });
        if (k === 0) for (let j = 0; j < 40; j++) el('circle', { cx: x + 20 + Math.random() * 280, cy: y + 32 + Math.random() * 50, r: 2.2, fill: j % 6 ? '#d0bfff' : '#ae3ec9' }, g);
        if (k === 1) for (let j = 0; j < 7; j++) el('circle', { cx: x + 30 + j * 40 + Math.random() * 10, cy: y + 40 + Math.random() * 40, r: 3.5, fill: '#3b5bdb' }, g);
        if (k === 2) {
          el('path', { d: `M${x + 110},${y + 30} L${x + 160},${y + 84} L${x + 210},${y + 30} Z`, fill: '#d3f9d8', stroke: '#2f9e44' }, g);
          for (let j = 0; j < 7; j++) el('circle', { cx: x + 160 + (j - 3) * 6, cy: y + 78 - j * 7, r: 3.5, fill: '#2f9e44' }, g);
        }
        if (k > 0) {
          const a = el('line', { x1: 580, x2: 580, y1: y - 18, y2: y - 2, stroke: c, 'stroke-width': 2.5, 'marker-end': 'url(#rf-b)' }, svg);
          a.classList.add('fadein');
          txt(svg, 592, y - 6, k === 1 ? 'Löwenheim–Skolem' : 'Mostowski collapse · 坍塌', { 'font-size': 11, fill: c });
        }
        await sleep(700);
      }
      $('rfMsg').innerHTML = bi('<b>Pipeline:</b> V<sub>α</sub> ⊨ Φ (reflection) → a countable X ≺ V<sub>α</sub> (downward LS), so X ⊨ Φ → X is well-founded and extensional (∈ is real), so it collapses to a <b>countable transitive M ⊨ Φ</b>. Each arrow is a theorem of ZFC, for this particular finite Φ.',
        '<b>流水线：</b>V<sub>α</sub> ⊨ Φ（反射原理）→ 取可数的 X ≺ V<sub>α</sub>（向下 LS 定理），于是 X ⊨ Φ → X 上的 ∈ 是真正的属于关系，良基且外延，于是坍塌成<b>可数传递模型 M ⊨ Φ</b>。对这个具体的有限 Φ，每一步都是 ZFC 的定理。');
    }
    base();
    $('rfGo').addEventListener('click', reflect);
    $('rfCtm').addEventListener('click', ctm);
    $('rfMsg').innerHTML = bi('Press Reflect.', '按“反射”开始。');
    onVisible(svg, reflect);
  })();

  /* ================= §9 flowchart ================= */
  (function flow() {
    const routes = {
      A: [
        ['Suppose ZF + X ⊢ ⊥', '(a finite proof)', '设 ZF + X ⊢ ⊥', '（一个有限证明）'],
        ['Define a class N = {x : θ(x)}', 'by a formula, e.g. L', '用公式定义类', 'N = {x : θ(x)}，如 L'],
        ['ZF ⊢ σᴺ for every', 'axiom σ of ZF + X', '对 ZF + X 的每条公理 σ', '都有 ZF ⊢ σᴺ'],
        ['Relativize each line', 'of the proof to N', '把证明的每一行', '都相对化到 N'],
        ['ZF ⊢ ⊥ᴺ, and ⊥ᴺ', 'is just ⊥: ZF ⊢ ⊥', 'ZF ⊢ ⊥ᴺ，而 ⊥ᴺ', '就是 ⊥：ZF ⊢ ⊥'],
        ['Hence Con(ZF) ⇒', 'Con(ZF + X)', '因此 Con(ZF) ⇒', 'Con(ZF + X)'],
      ],
      B: [
        ['Suppose ZF + X ⊢ ⊥', '', '设 ZF + X ⊢ ⊥', ''],
        ['The proof uses only', 'finitely many axioms Ψ', '证明只用到', '有限条公理 Ψ'],
        ['Pick finite Φ ⊆ ZF so that', 'ctm M ⊨ Φ ⇒ N ⊨ Ψ', '取有限 Φ ⊆ ZF，使', 'ctm M ⊨ Φ ⇒ N ⊨ Ψ'],
        ['ZF ⊢ ∃ ctm M ⊨ Φ', '(reflection+LS+collapse)', 'ZF ⊢ 存在 ctm M ⊨ Φ', '（反射 + LS + 坍塌）'],
        ['Build N from M,', 'e.g. N = M[G]; N ⊨ Ψ', '由 M 造出 N，', '如 N = M[G]；N ⊨ Ψ'],
        ['ZF ⊢ Con(Ψ), but', 'ZF ⊢ “Ψ ⊢ ⊥”: ZF ⊢ ⊥', 'ZF ⊢ Con(Ψ)，但又有', 'ZF ⊢ “Ψ ⊢ ⊥”：ZF ⊢ ⊥'],
        ['Hence Con(ZF) ⇒', 'Con(ZF + X)', '因此 Con(ZF) ⇒', 'Con(ZF + X)'],
      ],
    };
    const notes = {
      A: [
        ['Assume, toward a contradiction, that ZF + X is inconsistent. A proof is a finite object.', '用反证法：设 ZF + X 不一致。证明是一个有限对象。'],
        ['N is a class given by a formula θ. σᴺ means σ with every quantifier restricted to N.', 'N 是由公式 θ 给出的类。σᴺ 表示把 σ 的每个量词都限制到 N 上。'],
        ['This is the real work, e.g. ZF ⊢ (AC)^L and ZF ⊢ (GCH)^L in Lesson 15. Each is a separate theorem of ZF.', '这是真正的工作量，比如第 15 课的 ZF ⊢ (AC)^L 与 ZF ⊢ (GCH)^L。每一条都是 ZF 的一个独立定理。'],
        ['Logical rules are preserved by relativization (as long as N ≠ ∅), so the proof becomes a ZF-proof of each line relativized to N.', '只要 N 非空，逻辑规则在相对化下保持不变，于是原证明的每一行都变成 ZF 中关于 N 的定理。'],
        ['⊥ has no quantifiers, so relativizing does nothing. ZF itself is inconsistent.', '⊥ 不含量词，相对化后不变。于是 ZF 自身不一致。'],
        ['Contrapositive. Purely syntactic: no set model of ZF is ever needed, so Gödel 2 is not an obstacle. The argument is finitary and can even be carried out in PA.', '取逆否命题即得。这完全是语法层面的论证：从头到尾不需要 ZF 的集合模型，因此不与哥德尔第二定理冲突。整个论证是有穷的，甚至可以在 PA 中进行。'],
      ],
      B: [
        ['Again a finite proof of ⊥.', '同样，设有一个推出 ⊥ 的有限证明。'],
        ['Ψ is a finite set of axioms of ZF + X.', 'Ψ 是 ZF + X 中的有限条公理。'],
        ['Example: Lesson 16 shows for each axiom ψ of ZFC + ¬CH there is a finite Φ such that ZF ⊢ “if M is a ctm of Φ and G is M-generic, then M[G] ⊨ ψ”.', '例如第 16 课将证明：对 ZFC + ¬CH 的每条公理 ψ，都有有限的 Φ，使得 ZF ⊢ “若 M 是 Φ 的 ctm 且 G 是 M-脱殊的，则 M[G] ⊨ ψ”。'],
        ['§8: a theorem of ZF for this particular finite Φ. Not for all of ZF!', '§8：对这个特定的有限 Φ，这是 ZF 的定理。不是对整个 ZF！'],
        ['Countability of M is what makes generic filters exist (Lesson 16).', 'M 的可数性正是保证脱殊滤存在的关键（第 16 课）。'],
        ['A model of Ψ shows Ψ is consistent (soundness, provable in ZF). But “Ψ ⊢ ⊥” is a true finite fact, also provable in ZF. So ZF proves a contradiction.', '有模型就说明 Ψ 一致（可靠性定理，可在 ZF 中证明）。可“Ψ ⊢ ⊥”是一个真实的有限事实，ZF 也能证明它。于是 ZF 证出了矛盾。'],
        ['The same conclusion. Again only finite fragments are ever modelled, so Gödel 2 is respected.', '结论相同。整个过程只为有限片段造模型，因此与哥德尔第二定理并不冲突。'],
      ],
    };
    let route = 'A', tok = 0;
    const svg = $('flSvg');
    function layout(n) {
      const per = Math.ceil(n / 2), W = (720 - (per - 1) * 24) / per;
      return Array.from({ length: n }, (_, i) => {
        const row = i < per ? 0 : 1, col = row ? per - 1 - (i - per) : i;
        return { x: 20 + col * (W + 24), y: row ? 200 : 30, w: W, h: 96 };
      });
    }
    function draw(lit = -1) {
      svg.innerHTML = '';
      arrowDefs(svg, 'fl');
      const B = routes[route], P = layout(B.length);
      for (let i = 0; i + 1 < B.length; i++) {
        const a = P[i], b = P[i + 1];
        let x1, y1, x2, y2;
        if (a.y === b.y) { const dir = b.x > a.x ? 1 : -1; x1 = dir > 0 ? a.x + a.w : a.x; x2 = dir > 0 ? b.x : b.x + b.w; y1 = y2 = a.y + a.h / 2; }
        else { x1 = a.x + a.w / 2; x2 = b.x + b.w / 2; y1 = a.y + a.h; y2 = b.y; }
        el('line', { x1, y1, x2: x2 - Math.sign(x2 - x1) * 3, y2: y2 - Math.sign(y2 - y1) * 3, class: 'farrow', 'marker-end': 'url(#fl-g)' }, svg);
      }
      B.forEach((b, i) => {
        const p = P[i];
        const g = el('g', { class: 'fbox' + (i < lit ? ' done' : i === lit ? ' on' : '') }, svg);
        el('rect', { x: p.x, y: p.y, width: p.w, height: p.h, rx: 12 }, g);
        const cx = p.x + p.w / 2;
        txt(g, cx, p.y + 22, b[0], { class: 'en', style: 'font-size:12.5px', 'font-weight': 700 });
        txt(g, cx, p.y + 38, b[1], { class: 'en', style: 'font-size:12px' });
        txt(g, cx, p.y + 62, b[2], { class: 'zh', style: 'font-size:12.5px', fill: '#4a5568' });
        txt(g, cx, p.y + 78, b[3], { class: 'zh', style: 'font-size:12px', fill: '#4a5568' });
        g.style.cursor = 'pointer';
        g.addEventListener('click', () => { tok++; draw(i); note(i); });
      });
    }
    function note(i) { const n = notes[route][i]; $('flMsg').innerHTML = `<b>${i + 1}.</b> ` + bi(n[0], n[1]); }
    async function run() {
      const my = ++tok;
      for (let i = 0; i < routes[route].length; i++) {
        if (my !== tok) return;
        draw(i); note(i);
        await sleep(1600);
      }
      if (my === tok) draw(99);
    }
    function setRoute(r) { route = r; tok++; $('flA').classList.toggle('sel', r === 'A'); $('flB').classList.toggle('sel', r === 'B'); draw(); $('flMsg').innerHTML = bi('Press Run, or click any box.', '按“运行”，或点击任意方框。'); }
    $('flA').addEventListener('click', () => setRoute('A'));
    $('flB').addEventListener('click', () => setRoute('B'));
    $('flRun').addEventListener('click', run);
    $('flAll').addEventListener('click', () => {
      tok++;
      draw(99);
      $('flMsg').innerHTML = notes[route].map((n, i) => `<b>${i + 1}.</b> ` + bi(n[0], n[1])).join('');
    });
    setRoute('A');
  })();

  /* ================= E1 ranks ================= */
  (function e1() {
    let revealed = false;
    const items = [
      { s: '{{{∅}}, 2}' }, { s: '{{∅}, {{{∅}}}}' }, { s: 'V₃ = {∅, {∅}, {{∅}}, {∅,{∅}}}', p: '{∅,{∅},{{∅}},{∅,{∅}}}' },
      { s: '𝒫(3)', ans: 4 }, { s: 'ω', ans: 'ω' }, { s: '{ω, 5}', ans: 'ω+1' },
    ];
    items.forEach(it => { if (it.ans === undefined) it.ans = HF.parse(it.p || it.s).r; });
    $('e1List').innerHTML = items.map((it, i) => `<div class="tf"><div class="stmt">rank(${it.s}) =</div><input class="formula short" data-i="${i}"><span data-r="${i}"></span></div>`).join('');
    const norm = s => s.replace(/\s/g, '').replace(/omega|w/gi, 'ω');
    function check(reveal) {
      let ok = 0;
      items.forEach((it, i) => {
        const inp = document.querySelector(`#e1List input[data-i="${i}"]`);
        if (reveal) inp.value = it.ans;
        const good = norm(inp.value) === String(it.ans);
        if (good) ok++;
        document.querySelector(`#e1List [data-r="${i}"]`).innerHTML = inp.value ? (good ? '<span style="color:var(--true)">✓</span>' : '<span style="color:var(--false)">✗</span>') : '';
      });
      if (reveal) { okBox($('e1Msg'), bi('Answers: 3, 4, 3, 4, ω, ω+1. For 𝒫(3): it contains 3 itself, of rank 3, so its rank is 4. For {ω, 5}: rank ω has successor ω+1.', '答案：3, 4, 3, 4, ω, ω+1。𝒫(3) 含有 3 本身（秩 3），所以秩为 4；{ω, 5} 中 ω 的秩为 ω，再加一得 ω+1。'), 'info'); return; }
      if (ok === items.length) { okBox($('e1Msg'), bi('✓ All correct. rank(ω) = sup(n+1) = ω, and rank(x) = sup{rank(y)+1} works at infinite levels too.', '✓ 全对。rank(ω) = sup(n+1) = ω；公式 rank(x) = sup{rank(y)+1} 在无穷层同样适用。')); if (!revealed) Progress.mark('L14E1'); }
      else okBox($('e1Msg'), bi(`${ok} / ${items.length} correct. Use rank(x) = sup{rank(y) + 1 : y ∈ x}. Write ω as ω or w.`, `答对 ${ok} / ${items.length}。用 rank(x) = sup{rank(y) + 1 : y ∈ x}。ω 可写作 ω 或 w。`), 'warn');
    }
    $('e1Check').addEventListener('click', () => check(false));
    $('e1Show').addEventListener('click', () => { revealed = true; check(true); });
  })();

  /* ================= E2 V3 ================= */
  (function e2() {
    let revealed = false;
    const cands = ['∅', '{∅}', '{{{∅}}}', '{{∅}}', '{∅,{{∅}}}', '{∅,{∅}}', '{{∅,{∅}}}', '{∅,{∅},{{∅}}}'].map(s => ({ s, x: HF.parse(s), on: false }));
    function draw() {
      $('e2Chips').innerHTML = '';
      cands.forEach(c => {
        const d = document.createElement('span');
        d.className = 'pick' + (c.on ? ' on2' : '');
        d.style.fontSize = '15px';
        d.textContent = c.s;
        d.addEventListener('click', () => { c.on = !c.on; draw(); });
        c.el = d;
        $('e2Chips').appendChild(d);
      });
    }
    draw();
    function check(reveal) {
      if (reveal) { cands.forEach(c => c.on = c.x.r < 3); $('e2N').value = '65536'; draw(); }
      let right = 0;
      cands.forEach(c => { const good = c.on === (c.x.r < 3); if (good) right++; c.el.style.borderColor = good ? 'var(--true)' : 'var(--false)'; });
      const n = $('e2N').value.replace(/[\s,]/g, '');
      const nOk = ['65536', '2^16', '2¹⁶'].includes(n);
      if (reveal) { okBox($('e2Msg'), bi('V₃ = {∅, {∅}, {{∅}}, {∅,{∅}}}: exactly the sets of rank ≤ 2. The other four have rank 3 and first appear in V₄. |V₅| = 2^|V₄| = 2¹⁶ = 65 536.', 'V₃ = {∅, {∅}, {{∅}}, {∅,{∅}}}，恰为秩 ≤ 2 的集合。其余四个秩为 3，在 V₄ 中才首次出现。|V₅| = 2^|V₄| = 2¹⁶ = 65 536。'), 'info'); return; }
      if (right === cands.length && nOk) { okBox($('e2Msg'), bi('✓ Correct: x ∈ V₃ ⇔ rank(x) &lt; 3.', '✓ 正确：x ∈ V₃ ⇔ rank(x) &lt; 3。')); if (!revealed) Progress.mark('L14E2'); }
      else okBox($('e2Msg'), bi(`${right} / ${cands.length} chips right (green/red borders)${nOk ? '' : '; |V₅| not right yet'}. Hint: x ∈ V₃ iff rank(x) ≤ 2.`, `芯片判对 ${right} / ${cands.length}（绿/红边框）${nOk ? '' : '；|V₅| 还不对'}。提示：x ∈ V₃ 当且仅当 rank(x) ≤ 2。`), 'warn');
    }
    $('e2Check').addEventListener('click', () => check(false));
    $('e2Show').addEventListener('click', () => { revealed = true; check(true); });
  })();

  /* ================= E3 collapse by hand ================= */
  (function e3() {
    let revealed = false;
    const nodes = [{ id: 'a', x: 190, y: 225 }, { id: 'b', x: 90, y: 150 }, { id: 'c', x: 250, y: 140 }, { id: 'd', x: 70, y: 50 }, { id: 'e', x: 230, y: 45 }];
    const edges = [['a', 'b'], ['a', 'c'], ['b', 'c'], ['b', 'd'], ['c', 'e'], ['d', 'e']];
    const svg = $('e3Svg');
    arrowDefs(svg, 'e3');
    const pos = new Map(nodes.map(n => [n.id, n]));
    edges.forEach(([u, v]) => edgePath(svg, pos.get(u), pos.get(v), 20, 'gedge', 'e3-g'));
    nodes.forEach(n => { const g = el('g', { class: 'gnode', transform: `translate(${n.x},${n.y})` }, svg); el('circle', { r: 20 }, g); txt(g, 0, 0, n.id); });
    const res = mostowski(nodes.map(n => n.id), edges);
    $('e3Inputs').innerHTML = nodes.map(n => `<div class="toolbar"><b class="m">π(${n.id}) =</b> <input class="formula" data-n="${n.id}" style="min-width:200px"><span data-m="${n.id}"></span></div>`).join('');
    function check(reveal) {
      let ok = 0;
      nodes.forEach(n => {
        const inp = document.querySelector(`#e3Inputs input[data-n="${n.id}"]`);
        if (reveal) inp.value = HF.show(res.val.get(n.id));
        let good = false;
        try { good = HF.parse(inp.value) === res.val.get(n.id); } catch { good = false; }
        if (good) ok++;
        document.querySelector(`#e3Inputs [data-m="${n.id}"]`).innerHTML = inp.value ? (good ? ' <span style="color:var(--true)">✓</span>' : ' <span style="color:var(--false)">✗</span>') : '';
      });
      if (reveal) { okBox($('e3Msg'), bi('Work bottom-up: π(a) = ∅, π(b) = {∅} = 1, π(c) = {∅,{∅}} = 2, π(d) = {1} = {{∅}}, π(e) = {2, {1}}. The image {0, 1, 2, {1}, {2,{1}}} is transitive.', '自下而上计算：π(a) = ∅，π(b) = {∅} = 1，π(c) = {∅,{∅}} = 2，π(d) = {1} = {{∅}}，π(e) = {2, {1}}。像集 {0, 1, 2, {1}, {2,{1}}} 是传递的。'), 'info'); return; }
      if (ok === nodes.length) { okBox($('e3Msg'), bi('✓ All five correct. The image is transitive, and E has become ∈.', '✓ 五个全对。像集是传递的，E 变成了 ∈。')); if (!revealed) Progress.mark('L14E3'); }
      else okBox($('e3Msg'), bi(`${ok} / 5 correct. Start from the node with no incoming arrows: it collapses to ∅.`, `答对 ${ok} / 5。从没有入箭头的节点开始：它坍塌为 ∅。`), 'warn');
    }
    $('e3Check').addEventListener('click', () => check(false));
    $('e3Show').addEventListener('click', () => { revealed = true; check(true); });
  })();

  /* ================= E4 absolute or not ================= */
  (function e4() {
    let revealed = false;
    const cards = [
      ['x ⊆ y', 1], ['y = 𝒫(x)', 0], ['x is transitive · x 传递', 1], ['x is countable · x 可数', 0], ['x is an ordinal · x 是序数', 1],
      ['κ is a cardinal · κ 是基数', 0], ['x = ω', 1], ['f is a function · f 是函数', 1], ['x is uncountable · x 不可数', 0],
      ['y = ⋃x', 1], ['x is finite · x 有限', 1], ['κ = ω₁', 0],
    ].map(([h, a]) => ({ h, a, pos: 'tray' }));
    const order = ['tray', 'abs', 'not'];
    function render() {
      ['e4Tray', 'e4Abs', 'e4Not'].forEach(id => $(id).innerHTML = '');
      cards.forEach(c => {
        const d = document.createElement('div');
        d.className = 'chip m';
        d.textContent = c.h;
        d.addEventListener('click', () => { c.pos = order[(order.indexOf(c.pos) + 1) % 3]; render(); clearBox($('e4Msg')); });
        c.el = d;
        $({ tray: 'e4Tray', abs: 'e4Abs', not: 'e4Not' }[c.pos]).appendChild(d);
      });
    }
    render();
    function check(reveal) {
      if (reveal) { cards.forEach(c => c.pos = c.a ? 'abs' : 'not'); render(); }
      let right = 0;
      cards.forEach(c => { if (c.pos === 'tray') return; const ok = (c.pos === 'abs') === !!c.a; if (ok) right++; c.el.classList.add(ok ? 'ok' : 'no'); });
      if (reveal) { okBox($('e4Msg'), bi('Absolute: everything expressible by a Δ₀ formula (⊆, ⋃, transitive, ordinal, ω, function), plus “finite” (Δ₁ in ZF). Not absolute: power set, countable/uncountable, cardinal, ω₁, which all need an unbounded quantifier over functions or subsets.', '绝对的：凡能用 Δ₀ 公式表达的（⊆、⋃、传递、序数、ω、函数），再加上“有限”（在 ZF 中是 Δ₁ 的）。不绝对的：幂集、可数/不可数、基数、ω₁，它们都需要对函数或子集做无界量化。'), 'info'); return; }
      if (right === cards.length) { okBox($('e4Msg'), bi('✓ All correct. The dividing line: can you check it by looking only inside the sets involved?', '✓ 全对。分界线在于：能否只看相关集合的内部就判断出来？')); if (!revealed) Progress.mark('L14E4'); }
      else okBox($('e4Msg'), bi(`${right} / ${cards.length} correct. Ask: does the definition quantify over <i>all</i> sets (functions, subsets), or only over elements of the given sets?`, `答对 ${right} / ${cards.length}。问问自己：定义里是对<i>所有</i>集合（函数、子集）量化，还是只对给定集合的元素量化？`), 'warn');
    }
    $('e4Check').addEventListener('click', () => check(false));
    $('e4Show').addEventListener('click', () => { revealed = true; check(true); });
  })();

  /* ================= E5 grid ================= */
  (function e5() {
    let revealed = false;
    const ax = [['Extensionality', '外延公理'], ['Foundation', '正则公理'], ['Pairing', '配对公理'], ['Union', '并集公理'], ['Power set', '幂集公理'], ['Separation', '分离公理'], ['Replacement', '替换公理'], ['Infinity', '无穷公理'], ['Choice', '选择公理']];
    const cols = ['V<sub>ω</sub>', 'V<sub>ω+ω</sub>', 'V<sub>κ</sub>'];
    const ans = ax.map((a, i) => [i !== 7, i !== 6, true]);
    const user = ax.map(() => [null, null, null]);
    let h = `<table class="abs"><tr><th></th>${cols.map(c => `<th class="m" style="text-align:center">${c}</th>`).join('')}</tr>`;
    ax.forEach((a, i) => { h += `<tr><td>${bil(a[0], a[1])}</td>${cols.map((c, j) => `<td class="cell" data-i="${i}" data-j="${j}"></td>`).join('')}</tr>`; });
    $('e5Grid').innerHTML = h + '</table>';
    const cells = [...document.querySelectorAll('#e5Grid td.cell')];
    const paint = td => { const v = user[td.dataset.i][td.dataset.j]; td.textContent = v === null ? '' : v ? '✓' : '✗'; td.classList.remove('right', 'wrong'); };
    cells.forEach(td => td.addEventListener('click', () => {
      const i = +td.dataset.i, j = +td.dataset.j;
      user[i][j] = user[i][j] === null ? true : user[i][j] ? false : null;
      paint(td);
    }));
    function check(reveal) {
      let ok = 0;
      cells.forEach(td => {
        const i = +td.dataset.i, j = +td.dataset.j;
        if (reveal) user[i][j] = ans[i][j];
        paint(td);
        if (user[i][j] === ans[i][j]) { ok++; td.classList.add('right'); } else if (user[i][j] !== null) td.classList.add('wrong');
      });
      if (reveal) { okBox($('e5Msg'), bi('V<sub>ω</sub> fails only Infinity. V<sub>ω+ω</sub> (like every V<sub>λ</sub>, λ &gt; ω limit) fails only Replacement. V<sub>κ</sub> for inaccessible κ satisfies all of ZFC. Choice holds in each because a choice function on x ∈ V<sub>λ</sub> has rank only a few steps above x.', 'V<sub>ω</sub> 只有无穷公理不成立。V<sub>ω+ω</sub>（和任何极限 λ &gt; ω 的 V<sub>λ</sub> 一样）只有替换公理不成立。κ 不可达时 V<sub>κ</sub> 满足全部 ZFC。选择公理在三者中都成立：x ∈ V<sub>λ</sub> 上的选择函数，秩只比 x 高几层。'), 'info'); return; }
      if (ok === cells.length) { okBox($('e5Msg'), bi('✓ All 27 correct.', '✓ 27 格全对。')); if (!revealed) Progress.mark('L14E5'); }
      else okBox($('e5Msg'), bi(`${ok} / 27 correct. Each of V<sub>ω</sub> and V<sub>ω+ω</sub> fails exactly one axiom.`, `答对 ${ok} / 27。V<sub>ω</sub> 和 V<sub>ω+ω</sub> 各自恰有一条公理不成立。`), 'warn');
    }
    $('e5Check').addEventListener('click', () => check(false));
    $('e5Show').addEventListener('click', () => { revealed = true; check(true); });
  })();

  /* ================= E6 provable? ================= */
  (function e6() {
    const items = [
      { en: 'There is a countable transitive model of Extensionality + Pairing + Union + Power Set + Infinity.', zh: '存在“外延 + 配对 + 并集 + 幂集 + 无穷”的可数传递模型。', ans: true,
        xen: 'Provable. A finite fragment: reflect, then LS + collapse (§8). Here even V<sub>ω+ω</sub> already satisfies them.', xzh: '可证。这是有限片段：反射，再用 LS + 坍塌（§8）。其实 V<sub>ω+ω</sub> 本身就满足它们。' },
      { en: 'There is a countable transitive model of ZFC.', zh: '存在 ZFC 的可数传递模型。', ans: false,
        xen: 'Not provable: it implies Con(ZFC), contradicting Gödel 2. Each finite fragment has a ctm, but “each” is in the metatheory.', xzh: '不可证：它蕴涵 Con(ZFC)，与哥德尔第二定理矛盾。每个有限片段都有 ctm，但“每个”是元理论层面的说法。' },
      { en: 'Con(ZFC) → Con(ZFC + ∃ inaccessible).', zh: 'Con(ZFC) → Con(ZFC + 存在不可达基数)。', ans: false,
        xen: 'Not provable (if ZFC + IC is consistent): otherwise ZFC + IC would prove its own consistency (§7c).', xzh: '不可证（若 ZFC + IC 一致）：否则 ZFC + IC 将证明自身的一致性（§7c）。' },
      { en: 'If κ is inaccessible, then V<sub>κ</sub> ⊨ ZFC.', zh: '若 κ 不可达，则 V<sub>κ</sub> ⊨ ZFC。', ans: true,
        xen: 'Provable (§7c). The hypothesis is what ZFC cannot prove.', xzh: '可证（§7c）。ZFC 证明不了的是前提本身。' },
      { en: 'Con(ZFC) → Con(ZFC + there is no inaccessible).', zh: 'Con(ZFC) → Con(ZFC + 不存在不可达基数)。', ans: true,
        xen: 'Provable. Via an inner model (Route A, §9): relativize to V<sub>κ</sub> for the least inaccessible κ if there is one, else to V (§7c). Or directly: if ZFC + ¬IC ⊢ ⊥ then ZFC ⊢ IC, so ZFC ⊢ Con(ZFC), and Gödel 2 makes ZFC inconsistent.', xzh: '可证。用内模型（§9 路线 A）：若存在不可达基数，就相对化到最小者 κ 对应的 V<sub>κ</sub>，否则相对化到 V（§7c）。也可以直接论证：若 ZFC + ¬IC ⊢ ⊥，则 ZFC ⊢ IC，从而 ZFC ⊢ Con(ZFC)，由哥德尔第二定理 ZFC 不一致。' },
      { en: '(V<sub>ω</sub>, ∈) ⊨ ¬Infinity.', zh: '(V<sub>ω</sub>, ∈) ⊨ ¬无穷公理。', ans: true,
        xen: 'Provable: every element of V<sub>ω</sub> is finite, so no element is inductive (§7a).', xzh: '可证：V<sub>ω</sub> 的元素都是有限集，没有一个是归纳集（§7a）。' },
    ];
    const solved = items.map(() => false), shown = items.map(() => false);
    items.forEach((it, i) => {
      const row = document.createElement('div');
      row.className = 'tf';
      row.innerHTML = `<div class="stmt" style="font-family:var(--sans);font-size:15px">${String.fromCharCode(97 + i)}) ${bi(it.en, it.zh)}</div>
        <button class="btn small" data-v="1">${bil('Provable', '可证')}</button>
        <button class="btn small" data-v="0">${bil('Not provable', '不可证')}</button>
        <button class="btn small ghost" data-v="show">${bil('Show answer', '看答案')}</button>
        <div style="flex-basis:100%"><div class="msg"></div></div>`;
      $('e6List').appendChild(row);
      row.querySelectorAll('button').forEach(b => b.addEventListener('click', () => {
        const msg = row.querySelector('.msg');
        if (b.dataset.v === 'show') { shown[i] = true; okBox(msg, bi(it.xen, it.xzh), 'info'); return; }
        if ((b.dataset.v === '1') === it.ans) {
          okBox(msg, '✓ ' + bi(it.xen, it.xzh));
          if (!shown[i]) solved[i] = true;
          if (solved.every(Boolean)) Progress.mark('L14E6');
        } else okBox(msg, bi('✗ Not quite. Ask: would proving it let ZFC prove its own consistency (Gödel 2)?', '✗ 不对。问问自己：如果能证明它，ZFC 是否就能证明自身的一致性（哥德尔第二定理）？'), 'bad');
      }));
    });
  })();
}

if (typeof document !== 'undefined') lesson14Main();
