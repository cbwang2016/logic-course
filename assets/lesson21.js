// Lesson 21: ordinal notations & fast-growing hierarchies.
// Part A (ORD): pure math engine, no DOM; unit-testable with node.
// Part B: page interactions (only runs in a browser).

/* ======================================================================
   PART A · ordinal engine
   An ordinal below ε₀ is stored in Cantor normal form as an array of
   [exponent, coefficient] pairs with strictly decreasing exponents:
     ω^e1·c1 + … + ω^ek·ck   ↦   [[e1,c1], …, [ek,ck]],   0 ↦ [].
   Exponents are again such arrays (hereditary CNF), coefficients are
   positive JS integers. ε₀ itself is the string 'E0' (only at top level).
   ====================================================================== */
const ORD = (() => {
  const ZERO = [];
  const nat = k => (k > 0 ? [[ZERO, k]] : ZERO);
  const ONE = nat(1);
  const wpow = e => [[e, 1]];
  const OMEGA = wpow(ONE);
  const isZero = a => a !== 'E0' && a.length === 0;

  function cmp(a, b) {
    if (a === 'E0' || b === 'E0') return a === b ? 0 : a === 'E0' ? 1 : -1;
    const n = Math.min(a.length, b.length);
    for (let i = 0; i < n; i++) {
      const d = cmp(a[i][0], b[i][0]);
      if (d) return d;
      if (a[i][1] !== b[i][1]) return a[i][1] < b[i][1] ? -1 : 1;
    }
    return a.length === b.length ? 0 : a.length < b.length ? -1 : 1;
  }
  // ordinal addition (absorbs smaller left terms)
  function add(a, b) {
    if (!b.length) return a;
    const lead = b[0][0], out = [];
    for (const t of a) {
      const d = cmp(t[0], lead);
      if (d > 0) out.push(t);
      else if (d === 0) { out.push([lead, t[1] + b[0][1]]); return out.concat(b.slice(1)); }
      else break;
    }
    return out.concat(b);
  }
  // ordinal multiplication (left distributive over the CNF terms of b)
  function mul(a, b) {
    if (!a.length || !b.length) return ZERO;
    let r = ZERO;
    for (const [e, c] of b) {
      const piece = isZero(e) ? [[a[0][0], a[0][1] * c], ...a.slice(1)] : [[add(a[0][0], e), c]];
      r = add(r, piece);
    }
    return r;
  }
  // natural (Hessenberg) sum: merge the CNF terms
  function nsum(a, b) {
    const out = [];
    let i = 0, j = 0;
    while (i < a.length || j < b.length) {
      if (j >= b.length) out.push(a[i++]);
      else if (i >= a.length) out.push(b[j++]);
      else {
        const d = cmp(a[i][0], b[j][0]);
        if (d > 0) out.push(a[i++]);
        else if (d < 0) out.push(b[j++]);
        else { out.push([a[i][0], a[i][1] + b[j][1]]); i++; j++; }
      }
    }
    return out;
  }
  const isSucc = a => a !== 'E0' && a.length > 0 && isZero(a[a.length - 1][0]);
  const isLimit = a => a === 'E0' || (a.length > 0 && !isZero(a[a.length - 1][0]));
  function pred(a) {
    const out = a.slice(0, -1), c = a[a.length - 1][1];
    if (c > 1) out.push([ZERO, c - 1]);
    return out;
  }
  // ω-tower of height n: ω_0 = 1, ω_{k+1} = ω^{ω_k}
  function tower(n) { let t = ONE; for (let i = 0; i < n; i++) t = wpow(t); return t; }
  // Standard fundamental sequences (Wainer / Buchholz–Wainer style).
  //   α = β + ω^(δ+1):   α[n] = β + ω^δ·n
  //   α = β + ω^γ, γ limit:  α[n] = β + ω^(γ[n])
  //   ε₀[n] = ω_n  (ε₀[0] = 1, ε₀[n+1] = ω^(ε₀[n]))
  // where β + ω^γ is CNF (β's last exponent ≥ γ).
  function fs(a, n) {
    if (a === 'E0') return tower(n);
    if (!isLimit(a)) throw new Error('fs: not a limit');
    const [e, c] = a[a.length - 1];
    const prefix = a.slice(0, -1);
    if (c > 1) prefix.push([e, c - 1]);
    if (isSucc(e)) return add(prefix, n > 0 ? [[pred(e), n]] : ZERO);
    return add(prefix, wpow(fs(e, n)));
  }
  // which rule fs uses (for the ladder's explanation)
  function fsRule(a) {
    if (a === 'E0') return 'eps';
    if (!isLimit(a)) return 'succ';
    const e = a[a.length - 1][0];
    return isSucc(e) ? 'succExp' : 'limExp';
  }

  /* ---------- printing ---------- */
  const SUP = { '0': '⁰', '1': '¹', '2': '²', '3': '³', '4': '⁴', '5': '⁵', '6': '⁶', '7': '⁷', '8': '⁸', '9': '⁹' };
  function needParen(e) { return e.length > 1 || (e.length === 1 && e[0][1] > 1 && !isZero(e[0][0])); }
  function toStr(a) {
    if (a === 'E0') return 'ε₀';
    if (!a.length) return '0';
    return a.map(([e, c]) => {
      if (isZero(e)) return String(c);
      let s = 'ω';
      if (cmp(e, ONE) !== 0) {
        // small natural exponents as superscripts, everything else with ^
        if (e.length === 1 && isZero(e[0][0])) s += String(e[0][1]).split('').map(d => SUP[d]).join('');
        else s += '^' + (needParen(e) ? '(' + toStr(e) + ')' : toStr(e));
      }
      return c > 1 ? s + '·' + c : s;
    }).join(' + ');
  }
  function toHTML(a) {
    if (a === 'E0') return 'ε<sub>0</sub>';
    if (!a.length) return '0';
    return a.map(([e, c]) => {
      if (isZero(e)) return String(c);
      let s = 'ω';
      if (cmp(e, ONE) !== 0) s += '<sup>' + toHTML(e).replace(/ \+ /g, '+') + '</sup>';
      return c > 1 ? s + '·' + c : s;
    }).join(' + ');
  }

  /* ---------- parser: ω, w, ε₀/e0, naturals, + · * ^ ( ) and superscript digits ---------- */
  class OrdError extends Error { constructor(en, zh) { super(en); this.en = en; this.zh = zh; } }
  function tokenize(s) {
    s = s.replace(/[⁰¹²³⁴⁵⁶⁷⁸⁹]+/g, m => '^' + m.split('').map(ch => Object.keys(SUP).find(k => SUP[k] === ch)).join(''));
    const out = [];
    let i = 0;
    while (i < s.length) {
      const c = s[i];
      if (/\s/.test(c)) { i++; continue; }
      if (/[0-9]/.test(c)) { let j = i; while (j < s.length && /[0-9]/.test(s[j])) j++; out.push({ t: 'num', v: Number(s.slice(i, j)) }); i = j; continue; }
      if (c === 'ω' || c === 'w' || c === 'W') { out.push({ t: 'w' }); i++; continue; }
      if (s.startsWith('ε₀', i) || s.startsWith('ε0', i) || s.startsWith('e0', i) || s.startsWith('E0', i)) { out.push({ t: 'eps' }); i += 2; continue; }
      if (s.startsWith('**', i)) { out.push({ t: '^' }); i += 2; continue; }
      if ('+^()'.includes(c)) { out.push({ t: c }); i++; continue; }
      if ('*·×.'.includes(c)) { out.push({ t: '*' }); i++; continue; }
      throw new OrdError(`Unknown symbol “${c}”`, `无法识别的符号“${c}”`);
    }
    return out;
  }
  function parse(s, allowE0 = false) {
    const toks = tokenize(s);
    if (!toks.length) throw new OrdError('Empty input', '输入为空');
    let i = 0;
    const peek = () => toks[i];
    let sawEps = false;
    function pSum() { let a = pProd(); while (peek() && peek().t === '+') { i++; a = { op: '+', a, b: pProd() }; } return a; }
    function pProd() { let a = pPow(); while (peek() && peek().t === '*') { i++; a = { op: '*', a, b: pPow() }; } return a; }
    function pPow() { const a = pAtom(); if (peek() && peek().t === '^') { i++; return { op: '^', a, b: pPow() }; } return a; }
    function pAtom() {
      const tk = peek();
      if (!tk) throw new OrdError('Expression ends too early', '表达式不完整');
      i++;
      if (tk.t === 'num') return { op: 'num', v: tk.v };
      if (tk.t === 'w') return { op: 'w' };
      if (tk.t === 'eps') { sawEps = true; return { op: 'eps' }; }
      if (tk.t === '(') { const a = pSum(); if (!peek() || peek().t !== ')') throw new OrdError('Missing “)”', '缺少“)”'); i++; return a; }
      throw new OrdError(`Unexpected “${tk.t}”`, `此处不应出现“${tk.t}”`);
    }
    const ast = pSum();
    if (i < toks.length) throw new OrdError('Extra symbols at the end', '末尾有多余符号');
    if (sawEps) {
      if (ast.op === 'eps' && allowE0) return 'E0';
      throw new OrdError(allowE0 ? 'Here ε₀ may only appear on its own (this engine works below ε₀, plus ε₀ itself).' : 'This box works below ε₀ only.',
        allowE0 ? '这里 ε₀ 只能单独出现（本引擎只处理 ε₀ 以下的序数，外加 ε₀ 本身）。' : '这里只处理 ε₀ 以下的序数。');
    }
    return evalAst(ast);
  }
  const MAXN = 1e9;
  function evalAst(n) {
    switch (n.op) {
      case 'num': if (n.v > MAXN) throw new OrdError('Number too large for this toy', '数字太大'); return nat(n.v);
      case 'w': return OMEGA;
      case '+': return add(evalAst(n.a), evalAst(n.b));
      case '*': return mul(evalAst(n.a), evalAst(n.b));
      case '^': {
        const b = evalAst(n.b);
        if (n.a.op === 'w') return wpow(b);
        const a = evalAst(n.a);
        const bNat = b.length === 0 ? 0 : b.length === 1 && isZero(b[0][0]) ? b[0][1] : -1;
        if (bNat < 0) throw new OrdError('Only ω may be raised to an infinite power here (write ω^α).', '这里只有 ω 可以取无穷次幂（请写成 ω^α）。');
        if (bNat > 64) throw new OrdError('Exponent too large', '指数太大');
        let r = ONE;
        for (let k = 0; k < bNat; k++) { r = mul(r, a); if (r.length === 1 && isZero(r[0][0]) && r[0][1] > MAXN) throw new OrdError('Number too large for this toy', '数字太大'); }
        return r;
      }
    }
  }

  /* ---------- Goodstein: hereditary base-b trees (same shape as CNF) ---------- */
  // hereditary base-b representation of a BigInt m, as [[expTree, digit], …]
  function hered(m, b) {
    const B = BigInt(b);
    const digits = [];
    let k = 0;
    while (m > 0n) { const d = m % B; if (d) digits.push([k, Number(d)]); m /= B; k++; }
    return digits.reverse().map(([i, d]) => [hered(BigInt(i), b), d]);
  }
  // Number approximation of the value (may be Infinity)
  function numVal(T, b) { let s = 0; for (const [e, c] of T) s += c * Math.pow(b, numVal(e, b)); return s; }
  // log10 of value (approx; Infinity if huge), and log10 log10
  function lg(T, b) { if (!T.length) return -Infinity; const [e, c] = T[0]; return Math.log10(c) + numVal(e, b) * Math.log10(b); }
  function lglg(T, b) { const [e] = T[0]; return lg(e, b) + Math.log10(Math.log10(b)); }
  function exactVal(T, b) { const B = BigInt(b); let s = 0n; for (const [e, c] of T) s += BigInt(c) * B ** exactVal(e, b); return s; }
  const EXPAND_LIMIT = 4000;
  // subtract 1 in hereditary base b (T nonzero)
  function sub1(T, b) {
    const [e, c] = T[T.length - 1];
    const out = T.slice(0, -1);
    if (c > 1) out.push([e, c - 1]);
    if (isZero(e)) return out;
    const E = numVal(e, b); // b^E − 1 = Σ_{i<E} (b−1)·b^i
    if (!(E <= EXPAND_LIMIT)) throw new OrdError(`The next step would write b^${isFinite(E) ? E : '…'} − 1 with ${isFinite(E) ? E : 'astronomically many'} terms; too long to display.`, `下一步要把 b^${isFinite(E) ? E : '…'} − 1 写成 ${isFinite(E) ? E : '天文数字般多'} 项，太长，无法显示。`);
    for (let i = E - 1; i >= 0; i--) out.push([hered(BigInt(i), b), b - 1]);
    return out;
  }
  // tree printed in base b
  function heredHTML(T, b) {
    if (!T.length) return '0';
    return T.map(([e, c]) => {
      if (isZero(e)) return String(c);
      let s = `<b class="bs">${b}</b>`;
      if (!(e.length === 1 && isZero(e[0][0]) && e[0][1] === 1)) s += '<sup>' + heredHTML(e, b).replace(/ \+ /g, '+') + '</sup>';
      return c > 1 ? c + '·' + s : s;
    }).join(' + ');
  }
  // ordinal = same tree with the base replaced by ω. Coefficients are written on the right.
  const treeOrd = T => T; // identical representation

  /* ---------- hydra ---------- */
  function hydraOrd(node) {
    let r = ZERO;
    for (const ch of node.ch) r = nsum(r, wpow(hydraOrd(ch)));
    return r;
  }
  const cloneTree = n => ({ ch: n.ch.map(cloneTree) });
  // chop leaf `leaf` with parent path; copies = n. Returns true if done.
  function chop(root, leaf, copies) {
    const parentOf = new Map();
    (function walk(n) { n.ch.forEach(c => { parentOf.set(c, n); walk(c); }); })(root);
    const p = parentOf.get(leaf);
    if (!p || leaf.ch.length) return false;
    p.ch.splice(p.ch.indexOf(leaf), 1);
    if (p === root) return true;
    const g = parentOf.get(p);
    for (let k = 0; k < copies; k++) g.ch.push(cloneTree(p));
    return true;
  }
  const countNodes = n => 1 + n.ch.reduce((s, c) => s + countNodes(c), 0);

  /* ---------- fast-growing hierarchy with blow-up guards ---------- */
  // values: {k:'ex', v:BigInt} exact | {k:'ap', h, t} ≈ 10^10^…^t (h tens; h=0 means the number t)
  //         | {k:'bey'} beyond this calculator | {k:'bud'} step budget exhausted
  const LIM_BITS = 200000;
  const BEY = { k: 'bey' }, BUD = { k: 'bud' };
  const ex = v => ({ k: 'ex', v });
  const L2 = Math.log10(2);
  function ap(h, t) { return (h > 1e15 || !isFinite(t) || !isFinite(h)) ? BEY : { k: 'ap', h, t }; }
  function bits(v) { return v === 0n ? 0 : v.toString(2).length; }
  function log10Big(v) { const s = v.toString(16); const k = Math.min(13, s.length); return Math.log10(parseInt(s.slice(0, k), 16)) + (s.length - k) * 4 * L2; }
  function toAp(x) {
    if (x.k !== 'ex') return x;
    if (x.v < 1000000000000000n) return { k: 'ap', h: 0, t: Number(x.v) };
    return { k: 'ap', h: 1, t: log10Big(x.v) };
  }
  function apLog10(A) { return A.h === 0 ? { k: 'ap', h: 0, t: Math.log10(Math.max(A.t, 1)) } : { k: 'ap', h: A.h - 1, t: A.t }; }
  function apPow10(L) { return L.h === 0 && L.t < 15 ? { k: 'ap', h: 0, t: Math.pow(10, L.t) } : ap(L.h + 1, L.t); }
  function apScale(L, k) { return L.h === 0 ? { k: 'ap', h: 0, t: L.t * k } : L.h === 1 ? ap(1, L.t + Math.log10(k)) : L; }
  function apAdd(A, B) { // ≈ A + B
    if (A.h === 0 && B.h === 0) return { k: 'ap', h: 0, t: A.t + B.t };
    return (A.h > B.h || (A.h === B.h && A.t >= B.t)) ? A : B;
  }
  const isBig = x => x.k === 'bey' || x.k === 'bud';
  function smallNum(x) { // exact Number if x is an exact value ≤ 1e15, else null
    if (x.k === 'ex' && x.v <= 1000000000000000n) return Number(x.v);
    return null;
  }
  // x · 2^m
  function times2pow(x, m) {
    if (isBig(x) || isBig(m)) return x.k === 'bud' || m.k === 'bud' ? BUD : BEY;
    if (x.k === 'ex' && m.k === 'ex' && m.v <= BigInt(LIM_BITS) && bits(x.v) + Number(m.v) <= LIM_BITS) return ex(x.v << m.v);
    const Lx = apLog10(toAp(x)), Lm = apScale(toAp(m), L2);
    if (Lx.k !== 'ap' || Lm.k !== 'ap') return BEY;
    return apPow10(apAdd(Lx, Lm));
  }
  function plus(x, m) {
    if (isBig(x) || isBig(m)) return x.k === 'bud' || m.k === 'bud' ? BUD : BEY;
    if (x.k === 'ex' && m.k === 'ex') return ex(x.v + m.v);
    return apAdd(toAp(x), toAp(m));
  }
  function makeFGH(budget = 3e6) {
    let ops = 0;
    // f_β^m (x)
    function iterate(beta, m, x) {
      if (isBig(m) || isBig(x)) return m.k === 'bud' || x.k === 'bud' ? BUD : BEY;
      if (isZero(beta)) return plus(x, m);                 // f_0^m(x) = x + m
      if (cmp(beta, ONE) === 0) return times2pow(x, m);     // f_1^m(x) = x·2^m
      if (cmp(beta, nat(2)) === 0) {                        // f_2 iterated
        const mm = smallNum(m);
        let H = mm;
        if (H === null) { const A = toAp(m); H = A.h === 0 ? A.t : A.h === 1 && A.t < 15 ? Math.pow(10, A.t) : Infinity; }
        if (!isFinite(H) || H > 1e15) return BEY;
        for (let i = 0; i < H; i++) {
          if (++ops > budget) return BUD;
          x = times2pow(x, x);
          if (isBig(x)) return x;
          if (x.k === 'ap' && x.h >= 2) return ap(x.h + (H - i - 1), x.t);
        }
        return x;
      }
      const mm = smallNum(m);
      if (mm === null || mm > 1e6) return BEY;
      for (let i = 0; i < mm; i++) {
        if (++ops > budget) return BUD;
        x = f(beta, x);
        if (isBig(x)) return x;
      }
      return x;
    }
    let depth = 0;
    function f(alpha, x) {
      if (++ops > budget) return BUD;
      if (isBig(x)) return x;
      if (isZero(alpha)) return plus(x, ex(1n));
      // finite index k ≥ 4 and x ≥ 3: f_k(x) ≥ f_4(3), already far beyond what we can describe
      if (alpha.length === 1 && isZero(alpha[0][0]) && alpha[0][1] >= 4 && (smallNum(x) === null || smallNum(x) >= 3)) return BEY;
      if (depth > 1200) return BUD;
      depth++;
      let r;
      if (isLimit(alpha)) {
        const n = smallNum(x);
        r = (n === null || n > 1e6) ? BEY : f(fs(alpha, n), x);
      } else r = iterate(pred(alpha), x, x);
      depth--;
      return r;
    }
    return { f: (a, n) => f(a, ex(BigInt(n))), ops: () => ops };
  }
  // Hardy hierarchy walk: H_0(n)=n, H_{α+1}(n)=H_α(n+1), H_λ(n)=H_{λ[n]}(n)
  function hardyWalk(alpha, n, maxSteps = 200000, keep = 400) {
    const trace = [];
    let steps = 0;
    while (!isZero(alpha)) {
      if (steps >= maxSteps) return { done: false, trace, steps, n };
      if (trace.length < keep) trace.push([alpha, n]);
      if (isLimit(alpha)) alpha = fs(alpha, n);
      else { alpha = pred(alpha); n++; }
      steps++;
    }
    trace.push([alpha, n]);
    return { done: true, trace, steps, n };
  }

  return { ZERO, ONE, OMEGA, nat, wpow, isZero, cmp, add, mul, nsum, isSucc, isLimit, pred, tower, fs, fsRule,
    toStr, toHTML, parse, OrdError, hered, numVal, lg, lglg, exactVal, sub1, heredHTML, treeOrd,
    hydraOrd, cloneTree, chop, countNodes, makeFGH, hardyWalk, log10Big };
})();

if (typeof module !== 'undefined' && module.exports) module.exports = ORD;

/* ======================================================================
   PART B · page interactions
   ====================================================================== */
if (typeof document !== 'undefined') (function page() {
Lang.init();
Progress.paint();

const $ = id => document.getElementById(id);
const okBox = (box, html, kind = 'ok') => { box.className = 'msg ' + kind; box.innerHTML = html; };
const clearBox = box => { box.className = 'msg'; box.innerHTML = ''; };
const errHTML = e => (e && e.en ? bi(e.en, e.zh) : String(e));
const O = ORD;
const REDRAW = []; // SVG redraws on language switch
const H = a => `<span class="ordin">${O.toHTML(a)}</span>`;
const svgText = (parent, x, y, str, attrs = {}) => { const t = el('text', Object.assign({ x, y }, attrs), parent); t.textContent = str; return t; };

/* ---------- generic: check-yourself boxes ---------- */
document.querySelectorAll('.cy').forEach(box => {
  const ok = +box.dataset.ok;
  const btns = [...box.querySelectorAll('.cy-opts .btn')];
  btns.forEach((b, i) => b.addEventListener('click', () => {
    btns.forEach(x => x.classList.remove('right', 'wrongc'));
    b.classList.add(i === ok ? 'right' : 'wrongc');
    if (i === ok) box.classList.add('answered');
  }));
  box.querySelector('.cy-show').addEventListener('click', () => {
    btns.forEach(x => x.classList.remove('wrongc'));
    btns[ok].classList.add('right');
    box.classList.add('answered');
  });
});
/* ---------- generic: proofs revealed step by step ---------- */
document.querySelectorAll('.proof').forEach(pf => {
  const steps = [...pf.querySelectorAll('.step')];
  let k = 0;
  const next = pf.querySelector('.pf-next');
  next.addEventListener('click', () => { if (k < steps.length) steps[k++].classList.add('on'); if (k === steps.length) next.disabled = true; });
  pf.querySelector('.pf-all').addEventListener('click', () => { steps.forEach(s => s.classList.add('on')); k = steps.length; next.disabled = true; });
});

/* ================= Step 1: hereditary CNF tree ================= */
(function cnfTree() {
  const collapsed = new Set();
  let cur = null;
  function build(a, path) {
    // returns a node {label, kind, children, path}
    if (!a.length) return { label: '0', kind: 'num', children: [], path };
    if (a.length === 1) return termNode(a[0], path);
    return { label: '+', kind: 'sum', children: a.map((t, i) => termNode(t, path + '.' + i)), path };
  }
  function termNode([e, c], path) {
    if (O.isZero(e)) return { label: String(c), kind: 'num', children: [], path };
    const node = { kind: 'term', path, children: [] };
    if (collapsed.has(path)) { node.label = O.toStr([[e, c]]); node.folded = true; }
    else { node.label = c > 1 ? `ω^□ · ${c}` : 'ω^□'; node.children = [build(e, path + 'e')]; }
    return node;
  }
  function draw() {
    const stage = $('cnfStage');
    stage.innerHTML = '';
    if (!cur) return;
    const root = build(cur, 'r');
    const GY = 70;
    let maxD = 0;
    const wOf = n => Math.max(n.label.length * 10 + 26, 52);
    (function measure(n, d) {
      n.d = d; maxD = Math.max(maxD, d);
      n.children.forEach(c => measure(c, d + 1));
      n.w = Math.max(wOf(n) + 14, n.children.reduce((s, c) => s + c.w, 0));
    })(root, 0);
    (function place(n, left) {
      n.x = left + n.w / 2;
      let l = left + (n.w - n.children.reduce((s, c) => s + c.w, 0)) / 2;
      n.children.forEach(c => { place(c, l); l += c.w; });
    })(root, 10);
    const W = Math.max(root.w + 20, 200), Hh = (maxD + 1) * GY + 20;
    const svg = el('svg', { viewBox: `0 0 ${W} ${Hh}`, width: W, height: Hh, style: 'margin:0 auto' }, stage);
    const all = [];
    (function collect(n) { all.push(n); n.children.forEach(collect); })(root);
    const py = n => 30 + n.d * GY;
    all.forEach(n => n.children.forEach(c => {
      const ln = el('line', { x1: n.x, y1: py(n) + 15, x2: c.x, y2: py(c) - 15, stroke: '#9aa0aa', 'stroke-width': 2, class: 'fadein' }, svg);
      ln.style.animationDelay = (c.d * 0.15) + 's';
    }));
    all.forEach(n => {
      const g = el('g', { transform: `translate(${n.x},${py(n)})` }, svg);
      const inner = el('g', { class: 'pop' }, g);
      inner.style.animationDelay = (n.d * 0.15) + 's';
      const w = wOf(n);
      const fill = n.kind === 'num' ? '#fff3bf' : n.kind === 'sum' ? '#f1efe7' : n.folded ? '#d6defc' : '#e7ecff';
      const stroke = n.kind === 'num' ? '#f08c00' : n.kind === 'sum' ? '#6b7280' : '#3b5bdb';
      el('rect', { x: -w / 2, y: -15, width: w, height: 30, rx: 12, fill, stroke, 'stroke-width': 2 }, inner);
      svgText(inner, 0, 5, n.label, { 'text-anchor': 'middle', 'font-size': 15, 'font-weight': 700 });
      if (n.kind === 'term') {
        g.style.cursor = 'pointer';
        const tt = el('title', {}, g); tt.textContent = 'click to fold/unfold · 点击折叠/展开';
        g.addEventListener('click', () => { collapsed.has(n.path) ? collapsed.delete(n.path) : collapsed.add(n.path); draw(); });
      }
    });
  }
  function go() {
    try {
      cur = O.parse($('cnfIn').value);
      clearBox($('cnfErr'));
      collapsed.clear();
      $('cnfNorm').innerHTML = bil('CNF', '康托尔范式') + ': ' + H(cur);
      draw();
    } catch (e) { okBox($('cnfErr'), errHTML(e), 'bad'); }
  }
  $('cnfGo').addEventListener('click', go);
  $('cnfIn').addEventListener('keydown', e => e.key === 'Enter' && go());
  document.querySelectorAll('[data-cnf]').forEach(b => b.addEventListener('click', () => { $('cnfIn').value = b.dataset.cnf; go(); }));
  go();

  // comparison with trace
  function trace(a, b, depth, lines) {
    const pad = '&nbsp;&nbsp;'.repeat(depth);
    for (let i = 0; i < Math.min(a.length, b.length); i++) {
      lines.push(`${pad}${bil(`term ${i + 1}: exponents`, `第 ${i + 1} 项：指数`)} ${H(a[i][0])} ${bil('vs', '对比')} ${H(b[i][0])}`);
      const d = O.cmp(a[i][0], b[i][0]);
      if (d) {
        lines.push(`${pad}⇒ ${H(d < 0 ? a[i][0] : b[i][0])} &lt; ${H(d < 0 ? b[i][0] : a[i][0])} ${bil('(compared by the same procedure, one level down): the larger exponent wins', '（用同样的过程在下一层比较）：指数大者为大')}`);
        return d;
      }
      if (a[i][1] !== b[i][1]) { lines.push(`${pad}⇒ ${bil(`same exponent, coefficients ${a[i][1]} vs ${b[i][1]}`, `指数相同，系数 ${a[i][1]} 对比 ${b[i][1]}`)}`); return a[i][1] < b[i][1] ? -1 : 1; }
    }
    if (a.length !== b.length) { lines.push(`${pad}⇒ ${bil('one runs out of terms first: it is smaller', '一方的项先用完：它较小')}`); return a.length < b.length ? -1 : 1; }
    lines.push(`${pad}⇒ ${bil('identical', '完全相同')}`);
    return 0;
  }
  function cmpGo() {
    try {
      const a = O.parse($('cmpA').value), b = O.parse($('cmpB').value);
      const lines = [];
      const d = trace(a, b, 0, lines);
      $('cmpRel').textContent = d < 0 ? '<' : d > 0 ? '>' : '=';
      okBox($('cmpOut'), `${H(a)} <b>${d < 0 ? '&lt;' : d > 0 ? '&gt;' : '='}</b> ${H(b)}<br><span style="font-size:13px">${lines.join('<br>')}</span>`, 'info');
    } catch (e) { $('cmpRel').textContent = '?'; okBox($('cmpOut'), errHTML(e), 'bad'); }
  }
  $('cmpGo').addEventListener('click', cmpGo);
  cmpGo();
})();
// plain-text bilingual label for SVG
function bilText(en, zh) { const m = document.body.classList.contains('lang-zh') ? 'zh' : document.body.classList.contains('lang-en') ? 'en' : 'both'; return m === 'en' ? en : m === 'zh' ? zh : `${en} · ${zh}`; }

/* ---- SVG: draw an ω-tower of height k (k ω's) at (x,y) ---- */
function towerLabel(parent, x, y, k, size = 18, color = '#1f2430') {
  const g = el('g', {}, parent);
  if (k === 0) { svgText(g, x, y, '1', { 'font-size': size, fill: color, 'font-weight': 700 }); return g; }
  let cx = x, cy = y, s = size;
  for (let i = 0; i < k; i++) {
    svgText(g, cx, cy, 'ω', { 'font-size': s, fill: color, 'font-weight': 700 });
    cx += s * 0.62; cy -= s * 0.45; s = Math.max(s * 0.72, 7);
  }
  return g;
}

/* ================= Step 2: ε₀ tower ================= */
(function tower() {
  const svg = $('towSvg');
  let k = 2, playing = false;
  const X0 = 40, X1 = 850;
  const xOf = j => X0 + (X1 - X0 - 40) * (1 - Math.pow(0.5, j + 1));
  function draw(showLoop) {
    svg.innerHTML = '';
    el('line', { x1: X0, y1: 170, x2: X1, y2: 170, stroke: '#1f2430', 'stroke-width': 2 }, svg);
    el('line', { x1: X0, y1: 162, x2: X0, y2: 178, stroke: '#1f2430', 'stroke-width': 2 }, svg);
    svgText(svg, X0, 198, '0', { 'text-anchor': 'middle', 'font-size': 15 });
    // ε₀ end
    el('line', { x1: X1, y1: 150, x2: X1, y2: 190, stroke: '#c2255c', 'stroke-width': 3 }, svg);
    svgText(svg, X1, 214, 'ε₀', { 'text-anchor': 'middle', 'font-size': 20, fill: '#c2255c', 'font-weight': 700 });
    for (let j = 0; j <= k; j++) {
      const x = xOf(j);
      const g = el('g', { class: j === k ? 'pop' : '' }, svg);
      el('line', { x1: x, y1: 160, x2: x, y2: 180, stroke: '#3b5bdb', 'stroke-width': 3 }, g);
      if (j <= 5) towerLabel(g, x - 6, j % 2 ? 230 : 205, j, 16, '#3b5bdb');
      if (j < k) {
        const x2 = xOf(j + 1);
        const p = el('path', { d: `M${x},158 Q${(x + x2) / 2},${100 - 40 / (j + 1)} ${x2},158`, fill: 'none', stroke: '#ae3ec9', 'stroke-width': 1.8, 'marker-end': 'url(#arr21)', class: 'fadein' }, svg);
        p.style.animationDelay = '.1s';
        if (j < 4) svgText(svg, (x + x2) / 2 - 10, 110 - 40 / (j + 1), 'ω^·', { 'font-size': 13, fill: '#ae3ec9' });
      }
    }
    const defs = el('defs', {}, svg);
    const mk = el('marker', { id: 'arr21', viewBox: '0 0 10 10', refX: 9, refY: 5, markerWidth: 7, markerHeight: 7, orient: 'auto-start-reverse' }, defs);
    el('path', { d: 'M0,0 L10,5 L0,10 z', fill: '#ae3ec9' }, mk);
    if (showLoop) {
      el('path', { d: `M${X1 - 8},148 C${X1 - 50},70 ${X1 + 50},70 ${X1 + 8},148`, fill: 'none', stroke: '#c2255c', 'stroke-width': 2.4, 'marker-end': 'url(#arr21)', class: 'fadein' }, svg);
      svgText(svg, X1 - 60, 60, 'ω^ε₀ = ε₀', { 'font-size': 16, fill: '#c2255c', 'font-weight': 700 });
    }
    svgText(svg, 20, 30, bilText(`storeys built: ${k}`, `已建层数：${k}`), { 'font-size': 14, fill: '#6b7280' });
    const msg = k <= 5
      ? bi(`Newest marker: ω${'₀₁₂₃₄₅'[k]} = a tower of ${k} ω's. Still below ε₀: its CNF exponent ω${'₀₁₂₃₄₅'[k - 1]} is smaller than itself.`, `最新刻度：ω${'₀₁₂₃₄₅'[k]}，即 ${k} 个 ω 叠成的塔。仍在 ε₀ 之下：它的康托尔范式指数 ω${'₀₁₂₃₄₅'[k - 1]} 比它自身小。`)
      : bi(`${k} storeys: the markers crowd towards ε₀ but never reach it. Every finite tower is &lt; ε₀; ε₀ is their supremum.`, `${k} 层：刻度越来越挤向 ε₀，却始终到不了。每座有限高的塔都 &lt; ε₀；ε₀ 是它们的上确界。`);
    $('towMsg').innerHTML = showLoop ? bi('In the limit: ε₀ = sup of all towers, and ω^ε₀ = ε₀, so the arrow loops back. ε₀ is the first fixed point of α ↦ ω^α.', '取极限：ε₀ 是所有塔的上确界，并且 ω^ε₀ = ε₀，箭头绕回自身。ε₀ 是 α ↦ ω^α 的第一个不动点。') : msg;
  }
  REDRAW.push(() => draw(k >= 9));
  $('towAdd').addEventListener('click', () => { if (k < 9) k++; draw(k >= 9); });
  $('towReset').addEventListener('click', () => { k = 2; draw(false); });
  $('towPlay').addEventListener('click', async () => {
    if (playing) return; playing = true;
    while (k < 9) { k++; draw(false); await sleep(550); }
    draw(true); playing = false;
  });
  draw(false);
})();

/* ================= Step 3: fundamental sequence ladder ================= */
(function ladder() {
  let alpha = null;
  const svg = $('fsSvg');
  function ruleText(a) {
    if (a === 'E0') return bi('ε₀[n] = ωₙ: a tower of n ω\'s (ε₀[0] = 1).', 'ε₀[n] = ωₙ：n 个 ω 叠成的塔（ε₀[0] = 1）。');
    const r = O.fsRule(a);
    if (r === 'succ') return null;
    const [e, c] = a[a.length - 1];
    const beta = a.slice(0, -1); if (c > 1) beta.push([e, c - 1]);
    const bH = beta.length ? H(beta) + ' + ' : '';
    if (r === 'succExp') {
      const d = O.pred(e);
      return bi(`α = ${bH}ω<sup>${O.toHTML(e)}</sup>, exponent γ = ${O.toHTML(e)} is a successor δ + 1 with δ = ${O.toHTML(d)}. Rule: α[n] = ${bH}ω<sup>${O.toHTML(d)}</sup>·n.`,
        `α = ${bH}ω<sup>${O.toHTML(e)}</sup>，指数 γ = ${O.toHTML(e)} 是后继 δ + 1，δ = ${O.toHTML(d)}。规则：α[n] = ${bH}ω<sup>${O.toHTML(d)}</sup>·n。`);
    }
    return bi(`α = ${bH}ω<sup>${O.toHTML(e)}</sup>, exponent γ = ${O.toHTML(e)} is a limit. Rule: α[n] = ${bH}ω<sup>γ[n]</sup>, recursing into the exponent.`,
      `α = ${bH}ω<sup>${O.toHTML(e)}</sup>，指数 γ = ${O.toHTML(e)} 是极限。规则：α[n] = ${bH}ω<sup>γ[n]</sup>，递归进入指数。`);
  }
  function draw() {
    svg.innerHTML = '';
    if (!alpha) return;
    const N = 6, sel = +$('fsN').value;
    $('fsNv').textContent = sel;
    const top = 40, bot = 350;
    el('line', { x1: 70, y1: top, x2: 70, y2: bot, stroke: '#c9c3b3', 'stroke-width': 6, 'stroke-linecap': 'round' }, svg);
    el('line', { x1: 130, y1: top, x2: 130, y2: bot, stroke: '#c9c3b3', 'stroke-width': 6, 'stroke-linecap': 'round' }, svg);
    el('line', { x1: 50, y1: top, x2: 520, y2: top, stroke: '#c2255c', 'stroke-width': 2, 'stroke-dasharray': '6 5' }, svg);
    svgText(svg, 150, top - 8, 'α = ' + O.toStr(alpha), { 'font-size': 16, fill: '#c2255c', 'font-weight': 700 });
    for (let n = 0; n <= N; n++) {
      const y = bot - 10 - n * (bot - top - 60) / N;
      const g = el('g', { class: 'pop' }, svg);
      g.style.animationDelay = (n * 0.08) + 's';
      const on = n === sel;
      el('line', { x1: 70, y1: y, x2: 130, y2: y, stroke: on ? '#3b5bdb' : '#8a7f63', 'stroke-width': on ? 5 : 3 }, g);
      svgText(g, 20, y + 5, `[${n}]`, { 'font-size': 13, fill: '#6b7280' });
      const v = O.fs(alpha, n);
      let s = O.toStr(v);
      if (s.length > 44) s = s.slice(0, 42) + '…';
      svgText(g, 145, y + 5, s, { 'font-size': on ? 15 : 13, fill: on ? '#3b5bdb' : '#1f2430', 'font-weight': on ? 700 : 400 });
    }
    svgText(svg, 145, top + 22, '⋮', { 'font-size': 16, fill: '#6b7280' });
    $('fsRule').innerHTML = ruleText(alpha) + '<br>' + bil(`Highlighted: α[${sel}]`, `高亮：α[${sel}]`) + ' = ' + H(O.fs(alpha, sel));
  }
  function go() {
    try {
      const a = O.parse($('fsIn').value, true);
      if (!O.isLimit(a)) { okBox($('fsErr'), bi(`${O.toStr(a)} is ${O.isZero(a) ? 'zero' : 'a successor'}: it has no fundamental sequence. Try a limit ordinal.`, `${O.toStr(a)} 是${O.isZero(a) ? '零' : '后继序数'}：它没有基本序列。请换一个极限序数。`), 'bad'); return; }
      alpha = a; clearBox($('fsErr')); $('fsWalk').innerHTML = ''; draw();
    } catch (e) { okBox($('fsErr'), errHTML(e), 'bad'); }
  }
  $('fsGo').addEventListener('click', go);
  $('fsIn').addEventListener('keydown', e => e.key === 'Enter' && go());
  $('fsN').addEventListener('input', draw);
  REDRAW.push(draw);
  document.querySelectorAll('[data-fs]').forEach(b => b.addEventListener('click', () => { $('fsIn').value = b.dataset.fs; go(); }));
  $('fsDesc').addEventListener('click', () => {
    if (!alpha) return;
    const n = +$('fsN').value;
    let a = alpha, lines = [], moves = 0, minus = 0;
    while (!O.isZero(a) && moves < 400) {
      if (O.isLimit(a)) { const b = O.fs(a, n); lines.push(`<span class="lim">${O.toStr(a)} → [${n}] → ${O.toStr(b)}</span>`); a = b; }
      else { minus++; a = O.pred(a); if (minus <= 60 || O.isZero(a)) lines.push(`<span class="suc">−1 → ${O.toStr(a)}</span>`); else if (minus === 61) lines.push('<span class="muted">…</span>'); }
      moves++;
    }
    // number of −1 moves = α with ω replaced by n (slow-growing value)
    const base = alpha === 'E0' ? O.fs('E0', n) : alpha;
    const v = O.numVal(base, n), L = n >= 2 ? O.lg(base, n) : 0;
    const cnt = (isFinite(v) && v < 1e15) ? String(Math.round(v)) : isFinite(L) ? `≈ 10^${L.toFixed(1)}` : bilText('astronomically many', '天文数字般多');
    const head = bi(`Total “−1” moves = α with ω replaced by n = <b>${cnt}</b>.`, `“减一”总次数 = 把 α 中的 ω 换成 n = <b>${cnt}</b>。`);
    $('fsWalk').innerHTML = head + '<br>' + lines.join('<br>') + (O.isZero(a) ? `<br><b class="ok-mark">0 ✓</b>` : `<br><span class="muted">${bi('… (stopped displaying after 400 moves; the descent still ends)', '……（显示 400 步后停止；下降过程仍然会结束）')}</span>`);
  });
  go();
})();

/* ================= Step 4: Goodstein ================= */
(function goodstein() {
  let T = null, b = 2, k = 0, done = false, rows = [], blocked = false;
  const fmtVal = (T, b) => {
    if (!T.length) return '0';
    const L = O.lg(T, b);
    if (L < 40) return O.exactVal(T, b).toString();
    if (isFinite(L)) return `≈ 10^${Math.floor(L)} <span class="muted">(${bilText(`${Math.floor(L) + 1} digits`, `${Math.floor(L) + 1} 位`)})</span>`;
    const LL = O.lglg(T, b);
    return isFinite(LL) ? `≈ 10^(10^${LL.toFixed(1)})` : bilText('astronomical', '天文数字');
  };
  function digitsLog(T, b) { // log10(number of digits), for the chart
    if (!T.length) return 0;
    const L = O.lg(T, b);
    if (isFinite(L)) return Math.log10(Math.max(L, 0) + 1);
    const LL = O.lglg(T, b);
    return isFinite(LL) ? LL : 12;
  }
  function addRow() {
    const tr = document.createElement('tr');
    tr.className = 'newrow';
    const down = rows.length ? '<span class="down">↓</span> ' : '';
    tr.innerHTML = `<td class="m">${k}</td><td class="m">${b}</td><td class="m">${O.heredHTML(T, b)}</td><td class="m">${fmtVal(T, b)}</td><td class="m">${down}${H(T)}</td>`;
    $('gsTable').appendChild(tr);
    rows.push(digitsLog(T, b));
    const sb = $('gsTable').parentElement; sb.scrollTop = sb.scrollHeight;
  }
  function chart() {
    const svg = $('gsSvg');
    svg.innerHTML = '';
    const data = rows.slice(-40), off = rows.length - data.length;
    const mx = Math.max(1, ...data);
    el('line', { x1: 34, y1: 260, x2: 312, y2: 260, stroke: '#1f2430' }, svg);
    el('line', { x1: 34, y1: 20, x2: 34, y2: 260, stroke: '#1f2430' }, svg);
    svgText(svg, 6, 16, bilText('log₁₀(#digits)', 'log₁₀(位数)'), { 'font-size': 11, fill: '#6b7280' });
    svgText(svg, 310, 282, bilText('step k', '步数 k'), { 'font-size': 11, fill: '#6b7280', 'text-anchor': 'end' });
    const bw = 270 / Math.max(data.length, 1);
    data.forEach((v, i) => {
      const h = 230 * v / mx;
      el('rect', { x: 38 + i * bw, y: 260 - h, width: Math.max(bw - 2, 1), height: Math.max(h, 1), fill: '#f08c00', opacity: 0.8 }, svg);
    });
    svgText(svg, 38, 276, String(off), { 'font-size': 10, fill: '#6b7280' });
    svgText(svg, 8, 30, mx.toFixed(1), { 'font-size': 10, fill: '#6b7280' });
  }
  function start(mStr) {
    let m;
    try { m = BigInt(String(mStr).trim()); } catch { okBox($('gsMsg'), bi('Please enter a natural number.', '请输入一个自然数。'), 'bad'); return; }
    if (m < 0n || m > 1000000000000n) { okBox($('gsMsg'), bi('Please use 0 ≤ m ≤ 10¹².', '请取 0 ≤ m ≤ 10¹²。'), 'bad'); return; }
    T = O.hered(m, 2); b = 2; k = 0; done = !T.length; rows = []; blocked = false;
    $('gsTable').innerHTML = `<tr><th>k</th><th>${bil('base', '底数')}</th><th>${bil('hereditary form', '遗传表示')}</th><th>${bil('value g<sub>k</sub>', '值 g<sub>k</sub>')}</th><th>${bil('shadow ordinal o<sub>k</sub>', '影子序数 o<sub>k</sub>')}</th></tr>`;
    addRow(); chart();
    okBox($('gsMsg'), bi('Press “+1 step”. Watch the value column grow while the ordinal column goes down.', '按“走 1 步”。看数值列在增长，而序数列在下降。'), 'info');
  }
  function step(times) {
    if (!T) return;
    for (let i = 0; i < times; i++) {
      if (done) { okBox($('gsMsg'), bi(`Reached 0 at step ${k}. ✓`, `在第 ${k} 步到达 0。✓`)); break; }
      if (blocked) break;
      try { T = O.sub1(T, b + 1); }
      catch (e) {
        blocked = true;
        okBox($('gsMsg'), errHTML(e) + ' ' + bi('The theorem still guarantees that the sequence reaches 0; it just takes unimaginably long.', '定理仍然保证序列会到达 0，只是需要难以想象的漫长时间。'), 'warn');
        break;
      }
      b++; k++;
      addRow();
      if (!T.length) { done = true; okBox($('gsMsg'), bi(`Reached 0 at step ${k}. ✓ The ordinals went down at every step.`, `在第 ${k} 步到达 0。✓ 序数每一步都在下降。`)); break; }
      if (rows.length > 500) { blocked = true; okBox($('gsMsg'), bi('Display limit (500 rows) reached.', '已达显示上限（500 行）。'), 'warn'); break; }
    }
    chart();
  }
  REDRAW.push(chart);
  $('gsStart').addEventListener('click', () => start($('gsM').value));
  $('gsStep').addEventListener('click', () => step(1));
  $('gsStep10').addEventListener('click', () => step(10));
  document.querySelectorAll('[data-gs]').forEach(x => x.addEventListener('click', () => { $('gsM').value = x.dataset.gs; start(x.dataset.gs); }));
  start('4');
  step(3);
})();

/* ================= Step 5: hydra ================= */
const leafN = () => ({ ch: [] });
const nodeN = (...ch) => ({ ch });
function drawHydra(svg, root, opts = {}) {
  svg.innerHTML = '';
  let maxD = 0, leaves = 0;
  (function m(n, d) { n.d = d; maxD = Math.max(maxD, d); if (!n.ch.length) { n.x = leaves++; } else { n.ch.forEach(c => m(c, d + 1)); n.x = (n.ch[0].x + n.ch[n.ch.length - 1].x) / 2; } })(root, 0);
  const W = opts.W || 900, Hh = opts.H || 320;
  const gx = Math.min(60, (W - 60) / Math.max(leaves, 1));
  const totalW = gx * Math.max(leaves - 1, 0);
  const px = n => W / 2 - totalW / 2 + n.x * gx;
  const gy = Math.min(70, (Hh - 60) / Math.max(maxD, 1));
  const py = n => Hh - 25 - n.d * gy;
  const r = Math.max(3, Math.min(9, gx / 3));
  (function edges(n) { n.ch.forEach(c => { el('line', { x1: px(n), y1: py(n), x2: px(c), y2: py(c), stroke: '#2b8a3e', 'stroke-width': Math.max(1.5, r / 2.2), 'stroke-linecap': 'round' }, svg); edges(c); }); })(root);
  (function nodes(n, isRoot) {
    const head = !isRoot && !n.ch.length;
    const g = el('g', { class: head && opts.onChop ? 'hy-head' : '' }, svg);
    el('circle', { cx: px(n), cy: py(n), r: isRoot ? 12 : head ? r + 1 : r * 0.8, fill: isRoot ? '#2b8a3e' : head ? '#e03131' : '#40c057', stroke: '#fff', 'stroke-width': 1.5 }, g);
    if (head && opts.onChop) g.addEventListener('click', () => opts.onChop(n));
    if (head && opts.mark === n) svgText(svg, px(n) + 10, py(n) - 8, '✂', { 'font-size': 18, fill: '#1f2430' });
    n.ch.forEach(c => nodes(c, false));
  })(root, true);
}
(function hydra() {
  const presets = [
    () => nodeN(leafN(), nodeN(leafN(), leafN())),
    () => nodeN(leafN(), nodeN(leafN(), nodeN(leafN())), nodeN(leafN(), leafN())),
    () => nodeN(nodeN(nodeN(nodeN(leafN())))),
  ];
  let root, n, hist;
  const svg = $('hySvg');
  function info() {
    const o = O.hydraOrd(root);
    const cnt = O.countNodes(root);
    const won = !root.ch.length;
    $('hyInfo').innerHTML = won
      ? bi(`<b>Hercules wins</b> after ${n - 1} chops. Ordinal = 0.`, `赫拉克勒斯在砍了 ${n - 1} 刀后<b>获胜</b>。序数 = 0。`)
      : bi(`Next step n = <b>${n}</b> · nodes: ${cnt} · ordinal: `, `下一步 n = <b>${n}</b> · 节点数：${cnt} · 序数：`) + H(o);
    $('hyHist').innerHTML = hist.map(([s, h]) => `${s}: ${h}`).join('<br>');
    $('hyHist').scrollTop = 1e9;
  }
  function copies() { const v = $('hyMode').value; return v === 'n' ? n : +v; }
  function chopNode(leaf) {
    const backup = O.cloneTree(root);
    // map the leaf into the backup is unnecessary: we restore by swapping roots
    O.chop(root, leaf, copies());
    if (O.countNodes(root) > 1200) {
      root = backup;
      okBox($('hyInfo'), bi('That chop would grow the hydra beyond 1200 nodes, too many to draw. (The ordinal would still drop.) Try another head or a smaller copy count.', '这一刀会让九头蛇超过 1200 个节点，画不下了。（序数照样会下降。）换个头或调小副本数试试。'), 'warn');
      return false;
    }
    hist.push([bilText(`after step ${n}`, `第 ${n} 步后`), H(O.hydraOrd(root))]);
    n++;
    render();
    return true;
  }
  function render() { drawHydra(svg, root, { onChop: chopNode }); info(); }
  function load(i) { root = presets[i](); n = 1; hist = [[bilText('start', '开始'), H(O.hydraOrd(root))]]; $('hyInfo').className = 'msg info'; render(); }
  document.querySelectorAll('[data-hy]').forEach(b => b.addEventListener('click', () => load(+b.dataset.hy)));
  $('hyAuto').addEventListener('click', async () => {
    for (let i = 0; i < 20 && root.ch.length; i++) {
      let h = root; while (h.ch.length) h = h.ch[h.ch.length - 1];
      if (!chopNode(h)) break;
      await sleep(160);
    }
  });
  load(0);
})();

/* ================= Step 6: Gentzen staircase ================= */
(function gentzen() {
  const svg = $('gnSvg');
  const towerStr = j => j === 0 ? '1' : 'ω' + '^ω'.repeat(j - 1);
  let jumpT = 0;
  function draw(jumpLevel = -1) {
    svg.innerHTML = '';
    const n = +$('gnN').value;
    $('gnNv').textContent = n;
    const cols = 7, x0 = 40, w = 100, base = 290;
    for (let j = 1; j <= cols; j++) {
      const x = x0 + (j - 1) * (w + 6), h = 30 + j * 30;
      const reach = j <= n + 1;   // IΣn reaches below ω_{n+1}
      const isEdge = j === n + 1;
      const fill = isEdge ? '#fff3bf' : reach ? '#d3f9d8' : '#e7ecff';
      const r = el('rect', { x, y: base - h, width: w, height: h, rx: 8, fill, stroke: isEdge ? '#f08c00' : reach ? '#2f9e44' : '#3b5bdb', 'stroke-width': jumpLevel === j ? 4 : 1.5, class: 'pop' }, svg);
      r.style.animationDelay = (j * 0.05) + 's';
      towerLabel(svg, x + 12, base - h + 26, j, 16, '#1f2430');
      svgText(svg, x + 8, base - 6, `ω${'₀₁₂₃₄₅₆₇₈'[j]}`, { 'font-size': 12, fill: '#6b7280' });
      if (j >= 2) svgText(svg, x + 8, base - h + 46, `|IΣ${'₀₁₂₃₄₅₆₇₈'[j - 1]}|`, { 'font-size': 13, fill: '#1f2430' });
      if (jumpLevel >= 2 && j >= 2 && j <= jumpLevel) svgText(svg, x + 8, base - h + 66, 'φ' + '⁺'.repeat(j - 1), { 'font-size': 13, fill: '#ae3ec9', 'font-weight': 700 });
    }
    // ε₀ column
    const xe = x0 + cols * (w + 6) + 10;
    el('rect', { x: xe, y: 30, width: 70, height: base - 30, rx: 8, fill: '#ffe3e3', stroke: '#e03131', 'stroke-width': 2, 'stroke-dasharray': '6 4' }, svg);
    svgText(svg, xe + 20, 60, 'ε₀', { 'font-size': 22, fill: '#e03131', 'font-weight': 700 });
    svgText(svg, xe + 6, 90, 'PA ⊬', { 'font-size': 13, fill: '#e03131' });
    svgText(svg, xe + 6, 106, 'TI(ε₀)', { 'font-size': 13, fill: '#e03131' });
    // PA brace
    el('path', { d: `M${x0},${base + 12} L${x0},${base + 20} L${xe - 14},${base + 20} L${xe - 14},${base + 12}`, fill: 'none', stroke: '#2f9e44', 'stroke-width': 2 }, svg);
    const mode = document.body.classList.contains('lang-zh') ? 'zh' : document.body.classList.contains('lang-en') ? 'en' : 'both';
    if (mode !== 'zh') svgText(svg, x0 + 150, base + 36, 'PA = ⋃ IΣₙ reaches every storey below ε₀ (Gentzen 1943)', { 'font-size': 13, fill: '#2f9e44' });
    if (mode !== 'en') svgText(svg, x0 + 150, base + (mode === 'both' ? 52 : 36), 'PA = ⋃ IΣₙ 能到达 ε₀ 以下的每一层（根岑 1943）', { 'font-size': 13, fill: '#2f9e44' });
    const sub = '₀₁₂₃₄₅₆₇₈';
    $('gnMsg').innerHTML = bi(`<b>IΣ${sub[n]}</b> (induction for Σ${sub[n]} formulas): |IΣ${sub[n]}| = ω${sub[n + 1]} = <span class="m">${towerStr(n + 1)}</span> (yellow storey). It proves the well-foundedness of every α below ω${sub[n + 1]} (green), and the supremum is exactly ω${sub[n + 1]}. PA proves every one of these for every n, but never ε₀ itself.`,
      `<b>IΣ${sub[n]}</b>（只对 Σ${sub[n]} 公式归纳）：|IΣ${sub[n]}| = ω${sub[n + 1]} = <span class="m">${towerStr(n + 1)}</span>（黄色层）。它能证明 ω${sub[n + 1]} 以下每个 α 的良基性（绿色），且上确界恰为 ω${sub[n + 1]}。对每个 n，这些 PA 全都能证明，但永远证明不了 ε₀ 本身。`);
  }
  $('gnN').addEventListener('input', () => draw());
  REDRAW.push(() => draw());
  $('gnJump').addEventListener('click', async () => {
    const my = ++jumpT;
    const lines = [
      bi('<b>Gentzen\'s jump.</b> For a formula φ define <span class="m">φ⁺(β) :≡ ∀γ [ ∀δ≺γ φ(δ) → ∀δ≺γ+ω<sup>β</sup> φ(δ) ]</span>.', '<b>根岑跳跃.</b> 对公式 φ 定义 <span class="m">φ⁺(β) :≡ ∀γ [ ∀δ≺γ φ(δ) → ∀δ≺γ+ω<sup>β</sup> φ(δ) ]</span>。'),
      bi('PA proves: if φ is progressive, so is φ⁺; and TI(α, φ⁺) implies TI(ω<sup>α</sup>, φ).', 'PA 能证明：若 φ 累进，则 φ⁺ 也累进；并且 TI(α, φ⁺) 蕴涵 TI(ω<sup>α</sup>, φ)。'),
      bi('Ordinary induction gives TI(ω, ψ) for every ψ. Using φ⁺ we get TI(ω<sup>ω</sup>, φ); using φ⁺⁺, TI(ω<sup>ω<sup>ω</sup></sup>, φ); and so on, one storey per jump.', '普通归纳给出对一切 ψ 的 TI(ω, ψ)。用 φ⁺ 得到 TI(ω<sup>ω</sup>, φ)；用 φ⁺⁺ 得到 TI(ω<sup>ω<sup>ω</sup></sup>, φ)；依此类推，每跳一次上一层。'),
      bi('Each jump adds quantifiers to the induction formula. A single proof uses finitely many jumps, so it reaches some finite storey, never ε₀.', '每跳一次，归纳公式就多几个量词。一个证明只能跳有限次，所以只能到达某个有限的层，永远到不了 ε₀。'),
    ];
    $('gnMsg').innerHTML = '';
    for (let j = 1; j <= 7; j++) {
      if (my !== jumpT) return;
      draw(j);
      $('gnMsg').innerHTML = lines.slice(0, Math.min(4, Math.ceil(j * 4 / 7))).join('<br>');
      await sleep(500);
    }
  });
  draw();
})();

/* ================= Step 7: Veblen grid ================= */
(function veblen() {
  const rows = ['0', '1', '2', '3', 'ω'];
  const sub = '₀₁₂₃₄₅₆₇₈₉';
  const names = [
    b => ['1', 'ω', 'ω²', 'ω³', 'ω⁴'][b],
    b => 'ε' + sub[b], b => 'ζ' + sub[b], b => 'η' + sub[b], b => `φ<sub>ω</sub>(${b})`,
  ];
  const tbl = $('vgrid');
  let h = '<tr><th></th>' + [0, 1, 2, 3, 4].map(b => `<th>β=${b}</th>`).join('') + '<th></th></tr>';
  rows.forEach((a, i) => {
    h += `<tr><th>φ<sub>${a}</sub></th>` + [0, 1, 2, 3, 4].map(b => `<td data-a="${i}" data-b="${b}">${names[i](b)}</td>`).join('') + '<td style="border:0;background:none;cursor:default">…</td></tr>';
  });
  h += '<tr><th>⋮</th><td colspan="6" style="border:0;background:none;cursor:default;color:#6b7280;font-size:13px">' + bil('rows φ<sub>α</sub> for every ordinal α', '每个序数 α 都有一行 φ<sub>α</sub>') + '</td></tr>';
  tbl.innerHTML = h;
  const cells = [...tbl.querySelectorAll('td[data-a]')];
  function describe(i, b) {
    const v = names[i](b), a = rows[i];
    if (i === 0) return bi(`φ₀(${b}) = ω<sup>${b}</sup> = ${v}. Row 0 is just β ↦ ω<sup>β</sup>; its fixed points are the ε-numbers (row 1).`, `φ₀(${b}) = ω<sup>${b}</sup> = ${v}。第 0 行就是 β ↦ ω<sup>β</sup>；它的不动点就是 ε 数（第 1 行）。`);
    const prevName = i === 4 ? null : (i === 1 ? 'ω^' : names[i - 1](0)[0]);
    let how;
    if (i === 4) {
      how = b === 0 ? bi('φ<sub>ω</sub>(0) = sup{ε₀, ζ₀, η₀, …} = sup<sub>n</sub> φₙ(0): the first common fixed point of all φₙ, n &lt; ω.', 'φ<sub>ω</sub>(0) = sup{ε₀, ζ₀, η₀, …} = sup<sub>n</sub> φₙ(0)：所有 φₙ（n &lt; ω）的第一个公共不动点。')
        : bi(`φ<sub>ω</sub>(${b}) = sup<sub>n</sub> φₙ(φ<sub>ω</sub>(${b - 1}) + 1): the next common fixed point after φ<sub>ω</sub>(${b - 1}).`, `φ<sub>ω</sub>(${b}) = sup<sub>n</sub> φₙ(φ<sub>ω</sub>(${b - 1}) + 1)：φ<sub>ω</sub>(${b - 1}) 之后的下一个公共不动点。`);
    } else {
      const f = i === 1 ? 'ω^' : `φ${sub[i - 1]}`;
      const start = b === 0 ? (i === 1 ? '0' : names[i - 1](0)) : `${names[i](b - 1)}+1`;
      how = b === 0
        ? bi(`${v} = φ${sub[i]}(0) = sup{${i === 1 ? '1, ω, ω^ω' : `${names[i - 1](0)}, ${f}(${names[i - 1](0)}), ${f}(${f}(${names[i - 1](0)}))`}, …}: the <b>first</b> fixed point of φ${sub[i - 1]}.`,
             `${v} = φ${sub[i]}(0) = sup{${i === 1 ? '1, ω, ω^ω' : `${names[i - 1](0)}, ${f}(${names[i - 1](0)}), ${f}(${f}(${names[i - 1](0)}))`}, …}：φ${sub[i - 1]} 的<b>第一个</b>不动点。`)
        : bi(`${v} = φ${sub[i]}(${b}) = sup{${start}, ${f}(${start}), ${f}(${f}(${start})), …}: the next fixed point of φ${sub[i - 1]} after ${names[i](b - 1)} (note: start from ${start}, not from ${names[i](b - 1)}, which is already fixed).`,
             `${v} = φ${sub[i]}(${b}) = sup{${start}, ${f}(${start}), ${f}(${f}(${start})), …}：φ${sub[i - 1]} 在 ${names[i](b - 1)} 之后的下一个不动点（注意要从 ${start} 出发，而不是从已经是不动点的 ${names[i](b - 1)} 出发）。`);
    }
    const fixes = rows.slice(0, i).map(d => `φ<sub>${d}</sub>(${v}) = ${v}`).join(', ');
    void prevName;
    return how + '<br>' + bi(`Fixed by every earlier row: ${fixes}.`, `被前面每一行固定：${fixes}。`);
  }
  cells.forEach(c => c.addEventListener('click', () => {
    const i = +c.dataset.a, b = +c.dataset.b;
    cells.forEach(x => x.classList.remove('hl', 'fx', 'diag'));
    c.classList.add('hl');
    cells.filter(x => +x.dataset.a < i).forEach(x => x.classList.add('fx'));
    okBox($('vgInfo'), describe(i, b), 'info');
  }));
  cells[5].click();
  let runT = 0;
  $('vgRun').addEventListener('click', async () => {
    const my = ++runT;
    cells.forEach(x => x.classList.remove('hl', 'fx', 'diag'));
    const steps = [
      ['γ₀ = 0', null],
      ['γ₁ = φ₀(0) = 1', cells[0]],
      ['γ₂ = φ₁(0) = ε₀', cells[5]],
      ['γ₃ = φ<sub>ε₀</sub>(0)', null],
      ['γ₄ = φ<sub>φ<sub>ε₀</sub>(0)</sub>(0)', null],
      ['⋮', null],
      [bi('Γ₀ = sup γₙ, and φ<sub>Γ₀</sub>(0) = Γ₀: the index has caught up with the value.', 'Γ₀ = sup γₙ，并且 φ<sub>Γ₀</sub>(0) = Γ₀：下标追上了函数值。'), null],
    ];
    const out = [];
    for (const [t, cell] of steps) {
      if (my !== runT) return;
      out.push(t);
      $('vgDiag').innerHTML = out.join('<br>');
      if (cell) cell.classList.add('diag');
      await sleep(600);
    }
    okBox($('vgInfo'), bi('From γ₃ on, the row index is itself a huge ordinal (ε₀, then φ<sub>ε₀</sub>(0), …), far off this grid. Each γₙ₊₁ is the first value of row γₙ. Γ₀ is the first ordinal that names its own row: φ<sub>Γ₀</sub>(0) = Γ₀, so it cannot be built from smaller ordinals with + and φ.', '从 γ₃ 开始，行下标本身就是巨大的序数（ε₀，然后 φ<sub>ε₀</sub>(0)，……），远在这张表之外。每个 γₙ₊₁ 是第 γₙ 行的第一个值。Γ₀ 是第一个给自己所在行命名的序数：φ<sub>Γ₀</sub>(0) = Γ₀，所以它无法用 + 和 φ 从更小的序数造出来。'), 'info');
  });
})();

/* ================= Step 8: gallery ================= */
(function gallery() {
  const items = [
    { name: 'ε₀ = φ₁(0)', tag: 'thm', en: '<b>ε₀</b>. Limit of CNF (Step 2). |PA| = |ACA₀| = ε₀ (Gentzen).', zh: '<b>ε₀</b>。康托尔范式的极限（第 2 步）。|PA| = |ACA₀| = ε₀（根岑）。' },
    { name: 'Γ₀ = φ(1,0,0)', tag: 'thm', en: '<b>Γ₀</b>, Feferman–Schütte ordinal. Least α with φ<sub>α</sub>(0) = α; limit of the binary Veblen functions. |ATR₀| = Γ₀.', zh: '<b>Γ₀</b>，费弗曼–许特序数。满足 φ<sub>α</sub>(0) = α 的最小 α；二元维布伦函数的极限。|ATR₀| = Γ₀。' },
    { name: 'SVO = ϑ(Ω^ω)', tag: 'def', en: '<b>Small Veblen ordinal.</b> Extend φ to finitely many arguments: φ(1,0,0) = Γ₀, φ(1,0,0,0), φ(1,0,0,0,0), …; the SVO is the supremum of φ(1,0,…,0) over all finite lengths.', zh: '<b>小维布伦序数.</b> 把 φ 推广到有限多个自变量：φ(1,0,0) = Γ₀，φ(1,0,0,0)，φ(1,0,0,0,0)，……；小维布伦序数是所有有限长度的 φ(1,0,…,0) 的上确界。' },
    { name: 'LVO = ϑ(Ω^Ω)', tag: 'def', en: '<b>Large Veblen ordinal.</b> Allow transfinitely many arguments (finitely many nonzero); the LVO is the first ordinal that cannot be reached from 0 by + and these transfinite-argument Veblen functions.', zh: '<b>大维布伦序数.</b> 允许超限多个自变量（其中只有有限个非零）；大维布伦序数是从 0 出发、用 + 和这些超限多元维布伦函数造不出来的第一个序数。' },
    { name: 'BH = ψ(ε_{Ω+1})', tag: 'thm', en: '<b>Bachmann–Howard ordinal.</b> Needs a “collapsing function” ψ. It is the proof-theoretic ordinal of Kripke–Platek set theory KP (with infinity) and of ID₁ (one inductive definition), and of CZF.', zh: '<b>巴赫曼–霍华德序数.</b> 需要“坍缩函数” ψ。它是克里普克–普拉特克集合论 KP（含无穷公理）、ID₁（一次归纳定义理论）以及 CZF 的证明论序数。' },
    { name: 'ψ₀(Ω_ω)', tag: 'thm', en: '<b>Buchholz\'s ψ₀(Ω_ω)</b>: the proof-theoretic ordinal of Π¹₁-CA₀ (Π¹₁-comprehension).', zh: '<b>Buchholz 的 ψ₀(Ω_ω)</b>：Π¹₁-CA₀（Π¹₁ 概括）的证明论序数。' },
    { name: '|Z₂| = ?', tag: 'open', en: '<b>Frontier.</b> Ordinal analyses have been pushed to much stronger systems (e.g. KP with Π₃-reflection, and work of Rathjen and Arai towards Π¹₂-comprehension). For full second-order arithmetic Z₂, and for ZF, no ordinal analysis is known: <b>open</b>.', zh: '<b>前沿.</b> 序数分析已推进到强得多的系统（例如带 Π₃ 反射的 KP，以及 Rathjen 和 Arai 关于 Π¹₂ 概括的工作）。对完整的二阶算术 Z₂ 以及 ZF，尚无已知的序数分析：<b>未解决</b>。' },
    { name: 'ω₁^CK', tag: 'thm', en: '<b>ω₁<sup>CK</sup></b> (L18): the supremum of all recursive ordinals; itself not recursive, so it has no notation in any recursive notation system. For every recursively axiomatized theory that proves only true well-foundedness statements (Π¹₁-sound), |T| &lt; ω₁<sup>CK</sup>.', zh: '<b>ω₁<sup>CK</sup></b>（第 18 课）：所有递归序数的上确界；它本身不是递归序数，所以在任何递归记号系统中都没有记号。对每个只证明真的良基性命题（Π¹₁ 可靠）的递归公理化理论，|T| &lt; ω₁<sup>CK</sup>。' },
  ];
  const svg = $('galSvg');
  let sel = 0;
  function draw() {
    svg.innerHTML = '';
    el('line', { x1: 60, y1: 20, x2: 60, y2: 455, stroke: '#c9c3b3', 'stroke-width': 6 }, svg);
    el('line', { x1: 120, y1: 20, x2: 120, y2: 455, stroke: '#c9c3b3', 'stroke-width': 6 }, svg);
    items.forEach((it, i) => {
      const y = 440 - i * 56;
      const g = el('g', { class: 'pop', style: 'cursor:pointer' }, svg);
      g.style.animationDelay = (i * 0.06) + 's';
      const on = i === sel;
      const col = it.tag === 'open' ? '#f08c00' : i === items.length - 1 ? '#c2255c' : '#3b5bdb';
      el('line', { x1: 60, y1: y, x2: 120, y2: y, stroke: on ? col : '#8a7f63', 'stroke-width': on ? 6 : 3 }, g);
      el('circle', { cx: 140, cy: y, r: on ? 8 : 6, fill: col }, g);
      svgText(g, 155, y + 5, it.name, { 'font-size': on ? 16 : 14, 'font-weight': on ? 700 : 400, fill: col });
      el('rect', { x: 40, y: y - 24, width: 400, height: 46, fill: 'transparent' }, g);
      g.addEventListener('click', () => { sel = i; draw(); });
    });
    svgText(svg, 10, 455, '0', { 'font-size': 13, fill: '#6b7280' });
    const it = items[sel];
    const badge = it.tag === 'open' ? `<span class="badge-th open">${bilText('open', '未解决')}</span>` : it.tag === 'def' ? `<span class="badge-th def">${bilText('definition', '定义')}</span>` : `<span class="badge-th">${bilText('theorem', '定理')}</span>`;
    $('galInfo').innerHTML = `<div class="m" style="font-size:18px;font-weight:700">${it.name} ${badge}</div>` + bi(it.en, it.zh) +
      `<p class="muted" style="font-size:13px">${bi('Order on the ladder: ε₀ &lt; Γ₀ &lt; SVO &lt; LVO &lt; BH &lt; ψ₀(Ω_ω) &lt; … &lt; ω₁<sup>CK</sup> (theorems). All except ω₁<sup>CK</sup> are recursive ordinals.', '梯子上的顺序：ε₀ &lt; Γ₀ &lt; 小维布伦 &lt; 大维布伦 &lt; BH &lt; ψ₀(Ω_ω) &lt; … &lt; ω₁<sup>CK</sup>（均为定理）。除 ω₁<sup>CK</sup> 外都是递归序数。')}</p>`;
  }
  draw();
})();

/* ================= Step 9: fast-growing hierarchy ================= */
function fmtF(r, short = false) {
  if (r.k === 'ex') {
    const s = r.v.toString();
    if (s.length <= (short ? 12 : 80)) return s;
    if (short) return `≈10^${s.length - 1}`;
    return `${s.slice(0, 30)}…${s.slice(-10)} <span class="muted">(${bilText(`${s.length} digits`, `${s.length} 位`)})</span>`;
  }
  if (r.k === 'ap') {
    if (r.h === 0) return String(Math.round(r.t));
    if (short && r.h >= 2) return r.h <= 4 ? '≈' + '10^'.repeat(r.h) + fmtNum(r.t) : bilText(`tower of ${fmtNum(r.h)} 10s`, `${fmtNum(r.h)} 层 10 的幂塔`);
    const tt = r.t < 1e6 ? fmtNum(r.t) : '(' + fmtNum(r.t) + ')';
    if (r.h === 1) return short ? `≈10^${tt}` : `≈ 10^${tt} <span class="muted">(${bilText(`about ${fmtNum(r.t + 1)} digits`, `约 ${fmtNum(r.t + 1)} 位`)})</span>`;
    if (r.h === 2) return short ? `≈10^10^${tt}` : `≈ 10^(10^${tt}) <span class="muted">(${bilText('even its number of digits has about ' + fmtNum(r.t + 1) + ' digits', '连它的位数都约有 ' + fmtNum(r.t + 1) + ' 位')})</span>`;
    const hh = r.h > 1e6 ? fmtNum(r.h) : String(r.h);
    return short ? `10^^…(${hh})` : `≈ 10^10^…^10^${fmtNum(r.t)} <span class="muted">(${bilText(`a tower with ${hh} tens`, `由 ${hh} 个 10 叠成的幂塔`)})</span>`;
  }
  if (short) return bilText('too big', '太大');
  if (r.k === 'bud') return bilText('budget exceeded', '超出计算预算');
  return bilText('beyond', '超出');
}
function fmtNum(x) { return x < 1e6 ? (Math.round(x * 100) / 100).toString() : x.toExponential(3).replace('e+', '×10^'); }
(function fgh() {
  function trace(a, n) {
    const lines = [];
    let cur = a;
    for (let i = 0; i < 14; i++) {
      if (O.isZero(cur)) { lines.push(`f₀(${n}) = ${n + 1}`); break; }
      if (O.isLimit(cur)) { const nx = O.fs(cur, n); lines.push(`<span class="lim">f<sub>${O.toHTML(cur)}</sub>(${n}) = f<sub>${O.toHTML(nx)}</sub>(${n})</span>`); cur = nx; }
      else { const p = O.pred(cur); lines.push(`<span class="suc">f<sub>${O.toHTML(cur)}</sub>(${n}) = f<sub>${O.toHTML(p)}</sub><sup>${n}</sup>(${n})</span> &nbsp;${bil('(iterate n times)', '（迭代 n 次）')}`); break; }
    }
    return lines.join('<br>');
  }
  function go() {
    let a, n;
    try { a = O.parse($('fgA').value, true); } catch (e) { okBox($('fgOut'), errHTML(e), 'bad'); return; }
    n = Number($('fgN').value);
    if (!Number.isInteger(n) || n < 0 || n > 1000) { okBox($('fgOut'), bi('n must be an integer 0…1000.', 'n 必须是 0…1000 的整数。'), 'bad'); return; }
    let r;
    try { r = O.makeFGH().f(a, n); } catch (e) { r = { k: 'bud' }; }
    okBox($('fgOut'), `f<sub>${O.toHTML(a)}</sub>(${n}) = ${fmtF(r)}` + (r.k === 'bey' ? '<br>' + bi('This value is far too large for the calculator to describe (it does not even fit a short power-tower description).', '这个值大到本计算器无法描述（连简短的幂塔描述都放不下）。') : r.k === 'bud' ? '<br>' + bi('The calculator gave up: its step/recursion budget ran out before the evaluation finished. (The value exists, since f<sub>α</sub> is total; it is just out of reach here.)', '计算器放弃了：在求值完成之前，步数/递归预算就用完了。（这个值是存在的，因为 f<sub>α</sub> 是全函数；只是这里算不到。）') : ''), r.k === 'ex' || (r.k === 'ap') ? 'ok' : 'warn');
    $('fgTrace').innerHTML = trace(a, n);
  }
  $('fgGo').addEventListener('click', go);
  document.querySelectorAll('[data-fg]').forEach(b => b.addEventListener('click', () => { const [a, n] = b.dataset.fg.split(','); $('fgA').value = a; $('fgN').value = n; go(); }));
  go();
  // growth table
  const as = ['0', '1', '2', '3', 'ω', 'ω+1', 'ε0'];
  let h = '<table class="tbl21"><tr><th>α \\ n</th>' + [0, 1, 2, 3, 4].map(n => `<th>${n}</th>`).join('') + '</tr>';
  as.forEach(s => {
    const a = O.parse(s, true);
    h += `<tr><th>f<sub>${O.toHTML(a)}</sub></th>` + [0, 1, 2, 3, 4].map(n => `<td>${fmtF(O.makeFGH(2e5).f(a, n), true)}</td>`).join('') + '</tr>';
  });
  $('fgTable').innerHTML = h + '</table>';
  // Hardy walk
  function walk() {
    let a, n;
    try { a = O.parse($('hwA').value, true); } catch (e) { $('hwOut').innerHTML = errHTML(e); return; }
    n = Number($('hwN').value);
    if (!Number.isInteger(n) || n < 0 || n > 1000) { $('hwOut').innerHTML = bi('n must be an integer 0…1000.', 'n 必须是 0…1000 的整数。'); return; }
    const w = O.hardyWalk(a, n, 200000, 300);
    const lines = w.trace.map(([al, m], i) => {
      const nxt = w.trace[i + 1];
      const cls = O.isZero(al) ? 'ok-mark' : O.isLimit(al) ? 'lim' : 'suc';
      return `<span class="${cls}">(${O.toStr(al)}, n = ${m})</span>` + (nxt ? '' : '');
    });
    const head = w.done
      ? bi(`H<sub>${O.toHTML(a)}</sub>(${n}) = <b>${w.n}</b> after ${w.steps} moves.`, `H<sub>${O.toHTML(a)}</sub>(${n}) = <b>${w.n}</b>，共走 ${w.steps} 步。`)
      : bi(`Stopped after ${w.steps} moves (n has reached ${w.n}); the walk still ends, but later.`, `走了 ${w.steps} 步后停止显示（此时 n 已到 ${w.n}）；行走仍会结束，只是更晚。`);
    const extra = (w.done && a !== 'E0' && O.isZero(a) === false) ? '' : '';
    $('hwOut').innerHTML = head + extra + '<br>' + lines.join(' → ') + (w.trace.length >= 300 && w.done ? ' → …' : '');
  }
  $('hwGo').addEventListener('click', walk);
  walk();
})();

/* ================= Step 10: summary ladder ================= */
(function summary() {
  const pins = [
    { o: 'ω^ω', th: 'PRA, IΣ₁, RCA₀, WKL₀', tag: 'thm', en: 'ω<sup>ω</sup>: PRA, IΣ₁, RCA₀ and WKL₀ all have proof-theoretic ordinal ω<sup>ω</sup>.', zh: 'ω<sup>ω</sup>：PRA、IΣ₁、RCA₀、WKL₀ 的证明论序数都是 ω<sup>ω</sup>。' },
    { o: 'ω^ω^ω', th: 'IΣ₂', tag: 'thm', en: 'In general |IΣₙ| = ωₙ₊₁ (n ≥ 1): one more ω per quantifier alternation (Step 6).', zh: '一般地 |IΣₙ| = ωₙ₊₁（n ≥ 1）：每多一层量词交替，多一个 ω（第 6 步）。' },
    { o: 'ε₀', th: 'PA, ACA₀', tag: 'thm', en: 'ε₀: PA (Gentzen 1936/1943) and ACA₀ (conservative over PA for arithmetic sentences).', zh: 'ε₀：PA（根岑 1936/1943）与 ACA₀（对算术语句是 PA 的保守扩张）。' },
    { o: 'ε_ε₀', th: 'ACA', tag: 'thm', en: 'ε<sub>ε₀</sub>: ACA, i.e. ACA₀ plus full induction.', zh: 'ε<sub>ε₀</sub>：ACA，即 ACA₀ 加完全归纳。' },
    { o: 'Γ₀', th: 'ATR₀', tag: 'thm', en: 'Γ₀: ATR₀ (Friedman–McAloon–Simpson 1982); also the bound of Feferman–Schütte predicative analysis (Step 7, with the caveat stated there).', zh: 'Γ₀：ATR₀（Friedman–McAloon–Simpson 1982）；也是费弗曼–许特直谓分析的界（见第 7 步及那里的注意事项）。' },
    { o: 'ψ(ε_{Ω+1})', th: 'KP, ID₁', tag: 'thm', en: 'Bachmann–Howard ordinal: Kripke–Platek set theory KP (with infinity) and ID₁.', zh: '巴赫曼–霍华德序数：克里普克–普拉特克集合论 KP（含无穷公理）与 ID₁。' },
    { o: 'ψ₀(Ω_ω)', th: 'Π¹₁-CA₀', tag: 'thm', en: 'Buchholz\'s ψ₀(Ω_ω): Π¹₁-CA₀.', zh: 'Buchholz 的 ψ₀(Ω_ω)：Π¹₁-CA₀。' },
    { o: '?', th: 'Z₂, ZF', tag: 'open', en: 'Full second-order arithmetic Z₂ and ZF: no ordinal analysis known (open). Their ordinals, under any reasonable definition, would still be recursive if the theories are Π¹₁-sound.', zh: '完整二阶算术 Z₂ 与 ZF：尚无已知的序数分析（未解决）。若这些理论 Π¹₁ 可靠，那么在任何合理的定义下，它们的序数仍是递归序数。' },
    { o: 'ω₁^CK', th: bilText('bound', '上界'), tag: 'thm', en: 'ω₁<sup>CK</sup>: strict upper bound for |T| of every Π¹₁-sound recursively axiomatized T (L18). Not itself recursive.', zh: 'ω₁<sup>CK</sup>：每个 Π¹₁ 可靠的递归公理化理论 T 的 |T| 的严格上界（第 18 课）。它本身不是递归序数。' },
  ];
  const svg = $('sumSvg');
  let shown = pins.length, sel = 2;
  function draw() {
    svg.innerHTML = '';
    const x0 = 60, x1 = 860, y = 200;
    el('line', { x1: x0, y1: y, x2: x1, y2: y, stroke: '#1f2430', 'stroke-width': 3 }, svg);
    svgText(svg, x0 - 30, y + 5, 'ω', { 'font-size': 16 });
    pins.forEach((p, i) => {
      if (i >= shown) return;
      const x = 120 + i * (700 / (pins.length - 1));
      const up = i % 2 === 0;
      const col = p.tag === 'open' ? '#f08c00' : i === pins.length - 1 ? '#c2255c' : '#3b5bdb';
      const g = el('g', { class: 'pop', style: 'cursor:pointer' }, svg);
      const on = i === sel;
      el('line', { x1: x, y1: y, x2: x, y2: up ? y - 70 : y + 70, stroke: col, 'stroke-width': on ? 3 : 1.5 }, g);
      el('circle', { cx: x, cy: y, r: on ? 9 : 6, fill: col }, g);
      el('rect', { x: x - 75, y: up ? y - 150 : y + 70, width: 150, height: 76, rx: 10, fill: on ? '#fff' : '#fbfaf6', stroke: col, 'stroke-width': on ? 2.5 : 1 }, g);
      svgText(g, x, up ? y - 122 : y + 98, p.o, { 'text-anchor': 'middle', 'font-size': 15, 'font-weight': 700, fill: col });
      svgText(g, x, up ? y - 100 : y + 120, p.th, { 'text-anchor': 'middle', 'font-size': p.th.length > 16 ? 11 : 13, fill: '#1f2430' });
      svgText(g, x, up ? y - 82 : y + 138, p.tag === 'open' ? bilText('open', '未解决') : bilText('theorem', '定理'), { 'text-anchor': 'middle', 'font-size': 10.5, fill: p.tag === 'open' ? '#f08c00' : '#2f9e44' });
      g.addEventListener('click', () => { sel = i; draw(); });
    });
    const p = pins[sel];
    $('sumInfo').innerHTML = (sel < shown) ? bi(p.en, p.zh) : '';
  }
  $('sumPlay').addEventListener('click', async () => { for (shown = 0; shown <= pins.length; shown++) { sel = Math.max(0, shown - 1); draw(); await sleep(420); } shown = pins.length; });
  draw();
  // relabel SVG text when the language switches
  document.querySelectorAll('.lang-switch button').forEach(b => b.addEventListener('click', () => setTimeout(draw, 0)));
})();

/* ================= Exercises ================= */
function rowQ(container, qHTML, onCheck, opts = {}) {
  const d = document.createElement('div');
  d.className = 'row-q';
  d.innerHTML = `<div class="q">${qHTML}</div><input class="formula" style="min-width:${opts.w || 180}px;width:${opts.w || 180}px" placeholder="${opts.ph || ''}"><button class="btn small">${bil('Check', '检查')}</button><span class="res"></span>`;
  const inp = d.querySelector('input'), res = d.querySelector('.res');
  const run = () => { const r = onCheck(inp.value); res.innerHTML = r.html; res.className = 'res ' + (r.ok ? 'ok-mark' : 'bad-mark'); };
  d.querySelector('button').addEventListener('click', run);
  inp.addEventListener('keydown', e => e.key === 'Enter' && run());
  container.appendChild(d);
  return { show(html) { res.innerHTML = html; res.className = 'res ok-mark'; }, inp };
}

// E1: α[n]
(function e1() {
  const tasks = [['ω^2·2+ω', 3], ['ω^ω', 4], ['ω^(ω+1)', 2], ['ω^3·2', 2], ['ε0', 3]];
  const solved = tasks.map(() => false);
  let revealed = false; // Show answer pressed: no progress this page session
  const rows = tasks.map(([s, n], i) => {
    const a = O.parse(s, true), ans = O.fs(a, n);
    return rowQ($('e1List'), `<span class="ordin">(${O.toHTML(a)})[${n}]</span> = ?`, v => {
      let x; try { x = O.parse(v); } catch (e) { return { ok: false, html: errHTML(e) }; }
      if (O.cmp(x, ans) === 0) { solved[i] = true; if (solved.every(Boolean) && !revealed) Progress.mark('L21E1'); return { ok: true, html: '✓' }; }
      return { ok: false, html: bi(`✗ you wrote ${H(x)}; ${O.cmp(x, ans) < 0 ? 'too small' : 'too big'}`, `✗ 你写的是 ${H(x)}，${O.cmp(x, ans) < 0 ? '偏小' : '偏大'}`) };
    }, { ph: 'ω^…' });
  });
  $('e1Show').addEventListener('click', () => (revealed = true) && tasks.forEach(([s, n], i) => rows[i].show('= ' + H(O.fs(O.parse(s, true), n)))));
})();

// E2: Goodstein from 5
(function e2() {
  let T = O.hered(5n, 2), b = 2;
  const seq = [O.exactVal(T, b)];
  const trees = [T];
  for (let i = 0; i < 4; i++) { b++; T = O.sub1(T, b); seq.push(O.exactVal(T, b)); trees.push(T); }
  const o1 = trees[1];
  const solved = { a: false, b: false };
  let revealed = false;
  const fin = () => solved.a && solved.b && !revealed && Progress.mark('L21E2');
  $('e2aGo').addEventListener('click', () => {
    const v = $('e2a').value.split(/[,\s，]+/).filter(Boolean);
    const want = seq.map(String);
    if (v.length === 5 && v.every((x, i) => x === want[i])) { solved.a = true; okBox($('e2aMsg'), bi('✓ Correct.', '✓ 正确。')); fin(); }
    else {
      const k = v.findIndex((x, i) => x !== want[i]);
      okBox($('e2aMsg'), v.length < 5 && k === -1 ? bi('Correct so far; five terms are needed.', '目前都对，需要五项。') : k === 0 ? bi('g<sub>0</sub> is the starting value m = 5.', 'g<sub>0</sub> 就是初值 m = 5。') : bi(`Term g<sub>${k}</sub> is not right. Write g<sub>${Math.max(k - 1, 0)}</sub> in hereditary base ${k + 1}, bump the base to ${k + 2}, subtract 1.`, `g<sub>${k}</sub> 不对。把 g<sub>${Math.max(k - 1, 0)}</sub> 写成遗传 ${k + 1} 进制，换底为 ${k + 2}，再减 1。`), 'bad');
    }
  });
  $('e2bGo').addEventListener('click', () => {
    let x; try { x = O.parse($('e2b').value); } catch (e) { okBox($('e2bMsg'), errHTML(e), 'bad'); return; }
    if (O.cmp(x, o1) === 0) { solved.b = true; okBox($('e2bMsg'), bi(`✓ g₁ = 27 = 3<sup>3</sup>, so o₁ = ${H(o1)}.`, `✓ g₁ = 27 = 3<sup>3</sup>，所以 o₁ = ${H(o1)}。`)); fin(); }
    else okBox($('e2bMsg'), bi('✗ Write g₁ in hereditary base 3 first.', '✗ 先把 g₁ 写成遗传三进制。'), 'bad');
  });
  $('e2Show').addEventListener('click', () => {
    revealed = true;
    const forms = trees.map((t, i) => `g${'₀₁₂₃₄'[i]} = ${O.heredHTML(t, i + 2)} = ${seq[i]}`).join('<br>');
    okBox($('e2aMsg'), bi('Answer: ', '答案：') + seq.join(', ') + '<br><span class="m" style="font-size:14px">' + forms + '</span>', 'info');
    okBox($('e2bMsg'), bi(`o₁ = ${H(o1)} (since g₁ = 3<sup>3</sup>). Then o₂ = ${H(trees[2])}: smaller, as promised.`, `o₁ = ${H(o1)}（因为 g₁ = 3<sup>3</sup>）。接着 o₂ = ${H(trees[2])}：如定理所说，变小了。`), 'info');
  });
})();

// E3: comparisons
(function e3() {
  const P = s => O.parse(s);
  const rel = (a, b) => ['<', '=', '>'][O.cmp(P(a), P(b)) + 1];
  const items = [
    { l: 'ω^ω', r: 'ω^3·1000', a: rel('ω^ω', 'ω^3·1000'), why: ['Leading exponents ω &gt; 3.', '首项指数 ω &gt; 3。'] },
    { l: '1 + ω', r: 'ω', a: rel('1+ω', 'ω'), why: ['1 + ω = ω: the 1 is absorbed.', '1 + ω = ω：1 被吸收了。'] },
    { l: 'ω·2', r: '2·ω', a: rel('ω·2', '2·ω'), why: ['2·ω = sup 2n = ω, while ω·2 = ω + ω.', '2·ω = sup 2n = ω，而 ω·2 = ω + ω。'] },
    { l: 'ω^(ω+1)', r: 'ω^ω · ω', a: rel('ω^(ω+1)', 'ω^ω*ω'), why: ['ω<sup>ω</sup>·ω = ω<sup>ω+1</sup>.', 'ω<sup>ω</sup>·ω = ω<sup>ω+1</sup>。'] },
    { l: 'ε₀', r: 'ω^ε₀', a: '=', why: ['ε₀ is a fixed point of ω^·.', 'ε₀ 是 ω^· 的不动点。'] },
    { l: 'φ₁(1) = ε₁', r: 'ω^(ε₀+1)', a: '>', why: ['ω<sup>ε₀+1</sup> = ε₀·ω is not an ε-number; ε₁ is the next fixed point after ε₀, and ε₁ &gt; ε₀·ω.', 'ω<sup>ε₀+1</sup> = ε₀·ω 不是 ε 数；ε₁ 是 ε₀ 之后的下一个不动点，ε₁ &gt; ε₀·ω。'] },
    { l: 'φ₁(φ₂(0))', r: 'φ₂(0)', a: '=', why: ['ζ₀ = φ₂(0) is a fixed point of φ₁.', 'ζ₀ = φ₂(0) 是 φ₁ 的不动点。'] },
    { l: 'φ₁(ζ₀ + 1)', r: 'φ₂(1)', a: '<', why: ['Rule (a) with 1 &lt; 2: compare ζ₀+1 with φ₂(1) = ζ₁; ζ₀+1 &lt; ζ₁.', '规则 (a)，1 &lt; 2：比较 ζ₀+1 与 φ₂(1) = ζ₁；ζ₀+1 &lt; ζ₁。'] },
    { l: 'Γ₀', r: 'φ<sub>ε₀</sub>(0)', a: '>', why: ['φ<sub>ε₀</sub>(0) = γ₃ in the sequence whose sup is Γ₀; Γ₀ is above all γₙ.', 'φ<sub>ε₀</sub>(0) 是以 Γ₀ 为上确界的序列中的 γ₃；Γ₀ 大于所有 γₙ。'] },
  ];
  const solved = items.map(() => false);
  let revealed = false;
  const rowsEl = items.map((it, i) => {
    const d = document.createElement('div');
    d.className = 'row-q';
    d.innerHTML = `<div class="q"><span class="ordin">${it.l}</span> &nbsp;?&nbsp; <span class="ordin">${it.r}</span></div><span class="cmpbtns">${['<', '=', '>'].map(s => `<button class="btn small" data-v="${s}">${s}</button>`).join(' ')}</span><span class="res" style="flex:1 1 100%;font-size:14px"></span>`;
    const res = d.querySelector('.res');
    d.querySelectorAll('[data-v]').forEach(b => b.addEventListener('click', () => {
      d.querySelectorAll('[data-v]').forEach(x => x.classList.remove('right', 'wrongc'));
      const ok = b.dataset.v === it.a;
      b.classList.add(ok ? 'right' : 'wrongc');
      res.innerHTML = ok ? '✓ ' + bi(...it.why) : bi('✗ Not quite. Try again or use the comparator in Step 1.', '✗ 不对。再试试，或者用第 1 步的比较器。');
      res.className = 'res ' + (ok ? 'ok-mark' : 'bad-mark');
      if (ok) { solved[i] = true; if (solved.every(Boolean) && !revealed) Progress.mark('L21E3'); }
    }));
    $('e3List').appendChild(d);
    return d;
  });
  $('e3Show').addEventListener('click', () => (revealed = true) && rowsEl.forEach((d, i) => {
    d.querySelectorAll('[data-v]').forEach(x => x.classList.toggle('right', x.dataset.v === items[i].a));
    const res = d.querySelector('.res'); res.innerHTML = items[i].a + ' · ' + bi(...items[i].why); res.className = 'res ok-mark';
  }));
})();

// E4: small f values
(function e4() {
  const tasks = [['1', 5], ['2', 3], ['3', 2], ['ω', 2], ['ω+1', 1]];
  const solved = tasks.map(() => false);
  let revealed = false;
  const hints = { '3,2': ['f₃(2) = f₂(f₂(2)) = f₂(8).', 'f₃(2) = f₂(f₂(2)) = f₂(8)。'], 'ω,2': ['f<sub>ω</sub>(2) = f₂(2).', 'f<sub>ω</sub>(2) = f₂(2)。'], 'ω+1,1': ['f<sub>ω+1</sub>(1) = f<sub>ω</sub>(1) = f₁(1).', 'f<sub>ω+1</sub>(1) = f<sub>ω</sub>(1) = f₁(1)。'] };
  const rows = tasks.map(([s, n], i) => {
    const a = O.parse(s), ans = O.makeFGH().f(a, n).v.toString();
    return rowQ($('e4List'), `<span class="ordin">f<sub>${O.toHTML(a)}</sub>(${n})</span> = ?`, v => {
      if (v.replace(/[\s,]/g, '') === ans) { solved[i] = true; if (solved.every(Boolean) && !revealed) Progress.mark('L21E4'); return { ok: true, html: '✓' }; }
      const hk = hints[`${s},${n}`];
      return { ok: false, html: '✗ ' + (hk ? bi(...hk) : bi('Unfold the definition once more.', '再按定义展开一次。')) };
    }, { w: 120 });
  });
  $('e4Show').addEventListener('click', () => (revealed = true) && tasks.forEach(([s, n], i) => {
    const a = O.parse(s);
    rows[i].show('= ' + O.makeFGH().f(a, n).v.toString() + (hints[`${s},${n}`] ? ' · ' + bi(...hints[`${s},${n}`]) : ''));
  }));
})();

// E5: true / false
(function e5() {
  const st = [
    { t: true, en: 'Gentzen proved Con(PA) in PRA + quantifier-free transfinite induction up to ε₀.', zh: '根岑在 PRA + 直到 ε₀ 的无量词超限归纳中证明了 Con(PA)。', why: ['Exactly Gentzen\'s theorem (Step 6).', '这正是根岑定理（第 6 步）。'] },
    { t: false, en: 'Gentzen\'s consistency proof contradicts Gödel\'s second incompleteness theorem.', zh: '根岑的一致性证明与哥德尔第二不完全性定理相矛盾。', why: ['No: it uses QF-TI(ε₀), which PA does not prove.', '不矛盾：它用了 PA 证明不了的 QF-TI(ε₀)。'] },
    { t: true, en: 'For each fixed formula φ, PA proves transfinite induction for φ up to ω^ω^ω^ω.', zh: '对每个固定的公式 φ，PA 都能证明 φ 的直到 ω^ω^ω^ω 的超限归纳。', why: ['ω₄ &lt; ε₀, so Gentzen 1943 applies.', 'ω₄ &lt; ε₀，可用根岑 1943 的结果。'] },
    { t: false, en: 'PA proves: for every m, the Goodstein sequence of m terminates.', zh: 'PA 能证明：对每个 m，m 的古德斯坦序列都终止。', why: ['Kirby–Paris 1982: unprovable in PA (yet true).', '柯比–帕里斯 1982：在 PA 中不可证（但它是真的）。'] },
    { t: true, en: 'PA proves that the Goodstein sequence starting at m = 4 terminates.', zh: 'PA 能证明从 m = 4 开始的古德斯坦序列会终止。', why: ['A single instance is a true Σ⁰₁ sentence, and PA proves all true Σ⁰₁ sentences.', '单个实例是真的 Σ⁰₁ 语句，而 PA 能证明所有真的 Σ⁰₁ 语句。'] },
    { t: false, en: 'ε₀ is uncountable.', zh: 'ε₀ 是不可数的。', why: ['It is a countable supremum of countable ordinals.', '它是可数个可数序数的上确界。'] },
    { t: false, en: 'ω₁<sup>CK</sup> is the order type of some recursive well-ordering of ℕ.', zh: 'ω₁<sup>CK</sup> 是 ℕ 上某个递归良序的序型。', why: ['ω₁<sup>CK</sup> is exactly the least non-recursive ordinal.', 'ω₁<sup>CK</sup> 恰好是最小的非递归序数。'] },
    { t: true, en: '|ATR₀| = Γ₀ and |KP| is the Bachmann–Howard ordinal.', zh: '|ATR₀| = Γ₀，|KP| 是巴赫曼–霍华德序数。', why: ['Both are established ordinal analyses.', '两者都是已完成的序数分析。'] },
    { t: false, en: 'f<sub>ε₀</sub> is provably total in PA.', zh: 'f<sub>ε₀</sub> 在 PA 中可证为全函数。', why: ['It eventually dominates every PA-provably total recursive function, so it is not one of them.', '它最终控制每个 PA 可证全的递归函数，所以它自己不在其中。'] },
    { t: false, en: 'The functions f<sub>α</sub> depend only on the ordinal α, not on the chosen fundamental sequences.', zh: '函数 f<sub>α</sub> 只取决于序数 α，与所选基本序列无关。', why: ['They depend on the fundamental sequences (Step 9 pitfall).', '它们依赖于基本序列（见第 9 步的误区）。'] },
  ];
  const solved = st.map(() => false);
  let revealed = false;
  const rows = st.map((s, i) => {
    const d = document.createElement('div');
    d.className = 'row-q';
    d.innerHTML = `<div class="q">${bi(s.en, s.zh)}</div><span class="cmpbtns"><button class="btn small" data-v="1">${bil('True', '对')}</button> <button class="btn small" data-v="0">${bil('False', '错')}</button></span><span class="res" style="flex:1 1 100%;font-size:14px"></span>`;
    const res = d.querySelector('.res');
    d.querySelectorAll('[data-v]').forEach(b => b.addEventListener('click', () => {
      d.querySelectorAll('[data-v]').forEach(x => x.classList.remove('right', 'wrongc'));
      const ok = (b.dataset.v === '1') === s.t;
      b.classList.add(ok ? 'right' : 'wrongc');
      res.innerHTML = (ok ? '✓ ' : '✗ ') + (ok ? bi(...s.why) : bi('Think again.', '再想想。'));
      res.className = 'res ' + (ok ? 'ok-mark' : 'bad-mark');
      if (ok) { solved[i] = true; if (solved.every(Boolean) && !revealed) Progress.mark('L21E5'); }
    }));
    $('e5List').appendChild(d);
    return d;
  });
  $('e5Show').addEventListener('click', () => (revealed = true) && rows.forEach((d, i) => {
    d.querySelectorAll('[data-v]').forEach(x => x.classList.toggle('right', (x.dataset.v === '1') === st[i].t));
    const res = d.querySelector('.res'); res.innerHTML = (st[i].t ? bilText('True', '对') : bilText('False', '错')) + ' · ' + bi(...st[i].why); res.className = 'res ok-mark';
  }));
})();

// E6: hydra ordinal
(function e6() {
  const mark = leafN();
  const root = nodeN(leafN(), nodeN(mark, leafN()), nodeN(nodeN(leafN())));
  drawHydra($('e6Svg'), root, { W: 420, H: 220, mark });
  const ansA = O.hydraOrd(root);
  const after = O.cloneTree(root);
  // the marked head is the first child of the second child
  O.chop(after, after.ch[1].ch[0], 2);
  const ansB = O.hydraOrd(after);
  const solved = { a: false, b: false };
  let revealed = false;
  const fin = () => solved.a && solved.b && !revealed && Progress.mark('L21E6');
  function check(inp, ans, box, key, hint) {
    let x; try { x = O.parse($(inp).value); } catch (e) { okBox($(box), errHTML(e), 'bad'); return; }
    if (O.cmp(x, ans) === 0) { solved[key] = true; okBox($(box), '✓ ' + H(ans)); fin(); }
    else okBox($(box), '✗ ' + bi(...hint), 'bad');
  }
  $('e6aGo').addEventListener('click', () => check('e6a', ansA, 'e6aMsg', 'a', ['Compute bottom-up: a head is 0; a node is the natural sum of ω^(child).', '自下而上计算：头是 0；节点是各子节点 ω^(子) 的自然和。']));
  $('e6bGo').addEventListener('click', () => check('e6b', ansB, 'e6bMsg', 'b', ['The middle neck loses a head (ordinal 2 → 1), and n = 2 extra copies of it attach to the root.', '中间那根脖子少了一个头（序数 2 → 1），并且它的 n = 2 个副本接到根上。']));
  $('e6Show').addEventListener('click', () => {
    revealed = true;
    okBox($('e6aMsg'), bi(`(a) ${H(ansA)}: heads give 1, the two-headed neck gives ω², the long neck gives ω<sup>ω</sup>.`, `(a) ${H(ansA)}：单独的头贡献 1，双头脖子贡献 ω²，长脖子贡献 ω<sup>ω</sup>。`), 'info');
    okBox($('e6bMsg'), bi(`(b) ${H(ansB)}: the neck becomes one-headed (ω), and with 2 extra copies the root gets ω·3.`, `(b) ${H(ansB)}：那根脖子变成单头（ω），再加 2 个副本，根得到 ω·3。`), 'info');
  });
})();

// keep SVG labels in sync with the language switch (cheap redraws)
document.querySelectorAll('.lang-switch button').forEach(b => b.addEventListener('click', () => {
  setTimeout(() => { REDRAW.forEach(f => f()); }, 0);
}));
})();
