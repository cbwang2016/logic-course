// Lesson 9 interactions: cardinals, cardinal arithmetic, cofinality.
// The CNF ordinal engine and the matchstick drawer below are the same as in lesson8.js
// (each lesson is self-contained, so they are duplicated here).

// ==== ORD ENGINE START ====
// Ordinals below ε₀ in Cantor normal form.
// An ordinal is an array of terms [e, c] meaning ω^e·c, exponents e strictly decreasing, c a positive integer.
// 0 is [], the natural number n is [[[], n]].
const ORD = (() => {
  const LIMIT = 1e12;
  const big = n => {
    if (!Number.isSafeInteger(n) || n > LIMIT) throw new ParseError('Number too large for this calculator', '数字太大，计算器处理不了');
    return n;
  };
  const nat = n => (n === 0 ? [] : [[[], big(n)]]);
  const ONE = nat(1);
  const W = [[ONE, 1]];
  const wpow = e => [[e, 1]];
  function cmp(a, b) {
    for (let i = 0; ; i++) {
      if (i >= a.length) return i >= b.length ? 0 : -1;
      if (i >= b.length) return 1;
      const c = cmp(a[i][0], b[i][0]);
      if (c) return c;
      if (a[i][1] !== b[i][1]) return a[i][1] < b[i][1] ? -1 : 1;
    }
  }
  const eq = (a, b) => cmp(a, b) === 0;
  const isZero = a => a.length === 0;
  const isFin = a => a.length === 0 || (a.length === 1 && a[0][0].length === 0);
  const finVal = a => (a.length ? a[0][1] : 0);
  const isLimit = a => a.length > 0 && a[a.length - 1][0].length > 0;
  const isSucc = a => a.length > 0 && a[a.length - 1][0].length === 0;
  function add(a, b) {
    if (!b.length) return a;
    const e0 = b[0][0];
    const res = [];
    let i = 0;
    while (i < a.length && cmp(a[i][0], e0) > 0) res.push(a[i++]);
    if (i < a.length && cmp(a[i][0], e0) === 0) {
      res.push([e0, big(a[i][1] + b[0][1])]);
      return res.concat(b.slice(1));
    }
    return res.concat(b);
  }
  function mul(a, b) {
    if (!a.length || !b.length) return [];
    let res = [];
    for (const [e, c] of b) {
      const piece = e.length ? [[add(a[0][0], e), c]] : [[a[0][0], big(a[0][1] * c)], ...a.slice(1)];
      res = add(res, piece);
    }
    return res;
  }
  function pow(a, b) {
    if (!b.length) return ONE;
    if (!a.length) return [];
    if (eq(a, ONE)) return ONE;
    const last = b[b.length - 1];
    const m = last[0].length ? 0 : last[1];
    const binf = m ? b.slice(0, -1) : b;
    if (isFin(a)) {
      const km = Math.pow(finVal(a), m);
      const fpart = nat(big(km));
      if (!binf.length) return fpart;
      // b_inf = ω·γ, and k^(ω·γ) = ω^γ
      const gamma = binf.map(([e, c]) => [isFin(e) ? nat(finVal(e) - 1) : e, c]);
      return mul(wpow(gamma), fpart);
    }
    if (m > 64) throw new ParseError('Exponent too large for this calculator', '指数太大，计算器处理不了');
    let fpart = ONE;
    for (let i = 0; i < m; i++) fpart = mul(fpart, a);
    if (!binf.length) return fpart;
    // for limit λ and a ≥ ω with leading exponent a₁: a^λ = ω^(a₁·λ)
    return mul(wpow(mul(a[0][0], binf)), fpart);
  }
  function pred(a) {
    const t = a[a.length - 1];
    const r = a.slice(0, -1);
    if (t[1] > 1) r.push([[], t[1] - 1]);
    return r;
  }
  // Fundamental sequence a[k] → a, for a limit ordinal a.
  function fund(a, k) {
    const [e, c] = a[a.length - 1];
    const base = a.slice(0, -1);
    if (c > 1) base.push([e, c - 1]);
    const tail = isSucc(e) ? (k === 0 ? [] : [[pred(e), k]]) : wpow(fund(e, k));
    return add(base, tail);
  }
  const SUPS = '⁰¹²³⁴⁵⁶⁷⁸⁹';
  const supDigits = n => String(n).split('').map(d => SUPS[d]).join('');
  function toStr(a) {
    if (!a.length) return '0';
    return a.map(([e, c]) => {
      if (!e.length) return String(c);
      let s = 'ω';
      if (!eq(e, ONE)) {
        if (isFin(e)) s += supDigits(finVal(e));
        else if (e.length === 1 && e[0][1] === 1) s += '^' + toStr(e);
        else s += '^(' + toStr(e) + ')';
      }
      return c > 1 ? s + '·' + c : s;
    }).join('+');
  }
  function toHTML(a) {
    if (!a.length) return '0';
    return a.map(([e, c]) => {
      if (!e.length) return String(c);
      let s = 'ω';
      if (!eq(e, ONE)) s += '<sup>' + toHTML(e) + '</sup>';
      return c > 1 ? s + '·' + c : s;
    }).join(' + ');
  }
  function parse(src) {
    let s = String(src).replace(/[⁰¹²³⁴⁵⁶⁷⁸⁹]+/g, m => '^' + [...m].map(ch => SUPS.indexOf(ch)).join(''));
    s = s.replace(/\*\*/g, '^').replace(/[ωwW]/g, 'w').replace(/[·×*⋅]/g, '*');
    const toks = [];
    for (let i = 0; i < s.length;) {
      const c = s[i];
      if (/\s/.test(c)) { i++; continue; }
      if (/[0-9]/.test(c)) {
        let j = i;
        while (j < s.length && /[0-9]/.test(s[j])) j++;
        toks.push({ t: 'n', v: +s.slice(i, j) });
        i = j;
        continue;
      }
      if ('w+*^()'.includes(c)) { toks.push({ t: c }); i++; continue; }
      throw new ParseError(`Unknown symbol “${c}”. Use ω (or w), digits, + · ^ and parentheses.`, `无法识别的符号“${c}”。请只用 ω（或 w）、数字、+ · ^ 和括号。`);
    }
    if (!toks.length) throw new ParseError('Empty input', '输入为空');
    let i = 0;
    const peek = () => toks[i];
    function E() { let a = T(); while (peek() && peek().t === '+') { i++; a = add(a, T()); } return a; }
    function T() { let a = F(); while (peek() && peek().t === '*') { i++; a = mul(a, F()); } return a; }
    function F() { const a = A(); if (peek() && peek().t === '^') { i++; return pow(a, F()); } return a; }
    function A() {
      const tk = peek();
      if (!tk) throw new ParseError('Expression ends too early', '表达式不完整，结尾缺东西');
      if (tk.t === 'n') { i++; return nat(big(tk.v)); }
      if (tk.t === 'w') { i++; return W; }
      if (tk.t === '(') {
        i++;
        const a = E();
        if (!peek() || peek().t !== ')') throw new ParseError('Missing “)”', '缺少右括号“)”');
        i++;
        return a;
      }
      throw new ParseError(`Unexpected “${tk.t === 'w' ? 'ω' : tk.t}”`, `此处不应出现“${tk.t === 'w' ? 'ω' : tk.t}”`);
    }
    const r = E();
    if (i < toks.length) throw new ParseError('Extra symbols at the end. (Write multiplication explicitly with · or *.)', '结尾有多余符号。（乘法请明确写出 · 或 *。）');
    return r;
  }
  return { nat, ONE, W, wpow, cmp, eq, isZero, isFin, finVal, isLimit, isSucc, add, mul, pow, pred, fund, toStr, toHTML, parse };
})();
// ==== ORD ENGINE END ====

Lang.init();
Progress.paint();

/* ================= shared helpers ================= */
const $ = id => document.getElementById(id);
const okBox = (box, html, kind = 'ok') => { box.className = 'msg ' + kind; box.innerHTML = html; };
const clearBox = box => { box.className = 'msg'; box.innerHTML = ''; };
const COL = { ink: '#1f2430', accent: '#3b5bdb', meta: '#ae3ec9', gold: '#f08c00', tru: '#2f9e44', fal: '#e03131', muted: '#6b7280', line: '#e3dfd3', orange: '#e8590c' };
function svgText(parent, x, y, s, attrs = {}) {
  const t = el('text', Object.assign({ x, y }, attrs), parent);
  t.textContent = s;
  return t;
}
// parenthesise a CNF ordinal when it is a sum or a scaled power
const paren = (o, h = ORD.toHTML(o)) => (o.length > 1 || (o.length === 1 && o[0][1] > 1 && o[0][0].length) ? `(${h})` : h);
const ordColor = o => (ORD.isZero(o) ? COL.gold : ORD.isLimit(o) ? COL.meta : COL.ink);
function svgX(svg, ev) {
  const r = svg.getBoundingClientRect();
  return (ev.clientX - r.left) * svg.viewBox.baseVal.width / r.width;
}
function arrowDefs(svg, id, color) {
  const defs = el('defs', {}, svg);
  const m = el('marker', { id, viewBox: '0 0 10 10', refX: 9, refY: 5, markerWidth: 7, markerHeight: 7, orient: 'auto-start-reverse' }, defs);
  el('path', { d: 'M0,0 L10,5 L0,10 z', fill: color }, m);
}
// Step-by-step reveal with "show all"; onAll/onStep are optional hooks.
function stepper(stepsId, nextId, allId, hooks = {}) {
  const steps = [...document.querySelectorAll(`#${stepsId} .step`)];
  let k = 0;
  const upd = () => { $(nextId).disabled = k >= steps.length; hooks.onStep && hooks.onStep(k); };
  $(nextId).addEventListener('click', () => { if (k < steps.length) steps[k++].classList.add('on'); upd(); });
  $(allId).addEventListener('click', () => { steps.forEach(s => s.classList.add('on')); k = steps.length; upd(); });
  return { reset() { steps.forEach(s => s.classList.remove('on')); k = 0; upd(); }, get k() { return k; } };
}
function choiceButtons(box, opts, onPick) {
  opts.forEach((o, i) => {
    const b = document.createElement('button');
    b.className = 'btn choice';
    b.innerHTML = o.html;
    b.addEventListener('click', () => {
      box.querySelectorAll('.choice').forEach(x => x.classList.remove('right', 'wrongc'));
      b.classList.add(o.ok ? 'right' : 'wrongc');
      onPick(o, i);
    });
    box.appendChild(b);
  });
}

/* ================= matchstick drawer ================= */
function termWeight(e) { if (!e.length) return 0.24; if (ORD.eq(e, ORD.ONE)) return 1.3; return 1.9; }
function ordWeight(a) { return a.reduce((s, [e, c]) => s + Math.min(c, 300) * termWeight(e), 0); }
// Draws α between screen x = X0..X1 (virtual 0..1, optionally zoomed to v0..v1).
// Each stick gets {x, ord, h}. cfg.leaf(g, x0, x1, ord, h) replaces genuine element sticks by custom drawings.
function drawOrdinal(parent, alpha, cfg) {
  const { X0, X1, base, H } = cfg;
  const v0 = cfg.v0 ?? 0, v1 = cfg.v1 ?? 1, span = v1 - v0;
  const sx = u => X0 + (u - v0) / span * (X1 - X0);
  const pxOf = w => w / span * (X1 - X0);
  const sticks = cfg.sticks || [];
  const colorOf = cfg.color || ordColor;
  const minPx = cfg.minPx || 1.6;
  const g = el('g', {}, parent);
  let count = 0;
  function stick(u, ord, h, u1) {
    const x = sx(u);
    if (x < X0 - 0.5 || x > X1 + 0.5 || count > 6000) return;
    count++;
    if (cfg.leaf && u1 !== undefined) { cfg.leaf(g, x, sx(u1), ord, h); sticks.push({ x, ord, h }); return; }
    const ln = el('line', { x1: x, x2: x, y1: base, y2: base - h, stroke: colorOf(ord), 'stroke-width': h > H * 0.75 ? 2.4 : h > H * 0.5 ? 1.8 : 1.2, 'stroke-linecap': 'round' }, g);
    if (cfg.anim) { ln.classList.add('fadein'); ln.style.animationDelay = ((x - X0) / (X1 - X0) * cfg.anim).toFixed(3) + 's'; }
    sticks.push({ x, ord, h, ln });
  }
  function block(e, off, u0, u1, h) {
    if (u1 <= v0 || u0 > v1) return;
    if (!e.length) { stick(u0, off, h, u1); return; }
    if (pxOf(u1 - u0) < minPx) { stick(u0, off, h); return; }
    const succ = ORD.isSucc(e), ep = succ ? ORD.pred(e) : null;
    const r = ORD.eq(e, ORD.ONE) ? (cfg.r1 || 0.8) : 0.64;
    let u = u0, o = off, w = (u1 - u0) * (1 - r), rk = 1;
    for (let k = 0; k < 4000; k++) {
      if (u > v1 || pxOf(w) < 0.3) break;
      const ek = succ ? ep : ORD.fund(e, k + 1);
      block(ek, o, u, u + w, h * (0.66 + 0.34 * rk));
      o = ORD.add(o, ORD.wpow(ek));
      u += w; w *= r; rk *= r;
    }
  }
  const total = ordWeight(alpha) || 1;
  let u = 0, off = [];
  for (const [e, c] of alpha) {
    const wt = termWeight(e) / total;
    const start = off;
    for (let j = 0; j < Math.min(c, 300); j++) { block(e, off, u, u + wt, H); off = ORD.add(off, ORD.wpow(e)); u += wt; }
    if (c > 300) svgText(g, sx(u) - 4, base - H - 4, '…', { 'font-size': 14, fill: COL.muted });
    off = ORD.add(start, [[e, c]]);
  }
  return { sticks, g, sx };
}
function labelSticks(parent, sticks, base, opts = {}) {
  const cand = sticks.slice().sort((a, b) => b.h - a.h || a.x - b.x).slice(0, 500);
  const placed = [];
  const fs = opts.fs || 11;
  for (const s of cand) {
    const txt = ORD.toStr(s.ord);
    const w = txt.length * fs * 0.64 + 8;
    const L = s.x - w / 2, R = s.x + w / 2;
    if (L < (opts.minX ?? 0) || R > (opts.maxX ?? 1e9)) continue;
    if (placed.some(p => R > p.L && L < p.R)) continue;
    placed.push({ L, R });
    const c = ordColor(s.ord);
    svgText(parent, s.x, base + fs + 5, txt, { 'text-anchor': 'middle', 'font-size': fs, fill: c === COL.ink ? '#555' : c, 'font-weight': c === COL.ink ? 400 : 700 });
    if (placed.length >= (opts.max || 24)) break;
  }
}
function describeOrd(o) {
  const s = `<b>${ORD.toHTML(o)}</b>`;
  if (ORD.isZero(o)) return `${s} &nbsp;<span class="k">${bil('zero = ∅, the least element', '零 = ∅，最小元')}</span>`;
  if (ORD.isSucc(o)) return `${s} &nbsp;<span class="k">${bil('successor ordinal', '后继序数')}:</span> ${ORD.toHTML(ORD.pred(o))} + 1`;
  return `${s} &nbsp;<span class="k">${bil('limit ordinal: below it there is no largest element', '极限序数：它下面没有最大元')}</span>`;
}
function OrdView(container, opts = {}) {
  const W = opts.w || 900, HH = opts.h || 150;
  container.innerHTML = '';
  const svg = el('svg', { viewBox: `0 0 ${W} ${HH}`, width: W, height: HH, class: opts.onPick ? 'pickable' : 'zoomable' }, container);
  const read = document.createElement('div');
  read.className = 'ordread';
  container.appendChild(read);
  const X0 = 24, X1 = W - 34, base = HH - 30, H = HH - 54;
  let alpha = [], v0 = 0, v1 = 1, sticks = [], hl = null, picked = null;
  const hint = opts.hint || `<span class="k">${bil('Hover a stick to name it · click to zoom in ×3', '悬停可看火柴的名字 · 点击放大 3 倍')}</span>`;
  function render(anim) {
    svg.innerHTML = '';
    sticks = [];
    el('line', { x1: X0 - 12, x2: X1 + 18, y1: base, y2: base, stroke: '#cfc9b8', 'stroke-width': 1.5 }, svg);
    drawOrdinal(svg, alpha, { X0, X1, base, H, v0, v1, sticks, anim: anim ? 1.4 : 0, color: opts.color });
    labelSticks(svg, sticks, base, { max: opts.maxLabels || 22, minX: 0, maxX: W });
    if (v1 >= 1 && ORD.isLimit(alpha)) {
      el('line', { x1: X1 + 10, x2: X1 + 10, y1: base, y2: base - H, stroke: COL.meta, 'stroke-dasharray': '3 4', opacity: 0.6 }, svg);
      svgText(svg, X1 + 10, base - H - 6, ORD.toStr(alpha).length < 12 ? ORD.toStr(alpha) : 'α', { 'text-anchor': 'end', 'font-size': 11, fill: COL.meta, opacity: 0.8 });
    }
    if (v1 - v0 < 0.999) svgText(svg, W - 6, 14, `zoom ×${Math.round(1 / (v1 - v0)).toLocaleString('en-US')}`, { 'text-anchor': 'end', 'font-size': 12, fill: COL.accent, 'font-weight': 700 });
    hl = el('line', { y1: base + 3, y2: base - H - 4, stroke: COL.accent, 'stroke-width': 7, opacity: 0, 'stroke-linecap': 'round' }, svg);
    hl.style.pointerEvents = 'none';
    read.innerHTML = picked ? describeOrd(picked) : hint;
    if (!sticks.length && alpha.length) {
      svgText(svg, W / 2, base - H / 2, 'empty gap between two consecutive sticks · 两根相邻火柴之间的空隙', { 'text-anchor': 'middle', 'font-size': 13, fill: COL.muted });
      read.innerHTML = `<span class="k">${bil('You zoomed into a gap: between β and β+1 there is nothing. Zoom out and click where sticks pile up.', '你放大到了一个空隙：β 与 β+1 之间什么都没有。缩小后，点击火柴密集的地方。')}</span>`;
    }
    opts.afterRender && opts.afterRender(api);
  }
  function nearest(ev) {
    const x = svgX(svg, ev);
    let best = null, bd = opts.onPick ? 40 : 14;
    for (const s of sticks) { const d = Math.abs(s.x - x); if (d < bd) { bd = d; best = s; } }
    return best;
  }
  svg.addEventListener('mousemove', ev => {
    const s = nearest(ev);
    if (!s || !hl) { hl && hl.setAttribute('opacity', 0); return; }
    hl.setAttribute('x1', s.x); hl.setAttribute('x2', s.x); hl.setAttribute('opacity', 0.22);
    read.innerHTML = describeOrd(s.ord);
  });
  svg.addEventListener('mouseleave', () => { hl && hl.setAttribute('opacity', 0); read.innerHTML = picked ? describeOrd(picked) : hint; });
  svg.addEventListener('click', ev => {
    if (opts.onPick) { const s = nearest(ev); if (s) { picked = s.ord; opts.onPick(s, api); } return; }
    const span = v1 - v0;
    if (span < 1e-13) return;
    const t = Math.max(0, Math.min(1, (svgX(svg, ev) - X0) / (X1 - X0))), c = v0 + t * span, ns = span / 3;
    v0 = Math.max(0, Math.min(1 - ns, c - t * ns));
    v1 = v0 + ns;
    render(false);
  });
  const api = {
    show(a, anim = true) { alpha = a; v0 = 0; v1 = 1; picked = null; render(anim); },
    zoomOut() { const c = (v0 + v1) / 2, ns = Math.min(1, (v1 - v0) * 3); v0 = Math.max(0, Math.min(1 - ns, c - ns / 2)); v1 = v0 + ns; render(false); },
    reset() { v0 = 0; v1 = 1; render(false); },
    get sticks() { return sticks; },
    svg, read, base, H,
  };
  return api;
}

// ℵ with a subscript inside SVG text
// sub may be 'ω_ω' (nested subscript); tail is appended at normal size, e.g. ' = κ ?'
function alephSVG(parent, x, y, sub, attrs = {}, tail = '') {
  const t = el('text', Object.assign({ x, y }, attrs), parent);
  t.appendChild(document.createTextNode('ℵ'));
  const [s1, s2] = sub.split('_');
  const s = el('tspan', { 'baseline-shift': 'sub', 'font-size': '72%' }, t);
  s.textContent = s1;
  if (s2) { const u = el('tspan', { 'baseline-shift': 'sub', 'font-size': '72%' }, s); u.textContent = s2; }
  if (tail) { const r = el('tspan', {}, t); r.textContent = tail; }
  return t;
}
// SVG text with simple ^x (superscript) and _x (subscript) markers, e.g. 'ω^ω', 'ω_ω+1'
function richSVG(parent, x, y, str, attrs = {}) {
  const t = el('text', Object.assign({ x, y }, attrs), parent);
  str.split(/([\^_](?:ω|α|\d+|ℵ[₀-₉ω]))/).filter(Boolean).forEach(part => {
    if (part[0] === '^' || part[0] === '_') {
      const s = el('tspan', { 'baseline-shift': part[0] === '^' ? 'super' : 'sub', 'font-size': '75%' }, t);
      s.textContent = part.slice(1);
    } else t.appendChild(document.createTextNode(part));
  });
  return t;
}
const alephH = sub => `ℵ<sub>${sub}</sub>`;
const SUBS = '₀₁₂₃₄₅₆₇₈₉';
const subN = n => String(n).split('').map(d => SUBS[d]).join('');

/* ================= §1 bijections with ω ================= */
(function bijections() {
  const svg = $('bijSvg');
  const W = ORD.W, nat = ORD.nat, add = ORD.add;
  const PR = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37];
  function fromFactor(m) {
    const cs = [];
    PR.forEach((p, i) => { let c = 0; while (m % p === 0) { m /= p; c++; } cs[i] = c; });
    const terms = [];
    for (let i = cs.length - 1; i >= 0; i--) if (cs[i]) terms.push([nat(i), cs[i]]);
    return terms;
  }
  const items = [
    { a: 'w+1', g: n => (n === 0 ? W : nat(n - 1)), en: 'ω ↦ 0, &nbsp; n ↦ n+1 (the Hilbert hotel)', zh: 'ω ↦ 0，n ↦ n+1（希尔伯特旅馆）' },
    { a: 'w+3', g: n => (n < 3 ? add(W, nat(n)) : nat(n - 3)), en: 'ω+k ↦ k for k &lt; 3, &nbsp; n ↦ n+3', zh: 'ω+k ↦ k（k &lt; 3），n ↦ n+3' },
    { a: 'w*2', g: n => (n % 2 ? add(W, nat((n - 1) / 2)) : nat(n / 2)), en: 'n ↦ 2n, &nbsp; ω+n ↦ 2n+1', zh: 'n ↦ 2n，ω+n ↦ 2n+1' },
    { a: 'w^2', g: n => { const w = Math.floor((Math.sqrt(8 * n + 1) - 1) / 2), b = n - w * (w + 1) / 2, a = w - b; return add(ORD.mul(W, nat(a)), nat(b)); },
      en: 'ω·a + b ↦ (a+b)(a+b+1)/2 + b (Cantor pairing)', zh: 'ω·a + b ↦ (a+b)(a+b+1)/2 + b（康托尔配对函数）' },
    { a: 'w^w', g: n => fromFactor(n + 1), en: 'ω<sup>k</sup>·c<sub>k</sub> + ⋯ + c₀ ↦ 2<sup>c₀</sup>·3<sup>c₁</sup>·5<sup>c₂</sup>⋯ − 1 (unique factorisation)', zh: 'ω<sup>k</sup>·c<sub>k</sub> + ⋯ + c₀ ↦ 2<sup>c₀</sup>·3<sup>c₁</sup>·5<sup>c₂</sup>⋯ − 1（算术基本定理）' },
  ];
  const N = 40, base = 112, H = 74, Y2 = 236;
  let cur = 0, n = 0, sticks = [], gl = null, dots = [], token = 0;
  const xN = k => 40 + k * 20.8;
  function setup() {
    token++;
    svg.innerHTML = '';
    n = 0;
    const it = items[cur], a = ORD.parse(it.a);
    svgText(svg, 20, 18, `α = ${ORD.toStr(a)}`, { 'font-size': 13, 'font-weight': 700, fill: COL.ink });
    el('line', { x1: 20, x2: 880, y1: base, y2: base, stroke: '#cfc9b8' }, svg);
    sticks = [];
    drawOrdinal(svg, a, { X0: 40, X1: 850, base, H, sticks });
    labelSticks(svg, sticks, base, { max: 16 });
    gl = el('g', {}, svg);
    svgText(svg, 20, Y2 + 44, 'ℕ = ω', { 'font-size': 13, 'font-weight': 700, fill: COL.ink });
    el('line', { x1: 30, x2: 880, y1: Y2, y2: Y2, stroke: '#cfc9b8' }, svg);
    dots = [];
    for (let k = 0; k < N; k++) {
      dots.push(el('circle', { cx: xN(k), cy: Y2, r: 5, fill: '#fff', stroke: COL.ink, 'stroke-width': 1.4 }, svg));
      if (k < 10 || k % 5 === 0) svgText(svg, xN(k), Y2 + 20, k, { 'text-anchor': 'middle', 'font-size': 11, fill: '#555' });
    }
    svgText(svg, 878, Y2 + 5, '…', { 'font-size': 14, fill: COL.muted, 'text-anchor': 'end' });
    okBox($('bijMsg'), bi(`Bijection: ${it.en}. Press play.`, `双射：${it.zh}。按播放键。`), 'info');
  }
  function step() {
    if (n >= N) return false;
    const it = items[cur], b = it.g(n);
    const s = sticks.find(t => ORD.eq(t.ord, b));
    const c = ORD.isLimit(b) ? COL.meta : ORD.isZero(b) ? COL.gold : COL.accent;
    dots[n].setAttribute('fill', c);
    dots[n].setAttribute('stroke', c);
    if (s) el('line', { x1: s.x, y1: base + 2, x2: xN(n), y2: Y2 - 6, stroke: c, 'stroke-width': ORD.isLimit(b) ? 2 : 1, opacity: ORD.isLimit(b) ? 0.9 : 0.5, class: 'fadein' }, gl);
    const msg = `<span class="m">${ORD.toHTML(b)} ↦ ${n}</span>`;
    n++;
    if (n === N) okBox($('bijMsg'), msg + '<br>' + bi(`…and so on forever. Every element of α gets exactly one natural number and every number is used, so |α| = ℵ₀. α is in bijection with the <i>smaller</i> ordinal ω, so α is <b>not</b> a cardinal. (Rule: ${it.en}.)`, `……如此永远继续。α 的每个元素恰好分到一个自然数，每个自然数也都用上了，所以 |α| = ℵ₀。α 与<i>更小的</i>序数 ω 等势，因此 α <b>不是</b>基数。（规则：${it.zh}。）`), 'ok');
    else okBox($('bijMsg'), msg + ' &nbsp; ' + bi(`(${it.en})`, `（${it.zh}）`), 'info');
    return true;
  }
  items.forEach((it, i) => {
    const b = document.createElement('button');
    b.className = 'btn small' + (i === cur ? ' sel' : '');
    b.innerHTML = `<span class="m">${ORD.toHTML(ORD.parse(it.a))}</span>`;
    b.addEventListener('click', () => { cur = i; $('bijPick').querySelectorAll('button').forEach(x => x.classList.toggle('sel', x === b)); setup(); });
    $('bijPick').appendChild(b);
  });
  $('bijStep').addEventListener('click', () => { token++; step(); });
  $('bijReset').addEventListener('click', setup);
  $('bijPlay').addEventListener('click', async () => { const my = ++token; while (my === token && step()) await sleep(160); });
  setup();
})();

/* ================= §2 Cantor–Schröder–Bernstein ================= */
(function csb() {
  const svg = $('csbSvg');
  const XA = 170, XB = 730, NROW = 14;
  const exs = [
    { en: 'A = B = ℕ, f(n) = n+1, g(n) = n+1', zh: 'A = B = ℕ，f(n) = n+1，g(n) = n+1', els: Array.from({ length: NROW }, (_, i) => i),
      f: n => n + 1, g: n => n + 1, finv: m => (m >= 1 ? m - 1 : null), ginv: m => (m >= 1 ? m - 1 : null) },
    { en: 'A = B = ℕ, f(n) = 2n, g(n) = 2n', zh: 'A = B = ℕ，f(n) = 2n，g(n) = 2n', els: Array.from({ length: NROW }, (_, i) => i),
      f: n => 2 * n, g: n => 2 * n, finv: m => (m % 2 ? null : m / 2), ginv: m => (m % 2 ? null : m / 2) },
    { en: 'A = B = ℤ, f(z) = z+1, g(z) = z', zh: 'A = B = ℤ，f(z) = z+1，g(z) = z', els: Array.from({ length: NROW }, (_, i) => i - 6),
      f: z => z + 1, g: z => z, finv: m => m - 1, ginv: m => m, Z: true },
  ];
  const PAL = ['#3b5bdb', '#e8590c', '#2f9e44', '#ae3ec9', '#0c8599', '#c2255c', '#f08c00', '#5c940d', '#1864ab', '#862e9c'];
  let cur = 0, stage = 2;
  function trace(ex, side, v) {
    let s = side, x = v;
    const seen = [];
    for (let k = 0; k < 80; k++) {
      const key = s + x;
      if (seen.includes(key)) return { type: 'cycle', id: 'C' + seen.slice().sort()[0] };
      seen.push(key);
      if (s === 'A') { const p = ex.ginv(x); if (p === null) return { type: 'A', id: 'A' + x }; s = 'B'; x = p; }
      else { const p = ex.finv(x); if (p === null) return { type: 'B', id: 'B' + x }; s = 'A'; x = p; }
    }
    return { type: 'Z', id: 'Z' };
  }
  const TYPE = { A: ['A-chain (starts in A)', 'A 链（起点在 A）'], B: ['B-chain (starts in B)', 'B 链（起点在 B）'], cycle: ['finite cycle', '有限圈'], Z: ['ℤ-chain (no start)', 'ℤ 链（没有起点）'] };
  function draw() {
    const ex = exs[cur];
    svg.innerHTML = '';
    arrowDefs(svg, 'csbF', COL.accent);
    arrowDefs(svg, 'csbG', COL.orange);
    arrowDefs(svg, 'csbH', COL.tru);
    const idx = new Map(ex.els.map((v, i) => [v, i]));
    const y = i => 34 + i * 27.5;
    svgText(svg, XA, 18, 'A', { 'text-anchor': 'middle', 'font-size': 15, 'font-weight': 800 });
    svgText(svg, XB, 18, 'B', { 'text-anchor': 'middle', 'font-size': 15, 'font-weight': 800 });
    const colorOf = new Map();
    const chainOf = (side, v) => { const t = trace(ex, side, v); if (!colorOf.has(t.id)) colorOf.set(t.id, PAL[colorOf.size % PAL.length]); return { ...t, col: colorOf.get(t.id) }; };
    const g1 = el('g', {}, svg);
    const curve = (x1, y1, x2, y2, bend) => `M${x1},${y1} C${(x1 + x2) / 2},${y1 + bend} ${(x1 + x2) / 2},${y2 + bend} ${x2},${y2}`;
    ex.els.forEach((v, i) => {
      if (stage >= 1) {
        const t = ex.f(v), j = idx.get(t), ch = chainOf('A', v);
        const col = stage >= 3 ? ch.col : COL.accent, op = stage >= 4 ? 0.18 : 0.75;
        if (j !== undefined) el('path', { d: curve(XA + 12, y(i), XB - 14, y(j), -10), fill: 'none', stroke: col, 'stroke-width': 1.6, opacity: op, 'marker-end': stage >= 3 ? '' : 'url(#csbF)' }, g1);
        else el('path', { d: `M${XA + 12},${y(i)} L${XA + 120},${y(i) + 30}`, fill: 'none', stroke: col, 'stroke-width': 1.4, opacity: op * 0.7, 'stroke-dasharray': '4 4' }, g1);
      }
      if (stage >= 2) {
        const t = ex.g(v), j = idx.get(t), ch = chainOf('B', v);
        const col = stage >= 3 ? ch.col : COL.orange, op = stage >= 4 ? 0.18 : 0.75;
        if (j !== undefined) el('path', { d: curve(XB - 12, y(i), XA + 14, y(j), 10), fill: 'none', stroke: col, 'stroke-width': 1.6, opacity: op, 'stroke-dasharray': stage >= 3 ? '6 3' : '', 'marker-end': stage >= 3 ? '' : 'url(#csbG)' }, g1);
        else el('path', { d: `M${XB - 12},${y(i)} L${XB - 120},${y(i) + 30}`, fill: 'none', stroke: col, 'stroke-width': 1.4, opacity: op * 0.7, 'stroke-dasharray': '4 4' }, g1);
      }
    });
    const counts = { A: new Set(), B: new Set(), cycle: new Set(), Z: new Set() };
    ex.els.forEach((v, i) => {
      ['A', 'B'].forEach(side => {
        const x = side === 'A' ? XA : XB;
        const ch = chainOf(side, v);
        counts[ch.type].add(ch.id);
        const isStart = ch.id === side + v && (ch.type === 'A' || ch.type === 'B');
        const fill = stage >= 3 ? ch.col : '#fff';
        el('circle', { cx: x, cy: y(i), r: isStart && stage >= 3 ? 9 : 7, fill, stroke: stage >= 3 ? ch.col : COL.ink, 'stroke-width': isStart && stage >= 3 ? 3 : 1.5 }, svg);
        svgText(svg, side === 'A' ? x - 16 : x + 16, y(i) + 4, (side === 'A' ? 'a' : 'b') + (v < 0 ? '₋' + subN(-v) : subN(v)), { 'text-anchor': side === 'A' ? 'end' : 'start', 'font-size': 13, fill: '#444' });
        if (isStart && stage >= 3) svgText(svg, side === 'A' ? x - 48 : x + 48, y(i) + 4, 'start', { 'text-anchor': side === 'A' ? 'end' : 'start', 'font-size': 10, fill: ch.col, 'font-weight': 700 });
      });
    });
    if (stage >= 4) {
      ex.els.forEach((v, i) => {
        const ch = chainOf('A', v);
        const hv = ch.type === 'B' ? ex.ginv(v) : ex.f(v);
        const j = idx.get(hv);
        if (j === undefined) return;
        el('line', { x1: XA + 12, y1: y(i), x2: XB - 14, y2: y(j), stroke: COL.tru, 'stroke-width': 3, 'marker-end': 'url(#csbH)', class: 'fadein' }, svg);
      });
    }
    svgText(svg, 450, 18, ['', 'f: A → B', 'f (blue) and g (orange)', 'chains, coloured · 链（按颜色区分）', 'h: A → B (green) · 双射 h（绿色）'][stage] || '', { 'text-anchor': 'middle', 'font-size': 13, fill: COL.muted, 'font-weight': 700 });
    // message
    const fmt = (ids) => ids.size;
    const msgs = [
      bi(`${ex.en}. Only the first ${NROW} elements of each side are drawn. Press “Next step”.`, `${ex.zh}。两边各只画出前 ${NROW} 个元素。按“下一步”。`),
      bi('f: A → B is injective (no two blue arrows hit the same point) but not onto: some points of B receive no blue arrow.', 'f: A → B 是单射（没有两条蓝箭头指向同一点），但不是满射：B 中有些点没有蓝箭头指入。'),
      bi('g: B → A is injective too. Now follow arrows <b>backwards</b> from any point.', 'g: B → A 也是单射。现在从任意一点出发，沿箭头<b>往回</b>追。'),
      bi(`Chains in view: ${fmt(counts.A)} A-chain(s), ${fmt(counts.B)} B-chain(s), ${fmt(counts.cycle)} cycle(s), ${fmt(counts.Z)} ℤ-chain(s). Big rings mark where an A- or B-chain starts.`, `图中的链：A 链 ${fmt(counts.A)} 条，B 链 ${fmt(counts.B)} 条，圈 ${fmt(counts.cycle)} 个，ℤ 链 ${fmt(counts.Z)} 条。粗圈标出 A 链或 B 链的起点。`),
      bi('h = f on A-chains, cycles and ℤ-chains, and h = g⁻¹ on B-chains. Every b in view is hit by exactly one green arrow (arrows leaving the window are not drawn).', '在 A 链、圈和 ℤ 链上取 h = f，在 B 链上取 h = g⁻¹。图中每个 b 恰好被一条绿箭头指中（指出窗口的箭头没有画）。'),
    ];
    okBox($('csbMsg'), msgs[stage], 'info');
    $('csbNext').disabled = stage >= 4;
  }
  exs.forEach((ex, i) => {
    const b = document.createElement('button');
    b.className = 'btn small' + (i === cur ? ' sel' : '');
    b.innerHTML = `<span class="m">${ex.en}</span>`;
    b.addEventListener('click', () => { cur = i; stage = 2; $('csbPick').querySelectorAll('button').forEach(x => x.classList.toggle('sel', x === b)); draw(); });
    $('csbPick').appendChild(b);
  });
  $('csbNext').addEventListener('click', () => { if (stage < 4) stage++; draw(); });
  $('csbAll').addEventListener('click', () => { stage = 4; draw(); });
  $('csbReset').addEventListener('click', () => { stage = 0; draw(); });
  draw();
  stepper('csbProof', 'csbPNext', 'csbPAll');
})();

/* ================= §3 ℵ ruler ================= */
(function alephRuler() {
  const svg = $('alephSvg');
  const base = 120;
  const posts = [[130, '0', 'ω'], [440, '1', 'ω₁'], [650, '2', 'ω₂'], [745, '3', 'ω₃'], [815, 'ω', 'ω_ω']];
  const items = [
    { lab: '7', x: 70, card: '7', isCard: true, en: 'A natural number is a finite cardinal.', zh: '自然数都是有限基数。' },
    { lab: 'ω', x: 130, card: alephH('0'), isCard: true, en: 'ω = ℵ₀, the first infinite cardinal.', zh: 'ω = ℵ₀，第一个无穷基数。' },
    { lab: 'ω+1', x: 160, card: alephH('0'), isCard: false, en: 'Countable: ω ↦ 0, n ↦ n+1 (§1).', zh: '可数：ω ↦ 0，n ↦ n+1（§1）。' },
    { lab: 'ω·2', x: 210, card: alephH('0'), isCard: false, en: 'Countable: evens and odds (§1).', zh: '可数：偶数和奇数（§1）。' },
    { lab: 'ω²', x: 265, card: alephH('0'), isCard: false, en: 'Countable: Cantor pairing (§1).', zh: '可数：康托尔配对（§1）。' },
    { lab: 'ω^ω', html: 'ω<sup>ω</sup>', x: 320, card: alephH('0'), isCard: false, en: 'Countable: prime factorisation (§1).', zh: '可数：素因数分解（§1）。' },
    { lab: 'ε₀', x: 375, card: alephH('0'), isCard: false, en: 'Countable: every ordinal below ε₀ is a finite expression (Cantor normal form), and there are only countably many finite expressions.', zh: '可数：ε₀ 以下每个序数都是一个有限表达式（康托尔范式），而有限表达式只有可数多个。' },
    { lab: 'ω₁', x: 440, card: alephH('1'), isCard: true, en: 'ω₁ = ℵ₁ = the set of all countable ordinals = h(ω). It is uncountable, and every smaller ordinal is countable.', zh: 'ω₁ = ℵ₁ = 全体可数序数之集 = h(ω)。它不可数，而比它小的序数都可数。' },
    { lab: 'ω₁+1', x: 470, card: alephH('1'), isCard: false, en: 'Same trick as ω+1: the top element goes to 0, and 0, 1, 2, … shift up; limits stay put.', zh: '与 ω+1 同样的技巧：顶端元素送到 0，0, 1, 2, … 依次后移，极限点不动。' },
    { lab: 'ω₁·2', x: 525, card: alephH('1'), isCard: false, en: '|ω₁·2| = ℵ₁ + ℵ₁ = ℵ₁ (§4).', zh: '|ω₁·2| = ℵ₁ + ℵ₁ = ℵ₁（§4）。' },
    { lab: 'ω₁²', x: 580, card: alephH('1'), isCard: false, en: 'The ordinal ω₁·ω₁ has size ℵ₁·ℵ₁ = ℵ₁ (§4). Ordinal and cardinal arithmetic differ!', zh: '序数 ω₁·ω₁ 的大小是 ℵ₁·ℵ₁ = ℵ₁（§4）。序数运算和基数运算不是一回事！' },
    { lab: 'ω₂', x: 650, card: alephH('2'), isCard: true, en: 'ω₂ = ℵ₂: the ordinals of size ≤ ℵ₁.', zh: 'ω₂ = ℵ₂：全体大小 ≤ ℵ₁ 的序数。' },
    { lab: 'ω₂+ω₁', x: 695, card: alephH('2'), isCard: false, en: 'ℵ₂ + ℵ₁ = ℵ₂.', zh: 'ℵ₂ + ℵ₁ = ℵ₂。' },
    { lab: 'ω_ω', html: 'ω<sub>ω</sub>', x: 815, card: alephH('ω'), isCard: true, en: 'ℵ_ω = sup{ℵ₀, ℵ₁, ℵ₂, …}, the first limit cardinal after ℵ₀. A limit of cardinals is a cardinal.', zh: 'ℵ_ω = sup{ℵ₀, ℵ₁, ℵ₂, …}，ℵ₀ 之后第一个极限基数。基数的极限仍是基数。' },
    { lab: 'ω_ω+1', html: 'ω<sub>ω</sub>+1', x: 848, card: alephH('ω'), isCard: false, en: 'Successor ordinals above ω are never cardinals.', zh: 'ω 以上的后继序数都不是基数。' },
  ];
  let sel = null;
  function draw() {
    svg.innerHTML = '';
    el('line', { x1: 20, x2: 885, y1: base, y2: base, stroke: '#cfc9b8', 'stroke-width': 2 }, svg);
    if (sel) {
      const L = [...posts].reverse().find(p => p[0] <= sel.x);
      const R = posts.find(p => p[0] > sel.x);
      if (L) {
        el('rect', { x: L[0], y: base - 96, width: (R ? R[0] : 885) - L[0], height: 96, fill: COL.gold, opacity: 0.12 }, svg);
      } else el('rect', { x: 20, y: base - 96, width: 110, height: 96, fill: COL.gold, opacity: 0.08 }, svg);
    }
    for (let k = 0; k < 8; k++) { const x = 30 + 90 * (1 - Math.pow(0.7, k)); el('line', { x1: x, x2: x, y1: base, y2: base - 22, stroke: '#888', 'stroke-width': 1.2 }, svg); }
    posts.forEach(([x, sub, nm]) => {
      el('line', { x1: x, x2: x, y1: base, y2: base - 90, stroke: COL.gold, 'stroke-width': 4 }, svg);
      alephSVG(svg, x, base - 96, sub, { 'text-anchor': 'middle', 'font-size': 15, fill: COL.gold, 'font-weight': 800 });
    });
    items.forEach((it, i) => {
      if (posts.some(p => p[0] === it.x)) return;
      el('line', { x1: it.x, x2: it.x, y1: base, y2: base - 34, stroke: it === sel ? COL.fal : COL.meta, 'stroke-width': 2 }, svg);
    });
    items.forEach((it, i) => richSVG(svg, it.x, base + 18 + (i % 2) * 15, it.lab, { 'text-anchor': 'middle', 'font-size': 11, fill: it === sel ? COL.fal : '#555', 'font-weight': it === sel ? 800 : 400 }));
    [400, 615, 722, 780, 878].forEach(x => svgText(svg, x, base - 8, '⋯', { 'text-anchor': 'middle', 'font-size': 13, fill: COL.muted }));
    svgText(svg, 285, base - 60, 'countable · 可数', { 'text-anchor': 'middle', 'font-size': 12, fill: COL.muted });
    svgText(svg, 545, base - 60, 'size ℵ₁ · 大小为 ℵ₁', { 'text-anchor': 'middle', 'font-size': 12, fill: COL.muted });
    if (sel) el('path', { d: `M${sel.x - 8},${base - 44} L${sel.x + 8},${base - 44} L${sel.x},${base - 36} z`, fill: COL.fal }, svg);
  }
  items.forEach(it => {
    const c = document.createElement('div');
    c.className = 'chip m';
    c.innerHTML = it.html || it.lab;
    c.addEventListener('click', () => {
      sel = it;
      $('alephChips').querySelectorAll('.chip').forEach(x => x.classList.toggle('ok', x === c));
      draw();
      const nm = it.html || it.lab;
      okBox($('alephMsg'), `<span class="m" style="font-size:17px">|${nm}| = ${it.card}</span> &nbsp; ${it.isCard ? `<b style="color:var(--true)">${bil('a cardinal', '是基数')}</b>` : `<b style="color:var(--false)">${bil('not a cardinal', '不是基数')}</b>`}<br>${bi(it.en, it.zh)}`, 'info');
    });
    $('alephChips').appendChild(c);
  });
  draw();
  okBox($('alephMsg'), bi('Click an ordinal above.', '点击上面的一个序数。'), 'info');
})();

/* ================= §4 pairing order ================= */
const godelPos = (a, b) => { const m = Math.max(a, b); return a < m ? m * m + a : m * m + m + b; };
function drawPairGrid(svg, N, cell, x0, yb, opts = {}) {
  svg.innerHTML = '';
  const cells = [];
  for (let a = 0; a < N; a++) for (let b = 0; b < N; b++) {
    const x = x0 + a * cell, y = yb - (b + 1) * cell, m = Math.max(a, b);
    const r = el('rect', { x: x + 1.5, y: y + 1.5, width: cell - 3, height: cell - 3, rx: 6, fill: m % 2 ? '#fff4e6' : '#eef2ff', stroke: '#d8d3c4' }, svg);
    const t = svgText(svg, x + cell / 2, y + cell / 2 + 5, '', { 'text-anchor': 'middle', 'font-size': cell > 40 ? 15 : 13, 'font-weight': 700, fill: COL.ink });
    cells.push({ a, b, x, y, r, t, pos: godelPos(a, b) });
  }
  for (let k = 0; k < N; k++) {
    svgText(svg, x0 + k * cell + cell / 2, yb + 16, k, { 'text-anchor': 'middle', 'font-size': 12, fill: '#555' });
    svgText(svg, x0 - 10, yb - k * cell - cell / 2 + 4, k, { 'text-anchor': 'end', 'font-size': 12, fill: '#555' });
  }
  svgText(svg, x0 + N * cell / 2, yb + 32, 'α →', { 'text-anchor': 'middle', 'font-size': 12, fill: COL.muted });
  svgText(svg, x0 - 26, yb - N * cell / 2, 'β ↑', { 'text-anchor': 'middle', 'font-size': 12, fill: COL.muted });
  cells.sort((p, q) => p.pos - q.pos);
  return cells;
}
(function pairing() {
  const svg = $('pairSvg');
  const N = 8, cell = 44, x0 = 50, yb = 380;
  let cells = [], token = 0, path = null;
  function setup() {
    token++;
    cells = drawPairGrid(svg, N, cell, x0, yb);
    path = el('g', {}, svg);
    path.style.pointerEvents = 'none';
    cells.forEach(c => {
      c.r.style.cursor = 'pointer';
      c.r.addEventListener('click', () => pick(c));
      c.t.style.pointerEvents = 'none';
    });
    okBox($('pairMsg'), bi('Press play, or click any cell.', '按播放，或点击任意格子。'), 'info');
  }
  // the walk through the order: steps to a neighbouring cell solid, jumps between rows dashed
  function setPath(list) {
    path.innerHTML = '';
    for (let i = 1; i < list.length; i++) {
      const p = list[i - 1], q = list[i];
      const adj = Math.abs(p.a - q.a) + Math.abs(p.b - q.b) === 1;
      el('line', { x1: p.x + cell / 2, y1: p.y + cell / 2, x2: q.x + cell / 2, y2: q.y + cell / 2, stroke: COL.meta, 'stroke-width': adj ? 2.2 : 1.2, opacity: adj ? 0.7 : 0.35, 'stroke-dasharray': adj ? '' : '4 4' }, path);
    }
  }
  function pick(c) {
    token++;
    const m = Math.max(c.a, c.b);
    cells.forEach(d => {
      d.t.textContent = d.pos;
      d.r.setAttribute('fill', d === c ? COL.fal : d.pos < c.pos ? '#bac8ff' : Math.max(d.a, d.b) % 2 ? '#fff4e6' : '#eef2ff');
      d.t.setAttribute('fill', d === c ? '#fff' : COL.ink);
    });
    svg.querySelectorAll('.sq').forEach(e => e.remove());
    el('rect', { class: 'sq', x: x0, y: yb - (m + 1) * cell, width: (m + 1) * cell, height: (m + 1) * cell, fill: 'none', stroke: COL.meta, 'stroke-width': 3, 'stroke-dasharray': '7 4' }, svg).style.pointerEvents = 'none';
    setPath(cells.filter(d => d.pos <= c.pos));
    const how = c.a < m ? `m² + α = ${m}² + ${c.a}` : `m² + m + β = ${m}² + ${m} + ${c.b}`;
    okBox($('pairMsg'), `<span class="m">(${c.a}, ${c.b}) ${bil('is at position', '位于第')} <b>${c.pos}</b>${bil('', ' 位')} = ${how}</span><br>` +
      bi(`m = max = ${m}. The ${c.pos} cells before it (blue) all lie in the ${m + 1} × ${m + 1} square (purple), which has only ${(m + 1) ** 2} cells. Finite initial segments everywhere: order type ω.`,
        `m = max = ${m}。排在它前面的 ${c.pos} 个格子（蓝色）都落在 ${m + 1} × ${m + 1} 的方块（紫框）内，这个方块只有 ${(m + 1) ** 2} 个格子。处处是有限前段，所以序型是 ω。`), 'info');
  }
  $('pairPlay').addEventListener('click', async () => {
    setup();
    const my = token;
    const pts = [];
    for (const c of cells) {
      if (my !== token) return;
      c.t.textContent = c.pos;
      c.t.classList.add('pop');
      c.r.setAttribute('fill', Math.max(c.a, c.b) % 2 ? '#ffd8a8' : '#bac8ff');
      pts.push(c);
      setPath(pts);
      await sleep(110);
    }
    okBox($('pairMsg'), bi(`The first ${N * N} = ${N}² positions fill exactly the ${N} × ${N} square, shell by shell: shell m has 2m + 1 cells and (m+1)² = m² + (2m+1).`, `前 ${N * N} = ${N}² 个位置恰好一层层填满 ${N} × ${N} 方块：第 m 层有 2m + 1 格，且 (m+1)² = m² + (2m+1)。`), 'info');
  });
  $('pairReset').addEventListener('click', setup);
  setup();
  stepper('kkSteps', 'kkNext', 'kkAll');
})();

/* ================= §4 cardinal calculator ================= */
const CARD = (() => {
  // {f: n} finite, or {a: k} = ℵ_k with k ∈ 0,1,2,'ω'
  const rank = c => (c.f !== undefined ? -1 : c.a === 'ω' ? 1000 : c.a);
  const name = c => (c.f !== undefined ? String(c.f) : alephH(c.a === 'ω' ? 'ω' : c.a));
  const cmp = (x, y) => { if (x.f !== undefined && y.f !== undefined) return x.f - y.f; return rank(x) - rank(y); };
  const max = (x, y) => (cmp(x, y) >= 0 ? x : y);
  const two = c => `2<sup>${name(c)}</sup>`;
  function op(o, k, l) {
    const fin = c => c.f !== undefined;
    if (o === '+') {
      if (fin(k) && fin(l)) return { v: String(k.f + l.f), en: 'Finite cardinals add as natural numbers.', zh: '有限基数就按自然数相加。' };
      return { v: name(max(k, l)), en: 'κ + λ = max(κ, λ) when one of them is infinite (§4).', zh: '只要有一个无穷，κ + λ = max(κ, λ)（§4）。' };
    }
    if (o === '·') {
      if ((fin(k) && k.f === 0) || (fin(l) && l.f === 0)) return { v: '0', en: 'Anything times 0 is 0 (κ × ∅ = ∅).', zh: '任何基数乘 0 都是 0（κ × ∅ = ∅）。' };
      if (fin(k) && fin(l)) return { v: String(k.f * l.f), en: 'Finite cardinals multiply as natural numbers.', zh: '有限基数就按自然数相乘。' };
      return { v: name(max(k, l)), en: 'κ · λ = max(κ, λ) when both are nonzero and one is infinite (Hessenberg, §4).', zh: '两者都非零且有一个无穷时，κ · λ = max(κ, λ)（黑森贝格，§4）。' };
    }
    if (fin(l) && l.f === 0) return { v: '1', en: 'κ⁰ = 1: there is exactly one function ∅ → κ.', zh: 'κ⁰ = 1：从 ∅ 到 κ 的函数恰有一个。' };
    if (fin(k) && k.f === 0) return { v: '0', en: '0^λ = 0 for λ ≥ 1: there is no function from a nonempty set into ∅.', zh: 'λ ≥ 1 时 0^λ = 0：非空集到 ∅ 没有函数。' };
    if (fin(k) && k.f === 1) return { v: '1', en: '1^λ = 1.', zh: '1^λ = 1。' };
    if (fin(k) && fin(l)) return { v: String(k.f ** l.f), en: 'Finite powers.', zh: '有限的乘方。' };
    if (fin(l)) return { v: name(k), en: 'κⁿ = κ · κ ⋯ κ = κ for infinite κ and finite n ≥ 1.', zh: '对无穷 κ 与有限 n ≥ 1，κⁿ = κ · κ ⋯ κ = κ。' };
    if (cmp(k, l) <= 0) return { v: two(l), en: `Squeeze: 2<sup>λ</sup> ≤ κ<sup>λ</sup> ≤ (2<sup>κ</sup>)<sup>λ</sup> = 2<sup>κ·λ</sup> = 2<sup>λ</sup> when 2 ≤ κ ≤ λ. The value of 2<sup>λ</sup> itself is not decided by ZFC (§6).`, zh: `夹逼：当 2 ≤ κ ≤ λ 时，2<sup>λ</sup> ≤ κ<sup>λ</sup> ≤ (2<sup>κ</sup>)<sup>λ</sup> = 2<sup>κ·λ</sup> = 2<sup>λ</sup>。而 2<sup>λ</sup> 本身的值 ZFC 判定不了（§6）。` };
    // κ > λ, both infinite
    if (k.a === 'ω') return { v: `&gt; ${name(k)}`, en: `ZFC: κ<sup>λ</sup> &gt; ℵ<sub>ω</sub> by König (cf ℵ<sub>ω</sub> = ω ≤ λ, §8) and ≥ ${two(l)}; the exact value is independent. Under GCH it equals ℵ<sub>ω+1</sub>.`, zh: `ZFC：由柯尼希定理，κ<sup>λ</sup> &gt; ℵ<sub>ω</sub>（cf ℵ<sub>ω</sub> = ω ≤ λ，§8），且 ≥ ${two(l)}；确切值独立于 ZFC。在 GCH 下它等于 ℵ<sub>ω+1</sub>。` };
    if (k.a === l.a + 1) return { v: two(l), en: `Hausdorff: ℵ<sub>n+1</sub><sup>λ</sup> = ℵ<sub>n+1</sub> · ℵ<sub>n</sub><sup>λ</sup>. Here that is ${name(k)} · ${two(l)} = ${two(l)}, because ${two(l)} ≥ ${name(k)}.`, zh: `豪斯多夫公式：ℵ<sub>n+1</sub><sup>λ</sup> = ℵ<sub>n+1</sub> · ℵ<sub>n</sub><sup>λ</sup>。这里等于 ${name(k)} · ${two(l)} = ${two(l)}，因为 ${two(l)} ≥ ${name(k)}。` };
    return { v: `${name(k)} · ${two(l)}`, en: `Hausdorff's formula, applied repeatedly: = max(${name(k)}, ${two(l)}). Which one is bigger is independent of ZFC; under GCH the value is ${name(k)}.`, zh: `反复用豪斯多夫公式：= max(${name(k)}, ${two(l)})。哪个更大独立于 ZFC；在 GCH 下其值为 ${name(k)}。` };
  }
  return { op, name };
})();
(function calc() {
  const vals = [{ f: 0 }, { f: 1 }, { f: 2 }, { f: 5 }, { a: 0 }, { a: 1 }, { a: 2 }, { a: 'ω' }];
  let K = vals[4], L = vals[5], O = '·';
  function btns(box, list, get, set, lab) {
    $(box).innerHTML = '';
    list.forEach(v => {
      const b = document.createElement('button');
      b.className = 'btn small' + (v === get() ? ' sel' : '');
      b.innerHTML = `<span class="m">${lab(v)}</span>`;
      b.addEventListener('click', () => { set(v); render(); });
      $(box).appendChild(b);
    });
  }
  function render() {
    btns('ccK', vals, () => K, v => (K = v), CARD.name);
    btns('ccOp', ['+', '·', '^'], () => O, v => (O = v), x => x);
    btns('ccL', vals, () => L, v => (L = v), CARD.name);
    const r = CARD.op(O, K, L);
    const lhs = O === '^' ? `${CARD.name(K)}<sup>${CARD.name(L)}</sup>` : `${CARD.name(K)} ${O} ${CARD.name(L)}`;
    $('ccRes').innerHTML = `${lhs} = <b style="color:var(--accent)">${r.v}</b>`;
    $('ccWhy').innerHTML = bi(r.en, r.zh);
  }
  render();
})();

/* ================= §5 Cantor diagonal on a finite set ================= */
(function cantor() {
  const N = 5;
  let M = [[1, 0, 1, 0, 0], [1, 1, 0, 0, 1], [0, 0, 0, 1, 0], [0, 1, 1, 1, 0], [1, 0, 0, 0, 0]];
  const setStr = row => '{' + row.map((v, i) => (v ? i : null)).filter(v => v !== null).join(', ') + '}';
  function render() {
    const D = M.map((row, i) => 1 - row[i]);
    let h = '<table class="cm"><tr><th></th>';
    for (let j = 0; j < N; j++) h += `<th>${j}</th>`;
    h += '<th></th><th></th></tr>';
    M.forEach((row, i) => {
      h += `<tr><td class="lab">f(${i}) =</td>`;
      row.forEach((v, j) => (h += `<td class="c${v ? ' in' : ''}${i === j ? ' dg' : ''}" data-i="${i}" data-j="${j}">${v ? '∈' : ''}</td>`));
      h += `<td class="note2">≠ D @ ${i}</td><td><button class="btn small" data-copy="${i}" title="copy D into row ${i} · 把 D 抄到第 ${i} 行"><span class="m">D → f(${i})</span></button></td></tr>`;
    });
    h += '<tr><td class="lab"><b style="color:var(--meta)">D =</b></td>';
    D.forEach(v => (h += `<td class="D${v ? ' in' : ''}">${v ? '∈' : ''}</td>`));
    h += '<td></td><td></td></tr></table>';
    $('cantorTable').innerHTML = h;
    $('cantorTable').querySelectorAll('td.c').forEach(td => td.addEventListener('click', () => { const i = +td.dataset.i, j = +td.dataset.j; M[i][j] = 1 - M[i][j]; render(); }));
    $('cantorTable').querySelectorAll('[data-copy]').forEach(b => b.addEventListener('click', () => {
      const i = +b.dataset.copy;
      M[i] = D.slice();
      render();
      okBox($('cantorMsg'), bi(`Row ${i} is now the old D. But that changed the diagonal cell (${i}, ${i}), so the <i>new</i> D differs from row ${i} exactly there. You can never catch D.`, `第 ${i} 行现在等于旧的 D。可这一抄改变了对角格 (${i}, ${i})，于是<i>新的</i> D 恰好在这一格与第 ${i} 行不同。D 永远抓不住。`), 'warn');
    }));
    okBox($('cantorMsg'), bi(`D = ${setStr(D)}. For every x, D and f(x) disagree about x: x ∈ D ⇔ x ∉ f(x). So D is not in the range of f.`, `D = ${setStr(D)}。对每个 x，D 与 f(x) 在“x 是否属于它”这件事上意见相反：x ∈ D ⇔ x ∉ f(x)。所以 D 不在 f 的值域中。`), 'info');
  }
  $('cantorRand').addEventListener('click', () => { M = M.map(r => r.map(() => (Math.random() < 0.5 ? 1 : 0))); render(); });
  render();
})();

/* ================= §6 possible values of 2^ℵ₀ ================= */
(function continuum() {
  const svg = $('contSvg');
  const cands = [
    { sub: '0', ok: false, en: 'Impossible: Cantor, 2<sup>ℵ₀</sup> &gt; ℵ₀.', zh: '不可能：康托尔定理，2<sup>ℵ₀</sup> &gt; ℵ₀。' },
    { sub: '1', ok: true, en: 'Consistent: this is CH. It holds in Gödel\'s constructible universe L.', zh: '相容：这就是 CH，它在哥德尔可构成宇宙 L 中成立。' },
    { sub: '2', ok: true, en: 'Consistent: Cohen\'s model (add ℵ₂ Cohen reals by forcing).', zh: '相容：科恩的模型（用力迫法添加 ℵ₂ 个科恩实数）。' },
    { sub: '17', ok: true, en: 'Consistent: every ℵₙ with n ≥ 1 is possible; ℵₙ is regular, so cf(ℵₙ) = ℵₙ &gt; ℵ₀.', zh: '相容：每个 ℵₙ（n ≥ 1）都可能；ℵₙ 正则，cf(ℵₙ) = ℵₙ &gt; ℵ₀。' },
    { sub: 'ω', ok: false, en: 'Impossible: cf(ℵ<sub>ω</sub>) = ω, but König\'s theorem forces cf(2<sup>ℵ₀</sup>) &gt; ℵ₀.', zh: '不可能：cf(ℵ<sub>ω</sub>) = ω，而柯尼希定理要求 cf(2<sup>ℵ₀</sup>) &gt; ℵ₀。' },
    { sub: 'ω+1', ok: true, en: 'Consistent: ℵ<sub>ω+1</sub> is a successor cardinal, hence regular.', zh: '相容：ℵ<sub>ω+1</sub> 是后继基数，因而正则。' },
    { sub: 'ω·2', ok: false, en: 'Impossible: cf(ℵ<sub>ω·2</sub>) = cf(ω·2) = ω.', zh: '不可能：cf(ℵ<sub>ω·2</sub>) = cf(ω·2) = ω。' },
    { sub: 'ω₁', ok: true, en: 'Consistent, although ℵ<sub>ω₁</sub> is singular! Its cofinality is ω₁ &gt; ω, so König does not object (Solovay 1965: 2<sup>ℵ₀</sup> can be any κ with cf κ &gt; ω).', zh: '相容，尽管 ℵ<sub>ω₁</sub> 是奇异基数！它的共尾性是 ω₁ &gt; ω，柯尼希定理并不反对（索洛维 1965：2<sup>ℵ₀</sup> 可以是任意满足 cf κ &gt; ω 的 κ）。' },
    { sub: 'ω₁+ω', ok: false, en: 'Impossible: cf(ℵ<sub>ω₁+ω</sub>) = cf(ω₁+ω) = ω.', zh: '不可能：cf(ℵ<sub>ω₁+ω</sub>) = cf(ω₁+ω) = ω。' },
    { sub: 'ω₂', ok: true, en: 'Consistent: cf(ℵ<sub>ω₂</sub>) = ω₂ &gt; ω.', zh: '相容：cf(ℵ<sub>ω₂</sub>) = ω₂ &gt; ω。' },
  ];
  const shown = cands.map(() => false);
  const X = i => 50 + i * 89;
  function draw() {
    svg.innerHTML = '';
    el('line', { x1: 20, x2: 880, y1: 70, y2: 70, stroke: '#cfc9b8', 'stroke-width': 3 }, svg);
    richSVG(svg, 20, 24, '2^ℵ₀ = ?', { 'font-size': 14, fill: COL.muted, 'font-weight': 700 });
    cands.forEach((c, i) => {
      const g = el('g', {}, svg);
      g.style.cursor = 'pointer';
      const col = shown[i] ? (c.ok ? COL.tru : COL.fal) : '#fff';
      el('circle', { cx: X(i), cy: 70, r: 17, fill: col, stroke: shown[i] ? col : COL.ink, 'stroke-width': 2 }, g);
      if (shown[i]) svgText(g, X(i), 76, c.ok ? '✓' : '✗', { 'text-anchor': 'middle', 'font-size': 16, fill: '#fff', 'font-weight': 800 });
      alephSVG(g, X(i), 116, c.sub, { 'text-anchor': 'middle', 'font-size': 16, fill: COL.ink, 'font-weight': 700 });
      g.addEventListener('click', () => { shown[i] = true; draw(); okBox($('contMsg'), `<b class="m">2<sup>ℵ₀</sup> = ${alephH(c.sub)} ?</b> &nbsp;` + bi(c.en, c.zh), c.ok ? 'ok' : 'bad'); });
    });
  }
  $('contAll').addEventListener('click', () => {
    cands.forEach((_, i) => (shown[i] = true));
    draw();
    okBox($('contMsg'), bi('Green = consistent with ZFC, red = refuted by ZFC. The rule: 2<sup>ℵ₀</sup> can be any ℵ<sub>α</sub> with cf(ℵ<sub>α</sub>) &gt; ℵ₀ (and α ≥ 1).', '绿色 = 与 ZFC 相容，红色 = 被 ZFC 否定。规律是：2<sup>ℵ₀</sup> 可以是任何满足 cf(ℵ<sub>α</sub>) &gt; ℵ₀（且 α ≥ 1）的 ℵ<sub>α</sub>。'), 'info');
  });
  draw();
  okBox($('contMsg'), bi('Click a rung.', '点击一级梯子。'), 'info');
})();

/* ================= §7 cofinality pictures ================= */
(function cofinality() {
  const svg = $('cfSvg');
  const base = 120, H = 80;
  const P = ORD.parse, W = ORD.W, nat = ORD.nat;
  const opts = [
    { lab: 'ω+1', a: 'w+1', seq: k => (k === 0 ? W : null), cf: '1', en: 'The single element ω is cofinal: every successor ordinal has cofinality 1.', zh: '单独一个元素 ω 就是共尾的：后继序数的共尾性都是 1。' },
    { lab: 'ω', a: 'w', seq: k => nat(2 * k), cf: 'ω', en: 'Any infinite subset of ω is cofinal, e.g. the evens. A finite set is bounded, so cf(ω) = ω: ω is regular.', zh: 'ω 的任何无穷子集都共尾，比如全体偶数。有限集总是有界的，所以 cf(ω) = ω：ω 是正则的。' },
    { lab: 'ω·2', a: 'w*2', seq: k => ORD.add(W, nat(k)), cf: 'ω', en: 'ω, ω+1, ω+2, … is cofinal in ω·2, so cf(ω·2) = ω.', zh: 'ω, ω+1, ω+2, … 在 ω·2 中共尾，所以 cf(ω·2) = ω。' },
    { lab: 'ω²', a: 'w^2', seq: k => ORD.mul(W, nat(k + 1)), cf: 'ω', en: 'ω, ω·2, ω·3, … is cofinal in ω², so cf(ω²) = ω.', zh: 'ω, ω·2, ω·3, … 在 ω² 中共尾，所以 cf(ω²) = ω。' },
    { lab: 'ω^ω', html: 'ω<sup>ω</sup>', a: 'w^w', seq: k => ORD.pow(W, nat(k + 1)), cf: 'ω', en: 'ω, ω², ω³, … is cofinal in ω<sup>ω</sup>: cf = ω. Every countable limit ordinal has cofinality ω.', zh: 'ω, ω², ω³, … 在 ω<sup>ω</sup> 中共尾：cf = ω。每个可数极限序数的共尾性都是 ω。' },
    { lab: 'ω₁', special: 'w1', cf: 'ω₁', en: 'Any countable set of countable ordinals has a countable sup β &lt; ω₁ (a countable union of countable sets is countable, using AC). So no countable sequence reaches the top: cf(ω₁) = ω₁, regular.', zh: '任何可数个可数序数的上确界 β 仍可数，因而 β &lt; ω₁（可数个可数集之并可数，要用选择公理）。所以任何可数序列都到不了顶：cf(ω₁) = ω₁，正则。' },
    { lab: 'ℵ_ω', html: 'ℵ<sub>ω</sub>', special: 'aw', cf: 'ω', en: 'ℵ₀ &lt; ℵ₁ &lt; ℵ₂ &lt; ⋯ is cofinal in ℵ<sub>ω</sub>: just ω steps reach a huge cardinal. cf(ℵ<sub>ω</sub>) = ω &lt; ℵ<sub>ω</sub>, so ℵ<sub>ω</sub> is <b>singular</b>: it is a countable union of smaller sets.', zh: 'ℵ₀ &lt; ℵ₁ &lt; ℵ₂ &lt; ⋯ 在 ℵ<sub>ω</sub> 中共尾：只要 ω 步就能到达一个巨大的基数。cf(ℵ<sub>ω</sub>) = ω &lt; ℵ<sub>ω</sub>，所以 ℵ<sub>ω</sub> 是<b>奇异基数</b>：它是可数个更小集合的并。' },
    { lab: 'ℵ_ω₁', html: 'ℵ<sub>ω₁</sub>', special: 'aw1', cf: 'ω₁', en: 'ℵ<sub>α</sub> (α &lt; ω₁) is cofinal, of order type ω₁. A countable sequence ℵ<sub>αₙ</sub> stops below ℵ<sub>β</sub>, β = sup αₙ &lt; ω₁. So cf(ℵ<sub>ω₁</sub>) = ω₁ &lt; ℵ<sub>ω₁</sub>: singular, but of uncountable cofinality.', zh: 'ℵ<sub>α</sub>（α &lt; ω₁）构成序型为 ω₁ 的共尾子集。可数序列 ℵ<sub>αₙ</sub> 停在 ℵ<sub>β</sub> 之下，β = sup αₙ &lt; ω₁。所以 cf(ℵ<sub>ω₁</sub>) = ω₁ &lt; ℵ<sub>ω₁</sub>：奇异，但共尾性不可数。' },
  ];
  let cur = 2;
  function dot(x, y, k) {
    const c = el('circle', { cx: x, cy: y, r: 5, fill: COL.fal, class: 'pop' }, svg);
    c.style.animationDelay = (k * 0.12) + 's';
  }
  function draw() {
    const o = opts[cur];
    svg.innerHTML = '';
    el('line', { x1: 20, x2: 885, y1: base, y2: base, stroke: '#cfc9b8', 'stroke-width': 1.5 }, svg);
    if (!o.special) {
      const st = [];
      drawOrdinal(svg, P(o.a), { X0: 40, X1: 840, base, H, sticks: st });
      labelSticks(svg, st, base, { max: 14 });
      for (let k = 0; k < 40; k++) {
        const t = o.seq(k);
        if (!t) break;
        const s = st.find(q => ORD.eq(q.ord, t));
        if (!s) break;
        dot(s.x, base - s.h - 8, k);
      }
    } else if (o.special === 'w1') {
      el('line', { x1: 860, x2: 860, y1: base, y2: base - 90, stroke: COL.gold, 'stroke-width': 4 }, svg);
      svgText(svg, 860, base + 18, 'ω₁', { 'text-anchor': 'middle', 'font-size': 14, fill: COL.gold, 'font-weight': 800 });
      for (let k = 0; k < 18; k++) { const x = 60 + 520 * (1 - Math.pow(0.78, k)); el('line', { x1: x, x2: x, y1: base, y2: base - 40, stroke: COL.meta, 'stroke-width': 1.5 }, svg); dot(x, base - 48, k); }
      el('line', { x1: 580, x2: 580, y1: base, y2: base - 60, stroke: COL.accent, 'stroke-width': 3 }, svg);
      svgText(svg, 580, base + 18, 'β = sup αₙ', { 'text-anchor': 'middle', 'font-size': 12, fill: COL.accent, 'font-weight': 700 });
      svgText(svg, 60, base + 18, 'α₀', { 'text-anchor': 'middle', 'font-size': 12, fill: COL.fal });
      el('rect', { x: 590, y: base - 30, width: 260, height: 26, rx: 6, fill: COL.gold, opacity: 0.15 }, svg);
      svgText(svg, 720, base - 12, 'still room above: β+1, β+2, … · 上面还有空间', { 'text-anchor': 'middle', 'font-size': 11, fill: '#6b4500' });
      svgText(svg, 300, 22, 'a countable sequence in ω₁ · ω₁ 中的一个可数序列', { 'text-anchor': 'middle', 'font-size': 12, fill: COL.muted });
    } else if (o.special === 'aw') {
      for (let k = 0; k < 14; k++) {
        const x = 60 + 780 * (1 - Math.pow(0.72, k));
        el('line', { x1: x, x2: x, y1: base, y2: base - 70 + k * 2, stroke: COL.gold, 'stroke-width': 3 }, svg);
        if (k < 6) alephSVG(svg, x, base + 18, String(k), { 'text-anchor': 'middle', 'font-size': 14, fill: COL.gold, 'font-weight': 700 });
        dot(x, base - 78 + k * 2, k);
      }
      el('line', { x1: 860, x2: 860, y1: base, y2: base - 95, stroke: COL.gold, 'stroke-width': 5 }, svg);
      alephSVG(svg, 860, base + 18, 'ω', { 'text-anchor': 'middle', 'font-size': 15, fill: COL.fal, 'font-weight': 800 });
    } else {
      const labs = ['0', '1', '2', '…', 'ω', 'ω+1', '…', 'ω²', '…'];
      for (let k = 0; k < 22; k++) {
        const x = 60 + 540 * (1 - Math.pow(0.84, k));
        el('line', { x1: x, x2: x, y1: base, y2: base - 56, stroke: COL.gold, 'stroke-width': 2 }, svg);
        if (k < labs.length && labs[k] !== '…') alephSVG(svg, x, base + 18, labs[k], { 'text-anchor': 'middle', 'font-size': 12, fill: COL.gold });
        dot(x, base - 64, k);
      }
      el('line', { x1: 610, x2: 610, y1: base, y2: base - 70, stroke: COL.accent, 'stroke-width': 3 }, svg);
      alephSVG(svg, 610, base + 18, 'β', { 'text-anchor': 'middle', 'font-size': 13, fill: COL.accent, 'font-weight': 700 });
      for (let k = 0; k < 10; k++) { const x = 650 + k * 19; el('line', { x1: x, x2: x, y1: base, y2: base - 56, stroke: COL.gold, 'stroke-width': 2, opacity: 0.6 }, svg); }
      el('line', { x1: 860, x2: 860, y1: base, y2: base - 95, stroke: COL.gold, 'stroke-width': 5 }, svg);
      alephSVG(svg, 860, base + 18, 'ω₁', { 'text-anchor': 'middle', 'font-size': 15, fill: COL.gold, 'font-weight': 800 });
      richSVG(svg, 740, base - 72, 'ℵ_α for β ≤ α < ω₁', { 'text-anchor': 'middle', 'font-size': 11, fill: COL.muted });
    }
    svgText(svg, 880, 22, `cf = ${o.cf}`, { 'text-anchor': 'end', 'font-size': 16, fill: COL.fal, 'font-weight': 800 });
    okBox($('cfMsg'), `<b class="m">cf(${o.html || o.lab}) = ${o.cf}</b> &nbsp; ` + bi(o.en, o.zh), 'info');
  }
  opts.forEach((o, i) => {
    const b = document.createElement('button');
    b.className = 'btn small' + (i === cur ? ' sel' : '');
    b.innerHTML = `<span class="m">${o.html || o.lab}</span>`;
    b.addEventListener('click', () => { cur = i; $('cfPick').querySelectorAll('button').forEach(x => x.classList.toggle('sel', x === b)); draw(); });
    $('cfPick').appendChild(b);
  });
  draw();

  // regular / singular ladder
  const lad = $('ladSvg');
  const rungs = [
    { sub: '0', t: 'r', en: 'ℵ₀ = ω is regular: a finite union of finite sets is finite.', zh: 'ℵ₀ = ω 正则：有限个有限集之并仍有限。' },
    { sub: '1', t: 'r', en: 'Successor cardinal ⇒ regular (AC).', zh: '后继基数 ⇒ 正则（选择公理）。' },
    { sub: '2', t: 'r', en: 'Successor cardinal ⇒ regular.', zh: '后继基数 ⇒ 正则。' },
    { sub: '3', t: 'r', en: 'Successor cardinal ⇒ regular.', zh: '后继基数 ⇒ 正则。' },
    { sub: 'ω', t: 's', en: 'cf(ℵ<sub>ω</sub>) = cf(ω) = ω &lt; ℵ<sub>ω</sub>: singular. The first singular cardinal.', zh: 'cf(ℵ<sub>ω</sub>) = cf(ω) = ω &lt; ℵ<sub>ω</sub>：奇异。它是第一个奇异基数。' },
    { sub: 'ω+1', t: 'r', en: 'ℵ<sub>ω+1</sub> = (ℵ<sub>ω</sub>)⁺ is a successor, so it is regular.', zh: 'ℵ<sub>ω+1</sub> = (ℵ<sub>ω</sub>)⁺ 是后继基数，所以正则。' },
    { sub: 'ω·2', t: 's', en: 'cf(ℵ<sub>ω·2</sub>) = cf(ω·2) = ω: singular.', zh: 'cf(ℵ<sub>ω·2</sub>) = cf(ω·2) = ω：奇异。' },
    { sub: 'ω₁', t: 's', en: 'cf(ℵ<sub>ω₁</sub>) = cf(ω₁) = ω₁ &lt; ℵ<sub>ω₁</sub>: singular (of uncountable cofinality).', zh: 'cf(ℵ<sub>ω₁</sub>) = cf(ω₁) = ω₁ &lt; ℵ<sub>ω₁</sub>：奇异（共尾性不可数）。' },
    { sub: 'ω₁+1', t: 'r', en: 'Successor, regular.', zh: '后继基数，正则。' },
    { sub: 'ω_ω', t: 's', en: 'cf(ℵ<sub>ω<sub>ω</sub></sub>) = cf(ω<sub>ω</sub>) = ω: singular.', zh: 'cf(ℵ<sub>ω<sub>ω</sub></sub>) = cf(ω<sub>ω</sub>) = ω：奇异。' },
    { sub: 'κ=κ?', t: '?', en: 'A <b>regular limit</b> cardinal ℵ<sub>κ</sub> = κ &gt; ℵ₀ is called <b>weakly inaccessible</b>. Its index must equal itself, and ZFC cannot prove that one exists (if ZFC is consistent).', zh: '<b>正则的极限基数</b> ℵ<sub>κ</sub> = κ &gt; ℵ₀ 称为<b>弱不可达基数</b>。它的下标必须等于它自己，而且（若 ZFC 相容）ZFC 无法证明它存在。' },
  ];
  const lx = i => 45 + i * 82;
  function drawLad(sel) {
    lad.innerHTML = '';
    el('line', { x1: 20, x2: 885, y1: 90, y2: 90, stroke: '#cfc9b8', 'stroke-width': 2 }, lad);
    rungs.forEach((r, i) => {
      const col = r.t === 'r' ? COL.tru : r.t === 's' ? COL.fal : COL.gold;
      const g = el('g', {}, lad);
      g.style.cursor = 'pointer';
      el('rect', { x: lx(i) - 34, y: 6, width: 68, height: 116, fill: 'transparent' }, g);
      el('line', { x1: lx(i), x2: lx(i), y1: 90, y2: 40, stroke: col, 'stroke-width': i === sel ? 6 : 4 }, g);
      el('circle', { cx: lx(i), cy: 34, r: i === sel ? 10 : 8, fill: col }, g);
      alephSVG(g, lx(i), 112, r.sub === 'κ=κ?' ? 'κ' : r.sub, { 'text-anchor': 'middle', 'font-size': 14, fill: COL.ink, 'font-weight': i === sel ? 800 : 500 }, r.sub === 'κ=κ?' ? ' = κ ?' : '');
      g.addEventListener('click', () => { drawLad(i); okBox($('ladMsg'), `<b class="m">${alephH(r.sub === 'ω_ω' ? 'ω<sub>ω</sub>' : r.sub === 'κ=κ?' ? 'κ' : r.sub)}</b> &nbsp;` + bi(r.en, r.zh), 'info'); });
    });
  }
  drawLad(-1);
  okBox($('ladMsg'), bi('Click a rung for the reason.', '点击一级看理由。'), 'info');
})();

/* ================= §8 König matrix ================= */
(function konig() {
  const kap = [1, 2, 2, 3], lam = [2, 3, 3, 4], I = 4;
  let rows = [];
  function randomRows() {
    rows = [];
    kap.forEach((k, i) => { for (let x = 0; x < k; x++) rows.push({ i, x, v: lam.map(l => Math.floor(Math.random() * l)) }); });
  }
  let g = null, hot = -1;
  function computeG() { return lam.map((l, i) => { const used = new Set(rows.filter(r => r.i === i).map(r => r.v[i])); for (let c = 0; c < l; c++) if (!used.has(c)) return c; return null; }); }
  function render() {
    let h = '<table class="kt"><tr><th></th>';
    for (let i = 0; i < I; i++) h += `<th>i = ${i}<br>λ${subN(i)} = ${lam[i]}</th>`;
    h += '<th></th></tr>';
    rows.forEach((r, k) => {
      h += `<tr class="blk${r.i}"><td class="lab">F(${r.i}, ${r.x}) <span style="opacity:.6">${bil('block', '块')} ${r.i}</span></td>`;
      r.v.forEach((v, j) => (h += `<td class="cell${j === r.i ? ' diag' : ''}${j === r.i && hot === r.i ? ' hot' : ''}" data-k="${k}" data-j="${j}">${v}</td>`));
      h += `<td class="neq">${g ? (g[r.i] !== r.v[r.i] ? `≠ g ${bil('at coord', '于坐标')} ${r.i}` : '') : ''}</td></tr>`;
    });
    h += `<tr><td class="lab"><b style="color:var(--true)">g =</b></td>`;
    for (let i = 0; i < I; i++) h += `<td class="g">${g && g[i] !== undefined && i <= (hot < 0 ? I : hot) ? g[i] : '?'}</td>`;
    h += '<td class="neq"></td></tr></table>';
    $('konigTable').innerHTML = h;
    $('konigTable').querySelectorAll('td.cell').forEach(td => td.addEventListener('click', () => {
      const r = rows[+td.dataset.k], j = +td.dataset.j;
      r.v[j] = (r.v[j] + 1) % lam[j];
      g = null; hot = -1;
      render();
      clearBox($('konigMsg'));
    }));
  }
  let token = 0;
  async function build() {
    const my = ++token;
    g = computeG();
    for (let i = 0; i < I; i++) {
      if (my !== token) return;
      hot = i;
      render();
      const used = [...new Set(rows.filter(r => r.i === i).map(r => r.v[i]))].sort();
      okBox($('konigMsg'), bi(`Block ${i}: column ${i} uses {${used.join(', ')}}, which is ${used.length} ≤ κ${subN(i)} = ${kap[i]} values out of λ${subN(i)} = ${lam[i]}. Pick g(${i}) = ${g[i]}.`, `第 ${i} 块：第 ${i} 列用到 {${used.join(', ')}}，共 ${used.length} ≤ κ${subN(i)} = ${kap[i]} 个值，而 λ${subN(i)} = ${lam[i]}。取 g(${i}) = ${g[i]}。`), 'info');
      await sleep(900);
    }
    hot = -1;
    render();
    okBox($('konigMsg'), bi(`g = (${g.join(', ')}) differs from every row F(i, ξ) at coordinate i, so it is missing from the list. Σκᵢ = 8 rows can never cover Πλᵢ = 2·3·3·4 = 72 tuples, and the same block-diagonal argument works for infinite κᵢ &lt; λᵢ.`, `g = (${g.join(', ')}) 与每一行 F(i, ξ) 在坐标 i 上都不同，所以它不在列表里。Σκᵢ = 8 行永远盖不住 Πλᵢ = 2·3·3·4 = 72 个元组；对无穷的 κᵢ &lt; λᵢ，同样的分块对角线论证照样成立。`), 'ok');
  }
  $('konigBuild').addEventListener('click', build);
  $('konigRand').addEventListener('click', () => { token++; randomRows(); g = null; hot = -1; render(); clearBox($('konigMsg')); });
  randomRows();
  render();
  stepper('konigSteps', 'konigNext', 'konigAll');
})();

/* ================= E1 cardinal arithmetic ================= */
function optionRows(boxId, items, options, progId) {
  const solved = items.map(() => false);
  const revealed = items.map(() => false); // once an answer is shown, that item can no longer earn progress
  items.forEach((it, i) => {
    const row = document.createElement('div');
    row.className = 'ansrow';
    row.innerHTML = `<div class="q">(${String.fromCharCode(97 + i)}) &nbsp; ${it.q}</div><div class="opts"></div>
      <button class="btn small ghost">${bil('Show answer', '看答案')}</button><div class="msg"></div>`;
    $(boxId).appendChild(row);
    const msg = row.querySelector('.msg'), box = row.querySelector('.opts');
    const btns = options.map((o, k) => {
      const b = document.createElement('button');
      b.className = 'btn small';
      b.innerHTML = `<span class="m">${o}</span>`;
      b.addEventListener('click', () => {
        btns.forEach(x => x.classList.remove('right', 'wrongc'));
        if (k === it.ans) {
          b.classList.add('right');
          okBox(msg, '✓ ' + bi(it.en, it.zh));
          if (!revealed[i]) solved[i] = true;
          if (solved.every(Boolean)) Progress.mark(progId);
        } else { b.classList.add('wrongc'); okBox(msg, bi(it.hintEn || '✗ Not this one. Try again.', it.hintZh || '✗ 不是这个，再想想。'), 'bad'); }
      });
      box.appendChild(b);
      return b;
    });
    row.querySelector('.ghost').addEventListener('click', () => {
      revealed[i] = true;
      btns.forEach(x => x.classList.remove('right', 'wrongc'));
      btns[it.ans].classList.add('right');
      okBox(msg, bi(it.en, it.zh), 'info');
    });
  });
}
optionRows('e1List', [
  { q: 'ℵ₀ · ℵ₁', ans: 1, en: 'max(ℵ₀, ℵ₁) = ℵ₁.', zh: 'max(ℵ₀, ℵ₁) = ℵ₁。' },
  { q: 'ℵ₂ + ℵ₀', ans: 2, en: 'max(ℵ₂, ℵ₀) = ℵ₂.', zh: 'max(ℵ₂, ℵ₀) = ℵ₂。' },
  { q: 'ℵ₀<sup>ℵ₀</sup>', ans: 4, en: '2<sup>ℵ₀</sup> ≤ ℵ₀<sup>ℵ₀</sup> ≤ (2<sup>ℵ₀</sup>)<sup>ℵ₀</sup> = 2<sup>ℵ₀·ℵ₀</sup> = 2<sup>ℵ₀</sup>.', zh: '2<sup>ℵ₀</sup> ≤ ℵ₀<sup>ℵ₀</sup> ≤ (2<sup>ℵ₀</sup>)<sup>ℵ₀</sup> = 2<sup>ℵ₀·ℵ₀</sup> = 2<sup>ℵ₀</sup>。' },
  { q: 'ℵ₁<sup>ℵ₀</sup>', ans: 4, en: 'Since ℵ₁ ≤ 2<sup>ℵ₀</sup>: 2<sup>ℵ₀</sup> ≤ ℵ₁<sup>ℵ₀</sup> ≤ (2<sup>ℵ₀</sup>)<sup>ℵ₀</sup> = 2<sup>ℵ₀</sup>. This holds whether or not CH is true.', zh: '因为 ℵ₁ ≤ 2<sup>ℵ₀</sup>：2<sup>ℵ₀</sup> ≤ ℵ₁<sup>ℵ₀</sup> ≤ (2<sup>ℵ₀</sup>)<sup>ℵ₀</sup> = 2<sup>ℵ₀</sup>。无论 CH 是否成立都对。' },
  { q: '(2<sup>ℵ₀</sup>)<sup>ℵ₁</sup>', ans: 5, en: '(2<sup>ℵ₀</sup>)<sup>ℵ₁</sup> = 2<sup>ℵ₀·ℵ₁</sup> = 2<sup>ℵ₁</sup>.', zh: '(2<sup>ℵ₀</sup>)<sup>ℵ₁</sup> = 2<sup>ℵ₀·ℵ₁</sup> = 2<sup>ℵ₁</sup>。' },
  { q: 'ℵ<sub>ω</sub> + ℵ₃ · ℵ₅', ans: 3, en: 'ℵ₃ · ℵ₅ = ℵ₅, and ℵ<sub>ω</sub> + ℵ₅ = ℵ<sub>ω</sub>.', zh: 'ℵ₃ · ℵ₅ = ℵ₅，而 ℵ<sub>ω</sub> + ℵ₅ = ℵ<sub>ω</sub>。' },
  { q: 'Σ<sub>n&lt;ω</sub> ℵ<sub>n</sub>', ans: 3, en: 'The sum is the size of a disjoint union; it is ≥ every ℵ<sub>n</sub> and ≤ ℵ₀ · ℵ<sub>ω</sub> = ℵ<sub>ω</sub>. So it equals ℵ<sub>ω</sub>.', zh: '和是不交并的大小；它 ≥ 每个 ℵ<sub>n</sub>，且 ≤ ℵ₀ · ℵ<sub>ω</sub> = ℵ<sub>ω</sub>，所以等于 ℵ<sub>ω</sub>。' },
], ['ℵ₀', 'ℵ₁', 'ℵ₂', 'ℵ<sub>ω</sub>', '2<sup>ℵ₀</sup>', '2<sup>ℵ₁</sup>'], 'L9E1');

/* ================= E2 pairing position ================= */
(function e2() {
  const svg = $('e2Svg');
  const N = 6, cell = 34, x0 = 46, yb = 232;
  let cur = null, streak = 0, cells = [];
  function fresh() {
    let a, b;
    do { a = Math.floor(Math.random() * N); b = Math.floor(Math.random() * N); } while (cur && cur.a === a && cur.b === b);
    cur = { a, b, pos: godelPos(a, b), revealed: false, done: false };
    cells = drawPairGrid(svg, N, cell, x0, yb);
    const c = cells.find(d => d.a === a && d.b === b);
    c.r.setAttribute('fill', COL.fal);
    c.t.textContent = '?';
    c.t.setAttribute('fill', '#fff');
    $('e2Q').innerHTML = `(${a}, ${b}) ↦ ?`;
    $('e2In').value = '';
    clearBox($('e2Msg'));
  }
  const paintStreak = () => ($('e2Streak').innerHTML = bil(`streak: ${streak} / 3`, `连对：${streak} / 3`));
  function reveal() {
    cells.forEach(d => { d.t.textContent = d.pos; if (d.pos < cur.pos) d.r.setAttribute('fill', '#bac8ff'); });
    const c = cells.find(d => d.a === cur.a && d.b === cur.b);
    c.t.textContent = cur.pos;
    const m = Math.max(cur.a, cur.b);
    return cur.a < m ? `m = ${m}, α &lt; m: m² + α = ${m * m} + ${cur.a} = ${cur.pos}` : `m = ${m}, α = m: m² + m + β = ${m * m} + ${m} + ${cur.b} = ${cur.pos}`;
  }
  $('e2Check').addEventListener('click', () => {
    const v = parseInt($('e2In').value, 10);
    if (Number.isNaN(v)) { okBox($('e2Msg'), bi('Type a natural number.', '请输入一个自然数。'), 'bad'); return; }
    if (cur.done) return; // already answered; wait for the next pair
    if (v === cur.pos) {
      cur.done = true;
      // a pair whose answer was shown cannot count towards the streak
      if (cur.revealed) { okBox($('e2Msg'), `<span class="m">${reveal()}</span><br>` + bi('Right, but the answer was shown for this pair, so it does not count. Try a new pair.', '对了，但这一题已看过答案，不计入连对。换一题吧。'), 'info'); paintStreak(); return; }
      streak++;
      const why = reveal();
      okBox($('e2Msg'), `✓ <span class="m">${why}</span>`);
      if (streak >= 3) { Progress.mark('L9E2'); okBox($('e2Msg'), `✓ <span class="m">${why}</span><br>` + bi('Three in a row. Solved!', '连对三题，完成！')); }
      else setTimeout(fresh, 1600);
    } else {
      streak = 0;
      okBox($('e2Msg'), bi('✗ Not quite. Count the full shells below m = max(α, β) first: there are m² cells in them.', '✗ 不对。先数 m = max(α, β) 以内的完整方壳：一共 m² 个格子。'), 'bad');
    }
    paintStreak();
  });
  $('e2In').addEventListener('keydown', e => e.key === 'Enter' && $('e2Check').click());
  $('e2Show').addEventListener('click', () => { streak = 0; cur.revealed = true; paintStreak(); okBox($('e2Msg'), `<span class="m">${reveal()}</span>`, 'info'); });
  $('e2New').addEventListener('click', fresh);
  fresh();
  paintStreak();
})();

/* ================= E3 cofinalities ================= */
optionRows('e3List', [
  { q: 'cf(ω·2)', ans: 1, en: 'ω+n (n &lt; ω) is cofinal.', zh: 'ω+n（n &lt; ω）共尾。' },
  { q: 'cf(ω+5)', ans: 0, en: 'A successor ordinal: its largest element ω+4 is cofinal on its own.', zh: '后继序数：它的最大元 ω+4 单独就共尾。' },
  { q: 'cf(ω<sup>ω</sup>)', ans: 1, en: 'ω<sup>n</sup> (n &lt; ω) is cofinal.', zh: 'ω<sup>n</sup>（n &lt; ω）共尾。' },
  { q: 'cf(ω₁)', ans: 2, en: 'ω₁ is regular: countable sets of countable ordinals are bounded.', zh: 'ω₁ 正则：可数个可数序数总是有上界。' },
  { q: 'cf(ω₁·2)', ans: 2, en: 'ω₁ + α (α &lt; ω₁) is cofinal, and a countable set is bounded by some ω₁ + β. So cf = ω₁, although |ω₁·2| = ℵ₁ and ω₁·2 is not a cardinal.', zh: 'ω₁ + α（α &lt; ω₁）共尾，而任何可数集都被某个 ω₁ + β 界住。所以 cf = ω₁；尽管 |ω₁·2| = ℵ₁，且 ω₁·2 不是基数。' },
  { q: 'cf(ℵ<sub>ω</sub>)', ans: 1, en: 'ℵ<sub>n</sub> (n &lt; ω) is cofinal.', zh: 'ℵ<sub>n</sub>（n &lt; ω）共尾。' },
  { q: 'cf(ℵ<sub>ω₁</sub>)', ans: 2, en: 'cf(ℵ<sub>ω₁</sub>) = cf(ω₁) = ω₁.', zh: 'cf(ℵ<sub>ω₁</sub>) = cf(ω₁) = ω₁。' },
  { q: 'cf(ℵ<sub>ω₂+ω</sub>)', ans: 1, en: 'ℵ<sub>ω₂+n</sub> (n &lt; ω) is cofinal: cf = cf(ω₂+ω) = ω.', zh: 'ℵ<sub>ω₂+n</sub>（n &lt; ω）共尾：cf = cf(ω₂+ω) = ω。' },
  { q: 'cf(ℵ<sub>ω₂</sub>)', ans: 3, en: 'cf(ℵ<sub>ω₂</sub>) = cf(ω₂) = ω₂ (ω₂ is a successor cardinal, so regular).', zh: 'cf(ℵ<sub>ω₂</sub>) = cf(ω₂) = ω₂（ω₂ 是后继基数，所以正则）。' },
], ['1', 'ω', 'ω₁', 'ω₂'], 'L9E3');

/* ================= E4 regular or singular ================= */
(function e4() {
  const items = [['0', 'r'], ['1', 'r'], ['5', 'r'], ['ω', 's'], ['ω+1', 'r'], ['ω·2', 's'], ['ω₁', 's'], ['ω₁+1', 'r'], ['ω₂', 's'], ['ω₂+1', 'r']];
  const state = items.map(() => null);
  let revealed = false; // after "Show answer", Check no longer earns progress
  const cyc = [null, 'r', 's'];
  const LAB = { r: bil('regular', '正则'), s: bil('singular', '奇异') };
  const chips = items.map(([sub], i) => {
    const c = document.createElement('div');
    c.className = 'chip m';
    c.addEventListener('click', () => { state[i] = cyc[(cyc.indexOf(state[i]) + 1) % 3]; paint(); clearBox($('e4Msg')); });
    $('e4Chips').appendChild(c);
    return c;
  });
  function paint(mark) {
    chips.forEach((c, i) => {
      c.className = 'chip m' + (state[i] ? ' st-' + state[i] : '') + (mark ? (state[i] === items[i][1] ? ' ok' : ' no') : '');
      c.innerHTML = `${alephH(items[i][0])}<span class="st">${state[i] ? LAB[state[i]] : '?'}</span>`;
    });
  }
  paint();
  const expl = bi('Successor cardinals (ℵ₀ too) are regular. For a limit index λ, cf(ℵ<sub>λ</sub>) = cf(λ) ≤ λ &lt; ℵ<sub>λ</sub> unless ℵ<sub>λ</sub> = λ, so ℵ<sub>ω</sub>, ℵ<sub>ω·2</sub>, ℵ<sub>ω₁</sub>, ℵ<sub>ω₂</sub> are all singular. The trap: ℵ<sub>ω₂</sub> has a regular index ω₂, yet cf(ℵ<sub>ω₂</sub>) = ω₂ &lt; ℵ<sub>ω₂</sub>.',
    '后继基数（以及 ℵ₀）都正则。对极限下标 λ，除非 ℵ<sub>λ</sub> = λ，否则 cf(ℵ<sub>λ</sub>) = cf(λ) ≤ λ &lt; ℵ<sub>λ</sub>，所以 ℵ<sub>ω</sub>、ℵ<sub>ω·2</sub>、ℵ<sub>ω₁</sub>、ℵ<sub>ω₂</sub> 都奇异。陷阱：ℵ<sub>ω₂</sub> 的下标 ω₂ 是正则的，但 cf(ℵ<sub>ω₂</sub>) = ω₂ &lt; ℵ<sub>ω₂</sub>。');
  $('e4Check').addEventListener('click', () => {
    paint(true);
    const right = state.filter((s, i) => s === items[i][1]).length;
    if (right === items.length) { okBox($('e4Msg'), '✓ ' + expl); if (!revealed) Progress.mark('L9E4'); }
    else okBox($('e4Msg'), bi(`${right} / ${items.length} correct (red = wrong). Is the index a successor or a limit? If a limit, compare cf(index) with ℵ<sub>index</sub>.`, `答对 ${right} / ${items.length}（红色为错）。下标是后继还是极限？若是极限，比较 cf(下标) 与 ℵ<sub>下标</sub>。`), 'warn');
  });
  $('e4Show').addEventListener('click', () => { revealed = true; items.forEach((it, i) => (state[i] = it[1])); paint(true); okBox($('e4Msg'), expl, 'info'); });
})();

/* ================= E5 Schröder–Bernstein on [0,1] ================= */
(function e5() {
  const done = { a: false, b: [false, false, false] };
  let revealed = false; // after "Show answers", correct clicks no longer earn progress
  const fin = () => !revealed && done.a && done.b.every(Boolean) && Progress.mark('L9E5');
  const A = [
    { ok: false, html: '<span class="m">f(x) = x/2</span>', en: '✗ f(0) = 0 is not in (0,1).', zh: '✗ f(0) = 0 不在 (0,1) 里。' },
    { ok: true, html: '<span class="m">f(x) = (x+1)/3</span>', en: '✓ Injective, with image [1/3, 2/3] ⊂ (0,1).', zh: '✓ 是单射，像集 [1/3, 2/3] ⊂ (0,1)。' },
    { ok: false, html: '<span class="m">f(x) = x(1−x)</span>', en: '✗ Not injective (f(0) = f(1) = 0), and 0 ∉ (0,1) anyway.', zh: '✗ 不是单射（f(0) = f(1) = 0），而且 0 ∉ (0,1)。' },
    { ok: false, html: '<span class="m">f(x) = (1+x)/2</span>', en: '✗ f(1) = 1 is not in (0,1).', zh: '✗ f(1) = 1 不在 (0,1) 里。' },
  ];
  choiceButtons($('e5a'), A, o => {
    okBox($('e5aMsg'), bi(o.en, o.zh), o.ok ? 'ok' : 'bad');
    if (o.ok) { done.a = true; fin(); }
  });
  const Q = [
    { q: 'h(0)', opts: ['0', '1/3', '1/2', '4/9'], ans: 1, en: '0 ∉ g[(0,1)], so 0 starts an A-chain: 0 → 1/3 → 1/3 → 4/9 → … On it h = f, so h(0) = 1/3.', zh: '0 ∉ g[(0,1)]，所以 0 是一条 A 链的起点：0 → 1/3 → 1/3 → 4/9 → …。在这条链上 h = f，故 h(0) = 1/3。' },
    { q: 'h(1/3)', opts: ['1/3', '4/9', '2/3', '1/9'], ans: 1, en: '1/3 ∈ A is g(1/3), and 1/3 ∈ B is f(0): it lies on the A-chain of 0. So h(1/3) = f(1/3) = 4/9.', zh: '1/3 ∈ A 是 g(1/3)，而 1/3 ∈ B 是 f(0)：它在 0 的 A 链上。所以 h(1/3) = f(1/3) = 4/9。' },
    { q: 'h(1/9)', opts: ['1/9', '10/27', '1/3', '1/27'], ans: 0, en: 'Trace back: 1/9 ∈ A is g(1/9), and 1/9 ∈ B is not in f[A] = [1/3, 2/3]. So it is a B-chain and h(1/9) = g⁻¹(1/9) = 1/9. Outside the two chains through 0 and 1, h is the identity!', zh: '往回追：1/9 ∈ A 是 g(1/9)，而 1/9 ∈ B 不在 f[A] = [1/3, 2/3] 中。所以这是 B 链，h(1/9) = g⁻¹(1/9) = 1/9。除了经过 0 和 1 的两条链，h 就是恒等映射！' },
  ];
  Q.forEach((it, i) => {
    const row = document.createElement('div');
    row.className = 'ansrow';
    row.innerHTML = `<div class="q">${it.q} =</div><div class="opts"></div><div class="msg"></div>`;
    $('e5b').appendChild(row);
    it.row = row;
    it.btns = it.opts.map((o, k) => {
      const b = document.createElement('button');
      b.className = 'btn small';
      b.innerHTML = `<span class="m">${o}</span>`;
      b.addEventListener('click', () => {
        it.btns.forEach(x => x.classList.remove('right', 'wrongc'));
        if (k === it.ans) { b.classList.add('right'); okBox(row.querySelector('.msg'), '✓ ' + bi(it.en, it.zh)); done.b[i] = true; fin(); }
        else { b.classList.add('wrongc'); okBox(row.querySelector('.msg'), bi('✗ Trace back first: is the chain an A-chain (use f) or a B-chain (use g⁻¹)?', '✗ 先往回追：这是 A 链（用 f）还是 B 链（用 g⁻¹）？'), 'bad'); }
      });
      row.querySelector('.opts').appendChild(b);
      return b;
    });
  });
  $('e5Show').addEventListener('click', () => {
    revealed = true;
    $('e5a').querySelectorAll('.choice')[1].classList.add('right');
    okBox($('e5aMsg'), bi(A[1].en, A[1].zh), 'info');
    Q.forEach(it => { it.btns[it.ans].classList.add('right'); okBox(it.row.querySelector('.msg'), bi(it.en, it.zh), 'info'); });
    okBox($('e5bMsg'), bi('Summary: h(x) = f(x) = (x+1)/3 on the two chains 0, 1/3, 4/9, 13/27, … and 1, 2/3, 5/9, 14/27, …, and h(x) = x everywhere else.', '小结：在两条链 0, 1/3, 4/9, 13/27, … 与 1, 2/3, 5/9, 14/27, … 上 h(x) = f(x) = (x+1)/3，其余各处 h(x) = x。'), 'info');
  });
})();

/* ================= E6 what ZFC proves ================= */
(function e6() {
  const items = [
    { s: 'ℵ<sub>ω</sub><sup>ℵ₀</sup> &gt; ℵ<sub>ω</sub>', thm: true, en: 'Theorem: König, κ<sup>cf κ</sup> &gt; κ.', zh: '定理：柯尼希，κ<sup>cf κ</sup> &gt; κ。' },
    { s: '2<sup>ℵ₀</sup> ≠ ℵ<sub>ω</sub>', thm: true, en: 'Theorem: cf(2<sup>ℵ₀</sup>) &gt; ℵ₀ = cf(ℵ<sub>ω</sub>).', zh: '定理：cf(2<sup>ℵ₀</sup>) &gt; ℵ₀ = cf(ℵ<sub>ω</sub>)。' },
    { s: '2<sup>ℵ₀</sup> = ℵ₁', thm: false, en: 'Not provable (Cohen), and not refutable either (Gödel): CH is independent of ZFC (assuming ZFC is consistent).', zh: '证不出（科恩），也驳不倒（哥德尔）：CH 独立于 ZFC（假定 ZFC 相容）。' },
    { s: 'cf(2<sup>ℵ₁</sup>) &gt; ℵ₁', thm: true, en: 'Theorem: Corollary 3 of König with κ = ℵ₁.', zh: '定理：柯尼希定理推论 3，取 κ = ℵ₁。' },
    { s: '2<sup>ℵ₀</sup> &lt; 2<sup>ℵ₁</sup>', thm: false, en: 'Not provable: 2<sup>ℵ₀</sup> = 2<sup>ℵ₁</sup> is consistent (Luzin\'s hypothesis; e.g. both equal ℵ₂ in a suitable forcing extension). Only ≤ is a theorem.', zh: '证不出：2<sup>ℵ₀</sup> = 2<sup>ℵ₁</sup> 是相容的（卢津假设；例如在适当的力迫扩张中二者都等于 ℵ₂）。只有 ≤ 是定理。' },
    { s: 'Σ<sub>n&lt;ω</sub> ℵ<sub>n</sub> &lt; Π<sub>n&lt;ω</sub> ℵ<sub>n+1</sub>', thm: true, en: 'Theorem: König with κₙ = ℵₙ &lt; λₙ = ℵₙ₊₁.', zh: '定理：柯尼希定理，取 κₙ = ℵₙ &lt; λₙ = ℵₙ₊₁。' },
    { s: 'ℵ₁ ≤ 2<sup>ℵ₀</sup>', thm: true, en: 'Theorem (with AC): 2<sup>ℵ₀</sup> is an uncountable cardinal and ℵ₁ is the least one.', zh: '定理（用选择公理）：2<sup>ℵ₀</sup> 是不可数基数，而 ℵ₁ 是最小的不可数基数。' },
  ];
  const solved = items.map(() => false);
  const revealed = items.map(() => false);
  items.forEach((it, i) => {
    const row = document.createElement('div');
    row.className = 'tf';
    row.innerHTML = `<div class="stmt">${it.s}</div>
      <button class="btn small" data-v="1">${bil('ZFC theorem', 'ZFC 定理')}</button>
      <button class="btn small" data-v="0">${bil('Not provable', '证不出')}</button>
      <button class="btn small ghost" data-v="show">${bil('Show answer', '看答案')}</button>
      <div style="flex-basis:100%"><div class="msg"></div></div>`;
    $('e6List').appendChild(row);
    row.querySelectorAll('button').forEach(b => b.addEventListener('click', () => {
      const msg = row.querySelector('.msg');
      if (b.dataset.v === 'show') { revealed[i] = true; okBox(msg, bi(it.en, it.zh), 'info'); return; }
      if ((b.dataset.v === '1') === it.thm) {
        okBox(msg, '✓ ' + bi(it.en, it.zh));
        if (!revealed[i]) solved[i] = true;
        if (solved.every(Boolean)) Progress.mark('L9E6');
      } else okBox(msg, bi('✗ Not quite. Does König\'s theorem (or §4) give it, or could a forcing model break it?', '✗ 不对。柯尼希定理（或 §4）能推出它吗？还是某个力迫模型能让它失效？'), 'bad');
    }));
  });
})();
