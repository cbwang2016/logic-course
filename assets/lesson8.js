// Lesson 8 interactions: well-orders, ordinals, transfinite induction.

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

/* ================= §1 descending chain hunt ================= */
(function chainHunt() {
  const svg = $('chainSvg');
  const Y = 120;
  let mode = 'N', seq = [], busy = 0;
  const bgcd = (a, b) => { a = a < 0n ? -a : a; while (b) [a, b] = [b, a % b]; return a; };
  const frac = (p, q) => { const g = bgcd(p, q) || 1n; return [p / g, q / g]; };
  const fracStr = ([p, q]) => {
    if (p === 0n) return '0';
    if (q === 1n) return String(p);
    const s = `${p}/${q}`;
    return s.length <= 9 ? s : '≈' + (Number(p) / Number(q)).toExponential(1);
  };
  const M = {
    N: { wo: true, less: (a, b) => a < b, lab: v => String(v), eq: (a, b) => a === b },
    W2: { wo: true, less: (a, b) => a[0] < b[0] || (a[0] === b[0] && a[1] < b[1]), lab: v => (v[0] ? (v[1] ? 'ω+' + v[1] : 'ω') : String(v[1])), eq: (a, b) => a[0] === b[0] && a[1] === b[1] },
    Z: { wo: false, less: (a, b) => a < b, lab: v => String(v), eq: (a, b) => a === b },
    Q: { wo: false, less: (a, b) => a[0] * b[1] < b[0] * a[1], lab: fracStr, eq: (a, b) => a[0] === b[0] && a[1] === b[1] },
  };
  function points() {
    const last = seq[seq.length - 1];
    if (mode === 'N') return Array.from({ length: 22 }, (_, n) => ({ v: n, x: 40 + n * 38, lab: true }));
    if (mode === 'W2') {
      const out = [];
      for (let c = 0; c < 2; c++) for (let n = 0; n < 18; n++) out.push({ v: [c, n], x: 40 + c * 430 + 390 * (1 - Math.pow(0.8, n)), r: 8 * Math.pow(0.93, n), lab: n < 6 });
      return out;
    }
    if (mode === 'Z') { const c = last ?? 6; return Array.from({ length: 21 }, (_, k) => ({ v: c - 14 + k, x: 40 + k * 41, lab: true })); }
    const cur = last ?? [1n, 1n];
    return Array.from({ length: 13 }, (_, j) => ({ v: frac(cur[0] * BigInt(j), cur[1] * 12n), x: 40 + j * 66, lab: j % 2 === 0 || j === 12 }));
  }
  function render() {
    svg.innerHTML = '';
    arrowDefs(svg, 'chArr', COL.meta);
    const m = M[mode];
    const pts = points();
    const last = seq[seq.length - 1];
    el('line', { x1: 20, x2: 880, y1: Y, y2: Y, stroke: '#cfc9b8', 'stroke-width': 2 }, svg);
    if (mode === 'N' || mode === 'W2') svgText(svg, 884, Y + 5, '…', { 'font-size': 16, fill: COL.muted });
    if (mode === 'W2') svgText(svg, 448, Y + 5, '…', { 'font-size': 16, fill: COL.muted });
    if (mode === 'Z') { svgText(svg, 8, Y + 5, '…', { 'font-size': 16, fill: COL.muted }); svgText(svg, 884, Y + 5, '…', { 'font-size': 16, fill: COL.muted }); }
    if (mode === 'Q') svgText(svg, 880, 24, `window · 窗口 [0, ${last ? fracStr(last) : '1'}]`, { 'text-anchor': 'end', 'font-size': 12, fill: COL.muted });
    const chosenIdx = [];
    pts.forEach(p => {
      const k = seq.findIndex(s => m.eq(s, p.v));
      const ok = !busy && (seq.length === 0 || m.less(p.v, last));
      const r = p.r || 8;
      const c = el('circle', { cx: p.x, cy: Y, r, fill: k >= 0 ? COL.meta : '#fff', stroke: k >= 0 ? COL.meta : ok ? COL.accent : '#bbb', 'stroke-width': ok ? 2.5 : 1.5 }, svg);
      if (ok) {
        c.style.cursor = 'pointer';
        c.addEventListener('click', () => pick(p.v));
        const hit = el('circle', { cx: p.x, cy: Y, r: Math.max(r, 12), fill: 'transparent' }, svg);
        hit.style.cursor = 'pointer';
        hit.addEventListener('click', () => pick(p.v));
      }
      if (p.lab || k >= 0) svgText(svg, p.x, Y + 28, m.lab(p.v), { 'text-anchor': 'middle', 'font-size': 12, fill: k >= 0 ? COL.meta : '#555', 'font-weight': k >= 0 ? 700 : 400 });
      if (k >= 0) { chosenIdx.push({ k, x: p.x }); svgText(svg, p.x, Y + 4, k, { 'text-anchor': 'middle', 'font-size': 10, fill: '#fff', 'font-weight': 700 }); }
    });
    chosenIdx.sort((a, b) => a.k - b.k);
    for (let i = 1; i < chosenIdx.length; i++) {
      const a = chosenIdx[i - 1], b = chosenIdx[i];
      if (b.k !== a.k + 1) continue;
      const h = Math.min(80, 18 + Math.abs(a.x - b.x) * 0.25);
      el('path', { d: `M${a.x},${Y - 11} Q${(a.x + b.x) / 2},${Y - 11 - h} ${b.x},${Y - 11}`, fill: 'none', stroke: COL.meta, 'stroke-width': 2, 'marker-end': 'url(#chArr)' }, svg);
    }
    if (mode === 'W2') {
      svgText(svg, 235, 24, 'first copy of ω · 第一份 ω', { 'text-anchor': 'middle', 'font-size': 12, fill: COL.muted });
      svgText(svg, 665, 24, 'second copy of ω · 第二份 ω', { 'text-anchor': 'middle', 'font-size': 12, fill: COL.muted });
    }
    $('chainSeq').innerHTML = seq.map(v => m.lab(v)).join(' &gt; ') + (stuck() ? ' <span class="stop">⛔</span>' : seq.length ? ' &gt; ?' : '');
  }
  const stuck = () => {
    const last = seq[seq.length - 1];
    if (last === undefined) return false;
    if (mode === 'N') return last === 0;
    if (mode === 'W2') return last[0] === 0 && last[1] === 0;
    if (mode === 'Q') return last[0] === 0n;
    return false;
  };
  function message(v) {
    const box = $('chainMsg');
    if (mode === 'N') {
      if (v === 0) okBox(box, bi(`Stuck! 0 has nothing below it. Your chain had ${seq.length} elements, finite as always.`, `走不动了！0 下面什么都没有。你的链有 ${seq.length} 个元素，照例是有限的。`), 'warn');
      else okBox(box, bi(`At ${v}: whatever you do, you have <b>at most ${v} more steps</b>.`, `现在在 ${v}：不管怎么走，<b>至多还能走 ${v} 步</b>。`), 'info');
    } else if (mode === 'W2') {
      if (v[0] === 1) okBox(box, bi('You are in the second copy. From here you may drop into the first copy at any number, as large as you like. But that drop happens <b>once</b>, and then you are back in ℕ.', '你在第二份 ω 里。从这里可以跳回第一份中任意大的数，但这样的跳跃只能有<b>一次</b>，之后你就回到了 ℕ 里。'), 'info');
      else if (v[1] === 0) okBox(box, bi(`Stuck at 0 after ${seq.length} elements. Every descending chain in ω+ω is finite, but there is no fixed bound on its length.`, `走了 ${seq.length} 个元素后停在 0。ω+ω 中每条降链都有限，只是长度没有统一的上界。`), 'warn');
      else okBox(box, bi(`Back in the first copy at ${v[1]}: at most ${v[1]} more steps.`, `回到第一份，位于 ${v[1]}：至多再走 ${v[1]} 步。`), 'info');
    } else if (mode === 'Z') {
      okBox(box, bi(`There is always ${v - 1} below ${v}. The chain ${v} &gt; ${v - 1} &gt; ${v - 2} &gt; ⋯ never stops: ℤ is <b>not</b> well-ordered (ℤ itself has no least element).`, `${v} 下面永远有 ${v - 1}。降链 ${v} &gt; ${v - 1} &gt; ${v - 2} &gt; ⋯ 永不停止：ℤ <b>不是</b>良序（ℤ 本身就没有最小元）。`), 'bad');
    } else {
      if (v[0] === 0n) okBox(box, bi('You picked 0 and got stuck, but only because you chose to. Halving forever (1 &gt; 1/2 &gt; 1/4 &gt; ⋯) never stops, so ℚ ∩ [0,1] is <b>not</b> a well-order: the subset {1/2ⁿ} has no least element.', '你选了 0 所以停住了，但这是你自己选的。一直减半（1 &gt; 1/2 &gt; 1/4 &gt; ⋯）永远不会停，所以 ℚ ∩ [0,1] <b>不是</b>良序：子集 {1/2ⁿ} 没有最小元。'), 'warn');
      else okBox(box, bi(`The window is now [0, ${fracStr(v)}], zoomed in, and there are 11 rational points strictly between 0 and ${fracStr(v)}. You can keep going forever.`, `窗口放大为 [0, ${fracStr(v)}]，0 与 ${fracStr(v)} 之间依然有 11 个有理点可选，你可以永远走下去。`), 'bad');
    }
  }
  function pick(v) {
    const m = M[mode], last = seq[seq.length - 1];
    if (seq.length && !m.less(v, last)) return;
    seq.push(v);
    render();
    message(v);
  }
  async function auto() {
    if (busy) return;
    busy = 1;
    for (let step = 0; step < 14 && !stuck(); step++) {
      const m = M[mode], last = seq[seq.length - 1];
      let cand = points().filter(p => seq.length === 0 || m.less(p.v, last));
      if (mode === 'Q') cand = cand.filter(p => p.v[0] !== 0n);
      if (!seq.length) cand = cand.slice(-4);
      if (!cand.length) break;
      const p = cand[Math.floor(Math.random() * cand.length)];
      seq.push(p.v);
      render();
      message(p.v);
      await sleep(420);
    }
    busy = 0;
    render();
    if (!M[mode].wo) okBox($('chainMsg'), bi('…and it could go on like this forever. No well-order allows that.', '……而且可以这样一直走下去。良序不允许这种事发生。'), 'bad');
  }
  document.querySelectorAll('#chainModes [data-mode]').forEach(b => b.addEventListener('click', () => {
    if (busy) return;
    document.querySelectorAll('#chainModes [data-mode]').forEach(x => x.classList.toggle('sel', x === b));
    mode = b.dataset.mode;
    seq = [];
    clearBox($('chainMsg'));
    render();
    if (mode === 'W2') okBox($('chainMsg'), bi('Tip: start high, in the second copy.', '提示：从高处开始，先选第二份 ω 里的点。'), 'info');
  }));
  $('chainReset').addEventListener('click', () => { if (busy) return; seq = []; clearBox($('chainMsg')); render(); });
  $('chainAuto').addEventListener('click', auto);
  render();
})();

/* ================= §2 matchsticks ================= */
(function matchsticks() {
  const view = OrdView($('stickStage'), { h: 170 });
  const presets = ['w', 'w+1', 'w+2', 'w*2', 'w*3', 'w^2', 'w^2+w*2+3', 'w^3', 'w^w', 'w^w^w'];
  let cur = 'w^2';
  presets.forEach(p => {
    const b = document.createElement('button');
    b.className = 'btn small' + (p === cur ? ' sel' : '');
    b.innerHTML = `<span class="m">${ORD.toHTML(ORD.parse(p))}</span>`;
    b.addEventListener('click', () => {
      cur = p;
      $('stickPresets').querySelectorAll('button').forEach(x => x.classList.toggle('sel', x === b));
      view.show(ORD.parse(p), true);
    });
    $('stickPresets').appendChild(b);
  });
  view.show(ORD.parse(cur), true);
  $('stickPlay').addEventListener('click', () => view.show(ORD.parse(cur), true));
  $('stickOut').addEventListener('click', () => view.zoomOut());
  $('stickReset').addEventListener('click', () => view.reset());
})();

/* ================= §3 von Neumann ================= */
(function vonNeumann() {
  const A = ORD.parse('w*2+3');
  const vn = n => (n === 0 ? '∅' : '{' + Array.from({ length: n }, (_, k) => vn(k)).join(', ') + '}');
  function elementsText(a) {
    // segments [0,ω), [ω,ω·2), [ω·2, ω·2+3)
    const segs = [[], ORD.W, ORD.parse('w*2')];
    const parts = [];
    for (const s of segs) {
      if (ORD.cmp(a, s) <= 0) break;
      const names = k => ORD.toStr(ORD.add(s, ORD.nat(k)));
      const nextSeg = segs[segs.indexOf(s) + 1];
      if (nextSeg && ORD.cmp(a, nextSeg) >= 0) parts.push(`${names(0)}, ${names(1)}, ${names(2)}, …`);
      else {
        const k = ORD.isFin(a) ? ORD.finVal(a) : ORD.finVal([a[a.length - 1]].filter(t => !t[0].length)) || 0;
        const list = k <= 4 ? Array.from({ length: k }, (_, i) => names(i)).join(', ') : `${names(0)}, ${names(1)}, …, ${names(k - 1)}`;
        if (list) parts.push(list);
      }
    }
    return parts.length ? '{' + parts.join(', ') + '}' : '∅';
  }
  const view = OrdView($('vnStage'), {
    h: 150, maxLabels: 16,
    hint: `<span class="k">${bil('Click a stick', '点击一根火柴')}</span>`,
    onPick(s, api) {
      api.sticks.forEach(t => t.ln && t.ln.setAttribute('stroke', ORD.cmp(t.ord, s.ord) < 0 ? COL.tru : ORD.eq(t.ord, s.ord) ? COL.fal : '#d0ccc0'));
      const a = s.ord, nm = ORD.toHTML(a);
      let h = `<b class="m">${nm} = {β : β &lt; ${nm}} = ${elementsText(a)}</b><br>`;
      if (ORD.isFin(a) && ORD.finVal(a) <= 4) h += `<span class="m">${nm} = ${vn(ORD.finVal(a))}</span><br>`;
      if (ORD.isZero(a)) h += bi('<b>Zero:</b> the empty set. No elements, so no green sticks.', '<b>零：</b>空集。它没有元素，所以没有绿色火柴。');
      else if (ORD.isSucc(a)) { const p = ORD.toHTML(ORD.pred(a)); h += bi(`<b>Successor:</b> ${nm} = ${p} ∪ {${p}}. It has a largest element, ${p}.`, `<b>后继序数：</b>${nm} = ${p} ∪ {${p}}，它有最大元 ${p}。`); }
      else h += bi(`<b>Limit:</b> the green sticks have no largest one; ${nm} = ⋃${nm} = sup of everything below it.`, `<b>极限序数：</b>绿色火柴中没有最大的一根；${nm} = ⋃${nm} = 它下面所有序数的上确界。`);
      okBox($('vnInfo'), h, 'info');
    },
  });
  view.show(A, false);
  okBox($('vnInfo'), bi('Click a stick above. The picture is ω·2+3 = {0, 1, …, ω, ω+1, …, ω·2, ω·2+1, ω·2+2}.', '点击上面的火柴。图中画的是 ω·2+3 = {0, 1, …, ω, ω+1, …, ω·2, ω·2+1, ω·2+2}。'), 'info');

  // hereditarily finite set builder
  const mk = els => {
    const u = new Map();
    els.forEach(e => u.set(e.k, e));
    const arr = [...u.values()].sort((a, b) => (a.k < b.k ? -1 : a.k > b.k ? 1 : 0));
    return { k: '{' + arr.map(e => e.k).join(',') + '}', els: arr };
  };
  const V = [mk([])];
  for (let n = 1; n <= 5; n++) V.push(mk(V.slice(0, n)));
  const rank = x => x.els.reduce((r, e) => Math.max(r, rank(e) + 1), 0);
  const name = x => { const n = V.findIndex(v => v.k === x.k); return n >= 0 ? String(n) : '{' + x.els.slice().sort((a, b) => rank(a) - rank(b)).map(name).join(',') + '}'; };
  const has = (S, x) => S.some(e => e.k === x.k);
  const palette = [V[0], V[1], V[2], V[3], mk([V[1]]), mk([V[2]]), mk([V[0], V[2]])];
  const on = palette.map((_, i) => i < 3);
  const svg = $('hfSvg');
  function draw() {
    const S = palette.filter((_, i) => on[i]).sort((a, b) => rank(a) - rank(b) || (name(a) < name(b) ? -1 : 1));
    svg.innerHTML = '';
    arrowDefs(svg, 'hfA', '#7b8494');
    arrowDefs(svg, 'hfR', COL.fal);
    const n = S.length, Y = 128;
    const pos = new Map();
    S.forEach((x, i) => pos.set(x.k, n === 1 ? 450 : 90 + i * (720 / Math.max(1, n - 1))));
    // membership arcs
    S.forEach(y => S.forEach(x => {
      if (!has(y.els, x)) return;
      const x1 = pos.get(x.k), x2 = pos.get(y.k), hgt = Math.min(100, 16 + Math.abs(x2 - x1) * 0.2);
      el('path', { d: `M${x1},${Y - 16} Q${(x1 + x2) / 2},${Y - 16 - hgt} ${x2 - (x2 > x1 ? 6 : -6)},${Y - 17}`, fill: 'none', stroke: '#7b8494', 'stroke-width': 1.6, 'marker-end': 'url(#hfA)' }, svg);
    }));
    // ghosts: elements of elements missing from S
    const ghosts = new Map();
    S.forEach(x => x.els.forEach(z => { if (!has(S, z)) { if (!ghosts.has(z.k)) ghosts.set(z.k, { z, to: [] }); ghosts.get(z.k).to.push(x); } }));
    let gi = 0;
    ghosts.forEach(gh => {
      const gx = 160 + gi++ * 170, gy = 196;
      gh.to.forEach(x => el('line', { x1: gx, y1: gy - 14, x2: pos.get(x.k), y2: Y + 16, stroke: COL.fal, 'stroke-width': 1.6, 'stroke-dasharray': '5 4', 'marker-end': 'url(#hfR)' }, svg));
      const w = name(gh.z).length * 9 + 22;
      el('rect', { x: gx - w / 2, y: gy - 14, width: w, height: 28, rx: 8, fill: COL.fal + '18', stroke: COL.fal, 'stroke-dasharray': '4 3' }, svg);
      svgText(svg, gx, gy + 5, name(gh.z), { 'text-anchor': 'middle', 'font-size': 14, fill: COL.fal, 'font-weight': 700 });
    });
    S.forEach(x => {
      const cx = pos.get(x.k), w = name(x).length * 9 + 24;
      el('rect', { x: cx - w / 2, y: Y - 16, width: w, height: 32, rx: 9, fill: '#fff', stroke: COL.accent, 'stroke-width': 2 }, svg);
      svgText(svg, cx, Y + 5, name(x), { 'text-anchor': 'middle', 'font-size': 15, 'font-weight': 700 });
    });
    if (!n) svgText(svg, 450, Y + 5, 'S = ∅', { 'text-anchor': 'middle', 'font-size': 18, fill: COL.gold, 'font-weight': 700 });
    svgText(svg, 10, 20, 'x → y  means  x ∈ y', { 'font-size': 12, fill: COL.muted });
    const trans = ghosts.size === 0;
    let lin = true;
    for (let i = 0; i < n; i++) for (let j = i + 1; j < n; j++) if (!has(S[i].els, S[j]) && !has(S[j].els, S[i])) lin = false;
    const vd = (ok, en, zh) => `<span class="verdict ${ok ? 'y' : 'n'}">${ok ? '✓' : '✗'} ${bi(en, zh)}</span>`;
    let h = vd(trans, 'transitive', '传递') + vd(lin, 'any two elements comparable by ∈', '任两元素可用 ∈ 比较');
    h += trans && lin ? vd(true, `ordinal: S = ${n}`, `是序数：S = ${n}`) : vd(false, 'not an ordinal', '不是序数');
    $('hfVerdict').innerHTML = h;
  }
  palette.forEach((x, i) => {
    const c = document.createElement('div');
    c.className = 'chip hfchip' + (on[i] ? ' on' : '');
    c.textContent = name(x);
    c.title = x.els.length ? 'elements: ' + x.els.map(name).join(', ') : 'empty set';
    c.addEventListener('click', () => { on[i] = !on[i]; c.classList.toggle('on', on[i]); draw(); });
    $('hfPalette').appendChild(c);
  });
  draw();
})();

/* ================= §4 order type matching ================= */
(function isoMatch() {
  const svg = $('isoSvg');
  const P = ORD.parse, nat = ORD.nat, add = ORD.add;
  const base = 300, H = 62;
  const ex = [
    { en: 'ℕ, evens before odds', zh: 'ℕ，偶数排在奇数前', T: P('w*2'),
      els: () => Array.from({ length: 18 }, (_, n) => ({ x: 40 + n * 48, y: 80, lab: String(n), ord: n % 2 ? add(ORD.W, nat((n - 1) / 2)) : nat(n / 2) })),
      note: { en: 'Order: 0 ◁ 2 ◁ 4 ◁ ⋯ ◁ 1 ◁ 3 ◁ 5 ◁ ⋯', zh: '序：0 ◁ 2 ◁ 4 ◁ ⋯ ◁ 1 ◁ 3 ◁ 5 ◁ ⋯' } },
    { en: 'ℕ, with 0 moved to the end', zh: 'ℕ，把 0 挪到最后', T: P('w+1'),
      els: () => Array.from({ length: 18 }, (_, n) => ({ x: 40 + n * 48, y: 80, lab: String(n), ord: n ? nat(n - 1) : ORD.W })),
      note: { en: 'Order: 1 ◁ 2 ◁ 3 ◁ ⋯ ◁ 0', zh: '序：1 ◁ 2 ◁ 3 ◁ ⋯ ◁ 0' } },
    { en: '{k − 1/n : k = 1, 2; n ≥ 1} ∪ {2} ⊂ ℝ', zh: '{k − 1/n : k = 1, 2; n ≥ 1} ∪ {2} ⊂ ℝ', T: P('w*2+1'), real: true,
      els: () => {
        const out = [];
        for (let k = 1; k <= 2; k++) for (let n = 1; n <= 14; n++) out.push({ x: 40 + (k - 1 / n) * 410, y: 80, lab: '', ord: add(k === 2 ? ORD.W : [], nat(n - 1)) });
        out.push({ x: 40 + 2 * 410, y: 80, lab: '', ord: P('w*2') });
        return out;
      },
      note: { en: 'Usual order of the reals', zh: '取实数的通常序' } },
    { en: 'ℕ × ℕ, lexicographic', zh: 'ℕ × ℕ，字典序', T: P('w^2'),
      els: () => {
        const out = [];
        const cx = a => 40 + 810 * ((1 - Math.pow(0.64, a)) + (1 - Math.pow(0.64, a + 1))) / 2 - 14;
        for (let a = 0; a < 4; a++) for (let b = 0; b < 10; b++) out.push({ x: cx(a), y: 34 + b * 13.5, lab: `(${a},${b})`, side: true, ord: add(ORD.mul(ORD.W, nat(a)), nat(b)) });
        return out;
      },
      note: { en: '(a,b) ◁ (c,d) ⇔ a &lt; c, or a = c and b &lt; d', zh: '(a,b) ◁ (c,d) ⇔ a &lt; c，或 a = c 且 b &lt; d' } },
    { en: 'Five words, alphabetical', zh: '五个单词，按字母序', T: nat(5),
      els: () => ['pear', 'apple', 'kiwi', 'fig', 'lime'].map((w, i) => ({ x: 110 + i * 170, y: 80, lab: w, ord: nat(['apple', 'fig', 'kiwi', 'lime', 'pear'].indexOf(w)) })),
      note: { en: 'apple ◁ fig ◁ kiwi ◁ lime ◁ pear', zh: 'apple ◁ fig ◁ kiwi ◁ lime ◁ pear' } },
  ];
  let cur = 0, els = [], order = [], k = 0, sticks = [], gLines = null, token = 0;
  function setup() {
    token++;
    const E = ex[cur];
    svg.innerHTML = '';
    els = E.els();
    order = els.slice().sort((a, b) => ORD.cmp(a.ord, b.ord));
    k = 0;
    svgText(svg, 20, 16, cur === 3 ? 'given well-order: column a holds (a,0), (a,1), … · 给定的良序：第 a 列是 (a,0), (a,1), …' : 'given well-order · 给定的良序', { 'font-size': 12, fill: COL.muted });
    svgText(svg, 20, base - H - 22, 'ordinal · 序数', { 'font-size': 12, fill: COL.muted });
    if (E.real) {
      el('line', { x1: 30, x2: 870, y1: 80, y2: 80, stroke: '#cfc9b8', 'stroke-width': 1.5 }, svg);
      [['0', 0], ['1/2', 0.5], ['1', 1], ['3/2', 1.5], ['2', 2]].forEach(([s, v]) => svgText(svg, 40 + v * 410, 104, s, { 'text-anchor': 'middle', 'font-size': 11, fill: COL.muted }));
    }
    gLines = el('g', {}, svg);
    els.forEach(e => {
      e.dot = el('circle', { cx: e.x, cy: e.y, r: E.real || e.side ? 4 : 6, fill: '#fff', stroke: COL.ink, 'stroke-width': 1.6 }, svg);
      if (e.side) svgText(svg, e.x + 8, e.y + 3.5, e.lab, { 'font-size': 9.5, fill: '#444' });
      else if (e.lab) svgText(svg, e.x, e.y - 11, e.lab, { 'text-anchor': 'middle', 'font-size': 12, fill: '#444' });
    });
    el('line', { x1: 30, x2: 880, y1: base, y2: base, stroke: '#cfc9b8' }, svg);
    sticks = [];
    drawOrdinal(svg, E.T, { X0: 40, X1: 850, base, H, sticks });
    labelSticks(svg, sticks, base, { max: 20 });
    okBox($('isoMsg'), bi(`${E.note.en}<br>Press “Next element”: the least element not yet matched goes to the least ordinal not yet used.`, `${E.note.zh}<br>按“下一个元素”：尚未配对的最小元素，送到尚未使用的最小序数。`), 'info');
  }
  function stickFor(o) { return sticks.find(s => ORD.eq(s.ord, o)); }
  function step() {
    if (k >= order.length) return false;
    const e = order[k++];
    const s = stickFor(e.ord);
    const c = ordColor(e.ord);
    e.dot.setAttribute('fill', c);
    e.dot.setAttribute('stroke', c);
    if (s) {
      const ln = el('line', { x1: e.x, y1: e.y + (e.side ? 4 : 6), x2: s.x, y2: base - s.h - 2, stroke: c, 'stroke-width': ORD.isLimit(e.ord) ? 2.4 : 1.2, opacity: ORD.isLimit(e.ord) ? 0.9 : 0.55 }, gLines);
      ln.classList.add('fadein');
    }
    const nm = ORD.toHTML(e.ord), lab = e.lab || bil('this point', '该点');
    let h = `<span class="m">f(${lab}) = {f(y) : y ◁ ${lab}} = <b>${nm}</b></span>`;
    if (ORD.isLimit(e.ord)) h += '<br>' + bi('A <b>limit</b>: an entire infinite run lies below this element, with no largest member, so it goes to the limit ordinal.', '<b>极限</b>：它下面是一整段无穷序列，其中没有最大者，因此它被送到极限序数。');
    if (k === order.length) h += '<br>' + bi(`(Only the first few elements of each infinite run are drawn.) The order type is <b>${ORD.toHTML(ex[cur].T)}</b>.`, `（每段无穷序列只画了前几个元素。）序型是 <b>${ORD.toHTML(ex[cur].T)}</b>。`);
    okBox($('isoMsg'), h, 'info');
    return true;
  }
  ex.forEach((E, i) => {
    const b = document.createElement('button');
    b.className = 'btn small' + (i === cur ? ' sel' : '');
    b.innerHTML = E.en === E.zh ? E.en : bil(E.en, E.zh);
    b.addEventListener('click', () => { cur = i; $('isoPick').querySelectorAll('button').forEach(x => x.classList.toggle('sel', x === b)); setup(); });
    $('isoPick').appendChild(b);
  });
  $('isoNext').addEventListener('click', () => { token++; step(); });
  $('isoReset').addEventListener('click', setup);
  $('isoPlay').addEventListener('click', async () => {
    const my = ++token;
    while (my === token && step()) await sleep(order.length > 20 ? 110 : 380);
  });
  setup();
  stepper('isoSteps', 'isoStepNext', 'isoStepAll');
})();

/* ================= §5 arithmetic pictures ================= */
(function arithmetic() {
  const opts = ['1', '2', 'w', 'w+1', 'w*2'];
  let A = '1', B = 'w', op = '+';
  const BLUE = COL.accent, ORANGE = COL.orange;
  function buttons(boxId, list, get, set) {
    const box = $(boxId);
    box.innerHTML = '';
    list.forEach(v => {
      const b = document.createElement('button');
      b.className = 'btn small' + (v === get() ? ' sel' : '');
      b.innerHTML = `<span class="m">${v === '+' || v === '·' ? v : ORD.toHTML(ORD.parse(v))}</span>`;
      b.addEventListener('click', () => { set(v); draw(); });
      box.appendChild(b);
    });
  }
  function draw() {
    buttons('arA', opts, () => A, v => (A = v));
    buttons('arOp', ['+', '·'], () => op, v => (op = v));
    buttons('arB', opts, () => B, v => (B = v));
    const a = ORD.parse(A), b = ORD.parse(B);
    const res = op === '+' ? ORD.add(a, b) : ORD.mul(a, b);
    const rev = op === '+' ? ORD.add(b, a) : ORD.mul(b, a);
    // construction
    const s1 = $('arBuild');
    s1.innerHTML = '';
    const base = 84, H = 56;
    el('line', { x1: 20, x2: 880, y1: base, y2: base, stroke: '#cfc9b8' }, s1);
    if (op === '+') {
      const wa = ordWeight(a), wb = ordWeight(b), split = 40 + 800 * wa / (wa + wb);
      drawOrdinal(s1, a, { X0: 40, X1: split - 14, base, H, color: () => BLUE });
      drawOrdinal(s1, b, { X0: split, X1: 850, base, H, color: () => ORANGE });
      svgText(s1, 40, 18, `α = ${ORD.toStr(a)}`, { 'font-size': 13, fill: BLUE, 'font-weight': 700 });
      svgText(s1, split, 18, `then β = ${ORD.toStr(b)} · 再接 β`, { 'font-size': 13, fill: ORANGE, 'font-weight': 700 });
    } else {
      let copy = 0;
      drawOrdinal(s1, b, {
        X0: 40, X1: 850, base, H,
        leaf(g, x0, x1, ord, h) {
          const col = copy++ % 2 ? ORANGE : BLUE;
          if (x1 - x0 < 4) { el('line', { x1: x0, x2: x0, y1: base, y2: base - h, stroke: col, 'stroke-width': 1.2 }, g); return; }
          el('rect', { x: x0 - 2, y: base + 4, width: (x1 - x0) * 0.84 + 4, height: 4, rx: 2, fill: col, opacity: 0.35 }, g);
          drawOrdinal(g, a, { X0: x0, X1: x0 + (x1 - x0) * 0.8, base, H: h, color: () => col });
        },
      });
      svgText(s1, 40, 18, `β = ${ORD.toStr(b)} copies of α = ${ORD.toStr(a)} · 共 β 份 α（交替着色）`, { 'font-size': 13, fill: COL.ink, 'font-weight': 700 });
    }
    // normal form
    const s2 = $('arNorm');
    s2.innerHTML = '';
    el('line', { x1: 20, x2: 880, y1: base, y2: base, stroke: '#cfc9b8' }, s2);
    const st = [];
    drawOrdinal(s2, res, { X0: 40, X1: 850, base, H, sticks: st, color: op === '+' ? (o => (ORD.cmp(o, a) < 0 ? BLUE : ORANGE)) : undefined });
    labelSticks(s2, st, base, { max: 14 });
    svgText(s2, 40, 18, `α ${op} β = ${ORD.toStr(res)}`, { 'font-size': 13, fill: COL.ink, 'font-weight': 700 });
    // message
    const nA = ORD.toHTML(a), nB = ORD.toHTML(b), R = ORD.toHTML(res), R2 = ORD.toHTML(rev);
    let h = `<span class="m"><b>${paren(a)} ${op} ${paren(b)} = ${R}</b> &nbsp; ${bil('but', '而')} &nbsp; ${paren(b)} ${op} ${paren(a)} = ${R2}</span> &nbsp; ${ORD.eq(res, rev) ? bil('(equal here)', '（这里相等）') : `<b style="color:var(--false)">${bil('not commutative!', '不交换！')}</b>`}<br>`;
    const key = `${A}${op}${B}`;
    const notes = {
      '1+w': ['The extra stick in front is absorbed: relabel it as 0 and the old 0, 1, 2, … as 1, 2, 3, …, and the picture is ω again. So 1 + ω = ω. But ω + 1 ≠ ω: ω + 1 has a largest element and ω does not.', '前面多出来的那根火柴被“吸收”了：把它重新编号为 0，原来的 0, 1, 2, … 依次改为 1, 2, 3, …，图形又变回 ω。所以 1 + ω = ω。但 ω + 1 ≠ ω：ω + 1 有最大元，而 ω 没有。'],
      'w+1': ['The new stick sits <i>after</i> all of ω, with nothing to absorb it. ω + 1 has a largest element, ω does not, so they are not isomorphic.', '新加的火柴排在整个 ω <i>之后</i>，没有谁能把它吸收。ω + 1 有最大元而 ω 没有，二者不同构。'],
      '2·w': ['ω copies of a pair: (0,1), (2,3), (4,5), … is just one ω-sequence. So 2 · ω = ω, whereas ω · 2 = ω + ω.', 'ω 份“一对”：(0,1), (2,3), (4,5), … 连起来还是一条 ω 序列。所以 2 · ω = ω，而 ω · 2 = ω + ω。'],
      'w·2': ['Two copies of ω, one after the other: the start of the second copy is a limit point. ω · 2 = ω + ω ≠ ω.', '两份 ω 首尾相接：第二份的起点是一个极限点。ω · 2 = ω + ω ≠ ω。'],
    };
    if (notes[key]) h += bi(notes[key][0], notes[key][1]);
    else h += bi('Top: the literal construction. Bottom: the same order redrawn in Cantor normal form.', '上图：字面构造；下图：同一个序按康托尔范式重画。');
    okBox($('arMsg'), h, 'info');
  }
  $('arSwap').addEventListener('click', () => { [A, B] = [B, A]; draw(); });
  draw();
})();

/* ================= §6 CNF calculator ================= */
(function calculator() {
  const view = OrdView($('cnfStage'), { h: 160 });
  let op = '+';
  const OPS = [['+', '+'], ['·', '*'], ['^', '^']];
  OPS.forEach(([lab]) => {
    const b = document.createElement('button');
    b.className = 'btn small' + (lab === op ? ' sel' : '');
    b.innerHTML = `<span class="m" style="font-size:17px">${lab}</span>`;
    b.dataset.op = lab;
    b.addEventListener('click', () => { op = lab; paintOps(); run(); });
    $('cnfOps').appendChild(b);
  });
  const paintOps = () => $('cnfOps').querySelectorAll('button').forEach(b => b.classList.toggle('sel', b.dataset.op === op));
  const presets = [['1', '+', 'w'], ['w', '+', '1'], ['2', '·', 'w'], ['w', '·', '2'], ['w+1', '·', '2'], ['w+1', '^', '2'], ['2', '^', 'w+1'], ['w^2+w', '·', 'w+3'], ['w+1', '^', 'w'], ['w', '^', 'w^w']];
  presets.forEach(([a, o, b]) => {
    const btn = document.createElement('button');
    btn.className = 'btn small';
    const pa = ORD.parse(a), pb = ORD.parse(b);
    btn.innerHTML = `<span class="m">${o === '^' ? `${paren(pa)}<sup>${ORD.toHTML(pb)}</sup>` : `${paren(pa)} ${o} ${paren(pb)}`}</span>`;
    btn.addEventListener('click', () => { $('cnfA').value = a; $('cnfB').value = b; op = o; paintOps(); run(); });
    $('cnfPresets').appendChild(btn);
  });
  function apply(o, a, b) { return o === '+' ? ORD.add(a, b) : o === '·' ? ORD.mul(a, b) : ORD.pow(a, b); }
  function run() {
    let a, b, r;
    try {
      a = ORD.parse($('cnfA').value);
      b = ORD.parse($('cnfB').value);
      r = apply(op, a, b);
      clearBox($('cnfErr'));
    } catch (e) {
      okBox($('cnfErr'), e instanceof ParseError ? e.html() : String(e), 'bad');
      return;
    }
    const nA = ORD.toHTML(a), nB = ORD.toHTML(b);
    const show = (x, y) => (op === '^' ? `${paren(x)}<sup>${ORD.toHTML(y)}</sup>` : `${paren(x)} ${op} ${paren(y)}`);
    $('cnfRes').innerHTML = `${show(a, b)} = <b style="color:var(--accent)">${ORD.toHTML(r)}</b>`;
    const c = ORD.cmp(a, b);
    let h = `α = ${nA} &nbsp; ${c < 0 ? '&lt;' : c > 0 ? '&gt;' : '='} &nbsp; β = ${nB}`;
    try {
      const rv = apply(op, b, a);
      h += ` &nbsp;·&nbsp; ${bil('swapped', '交换后')}: ${show(b, a)} = ${ORD.toHTML(rv)} ${ORD.eq(rv, r) ? '' : `<b style="color:var(--false)">≠</b>`}`;
    } catch (e) { /* swapped value too large */ }
    h += ` &nbsp;·&nbsp; ${ORD.isZero(r) ? bil('zero', '零') : ORD.isLimit(r) ? bil('limit ordinal', '极限序数') : bil('successor ordinal', '后继序数')}`;
    $('cnfCmp').innerHTML = h;
    view.show(r, true);
  }
  ['cnfA', 'cnfB'].forEach(id => $(id).addEventListener('keydown', e => e.key === 'Enter' && run()));
  ['cnfA', 'cnfB'].forEach(id => $(id).addEventListener('input', run));
  $('cnfOut').addEventListener('click', () => view.zoomOut());
  $('cnfReset').addEventListener('click', () => view.reset());
  run();
})();

/* ================= §7 staircase ================= */
(function staircase() {
  const svg = $('stairSvg');
  const P = ORD.parse, nat = ORD.nat, add = ORD.add;
  const rules = {
    pow2: { lab: 'F(β) = 2<sup>β</sup>', f: b => ORD.pow(nat(2), b),
      base: 'F(0) = 1', succ: 'F(β+1) = F(β)·2' },
    wtimes: { lab: 'F(β) = ω·β', f: b => ORD.mul(ORD.W, b),
      base: 'F(0) = 0', succ: 'F(β+1) = F(β) + ω' },
    oneplus: { lab: 'F(β) = 1+β', f: b => add(ORD.ONE, b),
      base: 'F(0) = 1', succ: 'F(β+1) = F(β) + 1' },
  };
  let rule = 'pow2';
  // geometry
  const stairs = [];
  let x = 34, y = 292;
  function block(start, count, w0, r, dy0) {
    let w = w0, dy = dy0;
    for (let k = 0; k < count; k++) {
      stairs.push({ ord: add(start, nat(k)), x0: x, x1: x + w, y });
      x += w; y -= dy; w *= r; dy *= r;
    }
  }
  block([], 26, 60, 0.8, 15);
  block(ORD.W, 26, 60, 0.8, 15);
  block(P('w*2'), 4, 60, 0.82, 15);
  const climbs = ['0', '1', '2', '3', '4', '5', 'w', 'w+1', 'w+2', 'w+3', 'w*2', 'w*2+1', 'w*2+2'].map(P);
  const stepOf = o => stairs.find(s => ORD.eq(s.ord, o));
  let k = 0, climber = null, tagLayer = null;
  function draw() {
    svg.innerHTML = '';
    const d = ['M', stairs[0].x0, 305];
    stairs.forEach(s => { d.push('L', s.x0, s.y, 'L', s.x1, s.y); });
    d.push('L', stairs[stairs.length - 1].x1, 305, 'Z');
    el('path', { d: d.join(' '), fill: '#efece2', stroke: 'none' }, svg);
    stairs.forEach(s => {
      const c = ORD.isZero(s.ord) ? COL.gold : ORD.isLimit(s.ord) ? COL.meta : '#8a8f99';
      el('line', { x1: s.x0, x2: s.x1, y1: s.y, y2: s.y, stroke: c, 'stroke-width': ORD.isLimit(s.ord) || ORD.isZero(s.ord) ? 4 : 2 }, svg);
      if (s.x1 - s.x0 > 24) svgText(svg, (s.x0 + s.x1) / 2, s.y + 16, ORD.toStr(s.ord), { 'text-anchor': 'middle', 'font-size': 11, fill: c === '#8a8f99' ? '#555' : c, 'font-weight': c === '#8a8f99' ? 400 : 700 });
    });
    [stepOf(ORD.W), stepOf(P('w*2'))].forEach(s => {
      el('line', { x1: s.x0, x2: s.x0, y1: s.y, y2: 20, stroke: COL.meta, 'stroke-dasharray': '3 4', opacity: 0.5 }, svg);
    });
    svgText(svg, stepOf(ORD.W).x0 - 4, 30, 'limit · 极限', { 'text-anchor': 'end', 'font-size': 11, fill: COL.meta });
    tagLayer = el('g', {}, svg);
    climber = el('g', {}, svg);
    el('circle', { r: 9, fill: COL.accent }, climber);
    el('circle', { r: 3, cy: -2, cx: 2, fill: '#fff' }, climber);
    climber.style.transition = 'transform .45s cubic-bezier(.3,.9,.4,1)';
    move(stairs[0], false);
    $('stairLog').innerHTML = '';
  }
  function move(s, anim = true) {
    if (!anim) climber.style.transition = 'none';
    climber.style.transform = `translate(${(s.x0 + s.x1) / 2}px, ${s.y - 11}px)`;
    if (!anim) { void climber.getBoundingClientRect(); climber.style.transition = 'transform .45s cubic-bezier(.3,.9,.4,1)'; }
  }
  function visit(i) {
    const o = climbs[i], s = stepOf(o), R = rules[rule];
    const val = R.f(o);
    move(s);
    if (s.x1 - s.x0 > 30) svgText(tagLayer, (s.x0 + s.x1) / 2, s.y - 26, ORD.toStr(val), { 'text-anchor': 'middle', 'font-size': 11, fill: COL.accent, 'font-weight': 700 });
    let cls, h;
    const O = ORD.toHTML(o), V = ORD.toHTML(val);
    if (ORD.isZero(o)) { cls = 'case-base'; h = `<b>${bil('Base', '奠基')}</b> &nbsp; P(0) ✓ &nbsp;·&nbsp; ${R.base}`; }
    else if (ORD.isSucc(o)) { cls = 'case-succ'; h = `<b>${bil('Successor', '后继')}</b> &nbsp; P(${ORD.toHTML(ORD.pred(o))}) ⇒ P(${O}) &nbsp;·&nbsp; F(${O}) = ${V}`; }
    else {
      cls = 'case-lim';
      const st = ORD.eq(o, ORD.W) ? [] : ORD.W;
      const prev = [0, 1, 2].map(j => ORD.toHTML(R.f(add(st, nat(j))))).join(', ');
      h = `<b>${bil('Limit', '极限')}</b> &nbsp; ${bil(`P(β) for all β &lt; ${O}`, `对一切 β &lt; ${O} 有 P(β)`)} ⇒ P(${O}) &nbsp;·&nbsp; F(${O}) = sup{${prev}, …} = <b>${V}</b>`;
    }
    const d = document.createElement('div');
    d.className = cls + ' fadein';
    d.innerHTML = h;
    if (i === 6 || i === 10) {
      const j = document.createElement('div');
      j.className = 'case-succ';
      j.innerHTML = `<span class="muted">⋮ ${bil('infinitely many successor steps, each by the same argument', '无穷多个后继步，每一步论证都一样')}</span>`;
      $('stairLog').appendChild(j);
    }
    $('stairLog').appendChild(d);
    $('stairLog').scrollTop = 1e6;
  }
  function next() { if (k < climbs.length) visit(k++); $('stairNext').disabled = k >= climbs.length; }
  Object.entries(rules).forEach(([key, R]) => {
    const b = document.createElement('button');
    b.className = 'btn small' + (key === rule ? ' sel' : '');
    b.innerHTML = `<span class="m">${R.lab}</span> <span class="muted" style="font-size:12px">(${R.base}, ${R.succ})</span>`;
    b.addEventListener('click', () => { rule = key; $('stairRules').querySelectorAll('button').forEach(x => x.classList.toggle('sel', x === b)); reset(); });
    $('stairRules').appendChild(b);
  });
  function reset() { k = 0; draw(); $('stairNext').disabled = false; next(); }
  $('stairNext').addEventListener('click', next);
  $('stairAll').addEventListener('click', () => { while (k < climbs.length) next(); });
  $('stairReset').addEventListener('click', reset);
  reset();
  stepper('tiSteps', 'tiNext', 'tiAll');
})();

/* ================= §8 Burali–Forti ================= */
(function buraliForti() {
  const svg = $('bfSvg');
  const base = 150, H = 70;
  function draw(n) {
    svg.innerHTML = '';
    arrowDefs(svg, 'bfA', COL.fal);
    el('line', { x1: 20, x2: 860, y1: base, y2: base, stroke: '#cfc9b8', 'stroke-width': 1.5 }, svg);
    const st = [];
    drawOrdinal(svg, ORD.parse('w^w'), { X0: 30, X1: 470, base, H, sticks: st });
    labelSticks(svg, st, base, { max: 8 });
    // schematic continuation
    [[520, 'ω^ω', 0.8], [580, 'ε₀', 0.85], [660, 'ω₁', 1], [740, 'ω₂', 1]].forEach(([x, s, f]) => {
      el('line', { x1: x, x2: x, y1: base, y2: base - H * f, stroke: COL.meta, 'stroke-width': 2.4 }, svg);
      svgText(svg, x, base + 16, s, { 'text-anchor': 'middle', 'font-size': 12, fill: COL.meta, 'font-weight': 700 });
    });
    [490, 550, 620, 700, 780].forEach(x => svgText(svg, x, base - 10, '⋯', { 'text-anchor': 'middle', 'font-size': 14, fill: COL.muted }));
    svgText(svg, 892, base - 8, 'Ord →', { 'font-size': 13, fill: COL.muted, 'text-anchor': 'end' });
    if (n >= 1) {
      el('path', { d: `M30,${base - H - 18} L30,${base - H - 28} L800,${base - H - 28} L800,${base - H - 18}`, fill: 'none', stroke: COL.accent, 'stroke-width': 2 }, svg);
      svgText(svg, 415, base - H - 36, 'Ω = { all ordinals } — a set?  ·  全体序数之集？', { 'text-anchor': 'middle', 'font-size': 13, fill: COL.accent, 'font-weight': 700 });
    }
    if (n >= 2) svgText(svg, 30, 214, '✓ transitive: α ∈ Ω ⇒ α ⊆ Ω · 传递', { 'font-size': 13, fill: COL.tru, 'font-weight': 700 });
    if (n >= 3) {
      svgText(svg, 360, 214, '✓ well-ordered by ∈ ⇒ Ω is an ordinal · 是序数', { 'font-size': 13, fill: COL.tru, 'font-weight': 700 });
      const s = el('line', { x1: 830, x2: 830, y1: base, y2: base - H - 6, stroke: COL.fal, 'stroke-width': 4 }, svg);
      s.classList.add('fadein');
      svgText(svg, 830, base + 18, 'Ω', { 'text-anchor': 'middle', 'font-size': 16, fill: COL.fal, 'font-weight': 800 });
    }
    if (n >= 4) {
      el('path', { d: `M830,${base - H - 8} C 830,10 640,10 620,${base - H - 30}`, fill: 'none', stroke: COL.fal, 'stroke-width': 2.4, 'marker-end': 'url(#bfA)', 'stroke-dasharray': '6 4' }, svg);
      svgText(svg, 600, 30, 'Ω ∈ Ω  ⇒  Ω < Ω  ✗', { 'font-size': 16, fill: COL.fal, 'font-weight': 800, 'text-anchor': 'end' });
    }
  }
  const st = stepper('bfSteps', 'bfNext', 'bfAll', { onStep: draw });
  $('bfReset').addEventListener('click', () => st.reset());
  draw(0);
})();

/* ================= §9 Hartogs ================= */
(function hartogs() {
  const letters = ['a', 'b', 'c', 'd'];
  let n = 3;
  function perms(arr) { if (arr.length <= 1) return [arr]; return arr.flatMap((x, i) => perms([...arr.slice(0, i), ...arr.slice(i + 1)]).map(p => [x, ...p])); }
  function render() {
    const X = letters.slice(0, n);
    const groups = Array.from({ length: n + 1 }, () => []);
    for (let mask = 0; mask < (1 << n); mask++) {
      const A = X.filter((_, i) => mask >> i & 1);
      perms(A).forEach(p => groups[A.length].push(p));
    }
    let h = '';
    groups.forEach((g, t) => {
      h += `<div class="tcol fadein" style="animation-delay:${t * 0.15}s"><h4>${bil('type', '序型')} ${t} <span class="muted">(${g.length})</span></h4>`;
      h += g.map(p => `<span class="wo">${p.length ? p.join(' ◁ ') : '∅'}</span>`).join('');
      h += '</div>';
    });
    h += `<div class="tcol none fadein" style="animation-delay:${(n + 1) * 0.15}s"><h4>${bil('type', '序型')} ${n + 1}</h4>${bi('<b>none!</b> No subset of X is that long.', '<b>一个也没有！</b>X 没有那么长的子集。')}</div>`;
    $('hgCols').innerHTML = h;
    okBox($('hgMsg'), bi(`X = {${X.join(', ')}}. The types that occur are 0, …, ${n}, so H = {0, 1, …, ${n}} = <b>${n + 1}</b> = h(X). Indeed ${n + 1} does not inject into an ${n}-element set (pigeonhole). For infinite X nobody can list the well-orders like this, but Replacement still collects their types into a set.`,
      `X = {${X.join(', ')}}。出现的序型是 0, …, ${n}，所以 H = {0, 1, …, ${n}} = <b>${n + 1}</b> = h(X)。确实，${n + 1} 不能单射进 ${n} 元集（抽屉原理）。X 无穷时没法这样一一列出，但替换公理照样能把所有序型收集成一个集合。`), 'info');
  }
  [1, 2, 3].forEach(m => {
    const b = document.createElement('button');
    b.className = 'btn small' + (m === n ? ' sel' : '');
    b.innerHTML = `|X| = ${m}`;
    b.addEventListener('click', () => { n = m; $('hgN').querySelectorAll('button').forEach(x => x.classList.toggle('sel', x === b)); render(); });
    $('hgN').appendChild(b);
  });
  render();
  stepper('hgSteps', 'hgNext', 'hgAll');
})();

/* ================= E1 well-order or not ================= */
(function e1() {
  const items = [
    { s: bil('ℕ with the reversed order: ⋯ ◁ 2 ◁ 1 ◁ 0', 'ℕ 取逆序：⋯ ◁ 2 ◁ 1 ◁ 0'), wo: false,
      en: 'Not a well-order: 0 ▷ 1 ▷ 2 ▷ ⋯ is an infinite descending chain, and ℕ itself has no least element.', zh: '不是良序：0 ▷ 1 ▷ 2 ▷ ⋯ 是无穷降链，ℕ 本身就没有最小元。' },
    { s: bil('ℤ ordered as 0 ◁ −1 ◁ 1 ◁ −2 ◁ 2 ◁ ⋯', 'ℤ 按 0 ◁ −1 ◁ 1 ◁ −2 ◁ 2 ◁ ⋯ 排序'), wo: true,
      en: 'Well-order of type ω: it is ℤ listed as a sequence, and every element has only finitely many predecessors.', zh: '良序，序型 ω：这只是把 ℤ 排成一列，每个元素前面只有有限个元素。' },
    { s: bil('ℚ ∩ [0, ∞), usual order', 'ℚ ∩ [0, ∞)，通常序'), wo: false,
      en: 'Not a well-order: 1 &gt; 1/2 &gt; 1/3 &gt; ⋯. (It has a least element 0, but the subset of positive elements has none.)', zh: '不是良序：1 &gt; 1/2 &gt; 1/3 &gt; ⋯。（整个集合有最小元 0，但正元素构成的子集没有。）' },
    { s: bil('ℕ × ℕ, lexicographic order', 'ℕ × ℕ，字典序'), wo: true,
      en: 'Well-order of type ω²: a descending chain can lower the first coordinate only finitely often, and between two such drops the second coordinate only finitely often.', zh: '良序，序型 ω²：降链只能有限次降低第一个坐标，而在两次之间第二个坐标也只能下降有限次。' },
    { s: bil('finite 0/1-strings, dictionary order (ε &lt; 0 &lt; 00 &lt; ⋯ &lt; 01 &lt; ⋯ &lt; 1)', '有限 0/1 串，词典序（ε &lt; 0 &lt; 00 &lt; ⋯ &lt; 01 &lt; ⋯ &lt; 1）'), wo: false,
      en: 'Not a well-order: 1 &gt; 01 &gt; 001 &gt; 0001 &gt; ⋯. (Ordering by length first, then alphabetically, would give type ω.)', zh: '不是良序：1 &gt; 01 &gt; 001 &gt; 0001 &gt; ⋯。（若先按长度、再按字母排，就得到序型 ω。）' },
    { s: '{1 − 1/n : n ≥ 1} ∪ {1} ⊂ ℝ', wo: true,
      en: 'Well-order of type ω + 1: 0, 1/2, 2/3, … and then 1 on top.', zh: '良序，序型 ω + 1：0, 1/2, 2/3, …，最后是 1。' },
    { s: bil('any set of ordinals, ordered by ∈', '任意序数之集，按 ∈ 排序'), wo: true,
      en: 'Well-order: a nonempty set S of ordinals has least element ⋂S. (Its type can be any ordinal.)', zh: '良序：非空序数集 S 的最小元是 ⋂S。（它的序型可以是任何序数。）' },
  ];
  const solved = items.map(() => false);
  const revealed = items.map(() => false); // once an answer is shown, that item can no longer earn progress
  items.forEach((it, i) => {
    const row = document.createElement('div');
    row.className = 'tf';
    row.innerHTML = `<div class="stmt">${it.s}</div>
      <button class="btn small" data-v="1">${bil('Well-order', '是良序')}</button>
      <button class="btn small" data-v="0">${bil('Not', '不是')}</button>
      <button class="btn small ghost" data-v="show">${bil('Show answer', '看答案')}</button>
      <div style="flex-basis:100%"><div class="msg"></div></div>`;
    $('e1List').appendChild(row);
    row.querySelectorAll('button').forEach(b => b.addEventListener('click', () => {
      const msg = row.querySelector('.msg');
      if (b.dataset.v === 'show') { revealed[i] = true; okBox(msg, bi(it.en, it.zh), 'info'); return; }
      if ((b.dataset.v === '1') === it.wo) {
        okBox(msg, '✓ ' + bi(it.en, it.zh));
        if (!revealed[i]) solved[i] = true;
        if (solved.every(Boolean)) Progress.mark('L8E1');
      } else okBox(msg, bi('✗ Not quite. Try to build a descending chain, or look for a subset with no least element.', '✗ 不对。试着构造一条降链，或者找一个没有最小元的子集。'), 'bad');
    }));
  });
})();

/* ================= E2 compute in CNF ================= */
function parseNormalForm(str) {
  if (/[()]/.test(str)) throw new ParseError('Please answer in normal form, without parentheses.', '请用范式作答，不要带括号。');
  const terms = str.split('+').map(p => ORD.parse(p));
  terms.forEach(t => { if (t.length !== 1) throw new ParseError('Each summand should be a single term ω^β·c.', '每个加项都应是单独一项 ω^β·c。'); });
  for (let i = 1; i < terms.length; i++) {
    if (ORD.cmp(terms[i - 1][0][0], terms[i][0][0]) <= 0) throw new ParseError('Not in normal form: exponents must strictly decrease from left to right. Simplify further.', '还不是范式：指数必须从左到右严格递减，请继续化简。');
  }
  return terms.reduce((a, t) => ORD.add(a, t), []);
}
(function e2() {
  const items = [
    ['(ω + 1) + ω', 'w*2'], ['(ω + 1) · 2', 'w*2+1'], ['2 · (ω + 1)', 'w+2'],
    ['(ω + 1) · ω', 'w^2'], ['(ω + 1)²', 'w^2+w+1'], ['(ω² + ω) · (ω + 3)', 'w^3+w^2*3+w'],
  ];
  const solved = items.map(() => false);
  items.forEach(([q, ans], i) => {
    const row = document.createElement('div');
    row.className = 'ansrow';
    row.innerHTML = `<div class="q m" style="font-size:17px">(${String.fromCharCode(97 + i)}) &nbsp; ${q} =</div>
      <input class="formula" placeholder="normal form · 范式">
      <button class="btn small primary">${bil('Check', '检查')}</button>
      <button class="btn small ghost">${bil('Show answer', '看答案')}</button>
      <div class="msg"></div>`;
    $('e2List').appendChild(row);
    const [inp, chk, show] = [row.querySelector('input'), ...row.querySelectorAll('button')];
    const msg = row.querySelector('.msg');
    const want = ORD.parse(ans);
    let revealed = false;
    const check = () => {
      let v;
      try { v = parseNormalForm(inp.value); } catch (e) { okBox(msg, e instanceof ParseError ? e.html() : String(e), 'bad'); return; }
      if (ORD.eq(v, want)) {
        okBox(msg, `✓ <span class="m">${q} = ${ORD.toHTML(want)}</span>`);
        if (!revealed) solved[i] = true;
        if (solved.every(Boolean)) Progress.mark('L8E2');
      } else okBox(msg, bi(`✗ You wrote ${ORD.toHTML(v)}, which is ${ORD.cmp(v, want) < 0 ? 'too small' : 'too large'}. Picture it as copies of sticks: which parts get absorbed?`, `✗ 你写的是 ${ORD.toHTML(v)}，${ORD.cmp(v, want) < 0 ? '偏小' : '偏大'}了。用火柴图想一想：哪些部分会被吸收？`), 'bad');
    };
    chk.addEventListener('click', check);
    inp.addEventListener('keydown', e => e.key === 'Enter' && check());
    show.addEventListener('click', () => { revealed = true; okBox(msg, `<span class="m">${q} = ${ORD.toHTML(want)}</span>`, 'info'); });
  });
})();

/* ================= E3 order types of sets of reals ================= */
(function e3() {
  const pts = (ks, n) => { const o = []; ks.forEach(k => { for (let j = 1; j <= n; j++) o.push(k - 1 / j); }); return o; };
  const items = [
    { s: '{1 − 1/n : n ≥ 1} ∪ {2 − 1/n : n ≥ 1}', ans: 'w*2', p: pts([1, 2], 16), max: 2.2,
      en: 'ω·2: the points 0, 1/2, 2/3, … form an ω-sequence converging to 1; then 1, 3/2, 5/3, … form a second one.', zh: 'ω·2：0, 1/2, 2/3, … 是收敛到 1 的 ω 序列；接着 1, 3/2, 5/3, … 又是一条。' },
    { s: '{k − 1/n : k, n ≥ 1}', ans: 'w^2', p: pts([1, 2, 3, 4, 5], 12), max: 5.4, more: true,
      en: 'ω²: one ω-sequence inside each interval [k−1, k), and there are ω such intervals.', zh: 'ω²：每个区间 [k−1, k) 里都有一条 ω 序列，这样的区间共有 ω 个。' },
    { s: '{1 − 1/n : n ≥ 1} ∪ {1, 2}', ans: 'w+2', p: pts([1], 16).concat([1, 2]), max: 2.2,
      en: 'ω + 2: an ω-sequence, then two more points.', zh: 'ω + 2：一条 ω 序列，后面再加两个点。' },
    { s: '{m + 1 − 1/n : m = 0, 1, 2; n ≥ 1} ∪ {3}', ans: 'w*3+1', p: pts([1, 2, 3], 14).concat([3]), max: 3.2,
      en: 'ω·3 + 1: three ω-sequences converging to 1, 2, 3, and then the point 3 itself on top.', zh: 'ω·3 + 1：三条 ω 序列分别收敛到 1、2、3，最后是点 3 本身。' },
  ];
  const solved = items.map(() => false);
  items.forEach((it, i) => {
    const row = document.createElement('div');
    row.className = 'ansrow';
    row.innerHTML = `<div class="q m" style="font-size:16px">(${String.fromCharCode(97 + i)}) &nbsp; ${it.s}</div>
      <input class="formula" placeholder="order type · 序型">
      <button class="btn small primary">${bil('Check', '检查')}</button>
      <button class="btn small ghost">${bil('Show answer', '看答案')}</button>
      <div style="flex-basis:100%"><svg viewBox="0 0 760 50" width="760" height="50"></svg></div>
      <div class="msg"></div>`;
    $('e3List').appendChild(row);
    const svg = row.querySelector('svg');
    const X = v => 20 + v / it.max * 700;
    el('line', { x1: 10, x2: 740, y1: 22, y2: 22, stroke: '#cfc9b8' }, svg);
    for (let t = 0; t <= Math.floor(it.max); t++) svgText(svg, X(t), 44, t, { 'text-anchor': 'middle', 'font-size': 11, fill: COL.muted });
    it.p.forEach(v => el('circle', { cx: X(v), cy: 22, r: 3.2, fill: COL.accent }, svg));
    if (it.more) svgText(svg, 745, 26, '…', { 'font-size': 14, fill: COL.muted, 'text-anchor': 'end' });
    const [inp, chk, show] = [row.querySelector('input'), ...row.querySelectorAll('button')];
    const msg = row.querySelector('.msg');
    const want = ORD.parse(it.ans);
    let revealed = false;
    const check = () => {
      let v;
      try { v = ORD.parse(inp.value); } catch (e) { okBox(msg, e instanceof ParseError ? e.html() : String(e), 'bad'); return; }
      if (ORD.eq(v, want)) {
        okBox(msg, '✓ ' + bi(it.en, it.zh));
        if (!revealed) solved[i] = true;
        if (solved.every(Boolean)) Progress.mark('L8E3');
      } else okBox(msg, bi(`✗ Not ${ORD.toHTML(v)}. Count the accumulation points, and check whether there is a largest element.`, `✗ 不是 ${ORD.toHTML(v)}。数一数有几个聚点，再看看有没有最大元。`), 'bad');
    };
    chk.addEventListener('click', check);
    inp.addEventListener('keydown', e => e.key === 'Enter' && check());
    show.addEventListener('click', () => { revealed = true; okBox(msg, `<b class="m">${ORD.toHTML(want)}</b> · ` + bi(it.en, it.zh), 'info'); });
  });
})();

/* ================= E4 find the flaw ================= */
(function e4() {
  const done = { a: false, b: false };
  let revealed = false; // after "Show answers", picking the right options no longer earns progress
  const fin = () => !revealed && done.a && done.b && Progress.mark('L8E4');
  const A = [
    { ok: false, html: bi('The base case is wrong.', '奠基步错了。') },
    { ok: false, html: bi('The successor step is wrong.', '后继步错了。') },
    { ok: true, html: bi('The limit case is missing.', '缺了极限情形。') },
  ];
  const ansA = bi('The <b>limit case is missing</b>. “P(n) for all n &lt; ω” does not yield P(ω), and in fact ω is infinite. Base + successor only reach the natural numbers; that is ordinary induction.', '<b>缺了极限情形</b>。“对一切 n &lt; ω 有 P(n)”推不出 P(ω)，事实上 ω 就是无穷的。奠基加后继步只能走遍自然数，那只是普通的数学归纳法。');
  choiceButtons($('e4a'), A, o => {
    if (o.ok) { okBox($('e4aMsg'), '✓ ' + ansA); done.a = true; fin(); }
    else okBox($('e4aMsg'), bi('✗ That step is fine. Which ordinal is the first counterexample, and what kind of ordinal is it?', '✗ 这一步没问题。第一个反例是哪个序数？它是哪一类序数？'), 'bad');
  });
  const B = ['A', 'B', 'C', 'D'].map(x => ({ ok: x === 'D', html: bi(`Step (${x}) is wrong.`, `第 (${x}) 步错了。`) }));
  const ansB = bi('<b>(D)</b> is wrong. (C) is the definition of addition: + is continuous in its <i>right</i> argument. But sup{β+1 : β &lt; λ} = λ, not λ+1, because + is <b>not</b> continuous in the left argument. Indeed 1 + ω = ω ≠ ω + 1, so the claim fails at λ = ω.', '<b>(D)</b> 错了。(C) 正是加法的定义：加法对<i>右边</i>的变元连续。但 sup{β+1 : β &lt; λ} = λ，而不是 λ+1，因为加法对左边的变元<b>不</b>连续。事实上 1 + ω = ω ≠ ω + 1，命题在 λ = ω 处就不成立。');
  choiceButtons($('e4b'), B, o => {
    if (o.ok) { okBox($('e4bMsg'), '✓ ' + ansB); done.b = true; fin(); }
    else okBox($('e4bMsg'), bi('✗ That step is valid. Compute both sides for λ = ω.', '✗ 这一步是对的。取 λ = ω，把两边都算一算。'), 'bad');
  });
  $('e4Show').addEventListener('click', () => {
    revealed = true;
    $('e4a').querySelectorAll('.choice')[2].classList.add('right');
    $('e4b').querySelectorAll('.choice')[3].classList.add('right');
    okBox($('e4aMsg'), ansA, 'info');
    okBox($('e4bMsg'), ansB, 'info');
  });
})();

/* ================= E5 equations ================= */
(function e5() {
  const P = ORD.parse, W = ORD.W;
  const items = [
    { q: 'ω + β = ω²', v: 'β', test: x => ORD.eq(ORD.add(W, x), P('w^2')),
      ans: bi('β = ω² (and only ω²: left subtraction is unique). The ω in front is absorbed.', 'β = ω²（并且只有这一个解：左减法唯一）。前面的 ω 被吸收了。') },
    { q: 'α + ω = ω, &nbsp; α ≠ 0', v: 'α', test: x => !ORD.isZero(x) && ORD.eq(ORD.add(x, W), W),
      ans: bi('Any natural number α = n ≥ 1. No infinite α works, since then α + ω &gt; α ≥ ω.', '任意自然数 α = n ≥ 1。无穷的 α 都不行，因为那时 α + ω &gt; α ≥ ω。') },
    { q: 'α · ω = ω²', v: 'α', test: x => ORD.eq(ORD.mul(x, W), P('w^2')),
      ans: bi('Exactly the α with leading term ω: α = ω·k + n (k ≥ 1). For example (ω+5)·ω = ω².', '恰好是首项为 ω 的那些 α：α = ω·k + n（k ≥ 1）。例如 (ω+5)·ω = ω²。') },
    { q: 'α<sup>ω</sup> = ω, &nbsp; α &gt; 1', v: 'α', test: x => ORD.cmp(x, ORD.ONE) > 0 && ORD.eq(ORD.pow(x, W), W),
      ans: bi('Any natural number n ≥ 2: n<sup>ω</sup> = sup nᵏ = ω. If α ≥ ω, then α<sup>ω</sup> ≥ ω<sup>ω</sup>.', '任意自然数 n ≥ 2：n<sup>ω</sup> = sup nᵏ = ω。若 α ≥ ω，则 α<sup>ω</sup> ≥ ω<sup>ω</sup>。') },
  ];
  const solved = items.map(() => false);
  items.forEach((it, i) => {
    const row = document.createElement('div');
    row.className = 'ansrow';
    row.innerHTML = `<div class="q m" style="font-size:17px">(${String.fromCharCode(97 + i)}) &nbsp; ${it.q} &nbsp; → &nbsp; ${it.v} =</div>
      <input class="formula">
      <button class="btn small primary">${bil('Check', '检查')}</button>
      <button class="btn small ghost">${bil('Show answer', '看答案')}</button>
      <div class="msg"></div>`;
    $('e5List').appendChild(row);
    const [inp, chk, show] = [row.querySelector('input'), ...row.querySelectorAll('button')];
    const msg = row.querySelector('.msg');
    let revealed = false;
    const check = () => {
      let x;
      try { x = P(inp.value); } catch (e) { okBox(msg, e instanceof ParseError ? e.html() : String(e), 'bad'); return; }
      let ok = false;
      try { ok = it.test(x); } catch (e) { ok = false; }
      if (ok) { okBox(msg, '✓ ' + bi(`${it.v} = ${ORD.toHTML(x)} works. `, `${it.v} = ${ORD.toHTML(x)} 成立。`) + it.ans); if (!revealed) solved[i] = true; if (solved.every(Boolean)) Progress.mark('L8E5'); }
      else okBox(msg, bi(`✗ ${it.v} = ${ORD.toHTML(x)} does not satisfy the equation.`, `✗ ${it.v} = ${ORD.toHTML(x)} 不满足方程。`), 'bad');
    };
    chk.addEventListener('click', check);
    inp.addEventListener('keydown', e => e.key === 'Enter' && check());
    show.addEventListener('click', () => { revealed = true; okBox(msg, it.ans, 'info'); });
  });
})();

/* ================= E6 zero / successor / limit ================= */
(function e6() {
  const items = [['ω·2', 'w*2'], ['ω+1', 'w+1'], ['ω²', 'w^2'], ['ω<sup>ω</sup>+ω', 'w^w+w'], ['ω·3+2', 'w*3+2'], ['1', '1'], ['0', '0'], ['2<sup>ω</sup>', '2^w'], ['(ω+1)·ω', '(w+1)*w'], ['ω·(ω+1)', 'w*(w+1)'], ['(ω+1)²', '(w+1)^2']];
  const cyc = [null, 's', 'l', 'z'];
  const LAB = { s: bil('successor', '后继'), l: bil('limit', '极限'), z: bil('zero', '零') };
  const truth = items.map(([, e]) => { const o = ORD.parse(e); return ORD.isZero(o) ? 'z' : ORD.isLimit(o) ? 'l' : 's'; });
  const state = items.map(() => null);
  let revealed = false; // after "Show answer", Check no longer earns progress
  const chips = items.map(([d], i) => {
    const c = document.createElement('div');
    c.className = 'chip m';
    c.addEventListener('click', () => { state[i] = cyc[(cyc.indexOf(state[i]) + 1) % 4]; paint(); clearBox($('e6Msg')); });
    $('e6Chips').appendChild(c);
    return c;
  });
  function paint(mark) {
    chips.forEach((c, i) => {
      c.className = 'chip m' + (state[i] ? ' st-' + state[i] : '') + (mark ? (state[i] === truth[i] ? ' ok' : ' no') : '');
      c.innerHTML = `${items[i][0]}<span class="st">${state[i] ? LAB[state[i]] : '?'}</span>`;
    });
  }
  paint();
  $('e6Check').addEventListener('click', () => {
    paint(true);
    const right = state.filter((s, i) => s === truth[i]).length;
    if (right === items.length) {
      okBox($('e6Msg'), bi('✓ All correct. The traps: 2<sup>ω</sup> = ω, (ω+1)·ω = ω² and ω·(ω+1) = ω² + ω are all limits, while (ω+1)² = ω² + ω + 1 is a successor. Only the <b>last term</b> of the normal form matters.', '✓ 全对。容易错的几个：2<sup>ω</sup> = ω、(ω+1)·ω = ω²、ω·(ω+1) = ω² + ω 都是极限，而 (ω+1)² = ω² + ω + 1 是后继。只看范式的<b>最后一项</b>即可。'));
      if (!revealed) Progress.mark('L8E6');
    } else okBox($('e6Msg'), bi(`${right} / ${items.length} correct (red = wrong). Rewrite each one in normal form first and look at the last term.`, `答对 ${right} / ${items.length}（红色为错）。先化成范式，再看最后一项。`), 'warn');
  });
  $('e6Show').addEventListener('click', () => {
    revealed = true;
    truth.forEach((t, i) => (state[i] = t));
    paint(true);
    okBox($('e6Msg'), bi('Answer shown. Normal forms: ' + items.map(([d, e]) => `${d} = ${ORD.toHTML(ORD.parse(e))}`).join('; ') + '. Successor ⇔ the last term is a finite number.', '已显示答案。范式：' + items.map(([d, e]) => `${d} = ${ORD.toHTML(ORD.parse(e))}`).join('；') + '。后继 ⇔ 范式的最后一项是有限数。'), 'info');
  });
})();
