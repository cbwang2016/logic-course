// Lesson 19 interactions: Borel & projective hierarchies.
/* ======================================================================
   Pure logic (no DOM) – unit-tested with node
   ====================================================================== */
const SUBD = '₀₁₂₃₄₅₆₇₈₉';
const sub = n => String(n).split('').map(d => SUBD[d] || d).join('');
const SUPD = { 0: '⁰', 1: '¹', 2: '²', 3: '³', 4: '⁴', 5: '⁵', 6: '⁶', 7: '⁷', 8: '⁸', 9: '⁹' };
const sup = n => String(n).split('').map(d => SUPD[d]).join('');

// Left endpoint and length of the Cantor-set piece corresponding to binary string s.
function cantorLeft(s) {
  let x = 0;
  for (let i = 0; i < s.length; i++) x += (s[i] === '1' ? 2 : 0) / Math.pow(3, i + 1);
  return x;
}
const cantorLen = s => Math.pow(3, -s.length);

// s_n: the n-th nonempty binary string (s_0 = '0', s_1 = '1', s_2 = '00', s_3 = '01', ...)
const strOf = n => (n + 2).toString(2).slice(1);

// is s an initial segment of the eventually-zero sequence x (given as finite array/string)?
function prefixOf(s, x) {
  for (let i = 0; i < s.length; i++) if (String(x[i] ?? 0) !== s[i]) return false;
  return true;
}
// x ∈ U_code, where U_code = ⋃{ N_{s_n} : code(n) = 1 }  (code finite, x eventually 0)
function inU(code, x) {
  for (let n = 0; n < code.length; n++) if (code[n] === 1 && prefixOf(strOf(n), x)) return true;
  return false;
}

// Continued fractions: [0; a1, ..., an] as reduced fraction [p, q]
function gcd(a, b) { while (b) [a, b] = [b, a % b]; return Math.abs(a); }
function cfValue(as) {
  if (!as.length) return [0, 1];
  let p = as[as.length - 1], q = 1; // value of tail = p/q
  for (let i = as.length - 2; i >= 0; i--) { [p, q] = [as[i] * p + q, p]; } // a_i + q/p
  // result = 1 / (p/q) = q/p
  const g = gcd(q, p);
  return [q / g, p / g];
}
// N_s in Baire space ↦ irrationals in the open interval between these two rationals
function baireInterval(s) {
  if (!s.length) return [[0, 1], [1, 1]];
  const a = s.map(v => v + 1);
  const e1 = cfValue(a);
  const b = a.slice(); b[b.length - 1] += 1;
  const e2 = cfValue(b);
  return e1[0] / e1[1] < e2[0] / e2[1] ? [e1, e2] : [e2, e1];
}

// Class arithmetic. h = 0: Borel (Σ⁰/Π⁰/Δ⁰), h = 1: projective (Σ¹/Π¹/Δ¹). Borel = {h:1,t:'D',n:1}.
function climb(st, op) {
  const { h, t, n } = st;
  const dual = { S: 'P', P: 'S', D: 'D' };
  switch (op) {
    case 'comp': case 'N': return { h, t: dual[t], n };
    case 'fin': case 'pre': return { h, t, n };
    case 'cu':
      if (h === 0) return t === 'P' ? { h, t: 'S', n: n + 1 } : { h, t: 'S', n };
      return { h, t, n };
    case 'ci':
      if (h === 0) return t === 'S' ? { h, t: 'P', n: n + 1 } : { h, t: 'P', n };
      return { h, t, n };
    case 'U': return { h, t, n };
    case 'E': return t === 'P' ? { h, t: 'S', n: n + 1 } : { h, t: 'S', n };
    case 'A': return t === 'S' ? { h, t: 'P', n: n + 1 } : { h, t: 'P', n };
  }
  throw new Error('bad op ' + op);
}
const clsName = st => ({ S: 'Σ', P: 'Π', D: 'Δ' }[st.t]) + (st.h ? '¹' : '⁰') + sub(st.n);

// Exact level ex = {t, n} (t ∈ S,P,D for Borel finite levels, or 'S11'/'P11' non-Borel)
// node key: 'S3','P2','D1', 'W' (levels ≥ ω), 'B' (Borel), 'S11', 'P11'
function contains(ex, key) {
  const borel = ['S', 'P', 'D'].includes(ex.t);
  if (key === 'W' || key === 'B') return borel;
  if (key === 'S11') return borel || ex.t === 'S11';
  if (key === 'P11') return borel || ex.t === 'P11';
  if (!borel) return false;
  const t = key[0], k = +key.slice(1);
  if (ex.t === 'D') return ex.n === 1 ? true : k >= ex.n;
  if (t === ex.t) return k >= ex.n;
  return k >= ex.n + 1;
}

// Ordinals below ω^ω in Cantor normal form: c[k] = coefficient of ω^k.
function ordNorm(c) { const a = c.slice(); while (a.length && !a[a.length - 1]) a.pop(); return a; }
function ordPhi(c) { // order-preserving map ω^ω → [0,1)
  c = ordNorm(c);
  const d = c.length - 1;
  if (d < 0) return 0;
  const lead = c[d];
  if (d === 0) return 0.5 * (1 - 1 / (lead + 1));
  const base = 1 - Math.pow(2, -d), w = Math.pow(2, -d - 1);
  const inner = ordPhi(c.slice(0, d)) / (1 - Math.pow(2, -d));
  const u = (1 - 1 / lead) + (1 / lead - 1 / (lead + 1)) * inner;
  return base + w * u;
}
function ordStr(c) {
  c = ordNorm(c);
  if (!c.length) return '0';
  const parts = [];
  for (let k = c.length - 1; k >= 0; k--) {
    if (!c[k]) continue;
    if (k === 0) parts.push(String(c[k]));
    else parts.push((k === 1 ? 'ω' : 'ω' + sup(k)) + (c[k] > 1 ? '·' + c[k] : ''));
  }
  return parts.join('+');
}
const ORD_SEQS = [
  { name: 'αₙ = n', f: n => [n], lim: [0, 1], limS: 'ω' },
  { name: 'αₙ = ω + n', f: n => [n, 1], lim: [0, 2], limS: 'ω·2' },
  { name: 'αₙ = ω·n', f: n => [0, n], lim: [0, 0, 1], limS: 'ω²' },
  { name: 'αₙ = ωⁿ', f: n => { const a = Array(n + 1).fill(0); a[n] = 1; return a; }, lim: null, limS: 'ω^ω' },
];

// Rationals in [0,1], enumerated by denominator.
function rationals(count) {
  const out = [];
  for (let q = 1; out.length < count; q++)
    for (let p = 0; p <= q && out.length < count; p++)
      if (gcd(p, q) === 1) out.push([p, q]);
  return out;
}

// Regularity table: [PSP, LM, BP]; Y proved, N refuted, Q undecided by that theory.
const REG_ROWS = ['S11', 'P11', 'D12', 'S12', 'P12', 'S13', 'ALL'];
const REG = {
  ZFC: { S11: 'YYY', P11: 'QYY', D12: 'QQQ', S12: 'QQQ', P12: 'QQQ', S13: 'QQQ', ALL: 'NNN' },
  L:   { S11: 'YYY', P11: 'NYY', D12: 'NNN', S12: 'NNN', P12: 'NNN', S13: 'NNN', ALL: 'NNN' },
  MC:  { S11: 'YYY', P11: 'YYY', D12: 'YYY', S12: 'YYY', P12: 'QYY', S13: 'QQQ', ALL: 'NNN' },
  PD:  { S11: 'YYY', P11: 'YYY', D12: 'YYY', S12: 'YYY', P12: 'YYY', S13: 'YYY', ALL: 'NNN' },
};

// Wadge demo: II's Lipschitz strategy reducing A = {x : x has a 1} to B = {y : y has infinitely many 1s}.
const wadgeII = xs => (xs.includes(1) ? 1 : 0);

// E4: shadows of a finite grid C[col][row]
const existsCol = C => C.map(col => col.some(Boolean));
const forallCol = C => C.map(col => col.every(Boolean));

if (typeof module !== 'undefined' && typeof window === 'undefined') {
  module.exports = { cantorLeft, cantorLen, strOf, prefixOf, inU, cfValue, baireInterval, climb, clsName, contains,
    ordPhi, ordStr, ORD_SEQS, rationals, REG, REG_ROWS, wadgeII, existsCol, forallCol, gcd };
}

/* ======================================================================
   DOM
   ====================================================================== */
if (typeof window !== 'undefined') {
Lang.init();
Progress.paint();

const $ = id => document.getElementById(id);
const bl = (en, zh) => (en === zh ? en : bil(en, zh));
const okBox = (box, html, kind = 'ok') => { box.className = 'msg ' + kind; box.innerHTML = html; };
const clearBox = box => { box.className = 'msg'; box.innerHTML = ''; };
const T = (parent, x, y, s, attrs = {}) => { const t = el('text', { x, y, ...attrs }, parent); t.textContent = s; return t; };
const C = { ink: '#1f2430', muted: '#6b7280', line: '#e3dfd3', acc: '#3b5bdb', accS: '#e7ecff', tr: '#2f9e44', trS: '#d3f9d8',
  fa: '#e03131', faS: '#ffe3e3', meta: '#ae3ec9', metaS: '#f8e7fc', gold: '#f08c00', goldS: '#fff3bf', gray: '#c9c4b5' };

/* ---------- generic: check-yourself ---------- */
function checkYourself(id, cfg) {
  const box = $(id);
  box.innerHTML = `<div class="q">${bi('Check yourself: ' + cfg.q[0], '自测：' + cfg.q[1])}</div><div class="toolbar"></div><div class="msg"></div>`;
  const bar = box.querySelector('.toolbar'), msg = box.querySelector('.msg');
  const btns = cfg.opts.map((o, i) => {
    const b = document.createElement('button');
    b.className = 'btn small';
    b.innerHTML = bl(o[0], o[1]);
    b.addEventListener('click', () => {
      btns.forEach(x => x.classList.remove('sel'));
      if (i === cfg.ans) okBox(msg, '✓ ' + bi(cfg.why[0], cfg.why[1]));
      else okBox(msg, '✗ ' + bi(cfg.hint ? cfg.hint[0] : 'Not quite. Think again, or press “Show answer”.', cfg.hint ? cfg.hint[1] : '不太对。再想想，或者点“显示答案”。'), 'bad');
    });
    bar.appendChild(b);
    return b;
  });
  const sh = document.createElement('button');
  sh.className = 'btn small ghost';
  sh.innerHTML = bil('Show answer', '显示答案');
  sh.addEventListener('click', () => {
    btns.forEach((x, i) => x.classList.toggle('sel', i === cfg.ans));
    okBox(msg, bi('<b>Answer:</b> ' + cfg.opts[cfg.ans][0] + '. ' + cfg.why[0], '<b>答案：</b>' + cfg.opts[cfg.ans][1] + '。' + cfg.why[1]), 'info');
  });
  bar.appendChild(sh);
}

/* ---------- generic: step-by-step proofs ---------- */
document.querySelectorAll('[data-next]').forEach(b => b.addEventListener('click', () => {
  const steps = [...$(b.dataset.next).querySelectorAll('.step')];
  const nxt = steps.find(s => !s.classList.contains('on'));
  if (nxt) nxt.classList.add('on');
  if (steps.every(s => s.classList.contains('on'))) b.disabled = true;
}));
document.querySelectorAll('[data-all]').forEach(b => b.addEventListener('click', () => {
  $(b.dataset.all).querySelectorAll('.step').forEach(s => s.classList.add('on'));
  const nb = document.querySelector(`[data-next="${b.dataset.all}"]`);
  if (nb) nb.disabled = true;
}));

/* ================= §1 trees ================= */
(function trees() {
  const svg = $('treeSvg'), info = $('treeInfo');
  const X0 = 30, WC = 700, Y = d => 28 + d * 50, R = [11, 9, 8, 7, 6];
  let mode = 'cone', sel = '0', bsel = [1];
  const removed = new Set();
  let zeroAnim = false, animTok = 0;
  const cx = s => X0 + WC * (cantorLeft(s) + cantorLen(s) / 2);
  const strings = d => { const out = []; for (let m = 0; m < (1 << d); m++) out.push(d ? m.toString(2).padStart(d, '0') : ''); return out; };
  const isRemoved = s => { for (let k = 0; k <= s.length; k++) if (removed.has(s.slice(0, k))) return true; return false; };

  function drawCantor() {
    svg.innerHTML = '';
    const gE = el('g', {}, svg), gN = el('g', {}, svg), gB = el('g', {}, svg);
    for (let d = 0; d <= 4; d++) strings(d).forEach(s => {
      ['0', '1'].forEach(b => {
        const t = s + b;
        const y2 = d === 4 ? Y(4) + 32 : Y(d + 1);
        let stroke = '#b9b4a6', w = 1.6;
        if (mode === 'cone' && t.startsWith(sel) && t.length > sel.length) { stroke = C.acc; w = 3; }
        if (mode === 'cone' && sel.startsWith(t)) { stroke = C.gold; w = 3.4; }
        if (mode === 'prune' && isRemoved(t)) { stroke = '#f3b0b0'; w = 1.2; }
        el('line', { x1: cx(s), y1: Y(d), x2: cx(t), y2, stroke, 'stroke-width': w, class: 'tedge2', 'stroke-dasharray': mode === 'prune' && isRemoved(t) ? '3 3' : '' }, gE);
      });
    });
    for (let d = 0; d <= 4; d++) strings(d).forEach(s => {
      const g = el('g', { class: 'tnd' }, gN);
      let fill = '#fff', stroke = C.ink;
      if (mode === 'cone') {
        if (s.startsWith(sel)) { fill = C.accS; stroke = C.acc; }
        if (s === sel) { fill = C.acc; }
        else if (sel.startsWith(s)) { fill = C.goldS; stroke = C.gold; }
      } else if (isRemoved(s)) { fill = C.faS; stroke = C.fa; }
      el('circle', { cx: cx(s), cy: Y(d), r: R[d], fill, stroke, 'stroke-width': 2 }, g);
      if (mode === 'prune' && removed.has(s)) T(g, cx(s), Y(d) + 4, '✂', { 'text-anchor': 'middle', 'font-size': 11, fill: C.fa });
      if (d === 0) T(g, cx(s), Y(d) - R[d] - 5, '∅', { 'text-anchor': 'middle', 'font-size': 11, fill: C.muted });
      else if (d <= 3) { const left = s.endsWith('0'); T(g, cx(s) + (left ? -(R[d] + 4) : R[d] + 4), Y(d) - 4, s, { 'text-anchor': left ? 'end' : 'start', 'font-size': 10.5, fill: mode === 'cone' && s === sel ? C.acc : C.muted, 'font-weight': mode === 'cone' && s === sel ? 700 : 400 }); }
      el('title', {}, g).textContent = s === '' ? 'N∅ = 2^ω' : 'N' + sub(s);
      g.addEventListener('click', () => {
        if (mode === 'cone') sel = s;
        else { animTok++; zeroAnim = false; if (removed.has(s)) removed.delete(s); else removed.add(s); }
        drawCantor();
      });
    });
    // Cantor set approximations
    for (let L = 0; L <= 5; L++) strings(L).forEach(t => {
      let fill = C.ink, op = 0.85;
      if (mode === 'cone') {
        if (t.startsWith(sel)) fill = C.acc;
        else if (sel.startsWith(t)) { fill = C.acc; op = 0.3; }
        else { fill = '#bdb8aa'; op = 0.7; }
      } else if (isRemoved(t)) { fill = '#f3b0b0'; op = 0.8; }
      el('rect', { x: X0 + WC * cantorLeft(t), y: 290 + L * 17, width: Math.max(WC * cantorLen(t), 1.2), height: 9, fill, opacity: op, rx: 1 }, gB);
    });
    T(gB, X0, 397, '0', { 'font-size': 10, fill: C.muted, 'text-anchor': 'middle' });
    T(gB, X0 + WC, 397, '1', { 'font-size': 10, fill: C.muted, 'text-anchor': 'middle' });
    T(gB, X0 + WC / 2, 397, 'Cantor set C₀ ⊇ C₁ ⊇ … ⊇ C₅ · 康托尔集的逼近', { 'font-size': 10.5, fill: C.muted, 'text-anchor': 'middle' });
    describe();
  }

  function describe() {
    if (mode === 'cone') {
      const n = sel.length;
      const num = [...sel].reduce((a, c, i) => a + (c === '1' ? 2 * Math.pow(3, n - 1 - i) : 0), 0);
      const Ns = sel === '' ? 'N<sub>∅</sub> = 2^ω' : `N<sub>${sel}</sub>`;
      const frc = (p, q) => { const g = gcd(p, q) || 1; return q / g === 1 ? String(p / g) : `${p / g}/${q / g}`; };
      const lo = frc(num, Math.pow(3, n)), hi = frc(num + 1, Math.pow(3, n));
      okBox(info, bi(`<span class="m">${Ns} = {x ∈ 2^ω : ${sel || '∅'} ⊂ x}</span>: the blue cone. Gold: the path from the root down to <span class="m">${sel || '∅'}</span>. On the Cantor set it is the piece in <span class="m">[${lo}, ${hi}]</span>. Under the fair-coin measure it has measure <span class="m">2^(−${n}) = 1/${1 << n}</span>. Its complement is the union of the other ${(1 << n) - 1} cone(s) at depth ${n}, so it is <b>clopen</b>.`,
        `<span class="m">${Ns} = {x ∈ 2^ω : ${sel || '∅'} ⊂ x}</span>：蓝色的锥；金色是从树根到 <span class="m">${sel || '∅'}</span> 的路径。在康托尔集上它对应 <span class="m">[${lo}, ${hi}]</span> 中的那一段；在公平硬币测度下，它的测度是 <span class="m">2^(−${n}) = 1/${1 << n}</span>。它的补集是深度 ${n} 处其余 ${(1 << n) - 1} 个锥之并，所以它<b>既开又闭</b>。`), 'info');
    } else if (mode === 'prune') {
      const R2 = [...removed].sort((a, b) => a.length - b.length || a.localeCompare(b));
      if (zeroAnim) {
        okBox(info, bi('We cut <span class="m">1, 01, 001, 0001</span>, and we must keep going: <span class="m">00001, 000001, …</span>, infinitely many cuts. The only surviving branch is <span class="m">0^∞</span>, so <span class="m">[T] = {0^∞}</span>. It is <b>closed</b> (its complement <span class="m">⋃ₖ N_{0^k1}</span> is open) but <b>not open</b>: every cone <span class="m">N_{0^k}</span> around <span class="m">0^∞</span> contains other points. A closed set may need infinitely many cuts. A clopen set in <span class="m">2^ω</span> never does, by compactness.',
          '我们剪掉了 <span class="m">1, 01, 001, 0001</span>，还得一直剪下去：<span class="m">00001, 000001, …</span>，共无穷多刀。唯一幸存的分支是 <span class="m">0^∞</span>，所以 <span class="m">[T] = {0^∞}</span>。它是<b>闭集</b>（补集 <span class="m">⋃ₖ N_{0^k1}</span> 是开集），但<b>不是开集</b>：<span class="m">0^∞</span> 周围的每个锥 <span class="m">N_{0^k}</span> 都含有别的点。闭集可能需要剪无穷多刀；而由紧致性，<span class="m">2^ω</span> 中的既开又闭集只需有限多刀。'), 'info');
      } else if (!R2.length) {
        okBox(info, bi('Click nodes to <b>cut</b> them. Cutting <span class="m">s</span> removes the whole cone <span class="m">N_s</span>. What remains is a tree T, and its set of infinite branches <span class="m">[T]</span> is a closed set.', '点击节点即可<b>剪掉</b>它：剪掉 <span class="m">s</span> 就删去了整个锥 <span class="m">N_s</span>。剩下的是一棵树 T，它的无穷分支集 <span class="m">[T]</span> 是闭集。'), 'info');
      } else {
        const list = R2.map(s => `N<sub>${s || '∅'}</sub>`).join(' ∪ ');
        okBox(info, bi(`<span class="m">[T] = 2^ω ∖ (${list})</span>. The removed part is a union of cones, so it is <b>open</b>, and <span class="m">[T]</span> is <b>closed</b>. (With finitely many cuts, <span class="m">[T]</span> is even clopen. Try the <span class="m">{0^∞}</span> button for a genuinely non-open closed set.)`,
          `<span class="m">[T] = 2^ω ∖ (${list})</span>。被剪掉的部分是锥的并，所以是<b>开集</b>，从而 <span class="m">[T]</span> 是<b>闭集</b>。（只剪有限刀时，<span class="m">[T]</span> 甚至是既开又闭的。试试 <span class="m">{0^∞}</span> 按钮，看一个真正不开的闭集。）`), 'info');
      }
    }
  }

  // Baire space
  function drawBaire() {
    svg.innerHTML = '';
    const YB = d => 30 + d * 62;
    const nodes = [];
    (function rec(s, a, b, d) {
      const x = (a + b) / 2;
      nodes.push({ s, x, d });
      if (d === 3) return;
      const w = (b - a) / 4;
      for (let k = 0; k < 3; k++) rec([...s, k], a + k * w, a + (k + 1) * w, d + 1);
      nodes.push({ s, x: a + 3.5 * w, d: d + 1, dots: true });
    })([], X0, X0 + WC, 0);
    const key = s => s.join(',');
    const parentX = new Map(nodes.filter(n => !n.dots).map(n => [key(n.s), n.x]));
    const isPre = (p, s) => p.length <= s.length && p.every((v, i) => v === s[i]);
    nodes.forEach(n => {
      if (n.d === 0) return;
      const px = n.dots ? parentX.get(key(n.s)) : parentX.get(key(n.s.slice(0, -1)));
      const inCone = !n.dots && isPre(bsel, n.s) && n.s.length > bsel.length;
      const onPath = !n.dots && isPre(n.s, bsel);
      el('line', { x1: px, y1: YB(n.d - 1), x2: n.x, y2: YB(n.d) - (n.dots ? 8 : 0), stroke: inCone ? C.acc : onPath ? C.gold : '#b9b4a6', 'stroke-width': inCone || onPath ? 3 : 1.5, 'stroke-dasharray': n.dots ? '2 4' : '' }, svg);
    });
    nodes.forEach(n => {
      if (n.dots) { T(svg, n.x, YB(n.d) + 4, '…', { 'text-anchor': 'middle', 'font-size': 16, fill: C.muted }); return; }
      const g = el('g', { class: 'tnd' }, svg);
      const inCone = isPre(bsel, n.s), onPath = isPre(n.s, bsel);
      const r = [11, 9, 7, 4.5][n.d];
      el('circle', { cx: n.x, cy: YB(n.d), r, fill: n.s.length === bsel.length && inCone ? C.acc : inCone ? C.accS : onPath ? C.goldS : '#fff', stroke: inCone ? C.acc : onPath ? C.gold : C.ink, 'stroke-width': 2 }, g);
      if (n.d >= 1 && n.d <= 2) T(g, n.x, YB(n.d) + r + 12, n.s.join(''), { 'text-anchor': 'middle', 'font-size': 10.5, fill: C.muted });
      el('title', {}, g).textContent = 'N⟨' + n.s.join(',') + '⟩';
      g.addEventListener('click', () => { bsel = n.s; drawBaire(); });
    });
    // irrationals line
    const LY = 300, LX = X0, LW = WC;
    el('line', { x1: LX, x2: LX + LW, y1: LY, y2: LY, stroke: C.ink, 'stroke-width': 1.5 }, svg);
    [[0, '0'], [1 / 4, '1/4'], [1 / 3, '1/3'], [1 / 2, '1/2'], [1, '1']].forEach(([v, s]) => {
      el('line', { x1: LX + LW * v, x2: LX + LW * v, y1: LY - 4, y2: LY + 4, stroke: C.ink }, svg);
      T(svg, LX + LW * v, LY + 18, s, { 'text-anchor': 'middle', 'font-size': 10, fill: C.muted });
    });
    // children intervals of selection
    for (let k = 0; k < 6; k++) {
      const [e1, e2] = baireInterval([...bsel, k]);
      el('rect', { x: LX + LW * e1[0] / e1[1], y: LY - 26, width: Math.max(LW * (e2[0] / e2[1] - e1[0] / e1[1]), 1), height: 10, fill: k % 2 ? '#c5d0fa' : '#9fb1f5' }, svg);
    }
    const [a, b] = baireInterval(bsel);
    el('rect', { x: LX + LW * a[0] / a[1], y: LY - 12, width: Math.max(LW * (b[0] / b[1] - a[0] / a[1]), 1.5), height: 8, fill: C.acc }, svg);
    T(svg, LX, LY + 40, 'irrationals in (0,1) ≅ ω^ω via x ↦ [0; 1+x(0), 1+x(1), …] · 经连分数同胚于 (0,1) 中的无理数', { 'font-size': 11, fill: C.muted });
    T(svg, LX, LY - 34, 'pale bars: the sub-cones N_{s⌢k}, k = 0…5 (infinitely many more toward the left endpoint) · 浅色：子锥', { 'font-size': 10.5, fill: C.muted });
    const fr = f => f[1] === 1 ? String(f[0]) : f[0] + '/' + f[1];
    okBox(info, bi(`<span class="m">N<sub>⟨${bsel.join(',')}⟩</sub></span>: every node has <b>infinitely many</b> children (only 0, 1, 2 are drawn, then “…”). Via continued fractions, this cone is exactly the set of irrationals in the open interval <span class="m">(${fr(a)}, ${fr(b)})</span>. Its countably many sub-cones accumulate at one endpoint. That is why <span class="m">ω^ω</span> is <b>not compact</b>, unlike <span class="m">2^ω</span>.`,
      `<span class="m">N<sub>⟨${bsel.join(',')}⟩</sub></span>：每个节点都有<b>无穷多个</b>子节点（图中只画 0、1、2，后面用“…”）。经连分数对应，这个锥恰好是开区间 <span class="m">(${fr(a)}, ${fr(b)})</span> 中的无理数。它的可数多个子锥向一个端点聚集，这就是 <span class="m">ω^ω</span> 与 <span class="m">2^ω</span> 不同、<b>不紧致</b>的原因。`), 'info');
  }

  function draw() { $('pruneTools').style.display = mode === 'prune' ? '' : 'none'; mode === 'baire' ? drawBaire() : drawCantor(); }
  document.querySelectorAll('[data-tmode]').forEach(b => b.addEventListener('click', () => {
    document.querySelectorAll('[data-tmode]').forEach(x => x.classList.toggle('sel', x === b));
    mode = b.dataset.tmode;
    draw();
  }));
  $('pruneReset').addEventListener('click', () => { animTok++; removed.clear(); zeroAnim = false; draw(); });
  $('pruneZero').addEventListener('click', async () => {
    const my = ++animTok;
    removed.clear(); zeroAnim = false; draw();
    for (const s of ['1', '01', '001', '0001', '00001']) {
      await sleep(450);
      if (my !== animTok) return;
      removed.add(s); draw();
    }
    zeroAnim = true; draw();
  });
  draw();
})();

/* ================= diamond drawing (shared) ================= */
function drawDiamond(svg, o) {
  svg.innerHTML = '';
  const nodes = {};
  const { cx, dx, base, h, K, w = 70, hh = 28 } = o;
  const pos = {};
  for (let k = 1; k <= K; k++) {
    pos['D' + k] = [cx, base - (2 * k - 2) * h];
    pos['S' + k] = [cx - dx, base - (2 * k - 1) * h];
    pos['P' + k] = [cx + dx, base - (2 * k - 1) * h];
  }
  const top = base - (2 * K - 1) * h;
  if (o.full) {
    pos.W = [cx, top - 62];
    pos.B = [cx, top - 122];
    pos.S11 = [cx - dx, top - 182];
    pos.P11 = [cx + dx, top - 182];
  }
  const edges = [];
  for (let k = 1; k <= K; k++) {
    edges.push(['D' + k, 'S' + k], ['D' + k, 'P' + k]);
    if (k < K) edges.push(['S' + k, 'D' + (k + 1)], ['P' + k, 'D' + (k + 1)]);
  }
  if (o.full) edges.push(['S' + K, 'W'], ['P' + K, 'W'], ['W', 'B'], ['B', 'S11'], ['B', 'P11']);
  const gE = el('g', {}, svg);
  edges.forEach(([a, b]) => el('line', { x1: pos[a][0], y1: pos[a][1], x2: pos[b][0], y2: pos[b][1], stroke: '#cfc9b8', 'stroke-width': 2 }, gE));
  if (!o.full) T(svg, cx, top - 26, '⋮', { 'text-anchor': 'middle', 'font-size': 18, fill: C.muted });
  else T(svg, cx, pos.S11[1] - 28, '⋮  Σ¹₂ … projective · 投影集', { 'text-anchor': 'middle', 'font-size': 12, fill: C.muted });
  const names = { S1: 'open', P1: 'closed', D1: 'clopen', S2: 'F_σ', P2: 'G_δ', S3: 'G_δσ', P3: 'F_σδ' };
  Object.keys(pos).forEach(k => {
    const [x, y] = pos[k];
    const g = el('g', {}, svg);
    let label, small = names[k] || '', ww = w;
    if (k === 'W') { label = 'Σ⁰_α, Π⁰_α  (ω ≤ α < ω₁)'; ww = 230; small = ''; }
    else if (k === 'B') { label = 'Borel = Δ¹₁'; ww = 150; }
    else if (k === 'S11') { label = 'Σ¹₁'; small = 'analytic'; }
    else if (k === 'P11') { label = 'Π¹₁'; small = 'coanalytic'; }
    else label = ({ S: 'Σ', P: 'Π', D: 'Δ' }[k[0]]) + '⁰' + sub(k.slice(1));
    const r = el('rect', { x: x - ww / 2, y: y - hh / 2, width: ww, height: hh, rx: 9, fill: '#fff', stroke: '#b9b4a6', 'stroke-width': 2 }, g);
    r.style.transition = 'fill .35s, stroke .35s';
    const t = T(g, x, y + (small && o.full ? 0 : 5), label, { 'text-anchor': 'middle', 'font-size': o.full ? 14 : 13, 'font-weight': 700, fill: C.ink });
    if (small && o.full) T(g, x, y + 11, small, { 'text-anchor': 'middle', 'font-size': 9, fill: C.muted });
    nodes[k] = { g, r, t };
  });
  return nodes;
}
function paintNodes(nodes, f) {
  Object.entries(nodes).forEach(([k, n]) => {
    const st = f(k);
    const [fill, stroke, w] = st === 'cur' ? [C.acc, C.acc, 3] : st === 'yes' ? [C.trS, C.tr, 2.5] : st === 'exact' ? [C.tr, C.tr, 3] : st === 'no' ? ['#f4f2ec', '#d5d0c3', 2] : ['#fff', '#b9b4a6', 2];
    n.r.setAttribute('fill', fill); n.r.setAttribute('stroke', stroke); n.r.setAttribute('stroke-width', w);
    n.t.setAttribute('fill', st === 'cur' || st === 'exact' ? '#fff' : st === 'no' ? '#a8a294' : C.ink);
  });
}

/* ================= §2 climber + ruler ================= */
(function climber() {
  const mini = drawDiamond($('miniDia'), { cx: 210, dx: 115, base: 305, h: 35, K: 4, w: 64, hh: 26 });
  let st = { h: 0, t: 'S', n: 1 }, hist = ['Σ⁰₁'];
  const NAMES = { S1: ['open', '开集'], P1: ['closed', '闭集'], D1: ['clopen', '既开又闭'], S2: ['F_σ', 'F_σ'], P2: ['G_δ', 'G_δ'], S3: ['G_δσ', 'G_δσ'], P3: ['F_σδ', 'F_σδ'] };
  function render(msg) {
    const big = $('clBig');
    big.textContent = clsName(st);
    big.classList.remove('bump'); void big.offsetWidth; big.classList.add('bump');
    const nm = NAMES[st.t + st.n];
    $('clName').innerHTML = nm ? bil(nm[0], nm[1]) : '';
    $('clHist').innerHTML = hist.map((h, i) => `<span>${h}</span>${i < hist.length - 1 ? '' : ''}`).join('<b>→</b>');
    paintNodes(mini, k => (k === st.t + st.n ? 'cur' : ''));
    if (msg) okBox($('clMsg'), msg[0], msg[1]);
  }
  const OPN = { comp: 'X∖·', cu: '⋃ₙ', ci: '⋂ₙ', fin: '∪/∩', pre: 'f⁻¹' };
  document.querySelectorAll('[data-op]').forEach(b => b.addEventListener('click', () => {
    const op = b.dataset.op, old = st;
    st = climb(st, op);
    hist.push(OPN[op] + ' ' + clsName(st));
    if (hist.length > 9) hist = hist.slice(-9);
    const up = st.n > old.n;
    let m;
    if (op === 'comp') m = [bi('Complement swaps Σ and Π. Δ stays Δ. No climbing.', '取补交换 Σ 与 Π，Δ 仍是 Δ。不上升。'), 'info'];
    else if (op === 'fin') m = [bi('Finite unions and intersections never climb: every Σ⁰_α, Π⁰_α, Δ⁰_α is closed under them.', '有限并、有限交永远不上升：每个 Σ⁰_α、Π⁰_α、Δ⁰_α 都对它们封闭。'), 'info'];
    else if (op === 'pre') m = [bi('Continuous preimages never climb: f⁻¹ commutes with complements and unions, and f⁻¹[open] is open.', '连续原像永远不上升：f⁻¹ 与取补、取并可交换，且开集的原像是开集。'), 'info'];
    else if (up) m = [bi(`<b>Climbed!</b> A countable ${op === 'cu' ? 'union of Π' : 'intersection of Σ'}⁰${sub(old.n)} sets is in general only ${clsName(st)}, and §5 shows the jump is real.`, `<b>上升了！</b>可数个 ${op === 'cu' ? 'Π' : 'Σ'}⁰${sub(old.n)} 集的${op === 'cu' ? '并' : '交'}一般只能保证在 ${clsName(st)} 中；§5 说明这一跳是真实存在的。`), 'ok'];
    else m = [bi(`No climb: ${clsName(st)} is already closed under countable ${op === 'cu' ? 'unions' : 'intersections'}${old.t === 'D' ? ' (and Δ⁰ₙ ⊆ ' + clsName(st) + ')' : ''}.`, `不上升：${clsName(st)} 本身就对可数${op === 'cu' ? '并' : '交'}封闭${old.t === 'D' ? '（而且 Δ⁰ₙ ⊆ ' + clsName(st) + '）' : ''}。`), 'warn'];
    if (st.n > 4) m[0] += bi(` (Level ${st.n} is above the drawn part of the diagram.)`, `（第 ${st.n} 层已超出图中画出的部分。）`);
    render(m);
  }));
  $('clReset').addEventListener('click', () => { st = { h: 0, t: 'S', n: 1 }; hist = ['Σ⁰₁']; clearBox($('clMsg')); render(); });
  render([bi('Start: the open sets. Try ⋂ₙ (that gives G_δ), then X∖·, then ⋃ₙ again…', '起点：开集。先试 ⋂ₙ（得到 G_δ），再 X∖·，再 ⋃ₙ……'), 'info']);

  // ordinal ruler
  const svg = $('ruler');
  const X = p => 30 + 560 * p;
  let tok = 0;
  function base() {
    svg.innerHTML = '';
    el('line', { x1: 30, x2: 590, y1: 90, y2: 90, stroke: C.ink, 'stroke-width': 2 }, svg);
    T(svg, 612, 95, '⫽', { 'text-anchor': 'middle', 'font-size': 18, fill: C.muted });
    el('line', { x1: 635, x2: 730, y1: 90, y2: 90, stroke: C.ink, 'stroke-width': 2, 'stroke-dasharray': '2 5' }, svg);
    const marks = [[[0], '0'], [[1], '1'], [[2], '2'], [[0, 1], 'ω'], [[0, 2], 'ω·2'], [[0, 0, 1], 'ω²'], [[0, 0, 0, 1], 'ω³']];
    marks.forEach(([o, s]) => {
      el('line', { x1: X(ordPhi(o)), x2: X(ordPhi(o)), y1: 84, y2: 96, stroke: C.ink }, svg);
      T(svg, X(ordPhi(o)), 114, s, { 'text-anchor': 'middle', 'font-size': 12, fill: C.ink });
    });
    el('line', { x1: X(1), x2: X(1), y1: 82, y2: 98, stroke: C.ink, 'stroke-width': 2 }, svg);
    T(svg, X(1), 114, 'ω^ω', { 'text-anchor': 'middle', 'font-size': 12 });
    el('line', { x1: 730, x2: 730, y1: 78, y2: 102, stroke: C.meta, 'stroke-width': 3 }, svg);
    T(svg, 730, 118, 'ω₁', { 'text-anchor': 'middle', 'font-size': 15, 'font-weight': 800, fill: C.meta });
    T(svg, 30, 140, 'not to scale: an order-preserving squeeze of ω^ω into a segment · 非等比例：把 ω^ω 保序地压进一段线段', { 'font-size': 10.5, fill: C.muted });
  }
  async function run(i) {
    const my = ++tok;
    base();
    const S = ORD_SEQS[i];
    const terms = [];
    for (let n = 1; n <= 9; n++) {
      if (my !== tok) return;
      const o = S.f(n);
      terms.push(ordStr(o));
      const c = el('circle', { cx: X(ordPhi(o)), cy: 72, r: 5, fill: C.acc, class: 'pop' }, svg);
      el('title', {}, c).textContent = 'α' + sub(n) + ' = ' + ordStr(o);
      await sleep(260);
    }
    const lx = S.lim ? X(ordPhi(S.lim)) : X(1);
    el('path', { d: `M${lx},34 L${lx},62`, stroke: C.tr, 'stroke-width': 2.5, 'marker-end': '' }, svg);
    T(svg, lx, 28, 'sup = ' + S.limS, { 'text-anchor': 'middle', 'font-size': 13, 'font-weight': 700, fill: C.tr });
    okBox($('rulerMsg'), bi(`<span class="m">${S.name}</span>: ${terms.slice(0, 5).join(', ')}, … climb to <b>sup = ${S.limS}</b>, which is still countable, far below ω₁. If <span class="m">Aₙ ∈ Σ⁰_{αₙ}</span>, then <span class="m">αₙ + 1 &lt; ${S.limS}</span> for each n, so <span class="m">⋃ₙ Aₙ ∈ Σ⁰_{${S.limS}}</span>. A countable set of countable ordinals is always bounded below ω₁ (regularity of ω₁, using countable choice), so the levels below ω₁ are enough.`,
      `<span class="m">${S.name}</span>：${terms.slice(0, 5).join('，')}，……一路逼近 <b>sup = ${S.limS}</b>，它仍是可数序数，离 ω₁ 远得很。若 <span class="m">Aₙ ∈ Σ⁰_{αₙ}</span>，则对每个 n 有 <span class="m">αₙ + 1 &lt; ${S.limS}</span>，所以 <span class="m">⋃ₙ Aₙ ∈ Σ⁰_{${S.limS}}</span>。可数个可数序数总有一个小于 ω₁ 的上界（ω₁ 的正则性，用到可数选择），所以 ω₁ 以下的层就够用了。`), 'info');
  }
  document.querySelectorAll('[data-seq]').forEach(b => b.addEventListener('click', () => run(+b.dataset.seq)));
  base();
  okBox($('rulerMsg'), bi('Pick a sequence of levels αₙ. Where does its supremum land?', '选一列层级 αₙ，看看它的上确界落在哪里。'), 'info');
})();

/* ================= §3 big diamond ================= */
(function diamond() {
  const nodes = drawDiamond($('bigDia'), { cx: 235, dx: 120, base: 535, h: 44, K: 4, w: 78, hh: 32, full: true });
  const EX = [
    { n: ['N₀₁ (a cone)', 'N₀₁（一个锥）'], ex: { t: 'D', n: 1 },
      en: '<b>Clopen</b>: a basic open set whose complement is <span class="m">N₀₀ ∪ N₁₀ ∪ N₁₁</span>. It is in every class.', zh: '<b>既开又闭</b>：基本开集，补集为 <span class="m">N₀₀ ∪ N₁₀ ∪ N₁₁</span>。它属于每一个类。' },
    { n: ['“x has a 1”', '“x 含有 1”'], ex: { t: 'S', n: 1 },
      en: '<b>Upper:</b> <span class="m">⋃ₖ N_{0^k 1}</span> is open. <b>Lower:</b> not closed, since <span class="m">0^k10^∞ → 0^∞</span>, a limit that lies outside the set. Properly <span class="m">Σ⁰₁</span>.', zh: '<b>上界：</b><span class="m">⋃ₖ N_{0^k 1}</span> 是开集。<b>下界：</b>不是闭集，因为 <span class="m">0^k10^∞ → 0^∞</span>，极限却在集合之外。恰为 <span class="m">Σ⁰₁</span>。' },
    { n: ['{0^∞}', '{0^∞}'], ex: { t: 'P', n: 1 },
      en: '<b>Upper:</b> singletons are closed. <b>Lower:</b> not open, because every cone <span class="m">N_{0^k}</span> contains points other than <span class="m">0^∞</span>. Properly <span class="m">Π⁰₁</span>.', zh: '<b>上界：</b>单点集是闭集。<b>下界：</b>不是开集，因为每个锥 <span class="m">N_{0^k}</span> 都含有 <span class="m">0^∞</span> 以外的点。恰为 <span class="m">Π⁰₁</span>。' },
    { n: ['(N₀∖{0^∞}) ∪ {1^∞}', '(N₀∖{0^∞}) ∪ {1^∞}'], ex: { t: 'D', n: 2 },
      en: '<b>Upper:</b> a union of an open set and a closed set, both in <span class="m">Δ⁰₂</span>, which is closed under finite unions. <b>Lower:</b> not open (<span class="m">1^∞</span> is not an interior point) and not closed (<span class="m">0^∞</span> is a limit point outside it). Properly <span class="m">Δ⁰₂</span>.', zh: '<b>上界：</b>一个开集与一个闭集之并，二者都在 <span class="m">Δ⁰₂</span> 中，而 <span class="m">Δ⁰₂</span> 对有限并封闭。<b>下界：</b>不是开集（<span class="m">1^∞</span> 不是内点），也不是闭集（<span class="m">0^∞</span> 是它外面的极限点）。恰为 <span class="m">Δ⁰₂</span>。' },
    { n: ['“eventually 0”', '“最终为 0”'], ex: { t: 'S', n: 2 },
      en: '<b>Upper:</b> <span class="m">⋃ₙ ⋂_{m≥n} {x : x(m) = 0}</span>, a countable union of closed sets. <b>Lower:</b> it is countable and dense, so by Baire category it is not <span class="m">G_δ</span> (same proof as for ℚ in §4). Properly <span class="m">Σ⁰₂</span>.', zh: '<b>上界：</b><span class="m">⋃ₙ ⋂_{m≥n} {x : x(m) = 0}</span>，是闭集的可数并。<b>下界：</b>它可数且稠密，由贝尔纲定理它不是 <span class="m">G_δ</span>（证明同 §4 中的 ℚ）。恰为 <span class="m">Σ⁰₂</span>。' },
    { n: ['“infinitely many 1s”', '“有无穷多个 1”'], ex: { t: 'P', n: 2 },
      en: 'The complement of “eventually 0”. <span class="m">⋂ₙ ⋃_{m≥n} {x(m)=1}</span> is <span class="m">G_δ</span>, and it is not <span class="m">F_σ</span> because its complement is not <span class="m">G_δ</span>. Properly <span class="m">Π⁰₂</span>.', zh: '“最终为 0”的补集。<span class="m">⋂ₙ ⋃_{m≥n} {x(m)=1}</span> 是 <span class="m">G_δ</span>；又因为它的补集不是 <span class="m">G_δ</span>，所以它不是 <span class="m">F_σ</span>。恰为 <span class="m">Π⁰₂</span>。' },
    { n: ['ℚ ⊆ ℝ', 'ℚ ⊆ ℝ'], ex: { t: 'S', n: 2 },
      en: 'Properly <span class="m">Σ⁰₂</span> in ℝ: a countable union of singletons, and not <span class="m">G_δ</span> by the Baire argument of §4.', zh: '在 ℝ 中恰为 <span class="m">Σ⁰₂</span>：可数个单点集之并；由 §4 的贝尔论证，它不是 <span class="m">G_δ</span>。' },
    { n: ['ℝ ∖ ℚ', 'ℝ ∖ ℚ'], ex: { t: 'P', n: 2 },
      en: 'Properly <span class="m">Π⁰₂</span>: <span class="m">⋂_q (ℝ∖{q})</span>, and not <span class="m">F_σ</span> since ℚ is not <span class="m">G_δ</span>. It is Polish, being homeomorphic to <span class="m">ω^ω</span>.', zh: '恰为 <span class="m">Π⁰₂</span>：<span class="m">⋂_q (ℝ∖{q})</span>；又因 ℚ 不是 <span class="m">G_δ</span>，它不是 <span class="m">F_σ</span>。它同胚于 <span class="m">ω^ω</span>，是波兰空间。' },
    { n: ['P₃: every row eventually 0', 'P₃：每一行最终为 0'], ex: { t: 'P', n: 3 },
      en: 'In <span class="m">2^{ω×ω}</span>: <span class="m">P₃ = ⋂ₘ {x : row m of x is eventually 0}</span>, a countable intersection of <span class="m">Σ⁰₂</span> sets, so <span class="m">Π⁰₃</span>. It is in fact <span class="m">Π⁰₃</span>-complete, hence not <span class="m">Σ⁰₃</span> (Kechris, <i>Classical DST</i>, §23.A).', zh: '在 <span class="m">2^{ω×ω}</span> 中：<span class="m">P₃ = ⋂ₘ {x : x 的第 m 行最终为 0}</span>，是可数个 <span class="m">Σ⁰₂</span> 集之交，所以属于 <span class="m">Π⁰₃</span>。事实上它是 <span class="m">Π⁰₃</span>-完全的，因此不是 <span class="m">Σ⁰₃</span>（Kechris《Classical DST》§23.A）。' },
    { n: ['S₃ = complement of P₃', 'S₃ = P₃ 的补集'], ex: { t: 'S', n: 3 },
      en: '“Some row has infinitely many 1s”: properly <span class="m">Σ⁰₃</span>, by complementing the previous example.', zh: '“某一行有无穷多个 1”：对上一个例子取补，恰为 <span class="m">Σ⁰₃</span>。' },
    { n: ['IF: ill-founded trees', 'IF：非良基树'], ex: { t: 'S11' },
      en: '<span class="m">IF = {T : ∃y ∀n y↾n ∈ T}</span> is <span class="m">Σ¹₁</span> (the projection of a closed set), but it is <b>not Borel</b> (Lusin–Sierpiński; it is <span class="m">Σ¹₁</span>-complete). So it sits above every <span class="m">Σ⁰_α</span>, <span class="m">α &lt; ω₁</span>.', zh: '<span class="m">IF = {T : ∃y ∀n y↾n ∈ T}</span> 是 <span class="m">Σ¹₁</span>（闭集的投影），但<b>不是博雷尔集</b>（卢津–谢尔品斯基；它是 <span class="m">Σ¹₁</span>-完全的）。所以它高于每个 <span class="m">Σ⁰_α</span>（<span class="m">α &lt; ω₁</span>）。' },
    { n: ['WF: well-founded trees', 'WF：良基树'], ex: { t: 'P11' },
      en: '<span class="m">WF</span> = the complement of IF: properly <span class="m">Π¹₁</span>. Lesson 18 connects it to the computable ordinals, ω₁^CK.', zh: '<span class="m">WF</span> 是 IF 的补集：恰为 <span class="m">Π¹₁</span>。第 18 课把它与可计算序数 ω₁^CK 联系了起来。' },
  ];
  const box = $('diaChips');
  const chips = EX.map((e, i) => {
    const c = document.createElement('div');
    c.className = 'chip';
    c.innerHTML = bl(e.n[0], e.n[1]);
    c.addEventListener('click', () => pick(i));
    box.appendChild(c);
    return c;
  });
  function pick(i) {
    const e = EX[i];
    chips.forEach((c, j) => c.classList.toggle('sel', j === i));
    const exactKey = e.ex.t.length > 1 ? e.ex.t : e.ex.t + e.ex.n;
    paintNodes(nodes, k => (k === exactKey ? 'exact' : contains(e.ex, k) ? 'yes' : 'no'));
    okBox($('diaMsg'), bi(`<b>${e.n[0]}</b><br>${e.en}<br><span class="muted">Dark green = exact class; pale green = all classes containing it; grey = classes not containing it.</span>`,
      `<b>${e.n[1]}</b><br>${e.zh}<br><span class="muted">深绿＝恰好所在的类；浅绿＝所有包含它的类；灰色＝不包含它的类。</span>`), 'info');
  }
  pick(4);
})();

/* ================= §4 Baire category ================= */
(function baire() {
  const svg = $('qSvg');
  const X0 = 30, W = 700;
  const Q = rationals(60);
  let I, k, tok = 0, hist;
  function axis(y, a, b, label) {
    el('line', { x1: X0, x2: X0 + W, y1: y, y2: y, stroke: C.ink, 'stroke-width': 1.5 }, svg);
    T(svg, X0, y + 18, a, { 'font-size': 10.5, fill: C.muted, 'text-anchor': 'middle' });
    T(svg, X0 + W, y + 18, b, { 'font-size': 10.5, fill: C.muted, 'text-anchor': 'middle' });
    if (label) T(svg, X0, y - 22, label, { 'font-size': 11.5, fill: C.ink });
  }
  function reset() {
    tok++;
    svg.innerHTML = '';
    I = [0, 1]; k = 0; hist = [];
    axis(50, '0', '1', 'ℚ ∩ [0,1] = F₁ ∪ F₂ ∪ F₃ ∪ …   (Fₙ = {k/n} finite ⇒ closed) · 有限集 ⇒ 闭集');
    axis(145, '0', '1', 'global view: nested closed intervals I₀ ⊇ I₁ ⊇ … · 全局视图：套闭区间');
    el('g', { id: 'qRow1' }, svg);
    el('g', { id: 'qRow2' }, svg);
    el('g', { id: 'qRow3' }, svg);
    $('qStep').disabled = false;
    okBox($('qMsg'), bi('Press ① to see the upper bound, ② to run the Baire argument for the lower bound.', '按 ① 看上界，按 ② 运行贝尔论证得到下界。'), 'info');
  }
  $('qBuild').addEventListener('click', async () => {
    const my = ++tok;
    const g = $('qRow1'); g.innerHTML = '';
    const cols = ['#3b5bdb', '#2f9e44', '#f08c00', '#ae3ec9', '#e03131', '#1098ad'];
    for (let n = 1; n <= 16; n++) {
      if (my !== tok) return;
      for (let j = 0; j <= n; j++) {
        if (gcd(j, n) !== 1 && !(j === 0 && n === 1)) continue;
        const c = el('circle', { cx: X0 + W * j / n, cy: 50, r: Math.max(5 - n * 0.22, 1.8), fill: cols[n % cols.length], class: 'pop' }, g);
        el('title', {}, c).textContent = `${j}/${n} ∈ F${sub(n)}`;
      }
      okBox($('qMsg'), bi(`Added <span class="m">F${sub(n)}</span>. Each <span class="m">Fₙ</span> is finite, hence closed. So <span class="m">ℚ∩[0,1] = ⋃ₙ Fₙ</span> is <span class="m">F_σ = Σ⁰₂</span>.`, `加入 <span class="m">F${sub(n)}</span>。每个 <span class="m">Fₙ</span> 都是有限集，因而是闭集，所以 <span class="m">ℚ∩[0,1] = ⋃ₙ Fₙ</span> 是 <span class="m">F_σ = Σ⁰₂</span>。`), 'info');
      await sleep(170);
    }
  });
  const fmt = (v, d) => v.toFixed(Math.min(Math.max(d, 2), 12));
  $('qStep').addEventListener('click', () => {
    if (k >= 14) return;
    const [a, b] = I, L = b - a;
    let na, nb, msg;
    if (k % 2 === 0) {
      const n = k / 2;
      na = a + L * (0.1 + 0.56 * Math.random()); nb = na + L / 3;
      msg = bi(`<span class="m">I${sub(k)} ⊆ U${sub(n)}</span>: <span class="m">U${sub(n)}</span> is dense open, so it meets the interior of the previous interval in a nonempty open set. Choose a closed subinterval inside it. (The hypothetical <span class="m">U${sub(n)}</span> cannot be drawn, so this choice is schematic.)`,
        `<span class="m">I${sub(k)} ⊆ U${sub(n)}</span>：<span class="m">U${sub(n)}</span> 是稠密开集，与上一个区间的内部之交是非空开集，在其中选一个闭子区间。（假想中的 <span class="m">U${sub(n)}</span> 画不出来，这一步的选取只是示意。）`);
    } else {
      const m = (k - 1) / 2, [p, q] = Q[m], qv = p / q;
      if (qv >= a && qv <= b) {
        if (qv - a >= b - qv) { na = a + (qv - a) * 0.15; nb = a + (qv - a) * 0.65; }
        else { na = qv + (b - qv) * 0.35; nb = qv + (b - qv) * 0.85; }
        msg = bi(`<span class="m">I${sub(k)} ⊆ V${sub(m)} = ℝ∖{${p}/${q}}</span>: the rational <span class="m">q${sub(m)} = ${p}/${q}</span> (red) lies in the previous interval, so we pick a closed piece on its larger side.`,
          `<span class="m">I${sub(k)} ⊆ V${sub(m)} = ℝ∖{${p}/${q}}</span>：有理数 <span class="m">q${sub(m)} = ${p}/${q}</span>（红点）落在上一个区间里，于是在它较长的一侧取一个闭子区间。`);
      } else {
        na = a + L / 3; nb = a + 2 * L / 3;
        msg = bi(`<span class="m">I${sub(k)} ⊆ V${sub(m)} = ℝ∖{${p}/${q}}</span>: <span class="m">q${sub(m)} = ${p}/${q}</span> is not in the previous interval, so any closed subinterval avoids it.`,
          `<span class="m">I${sub(k)} ⊆ V${sub(m)} = ℝ∖{${p}/${q}}</span>：<span class="m">q${sub(m)} = ${p}/${q}</span> 不在上一个区间里，任取闭子区间都能避开它。`);
      }
    }
    // zoom row
    const g3 = $('qRow3'); g3.innerHTML = '';
    const d = Math.ceil(-Math.log10(L)) + 2;
    const y3 = 245;
    el('line', { x1: X0, x2: X0 + W, y1: y3, y2: y3, stroke: C.ink, 'stroke-width': 1.5 }, g3);
    T(g3, X0, y3 - 22, `zoom on I${k ? sub(k - 1) : '₋₁ = [0,1]'} · 放大上一个区间`, { 'font-size': 11.5, fill: C.ink });
    T(g3, X0, y3 + 18, fmt(a, d), { 'font-size': 10.5, fill: C.muted, 'text-anchor': 'start' });
    T(g3, X0 + W, y3 + 18, fmt(b, d), { 'font-size': 10.5, fill: C.muted, 'text-anchor': 'end' });
    const zx = v => X0 + W * (v - a) / L;
    const r = el('rect', { x: zx(a), y: y3 - 7, width: W, height: 14, rx: 4, fill: k % 2 ? C.faS : C.trS, opacity: 0.9 }, g3);
    r.style.transition = 'all .7s cubic-bezier(.2,.9,.3,1)';
    if (k % 2) {
      const [p, q] = Q[(k - 1) / 2], qv = p / q;
      if (qv >= a && qv <= b) { el('circle', { cx: zx(qv), cy: y3, r: 6, fill: C.fa, class: 'pop' }, g3); T(g3, zx(qv), y3 - 12, `${p}/${q}`, { 'text-anchor': 'middle', 'font-size': 11, fill: C.fa, 'font-weight': 700 }); }
    }
    requestAnimationFrame(() => requestAnimationFrame(() => {
      r.setAttribute('x', zx(na)); r.setAttribute('width', zx(nb) - zx(na));
      r.setAttribute('fill', k % 2 ? C.acc : C.tr);
    }));
    T(g3, (zx(na) + zx(nb)) / 2, y3 + 34, `I${sub(k)} ${k % 2 ? '⊆ V' + sub((k - 1) / 2) : '⊆ U' + sub(k / 2)}`, { 'text-anchor': 'middle', 'font-size': 12, 'font-weight': 700, fill: k % 2 ? C.acc : C.tr });
    // global row
    const g2 = $('qRow2');
    const gx = v => X0 + W * v;
    el('rect', { x: gx(na), y: 145 - 8 + (k % 4) * 0, width: Math.max(gx(nb) - gx(na), 2), height: 16, fill: k % 2 ? C.acc : C.tr, opacity: 0.25 + 0.05 * k }, g2);
    hist.push([na, nb]);
    I = [na, nb]; k++;
    const mark = g2.querySelector('.mk') || el('path', { class: 'mk', fill: C.meta }, g2);
    const mx = gx((na + nb) / 2);
    mark.setAttribute('d', `M${mx},128 l-6,-10 l12,0 z`);
    if (k >= 14) {
      $('qStep').disabled = true;
      msg += bi(`<br><b>The lengths shrink to 0, so the intervals close down on one point <span class="m">x* ≈ ${fmt((na + nb) / 2, d + 1)}</span>.</b> Continuing forever, <span class="m">x*</span> lies in every <span class="m">Uₙ</span>, so <span class="m">x* ∈ ℚ</span>, and in every <span class="m">Vₘ</span>, so <span class="m">x* ∉ ℚ</span>. Contradiction: ℚ is not <span class="m">G_δ</span>.`,
        `<br><b>区间长度趋于 0，最终收缩到一点 <span class="m">x* ≈ ${fmt((na + nb) / 2, d + 1)}</span>。</b>无限进行下去，<span class="m">x*</span> 属于每个 <span class="m">Uₙ</span>，所以 <span class="m">x* ∈ ℚ</span>；它又属于每个 <span class="m">Vₘ</span>，所以 <span class="m">x* ∉ ℚ</span>。矛盾：ℚ 不是 <span class="m">G_δ</span>。`);
    }
    okBox($('qMsg'), msg, k >= 14 ? 'ok' : 'info');
  });
  $('qReset').addEventListener('click', reset);
  reset();
  $('qBuild').click();
})();

/* ================= §5 diagonal ================= */
(function diagonal() {
  const svg = $('dgSvg');
  const N = 7, X0 = 360, CW = 52, Y0 = 70, RH = 44;
  let codes = [], M = [], tok = 0;
  function gen() {
    for (let tries = 0; tries < 500; tries++) {
      const seen = new Set();
      codes = [];
      while (codes.length < N) {
        const c = Array.from({ length: 8 }, () => (Math.random() < 0.28 ? 1 : 0));
        const key = c.join('');
        if (c.some(Boolean) && !seen.has(key)) { seen.add(key); codes.push(c); }
      }
      M = codes.map(y => codes.map(x => inU(y, x)));
      const diag = M.filter((r, i) => r[i]).length, tot = M.flat().filter(Boolean).length;
      if (diag >= 2 && diag <= N - 2 && tot >= 0.3 * N * N && tot <= 0.7 * N * N) return;
    }
  }
  const cones = c => c.map((b, n) => b ? 'N' + sub(strOf(n)) : null).filter(Boolean).join(' ∪ ');
  function draw() {
    tok++;
    svg.innerHTML = '';
    T(svg, 10, 22, 'code y → open set U_y · 编码 → 开集', { 'font-size': 11.5, fill: C.muted });
    T(svg, X0 + N * CW / 2, 22, 'points (the same reals!) · 点（同一批实数！）', { 'font-size': 11.5, fill: C.muted, 'text-anchor': 'middle' });
    for (let j = 0; j < N; j++) T(svg, X0 + j * CW + CW / 2, Y0 - 12, 'y' + sub(j), { 'text-anchor': 'middle', 'font-size': 14, 'font-weight': 700, fill: C.gold });
    codes.forEach((c, i) => {
      const y = Y0 + i * RH + RH / 2 + 5;
      T(svg, 10, y, `y${sub(i)} = ${c.join('')}000…`, { 'font-size': 12, fill: C.ink });
      T(svg, 152, y, '→ ' + cones(c), { 'font-size': 11, fill: C.acc, 'font-weight': 700 });
      for (let j = 0; j < N; j++) {
        el('rect', { x: X0 + j * CW + 3, y: Y0 + i * RH + 3, width: CW - 6, height: RH - 6, rx: 7, fill: M[i][j] ? C.trS : C.faS, id: `dg${i}_${j}` }, svg);
        T(svg, X0 + j * CW + CW / 2, y, M[i][j] ? '✓' : '✗', { 'text-anchor': 'middle', 'font-size': 15, fill: M[i][j] ? C.tr : C.fa });
      }
    });
    T(svg, 10, Y0 + N * RH + 20, '⋮ (all 2^ℵ₀ codes; every open set appears as some row) · 所有编码；每个开集都是某一行', { 'font-size': 11, fill: C.muted });
    okBox($('dgMsg'), bi('Row i lists which points <span class="m">y_j</span> lie in <span class="m">U_{y_i}</span>. These entries are computed exactly: <span class="m">y_j ∈ U_{y_i}</span> iff some chosen <span class="m">sₙ</span> is an initial segment of <span class="m">y_j</span>.', '第 i 行列出哪些点 <span class="m">y_j</span> 属于 <span class="m">U_{y_i}</span>。这些格子是精确计算的：<span class="m">y_j ∈ U_{y_i}</span> 当且仅当某个选中的 <span class="m">sₙ</span> 是 <span class="m">y_j</span> 的初始段。'), 'info');
  }
  async function run() {
    draw();
    const my = tok;
    const yD = Y0 + N * RH + 40;
    T(svg, 10, yD + RH / 2 + 5, 'D = {y : y ∉ U_y}', { 'font-size': 14, 'font-weight': 800, fill: C.meta });
    T(svg, 175, yD + RH / 2 + 5, '(flip the diagonal · 翻转对角线)', { 'font-size': 11, fill: C.meta });
    for (let k = 0; k < N; k++) {
      await sleep(480);
      if (my !== tok) return;
      const cell = svg.querySelector(`#dg${k}_${k}`);
      cell.setAttribute('stroke', C.meta); cell.setAttribute('stroke-width', 3.5);
      const inD = !M[k][k];
      el('rect', { x: X0 + k * CW + 3, y: yD + 3, width: CW - 6, height: RH - 6, rx: 7, fill: C.metaS, stroke: C.meta, 'stroke-width': 2, class: 'pop' }, svg);
      T(svg, X0 + k * CW + CW / 2, yD + RH / 2 + 5, inD ? '✓' : '✗', { 'text-anchor': 'middle', 'font-size': 15, 'font-weight': 800, fill: C.meta });
    }
    await sleep(300);
    if (my !== tok) return;
    okBox($('dgMsg'), bi('<b>D disagrees with row i at column i</b>, for every i: <span class="m">y_i ∈ D ⇔ y_i ∉ U_{y_i}</span>. Since every open set is some row <span class="m">U_y</span>, D is <b>not open</b>. But <span class="m">D = {y : (y,y) ∉ U}</span> is the continuous preimage of the closed set <span class="m">U^c</span>, so D is <b>closed</b>: <span class="m">D ∈ Π⁰₁ ∖ Σ⁰₁</span>. With universal sets for <span class="m">Σ⁰_α</span>, the same diagonal works at every level <span class="m">α &lt; ω₁</span>.',
      '<b>对每个 i，D 在第 i 列与第 i 行不同</b>：<span class="m">y_i ∈ D ⇔ y_i ∉ U_{y_i}</span>。由于每个开集都是某一行 <span class="m">U_y</span>，D <b>不是开集</b>。但 <span class="m">D = {y : (y,y) ∉ U}</span> 是闭集 <span class="m">U^c</span> 的连续原像，所以 D 是<b>闭集</b>：<span class="m">D ∈ Π⁰₁ ∖ Σ⁰₁</span>。只要有 <span class="m">Σ⁰_α</span> 的万有集，同样的对角线在每一层 <span class="m">α &lt; ω₁</span> 都管用。'), 'ok');
  }
  $('dgGo').addEventListener('click', run);
  $('dgNew').addEventListener('click', () => { gen(); draw(); });
  gen(); draw();
})();

/* ================= §6 lightface / boldface ================= */
(function lightface() {
  const v = {};
  const names = [];
  for (let n = 0; n < 8; n++) { const nm = `a(${n})`; names.push(nm); v[nm] = [1, 3, 6].includes(n) ? 1 : 0; }
  let tail = '0';
  const svg = $('aSvg');
  const X0 = 150, W = 590;
  const cxL = s => X0 + W * cantorLeft(s);
  function draw() {
    svg.innerHTML = '';
    const code = names.map(nm => v[nm]);
    for (let n = 0; n < 8; n++) {
      const s = strOf(n), y = 8 + n * 12;
      T(svg, 4, y + 8, `n=${n}: s${sub(n)} = ${s || '∅'}`, { 'font-size': 10, fill: code[n] ? C.acc : C.muted, 'font-weight': code[n] ? 700 : 400 });
      el('rect', { x: cxL(s), y, width: W * cantorLen(s), height: 8, rx: 2, fill: code[n] ? C.acc : '#e6e2d6' }, svg);
    }
    const yb = 112;
    T(svg, 4, yb + 9, 'G_a (union) · 并集', { 'font-size': 11, 'font-weight': 700, fill: C.ink });
    for (let m = 0; m < 64; m++) {
      const t = m.toString(2).padStart(6, '0');
      const inG = code.some((b, n) => b && t.startsWith(strOf(n)));
      el('rect', { x: cxL(t), y: yb, width: Math.max(W * cantorLen(t), 1.2), height: 12, fill: inG ? C.tr : '#cfcabb' }, svg);
    }
    if (tail === 'K') {
      el('rect', { x: X0, y: yb - 2, width: W, height: 16, fill: 'url(#hatch)', opacity: 0.6 }, svg);
      const defs = el('defs', {}, svg);
      const p = el('pattern', { id: 'hatch', width: 6, height: 6, patternUnits: 'userSpaceOnUse', patternTransform: 'rotate(45)' }, defs);
      el('line', { x1: 0, y1: 0, x2: 0, y2: 6, stroke: C.gold, 'stroke-width': 2 }, p);
      T(svg, X0 + W, yb + 32, '+ N_{sₙ} for n ∈ K, n ≥ 8: enumerable, never finished · 可枚举，但永远列不完', { 'font-size': 10.5, fill: '#9a5b00', 'text-anchor': 'end' });
    } else T(svg, X0 + W, yb + 32, 'a(n) = 0 for n ≥ 8', { 'font-size': 10.5, fill: C.muted, 'text-anchor': 'end' });
    const chosen = code.map((b, n) => b ? `N<sub>${strOf(n) || '∅'}</sub>` : null).filter(Boolean);
    const set = chosen.length ? chosen.join(' ∪ ') : '∅';
    if (tail === '0') okBox($('aMsg'), bi(`<span class="m">G_a = ${set}</span>. This code is finite, hence computable, so <span class="m">G_a</span> is <b>lightface</b> <span class="m">Σ⁰₁</span> (indeed clopen). For an arbitrary real <span class="m">a</span>, <span class="m">G_a</span> is <span class="m">Σ⁰₁(a)</span>, and as a ranges over all reals we get <b>every</b> open set: <span class="m">𝚺⁰₁ = ⋃ₐ Σ⁰₁(a)</span>.`,
      `<span class="m">G_a = ${set}</span>。这个编码是有限的，因而可计算，所以 <span class="m">G_a</span> 是<b>细体</b> <span class="m">Σ⁰₁</span>（实际上既开又闭）。对任意实数 <span class="m">a</span>，<span class="m">G_a</span> 是 <span class="m">Σ⁰₁(a)</span>；让 a 跑遍所有实数，就得到<b>所有</b>开集：<span class="m">𝚺⁰₁ = ⋃ₐ Σ⁰₁(a)</span>。`), 'info');
    else okBox($('aMsg'), bi(`<span class="m">G_a = ${set} ∪ ⋃_{n∈K, n≥8} N_{sₙ}</span>. The code <span class="m">a</span> is <b>not computable</b> (it encodes the halting problem). Still, <span class="m">G_a</span> is <b>lightface</b> <span class="m">Σ⁰₁</span>: we can <i>enumerate</i> its cones by running all programs, and an effectively open set needs nothing more. Hatched = cones that keep arriving forever. There are only ℵ₀ lightface sets but 2^ℵ₀ open sets, so most open sets are not lightface.`,
      `<span class="m">G_a = ${set} ∪ ⋃_{n∈K, n≥8} N_{sₙ}</span>。编码 <span class="m">a</span> <b>不可计算</b>（它编码了停机问题），但 <span class="m">G_a</span> 仍是<b>细体</b> <span class="m">Σ⁰₁</span>：运行所有程序就能把它的锥<i>逐个枚举</i>出来，而能行开集只需要这一点。阴影表示永远在陆续到来的锥。细体集只有 ℵ₀ 个，开集却有 2^ℵ₀ 个，所以绝大多数开集都不是细体的。`), 'info');
  }
  Switches($('aSw'), names, v, draw);
  document.querySelectorAll('[data-tail]').forEach(b => b.addEventListener('click', () => {
    tail = b.dataset.tail;
    document.querySelectorAll('[data-tail]').forEach(x => x.classList.toggle('sel', x === b));
    draw();
  }));
  draw();
})();

/* ================= §7 projection ================= */
(function projection() {
  const svg = $('projSvg');
  const XL = 70, XR = 720, YT = 30, YB = 250, AX = 300;
  const SHAPES = [
    [{ cx: 190, cy: 110, rx: 75, ry: 40 }, { cx: 300, cy: 200, rx: 50, ry: 28 }, { cx: 545, cy: 120, rx: 95, ry: 38 }],
    [0, 1, 2, 3, 4, 5].map(i => ({ cx: 120 + i * 105, cy: 70 + (i % 3) * 65, rx: 14 + (i % 2) * 12, ry: 30 }))
  ];
  let shape = 0, scanX = 250, mode = 'proj', tok = 0;
  const shadow = () => {
    const iv = SHAPES[shape].map(e => [e.cx - e.rx, e.cx + e.rx]).sort((a, b) => a[0] - b[0]);
    const out = [];
    iv.forEach(([a, b]) => { if (out.length && a <= out[out.length - 1][1]) out[out.length - 1][1] = Math.max(out[out.length - 1][1], b); else out.push([a, b]); });
    return out;
  };
  const section = x => SHAPES[shape].filter(e => Math.abs(x - e.cx) < e.rx).map(e => { const h = e.ry * Math.sqrt(1 - ((x - e.cx) / e.rx) ** 2); return [e.cy - h, e.cy + h]; });
  function frame() {
    svg.innerHTML = '';
    el('rect', { x: XL, y: YT, width: XR - XL, height: YB - YT, fill: '#fbfaf6', stroke: C.line }, svg);
    el('line', { x1: XL, x2: XR, y1: AX, y2: AX, stroke: C.ink, 'stroke-width': 2 }, svg);
    T(svg, XR + 6, AX + 4, 'X', { 'font-size': 14, 'font-weight': 700 });
    const lab = T(svg, 0, 0, mode === 'leb' ? 'ℝ (heights n = 0,1,2,…)' : 'Y = ω^ω', { 'font-size': 12, fill: C.muted, 'text-anchor': 'middle', transform: `translate(${XL - 14},${(YT + YB) / 2}) rotate(-90)` });
    lab.setAttribute('x', 0); lab.setAttribute('y', 0);
  }
  function drawProj(showShadow) {
    frame();
    const g = el('g', {}, svg);
    SHAPES[shape].forEach(e => el('ellipse', { cx: e.cx, cy: e.cy, rx: e.rx, ry: e.ry, fill: 'rgba(59,91,219,.22)', stroke: C.acc, 'stroke-width': 2 }, g));
    T(svg, XL + 8, YT + 16, 'C (closed) · 闭集 C', { 'font-size': 12, fill: C.acc, 'font-weight': 700 });
    const gs = el('g', { id: 'shadowG' }, svg);
    if (showShadow) shadow().forEach(([a, b]) => el('rect', { x: a, y: AX - 6, width: b - a, height: 12, rx: 3, fill: C.gold, class: 'fadein' }, gs));
    T(svg, XL, AX + 30, 'shadow p[C] = {x : ∃y (x,y) ∈ C} · 影子', { 'font-size': 12, fill: '#9a5b00', 'font-weight': 700 });
    drawScan();
  }
  function drawScan() {
    svg.querySelectorAll('.scan').forEach(n => n.remove());
    const g = el('g', { class: 'scan' }, svg);
    el('line', { x1: scanX, x2: scanX, y1: YT - 8, y2: AX + 8, stroke: C.meta, 'stroke-width': 2, 'stroke-dasharray': '5 4' }, g);
    const sec = section(scanX);
    sec.forEach(([a, b]) => el('line', { x1: scanX, x2: scanX, y1: a, y2: b, stroke: C.fa, 'stroke-width': 6, 'stroke-linecap': 'round' }, g));
    el('circle', { cx: scanX, cy: AX, r: 7, fill: sec.length ? C.tr : '#fff', stroke: sec.length ? C.tr : C.fa, 'stroke-width': 3 }, g);
    el('rect', { x: scanX - 10, y: YT - 22, width: 20, height: 14, rx: 4, fill: C.meta, style: 'cursor:ew-resize' }, g);
    T(g, scanX, YT - 12, '⇔', { 'text-anchor': 'middle', 'font-size': 10, fill: '#fff' });
    okBox($('projMsg'), sec.length
      ? bi('The section <span class="m">C_x</span> (red) is <b>nonempty</b>: some y has <span class="m">(x,y) ∈ C</span>, so <span class="m">x ∈ p[C]</span>.', '截面 <span class="m">C_x</span>（红色）<b>非空</b>：存在 y 使 <span class="m">(x,y) ∈ C</span>，所以 <span class="m">x ∈ p[C]</span>。')
      : bi('The section <span class="m">C_x</span> is <b>empty</b>: no witness y exists, so <span class="m">x ∉ p[C]</span>. Drag the purple handle.', '截面 <span class="m">C_x</span> 是<b>空的</b>：不存在见证 y，所以 <span class="m">x ∉ p[C]</span>。拖动紫色把手试试。'), sec.length ? 'ok' : 'info');
  }
  let drag = false;
  const toX = ev => { const r = svg.getBoundingClientRect(); return Math.min(XR - 2, Math.max(XL + 2, (ev.clientX - r.left) * 760 / r.width)); };
  svg.addEventListener('pointerdown', ev => { if (mode !== 'proj') return; drag = true; scanX = toX(ev); drawScan(); svg.setPointerCapture(ev.pointerId); });
  svg.addEventListener('pointermove', ev => { if (drag) { scanX = toX(ev); drawScan(); } });
  svg.addEventListener('pointerup', () => { drag = false; });
  svg.style.touchAction = 'none';
  async function sun() {
    if (mode !== 'proj') { mode = 'proj'; }
    const my = ++tok;
    drawProj(false);
    const rays = el('g', {}, svg);
    const xs = [];
    for (let x = XL + 6; x < XR; x += 9) xs.push(x);
    const lines = xs.map(x => {
      const sec = section(x);
      const stop = sec.length ? Math.min(...sec.map(s => s[0])) : AX;
      return { l: el('line', { x1: x, x2: x, y1: YT - 10, y2: YT - 10, stroke: C.gold, 'stroke-width': 1.4, opacity: 0.8 }, rays), stop };
    });
    const t0 = performance.now();
    await new Promise(res => {
      (function f(t) {
        if (my !== tok) return res();
        const p = Math.min(1, (t - t0) / 900);
        lines.forEach(o => o.l.setAttribute('y2', YT - 10 + (o.stop - YT + 10) * p));
        if (p < 1) requestAnimationFrame(f); else res();
      })(t0);
    });
    if (my !== tok) return;
    shadow().forEach(([a, b]) => el('rect', { x: a, y: AX - 6, width: b - a, height: 12, rx: 3, fill: '#5c5c5c', class: 'fadein' }, $('shadowG')));
    okBox($('projMsg'), bi('Light blocked by C leaves a dark shadow on X: exactly the x whose vertical line meets C. That is the projection, i.e. the quantifier <span class="m">∃y</span>.', '被 C 挡住的光在 X 上留下黑影：恰好是那些竖线碰到 C 的 x。这就是投影，也就是量词 <span class="m">∃y</span>。'), 'ok');
  }
  async function lebesgue() {
    const my = ++tok;
    mode = 'leb';
    for (let n = 0; n <= 6; n++) {
      if (my !== tok) return;
      frame();
      const yn = YB - n * 34;
      for (let j = 0; j <= 6; j++) {
        el('line', { x1: XL - 4, x2: XL, y1: YB - j * 34, y2: YB - j * 34, stroke: C.muted }, svg);
        T(svg, XL - 6, YB - j * 34 + 4, String(j), { 'font-size': 10, fill: C.muted, 'text-anchor': 'end' });
      }
      if (n < 6) {
        el('rect', { x: XL, y: YT, width: XR - XL, height: Math.max(yn - YT, 0), fill: 'rgba(174,62,201,.22)', stroke: C.meta, 'stroke-width': 2 }, svg);
        T(svg, (XL + XR) / 2, Math.max(yn - 10, YT + 16), `Bₙ = X × [${n}, ∞), n = ${n}   ↑ continues to ∞ · 向上延伸到 ∞`, { 'text-anchor': 'middle', 'font-size': 12, fill: C.meta, 'font-weight': 700 });
        el('rect', { x: XL, y: AX - 6, width: XR - XL, height: 12, rx: 3, fill: C.gold }, svg);
        T(svg, XL, AX + 30, `p[B${sub(n)}] = X  (whole axis · 整条轴)`, { 'font-size': 12, fill: '#9a5b00', 'font-weight': 700 });
      } else {
        T(svg, (XL + XR) / 2, (YT + YB) / 2, '⋂ₙ Bₙ = ∅', { 'text-anchor': 'middle', 'font-size': 22, fill: C.meta, 'font-weight': 800 });
        T(svg, XL, AX + 30, 'p[⋂ₙ Bₙ] = ∅   but   ⋂ₙ p[Bₙ] = X', { 'font-size': 13, fill: C.fa, 'font-weight': 800 });
      }
      await sleep(n < 6 ? 700 : 0);
    }
    okBox($('projMsg'), bi('Each <span class="m">Bₙ</span> is closed, the sequence decreases, and every shadow is all of X. Yet no point lies above <i>every</i> height n, so <span class="m">⋂Bₙ = ∅</span>. <b>Projection commutes with unions but not with decreasing intersections.</b> That was the hidden gap in Lebesgue\'s 1905 argument.', '每个 <span class="m">Bₙ</span> 都是闭集，序列递减，每个影子都是整个 X。可是没有哪个点高于<i>所有</i>高度 n，所以 <span class="m">⋂Bₙ = ∅</span>。<b>投影与并可交换，却与递减交不可交换。</b>这正是勒贝格 1905 年论证中暗藏的漏洞。'), 'warn');
  }
  document.querySelectorAll('[data-shape]').forEach(b => b.addEventListener('click', () => {
    tok++; shape = +b.dataset.shape; mode = 'proj';
    document.querySelectorAll('[data-shape]').forEach(x => x.classList.toggle('sel', x === b));
    drawProj(true);
  }));
  $('sunBtn').addEventListener('click', sun);
  $('lebBtn').addEventListener('click', lebesgue);
  drawProj(true);
})();

/* ================= §8 projective ladder ================= */
(function ladder() {
  const svg = $('ladSvg');
  const P = { B: [195, 410], S1: [95, 350], P1: [295, 350], D2: [195, 290], S2: [95, 230], P2: [295, 230], D3: [195, 170], S3: [95, 110], P3: [295, 110], D4: [195, 50] };
  const keyOf = st => (st.t === 'D' && st.n === 1) ? 'B' : st.t + st.n;
  el('line', { x1: 95, x2: 95, y1: 365, y2: 95, stroke: '#cfc9b8', 'stroke-width': 6, 'stroke-linecap': 'round' }, svg);
  el('line', { x1: 295, x2: 295, y1: 365, y2: 95, stroke: '#cfc9b8', 'stroke-width': 6, 'stroke-linecap': 'round' }, svg);
  [[ 'B', 'S1'], ['B', 'P1'], ['S1', 'D2'], ['P1', 'D2'], ['D2', 'S2'], ['D2', 'P2'], ['S2', 'D3'], ['P2', 'D3'], ['D3', 'S3'], ['D3', 'P3'], ['S3', 'D4'], ['P3', 'D4']]
    .forEach(([a, b]) => el('line', { x1: P[a][0], y1: P[a][1], x2: P[b][0], y2: P[b][1], stroke: '#e0dbcd', 'stroke-width': 2 }, svg));
  const lbl = { B: 'Borel = Δ¹₁', S1: 'Σ¹₁', P1: 'Π¹₁', D2: 'Δ¹₂', S2: 'Σ¹₂', P2: 'Π¹₂', D3: 'Δ¹₃', S3: 'Σ¹₃', P3: 'Π¹₃', D4: 'Δ¹₄' };
  const nodes = {};
  Object.keys(P).forEach(k => {
    const [x, y] = P[k], w = k === 'B' ? 120 : 64;
    const r = el('rect', { x: x - w / 2, y: y - 15, width: w, height: 30, rx: 9, fill: '#fff', stroke: '#b9b4a6', 'stroke-width': 2 }, svg);
    r.style.transition = 'fill .3s';
    T(svg, x, y + 5, lbl[k], { 'text-anchor': 'middle', 'font-size': 14, 'font-weight': 700 });
    nodes[k] = r;
  });
  T(svg, 195, 20, '⋮  projective = ⋃ₙ Σ¹ₙ', { 'text-anchor': 'middle', 'font-size': 12, fill: C.muted });
  T(svg, 20, 434, 'rails: ∃ (left, Σ) and ∀ (right, Π) · 左轨 ∃，右轨 ∀', { 'font-size': 10.5, fill: C.muted });
  const tokG = el('g', {}, svg);
  tokG.style.transition = 'transform .6s cubic-bezier(.2,1.3,.4,1)';
  el('circle', { cx: 0, cy: 0, r: 9, fill: C.gold, stroke: '#fff', 'stroke-width': 2 }, tokG);
  let st = { h: 1, t: 'D', n: 1 }, tok = 0;
  const qs = (first, n) => { const out = []; let q = first; for (let i = 1; i <= n; i++) { out.push(q + 'y' + sub(i)); q = q === '∃' ? '∀' : '∃'; } return out.join(' '); };
  function render(msg) {
    const k = keyOf(st);
    Object.entries(nodes).forEach(([kk, r]) => r.setAttribute('fill', kk === k ? C.goldS : '#fff'));
    const pos = P[k] || [195, 50];
    tokG.setAttribute('transform', `translate(${pos[0] + (k === 'B' ? 70 : 40)},${pos[1] - 12})`);
    const big = $('ladBig');
    big.textContent = k === 'B' ? 'Δ¹₁ = Borel' : clsName(st);
    big.classList.remove('bump'); void big.offsetWidth; big.classList.add('bump');
    let form;
    if (k === 'B') form = bi('x ∈ A ⇔ x ∈ B, with B Borel (no real quantifier needed)', 'x ∈ A ⇔ x ∈ B，B 为博雷尔集（不需要实数量词）');
    else if (st.t === 'S') form = `x ∈ A ⇔ ${qs('∃', st.n)} (x, ȳ) ∈ B` + bi('&nbsp; (B Borel)', '&nbsp;（B 为博雷尔集）');
    else if (st.t === 'P') form = `x ∈ A ⇔ ${qs('∀', st.n)} (x, ȳ) ∈ B` + bi('&nbsp; (B Borel)', '&nbsp;（B 为博雷尔集）');
    else form = bi(`A has <b>both</b> a Σ¹${sub(st.n)} and a Π¹${sub(st.n)} definition`, `A <b>同时</b>有 Σ¹${sub(st.n)} 定义与 Π¹${sub(st.n)} 定义`);
    if (st.n > 4 || (st.n === 4 && st.t !== 'D')) form += bi('<br>(above the drawn ladder)', '<br>（已超出图中画出的阶梯）');
    $('ladForm').innerHTML = form;
    if (msg) okBox($('ladMsg'), msg[0], msg[1]); else clearBox($('ladMsg'));
  }
  function apply(op) {
    const old = st;
    st = climb(st, op);
    let m;
    if (op === 'N') m = [bi('Complement: ∃ ↔ ∀ (push ¬ inside, so Σ ↔ Π). Δ stays Δ.', '取补：∃ ↔ ∀（把 ¬ 推进去，Σ ↔ Π），Δ 仍是 Δ。'), 'info'];
    else if (op === 'U') m = [bi('Countable unions and intersections do not climb: each Σ¹ₙ, Π¹ₙ, Δ¹ₙ is a σ-algebra-like class closed under both.', '可数并与可数交不会上升：每个 Σ¹ₙ、Π¹ₙ、Δ¹ₙ 对二者都封闭。'), 'info'];
    else if (st.n > old.n || (old.t === 'D' && old.n === 1)) m = [bi(`<b>Climbed</b> to ${clsName(st)}: a new alternation of real quantifiers.`, `<b>上升</b>到 ${clsName(st)}：多了一次实数量词交替。`), 'ok'];
    else if (old.t === 'D') m = [bi(`${clsName(st)}: Δ¹${sub(old.n)} ⊆ ${clsName(st)}, which is closed under ${op === 'E' ? '∃' : '∀'}. No climb.`, `${clsName(st)}：Δ¹${sub(old.n)} ⊆ ${clsName(st)}，而后者对 ${op === 'E' ? '∃' : '∀'} 封闭。不上升。`), 'warn'];
    else m = [bi(`<b>No climb!</b> ${op === 'E' ? '∃y₁∃y₂' : '∀y₁∀y₂'} merges into a single quantifier via a pairing homeomorphism <span class="m">ω^ω × ω^ω ≅ ω^ω</span>.`, `<b>不上升！</b>${op === 'E' ? '∃y₁∃y₂' : '∀y₁∀y₂'} 借助配对同胚 <span class="m">ω^ω × ω^ω ≅ ω^ω</span> 合并成一个量词。`), 'warn'];
    render(m);
  }
  document.querySelectorAll('[data-lop]').forEach(b => b.addEventListener('click', () => { tok++; apply(b.dataset.lop); }));
  $('ladReset').addEventListener('click', () => { tok++; st = { h: 1, t: 'D', n: 1 }; render(); });
  $('ladAuto').addEventListener('click', async () => {
    const my = ++tok;
    st = { h: 1, t: 'D', n: 1 }; render();
    for (const op of ['E', 'N', 'E', 'E', 'N', 'E']) {
      await sleep(1000);
      if (my !== tok) return;
      apply(op);
    }
  });
  render([bi('Start from the Borel sets (= Δ¹₁). Press ∃y.', '从博雷尔集（= Δ¹₁）出发，按 ∃y。'), 'info']);
})();

/* ================= §9 regularity ================= */
(function regularity() {
  const COLS = [['ZFC', 'ZFC', 'ZFC'], ['L', 'V = L', 'V = L'], ['MC', 'ZFC + ∃ measurable', 'ZFC + 存在可测基数'], ['PD', 'ZFC + PD', 'ZFC + PD']];
  const ROWN = { S11: 'Σ¹₁', P11: 'Π¹₁', D12: 'Δ¹₂', S12: 'Σ¹₂', P12: 'Π¹₂', S13: ['Σ¹₃, Π¹₃, … (higher)', 'Σ¹₃、Π¹₃……（更高）'], ALL: ['all sets of reals', '所有实数集'] };
  const rowLabel = r => Array.isArray(ROWN[r]) ? bil(ROWN[r][0], ROWN[r][1]) : `<span class="m">${ROWN[r]}</span>`;
  let col = 'ZFC';
  const tbl = $('regTable');
  function why(c, r) {
    if (r === 'ALL') return bi('ZFC (the axiom of choice) builds sets with none of the properties: a Vitali set is not LM and lacks BP; a Bernstein set (it meets every perfect set, and so does its complement) is uncountable without a perfect subset, and also fails LM and BP. This holds in every column, because each theory includes ZFC.', 'ZFC（选择公理）能造出三条性质都不满足的集合：维塔利集不可测且无 BP；伯恩斯坦集（它和它的补集都与每个完美集相交）不可数却不含完美子集，同样不 LM、无 BP。每一列都包含 ZFC，所以每一列都如此。');
    if (r === 'S11') return bi('ZFC theorem: analytic sets have PSP (Suslin) and are LM and BP (Lusin–Sierpiński). Every extension of ZFC inherits this.', 'ZFC 定理：解析集有 PSP（Suslin），且 LM、BP（卢津–谢尔品斯基）。ZFC 的任何扩张都继承这一点。');
    if (c === 'PD') return bi('PD ⇒ every projective set is LM (Mycielski–Świerczkowski), BP (Banach–Mazur games) and has PSP (Davis), via games whose payoff sets are projective. PD itself follows from infinitely many Woodin cardinals (Martin–Steel); see L25.', 'PD ⇒ 每个投影集都 LM（Mycielski–Świerczkowski）、BP（Banach–Mazur 博弈）、有 PSP（Davis），证明都用支付集为投影集的博弈。PD 本身可由无穷多个伍丁基数推出（Martin–Steel）；见第 25 课。');
    if (c === 'L') {
      if (r === 'P11') return bi('LM and BP: still ZFC theorems (complements of analytic sets). PSP fails: in L there is an uncountable Π¹₁ set with no perfect subset (Gödel). Note that Π¹₁ is the very first level where this can happen.', 'LM 与 BP：仍是 ZFC 定理（解析集的补）。PSP 不成立：在 L 中存在不含完美子集的不可数 Π¹₁ 集（哥德尔）。注意 Π¹₁ 正是可能出现这种情况的最低一层。');
      return bi('Gödel: L has a Δ¹₂ well-ordering ≤_L of ℝ in which every proper initial segment is countable. W = {(x,y) : x ≤_L y} ⊆ ℝ² is Δ¹₂. Its vertical sections are countable and its horizontal sections co-countable, so W is not LM (Fubini) and lacks BP (Kuratowski–Ulam). PSP already fails at Π¹₁ ⊆ Δ¹₂. Each higher class contains Δ¹₂, so it fails there too.', '哥德尔：L 中有 ℝ 的 Δ¹₂ 良序 ≤_L，其每个真初始段都可数。W = {(x,y) : x ≤_L y} ⊆ ℝ² 是 Δ¹₂ 集；它的竖截面可数、横截面余可数，所以 W 不 LM（Fubini）且无 BP（Kuratowski–Ulam）。PSP 在 Π¹₁ ⊆ Δ¹₂ 处就已失败。更高的类都包含 Δ¹₂，所以也都失败。');
    }
    if (c === 'MC') {
      if (r === 'P12') return bi('LM and BP pass to complements, so they follow from the Σ¹₂ case. PSP for Π¹₂ is <b>not</b> provable from one measurable cardinal: in Silver\'s model L[μ] there is a Δ¹₃ well-ordering of ℝ, and the analogue of Gödel\'s construction one level up gives an uncountable Π¹₂ set without a perfect subset. Under PD it holds.', 'LM 与 BP 对补集封闭，由 Σ¹₂ 的情形即得。Π¹₂ 的 PSP 由一个可测基数<b>证不出来</b>：在 Silver 研究的 L[μ] 中有 ℝ 的 Δ¹₃ 良序，把哥德尔的构造上移一层，就得到不含完美子集的不可数 Π¹₂ 集。在 PD 下它成立。');
      if (r === 'S13') return bi('Undecided by one measurable: L[μ] (Silver) has a Δ¹₃ well-ordering of ℝ, hence a Δ¹₃ non-measurable set, while PD (consistent with a measurable, given enough Woodin cardinals) makes them all regular.', '一个可测基数定不下来：L[μ]（Silver）中有 ℝ 的 Δ¹₃ 良序，从而有 Δ¹₃ 不可测集；而 PD（在有足够多伍丁基数的前提下与可测基数相容）使它们全部正则。');
      return bi('Solovay: if a measurable cardinal exists (indeed if a<sup>#</sup> exists for every real a), every Σ¹₂ set is LM, BP and has PSP. Π¹₁ ⊆ Δ¹₂ ⊆ Σ¹₂, so those rows follow. In particular a measurable cardinal implies V ≠ L (Scott).', 'Solovay：若存在可测基数（实际上只需每个实数 a 都有 a<sup>#</sup>），则每个 Σ¹₂ 集都 LM、BP 且有 PSP。由 Π¹₁ ⊆ Δ¹₂ ⊆ Σ¹₂，这几行随之成立。特别地，可测基数蕴涵 V ≠ L（Scott）。');
    }
    // ZFC
    if (r === 'P11') return bi('LM and BP: yes, as complements of analytic sets. PSP: <b>independent</b>. It fails in L. It holds iff ω₁^{L[a]} &lt; ω₁ for every real a (Solovay), e.g. if a measurable cardinal exists. That statement implies ω₁ is inaccessible in L, so its consistency strength is exactly an inaccessible cardinal.', 'LM 与 BP：成立，因为它们是解析集的补。PSP：<b>独立</b>。它在 L 中不成立；它成立当且仅当对每个实数 a 有 ω₁^{L[a]} &lt; ω₁（Solovay），例如存在可测基数时。这个命题蕴涵 ω₁ 在 L 中不可达，所以其一致性强度恰为一个不可达基数。');
    return bi('Independent of ZFC (assuming the relevant consistency): V = L gives Δ¹₂ counterexamples to all three, while large cardinals prove them (a measurable for Σ¹₂, PD for all projective levels). Shelah: “all Σ¹₃ sets are LM” already implies ω₁ is inaccessible in L, whereas the Baire-property analogue needs no large cardinal (his model of ZF + DC + “every set has BP” is built from ZFC alone).', '独立于 ZFC（在相应一致性假设下）：V = L 给出这三条性质的 Δ¹₂ 反例，而大基数能证明它们（Σ¹₂ 用一个可测基数，所有投影层用 PD）。Shelah：“所有 Σ¹₃ 集都 LM”就已蕴涵 ω₁ 在 L 中不可达；而 Baire 性质的对应命题不需要大基数（他仅从 ZFC 出发就构造出了 ZF + DC +“所有集合都有 BP”的模型）。');
  }
  function build() {
    let h = `<tr><th></th>${COLS.map(([k, en, zh]) => `<th style="${k === col ? 'color:var(--accent)' : ''}">${bl(en, zh)}</th>`).join('')}</tr>`;
    h += `<tr class="hd"><th></th>${COLS.map(() => '<th>PSP · LM · BP</th>').join('')}</tr>`;
    REG_ROWS.forEach(r => {
      h += `<tr><th style="text-align:left">${rowLabel(r)}</th>`;
      COLS.forEach(([k]) => {
        const v = REG[k][r];
        h += `<td class="cell${k === col ? ' pick' : ''}" data-c="${k}" data-r="${r}">${[...v].map(x => `<span class="v ${x}">${x === 'Y' ? '✓' : x === 'N' ? '✗' : '?'}</span>`).join('')}</td>`;
      });
      h += '</tr>';
    });
    tbl.innerHTML = h;
    tbl.querySelectorAll('td.cell').forEach((td, i) => {
      if (td.dataset.c === col) { td.style.opacity = 0; setTimeout(() => { td.style.transition = 'opacity .35s'; td.style.opacity = 1; }, 80 + 90 * Math.floor(i / 4)); }
      td.addEventListener('click', () => {
        tbl.querySelectorAll('td.cell').forEach(x => x.classList.remove('pick'));
        td.classList.add('pick');
        const cn = COLS.find(x => x[0] === td.dataset.c);
        const rn = Array.isArray(ROWN[td.dataset.r]) ? ROWN[td.dataset.r] : [ROWN[td.dataset.r], ROWN[td.dataset.r]];
        okBox($('regMsg'), `<b>${bl(cn[1], cn[2])} · ${bl(rn[0], rn[1])}</b><br>` + why(td.dataset.c, td.dataset.r), 'info');
      });
    });
  }
  const SUMM = {
    ZFC: ['ZFC settles Σ¹₁ (all three), Π¹₁ (LM and BP), and refutes the properties for arbitrary sets. Everything in between is open-ended: “?”.', 'ZFC 搞定了 Σ¹₁（三条全有）、Π¹₁（LM 与 BP），并对任意集合否定了这些性质；中间的一切都是“?”。'],
    L: ['In L, the pathologies come as low as possible: Π¹₁ for PSP, Δ¹₂ for LM and BP. ZFC theorems still hold, so Σ¹₁ stays ✓.', '在 L 中，病态集出现得尽可能低：PSP 在 Π¹₁ 失败，LM 与 BP 在 Δ¹₂ 失败。ZFC 定理照样成立，所以 Σ¹₁ 仍是 ✓。'],
    MC: ['One measurable cardinal pushes regularity up exactly one level, to Σ¹₂.', '一个可测基数恰好把正则性向上推一层，推到 Σ¹₂。'],
    PD: ['PD (from infinitely many Woodin cardinals) makes every projective set regular. Arbitrary sets still fail, by AC.', 'PD（由无穷多个伍丁基数推出）使所有投影集都正则；但由选择公理，任意集合仍会失败。'],
  };
  const tabs = $('regTabs');
  COLS.forEach(([k, en, zh]) => {
    const b = document.createElement('button');
    b.className = 'btn small' + (k === col ? ' sel' : '');
    b.innerHTML = bl(en, zh);
    b.addEventListener('click', () => {
      col = k;
      tabs.querySelectorAll('button').forEach(x => x.classList.toggle('sel', x === b));
      build();
      okBox($('regMsg'), bi(SUMM[k][0], SUMM[k][1]) + bi('<br><span class="muted">Click any cell for the reasons.</span>', '<br><span class="muted">点任一格看理由。</span>'), 'info');
    });
    tabs.appendChild(b);
  });
  build();
  okBox($('regMsg'), bi(SUMM.ZFC[0], SUMM.ZFC[1]) + bi('<br><span class="muted">✓ = provable, ✗ = refutable, ? = independent of that theory. Click any cell for the reasons.</span>', '<br><span class="muted">✓ = 可证，✗ = 可否证，? = 独立于该理论。点任一格看理由。</span>'), 'info');
})();

/* ================= §10 Wadge ================= */
(function wadge() {
  const svg = $('wSvg');
  const N = 14, X0 = 110, CW = 44;
  let xs = [], ys = [];
  function draw() {
    svg.innerHTML = '';
    T(svg, 6, 44, 'I  (x):', { 'font-size': 14, 'font-weight': 700, fill: C.acc });
    T(svg, 6, 96, 'II (y):', { 'font-size': 14, 'font-weight': 700, fill: C.meta });
    for (let i = 0; i < N; i++) {
      el('rect', { x: X0 + i * CW + 3, y: 22, width: CW - 6, height: 32, rx: 7, fill: i < xs.length ? C.accS : '#f4f2ec', stroke: '#d8d3c4' }, svg);
      el('rect', { x: X0 + i * CW + 3, y: 74, width: CW - 6, height: 32, rx: 7, fill: i < ys.length ? C.metaS : '#f4f2ec', stroke: '#d8d3c4' }, svg);
      if (i < xs.length) { const g = el('g', { class: 'pop' }, svg); T(g, X0 + i * CW + CW / 2, 44, String(xs[i]), { 'text-anchor': 'middle', 'font-size': 17, 'font-weight': 800, fill: C.acc }); }
      if (i < ys.length) { const g = el('g', { class: 'pop' }, svg); g.style.animationDelay = '.25s'; T(g, X0 + i * CW + CW / 2, 96, String(ys[i]), { 'text-anchor': 'middle', 'font-size': 17, 'font-weight': 800, fill: C.meta }); }
      if (i === xs.length - 1) el('path', { d: `M${X0 + i * CW + CW / 2},58 l0,12`, stroke: C.muted, 'stroke-width': 2, 'marker-end': '' }, svg);
    }
    T(svg, X0 + N * CW + 4, 44, '…', { 'font-size': 16, fill: C.muted });
    T(svg, X0 + N * CW + 4, 96, '…', { 'font-size': 16, fill: C.muted });
    T(svg, 6, 130, 'A = {x : x has a 1} (open) · B = {y : infinitely many 1s} (Π⁰₂) · II wins iff (x ∈ A ⇔ y ∈ B)', { 'font-size': 11, fill: C.muted });
  }
  function msg() {
    const has = xs.includes(1);
    if (!xs.length) { okBox($('wMsg'), bi('You are player I. Play bits for x and try to beat II.', '你是玩家 I。给 x 下比特，试着打败 II。'), 'info'); return; }
    let m = bi(`II's rule: <b>play 1 iff x has already shown a 1</b> (II may use the bit you just played). So far: x ${has ? 'contains a 1, so y has turned into 1, 1, 1, …' : 'is all 0s, so y is all 0s'}.`,
      `II 的规则：<b>当且仅当 x 已出现过 1 时下 1</b>（II 可以利用你刚下的那一位）。目前：x ${has ? '含有 1，所以 y 已变成 1, 1, 1, …' : '全是 0，所以 y 也全是 0'}。`);
    if (xs.length >= N) m += bi(`<br><b>Imagine the play continuing forever.</b> If I ever plays a 1, then y ends in 1111… ∈ B. If I never does, then y = 000… ∉ B. Either way <span class="m">x ∈ A ⇔ y ∈ B</span>, so II wins every play and <span class="m">A ≤_W B</span> (even via a Lipschitz map). The reverse game is hopeless for II: <span class="m">B ≤_W A</span> would make B a continuous preimage of an open set, hence open, but B is properly Π⁰₂.`,
      `<br><b>想象对局无限进行下去。</b>如果 I 某时下了 1，y 就以 1111… 结尾，属于 B；如果 I 从不下 1，y = 000…，不属于 B。无论哪种情形都有 <span class="m">x ∈ A ⇔ y ∈ B</span>，所以 II 每局必胜，<span class="m">A ≤_W B</span>（甚至是经由 Lipschitz 映射）。反过来的博弈 II 毫无希望：若 <span class="m">B ≤_W A</span>，B 就是开集的连续原像，从而是开集；但 B 恰为 Π⁰₂。`);
    okBox($('wMsg'), m, xs.length >= N ? 'ok' : 'info');
  }
  document.querySelectorAll('[data-wplay]').forEach(b => b.addEventListener('click', () => {
    if (xs.length >= N) return;
    xs.push(+b.dataset.wplay);
    ys.push(wadgeII(xs));
    draw(); msg();
  }));
  $('wReset').addEventListener('click', () => { xs = []; ys = []; draw(); msg(); });
  draw(); msg();

  // degree tower
  const s2 = $('wdSvg');
  const rows = [
    { y: 300, pair: ['∅', 'ω^ω'] },
    { y: 262, self: 'clopen · 既开又闭' },
    { y: 224, pair: ['Σ⁰₁', 'Π⁰₁'] },
    { y: 186, self: '•' },
    { y: 148, pair: ['D₂(Σ⁰₁)', 'dual · 对偶'] },
    { y: 116, dots: '⋮  (ω₁ more rungs inside Δ⁰₂)' },
    { y: 84, pair: ['Σ⁰₂', 'Π⁰₂'] },
    { y: 54, dots: '⋮  (all Borel degrees)' },
    { y: 22, pair: ['Σ¹₁ (IF)', 'Π¹₁ (WF)'] },
  ];
  el('line', { x1: 170, x2: 170, y1: 312, y2: 10, stroke: '#e0dbcd', 'stroke-width': 3 }, s2);
  rows.forEach((r, i) => {
    const g = el('g', { class: 'pop' }, s2);
    g.style.animationDelay = (i * 0.12) + 's';
    if (r.pair) {
      r.pair.forEach((s, j) => {
        const x = j ? 245 : 95;
        el('rect', { x: x - 60, y: r.y - 13, width: 120, height: 26, rx: 13, fill: j ? '#fff0f6' : C.accS, stroke: j ? '#c2255c' : C.acc, 'stroke-width': 1.8 }, g);
        T(g, x, r.y + 5, s, { 'text-anchor': 'middle', 'font-size': 12, 'font-weight': 700 });
      });
      el('line', { x1: 155, x2: 185, y1: r.y, y2: r.y, stroke: C.muted, 'stroke-dasharray': '3 3' }, g);
    } else if (r.self) {
      el('rect', { x: 110, y: r.y - 12, width: 120, height: 24, rx: 12, fill: C.trS, stroke: C.tr, 'stroke-width': 1.8 }, g);
      T(g, 170, r.y + 5, r.self, { 'text-anchor': 'middle', 'font-size': 11.5, 'font-weight': 700 });
    } else T(g, 170, r.y + 4, r.dots, { 'text-anchor': 'middle', 'font-size': 11, fill: C.muted });
  });
  T(s2, 170, 326, 'schematic · 示意图: pair = non-self-dual, green = self-dual', { 'font-size': 9.5, fill: C.muted, 'text-anchor': 'middle' });
})();

/* ================= check yourself ================= */
checkYourself('cy1', {
  q: ['Is Baire space ω^ω compact?', '贝尔空间 ω^ω 紧致吗？'],
  opts: [['Yes, like 2^ω', '是，和 2^ω 一样'], ['No', '不是']], ans: 1,
  why: ['The cones N⟨k⟩ (k ∈ ω) form an open cover by pairwise disjoint nonempty sets, so no finite subfamily covers ω^ω. (2^ω is compact by König\'s lemma: only finitely many branchings per level.)', '锥 N⟨k⟩（k ∈ ω）构成一个由两两不交的非空开集组成的覆盖，所以没有有限子族能覆盖 ω^ω。（2^ω 紧致则由柯尼希引理保证：每层只有有限个分叉。）'],
});
checkYourself('cy2', {
  q: ['Why does the hierarchy continue past all finite levels to Σ⁰_ω, Σ⁰_{ω+1}, …?', '为什么层级在所有有限层之后还要继续，出现 Σ⁰_ω、Σ⁰_{ω+1}……？'],
  opts: [['⋃ₙ Σ⁰ₙ is not closed under countable unions', '⋃ₙ Σ⁰ₙ 对可数并不封闭'], ['The Δ⁰ₙ are not closed under complement', 'Δ⁰ₙ 对取补不封闭'], ['It doesn\'t: ⋃ₙ Σ⁰ₙ is already all Borel sets', '并不需要：⋃ₙ Σ⁰ₙ 已经是全部博雷尔集']], ans: 0,
  why: ['Put a properly Σ⁰ₙ set Aₙ (from §5) inside the n-th piece of a partition of 2^ω into disjoint clopen copies of 2^ω. The union A is Borel, but A ∩ (piece n) is properly Σ⁰ₙ, so A lies in no finite level Σ⁰ₘ. It is Σ⁰_ω.', '把 2^ω 分成可数多块两两不交、且都同胚于 2^ω 的既开又闭集，在第 n 块里放一个恰为 Σ⁰ₙ 的集合 Aₙ（由 §5）。它们的并 A 是博雷尔集，但 A 与第 n 块之交恰为 Σ⁰ₙ，所以 A 不在任何有限层 Σ⁰ₘ 中。它属于 Σ⁰_ω。'],
});
checkYourself('cy3', {
  q: ['In 2^ω, the set {0^∞} ∪ N₁ is…', '在 2^ω 中，集合 {0^∞} ∪ N₁ 是……'],
  opts: [['Δ⁰₁ (clopen)', 'Δ⁰₁（既开又闭）'], ['properly Σ⁰₁', '恰为 Σ⁰₁'], ['properly Π⁰₁', '恰为 Π⁰₁'], ['properly Δ⁰₂', '恰为 Δ⁰₂']], ans: 2,
  why: ['It is a union of two closed sets, so it is closed. It is not open: each neighbourhood N_{0^k} of 0^∞ contains 0^k1 0^∞, which starts with 0, so it is not in N₁, and it is not 0^∞.', '它是两个闭集之并，所以是闭集。它不是开集：0^∞ 的每个邻域 N_{0^k} 都含有 0^k1 0^∞，这个点以 0 开头，不在 N₁ 中，也不等于 0^∞。'],
});
checkYourself('cy4', {
  q: ['Is the set of irrationals ℝ ∖ ℚ an F_σ set?', '无理数集 ℝ ∖ ℚ 是 F_σ 集吗？'],
  opts: [['Yes', '是'], ['No', '不是']], ans: 1,
  why: ['If ℝ∖ℚ were F_σ, its complement ℚ would be G_δ, which §4 just refuted. So ℝ∖ℚ is properly Π⁰₂.', '若 ℝ∖ℚ 是 F_σ，则它的补集 ℚ 就是 G_δ，而 §4 刚刚否定了这一点。所以 ℝ∖ℚ 恰为 Π⁰₂。'],
});
checkYourself('cy5', {
  q: ['In the countable discrete space ω every subset is open, so Σ⁰₁(ω) = Π⁰₁(ω). Does this contradict the theorem?', '在可数离散空间 ω 中，每个子集都是开集，所以 Σ⁰₁(ω) = Π⁰₁(ω)。这与定理矛盾吗？'],
  opts: [['Yes', '矛盾'], ['No', '不矛盾']], ans: 1,
  why: ['The theorem is for uncountable Polish spaces. ω has no copy of 2^ω, and there is no 2^ω-indexed universal set inside ω × ω to diagonalize against.', '定理针对的是不可数波兰空间。ω 中没有 2^ω 的拷贝，ω × ω 里也没有以 2^ω 为指标的万有集可供对角线论证使用。'],
});
checkYourself('cy6', {
  q: ['For every real a ∈ 2^ω, {a} is (boldface) Π⁰₁. Is {a} also lightface Π⁰₁ for every a?', '对每个实数 a ∈ 2^ω，{a} 都是（粗体）Π⁰₁。那它是否对每个 a 都是细体 Π⁰₁？'],
  opts: [['Yes', '是'], ['No', '不是']], ans: 1,
  why: ['If {a} is a lightface Π⁰₁ subset of 2^ω, then a is computable: by compactness, the strings s of length n with N_s ∩ {a} = ∅ are eventually all enumerated, and the one left over is a↾n. So {a} is lightface Π⁰₁ only for computable a. (Also, there are only countably many lightface sets.)', '若 {a} 是 2^ω 的细体 Π⁰₁ 子集，则 a 可计算：由紧致性，长度为 n 且 N_s ∩ {a} = ∅ 的串 s 终将全部被枚举出来，剩下的那一个就是 a↾n。所以只有可计算的 a 才使 {a} 是细体 Π⁰₁。（何况细体集只有可数个。）'],
});
checkYourself('cy7', {
  q: ['A ⊆ ℝ is analytic and ℝ ∖ A is analytic. Then A is…', 'A ⊆ ℝ 是解析集，ℝ ∖ A 也是解析集。那么 A ……'],
  opts: [['Borel', '是博雷尔集'], ['possibly non-Borel', '可能不是博雷尔集'], ['necessarily closed', '一定是闭集']], ans: 0,
  why: ['Suslin\'s theorem: Δ¹₁ = Borel. Lusin separation gives a Borel C with A ⊆ C and C ∩ (ℝ∖A) = ∅, so C = A.', 'Suslin 定理：Δ¹₁ = 博雷尔。由卢津分离定理，存在博雷尔集 C 使 A ⊆ C 且 C ∩ (ℝ∖A) = ∅，于是 C = A。'],
});
checkYourself('cy8', {
  q: ['x ∈ A ⇔ ∃y₁ ∀y₂ ∀y₃ (x,y₁,y₂,y₃) ∈ B with B Borel. Then A is guaranteed to be in…', 'x ∈ A ⇔ ∃y₁ ∀y₂ ∀y₃ (x,y₁,y₂,y₃) ∈ B，B 为博雷尔集。那么 A 保证属于……'],
  opts: [['Σ¹₂', 'Σ¹₂'], ['Σ¹₃', 'Σ¹₃'], ['Π¹₃', 'Π¹₃']], ans: 0,
  why: ['∀y₂∀y₃ merges into one ∀ (pair y₂, y₃ into one real), so the prefix is ∃∀, i.e. Σ¹₂. Count alternations, not quantifiers.', '∀y₂∀y₃ 合并成一个 ∀（把 y₂、y₃ 配成一个实数），前缀是 ∃∀，即 Σ¹₂。数的是交替次数，不是量词个数。'],
});
checkYourself('cy9', {
  q: ['Assume V = L. Is there a Π¹₁ set that is not Lebesgue measurable?', '假设 V = L。存在不可测的 Π¹₁ 集吗？'],
  opts: [['Yes', '存在'], ['No', '不存在']], ans: 1,
  why: ['“Every Π¹₁ set is LM” is a ZFC theorem (complements of analytic sets), and L satisfies ZFC. In L the first non-measurable sets appear at Δ¹₂. What fails at Π¹₁ in L is the perfect set property.', '“每个 Π¹₁ 集都可测”是 ZFC 定理（解析集的补），而 L 满足 ZFC。L 中最早的不可测集出现在 Δ¹₂。在 L 中，Π¹₁ 处失败的是完美集性质。'],
});
checkYourself('cy10', {
  q: ['A ⊆ 2^ω is open but not closed, B is closed but not open. Who wins G_L(A, B)?', 'A ⊆ 2^ω 是开集但不是闭集，B 是闭集但不是开集。谁赢 G_L(A, B)？'],
  opts: [['II', 'II'], ['I', 'I'], ['Neither has a winning strategy', '双方都没有必胜策略']], ans: 1,
  why: ['The game is determined (its payoff set is Borel: Martin; here even simpler). If II won, A ≤_W B would make A closed, which is impossible. So I wins, and I\'s strategy gives B ≤_W ¬A: closed reduces to closed.', '这个博弈是决定的（支付集是博雷尔集，由 Martin 定理；此处甚至更简单）。若 II 获胜，则 A ≤_W B 使 A 成为闭集，不可能。所以 I 获胜，I 的策略给出 B ≤_W ¬A：闭集归约到闭集。'],
});

/* ================= exercises: generic multiple-choice rows ================= */
function mcq(listId, items, prog, showId, msgId, doneMsg) {
  const box = $(listId);
  const solved = items.map(() => false);
  let revealed = false; // once answers are shown, no progress this page session
  const rows = items.map((it, i) => {
    const row = document.createElement('div');
    row.className = 'mrow';
    row.innerHTML = `<div class="stmt">${it.s}</div><div class="opts"></div><div class="fb"><div class="msg"></div></div>`;
    const opts = row.querySelector('.opts'), msg = row.querySelector('.msg');
    const btns = it.o.map((o, j) => {
      const b = document.createElement('button');
      b.className = 'btn small';
      b.innerHTML = Array.isArray(o) ? bl(o[0], o[1]) : `<span class="m">${o}</span>`;
      b.addEventListener('click', () => {
        btns.forEach(x => x.classList.remove('right', 'wrongc'));
        if (j === it.a) {
          b.classList.add('right');
          okBox(msg, '✓ ' + bi(it.w[0], it.w[1]));
          solved[i] = true;
          if (solved.every(Boolean) && !revealed) { Progress.mark(prog); okBox($(msgId), bi(doneMsg[0], doneMsg[1])); }
        } else {
          b.classList.add('wrongc');
          okBox(msg, '✗ ' + bi(it.h ? it.h[0] : 'Not this one. Check the upper and lower bounds separately.', it.h ? it.h[1] : '不是这个。分别检查上界和下界。'), 'bad');
        }
      });
      opts.appendChild(b);
      return b;
    });
    box.appendChild(row);
    return { btns, msg };
  });
  $(showId).addEventListener('click', () => {
    revealed = true;
    rows.forEach((r, i) => {
      r.btns.forEach((b, j) => { b.classList.remove('right', 'wrongc'); if (j === items[i].a) b.classList.add('right'); });
      okBox(r.msg, bi(items[i].w[0], items[i].w[1]), 'info');
    });
    okBox($(msgId), bi('Answers shown. (Since the answers were revealed, this exercise will not be marked as solved during this visit.)', '已显示答案。（由于已查看答案，本次访问中这道题不会再被记为完成。）'), 'info');
  });
}

const LV = [['Δ⁰₁ (clopen)', 'Δ⁰₁（既开又闭）'], ['Σ⁰₁ ∖ Π⁰₁', 'Σ⁰₁ ∖ Π⁰₁'], ['Π⁰₁ ∖ Σ⁰₁', 'Π⁰₁ ∖ Σ⁰₁'], ['Σ⁰₂ ∖ Π⁰₂', 'Σ⁰₂ ∖ Π⁰₂'], ['Π⁰₂ ∖ Σ⁰₂', 'Π⁰₂ ∖ Σ⁰₂'], ['Π⁰₃ ∖ Σ⁰₃', 'Π⁰₃ ∖ Σ⁰₃']];
mcq('e1List', [
  { s: bl('(a) <span class="m">{x : x(3) = 1}</span>', '(a) <span class="m">{x : x(3) = 1}</span>'), o: LV, a: 0,
    w: ['A finite union of cones N_s with |s| = 4 and s(3) = 1; its complement is the analogous union with s(3) = 0.', '它是 |s| = 4、s(3) = 1 的有限个锥 N_s 之并；补集是 s(3) = 0 的同类并。'] },
  { s: bl('(b) <span class="m">{x : ∃n x(n) = x(n+1) = 1}</span>', '(b) <span class="m">{x : ∃n x(n) = x(n+1) = 1}</span>'), o: LV, a: 1,
    w: ['Open: the union of cones N_s with s ending in 11. Not closed: 0^k110^∞ → 0^∞, which is outside the set.', '开集：所有以 11 结尾的 s 的锥 N_s 之并。不是闭集：0^k110^∞ → 0^∞，而 0^∞ 在集合之外。'] },
  { s: bl('(c) <span class="m">{x : ∀n x(2n) = 0}</span>', '(c) <span class="m">{x : ∀n x(2n) = 0}</span>'), o: LV, a: 2,
    w: ['Closed: an intersection of the clopen sets {x(2n) = 0}. Not open: every cone N_s contains points with a 1 at some large even position.', '闭集：既开又闭集 {x(2n) = 0} 之交。不是开集：每个锥 N_s 都含有在某个很大的偶数位置上为 1 的点。'] },
  { s: bl('(d) <span class="m">{x : x has at most three 1s}</span>', '(d) <span class="m">{x : x 至多有三个 1}</span>'), o: LV, a: 2,
    w: ['Closed: the complement “at least four 1s” is witnessed by a finite prefix, so it is open. Not open: 0^∞ is in the set, but every N_{0^k} contains 0^k1111 0^∞.', '闭集：补集“至少四个 1”可由有限前缀见证，是开集。不是开集：0^∞ 在集合中，但每个 N_{0^k} 都含有 0^k1111 0^∞。'] },
  { s: bl('(e) <span class="m">{x : x is eventually constant}</span>', '(e) <span class="m">{x : x 最终为常值}</span>'), o: LV, a: 3,
    w: ['Σ⁰₂: ⋃ₙ ⋂_{m≥n} {x(m) = x(n)}. It is countable and dense, so it is not G_δ (the Baire argument of §4).', 'Σ⁰₂：⋃ₙ ⋂_{m≥n} {x(m) = x(n)}。它可数且稠密，所以不是 G_δ（§4 的贝尔论证）。'] },
  { s: bl('(f) <span class="m">{x : x has infinitely many 1s}</span>', '(f) <span class="m">{x : x 有无穷多个 1}</span>'), o: LV, a: 4,
    w: ['G_δ: ⋂ₙ ⋃_{m≥n} {x(m) = 1}. Not F_σ, because its complement “eventually 0” is not G_δ.', 'G_δ：⋂ₙ ⋃_{m≥n} {x(m) = 1}。不是 F_σ，因为它的补集“最终为 0”不是 G_δ。'] },
  { s: bl('(g) <span class="m">{x ∈ 2^{ω×ω} : every row of x has finitely many 1s}</span>', '(g) <span class="m">{x ∈ 2^{ω×ω} : x 的每一行只有有限个 1}</span>'), o: LV, a: 5,
    w: ['⋂ₘ (row m is eventually 0) is a countable intersection of Σ⁰₂ sets, so it is Π⁰₃. It is Π⁰₃-complete (Kechris 23.A), hence not Σ⁰₃.', '⋂ₘ（第 m 行最终为 0）是可数个 Σ⁰₂ 集之交，属于 Π⁰₃；它是 Π⁰₃-完全的（Kechris 23.A），因此不是 Σ⁰₃。'] },
], 'L19E1', 'e1Show', 'e1Msg', ['✓ All exact levels correct!', '✓ 恰好层级全部正确！']);

mcq('e2List', [
  { s: bl('(a) <span class="m">⋃ₙ Fₙ</span>, each Fₙ closed', '(a) <span class="m">⋃ₙ Fₙ</span>，每个 Fₙ 为闭集'), o: ['Π⁰₁', 'Σ⁰₂', 'Π⁰₂'], a: 1, w: ['F_σ = Σ⁰₂: the definition of Σ⁰₂.', 'F_σ = Σ⁰₂：这正是 Σ⁰₂ 的定义。'] },
  { s: bl('(b) <span class="m">⋃ₙ Aₙ</span>, each Aₙ ∈ Σ⁰₂', '(b) <span class="m">⋃ₙ Aₙ</span>，每个 Aₙ ∈ Σ⁰₂'), o: ['Σ⁰₂', 'Σ⁰₃', 'Π⁰₃'], a: 0, w: ['No climb: a countable union of countable unions of closed sets is again a countable union of closed sets.', '不上升：闭集可数并的可数并，仍是闭集的可数并。'] },
  { s: bl('(c) <span class="m">⋂ₙ Aₙ</span>, each Aₙ ∈ Σ⁰₂', '(c) <span class="m">⋂ₙ Aₙ</span>，每个 Aₙ ∈ Σ⁰₂'), o: ['Σ⁰₂', 'Π⁰₂', 'Π⁰₃'], a: 2, w: ['Climb: countable intersections of Σ⁰₂ = complements of countable unions of Π⁰₂ = Π⁰₃. Example: P₃ from §3.', '上升：Σ⁰₂ 的可数交 = Π⁰₂ 可数并的补 = Π⁰₃。例：§3 中的 P₃。'] },
  { s: bl('(d) <span class="m">f⁻¹[A]</span>, f continuous, A ∈ Π⁰₄', '(d) <span class="m">f⁻¹[A]</span>，f 连续，A ∈ Π⁰₄'), o: ['Π⁰₄', 'Σ⁰₅', 'Δ⁰₅'], a: 0, w: ['Continuous preimages preserve every level.', '连续原像保持每一层。'] },
  { s: bl('(e) projection of a closed <span class="m">C ⊆ X × ω^ω</span>', '(e) 闭集 <span class="m">C ⊆ X × ω^ω</span> 的投影'), o: ['Π⁰₁', 'Σ⁰₂', 'Σ¹₁'], a: 2, w: ['That is a definition of analytic sets. It need not be Borel (IF). The F_σ answer would be right only for a σ-compact hidden factor.', '这正是解析集的一种定义。它未必是博雷尔集（例如 IF）。只有被投影掉的因子是 σ-紧时，F_σ 这个答案才对。'] },
  { s: bl('(f) projection of a Σ¹₂ set', '(f) Σ¹₂ 集的投影'), o: ['Σ¹₂', 'Σ¹₃', 'Π¹₃'], a: 0, w: ['∃∃ = ∃: no climb.', '∃∃ = ∃：不上升。'] },
  { s: bl('(g) projection of a Π¹₂ set', '(g) Π¹₂ 集的投影'), o: ['Σ¹₂', 'Σ¹₃', 'Δ¹₃'], a: 1, w: ['∃∀∃: one more alternation, Σ¹₃ by definition.', '∃∀∃：多一次交替，按定义是 Σ¹₃。'] },
  { s: bl('(h) complement of a Σ¹₃ set', '(h) Σ¹₃ 集的补集'), o: ['Σ¹₃', 'Π¹₃', 'Δ¹₄'], a: 1, w: ['Complement swaps Σ and Π. (It is also in Δ¹₄, but Π¹₃ is smaller.)', '取补交换 Σ 与 Π。（它也在 Δ¹₄ 中，但 Π¹₃ 更小。）'] },
  { s: bl('(i) <span class="m">⋃ₙ Aₙ</span> with <span class="m">Aₙ ∈ Σ⁰ₙ</span>', '(i) <span class="m">⋃ₙ Aₙ</span>，其中 <span class="m">Aₙ ∈ Σ⁰ₙ</span>'), o: ['Σ⁰_ω', 'Σ⁰_{ω+1}', ['not necessarily Borel', '未必是博雷尔集']], a: 0, w: ['Each Aₙ ∈ Π⁰ₙ₊₁ with n+1 < ω, so the union is in Σ⁰_ω. Borel sets are closed under countable unions.', '每个 Aₙ ∈ Π⁰ₙ₊₁ 且 n+1 < ω，所以并集属于 Σ⁰_ω。博雷尔集对可数并封闭。'] },
], 'L19E2', 'e2Show', 'e2Msg', ['✓ You know which moves climb!', '✓ 你已经清楚哪些运算会上升了！']);

const TF = [['True', '对'], ['False', '错']];
mcq('e3List', [
  { s: bl('(a) ZFC proves: every analytic set is Lebesgue measurable.', '(a) ZFC 证明：每个解析集都勒贝格可测。'), o: TF, a: 0, w: ['Lusin–Sierpiński: analytic sets are even universally measurable.', '卢津–谢尔品斯基：解析集甚至是普遍可测的。'] },
  { s: bl('(b) ZFC proves: every coanalytic set has the perfect set property.', '(b) ZFC 证明：每个余解析集都有完美集性质。'), o: TF, a: 1, w: ['False if ZFC is consistent: in L there is an uncountable Π¹₁ set with no perfect subset (Gödel).', '若 ZFC 一致则错：L 中存在不含完美子集的不可数 Π¹₁ 集（哥德尔）。'] },
  { s: bl('(c) ZFC proves: every coanalytic set has the Baire property.', '(c) ZFC 证明：每个余解析集都有 Baire 性质。'), o: TF, a: 0, w: ['BP is closed under complements, and analytic sets have it.', 'Baire 性质对取补封闭，而解析集都有它。'] },
  { s: bl('(d) If V = L, some Σ¹₁ set is not Lebesgue measurable.', '(d) 若 V = L，则存在不可测的 Σ¹₁ 集。'), o: TF, a: 1, w: ['L satisfies ZFC, and ZFC proves all Σ¹₁ sets are measurable.', 'L 满足 ZFC，而 ZFC 证明了所有 Σ¹₁ 集都可测。'] },
  { s: bl('(e) If V = L, some Δ¹₂ set lacks the Baire property.', '(e) 若 V = L，则存在没有 Baire 性质的 Δ¹₂ 集。'), o: TF, a: 0, w: ['From Gödel\'s Δ¹₂ well-ordering of ℝ, via Kuratowski–Ulam.', '由哥德尔的 ℝ 的 Δ¹₂ 良序，经 Kuratowski–Ulam 定理得到。'] },
  { s: bl('(f) PD implies every projective set is Lebesgue measurable.', '(f) PD 蕴涵每个投影集都勒贝格可测。'), o: TF, a: 0, w: ['Mycielski–Świerczkowski, applied level by level.', 'Mycielski–Świerczkowski，逐层应用。'] },
  { s: bl('(g) PD implies every set of reals has the perfect set property.', '(g) PD 蕴涵每个实数集都有完美集性质。'), o: TF, a: 1, w: ['PD is added to ZFC, and AC still yields a Bernstein set. Only for projective sets does PD give PSP.', 'PD 是加在 ZFC 上的，选择公理仍能造出伯恩斯坦集。PD 只对投影集给出 PSP。'] },
  { s: bl('(h) ZFC proves: every uncountable Borel set has cardinality 2^ℵ₀, even if CH fails.', '(h) ZFC 证明：每个不可数博雷尔集的基数都是 2^ℵ₀，即使 CH 不成立。'), o: TF, a: 0, w: ['Borel ⊆ analytic, and analytic sets have PSP; a perfect set has size 2^ℵ₀. So CH holds “for Borel sets”.', '博雷尔 ⊆ 解析，解析集有 PSP，完美集的基数为 2^ℵ₀。所以 CH 对博雷尔集成立。'] },
  { s: bl('(i) If ZFC is consistent, so is ZFC + “some Δ¹₂ set is not Lebesgue measurable”.', '(i) 若 ZFC 一致，则 ZFC +“存在不可测的 Δ¹₂ 集”也一致。'), o: TF, a: 0, w: ['Gödel: Con(ZFC) ⇒ Con(ZFC + V = L), and V = L gives such a set.', '哥德尔：Con(ZFC) ⇒ Con(ZFC + V = L)，而 V = L 给出这样的集合。'] },
], 'L19E3', 'e3Show', 'e3Msg', ['✓ All correct. You can tell what ZFC proves from what needs L or large cardinals.', '✓ 全对！你已分得清哪些是 ZFC 能证的，哪些要靠 L 或大基数。']);

const CARD = ['ℵ₀', '2^ℵ₀', '2^(2^ℵ₀)'];
mcq('e5List', [
  { s: bl('(a) lightface Σ⁰₁ subsets of 2^ω', '(a) 2^ω 的细体 Σ⁰₁ 子集'), o: CARD, a: 0, w: ['Each is given by a c.e. set of strings, i.e. by a program: countably many.', '每个都由一个可计算可枚举的串集给出，即由一个程序给出：可数个。'] },
  { s: bl('(b) open subsets of 2^ω', '(b) 2^ω 的开集'), o: CARD, a: 1, w: ['At most 2^ℵ₀, since each has a code y ∈ 2^ω (§5). At least 2^ℵ₀, since the sets 2^ω∖{x} are all different.', '至多 2^ℵ₀：每个开集都有编码 y ∈ 2^ω（§5）；至少 2^ℵ₀：集合 2^ω∖{x} 两两不同。'] },
  { s: bl('(c) closed subsets of ω^ω', '(c) ω^ω 的闭集'), o: CARD, a: 1, w: ['Closed sets are [T] for trees T ⊆ ω^{<ω}, and there are 2^ℵ₀ trees.', '闭集就是树 T ⊆ ω^{<ω} 的 [T]，而树有 2^ℵ₀ 棵。'] },
  { s: bl('(d) Borel subsets of ℝ', '(d) ℝ 的博雷尔子集'), o: CARD, a: 1, w: ['Every Borel set has a real Borel code (a well-founded tree of countable unions and complements), so there are 2^ℵ₀ of them; singletons show at least that many.', '每个博雷尔集都有一个实数博雷尔编码（由可数并与取补构成的良基树），所以有 2^ℵ₀ 个；单点集说明至少这么多。'] },
  { s: bl('(e) projective subsets of ℝ', '(e) ℝ 的投影子集'), o: CARD, a: 1, w: ['Countably many levels, each with 2^ℵ₀ sets (codes are reals). ℵ₀ · 2^ℵ₀ = 2^ℵ₀.', '可数多层，每层 2^ℵ₀ 个集合（编码都是实数）。ℵ₀ · 2^ℵ₀ = 2^ℵ₀。'] },
  { s: bl('(f) all subsets of ℝ', '(f) ℝ 的全部子集'), o: CARD, a: 2, w: ['Cantor: |P(ℝ)| = 2^(2^ℵ₀) > 2^ℵ₀. So most sets of reals are not even projective.', '康托尔：|P(ℝ)| = 2^(2^ℵ₀) > 2^ℵ₀。所以绝大多数实数集甚至不是投影集。'] },
], 'L19E5', 'e5Show', 'e5Msg', ['✓ Counting by codes works! Definable sets are few; arbitrary sets are many.', '✓ 用编码数集合，奏效了！可定义的集合很少，任意集合多得多。']);

/* ================= E4 shadows ================= */
(function e4() {
  const svg = $('e4Svg');
  const NC = 16, NR = 7, X0 = 90, CW = 40, Y0 = 14, RH = 26;
  let Cg, uE, uA, revealed = false; // revealed: Show answer pressed this page session
  function gen() {
    Cg = Array.from({ length: NC }, () => {
      const r = Math.random();
      if (r < 0.22) return Array(NR).fill(0);
      if (r < 0.42) return Array(NR).fill(1);
      const col = Array.from({ length: NR }, () => (Math.random() < 0.4 ? 1 : 0));
      if (col.every(Boolean)) col[Math.floor(Math.random() * NR)] = 0;
      if (!col.some(Boolean)) col[Math.floor(Math.random() * NR)] = 1;
      return col;
    });
    uE = Array(NC).fill(0); uA = Array(NC).fill(0);
    draw();
    clearBox($('e4Msg'));
  }
  function draw(marks) {
    svg.innerHTML = '';
    for (let i = 0; i < NC; i++) for (let j = 0; j < NR; j++)
      el('rect', { x: X0 + i * CW + 2, y: Y0 + j * RH + 2, width: CW - 4, height: RH - 4, rx: 4, fill: Cg[i][j] ? C.acc : '#ece9e0' }, svg);
    T(svg, 6, Y0 + NR * RH / 2, 'C ⊆ X×Y', { 'font-size': 12, 'font-weight': 700, fill: C.acc });
    const strip = (yy, arr, label, key) => {
      T(svg, 6, yy + 18, label, { 'font-size': 12.5, 'font-weight': 700 });
      for (let i = 0; i < NC; i++) {
        const ok = marks ? (arr[i] === (key === 'E' ? existsCol(Cg)[i] : forallCol(Cg)[i]) ? 1 : 0) : null;
        const r = el('rect', { x: X0 + i * CW + 2, y: yy, width: CW - 4, height: 26, rx: 5, fill: arr[i] ? C.gold : '#fff', stroke: ok === null ? '#c9c4b5' : ok ? C.tr : C.fa, 'stroke-width': ok === null ? 1.5 : 3 }, svg);
        r.addEventListener('click', () => { arr[i] = arr[i] ? 0 : 1; draw(); clearBox($('e4Msg')); });
      }
    };
    strip(220, uE, '∃y C', 'E');
    strip(262, uA, '∀y C', 'A');
    T(svg, X0, 314, 'click the strip cells to toggle · 点击格子切换', { 'font-size': 11, fill: C.muted });
  }
  $('e4Check').addEventListener('click', () => {
    const E = existsCol(Cg), A = forallCol(Cg);
    const okE = E.every((v, i) => !!uE[i] === v), okA = A.every((v, i) => !!uA[i] === v);
    draw(true);
    if (okE && okA) {
      okBox($('e4Msg'), bi('✓ Both shadows correct. ∃y: some cell in the column is dark. ∀y: the whole column is dark. Note that ∀y C ⊆ ∃y C (Y is nonempty), and that ∀ is “∃ of the complement, complemented”: exactly how Π¹ₙ arises from Σ¹ₙ.', '✓ 两个影子都对。∃y：该列至少有一格深色；∀y：整列都是深色。注意 ∀y C ⊆ ∃y C（因为 Y 非空），而且 ∀ 就是“对补集取 ∃ 再取补”，这正是 Π¹ₙ 由 Σ¹ₙ 得到的方式。'));
      if (!revealed) Progress.mark('L19E4');
    } else okBox($('e4Msg'), bi(`Red-framed cells are wrong (∃ row: ${okE ? 'all correct' : 'errors'}; ∀ row: ${okA ? 'all correct' : 'errors'}). For each column x, ask: is there <i>some</i> dark cell? Is <i>every</i> cell dark?`, `红框格子是错的（∃ 行：${okE ? '全对' : '有错'}；∀ 行：${okA ? '全对' : '有错'}）。对每一列 x 问：<i>有没有</i>深色格？是否<i>每一格</i>都是深色？`), 'bad');
  });
  $('e4Show').addEventListener('click', () => {
    revealed = true;
    uE = existsCol(Cg).map(Number); uA = forallCol(Cg).map(Number);
    draw(true);
    okBox($('e4Msg'), bi('Answer shown: ∃y C marks the columns with at least one dark cell; ∀y C marks the fully dark columns. (Since the answer was revealed, this exercise will not be marked as solved during this visit; you can still press “New set C” to practise.)', '已显示答案：∃y C 标出至少有一格深色的列；∀y C 标出整列深色的列。（由于已查看答案，本次访问中这道题不会再被记为完成；仍可点“换一个 C”继续练习。）'), 'info');
  });
  $('e4New').addEventListener('click', gen);
  gen();
})();
}
