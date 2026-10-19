// Lesson 2: Hilbert proofs, deduction theorem, soundness, Lindenbaum, completeness, compactness.

/* =====================================================================
   Pure proof engine (no DOM). Formulas are logic.js ASTs; equality is
   equality of the official string show(·). Metavariables are atoms φ ψ χ.
   ===================================================================== */
const At = n => ({ type: 'atom', name: n });
const Ng = a => ({ type: 'not', a });
const Im = (a, b) => ({ type: 'bin', op: 'imp', a, b });
const same = (x, y) => show(x) === show(y);
const META = ['φ', 'ψ', 'χ'];
const SCHEMA = {
  A1: parse('φ → (ψ → φ)'),
  A2: parse('(φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))'),
  A3: parse('(¬ψ → ¬φ) → (φ → ψ)'),
};
const SCHEMA_VARS = { A1: ['φ', 'ψ'], A2: ['φ', 'ψ', 'χ'], A3: ['φ', 'ψ'] };

// Match a schema against a formula; returns the binding or null.
function matchP(pat, f, b) {
  if (pat.type === 'atom' && META.includes(pat.name)) {
    if (b[pat.name]) return same(b[pat.name], f) ? b : null;
    b[pat.name] = f;
    return b;
  }
  if (pat.type !== f.type) return null;
  if (pat.type === 'atom') return pat.name === f.name ? b : null;
  if (pat.type === 'not') return matchP(pat.a, f.a, b);
  if (pat.op !== f.op) return null;
  return matchP(pat.a, f.a, b) && matchP(pat.b, f.b, b);
}
// Same, but reports the first place where the stencil breaks.
function matchWhy(pat, f) {
  const b = {};
  let why = null;
  (function go(p, g) {
    if (why) return;
    if (p.type === 'atom' && META.includes(p.name)) {
      if (b[p.name] && !same(b[p.name], g)) why = { k: 'clash', v: p.name, was: b[p.name], now: g };
      else b[p.name] = g;
      return;
    }
    if (p.type !== g.type || (p.type === 'bin' && p.op !== g.op)) { why = { k: 'shape', want: p, got: g }; return; }
    if (p.type === 'not') go(p.a, g.a);
    else { go(p.a, g.a); go(p.b, g.b); }
  })(pat, f);
  return { ok: !why, b, why };
}
function inst(pat, b) {
  if (pat.type === 'atom') return META.includes(pat.name) ? b[pat.name] : pat;
  if (pat.type === 'not') return Ng(inst(pat.a, b));
  return { type: 'bin', op: pat.op, a: inst(pat.a, b), b: inst(pat.b, b) };
}
function axiomOf(f) {
  for (const k of ['A1', 'A2', 'A3']) {
    const b = matchP(SCHEMA[k], f, {});
    if (b) return { ax: k, b };
  }
  return null;
}
// Find a justification for f given earlier lines and hypotheses.
function justify(f, lines, hyps) {
  if (hyps.some(h => same(h, f))) return { t: 'hyp' };
  const ax = axiomOf(f);
  if (ax) return { t: 'ax', ax: ax.ax };
  for (let j = 0; j < lines.length; j++) {
    const g = lines[j].f;
    if (g.type === 'bin' && g.op === 'imp' && same(g.b, f)) {
      const i = lines.findIndex(l => same(l.f, g.a));
      if (i >= 0) return { t: 'mp', i, j };
    }
  }
  return null;
}
function lineOK(lines, k, hyps) {
  const { f, why } = lines[k];
  if (why.t === 'hyp') return hyps.some(h => same(h, f));
  if (why.t === 'ax') return !!matchP(SCHEMA[why.ax], f, {});
  if (why.t === 'mp') {
    const { i, j } = why;
    if (!(i >= 0 && j >= 0 && i < k && j < k)) return false;
    const g = lines[j].f;
    return g.type === 'bin' && g.op === 'imp' && same(g.a, lines[i].f) && same(g.b, f);
  }
  return false;
}
// Index of the first invalid line, or -1 if the whole sequence is a proof from hyps.
function checkProof(lines, hyps) {
  for (let k = 0; k < lines.length; k++) if (!lineOK(lines, k, hyps)) return k;
  return -1;
}
// Build lines from a compact spec: [formula, 'hyp'|'A1'|'A2'|'A3'|'mp', i, j] with 1-based i, j.
function mkLines(spec) {
  return spec.map(([s, t, i, j]) => ({
    f: parse(s),
    why: t === 'hyp' ? { t: 'hyp' } : t === 'mp' ? { t: 'mp', i: i - 1, j: j - 1 } : { t: 'ax', ax: t },
  }));
}
// The deduction theorem as an algorithm: a proof of ψ from Γ ∪ {φ} becomes a proof of φ → ψ from Γ.
// Every output line remembers the source line (src) and which case produced it (role).
function dtTransform(lines, phi) {
  const out = [], map = [];
  const push = (f, why, src, role) => { out.push({ f, why, src, role }); return out.length - 1; };
  lines.forEach((l, k) => {
    const chi = l.f;
    if (same(chi, phi)) {
      const pp = Im(phi, phi);
      const a = push(inst(SCHEMA.A2, { φ: phi, ψ: pp, χ: phi }), { t: 'ax', ax: 'A2' }, k, 'self');
      const b = push(Im(phi, Im(pp, phi)), { t: 'ax', ax: 'A1' }, k, 'self');
      const c = push(Im(Im(phi, pp), pp), { t: 'mp', i: b, j: a }, k, 'self');
      const d = push(Im(phi, pp), { t: 'ax', ax: 'A1' }, k, 'self');
      map[k] = push(pp, { t: 'mp', i: d, j: c }, k, 'self');
    } else if (l.why.t === 'mp') {
      const { i, j } = l.why;
      const mid = lines[i].f;
      const a = push(inst(SCHEMA.A2, { φ: phi, ψ: mid, χ: chi }), { t: 'ax', ax: 'A2' }, k, 'mp');
      const b = push(Im(Im(phi, mid), Im(phi, chi)), { t: 'mp', i: map[j], j: a }, k, 'mp');
      map[k] = push(Im(phi, chi), { t: 'mp', i: map[i], j: b }, k, 'mp');
    } else {
      const a = push(chi, l.why, k, 'leaf');
      const b = push(Im(chi, Im(phi, chi)), { t: 'ax', ax: 'A1' }, k, 'leaf');
      map[k] = push(Im(phi, chi), { t: 'mp', i: a, j: b }, k, 'leaf');
    }
  });
  return out;
}
function proofTree(lines, k) {
  const l = lines[k];
  return { k, f: l.f, why: l.why, kids: l.why.t === 'mp' ? [proofTree(lines, l.why.i), proofTree(lines, l.why.j)] : [] };
}
function treeSize(lines, k, memo = {}) {
  if (memo[k] !== undefined) return memo[k];
  const w = lines[k].why;
  return (memo[k] = w.t === 'mp' ? 1 + treeSize(lines, w.i, memo) + treeSize(lines, w.j, memo) : 1);
}
// Valuations helpers (any number of atoms; used for small sets only).
function satisfiable(set) {
  const s = new Set();
  set.forEach(f => atomsOf(f, s));
  return allValuations(sortAtoms(s)).some(v => set.every(f => evalF(f, v)));
}
function entailsCounter(prem, concl) {
  const s = new Set();
  prem.forEach(f => atomsOf(f, s));
  atomsOf(concl, s);
  const atoms = sortAtoms(s);
  const v = allValuations(atoms).find(v => prem.every(f => evalF(f, v)) && !evalF(concl, v));
  return { atoms, counter: v || null };
}
function renameAtoms(n, m) {
  if (n.type === 'atom') return At(m[n.name] || n.name);
  if (n.type === 'not') return Ng(renameAtoms(n.a, m));
  return { type: 'bin', op: n.op, a: renameAtoms(n.a, m), b: renameAtoms(n.b, m) };
}
// Backtracking k-colouring of a finite graph.
function colourGraph(vs, edges, k) {
  const adj = {};
  vs.forEach(v => adj[v] = []);
  edges.forEach(([a, b]) => { adj[a].push(b); adj[b].push(a); });
  const col = {};
  function go(i) {
    if (i === vs.length) return true;
    const v = vs[i];
    for (let c = 0; c < k; c++) {
      if (adj[v].some(u => col[u] === c)) continue;
      col[v] = c;
      if (go(i + 1)) return true;
      delete col[v];
    }
    return false;
  }
  return go(0) ? col : null;
}

/* ---------------- preset proofs ---------------- */
const PROOFS = {
  pp: { hyps: [], goal: 'p → p', spec: [
    ['(p → ((p → p) → p)) → ((p → (p → p)) → (p → p))', 'A2'],
    ['p → ((p → p) → p)', 'A1'],
    ['(p → (p → p)) → (p → p)', 'mp', 2, 1],
    ['p → (p → p)', 'A1'],
    ['p → p', 'mp', 4, 3]] },
  mp: { hyps: ['p', 'p → q'], goal: 'q', spec: [
    ['p', 'hyp'], ['p → q', 'hyp'], ['q', 'mp', 1, 2]] },
  hs: { hyps: ['p → q', 'q → r'], goal: 'p → r', spec: [
    ['q → r', 'hyp'],
    ['(q → r) → (p → (q → r))', 'A1'],
    ['p → (q → r)', 'mp', 1, 2],
    ['(p → (q → r)) → ((p → q) → (p → r))', 'A2'],
    ['(p → q) → (p → r)', 'mp', 3, 4],
    ['p → q', 'hyp'],
    ['p → r', 'mp', 6, 5]] },
  a1: { hyps: ['p'], goal: 'q → p', spec: [
    ['p', 'hyp'], ['p → (q → p)', 'A1'], ['q → p', 'mp', 1, 2]] },
  a3: { hyps: ['¬q → ¬p', 'p'], goal: 'q', spec: [
    ['(¬q → ¬p) → (p → q)', 'A3'], ['¬q → ¬p', 'hyp'], ['p → q', 'mp', 2, 1], ['p', 'hyp'], ['q', 'mp', 4, 3]] },
  chain: { hyps: ['p → q', 'q → r', 'p'], goal: 'r', spec: [
    ['p', 'hyp'], ['p → q', 'hyp'], ['q', 'mp', 1, 2], ['q → r', 'hyp'], ['r', 'mp', 3, 4]] },
  self: { hyps: ['p'], goal: 'p', spec: [['p', 'hyp']] },
};

if (typeof module !== 'undefined') {
  module.exports = { matchP, matchWhy, inst, axiomOf, justify, checkProof, mkLines, dtTransform, proofTree, treeSize, satisfiable, entailsCounter, colourGraph, PROOFS, SCHEMA, Im, Ng, At, same };
}

/* =====================================================================
   UI
   ===================================================================== */
if (typeof document !== 'undefined') {
Lang.init();
Progress.paint();

const $ = id => document.getElementById(id);
const errBox = (box, e) => { box.className = 'msg bad'; box.innerHTML = e instanceof ParseError ? e.html() : String(e); };
const okBox = (box, html, kind = 'ok') => { box.className = 'msg ' + kind; box.innerHTML = html; };
const clearBox = box => { box.className = 'msg'; box.innerHTML = ''; };
const SUB = '₀₁₂₃₄₅₆₇₈₉';
const sub = n => String(n).split('').map(d => SUB[d]).join('');
const P = s => parse(s);
const setStr = hs => hs.length ? '{' + hs.map(pretty).join(', ') + '}' : '∅';
const whyHTML = w => w.t === 'hyp' ? `<span class="jt hyp">${bil('Hyp', '假设')}</span>`
  : w.t === 'ax' ? `<span class="jt ax">${w.ax}</span>` : `<span class="jt mp">MP ${w.i + 1}, ${w.j + 1}</span>`;
const PALETTE = ['#fff3bf', '#d3f9d8', '#e7ecff', '#f8e7fc', '#ffe8cc', '#c5f6fa', '#ffdeeb', '#e9fac8', '#eceae3'];
const EDGE = ['#f08c00', '#2f9e44', '#3b5bdb', '#ae3ec9', '#e8590c', '#0c8599', '#d6336c', '#66a80f', '#868e96'];

/* ---------------- proof tree (Gentzen style: leaves on top) ---------------- */
const CHW = 8.15;
const tagW = s => [...s].reduce((w, c) => w + (/[\u4e00-\u9fff]/.test(c) ? 11.5 : 6.8), 0);
function ProofTreeSVG(container, lines, k, opts = {}) {
  container.innerHTML = '';
  const fmt = opts.fmt || pretty;
  const root = proofTree(lines, k);
  const LH = 56, GAP = 22, ML = 26;
  let maxD = 0;
  function measure(n, d) {
    n.d = d;
    maxD = Math.max(maxD, d);
    n.txt = fmt(n.f);
    n.w = [...n.txt].length * CHW + 16;
    if (!n.kids.length) { n.tag = (n.why.t === 'ax' ? n.why.ax : 'Hyp · 假设') + ` [${n.k + 1}]`; n.W = Math.max(n.w, tagW(n.tag) + 4); return; }
    n.kids.forEach(c => measure(c, d + 1));
    n.cw = n.kids.reduce((s, c) => s + c.W, 0) + GAP * (n.kids.length - 1);
    n.W = Math.max(n.w, n.cw) + ML;
  }
  measure(root, 0);
  function place(n, x0) {
    if (!n.kids.length) { n.x = x0 + n.W / 2; return; }
    const inner = n.W - ML;
    n.x = x0 + inner / 2;
    let x = x0 + (inner - n.cw) / 2;
    n.kids.forEach(c => { place(c, x); x += c.W + GAP; });
  }
  place(root, 10);
  const W = root.W + 20, H = (maxD + 1) * LH + 24;
  const svg = el('svg', { viewBox: `0 0 ${W} ${H}`, width: W, height: H, class: 'ptree' }, container);
  const y = n => H - 16 - n.d * LH;
  const groups = [];
  (function draw(n) {
    const g = el('g', { class: 'pn' }, svg);
    const yy = y(n);
    if (!n.kids.length) {
      const ax = n.why.t === 'ax';
      el('rect', { x: n.x - n.w / 2, y: yy - 16, width: n.w, height: 24, rx: 6, fill: ax ? '#fff3bf' : '#e7ecff', stroke: ax ? '#f08c00' : '#3b5bdb', 'stroke-width': 1.5 }, g);
      const tg = el('text', { x: n.x, y: yy - 21, 'text-anchor': 'middle', 'font-size': 11, fill: ax ? '#8a5300' : '#23336e', 'font-weight': 700 }, g);
      tg.textContent = n.tag;
    } else {
      const l = Math.min(...n.kids.map(c => c.x - c.w / 2), n.x - n.w / 2);
      const r = Math.max(...n.kids.map(c => c.x + c.w / 2), n.x + n.w / 2);
      el('line', { x1: l, x2: r, y1: yy - 21, y2: yy - 21, stroke: '#1f2430', 'stroke-width': 2, class: 'bar' }, g);
      const t = el('text', { x: r + 4, y: yy - 17, 'font-size': 11, fill: '#6b7280', 'font-weight': 700 }, g);
      t.textContent = `MP [${n.k + 1}]`;
    }
    const t = el('text', { x: n.x, y: yy + 1, 'text-anchor': 'middle', 'font-size': 13.5, 'font-weight': n.d === 0 ? 700 : 400 }, g);
    t.textContent = n.txt;
    groups.push({ g, k: n.k });
    n.kids.forEach(draw);
  })(root);
  function reveal(kMax, hl = -1) {
    groups.forEach(({ g, k }) => { g.classList.toggle('off', k > kMax); g.classList.toggle('hl', k === hl); });
  }
  return { reveal, svg };
}

/* ---------------- proof builder ---------------- */
let builderCount = 0;
function ProofBuilder(root, cfg) {
  const uid = 'pb' + (builderCount++);
  const st = { hyps: cfg.hyps.map(P), goal: P(cfg.goal), lines: [], sel: [], tainted: false, revealed: false, ax: 'A1', reached: -1, busy: false };
  root.innerHTML = `
  <div class="pb">
    <div class="pb-goal"><b>${bil('Goal', '目标')}:</b> <span class="m goalTxt" style="font-size:17px"></span> <span class="muted pbCount" style="font-size:13px;margin-left:10px"></span></div>
    <div class="pb-tools">
      <div class="pb-box"><h5>${bil('HYPOTHESES Γ: click to add', '假设 Γ：点击加入')}</h5><div class="chips hypChips"></div></div>
      <div class="pb-box"><h5>${bil('AXIOM INSTANCE', '公理实例')}</h5>
        <div class="toolbar axBtns" style="margin:4px 0"></div>
        <div class="m schemaTxt" style="font-size:13px"></div>
        <div class="mvrow">${META.map(m => `<span class="lab-${m}">${m}</span><input class="formula mvIn" data-mv="${m}" placeholder="${m} := …">`).join('')}</div>
        <div class="pb-prev"></div>
        <button class="btn small primary addAx">${bil('Add line', '加入此行')}</button>
      </div>
      <div class="pb-box"><h5>${bil('MP: CLICK TWO LINES', 'MP：点选两行')}</h5>
        <div style="font-size:14px">${bi('Click the line <span class="m">φ</span> and the line <span class="m">φ → ψ</span> in the list below (either order). The machine adds <span class="m">ψ</span>.', '在下面列表中点选 <span class="m">φ</span> 那一行和 <span class="m">φ → ψ</span> 那一行（顺序不限），机器就会加上 <span class="m">ψ</span>。')}</div>
        <div class="m mpState" style="font-size:13px;margin-top:6px;color:var(--gold)"></div></div>
      <div class="pb-box"><h5>${bil('TYPE A LINE', '直接输入一行')}</h5>
        <input class="formula typeIn" placeholder="p → (q → p)">
        <button class="btn small addTyped" style="margin-top:6px">${bil('Add (auto-justify)', '加入（自动找依据）')}</button></div>
    </div>
    <div class="pf-wrap"><table class="pf"></table></div>
    <div class="toolbar">
      <button class="btn small undo">${bil('Undo', '撤销')}</button>
      <button class="btn small ghost clear">${bil('Clear', '清空')}</button>
      <button class="btn small ghost showAns">${bil('Show answer', '显示答案')}</button>
      ${cfg.dt ? `<span style="margin-left:14px">${bil('Deduction theorem', '演绎定理')}:</span> <select class="dtSel"></select>
        <button class="btn small primary dtGo">${bil('Discharge this hypothesis', '消去这个假设')}</button>` : ''}
    </div>
    <div class="msg pbMsg"></div>
    <div class="stage treeStage" style="display:none"></div>
  </div>`;
  const q = s => root.querySelector(s);
  const msg = q('.pbMsg');
  // axiom buttons
  ['A1', 'A2', 'A3'].forEach(a => {
    const b = document.createElement('button');
    b.className = 'btn small';
    b.textContent = a;
    b.addEventListener('click', () => { st.ax = a; paintAx(); });
    b.dataset.ax = a;
    q('.axBtns').appendChild(b);
  });
  function paintAx() {
    q('.axBtns').querySelectorAll('button').forEach(b => b.classList.toggle('sel', b.dataset.ax === st.ax));
    q('.schemaTxt').innerHTML = prettyH(SCHEMA[st.ax]);
    root.querySelectorAll('.mvIn').forEach(i => {
      const on = SCHEMA_VARS[st.ax].includes(i.dataset.mv);
      i.style.display = on ? '' : 'none';
      root.querySelector('.lab-' + i.dataset.mv).style.display = on ? '' : 'none';
    });
    preview();
  }
  function readBinding() {
    const b = {};
    for (const m of SCHEMA_VARS[st.ax]) {
      const v = root.querySelector(`.mvIn[data-mv="${m}"]`).value;
      if (!v.trim()) return { missing: m };
      b[m] = P(v);
    }
    return { b };
  }
  function preview() {
    const box = q('.pb-prev');
    try {
      const r = readBinding();
      if (r.missing) { box.innerHTML = bil(`fill in ${r.missing}`, `请填写 ${r.missing}`); return null; }
      box.innerHTML = '→ ' + prettyH(SCHEMA[st.ax], r.b);
      return inst(SCHEMA[st.ax], r.b);
    } catch (e) { box.innerHTML = e instanceof ParseError ? e.html() : String(e); return null; }
  }
  root.querySelectorAll('.mvIn').forEach(i => i.addEventListener('input', preview));
  q('.addAx').addEventListener('click', () => {
    const f = preview();
    if (!f) { okBox(msg, bi('Fill in every metavariable with a formula first.', '先把每个元变元都填上公式。'), 'warn'); return; }
    add(f, { t: 'ax', ax: st.ax });
  });
  function paintHyps() {
    const box = q('.hypChips');
    box.innerHTML = st.hyps.length ? '' : `<span class="muted">${bil('none: Γ = ∅', '无：Γ = ∅')}</span>`;
    st.hyps.forEach(h => {
      const c = document.createElement('div');
      c.className = 'chip m';
      c.textContent = pretty(h);
      c.addEventListener('click', () => add(h, { t: 'hyp' }));
      box.appendChild(c);
    });
    if (cfg.dt) {
      q('.dtSel').innerHTML = st.hyps.map((h, i) => `<option value="${i}">${pretty(h)}</option>`).join('');
      q('.dtGo').disabled = !st.hyps.length;
    }
    q('.goalTxt').textContent = `${setStr(st.hyps)} ⊢ ${pretty(st.goal)}`;
  }
  function add(f, why, quiet) {
    st.lines.push({ f, why });
    st.sel = [];
    render(true);
    if (!quiet) clearBox(msg);
    check(quiet);
  }
  function render(newLast) {
    const t = q('table.pf');
    const big = st.lines.length > 120;
    t.innerHTML = st.lines.map((l, i) => `<tr data-i="${i}" class="${same(l.f, st.goal) ? 'goal' : ''}${st.sel.includes(i) ? ' sel' : ''}${newLast && i === st.lines.length - 1 && !big ? ' new' : ''}">
      <td class="n">${i + 1}</td><td class="f">${pretty(l.f)}</td><td class="j">${whyHTML(l.why)}</td></tr>`).join('')
      || `<tr><td class="muted" style="font-family:var(--sans);font-size:14px;padding:10px">${bil('No lines yet.', '还没有任何行。')}</td></tr>`;
    t.querySelectorAll('tr[data-i]').forEach(tr => tr.addEventListener('click', () => pick(+tr.dataset.i)));
    q('.pbCount').innerHTML = bil(`${st.lines.length} line${st.lines.length === 1 ? '' : 's'}`, `共 ${st.lines.length} 行`);
    q('.mpState').innerHTML = st.sel.length ? bil(`selected line ${st.sel[0] + 1}; now click the other one`, `已选第 ${st.sel[0] + 1} 行，再点另一行`) : '';
  }
  function pick(i) {
    if (st.busy) return;
    if (st.sel.includes(i)) { st.sel = []; render(); return; }
    st.sel.push(i);
    if (st.sel.length < 2) { render(); return; }
    const [a, b] = st.sel;
    const tryMP = (i, j) => {
      const g = st.lines[j].f;
      return g.type === 'bin' && g.op === 'imp' && same(g.a, st.lines[i].f) ? g.b : null;
    };
    let r;
    if ((r = tryMP(a, b))) add(r, { t: 'mp', i: a, j: b });
    else if ((r = tryMP(b, a))) add(r, { t: 'mp', i: b, j: a });
    else {
      st.sel = [];
      render();
      okBox(msg, bi(`MP does not apply to lines ${a + 1} and ${b + 1}: neither has the form “(the other) → ψ”.`, `第 ${a + 1}、${b + 1} 两行用不了 MP：哪一行都不是“（另一行）→ ψ”的形状。`), 'bad');
    }
  }
  q('.addTyped').addEventListener('click', typed);
  q('.typeIn').addEventListener('keydown', e => e.key === 'Enter' && typed());
  function typed() {
    let f;
    try { f = P(q('.typeIn').value); } catch (e) { errBox(msg, e); return; }
    const why = justify(f, st.lines, st.hyps);
    if (!why) {
      okBox(msg, bi('No justification found: it is not a hypothesis, not an instance of A1–A3, and does not follow by MP from two existing lines.', '找不到依据：它不是假设，不是 A1–A3 的实例，也不能由现有两行经 MP 得到。'), 'bad');
      return;
    }
    q('.typeIn').value = '';
    add(f, why);
  }
  q('.undo').addEventListener('click', () => { if (st.busy) return; st.lines.pop(); st.sel = []; render(); check(true); });
  q('.clear').addEventListener('click', () => {
    if (st.busy) return;
    st.lines = []; st.sel = []; st.tainted = false;
    st.hyps = cfg.hyps.map(P); st.goal = P(cfg.goal);
    paintHyps(); render(); clearBox(msg); check(true);
  });
  q('.showAns').addEventListener('click', async () => {
    if (st.busy) return;
    st.busy = true;
    st.tainted = true;
    st.revealed = true;
    st.hyps = cfg.hyps.map(P); st.goal = P(cfg.goal); st.lines = []; st.sel = [];
    paintHyps(); render();
    for (const l of mkLines(cfg.solution)) { add(l.f, l.why, true); await sleep(260); }
    for (const h of cfg.dtOrder || []) { await sleep(700); discharge(st.hyps.findIndex(x => same(x, P(h)))); }
    st.busy = false;
    if (!cfg.onChange) okBox(msg, bi('This is a model answer. Clear the board and try it yourself.', '这是参考答案。清空后自己试一遍吧。'), 'info');
    else okBox(msg, bi('This is a model answer. Clear the board and try it yourself for practice. Since the answer has been shown, this exercise will not be marked as solved during this visit (reload the page to start fresh).', '这是参考答案。可以清空后自己练一遍；不过既然已经看过答案，本次访问中这道题不会再计入进度（刷新页面可重新开始）。'), 'info');
  });
  function discharge(hi) {
    if (hi < 0 || hi >= st.hyps.length) return;
    const phi = st.hyps[hi];
    const idx = st.reached >= 0 ? st.reached : st.lines.length - 1;
    if (idx < 0) { okBox(msg, bi('There is no proof to transform yet.', '还没有可以变换的证明。'), 'warn'); return; }
    const used = st.lines.slice(0, idx + 1);
    const before = used.length;
    st.lines = dtTransform(used, phi).map(l => ({ f: l.f, why: l.why }));
    st.hyps = st.hyps.filter((h, i) => i !== hi);
    st.goal = Im(phi, used[idx].f);
    st.sel = [];
    paintHyps();
    render();
    const bad = checkProof(st.lines, st.hyps);
    okBox(msg, bi(`Discharged <span class="m">${pretty(phi)}</span>: ${before} lines became <b>${st.lines.length}</b> lines, now proving <span class="m">${setStr(st.hyps)} ⊢ ${pretty(st.goal)}</span>. ${bad < 0 ? 'Machine check: every line is justified ✓' : 'Machine check failed at line ' + (bad + 1)}`,
      `已消去 <span class="m">${pretty(phi)}</span>：${before} 行变成了 <b>${st.lines.length}</b> 行，现在证明的是 <span class="m">${setStr(st.hyps)} ⊢ ${pretty(st.goal)}</span>。${bad < 0 ? '机器复核：每一行都有依据 ✓' : '机器复核在第 ' + (bad + 1) + ' 行失败'}`), 'info');
    check(true);
  }
  if (cfg.dt) q('.dtGo').addEventListener('click', () => { if (!st.busy) discharge(+q('.dtSel').value); });
  function check(quiet) {
    const prev = st.reached;
    st.reached = st.lines.findIndex(l => same(l.f, st.goal));
    const ts = q('.treeStage');
    if (st.reached >= 0) {
      const size = treeSize(st.lines, st.reached);
      ts.style.display = '';
      if (size <= 41) ProofTreeSVG(ts, st.lines, st.reached).reveal(1e9);
      else ts.innerHTML = `<div class="muted">${bi(`The proof tree of the goal has ${size} nodes, too big to draw here. Proofs produced by the deduction theorem grow fast.`, `目标的证明树有 ${size} 个节点，太大了画不下。演绎定理生成的证明增长得很快。`)}</div>`;
      if (prev < 0 && !quiet) okBox(msg, bi(`✓ Goal reached at line ${st.reached + 1}. Its proof tree is drawn below.`, `✓ 第 ${st.reached + 1} 行达成目标，证明树见下方。`));
    } else { ts.style.display = 'none'; ts.innerHTML = ''; }
    cfg.onChange && cfg.onChange({ reached: st.reached, genuine: !st.tainted && !st.revealed, lines: st.lines, hyps: st.hyps, goal: st.goal, msg });
  }
  paintHyps(); paintAx(); render();
  return { get state() { return st; } };
}

// Schema HTML with coloured metavariables; with a binding, shows the instance with coloured slots.
function showH(n, b) {
  if (n.type === 'atom') return META.includes(n.name) ? `<span class="mv-${n.name}">${b ? show(b[n.name]) : n.name}</span>` : n.name;
  if (n.type === 'not') return '¬' + showH(n.a, b);
  return '(' + showH(n.a, b) + ' ' + SYM[n.op] + ' ' + showH(n.b, b) + ')';
}
function prettyH(n, b) { const s = showH(n, b); return n.type === 'bin' ? s.slice(1, -1) : s; }

/* ================= §1 two machines ================= */
(function twin() {
  const EX = [
    { key: 'pp', label: '⊢ p → p' },
    { key: 'mp', label: '{p, p → q} ⊢ q' },
    { key: 'hs', label: '{p → q, q → r} ⊢ p → r' },
    { key: 'bad', label: '{q, p → q} ⊢ p ?', hyps: ['q', 'p → q'], goal: 'p' },
  ];
  const SHAPES = { p: '■', q: '●', r: '▲' };
  let cur = EX[0], token = 0;
  EX.forEach(ex => {
    const b = document.createElement('button');
    b.className = 'btn small';
    b.innerHTML = `<span class="m">${ex.label}</span>`;
    b.addEventListener('click', () => { cur = ex; run(); });
    ex.btn = b;
    $('twinBtns').appendChild(b);
  });
  $('blind').addEventListener('change', run);
  function bridge(ok) {
    const svg = $('bridge');
    svg.innerHTML = '';
    const defs = el('defs', {}, svg);
    const mk = el('marker', { id: 'arr', viewBox: '0 0 10 10', refX: 9, refY: 5, markerWidth: 7, markerHeight: 7, orient: 'auto-start-reverse' }, defs);
    el('path', { d: 'M0,0 L10,5 L0,10 z', fill: '#1f2430' }, mk);
    const box = (x, col, soft, title, sub1, sub2) => {
      el('rect', { x, y: 30, width: 230, height: 90, rx: 14, fill: soft, stroke: col, 'stroke-width': 2.5 }, svg);
      const t = el('text', { x: x + 115, y: 66, 'text-anchor': 'middle', 'font-size': 22, 'font-weight': 700, fill: col }, svg);
      t.textContent = title;
      const s = el('text', { x: x + 115, y: 90, 'text-anchor': 'middle', 'font-size': 12, fill: '#555' }, svg);
      s.textContent = sub1;
      const s2 = el('text', { x: x + 115, y: 108, 'text-anchor': 'middle', 'font-size': 12, fill: '#555' }, svg);
      s2.textContent = sub2;
    };
    box(20, '#f08c00', '#fff3bf', ok ? 'Γ ⊢ φ  ✓' : 'Γ ⊬ φ', 'finite strings, rules', '有限符号串与规则');
    box(510, '#3b5bdb', '#e7ecff', ok ? 'Γ ⊨ φ  ✓' : 'Γ ⊭ φ', 'all valuations', '遍历所有赋值');
    el('path', { d: 'M255,55 C330,20 430,20 505,55', fill: 'none', stroke: '#1f2430', 'stroke-width': 2, 'marker-end': 'url(#arr)' }, svg);
    el('path', { d: 'M505,100 C430,135 330,135 255,100', fill: 'none', stroke: '#1f2430', 'stroke-width': 2, 'marker-end': 'url(#arr)' }, svg);
    const a = el('text', { x: 380, y: 22, 'text-anchor': 'middle', 'font-size': 13, 'font-weight': 700, fill: '#2f9e44' }, svg);
    a.textContent = 'Soundness · 可靠性 (§5)';
    const c = el('text', { x: 380, y: 144, 'text-anchor': 'middle', 'font-size': 13, 'font-weight': 700, fill: '#ae3ec9' }, svg);
    c.textContent = 'Completeness · 完备性 (§7)';
  }
  async function run() {
    const my = ++token;
    EX.forEach(e => e.btn.classList.toggle('sel', e === cur));
    const blind = $('blind').checked;
    const fmt = f => pretty(blind ? renameAtoms(f, SHAPES) : f);
    const pr = PROOFS[cur.key];
    const hyps = (pr ? pr.hyps : cur.hyps).map(P), goal = P(pr ? pr.goal : cur.goal);
    // semantics
    const sem = $('semOut');
    sem.innerHTML = `<div class="m" style="margin-bottom:4px">Γ = ${setStr(hyps)}, &nbsp; φ = ${pretty(goal)}</div><div class="cv"></div><div class="msg"></div>`;
    const res = ConsequenceView(sem.querySelector('.cv'), hyps, goal, { small: true });
    okBox(sem.querySelector('.msg'), res.holds ? bi(`Every blue-framed tile is green, so Γ ⊨ φ.`, `所有蓝框砖都是绿的，所以 Γ ⊨ φ。`)
      : bi(`Red tile = counterexample (p = 0, q = 1), so Γ ⊭ φ.`, `红砖就是反例（p = 0, q = 1），所以 Γ ⊭ φ。`), res.holds ? 'ok' : 'bad');
    bridge(res.holds);
    // syntax
    const syn = $('synOut');
    syn.innerHTML = `<div class="m" style="margin-bottom:6px">${blind ? bil('Γ, φ with atoms replaced by shapes', 'Γ、φ 的原子都换成了图形') : ''}</div>`;
    if (!pr) {
      const tick = document.createElement('div');
      tick.className = 'ticker';
      syn.appendChild(tick);
      for (let n = 1; n <= 40; n++) {
        if (my !== token) return;
        tick.innerHTML = bi(`Searching: candidate sequences checked: ${Math.floor(n ** 3.2).toLocaleString('en-US')} … no proof of ${fmt(goal)} yet`, `搜索中：已检查候选序列 ${Math.floor(n ** 3.2).toLocaleString('en-US')} 个……仍未找到 ${fmt(goal)} 的证明`);
        await sleep(60);
      }
      const m = document.createElement('div');
      m.className = 'msg warn fadein';
      m.innerHTML = bi('The search would run forever: <b>no proof exists</b>. We know this without searching, from the red tile on the right plus soundness (§5): provable ⇒ true in every model of Γ.',
        '这样搜下去永远停不下来：<b>证明根本不存在</b>。不用搜也知道，靠的是右边那块红砖加上可靠性定理（§5）：可证 ⇒ 在 Γ 的每个模型中都真。');
      syn.appendChild(m);
      return;
    }
    const lines = mkLines(pr.spec);
    for (let k = 0; k < lines.length; k++) {
      if (my !== token) return;
      const l = lines[k];
      const d = document.createElement('div');
      d.className = 'pline fadein';
      const pat = l.why.t === 'ax' ? bil(`matches ${l.why.ax}`, `套上 ${l.why.ax}`) : l.why.t === 'hyp' ? bil('is in Γ', '属于 Γ') : bil(`lines ${l.why.i + 1}, ${l.why.j + 1} fit “φ, φ→ψ”`, `第 ${l.why.i + 1}、${l.why.j + 1} 行形如“φ, φ→ψ”`);
      d.innerHTML = `<span class="n">${k + 1}</span><span class="f">${fmt(l.f)}</span><span class="j">${pat} <span class="stamp">✓</span></span>`;
      syn.appendChild(d);
      await sleep(380);
    }
    const m = document.createElement('div');
    m.className = 'msg ok fadein';
    m.innerHTML = bi(`A valid proof of ${fmt(goal)}: every line passed a pure shape check. ${blind ? 'Even blindfolded!' : 'Try the blindfold.'}`, `${fmt(goal)} 的合法证明：每一行都只经过“形状检查”。${blind ? '蒙着眼也照样成立！' : '试试蒙上眼。'}`);
    syn.appendChild(m);
  }
  run();
})();

/* ================= §2 schemas & instance detector ================= */
(function schemas() {
  const row = $('schemaRow');
  const cards = {};
  const names = { A1: bil('weakening', '后件弱化'), A2: bil('distribution', '分配律'), A3: bil('contraposition', '换位律') };
  ['A1', 'A2', 'A3'].forEach(k => {
    const d = document.createElement('div');
    d.className = 'schema';
    d.innerHTML = `<b>${k}</b><span style="font-family:var(--sans);font-size:12px" class="muted">${names[k]}</span><br>${prettyH(SCHEMA[k])}<div class="res" style="font-family:var(--sans);font-size:13px;margin-top:4px"></div>`;
    row.appendChild(d);
    cards[k] = d;
  });
  const inp = $('matchIn');
  attachKeys($('matchKeys'), inp);
  function run() {
    let f;
    try { f = P(inp.value); clearBox($('matchErr')); } catch (e) { errBox($('matchErr'), e); return; }
    let hit = null;
    for (const k of ['A1', 'A2', 'A3']) {
      const r = matchWhy(SCHEMA[k], f);
      const c = cards[k], res = c.querySelector('.res');
      c.classList.toggle('hit', r.ok);
      c.classList.toggle('miss', !r.ok);
      if (r.ok) {
        hit = hit || { k, b: r.b };
        res.innerHTML = '✓ ' + SCHEMA_VARS[k].map(m => `<span class="m mv-${m}">${m} := ${pretty(r.b[m])}</span>`).join(' ');
      } else if (r.why.k === 'clash') {
        res.innerHTML = '✗ ' + bil(`${r.why.v} would have to be both <span class="m">${pretty(r.why.was)}</span> and <span class="m">${pretty(r.why.now)}</span>`, `${r.why.v} 既要是 <span class="m">${pretty(r.why.was)}</span> 又要是 <span class="m">${pretty(r.why.now)}</span>`);
      } else {
        const want = r.why.want.type === 'not' ? '¬…' : '… → …';
        res.innerHTML = '✗ ' + bil(`needs shape <span class="m">${want}</span> where it finds <span class="m">${pretty(r.why.got)}</span>`, `此处需要 <span class="m">${want}</span> 的形状，实际是 <span class="m">${pretty(r.why.got)}</span>`);
      }
    }
    const show = $('matchShow');
    show.innerHTML = hit ? prettyH(SCHEMA[hit.k], hit.b) : pretty(f);
    show.classList.remove('fadein'); void show.offsetWidth; show.classList.add('fadein');
    $('matchOut').innerHTML = hit
      ? `<div class="msg ok">${bi(`An axiom: instance of <b>${hit.k}</b>. Coloured blocks show what each metavariable stands for.`, `是公理：<b>${hit.k}</b> 的实例。彩色块显示每个元变元代表的公式。`)}</div>`
      : `<div class="msg warn">${bi('Not an axiom. (It may still be a <i>theorem</i>, provable in several steps, e.g. p → (q → q).)', '不是公理。（它仍可能是<i>定理</i>，需要多步才能证出，例如 p → (q → q)。）')}</div>`;
  }
  inp.addEventListener('input', run);
  document.querySelectorAll('[data-m]').forEach(b => b.addEventListener('click', () => { inp.value = b.dataset.m; run(); }));
  $('matchRand').addEventListener('click', () => {
    const k = ['A1', 'A2', 'A3'][Math.floor(Math.random() * 3)];
    const b = {};
    META.forEach(m => b[m] = randomFormula(['p', 'q', 'r'], 1, ['not', 'imp']));
    inp.value = pretty(inst(SCHEMA[k], b));
    run();
  });
  run();
})();

/* ================= §3 ⊢ p → p and sandbox ================= */
let sandbox = null;
(function ptop() {
  const lines = mkLines(PROOFS.pp.spec);
  const notes = [
    bi('Line 1: an instance of A2 with φ := p, ψ := p → p, χ := p.', '第 1 行：A2 的实例，取 φ := p，ψ := p → p，χ := p。'),
    bi('Line 2: an instance of A1 with φ := p, ψ := p → p.', '第 2 行：A1 的实例，取 φ := p，ψ := p → p。'),
    bi('Line 3: MP on lines 2 and 1. Line 2 is exactly the antecedent of line 1.', '第 3 行：对第 2、1 行用 MP。第 2 行恰好是第 1 行的前件。'),
    bi('Line 4: an instance of A1 with φ := p, ψ := p.', '第 4 行：A1 的实例，取 φ := p，ψ := p。'),
    bi('Line 5: MP on lines 4 and 3. Done: <b>⊢ p → p</b>. The trick was choosing the instances of A2 cleverly. §4 shows where this trick comes from.', '第 5 行：对第 4、3 行用 MP。完成：<b>⊢ p → p</b>。窍门在于巧妙地选 A2 的实例。§4 会揭示这个窍门的来历。'),
  ];
  const list = $('ppList');
  list.innerHTML = lines.map((l, i) => `<div class="pline" data-i="${i}"><span class="n">${i + 1}</span><span class="f">${pretty(l.f)}</span><span class="j">${whyHTML(l.why)}</span></div>`).join('');
  const tv = ProofTreeSVG($('ppTree'), lines, 4);
  let k = 0;
  function paint() {
    tv.reveal(k, k);
    list.querySelectorAll('.pline').forEach((d, i) => {
      d.style.opacity = i <= k ? 1 : 0.25;
      d.style.outline = i === k ? '2px solid var(--accent)' : '';
    });
    $('ppMsg').innerHTML = k < 0 ? bi('Press “Next line”.', '请按“下一行”。') : k === 4 ? notes[4] : notes[k];
    $('ppNext').disabled = k >= 4;
  }
  $('ppNext').addEventListener('click', () => { k++; paint(); });
  $('ppAll').addEventListener('click', () => { k = 4; paint(); tv.reveal(4, -1); });
  $('ppReset').addEventListener('click', () => { k = 0; paint(); });
  paint();

  // sandbox
  const goals = [
    { key: 'pp', label: '⊢ p → p' },
    { key: 'a1', label: '{p} ⊢ q → p' },
    { key: 'a3', label: '{¬q → ¬p, p} ⊢ q' },
    { key: 'chain', label: '{p → q, q → r, p} ⊢ r' },
  ];
  function load(g) {
    document.querySelectorAll('#sbGoals button').forEach(b => b.classList.toggle('sel', b.dataset.k === g.key));
    const pr = PROOFS[g.key];
    sandbox = ProofBuilder($('sandbox'), { hyps: pr.hyps, goal: pr.goal, solution: pr.spec });
  }
  goals.forEach(g => {
    const b = document.createElement('button');
    b.className = 'btn small';
    b.dataset.k = g.key;
    b.innerHTML = `<span class="m">${g.label}</span>`;
    b.addEventListener('click', () => load(g));
    $('sbGoals').appendChild(b);
  });
  load(goals[1]);
})();

/* ================= §4 deduction theorem ================= */
(function deduction() {
  const presets = [
    { key: 'self', label: '<span class="m">{p} ⊢ p  ⇒  ⊢ p → p</span>', phi: 'p' },
    { key: 'chain', label: '<span class="m">{p→q, q→r, p} ⊢ r  ⇒  {p→q, q→r} ⊢ p → r</span>', phi: 'p' },
    { key: 'a3', label: '<span class="m">{¬q→¬p, p} ⊢ q  ⇒  {¬q→¬p} ⊢ p → q</span>', phi: 'p' },
    { key: 'mine', label: bil('your sandbox proof (§3)', '你在 §3 搭的证明') },
  ];
  let L = [], R = [], hyps = [], phi = null, k = -1;
  presets.forEach(p => {
    const b = document.createElement('button');
    b.className = 'btn small';
    b.innerHTML = p.label;
    b.addEventListener('click', () => load(p, b));
    $('dtBtns').appendChild(b);
  });
  function load(p, btn) {
    document.querySelectorAll('#dtBtns button').forEach(b => b.classList.toggle('sel', b === btn));
    clearBox($('dtMsg'));
    if (p.key === 'mine') {
      const s = sandbox && sandbox.state;
      if (!s || !s.lines.length || !s.hyps.length) {
        okBox($('dtMsg'), bi('Your sandbox needs at least one line and a goal with hypotheses (e.g. {p} ⊢ q → p). Build something in §3 first.', '§3 的搭建器里至少要有一行，且目标要带假设（如 {p} ⊢ q → p）。先去 §3 搭一个吧。'), 'warn');
        return;
      }
      const end = s.reached >= 0 ? s.reached : s.lines.length - 1;
      L = s.lines.slice(0, end + 1).map(l => ({ f: l.f, why: l.why }));
      hyps = s.hyps.slice();
      phi = hyps[hyps.length - 1];
    } else {
      const pr = PROOFS[p.key];
      L = mkLines(pr.spec);
      hyps = pr.hyps.map(P);
      phi = P(p.phi);
    }
    R = dtTransform(L, phi);
    k = 0;
    const rest = hyps.filter(h => !same(h, phi));
    $('dtLHead').innerHTML = bil(`Proof of ${pretty(L[L.length - 1].f)} from ${setStr(hyps)}`, `从 ${setStr(hyps)} 证 ${pretty(L[L.length - 1].f)}`);
    $('dtRHead').innerHTML = bil(`Proof of ${pretty(Im(phi, L[L.length - 1].f))} from ${setStr(rest)}`, `从 ${setStr(rest)} 证 ${pretty(Im(phi, L[L.length - 1].f))}`);
    paint();
  }
  function paint() {
    $('dtLeft').innerHTML = L.map((l, i) => `<div class="dtl${i === k ? ' cur' : ''}${i > k ? ' dim' : ''}" style="border-left-color:${EDGE[i % EDGE.length]};background:${i <= k ? PALETTE[i % PALETTE.length] : '#fff'}">
      <span class="n">${i + 1}</span><span class="f">${pretty(l.f)}</span><span class="j">${whyHTML(l.why)}</span></div>`).join('');
    $('dtRight').innerHTML = R.map((l, i) => l.src > k ? '' : `<div class="dtl${l.src === k ? ' fadein' : ''}" style="border-left-color:${EDGE[l.src % EDGE.length]};background:${PALETTE[l.src % PALETTE.length]}">
      <span class="n">${i + 1}</span><span class="f">${pretty(l.f)}</span><span class="j">${whyHTML(l.why)}</span></div>`).join('');
    if (k < 0) okBox($('dtCase'), bi(`Discharging <span class="m">φ = ${pretty(phi)}</span>. Press “Transform next line”.`, `要消去的假设是 <span class="m">φ = ${pretty(phi)}</span>。请按“变换下一行”。`), 'info');
    else {
      const l = L[k];
      const role = R.find(r => r.src === k).role;
      const t = role === 'self'
        ? bi(`Case 1: line ${k + 1} <i>is</i> φ. We need φ → φ, so paste in the 5-line proof of φ → φ from §3.`, `情形 1：第 ${k + 1} 行<i>就是</i> φ。需要 φ → φ，于是把 §3 那个 5 行证明搬过来。`)
        : role === 'leaf'
          ? bi(`Case 2: line ${k + 1} is ${l.why.t === 'ax' ? 'an axiom' : 'a hypothesis in Γ'}: χ. Write χ, then the A1 instance χ → (φ → χ), then MP gives φ → χ.`, `情形 2：第 ${k + 1} 行是${l.why.t === 'ax' ? '公理' : 'Γ 中的假设'} χ。先写 χ，再写 A1 的实例 χ → (φ → χ)，用 MP 得 φ → χ。`)
          : bi(`Case 3: line ${k + 1} came by MP from lines ${l.why.i + 1} (θ) and ${l.why.j + 1} (θ → χ). We already have φ → θ and φ → (θ → χ). A2 gives (φ → (θ → χ)) → ((φ → θ) → (φ → χ)), then two MPs.`, `情形 3：第 ${k + 1} 行由第 ${l.why.i + 1} 行（θ）和第 ${l.why.j + 1} 行（θ → χ）经 MP 得到。前面已经有 φ → θ 和 φ → (θ → χ)。A2 给出 (φ → (θ → χ)) → ((φ → θ) → (φ → χ))，再用两次 MP。`);
      okBox($('dtCase'), t, 'info');
    }
    $('dtNext').disabled = k >= L.length - 1;
    if (k >= L.length - 1) {
      const bad = checkProof(R, hyps.filter(h => !same(h, phi)));
      okBox($('dtMsg'), bi(`Done: ${L.length} line${L.length > 1 ? 's' : ''} → ${R.length} lines. The last line is <span class="m">${pretty(R[R.length - 1].f)}</span>. ${bad < 0 ? 'Machine check: every line is justified ✓' : 'check failed'}. By induction on the length of the proof, this works for <i>every</i> proof: that is the deduction theorem.`,
        `完成：${L.length} 行 → ${R.length} 行，最后一行是 <span class="m">${pretty(R[R.length - 1].f)}</span>。${bad < 0 ? '机器复核：每一行都有依据 ✓' : '复核失败'}。对证明长度归纳，可知这对<i>任何</i>证明都行得通，这就是演绎定理。`));
    } else clearBox($('dtMsg'));
  }
  $('dtNext').addEventListener('click', () => { if (k < L.length - 1) { k++; paint(); } });
  $('dtAll').addEventListener('click', () => { k = L.length - 1; paint(); });
  load(presets[0], $('dtBtns').querySelector('button'));
})();

/* ================= §5 soundness ================= */
(function soundness() {
  // ① axioms are tautologies
  function axDemo(k) {
    const b = {};
    META.forEach(m => b[m] = randomFormula(['p', 'q', 'r'], 1, ['not', 'imp']));
    const f = inst(SCHEMA[k], b);
    $('saF').innerHTML = `<b>${k}</b>: ${prettyH(SCHEMA[k], b)}`;
    const res = ConsequenceView($('saTiles'), [], f, { small: true, noLegend: true });
    okBox($('saMsg'), bi(`All ${res.total} valuations make it true: a tautology. Roll again; it is always all green. (Check A1 by hand: φ → (ψ → φ) can only fail if φ = 1 and ψ → φ = 0, which needs φ = 0.)`,
      `${res.total} 个赋值全都使它为真：重言式。再掷几次，永远全绿。（手动验证 A1：φ → (ψ → φ) 要为假，需 φ = 1 且 ψ → φ = 0，而后者要求 φ = 0，矛盾。）`));
  }
  document.querySelectorAll('[data-sa]').forEach(b => b.addEventListener('click', () => axDemo(b.dataset.sa)));
  axDemo('A2');

  // ② MP preserves truth
  async function mpDemo() {
    let a, b;
    try { a = P($('mpA').value); b = P($('mpB').value); clearBox($('mpErr')); } catch (e) { errBox($('mpErr'), e); return; }
    const s = new Set(); atomsOf(a, s); atomsOf(b, s);
    const atoms = sortAtoms(s);
    if (atoms.length > 4) { okBox($('mpErr'), bi('At most 4 atoms here.', '这里最多 4 个原子。'), 'warn'); return; }
    const vals = allValuations(atoms);
    const rows = [['', null], [pretty(a), a], [pretty(Im(a, b)), Im(a, b)], [pretty(b), b]];
    let h = '';
    rows.forEach(([lab, f], r) => {
      h += `<div class="mprow"><span class="lbl m" title="${r ? lab : ''}">${r === 0 ? lab : (r === 1 ? 'φ' : r === 2 ? 'φ → ψ' : 'ψ')}</span>`;
      vals.forEach((v, c) => {
        if (r === 0) h += `<span class="t" style="font-size:10px;font-weight:400;color:#666">${atoms.map(x => v[x]).join('')}</span>`;
        else { const x = evalF(f, v); h += `<span class="t c${x}" data-c="${c}">${x ? '✓' : '✗'}</span>`; }
      });
      h += '</div>';
    });
    h += `<div class="muted" style="font-size:12px">${bil('columns read', '列标为')} ${atoms.join('')}</div>`;
    $('mpRows').innerHTML = h;
    clearBox($('mpMsg'));
    await sleep(600);
    let fr = 0, bad = 0;
    vals.forEach((v, c) => {
      const both = evalF(a, v) && evalF(Im(a, b), v);
      $('mpRows').querySelectorAll(`.t[data-c="${c}"]`).forEach(t => { t.classList.toggle('fr', !!both); t.classList.toggle('dim', !both); });
      if (both) { fr++; if (!evalF(b, v)) bad++; }
    });
    okBox($('mpMsg'), bi(`In the ${fr} framed column${fr === 1 ? '' : 's'} (φ and φ → ψ both true), ψ is true ${bad ? '— impossible?!' : 'every time'}. Reason: if v̄(φ) = 1 and v̄(ψ) = 0 then v̄(φ → ψ) = 0.`,
      `在 ${fr} 个带框的列（φ 与 φ → ψ 都真）中，ψ ${bad ? '居然为假？！' : '每次都真'}。原因：若 v̄(φ) = 1 而 v̄(ψ) = 0，则 v̄(φ → ψ) = 0。`));
  }
  $('mpGo').addEventListener('click', mpDemo);
  mpDemo();

  // ③ induction matrix
  const presets = [
    { key: 'hs', label: '{p → q, q → r} ⊢ p → r' },
    { key: 'a3', label: '{¬q → ¬p, p} ⊢ q' },
    { key: 'pp', label: '⊢ p → p' },
    { key: 'mine', label: bil('your sandbox proof (§3)', '你在 §3 搭的证明') },
  ];
  let lines = [], hyps = [], k = -1;
  presets.forEach(p => {
    const b = document.createElement('button');
    b.className = 'btn small';
    b.innerHTML = p.key === 'mine' ? p.label : `<span class="m">${p.label}</span>`;
    b.addEventListener('click', () => load(p, b));
    $('smBtns').appendChild(b);
  });
  function load(p, btn) {
    document.querySelectorAll('#smBtns button').forEach(b => b.classList.toggle('sel', b === btn));
    if (p.key === 'mine') {
      const s = sandbox && sandbox.state;
      if (!s || !s.lines.length) { okBox($('smMsg'), bi('The §3 sandbox is empty. Build a few lines there first.', '§3 的搭建器还是空的，先去搭几行吧。'), 'warn'); return; }
      lines = s.lines.slice(); hyps = s.hyps.slice();
    } else { const pr = PROOFS[p.key]; lines = mkLines(pr.spec); hyps = pr.hyps.map(P); }
    const s = new Set(); lines.forEach(l => atomsOf(l.f, s)); hyps.forEach(h => atomsOf(h, s));
    const atoms = sortAtoms(s);
    if (atoms.length > 4) { okBox($('smMsg'), bi('Too many atoms to draw (max 4).', '原子太多画不下（最多 4 个）。'), 'warn'); return; }
    const vals = allValuations(atoms);
    const inMod = vals.map(v => hyps.every(h => evalF(h, v)));
    let h = `<table class="sm"><tr><th></th><th></th>${vals.map((v, c) => `<th class="${inMod[c] ? 'mod' : ''}" title="${atoms.map(a => a + '=' + v[a]).join(', ')}">${atoms.map(a => v[a]).join('')}${inMod[c] ? '<br>★' : ''}</th>`).join('')}<th></th></tr>`;
    lines.forEach((l, i) => {
      h += `<tr data-r="${i}"><td class="lab muted">${i + 1}</td><td class="lab">${pretty(l.f)}</td>`;
      vals.forEach((v, c) => { const x = evalF(l.f, v); h += `<td class="cell c${x}${inMod[c] ? '' : ' out'}">${x}</td>`; });
      const why = l.why.t === 'ax' ? bil(`${l.why.ax}: tautology, all green`, `${l.why.ax}：重言式，全绿`)
        : l.why.t === 'hyp' ? bil('in Γ: green on every ★ column', '属于 Γ：★ 列全绿')
          : bil(`MP from ${l.why.i + 1}, ${l.why.j + 1}: green wherever both are`, `由 ${l.why.i + 1}、${l.why.j + 1} 行 MP：两者都绿处必绿`);
      h += `<td class="why">${whyHTML(l.why)} ${why}</td></tr>`;
    });
    h += '</table>';
    h += `<div class="muted" style="font-size:12px;margin-top:6px">${bil(`columns: values of ${atoms.join('')}; ★ = in Mod(Γ)`, `列：${atoms.join('')} 的取值；★ = 属于 Mod(Γ)`)}</div>`;
    $('smStage').innerHTML = h;
    k = -1;
    paint();
  }
  function paint() {
    $('smStage').querySelectorAll('tr[data-r]').forEach(tr => {
      const r = +tr.dataset.r;
      tr.classList.toggle('hidden', r > k);
      tr.style.outline = r === k ? '2px solid var(--accent)' : '';
    });
    $('smNext').disabled = k >= lines.length - 1;
    if (k >= lines.length - 1 && lines.length) {
      const last = lines[lines.length - 1].f;
      okBox($('smMsg'), bi(`The last line <span class="m">${pretty(last)}</span> is green on every ★ column: <span class="m">${setStr(hyps)} ⊨ ${pretty(last)}</span>. No red cell ever appears in a ★ column, and the induction shows why it never can.`,
        `最后一行 <span class="m">${pretty(last)}</span> 在所有 ★ 列上都是绿的：<span class="m">${setStr(hyps)} ⊨ ${pretty(last)}</span>。★ 列里从不出现红格，而归纳法说明了它为什么永远不会出现。`));
    } else clearBox($('smMsg'));
  }
  $('smNext').addEventListener('click', () => { k++; paint(); });
  $('smAll').addEventListener('click', () => { k = lines.length - 1; paint(); });
  load(presets[0], $('smBtns').querySelector('button'));
})();

/* ================= §6 Lindenbaum ================= */
(function lindenbaum() {
  const gamma = ['p₀ → p₁', 'p₁ → ¬p₂'].map(P);
  const phis = ['p₁ → p₂', 'p₀', 'p₂', '¬p₁ → p₃', 'p₁', 'p₃', 'p₂ → p₀', '¬(p₀ → p₃)'].map(P);
  const ATOMS = ['p₀', 'p₁', 'p₂', 'p₃'];
  const svg = $('linSvg');
  let ch = [];
  const delta = () => [...gamma, ...ch.map((c, i) => c ? phis[i] : Ng(phis[i]))];
  const opts = n => { const d = delta(); return [satisfiable([...d, phis[n]]), satisfiable([...d, Ng(phis[n])])]; };
  function draw() {
    svg.innerHTML = '';
    const X = [150, 410], Y0 = 70, DY = 54, BW = 200, BH = 30;
    const Hh = Y0 + (Math.min(ch.length, phis.length - 1) + 1) * DY + (ch.length >= phis.length ? 40 : 10);
    svg.setAttribute('viewBox', `0 0 560 ${Hh}`);
    svg.setAttribute('height', Hh);
    // root
    el('rect', { x: 180, y: 8, width: 200, height: 30, rx: 10, fill: '#e7ecff', stroke: '#3b5bdb', 'stroke-width': 2 }, svg);
    const rt = el('text', { x: 280, y: 28, 'text-anchor': 'middle', 'font-size': 13, 'font-weight': 700 }, svg);
    rt.textContent = 'Δ₀ = Γ';
    let prev = { x: 280, y: 38 };
    const n = ch.length;
    for (let i = 0; i <= Math.min(n, phis.length - 1); i++) {
      const y = Y0 + i * DY;
      const lv = el('text', { x: 6, y: y + 20, 'font-size': 12, fill: '#999' }, svg);
      lv.textContent = 'φ' + sub(i);
      const ok = i < n ? null : opts(i);
      [0, 1].forEach(side => {
        const f = side === 0 ? phis[i] : Ng(phis[i]);
        const chosen = i < n && ch[i] === (side === 0);
        const blocked = ok ? !ok[side] : false;
        const cx = X[side];
        const edge = el('line', { x1: prev.x, y1: prev.y, x2: cx, y2: y, stroke: chosen ? '#ae3ec9' : '#ccc', 'stroke-width': chosen ? 4 : 1.5, 'stroke-dasharray': i === n ? '5 4' : '' }, svg);
        if (i < n && !chosen) edge.setAttribute('opacity', .4);
        const g = el('g', { class: i === n && !blocked ? 'lnode' : '' }, svg);
        const fill = chosen ? '#f8e7fc' : blocked ? '#ffe3e3' : i === n ? '#fff' : '#f4f2ec';
        const stroke = chosen ? '#ae3ec9' : blocked ? '#e03131' : i === n ? '#3b5bdb' : '#ddd';
        el('rect', { x: cx - BW / 2, y, width: BW, height: BH, rx: 9, fill, stroke, 'stroke-width': chosen || i === n ? 2 : 1 }, g);
        const t = el('text', { x: cx, y: y + 20, 'text-anchor': 'middle', 'font-size': 13.5, fill: i < n && !chosen ? '#aaa' : '#1f2430', 'font-weight': chosen ? 700 : 400 }, g);
        t.textContent = pretty(f) + (blocked ? '  ✗' : '');
        if (i === n) g.addEventListener('click', () => choose(side === 0));
        if (i === n) g.style.cursor = 'pointer';
        if (chosen) prev = { x: cx, y: y + BH };
      });
    }
    if (n >= phis.length) {
      const t = el('text', { x: prev.x, y: Y0 + n * DY + 10, 'text-anchor': 'middle', 'font-size': 18, fill: '#ae3ec9' }, svg);
      t.textContent = '⋮';
      const t2 = el('text', { x: 280, y: Y0 + n * DY + 34, 'text-anchor': 'middle', 'font-size': 12, fill: '#ae3ec9' }, svg);
      t2.textContent = 'φ₈, φ₉, … forever · 永远继续下去：Δ = ⋃ Δₙ';
    }
    // valuation
    const d = delta();
    $('linVal').innerHTML = ATOMS.map(a => {
      const pos = d.some(f => same(f, At(a))), neg = d.some(f => same(f, Ng(At(a))));
      return `<span class="vchip ${pos ? 'v1' : neg ? 'v0' : ''}">${a} = ${pos ? 1 : neg ? 0 : '?'}</span>`;
    }).join('');
    if (n >= phis.length) {
      const v = Object.fromEntries(ATOMS.map(a => [a, d.some(f => same(f, At(a))) ? 1 : 0]));
      let h = `<table class="tt"><tr><th>φₙ</th><th>${bil('in Δ?', '∈ Δ？')}</th><th>v̄(φₙ)</th></tr>`;
      phis.forEach((f, i) => {
        const inD = ch[i], val = evalF(f, v);
        h += `<tr><td>${pretty(f)}</td><td class="c${inD ? 1 : 0}">${inD ? bil('yes', '是') : bil('no', '否')}</td><td class="c${val} ${(+inD === val) ? 'right' : 'wrong'}">${val}</td></tr>`;
      });
      $('linTruth').innerHTML = h + '</table>' + `<div class="msg ok">${bi('Truth lemma in miniature: membership in Δ and truth under v agree on every row.', '真值引理的缩影：每一行上，“属于 Δ”与“在 v 下为真”都一致。')}</div>`;
    } else $('linTruth').innerHTML = '';
  }
  function choose(pos) {
    const n = ch.length;
    if (n >= phis.length) return;
    const ok = opts(n);
    const f = pos ? phis[n] : Ng(phis[n]);
    if (!ok[pos ? 0 : 1]) {
      okBox($('linMsg'), bi(`Blocked: Δ${sub(n)} ∪ {${pretty(f)}} has no model, so it is inconsistent. The other branch must be consistent (key lemma).`, `此路不通：Δ${sub(n)} ∪ {${pretty(f)}} 没有模型，所以不一致。由关键引理，另一支必然一致。`), 'bad');
      return;
    }
    ch.push(pos);
    const forced = !ok[0] || !ok[1];
    okBox($('linMsg'), forced ? bi(`Forced move: only one branch was consistent.`, `被迫的一步：只有一支是一致的。`)
      : bi(`Free choice: both branches were consistent. Different choices lead to different maximal consistent sets, i.e. different valuations.`, `自由选择：两支都一致。不同的选择会走向不同的极大一致集，也就是不同的赋值。`), forced ? 'warn' : 'info');
    if (ch.length === phis.length) okBox($('linMsg'), bi('Path complete for the first 8 formulas. Continuing forever gives a maximal consistent Δ, and it decides every atom.', '前 8 个公式都已决定。无限地走下去，就得到决定每个原子的极大一致集 Δ。'));
    draw();
  }
  $('linAuto').addEventListener('click', () => { const n = ch.length; if (n < phis.length) choose(opts(n)[0]); });
  $('linAll').addEventListener('click', () => { while (ch.length < phis.length) choose(opts(ch.length)[0]); });
  $('linReset').addEventListener('click', () => { ch = []; clearBox($('linMsg')); draw(); });
  draw();
})();

/* ================= §7 completeness flow ================= */
(function completeness() {
  const svg = $('flow');
  const B = [
    ['Γ ⊬ φ', 'assumption', '假设'],
    ['Γ ∪ {¬φ} consistent', 'Step 1 · DT + two theorems', '第 1 步 · 一致'],
    ['Δ ⊇ Γ ∪ {¬φ}', 'Step 2 · maximal consistent', '第 2 步 · 极大一致'],
    ['v(p) = 1 ⇔ p ∈ Δ', 'Step 3 · read off atoms', '第 3 步 · 读出原子'],
    ['v̄(ψ) = 1 ⇔ ψ ∈ Δ', 'Step 4 · truth lemma', '第 4 步 · 真值引理'],
    ['v ⊨ Γ, v̄(φ) = 0', 'Step 5 · so Γ ⊭ φ', '第 5 步 · 故 Γ ⊭ φ'],
  ];
  const pos = i => ({ x: 20 + (i % 3) * 300, y: i < 3 ? 6 : 120 });
  const defs = el('defs', {}, svg);
  const mk = el('marker', { id: 'arr2', viewBox: '0 0 10 10', refX: 9, refY: 5, markerWidth: 7, markerHeight: 7, orient: 'auto' }, defs);
  el('path', { d: 'M0,0 L10,5 L0,10 z', fill: '#ae3ec9' }, mk);
  const gs = B.map((b, i) => {
    const { x, y } = pos(i);
    const g = el('g', { class: 'fbox off' }, svg);
    el('rect', { x, y, width: 250, height: 80, rx: 14, fill: i === 0 ? '#ffe3e3' : i === 5 ? '#d3f9d8' : '#f8e7fc', stroke: i === 0 ? '#e03131' : i === 5 ? '#2f9e44' : '#ae3ec9', 'stroke-width': 2 }, g);
    const t = el('text', { x: x + 125, y: y + 28, 'text-anchor': 'middle', 'font-size': 16, 'font-weight': 700 }, g);
    t.textContent = b[0];
    const s1 = el('text', { x: x + 125, y: y + 50, 'text-anchor': 'middle', 'font-size': 12, fill: '#555' }, g);
    s1.textContent = b[1];
    const s2 = el('text', { x: x + 125, y: y + 68, 'text-anchor': 'middle', 'font-size': 12, fill: '#555' }, g);
    s2.textContent = b[2];
    if (i > 0) {
      const p = pos(i - 1);
      const d = i === 3 ? `M${p.x + 125},${p.y + 80} C${p.x + 125},${p.y + 105} ${x + 125},${y - 25} ${x + 125},${y}` : `M${p.x + 250},${p.y + 40} L${x},${y + 40}`;
      el('path', { d, fill: 'none', stroke: '#ae3ec9', 'stroke-width': 2.5, 'marker-end': 'url(#arr2)' }, g);
    }
    return g;
  });
  const steps = [...document.querySelectorAll('#cpSteps .step')];
  // step s (1..5) reveals boxes 0..s
  let s = 0;
  function paint() {
    gs.forEach((g, i) => g.classList.toggle('off', i > s));
    steps.forEach((st, i) => st.classList.toggle('on', i < s));
    $('cpNext').disabled = s >= 5;
  }
  $('cpNext').addEventListener('click', () => { if (s < 5) { s++; paint(); } });
  $('cpAll').addEventListener('click', () => { s = 5; paint(); });
  $('cpReset').addEventListener('click', () => { s = 0; paint(); });
  paint();
})();

/* ================= §8 compactness / König ================= */
(function konig() {
  const D = 6;
  const pp = i => 'p' + sub(i);
  const PRE = [
    { key: 'alt', label: bil('alternate', '交替'), desc: 'Γ = { pₙ → ¬pₙ₊₁,  ¬pₙ → pₙ₊₁ : n ∈ ℕ }',
      at: n => n >= 2 ? [`${pp(n - 2)} → ¬${pp(n - 1)}`, `¬${pp(n - 2)} → ${pp(n - 1)}`] : [] },
    { key: 'chain', label: bil('domino', '多米诺'), desc: 'Γ = { p₀ } ∪ { pₙ → pₙ₊₁ : n ∈ ℕ }',
      at: n => n === 1 ? ['p₀'] : n >= 2 ? [`${pp(n - 2)} → ${pp(n - 1)}`] : [] },
    { key: 'unsat', label: bil('domino + ¬p₄', '多米诺 + ¬p₄'), desc: 'Γ = { p₀, ¬p₄ } ∪ { pₙ → pₙ₊₁ : n ∈ ℕ }',
      at: n => n === 1 ? ['p₀'] : n === 5 ? ['p₃ → p₄', '¬p₄'] : n >= 2 ? [`${pp(n - 2)} → ${pp(n - 1)}`] : [] },
    { key: 'free', label: bil('pₙ → pₙ₊₂', 'pₙ → pₙ₊₂'), desc: 'Γ = { ¬p₀ ∨ ¬p₁ } ∪ { pₙ → pₙ₊₂ : n ∈ ℕ }   (∨ as abbreviation · ∨ 为缩写)',
      at: n => n === 2 ? ['¬p₀ ∨ ¬p₁'] : n >= 3 ? [`${pp(n - 3)} → ${pp(n - 1)}`] : [] },
  ];
  let pre = PRE[0], lvl = 0, nodes = [], token = 0;
  const svg = $('kgSvg');
  const W = 920, X0 = 20, Y = d => 30 + d * 68;
  const X = (d, i) => X0 + (i + 0.5) * (W - 2 * X0) / (1 << d);
  PRE.forEach(p => {
    const b = document.createElement('button');
    b.className = 'btn small';
    b.innerHTML = p.label;
    b.addEventListener('click', () => { pre = p; document.querySelectorAll('#kgBtns button').forEach(x => x.classList.toggle('sel', x === b)); reset(); });
    $('kgBtns').appendChild(b);
  });
  $('kgBtns').querySelector('button').classList.add('sel');
  const gammaUpTo = n => { const out = []; for (let m = 1; m <= n; m++) out.push(...pre.at(m).map(P)); return out; };
  function reset() {
    token++;
    svg.innerHTML = '';
    nodes = [[{ i: 0, alive: true, bits: [] }]];
    lvl = 0;
    $('kgGamma').textContent = pre.desc;
    $('kgChips').innerHTML = `<span class="muted" style="font-size:13px">${bil('formulas checked so far (Γₙ)', '已检查的公式（Γₙ）')}:</span>`;
    const c = el('circle', { cx: X(0, 0), cy: Y(0), r: 11, fill: '#fff', stroke: '#1f2430', 'stroke-width': 2 }, svg);
    nodes[0][0].c = c;
    clearBox($('kgMsg'));
    $('kgNext').disabled = false;
  }
  async function next(fast) {
    if (lvl >= D) return;
    const my = token;
    lvl++;
    const d = lvl;
    const layer = [];
    const gE = el('g', {}, svg), gN = el('g', {}, svg);
    nodes[d - 1].forEach(par => {
      if (!par.alive) return;
      [0, 1].forEach(b => {
        const i = par.i * 2 + b;
        const node = { i, bits: [...par.bits, b], alive: true, par };
        const ln = el('line', { x1: X(d - 1, par.i), y1: Y(d - 1), x2: X(d, i), y2: Y(d), stroke: '#9aa0aa', 'stroke-width': 2 }, gE);
        ln.classList.add('fadein');
        if (d <= 4) {
          const t = el('text', { x: (X(d - 1, par.i) + X(d, i)) / 2 + (b ? 6 : -12), y: (Y(d - 1) + Y(d)) / 2, 'font-size': 11, fill: '#888' }, gE);
          t.textContent = b;
        }
        node.edge = ln;
        node.c = el('circle', { cx: X(d, i), cy: Y(d), r: Math.max(4, 11 - d * 1.2), fill: '#fff', stroke: '#1f2430', 'stroke-width': 1.6, class: 'pop' }, gN);
        layer.push(node);
      });
    });
    nodes[d] = layer;
    const lab = el('text', { x: 4, y: Y(d) - 8, 'font-size': 11, fill: '#3b5bdb' }, svg);
    lab.textContent = pp(d - 1);
    // new formulas
    pre.at(d).forEach(s => { const c = document.createElement('span'); c.className = 'gchip'; c.textContent = s; $('kgChips').appendChild(c); });
    if (!fast) await sleep(550);
    if (my !== token) return;
    const G = gammaUpTo(d);
    let alive = 0;
    layer.forEach(nd => {
      const v = {};
      nd.bits.forEach((b, k) => v[pp(k)] = b);
      nd.alive = G.every(f => evalF(f, v));
      if (nd.alive) { alive++; nd.c.setAttribute('fill', '#d3f9d8'); nd.c.setAttribute('stroke', '#2f9e44'); }
      else {
        nd.c.setAttribute('fill', '#ffe3e3'); nd.c.setAttribute('stroke', '#e03131');
        nd.edge.setAttribute('stroke', '#f2b8b8'); nd.edge.setAttribute('stroke-dasharray', '3 3');
        const x = el('text', { x: X(d, nd.i), y: Y(d) + 4, 'text-anchor': 'middle', 'font-size': 10, fill: '#e03131', 'font-weight': 700 }, svg);
        x.textContent = '✗';
      }
    });
    if (!alive) {
      okBox($('kgMsg'), bi(`Every node at depth ${d} is dead: the <b>finite</b> set Γ${sub(d)} is already unsatisfiable, so Γ is unsatisfiable. (Read backwards, this is compactness: an unsatisfiable Γ always has a finite unsatisfiable subset.)`,
        `深度 ${d} 的节点全军覆没：<b>有限</b>集 Γ${sub(d)} 已经不可满足，所以 Γ 不可满足。（反过来读，这就是紧致性：不可满足的 Γ 总有一个有限的不可满足子集。）`), 'bad');
      $('kgNext').disabled = true;
      lvl = D;
      return;
    }
    if (d < D) okBox($('kgMsg'), bi(`Depth ${d}: ${alive} of ${1 << d} partial valuations survive Γ${sub(d)}.`, `深度 ${d}：${1 << d} 个部分赋值中有 ${alive} 个通过 Γ${sub(d)} 的检查。`), 'info');
    else {
      // highlight surviving branches
      layer.filter(n => n.alive).forEach(n => {
        let cur = n;
        while (cur.par) { cur.edge.setAttribute('stroke', '#ae3ec9'); cur.edge.setAttribute('stroke-width', 3.5); cur = cur.par; }
        const t = el('text', { x: X(d, n.i), y: Y(d) + 26, 'text-anchor': 'middle', 'font-size': 14, fill: '#ae3ec9', 'font-weight': 700 }, svg);
        t.textContent = '⋮';
      });
      const bitsTxt = layer.filter(n => n.alive).slice(0, 3).map(n => n.bits.join('')).join(', ');
      okBox($('kgMsg'), bi(`Depth ${D}: ${alive} survivor${alive > 1 ? 's' : ''} (${bitsTxt}${alive > 3 ? ', …' : ''}). Every level is nonempty, because every finite subset of Γ is satisfiable. König's lemma turns this into an infinite purple branch: a valuation satisfying all of Γ.`,
        `深度 ${D}：有 ${alive} 个幸存者（${bitsTxt}${alive > 3 ? '，…' : ''}）。每一层都非空，因为 Γ 的每个有限子集都可满足。柯尼希引理把这一点变成一条无穷的紫色分支，也就是满足整个 Γ 的赋值。`));
      $('kgNext').disabled = true;
    }
  }
  $('kgNext').addEventListener('click', () => next(false));
  $('kgAll').addEventListener('click', async () => { while (lvl < D) await next(true); });
  $('kgReset').addEventListener('click', reset);
  reset();
  next(true).then(() => next(true));
  // König steps
  const st = [...document.querySelectorAll('#konig .step')];
  let k = 0;
  $('konigNext').addEventListener('click', () => { if (k < st.length) st[k++].classList.add('on'); $('konigNext').disabled = k >= st.length; });
  $('konigAll').addEventListener('click', () => { st.forEach(s => s.classList.add('on')); k = st.length; $('konigNext').disabled = true; });
})();

/* ================= §9 graph colouring ================= */
(function colouring() {
  const COLS = ['#e03131', '#3b5bdb', '#2f9e44', '#f08c00'];
  const CN = ['red · 红', 'blue · 蓝', 'green · 绿', 'orange · 橙'];
  const GRAPHS = [
    { key: 'strip', label: bil('triangle strip (χ = 3)', '三角带（χ = 3）'),
      build: n => {
        const V = [], E = [];
        for (let c = 0; c <= n; c++) { V.push({ id: 't' + c, x: 60 + c * 95, y: 60 }); V.push({ id: 'b' + c, x: 107 + c * 95, y: 190 }); }
        for (let c = 0; c <= n; c++) {
          E.push(['t' + c, 'b' + c]);
          if (c < n) { E.push(['t' + c, 't' + (c + 1)]); E.push(['b' + c, 'b' + (c + 1)]); E.push(['t' + (c + 1), 'b' + c]); }
        }
        return { V, E, endX: 107 + n * 95 };
      } },
    { key: 'k4', label: bil('chain of K₄ (χ = 4)', 'K₄ 链（χ = 4）'),
      build: n => {
        const V = [], E = [];
        for (let i = 0; i <= n; i++) V.push({ id: 'x' + i, x: 50 + i * 105, y: 215 });
        for (let i = 0; i < n; i++) {
          V.push({ id: 'y' + i, x: 102 + i * 105, y: 35 }, { id: 'z' + i, x: 102 + i * 105, y: 150 });
          const q = ['x' + i, 'x' + (i + 1), 'y' + i, 'z' + i];
          for (let a = 0; a < 4; a++) for (let b = a + 1; b < 4; b++) E.push([q[a], q[b]]);
        }
        return { V, E, endX: 50 + n * 105 };
      } },
  ];
  let gdef = GRAPHS[0], k = 3, col = {}, hover = null;
  GRAPHS.forEach(g => {
    const b = document.createElement('button');
    b.className = 'btn small';
    b.innerHTML = g.label;
    b.addEventListener('click', () => { gdef = g; col = {}; document.querySelectorAll('#colBtns button').forEach(x => x.classList.toggle('sel', x === b)); draw(); });
    $('colBtns').appendChild(b);
  });
  $('colBtns').querySelector('button').classList.add('sel');
  [2, 3, 4].forEach(n => {
    const b = document.createElement('button');
    b.className = 'btn small';
    b.textContent = n;
    b.dataset.k = n;
    b.addEventListener('click', () => { k = n; Object.keys(col).forEach(v => { if (col[v] >= k) delete col[v]; }); draw(); });
    $('colK').appendChild(b);
  });
  $('colN').addEventListener('input', () => { $('colNv').textContent = $('colN').value; draw(); });
  $('colClear').addEventListener('click', () => { col = {}; draw(); clearBox($('colMsg')); });
  function graph() { return gdef.build(+$('colN').value); }
  function enc(v, G) {
    const nb = G.E.filter(e => e.includes(v)).map(e => e[0] === v ? e[1] : e[0]);
    const c = i => `c<sub>${v},${i + 1}</sub>`;
    const atLeast = Array.from({ length: k }, (_, i) => c(i)).join(' ∨ ');
    const atMost = [];
    for (let i = 0; i < k; i++) for (let j = i + 1; j < k; j++) atMost.push(`¬(${c(i)} ∧ ${c(j)})`);
    const diff = nb.slice(0, 2).map(u => `¬(${c(0)} ∧ c<sub>${u},1</sub>)`);
    return bi(`Vertex <b>${v}</b> in Γ: &nbsp; ${atLeast} &nbsp;·&nbsp; ${atMost.join(', ')} &nbsp;·&nbsp; ${diff.join(', ')}${nb.length ? ', …' : ''} (one per neighbour ${nb.join(', ')} and colour)`,
      `顶点 <b>${v}</b> 在 Γ 中的公式： &nbsp; ${atLeast} &nbsp;·&nbsp; ${atMost.join('，')} &nbsp;·&nbsp; ${diff.join('，')}${nb.length ? '，…' : ''}（对每个邻点 ${nb.join(', ')} 和每种颜色各一条）`);
  }
  function draw() {
    document.querySelectorAll('#colK button').forEach(b => b.classList.toggle('sel', +b.dataset.k === k));
    const G = graph();
    const svg = $('colSvg');
    svg.innerHTML = '';
    const pos = Object.fromEntries(G.V.map(v => [v.id, v]));
    let bad = 0;
    G.E.forEach(([a, b]) => {
      const conflict = col[a] !== undefined && col[a] === col[b];
      if (conflict) bad++;
      el('line', { x1: pos[a].x, y1: pos[a].y, x2: pos[b].x, y2: pos[b].y, class: 'ge' + (conflict ? ' bad' : '') }, svg);
    });
    [0, 1, 2].forEach(i => el('circle', { cx: G.endX + 32 + i * 12, cy: 128, r: 3.5, fill: '#888' }, svg));
    const more = el('text', { x: G.endX + 30, y: 152, 'font-size': 12, fill: '#888' }, svg);
    more.textContent = '∞ →';
    G.V.forEach(v => {
      const g = el('g', { class: 'gv' }, svg);
      el('circle', { cx: v.x, cy: v.y, r: 15, fill: col[v.id] !== undefined ? COLS[col[v.id]] : '#fff' }, g);
      const t = el('text', { x: v.x, y: v.y + 4, 'text-anchor': 'middle', 'font-size': 10, fill: col[v.id] !== undefined ? '#fff' : '#555', 'font-weight': 700 }, g);
      t.textContent = v.id;
      g.addEventListener('click', () => {
        const c = col[v.id];
        if (c === undefined) col[v.id] = 0; else if (c + 1 < k) col[v.id] = c + 1; else delete col[v.id];
        draw();
      });
      g.addEventListener('mouseenter', () => { hover = v.id; $('colEnc').innerHTML = enc(v.id, G); });
    });
    if (!hover || !pos[hover]) { hover = G.V[0].id; }
    $('colEnc').innerHTML = enc(hover, G);
    const unc = G.V.filter(v => col[v.id] === undefined).length;
    if (bad) okBox($('colMsg'), bi(`${bad} red edge${bad > 1 ? 's' : ''}: both ends have the same colour.`, `有 ${bad} 条红边：两端颜色相同。`), 'bad');
    else if (unc) okBox($('colMsg'), bi(`${unc} vertices still uncoloured. Palette: ${CN.slice(0, k).join(', ')}.`, `还有 ${unc} 个顶点没上色。可用颜色：${CN.slice(0, k).join('，')}。`), 'info');
    else okBox($('colMsg'), bi(`✓ This finite window is properly ${k}-coloured: you found a valuation satisfying the corresponding finite part of Γ.`, `✓ 这个有限窗口已经正常 ${k}-着色：你找到了满足 Γ 相应有限部分的一个赋值。`));
  }
  $('colSolve').addEventListener('click', () => {
    const G = graph();
    const r = colourGraph(G.V.map(v => v.id), G.E, k);
    if (!r) {
      col = {};
      draw();
      okBox($('colMsg'), bi(`No ${k}-colouring exists even for this finite window. So a <b>finite</b> subset of Γ is unsatisfiable, and the infinite graph is not ${k}-colourable either.`,
        `连这个有限窗口都不存在 ${k}-着色。于是 Γ 的某个<b>有限</b>子集不可满足，整个无穷图也就不能 ${k}-着色。`), 'bad');
      return;
    }
    col = r;
    draw();
    okBox($('colMsg'), bi(`Found a ${k}-colouring of this window. Slide the window wider: it works for every finite window, so by compactness the whole infinite graph is ${k}-colourable, even though no single finite search ever sees all of it.`,
      `找到了该窗口的 ${k}-着色。把窗口拉宽：对每个有限窗口都行，于是由紧致性，整个无穷图可以 ${k}-着色，尽管任何一次有限搜索都看不全整张图。`));
  });
  draw();
})();

/* ================= E1 ================= */
(function e1() {
  const pr = PROOFS.hs;
  ProofBuilder($('e1Builder'), {
    hyps: pr.hyps, goal: pr.goal, solution: pr.spec,
    onChange: s => {
      if (s.reached >= 0 && s.genuine) {
        okBox(s.msg, bi(`✓ Proved in ${s.reached + 1} lines without the deduction theorem. Compare §4: the deduction theorem produces exactly this kind of proof automatically.`, `✓ 用 ${s.reached + 1} 行证出，没用演绎定理。对照 §4：演绎定理自动生成的正是这类证明。`));
        Progress.mark('L2E1');
      }
    },
  });
})();

/* ================= E2 ================= */
(function e2() {
  const items = [
    { G: [], F: '((p → q) → p) → p', ans: true,
      en: 'Provable. Peirce\'s law is a tautology (all tiles green), so ∅ ⊨ φ, and <b>completeness</b> gives ⊢ φ. Finding the actual Hilbert proof is hard, but we know it exists.',
      zh: '证得出。皮尔士定律是重言式（全绿），故 ∅ ⊨ φ，由<b>完备性</b>得 ⊢ φ。真要写出希尔伯特证明很费劲，但我们知道它存在。' },
    { G: ['p → q'], F: 'q → p', ans: false,
      en: 'Not provable. The red tile p = 0, q = 1 satisfies p → q but not q → p, so Γ ⊭ φ, and by <b>soundness</b> Γ ⊬ φ.',
      zh: '证不出。红砖 p = 0, q = 1 满足 p → q 却弄假 q → p，故 Γ ⊭ φ，由<b>可靠性</b>得 Γ ⊬ φ。' },
    { G: ['¬¬p'], F: 'p', ans: true,
      en: 'Provable: every valuation with ¬¬p = 1 has p = 1, so completeness applies.',
      zh: '证得出：凡使 ¬¬p = 1 的赋值都有 p = 1，用完备性即可。' },
    { G: ['p → q', '¬p'], F: '¬q', ans: false,
      en: 'Not provable (“denying the antecedent”). Counterexample p = 0, q = 1, then soundness.',
      zh: '证不出（“否定前件”谬误）。反例 p = 0, q = 1，再用可靠性。' },
    { G: ['p → ¬p'], F: '¬p', ans: true,
      en: 'Provable: if p = 1 the premise is 1 → 0 = 0, so every model of Γ has p = 0.',
      zh: '证得出：若 p = 1，前提为 1 → 0 = 0；所以 Γ 的每个模型都有 p = 0。' },
  ];
  const solved = items.map(() => false);
  const revealed = items.map(() => false);
  const box = $('e2List');
  items.forEach((it, i) => {
    const row = document.createElement('div');
    row.className = 'tf';
    const G = it.G.map(P), F = P(it.F);
    row.innerHTML = `<div class="stmt">(${'abcde'[i]}) &nbsp; ${setStr(G)} ⊢ ${pretty(F)} ?</div>
      <button class="btn small" data-v="1">${bil('Provable', '可证')}</button>
      <button class="btn small" data-v="0">${bil('Not provable', '不可证')}</button>
      <button class="btn small ghost" data-v="show">${bil('Show answer', '看答案')}</button>
      <div style="flex-basis:100%"><div class="msg"></div><div class="grid"></div></div>`;
    box.appendChild(row);
    row.querySelectorAll('button').forEach(b => b.addEventListener('click', () => {
      const showA = b.dataset.v === 'show';
      if (showA) revealed[i] = true;
      const guess = showA ? it.ans : b.dataset.v === '1';
      const msg = row.querySelector('.msg');
      if (guess === it.ans) {
        okBox(msg, (showA ? '' : '✓ ') + bi(it.en, it.zh), showA ? 'info' : 'ok');
        ConsequenceView(row.querySelector('.grid'), G, F, { small: true, noLegend: true });
        if (showA || revealed[i]) return;
        solved[i] = true;
        if (solved.every(Boolean)) Progress.mark('L2E2');
      } else {
        okBox(msg, bi('✗ Not quite. Draw the valuation grid in your head: is there a tile with all premises true and the conclusion false?', '✗ 不对。在脑中画出赋值格子：有没有一块砖前提全真、结论为假？'), 'bad');
        row.querySelector('.grid').innerHTML = '';
      }
    }));
  });
})();

/* ================= E3 ================= */
(function e3() {
  const pp = i => 'p' + sub(i);
  const members = ['p₁', '¬p₀', ...Array.from({ length: 8 }, (_, n) => `${pp(n)} → ${pp(n + 2)}`)];
  const on = members.map(() => false);
  const box = $('e3Pick');
  members.forEach((m, i) => {
    const c = document.createElement('div');
    c.className = 'chip';
    c.textContent = m;
    c.addEventListener('click', () => { on[i] = !on[i]; c.classList.toggle('on', on[i]); clearBox($('e3Msg')); $('e3Bits').innerHTML = ''; });
    box.appendChild(c);
  });
  const dots = document.createElement('span');
  dots.className = 'muted m';
  dots.textContent = '…';
  box.appendChild(dots);
  const goal = P('p₇');
  let revealed = false;
  function check(reveal) {
    if (reveal) revealed = true;
    const sel = members.filter((m, i) => on[i]).map(P);
    const { atoms, counter } = entailsCounter(sel, goal);
    if (counter) {
      okBox($('e3Msg'), bi('✗ Not yet: here is a valuation satisfying your Γ₀ with p₇ = 0.', '✗ 还不行：下面这个赋值满足你的 Γ₀，却有 p₇ = 0。'), 'bad');
      $('e3Bits').innerHTML = `<div class="bitrow">${atoms.map(a => `<span class="b${counter[a]}">${a}=${counter[a]}</span>`).join('')}</div>`;
      return;
    }
    $('e3Bits').innerHTML = '';
    const n = sel.length;
    okBox($('e3Msg'), (reveal ? '' : '✓ ') + bi(`Γ₀ ⊨ p₇ with ${n} formula${n === 1 ? '' : 's'}${n === 4 ? ', which is minimal: the chain p₁ → p₃ → p₅ → p₇ needs every link.' : '. Can you drop some? The minimum is 4.'} The even-indexed and ¬p₀ formulas are irrelevant. Γ is infinite, but the reason for p₇ is finite: exactly what compactness promises.`,
      `Γ₀ ⊨ p₇，用了 ${n} 个公式${n === 4 ? '，已是最少：链条 p₁ → p₃ → p₅ → p₇ 缺一环都不行。' : '。还能删掉几个吗？最少需要 4 个。'}偶数下标的公式和 ¬p₀ 都无关紧要。Γ 是无穷的，而 p₇ 成立的理由却是有限的，这正是紧致性所保证的。`), reveal ? 'info' : 'ok');
    if (!revealed) Progress.mark('L2E3');
  }
  $('e3Check').addEventListener('click', () => check(false));
  $('e3Show').addEventListener('click', () => {
    const want = ['p₁', 'p₁ → p₃', 'p₃ → p₅', 'p₅ → p₇'];
    box.querySelectorAll('.chip').forEach((c, i) => { on[i] = want.includes(members[i]); c.classList.toggle('on', on[i]); });
    check(true);
  });
})();

/* ================= E4 ================= */
(function e4() {
  const cards = [
    bi('Suppose every finite subset of Γ is satisfiable, but Γ itself is not.', '设 Γ 的每个有限子集都可满足，但 Γ 本身不可满足。'),
    bi('No valuation satisfies Γ, so vacuously <span class="m">Γ ⊨ ¬(p → p)</span>.', '没有赋值满足 Γ，所以空真地有 <span class="m">Γ ⊨ ¬(p → p)</span>。'),
    bi('By completeness, <span class="m">Γ ⊢ ¬(p → p)</span>.', '由完备性，<span class="m">Γ ⊢ ¬(p → p)</span>。'),
    bi('That proof is a finite sequence, so it cites only finitely many hypotheses: <span class="m">Γ₀ ⊢ ¬(p → p)</span> for some finite <span class="m">Γ₀ ⊆ Γ</span>.', '这个证明是有限序列，只引用了有限个假设：存在有限的 <span class="m">Γ₀ ⊆ Γ</span> 使 <span class="m">Γ₀ ⊢ ¬(p → p)</span>。'),
    bi('By soundness, <span class="m">Γ₀ ⊨ ¬(p → p)</span>. But <span class="m">¬(p → p)</span> is false under every valuation, so Γ₀ has no model.', '由可靠性，<span class="m">Γ₀ ⊨ ¬(p → p)</span>。而 <span class="m">¬(p → p)</span> 在任何赋值下都假，所以 Γ₀ 没有模型。'),
    bi('This contradicts the assumption that the finite set Γ₀ is satisfiable. ∎', '这与“有限集 Γ₀ 可满足”的假设矛盾。∎'),
  ];
  const shuffled = [3, 5, 1, 4, 0, 2];
  let placed = [], revealed = false;
  function render(marks) {
    $('e4Tray').innerHTML = '';
    $('e4Slot').innerHTML = placed.length ? '' : `<span class="muted">${bil('click cards on the left', '点击左边的卡片')}</span>`;
    shuffled.filter(i => !placed.includes(i)).forEach(i => {
      const b = document.createElement('button');
      b.className = 'btn ocard';
      b.innerHTML = cards[i];
      b.addEventListener('click', () => { placed.push(i); clearBox($('e4Msg')); render(); });
      $('e4Tray').appendChild(b);
    });
    placed.forEach((i, pos) => {
      const b = document.createElement('button');
      b.className = 'btn ocard' + (marks ? (i === pos ? ' right' : ' wrong') : '');
      b.innerHTML = `<b>${pos + 1}.</b> ${cards[i]}`;
      b.addEventListener('click', () => { placed = placed.filter(x => x !== i); clearBox($('e4Msg')); render(); });
      $('e4Slot').appendChild(b);
    });
  }
  render();
  $('e4Check').addEventListener('click', () => {
    if (placed.length < cards.length) { okBox($('e4Msg'), bi('Place all six cards first.', '请先把六张卡片都放好。'), 'warn'); return; }
    const right = placed.filter((i, pos) => i === pos).length;
    render(true);
    if (right === cards.length) {
      okBox($('e4Msg'), bi('✓ Exactly. The whole argument rests on one syntactic fact: <b>a proof is finite</b>. Completeness turns “semantic” into “syntactic”, finiteness shrinks Γ to Γ₀, and soundness turns it back.', '✓ 完全正确。整个论证只依赖一个语法事实：<b>证明是有限的</b>。完备性把“语义”转成“语法”，有限性把 Γ 缩成 Γ₀，可靠性再把它转回来。'));
      if (!revealed) Progress.mark('L2E4');
    } else okBox($('e4Msg'), bi(`${right} / 6 in the right place (green). Hint: semantic → syntactic → finite → semantic.`, `${right} / 6 张放对了（绿色）。提示：语义 → 语法 → 有限 → 语义。`), 'warn');
  });
  $('e4Show').addEventListener('click', () => {
    revealed = true;
    placed = [0, 1, 2, 3, 4, 5];
    render(true);
    okBox($('e4Msg'), bi('Model answer: semantic → (completeness) → syntactic → (finiteness of proofs) → finite Γ₀ → (soundness) → semantic.', '参考答案：语义 →（完备性）→ 语法 →（证明有限）→ 有限 Γ₀ →（可靠性）→ 语义。'), 'info');
  });
})();

/* ================= E5 ================= */
(function e5() {
  const items = [
    { s: bi('If φ ∈ Δ and φ → ψ ∈ Δ, then ψ ∈ Δ.', '若 φ ∈ Δ 且 φ → ψ ∈ Δ，则 ψ ∈ Δ。'), ans: true,
      en: 'True. Δ ⊢ ψ by MP; if ψ ∉ Δ then ¬ψ ∈ Δ by maximality and Δ would be inconsistent. Δ is deductively closed.',
      zh: '对。由 MP 得 Δ ⊢ ψ；若 ψ ∉ Δ，由极大性 ¬ψ ∈ Δ，Δ 就不一致了。Δ 对推演封闭。' },
    { s: bi('For every φ, exactly one of φ and ¬φ is in Δ.', '对每个 φ，φ 与 ¬φ 恰有一个属于 Δ。'), ans: true,
      en: 'True. At least one, by maximality; at most one, by consistency.',
      zh: '对。至少一个，由极大性；至多一个，由一致性。' },
    { s: bi('Every consistent Γ has exactly one maximal consistent extension.', '每个一致集 Γ 恰有一个极大一致扩张。'), ans: false,
      en: 'False. Whenever both branches in the Lindenbaum tree are consistent, the two choices lead to different extensions. Γ = ∅ has one extension per valuation.',
      zh: '错。只要林登鲍姆树中两支都一致，两种选择就通向不同的扩张。Γ = ∅ 的扩张与赋值一一对应。' },
    { s: bi('There are only countably many maximal consistent sets.', '极大一致集只有可数多个。'), ans: false,
      en: 'False. Δ ↦ v_Δ is a bijection onto all valuations, i.e. onto {0,1}^ℕ, which is uncountable by Cantor\'s diagonal argument (Lesson 1, §8).',
      zh: '错。Δ ↦ v_Δ 是到全体赋值，即到 {0,1}^ℕ 的双射，而由康托尔对角线论证（第 1 课 §8），后者不可数。' },
    { s: bi('The union of an increasing chain Δ₀ ⊆ Δ₁ ⊆ … of consistent sets is consistent.', '一致集的递增链 Δ₀ ⊆ Δ₁ ⊆ … 之并仍一致。'), ans: true,
      en: 'True. A proof of ψ and of ¬ψ uses finitely many hypotheses, all inside a single Δₙ, which would then be inconsistent. This is Step 2 of §7.',
      zh: '对。推出 ψ 与 ¬ψ 的证明只用到有限个假设，它们全在某一个 Δₙ 里，那个 Δₙ 就不一致了。这正是 §7 的第 2 步。' },
  ];
  const solved = items.map(() => false);
  const revealed = items.map(() => false);
  items.forEach((it, i) => {
    const row = document.createElement('div');
    row.className = 'tf';
    row.innerHTML = `<div class="stmt" style="font-family:var(--sans)">(${'abcde'[i]}) ${it.s}</div>
      <button class="btn small" data-v="1">${bil('True', '对')}</button>
      <button class="btn small" data-v="0">${bil('False', '错')}</button>
      <button class="btn small ghost" data-v="show">${bil('Show answer', '看答案')}</button>
      <div style="flex-basis:100%"><div class="msg"></div></div>`;
    $('e5List').appendChild(row);
    row.querySelectorAll('button').forEach(b => b.addEventListener('click', () => {
      const showA = b.dataset.v === 'show';
      if (showA) revealed[i] = true;
      const msg = row.querySelector('.msg');
      if (showA || (b.dataset.v === '1') === it.ans) {
        okBox(msg, (showA ? (it.ans ? bi('<b>True.</b> ', '<b>对。</b>') : bi('<b>False.</b> ', '<b>错。</b>')) : '✓ ') + bi(it.en, it.zh), showA ? 'info' : 'ok');
        if (showA || revealed[i]) return;
        solved[i] = true;
        if (solved.every(Boolean)) Progress.mark('L2E5');
      } else okBox(msg, bi('✗ Think again: maximality, consistency, or finiteness of proofs?', '✗ 再想想：用极大性、一致性，还是证明的有限性？'), 'bad');
    }));
  });
})();

/* ================= E6 ================= */
(function e6() {
  const target = P('(p → q) → ((q → r) → (p → r))');
  ProofBuilder($('e6Builder'), {
    hyps: ['p → q', 'q → r', 'p'], goal: 'r', solution: PROOFS.chain.spec, dt: true, dtOrder: ['p', 'q → r', 'p → q'],
    onChange: s => {
      if (s.reached < 0 || s.hyps.length) return;
      if (!same(s.goal, target)) {
        okBox(s.msg, bi(`You proved <span class="m">⊢ ${pretty(s.goal)}</span>, a theorem, but not the target. The <b>last</b> hypothesis you discharge becomes the <b>outermost</b> antecedent. Press Clear and try another order.`,
          `你证出的是 <span class="m">⊢ ${pretty(s.goal)}</span>，也是定理，但不是目标。<b>最后</b>消去的假设会成为<b>最外层</b>的前件。按“清空”换个顺序再试。`), 'warn');
        return;
      }
      if (s.genuine) {
        okBox(s.msg, bi(`✓ A hypothesis-free Hilbert proof of the target, ${s.lines.length} lines long, every line machine-checked. Only the short proof of r was written by hand; the deduction theorem generated the rest.`, `✓ 得到目标公式的不含假设的希尔伯特证明，共 ${s.lines.length} 行，每行都经机器复核。亲手写的只有那个推出 r 的短证明，其余全由演绎定理自动生成。`));
        Progress.mark('L2E6');
      }
    },
  });
})();
}
