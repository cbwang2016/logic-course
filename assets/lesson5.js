// Lesson 5 interactions: compactness and Löwenheim–Skolem.
Lang.init();
Progress.paint();

const $ = id => document.getElementById(id);
const okBox = (box, html, kind = 'ok') => { box.className = 'msg ' + kind; box.innerHTML = html; };
const clearBox = box => { box.className = 'msg'; box.innerHTML = ''; };
const SUB = '₀₁₂₃₄₅₆₇₈₉';
const sub = n => String(n).split('').map(d => SUB[d]).join('');
const C = {
  accent: '#3b5bdb', true: '#2f9e44', false: '#e03131', meta: '#ae3ec9', gold: '#f08c00', ink: '#1f2430',
  muted: '#6b7280', line: '#d8d3c4', trueSoft: '#d3f9d8', falseSoft: '#ffe3e3', accentSoft: '#e7ecff',
  goldSoft: '#fff3bf', metaSoft: '#f8e7fc', paper: '#f1efe7',
};
function txt(parent, x, y, s, attrs = {}) {
  const t = el('text', Object.assign({ x, y }, attrs), parent);
  t.textContent = s;
  return t;
}
const rnd = n => Math.floor(Math.random() * n);
function shuffle(a) { for (let i = a.length - 1; i > 0; i--) { const j = rnd(i + 1); [a[i], a[j]] = [a[j], a[i]]; } return a; }
const gcd = (a, b) => { a = Math.abs(a); b = Math.abs(b); while (b) [a, b] = [b, a % b]; return a; };

// Step-by-step reveal with a "Show all" button.
function stepper(boxId, nextId, allId) {
  const steps = [...document.querySelectorAll(`#${boxId} .step`)];
  let k = 0;
  const upd = () => { $(nextId).disabled = k >= steps.length; };
  $(nextId).addEventListener('click', () => { if (k < steps.length) steps[k++].classList.add('on'); upd(); });
  $(allId).addEventListener('click', () => { steps.forEach(s => s.classList.add('on')); k = steps.length; upd(); });
}
// Selection buttons in a group: [data-attr] buttons, one selected.
function selGroup(attr, onPick) {
  const bs = [...document.querySelectorAll(`[data-${attr}]`)];
  bs.forEach(b => b.addEventListener('click', () => {
    bs.forEach(x => x.classList.toggle('sel', x === b));
    onPick(b.dataset[attr]);
  }));
}
// Quiz rows: each item {s, ans (index into opts), en, zh, hen?, hzh?}. Marks progress when all solved by the user.
function quizRows(box, items, opts, progId) {
  const solved = items.map(() => false), revealed = items.map(() => false);
  items.forEach((it, i) => {
    const row = document.createElement('div');
    row.className = 'tf';
    row.innerHTML = `<div class="stmt">${it.s}</div>` +
      opts.map((o, k) => `<button class="btn small" data-k="${k}">${o}</button>`).join('') +
      `<button class="btn small ghost" data-k="show">${bil('Show answer', '看答案')}</button>
       <div style="flex-basis:100%"><div class="msg"></div></div>`;
    box.appendChild(row);
    const msg = row.querySelector('.msg');
    row.querySelectorAll('button').forEach(b => b.addEventListener('click', () => {
      if (b.dataset.k === 'show') { revealed[i] = true; okBox(msg, `<b>${opts[it.ans]}</b>. ` + bi(it.en, it.zh), 'info'); return; }
      if (+b.dataset.k === it.ans) {
        okBox(msg, '✓ ' + bi(it.en, it.zh));
        if (!revealed[i]) solved[i] = true;
        if (solved.every(Boolean)) Progress.mark(progId);
      } else okBox(msg, '✗ ' + bi(it.hen || 'Not quite. Think about which finite subsets are satisfiable.', it.hzh || '不对。想想哪些有限子集是可满足的。'), 'bad');
    }));
  });
}
// Single-choice list. opts: {en, zh, ok}. Returns {reveal()}. After reveal(), onRight no longer fires.
function choiceList(box, opts, msgBox, onRight) {
  let revealed = false;
  const btns = opts.map(o => {
    const b = document.createElement('button');
    b.className = 'btn choice';
    b.innerHTML = bi(o.en, o.zh);
    b.addEventListener('click', () => {
      btns.forEach(x => x.classList.remove('right', 'wrongc'));
      b.classList.add(o.ok ? 'right' : 'wrongc');
      if (o.ok) { okBox(msgBox, '✓ ' + bi(o.why_en, o.why_zh)); if (!revealed && onRight) onRight(); }
      else okBox(msgBox, '✗ ' + bi(o.why_en, o.why_zh), 'bad');
    });
    box.appendChild(b);
    return b;
  });
  return {
    reveal() {
      revealed = true;
      const k = opts.findIndex(o => o.ok);
      btns.forEach(x => x.classList.remove('right', 'wrongc'));
      btns[k].classList.add('right');
      okBox(msgBox, bi(opts[k].why_en, opts[k].why_zh), 'info');
    },
  };
}

/* ================= §1 compactness: proof uses finitely many premises ================= */
(function compactProof() {
  const svg = $('cpSvg');
  const NP = 12, BX = k => 20 + k * 66;
  let tok = 0, prem = [], boxes = [], gTrace, gTop;
  function draw() {
    tok++;
    svg.innerHTML = '';
    txt(svg, 20, 16, 'Γ = {σ₀, σ₁, σ₂, …}', { 'font-size': 13, 'font-weight': 700, fill: C.accent });
    txt(svg, 860, 16, 'infinitely many premises · 无穷多个前提', { 'text-anchor': 'end', 'font-size': 12, fill: C.muted });
    gTrace = el('g', {}, svg);
    const gE = el('g', {}, svg), gN = el('g', {}, svg);
    gTop = el('g', {}, svg);
    boxes = [];
    for (let k = 0; k < NP; k++) {
      const g = el('g', { class: 'fadeop' }, svg);
      el('rect', { x: BX(k), y: 26, width: 58, height: 30, rx: 8, fill: '#fff', stroke: C.accent, 'stroke-width': 1.5 }, g);
      txt(g, BX(k) + 29, 46, 'σ' + sub(k), { 'text-anchor': 'middle', 'font-size': 14, 'font-weight': 700 });
      boxes.push(g);
    }
    txt(svg, BX(NP) + 6, 47, '…', { 'font-size': 20, fill: C.muted });
    // derivation tree: 8 leaves → root ⊥
    const m = 3 + rnd(2);
    const leafIdx = shuffle([0, 1, 2, 3, 4, 5, 6, 7]).slice(0, m);
    const ks = shuffle([...Array(NP).keys()]).slice(0, m).sort((a, b) => a - b);
    leafIdx.sort((a, b) => a - b);
    prem = leafIdx.map((li, j) => ({ li, k: ks[j] }));
    const levels = [];
    levels[3] = [...Array(8).keys()].map(i => ({ x: 75 + i * 104, y: 150 }));
    levels[2] = [0, 1, 2, 3].map(i => ({ x: (levels[3][2 * i].x + levels[3][2 * i + 1].x) / 2, y: 210 }));
    levels[1] = [0, 1].map(i => ({ x: (levels[2][2 * i].x + levels[2][2 * i + 1].x) / 2, y: 262 }));
    levels[0] = [{ x: (levels[1][0].x + levels[1][1].x) / 2, y: 312 }];
    for (let d = 1; d <= 3; d++) levels[d].forEach((n, i) => {
      const p = levels[d - 1][i >> 1];
      const ln = el('line', { x1: n.x, y1: n.y, x2: p.x, y2: p.y, stroke: '#9aa0aa', 'stroke-width': 2, class: 'fadein' }, gE);
      ln.style.animationDelay = ((3 - d) * 0.25 + 0.2) + 's';
    });
    for (let d = 3; d >= 0; d--) levels[d].forEach((n, i) => {
      const g = el('g', { transform: `translate(${n.x},${n.y})` }, gN);
      const inner = el('g', { class: 'pop' }, g);
      inner.style.animationDelay = ((3 - d) * 0.25) + 's';
      let label = 'MP', fill = '#fff', stroke = C.ink;
      if (d === 3) {
        const p = prem.find(q => q.li === i);
        if (p) { label = 'σ' + sub(p.k); fill = C.goldSoft; stroke = C.gold; }
        else { label = 'Ax'; fill = C.paper; stroke = '#9aa0aa'; }
      }
      if (d === 0) { label = '⊥'; fill = C.falseSoft; stroke = C.false; }
      el('circle', { r: d === 0 ? 20 : 17, fill, stroke, 'stroke-width': 2 }, inner);
      txt(inner, 0, 5, label, { 'text-anchor': 'middle', 'font-size': d === 3 || d === 0 ? 14 : 11, 'font-weight': 700 });
    });
    txt(svg, 860, 316, 'a derivation of ⊥ from Γ · 从 Γ 推出 ⊥', { 'text-anchor': 'end', 'font-size': 12, fill: C.muted });
    txt(svg, 20, 316, 'Ax = logical axiom · 逻辑公理', { 'font-size': 12, fill: C.muted });
  }
  async function trace() {
    const my = tok;
    boxes.forEach(b => b.style.opacity = 1);
    gTrace.innerHTML = '';
    gTop.innerHTML = '';
    for (const p of prem) {
      if (my !== tok) return;
      el('line', { x1: 75 + p.li * 104, y1: 133, x2: BX(p.k) + 29, y2: 56, stroke: C.gold, 'stroke-width': 2.5, 'stroke-dasharray': '6 4', class: 'fadein' }, gTrace);
      const r = boxes[p.k].querySelector('rect');
      r.setAttribute('fill', C.goldSoft); r.setAttribute('stroke', C.gold); r.setAttribute('stroke-width', 3);
      await sleep(550);
    }
    if (my !== tok) return;
    boxes.forEach((b, k) => { if (!prem.some(p => p.k === k)) b.style.opacity = 0.25; });
    const s = 'Δ = {' + prem.map(p => 'σ' + sub(p.k)).join(', ') + '}  finite! · 有限！';
    el('rect', { x: 270, y: 84, width: 340, height: 26, rx: 8, fill: '#fff', stroke: C.gold, 'stroke-width': 2 }, gTop);
    txt(gTop, 440, 102, s, { 'text-anchor': 'middle', 'font-size': 14, 'font-weight': 700, fill: '#8a5a00' });
  }
  $('cpTrace').addEventListener('click', trace);
  $('cpNew').addEventListener('click', () => { draw(); setTimeout(trace, 1100); });
  draw();
  stepper('cpSteps', 'cpNext', 'cpAll');
})();

/* ================= §1 picker: λ_n and μ_n ================= */
(function picker() {
  const N = 10;
  const selL = new Set([3, 5]), selM = new Set();
  const chipsL = [], chipsM = [];
  function mk(box, arr, set, name) {
    for (let n = 1; n <= N; n++) {
      const c = document.createElement('div');
      c.className = 'chip';
      c.textContent = name + sub(n);
      c.addEventListener('click', () => { set.has(n) ? set.delete(n) : set.add(n); render(); });
      box.appendChild(c);
      arr.push(c);
    }
    const dots = document.createElement('span');
    dots.className = 'muted';
    dots.textContent = ' …';
    box.appendChild(dots);
  }
  mk($('pkL'), chipsL, selL, 'λ');
  mk($('pkM'), chipsM, selM, 'μ');
  function render() {
    const lo = selL.size ? Math.max(...selL) : 1, hi = selM.size ? Math.min(...selM) : Infinity;
    chipsL.forEach((c, i) => { c.className = 'chip' + (selL.has(i + 1) ? ' sel' : ''); });
    chipsM.forEach((c, i) => { c.className = 'chip' + (selM.has(i + 1) ? ' sel' : ''); });
    const svg = $('pkSvg');
    svg.innerHTML = '';
    const D = '{' + [...[...selL].sort((a, b) => a - b).map(n => 'λ' + sub(n)), ...[...selM].sort((a, b) => a - b).map(n => 'μ' + sub(n))].join(', ') + '}';
    if (lo <= hi) {
      const n = lo;
      el('ellipse', { cx: 180, cy: 108, rx: 150, ry: 82, fill: C.trueSoft, stroke: C.true, 'stroke-width': 2 }, svg);
      for (let i = 0; i < n; i++) {
        const a = -Math.PI / 2 + i * 2 * Math.PI / n, r = n === 1 ? 0 : 52;
        const c = el('circle', { cx: 180 + r * Math.cos(a) * 1.6, cy: 108 + r * Math.sin(a), r: 9, fill: C.accent, class: 'pop' }, svg);
        c.style.animationDelay = (i * 0.05) + 's';
      }
      txt(svg, 180, 18, `model with ${n} element${n > 1 ? 's' : ''} · ${n} 元模型`, { 'text-anchor': 'middle', 'font-size': 13, 'font-weight': 700, fill: C.true });
      okBox($('pkMsg'), bi(`Δ = ${D || '∅'} has a model: any set with exactly ${n} element${n > 1 ? 's' : ''} works${hi < Infinity ? ` (sizes ${lo}…${hi} all work)` : ' (indeed any size ≥ ' + lo + ')'}. Every finite subset of {λ₁, λ₂, …} is satisfiable, and so, by compactness, is the whole infinite set.`,
        `Δ = ${D || '∅'} 有模型：恰有 ${n} 个元素的集合即可${hi < Infinity ? `（大小在 ${lo}…${hi} 之间的都行）` : `（实际上任何 ≥ ${lo} 的大小都行）`}。{λ₁, λ₂, …} 的每个有限子集都可满足，所以由紧致性，整个无穷集也可满足。`));
    } else {
      chipsL[lo - 1].className = 'chip no'; chipsM[hi - 1].className = 'chip no';
      el('ellipse', { cx: 180, cy: 108, rx: 150, ry: 82, fill: C.falseSoft, stroke: C.false, 'stroke-width': 2, 'stroke-dasharray': '6 5' }, svg);
      txt(svg, 180, 104, '∅', { 'text-anchor': 'middle', 'font-size': 40, fill: C.false });
      txt(svg, 180, 140, `λ${sub(lo)} ∧ μ${sub(hi)}: ≥ ${lo} and ≤ ${hi}`, { 'text-anchor': 'middle', 'font-size': 13, 'font-weight': 700, fill: C.false });
      txt(svg, 180, 18, 'no model · 没有模型', { 'text-anchor': 'middle', 'font-size': 13, 'font-weight': 700, fill: C.false });
      okBox($('pkMsg'), bi(`Δ = ${D} has no model: λ${sub(lo)} and μ${sub(hi)} already clash. This is compactness read backwards: Γ = {λₙ : n ≥ 1} ∪ {μ${sub(hi)}} is unsatisfiable, and a <b>finite</b> piece of it (here two sentences) already witnesses that.`,
        `Δ = ${D} 没有模型：λ${sub(lo)} 和 μ${sub(hi)} 已经冲突。这就是反过来读的紧致性：Γ = {λₙ : n ≥ 1} ∪ {μ${sub(hi)}} 不可满足，而它的一个<b>有限</b>部分（这里只有两句）就已经说明了这一点。`), 'bad');
    }
  }
  $('pkRand').addEventListener('click', () => {
    selL.clear(); selM.clear();
    for (let i = 0; i < 1 + rnd(3); i++) selL.add(1 + rnd(N));
    if (Math.random() < 0.7) selM.add(1 + rnd(N));
    render();
  });
  $('pkClear').addEventListener('click', () => { selL.clear(); selM.clear(); render(); });
  render();
})();

/* ================= §2 finiteness ================= */
(function finiteness() {
  const svg = $('finSvg');
  function lambdaStr(n) {
    if (n === 1) return 'λ₁ = ∃x₁ (x₁ = x₁)';
    const qs = [...Array(n).keys()].map(i => '∃x' + sub(i + 1)).join('');
    const ineq = [];
    for (let i = 1; i <= n; i++) for (let j = i + 1; j <= n; j++) ineq.push(`x${sub(i)}≠x${sub(j)}`);
    if (n <= 4) return `λ${sub(n)} = ${qs} (${ineq.join(' ∧ ')})`;
    return `λ${sub(n)} = ${qs} ⋀<sub>1≤i&lt;j≤${n}</sub> xᵢ≠xⱼ &nbsp;<span class="muted" style="font-size:13px">(${ineq.length} ${bil('inequalities', '个不等式')})</span>`;
  }
  function render() {
    const n = +$('finN').value;
    $('finNv').textContent = n;
    $('finFormula').innerHTML = lambdaStr(n);
    svg.innerHTML = '';
    for (let s = 1; s <= 9; s++) {
      const x = 8 + (s - 1) * 97, w = 88, inf = s === 9, sat = inf || s >= n;
      const r = el('rect', { x, y: 30, width: w, height: 118, rx: 12, fill: sat ? C.trueSoft : C.paper, stroke: sat ? C.true : C.line, 'stroke-width': inf ? 3 : 2 }, svg);
      r.style.transition = 'fill .3s, stroke .3s';
      txt(svg, x + w / 2, 20, inf ? '|M| = ∞' : `|M| = ${s}`, { 'text-anchor': 'middle', 'font-size': 13, 'font-weight': 700, fill: inf ? C.meta : C.ink });
      const cnt = inf ? 9 : s;
      for (let i = 0; i < cnt; i++) {
        el('circle', { cx: x + 22 + (i % 3) * 22, cy: 54 + Math.floor(i / 3) * 26, r: 7, fill: sat ? C.accent : '#9aa0aa' }, svg);
      }
      if (inf) txt(svg, x + w - 12, 136, '…', { 'font-size': 18, fill: C.meta, 'text-anchor': 'middle' });
      txt(svg, x + w / 2, 172, (sat ? '⊨ λ' : '⊭ λ') + sub(n), { 'text-anchor': 'middle', 'font-size': 15, 'font-weight': 700, fill: sat ? C.true : C.false });
    }
  }
  $('finN').addEventListener('input', render);
  render();
  stepper('finSteps', 'finNext', 'finAll');
})();

/* ================= §3 nonstandard arithmetic ================= */
(function nonstandard() {
  const svg = $('nsA');
  const K = 20, X = k => 30 + k * 32;
  const sel = new Set();
  let allMode = false;
  const chips = [];
  const thc = document.createElement('div');
  thc.className = 'chip sel';
  thc.innerHTML = 'Th(ℕ)';
  thc.title = 'always included · 总是包含';
  $('nsChips').appendChild(thc);
  for (let k = 0; k < K; k++) {
    const c = document.createElement('div');
    c.className = 'chip';
    c.innerHTML = `c &gt; <span style="text-decoration:overline">${k}</span>`;
    c.addEventListener('click', () => { allMode = false; sel.has(k) ? sel.delete(k) : sel.add(k); render(); });
    $('nsChips').appendChild(c);
    chips.push(c);
  }
  const more = document.createElement('span');
  more.className = 'muted';
  more.textContent = ' …';
  $('nsChips').appendChild(more);
  // static axis
  el('line', { x1: 20, y1: 80, x2: 850, y2: 80, stroke: C.ink, 'stroke-width': 2 }, svg);
  const ticks = [];
  for (let k = 0; k <= 25; k++) {
    el('line', { x1: X(k), y1: 74, x2: X(k), y2: 86, stroke: C.ink }, svg);
    ticks.push(txt(svg, X(k), 104, String(k), { 'text-anchor': 'middle', 'font-size': 12 }));
  }
  txt(svg, 858, 85, '…', { 'font-size': 18, fill: C.muted });
  txt(svg, 20, 124, 'ℕ', { 'font-size': 13, 'font-weight': 700, fill: C.accent });
  const mk = el('g', { class: 'mv' }, svg);
  el('path', { d: 'M0,70 L-8,54 L8,54 Z', fill: C.meta }, mk);
  const mlab = txt(mk, 0, 44, 'c', { 'text-anchor': 'middle', 'font-size': 15, 'font-weight': 800, fill: C.meta });
  function render() {
    chips.forEach((c, k) => c.className = 'chip' + (allMode || sel.has(k) ? ' sel' : ''));
    ticks.forEach((t, k) => t.setAttribute('fill', (allMode || sel.has(k)) ? C.false : C.ink));
    if (allMode) {
      mk.style.transform = 'translate(884px, 0px)';
      mlab.textContent = 'c ?';
      okBox($('nsMsgA'), bi('All of Γ at once: c would have to exceed <b>every</b> numeral, and no element of ℕ does that. But every <b>finite</b> Δ ⊆ Γ is satisfied in ℕ, so by compactness Γ has a model M. In M, c is bigger than every n̄: a <b>nonstandard</b> number. And M ⊨ Th(ℕ), so M satisfies exactly the same first-order sentences as ℕ, yet M ≇ ℕ.',
        '同时取整个 Γ：c 必须大于<b>每一个</b>数码，ℕ 中没有这样的元素。但 Γ 的每个<b>有限</b>子集 Δ 都在 ℕ 中被满足，所以由紧致性 Γ 有模型 M。在 M 中 c 比每个 n̄ 都大，是一个<b>非标准</b>数。M ⊨ Th(ℕ)，所以 M 与 ℕ 满足完全相同的一阶语句，却 M ≇ ℕ。'), 'warn');
      return;
    }
    const c = sel.size ? Math.max(...sel) + 1 : 0;
    const D = sel.size ? 'Δ = Th(ℕ) ∪ {' + [...sel].sort((a, b) => a - b).map(k => `c &gt; <span style="text-decoration:overline">${k}</span>`).join(', ') + '}' : 'Δ = Th(ℕ)';
    mk.style.transform = `translate(${X(c)}px, 0px)`;
    mlab.textContent = `c = ${c}`;
    okBox($('nsMsgA'), bi(`${D} is satisfied by ℕ itself with c interpreted as ${c}${sel.size ? ' (one more than the largest bound)' : ''}. Every finite Δ works this way.`,
      `${D} 在 ℕ 本身中成立，只要把 c 解释为 ${c}${sel.size ? '（比最大的下界多 1）' : ''}。每个有限 Δ 都可以这样满足。`));
  }
  $('nsRand').addEventListener('click', () => { allMode = false; sel.clear(); for (let i = 0; i < 2 + rnd(4); i++) sel.add(rnd(K)); render(); });
  $('nsClear').addEventListener('click', () => { allMode = false; sel.clear(); render(); });
  $('nsAll').addEventListener('click', () => { allMode = true; render(); });
  render();

  // Part B: ℤ-blocks
  const svgB = $('nsB');
  let blocks;
  const norm = (n, d) => { const g = gcd(n, d); return [n / g, d / g]; };
  const lab = ([n, d]) => d === 1 ? (n === 1 ? 'c' : n + 'c') : `⌊${n === 1 ? '' : n}c/${d}⌋`;
  function drawB(newIdx = -1) {
    svgB.innerHTML = '';
    for (let i = 0; i < 7; i++) {
      el('circle', { cx: 24 + i * 22, cy: 92, r: 5, fill: C.gold }, svgB);
      txt(svgB, 24 + i * 22, 116, String(i), { 'text-anchor': 'middle', 'font-size': 11 });
    }
    el('line', { x1: 18, y1: 92, x2: 168, y2: 92, stroke: C.gold, 'stroke-width': 2 }, svgB);
    txt(svgB, 180, 97, '…', { 'font-size': 16, fill: C.muted });
    txt(svgB, 90, 150, 'ℕ: standard · 标准部分', { 'text-anchor': 'middle', 'font-size': 12, 'font-weight': 700, fill: '#8a5a00' });
    const L = 230, R = 880, m = blocks.length, slot = (R - L) / m;
    blocks.forEach((b, i) => {
      const cx = L + slot * (i + 0.5), half = Math.min(slot / 2 - 16, 58);
      const g = el('g', {}, svgB);
      if (i === newIdx) g.setAttribute('class', 'pop');
      el('line', { x1: cx - half, y1: 92, x2: cx + half, y2: 92, stroke: i === newIdx ? C.meta : C.accent, 'stroke-width': 2, 'stroke-dasharray': '1 0' }, g);
      for (let j = -2; j <= 2; j++) el('circle', { cx: cx + j * half / 3, cy: 92, r: j ? 3.5 : 5.5, fill: i === newIdx ? C.meta : C.accent }, g);
      txt(g, cx - half - 2, 96, '‹', { 'text-anchor': 'end', 'font-size': 14, fill: C.muted });
      txt(g, cx + half + 2, 96, '›', { 'font-size': 14, fill: C.muted });
      txt(g, cx, 118, lab(b), { 'text-anchor': 'middle', 'font-size': 12, 'font-weight': 700, fill: i === newIdx ? C.meta : C.ink });
    });
    for (let i = 0; i <= m; i++) {
      const gx = i === 0 ? L - 12 : i === m ? R + 8 : L + slot * i;
      const g = el('g', { class: 'clk', transform: `translate(${gx},56)` }, svgB);
      el('circle', { r: 11, fill: '#fff', stroke: C.gold, 'stroke-width': 2 }, g);
      txt(g, 0, 5, '+', { 'text-anchor': 'middle', 'font-size': 16, 'font-weight': 800, fill: C.gold });
      const tt = el('title', {}, g);
      tt.textContent = 'insert a block here · 在此插入一个块';
      g.addEventListener('click', () => insert(i));
    }
    txt(svgB, (L + R) / 2, 160, 'ℤ-blocks, ordered like ℚ: dense, no first, no last · ℤ 块按 ℚ 的方式排列：稠密、无首无尾', { 'text-anchor': 'middle', 'font-size': 12, 'font-weight': 700, fill: C.accent });
    txt(svgB, (L + R) / 2, 180, '(⊕ = click to insert · 点击插入)', { 'text-anchor': 'middle', 'font-size': 11, fill: C.muted });
  }
  function insert(i) {
    if (blocks.length >= 10) {
      okBox($('nsMsgB'), bi('The screen is full (the real model has infinitely many blocks). Press “Reset blocks” to start again.', '画面放不下了（真正的模型有无穷多个块）。按“重置”重新开始。'), 'warn');
      return;
    }
    const m = blocks.length;
    let nb, en, zh;
    if (i === 0) {
      const [n, d] = blocks[0]; nb = norm(n, 2 * d);
      en = `<b>${lab(nb)}</b> is nonstandard (if it were a standard k, then ${lab(blocks[0])} ≤ 2k+1 would be standard too), and ${lab(blocks[0])} − ${lab(nb)} is also nonstandard, so it lies in a <b>new block below</b>. Hence there is <b>no least</b> nonstandard block, and no least nonstandard number.`;
      zh = `<b>${lab(nb)}</b> 是非标准的（若它等于某个标准的 k，则 ${lab(blocks[0])} ≤ 2k+1 也是标准的），而 ${lab(blocks[0])} − ${lab(nb)} 同样是非标准的，所以它落在<b>下方的新块</b>里。因此<b>没有最小的</b>非标准块，也没有最小的非标准数。`;
    } else if (i === m) {
      const [n, d] = blocks[m - 1]; nb = norm(2 * n, d);
      en = `<b>${lab(nb)}</b> − ${lab(blocks[m - 1])} = ${lab(blocks[m - 1])} is nonstandard, so ${lab(nb)} is in a <b>new block above</b>. There is <b>no last</b> block.`;
      zh = `<b>${lab(nb)}</b> − ${lab(blocks[m - 1])} = ${lab(blocks[m - 1])} 是非标准的，所以 ${lab(nb)} 在<b>上方的新块</b>里。<b>没有最后一块</b>。`;
    } else {
      const [n1, d1] = blocks[i - 1], [n2, d2] = blocks[i];
      nb = norm(n1 * d2 + n2 * d1, 2 * d1 * d2);
      en = `<b>${lab(nb)}</b> is the (floor of the) average of ${lab(blocks[i - 1])} and ${lab(blocks[i])}. Its distance to each of them is about half their distance, which is nonstandard, so it lies in a <b>new block in between</b>. The blocks are <b>densely</b> ordered.`;
      zh = `<b>${lab(nb)}</b> 是 ${lab(blocks[i - 1])} 与 ${lab(blocks[i])} 的平均值（取整）。它到两者的距离约为两者距离的一半，仍是非标准的，所以它落在<b>两块之间的新块</b>里。各块之间是<b>稠密</b>排列的。`;
    }
    blocks.splice(i, 0, nb);
    drawB(i);
    okBox($('nsMsgB'), bi(en, zh), 'info');
  }
  function resetB() {
    blocks = [[1, 1], [2, 1], [4, 1]];
    drawB();
    okBox($('nsMsgB'), bi('Two elements are in the same block iff they differ by a standard number. c and 2c differ by c, which is nonstandard, so they lie in different blocks.', '两个元素在同一块中，当且仅当它们相差一个标准数。c 与 2c 相差 c，c 是非标准的，所以它们在不同的块里。'), 'info');
  }
  $('nsReset').addEventListener('click', resetB);
  resetB();
})();

/* ================= §4 graph coloring ================= */
(function coloring() {
  const svg = $('gcSvg');
  const PAL = ['#3b5bdb', '#f08c00', '#2f9e44', '#ae3ec9'];
  let kind = 'strip', k = 3, N = 9;
  let col = Array(40).fill(-1);
  const pos = i => kind === 'strip' ? [40 + i * 52, i % 2 ? 165 : 65] : [40 + Math.floor(i / 2) * 104, i % 2 ? 165 : 65];
  function edges(M) {
    const E = [];
    for (let v = 0; v < M; v++) {
      if (kind === 'strip') { E.push([v, v + 1]); E.push([v, v + 2]); }
      else { if (v % 2 === 0) E.push([v, v + 1]); E.push([v, v + 2]); }
    }
    return E;
  }
  function draw() {
    svg.innerHTML = '';
    const E = edges(N);
    let conflicts = 0;
    E.forEach(([u, v]) => {
      const [x1, y1] = pos(u), [x2, y2] = pos(v);
      if (v >= N) {
        el('line', { x1, y1, x2: (x1 + x2) / 2, y2: (y1 + y2) / 2, stroke: '#9aa0aa', 'stroke-width': 2, 'stroke-dasharray': '4 4', opacity: .7 }, svg);
        return;
      }
      const bad = col[u] >= 0 && col[u] === col[v];
      if (bad) conflicts++;
      el('line', { x1, y1, x2, y2, stroke: bad ? C.false : '#9aa0aa', 'stroke-width': bad ? 5 : 2 }, svg);
    });
    const [lx] = pos(N - 1);
    txt(svg, Math.min(lx + 62, 880), 120, '…', { 'font-size': 22, fill: C.muted, 'text-anchor': 'middle' });
    for (let i = 0; i < N; i++) {
      const [x, y] = pos(i);
      const g = el('g', { class: 'clk', transform: `translate(${x},${y})` }, svg);
      el('circle', { r: 16, fill: col[i] >= 0 ? PAL[col[i]] : '#fff', stroke: C.ink, 'stroke-width': 2 }, g);
      txt(g, 0, 4, 'v' + sub(i), { 'text-anchor': 'middle', 'font-size': 10, 'font-weight': 700, fill: col[i] >= 0 ? '#fff' : C.ink });
      g.addEventListener('click', () => { col[i] = col[i] + 1 >= k ? -1 : col[i] + 1; draw(); status(); });
    }
    txt(svg, 20, 18, `window G${sub(N)}: first ${N} vertices of an infinite graph · 无穷图的前 ${N} 个顶点`, { 'font-size': 12, fill: C.muted });
    draw.conflicts = conflicts;
  }
  function status(extra) {
    const colored = col.slice(0, N).filter(c => c >= 0).length;
    if (extra) { okBox($('gcMsg'), extra.html, extra.kind); return; }
    if (draw.conflicts) okBox($('gcMsg'), bi(`${draw.conflicts} clashing edge(s) (red).`, `有 ${draw.conflicts} 条冲突边（红色）。`), 'bad');
    else if (colored === N) okBox($('gcMsg'), bi(`A proper ${k}-coloring of this window. Every finite subgraph sits inside some window, so if all windows are colorable, compactness gives a coloring of the whole infinite graph.`,
      `这是该窗口的一个合法 ${k} 着色。每个有限子图都包含在某个窗口里；若所有窗口都可着色，紧致性就给出整个无穷图的着色。`));
    else okBox($('gcMsg'), bi(`${colored} / ${N} vertices colored, no clashes yet.`, `已着色 ${colored} / ${N} 个顶点，暂无冲突。`), 'info');
  }
  function solve() {
    const adj = [...Array(N)].map(() => []);
    edges(N).forEach(([u, v]) => { if (v < N) { adj[u].push(v); adj[v].push(u); } });
    const c = Array(N).fill(-1);
    let nodes = 0;
    function bt(i) {
      nodes++;
      if (i === N) return true;
      for (let x = 0; x < k; x++) {
        if (adj[i].every(j => j > i || c[j] !== x)) { c[i] = x; if (bt(i + 1)) return true; }
      }
      c[i] = -1;
      return false;
    }
    const ok = bt(0);
    if (ok) {
      col = col.map((v, i) => i < N ? c[i] : v);
      draw();
      status({ kind: 'ok', html: bi(`Backtracking found a ${k}-coloring (${nodes} search nodes). By compactness: since <b>every</b> window is ${k}-colorable, so is the infinite graph.`, `回溯找到了一个 ${k} 着色（搜索了 ${nodes} 个节点）。由紧致性：既然<b>每个</b>窗口都可 ${k} 着色，整个无穷图也可以。`) });
    } else {
      col = Array(40).fill(-1);
      draw();
      status({ kind: 'bad', html: bi(`No ${k}-coloring of this finite window exists (search exhausted after ${nodes} nodes). Then the infinite graph is not ${k}-colorable either: a coloring of G would restrict to one of the window. ${kind === 'strip' ? 'Here v₀, v₁, v₂ form a triangle.' : ''}`,
        `这个有限窗口不存在 ${k} 着色（搜索 ${nodes} 个节点后穷尽）。那么无穷图也不可 ${k} 着色：G 的着色限制到窗口上就是窗口的着色。${kind === 'strip' ? '这里 v₀、v₁、v₂ 构成三角形。' : ''}`) });
    }
  }
  selGroup('gk', v => { kind = v; col = Array(40).fill(-1); draw(); status(); });
  selGroup('kk', v => { k = +v; col = col.map(c => c >= k ? -1 : c); draw(); status(); });
  $('gcN').addEventListener('input', () => { N = +$('gcN').value; $('gcNv').textContent = N; draw(); status(); });
  $('gcAuto').addEventListener('click', solve);
  $('gcClear').addEventListener('click', () => { col = Array(40).fill(-1); draw(); status(); });
  draw(); status();
  stepper('gcSteps', 'gcNext', 'gcAll');
})();

/* ================= §5 Skolem hull in (ℝ,<,+) ================= */
// Elements of ℚ + ℚ√2 as (a + b√2)/d with integers a, b, d.
const Hull = (() => {
  const mk = (a, b, d) => { if (d < 0) { a = -a; b = -b; d = -d; } const g = gcd(gcd(a, b), d) || 1; return { a: a / g, b: b / g, d: d / g }; };
  const val = x => (x.a + x.b * Math.SQRT2) / x.d;
  const key = x => x.a + ',' + x.b + ',' + x.d;
  const add = (x, y) => mk(x.a * y.d + y.a * x.d, x.b * y.d + y.b * x.d, x.d * y.d);
  const neg = x => mk(-x.a, -x.b, x.d);
  const div = (x, n) => mk(x.a, x.b, x.d * n);
  function show(x) {
    const fr = (n, d) => { const g = gcd(n, d) || 1; n /= g; d /= g; return (n < 0 ? '−' : '') + (d === 1 ? String(Math.abs(n)) : `${Math.abs(n)}/${d}`); };
    const parts = [];
    if (x.a) parts.push(fr(x.a, x.d));
    if (x.b) {
      const g = gcd(x.b, x.d) || 1, n = Math.abs(x.b) / g, d = x.d / g;
      const s = (n === 1 ? '' : n) + '√2' + (d === 1 ? '' : '/' + d);
      parts.push(parts.length ? (x.b < 0 ? '− ' : '+ ') + s : (x.b < 0 ? '−' : '') + s);
    }
    return parts.length ? parts.join(' ') : '0';
  }
  // One closure layer, restricted to a drawable window.
  function layer(all, ok, cap = 70) {
    const cur = [...all.values()].sort((x, y) => x.d - y.d || (Math.abs(x.a) + Math.abs(x.b)) - (Math.abs(y.a) + Math.abs(y.b))).slice(0, cap);
    const fresh = [];
    const push = x => { const kk = key(x); if (ok(x) && !all.has(kk)) { all.set(kk, x); fresh.push(x); } };
    cur.forEach(x => { push(neg(x)); push(div(x, 2)); push(div(x, 3)); });
    cur.forEach(x => cur.forEach(y => { push(add(x, y)); push(add(x, neg(y))); }));
    return fresh;
  }
  return { mk, val, key, add, neg, div, show, layer };
})();
(function hull() {
  const svg = $('shSvg');
  const LO = -3, HI = 3, X = v => 40 + (v - LO) / (HI - LO) * 820;
  const LC = ['#f08c00', '#3b5bdb', '#2f9e44', '#ae3ec9', '#e03131'];
  let seeds = 1, all, layers;
  const ok = x => Math.abs(Hull.val(x)) <= HI + 1e-9 && x.d <= 36 && Math.abs(x.a) <= 300 && Math.abs(x.b) <= 300;
  function reset() {
    all = new Map();
    const s = [Hull.mk(1, 0, 1)];
    if (seeds === 2) s.push(Hull.mk(0, 1, 1));
    s.forEach(x => all.set(Hull.key(x), x));
    layers = [s];
    draw();
  }
  function draw() {
    svg.innerHTML = '';
    el('line', { x1: 30, y1: 190, x2: 870, y2: 190, stroke: C.ink, 'stroke-width': 2 }, svg);
    for (let v = LO; v <= HI; v++) {
      el('line', { x1: X(v), y1: 190, x2: X(v), y2: 198, stroke: C.ink }, svg);
      txt(svg, X(v), 214, String(v), { 'text-anchor': 'middle', 'font-size': 12 });
    }
    txt(svg, 878, 195, 'ℝ', { 'font-size': 14, 'font-weight': 700 });
    layers.forEach((L, li) => {
      const h = 120 - li * 18, last = li === layers.length - 1 && li > 0;
      const g = el('g', last ? { class: 'fadein' } : {}, svg);
      L.forEach(x => {
        const xx = X(Hull.val(x));
        el('line', { x1: xx, y1: 190, x2: xx, y2: 190 - h, stroke: LC[li], 'stroke-width': li === 0 ? 3 : 1.2, opacity: li === 0 ? 1 : 0.75 }, g);
      });
      if (li === 0) L.forEach(x => {
        const xx = X(Hull.val(x));
        el('circle', { cx: xx, cy: 190 - h, r: 6, fill: LC[0] }, g);
        txt(g, xx + 8, 190 - h - 4, Hull.show(x), { 'font-size': 13, 'font-weight': 700, fill: '#8a5a00' });
      });
    });
    // legend
    layers.forEach((L, li) => {
      el('rect', { x: 30 + li * 165, y: 14, width: 12, height: 12, fill: LC[li], rx: 2 }, svg);
      txt(svg, 46 + li * 165, 25, `X${sub(li)}${li ? ' new' : ''}: ${L.length}${li ? '' : (L.length > 1 ? ' seeds' : ' seed')}`, { 'font-size': 12 });
    });
  }
  function step() {
    if (layers.length >= 5) return;
    layers.push(Hull.layer(all, ok));
    draw();
    msg();
  }
  function msg() {
    const n = layers.length - 1;
    const sample = layers[n].slice(0, 6).map(Hull.show).join(', ');
    okBox($('shMsg'), bi(`Layer X${sub(n)}${n ? `: ${layers[n].length} new elements drawn in [−3, 3], e.g. ${sample}` : ': the seeds'}. Each layer is the image of the previous one under countably many functions, so countable; the union of ω layers is countable. With only x/2 and x/3 the union would contain just the fractions whose denominators are products of 2s and 3s; with x ↦ x/n for <i>every</i> n the limit is ${seeds === 1 ? '<b>ℚ</b>' : '<b>ℚ + ℚ√2</b>'}: dense in ℝ, yet countable, and an elementary substructure of (ℝ, &lt;, +). (Only elements with denominator ≤ 36 are drawn.)`,
      `第 X${sub(n)} 层${n ? `：在 [−3, 3] 中新画出 ${layers[n].length} 个元素，例如 ${sample}` : '：种子'}。每一层都是上一层在可数多个函数下的像，所以可数；ω 层之并仍可数。只用 x/2 和 x/3 时，并集只含分母为 2 与 3 的乘积的分数；对<i>每个</i> n 都用 x ↦ x/n，极限就是 ${seeds === 1 ? '<b>ℚ</b>' : '<b>ℚ + ℚ√2</b>'}：在 ℝ 中稠密，却是可数的，而且是 (ℝ, &lt;, +) 的初等子结构。（图中只画分母 ≤ 36 的元素。）`), 'info');
  }
  selGroup('seed', v => { seeds = +v; reset(); msg(); });
  $('shStep').addEventListener('click', step);
  $('shAll').addEventListener('click', () => { reset(); for (let i = 0; i < 4; i++) layers.push(Hull.layer(all, ok)); draw(); msg(); });
  reset(); msg();
  stepper('shSteps', 'shNext', 'shAllP');
})();

/* ================= §6 elementary substructures ================= */
const EL_PAIRS = [
  { id: 'QR', name: '(ℚ,<) ⊆ (ℝ,<)', big: 'R', small: { type: 'Q' }, lo: -2, hi: 3, elem: true,
    tests: [
      { f: '∃y (x < y ∧ y < z)', p: [['x', 0, '0'], ['z', 1, '1']], M: true, N: true, w: [0.5, '1/2'], wIn: true },
      { f: '∃y (y < x)', p: [['x', 0, '0']], M: true, N: true, w: [-1, '−1'], wIn: true },
      { f: '∃y (x < y ∧ ¬∃u (x < u ∧ u < y))', p: [['x', 0, '0']], M: false, N: false, en: 'x has an immediate successor', zh: 'x 有直接后继' },
    ],
    en: '<b>Elementary: (ℚ,&lt;) ≼ (ℝ,&lt;).</b> Tarski–Vaught: if ℝ ⊨ ∃y φ(ā, y) with ā rational, take a witness b. There is an order-automorphism σ of ℝ (piecewise linear) fixing every aᵢ and sending b to a rational in the same gap. σ preserves truth, so σ(b) ∈ ℚ is a witness.',
    zh: '<b>是初等子结构：(ℚ,&lt;) ≼ (ℝ,&lt;)。</b>用塔斯基–沃特判别法：若 ℝ ⊨ ∃y φ(ā, y)，ā 是有理数，取一个见证 b。存在 ℝ 的保序自同构 σ（分段线性），固定每个 aᵢ，并把 b 送到同一空隙中的某个有理数。σ 保持真假，所以 σ(b) ∈ ℚ 也是见证。' },
  { id: 'NN', name: '(ℕ⁺,<) ⊆ (ℕ,<)', big: 'Z0', small: { type: 'Z', pred: v => v >= 1 }, lo: 0, hi: 9, elem: false,
    tests: [
      { f: '∃y (y < x)', p: [['x', 1, '1']], M: false, N: true, w: [0, '0'], wIn: false },
      { f: '∃y (y < x)', p: [['x', 3, '3']], M: true, N: true, w: [2, '2'], wIn: true },
      { f: '∃x ∀y (x ≤ y)', p: [], M: true, N: true, en: 'a sentence: there is a least element', zh: '语句：存在最小元' },
    ],
    en: '<b>Not elementary</b>, although (ℕ⁺,&lt;) ≅ (ℕ,&lt;) via n ↦ n−1, so they satisfy the same <i>sentences</i>. With the parameter 1, “∃y (y &lt; 1)” is false in ℕ⁺ but true in ℕ: the only witness, 0, is outside ℕ⁺. Isomorphic ≠ elementary substructure.',
    zh: '<b>不是初等子结构</b>，尽管 (ℕ⁺,&lt;) 经 n ↦ n−1 与 (ℕ,&lt;) 同构，二者满足相同的<i>语句</i>。代入参数 1，“∃y (y &lt; 1)”在 ℕ⁺ 中假、在 ℕ 中真：唯一的见证 0 不在 ℕ⁺ 里。同构 ≠ 初等子结构。' },
  { id: 'ZQ', name: '(ℤ,<) ⊆ (ℚ,<)', big: 'Q', small: { type: 'Z', pred: () => true }, lo: -3, hi: 4, elem: false,
    tests: [
      { f: '∃y (x < y ∧ y < z)', p: [['x', 0, '0'], ['z', 1, '1']], M: false, N: true, w: [0.5, '1/2'], wIn: false },
      { f: '∀x ∀z (x < z → ∃y (x < y ∧ y < z))', p: [], M: false, N: true, en: 'density (a sentence)', zh: '稠密性（语句）' },
    ],
    en: '<b>Not elementary</b>, not even elementarily equivalent: the density sentence is false in ℤ and true in ℚ.',
    zh: '<b>不是初等子结构</b>，连初等等价都不是：稠密性语句在 ℤ 中假、在 ℚ 中真。' },
  { id: '2Z', name: '(2ℤ,+) ⊆ (ℤ,+)', big: 'Z', small: { type: 'Z', pred: v => v % 2 === 0 }, lo: -4, hi: 6, elem: false,
    tests: [
      { f: '∃y (y + y = x)', p: [['x', 2, '2']], M: false, N: true, w: [1, '1'], wIn: false },
      { f: '∃y (y + y = x)', p: [['x', 4, '4']], M: true, N: true, w: [2, '2'], wIn: true },
      { f: '∃x ∀y (y + y ≠ x)', p: [], M: true, N: true, en: 'a sentence: some element is not a double', zh: '语句：有元素不是“二倍”' },
    ],
    en: '<b>Not elementary</b>, although n ↦ 2n is an isomorphism (ℤ,+) ≅ (2ℤ,+), so the two satisfy the same sentences. “2 is divisible by 2” holds in ℤ but not in 2ℤ.',
    zh: '<b>不是初等子结构</b>，尽管 n ↦ 2n 是同构 (ℤ,+) ≅ (2ℤ,+)，二者满足相同的语句。“2 能被 2 整除”在 ℤ 中成立，在 2ℤ 中不成立。' },
  { id: 'H', name: '([0,∞),<) ⊆ (ℝ,<)', big: 'R', small: { type: 'int', a: 0, b: Infinity, aOpen: false }, lo: -2, hi: 3, elem: false,
    tests: [
      { f: '∃y (y < x)', p: [['x', 0, '0']], M: false, N: true, w: [-1, '−1'], wIn: false },
      { f: '∃x ∀y (x ≤ y)', p: [], M: true, N: false, en: 'a least element exists (a sentence)', zh: '存在最小元（语句）' },
    ],
    en: '<b>Not elementary</b>, not even ≡: [0,∞) has a least element and ℝ does not.',
    zh: '<b>不是初等子结构</b>，连 ≡ 都不是：[0,∞) 有最小元，ℝ 没有。' },
  { id: 'I', name: '((0,1),<) ⊆ (ℝ,<)', big: 'R', small: { type: 'int', a: 0, b: 1, aOpen: true, bOpen: true }, lo: -1, hi: 2, elem: true,
    tests: [
      { f: '∃y (y < x)', p: [['x', 0.5, '1/2']], M: true, N: true, w: [0.25, '1/4'], wIn: true },
      { f: '∃y (x < y ∧ y < z)', p: [['x', 0.25, '1/4'], ['z', 0.75, '3/4']], M: true, N: true, w: [0.5, '1/2'], wIn: true },
      { f: '∃x ∀y (x ≤ y)', p: [], M: false, N: false, en: 'no least element (a sentence)', zh: '没有最小元（语句）' },
    ],
    en: '<b>Elementary.</b> Same automorphism trick as ℚ ⊆ ℝ: an order-automorphism of ℝ fixing the finitely many parameters in (0,1) can move any witness into (0,1). Note that ℝ ⊨ ∃y (y &lt; 1/2) also has witnesses like −5 outside M; Tarski–Vaught only needs <i>one</i> witness inside.',
    zh: '<b>是初等子结构。</b>与 ℚ ⊆ ℝ 同样的自同构技巧：ℝ 的一个保序自同构固定 (0,1) 中有限多个参数，并能把任何见证移进 (0,1)。注意 ℝ ⊨ ∃y (y &lt; 1/2) 也有 −5 这样在 M 之外的见证；塔斯基–沃特判别法只要求 M 中<i>有一个</i>见证。' },
];
(function elementary() {
  const svg = $('elSvg');
  let pair = EL_PAIRS[0], cur = -1, seen = new Set();
  const X = v => 60 + (v - pair.lo) / (pair.hi - pair.lo) * 780;
  function inSmall(v) {
    const s = pair.small;
    if (s.type === 'Q') return Number.isInteger(v * 8);
    if (s.type === 'Z') return Number.isInteger(v) && s.pred(v);
    return (s.aOpen ? v > s.a : v >= s.a) && (s.bOpen ? v < s.b : v <= s.b);
  }
  function draw() {
    svg.innerHTML = '';
    const Y = 92, s = pair.small;
    const [mName, nName] = pair.name.split(' ⊆ ');
    txt(svg, 20, 20, `N = ${nName}`, { 'font-size': 13, 'font-weight': 700, fill: C.muted });
    txt(svg, 20, 38, `M = ${mName}`, { 'font-size': 13, 'font-weight': 700, fill: C.accent });
    if (pair.big === 'R') el('line', { x1: 50, y1: Y, x2: 850, y2: Y, stroke: '#9aa0aa', 'stroke-width': 3 }, svg);
    if (pair.big === 'Q') el('line', { x1: 50, y1: Y, x2: 850, y2: Y, stroke: '#9aa0aa', 'stroke-width': 3, 'stroke-dasharray': '2 3' }, svg);
    if (s.type === 'Q') el('line', { x1: 50, y1: Y, x2: 850, y2: Y, stroke: C.accent, 'stroke-width': 3, 'stroke-dasharray': '2 4' }, svg);
    if (s.type === 'int') {
      const a = Math.max(s.a, pair.lo - 1), b = Math.min(s.b, pair.hi + 1);
      el('line', { x1: Math.max(50, X(a)), y1: Y, x2: Math.min(850, X(b)), y2: Y, stroke: C.accent, 'stroke-width': 6 }, svg);
      [[s.a, s.aOpen], [s.b, s.bOpen]].forEach(([e, open]) => {
        if (e >= pair.lo && e <= pair.hi) el('circle', { cx: X(e), cy: Y, r: 6, fill: open ? '#fff' : C.accent, stroke: C.accent, 'stroke-width': 2.5 }, svg);
      });
    }
    for (let v = Math.ceil(pair.lo); v <= pair.hi; v++) {
      if (pair.big === 'Z' || pair.big === 'Z0') {
        if (pair.big === 'Z0' && v < 0) continue;
        const inn = inSmall(v);
        el('circle', { cx: X(v), cy: Y, r: 8, fill: inn ? C.accent : '#fff', stroke: inn ? C.accent : '#9aa0aa', 'stroke-width': 2 }, svg);
      } else el('line', { x1: X(v), y1: Y - 6, x2: X(v), y2: Y + 6, stroke: C.ink }, svg);
      txt(svg, X(v), Y + 26, String(v), { 'text-anchor': 'middle', 'font-size': 12 });
    }
    if (pair.big !== 'Z0') txt(svg, 856, Y + 5, '…', { 'font-size': 16, fill: C.muted });
    else txt(svg, X(pair.hi) + 22, Y + 5, '…', { 'font-size': 16, fill: C.muted });
    if (cur < 0) {
      txt(svg, 450, 150, 'click a formula row below · 点击下面的公式行', { 'text-anchor': 'middle', 'font-size': 12, fill: C.muted });
      return;
    }
    const t = pair.tests[cur];
    t.p.forEach(([nm, v, lb], i) => {
      const g = el('g', { class: 'pop' }, el('g', { transform: `translate(${X(v)},${Y - 14})` }, svg));
      el('path', { d: 'M0,0 L-7,-12 L7,-12 Z', fill: C.meta }, g);
      txt(g, 0, -17 - (i % 2) * 15, `${nm} = ${lb}`, { 'text-anchor': 'middle', 'font-size': 12, 'font-weight': 700, fill: C.meta });
    });
    if (t.w) {
      const [v, lb] = t.w, colr = t.wIn ? C.true : C.false;
      const g = el('g', { class: 'pop' }, el('g', { transform: `translate(${X(v)},${Y + 40})` }, svg));
      el('path', { d: 'M0,-12 L7,0 L-7,0 Z', fill: colr }, g);
      txt(g, 0, 16, `y = ${lb} ${t.wIn ? '∈ M' : '∉ M'}`, { 'text-anchor': 'middle', 'font-size': 12, 'font-weight': 700, fill: colr });
    }
  }
  function table() {
    const yes = '<b style="color:var(--true)">✓</b>', no = '<b style="color:var(--false)">✗</b>';
    let h = `<table class="tt rows"><thead><tr><th>φ</th><th>${bil('parameters', '参数')}</th><th>M ⊨ φ ?</th><th>N ⊨ φ ?</th><th>${bil('Tarski–Vaught', '塔斯基–沃特')}</th></tr></thead><tbody>`;
    pair.tests.forEach((t, i) => {
      const s = seen.has(i);
      let tv = '—';
      if (s && t.w) tv = t.wIn ? bil('witness in M', '见证在 M 中') : `<b style="color:var(--false)">${bil('witness only outside M', '见证只在 M 外')}</b>`;
      if (s && !t.w) tv = t.en ? `<span class="muted">${bil(t.en, t.zh)}</span>` : '—';
      const differ = s && t.M !== t.N;
      h += `<tr class="clk${i === cur ? ' cur' : ''}" data-i="${i}"><td class="m">${t.f}</td><td class="m">${t.p.map(q => q[0] + '=' + q[2]).join(', ') || '—'}</td>
        <td class="${s ? '' : 'q'}">${s ? (t.M ? yes : no) : '?'}</td><td class="${s ? '' : 'q'}">${s ? (t.N ? yes : no) : '?'}</td>
        <td style="${differ ? 'background:var(--false-soft)' : ''}">${tv}</td></tr>`;
    });
    $('elTable').innerHTML = h + '</tbody></table>';
    $('elTable').querySelectorAll('tr.clk').forEach(tr => tr.addEventListener('click', () => {
      cur = +tr.dataset.i; seen.add(cur); draw(); table();
      const t = pair.tests[cur];
      if (t.M !== t.N) okBox($('elMsg'), bi(`M and N <b>disagree</b> on this formula, so M ⋠ N.`, `M 与 N 对这个公式的判断<b>不一致</b>，所以 M ⋠ N。`), 'bad');
      else okBox($('elMsg'), bi(`M and N agree here (${t.M ? 'both true' : 'both false'}).`, `M 与 N 在这里一致（${t.M ? '都为真' : '都为假'}）。`), 'info');
    }));
  }
  function pick(i) {
    pair = EL_PAIRS[i]; cur = -1; seen = new Set();
    $('elPairs').querySelectorAll('button').forEach((b, k) => b.classList.toggle('sel', k === i));
    clearBox($('elMsg')); clearBox($('elVerdict'));
    draw(); table();
  }
  EL_PAIRS.forEach((p, i) => {
    const b = document.createElement('button');
    b.className = 'btn small';
    b.innerHTML = `<span class="m">${p.name}</span>`;
    b.addEventListener('click', () => pick(i));
    $('elPairs').appendChild(b);
  });
  $('elVerdictBtn').addEventListener('click', () => okBox($('elVerdict'), bi(pair.en, pair.zh), pair.elem ? 'ok' : 'warn'));
  pick(0);
})();

/* ================= §7 Skolem's paradox ================= */
(function skolem() {
  const svg = $('skSvg');
  let mode = 'in', tok = 0;
  const cloud = [];
  for (let i = 0; i < 160; i++) {
    const a = Math.random() * 2 * Math.PI, r = Math.sqrt(Math.random());
    cloud.push([580 + r * 255 * Math.cos(a), 222 + r * 68 * Math.sin(a)]);
  }
  function draw() {
    tok++;
    svg.innerHTML = '';
    if (mode === 'in') {
      el('rect', { x: 10, y: 10, width: 880, height: 340, rx: 24, fill: C.metaSoft, stroke: C.meta, 'stroke-width': 2 }, svg);
      txt(svg, 30, 38, 'M, seen from inside: this is “the universe” · 从 M 内部看：这就是“全宇宙”', { 'font-size': 14, 'font-weight': 700, fill: C.meta });
      txt(svg, 40, 86, 'ω', { 'font-size': 16, 'font-weight': 700 });
      for (let n = 0; n < 9; n++) {
        el('circle', { cx: 80 + n * 40, cy: 82, r: 6, fill: C.gold }, svg);
        txt(svg, 80 + n * 40, 104, String(n), { 'text-anchor': 'middle', 'font-size': 11 });
      }
      txt(svg, 80 + 9 * 40 - 8, 87, '…', { 'font-size': 16, fill: C.muted });
      el('ellipse', { cx: 580, cy: 222, rx: 270, ry: 80, fill: '#fff', stroke: C.accent, 'stroke-width': 2 }, svg);
      cloud.forEach(([x, y]) => el('circle', { cx: x, cy: y, r: 1.6, fill: C.accent, opacity: 0.6 }, svg));
      txt(svg, 40, 226, 'ℝ (huge) · ℝ（极大）', { 'font-size': 14, 'font-weight': 700, fill: C.accent });
      txt(svg, 30, 330, 'M ⊨ “no g: ω → ℝ is onto” · M ⊨ “不存在 ω 到 ℝ 的满射”', { 'font-size': 13, 'font-weight': 700, fill: C.ink });
    } else {
      el('rect', { x: 10, y: 10, width: 880, height: 340, rx: 24, fill: '#fbfaf6', stroke: C.ink, 'stroke-width': 2 }, svg);
      txt(svg, 30, 38, 'V: the real universe of sets (outside view) · V：真正的集合宇宙（外部视角）', { 'font-size': 14, 'font-weight': 700 });
      el('circle', { cx: 600, cy: 195, r: 140, fill: C.metaSoft, stroke: C.meta, 'stroke-width': 2 }, svg);
      txt(svg, 600, 88, 'M (countable · 可数)', { 'text-anchor': 'middle', 'font-size': 13, 'font-weight': 700, fill: C.meta });
      el('rect', { x: 510, y: 100, width: 180, height: 200, rx: 14, fill: '#fff', stroke: C.accent, 'stroke-width': 2 }, svg);
      txt(svg, 600, 120, 'ℝ^M', { 'text-anchor': 'middle', 'font-size': 14, 'font-weight': 700, fill: C.accent });
      for (let n = 0; n < 8; n++) {
        const x = 545 + (n % 2) * 70, y = 145 + Math.floor(n / 2) * 36;
        el('circle', { cx: x, cy: y, r: 6, fill: C.accent }, svg);
        txt(svg, x + 12, y + 5, 'r' + sub(n), { 'font-size': 12 });
      }
      txt(svg, 600, 292, '⋮', { 'text-anchor': 'middle', 'font-size': 16, fill: C.muted });
      txt(svg, 70, 88, 'ℕ', { 'font-size': 16, 'font-weight': 700 });
      for (let n = 0; n < 8; n++) {
        el('circle', { cx: 90, cy: 110 + n * 26, r: 6, fill: C.gold }, svg);
        txt(svg, 74, 115 + n * 26, String(n), { 'text-anchor': 'end', 'font-size': 11 });
      }
      txt(svg, 90, 330, '⋮', { 'text-anchor': 'middle', 'font-size': 16, fill: C.muted });
    }
  }
  async function run() {
    draw();
    const my = tok;
    if (mode === 'in') {
      const hits = [];
      for (let n = 0; n < 9; n++) {
        if (my !== tok) return;
        const [x, y] = cloud[rnd(cloud.length)];
        hits.push([x, y]);
        el('path', { d: `M${80 + n * 40},88 Q${(80 + n * 40 + x) / 2},${150} ${x},${y}`, fill: 'none', stroke: C.gold, 'stroke-width': 1.6, class: 'fadein' }, svg);
        el('circle', { cx: x, cy: y, r: 5, fill: C.gold, class: 'pop' }, svg);
        await sleep(260);
      }
      if (my !== tok) return;
      const g = el('g', { class: 'pop' }, el('g', { transform: 'translate(820,262)' }, svg));
      el('path', { d: 'M0,-12 L3.5,-4 L12,-4 L5,2 L8,11 L0,5 L-8,11 L-5,2 L-12,-4 L-3.5,-4 Z', fill: C.false }, g);
      txt(svg, 870, 318, 'diagonal d ∉ range(g) · 对角线实数 d 不在 g 的值域中', { 'text-anchor': 'end', 'font-size': 12, 'font-weight': 700, fill: C.false });
      okBox($('skMsg'), bi('Here g ∈ M is an attempted enumeration. M can run Cantor\'s diagonal argument on g and build d ∈ ℝ<sup>M</sup> outside the range of g. Since this works for <b>every</b> g ∈ M, M ⊨ “ℝ is uncountable”. Press Run again for another g.',
        'g ∈ M 是一个试图枚举 ℝ 的函数。M 可以对 g 做康托尔对角线论证，造出不在 g 值域中的 d ∈ ℝ<sup>M</sup>。这对 M 中的<b>每个</b> g 都成立，所以 M ⊨ “ℝ 不可数”。再按一次“演示”换一个 g。'), 'info');
    } else {
      for (let n = 0; n < 8; n++) {
        if (my !== tok) return;
        const x = 545 + (n % 2) * 70, y = 145 + Math.floor(n / 2) * 36;
        el('line', { x1: 98, y1: 110 + n * 26, x2: x - 8, y2: y, stroke: C.false, 'stroke-width': 1.8, 'stroke-dasharray': '6 4', class: 'fadein' }, svg);
        await sleep(280);
      }
      if (my !== tok) return;
      el('rect', { x: 150, y: 296, width: 330, height: 42, rx: 10, fill: '#fff', stroke: C.false, 'stroke-width': 2, class: 'fadein' }, svg);
      txt(svg, 315, 314, 'f: ℕ → ℝ^M onto;  f ∈ V,  f ∉ M', { 'text-anchor': 'middle', 'font-size': 13, 'font-weight': 700, fill: C.false });
      txt(svg, 315, 331, 'f 是满射，f 在 V 中，但 f 不属于 M', { 'text-anchor': 'middle', 'font-size': 12, 'font-weight': 700, fill: C.false });
      okBox($('skMsg'), bi('From outside, M is countable, so its set ℝ<sup>M</sup> has only countably many members and we can list them: f(n) = rₙ. The red arrows are drawn <b>outside</b> M because f is not an element of M. M cannot see f, so M\'s claim “no onto map ω → ℝ exists” remains true <i>in M</i>.',
        '从外面看，M 可数，所以 ℝ<sup>M</sup> 只有可数个成员，可以列出来：f(n) = rₙ。红色箭头画在 M <b>外面</b>，因为 f 不是 M 的元素。M 看不见 f，所以 M 的断言“不存在 ω 到 ℝ 的满射”<i>在 M 中</i>仍然成立。'), 'info');
    }
  }
  selGroup('sk', v => { mode = v; draw(); clearBox($('skMsg')); });
  $('skGo').addEventListener('click', run);
  draw();
  stepper('skSteps', 'skNext', 'skAll');
})();

/* ================= §8 upward LS ================= */
(function upward() {
  const svg = $('upSvg');
  let kap = 'ℵ₁', stage = 0;
  function blob(cx, w, label, color, soft, dots, cls) {
    const g = el('g', cls ? { class: cls } : {}, svg);
    el('ellipse', { cx, cy: 110, rx: w, ry: 62, fill: soft, stroke: color, 'stroke-width': 2 }, g);
    txt(g, cx, 32, label, { 'text-anchor': 'middle', 'font-size': 13, 'font-weight': 700, fill: color });
    dots.forEach(([x, y, l, c]) => {
      el('circle', { cx: x, cy: y, r: 4, fill: c || C.accent }, g);
      if (l) txt(g, x + 6, y + 4, l, { 'font-size': 10, fill: c || C.ink });
    });
    return g;
  }
  function draw() {
    svg.innerHTML = '';
    const md = [];
    for (let i = 0; i < 12; i++) md.push([105 + (i % 4) * 22, 88 + Math.floor(i / 4) * 22]);
    blob(140, 80, 'M ⊨ T (infinite · 无穷)', C.accent, C.accentSoft, md);
    if (stage >= 1) {
      txt(svg, 300, 100, '⟶', { 'text-anchor': 'middle', 'font-size': 26, fill: C.gold, class: 'fadein' });
      txt(svg, 300, 128, 'compactness', { 'text-anchor': 'middle', 'font-size': 11, fill: C.gold });
      txt(svg, 300, 142, '紧致性', { 'text-anchor': 'middle', 'font-size': 11, fill: C.gold });
      const d = [];
      for (let i = 0; i < 12; i++) d.push([385 + (i % 6) * 22, 80 + Math.floor(i / 6) * 22]);
      const cl = ['c₀', 'c₁', 'c₂', 'c_ω', 'c_α', '…'];
      cl.forEach((l, i) => d.push([382 + i * 26, 140 + (i % 2) * 18, l, C.gold]));
      blob(450, 110, `N ⊨ T ∪ {cᵢ ≠ cⱼ}, |N| ≥ ${kap}`, C.gold, C.goldSoft, d, 'pop');
    }
    if (stage >= 2) {
      txt(svg, 615, 100, '⟶', { 'text-anchor': 'middle', 'font-size': 26, fill: C.true, class: 'fadein' });
      txt(svg, 615, 128, 'downward LS', { 'text-anchor': 'middle', 'font-size': 11, fill: C.true });
      txt(svg, 615, 142, '向下 LS', { 'text-anchor': 'middle', 'font-size': 11, fill: C.true });
      const d = [];
      for (let i = 0; i < 8; i++) d.push([700 + (i % 4) * 22, 84 + Math.floor(i / 4) * 22]);
      ['c₀', 'c₁', 'c_α', '…'].forEach((l, i) => d.push([700 + i * 30, 140 + (i % 2) * 14, l, C.gold]));
      blob(760, 100, `N' ≼ N, |N'| = ${kap}`, C.true, C.trueSoft, d, 'pop');
    }
  }
  function msg() {
    const m = [
      bi(`Start: T has an infinite model M. Target: a model of size exactly κ = ${kap}. Press “Next move”.`, `起点：T 有无穷模型 M。目标：一个大小恰为 κ = ${kap} 的模型。按“下一步”。`),
      bi(`Add κ new constants cᵢ (i &lt; κ) and the sentences cᵢ ≠ cⱼ (i ≠ j). A finite subset mentions only finitely many cᵢ, and M satisfies it: interpret those cᵢ as distinct elements of the infinite M. By compactness, T ∪ {cᵢ ≠ cⱼ} has a model N, and the cᵢ name κ distinct elements, so |N| ≥ κ.`,
        `加入 κ 个新常元 cᵢ（i &lt; κ）以及语句 cᵢ ≠ cⱼ（i ≠ j）。任一有限子集只涉及有限个 cᵢ，M 就能满足它：把这些 cᵢ 解释成无穷集 M 中互不相同的元素。由紧致性，T ∪ {cᵢ ≠ cⱼ} 有模型 N，其中 cᵢ 指称 κ 个不同元素，所以 |N| ≥ κ。`),
      bi(`The expanded language has size κ. Apply downward LS in N to X = {cᵢ<sup>N</sup> : i &lt; κ}: get N' ≼ N with X ⊆ N' and |N'| ≤ κ + |L| + ℵ₀ = κ. Since X ⊆ N', |N'| = κ exactly, and N' ⊨ T. ∎`,
        `扩充后的语言大小为 κ。在 N 中对 X = {cᵢ<sup>N</sup> : i &lt; κ} 用向下 LS 定理，得到 N' ≼ N，X ⊆ N'，且 |N'| ≤ κ + |L| + ℵ₀ = κ。又 X ⊆ N'，所以 |N'| 恰为 κ，且 N' ⊨ T。∎`),
    ];
    $('upMsg').innerHTML = m[stage];
  }
  selGroup('kap', v => { kap = v; draw(); msg(); });
  $('upStep').addEventListener('click', () => { if (stage < 2) stage++; draw(); msg(); });
  $('upReset').addEventListener('click', () => { stage = 0; draw(); msg(); });
  draw(); msg();

  // spectra
  const sp = $('spSvg');
  const PTS = [
    { l: '1', x: 40, f: 1 }, { l: '2', x: 85, f: 2 }, { l: '3', x: 130, f: 3 }, { l: '4', x: 175, f: 4 }, { l: '5', x: 220, f: 5 }, { l: '…', x: 265, f: 6, dots: 1 },
    { l: 'ℵ₀', x: 370, i: 0 }, { l: 'ℵ₁', x: 450, i: 1 }, { l: 'ℵ₂', x: 530, i: 2 }, { l: '…', x: 600, i: 3, dots: 1 }, { l: 'ℵ_ω', x: 670, i: 4 }, { l: 'ℵ_ω+1', x: 760, i: 5 }, { l: '…', x: 840, i: 6, dots: 1 },
  ];
  const TH = [
    { en: 'exactly 3 elements', zh: '恰有 3 个元素', mod: p => p.f === 3, cat: p => p.f === 3,
      ten: 'λ₃ ∧ μ₃: only a 3-element model, unique up to ≅. No infinite model, so LS says nothing.', tzh: 'λ₃ ∧ μ₃：只有 3 元模型，在同构意义下唯一。没有无穷模型，LS 定理管不着。' },
    { en: 'pure sets (empty theory in {=})', zh: '纯集合（{=} 上的空理论）', mod: () => true, cat: () => true,
      ten: 'Every nonempty set is a model; two models are isomorphic iff they have the same size. Categorical in every cardinality.', tzh: '每个非空集合都是模型；两个模型同构当且仅当大小相同。在每个基数上都是范畴的。' },
    { en: 'infinite sets {λₙ}', zh: '无穷集合 {λₙ}', mod: p => p.i !== undefined, cat: p => p.i !== undefined,
      ten: 'Models: exactly the infinite sets. κ-categorical for every infinite κ (a bijection is an isomorphism).', tzh: '模型恰好是无穷集合。对每个无穷基数 κ 都是 κ-范畴的（任何双射都是同构）。' },
    { en: 'DLO without endpoints', zh: '无端点稠密线序 DLO', mod: p => p.i !== undefined, cat: p => p.i === 0,
      ten: 'Models in every infinite size (LS), ℵ₀-categorical (Cantor, §9), but not categorical in any uncountable κ.', tzh: '每个无穷基数上都有模型（LS 定理），ℵ₀-范畴（康托尔，见 §9），但在任何不可数 κ 上都不是范畴的。' },
    { en: 'ACF₀ (alg. closed fields, char 0)', zh: 'ACF₀（特征 0 的代数闭域）', mod: p => p.i !== undefined, cat: p => p.i !== undefined && p.i > 0,
      ten: 'Categorical in every uncountable κ (a model is determined by its transcendence degree), but not ℵ₀-categorical: the algebraic closures of ℚ, ℚ(t), ℚ(t,u), … are pairwise non-isomorphic countable models.', tzh: '在每个不可数 κ 上都是范畴的（模型由超越次数决定），但不是 ℵ₀-范畴的：ℚ、ℚ(t)、ℚ(t,u)…的代数闭包是两两不同构的可数模型。' },
    { en: 'Th(ℕ, +, ·)', zh: 'Th(ℕ, +, ·)', mod: p => p.i !== undefined, cat: () => false,
      ten: 'A complete theory with models in every infinite size, categorical in none: already there are 2^ℵ₀ non-isomorphic countable models. First-order logic cannot pin down ℕ.', tzh: '完全理论，每个无穷基数上都有模型，却在任何基数上都不是范畴的：仅可数模型就有 2^ℵ₀ 个互不同构。一阶逻辑刻画不了 ℕ。' },
  ];
  let th = 3;
  function drawSp() {
    sp.innerHTML = '';
    const Y = 62, t = TH[th];
    el('line', { x1: 20, y1: Y, x2: 880, y2: Y, stroke: C.line, 'stroke-width': 3 }, sp);
    el('line', { x1: 315, y1: 20, x2: 315, y2: 110, stroke: C.muted, 'stroke-dasharray': '4 4' }, sp);
    txt(sp, 160, 18, 'finite · 有限', { 'text-anchor': 'middle', 'font-size': 12, fill: C.muted });
    txt(sp, 600, 18, 'infinite · 无穷', { 'text-anchor': 'middle', 'font-size': 12, fill: C.muted });
    PTS.forEach((p, k) => {
      const has = t.mod(p), cat = t.cat(p);
      if (p.dots) {
        txt(sp, p.x, Y + 6, '…', { 'text-anchor': 'middle', 'font-size': 20, fill: has ? C.true : C.muted });
        return;
      }
      if (has && cat) el('circle', { cx: p.x, cy: Y, r: 15, fill: 'none', stroke: C.gold, 'stroke-width': 3 }, sp);
      el('circle', { cx: p.x, cy: Y, r: 9, fill: has ? C.true : '#fff', stroke: has ? C.true : '#9aa0aa', 'stroke-width': 2 }, sp);
      txt(sp, p.x, Y + 38, p.l, { 'text-anchor': 'middle', 'font-size': 14, 'font-weight': 700 });
    });
    el('circle', { cx: 30, cy: 124, r: 6, fill: C.true }, sp);
    txt(sp, 42, 128, 'has a model · 有模型', { 'font-size': 12 });
    el('circle', { cx: 230, cy: 124, r: 8, fill: 'none', stroke: C.gold, 'stroke-width': 3 }, sp);
    txt(sp, 244, 128, 'unique up to ≅ (categorical) · 同构意义下唯一（范畴）', { 'font-size': 12 });
    $('spMsg').innerHTML = bi(t.ten, t.tzh);
  }
  TH.forEach((t, i) => {
    const b = document.createElement('button');
    b.className = 'btn small' + (i === th ? ' sel' : '');
    b.innerHTML = bil(t.en, t.zh);
    b.addEventListener('click', () => { th = i; $('spBtns').querySelectorAll('button').forEach((x, k) => x.classList.toggle('sel', k === i)); drawSp(); });
    $('spBtns').appendChild(b);
  });
  drawSp();
})();

/* ================= §9 back-and-forth ================= */
const Frac = {
  cmp: (x, y) => x[0] * y[1] - y[0] * x[1],
  str: x => `${x[0]}/${x[1]}`,
  val: x => x[0] / x[1],
};
// Back-and-forth engine over two enumerations.
function BackForth(A, B) {
  const pairs = []; // {a, b, kind}
  const usedA = new Set(), usedB = new Set();
  const K = Frac.str;
  function partner(x, fromA) {
    // find bounds among existing pairs
    let lo = null, hi = null;
    pairs.forEach(p => {
      const s = fromA ? p.a : p.b, t = fromA ? p.b : p.a;
      if (Frac.cmp(s, x) < 0 && (!lo || Frac.cmp(s, lo.s) > 0)) lo = { s, t };
      if (Frac.cmp(s, x) > 0 && (!hi || Frac.cmp(s, hi.s) < 0)) hi = { s, t };
    });
    const list = fromA ? B : A, used = fromA ? usedB : usedA;
    const y = list.find(y => !used.has(K(y)) && (!lo || Frac.cmp(y, lo.t) > 0) && (!hi || Frac.cmp(y, hi.t) < 0));
    return { y, lo, hi };
  }
  function step() {
    const forth = pairs.length % 2 === 0;
    if (forth) {
      const a = A.find(a => !usedA.has(K(a)));
      const { y: b, lo, hi } = partner(a, true);
      pairs.push({ a, b, kind: 'forth', lo: lo && lo.t, hi: hi && hi.t });
    } else {
      const b = B.find(b => !usedB.has(K(b)));
      const { y: a, lo, hi } = partner(b, false);
      pairs.push({ a, b, kind: 'back', lo: lo && lo.t, hi: hi && hi.t });
    }
    const p = pairs[pairs.length - 1];
    usedA.add(K(p.a)); usedB.add(K(p.b));
    return p;
  }
  return { pairs, step, usedA, usedB };
}
const ENUM_A = (() => { const out = []; for (let q = 2; q <= 60; q++) for (let p = 1; p < q; p++) if (gcd(p, q) === 1) out.push([p, q]); return out; })();
const ENUM_B = (() => { const out = []; for (let k = 1; k <= 14; k++) for (let p = 1; p < (1 << k); p += 2) out.push([p, 1 << k]); return out; })();
(function backforth() {
  const svg = $('bfSvg');
  const X = v => 50 + v * 800, YA = 60, YB = 180;
  let bf, timer = null;
  function draw() {
    svg.innerHTML = '';
    [[YA, 'A = ℚ ∩ (0,1)', ENUM_A], [YB, 'B = dyadic rationals in (0,1) · 二进有理数', ENUM_B]].forEach(([y, lab, E]) => {
      el('line', { x1: 50, y1: y, x2: 850, y2: y, stroke: C.ink, 'stroke-width': 2 }, svg);
      [0, 1].forEach(v => { el('circle', { cx: X(v), cy: y, r: 4, fill: '#fff', stroke: C.ink }, svg); });
      E.slice(0, 120).forEach(f => el('line', { x1: X(Frac.val(f)), y1: y - 4, x2: X(Frac.val(f)), y2: y + 4, stroke: '#c9c4b6' }, svg));
      txt(svg, 50, y === YA ? y - 34 : y + 46, lab, { 'font-size': 13, 'font-weight': 700, fill: y === YA ? C.accent : C.meta });
    });
    bf.pairs.forEach((p, i) => {
      const last = i === bf.pairs.length - 1;
      const xa = X(Frac.val(p.a)), xb = X(Frac.val(p.b));
      const col = p.kind === 'forth' ? C.accent : C.meta;
      el('line', { x1: xa, y1: YA, x2: xb, y2: YB, stroke: col, 'stroke-width': last ? 3 : 1.4, opacity: last ? 1 : 0.55, class: last ? 'fadein' : '' }, svg);
      el('circle', { cx: xa, cy: YA, r: last ? 6 : 3.5, fill: col }, svg);
      el('circle', { cx: xb, cy: YB, r: last ? 6 : 3.5, fill: col }, svg);
      if (last) {
        txt(svg, xa, YA - 12, Frac.str(p.a), { 'text-anchor': 'middle', 'font-size': 13, 'font-weight': 800, fill: col });
        txt(svg, xb, YB + 22, Frac.str(p.b), { 'text-anchor': 'middle', 'font-size': 13, 'font-weight': 800, fill: col });
        if (p.lo || p.hi) {
          const l = p.lo ? X(Frac.val(p.lo)) : 50, h = p.hi ? X(Frac.val(p.hi)) : 850;
          const yy = p.kind === 'forth' ? YB : YA;
          el('rect', { x: l, y: yy - 10, width: Math.max(2, h - l), height: 20, fill: C.gold, opacity: 0.18, class: 'fadein' }, svg);
        }
      }
    });
    txt(svg, 860, 125, `${bf.pairs.length}`, { 'text-anchor': 'end', 'font-size': 13, 'font-weight': 700, fill: C.muted });
    txt(svg, 860, 140, 'pairs · 对', { 'text-anchor': 'end', 'font-size': 11, fill: C.muted });
    // queues
    const q = (E, used, nextKind) => {
      const nextIdx = E.findIndex(f => !used.has(Frac.str(f)));
      return E.slice(0, 22).map((f, i) => `<span class="qchip${used.has(Frac.str(f)) ? ' used' : ''}${i === nextIdx && nextKind ? ' next' : ''}">${Frac.str(f)}</span>`).join('') + ' …';
    };
    const forthNext = bf.pairs.length % 2 === 0;
    $('bfQA').innerHTML = q(ENUM_A, bf.usedA, forthNext);
    $('bfQB').innerHTML = q(ENUM_B, bf.usedB, !forthNext);
  }
  function log(p, n) {
    const d = document.createElement('div');
    const gap = `(${p.lo ? Frac.str(p.lo) : (p.kind === 'forth' ? '0' : '0')}, ${p.hi ? Frac.str(p.hi) : '1'})`;
    d.innerHTML = p.kind === 'forth'
      ? `${n}. <b style="color:${C.accent}">${bil('forth', '去')}</b> a = ${Frac.str(p.a)} → ${bil('first unused b in gap', '空隙中第一个未用的 b')} ${gap}: <b>${Frac.str(p.b)}</b>`
      : `${n}. <b style="color:${C.meta}">${bil('back', '回')}</b> b = ${Frac.str(p.b)} → ${bil('first unused a in gap', '空隙中第一个未用的 a')} ${gap}: <b>${Frac.str(p.a)}</b>`;
    $('bfLog').prepend(d);
  }
  function step() {
    if (bf.pairs.length >= 80) { stop(); return; }
    const p = bf.step();
    log(p, bf.pairs.length);
    draw();
  }
  function stop() { if (timer) clearInterval(timer); timer = null; }
  function reset() { stop(); bf = BackForth(ENUM_A, ENUM_B); $('bfLog').innerHTML = `<span class="muted">${bil('Step log appears here (newest first).', '每一步的记录显示在这里（最新的在上）。')}</span>`; draw(); }
  $('bfStep').addEventListener('click', step);
  $('bf10').addEventListener('click', () => { for (let i = 0; i < 10; i++) step(); });
  $('bfPlay').addEventListener('click', () => { if (timer) stop(); else timer = setInterval(step, 750); });
  $('bfReset').addEventListener('click', reset);
  reset();
  stepper('bfSteps', 'bfNext', 'bfAllP');
})();

/* ================= E1 compactness T/F ================= */
quizRows($('e1List'), [
  { s: bil('(a) Some first-order sentence is true in exactly the finite structures.', '(a) 存在一个一阶语句，恰好在有限结构中为真。'), ans: 1,
    en: 'False. Its models would have arbitrarily large finite size, hence (§2) an infinite model too.', zh: '错。它的模型有任意大的有限规模，由 §2 必有无穷模型。' },
  { s: bil('(b) The connected graphs (language {E}) are exactly the models of some set of sentences.', '(b) 连通图（语言 {E}）恰好是某个语句集的全部模型。'), ans: 1,
    en: 'False. Suppose T axiomatizes connectedness. Add constants a, b and, for each n, δₙ = “no path of length ≤ n from a to b”. Any finite part is satisfied by a long enough path graph with a, b at its ends, so by compactness some model of T has a, b with no path at all, which means it is not connected.',
    zh: '错。设 T 公理化连通性。加常元 a、b，并对每个 n 加 δₙ =“a 到 b 之间没有长度 ≤ n 的路”。任一有限部分都能被一条足够长的路（a、b 在两端）满足，于是由紧致性，T 有一个模型，其中 a、b 之间根本没有路，即它不连通。' },
  { s: bil('(c) If T has a model with at least n elements for every n, then T has an infinite model.', '(c) 若对每个 n，T 都有至少 n 个元素的模型，则 T 有无穷模型。'), ans: 0,
    en: 'True. T ∪ {λₙ : n ≥ 1} is finitely satisfiable.', zh: '对。T ∪ {λₙ : n ≥ 1} 是有限可满足的。' },
  { s: bil('(d) The torsion groups (every element has finite order) are first-order axiomatizable.', '(d) 挠群（每个元素都有有限阶）可以一阶公理化。'), ans: 1,
    en: 'False. Add a constant c and sentences cⁿ ≠ e for all n ≥ 1. Finite parts are satisfied in a cyclic group ℤ/m with m large and c a generator; compactness gives a “torsion group” with an element of infinite order.',
    zh: '错。加常元 c 和语句 cⁿ ≠ e（n ≥ 1）。任一有限部分都可在 m 足够大的循环群 ℤ/m 中取 c 为生成元来满足；紧致性给出一个“挠群”，却含有无穷阶元素。' },
  { s: bil('(e) Fields of characteristic 0 are axiomatized by an infinite set of sentences but by no single sentence.', '(e) 特征 0 的域能用无穷个语句公理化，但不能用单个语句公理化。'), ans: 0,
    en: 'True. Field axioms + {p·1 ≠ 0 : p prime} works. If a single σ did, then σ would follow from finitely many of these (compactness), so σ would hold in fields of large prime characteristic, which are not of characteristic 0.',
    zh: '对。域公理加上 {p·1 ≠ 0 : p 为素数} 即可。若单个 σ 就能公理化，由紧致性 σ 可由其中有限多条推出，于是 σ 在特征为大素数的域中也成立，而这些域的特征不是 0。' },
], [bil('True', '对'), bil('False', '错')], 'L5E1');

/* ================= E2 elementary or not ================= */
quizRows($('e2List'), [
  { s: '(a) &nbsp; <span class="m">(ℚ,<) ⊆ (ℝ,<)</span>', ans: 0, en: 'Elementary: automorphisms of ℝ fixing finitely many rationals move any witness to a rational (§6).', zh: '是：固定有限个有理数的 ℝ 的自同构可以把任何见证移到有理数上（见 §6）。', hen: 'Try the Tarski–Vaught test with an automorphism of ℝ.', hzh: '试试用 ℝ 的自同构做塔斯基–沃特判别。' },
  { s: '(b) &nbsp; <span class="m">([0,∞),<) ⊆ (ℝ,<)</span>', ans: 1, en: 'Not elementary: ∃y (y &lt; 0) is false in [0,∞), true in ℝ.', zh: '不是：∃y (y &lt; 0) 在 [0,∞) 中假，在 ℝ 中真。', hen: 'Look at the parameter 0.', hzh: '看看参数 0。' },
  { s: '(c) &nbsp; <span class="m">(3ℤ,+) ⊆ (ℤ,+)</span>', ans: 1, en: 'Not elementary: ∃y (y+y+y = 3) holds in ℤ (y = 1) but not in 3ℤ, even though 3ℤ ≅ ℤ.', zh: '不是：∃y (y+y+y = 3) 在 ℤ 中成立（y = 1），在 3ℤ 中不成立，尽管 3ℤ ≅ ℤ。', hen: 'Isomorphic is not enough. Try the parameter 3.', hzh: '同构还不够。试试参数 3。' },
  { s: '(d) &nbsp; <span class="m">((0,1),<) ⊆ (ℝ,<)</span>', ans: 0, en: 'Elementary: both are DLOs without endpoints, and the automorphism argument applies.', zh: '是：两者都是无端点稠密线序，自同构论证适用。', hen: 'Can you find a witness that must lie outside (0,1)?', hzh: '能找到一个必须落在 (0,1) 外的见证吗？' },
  { s: '(e) &nbsp; <span class="m">(ℚ,+) ⊆ (ℝ,+)</span>', ans: 0, en: 'Elementary. Both are nontrivial divisible torsion-free abelian groups, a theory with quantifier elimination, so every inclusion of models is elementary.', zh: '是。两者都是非平凡的可除无挠阿贝尔群，这个理论有量词消去，所以模型之间的任何包含都是初等的。', hen: 'Does any equation with rational parameters have a real solution but no rational one?', hzh: '有没有以有理数为参数、在 ℝ 中有解而在 ℚ 中无解的方程？' },
], ['M ≼ N', bil('⊆ but not ≼', '⊆ 但不是 ≼')], 'L5E2');

/* ================= E3 back-and-forth by hand ================= */
(function e3() {
  const svg = $('e3Svg');
  const X = v => 60 + v * 780, YA = 50, YB = 165;
  const base = [[[1, 4], [1, 8]], [[1, 3], [1, 4]], [[1, 2], [1, 2]], [[2, 3], [7, 8]]];
  const PARTS = [
    { kind: 'forth', given: [3, 5], cands: [[3, 16], [3, 8], [5, 8], [3, 4], [15, 16]] },
    { kind: 'back', given: [1, 16], cands: [[1, 7], [1, 5], [2, 7], [2, 5], [5, 6]] },
  ];
  let phase, pairs, solvedSelf, revealed = false; // revealed persists across Reset for this page session
  function valid(part, c) {
    const a = part.kind === 'forth' ? part.given : c, b = part.kind === 'forth' ? c : part.given;
    return pairs.every(([pa, pb]) => Math.sign(Frac.cmp(a, pa)) === Math.sign(Frac.cmp(b, pb)));
  }
  function prompt() {
    const p = PARTS[Math.min(phase, 1)];
    $('e3Prompt').innerHTML = phase > 1 ? bi('Both steps done. The partial isomorphism grew by two pairs, and no lines cross.', '两步都完成了。部分同构多了两对，配对线没有交叉。') :
      p.kind === 'forth'
        ? bi(`<b>(a) Forth.</b> The current finite partial isomorphism is drawn below. The next element of A is <b class="m">a = 3/5</b>. Click a gold point of B that can be its partner.`, `<b>(a) “去”.</b> 下图是当前的有限部分同构。A 的下一个元素是 <b class="m">a = 3/5</b>。点击 B 上一个可以作它配对的金色点。`)
        : bi(`<b>(b) Back.</b> Now the next element of B is <b class="m">b = 1/16</b>. Click a gold point of A that can be its partner.`, `<b>(b) “回”.</b> 现在 B 的下一个元素是 <b class="m">b = 1/16</b>。点击 A 上一个可以作它配对的金色点。`);
  }
  function draw(bad) {
    svg.innerHTML = '';
    el('line', { x1: 50, y1: YA, x2: 850, y2: YA, stroke: C.ink, 'stroke-width': 2 }, svg);
    el('line', { x1: 50, y1: YB, x2: 850, y2: YB, stroke: C.ink, 'stroke-width': 2 }, svg);
    txt(svg, 20, YA + 5, 'A', { 'font-size': 15, 'font-weight': 800, fill: C.accent });
    txt(svg, 20, YB + 5, 'B', { 'font-size': 15, 'font-weight': 800, fill: C.meta });
    pairs.forEach(([a, b], i) => {
      const nw = i >= base.length;
      el('line', { x1: X(Frac.val(a)), y1: YA, x2: X(Frac.val(b)), y2: YB, stroke: nw ? C.true : '#9aa0aa', 'stroke-width': nw ? 3 : 2 }, svg);
      el('circle', { cx: X(Frac.val(a)), cy: YA, r: 5, fill: nw ? C.true : C.ink }, svg);
      el('circle', { cx: X(Frac.val(b)), cy: YB, r: 5, fill: nw ? C.true : C.ink }, svg);
      txt(svg, X(Frac.val(a)), YA - 12, Frac.str(a), { 'text-anchor': 'middle', 'font-size': 12, 'font-weight': 700 });
      txt(svg, X(Frac.val(b)), YB + 24, Frac.str(b), { 'text-anchor': 'middle', 'font-size': 12, 'font-weight': 700 });
    });
    if (bad) {
      const [a, b] = bad;
      el('line', { x1: X(Frac.val(a)), y1: YA, x2: X(Frac.val(b)), y2: YB, stroke: C.false, 'stroke-width': 3, 'stroke-dasharray': '6 4' }, svg);
    }
    if (phase > 1) return;
    const part = PARTS[phase];
    const gy = part.kind === 'forth' ? YA : YB, cy = part.kind === 'forth' ? YB : YA;
    const g0 = el('g', { class: 'pop' }, svg);
    el('circle', { cx: X(Frac.val(part.given)), cy: gy, r: 8, fill: C.gold, stroke: C.ink, 'stroke-width': 2 }, g0);
    txt(g0, X(Frac.val(part.given)), part.kind === 'forth' ? gy - 14 : gy + 26, Frac.str(part.given) + ' ?', { 'text-anchor': 'middle', 'font-size': 13, 'font-weight': 800, fill: '#8a5a00' });
    part.cands.forEach(c => {
      const g = el('g', { class: 'clk' }, svg);
      el('circle', { cx: X(Frac.val(c)), cy: cy, r: 9, fill: C.goldSoft, stroke: C.gold, 'stroke-width': 2.5 }, g);
      txt(g, X(Frac.val(c)), part.kind === 'forth' ? cy - 16 : cy + 28, Frac.str(c), { 'text-anchor': 'middle', 'font-size': 12, fill: '#8a5a00', 'font-weight': 700 });
      g.addEventListener('click', () => choose(c));
    });
  }
  function choose(c) {
    const part = PARTS[phase];
    const pr = part.kind === 'forth' ? [part.given, c] : [c, part.given];
    if (valid(part, c)) {
      pairs.push(pr);
      solvedSelf[phase] = true;
      okBox($('e3Msg'), bi(`✓ ${Frac.str(pr[0])} ↦ ${Frac.str(pr[1])} keeps the map order-preserving: it sits in the same gap on both sides.`, `✓ ${Frac.str(pr[0])} ↦ ${Frac.str(pr[1])} 保持映射保序：它在两边落在同一个空隙里。`));
      phase++;
      if (phase > 1 && solvedSelf.every(Boolean) && !revealed) Progress.mark('L5E3');
      draw(); prompt();
    } else {
      const off = pairs.find(([pa, pb]) => Math.sign(Frac.cmp(pr[0], pa)) !== Math.sign(Frac.cmp(pr[1], pb)));
      okBox($('e3Msg'), bi(`✗ ${Frac.str(pr[0])} ↦ ${Frac.str(pr[1])} would cross the pair ${Frac.str(off[0])} ↦ ${Frac.str(off[1])} (red dashed line): order would not be preserved.`, `✗ ${Frac.str(pr[0])} ↦ ${Frac.str(pr[1])} 会与配对 ${Frac.str(off[0])} ↦ ${Frac.str(off[1])} 交叉（红色虚线）：不保序。`), 'bad');
      draw(pr);
    }
  }
  function reset() { phase = 0; pairs = base.map(p => p.slice()); solvedSelf = [false, false]; clearBox($('e3Msg')); draw(); prompt(); }
  $('e3Reset').addEventListener('click', reset);
  $('e3Show').addEventListener('click', () => {
    revealed = true;
    while (phase <= 1) { const part = PARTS[phase]; const c = part.cands.find(x => valid(part, x)); pairs.push(part.kind === 'forth' ? [part.given, c] : [c, part.given]); phase++; }
    draw(); prompt();
    okBox($('e3Msg'), bi('(a) 3/5 lies between 1/2 and 2/3, so its partner must lie between 1/2 and 7/8: 5/8 or 3/4 both work. (b) 1/16 is below 1/8, the image of 1/4, so its partner must be below 1/4: 1/7 or 1/5 both work.',
      '(a) 3/5 在 1/2 与 2/3 之间，所以它的配对必须在 1/2 与 7/8 之间：5/8 或 3/4 都行。(b) 1/16 小于 1/8（即 1/4 的像），所以它的配对必须小于 1/4：1/7 或 1/5 都行。'), 'info');
  });
  reset();
})();

/* ================= E4 LS cardinalities ================= */
(function e4() {
  const cards = [['7', false], ['ℵ₀', true], ['ℵ₁', true], ['2^ℵ₀', true], ['ℵ_ω', true]];
  const sel = new Set();
  const chips = cards.map(([l], i) => {
    const c = document.createElement('div');
    c.className = 'chip';
    c.textContent = l;
    c.addEventListener('click', () => { sel.has(i) ? sel.delete(i) : sel.add(i); c.classList.toggle('sel', sel.has(i)); c.classList.remove('ok', 'no'); });
    $('e4Cards').appendChild(c);
    return c;
  });
  const solved = { a: false, b: false };
  let revealed = false;
  const fin = () => !revealed && solved.a && solved.b && Progress.mark('L5E4');
  const ansA = bi('Exactly the infinite cardinals: ℵ₀, ℵ₁, 2^ℵ₀, ℵ_ω. ℕ is an infinite model, so upward and downward LS give a model of every infinite size. No finite model: T contains “0, 1, 1+1, … are distinct” for any finite number of numerals.',
    '恰好是所有无穷基数：ℵ₀、ℵ₁、2^ℵ₀、ℵ_ω。ℕ 是一个无穷模型，于是向上和向下 LS 定理给出每个无穷大小的模型。没有有限模型：T 包含“0、1、1+1、…（任意有限个数码）两两不同”。');
  $('e4Check').addEventListener('click', () => {
    let ok = true;
    cards.forEach(([, want], i) => {
      const got = sel.has(i);
      chips[i].classList.remove('ok', 'no');
      if (got !== want) { ok = false; if (got) chips[i].classList.add('no'); }
      else if (got) chips[i].classList.add('ok');
    });
    if (ok) { okBox($('e4aMsg'), '✓ ' + ansA); if (!revealed) solved.a = true; fin(); }
    else okBox($('e4aMsg'), bi('Not yet. Red = should not be selected; and maybe something is missing. Does T have a finite model? Which infinite sizes does LS reach?', '还不对。红色表示不该选；可能还漏选了。T 有有限模型吗？LS 定理能到达哪些无穷大小？'), 'bad');
  });
  const ch = choiceList($('e4b'), [
    { ok: true, en: 'Yes, by downward LS (take X = ∅; |L| + ℵ₀ = ℵ₀).', zh: '一定有，由向下 LS 定理（取 X = ∅；|L| + ℵ₀ = ℵ₀）。',
      why_en: 'Downward LS gives N ≼ M with |N| ≤ ℵ₀; N is infinite because M is (λₙ transfers), so |N| = ℵ₀.', why_zh: '向下 LS 定理给出 N ≼ M 且 |N| ≤ ℵ₀；M 无穷，λₙ 都传递到 N，所以 N 也无穷，|N| = ℵ₀。' },
    { ok: false, en: 'Not necessarily: a model of size ℵ₅ might have no countable elementary substructure.', zh: '不一定：大小为 ℵ₅ 的模型可能没有可数初等子结构。',
      why_en: 'Downward LS says exactly that it has one.', why_zh: '向下 LS 定理恰恰保证它有。' },
    { ok: false, en: 'Only if T is complete.', zh: '只有当 T 是完全理论时才有。',
      why_en: 'Completeness of T plays no role in downward LS.', why_zh: '向下 LS 定理与 T 是否完全无关。' },
  ], $('e4bMsg'), () => { solved.b = true; fin(); });
  $('e4Show').addEventListener('click', () => {
    revealed = true;
    cards.forEach(([, want], i) => { chips[i].classList.toggle('sel', want); chips[i].classList.remove('no'); chips[i].classList.toggle('ok', want); });
    okBox($('e4aMsg'), ansA, 'info');
    ch.reveal();
  });
})();

/* ================= E5 nonstandard model T/F ================= */
quizRows($('e5List'), [
  { s: bil('(a) c has an immediate predecessor c − 1.', '(a) c 有直接前驱 c − 1。'), ans: 0,
    en: 'True. Th(ℕ) contains ∀x (x ≠ 0 → ∃y (y + 1 = x)), and M satisfies it. And c − 1 is nonstandard too.', zh: '对。Th(ℕ) 含有 ∀x (x ≠ 0 → ∃y (y + 1 = x))，M 满足它。而且 c − 1 也是非标准的。' },
  { s: bil('(b) There is a least nonstandard element.', '(b) 存在最小的非标准元素。'), ans: 1,
    en: 'False. If c is nonstandard, so is c − 1 (if c − 1 = n then c = n + 1 would be standard).', zh: '错。若 c 非标准，则 c − 1 也非标准（若 c − 1 = n，则 c = n + 1 是标准的）。' },
  { s: bil('(c) c and c + c lie in the same ℤ-block.', '(c) c 与 c + c 在同一个 ℤ 块里。'), ans: 1,
    en: 'False. They differ by c, which is nonstandard, not by a standard n.', zh: '错。它们相差 c，c 是非标准的，而不是某个标准的 n。' },
  { s: bil('(d) Some formula φ(x) (possibly with parameters) defines the set of standard elements in M.', '(d) 有某个公式 φ(x)（可带参数）在 M 中定义了标准元素集。'), ans: 1,
    en: 'False. Such a set contains 0 and is closed under x ↦ x+1, so by the induction instance for φ (true in ℕ, hence in M) it would be all of M, but c is not in it.', zh: '错。这个集合含 0 且对 x ↦ x+1 封闭，由关于 φ 的归纳法实例（在 ℕ 中为真，因而在 M 中为真），它将是整个 M，可 c 不在其中。' },
  { s: bil('(e) Either c or c + 1 is even (of the form y + y).', '(e) c 与 c + 1 中必有一个是偶数（形如 y + y）。'), ans: 0,
    en: 'True. ∀x ∃y (x = y + y ∨ x = y + y + 1) is in Th(ℕ).', zh: '对。∀x ∃y (x = y + y ∨ x = y + y + 1) 属于 Th(ℕ)。' },
], [bil('True', '对'), bil('False', '错')], 'L5E5');

/* ================= E6 Skolem's paradox ================= */
(function e6() {
  const ch = choiceList($('e6Choices'), [
    { ok: false, en: 'It shows ZFC is inconsistent.', zh: '这说明 ZFC 不一致。',
      why_en: 'No: nothing contradictory is derived inside ZFC; the two claims live at different levels.', why_zh: '不对：ZFC 内部并没有推出矛盾；两个断言处在不同的层次。' },
    { ok: true, en: 'The enumeration of ℝ<sup>M</sup> exists in V but is not an element of M; “uncountable” in M means “no surjection from ω that belongs to M”.', zh: 'ℝ<sup>M</sup> 的枚举在 V 中存在，但不是 M 的元素；M 中的“不可数”指“M 中不存在从 ω 出发的满射”。',
      why_en: 'Exactly. Countability is not absolute between M and V.', why_zh: '正是如此。可数性在 M 与 V 之间不是绝对的。' },
    { ok: false, en: 'Downward LS does not apply to ZFC because ZFC has infinitely many axioms.', zh: '向下 LS 定理不适用于 ZFC，因为 ZFC 有无穷多条公理。',
      why_en: 'LS applies to any theory in a countable language, however many axioms it has.', why_zh: 'LS 定理适用于可数语言中的任何理论，不论公理有多少条。' },
    { ok: false, en: 'ℝ<sup>M</sup> is really uncountable; M only looks countable from inside.', zh: 'ℝ<sup>M</sup> 其实不可数；M 只是从内部看起来可数。',
      why_en: 'Backwards: from outside, ℝ<sup>M</sup> is countable; it is M that believes it is uncountable.', why_zh: '说反了：从外部看 ℝ<sup>M</sup> 是可数的；认为它不可数的是 M 自己。' },
  ], $('e6Msg'), () => Progress.mark('L5E6'));
  $('e6Show').addEventListener('click', () => ch.reveal());
})();
