// Lesson 11 interactions: computability and the halting problem.

/*CORE-BEGIN*/
// Pure Turing-machine core (no DOM access; unit-tested with node).
// Convention: the machine halts when no rule matches (state, symbol). Every applied rule is one step,
// including the rule that enters the halt state.
const TMCore = (() => {
  const BLANK = '_';
  const MOVES = { L: -1, R: 1, N: 0 };
  function parse(text) {
    const rules = {}, order = [], errors = [];
    let start = null;
    String(text).split('\n').forEach((raw, ln) => {
      const line = raw.replace(/#.*/, '').trim();
      if (!line) return;
      const sm = line.match(/^start\s*[:=]\s*(\S+)$/i);
      if (sm) { start = sm[1]; return; }
      const parts = line.replace(/->|→/g, ' ').split(/[\s,]+/).filter(Boolean);
      if (parts.length !== 5) { errors.push({ line: ln + 1, kind: 'arity' }); return; }
      const [q, r, n, w] = parts;
      let m = parts[4].toUpperCase();
      if (m === 'S') m = 'N';
      if (!(m in MOVES)) { errors.push({ line: ln + 1, kind: 'move' }); return; }
      if ([...r].length !== 1 || [...w].length !== 1) { errors.push({ line: ln + 1, kind: 'symbol' }); return; }
      rules[q] = rules[q] || {};
      if (rules[q][r]) { errors.push({ line: ln + 1, kind: 'dup' }); return; }
      rules[q][r] = { w, m, n };
      order.push({ q, r, w, m, n, line: ln + 1 });
    });
    if (!start && order.length) start = order[0].q;
    const states = [];
    const addS = s => { if (s != null && !states.includes(s)) states.push(s); };
    addS(start);
    order.forEach(o => { addS(o.q); addS(o.n); });
    const symbols = [BLANK];
    order.forEach(o => [o.r, o.w].forEach(s => { if (!symbols.includes(s)) symbols.push(s); }));
    return { rules, order, start, states, symbols, errors };
  }
  const read = (cfg, i = cfg.head) => cfg.tape.has(i) ? cfg.tape.get(i) : BLANK;
  const ruleFor = (M, cfg) => (M.rules[cfg.state] || {})[read(cfg)] || null;
  function init(M, input) {
    const tape = new Map();
    [...(input || '')].forEach((c, i) => { if (c !== BLANK && c !== ' ') tape.set(i, c); });
    const cfg = { tape, head: 0, state: M.start, steps: 0, halted: false, last: null };
    cfg.halted = !ruleFor(M, cfg);
    return cfg;
  }
  function step(M, cfg) {
    if (cfg.halted) return null;
    const sym = read(cfg), r = ruleFor(M, cfg), pos = cfg.head, from = cfg.state;
    if (r.w === BLANK) cfg.tape.delete(pos); else cfg.tape.set(pos, r.w);
    cfg.head += MOVES[r.m];
    cfg.state = r.n;
    cfg.steps++;
    cfg.last = { q: from, r: sym, w: r.w, m: r.m, n: r.n, pos };
    cfg.halted = !ruleFor(M, cfg);
    return cfg.last;
  }
  function run(M, input, max = 10000) {
    const cfg = init(M, input);
    while (!cfg.halted && cfg.steps < max) step(M, cfg);
    return cfg;
  }
  function content(cfg) {
    if (!cfg.tape.size) return '';
    const ks = [...cfg.tape.keys()];
    const lo = Math.min(...ks), hi = Math.max(...ks);
    let s = '';
    for (let i = lo; i <= hi; i++) s += read(cfg, i);
    return s;
  }
  const ones = cfg => [...cfg.tape.values()].filter(c => c === '1').length;
  const verdict = st => /^acc/i.test(st) ? 'acc' : /^rej/i.test(st) ? 'rej' : 'halt';
  // Code of a machine: rule (q_i, s_j) -> (q_k, s_l, m) becomes 0^i 1 0^j 1 0^k 1 0^l 1 0^m; rules joined by 11.
  function encode(M) {
    const mv = { L: 1, R: 2, N: 3 };
    const blocks = M.order.map(o => {
      const nums = [M.states.indexOf(o.q) + 1, M.symbols.indexOf(o.r) + 1, M.states.indexOf(o.n) + 1, M.symbols.indexOf(o.w) + 1, mv[o.m]];
      return { rule: o, nums, bits: nums.map(k => '0'.repeat(k)).join('1') };
    });
    return { blocks, bits: blocks.map(b => b.bits).join('11') };
  }
  function decode(bits) {
    return bits.split('11').map(b => b.split('1').map(z => z.length));
  }
  return { BLANK, parse, init, step, run, content, ones, verdict, encode, decode, read, ruleFor };
})();

const PRESETS = {
  uinc: { en: 'Unary +1', zh: '一进制加一', input: '111',
    den: 'Input n in unary (n ones). Walk right to the first blank, write one more 1.', dzh: '输入为一进制的 n（n 个 1）。向右走到第一个空格，再补写一个 1。',
    text: `# unary increment: 1^n -> 1^(n+1)
q0 1 -> q0 1 R
q0 _ -> H 1 N` },
  binc: { en: 'Binary +1', zh: '二进制加一', input: '1011',
    den: 'Go to the right end, then add 1 with carries moving left: 1 becomes 0 and the carry moves on; the first 0 (or blank) becomes 1.', dzh: '先走到最右端，再向左做进位加法：遇 1 写 0 继续进位，遇到第一个 0（或空格）写 1 结束。',
    text: `# binary increment
q0 0 -> q0 0 R
q0 1 -> q0 1 R
q0 _ -> q1 _ L
q1 1 -> q1 0 L
q1 0 -> H 1 N
q1 _ -> H 1 N` },
  uadd: { en: 'Unary addition', zh: '一进制加法', input: '11+111',
    den: 'Input 1^m + 1^n. Replace + by 1, then erase the last 1: the result is 1^(m+n).', dzh: '输入 1^m + 1^n。把 + 改成 1，再擦掉最后一个 1，结果就是 1^(m+n)。',
    text: `# unary addition: 1^m + 1^n -> 1^(m+n)
q0 1 -> q0 1 R
q0 + -> q1 1 R
q1 1 -> q1 1 R
q1 _ -> q2 _ L
q2 1 -> H _ N` },
  pal: { en: 'Palindrome', zh: '回文判定', input: 'abba',
    den: 'Erase the first letter and remember it in the state (qa / qb), run to the right end, compare it with the last letter, erase that, and come back. Ends in acc or rej.',
    dzh: '擦掉第一个字母并用状态记住它（qa / qb），跑到最右端与最后一个字母比较，擦掉后返回。最终停在 acc 或 rej。',
    pos: { q0: [50, 190], qa: [160, 65, -2.4], ca: [330, 65], qb: [160, 310, 2.4], cb: [330, 310], back: [245, 190, Math.PI / 2], acc: [485, 60], rej: [485, 190] },
    text: `# palindromes over {a, b}
q0 a -> qa _ R
q0 b -> qb _ R
q0 _ -> acc _ N
qa a -> qa a R
qa b -> qa b R
qa _ -> ca _ L
ca a -> back _ L
ca b -> rej b N
ca _ -> acc _ N
qb a -> qb a R
qb b -> qb b R
qb _ -> cb _ L
cb b -> back _ L
cb a -> rej a N
cb _ -> acc _ N
back a -> back a L
back b -> back b L
back _ -> q0 _ R` },
  bb2: { en: 'Busy beaver (2)', zh: '忙碌海狸（2 状态）', input: '',
    den: 'Start on a blank tape. Among all halting 2-state machines over {_, 1}, this one leaves the most 1s: Σ(2) = 4, after 6 steps.',
    dzh: '从空白带出发。在字母表 {_, 1} 上所有会停机的 2 状态机器中，它留下的 1 最多：Σ(2) = 4，共 6 步。',
    text: `# 2-state busy beaver (_ plays the role of 0)
A _ -> B 1 R
A 1 -> B 1 L
B _ -> A 1 L
B 1 -> H 1 R` },
  bb3: { en: 'Busy beaver (3)', zh: '忙碌海狸（3 状态）', input: '',
    den: 'The 3-state champion: Σ(3) = 6 ones, here after 14 steps. (The longest-running halting 3-state machine takes S(3) = 21 steps but leaves only 5 ones.)',
    dzh: '3 状态冠军机：Σ(3) = 6 个 1，这台用了 14 步。（运行最久的 3 状态停机机器要走 S(3) = 21 步，但只留下 5 个 1。）',
    text: `# 3-state busy beaver (Sigma champion)
A _ -> B 1 R
A 1 -> H 1 R
B _ -> C _ R
B 1 -> B 1 R
C _ -> C 1 L
C 1 -> A 1 L` },
};
/*CORE-END*/

if (typeof document !== 'undefined') {
Lang.init();
Progress.paint();

const $ = id => document.getElementById(id);
const okBox = (box, html, kind = 'ok') => { box.className = 'msg ' + kind; box.innerHTML = html; };
const clearBox = box => { box.className = 'msg'; box.innerHTML = ''; };
const SUBD = '₀₁₂₃₄₅₆₇₈₉', SUPD = '⁰¹²³⁴⁵⁶⁷⁸⁹';
const sub = n => String(n).split('').map(d => SUBD[d]).join('');
const sup = n => String(n).split('').map(d => SUPD[d]).join('');
const txt = (parent, attrs, s) => { const t = el('text', attrs, parent); t.textContent = s; return t; };
function stepper(stepsSel, nextBtn, allBtn) {
  const steps = [...document.querySelectorAll(stepsSel + ' .step')];
  let k = 0;
  $(nextBtn).addEventListener('click', () => { if (k < steps.length) steps[k++].classList.add('on'); if (k === steps.length) $(nextBtn).disabled = true; });
  $(allBtn).addEventListener('click', () => { steps.forEach(s => s.classList.add('on')); k = steps.length; $(nextBtn).disabled = true; });
}
const ERR = {
  arity: ['needs exactly 5 parts: state read -> next write move', '需要恰好 5 部分：状态 读入 -> 新状态 写入 移动'],
  move: ['move must be L, R or N', '移动只能是 L、R 或 N'],
  symbol: ['symbols must be single characters', '符号必须是单个字符'],
  dup: ['a second rule for the same (state, symbol): the machine must be deterministic', '同一个（状态, 符号）出现了第二条规则：机器必须是确定型的'],
};
const errHtml = errs => errs.map(e => bi(`Line ${e.line}: ${ERR[e.kind][0]}.`, `第 ${e.line} 行：${ERR[e.kind][1]}。`)).join('');

/* ================= tape view ================= */
function TapeView(svg, opts = {}) {
  const W = opts.w || 900, CW = opts.cw || 44, H = 92, Y = 24;
  svg.setAttribute('viewBox', `0 0 ${W} ${H}`);
  svg.setAttribute('width', W);
  svg.setAttribute('height', H);
  svg.innerHTML = '';
  const g = el('g', { class: 'cells' }, svg);
  const hd = el('g', {}, svg);
  el('path', { d: `M${W / 2 - 9},4 L${W / 2 + 9},4 L${W / 2},18 Z`, fill: '#ae3ec9' }, hd);
  el('rect', { x: W / 2 - CW / 2 + 1, y: Y - 1, width: CW - 2, height: CW + 2, rx: 6, fill: 'none', stroke: '#ae3ec9', 'stroke-width': 3 }, hd);
  const lab = txt(hd, { x: W / 2 + 16, y: 15, 'font-size': 13, fill: '#ae3ec9', 'font-weight': 700 }, '');
  function render(cfg) {
    g.innerHTML = '';
    const ks = [...cfg.tape.keys(), cfg.head];
    const span = Math.ceil(W / CW / 2) + 2;
    const lo = Math.min(...ks) - span, hi = Math.max(...ks) + span;
    for (let i = lo; i <= hi; i++) {
      const c = el('g', { class: 'cell' + (cfg.last && cfg.last.pos === i ? ' flash' : '') }, g);
      el('rect', { x: i * CW + 2, y: Y, width: CW - 4, height: CW, rx: 6 }, c);
      const s = TMCore.read(cfg, i);
      txt(c, { x: i * CW + CW / 2, y: Y + CW / 2, class: s === '_' ? 'blank' : '' }, s === '_' ? '_' : s);
      txt(g, { x: i * CW + CW / 2, y: Y + CW + 14, class: 'idx' }, i);
    }
    g.style.transform = `translateX(${W / 2 - CW / 2 - cfg.head * CW}px)`;
    lab.textContent = (opts.label || 'state · 状态: ') + cfg.state;
  }
  return { render };
}

/* ================= state diagram ================= */
let diagUid = 0;
function StateDiagram(svg, M, pos) {
  const W = 540, H = 380;
  svg.setAttribute('viewBox', `0 0 ${W} ${H}`);
  svg.setAttribute('width', W);
  svg.setAttribute('height', H);
  svg.innerHTML = '';
  const uid = ++diagUid;
  const defs = el('defs', {}, svg);
  [['a', '#9aa0aa'], ['h', '#3b5bdb']].forEach(([k, col]) => {
    const mk = el('marker', { id: `ar${k}${uid}`, viewBox: '0 0 10 10', refX: 9, refY: 5, markerWidth: 8, markerHeight: 8, orient: 'auto-start-reverse', markerUnits: 'userSpaceOnUse' }, defs);
    el('path', { d: 'M0,0 L10,5 L0,10 z', fill: col }, mk);
  });
  const R = 22, cx = W / 2, cy = H / 2;
  const n = M.states.length;
  const P = {};
  M.states.forEach((s, k) => {
    if (pos && pos[s]) { P[s] = pos[s]; return; }
    if (n === 1) { P[s] = [cx, cy]; return; }
    const a = -Math.PI + (k / n) * 2 * Math.PI;
    P[s] = [cx + (W / 2 - 140) * Math.cos(a), cy + (H / 2 - 80) * Math.sin(a)];
  });
  const groups = new Map();
  M.order.forEach(o => {
    const key = o.q + '\u0000' + o.n;
    if (!groups.has(key)) groups.set(key, []);
    groups.get(key).push(o);
  });
  const gE = el('g', {}, svg), gL = el('g', {}, svg), gN = el('g', {}, svg);
  const edges = {};
  groups.forEach((rs, key) => {
    const [a, b] = key.split('\u0000');
    const [ax, ay] = P[a], [bx, by] = P[b];
    const lines = rs.map(o => `${o.r}→${o.w},${o.m}`);
    let d, lx, ly, anchor = 'middle';
    if (a === b) {
      let th = Math.atan2(ay - cy, ax - cx);
      if (Math.hypot(ax - cx, ay - cy) < 5) th = -Math.PI / 2;
      if (P[a].length > 2) th = P[a][2];
      const pt = (ang, r) => [ax + r * Math.cos(ang), ay + r * Math.sin(ang)];
      const s0 = pt(th - 0.45, R), e0 = pt(th + 0.45, R + 2), c1 = pt(th - 0.75, 70), c2 = pt(th + 0.75, 70);
      d = `M${s0} C${c1} ${c2} ${e0}`;
      [lx, ly] = pt(th, 64);
      anchor = Math.cos(th) > 0.35 ? 'start' : Math.cos(th) < -0.35 ? 'end' : 'middle';
      if (anchor === 'middle') ly += Math.sin(th) > 0 ? 10 : -10 * lines.length;
    } else {
      const dx = bx - ax, dy = by - ay, L = Math.hypot(dx, dy);
      const nx = -dy / L, ny = dx / L;
      const off = groups.has(b + '\u0000' + a) ? 26 : 0;
      const mx = (ax + bx) / 2, my = (ay + by) / 2;
      const ccx = mx + nx * off * 2, ccy = my + ny * off * 2;
      const u = (x, y, tx, ty, r) => { const l = Math.hypot(tx - x, ty - y); return [x + (tx - x) / l * r, y + (ty - y) / l * r]; };
      const s0 = u(ax, ay, ccx, ccy, R), e0 = u(bx, by, ccx, ccy, R + 2);
      d = `M${s0} Q${ccx},${ccy} ${e0}`;
      lx = mx + nx * (off + 12);
      ly = my + ny * (off + 12);
      anchor = Math.abs(nx) > 0.5 ? (nx > 0 ? 'start' : 'end') : 'middle';
      if (anchor === 'middle' && ny < 0) ly -= 12 * (lines.length - 1);
    }
    const path = el('path', { d, class: 'edge', 'marker-end': `url(#ara${uid})` }, gE);
    const t = el('text', { x: lx, y: ly, class: 'elab', 'text-anchor': anchor }, gL);
    lines.forEach((s, i) => { const ts = el('tspan', { x: lx, dy: i ? 13 : 4 }, t); ts.textContent = s; });
    edges[key] = { path, t };
  });
  const nodes = {};
  M.states.forEach(s => {
    const halt = !M.rules[s];
    const v = TMCore.verdict(s);
    const g = el('g', { class: 'node' + (halt ? ' halt' : '') + (v !== 'halt' ? ' ' + v : ''), transform: `translate(${P[s][0]},${P[s][1]})` }, gN);
    el('circle', { r: R, class: 'inner' }, g);
    if (halt) el('circle', { r: R - 4, class: 'outer' }, g);
    txt(g, { 'font-size': s.length > 3 ? 11 : 14 }, s);
    const [nx0, ny0] = P[s];
    let th0 = Math.atan2(ny0 - cy, nx0 - cx);
    if (Math.hypot(nx0 - cx, ny0 - cy) < 5) th0 = -Math.PI / 2;
    const sa = th0 - Math.PI / 2;
    if (s === M.start) el('path', { d: `M${(R + 20) * Math.cos(sa)},${(R + 20) * Math.sin(sa)} L${(R + 2) * Math.cos(sa)},${(R + 2) * Math.sin(sa)}`, stroke: '#1f2430', 'stroke-width': 2, 'marker-end': `url(#ara${uid})` }, g);
    nodes[s] = g;
  });
  function highlight(cfg) {
    Object.values(nodes).forEach(g => g.classList.remove('cur'));
    Object.values(edges).forEach(e => { e.path.classList.remove('hot'); e.path.setAttribute('marker-end', `url(#ara${uid})`); e.t.classList.remove('hot'); });
    if (nodes[cfg.state]) nodes[cfg.state].classList.add('cur');
    if (cfg.last) {
      const e = edges[cfg.last.q + '\u0000' + cfg.last.n];
      if (e) { e.path.classList.add('hot'); e.path.setAttribute('marker-end', `url(#arh${uid})`); e.t.classList.add('hot'); }
    }
  }
  return { highlight };
}

/* ================= §1 simulator ================= */
(function simulator() {
  let M, cfg, tape, diag, timer = null, preset = 'uinc', pos = null;
  const speeds = [700, 380, 180, 70, 15];
  tape = TapeView($('tmTape'));
  function status() {
    const parts = [`<span>${bil('state', '状态')}: <b>${cfg.state}</b></span>`, `<span>${bil('steps', '步数')}: <b>${cfg.steps}</b></span>`,
      `<span>${bil('reading', '读到')}: <b>${TMCore.read(cfg)}</b></span>`];
    if (cfg.halted) {
      const v = TMCore.verdict(cfg.state);
      const out = TMCore.content(cfg);
      if (v === 'acc') parts.push(`<span class="halt">✓ ${bil('halted: ACCEPT', '停机：接受')}</span>`);
      else if (v === 'rej') parts.push(`<span class="rej">✗ ${bil('halted: REJECT', '停机：拒绝')}</span>`);
      else parts.push(`<span class="halt">■ ${bil('halted', '已停机')} · ${bil('tape', '带上')}: ${out || 'ε'}</span>`);
      if (preset.startsWith('bb')) parts.push(`<span class="halt">${bil('ones', '1 的个数')}: ${TMCore.ones(cfg)}</span>`);
    } else if (cfg.steps >= 5000) parts.push(`<span class="rej">${bil('5000 steps and still running: maybe it never halts', '已跑 5000 步仍未停机：也许永远不停')}</span>`);
    $('tmStatus').innerHTML = parts.join('');
  }
  function rulesTable() {
    const nx = cfg.halted ? null : { q: cfg.state, r: TMCore.read(cfg) };
    let h = `<table class="rules"><tr><th>${bi('state', '状态')}</th><th>${bi('read', '读')}</th><th>→</th><th>${bi('next', '新状态')}</th><th>${bi('write', '写')}</th><th>${bi('move', '移动')}</th></tr>`;
    M.order.forEach(o => {
      h += `<tr class="${nx && nx.q === o.q && nx.r === o.r ? 'next' : ''}"><td>${o.q}</td><td>${o.r}</td><td>→</td><td>${o.n}</td><td>${o.w}</td><td>${o.m}</td></tr>`;
    });
    $('tmRules').innerHTML = h + '</table>';
    const nr = $('tmRules').querySelector('tr.next');
    if (nr) $('tmRules').scrollTop = Math.max(0, nr.offsetTop - 90);
  }
  function render() { tape.render(cfg); diag.highlight(cfg); status(); rulesTable(); }
  function stop() { clearInterval(timer); timer = null; $('tmRun').innerHTML = bi('Run ▶', '运行 ▶'); }
  function reset() {
    stop();
    cfg = TMCore.init(M, $('tmInput').value.trim());
    render();
  }
  function load(text, p) {
    const m = TMCore.parse(text);
    if (m.errors.length || !m.order.length) {
      okBox($('tmErr'), m.order.length ? errHtml(m.errors) : bi('The table is empty.', '转移表是空的。'), 'bad');
      return false;
    }
    clearBox($('tmErr'));
    M = m;
    diag = StateDiagram($('tmDiagram'), M, p);
    reset();
    return true;
  }
  function choose(key) {
    preset = key;
    const P = PRESETS[key];
    document.querySelectorAll('#tmPresets button').forEach(b => b.classList.toggle('sel', b.dataset.k === key));
    $('tmText').value = P.text;
    $('tmInput').value = P.input;
    $('tmDesc').innerHTML = bi(P.den, P.dzh);
    pos = P.pos || null;
    load(P.text, pos);
  }
  Object.entries(PRESETS).forEach(([k, P]) => {
    const b = document.createElement('button');
    b.className = 'btn small';
    b.dataset.k = k;
    b.innerHTML = bil(P.en, P.zh);
    b.addEventListener('click', () => choose(k));
    $('tmPresets').appendChild(b);
  });
  function stepOnce() {
    if (cfg.halted || cfg.steps >= 5000) { stop(); return; }
    TMCore.step(M, cfg);
    render();
    if (cfg.halted) stop();
  }
  $('tmStep').addEventListener('click', () => { stop(); stepOnce(); });
  $('tmRun').addEventListener('click', () => {
    if (timer) { stop(); return; }
    if (cfg.halted) reset();
    $('tmRun').innerHTML = bi('Pause ❚❚', '暂停 ❚❚');
    timer = setInterval(stepOnce, speeds[+$('tmSpeed').value]);
  });
  $('tmSpeed').addEventListener('input', () => { if (timer) { clearInterval(timer); timer = setInterval(stepOnce, speeds[+$('tmSpeed').value]); } });
  $('tmReset').addEventListener('click', reset);
  $('tmInput').addEventListener('change', reset);
  $('tmApply').addEventListener('click', () => {
    preset = 'custom';
    document.querySelectorAll('#tmPresets button').forEach(b => b.classList.remove('sel'));
    const usePos = pos && TMCore.parse($('tmText').value).states.every(s => pos[s]) ? pos : null;
    if (load($('tmText').value, usePos)) $('tmDesc').innerHTML = bi('Your own machine is loaded. Press Step or Run.', '已载入你自己的机器。按“单步”或“运行”。');
  });
  choose('uinc');
})();

/* ================= §2 primitive recursion ================= */
const PR = (() => {
  const Z = k => ({ t: 'Z', k }), S = { t: 'S' }, P = (n, i) => ({ t: 'P', n, i });
  const C = (f, gs) => ({ t: 'C', f, gs }), R = (g, h) => ({ t: 'R', g, h }), ref = name => ({ t: 'ref', name });
  const DEFS = {
    add: { ar: 2, term: R(P(1, 1), C(S, [P(3, 3)])), g: x => `${x}`, gx: 'x', h: (x, y, r) => `S(${r})`, hx: 'S(r)', f: (x, y) => x + y, max: [5, 5] },
    mult: { ar: 2, term: R(Z(1), C(ref('add'), [P(3, 3), P(3, 1)])), g: () => '0', gx: '0', h: (x, y, r) => `add(${r}, ${x})`, hx: 'add(r, x)', f: (x, y) => x * y, max: [5, 5] },
    exp: { ar: 2, term: R(C(S, [Z(1)]), C(ref('mult'), [P(3, 3), P(3, 1)])), g: () => 'S(0)', gx: 'S(Z(x)) = 1', h: (x, y, r) => `mult(${r}, ${x})`, hx: 'mult(r, x)', f: (x, y) => x ** y, max: [5, 5] },
    pred: { ar: 1, term: R(Z(0), P(2, 1)), g: () => '0', gx: '0', h: (x, y) => `${y}`, hx: 'y', f: (x, y) => Math.max(0, y - 1), max: [5, 5] },
    monus: { ar: 2, term: R(P(1, 1), C(ref('pred'), [P(3, 3)])), g: x => `${x}`, gx: 'x', h: (x, y, r) => `pred(${r})`, hx: 'pred(r)', f: (x, y) => Math.max(0, x - y), max: [5, 5] },
    fact: { ar: 1, term: R(C(S, [Z(0)]), C(ref('mult'), [C(S, [P(2, 1)]), P(2, 2)])), g: () => '1', gx: 'S(Z) = 1', h: (x, y, r) => `mult(S(${y}), ${r})`, hx: 'mult(S(y), r)', f: (x, y) => { let p = 1; for (let i = 2; i <= y; i++) p *= i; return p; }, max: [5, 5] },
  };
  function ev(t, args, cnt) {
    switch (t.t) {
      case 'Z': return 0;
      case 'S': cnt.s++; return args[0] + 1;
      case 'P': return args[t.i - 1];
      case 'C': return ev(t.f, t.gs.map(g => ev(g, args, cnt)), cnt);
      case 'R': {
        const xs = args.slice(0, -1), y = args[args.length - 1];
        let r = ev(t.g, xs, cnt);
        for (let k = 0; k < y; k++) r = ev(t.h, [...xs, k, r], cnt);
        return r;
      }
      case 'ref': return ev(DEFS[t.name].term, args, cnt);
    }
  }
  return { DEFS, ev };
})();

(function primRec() {
  const NAMES = { add: ['add(x, y) = x + y', 'add(x, y) = x + y'], mult: ['mult(x, y) = x · y', 'mult(x, y) = x · y'], exp: ['exp(x, y) = xʸ', 'exp(x, y) = xʸ'],
    pred: ['pred(y) = y ∸ 1', 'pred(y) = y ∸ 1'], monus: ['x ∸ y (cut-off subtraction)', 'x ∸ y（截断减法）'], fact: ['fact(y) = y!', 'fact(y) = y!'] };
  let cur = 'add';
  const expanded = new Set();
  Object.keys(PR.DEFS).forEach(k => {
    const b = document.createElement('button');
    b.className = 'btn small';
    b.dataset.k = k;
    b.innerHTML = `<span class="m">${NAMES[k][0]}</span>`;
    b.addEventListener('click', () => { cur = k; expanded.clear(); draw(); ladder(); });
    $('prPick').appendChild(b);
  });
  function info(t, ar) {
    switch (t.t) {
      case 'Z': return bi(`<b>Z</b>: the constant 0 (here with ${ar} argument${ar === 1 ? '' : 's'}).`, `<b>Z</b>：常数 0（此处有 ${ar} 个自变量）。`);
      case 'S': return bi('<b>S</b>: successor, x ↦ x + 1. The only block that ever makes a number bigger.', '<b>S</b>：后继，x ↦ x + 1。唯一能让数变大的积木。');
      case 'P': return bi(`<b>P${sup(t.n)}${sub(t.i)}</b>: pick argument number ${t.i} out of ${t.n}.${t.n === 3 ? (t.i === 3 ? ' Inside a recursion step the arguments are (x, y, r), so this is r, the previous value.' : t.i === 1 ? ' Inside a recursion step this is x.' : ' Inside a recursion step this is the counter y.') : ''}`,
        `<b>P${sup(t.n)}${sub(t.i)}</b>：从 ${t.n} 个自变量中取第 ${t.i} 个。${t.n === 3 ? (t.i === 3 ? '在递推步里自变量是 (x, y, r)，所以这里取的是 r，即前一个值。' : t.i === 1 ? '在递推步里取的是 x。' : '在递推步里取的是计数器 y。') : ''}`);
      case 'C': return bi('<b>∘ composition</b>: the first child is the outer function h, the others g₁,…,gₘ are fed the same arguments, and h is applied to their results.', '<b>∘ 复合</b>：第一个孩子是外层函数 h，其余的 g₁,…,gₘ 吃同样的自变量，再把结果交给 h。');
      case 'R': return bi('<b>Rec(g, h)</b>: primitive recursion. Left child g gives f(<span class="vx">x</span>, 0); right child h computes f(<span class="vx">x</span>, y+1) from (<span class="vx">x</span>, y, f(<span class="vx">x</span>, y)).', '<b>Rec(g, h)</b>：原始递归。左孩子 g 给出 f(<span class="vx">x</span>, 0)；右孩子 h 由 (<span class="vx">x</span>, y, f(<span class="vx">x</span>, y)) 算出 f(<span class="vx">x</span>, y+1)。');
      case 'ref': return bi(`<b>${t.name}</b> was defined before. Click to ${expanded.has(t.name) ? 'fold' : 'unfold'} its own tree.`, `<b>${t.name}</b> 是先前定义好的函数。点击可${expanded.has(t.name) ? '折叠' : '展开'}它自己的构造树。`);
    }
  }
  function draw(animate = true) {
    document.querySelectorAll('#prPick button').forEach(b => b.classList.toggle('sel', b.dataset.k === cur));
    const svg = $('prTree');
    svg.innerHTML = '';
    let leaf = 0, maxD = 0;
    const nodes = [];
    function walk(t, depth, ar, role) {
      maxD = Math.max(maxD, depth);
      const nd = { t, depth, ar, role, kids: [] };
      nodes.push(nd);
      let label, kind;
      if (t.t === 'Z') { label = 'Z'; kind = 'basic'; }
      else if (t.t === 'S') { label = 'S'; kind = 'basic'; }
      else if (t.t === 'P') { label = 'P' + sup(t.n) + sub(t.i); kind = 'basic'; }
      else if (t.t === 'C') {
        label = '∘'; kind = 'comp';
        nd.kids = [walk(t.f, depth + 1, t.gs.length, bil('outer', '外层')), ...t.gs.map(g => walk(g, depth + 1, ar, ''))];
      } else if (t.t === 'R') {
        label = 'Rec'; kind = 'rec';
        nd.kids = [walk(t.g, depth + 1, ar - 1, 'g'), walk(t.h, depth + 1, ar + 1, 'h')];
      } else {
        const open = expanded.has(t.name);
        label = t.name + (open ? ' ▾' : ' ▸'); kind = 'ref';
        if (open) nd.kids = [walk(PR.DEFS[t.name].term, depth + 1, ar, '')];
      }
      nd.label = label; nd.kind = kind;
      if (!nd.kids.length) nd.x = leaf++;
      else nd.x = (nd.kids[0].x + nd.kids[nd.kids.length - 1].x) / 2;
      return nd;
    }
    const root = walk(PR.DEFS[cur].term, 0, PR.DEFS[cur].ar, '');
    const GX = 76, GY = 72;
    const W = Math.max(leaf * GX + 120, 300), H = (maxD + 1) * GY + 40;
    svg.setAttribute('viewBox', `0 0 ${W} ${H}`);
    svg.setAttribute('width', W);
    svg.setAttribute('height', H);
    const px = n => 60 + GX / 2 + n.x * GX, py = n => 36 + n.depth * GY;
    const gE = el('g', {}, svg);
    txt(svg, { x: 8, y: 16, 'font-size': 13, fill: '#6b7280' }, cur + ' =');
    nodes.forEach(n => n.kids.forEach(c => {
      el('line', { x1: px(n), y1: py(n) + 15, x2: px(c), y2: py(c) - 15, stroke: '#9aa0aa', 'stroke-width': 2 }, gE);
      if (c.role && c.role !== '') {
        const t = el('text', { x: (px(n) + px(c)) / 2 + (px(c) < px(n) ? -6 : 6), y: (py(n) + py(c)) / 2 + 4, 'font-size': 11, fill: '#ae3ec9', 'text-anchor': px(c) < px(n) ? 'end' : 'start' }, gE);
        t.textContent = c.role === 'g' ? 'g · base 初值' : c.role === 'h' ? 'h · step 递推' : 'outer · 外层';
      }
    }));
    nodes.forEach((n, i) => {
      const w = Math.max(40, [...n.label].length * 10 + 18);
      const g = el('g', { class: 'pn ' + n.kind, transform: `translate(${px(n)},${py(n)})` }, svg);
      const inner = el('g', { class: animate ? 'pop' : '' }, g);
      if (animate) inner.style.animationDelay = (n.depth * 0.08) + 's';
      el('rect', { x: -w / 2, y: -15, width: w, height: 30, rx: 8 }, inner);
      txt(inner, {}, n.label);
      g.style.cursor = 'pointer';
      g.addEventListener('click', () => {
        if (n.t.t === 'ref') { expanded.has(n.t.name) ? expanded.delete(n.t.name) : expanded.add(n.t.name); draw(false); }
        $('prNode').innerHTML = info(n.t, n.ar);
      });
      g.addEventListener('mouseenter', () => g.classList.add('hi'));
      g.addEventListener('mouseleave', () => g.classList.remove('hi'));
    });
    $('prNode').innerHTML = bi('Click any node to see what it does.', '点击任一节点，查看它的作用。');
  }
  let tok = 0;
  async function ladder() {
    const my = ++tok;
    const D = PR.DEFS[cur];
    const x = +$('prX').value, y = +$('prY').value;
    $('prXv').textContent = x; $('prYv').textContent = y;
    const box = $('prLadder');
    box.innerHTML = '';
    clearBox($('prOut'));
    const fx = D.ar === 2 ? `${x}, ` : '';
    const args = D.ar === 2 ? [x] : [];
    let r = PR.ev(PR.DEFS[cur].term.g, args, { s: 0 });
    const head = document.createElement('div');
    head.className = 'muted';
    head.style.borderLeftColor = 'transparent';
    head.innerHTML = `g(${D.ar === 2 ? 'x' : ''}) = ${D.gx} &nbsp; · &nbsp; h(${D.ar === 2 ? 'x, ' : ''}y, r) = ${D.hx}`;
    box.appendChild(head);
    const add = h => { const d = document.createElement('div'); d.className = 'fadein'; d.innerHTML = h; box.appendChild(d); };
    add(`${cur}(${fx}0) = g(${D.ar === 2 ? x : ''}) = ${D.g(x)} = <b>${r}</b>`);
    for (let k = 0; k < y; k++) {
      await sleep(420);
      if (my !== tok) return;
      const nr = PR.ev(PR.DEFS[cur].term.h, [...args, k, r], { s: 0 });
      add(`${cur}(${fx}${k + 1}) = h(${fx}${k}, ${r}) = ${D.h(x, k, r)} = <b>${nr}</b>`);
      r = nr;
    }
    const cnt = { s: 0 };
    const val = PR.ev(PR.DEFS[cur].term, [...args, y], cnt);
    await sleep(300);
    if (my !== tok) return;
    okBox($('prOut'), bi(`${cur}(${fx}${y}) = <b>${val}</b>. Along the way the successor block S fired ${cnt.s} times: everything is built from counting up by one.`,
      `${cur}(${fx}${y}) = <b>${val}</b>。整个计算中后继积木 S 一共被调用 ${cnt.s} 次：一切都是从“加一”搭起来的。`));
  }
  $('prGo').addEventListener('click', ladder);
  $('prX').addEventListener('input', () => { $('prXv').textContent = $('prX').value; });
  $('prY').addEventListener('input', () => { $('prYv').textContent = $('prY').value; });
  draw();
  ladder();
})();

/* ================= §3 Ackermann ================= */
function ackTrace(m, n) {
  const st = [m];
  let calls = 0, maxD = 1;
  const depth = [];
  while (st.length) {
    const mm = st.pop();
    calls++;
    if (mm === 0) n = n + 1;
    else if (n === 0) { n = 1; st.push(mm - 1); }
    else { st.push(mm - 1); st.push(mm); n = n - 1; }
    depth.push(st.length);
    if (st.length > maxD) maxD = st.length;
  }
  return { val: n, calls, depth, maxD };
}
(function ackermann() {
  const ROWS = [['n + 1', 'succ · 后继'], ['n + 2', '+ · 加法'], ['2n + 3', '× · 乘法'], ['2ⁿ⁺³ − 3', '^ · 乘方'], ['2↑↑(n+3) − 3', '↑↑ tower · 指数塔'], ['2↑↑↑(n+3) − 3', '↑↑↑ · 五级运算']];
  function val(m, n) {
    if (m === 0) return String(n + 1);
    if (m === 1) return String(n + 2);
    if (m === 2) return String(2 * n + 3);
    if (m === 3) return String(2 ** (n + 3) - 3);
    if (m === 4) {
      if (n === 0) return '13';
      if (n === 1) return '65533';
      if (n === 2) return 'big:≈ 2×10¹⁹⁷²⁸';
      return `big:2↑↑${n + 3} − 3`;
    }
    if (n === 0) return '65533';
    return `big:2↑↑↑${n + 3} − 3`;
  }
  let h = `<table class="tt ack"><thead><tr><th>m \\ n</th>`;
  for (let n = 0; n <= 5; n++) h += `<th>${n}</th>`;
  h += `</tr></thead><tbody>`;
  ROWS.forEach((r, m) => {
    h += `<tr><th style="text-align:left">m = ${m}<br><span class="muted" style="font-size:11px;font-weight:400;white-space:nowrap">${r[1]}<br>A = ${r[0]}</span></th>`;
    for (let n = 0; n <= 5; n++) {
      const v = val(m, n), big = v.startsWith('big:');
      h += `<td class="${big ? 'big' : ''}${m === n ? ' diag' : ''}" data-m="${m}" data-n="${n}">${big ? v.slice(4) : v}</td>`;
    }
    h += `</tr>`;
  });
  $('ackTable').innerHTML = h + '</tbody></table>';
  const svg = $('ackStack');
  function plot(m, n) {
    svg.innerHTML = '';
    const tr = ackTrace(m, n);
    const X0 = 46, Y0 = 200, PW = 360, PH = 170;
    el('line', { x1: X0, y1: Y0, x2: X0 + PW, y2: Y0, stroke: '#999' }, svg);
    el('line', { x1: X0, y1: Y0, x2: X0, y2: Y0 - PH, stroke: '#999' }, svg);
    txt(svg, { x: X0 + PW, y: Y0 + 18, 'font-size': 11, fill: '#777', 'text-anchor': 'end' }, `calls · 调用次数 → ${tr.calls}`);
    txt(svg, { x: X0 - 6, y: Y0 - PH + 4, 'font-size': 11, fill: '#777', 'text-anchor': 'end' }, tr.maxD);
    txt(svg, { x: X0 - 6, y: Y0 + 4, 'font-size': 11, fill: '#777', 'text-anchor': 'end' }, 0);
    txt(svg, { x: X0 + 4, y: 14, 'font-size': 12, fill: '#ae3ec9', 'font-weight': 700 }, `A(${m}, ${n}) = ${tr.val} · stack depth 栈深度`);
    const B = Math.min(PW, tr.depth.length);
    const pts = [];
    for (let b = 0; b < B; b++) {
      const i0 = Math.floor(b * tr.depth.length / B), i1 = Math.max(i0 + 1, Math.floor((b + 1) * tr.depth.length / B));
      let mx = 0;
      for (let i = i0; i < i1; i++) mx = Math.max(mx, tr.depth[i]);
      pts.push(`${X0 + (b + 0.5) * PW / B},${Y0 - mx / tr.maxD * PH}`);
    }
    const pl = el('polyline', { points: pts.join(' '), fill: 'none', stroke: '#3b5bdb', 'stroke-width': 2 }, svg);
    const L = pl.getTotalLength ? pl.getTotalLength() : 1000;
    pl.style.strokeDasharray = L;
    pl.style.strokeDashoffset = L;
    pl.style.transition = 'stroke-dashoffset 1.6s ease';
    requestAnimationFrame(() => requestAnimationFrame(() => { pl.style.strokeDashoffset = 0; }));
    okBox($('ackMsg'), bi(`A(${m}, ${n}) = <b>${tr.val}</b> took <b>${tr.calls.toLocaleString('en-US')}</b> recursive calls, with the pending-call stack up to ${tr.maxD} deep. No bound on the number of loop rounds is visible in advance.`,
      `A(${m}, ${n}) = <b>${tr.val}</b>，共 <b>${tr.calls}</b> 次递归调用，待处理调用栈最深达 ${tr.maxD} 层。循环要转多少圈，事先看不出任何上界。`), 'info');
  }
  $('ackTable').querySelectorAll('td[data-m]').forEach(td => td.addEventListener('click', () => {
    $('ackTable').querySelectorAll('td.sel').forEach(x => x.classList.remove('sel'));
    td.classList.add('sel');
    const m = +td.dataset.m, n = +td.dataset.n;
    if (m <= 3) plot(m, n);
    else okBox($('ackMsg'), bi(`A(${m}, ${n}) is far too large to compute here${m === 4 && n === 1 ? ' (65533 needs about 2.9 billion calls)' : ''}. A(4, 2) already has 19,729 decimal digits; A(4, 4) is a tower of seven 2's minus 3.`,
      `A(${m}, ${n}) 太大，这里算不动${m === 4 && n === 1 ? '（65533 需要大约 29 亿次调用）' : ''}。A(4, 2) 已有 19729 位十进制数字；A(4, 4) 是 7 层 2 的指数塔减 3。`), 'warn');
  }));
  plot(2, 3);
  stepper('#ackSteps', 'ackNext', 'ackAll');
})();

/* ================= §4 μ-operator ================= */
(function mu() {
  const EX = {
    sqrt: { lab: '⌈√x⌉', f: (x, y) => Math.max(0, x - y * y), s: 'μy[ x ∸ y·y = 0 ]', ge: 'g(x, y) = x ∸ y²', gzh: 'g(x, y) = x ∸ y²' },
    half: { lab: 'x / 2', f: (x, y) => Math.abs(2 * y - x), s: 'μy[ |2y − x| = 0 ]', ge: 'g(x, y) = |2y − x|', gzh: 'g(x, y) = |2y − x|' },
    log: { lab: '⌈log₂ x⌉', f: (x, y) => Math.max(0, x - 2 ** y), s: 'μy[ x ∸ 2ʸ = 0 ]', ge: 'g(x, y) = x ∸ 2ʸ', gzh: 'g(x, y) = x ∸ 2ʸ' },
    never: { lab: '∅', f: () => 1, s: 'μy[ 1 = 0 ]', ge: 'g(x, y) = 1', gzh: 'g(x, y) = 1' },
  };
  let cur = 'sqrt', tok = 0;
  Object.entries(EX).forEach(([k, e]) => {
    const b = document.createElement('button');
    b.className = 'btn small';
    b.dataset.k = k;
    b.innerHTML = `<span class="m">${e.lab}</span>`;
    b.addEventListener('click', () => { cur = k; go(); });
    $('muPick').appendChild(b);
  });
  async function go() {
    const my = ++tok;
    document.querySelectorAll('#muPick button').forEach(b => b.classList.toggle('sel', b.dataset.k === cur));
    const e = EX[cur], x = +$('muX').value;
    $('muXv').textContent = x;
    $('muFormula').innerHTML = `${e.s} &nbsp; <span class="muted">(${e.ge}, x = ${x})</span>`;
    const box = $('muCells');
    box.innerHTML = '';
    clearBox($('muOut'));
    const LIMIT = 24;
    for (let y = 0; y < LIMIT; y++) {
      const v = e.f(x, y);
      const d = document.createElement('div');
      d.className = 'pop cur ' + (v === 0 ? 'zero' : 'nz');
      d.innerHTML = `y = ${y}<br>g = ${v}`;
      box.querySelectorAll('.cur').forEach(c => c.classList.remove('cur'));
      box.appendChild(d);
      if (v === 0) {
        okBox($('muOut'), bi(`Found it: the first zero is at y = ${y}, so the value is <b>${y}</b>. The search halted, but nothing told us in advance how long it would take.`,
          `找到了：第一个零出现在 y = ${y}，所以函数值为 <b>${y}</b>。搜索停了下来，但事先没有任何东西告诉我们要搜多久。`) +
          (cur === 'log' && x === 0 ? bi(' (For x = 0 the search returns 0, although log₂ 0 itself is undefined: this search agrees with ⌈log₂ x⌉ only for x ≥ 1.)', '（x = 0 时搜索返回 0，但 log₂ 0 本身无定义：这个搜索只在 x ≥ 1 时与 ⌈log₂ x⌉ 一致。）') : ''));
        return;
      }
      await sleep(y < 8 ? 260 : 110);
      if (my !== tok) return;
    }
    const d = document.createElement('div');
    d.className = 'nz';
    d.innerHTML = '…<br>∞';
    box.appendChild(d);
    const why = cur === 'half' ? bi(`x = ${x} is odd, so 2y − x is never 0.`, `x = ${x} 是奇数，2y − x 永远不为 0。`) : bi('g is never 0.', 'g 永远不为 0。');
    okBox($('muOut'), bi('No zero yet, and none will ever come: ', '还没找到零，而且永远找不到：') + why +
      bi(' The search runs forever, so the function is <b>undefined</b> here. We can see that from outside, but the search itself cannot. This is how partial functions enter computability.',
        '搜索永不停止，所以函数在这里<b>无定义</b>。我们站在外面看得出来，搜索过程自己却不知道。部分函数正是这样进入可计算性理论的。'), 'warn');
  }
  $('muGo').addEventListener('click', go);
  $('muX').addEventListener('input', () => { $('muXv').textContent = $('muX').value; });
  go();

  // Church–Turing model map
  const svg = $('ctSvg');
  const models = [
    { x: 20, y: 24, en: 'Turing machines', zh: '图灵机', yr: 'Turing 1936',
      ien: 'A finite control reading and writing a tape. Turing argued directly from what a human computer with pencil and paper can do: finitely many states of mind, finitely many symbols in view, local changes.',
      izh: '一个有限控制器在纸带上读写。图灵直接从“一个人拿纸笔计算能做什么”出发论证：有限多种心智状态，一次只看有限个符号，每步只做局部改动。' },
    { x: 20, y: 134, en: 'λ-calculus', zh: 'λ 演算', yr: 'Church 1936',
      ien: 'Everything is a function; computation is substitution (β-reduction). Church and Kleene showed λ-definable = general recursive; Turing showed λ-definable = Turing computable.',
      izh: '一切皆函数，计算就是代入（β 归约）。丘奇和克莱尼证明了 λ 可定义 = 一般递归；图灵证明了 λ 可定义 = 图灵可计算。' },
    { x: 20, y: 244, en: 'General recursive', zh: '一般递归函数', yr: 'Gödel–Herbrand 1934 · Kleene 1936',
      ien: 'Primitive recursion plus the μ-operator (§4). Kleene normal form: every partial recursive function is U(μy T(e, x, y)) with T, U primitive recursive, so a single unbounded search is enough.',
      izh: '原始递归加上 μ 算子（§4）。克莱尼范式定理：每个部分递归函数都可写成 U(μy T(e, x, y))，其中 T、U 是原始递归的，所以只需要一次无界搜索。' },
    { x: 570, y: 24, en: 'Post systems', zh: '波斯特系统', yr: 'Post 1936/1943',
      ien: 'String-rewriting rules: replace patterns in words (Post\'s canonical/production systems, published 1943). Already in 1936 Post had independently described a machine-like model (“Formulation 1”) essentially equivalent to Turing\'s.',
      izh: '字符串改写规则：在字上按模式替换（波斯特的规范系统/产生式系统，1943 年发表）。早在 1936 年，波斯特就独立提出了一个类似机器的模型（“表述 1”），本质上与图灵机等价。' },
    { x: 570, y: 134, en: 'Register machines', zh: '寄存器机', yr: 'Minsky; Shepherdson–Sturgis',
      ien: 'Finitely many registers holding natural numbers, with instructions “increment”, “decrement or jump if zero”. Two registers already suffice (with suitable coding).',
      izh: '有限个存放自然数的寄存器，指令只有“加一”和“为零则跳转否则减一”。（经适当编码）两个寄存器就够了。' },
    { x: 570, y: 244, en: 'Programming languages', zh: '程序设计语言', yr: 'C, Python, Lisp, …',
      ien: 'Any language with unbounded loops (or recursion) and unbounded memory is Turing complete. Remove unbounded while-loops (and general recursion) and keep only for-loops with a fixed bound, and you are back to primitive recursion.',
      izh: '只要有无界循环（或递归）和无界存储，任何语言都是图灵完备的。去掉无界 while 循环（以及一般递归）、只留事先定好次数的 for 循环，就退回到原始递归。' },
  ];
  el('ellipse', { cx: 380, cy: 160, rx: 150, ry: 56, fill: '#f8e7fc', stroke: '#ae3ec9', 'stroke-width': 3 }, svg);
  txt(svg, { x: 380, y: 152, 'text-anchor': 'middle', 'font-size': 16, 'font-weight': 700, fill: '#ae3ec9' }, 'Computable functions');
  txt(svg, { x: 380, y: 176, 'text-anchor': 'middle', 'font-size': 16, 'font-weight': 700, fill: '#ae3ec9' }, '可计算函数');
  const boxes = [];
  models.forEach(md => {
    const right = md.x > 300;
    el('line', { x1: right ? md.x : md.x + 170, y1: md.y + 28, x2: right ? 515 : 245, y2: 160 + (md.y - 134) * 0.35, stroke: '#ae3ec9', 'stroke-width': 2, 'stroke-dasharray': '5 4' }, svg);
    txt(svg, { x: right ? (md.x + 515) / 2 : (md.x + 170 + 245) / 2, y: (md.y + 28 + 160 + (md.y - 134) * 0.35) / 2 - 6, 'text-anchor': 'middle', 'font-size': 15, fill: '#ae3ec9', 'font-weight': 700 }, '⇔');
    const g = el('g', { class: 'ctbox', transform: `translate(${md.x},${md.y})` }, svg);
    el('rect', { width: 170, height: 58, rx: 10, fill: '#fff', stroke: '#c9c3b3', 'stroke-width': 2 }, g);
    txt(g, { x: 85, y: 19, 'text-anchor': 'middle', 'font-size': 13.5, 'font-weight': 700 }, md.en);
    txt(g, { x: 85, y: 35, 'text-anchor': 'middle', 'font-size': 12.5 }, md.zh);
    txt(g, { x: 85, y: 51, 'text-anchor': 'middle', 'font-size': 10, fill: '#777' }, md.yr);
    g.addEventListener('click', () => {
      boxes.forEach(b => b.classList.remove('on'));
      g.classList.add('on');
      $('ctMsg').innerHTML = `<b>${bil(md.en, md.zh)}</b> · ${bi(md.ien, md.izh)}`;
    });
    boxes.push(g);
  });
  const pg = el('g', { class: 'ctbox', transform: 'translate(290,262)' }, svg);
  el('rect', { width: 180, height: 50, rx: 10, fill: '#fff3bf', stroke: '#f08c00', 'stroke-width': 2, 'stroke-dasharray': '6 4' }, pg);
  txt(pg, { x: 90, y: 20, 'text-anchor': 'middle', 'font-size': 13, 'font-weight': 700 }, 'Primitive recursive ⊊');
  txt(pg, { x: 90, y: 38, 'text-anchor': 'middle', 'font-size': 12.5 }, '原始递归函数（真子类）');
  el('line', { x1: 380, y1: 262, x2: 380, y2: 218, stroke: '#f08c00', 'stroke-width': 2, 'marker-end': '' }, svg);
  pg.addEventListener('click', () => {
    boxes.forEach(b => b.classList.remove('on'));
    $('ctMsg').innerHTML = bi('<b>Primitive recursive functions</b> are a proper subclass: all total, all computable, but they miss the Ackermann function (§3). In fact <i>no</i> effective listing of total computable functions can contain them all: diagonalize, f(n) = fₙ(n) + 1.',
      '<b>原始递归函数</b>是一个真子类：都是全函数、都可计算，却漏掉了阿克曼函数（§3）。事实上，<i>任何</i>能行地列出的全可计算函数清单都不可能包含全部：对角化一下，f(n) = fₙ(n) + 1 即可。');
  });
  $('ctMsg').innerHTML = bi('Click a box.', '点击一个方框。');
})();

/* ================= §5 universal machine ================= */
(function universal() {
  const keys = ['uinc', 'binc', 'uadd', 'bb2'];
  const PH = [['find the rule', '查找规则'], ['write', '写入'], ['move', '移动'], ['update state', '更新状态']];
  let M, cfg, enc, cur = 'binc', busy = false;
  const tape = TapeView($('uTape'), { w: 720, cw: 40, label: 'M · ' });
  $('uPhase').innerHTML = PH.map(p => `<span>${bil(p[0], p[1])}</span>`).join('');
  const phase = k => $('uPhase').querySelectorAll('span').forEach((s, i) => s.classList.toggle('on', i === k));
  keys.forEach(k => {
    const b = document.createElement('button');
    b.className = 'btn small';
    b.dataset.k = k;
    b.innerHTML = bil(PRESETS[k].en, PRESETS[k].zh);
    b.addEventListener('click', () => { cur = k; load(); });
    $('uPick').appendChild(b);
  });
  function stateTape() {
    const i = M.states.indexOf(cfg.state) + 1;
    $('uState').innerHTML = `<span style="color:#3b5bdb;font-weight:700">${'0'.repeat(i)}</span> <span class="muted">= q${sub(i)} (${cfg.state})</span>`;
  }
  function load() {
    busy = false;
    document.querySelectorAll('#uPick button').forEach(b => b.classList.toggle('sel', b.dataset.k === cur));
    M = TMCore.parse(PRESETS[cur].text);
    enc = TMCore.encode(M);
    cfg = TMCore.init(M, PRESETS[cur].input);
    $('uBits').innerHTML = `<b style="font-family:var(--sans)">${bil('tape 1: ⟨M⟩', '带 1：⟨M⟩')}</b>&nbsp; ` + enc.blocks.map((b, i) =>
      `<span class="blk" data-i="${i}" title="${b.rule.q} ${b.rule.r} → ${b.rule.n} ${b.rule.w} ${b.rule.m}  =  (${b.nums.join(', ')})">${b.bits}</span>`).join('<span class="sep">11</span>');
    const big = BigInt('0b1' + enc.bits).toString();
    $('uNum').innerHTML = bi(`${enc.bits.length} bits, ${enc.blocks.length} rules. States: ${M.states.map((s, i) => `q${sub(i + 1)}=${s}`).join(', ')}; symbols: ${M.symbols.map((s, i) => `s${sub(i + 1)}=${s}`).join(', ')}. Read as a number (with a leading 1 so no zeros are lost), e = ${big.length > 40 ? big.slice(0, 40) + '…' : big} (${big.length} digits). Hover a block to decode it.`,
      `共 ${enc.bits.length} 位、${enc.blocks.length} 条规则。状态：${M.states.map((s, i) => `q${sub(i + 1)}=${s}`).join('，')}；符号：${M.symbols.map((s, i) => `s${sub(i + 1)}=${s}`).join('，')}。前面补一个 1（免得丢掉开头的 0）后读成二进制数，e = ${big.length > 40 ? big.slice(0, 40) + '…' : big}（共 ${big.length} 位十进制数字）。鼠标悬停在某一段上可以看到它的译码。`);
    tape.render(cfg);
    stateTape();
    phase(-1);
    okBox($('uMsg'), bi(`U is ready: tape 1 holds ⟨M⟩, tape 2 holds M's input “${PRESETS[cur].input || 'ε'}”.`, `U 已就绪：带 1 存放 ⟨M⟩，带 2 存放 M 的输入“${PRESETS[cur].input || 'ε'}”。`), 'info');
  }
  async function stepU() {
    if (busy) return;
    if (cfg.halted) {
      okBox($('uMsg'), bi(`No block on tape 1 starts with ${'0'.repeat(M.states.indexOf(cfg.state) + 1)}1${'0'.repeat(M.symbols.indexOf(TMCore.read(cfg)) + 1)}1, so M has halted after ${cfg.steps} steps, and U halts too, leaving M's output on tape 2.`,
        `带 1 上没有以 ${'0'.repeat(M.states.indexOf(cfg.state) + 1)}1${'0'.repeat(M.symbols.indexOf(TMCore.read(cfg)) + 1)}1 开头的段，所以 M 在 ${cfg.steps} 步后停机，U 也随之停机，带 2 上留下的就是 M 的输出。`));
      return;
    }
    busy = true;
    const sym = TMCore.read(cfg);
    const idx = M.order.findIndex(o => o.q === cfg.state && o.r === sym);
    const b = enc.blocks[idx];
    phase(0);
    const span = $('uBits').querySelector(`.blk[data-i="${idx}"]`);
    $('uBits').querySelectorAll('.blk').forEach(s => s.classList.remove('hot'));
    span.classList.add('hot');
    okBox($('uMsg'), bi(`State q${sub(b.nums[0])}, reading s${sub(b.nums[1])}: U scans tape 1 for the block starting 0${sup(b.nums[0])}1 0${sup(b.nums[1])}1 and finds rule #${idx + 1}: write s${sub(b.nums[3])}, move ${b.rule.m}, go to q${sub(b.nums[2])}.`,
      `状态 q${sub(b.nums[0])}，读到 s${sub(b.nums[1])}：U 在带 1 上找以 0${sup(b.nums[0])}1 0${sup(b.nums[1])}1 开头的段，找到第 ${idx + 1} 条规则：写 s${sub(b.nums[3])}，移动 ${b.rule.m}，转入 q${sub(b.nums[2])}。`), 'info');
    await sleep(650);
    phase(1); await sleep(300);
    phase(2);
    TMCore.step(M, cfg);
    tape.render(cfg);
    await sleep(350);
    phase(3);
    stateTape();
    await sleep(250);
    busy = false;
  }
  $('uStep').addEventListener('click', stepU);
  $('uReset').addEventListener('click', load);
  load();
})();

/* ================= §6 halting by diagonalization ================= */
(function halting() {
  const N = 8, CS = 44, X0 = 84, Y0 = 70;
  const Hh = Array.from({ length: N }, (_, e) => Array.from({ length: N }, (_, i) => ((e * 5 + i * 3 + e * i) % 7) < 4 ? 1 : 0));
  const svg = $('hpTable');
  let flipped = false, tok = 0;
  const sym = v => v ? '↓' : '↑';
  function draw() {
    tok++;
    svg.innerHTML = '';
    txt(svg, { x: X0 + N * CS / 2, y: 18, 'text-anchor': 'middle', 'font-size': 13, fill: '#6b7280' }, 'input i · 输入 i →');
    for (let i = 0; i < N; i++) txt(svg, { x: X0 + i * CS + CS / 2, y: Y0 - 12, 'text-anchor': 'middle', 'font-size': 14, 'font-weight': 700, fill: '#f08c00' }, i);
    txt(svg, { x: X0 + N * CS + 14, y: Y0 - 12, 'font-size': 14, fill: '#999' }, '…');
    for (let e = 0; e < N; e++) {
      const lab = txt(svg, { x: X0 - 12, y: Y0 + e * CS + CS / 2 + 5, 'text-anchor': 'end', 'font-size': 15, 'font-weight': 700, id: 'hpL' + e, style: 'cursor:pointer' }, 'M' + sub(e));
      lab.addEventListener('click', () => compare(e));
      for (let i = 0; i < N; i++) {
        el('rect', { x: X0 + i * CS + 2, y: Y0 + e * CS + 2, width: CS - 4, height: CS - 4, rx: 6, fill: Hh[e][i] ? '#d3f9d8' : '#ffe3e3', id: `hc${e}_${i}` }, svg);
        txt(svg, { x: X0 + i * CS + CS / 2, y: Y0 + e * CS + CS / 2 + 6, 'text-anchor': 'middle', 'font-size': 18, fill: Hh[e][i] ? '#2f9e44' : '#e03131' }, sym(Hh[e][i]));
      }
      txt(svg, { x: X0 + N * CS + 14, y: Y0 + e * CS + CS / 2 + 5, 'font-size': 14, fill: '#999' }, '…');
    }
    txt(svg, { x: X0 - 40, y: Y0 + N * CS + 6, 'font-size': 14, fill: '#999' }, '⋮');
    txt(svg, { x: X0 - 12, y: Y0 + N * CS + 20 + CS / 2 + 5, 'text-anchor': 'end', 'font-size': 16, 'font-weight': 800, fill: '#ae3ec9' }, 'D');
    flipped = false;
    $('hpMsg').innerHTML = bi('Green ↓ = halts, red ↑ = runs forever. Press “Flip the diagonal”, then click any row label Mₑ to compare it with D.', '绿色 ↓ = 停机，红色 ↑ = 永不停机。按“翻转对角线”，再点击任一行标签 Mₑ，把它和 D 比一比。');
  }
  function dCell(k, cls = 'pop') {
    const yD = Y0 + N * CS + 20, v = 1 - Hh[k][k];
    el('rect', { x: X0 + k * CS + 2, y: yD + 2, width: CS - 4, height: CS - 4, rx: 6, fill: '#f8e7fc', stroke: '#ae3ec9', 'stroke-width': 2, class: cls }, svg);
    txt(svg, { x: X0 + k * CS + CS / 2, y: yD + CS / 2 + 6, 'text-anchor': 'middle', 'font-size': 18, 'font-weight': 800, fill: '#ae3ec9' }, sym(v));
  }
  async function flip() {
    draw();
    const my = tok;
    for (let k = 0; k < N; k++) {
      await sleep(380);
      if (my !== tok) return;
      const c = svg.querySelector(`#hc${k}_${k}`);
      c.setAttribute('stroke', '#ae3ec9');
      c.setAttribute('stroke-width', 3);
      dCell(k);
    }
    txt(svg, { x: X0 + N * CS + 14, y: Y0 + N * CS + 20 + CS / 2 + 5, 'font-size': 14, fill: '#ae3ec9' }, '…');
    flipped = true;
    okBox($('hpMsg'), bi('D(e) does the opposite of Mₑ(e): it halts exactly when Mₑ(e) runs forever. If a halting decider H existed, D would be a Turing machine. Click a row label: which Mₑ is D?',
      'D(e) 总是和 Mₑ(e) 反着来：恰在 Mₑ(e) 永不停机时停机。假如存在停机判定器 H，D 就是一台图灵机。点击行标签：D 是哪一台 Mₑ？'), 'info');
  }
  function compare(e) {
    if (!flipped) { draw(); for (let k = 0; k < N; k++) { svg.querySelector(`#hc${k}_${k}`).setAttribute('stroke', '#ae3ec9'); svg.querySelector(`#hc${k}_${k}`).setAttribute('stroke-width', 3); dCell(k, ''); } flipped = true; }
    svg.querySelectorAll('.cmp').forEach(x => x.remove());
    el('rect', { x: X0 - 2, y: Y0 + e * CS, width: N * CS + 4, height: CS, rx: 8, fill: 'none', stroke: '#3b5bdb', 'stroke-width': 2.5, class: 'cmp' }, svg);
    el('rect', { x: X0 + e * CS - 3, y: Y0 + e * CS - 3, width: CS + 6, height: (N - e) * CS + 20 + CS + 6, rx: 9, fill: 'none', stroke: '#e03131', 'stroke-width': 3, 'stroke-dasharray': '6 4', class: 'cmp' }, svg);
    const a = Hh[e][e];
    okBox($('hpMsg'), bi(`D ≠ M${sub(e)}: on input ${e}, M${sub(e)} ${a ? 'halts ↓' : 'runs forever ↑'} but D ${a ? 'runs forever ↑' : 'halts ↓'}. The same happens in every row, so D is nowhere in the list. But the list contains <i>every</i> Turing machine, so D cannot be a Turing machine. Yet D would be one if H existed. Therefore H cannot exist.`,
      `D ≠ M${sub(e)}：在输入 ${e} 上，M${sub(e)} ${a ? '停机 ↓' : '永不停机 ↑'}，而 D ${a ? '永不停机 ↑' : '停机 ↓'}。每一行都是如此，所以 D 不在清单里。可是清单包含了<i>所有</i>图灵机，所以 D 不可能是图灵机；而假如 H 存在，D 就是图灵机。因此 H 不可能存在。`), 'bad');
  }
  $('hpFlip').addEventListener('click', flip);
  $('hpReset').addEventListener('click', draw);
  draw();

  // flowchart: D on its own code
  const fs = $('hpFlow');
  const boxes = {};
  function box(id, x, y, w, h, en, zh, shape = 'rect') {
    const g = el('g', {}, fs);
    let s;
    if (shape === 'diamond') s = el('path', { d: `M${x},${y - h / 2} L${x + w / 2},${y} L${x},${y + h / 2} L${x - w / 2},${y} Z`, fill: '#fff', stroke: '#9aa0aa', 'stroke-width': 2 }, g);
    else s = el('rect', { x: x - w / 2, y: y - h / 2, width: w, height: h, rx: 10, fill: '#fff', stroke: '#9aa0aa', 'stroke-width': 2 }, g);
    txt(g, { x, y: y - 3, 'text-anchor': 'middle', 'font-size': 12.5, 'font-weight': 700 }, en);
    txt(g, { x, y: y + 14, 'text-anchor': 'middle', 'font-size': 12 }, zh);
    boxes[id] = s;
  }
  const arrow = (x1, y1, x2, y2) => el('path', { d: `M${x1},${y1} L${x2},${y2}`, stroke: '#9aa0aa', 'stroke-width': 2, fill: 'none' }, fs);
  arrow(190, 52, 190, 78); arrow(190, 142, 95, 172); arrow(190, 142, 285, 172); arrow(95, 218, 95, 252); arrow(285, 218, 285, 252); arrow(95, 298, 95, 332); arrow(285, 298, 285, 332);
  box('top', 190, 30, 250, 44, 'D receives its own code d', 'D 收到自己的编码 d');
  box('ask', 190, 110, 230, 64, 'H(d, d) = ?', '问判定器 H', 'diamond');
  box('l1', 95, 195, 170, 46, 'H: “D(d) halts”', 'H 说：会停机');
  box('r1', 285, 195, 170, 46, 'H: “D(d) loops”', 'H 说：不停机');
  box('l2', 95, 275, 170, 46, 'so D loops forever', '于是 D 死循环');
  box('r2', 285, 275, 170, 46, 'so D halts', '于是 D 停机');
  box('l3', 95, 355, 170, 46, '✗ H was wrong', '✗ H 判断错了');
  box('r3', 285, 355, 170, 46, '✗ H was wrong', '✗ H 判断错了');
  const tokEl = el('circle', { r: 9, fill: '#ae3ec9', cx: 190, cy: 30, opacity: 0 }, fs);
  tokEl.style.transition = 'cx .4s, cy .4s';
  let ftok = 0;
  async function runFlow() {
    const my = ++ftok;
    Object.values(boxes).forEach(b => { b.setAttribute('fill', '#fff'); b.setAttribute('stroke', '#9aa0aa'); });
    tokEl.setAttribute('opacity', 1);
    const visit = async (id, x, y, bad) => {
      if (my !== ftok) throw 0;
      tokEl.setAttribute('cx', x - (id === 'ask' ? 0 : 0)); tokEl.setAttribute('cy', y - 30 < 0 ? y : y - 22);
      boxes[id].setAttribute('fill', bad ? '#ffe3e3' : '#e7ecff');
      boxes[id].setAttribute('stroke', bad ? '#e03131' : '#3b5bdb');
      await sleep(650);
    };
    try {
      await visit('top', 190, 30); await visit('ask', 190, 110);
      await visit('l1', 95, 195); await visit('l2', 95, 275); await visit('l3', 95, 355, true);
      tokEl.setAttribute('cx', 190); tokEl.setAttribute('cy', 88); await sleep(500);
      await visit('r1', 285, 195); await visit('r2', 285, 275); await visit('r3', 285, 355, true);
      tokEl.setAttribute('opacity', 0);
    } catch (e) { /* interrupted */ }
  }
  $('hpRun').addEventListener('click', runFlow);
  stepper('#hpSteps', 'hpNext', 'hpAll');
})();

/* ================= §7 Venn + dovetailing ================= */
(function venn() {
  const svg = $('venn');
  el('rect', { x: 8, y: 8, width: 704, height: 314, rx: 16, fill: '#f1efe7', stroke: '#d8d3c4' }, svg);
  txt(svg, { x: 22, y: 28, 'font-size': 12, fill: '#777' }, 'all sets A ⊆ ℕ · 所有子集 A ⊆ ℕ  (neither · 都不是)');
  el('ellipse', { cx: 285, cy: 180, rx: 195, ry: 125, fill: 'rgba(59,91,219,.12)', stroke: '#3b5bdb', 'stroke-width': 2.5 }, svg);
  el('ellipse', { cx: 435, cy: 180, rx: 195, ry: 125, fill: 'rgba(240,140,0,.12)', stroke: '#f08c00', 'stroke-width': 2.5 }, svg);
  txt(svg, { x: 198, y: 122, 'text-anchor': 'middle', 'font-size': 13, 'font-weight': 700, fill: '#3b5bdb' }, 'r.e. · 递归可枚举');
  txt(svg, { x: 532, y: 122, 'text-anchor': 'middle', 'font-size': 13, 'font-weight': 700, fill: '#f08c00' }, 'co-r.e. · 余递归可枚举');
  txt(svg, { x: 360, y: 122, 'text-anchor': 'middle', 'font-size': 14, 'font-weight': 700, fill: '#2f9e44' }, 'decidable · 可判定');
  const ITEMS = [
    { s: 'prime', en: 'n is prime', zh: 'n 是素数', r: 'dec', ien: 'Trial division always finishes.', izh: '试除法总能在有限步内结束。' },
    { s: 'K', en: 'K = {e : Mₑ(e)↓}', zh: 'K = {e : Mₑ(e)↓}', r: 're', ien: 'r.e. by dovetailing (below), undecidable by §6.', izh: '用交错运行（见下）可枚举；由 §6 不可判定。' },
    { s: 'ℕ∖K', en: 'ℕ ∖ K', zh: 'ℕ ∖ K', r: 'core', ien: 'Its complement K is r.e.; if ℕ∖K were r.e. too, K would be decidable by the complementation theorem.', izh: '它的补集 K 递归可枚举；若 ℕ∖K 也递归可枚举，由补集定理 K 就可判定了。' },
    { s: 'TOT', en: 'TOT = {e : φₑ total}', zh: 'TOT = {e : φₑ 是全函数}', r: 'nei', ien: '“For every x there is a halting time”: ∀∃, two unbounded quantifiers. Neither r.e. nor co-r.e. (it is Π₂-complete).', izh: '“对每个 x 都存在停机时刻”：∀∃，两层无界量词。既不递归可枚举也不余递归可枚举（它是 Π₂ 完全的）。' },
    { s: 'Diophantine', en: 'polynomial equations with an integer solution', zh: '有整数解的多项式方程', r: 're', ien: 'Search all integer tuples: r.e. Undecidable by the Matiyasevich–Robinson–Davis–Putnam theorem (1970): Hilbert\'s 10th problem has a negative answer.', izh: '逐一搜索所有整数组：递归可枚举。由马季亚谢维奇–罗宾逊–戴维斯–普特南定理（1970）不可判定：希尔伯特第十问题的答案是否定的。' },
    { s: 'valid FO', en: 'valid first-order sentences', zh: '一阶逻辑的普遍有效语句', r: 're', ien: 'Enumerate all proofs: r.e. by Gödel\'s completeness theorem (Lesson 4). Undecidable by Church–Turing (1936), as soon as the language has a binary relation symbol (for purely unary languages validity is decidable).', izh: '枚举所有证明：由哥德尔完备性定理（第 4 课）递归可枚举。只要语言中有一个二元关系符号，由丘奇–图灵（1936）它就不可判定（只含一元谓词的语言则可判定）。' },
    { s: 'Th(ℕ)', en: 'true sentences of arithmetic', zh: '算术真语句的全体', r: 'nei', ien: 'Not even arithmetically definable (Tarski, Lesson 13). Coming up in Lessons 12–13.', izh: '它甚至不能在算术中定义（塔斯基，第 13 课）。第 12–13 课详谈。' },
    { s: 'Wₑ=∅', en: '{e : Mₑ halts on no input}', zh: '{e : Mₑ 在任何输入上都不停机}', r: 'core', ien: 'Its complement “halts on some input” is r.e. by dovetailing over (input, steps). Undecidable by Rice (§8).', izh: '其补集“在某个输入上停机”可以对（输入, 步数）交错运行而枚举。由莱斯定理（§8）不可判定。' },
    { s: '≤1000', en: 'Mₑ halts on 0 within 1000 steps', zh: 'Mₑ 在输入 0 上 1000 步内停机', r: 'dec', ien: 'Just simulate 1000 steps. A time bound kills undecidability.', izh: '模拟 1000 步即可。有了时间上界，不可判定性就消失了。' },
  ];
  const SLOTS = { dec: [[360, 155], [360, 188], [360, 221], [360, 254]], re: [[180, 155], [180, 188], [180, 221], [180, 254]],
    core: [[540, 155], [540, 188], [540, 221], [540, 254]], nei: [[70, 60], [650, 60], [70, 300], [650, 300]] };
  const used = { dec: 0, re: 0, core: 0, nei: 0 };
  const NAME = { dec: ['decidable', '可判定'], re: ['r.e., not decidable', '递归可枚举但不可判定'], core: ['co-r.e., not decidable', '余递归可枚举但不可判定'], nei: ['neither r.e. nor co-r.e.', '既非递归可枚举也非余递归可枚举'] };
  ITEMS.forEach(it => {
    const c = document.createElement('div');
    c.className = 'chip';
    c.innerHTML = bil(it.en, it.zh);
    c.addEventListener('click', () => {
      if (!it.placed) {
        const [x, y] = SLOTS[it.r][used[it.r]++ % 4];
        const g = el('g', {}, svg);
        el('circle', { cx: x - 4 - it.s.length * 3.6, cy: y - 4, r: 5, fill: '#ae3ec9' }, g);
        txt(g, { x: x + 4, y, 'text-anchor': 'middle', 'font-size': 13, 'font-weight': 700 }, it.s);
        it.placed = g;
        c.classList.add('ok');
      }
      $('vennMsg').innerHTML = `<b>${bil(it.en, it.zh)}</b>: <b>${bil(NAME[it.r][0], NAME[it.r][1])}</b>. ${bi(it.ien, it.izh)}`;
    });
    $('vennChips').appendChild(c);
  });
  $('vennMsg').innerHTML = bi('Click a chip above.', '点击上面的卡片。');

  // dovetailing
  const ds = $('dtSvg');
  const T = [3, Infinity, 1, 6, Infinity, 2, 9, Infinity];
  const NR = 8, NC = 12, CS = 34, X0 = 80, Y0 = 44;
  let dtok = 0;
  function dtDraw() {
    dtok++;
    ds.innerHTML = '';
    txt(ds, { x: X0 + NC * CS / 2, y: 16, 'text-anchor': 'middle', 'font-size': 12, fill: '#6b7280' }, 'step t of the computation · 计算的第 t 步 →');
    for (let t = 1; t <= NC; t++) txt(ds, { x: X0 + (t - 1) * CS + CS / 2, y: Y0 - 8, 'text-anchor': 'middle', 'font-size': 12, fill: '#f08c00', 'font-weight': 700 }, t);
    for (let e = 0; e < NR; e++) {
      txt(ds, { x: X0 - 8, y: Y0 + e * CS + CS / 2 + 5, 'text-anchor': 'end', 'font-size': 13, 'font-weight': 700 }, `M${sub(e)}(${e})`);
      for (let t = 1; t <= NC; t++) el('rect', { x: X0 + (t - 1) * CS + 2, y: Y0 + e * CS + 2, width: CS - 4, height: CS - 4, rx: 5, fill: '#fff', stroke: '#e3dfd3', id: `dt${e}_${t}` }, ds);
    }
    $('dtOut').innerHTML = '<span class="muted">K ∋ …</span>';
  }
  async function dtRun() {
    dtDraw();
    const my = dtok;
    const found = [];
    for (let s = 0; s < NR + NC - 1; s++) {
      for (let e = 0; e <= Math.min(s, NR - 1); e++) {
        const t = s - e + 1;
        if (t > NC || t > T[e]) continue;
        const r = ds.querySelector(`#dt${e}_${t}`);
        if (t === T[e]) {
          r.setAttribute('fill', '#2f9e44');
          txt(ds, { x: X0 + (t - 1) * CS + CS / 2, y: Y0 + e * CS + CS / 2 + 6, 'text-anchor': 'middle', 'font-size': 16, fill: '#fff', 'font-weight': 800 }, '↓');
          found.push(e);
          $('dtOut').innerHTML = `K ∋ ${found.map((x, i) => `<b class="${i === found.length - 1 ? 'pop' : ''}" style="display:inline-block;color:#2f9e44">${x}</b>`).join(', ')}, …`;
        } else r.setAttribute('fill', '#bac8ff');
      }
      await sleep(330);
      if (my !== dtok) return;
    }
    for (let e = 0; e < NR; e++) if (T[e] === Infinity) txt(ds, { x: X0 + NC * CS + 4, y: Y0 + e * CS + CS / 2 + 5, 'font-size': 14, fill: '#e03131' }, '… ↑?');
  }
  $('dtGo').addEventListener('click', dtRun);
  $('dtReset').addEventListener('click', dtDraw);
  dtDraw();
})();

/* ================= §8 reductions & Rice ================= */
(function reductions() {
  const TG = {
    blank: { en: 'HALT<sub>ε</sub>: M halts on the blank tape', zh: 'HALT<sub>ε</sub>：M 在空白带上停机', svg: 'halts on blank · 空白带上停机',
      ten: 'Given (M, w), let <span class="m">f(M, w) = M′</span>: “erase the input, write w, run M”. M′ ignores its own input, so <span class="m">M′ halts on blank ⇔ M halts on w</span>.',
      tzh: '给定 (M, w)，令 <span class="m">f(M, w) = M′</span>：“擦掉输入，写上 w，运行 M”。M′ 不理会自己的输入，所以 <span class="m">M′ 在空白带上停机 ⇔ M 在 w 上停机</span>。' },
    tot: { en: 'TOT: M halts on every input', zh: 'TOT：M 在所有输入上停机', svg: 'TOT',
      ten: 'Same M′. Since M′ behaves identically on every input, <span class="m">M′ is total ⇔ M halts on w</span>. (TOT is in fact much worse: not even r.e. or co-r.e.)',
      tzh: '同一个 M′。由于 M′ 在每个输入上行为完全相同，<span class="m">M′ 是全函数 ⇔ M 在 w 上停机</span>。（其实 TOT 比这糟得多：既不递归可枚举，也不余递归可枚举。）' },
    some: { en: 'NE: M halts on some input', zh: 'NE：M 在某个输入上停机', svg: 'NE',
      ten: 'Same M′ again: <span class="m">W<sub>M′</sub> = ℕ</span> if M halts on w, and <span class="m">W<sub>M′</sub> = ∅</span> otherwise.',
      tzh: '还是同一个 M′：若 M 在 w 上停机则 <span class="m">W<sub>M′</sub> = ℕ</span>，否则 <span class="m">W<sub>M′</sub> = ∅</span>。' },
    zero: { en: 'ZERO: M computes the constant 0', zh: 'ZERO：M 计算常数函数 0', svg: 'ZERO',
      ten: 'Let M′ = “run M on w; if that ever finishes, erase everything and output 0”. Then <span class="m">φ<sub>M′</sub> = const 0 ⇔ M halts on w</span>.',
      tzh: '令 M′ =“在 w 上运行 M；一旦它结束，就清空带子并输出 0”。则 <span class="m">φ<sub>M′</sub> = 常数 0 ⇔ M 在 w 上停机</span>。' },
  };
  let cur = 'blank';
  const svg = $('redSvg');
  const LEFT = [[110, 80], [170, 110], [95, 130], [120, 190], [180, 215], [90, 235]];
  const RIGHT = [[470, 80], [540, 105], [490, 130], [480, 195], [545, 220], [500, 240]];
  let dots = [];
  function draw() {
    svg.innerHTML = '';
    document.querySelectorAll('#redPick button').forEach(b => b.classList.toggle('sel', b.dataset.k === cur));
    [[150, 'HALT'], [500, 'B']].forEach(([cx, name]) => {
      el('ellipse', { cx, cy: 160, rx: 125, ry: 118, fill: '#fff', stroke: '#9aa0aa', 'stroke-width': 2 }, svg);
      el('path', { d: `M${cx - 125},160 A125,118 0 0 1 ${cx + 125},160 Z`, fill: 'rgba(47,158,68,.12)' }, svg);
      txt(svg, { x: cx, y: 22, 'text-anchor': 'middle', 'font-size': 14, 'font-weight': 700 }, name === 'HALT' ? '⟨M, w⟩ ∈ HALT ?' : 'x ∈ B ?');
      txt(svg, { x: cx + 72, y: 66, 'font-size': 12, fill: '#2f9e44', 'font-weight': 700 }, 'yes · 是');
      txt(svg, { x: cx + 72, y: 262, 'font-size': 12, fill: '#e03131', 'font-weight': 700 }, 'no · 否');
    });
    txt(svg, { x: 325, y: 152, 'text-anchor': 'middle', 'font-size': 22, fill: '#ae3ec9', 'font-weight': 800 }, 'f');
    txt(svg, { x: 325, y: 172, 'text-anchor': 'middle', 'font-size': 11, fill: '#ae3ec9' }, 'computable · 可计算');
    txt(svg, { x: 325, y: 290, 'text-anchor': 'middle', 'font-size': 12, fill: '#555' }, 'B = ' + TG[cur].svg);
    [[480, 260], [560, 160], [430, 160]].forEach(([x, y]) => el('circle', { cx: x, cy: y, r: 5, fill: '#ccc' }, svg));
    dots = LEFT.map(([x, y], i) => {
      const yes = y < 160;
      const c = el('circle', { cx: x, cy: y, r: 8, fill: yes ? '#2f9e44' : '#e03131', stroke: '#fff', 'stroke-width': 2 }, svg);
      const cl = el('circle', { cx: x, cy: y, r: 8, fill: yes ? '#2f9e44' : '#e03131', stroke: '#fff', 'stroke-width': 2, opacity: 0 }, svg);
      return { c, cl, x, y, tx: RIGHT[i][0], ty: RIGHT[i][1] };
    });
    $('redText').innerHTML = `<p style="margin:0 0 8px"><b>${bi(TG[cur].en, TG[cur].zh)}</b></p><p style="margin:0 0 8px">` + bi(TG[cur].ten, TG[cur].tzh) + '</p><p style="margin:0">' +
      bi('So <span class="m">HALT ≤ₘ B</span>, and a decider for B would decide HALT. Hence B is <b>undecidable</b>.', '所以 <span class="m">HALT ≤ₘ B</span>，B 的判定器能用来判定 HALT。因此 B <b>不可判定</b>。') + '</p>';
  }
  let rtok = 0;
  async function go() {
    const my = ++rtok;
    draw();
    dots.forEach(d => {
      el('path', { d: `M${d.x + 9},${d.y} C${325},${d.y - 30} ${325},${d.ty - 30} ${d.tx - 10},${d.ty}`, fill: 'none', stroke: '#ae3ec9', 'stroke-width': 1.3, 'stroke-dasharray': '4 4' }, svg);
      d.cl.setAttribute('opacity', 1);
      svg.appendChild(d.cl);
    });
    const N = 24;
    for (let k = 1; k <= N; k++) {
      await sleep(35);
      if (my !== rtok) return;
      const t = k / N, e = 1 - (1 - t) ** 3;
      dots.forEach(d => {
        d.cl.setAttribute('cx', d.x + (d.tx - d.x) * e);
        d.cl.setAttribute('cy', d.y + (d.ty - d.y) * e - Math.sin(Math.PI * t) * 40);
      });
    }
  }
  Object.entries(TG).forEach(([k, t]) => {
    const b = document.createElement('button');
    b.className = 'btn small';
    b.dataset.k = k;
    b.innerHTML = t.en.split(':')[0];
    b.addEventListener('click', () => { cur = k; go(); });
    $('redPick').appendChild(b);
  });
  $('redGo').addEventListener('click', go);
  draw();

  // Rice clusters
  const rs = $('riceSvg');
  const CL = [
    { x: 130, y: 82, en: '∅ (never halts)', zh: '处处无定义' }, { x: 370, y: 82, en: 'x ↦ 0', zh: '常数 0' }, { x: 610, y: 82, en: 'x ↦ x + 1', zh: '后继' },
    { x: 130, y: 212, en: 'x ↦ 2x', zh: '加倍' }, { x: 370, y: 212, en: 'halts iff x even', zh: '仅在偶数上停机' }, { x: 610, y: 212, en: 'x ↦ x²', zh: '平方' },
  ];
  const STATES = [[3, 9, 4, 14, 6], [2, 7, 11, 5, 3], [4, 12, 3, 8, 6], [9, 5, 13, 4, 7], [6, 3, 10, 5, 15], [12, 4, 8, 16, 7]];
  const OFF = [[-50, 8], [-18, 22], [14, 6], [44, 22], [-2, -6]];
  const sel = CL.map(() => false);
  let syn = false;
  const cls = CL.map((c, i) => {
    const g = el('g', { class: 'clu' }, rs);
    const e = el('ellipse', { cx: c.x, cy: c.y, rx: 114, ry: 54, fill: '#fff', stroke: '#9aa0aa', 'stroke-width': 2 }, g);
    txt(g, { x: c.x, y: c.y - 26, 'text-anchor': 'middle', 'font-size': 12.5, 'font-weight': 700 }, `${c.en} · ${c.zh}`);
    const ds = OFF.map(([dx, dy], k) => {
      const d = el('circle', { cx: c.x + dx, cy: c.y + dy + 8, r: 6, fill: '#3b5bdb', stroke: '#f08c00', 'stroke-width': 0, class: 'riceDot' }, g);
      d.dataset.st = STATES[i][k];
      return d;
    });
    g.addEventListener('click', () => { sel[i] = !sel[i]; render(); });
    return { e, ds };
  });
  txt(rs, { x: 370, y: 290, 'text-anchor': 'middle', 'font-size': 12, fill: '#777' }, '… and infinitely many other partial functions · 还有无穷多个其他部分函数 …');
  function render() {
    cls.forEach((c, i) => {
      c.e.setAttribute('fill', sel[i] ? '#f8e7fc' : '#fff');
      c.e.setAttribute('stroke', sel[i] ? '#ae3ec9' : '#9aa0aa');
      c.ds.forEach(d => { const on = syn && +d.dataset.st <= 5; d.setAttribute('stroke-width', on ? 4 : 0); d.setAttribute('r', on ? 7 : 6); });
    });
    const k = sel.filter(Boolean).length;
    if (syn) {
      $('riceMsg').innerHTML = bi('Gold-ringed programs have at most 5 states. This property splits clouds: two programs computing the <i>same</i> function can disagree on it. It is <b>syntactic</b>, not semantic, so Rice says nothing, and indeed it is decidable: just count the states in the code.',
        '金圈标出的是状态数 ≤ 5 的程序。这个性质会把同一朵云劈开：计算<i>同一个</i>函数的两个程序，可能一个有一个没有。它是<b>语法</b>性质而非语义性质，莱斯定理管不着；事实上它可判定：数一数代码里的状态就行。') +
        (k ? bi(' (Clouds you selected stay purple.)', '（你选中的云仍以紫色显示。）') : '');
      return;
    }
    if (!k) $('riceMsg').innerHTML = bi('P = ∅: no program has it. A <b>trivial</b> property, decided by the machine that always answers “no”. Click clouds to build a non-trivial property.',
      'P = ∅：没有程序具有它。这是<b>平凡</b>性质，由永远回答“否”的机器判定。点击云朵来构造非平凡性质。');
    else {
      const names = CL.filter((c, i) => sel[i]).map(c => c.en).join(', ');
      $('riceMsg').innerHTML = bi(`P = “the program computes one of: ${names}”. It contains whole clouds, so it is semantic, and it is non-trivial (some program has it, some doesn't). By Rice's theorem, <b>{e : Mₑ has P} is undecidable</b>.`,
        `P =“程序计算的是：${names} 之一”。它由整朵云组成，所以是语义性质；而且非平凡（有的程序有，有的没有）。由莱斯定理，<b>{e : Mₑ 具有 P} 不可判定</b>。`) +
        (sel[0] ? bi(' Since ∅ ∈ P, the proof below is applied to the complement of P.', '由于 ∅ ∈ P，下面的证明要用在 P 的补集上。') : '');
    }
  }
  $('riceSyn').addEventListener('click', () => { syn = !syn; $('riceSyn').classList.toggle('sel', syn); render(); });
  $('riceClear').addEventListener('click', () => { sel.fill(false); syn = false; $('riceSyn').classList.remove('sel'); render(); });
  render();
  stepper('#riceSteps', 'riceNext', 'riceAll');
})();

/* ================= shared: multiple-choice rows ================= */
function choiceRows(box, items, opts, progId, defHint = ['', '']) {
  const solved = items.map(() => false), revealed = items.map(() => false);
  items.forEach((it, i) => {
    const row = document.createElement('div');
    row.className = 'tf';
    row.innerHTML = `<div class="stmt" style="font-family:var(--sans);font-size:15px">${it.en === it.zh ? it.en : bi(it.en, it.zh)}</div><div class="cls"></div>
      <div style="flex-basis:100%"><div class="msg"></div></div>`;
    const cl = row.querySelector('.cls'), msg = row.querySelector('.msg');
    const btns = [];
    const answer = show => {
      btns.forEach(b => b.classList.remove('right', 'wrongc'));
      btns.find(b => b.dataset.v === it.a).classList.add('right');
      okBox(msg, (show ? '' : '✓ ') + bi(it.wen, it.wzh), show ? 'info' : 'ok');
    };
    opts.forEach(([v, en, zh]) => {
      const b = document.createElement('button');
      b.className = 'btn small choice';
      b.style.width = 'auto';
      b.dataset.v = v;
      b.innerHTML = bil(en, zh);
      b.addEventListener('click', () => {
        if (v === it.a) {
          answer(false);
          if (!revealed[i]) solved[i] = true;
          if (solved.every(Boolean)) Progress.mark(progId);
        } else {
          btns.forEach(x => x.classList.remove('right', 'wrongc'));
          b.classList.add('wrongc');
          okBox(msg, bi('✗ Not quite. ' + (it.hen || defHint[0]), '✗ 不对。' + (it.hzh || defHint[1])), 'bad');
        }
      });
      btns.push(b);
      cl.appendChild(b);
    });
    const sb = document.createElement('button');
    sb.className = 'btn small ghost';
    sb.innerHTML = bil('Show answer', '看答案');
    sb.addEventListener('click', () => { revealed[i] = true; answer(true); });
    cl.appendChild(sb);
    box.appendChild(row);
  });
}

/* ================= E1 design a TM ================= */
(function e1() {
  const flip = w => [...w].map(c => c === '0' ? '1' : '0').join('');
  const TASKS = {
    flip: { en: 'Flip bits', zh: '按位取反',
      den: 'Input: a binary string. Output: the same string with every bit flipped (0 ↔ 1), e.g. 0110 ↦ 1001. Halt in any state.', dzh: '输入：一个二进制串。输出：每一位都取反（0 ↔ 1）后的串，例如 0110 ↦ 1001。停在哪个状态都行。',
      tests: ['', '0', '1', '0110', '111000', '10101'], check: (w, cfg) => TMCore.content(cfg) === flip(w), exp: w => flip(w) || 'ε',
      got: cfg => TMCore.content(cfg) || 'ε',
      start: '# flip every bit\nq0 0 -> q0 1 R\n',
      sol: '# flip every bit, halt at the first blank\nq0 0 -> q0 1 R\nq0 1 -> q0 0 R' },
    parity: { en: 'Even number of 1s', zh: '1 的个数为偶数',
      den: 'Input: a binary string. Halt in state <span class="m">acc</span> if it contains an even number of 1s, and in state <span class="m">rej</span> otherwise. (Two states are enough to remember the parity.)', dzh: '输入：一个二进制串。若其中 1 的个数为偶数，停在状态 <span class="m">acc</span>，否则停在状态 <span class="m">rej</span>。（记住奇偶性只需要两个状态。）',
      tests: ['', '0', '1', '11', '101', '1101', '0000', '111', '0110110'], check: (w, cfg) => cfg.state === ([...w].filter(c => c === '1').length % 2 ? 'rej' : 'acc'),
      exp: w => [...w].filter(c => c === '1').length % 2 ? 'rej' : 'acc', got: cfg => cfg.state,
      start: '# remember the parity in the state\neven 0 -> even 0 R\n',
      sol: '# the state remembers the parity read so far\neven 0 -> even 0 R\neven 1 -> odd 1 R\nodd 0 -> odd 0 R\nodd 1 -> even 1 R\neven _ -> acc _ N\nodd _ -> rej _ N' },
  };
  let cur = 'flip';
  const drafts = {};
  const revealed = {};
  let started = false;
  function choose(k) {
    if (started) drafts[cur] = $('e1Text').value;
    started = true;
    cur = k;
    document.querySelectorAll('#e1Tasks button').forEach(b => b.classList.toggle('sel', b.dataset.k === k));
    $('e1Desc').innerHTML = bi(TASKS[k].den, TASKS[k].dzh);
    $('e1Text').value = drafts[k] ?? TASKS[k].start;
    $('e1Res').innerHTML = '';
    clearBox($('e1Msg'));
  }
  Object.entries(TASKS).forEach(([k, t]) => {
    const b = document.createElement('button');
    b.className = 'btn small';
    b.dataset.k = k;
    b.innerHTML = bil(t.en, t.zh);
    b.addEventListener('click', () => choose(k));
    $('e1Tasks').appendChild(b);
  });
  function test() {
    const T = TASKS[cur];
    const M = TMCore.parse($('e1Text').value);
    if (M.errors.length || !M.order.length) { okBox($('e1Msg'), M.order.length ? errHtml(M.errors) : bi('The table is empty.', '转移表是空的。'), 'bad'); $('e1Res').innerHTML = ''; return; }
    let pass = 0;
    let h = `<table class="res"><tr><th>${bil('input', '输入')}</th><th>${bil('expected', '期望')}</th><th>${bil('your machine', '你的机器')}</th><th>${bil('steps', '步数')}</th><th></th></tr>`;
    T.tests.forEach(w => {
      const cfg = TMCore.run(M, w, 2000);
      const ok = cfg.halted && T.check(w, cfg);
      if (ok) pass++;
      h += `<tr><td>${w || 'ε'}</td><td>${T.exp(w)}</td><td>${cfg.halted ? T.got(cfg) : bil('no halt in 2000 steps', '2000 步未停机')}</td><td>${cfg.steps}</td><td class="${ok ? 'okc' : 'badc'}">${ok ? '✓' : '✗'}</td></tr>`;
    });
    $('e1Res').innerHTML = h + '</table>';
    if (pass === T.tests.length) {
      okBox($('e1Msg'), bi(`✓ All ${pass} tests pass. Load your table into §1 to watch it run.`, `✓ ${pass} 个测试全部通过。可以把转移表贴到 §1 里看它运行。`));
      if (!revealed[cur]) Progress.mark('L11E1');
    } else okBox($('e1Msg'), bi(`${pass} / ${T.tests.length} tests pass. Remember: the machine halts as soon as no rule matches (state, symbol).`, `通过 ${pass} / ${T.tests.length} 个测试。记住：一旦没有规则匹配（状态, 符号），机器就停机。`), 'warn');
  }
  $('e1Run').addEventListener('click', test);
  $('e1Show').addEventListener('click', () => { $('e1Text').value = TASKS[cur].sol; revealed[cur] = true; test(); });
  choose('flip');
})();

/* ================= E2 trace ================= */
(function e2() {
  const M = TMCore.parse(PRESETS.binc.text);
  $('e2Table').textContent = M.order.map(o => `${o.q} ${o.r} -> ${o.n} ${o.w} ${o.m}`).join('\n');
  const fin = TMCore.run(M, '1011');
  const want = { tape: TMCore.content(fin), steps: fin.steps };
  let revealed = false;
  function trace() {
    const cfg = TMCore.init(M, '1011');
    const rows = [];
    const snap = () => {
      const ks = [...cfg.tape.keys(), cfg.head];
      const lo = Math.min(...ks, 0), hi = Math.max(...ks, 4);
      let s = '';
      for (let i = lo; i <= hi; i++) { const c = TMCore.read(cfg, i); s += i === cfg.head ? `<b style="color:#ae3ec9">[${c}]</b>` : ` ${c} `; }
      rows.push(`<tr><td>${cfg.steps}</td><td>${cfg.state}</td><td style="text-align:left;white-space:pre">${s}</td></tr>`);
    };
    snap();
    while (!cfg.halted) { TMCore.step(M, cfg); snap(); }
    $('e2Trace').innerHTML = `<table class="res"><tr><th>${bil('step', '步')}</th><th>${bil('state', '状态')}</th><th>${bil('tape ([ ] = head)', '带（[ ] 为读写头）')}</th></tr>${rows.join('')}</table>`;
  }
  $('e2Check').addEventListener('click', () => {
    const t = $('e2Tape').value.replace(/[\s_]/g, ''), s = parseInt($('e2Steps').value, 10);
    const okT = t === want.tape, okS = s === want.steps;
    if (okT && okS) {
      okBox($('e2Msg'), bi(`✓ Right: 1011 + 1 = 1100 (11 + 1 = 12), in ${want.steps} steps: 4 moving right, 1 turning back at the blank, 2 carries, 1 final write.`, `✓ 正确：1011 + 1 = 1100（11 + 1 = 12），共 ${want.steps} 步：右移 4 步，遇空格回头 1 步，进位 2 步，最后写入 1 步。`));
      trace();
      if (!revealed) Progress.mark('L11E2');
    } else okBox($('e2Msg'), bi(`${okT ? '✓ tape' : '✗ tape'} · ${okS ? '✓ steps' : '✗ steps'}. Hint: the step that reads the blank at the right end and turns around counts too.`, `${okT ? '✓ 带内容' : '✗ 带内容'} · ${okS ? '✓ 步数' : '✗ 步数'}。提示：在右端读到空格、掉头的那一步也算。`), 'bad');
  });
  $('e2Show').addEventListener('click', () => {
    revealed = true;
    okBox($('e2Msg'), bi(`Final tape <b>${want.tape}</b>, <b>${want.steps}</b> steps. Full trace:`, `最终带内容 <b>${want.tape}</b>，共 <b>${want.steps}</b> 步。完整轨迹：`), 'info');
    trace();
  });
})();

/* ================= E3 classify ================= */
choiceRows($('e3List'), [
  { en: '{e : Mₑ halts on input 0 within 10⁶ steps}', zh: '{e : Mₑ 在输入 0 上 10⁶ 步之内停机}', a: 'dec',
    wen: 'Decidable: simulate for 10⁶ steps and look.', wzh: '可判定：模拟 10⁶ 步看结果即可。', hen: 'Is there a bound on the work?', hzh: '工作量有没有上界？' },
  { en: '{e : Mₑ halts on input 0}', zh: '{e : Mₑ 在输入 0 上停机}', a: 're',
    wen: 'r.e. (run it and wait), and undecidable: K reduces to it, since e ↦ “ignore input, run Mₑ(e)”.', wzh: '递归可枚举（运行并等待），且不可判定：K 可归约到它，e ↦“忽略输入，运行 Mₑ(e)”。', hen: 'You can confirm “yes” by waiting. Can you ever confirm “no”?', hzh: '“是”可以靠等待来确认。“否”能确认吗？' },
  { en: '{e : Wₑ = ∅}, i.e. Mₑ halts on no input', zh: '{e : Wₑ = ∅}，即 Mₑ 在任何输入上都不停机', a: 'core',
    wen: 'co-r.e.: its complement “Mₑ halts on some input” is r.e. by dovetailing over (input, time). Undecidable by Rice.', wzh: '余递归可枚举：它的补集“Mₑ 在某个输入上停机”可以对（输入, 时间）交错运行而枚举。由莱斯定理不可判定。', hen: 'Look at the complement.', hzh: '看看它的补集。' },
  { en: 'TOT = {e : Mₑ halts on every input}', zh: 'TOT = {e : Mₑ 在每个输入上都停机}', a: 'nei',
    wen: 'Neither: “∀x ∃t (Mₑ(x) halts by time t)” needs two alternating unbounded quantifiers; TOT is Π₂-complete.', wzh: '都不是：“∀x ∃t（Mₑ(x) 在 t 步内停机）”需要两层交替的无界量词；TOT 是 Π₂ 完全的。', hen: 'Count the unbounded quantifiers: ∀x ∃t …', hzh: '数一数无界量词：∀x ∃t …' },
  { en: '{(a, b, c) ∈ ℕ³ : a · b = c}', zh: '{(a, b, c) ∈ ℕ³ : a · b = c}', a: 'dec',
    wen: 'Decidable: multiply and compare (it is even primitive recursive).', wzh: '可判定：乘一下再比较（甚至是原始递归的）。' },
  { en: 'polynomials p ∈ ℤ[x₁,…,xₙ] with an integer root', zh: '有整数根的多项式 p ∈ ℤ[x₁,…,xₙ]', a: 're',
    wen: 'r.e. (search all integer tuples); undecidable by the MRDP theorem (Hilbert\'s 10th problem).', wzh: '递归可枚举（搜索所有整数组）；由 MRDP 定理（希尔伯特第十问题）不可判定。' },
  { en: 'first-order sentences that are <i>not</i> valid', zh: '<i>不</i>普遍有效的一阶语句', a: 'core',
    wen: 'co-r.e.: the valid sentences are r.e. by the completeness theorem (enumerate proofs), and undecidable by Church\'s theorem (for a language with at least one binary relation symbol).', wzh: '余递归可枚举：由完备性定理，普遍有效语句递归可枚举（枚举证明）；由丘奇定理不可判定（语言中至少有一个二元关系符号时）。', hen: 'What does Gödel\'s completeness theorem say about the valid ones?', hzh: '哥德尔完备性定理对普遍有效语句说了什么？' },
  { en: '{e : Wₑ is finite}', zh: '{e : Wₑ 是有限集}', a: 'nei',
    wen: 'Neither: “∃n ∀x > n, Mₑ(x)↑” has alternating quantifiers; FIN is Σ₂-complete.', wzh: '都不是：“∃n ∀x > n，Mₑ(x)↑”含交替量词；FIN 是 Σ₂ 完全的。', hen: '∃n ∀x … : two alternating quantifiers.', hzh: '∃n ∀x …：两层交替量词。' },
], [['dec', 'decidable', '可判定'], ['re', 'r.e.', '递归可枚举'], ['core', 'co-r.e.', '余递归可枚举'], ['nei', 'neither', '都不是']], 'L11E3',
  ['Can a “yes” be confirmed by a finite search? Can a “no”?', '“是”能否靠有限搜索来确认？“否”呢？']);

/* ================= E4 order ================= */
(function e4() {
  const STEPS = [
    ['Assume some machine H decides HALT: it always halts, and H(e, x) = 1 iff Mₑ(x)↓.', '假设某台机器 H 判定 HALT：它总会停机，且 H(e, x) = 1 当且仅当 Mₑ(x)↓。'],
    ['Build D: on input e, run H(e, e); if the answer is 1, loop forever, otherwise halt.', '构造 D：输入 e 时运行 H(e, e)；若答案为 1 就死循环，否则停机。'],
    ['D is a Turing machine, so D = M<sub>d</sub> for some code d.', 'D 是图灵机，所以对某个编码 d 有 D = M<sub>d</sub>。'],
    ['Feed D its own code: does D(d) halt?', '把 D 自己的编码喂给它：D(d) 停机吗？'],
    ['D(d)↓ ⇔ H(d, d) = 0 ⇔ M<sub>d</sub>(d)↑ ⇔ D(d)↑.', 'D(d)↓ ⇔ H(d, d) = 0 ⇔ M<sub>d</sub>(d)↑ ⇔ D(d)↑。'],
    ['Contradiction, so no such H exists: HALT is undecidable.', '矛盾，所以这样的 H 不存在：HALT 不可判定。'],
  ];
  const perm = [3, 0, 5, 2, 4, 1];
  let placed = [], revealed = false;
  function render() {
    const pool = $('e4Pool'), list = $('e4List');
    pool.innerHTML = ''; list.innerHTML = '';
    perm.filter(i => !placed.includes(i)).forEach(i => {
      const c = document.createElement('div');
      c.className = 'chip';
      c.innerHTML = bi(STEPS[i][0], STEPS[i][1]);
      c.addEventListener('click', () => { placed.push(i); render(); clearBox($('e4Msg')); });
      pool.appendChild(c);
    });
    placed.forEach((i, k) => {
      const c = document.createElement('div');
      c.className = 'chip';
      c.innerHTML = `<span class="num">${k + 1}.</span>` + bi(STEPS[i][0], STEPS[i][1]);
      c.addEventListener('click', () => { placed = placed.filter(x => x !== i); render(); clearBox($('e4Msg')); });
      list.appendChild(c);
    });
    if (!placed.length) list.innerHTML = `<span class="muted">${bil('click steps on the left', '点击左边的步骤')}</span>`;
  }
  function check(show) {
    if (show) { placed = [0, 1, 2, 3, 4, 5]; revealed = true; }
    render();
    const chips = $('e4List').querySelectorAll('.chip');
    let ok = 0;
    placed.forEach((i, k) => { const r = i === k; if (r) ok++; chips[k].classList.add(r ? 'ok' : 'no'); });
    if (show) { okBox($('e4Msg'), bi('The correct order: assume H, build D, D gets a code, self-application, the two-way equivalence, contradiction.', '正确顺序：假设 H，构造 D，D 获得编码，自我应用，双向等价，矛盾。'), 'info'); return; }
    if (ok === 6) { okBox($('e4Msg'), bi('✓ Exactly the structure of Cantor\'s proof: assume a complete list, build the diagonal object, locate it in the list, and evaluate it at its own index.', '✓ 和康托尔的证明结构完全一样：假设一份完整清单，构造对角对象，在清单里找它，再在它自己的编号处求值。')); if (!revealed) Progress.mark('L11E4'); }
    else okBox($('e4Msg'), bi(`${ok} / 6 in the right place${placed.length < 6 ? ' (not all steps placed yet)' : ''}. D can only get a code after it has been built.`, `${ok} / 6 个位置正确${placed.length < 6 ? '（还有步骤没放）' : ''}。D 要先造出来，才谈得上有编码。`), 'warn');
  }
  $('e4Check').addEventListener('click', () => check(false));
  $('e4Show').addEventListener('click', () => check(true));
  render();
})();

/* ================= E5 Rice ================= */
choiceRows($('e5List'), [
  { en: 'M has at most 10 states.', zh: 'M 至多有 10 个状态。', a: 'd',
    wen: 'Decidable: a property of the code, not of the function. Rice does not apply.', wzh: '可判定：这是代码的性质，不是函数的性质。莱斯定理不适用。', hen: 'Is this about what M computes, or about how M is written?', hzh: '这说的是 M 算什么，还是 M 怎么写的？' },
  { en: 'M halts on every input.', zh: 'M 在每个输入上都停机。', a: 'u',
    wen: 'Undecidable (Rice): “φ<sub>M</sub> is total” is semantic and non-trivial.', wzh: '不可判定（莱斯）：“φ<sub>M</sub> 是全函数”是非平凡的语义性质。' },
  { en: 'φ<sub>M</sub>(3) = 5.', zh: 'φ<sub>M</sub>(3) = 5。', a: 'u',
    wen: 'Undecidable (Rice): it depends only on φ<sub>M</sub>, and some programs have it while others don\'t.', wzh: '不可判定（莱斯）：它只依赖于 φ<sub>M</sub>，且有的程序具有、有的不具有。' },
  { en: 'M halts on the blank tape within 100 steps.', zh: 'M 在空白带上 100 步之内停机。', a: 'd',
    wen: 'Decidable: run 100 steps. (Not semantic either: padding M with useless steps changes the answer but not φ<sub>M</sub>.)', wzh: '可判定：跑 100 步就知道。（它也不是语义性质：给 M 塞一些无用步骤会改变答案，却不改变 φ<sub>M</sub>。）', hen: 'There is a time bound.', hzh: '有时间上界。' },
  { en: 'The set of inputs on which M halts is finite.', zh: 'M 停机的输入集合是有限集。', a: 'u',
    wen: 'Undecidable (Rice): it is a property of W<sub>M</sub> = dom φ<sub>M</sub>, so semantic, and non-trivial.', wzh: '不可判定（莱斯）：这是 W<sub>M</sub> = dom φ<sub>M</sub> 的性质，所以是语义的，而且非平凡。' },
  { en: 'M\'s table contains a rule that moves left.', zh: 'M 的转移表里有一条左移规则。', a: 'd',
    wen: 'Decidable: read the table.', wzh: '可判定：读一遍转移表即可。' },
  { en: 'M computes the same partial function as the unary-increment machine of §1.', zh: 'M 计算的部分函数与 §1 的一进制加一机器相同。', a: 'u',
    wen: 'Undecidable (Rice): “φ<sub>M</sub> = x ↦ x + 1” is a single cloud, which is non-trivial. So program equivalence is undecidable.', wzh: '不可判定（莱斯）：“φ<sub>M</sub> = x ↦ x + 1”只是一朵云，非平凡。所以程序等价性不可判定。' },
], [['d', 'decidable', '可判定'], ['u', 'undecidable', '不可判定']], 'L11E5',
  ['Does the property depend only on the function φ_M computed, and is it non-trivial? Or is it about the code, or a bounded run?'.replace('φ_M', 'φ<sub>M</sub>'), '这个性质是否只依赖于 M 计算的函数 φ<sub>M</sub>，并且非平凡？还是说它关乎代码本身，或只是有界步数的运行？']);

/* ================= E6 exp by primitive recursion ================= */
(function e6() {
  function parseExpr(s, allowed) {
    const toks = s.replace(/\s+/g, '').match(/\d+|[A-Za-z]+|[()+*,]|./g) || [];
    let i = 0;
    const fail = (en, zh) => { throw { en, zh }; };
    const peek = () => toks[i];
    const eat = t => { if (toks[i] !== t) fail(`expected “${t}”`, `此处应为“${t}”`); i++; };
    function E() { let a = Tm(); while (peek() === '+') { i++; const b = Tm(), aa = a; a = env => aa(env) + b(env); } return a; }
    function Tm() { let a = F(); while (peek() === '*') { i++; const b = F(), aa = a; a = env => aa(env) * b(env); } return a; }
    function F() {
      const t = peek();
      if (t === undefined) fail('expression ends too early', '表达式不完整');
      i++;
      if (/^\d+$/.test(t)) { const v = +t; return () => v; }
      if (t === '(') { const a = E(); eat(')'); return a; }
      if (t === '^') fail('“^” is not allowed: that is what you are defining', '不准用“^”：这正是你要定义的东西');
      if (['x', 'y', 'r'].includes(t)) { if (!allowed.includes(t)) fail(`“${t}” is not available here`, `这里不能用“${t}”`); return env => env[t]; }
      if (t === 'S') { eat('('); const a = E(); eat(')'); return env => a(env) + 1; }
      if (t === 'add' || t === 'mult') { eat('('); const a = E(); eat(','); const b = E(); eat(')'); return t === 'add' ? env => a(env) + b(env) : env => a(env) * b(env); }
      fail(`unknown symbol “${t}”`, `无法识别的符号“${t}”`);
    }
    const f = E();
    if (i < toks.length) fail(`unexpected “${toks[i]}”`, `多余的“${toks[i]}”`);
    return f;
  }
  let revealed = false;
  function check(fromShow) {
    let g, h;
    try { g = parseExpr($('e6Base').value, ['x']); h = parseExpr($('e6Step').value, ['x', 'y', 'r']); }
    catch (e) { okBox($('e6Msg'), bi('Syntax: ' + (e.en || e), '语法：' + (e.zh || e)), 'bad'); $('e6Grid').innerHTML = ''; return; }
    let ok = 0;
    let t = `<table class="res"><tr><th>x \\ y</th>${[0, 1, 2, 3, 4].map(y => `<th>${y}</th>`).join('')}</tr>`;
    for (let x = 0; x <= 4; x++) {
      t += `<tr><th>${x}</th>`;
      let r = g({ x, y: 0 });
      for (let y = 0; y <= 4; y++) {
        if (y > 0) r = h({ x, y: y - 1, r });
        const want = x ** y, good = r === want;
        if (good) ok++;
        t += `<td class="${good ? 'okc' : 'badc'}">${r}${good ? '' : ` <span class="muted">(${want})</span>`}</td>`;
      }
      t += '</tr>';
    }
    $('e6Grid').innerHTML = t + '</table>';
    if (ok === 25) {
      okBox($('e6Msg'), bi('✓ All 25 values match xʸ. As a tree: exp = Rec(S∘Z, mult∘(P³₃, P³₁)), which is exactly the tree in §2.', '✓ 25 个值全部等于 xʸ。写成构造树就是 exp = Rec(S∘Z, mult∘(P³₃, P³₁))，正是 §2 中的那棵树。'), fromShow ? 'info' : 'ok');
      if (!fromShow && !revealed) Progress.mark('L11E6');
    } else okBox($('e6Msg'), bi(`${ok} / 25 values correct (expected value in parentheses). What is x⁰? How do you get xʸ⁺¹ from xʸ?`, `${ok} / 25 个值正确（括号内为应有的值）。x⁰ 等于几？怎样由 xʸ 得到 xʸ⁺¹？`), 'warn');
  }
  $('e6Check').addEventListener('click', () => check(false));
  $('e6Show').addEventListener('click', () => { $('e6Base').value = '1'; $('e6Step').value = 'mult(r, x)'; revealed = true; check(true); });
})();
}
