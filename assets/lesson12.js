// Lesson 12: Gödel's incompleteness theorems.
// Pure logic first (testable in node), DOM code afterwards.

/* ================= Gödel numbering (BigInt) ================= */
const GSYM = [['0', 1], ['S', 2], ['+', 3], ['×', 4], ['=', 5], ['(', 6], [')', 7], ['¬', 8], ['∧', 9], ['∨', 10],
  ['→', 11], ['∀', 12], ['∃', 13], ['x', 14], ['y', 15], ['z', 16]];
const GCODE = Object.fromEntries(GSYM);
const GSYMOF = Object.fromEntries(GSYM.map(([s, c]) => [c, s]));

class GErr extends Error {
  constructor(en, zh) { super(en); this.en = en; this.zh = zh; }
}

const PRIMES = (() => {
  const N = 2000, sieve = new Uint8Array(N + 1), out = [];
  for (let i = 2; i <= N; i++) {
    if (sieve[i]) continue;
    out.push(i);
    for (let j = i * i; j <= N; j += i) sieve[j] = 1;
  }
  return out;
})();

// Normalise ASCII aliases and split into symbols.
function gTokens(str) {
  const s = str.replace(/->/g, '→').replace(/\*/g, '×').replace(/[~!]/g, '¬').replace(/A/g, '∀')
    .replace(/E/g, '∃').replace(/&/g, '∧').replace(/\|/g, '∨').replace(/\s+/g, '');
  const out = [];
  [...s].forEach((c, i) => {
    if (!(c in GCODE)) throw new GErr(`Symbol “${c}” is not in the code table`, `符号“${c}”不在代码表中`);
    out.push(c);
  });
  return out;
}
function gEncode(syms) {
  let n = 1n;
  syms.forEach((c, i) => { n *= BigInt(PRIMES[i]) ** BigInt(GCODE[c]); });
  return n;
}
const gEncodeStr = str => gEncode(gTokens(str));

// Decode by peeling consecutive primes. Returns {ok, steps:[{p,e,rest}], syms, err}
function gDecode(n) {
  const steps = [], syms = [];
  if (typeof n !== 'bigint') n = BigInt(n);
  if (n < 1n) return { ok: false, steps, syms, err: ['0 and negative numbers code nothing.', '0 和负数不编码任何东西。'] };
  let i = 0;
  while (n > 1n) {
    if (i >= PRIMES.length) return { ok: false, steps, syms, err: ['Too long for this demo.', '对本演示来说太长了。'] };
    const p = BigInt(PRIMES[i]);
    let e = 0;
    while (n % p === 0n) { n /= p; e++; }
    steps.push({ p: PRIMES[i], e, rest: n });
    if (e === 0) return { ok: false, steps, syms, err: [`The prime ${PRIMES[i]} does not divide the rest, yet the rest is not 1: a skipped prime. Every symbol has code ≥ 1, so this is not the code of a string.`,
      `素数 ${PRIMES[i]} 不整除剩下的部分，而剩下的部分又不是 1：中间跳过了一个素数。每个符号的代码都 ≥ 1，所以它不是任何符号串的编码。`] };
    if (!(e in GSYMOF)) return { ok: false, steps, syms, err: [`Exponent ${e} is not the code of any symbol.`, `指数 ${e} 不是任何符号的代码。`] };
    syms.push(GSYMOF[e]);
    i++;
  }
  return { ok: true, steps, syms };
}
// approximate log10 of a BigInt
function log10Big(n) {
  const s = n.toString();
  const head = s.slice(0, 15);
  return Math.log10(Number(head)) + (s.length - head.length);
}

/* ================= closed terms of arithmetic ================= */
// AST: {k:'0'} | {k:'S',a} | {k:'+',a,b} | {k:'×',a,b}
const Z = { k: '0' };
const mkS = a => ({ k: 'S', a });
const mkOp = (k, a, b) => ({ k, a, b });
const numeral = n => { let t = Z; for (let i = 0; i < n; i++) t = mkS(t); return t; };
function numVal(t) { let n = 0; while (t.k === 'S') { n++; t = t.a; } return t.k === '0' ? n : null; }

function parseTerm(str) {
  const s = str.replace(/\*/g, '×').replace(/\s+/g, '');
  let i = 0;
  const fail = (en, zh) => { throw new GErr(en, zh); };
  function sum() {
    let a = prod();
    while (s[i] === '+') { i++; a = mkOp('+', a, prod()); }
    return a;
  }
  function prod() {
    let a = un();
    while (s[i] === '×') { i++; a = mkOp('×', a, un()); }
    return a;
  }
  function un() {
    const c = s[i];
    if (c === 'S') { i++; return mkS(un()); }
    if (c === '0') { i++; return Z; }
    if (c === '(') { i++; const a = sum(); if (s[i] !== ')') fail('Missing “)”', '缺少“)”'); i++; return a; }
    fail(c === undefined ? 'Term ends too early' : `Unexpected “${c}”`, c === undefined ? '项不完整' : `此处不应出现“${c}”`);
  }
  const t = sum();
  if (i < s.length) fail(`Extra symbols “${s.slice(i)}”`, `多余的符号“${s.slice(i)}”`);
  return t;
}
function parseEq(str) {
  const parts = str.split('=');
  if (parts.length !== 2) throw new GErr('A line must be one equation “s = t”', '每一行必须是一个等式“s = t”');
  return { l: parseTerm(parts[0]), r: parseTerm(parts[1]) };
}
function showT(t, hl) {
  let s;
  if (t.k === '0') s = '0';
  else if (t.k === 'S') s = 'S' + (t.a.k === '+' || t.a.k === '×' ? '(' + showT(t.a, hl) + ')' : showT(t.a, hl));
  else if (t.k === '+') s = showT(t.a, hl) + '+' + (t.b.k === '+' ? '(' + showT(t.b, hl) + ')' : showT(t.b, hl));
  else s = (t.a.k === '+' ? '(' + showT(t.a, hl) + ')' : showT(t.a, hl)) + '×' + (t.b.k === '0' || t.b.k === 'S' ? showT(t.b, hl) : '(' + showT(t.b, hl) + ')');
  return hl && t === hl ? `<span class="redex">${s}</span>` : s;
}
function eqT(a, b) {
  if (a.k !== b.k) return false;
  if (a.k === '0') return true;
  if (a.k === 'S') return eqT(a.a, b.a);
  return eqT(a.a, b.a) && eqT(a.b, b.b);
}
// all terms obtained from v by replacing exactly one occurrence of s by t
function replaceOne(v, s, t) {
  const out = [];
  if (eqT(v, s)) out.push(t);
  if (v.k === 'S') replaceOne(v.a, s, t).forEach(x => out.push(mkS(x)));
  if (v.k === '+' || v.k === '×') {
    replaceOne(v.a, s, t).forEach(x => out.push(mkOp(v.k, x, v.b)));
    replaceOne(v.b, s, t).forEach(x => out.push(mkOp(v.k, v.a, x)));
  }
  return out;
}
// Leftmost-innermost redex for Q3–Q6.
function findRedex(t) {
  if (t.k === 'S') { const r = findRedex(t.a); if (r) return { ...r, rebuild: x => mkS(r.rebuild(x)) }; }
  if (t.k === '+' || t.k === '×') {
    const ra = findRedex(t.a);
    if (ra) return { ...ra, rebuild: x => mkOp(t.k, ra.rebuild(x), t.b) };
    const rb = findRedex(t.b);
    if (rb) return { ...rb, rebuild: x => mkOp(t.k, t.a, rb.rebuild(x)) };
  }
  const id = x => x;
  if (t.k === '+' && t.b.k === '0') return { node: t, rule: 'Q3', res: t.a, rebuild: id };
  if (t.k === '+' && t.b.k === 'S') return { node: t, rule: 'Q4', res: mkS(mkOp('+', t.a, t.b.a)), rebuild: id };
  if (t.k === '×' && t.b.k === '0') return { node: t, rule: 'Q5', res: Z, rebuild: id };
  if (t.k === '×' && t.b.k === 'S') return { node: t, rule: 'Q6', res: mkOp('+', mkOp('×', t.a, t.b.a), t.a), rebuild: id };
  return null;
}
function rewriteChain(t) {
  const out = [];
  let guard = 0;
  for (;;) {
    const r = findRedex(t);
    if (!r || guard++ > 400) { out.push({ t, rule: null, node: null }); break; }
    out.push({ t, rule: r.rule, node: r.node });
    t = r.rebuild(r.res);
  }
  return out;
}

/* ================= toy proof checker ================= */
// lines: [{f:'S0+0=S0', j:'Q3'}]; returns per-line {ok, en, zh}
function checkProof(lines) {
  const res = [];
  const eqs = [];
  lines.forEach((ln, idx) => {
    let e;
    try { e = parseEq(ln.f); } catch (err) { res.push({ ok: false, en: 'Not a well-formed equation: ' + err.en, zh: '不是合式等式：' + err.zh }); eqs.push(null); return; }
    eqs.push(e);
    const j = ln.j.trim();
    const { l, r } = e;
    let m;
    if ((m = j.match(/^Q\s*([3-6])$/i))) {
      const q = +m[1];
      let ok = false;
      if (q === 3) ok = l.k === '+' && l.b.k === '0' && eqT(l.a, r);
      if (q === 4) ok = l.k === '+' && l.b.k === 'S' && r.k === 'S' && r.a.k === '+' && eqT(r.a.a, l.a) && eqT(r.a.b, l.b.a);
      if (q === 5) ok = l.k === '×' && l.b.k === '0' && r.k === '0';
      if (q === 6) ok = l.k === '×' && l.b.k === 'S' && r.k === '+' && r.a.k === '×' && eqT(r.a.a, l.a) && eqT(r.a.b, l.b.a) && eqT(r.b, l.a);
      const pat = { 3: 'a+0 = a', 4: 'a+Sb = S(a+b)', 5: 'a×0 = 0', 6: 'a×Sb = a×b+a' }[q];
      res.push(ok ? { ok, en: `instance of Q${q}: ${pat}`, zh: `Q${q} 的实例：${pat}` }
        : { ok, en: `not an instance of Q${q} (${pat})`, zh: `不是 Q${q}（${pat}）的实例` });
      return;
    }
    if ((m = j.match(/^Rw\s*(\d+)\s*,\s*(\d+)$/i))) {
      const a = +m[1] - 1, b = +m[2] - 1;
      if (a < 0 || b < 0 || a >= idx || b >= idx) { res.push({ ok: false, en: 'Rw may only cite earlier lines', zh: 'Rw 只能引用前面的行' }); return; }
      if (!res[a].ok || !res[b].ok) { res.push({ ok: false, en: 'cites a line that failed the check', zh: '引用了未通过检验的行' }); return; }
      const s = eqs[a], u = eqs[b];
      const ok = eqT(l, u.l) && replaceOne(u.r, s.l, s.r).some(x => eqT(x, r));
      res.push(ok ? { ok, en: `line ${b + 1} with ${showT(s.l)} ↦ ${showT(s.r)}`, zh: `第 ${b + 1} 行中把 ${showT(s.l)} 换成 ${showT(s.r)}` }
        : { ok, en: `does not arise from line ${b + 1} by one replacement ${showT(s.l)} ↦ ${showT(s.r)}`, zh: `无法由第 ${b + 1} 行经一次替换 ${showT(s.l)} ↦ ${showT(s.r)} 得到` });
      return;
    }
    res.push({ ok: false, en: 'unknown justification (use Q3–Q6 or Rw i,j)', zh: '无法识别的理由（请用 Q3–Q6 或 Rw i,j）' });
  });
  return res;
}

const PROOFS = {
  add: [['S0+S0=S(S0+0)', 'Q4'], ['S0+0=S0', 'Q3'], ['S0+S0=SS0', 'Rw 2,1']],
  mul: [['SS0×SS0=SS0×S0+SS0', 'Q6'], ['SS0×S0=SS0×0+SS0', 'Q6'], ['SS0×0=0', 'Q5'], ['SS0×S0=0+SS0', 'Rw 3,2'],
    ['SS0×SS0=0+SS0+SS0', 'Rw 4,1'], ['0+SS0=S(0+S0)', 'Q4'], ['0+S0=S(0+0)', 'Q4'], ['0+0=0', 'Q3'], ['0+S0=S0', 'Rw 8,7'],
    ['0+SS0=SS0', 'Rw 9,6'], ['SS0×SS0=SS0+SS0', 'Rw 10,5'], ['SS0+SS0=S(SS0+S0)', 'Q4'], ['SS0+S0=S(SS0+0)', 'Q4'],
    ['SS0+0=SS0', 'Q3'], ['SS0+S0=SSS0', 'Rw 14,13'], ['SS0+SS0=SSSS0', 'Rw 15,12'], ['SS0×SS0=SSSS0', 'Rw 16,11']],
  bad: [['S0+S0=S(S0+0)', 'Q4'], ['S0+0=S0', 'Q3'], ['S0+S0=SSS0', 'Rw 2,1']],
  fake: [['S0+0=0', 'Q3'], ['S0+S0=S(S0+0)', 'Q4'], ['S0+S0=S0', 'Rw 1,2']],
};

if (typeof module !== 'undefined') {
  module.exports = { gTokens, gEncode, gEncodeStr, gDecode, log10Big, parseTerm, parseEq, showT, eqT, replaceOne, rewriteChain, numeral, numVal, checkProof, PROOFS, PRIMES };
}

/* ======================================================================= */
/* ============================ DOM part ================================= */
/* ======================================================================= */
if (typeof document !== 'undefined') {
Lang.init();
Progress.paint();

const $ = id => document.getElementById(id);
const okBox = (box, html, kind = 'ok') => { box.className = 'msg ' + kind; box.innerHTML = html; };
const clearBox = box => { box.className = 'msg'; box.innerHTML = ''; };
const SUBD = '₀₁₂₃₄₅₆₇₈₉';
const subs = n => String(n).split('').map(d => SUBD[d] ?? d).join('');
const SUPD = '⁰¹²³⁴⁵⁶⁷⁸⁹';
const sups = n => String(n).split('').map(d => SUPD[d]).join('');
const errHtml = e => e && e.en ? bi(e.en, e.zh) : String(e);
const shortBig = n => { const s = n.toString(); return s.length <= 12 ? s : `${s[0]}.${s.slice(1, 3)}e${s.length - 1}`; };
const fmtBig = n => { const s = n.toString(); return s.length <= 60 ? s : s.slice(0, 28) + '…' + s.slice(-20); };

// bilingual SVG text: "English · 中文" with language-aware tspans
function svgBi(parent, attrs, en, zh) {
  const t = el('text', attrs, parent);
  const a = el('tspan', { class: 'en' }, t); a.textContent = en;
  const s = el('tspan', { class: 'bisep', fill: '#999' }, t); s.textContent = ' · ';
  const b = el('tspan', { class: 'zh' }, t); b.textContent = zh;
  return t;
}
// stacked bilingual SVG text: English line, Chinese line below
function svgBi2(parent, attrs, en, zh, dy = 16) {
  const st = attrs['font-size'] ? `font-size:${attrs['font-size']}px` : '';
  const a = el('text', { ...attrs, class: 'en', style: st }, parent); a.textContent = en;
  const b = el('text', { ...attrs, class: 'zh', y: +attrs.y + dy, style: st }, parent); b.textContent = zh;
  return [a, b];
}
function svgT(parent, attrs, txt) { const t = el('text', attrs, parent); t.textContent = txt; return t; }

// step reveal with "show all"
function stepper(stepsId, nextId, allId) {
  const steps = [...$(stepsId).querySelectorAll(':scope > .step')];
  let k = 0;
  const all = () => { steps.forEach(s => s.classList.add('on')); k = steps.length; $(nextId).disabled = true; };
  $(nextId).addEventListener('click', () => { if (k < steps.length) steps[k++].classList.add('on'); if (k === steps.length) $(nextId).disabled = true; });
  $(allId).addEventListener('click', all);
  return { all, steps };
}

// animated chain of implications
async function chain(box, links, instant) {
  const my = (box._tok = (box._tok || 0) + 1);
  box.innerHTML = '<div class="chain"></div>';
  const c = box.firstChild;
  for (let i = 0; i < links.length; i++) {
    if (i) { const a = document.createElement('div'); a.className = 'ar'; a.textContent = '⇓'; c.appendChild(a); }
    const d = document.createElement('div');
    d.className = 'lk ' + (links[i].k || '');
    d.innerHTML = links[i].h + (links[i].why ? `<div class="why">${links[i].why}</div>` : '');
    c.appendChild(d);
    if (!instant) { await sleep(650); if (box._tok !== my) return; }
  }
}

// true/false (or two-label) judgement list
function tfList(box, items, progId, opts = {}) {
  const L = opts.labels || [['True', '对'], ['False', '错']];
  if (opts.grid) { box.classList.add('cards'); box.style.gridTemplateColumns = 'repeat(auto-fill, minmax(260px, 1fr))'; }
  const solved = items.map(() => false), revealed = items.map(() => false);
  items.forEach((it, i) => {
    const row = document.createElement('div');
    row.className = opts.grid ? 'fcard myth' : 'tf';
    row.innerHTML = `<div class="stmt" style="font-family:var(--sans);font-size:15px${opts.grid ? ';flex-shrink:0' : ''}">${it.s}</div>
      <div class="btnrow" style="display:flex;gap:8px;flex-wrap:wrap"><button class="btn small" data-v="1">${bil(L[0][0], L[0][1])}</button>
      <button class="btn small" data-v="0">${bil(L[1][0], L[1][1])}</button>
      <button class="btn small ghost" data-v="show">${bil('Show answer', '看答案')}</button></div>
      <div style="flex-basis:100%"><div class="msg"></div></div>`;
    box.appendChild(row);
    const msg = row.querySelector('.msg');
    row.querySelectorAll('button').forEach(b => b.addEventListener('click', () => {
      const verdict = it.ans ? bi(`<b>${L[0][0]}.</b> `, `<b>${L[0][1]}。</b>`) : bi(`<b>${L[1][0]}.</b> `, `<b>${L[1][1]}。</b>`);
      row.classList.remove('good', 'wrong');
      if (b.dataset.v === 'show') { revealed[i] = true; okBox(msg, verdict + bi(it.en, it.zh), 'info'); row.classList.add('good'); return; }
      if ((b.dataset.v === '1') === it.ans) {
        row.classList.add('good');
        okBox(msg, '✓ ' + verdict + bi(it.en, it.zh));
        if (!revealed[i]) solved[i] = true;
        if (progId && solved.every(Boolean)) { Progress.mark(progId); okBox(msg, msg.innerHTML + bi('<br><b>All items solved. ✓</b>', '<br><b>全部答对。✓</b>')); }
      } else row.classList.add('wrong'), okBox(msg, bi('✗ Not quite. Think again about the exact hypotheses.', '✗ 不对。再仔细想想定理的确切前提。') + (it.hint ? ' ' + bi(it.hint[0], it.hint[1]) : ''), 'bad');
    }));
  });
}

// click-to-order game
function orderGame(box, steps, progId) {
  const n = steps.length;
  let order;
  do order = [...Array(n).keys()].sort(() => Math.random() - .5); while (order.every((x, i) => x === i));
  let placed = [], revealed = false;
  box.innerHTML = `<div class="row"><div class="col"><h4>${bil('Steps (shuffled)', '步骤（已打乱）')}</h4><div class="ord tray"></div></div>
    <div class="col"><h4>${bil('Your proof', '你的证明')}</h4><div class="ordslots"><div class="ord slots"></div></div></div></div>
    <div class="toolbar"><button class="btn primary chk">${bi('Check', '检查')}</button><button class="btn ghost rst">${bi('Reset', '重置')}</button>
    <button class="btn ghost shw">${bi('Show answer', '看答案')}</button></div><div class="msg"></div>`;
  const tray = box.querySelector('.tray'), slots = box.querySelector('.slots'), msg = box.querySelector('.msg');
  function render(marks) {
    tray.innerHTML = ''; slots.innerHTML = '';
    order.filter(i => !placed.includes(i)).forEach(i => {
      const c = document.createElement('div'); c.className = 'chip'; c.innerHTML = steps[i];
      c.addEventListener('click', () => { placed.push(i); clearBox(msg); render(); });
      tray.appendChild(c);
    });
    placed.forEach((i, k) => {
      const c = document.createElement('div');
      c.className = 'chip' + (marks ? (marks[k] ? ' ok' : ' no') : '');
      c.innerHTML = `<span class="k">${k + 1}.</span> ${steps[i]}`;
      c.addEventListener('click', () => { placed = placed.filter(x => x !== i); clearBox(msg); render(); });
      slots.appendChild(c);
    });
  }
  render();
  box.querySelector('.chk').addEventListener('click', () => {
    if (placed.length < n) { okBox(msg, bi('Place all the steps first.', '请先把所有步骤都放好。'), 'warn'); return; }
    const marks = placed.map((x, k) => x === k);
    render(marks);
    if (marks.every(Boolean)) { okBox(msg, bi('✓ Correct order.', '✓ 顺序正确。')); if (!revealed) Progress.mark(progId); }
    else okBox(msg, bi(`${marks.filter(Boolean).length} / ${n} in the right position (green). Ask: what does each step need from the previous ones?`, `${marks.filter(Boolean).length} / ${n} 个位置正确（绿色）。想一想：每一步需要用到前面的什么？`), 'bad');
  });
  box.querySelector('.rst').addEventListener('click', () => { placed = []; clearBox(msg); render(); });
  box.querySelector('.shw').addEventListener('click', () => { revealed = true; placed = [...Array(n).keys()]; render(placed.map(() => true)); okBox(msg, bi('This is the correct order.', '这是正确的顺序。'), 'info'); });
}

// multiple choice
function choices(box, opts, msgBox, onRight) {
  opts.forEach(o => {
    const b = document.createElement('button');
    b.className = 'btn choice';
    b.innerHTML = bi(o.en, o.zh);
    b.addEventListener('click', () => {
      box.querySelectorAll('.choice').forEach(x => x.classList.remove('right', 'wrongc'));
      b.classList.add(o.ok ? 'right' : 'wrongc');
      if (o.ok) { okBox(msgBox, '✓ ' + bi(o.fen, o.fzh)); onRight && onRight(); }
      else okBox(msgBox, '✗ ' + bi(o.fen, o.fzh), 'bad');
    });
    box.appendChild(b);
  });
  return { reveal() { box.querySelectorAll('.choice').forEach((b, i) => opts[i].ok && b.classList.add('right')); } };
}

/* ================= §1 Gödel numbering ================= */
(function godelNumbering() {
  const inp = $('gIn');
  GSYM.forEach(([s, c]) => {
    const d = document.createElement('div');
    d.className = 'sym';
    d.innerHTML = `<b>${s}</b><small>${c}</small>`;
    d.title = `code ${c} · 代码 ${c}`;
    d.addEventListener('click', () => {
      const st = inp.selectionStart ?? inp.value.length, en = inp.selectionEnd ?? inp.value.length;
      inp.value = inp.value.slice(0, st) + s + inp.value.slice(en);
      inp.focus(); inp.setSelectionRange(st + 1, st + 1);
      encode();
    });
    $('symtab').appendChild(d);
  });
  let last = null;
  function encode() {
    let syms;
    try { syms = gTokens(inp.value); } catch (e) { okBox($('gErr'), errHtml(e), 'bad'); return; }
    clearBox($('gErr'));
    if (!syms.length) { $('gEnc').innerHTML = ''; $('gNum').innerHTML = bi('Empty string: the empty product is 1.', '空串：空积等于 1。'); last = 1n; return; }
    let h = '';
    syms.forEach((c, i) => {
      if (i) h += '<div style="align-self:center;color:var(--muted)">·</div>';
      h += `<div class="cell pop" style="animation-delay:${i * 0.04}s"><div class="s">${c}</div><div class="c">c = ${GCODE[c]}</div><div class="pp">${PRIMES[i]}${sups(GCODE[c])}</div></div>`;
    });
    $('gEnc').innerHTML = h;
    const n = gEncode(syms);
    last = n;
    const s = n.toString();
    $('gNum').innerHTML = `⌜${syms.join('')}⌝ = ${syms.map((c, i) => `${PRIMES[i]}<sup>${GCODE[c]}</sup>`).join('·')} = <b>${s}</b>
      <div class="muted" style="font-family:var(--sans);font-size:13px">${bi(`${s.length} digits for ${syms.length} symbols.`, `${syms.length} 个符号，${s.length} 位数字。`)}</div>`;
  }
  inp.addEventListener('input', encode);
  $('gBack').addEventListener('click', () => { inp.value = [...inp.value].slice(0, -1).join(''); encode(); });
  document.querySelectorAll('[data-g]').forEach(b => b.addEventListener('click', () => { inp.value = b.dataset.g; encode(); }));
  encode();

  // decoder
  let tok = 0;
  async function decode(instant) {
    const my = ++tok;
    const stage = $('dStage');
    let n;
    try { n = BigInt($('dIn').value.trim().replace(/[,\s_]/g, '')); } catch { okBox($('dMsg'), bi('Please type a whole number.', '请输入一个整数。'), 'bad'); return; }
    const r = gDecode(n);
    stage.innerHTML = '';
    const STEP = 128, W = Math.max(70 + (r.steps.length + 1) * STEP + 40, 400), H = 190;
    const svg = el('svg', { viewBox: `0 0 ${W} ${H}`, width: W, height: H }, stage);
    const node = (x, label, fill = '#fff', stroke = '#1f2430') => {
      const g = el('g', { class: 'pop' }, svg);
      el('rect', { x: x - 52, y: 18, width: 104, height: 32, rx: 9, fill, stroke, 'stroke-width': 2 }, g);
      svgT(g, { x, y: 39, 'text-anchor': 'middle', 'font-size': 13, 'font-weight': 700 }, label);
      return g;
    };
    node(60, shortBig(n), '#e7ecff', '#3b5bdb');
    if (r.steps.length === 0) {
      okBox($('dMsg'), r.ok ? bi('1 is the empty product: it codes the empty string.', '1 是空积：它编码空串。') : bi(r.err[0], r.err[1]), r.ok ? 'info' : 'bad');
      return;
    }
    clearBox($('dMsg'));
    for (let i = 0; i < r.steps.length; i++) {
      if (!instant) { await sleep(420); if (my !== tok) return; }
      const st = r.steps[i];
      const x0 = 60 + i * STEP, x1 = x0 + STEP;
      const bad = st.e === 0 || !(st.e in GSYMOF);
      // leaf
      el('line', { x1: x0, y1: 50, x2: x0 + 34, y2: 98, stroke: '#9aa0aa', 'stroke-width': 2, class: 'fadein' }, svg);
      const lg = el('g', { class: 'pop' }, svg);
      el('circle', { cx: x0 + 40, cy: 116, r: 24, fill: bad ? '#ffe3e3' : '#fff3bf', stroke: bad ? '#e03131' : '#f08c00', 'stroke-width': 2 }, lg);
      svgT(lg, { x: x0 + 40, y: 121, 'text-anchor': 'middle', 'font-size': 14, 'font-weight': 700 }, `${st.p}${sups(st.e)}`);
      svgT(lg, { x: x0 + 40, y: 166, 'text-anchor': 'middle', 'font-size': 20, 'font-weight': 800, fill: bad ? '#e03131' : '#3b5bdb' }, bad ? '✗' : GSYMOF[st.e]);
      // remainder
      if (!bad) {
        el('line', { x1: x0 + 52, y1: 34, x2: x1 - 52, y2: 34, stroke: '#9aa0aa', 'stroke-width': 2, 'marker-end': 'url(#arr12)', class: 'fadein' }, svg);
        node(x1, st.rest === 1n ? '1' : shortBig(st.rest), st.rest === 1n ? '#d3f9d8' : '#fff', st.rest === 1n ? '#2f9e44' : '#1f2430');
      }
      stage.scrollLeft = Math.max(0, x1 - stage.clientWidth + 120);
    }
    if (r.ok) okBox($('dMsg'), bi(`Decoded: <span class="m"><b>${r.syms.join('')}</b></span> (${r.syms.length} symbols).`, `解码结果：<span class="m"><b>${r.syms.join('')}</b></span>（共 ${r.syms.length} 个符号）。`));
    else okBox($('dMsg'), bi(r.err[0], r.err[1]), 'bad');
  }
  const defs = el('svg', { width: 0, height: 0, style: 'position:absolute' }, document.body);
  const mk = el('marker', { id: 'arr12', viewBox: '0 0 10 10', refX: 9, refY: 5, markerWidth: 7, markerHeight: 7, orient: 'auto-start-reverse' }, el('defs', {}, defs));
  el('path', { d: 'M0,0 L10,5 L0,10 z', fill: '#9aa0aa' }, mk);
  $('dGo').addEventListener('click', () => decode(false));
  $('dIn').addEventListener('keydown', e => e.key === 'Enter' && decode(false));
  $('dUse').addEventListener('click', () => { if (last !== null) { $('dIn').value = last.toString(); decode(false); } });
  document.querySelectorAll('[data-d]').forEach(b => b.addEventListener('click', () => { $('dIn').value = b.dataset.d; decode(false); }));
  $('dIn').value = '180';
  decode(true);

  // proof code
  const lines = PROOFS.add.map(x => x[0]);
  const codes = lines.map(gEncodeStr);
  const L = codes.map(log10Big);
  // digits of x = sum g_i * log10(p_i); its log10 via log-sum-exp
  const terms = L.map((l, i) => l + Math.log10(Math.log10(PRIMES[i])));
  const mx = Math.max(...terms);
  const logDigits = mx + Math.log10(terms.reduce((s, t) => s + 10 ** (t - mx), 0));
  const maxL = Math.max(...L);
  let h = '<div class="stage"><table class="tt" style="width:100%"><tr><th>#</th><th>φᵢ</th><th>⌜φᵢ⌝</th><th style="width:40%">' + bil('size (digits)', '大小（位数）') + '</th></tr>';
  lines.forEach((f, i) => {
    const d = codes[i].toString().length;
    h += `<tr><td>${i + 1}</td><td><b>${f}</b></td><td>${shortBig(codes[i])}</td><td style="text-align:left"><div class="pop" style="animation-delay:${i * .2}s;height:14px;border-radius:7px;background:var(--gold);width:${(L[i] / maxL * 90).toFixed(1)}%;display:inline-block"></div> ${d}</td></tr>`;
  });
  h += `<tr><td colspan="2"><b>${bil('the whole proof', '整个证明')}</b></td><td><b>x = 2<sup>⌜φ₁⌝</sup>·3<sup>⌜φ₂⌝</sup>·5<sup>⌜φ₃⌝</sup></b></td>
    <td style="text-align:left"><div style="height:14px;border-radius:7px;background:linear-gradient(90deg,var(--meta),transparent);width:100%"></div>
    ≈ 10<sup>${logDigits.toFixed(1)}</sup> ${bil('digits', '位')}</td></tr></table></div>
    <div class="msg info">${bi(`Writing x out would need about 10^${Math.floor(logDigits)} digits, far more than the ~10^80 atoms in the observable universe. Arithmetic does not care: “x codes a proof of y” is still a perfectly definite relation between two numbers.`,
    `把 x 写出来大约要 10^${Math.floor(logDigits)} 位数字，远超可观测宇宙中约 10^80 个原子。算术不在乎这些：“x 编码了 y 的一个证明”依然是两个数之间一个完全确定的关系。`)}</div>`;
  $('pfCode').innerHTML = h;
})();

/* ================= §2 Q and PA ================= */
(function axioms() {
  const AX = [
    { nm: 'Q1', f: '∀x ¬(Sx = 0)', en: '0 is not a successor. Without it, the one-element structure with S0 = 0 would be a model.', zh: '0 不是任何数的后继。去掉它，单元素结构（S0 = 0）就成了模型。' },
    { nm: 'Q2', f: '∀x∀y (Sx = Sy → x = y)', en: 'S is injective. With Q1 this makes 0, 1, 2, … pairwise distinct: Q ⊢ n̄ ≠ m̄ whenever n ≠ m.', zh: 'S 是单射。结合 Q1，0, 1, 2, … 两两不同：只要 n ≠ m，就有 Q ⊢ n̄ ≠ m̄。' },
    { nm: 'Q3', f: '∀x (x + 0 = x)', en: 'Recursive definition of +: base case.', zh: '加法的递归定义：初始情形。' },
    { nm: 'Q4', f: '∀x∀y (x + Sy = S(x + y))', en: 'Recursive definition of +: step. Q3 and Q4 let Q evaluate any closed sum.', zh: '加法的递归定义：递推情形。Q3、Q4 使 Q 能算出任何闭的和式。' },
    { nm: 'Q5', f: '∀x (x × 0 = 0)', en: 'Recursive definition of ×: base case.', zh: '乘法的递归定义：初始情形。' },
    { nm: 'Q6', f: '∀x∀y (x × Sy = x × y + x)', en: 'Recursive definition of ×: step. Multiplication is what makes coding (and hence incompleteness) possible: Presburger arithmetic, which lacks it, is complete.', zh: '乘法的递归定义：递推情形。正是乘法使编码成为可能（从而导致不完全性）：没有乘法的普瑞斯伯格算术是完全的。' },
    { nm: 'Q7', f: '∀x (x ≠ 0 → ∃y (x = Sy))', en: 'Every nonzero element is a successor. In PA this is provable by induction.', zh: '每个非零元都是后继。在 PA 中它可以用归纳法证出。' },
  ];
  const IND = { nm: 'Ind', f: '[φ(0) ∧ ∀x(φ(x) → φ(Sx))] → ∀x φ(x)', en: 'Induction schema: one axiom for every formula φ(x, ȳ) (parameters universally quantified). Infinitely many axioms, but a decidable set, so PA is recursively axiomatized. It proves general laws such as ∀x (0 + x = x) and commutativity.',
    zh: '归纳公理模式：每个公式 φ(x, ȳ) 对应一条公理（参数全称量化）。公理有无穷多条，但构成可判定集，所以 PA 是递归可公理化的。它能证明 ∀x (0 + x = x)、交换律这类一般规律。' };
  let mode = 'Q';
  function render() {
    const box = $('axCards');
    box.innerHTML = '';
    const list = mode === 'Q' ? AX : [...AX, IND];
    list.forEach((a, i) => {
      const d = document.createElement('div');
      const dim = mode === 'PA' && a.nm === 'Q7';
      d.className = 'fcard pop' + (a.nm === 'Ind' ? ' ind' : '') + (dim ? ' dim' : '');
      d.style.animationDelay = (i * 0.05) + 's';
      d.innerHTML = `<span class="hint">${bil('click', '点击')}</span><div class="nm">${a.nm}${dim ? ' · ' + bil('theorem of PA', 'PA 的定理') : ''}</div><div class="fm">${a.f}</div><div class="back">${bi(a.en, a.zh)}</div>`;
      d.addEventListener('click', () => d.classList.toggle('open'));
      box.appendChild(d);
    });
    $('showQ').classList.toggle('sel', mode === 'Q');
    $('showPA').classList.toggle('sel', mode === 'PA');
    $('axMsg').innerHTML = mode === 'Q'
      ? bi('<b>Q</b>: seven axioms, finitely axiomatized, no induction. Weak, yet it represents every decidable relation, and that is all the first incompleteness theorem needs.', '<b>Q</b>：七条公理，有穷公理化，没有归纳法。它很弱，却能表示一切可判定关系，而第一不完全性定理需要的正是这一点。')
      : bi('<b>PA</b> = Q1–Q6 + the induction schema. Q7 becomes a theorem (dimmed). The second incompleteness theorem uses this extra strength.', '<b>PA</b> = Q1–Q6 + 归纳公理模式。Q7 成为定理（变灰）。第二不完全性定理要用到这部分额外的力量。');
  }
  $('showQ').addEventListener('click', () => { mode = 'Q'; render(); });
  $('showPA').addEventListener('click', () => { mode = 'PA'; render(); });
  render();

  // rewriting
  ['rwM', 'rwN'].forEach(id => { for (let i = 0; i <= 4; i++) $(id).innerHTML += `<option value="${i}">${i}</option>`; });
  $('rwM').value = '2'; $('rwN').value = '2';
  let ch = [], shown = 0;
  function load() {
    const m = +$('rwM').value, n = +$('rwN').value, op = $('rwOp').value;
    ch = rewriteChain(mkOp(op, numeral(m), numeral(n)));
    shown = 1;
    draw();
  }
  function draw() {
    const m = +$('rwM').value, n = +$('rwN').value, op = $('rwOp').value;
    let h = '';
    for (let i = 0; i < shown; i++) {
      const c = ch[i];
      const nextRule = i < shown - 1 || shown === ch.length ? c.rule : null;
      h += `<div class="fadein">${i ? '= ' : '&nbsp;&nbsp;'}${showT(c.t, i === shown - 1 && c.rule ? c.node : null)}${nextRule ? `<span class="ax">${nextRule}</span>` : ''}</div>`;
    }
    if (shown === ch.length) {
      const v = numVal(ch[ch.length - 1].t);
      h += `<div class="msg ok" style="font-family:var(--sans)">${bi(`Normal form reached: the numeral for ${v}. Each line is justified by one axiom, so <span class="m">Q ⊢ ${showT(numeral(m))} ${op} ${showT(numeral(n))} = ${showT(numeral(v))}</span> (${ch.length - 1} rewrites).`,
        `到达标准形：${v} 的数字项。每一行都由一条公理保证，所以 <span class="m">Q ⊢ ${showT(numeral(m))} ${op} ${showT(numeral(n))} = ${showT(numeral(v))}</span>（共 ${ch.length - 1} 步改写）。`)}</div>`;
      $('rwStep').disabled = true;
    } else $('rwStep').disabled = false;
    $('rwStage').innerHTML = h;
  }
  $('rwStep').addEventListener('click', () => { if (shown < ch.length) { shown++; draw(); } });
  $('rwAll').addEventListener('click', () => { shown = ch.length; draw(); });
  ['rwM', 'rwN', 'rwOp'].forEach(id => $(id).addEventListener('change', load));
  load();
})();

/* ================= §3 proof checker ================= */
(function checker() {
  let rows = PROOFS.add.map(([f, j]) => ({ f, j }));
  const tbl = $('pfTable');
  function render() {
    tbl.innerHTML = '';
    rows.forEach((r, i) => {
      const tr = document.createElement('tr');
      tr.innerHTML = `<td class="n">${i + 1}</td><td><input value="${r.f}"></td><td class="j"><input value="${r.j}"></td><td class="v"></td><td class="why"></td>`;
      const [a, b] = tr.querySelectorAll('input');
      a.addEventListener('input', () => { r.f = a.value; resetMarks(); });
      b.addEventListener('input', () => { r.j = b.value; resetMarks(); });
      tbl.appendChild(tr);
    });
  }
  function resetMarks() {
    [...tbl.rows].forEach(tr => { tr.className = ''; tr.cells[3].textContent = ''; tr.cells[4].innerHTML = ''; });
    clearBox($('pfMsg'));
    lamp(null);
  }
  // machine
  const svg = $('machine');
  el('rect', { x: 10, y: 10, width: 320, height: 150, rx: 18, fill: '#f1efe7', stroke: '#1f2430', 'stroke-width': 2 }, svg);
  svgT(svg, { x: 170, y: 34, 'text-anchor': 'middle', 'font-size': 14, 'font-weight': 700 }, 'Prf_T(x, y)');
  svgBi(svg, { x: 170, y: 52, 'text-anchor': 'middle', 'font-size': 11, fill: '#6b7280' }, 'decidable', '可判定');
  const gear = el('g', { class: 'gear' }, svg);
  for (let k = 0; k < 8; k++) {
    const a = k * Math.PI / 4;
    el('rect', { x: 70 + 26 * Math.cos(a) - 6, y: 100 + 26 * Math.sin(a) - 6, width: 12, height: 12, fill: '#6b7280', transform: `rotate(${k * 45} ${70 + 26 * Math.cos(a)} ${100 + 26 * Math.sin(a)})` }, gear);
  }
  el('circle', { cx: 70, cy: 100, r: 22, fill: '#6b7280' }, gear);
  el('circle', { cx: 70, cy: 100, r: 8, fill: '#f1efe7' }, gear);
  const xT = svgT(svg, { x: 120, y: 86, 'font-size': 12 }, 'x = …');
  const yT = svgT(svg, { x: 120, y: 106, 'font-size': 12 }, 'y = …');
  const lampY = el('circle', { cx: 250, cy: 136, r: 11, fill: '#e3dfd3', stroke: '#2f9e44', 'stroke-width': 2 }, svg);
  const lampN = el('circle', { cx: 300, cy: 136, r: 11, fill: '#e3dfd3', stroke: '#e03131', 'stroke-width': 2 }, svg);
  svgBi(svg, { x: 236, y: 140, 'text-anchor': 'end', 'font-size': 11, fill: '#2f9e44' }, 'YES', '是');
  svgT(svg, { x: 300, y: 118, 'text-anchor': 'middle', 'font-size': 11, fill: '#e03131' }, 'NO · 否');
  // Prov box
  el('rect', { x: 10, y: 180, width: 320, height: 110, rx: 18, fill: '#fff', stroke: '#ae3ec9', 'stroke-width': 2, 'stroke-dasharray': '6 4' }, svg);
  svgT(svg, { x: 170, y: 204, 'text-anchor': 'middle', 'font-size': 14, 'font-weight': 700, fill: '#ae3ec9' }, 'Prov_T(y) = ∃x Prf_T(x, y)');
  svgBi(svg, { x: 170, y: 224, 'text-anchor': 'middle', 'font-size': 11, fill: '#6b7280' }, 'search x = 0, 1, 2, …', '依次搜索 x = 0, 1, 2, …');
  const lampP = el('circle', { cx: 120, cy: 260, r: 11, fill: '#e3dfd3', stroke: '#2f9e44', 'stroke-width': 2 }, svg);
  svgBi(svg, { x: 140, y: 264, 'font-size': 11, fill: '#2f9e44' }, 'YES lamp only', '只有“是”灯');
  svgBi(svg, { x: 170, y: 284, 'text-anchor': 'middle', 'font-size': 10, fill: '#999' }, 'no proof? runs forever', '没有证明？永远跑下去');
  function lamp(v) {
    lampY.setAttribute('fill', v === true ? '#2f9e44' : '#e3dfd3');
    lampN.setAttribute('fill', v === false ? '#e03131' : '#e3dfd3');
    lampP.setAttribute('fill', v === true ? '#2f9e44' : '#e3dfd3');
  }
  let tok = 0;
  async function run() {
    const my = ++tok;
    resetMarks();
    const res = checkProof(rows);
    let codeOK = true, codes = [];
    try { codes = rows.map(r => gEncodeStr(r.f)); } catch { codeOK = false; }
    if (codeOK && codes.length) {
      const lg = codes.reduce((s, g, i) => Math.max(s, log10Big(g) + Math.log10(Math.log10(PRIMES[i]))), 0);
      xT.textContent = `x = ⌜proof⌝ ≈ 10^(10^${lg.toFixed(1)})`;
      yT.textContent = `y = ⌜${rows[rows.length - 1].f}⌝`.slice(0, 30);
    }
    gear.classList.add('spin');
    let allOk = true;
    for (let i = 0; i < rows.length; i++) {
      const tr = tbl.rows[i];
      tr.className = 'scan';
      await sleep(rows.length > 8 ? 160 : 380);
      if (my !== tok) return;
      tr.className = res[i].ok ? 'ok' : 'bad';
      tr.cells[3].textContent = res[i].ok ? '✓' : '✗';
      tr.cells[4].innerHTML = bi(res[i].en, res[i].zh);
      if (!res[i].ok) allOk = false;
    }
    gear.classList.remove('spin');
    lamp(allOk && rows.length > 0);
    const last = rows.length ? rows[rows.length - 1].f : '';
    if (allOk && rows.length) okBox($('pfMsg'), bi(`Every line checks. So Proof(x, y) holds for x = ⌜this sequence⌝ and y = ⌜${last}⌝, and the theory proves <span class="m">${last}</span>.`, `每一行都通过了检验。于是对 x = ⌜这个序列⌝、y = ⌜${last}⌝，Proof(x, y) 成立，理论证明了 <span class="m">${last}</span>。`));
    else okBox($('pfMsg'), bi('The checker rejects this sequence: Proof(x, y) is false. Note that it always <b>stops</b> with an answer: that is decidability.', '检验机拒绝了这个序列：Proof(x, y) 为假。注意它总会<b>停下来</b>给出答案，这就是可判定性。'), 'bad');
  }
  $('pfRun').addEventListener('click', run);
  $('pfAdd').addEventListener('click', () => { rows.push({ f: '', j: '' }); render(); });
  $('pfDel').addEventListener('click', () => { rows.pop(); render(); });
  document.querySelectorAll('[data-pf]').forEach(b => b.addEventListener('click', () => {
    rows = PROOFS[b.dataset.pf].map(([f, j]) => ({ f, j }));
    render(); resetMarks(); run();
  }));
  render();
  setTimeout(run, 400);
})();

/* ================= §4 diagonal lemma ================= */
(function diagonal() {
  const svg = $('dlSvg');
  const ROWS = ['x = 0', '∃y (x = y + y)', '¬(x = x)', 'Prov_T(x)', '¬Prov_T(x)'];
  const PSI = [
    { f: '¬Prov_T', en: 'G says “I am not provable in T”. This is Gödel’s sentence: see §5.', zh: 'G 说“我在 T 中不可证”。这就是哥德尔语句，见 §5。' },
    { f: 'Prov_T', en: 'H says “I am provable in T”: Henkin’s sentence. Is it provable? Löb’s theorem (§8, E6) says yes.', zh: 'H 说“我在 T 中可证”：亨金语句。它可证吗？勒布定理（§8、E6）说：可证。' },
    { f: 'Even', en: 'G says “my code is even”. In our numbering every code 2^c₁·… is even, so this G is simply true and provable: fixed points need not be paradoxical.', zh: 'G 说“我的编码是偶数”。在我们的编码下每个编码 2^c₁·… 都是偶数，所以这个 G 就是真的，而且可证：不动点未必带来悖论。' },
    { f: '¬True', en: 'G says “I am not true”: the liar! If a formula True(x) defining arithmetic truth existed, this G would satisfy G ↔ ¬G in ℕ. So no such formula exists: Tarski’s theorem, Lesson 13.', zh: 'G 说“我不是真的”：说谎者！倘若有公式 True(x) 定义了算术真，这个 G 就会在 ℕ 中满足 G ↔ ¬G。所以这样的公式不存在：这就是第 13 课的塔斯基定理。' },
  ];
  const X0 = 210, Y0 = 78, CW = 86, CH = 46;
  const COLS = 7, colX = c => X0 + c * CW, rowY = r => Y0 + r * CH; // col 5 = '⋯', col 6 = d; row 5 = '⋮', row 6 = D
  let cells = {}, tok = 0;
  function rowLabel(r) { return r < 5 ? `φ${subs(r)}(x) := ${ROWS[r]}` : r === 5 ? '⋮' : `φ_d = D(x)`; }
  function colLabel(c) { return c < 5 ? `⌜φ${subs(c)}⌝` : c === 5 ? '⋯' : 'd = ⌜D⌝'; }
  function cellText(r, c) { const R = r < 5 ? `φ${subs(r)}` : 'D'; const C = c < 5 ? `⌜φ${subs(c)}⌝` : 'd'; return `${R}(${C})`; }
  function draw() {
    tok++;
    svg.innerHTML = '';
    cells = {};
    svgBi(svg, { x: X0 + 3 * CW, y: 20, 'text-anchor': 'middle', 'font-size': 13, fill: '#3b5bdb' }, 'columns → codes ⌜φₘ⌝ of formulas', '列 → 公式的编码 ⌜φₘ⌝');
    svgBi(svg, { x: 10, y: 44, 'font-size': 13, fill: '#1f2430' }, 'rows ↓ all formulas', '行 ↓ 全体公式');
    for (let c = 0; c < COLS; c++) svgT(svg, { x: colX(c) + CW / 2, y: Y0 - 12, 'text-anchor': 'middle', 'font-size': 12.5, 'font-weight': 700, fill: c === 6 ? '#ae3ec9' : '#3b5bdb', opacity: c === 6 ? 0 : 1, id: c === 6 ? 'dlColD' : null }, colLabel(c));
    for (let r = 0; r < 7; r++) {
      const lab = svgT(svg, { x: X0 - 10, y: rowY(r) + CH / 2 + 4, 'text-anchor': 'end', 'font-size': 12.5, 'font-weight': 700, fill: r === 6 ? '#ae3ec9' : '#1f2430' }, rowLabel(r));
      if (r === 6) { lab.setAttribute('opacity', 0); lab.id = 'dlRowD'; }
      for (let c = 0; c < COLS; c++) {
        if (r === 5 || c === 5) {
          const ph = svgT(svg, { x: colX(c) + CW / 2, y: rowY(r) + CH / 2 + 5, 'text-anchor': 'middle', 'font-size': 16, fill: '#aaa' }, r === 5 && c === 5 ? '⋱' : r === 5 ? '⋮' : '⋯');
          if (r === 6 || c === 6) { ph.setAttribute('opacity', 0); ph.classList.add('dlLate'); }
          continue;
        }
        const g = el('g', { style: 'cursor:pointer' }, svg);
        const rect = el('rect', { x: colX(c) + 3, y: rowY(r) + 3, width: CW - 6, height: CH - 6, rx: 8, fill: r === c ? '#f8e7fc' : '#fff', stroke: '#e3dfd3', 'stroke-width': 1.5 }, g);
        const t = svgT(g, { x: colX(c) + CW / 2, y: rowY(r) + CH / 2 + 4, 'text-anchor': 'middle', 'font-size': 12 }, cellText(r, c));
        if (r === 6 || c === 6) g.setAttribute('opacity', 0);
        cells[r + ',' + c] = { g, rect, t };
        g.addEventListener('click', () => explain(r, c));
      }
    }
    // diagonal guide
    el('line', { x1: colX(0), y1: rowY(0), x2: colX(5), y2: rowY(5), stroke: '#ae3ec9', 'stroke-width': 1, 'stroke-dasharray': '3 5', opacity: .5 }, svg);
    okBox($('dlMsg'), bi('Click any cell. Diagonal cells (lilac) feed a formula its own code.', '点击任意格子。对角格（淡紫色）把公式自己的编码喂给它自己。'), 'info');
  }
  function explain(r, c) {
    const psi = PSI[+$('psiSel').value];
    const R = r < 5 ? ROWS[r] : `${psi.f}(sub(x, x))`;
    const code = c < 5 ? `⌜φ${subs(c)}⌝` : '⌜D⌝';
    const sent = R.replace(/x(?![a-z])/g, code);
    let h = bi(`Cell (${r < 5 ? r : 'D'}, ${c < 5 ? c : 'd'}) is the sentence <span class="m">${sent}</span>.`, `第 (${r < 5 ? r : 'D'}, ${c < 5 ? c : 'd'}) 格是语句 <span class="m">${sent}</span>。`);
    if (r === c) h += bi(` A <b>diagonal</b> cell: its code is <span class="m">sub(${code}, ${code})</span>.`, ` 这是<b>对角格</b>：其编码为 <span class="m">sub(${code}, ${code})</span>。`);
    if (r === 6 && c === 6) h += bi(` Since <span class="m">sub(d, d) = ⌜D(d̄)⌝</span>, this sentence talks about <b>its own</b> code: it is G, and <span class="m">G ↔ ${psi.f}(⌜G⌝)</span>.`, ` 由于 <span class="m">sub(d, d) = ⌜D(d̄)⌝</span>，这个语句谈论的正是<b>它自己</b>的编码：它就是 G，且 <span class="m">G ↔ ${psi.f}(⌜G⌝)</span>。`);
    okBox($('dlMsg'), h, 'info');
  }
  async function build() {
    draw();
    const my = tok;
    const psi = PSI[+$('psiSel').value];
    const say = (en, zh) => okBox($('dlMsg'), bi(en, zh), 'info');
    say('Step 1: walk down the diagonal. Each diagonal cell has code sub(n, n).', '第 1 步：沿对角线走一遍。每个对角格的编码是 sub(n, n)。');
    for (let k = 0; k < 5; k++) {
      await sleep(380); if (my !== tok) return;
      const c = cells[k + ',' + k];
      c.rect.setAttribute('stroke', '#ae3ec9'); c.rect.setAttribute('stroke-width', 3);
    }
    await sleep(500); if (my !== tok) return;
    say(`Step 2: twist with ψ = ${psi.f}. The new row D(x) := ${psi.f}(sub(x, x)) applies ψ to the diagonal.`, `第 2 步：用 ψ = ${psi.f} 扭转。新的一行 D(x) := ${psi.f}(sub(x, x))，即把 ψ 作用在对角线上。`);
    $('dlRowD').textContent = `φ_d = D(x) := ${psi.f}(sub(x,x))`;
    $('dlRowD').setAttribute('opacity', 1);
    $('dlRowD').setAttribute('font-size', 10.5);
    for (let k = 0; k < 5; k++) {
      await sleep(300); if (my !== tok) return;
      const from = cells[k + ',' + k], to = cells['6,' + k];
      const ln = el('path', { d: `M${colX(k) + CW / 2} ${rowY(k) + CH - 4} C ${colX(k) + CW / 2 + 30} ${rowY(k) + 80}, ${colX(k) + CW / 2 + 30} ${rowY(6) - 30}, ${colX(k) + CW / 2} ${rowY(6) + 4}`, fill: 'none', stroke: '#ae3ec9', 'stroke-width': 1.5, 'stroke-dasharray': '4 3', class: 'fadein' }, svg);
      to.g.setAttribute('opacity', 1);
      to.g.classList.add('pop');
      void from; void ln;
    }
    await sleep(600); if (my !== tok) return;
    say('Step 3: but D is a formula, so it is already in the list, as some row φ_d. Its code d gets a column too.', '第 3 步：可 D 也是公式，所以它本来就在清单里，是某一行 φ_d。它的编码 d 也有对应的一列。');
    $('dlColD').setAttribute('opacity', 1);
    svg.querySelectorAll('.dlLate').forEach(x => x.setAttribute('opacity', 1));
    for (let r = 0; r < 5; r++) { cells[r + ',6'].g.setAttribute('opacity', 1); cells[r + ',6'].g.classList.add('pop'); await sleep(120); if (my !== tok) return; }
    await sleep(600); if (my !== tok) return;
    const G = cells['6,6'];
    G.g.setAttribute('opacity', 1); G.g.classList.add('pop');
    G.rect.setAttribute('fill', '#fff3bf'); G.rect.setAttribute('stroke', '#f08c00'); G.rect.setAttribute('stroke-width', 3);
    G.t.textContent = 'G = D(d)';
    G.t.setAttribute('font-weight', 800);
    const cx = colX(6) + CW / 2, cy = rowY(6);
    el('path', { d: `M${cx + 30} ${cy + 6} C ${cx + 70} ${cy - 50}, ${cx - 70} ${cy - 50}, ${cx - 30} ${cy + 6}`, fill: 'none', stroke: '#f08c00', 'stroke-width': 2.5, 'marker-end': 'url(#arr12)', class: 'fadein' }, svg);
    svgT(svg, { x: cx, y: cy - 44, 'text-anchor': 'middle', 'font-size': 12, 'font-weight': 700, fill: '#f08c00', class: 'fadein' }, 'sub(d,d) = ⌜G⌝');
    say(`Step 4: the twisted diagonal meets itself at (D, d). The cell is G := D(d̄) = ${psi.f}(sub(d̄, d̄)), and sub(d, d) = ⌜G⌝, so Q ⊢ G ↔ ${psi.f}(⌜G⌝). ${psi.en}`,
      `第 4 步：扭转后的对角线在 (D, d) 处与自身相遇。这一格是 G := D(d̄) = ${psi.f}(sub(d̄, d̄))，而 sub(d, d) = ⌜G⌝，所以 Q ⊢ G ↔ ${psi.f}(⌜G⌝)。${psi.zh}`);
  }
  $('dlGo').addEventListener('click', build);
  $('dlReset').addEventListener('click', draw);
  $('psiSel').addEventListener('change', draw);
  draw();
  stepper('dlSteps', 'dlNext', 'dlAll');

  // comparison minis
  const MINI = [
    { t: ['Cantor', '康托尔'], rows: ['sequences fₙ', '序列 fₙ'], twist: '1 − fₙ(n)', inList: false,
      en: 'The flipped diagonal differs from every row, so it is <b>not in the list</b>: no list of 0/1 sequences is complete.', zh: '翻转后的对角线与每一行都不同，所以它<b>不在清单里</b>：任何 0/1 序列清单都不完整。' },
    { t: ['Turing (L11)', '图灵（第 11 课）'], rows: ['programs e', '程序 e'], twist: 'halt ↔ loop', inList: false,
      en: 'If halting were decidable, the twisted program D would be in the list; at (D, D) it would halt iff it doesn’t. So halting is undecidable.', zh: '若停机可判定，扭转后的程序 D 就在清单里；在 (D, D) 处它停机当且仅当它不停机。所以停机问题不可判定。' },
    { t: ['Gödel', '哥德尔'], rows: ['formulas φₙ(x)', '公式 φₙ(x)'], twist: 'ψ(·)', inList: true,
      en: 'ψ(sub(x, x)) <b>is</b> a formula, so the twisted row <b>is in the list</b>. No contradiction: at (D, d) we get a <b>fixed point</b> G ↔ ψ(⌜G⌝).', zh: 'ψ(sub(x, x)) <b>本身就是</b>公式，所以扭转后的一行<b>就在清单里</b>。这里不产生矛盾，而是在 (D, d) 处得到一个<b>不动点</b> G ↔ ψ(⌜G⌝)。' },
  ];
  MINI.forEach(m => {
    const d = document.createElement('div');
    d.className = 'col mini';
    d.style.flex = '1 1 240px';
    d.innerHTML = `<h4>${bil(m.t[0], m.t[1])}</h4><div class="muted" style="font-size:12px">${bil('rows', '行')}: ${bil(m.rows[0], m.rows[1])} · ${bil('twist', '扭转')}: <span class="m">${m.twist}</span></div>`;
    const s = el('svg', { viewBox: '0 0 220 172', width: 220, height: 172 }, d);
    const N = 4, C = 24, x0 = 20, y0 = 10;
    for (let r = 0; r < N; r++) for (let c = 0; c < N; c++) {
      el('rect', { x: x0 + c * C, y: y0 + r * C, width: C - 3, height: C - 3, rx: 4, fill: r === c ? '#f8e7fc' : '#f1efe7', stroke: r === c ? '#ae3ec9' : 'none' }, s);
    }
    const yD = m.inList ? y0 + 3 * C : y0 + N * C + 14;
    for (let c = 0; c < N; c++) {
      el('rect', { x: x0 + c * C, y: yD, width: C - 3, height: C - 3, rx: 4, fill: m.inList && c === 3 ? '#fff3bf' : 'rgba(174,62,201,.25)', stroke: m.inList && c === 3 ? '#f08c00' : '#ae3ec9', 'stroke-width': m.inList && c === 3 ? 3 : 1 }, s);
    }
    svgT(s, { x: x0 + N * C + 8, y: yD + 16, 'font-size': 12, 'font-weight': 700, fill: m.inList ? '#f08c00' : '#e03131' }, m.inList ? '★ G' : '✗');
    svgBi2(s, { x: x0 + N * C + 8, y: yD + 32, 'font-size': 10, fill: '#6b7280' }, m.inList ? 'in the list' : 'not in the list', m.inList ? '在清单中' : '不在清单中', 13);
    d.insertAdjacentHTML('beforeend', `<div style="font-size:13.5px">${bi(m.en, m.zh)}</div>`);
    d.addEventListener('click', () => { document.querySelectorAll('#dlCompare .mini').forEach(x => x.classList.remove('hot')); d.classList.add('hot'); });
    $('dlCompare').appendChild(d);
  });
})();

/* ================= §5 Gödel sentence ================= */
(function godelSentence() {
  const svg = $('mirror');
  const defs = el('defs', {}, svg);
  const lg = el('linearGradient', { id: 'mglass', x1: 0, x2: 1 }, defs);
  el('stop', { offset: '0', 'stop-color': '#dbe4ff' }, lg);
  el('stop', { offset: '.5', 'stop-color': '#ffffff' }, lg);
  el('stop', { offset: '1', 'stop-color': '#bac8ff' }, lg);
  const loop = 'M 250 70 C 330 10, 490 10, 570 70 M 570 170 C 490 235, 330 235, 250 170';
  el('path', { d: loop, fill: 'none', stroke: '#bbb', 'stroke-width': 2, 'stroke-dasharray': '5 5' }, svg);
  const cardG = el('rect', { x: 40, y: 55, width: 210, height: 130, rx: 16, fill: '#fff', stroke: '#1f2430', 'stroke-width': 2.5 }, svg);
  svgT(svg, { x: 145, y: 112, 'text-anchor': 'middle', 'font-size': 46, 'font-weight': 800 }, 'G');
  svgBi2(svg, { x: 145, y: 146, 'text-anchor': 'middle', 'font-size': 12 }, '“I am not provable”', '“我不可证”');
  const stG = svgT(svg, { x: 145, y: 210, 'text-anchor': 'middle', 'font-size': 14, 'font-weight': 800 }, '');
  el('rect', { x: 400, y: 34, width: 18, height: 140, rx: 6, fill: 'url(#mglass)', stroke: '#91a7ff' }, svg);
  svgBi(svg, { x: 409, y: 240, 'text-anchor': 'middle', 'font-size': 11, fill: '#6b7280' }, 'mirror = coding', '镜子 = 编码');
  const cardP = el('rect', { x: 570, y: 55, width: 220, height: 130, rx: 16, fill: '#fbfaff', stroke: '#3b5bdb', 'stroke-width': 2.5 }, svg);
  svgT(svg, { x: 680, y: 112, 'text-anchor': 'middle', 'font-size': 20, 'font-weight': 800, fill: '#3b5bdb' }, '¬Prov_T(⌜G⌝)');
  svgBi2(svg, { x: 680, y: 146, 'text-anchor': 'middle', 'font-size': 12, fill: '#3b5bdb' }, 'a claim about a number', '关于一个数的断言');
  svgT(svg, { x: 410, y: 20, 'text-anchor': 'middle', 'font-size': 13, fill: '#6b7280' }, 'G  ⟶  ⌜G⌝ = 2^…·3^…·5^…');
  svgT(svg, { x: 410, y: 196, 'text-anchor': 'middle', 'font-size': 13, 'font-weight': 700, fill: '#ae3ec9' }, 'T ⊢ G ↔ ¬Prov_T(⌜G⌝)');
  const dot = el('circle', { r: 6, fill: '#f08c00' }, svg);
  const am = el('animateMotion', { dur: '5s', repeatCount: 'indefinite', path: 'M 250 70 C 330 10, 490 10, 570 70 L 570 170 C 490 235, 330 235, 250 170 Z' }, dot);
  void am;
  function status(txt, color, which) {
    stG.textContent = txt; stG.setAttribute('fill', color);
    cardG.setAttribute('stroke', which === 'G' || which === 'both' ? color : '#1f2430');
    cardP.setAttribute('stroke', which === 'P' || which === 'both' ? color : '#3b5bdb');
  }
  const A = [
    { k: 'pre', h: bi('Suppose T ⊢ G, by a proof with code n.', '假设 T ⊢ G，其证明的编码为 n。') },
    { h: bi('Proof_T(n, ⌜G⌝) is true, so <span class="m">Q ⊢ Prf(n̄, ⌜G⌝)</span>.', 'Proof_T(n, ⌜G⌝) 成立，所以 <span class="m">Q ⊢ Prf(n̄, ⌜G⌝)</span>。'), why: bi('representability (§3)', '可表示性（§3）') },
    { h: bi('Hence <span class="m">T ⊢ ∃x Prf(x, ⌜G⌝)</span>, i.e. <span class="m">T ⊢ Prov(⌜G⌝)</span>.', '于是 <span class="m">T ⊢ ∃x Prf(x, ⌜G⌝)</span>，即 <span class="m">T ⊢ Prov(⌜G⌝)</span>。'), why: bi('∃-introduction', '∃ 引入') },
    { h: bi('But <span class="m">T ⊢ G → ¬Prov(⌜G⌝)</span>, so <span class="m">T ⊢ ¬Prov(⌜G⌝)</span>.', '但 <span class="m">T ⊢ G → ¬Prov(⌜G⌝)</span>，所以 <span class="m">T ⊢ ¬Prov(⌜G⌝)</span>。'), why: bi('fixed point (§4)', '不动点（§4）') },
    { k: 'bad', h: bi('T proves a sentence and its negation: T is inconsistent. So: T consistent ⇒ T ⊬ G.', 'T 同时证明了一个语句及其否定：T 不一致。所以：T 一致 ⇒ T ⊬ G。') },
  ];
  const B = [
    { k: 'pre', h: bi('Suppose T ⊢ ¬G. By the fixed point, <span class="m">T ⊢ ∃x Prf(x, ⌜G⌝)</span>.', '假设 T ⊢ ¬G。由不动点，<span class="m">T ⊢ ∃x Prf(x, ⌜G⌝)</span>。') },
    { h: bi('If T is consistent, T ⊬ G (left), so <b>no</b> number n codes a proof of G.', '若 T 一致，则 T ⊬ G（见左），所以<b>没有</b>哪个数 n 编码 G 的证明。') },
    { h: bi('So for each n, <span class="m">T ⊢ ¬Prf(n̄, ⌜G⌝)</span>: n = 0, 1, 2, …', '于是对每个 n，都有 <span class="m">T ⊢ ¬Prf(n̄, ⌜G⌝)</span>：n = 0, 1, 2, …'), why: bi('representability, the “NO” lamp', '可表示性，“否”灯') },
    { k: 'bad', h: bi('T proves “some x works” yet refutes every single x: T is <b>ω-inconsistent</b>. So: T ω-consistent ⇒ T ⊬ ¬G.', 'T 证明“有某个 x 满足”，却又逐一否定每个 x：T 是 <b>ω-不一致的</b>。所以：T ω-一致 ⇒ T ⊬ ¬G。'),
      why: bi('ω-inconsistent is not the same as inconsistent; Rosser closes this gap (below).', 'ω-不一致不等于不一致；罗瑟堵上了这个缺口（见下）。') },
  ];
  const C = [
    { k: 'pre', h: bi('T consistent ⇒ T ⊬ G ⇒ no number codes a proof of G.', 'T 一致 ⇒ T ⊬ G ⇒ 没有哪个数编码 G 的证明。') },
    { h: bi('So <span class="m">ℕ ⊨ ¬Prov(⌜G⌝)</span>.', '所以 <span class="m">ℕ ⊨ ¬Prov(⌜G⌝)</span>。') },
    { h: bi('Q ⊢ G ↔ ¬Prov(⌜G⌝), and Q is true in ℕ, so this equivalence is true in ℕ.', 'Q ⊢ G ↔ ¬Prov(⌜G⌝)，而 Q 在 ℕ 中为真，所以这个等价式在 ℕ 中成立。') },
    { k: 'good', h: bi('Hence <span class="m">ℕ ⊨ G</span>: G is true but unprovable in T. (A metatheorem, assuming T is consistent.)', '所以 <span class="m">ℕ ⊨ G</span>：G 为真但在 T 中不可证。（这是元定理，以 T 一致为前提。）') },
  ];
  $('gsA').addEventListener('click', () => { chain($('gsOut1'), A); status('T ⊬ G', '#e03131', 'G'); });
  $('gsB').addEventListener('click', () => { chain($('gsOut2'), B); status('T ⊬ ¬G (ω-cons.)', '#e03131', 'P'); });
  $('gsC').addEventListener('click', () => { chain($('gsOut3'), C); status('ℕ ⊨ G', '#2f9e44', 'both'); });
  $('gsAll').addEventListener('click', () => { chain($('gsOut1'), A, true); chain($('gsOut2'), B, true); chain($('gsOut3'), C, true); status('T ⊬ G, T ⊬ ¬G, ℕ ⊨ G', '#ae3ec9', 'both'); });

  // hypothesis switchboard
  const H = [
    { id: 'con', en: 'consistent', zh: '一致' },
    { id: 'rec', en: 'recursively axiomatized', zh: '递归可公理化' },
    { id: 'q', en: 'contains (interprets) Q', zh: '包含（能解释）Q' },
  ];
  const on = { con: 1, rec: 1, q: 1 };
  const CE = {
    con: ['<b>Drop consistency:</b> an inconsistent theory proves every sentence, so it is “complete”, trivially and uselessly.', '<b>去掉一致性：</b>不一致的理论证明一切语句，因而“完全”，但这是平凡而无用的完全。'],
    rec: ['<b>Drop recursive axiomatizability:</b> true arithmetic Th(ℕ) (all sentences true in ℕ) is consistent, contains Q, and complete. But no algorithm lists its axioms; by Lesson 13 it is not even definable in arithmetic.', '<b>去掉递归可公理化：</b>真算术 Th(ℕ)（ℕ 中全部真语句）一致、包含 Q、而且完全。但没有算法能列出它的公理；由第 13 课，它甚至在算术中不可定义。'],
    q: ['<b>Drop “contains Q”:</b> Presburger arithmetic Th(ℕ, 0, S, +) and the theory of real closed fields (Tarski) are consistent, recursively axiomatized, complete and even decidable. Without enough arithmetic, you cannot represent proofs.', '<b>去掉“包含 Q”：</b>普瑞斯伯格算术 Th(ℕ, 0, S, +) 和实闭域理论（塔斯基）都一致、递归可公理化、完全，甚至可判定。没有足够的算术，就表示不了“证明”。'],
  };
  function upd() {
    const off = H.filter(h => !on[h.id]);
    if (!off.length) okBox($('hypMsg'), bi('All three hold, so T is <b>incomplete</b>: for example PA, ZFC, Q itself, PA + Con(PA).', '三条全部成立，所以 T <b>不完全</b>：例如 PA、ZFC、Q 本身、PA + Con(PA)。'), 'ok');
    else okBox($('hypMsg'), off.map(h => bi(CE[h.id][0], CE[h.id][1])).join('<br>') + bi('<br><i>Dropping a hypothesis does not force completeness, it only makes it possible.</i>', '<br><i>去掉某条假设并不意味着理论一定完全，只是完全成为可能。</i>'), 'warn');
  }
  H.forEach(h => {
    const sw = document.createElement('div');
    sw.className = 'sw on';
    sw.innerHTML = `<span class="track"><span class="knob"></span></span><span>${bil(h.en, h.zh)}</span>`;
    sw.addEventListener('click', () => { on[h.id] = 1 - on[h.id]; sw.classList.toggle('on', !!on[h.id]); upd(); });
    $('hypBox').appendChild(sw);
  });
  upd();

  // Rosser race
  const rs = $('race');
  const X = k => 160 + k * 30, LY = [62, 132];
  const pos = [null, null];
  svgBi2(rs, { x: 10, y: LY[0] - 2, 'font-size': 12, 'font-weight': 700, fill: '#3b5bdb' }, 'proofs of R', 'R 的证明');
  svgBi2(rs, { x: 10, y: LY[1] - 2, 'font-size': 12, 'font-weight': 700, fill: '#e03131' }, 'proofs of ¬R', '¬R 的证明');
  svgBi(rs, { x: 160, y: 20, 'font-size': 11, fill: '#6b7280' }, 'proof codes x = 0, 1, 2, … (click to place a proof)', '证明编码 x = 0, 1, 2, …（点击放置证明）');
  const marks = [];
  for (let l = 0; l < 2; l++) {
    el('line', { x1: X(0), x2: X(20), y1: LY[l], y2: LY[l], stroke: '#ccc', 'stroke-width': 3 }, rs);
    marks.push([]);
    for (let k = 0; k <= 20; k++) {
      const g = el('g', { style: 'cursor:pointer' }, rs);
      el('rect', { x: X(k) - 15, y: LY[l] - 20, width: 30, height: 40, fill: 'transparent' }, g);
      const c = el('circle', { cx: X(k), cy: LY[l], r: 5, fill: '#ddd' }, g);
      if (l === 1) svgT(rs, { x: X(k), y: LY[1] + 30, 'text-anchor': 'middle', 'font-size': 10, fill: '#999' }, k);
      marks[l].push(c);
      g.addEventListener('click', () => { pos[l] = pos[l] === k ? null : k; race(); });
    }
  }
  const runner = el('line', { x1: X(0), x2: X(0), y1: 40, y2: 152, stroke: '#f08c00', 'stroke-width': 3, opacity: 0 }, rs);
  runner.style.transition = 'transform .8s ease';
  function race() {
    marks.forEach((row, l) => row.forEach((c, k) => { c.setAttribute('r', pos[l] === k ? 11 : 5); c.setAttribute('fill', pos[l] === k ? (l ? '#e03131' : '#3b5bdb') : '#ddd'); }));
    const p = pos[0], q = pos[1];
    let first = null;
    if (p !== null || q !== null) first = q === null || (p !== null && p < q) ? 0 : 1;
    runner.setAttribute('opacity', first === null ? 0 : 1);
    runner.style.transform = `translateX(${first === null ? 0 : X(first ? q : p) - X(0)}px)`;
    let en, zh, kind = 'bad';
    if (p === null && q === null) { en = 'No proof of R and none of ¬R: R is undecided. Every hypothesis on R’s condition is vacuous, so R is in fact true. This is the only possibility for consistent T.'; zh = 'R 与 ¬R 都没有证明：R 不可判定。R 中的条件全都空真，所以 R 实际上为真。对一致的 T 而言，这是唯一可能的情形。'; kind = 'ok'; }
    else if (p !== null && q !== null) { en = `T proves both R (proof ${p}) and ¬R (proof ${q}): inconsistent by definition.`; zh = `T 既证明了 R（证明 ${p}）又证明了 ¬R（证明 ${q}）：按定义就是不一致的。`; }
    else if (p !== null) { en = `Say T ⊢ R with proof ${p}. If T is consistent, no y &lt; ${p} proves ¬R, and T can check each of these finitely many y. So T ⊢ Prf(${p}̄, ⌜R⌝) ∧ ∀y &lt; ${p}̄ ¬Prf(y, ⌜¬R⌝), which refutes R. Then T ⊢ ¬R too: inconsistent!`; zh = `设 T ⊢ R，证明编码为 ${p}。若 T 一致，则没有 y &lt; ${p} 是 ¬R 的证明，而 T 能对这有限多个 y 逐一核实。于是 T ⊢ Prf(${p}̄, ⌜R⌝) ∧ ∀y &lt; ${p}̄ ¬Prf(y, ⌜¬R⌝)，这否定了 R。于是 T ⊢ ¬R：不一致！`; }
    else { en = `Say T ⊢ ¬R with proof ${q}. For any x: if x ≤ ${q}, T checks that x is not a proof of R (finitely many cases, consistency); if x &gt; ${q}, then y = ${q} is an earlier proof of ¬R. So T ⊢ R: inconsistent!`; zh = `设 T ⊢ ¬R，证明编码为 ${q}。对任意 x：若 x ≤ ${q}，T 能逐一核实 x 不是 R 的证明（有限多种情形，用到一致性）；若 x &gt; ${q}，则 y = ${q} 就是 ¬R 的一个更早的证明。于是 T ⊢ R：不一致！`; }
    okBox($('raceMsg'), bi(en, zh), kind);
  }
  race();
})();

/* ================= §6 halting ================= */
(function halting() {
  const PROGS = [
    { en: 'P₁: count to 3, then halt', zh: 'P₁：数到 3 后停机', lane: 0, at: 4 },
    { en: 'P₂: while true: skip', zh: 'P₂：while true: 空转', lane: 1, at: 6 },
    { en: 'P₃: search for a counterexample to Goldbach', zh: 'P₃：搜索哥德巴赫猜想的反例', lane: -1, at: 19 },
  ];
  let cur = 0, tok = 0;
  PROGS.forEach((p, i) => {
    const b = document.createElement('button');
    b.className = 'btn small' + (i === 0 ? ' sel' : '');
    b.innerHTML = bil(p.en, p.zh);
    b.addEventListener('click', () => { cur = i; $('hpProgs').querySelectorAll('button').forEach((x, j) => x.classList.toggle('sel', j === i)); draw(); });
    $('hpProgs').appendChild(b);
  });
  const svg = $('hpSvg');
  const X = k => 250 + k * 28, LY = [70, 150];
  let boxes = [];
  function draw() {
    tok++;
    svg.innerHTML = '';
    clearBox($('hpMsg'));
    svgBi(svg, { x: 10, y: 22, 'font-size': 12, fill: '#6b7280' }, 'dovetail: A₀ B₀ A₁ B₁ A₂ B₂ …', '交替进行：A₀ B₀ A₁ B₁ A₂ B₂ …');
    svgBi2(svg, { x: 10, y: LY[0] - 2, 'font-size': 12, 'font-weight': 700, fill: '#2f9e44' }, 'A: proof of H(ē)?', 'A：找 H(ē) 的证明', 17);
    svgBi2(svg, { x: 10, y: LY[1] - 2, 'font-size': 12, 'font-weight': 700, fill: '#e03131' }, 'B: proof of ¬H(ē)?', 'B：找 ¬H(ē) 的证明', 17);
    boxes = [[], []];
    for (let l = 0; l < 2; l++) for (let k = 0; k < 20; k++) {
      const r = el('rect', { x: X(k) - 11, y: LY[l] - 11, width: 22, height: 22, rx: 5, fill: '#f1efe7', stroke: '#e3dfd3' }, svg);
      boxes[l].push(r);
    }
    for (let k = 0; k < 20; k += 5) svgT(svg, { x: X(k), y: 196, 'text-anchor': 'middle', 'font-size': 10, fill: '#999' }, k);
  }
  async function run(instant) {
    draw();
    const my = tok, p = PROGS[cur];
    for (let k = 0; k <= p.at; k++) {
      for (let l = 0; l < 2; l++) {
        if (!instant) { await sleep(90); if (my !== tok) return; }
        const hit = l === p.lane && k === p.at;
        boxes[l][k].setAttribute('fill', hit ? (l ? '#e03131' : '#2f9e44') : '#d8d3c4');
        if (hit) {
          boxes[l][k].classList.add('pop');
          svgT(svg, { x: X(k), y: LY[l] - 18, 'text-anchor': 'middle', 'font-size': 18, 'font-weight': 800, fill: l ? '#e03131' : '#2f9e44' }, '★');
          break;
        }
      }
    }
    if (p.lane === 0) okBox($('hpMsg'), bi('Lane A hits: <b>H(ē) is provable</b>, so the decider answers “halts”. This lane is real: true Σ₁ sentences are always provable (Σ₁-completeness).', 'A 道命中：<b>H(ē) 可证</b>，判定机回答“停机”。这一路是真实存在的：真的 Σ₁ 语句总是可证（Σ₁ 完全性）。'));
    else if (p.lane === 1) okBox($('hpMsg'), bi('Lane B hits: <b>¬H(ē) is provable</b>, answer “loops”. For this trivial loop such a proof really exists (PA proves it never halts). But only in the <i>imagined</i> world where T is complete is lane B guaranteed to light up for <i>every</i> non-halting program; in reality, for some non-halting programs T proves no such thing, since otherwise the halting problem would be decidable.', 'B 道命中：<b>¬H(ē) 可证</b>，回答“不停机”。对这个平凡的死循环，这样的证明确实存在（PA 能证明它永不停机）。但只有在 T 是完全的这个<i>假想</i>世界里，B 道才保证对<i>每个</i>不停机的程序都亮灯；现实中，总有一些不停机的程序，T 证明不了它们不停机，否则停机问题就可判定了。'), 'warn');
    else {
      svgT(svg, { x: X(19) + 22, y: 116, 'font-size': 22, fill: '#ae3ec9', 'font-weight': 800 }, '?');
      okBox($('hpMsg'), bi('Still searching… If T were complete, one lane would eventually light up and the decider would <b>settle Goldbach’s conjecture</b> mechanically. A machine that settles every such question cannot exist (Lesson 11), so T is not complete.', '仍在搜索……若 T 是完全的，终会有一道亮灯，判定机就能机械地<b>判定哥德巴赫猜想</b>。能解决一切此类问题的机器不存在（第 11 课），所以 T 不是完全的。'), 'info');
    }
  }
  $('hpGo').addEventListener('click', () => run(false));
  $('hpFast').addEventListener('click', () => run(true));
  draw();
  stepper('hpSteps', 'hpNext', 'hpAll');
})();

/* ================= §7 second theorem ================= */
(function second() {
  const DC = [
    { nm: 'D1', f: 'T ⊢ φ  ⇒  T ⊢ Prov(⌜φ⌝)', en: 'If T proves φ, T can verify that fact: the proof is a concrete number, checked by a Σ₁ computation.', zh: '若 T 证明了 φ，T 能核实这件事：证明是个具体的数，可以通过 Σ₁ 计算来检验。' },
    { nm: 'D2', f: 'T ⊢ Prov(⌜φ→ψ⌝) → (Prov(⌜φ⌝) → Prov(⌜ψ⌝))', en: 'T knows that provability is closed under modus ponens: concatenate the two proofs and add ψ.', zh: 'T 知道可证性对肯定前件式封闭：把两个证明首尾相接，再添上 ψ 即可。' },
    { nm: 'D3', f: 'T ⊢ Prov(⌜φ⌝) → Prov(⌜Prov(⌜φ⌝)⌝)', en: 'T knows D1: “provable implies provably provable”. This is formalized Σ₁-completeness; it needs some induction, which is why the second theorem is stated for extensions of PA (or IΣ₁).', zh: 'T 知道 D1：“可证则可证地可证”。这是形式化的 Σ₁ 完全性，需要一定的归纳法，所以第二定理通常针对 PA（或 IΣ₁）的扩张来陈述。' },
  ];
  const steps = stepper('g2Steps', 'g2Next', 'g2All');
  DC.forEach(dc => {
    const d = document.createElement('div');
    d.className = 'fcard';
    d.innerHTML = `<span class="hint">${bil('click', '点击')}</span><div class="nm">${dc.nm}</div><div class="fm" style="font-size:14px">${dc.f}</div><div class="back">${bi(dc.en, dc.zh)}</div>`;
    d.addEventListener('click', () => {
      const was = d.classList.contains('hl');
      document.querySelectorAll('#dcCards .fcard').forEach(x => x.classList.remove('hl', 'open'));
      steps.steps.forEach(s => s.classList.remove('hl'));
      if (was) return;
      d.classList.add('hl', 'open');
      steps.all();
      steps.steps.forEach(s => (s.dataset.d || '').split(' ').includes(dc.nm) && s.classList.add('hl'));
    });
    $('dcCards').appendChild(d);
  });

  // tower
  const svg = $('tower');
  let n = 0;
  const FH = 38, GAP = 8, BASE = 334;
  const names = k => k === 0 ? 'T₀ = PA' : `T${subs(k)} = T${subs(k - 1)} + Con(T${subs(k - 1)})`;
  function floor(k) {
    const y = BASE - (k + 1) * (FH + GAP);
    const g = el('g', { class: 'pop' }, svg);
    const hue = [59, 47, 39, 33, 28, 22][k] ?? 20;
    el('rect', { x: 60, y, width: 250, height: FH, rx: 8, fill: `hsl(${200 + k * 20},70%,${92 - k * 3}%)`, stroke: '#3b5bdb', 'stroke-width': 1.5 }, g);
    svgT(g, { x: 70, y: y + 24, 'font-size': 13, 'font-weight': 700 }, names(k));
    svgT(g, { x: 318, y: y + 24, 'font-size': 12, fill: '#e03131', 'font-weight': 700 }, `⊬ Con(T${subs(k)})`);
    if (k > 0) {
      el('path', { d: `M 55 ${y + FH / 2} C 25 ${y + FH / 2}, 25 ${y + FH + GAP + FH / 2}, 55 ${y + FH + GAP + FH / 2}`, fill: 'none', stroke: '#2f9e44', 'stroke-width': 2, 'marker-end': 'url(#arr12)' }, g);
      svgT(g, { x: 4, y: y + FH + 8, 'font-size': 10, fill: '#2f9e44', 'font-weight': 700 }, '⊢Con');
    }
    void hue;
  }
  function reset() {
    svg.innerHTML = '';
    el('line', { x1: 20, x2: 420, y1: BASE + 4, y2: BASE + 4, stroke: '#aaa', 'stroke-width': 2 }, svg);
    n = 0; floor(0); floor(1); n = 2;
    $('towAdd').disabled = false;
  }
  $('towAdd').addEventListener('click', () => {
    if (n < 6) { floor(n); n++; }
    if (n === 6) {
      $('towAdd').disabled = true;
      svgT(svg, { x: 185, y: 22, 'text-anchor': 'middle', 'font-size': 13, 'font-weight': 700, fill: '#ae3ec9', class: 'fadein' }, '⋮  T_ω = ⋃ Tₙ  ⊬ Con(T_ω)');
    }
  });
  $('towReset').addEventListener('click', reset);
  reset();
})();

/* ================= §8 Löb ================= */
(function lob() {
  stepper('lobSteps', 'lobNext', 'lobAll');
  const OUT = [
    [{ k: 'pre', h: bi('Hypothesis: <span class="m">T ⊢ Prov(⌜0=1⌝) → 0=1</span>, i.e. <span class="m">T ⊢ ¬Prov(⌜0=1⌝)</span>, i.e. <span class="m">T ⊢ Con(T)</span>.', '前提：<span class="m">T ⊢ Prov(⌜0=1⌝) → 0=1</span>，即 <span class="m">T ⊢ ¬Prov(⌜0=1⌝)</span>，也就是 <span class="m">T ⊢ Con(T)</span>。') },
      { h: bi('Löb’s conclusion: <span class="m">T ⊢ 0=1</span>.', '勒布定理的结论：<span class="m">T ⊢ 0=1</span>。') },
      { k: 'good', h: bi('So if T proves its own consistency, T is inconsistent. That is the <b>second incompleteness theorem</b>, as a special case.', '所以，若 T 证明了自身的一致性，T 就不一致。这正是<b>第二不完全性定理</b>，作为特例。') }],
    [{ k: 'pre', h: bi('H ↔ Prov(⌜H⌝) gives <span class="m">T ⊢ Prov(⌜H⌝) → H</span> for free.', '由 H ↔ Prov(⌜H⌝)，直接得到 <span class="m">T ⊢ Prov(⌜H⌝) → H</span>。') },
      { k: 'good', h: bi('Löb: <span class="m">T ⊢ H</span>. The sentence “I am provable” is provable (Henkin’s question, answered by Löb in 1955).', '勒布：<span class="m">T ⊢ H</span>。“我是可证的”这句话确实可证（亨金提出的问题，勒布于 1955 年解答）。') }],
    [{ k: 'pre', h: bi('Could <span class="m">T ⊢ Prov(⌜G⌝) → G</span>?', '有没有可能 <span class="m">T ⊢ Prov(⌜G⌝) → G</span>？') },
      { h: bi('Then Löb gives T ⊢ G, impossible for consistent T.', '那样的话勒布定理给出 T ⊢ G，对一致的 T 不可能。') },
      { k: 'bad', h: bi('So T cannot prove “if G is provable then G is true”, although it is true in ℕ. T cannot prove its own soundness, even for one sentence.', '所以 T 证明不了“若 G 可证则 G 为真”，尽管这在 ℕ 中成立。T 连对单个语句的可靠性都证明不了。') }],
    [{ k: 'pre', h: bi('T ⊢ 0=0, so trivially <span class="m">T ⊢ Prov(⌜0=0⌝) → 0=0</span>.', 'T ⊢ 0=0，所以平凡地有 <span class="m">T ⊢ Prov(⌜0=0⌝) → 0=0</span>。') },
      { k: 'good', h: bi('Löb’s moral: T proves the reflection “Prov(⌜φ⌝) → φ” <b>exactly</b> for those φ it already proves.', '勒布定理的寓意：T 能证明反射原理“Prov(⌜φ⌝) → φ”，<b>恰好</b>只针对它本来就能证明的那些 φ。') }],
  ];
  $('lobGo').addEventListener('click', () => chain($('lobOut'), OUT[+$('lobSel').value]));
  $('lobSel').addEventListener('change', () => chain($('lobOut'), OUT[+$('lobSel').value]));
  chain($('lobOut'), OUT[0], true);
})();

/* ================= §9 myths ================= */
tfList($('mythList'), [
  { s: bi('“The Gödel sentence of PA is true but unprovable.”', '“PA 的哥德尔语句为真但不可证。”'), ans: true,
    en: 'Correct with two caveats: “true” means true in ℕ, which follows <i>if PA is consistent</i>; “unprovable” means unprovable <i>in PA</i>. PA + Con(PA) proves it.', zh: '正确，但有两点要说清：“真”指在 ℕ 中为真，这要<i>以 PA 一致为前提</i>；“不可证”指<i>在 PA 中</i>不可证。PA + Con(PA) 就能证明它。' },
  { s: bi('“Some mathematical statements are unprovable, period.”', '“有些数学命题是绝对不可证的。”'), ans: false,
    en: 'Provability is always relative to a theory. Any sentence σ is provable in T + σ. The theorem says: no <i>single</i> consistent, recursively axiomatized T ⊇ Q decides everything.', zh: '可证性总是相对于某个理论而言的。任何语句 σ 在 T + σ 中都可证。定理说的是：没有<i>任何一个</i>一致、递归可公理化、包含 Q 的理论能判定一切。' },
  { s: bi('“Presburger arithmetic (ℕ with + only) is incomplete by Gödel.”', '“由哥德尔定理，普瑞斯伯格算术（只有加法的 ℕ）是不完全的。”'), ans: false,
    en: 'Presburger arithmetic is complete and decidable (Presburger 1929). Without × it cannot represent all decidable relations, so the theorem does not apply.', zh: '普瑞斯伯格算术是完全且可判定的（普瑞斯伯格 1929）。没有乘法，它无法表示所有可判定关系，定理不适用。' },
  { s: bi('“The theory of real closed fields has + and ×, so it is incomplete.”', '“实闭域理论有加法和乘法，所以是不完全的。”'), ans: false,
    en: 'Tarski proved it complete and decidable (quantifier elimination). A consistent theory that interprets Q is undecidable, so this theory does not interpret Q; in particular ℕ is not definable in (ℝ, +, ×).', zh: '塔斯基证明了它完全且可判定（量词消去）。能解释 Q 的一致理论都不可判定，所以该理论不能解释 Q；特别地，ℕ 在 (ℝ, +, ×) 中不可定义。' },
  { s: bi('“Add G as a new axiom and the theory becomes complete.”', '“把 G 作为新公理加进去，理论就完全了。”'), ans: false,
    en: 'PA + G is still consistent, recursively axiomatized and contains Q, so it has its own Gödel sentence G′. Incompleteness cannot be patched.', zh: 'PA + G 仍然一致、递归可公理化、包含 Q，所以它有自己的哥德尔语句 G′。不完全性是补不完的。' },
  { s: bi('“Q, which has no induction at all, is already incomplete.”', '“完全没有归纳法的 Q 已经是不完全的。”'), ans: true,
    en: 'Yes. Q is even essentially undecidable: every consistent extension of it is undecidable.', zh: '是的。Q 甚至是本质不可判定的：它的每个一致扩张都不可判定。' },
  { s: bi('“Incompleteness implies PA has nonstandard models.”', '“不完全性蕴涵 PA 有非标准模型。”'), ans: true,
    en: 'PA + ¬G is consistent, so by the completeness theorem it has a model. G is true in ℕ, so this model is not ℕ: it contains nonstandard numbers (one of them codes a “proof” of G).', zh: 'PA + ¬G 是一致的，由完备性定理它有模型。G 在 ℕ 中为真，所以这个模型不是 ℕ：它含有非标准的数（其中之一编码了 G 的一个“证明”）。' },
  { s: bi('“Gödel proved that mathematics is inconsistent.”', '“哥德尔证明了数学是不一致的。”'), ans: false,
    en: 'No. The theorems assume consistency. The second theorem only says a consistent theory cannot prove its own consistency.', zh: '没有。定理以一致性为前提。第二定理只是说，一致的理论证明不了自身的一致性。' },
  { s: bi('“Th(ℕ), the set of all true arithmetic sentences, is complete.”', '“Th(ℕ)，即全体真算术语句，是完全的。”'), ans: true,
    en: 'Yes, trivially, and it does not contradict Gödel: Th(ℕ) is not recursively axiomatizable.', zh: '是的，而且是平凡的，与哥德尔并不矛盾：Th(ℕ) 不是递归可公理化的。' },
], null, { grid: true });

/* ================= Exercises ================= */
(function e1() {
  const st = { a: false, b: false, c: false };
  let revealed = false;
  const fin = () => st.a && st.b && st.c && Progress.mark('L12E1');
  $('e1aGo').addEventListener('click', () => {
    const v = $('e1a').value.replace(/[,\s]/g, '');
    if (v === '2430') { okBox($('e1aMsg'), bi('✓ 2¹·3⁵·5¹ = 2·243·5 = 2430.', '✓ 2¹·3⁵·5¹ = 2·243·5 = 2430。')); if (!revealed) st.a = true; fin(); }
    else okBox($('e1aMsg'), bi('Not yet. Three symbols 0, =, 0 with codes 1, 5, 1 go on the primes 2, 3, 5.', '还不对。三个符号 0、=、0 的代码分别是 1、5、1，依次放在素数 2、3、5 上。'), 'bad');
  });
  $('e1bGo').addEventListener('click', () => {
    let ok = false;
    try { ok = gEncodeStr($('e1b').value) === 180n; } catch { ok = false; }
    if (ok) { okBox($('e1bMsg'), bi('✓ 180 = 2²·3²·5¹, codes 2, 2, 1: <span class="m">SS0</span>, the numeral for 2.', '✓ 180 = 2²·3²·5¹，代码依次为 2、2、1：<span class="m">SS0</span>，即数 2 的数字项。')); if (!revealed) st.b = true; fin(); }
    else okBox($('e1bMsg'), bi('Not yet. Factor 180 into powers of 2, 3, 5 and read the exponents as codes.', '还不对。把 180 分解成 2、3、5 的幂，把指数当成代码来读。'), 'bad');
  });
  const c = ok => {
    if (ok) { okBox($('e1cMsg'), bi('✓ No. 10 = 2¹·3⁰·5¹: the prime 3 is skipped, but every symbol code is ≥ 1, so no string has this code.', '✓ 不是。10 = 2¹·3⁰·5¹：跳过了素数 3，而每个符号的代码都 ≥ 1，所以没有符号串的编码是 10。')); if (!revealed) st.c = true; fin(); }
    else okBox($('e1cMsg'), bi('✗ Factor it: what is the exponent of 3?', '✗ 分解一下：3 的指数是多少？'), 'bad');
  };
  $('e1cY').addEventListener('click', () => c(false));
  $('e1cN').addEventListener('click', () => c(true));
  $('e1Show').addEventListener('click', () => {
    revealed = true;
    okBox($('e1aMsg'), bi('(a) 2¹·3⁵·5¹ = 2430.', '(a) 2¹·3⁵·5¹ = 2430。'), 'info');
    okBox($('e1bMsg'), bi('(b) 180 = 2²·3²·5¹ → SS0.', '(b) 180 = 2²·3²·5¹ → SS0。'), 'info');
    okBox($('e1cMsg'), bi('(c) No: 10 = 2·5 skips the prime 3.', '(c) 不是：10 = 2·5 跳过了素数 3。'), 'info');
  });
})();

orderGame($('e2Game'), [
  bi('Represent <span class="m">sub(m, n)</span> in Q by a formula <span class="m">Sub(x, y, z)</span>.', '在 Q 中用公式 <span class="m">Sub(x, y, z)</span> 表示 <span class="m">sub(m, n)</span>。'),
  bi('Define <span class="m">D(x) :≡ ∃z (Sub(x, x, z) ∧ ψ(z))</span>.', '定义 <span class="m">D(x) :≡ ∃z (Sub(x, x, z) ∧ ψ(z))</span>。'),
  bi('Let <span class="m">d = ⌜D⌝</span> and <span class="m">G :≡ D(d̄)</span>.', '令 <span class="m">d = ⌜D⌝</span>，<span class="m">G :≡ D(d̄)</span>。'),
  bi('Observe <span class="m">sub(d, d) = ⌜G⌝</span>.', '注意到 <span class="m">sub(d, d) = ⌜G⌝</span>。'),
  bi('Conclude <span class="m">Q ⊢ G ↔ ψ(⌜G⌝)</span>.', '得出 <span class="m">Q ⊢ G ↔ ψ(⌜G⌝)</span>。'),
], 'L12E2');

tfList($('e3List'), [
  { s: 'PA', ans: true, en: 'Consistent, recursively axiomatized, contains Q: incomplete.', zh: '一致、递归可公理化、包含 Q：不完全。' },
  { s: 'ZFC', ans: true, en: 'Assuming ZFC is consistent: it is recursively axiomatized and interprets Q (via ω), so it is incomplete.', zh: '假定 ZFC 一致：它递归可公理化，并能（通过 ω）解释 Q，所以不完全。' },
  { s: 'PA + Con(PA)', ans: true, en: 'Still consistent and recursively axiomatized: it has its own undecidable sentence.', zh: '仍然一致且递归可公理化：它有自己的不可判定语句。' },
  { s: bi('Presburger arithmetic Th(ℕ, 0, S, +)', '普瑞斯伯格算术 Th(ℕ, 0, S, +)'), ans: false, en: 'No multiplication, does not interpret Q; it is complete and decidable.', zh: '没有乘法，不能解释 Q；它完全且可判定。' },
  { s: bi('True arithmetic Th(ℕ, 0, S, +, ×)', '真算术 Th(ℕ, 0, S, +, ×)'), ans: false, en: 'Complete, but not recursively axiomatizable.', zh: '完全，但不是递归可公理化的。' },
  { s: bi('Real closed fields', '实闭域理论'), ans: false, en: 'Complete and decidable (Tarski); does not interpret Q.', zh: '完全且可判定（塔斯基）；不能解释 Q。' },
  { s: 'PA + 0 = S0', ans: false, en: 'Inconsistent (contradicts Q1), so it proves everything.', zh: '不一致（与 Q1 矛盾），所以它证明一切。' },
  { s: bi('Dense linear orders without endpoints (DLO)', '无端点稠密线序理论（DLO）'), ans: false, en: 'Complete (ℵ₀-categorical, Łoś–Vaught) and decidable; no arithmetic inside.', zh: '完全（ℵ₀-范畴，由沃什–沃特检验）且可判定；里面没有算术。' },
], 'L12E3', { labels: [['Applies', '适用'], ['Doesn’t apply', '不适用']] });

tfList($('e4List'), [
  { s: bi('If T is consistent, then T + ¬G_T is consistent.', '若 T 一致，则 T + ¬G_T 一致。'), ans: true, en: 'If T + ¬G were inconsistent, then T ⊢ G, impossible.', zh: '若 T + ¬G 不一致，则 T ⊢ G，这不可能。' },
  { s: bi('If T is consistent, then T + ¬G_T is ω-consistent.', '若 T 一致，则 T + ¬G_T 是 ω-一致的。'), ans: false, en: 'T + ¬G proves ∃x Prf(x, ⌜G⌝), yet refutes each Prf(n̄, ⌜G⌝), since no actual proof exists. ω-inconsistent.', zh: 'T + ¬G 证明 ∃x Prf(x, ⌜G⌝)，却又否定每一个 Prf(n̄, ⌜G⌝)，因为实际上并无证明。它是 ω-不一致的。' },
  { s: bi('The Gödel sentence is (equivalent to) a Π₁ sentence.', '哥德尔语句（等价于）一个 Π₁ 语句。'), ans: true, en: 'G ↔ ∀x ¬Prf(x, ⌜G⌝), and Prf can be taken Δ₀. So G says “a certain computation never succeeds”.', zh: 'G ↔ ∀x ¬Prf(x, ⌜G⌝)，而 Prf 可取为 Δ₀ 公式。所以 G 说的是“某个计算永远不会成功”。' },
  { s: bi('Every complete, recursively axiomatized theory is decidable.', '每个完全且递归可公理化的理论都是可判定的。'), ans: true, en: 'List all theorems; φ or ¬φ will appear (if inconsistent, everything appears at once). This is the engine of §6.', zh: '列举全部定理，φ 或 ¬φ 必会出现（若不一致，一切都会出现）。这正是 §6 的引擎。' },
  { s: bi('If T ⊇ Q is consistent and proves every true Σ₁ sentence, then T is complete.', '若 T ⊇ Q 一致，且证明所有真 Σ₁ 语句，则 T 是完全的。'), ans: false, en: 'Q itself is a counterexample: it proves every true Σ₁ sentence, yet it is incomplete. The gap lies one level up, at Π₁ sentences such as G.', zh: 'Q 本身就是反例：它证明所有真 Σ₁ 语句，却不完全。缺口在高一层的 Π₁ 语句上，比如 G。' },
], 'L12E4');

tfList($('e5List'), [
  { s: 'PA ⊬ Con(PA)', ans: true, en: 'The second incompleteness theorem.', zh: '第二不完全性定理。' },
  { s: 'PA ⊢ ¬Con(PA)', ans: false, en: 'PA is true in ℕ and ¬Con(PA) is false, so PA does not prove it.', zh: 'PA 在 ℕ 中为真，而 ¬Con(PA) 为假，所以 PA 证明不了它。' },
  { s: bi('PA + ¬Con(PA) is consistent.', 'PA + ¬Con(PA) 是一致的。'), ans: true, en: 'Otherwise PA ⊢ Con(PA). It is consistent but proves a false sentence.', zh: '否则 PA ⊢ Con(PA)。它一致，却证明了一个假语句。' },
  { s: 'ZFC ⊢ Con(PA)', ans: true, en: 'ZFC proves ω is a model of PA, hence Con(PA). No conflict: ZFC is a different, stronger theory.', zh: 'ZFC 证明 ω 是 PA 的模型，从而 Con(PA)。不矛盾：ZFC 是另一个更强的理论。' },
  { s: bi('If ZFC is consistent, then ZFC ⊢ Con(ZFC).', '若 ZFC 一致，则 ZFC ⊢ Con(ZFC)。'), ans: false, en: 'Exactly what the second theorem forbids. This is why L14 can only build models of ZFC from extra assumptions.', zh: '这恰恰是第二定理禁止的。这也是为什么第 14 课只能在额外假设下构造 ZFC 的模型。' },
], 'L12E5');

(function e6() {
  const proof = document.querySelector('#e6Proof .step');
  let revealed = false;
  const ch = choices($('e6Choice'), [
    { ok: true, en: 'H is provable in PA.', zh: 'H 在 PA 中可证。', fen: 'Right: Löb’s theorem.', fzh: '对：勒布定理。' },
    { ok: false, en: 'H is refutable in PA.', zh: 'H 在 PA 中可否证。', fen: 'Not so. Look at Löb’s theorem: is its hypothesis Prov(⌜H⌝) → H available here?', fzh: '不对。看看勒布定理：它的前提 Prov(⌜H⌝) → H 在这里成立吗？' },
    { ok: false, en: 'H is undecidable, just like G.', zh: 'H 和 G 一样不可判定。', fen: 'The fixed-point equation alone does not decide it, but Löb’s theorem does.', fzh: '仅凭不动点方程确实看不出来，但勒布定理可以。' },
    { ok: false, en: 'No such H exists.', zh: '这样的 H 不存在。', fen: 'It exists: apply the diagonal lemma to ψ(x) = Prov(x).', fzh: '它存在：对 ψ(x) = Prov(x) 用对角线引理即可。' },
  ], $('e6Msg'), () => { proof.classList.add('on'); if (!revealed) Progress.mark('L12E6'); });
  $('e6Show').addEventListener('click', () => { revealed = true; ch.reveal(); proof.classList.add('on'); okBox($('e6Msg'), bi('H is provable.', 'H 可证。'), 'info'); });
})();
}
