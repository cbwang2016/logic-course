// Lesson 3: first-order logic — languages, structures, truth.
// The first part (FOL) is pure logic with no DOM access, so it can be unit-tested with node.

/* =====================================================================
   PURE CORE: parser, printer, free variables, substitution, evaluator
   ===================================================================== */
const FOL = (function () {
  class FolError extends Error {
    constructor(en, zh) { super(en); this.en = en; this.zh = zh; }
  }
  // Variables: names starting with u–z, or any lowercase name carrying digits/primes (x1, a', …).
  const isVarName = v => /^[u-z]/.test(v) || /[0-9₀-₉']/.test(v.slice(1));
  const SY = { and: '∧', or: '∨', imp: '→', iff: '↔' };

  function tokenize(s) {
    const out = [];
    let i = 0;
    const push = (t, n) => { out.push({ t, pos: i }); i += n; };
    const single = {
      '↔': 'iff', '→': 'imp', '∧': 'and', '&': 'and', '^': 'and', '∨': 'or', '|': 'or',
      '¬': 'not', '~': 'not', '!': 'not', '∀': 'all', '∃': 'ex', '(': '(', ')': ')', ',': ',', '.': '.',
      '=': 'eq', '≠': 'neq', '<': 'lt', '+': 'plus', '·': 'times', '*': 'times', '×': 'times', '⋅': 'times',
    };
    while (i < s.length) {
      const c = s[i], rest = s.slice(i);
      if (/\s/.test(c)) { i++; continue; }
      if (rest.startsWith('<->') || rest.startsWith('<=>')) { push('iff', 3); continue; }
      if (rest.startsWith('->') || rest.startsWith('=>')) { push('imp', 2); continue; }
      if (rest.startsWith('!=') || rest.startsWith('/=')) { push('neq', 2); continue; }
      if (rest.startsWith('/\\')) { push('and', 2); continue; }
      if (rest.startsWith('\\/')) { push('or', 2); continue; }
      if (/^forall(?![A-Za-z])/.test(rest)) { push('all', 6); continue; }
      if (/^exists(?![A-Za-z])/.test(rest)) { push('ex', 6); continue; }
      if ((c === 'A' || c === 'E') && /^[u-z]/.test(s[i + 1] || '')) { push(c === 'A' ? 'all' : 'ex', 1); continue; }
      if (single[c]) { push(single[c], 1); continue; }
      if (/[0-9]/.test(c)) {
        let j = i + 1;
        while (j < s.length && /[0-9]/.test(s[j])) j++;
        out.push({ t: 'num', v: s.slice(i, j), pos: i });
        i = j;
        continue;
      }
      if (/[A-Za-z]/.test(c)) {
        let j = i + 1;
        while (j < s.length && /[0-9₀-₉']/.test(s[j])) j++;
        out.push({ t: /[A-Z]/.test(c) ? 'up' : 'low', v: s.slice(i, j), pos: i });
        i = j;
        continue;
      }
      throw new FolError(`Unknown symbol “${c}” at position ${i + 1}`, `第 ${i + 1} 个位置出现了无法识别的符号“${c}”`);
    }
    return out;
  }

  function makeParser(toks) {
    let i = 0;
    const peek = (k = 0) => toks[i + k];
    const is = t => !!peek() && peek().t === t;
    const fail = (en, zh) => { throw new FolError(en, zh); };
    const expect = (t, en, zh) => { if (!is(t)) fail(en, zh); i++; };

    function pIff() {
      let a = pImp();
      while (is('iff')) { i++; a = { type: 'bin', op: 'iff', a, b: pImp() }; }
      return a;
    }
    function pImp() {
      const a = pOr();
      if (is('imp')) { i++; return { type: 'bin', op: 'imp', a, b: pImp() }; }
      return a;
    }
    function pOr() {
      let a = pAnd();
      while (is('or')) { i++; a = { type: 'bin', op: 'or', a, b: pAnd() }; }
      return a;
    }
    function pAnd() {
      let a = pUn();
      while (is('and')) { i++; a = { type: 'bin', op: 'and', a, b: pUn() }; }
      return a;
    }
    function pUn() {
      if (is('not')) { i++; return { type: 'not', a: pUn() }; }
      if (is('all') || is('ex')) {
        const q = peek().t;
        i++;
        const v = peek();
        if (!v || v.t !== 'low') fail('A quantifier must be followed by a variable', '量词后面必须紧跟一个变元');
        if (!isVarName(v.v)) fail(`“${v.v}” is a constant, not a variable (variables: u, v, w, x, y, z, …)`, `“${v.v}”是常元而不是变元（变元为 u, v, w, x, y, z, …）`);
        i++;
        if (is('.')) { i++; return { type: 'q', q, v: v.v, a: pIff() }; }
        return { type: 'q', q, v: v.v, a: pUn() };
      }
      return pAtom();
    }
    const isRelOp = () => is('eq') || is('neq') || is('lt');
    function pAtom() {
      const tk = peek();
      if (!tk) fail('Formula ends too early', '公式不完整，结尾缺少内容');
      if (tk.t === '(') {
        const save = i;
        let first = null;
        try {
          i++;
          const f = pIff();
          if (is(')')) {
            i++;
            if (!isRelOp()) return f;
          } else first = new FolError('Missing “)”', '缺少右括号“)”');
        } catch (e) { first = e; }
        i = save;
        try { return pCompare(); } catch (e2) { throw first || e2; }
      }
      if (tk.t === 'up' && tk.v !== 'S') {
        if (!peek(1) || peek(1).t !== '(') fail(`The relation symbol ${tk.v} needs arguments, e.g. ${tk.v}(x,y)`, `关系符号 ${tk.v} 需要带上变元，例如 ${tk.v}(x,y)`);
        i += 2;
        const args = [pTerm()];
        while (is(',')) { i++; args.push(pTerm()); }
        expect(')', 'Missing “)” after the arguments', '参数后面缺少“)”');
        return { type: 'rel', name: tk.v, args };
      }
      return pCompare();
    }
    function pCompare() {
      const a = pTerm();
      if (is('eq')) { i++; return { type: 'eq', a, b: pTerm() }; }
      if (is('neq')) { i++; return { type: 'not', a: { type: 'eq', a, b: pTerm() } }; }
      if (is('lt')) { i++; return { type: 'rel', name: '<', args: [a, pTerm()], infix: true }; }
      fail('Expected a formula here, e.g. E(x,y) or x = y (a term alone is not a formula)', '这里应当是一个公式，例如 E(x,y) 或 x = y（单独一个项不是公式）');
    }
    function pTerm() {
      let a = pProd();
      while (is('plus')) { i++; a = { type: 'fn', name: '+', args: [a, pProd()], infix: true }; }
      return a;
    }
    function pProd() {
      let a = pTPrim();
      while (is('times')) { i++; a = { type: 'fn', name: '·', args: [a, pTPrim()], infix: true }; }
      return a;
    }
    function pTPrim() {
      const tk = peek();
      if (!tk) fail('A term ends too early', '项不完整，结尾缺少内容');
      if (tk.t === 'num') { i++; return { type: 'const', name: tk.v }; }
      if (tk.t === '(') {
        i++;
        const t = pTerm();
        expect(')', 'Missing “)” in a term', '项中缺少“)”');
        return t;
      }
      if ((tk.t === 'low' || tk.t === 'up') && peek(1) && peek(1).t === '(') {
        i += 2;
        const args = [pTerm()];
        while (is(',')) { i++; args.push(pTerm()); }
        expect(')', 'Missing “)” after the arguments', '参数后面缺少“)”');
        return { type: 'fn', name: tk.v, args };
      }
      if (tk.t === 'low') { i++; return isVarName(tk.v) ? { type: 'var', name: tk.v } : { type: 'const', name: tk.v }; }
      fail('Expected a term (a variable, a constant, or f(…)) here', '这里应当是一个项（变元、常元或 f(…)）');
    }
    const done = () => {
      if (i < toks.length) fail('Extra symbols after the end', '末尾多出了符号');
    };
    return { pIff, pTerm, done };
  }

  function parseFormula(s) {
    const toks = tokenize(s);
    if (!toks.length) throw new FolError('Empty input', '输入为空');
    const P = makeParser(toks);
    const f = P.pIff();
    P.done();
    return f;
  }
  function parseTerm(s) {
    const toks = tokenize(s);
    if (!toks.length) throw new FolError('Empty input', '输入为空');
    const P = makeParser(toks);
    const t = P.pTerm();
    P.done();
    return t;
  }

  /* ---------- printing as segments (so the UI can colour each occurrence) ---------- */
  const TP = { '+': 1, '·': 2 };
  const tprec = t => (t.type === 'fn' && t.args.length === 2 && t.name in TP) ? TP[t.name] : 3;
  function tsegs(t, out) {
    const S = text => out.push({ text, kind: 'sym' });
    if (t.type === 'var') out.push({ text: t.name, kind: 'var', node: t });
    else if (t.type === 'const') out.push({ text: t.name, kind: 'const' });
    else if (t.args.length === 2 && t.name in TP) {
      const p = TP[t.name];
      const wrap = (u, right) => {
        const need = right ? tprec(u) <= p : tprec(u) < p;
        if (need) S('(');
        tsegs(u, out);
        if (need) S(')');
      };
      wrap(t.args[0], false);
      S(` ${t.name} `);
      wrap(t.args[1], true);
    } else if (t.name === '⁻¹' && t.args.length === 1) {
      const need = t.args[0].type === 'fn';
      if (need) S('(');
      tsegs(t.args[0], out);
      if (need) S(')');
      S('⁻¹');
    } else {
      S(t.name + '(');
      t.args.forEach((a, k) => { if (k) S(','); tsegs(a, out); });
      S(')');
    }
    return out;
  }
  const FP = { iff: 1, imp: 2, or: 3, and: 4 };
  const fprec = f => f.type === 'bin' ? FP[f.op] : (f.type === 'not' || f.type === 'q') ? 5 : 6;
  function fsegs(f, out = []) {
    const S = text => out.push({ text, kind: 'sym' });
    const wrap = (g, need) => { if (need) S('('); fsegs(g, out); if (need) S(')'); };
    switch (f.type) {
      case 'rel':
        if (f.infix) { tsegs(f.args[0], out); S(` ${f.name} `); tsegs(f.args[1], out); }
        else { S(f.name + '('); f.args.forEach((a, k) => { if (k) S(','); tsegs(a, out); }); S(')'); }
        break;
      case 'eq': tsegs(f.a, out); S(' = '); tsegs(f.b, out); break;
      case 'not': S('¬'); wrap(f.a, fprec(f.a) < 5 || f.a.type === 'eq' || !!f.a.infix); break;
      case 'q':
        out.push({ text: (f.q === 'all' ? '∀' : '∃') + f.v, kind: 'q', node: f });
        if (f.a.type === 'q' || f.a.type === 'not') fsegs(f.a, out);
        else if (fprec(f.a) < 5 || f.a.type === 'eq' || f.a.infix) wrap(f.a, true);
        else { S(' '); fsegs(f.a, out); }
        break;
      case 'bin': {
        const p = FP[f.op], pa = fprec(f.a), pb = fprec(f.b);
        const left = f.op === 'imp' ? pa <= p : pa < p;
        const right = f.op === 'imp' ? pb < p : pb <= p;
        wrap(f.a, left);
        S(` ${SY[f.op]} `);
        wrap(f.b, right);
        break;
      }
    }
    return out;
  }
  const show = f => fsegs(f).map(s => s.text).join('');
  const showT = t => tsegs(t, []).map(s => s.text).join('');

  /* ---------- variables ---------- */
  function termVars(t, acc = new Set()) {
    if (t.type === 'var') acc.add(t.name);
    else if (t.type === 'fn') t.args.forEach(a => termVars(a, acc));
    return acc;
  }
  function freeVars(f) {
    switch (f.type) {
      case 'rel': { const s = new Set(); f.args.forEach(a => termVars(a, s)); return s; }
      case 'eq': return termVars(f.b, termVars(f.a));
      case 'not': return freeVars(f.a);
      case 'bin': return new Set([...freeVars(f.a), ...freeVars(f.b)]);
      case 'q': { const s = freeVars(f.a); s.delete(f.v); return s; }
    }
  }
  function allVars(f, acc = new Set()) {
    switch (f.type) {
      case 'rel': f.args.forEach(a => termVars(a, acc)); break;
      case 'eq': termVars(f.a, acc); termVars(f.b, acc); break;
      case 'not': allVars(f.a, acc); break;
      case 'bin': allVars(f.a, acc); allVars(f.b, acc); break;
      case 'q': acc.add(f.v); allVars(f.a, acc); break;
    }
    return acc;
  }
  const isSentence = f => freeVars(f).size === 0;
  // Set .binder on every variable node: the quantifier node binding it, or null if free.
  function annotate(f, env = {}) {
    const tv = t => {
      if (t.type === 'var') t.binder = env[t.name] || null;
      else if (t.type === 'fn') t.args.forEach(tv);
    };
    switch (f.type) {
      case 'rel': f.args.forEach(tv); break;
      case 'eq': tv(f.a); tv(f.b); break;
      case 'not': annotate(f.a, env); break;
      case 'bin': annotate(f.a, env); annotate(f.b, env); break;
      case 'q': annotate(f.a, Object.assign({}, env, { [f.v]: f })); break;
    }
    return f;
  }
  // Variable occurrences in print order (not counting the variable right after a quantifier).
  function occurrences(f) { return fsegs(f).filter(s => s.kind === 'var').map(s => s.node); }

  /* ---------- substitution ---------- */
  function cloneT(t, flag) {
    if (t.type === 'var') { const v = { type: 'var', name: t.name }; const fl = flag || t.flag; if (fl) v.flag = fl; return v; }
    if (t.type === 'const') return { type: 'const', name: t.name };
    const r = { type: 'fn', name: t.name, args: t.args.map(a => cloneT(a, flag)) };
    if (t.infix) r.infix = true;
    return r;
  }
  function cloneF(f) {
    switch (f.type) {
      case 'rel': { const r = { type: 'rel', name: f.name, args: f.args.map(a => cloneT(a)) }; if (f.infix) r.infix = true; return r; }
      case 'eq': return { type: 'eq', a: cloneT(f.a), b: cloneT(f.b) };
      case 'not': return { type: 'not', a: cloneF(f.a) };
      case 'bin': return { type: 'bin', op: f.op, a: cloneF(f.a), b: cloneF(f.b) };
      case 'q': { const r = { type: 'q', q: f.q, v: f.v, a: cloneF(f.a) }; if (f.renamed) r.renamed = true; return r; }
    }
  }
  function substT(t, x, s, flag) {
    if (t.type === 'var') return t.name === x ? cloneT(s, flag) : cloneT(t);
    if (t.type === 'const') return cloneT(t);
    const r = { type: 'fn', name: t.name, args: t.args.map(a => substT(a, x, s, flag)) };
    if (t.infix) r.infix = true;
    return r;
  }
  function fresh(v, used) {
    for (const c of ['z', 'w', 'u', 'v', 'y', 'x']) if (!used.has(c)) return c;
    let k = 1;
    while (used.has(v + k)) k++;
    return v + k;
  }
  // φ[t/x]. safe = true renames bound variables to avoid capture; safe = false is naive textual replacement.
  function subst(f, x, t, safe = true, flag = 'sub') {
    const st = u => substT(u, x, t, flag);
    switch (f.type) {
      case 'rel': { const r = { type: 'rel', name: f.name, args: f.args.map(st) }; if (f.infix) r.infix = true; return r; }
      case 'eq': return { type: 'eq', a: st(f.a), b: st(f.b) };
      case 'not': return { type: 'not', a: subst(f.a, x, t, safe, flag) };
      case 'bin': return { type: 'bin', op: f.op, a: subst(f.a, x, t, safe, flag), b: subst(f.b, x, t, safe, flag) };
      case 'q': {
        if (f.v === x) return cloneF(f);
        const tv = termVars(t);
        if (safe && tv.has(f.v) && freeVars(f.a).has(x)) {
          const used = new Set([...tv, ...allVars(f.a), x]);
          const z = fresh(f.v, used);
          const body = subst(f.a, f.v, { type: 'var', name: z }, true, 'ren');
          return { type: 'q', q: f.q, v: z, renamed: true, a: subst(body, x, t, safe, flag) };
        }
        return { type: 'q', q: f.q, v: f.v, a: subst(f.a, x, t, safe, flag) };
      }
    }
  }

  /* ---------- semantics ---------- */
  // A structure: { n, rels: {name: fn}, funcs: {name: fn}, consts: {name: value} }, domain = {0, …, n-1}.
  function checkLang(f, M) {
    const ct = t => {
      if (t.type === 'const' && !(M.consts && t.name in M.consts)) throw new FolError(`The constant “${t.name}” is not in this language`, `常元“${t.name}”不在这个语言里`);
      if (t.type === 'fn') {
        const fn = M.funcs && M.funcs[t.name];
        if (!fn) throw new FolError(`The function symbol “${t.name}” is not in this language`, `函数符号“${t.name}”不在这个语言里`);
        if (fn.length !== t.args.length) throw new FolError(`“${t.name}” takes ${fn.length} argument(s)`, `“${t.name}”应带 ${fn.length} 个参数`);
        t.args.forEach(ct);
      }
    };
    switch (f.type) {
      case 'rel': {
        const R = M.rels && M.rels[f.name];
        const names = Object.keys(M.rels || {}).join(', ');
        if (!R) throw new FolError(`The relation symbol “${f.name}” is not in this language (available: ${names || 'none'}, and =)`, `关系符号“${f.name}”不在这个语言里（可用的有：${names || '无'}，以及 =）`);
        if (R.length !== f.args.length) throw new FolError(`“${f.name}” is ${R.length}-ary but has ${f.args.length} argument(s)`, `“${f.name}”是 ${R.length} 元关系，却给了 ${f.args.length} 个参数`);
        f.args.forEach(ct);
        break;
      }
      case 'eq': ct(f.a); ct(f.b); break;
      case 'not': checkLang(f.a, M); break;
      case 'bin': checkLang(f.a, M); checkLang(f.b, M); break;
      case 'q': checkLang(f.a, M); break;
    }
  }
  function evalT(t, M, s) {
    if (t.type === 'var') {
      if (!(t.name in s)) throw new FolError(`Variable ${t.name} is free and the assignment gives it no value`, `变元 ${t.name} 是自由的，而赋值没有给它指定值`);
      return s[t.name];
    }
    if (t.type === 'const') {
      if (M.consts && t.name in M.consts) return M.consts[t.name];
      throw new FolError(`The constant “${t.name}” is not in this language`, `常元“${t.name}”不在这个语言里`);
    }
    const fn = M.funcs && M.funcs[t.name];
    if (!fn) throw new FolError(`The function symbol “${t.name}” is not in this language`, `函数符号“${t.name}”不在这个语言里`);
    return fn(...t.args.map(a => evalT(a, M, s)));
  }
  function holds(f, M, s = {}) {
    switch (f.type) {
      case 'rel': return !!M.rels[f.name](...f.args.map(a => evalT(a, M, s)));
      case 'eq': return evalT(f.a, M, s) === evalT(f.b, M, s);
      case 'not': return !holds(f.a, M, s);
      case 'bin': {
        const a = holds(f.a, M, s);
        if (f.op === 'and') return a && holds(f.b, M, s);
        if (f.op === 'or') return a || holds(f.b, M, s);
        if (f.op === 'imp') return !a || holds(f.b, M, s);
        return a === holds(f.b, M, s);
      }
      case 'q': {
        for (let e = 0; e < M.n; e++) {
          const r = holds(f.a, M, Object.assign({}, s, { [f.v]: e }));
          if (f.q === 'all' && !r) return false;
          if (f.q === 'ex' && r) return true;
        }
        return f.q === 'all';
      }
    }
  }
  // Step-by-step Tarski evaluation (short-circuiting), as a list of enter/exit events.
  function trace(f, M, s = {}, limit = 700) {
    const ev = [];
    let over = false;
    function go(g, s, d) {
      if (ev.length >= limit) { over = true; throw 'limit'; }
      const enter = { kind: 'enter', f: g, s, d };
      ev.push(enter);
      let v, w = null;
      switch (g.type) {
        case 'rel': case 'eq': v = holds(g, M, s); break;
        case 'not': v = !go(g.a, s, d + 1); break;
        case 'bin': {
          const a = go(g.a, s, d + 1);
          if (g.op === 'and') v = a && go(g.b, s, d + 1);
          else if (g.op === 'or') v = a || go(g.b, s, d + 1);
          else if (g.op === 'imp') v = !a || go(g.b, s, d + 1);
          else v = a === go(g.b, s, d + 1);
          break;
        }
        case 'q': {
          v = g.q === 'all';
          for (let e = 0; e < M.n; e++) {
            const r = go(g.a, Object.assign({}, s, { [g.v]: e }), d + 1);
            if (g.q === 'all' && !r) { v = false; w = e; break; }
            if (g.q === 'ex' && r) { v = true; w = e; break; }
          }
          break;
        }
      }
      ev.push({ kind: 'exit', f: g, s, d, v, w, enter });
      return v;
    }
    let value = null;
    try { value = go(f, s, 0); } catch (e) { if (e !== 'limit') throw e; }
    return { ev, over, value };
  }

  /* ---------- evaluation game ---------- */
  // 'claim' = the player currently claiming the formula is true chooses; 'opp' = the other player chooses.
  function gameStep(f) {
    switch (f.type) {
      case 'rel': case 'eq': return { kind: 'atom' };
      case 'not': return { kind: 'swap', next: f.a };
      case 'bin':
        if (f.op === 'or') return { kind: 'pick', by: 'claim', opts: [f.a, f.b] };
        if (f.op === 'and') return { kind: 'pick', by: 'opp', opts: [f.a, f.b] };
        if (f.op === 'imp') return { kind: 'pick', by: 'claim', opts: [{ type: 'not', a: f.a }, f.b] };
        return { kind: 'pick', by: 'opp', opts: [{ type: 'bin', op: 'imp', a: f.a, b: f.b }, { type: 'bin', op: 'imp', a: f.b, b: f.a }] };
      case 'q': return { kind: 'elem', by: f.q === 'ex' ? 'claim' : 'opp', v: f.v, body: f.a };
    }
  }

  /* ---------- finite graphs ---------- */
  function graph(n, edges) {
    const set = edges instanceof Set ? edges : new Set(edges.map(e => e.join(',')));
    return { n, edges: set, rels: { E: (a, b) => set.has(a + ',' + b) } };
  }
  // All directed graphs (loops allowed) with 1..maxN elements, one representative per isomorphism
  // class (the labelled graph with the smallest edge bitmask). Isomorphic graphs satisfy the same
  // sentences (§8), so checking the representatives is the same as checking every labelled graph.
  // Counts: 2, 10, 104, 3044 classes for n = 1, 2, 3, 4 (3160 in total).
  let _battery = null;
  function perms(n) {
    if (n === 0) return [[]];
    const out = [];
    perms(n - 1).forEach(p => { for (let i = 0; i <= p.length; i++) out.push([...p.slice(0, i), n - 1, ...p.slice(i)]); });
    return out;
  }
  function battery(maxN = 4) {
    if (_battery && _battery.maxN === maxN) return _battery.list;
    const out = [];
    for (let n = 1; n <= maxN; n++) {
      const P = perms(n), N2 = n * n;
      // bit (a*n+b) of a mask = edge a→b; permuted bit index for each permutation
      const maps = P.map(p => { const m = []; for (let a = 0; a < n; a++) for (let b = 0; b < n; b++) m.push(p[a] * n + p[b]); return m; });
      for (let m = 0; m < (1 << N2); m++) {
        let isMin = true;
        for (const map of maps) {
          let r = 0;
          for (let k = 0; k < N2; k++) if ((m >> k) & 1) r |= 1 << map[k];
          if (r < m) { isMin = false; break; }
        }
        if (!isMin) continue;
        const edges = [];
        for (let k = 0; k < N2; k++) if ((m >> k) & 1) edges.push([Math.floor(k / n), k % n]);
        out.push(graph(n, edges));
      }
    }
    _battery = { maxN, list: out };
    return out;
  }
  // First structure in the list where the two sentences disagree, or null.
  function firstDiff(f, g, structs) {
    for (const M of structs) if (holds(f, M) !== holds(g, M)) return M;
    return null;
  }
  // Is g an isomorphism from graph A to graph B? (g: array, A,B: graph structures)
  function isIso(A, B, g) {
    if (A.n !== B.n || g.length !== A.n) return false;
    if (new Set(g).size !== A.n || g.some(x => x === undefined || x === null || x < 0 || x >= B.n)) return false;
    for (let a = 0; a < A.n; a++) for (let b = 0; b < A.n; b++)
      if (A.rels.E(a, b) !== B.rels.E(g[a], g[b])) return false;
    return true;
  }

  return {
    FolError, tokenize, parseFormula, parseTerm, fsegs, tsegs, show, showT, isVarName,
    termVars, freeVars, allVars, isSentence, annotate, occurrences, subst, cloneF,
    checkLang, evalT, holds, trace, gameStep, graph, battery, firstDiff, isIso,
  };
})();

if (typeof module !== 'undefined' && module.exports) module.exports = FOL;

/* =====================================================================
   DOM PART
   ===================================================================== */
if (typeof document !== 'undefined') {
Lang.init();
Progress.paint();

const $ = id => document.getElementById(id);
const errHtml = e => (e && e.en) ? bi(e.en, e.zh) : String(e);
const errBox = (box, e) => { box.className = 'msg bad'; box.innerHTML = errHtml(e); };
const okBox = (box, html, kind = 'ok') => { box.className = 'msg ' + kind; box.innerHTML = html; };
const clearBox = box => { box.className = 'msg'; box.innerHTML = ''; };
const esc = s => String(s).replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;');
const M_ = s => `<span class="m">${esc(s)}</span>`;
const PAL = ['#3b5bdb', '#2f9e44', '#ae3ec9', '#f08c00', '#0c8599', '#c2255c', '#5f3dc4'];
const asgStr = s => {
  const ks = Object.keys(s);
  return ks.length ? '[' + ks.map(k => `${k}↦${s[k]}`).join(', ') + ']' : '';
};

// Symbol keyboard for first-order inputs. getInput may return the currently focused input.
function folKeys(container, getInput, extra = []) {
  container.innerHTML = '';
  ['∀', '∃', '¬', '∧', '∨', '→', '↔', '(', ')', '=', 'E(', ',', 'x', 'y', 'z', ...extra].forEach(s => {
    const b = document.createElement('button');
    b.type = 'button';
    b.textContent = s;
    b.addEventListener('mousedown', ev => ev.preventDefault());
    b.addEventListener('click', () => {
      const input = getInput();
      if (!input) return;
      const st = input.selectionStart ?? input.value.length, en = input.selectionEnd ?? input.value.length;
      input.value = input.value.slice(0, st) + s + input.value.slice(en);
      input.focus();
      input.setSelectionRange(st + s.length, st + s.length);
      input.dispatchEvent(new Event('input'));
    });
    container.appendChild(b);
  });
}
// Parse a formula and make sure it is in the language {E, =}.
const GRAPH_LANG = FOL.graph(1, []);
function parseGraphFormula(src) {
  const f = FOL.parseFormula(src);
  FOL.checkLang(f, GRAPH_LANG);
  return f;
}
function parseGraphSentence(src) {
  const f = parseGraphFormula(src);
  const fv = [...FOL.freeVars(f)];
  if (fv.length) throw new FOL.FolError(`Not a sentence: ${fv.join(', ')} occur(s) free. Bind every variable with ∀ or ∃.`, `这不是语句：${fv.join(', ')} 有自由出现。请用 ∀ 或 ∃ 约束每个变元。`);
  return f;
}

/* ================= graph view / editor ================= */
let gvCount = 0;
function GraphView(container, opts = {}) {
  const W = opts.w || 360, H = opts.h || 300, R = opts.r || 19, MAXN = opts.maxN || 6;
  const st = { n: opts.n || 0, edges: new Set((opts.edges || []).map(e => e.join(','))) };
  let sel = null, hl = new Set(), ring = new Set(), cls = {}, tags = {}, fills = {}, probe = null;
  const id = 'gv' + (++gvCount);
  const label = opts.label || (i => String(i));
  container.innerHTML = '';
  const svg = el('svg', { viewBox: `0 0 ${W} ${H}`, width: W, height: H, class: 'gsvg' }, container);
  function pos(i) {
    if (opts.pos && opts.pos[i]) return opts.pos[i];
    if (st.n === 1) return [W / 2, H / 2];
    const rad = Math.min(W, H) / 2 - (opts.pad || 50);
    const a = -Math.PI / 2 + (opts.rot || 0) + 2 * Math.PI * i / st.n;
    return [W / 2 + rad * Math.cos(a), H / 2 + rad * Math.sin(a)];
  }
  function outward(i) {
    const [x, y] = pos(i);
    let dx = x - W / 2, dy = y - H / 2, L = Math.hypot(dx, dy);
    if (L < 1) return [0, -1];
    return [dx / L, dy / L];
  }
  const norm = (x, y) => { const L = Math.hypot(x, y) || 1; return [x / L, y / L]; };
  function edgePath(a, b) {
    const [x1, y1] = pos(a), [x2, y2] = pos(b);
    if (a === b) {
      const [dx, dy] = outward(a);
      const rot = g => [dx * Math.cos(g) - dy * Math.sin(g), dx * Math.sin(g) + dy * Math.cos(g)];
      const [ax, ay] = rot(-0.5), [bx, by] = rot(0.5), [c1x, c1y] = rot(-0.75), [c2x, c2y] = rot(0.75);
      const k = 2.9;
      return `M${x1 + ax * R},${y1 + ay * R} C${x1 + c1x * R * k},${y1 + c1y * R * k} ${x1 + c2x * R * k},${y1 + c2y * R * k} ${x1 + bx * (R + 2)},${y1 + by * (R + 2)}`;
    }
    const both = st.edges.has(b + ',' + a);
    const [ux, uy] = norm(x2 - x1, y2 - y1);
    const off = both ? 17 : 0;
    const mx = (x1 + x2) / 2 - uy * off, my = (y1 + y2) / 2 + ux * off;
    const s1 = norm(mx - x1, my - y1), s2 = norm(mx - x2, my - y2);
    return `M${x1 + s1[0] * R},${y1 + s1[1] * R} Q${mx},${my} ${x2 + s2[0] * (R + 3)},${y2 + s2[1] * (R + 3)}`;
  }
  function render() {
    svg.innerHTML = '';
    const defs = el('defs', {}, svg);
    const mk = (name, color) => {
      const m = el('marker', { id: id + name, viewBox: '0 0 10 10', refX: 8, refY: 5, markerWidth: 7, markerHeight: 7, orient: 'auto' }, defs);
      el('path', { d: 'M0,0 L10,5 L0,10 z', fill: color }, m);
    };
    mk('a', '#555'); mk('ok', '#2f9e44'); mk('no', '#e03131');
    if (opts.editable) {
      const t = el('text', { x: 8, y: H - 8, class: 'ghint' }, svg);
      t.textContent = st.n ? 'click 2 nodes: edge · 依次点两点：连边' : 'click to add an element · 点击添加元素';
    }
    const gE = el('g', {}, svg), gP = el('g', {}, svg), gN = el('g', {}, svg);
    for (const e of st.edges) {
      const [a, b] = e.split(',').map(Number);
      el('path', { d: edgePath(a, b), class: 'gedge', 'marker-end': `url(#${id}a)` }, gE);
    }
    if (probe && probe.a < st.n && probe.b < st.n) {
      el('path', { d: edgePath(probe.a, probe.b), class: 'gprobe ' + (probe.ok ? 'ok' : 'no'), 'marker-end': `url(#${id}${probe.ok ? 'ok' : 'no'})` }, gP);
    }
    for (let i = 0; i < st.n; i++) {
      const [x, y] = pos(i);
      const g = el('g', { class: 'gnode' + (i === sel ? ' sel' : '') + (hl.has(i) ? ' hl' : '') + (cls[i] ? ' ' + cls[i] : ''), transform: `translate(${x},${y})` }, gN);
      if (ring.has(i)) el('circle', { r: R + 7, fill: 'none', stroke: '#f08c00', 'stroke-width': 2.5, 'stroke-dasharray': '5 4' }, g);
      const c = el('circle', { r: R, class: 'body' }, g);
      if (fills[i]) { c.style.fill = fills[i]; c.style.stroke = '#1f2430'; }
      el('text', { class: 'lab' }, g).textContent = label(i);
      if (tags[i] && tags[i].length) {
        const s = tags[i].join(',');
        const w = 12 + s.length * 7.5;
        const [dx, dy] = st.n === 1 ? [0, 1] : outward(i);
        const tg = el('g', { class: 'gtag', transform: `translate(${-dx * (R + 16)},${-dy * (R + 16)})` }, g);
        el('rect', { x: -w / 2, y: -9, width: w, height: 18, rx: 9 }, tg);
        el('text', {}, tg).textContent = s;
      }
      g.addEventListener('click', ev => { ev.stopPropagation(); nodeClick(i); });
    }
  }
  function changed() { render(); opts.onChange && opts.onChange(); }
  function nodeClick(i) {
    if (opts.onNodeClick && opts.onNodeClick(i)) return;
    if (!opts.editable) return;
    if (sel === null) { sel = i; render(); return; }
    const k = sel + ',' + i;
    if (st.edges.has(k)) st.edges.delete(k); else st.edges.add(k);
    sel = null;
    changed();
  }
  svg.addEventListener('click', () => {
    if (!opts.editable) return;
    if (sel !== null) { sel = null; render(); return; }
    if (st.n < MAXN) { st.n++; changed(); }
  });
  render();
  const api = {
    get n() { return st.n; },
    struct: () => FOL.graph(st.n, new Set(st.edges)),
    set(n, edges) { st.n = n; st.edges = new Set(edges.map(e => e.join(','))); sel = null; changed(); },
    add() { if (st.n < MAXN) { st.n++; changed(); } },
    removeLast() {
      if (st.n <= 1) return;
      st.n--;
      for (const e of [...st.edges]) if (e.split(',').map(Number).some(v => v >= st.n)) st.edges.delete(e);
      sel = null;
      changed();
    },
    clearEdges() { st.edges.clear(); changed(); },
    setHL(s) { hl = new Set(s); render(); },
    setRing(s) { ring = new Set(s); render(); },
    setCls(m) { cls = m || {}; render(); },
    setFills(m) { fills = m || {}; render(); },
    setSel(i) { sel = i; render(); },
    setTags(s) {
      tags = {};
      for (const k in (s || {})) (tags[s[k]] = tags[s[k]] || []).push(k);
      render();
    },
    setProbe(p) { probe = p; render(); },
    render,
  };
  return api;
}
function graphTools(container, gv, presets = []) {
  container.innerHTML = '';
  const add = (html, fn, cls = 'btn small') => {
    const b = document.createElement('button');
    b.className = cls;
    b.innerHTML = html;
    b.addEventListener('click', fn);
    container.appendChild(b);
  };
  add('+ ' + bil('element', '元素'), () => gv.add());
  add('− ' + bil('element', '元素'), () => gv.removeLast());
  add(bil('clear edges', '清空边'), () => gv.clearEdges());
  presets.forEach(p => add(bil(p.en, p.zh), () => gv.set(p.n, p.edges), 'btn small ghost'));
}
const PRESET_GRAPHS = {
  cycle3: { en: '3-cycle', zh: '三元环', n: 3, edges: [[0, 1], [1, 2], [2, 0]] },
  path: { en: 'path', zh: '路径', n: 4, edges: [[0, 1], [1, 2], [2, 3]] },
  star: { en: 'star', zh: '星形', n: 5, edges: [[0, 1], [0, 2], [0, 3], [0, 4]] },
  full: { en: 'complete', zh: '完全图', n: 3, edges: [[0, 0], [0, 1], [0, 2], [1, 0], [1, 1], [1, 2], [2, 0], [2, 1], [2, 2]] },
};

/* ================= winning strategy / justification ================= */
// Lines explaining why M ⊨ f[s] has the value it has (a winning strategy for the right player).
function explain(f, M, s, out = [], d = 0, budget = { n: 34 }) {
  if (budget.n <= 0) { if (budget.n === 0) out.push({ d, html: '…' }); budget.n--; return out; }
  const val = FOL.holds(f, M, s);
  const push = html => { budget.n--; out.push({ d, html }); };
  const V = val ? '<b style="color:var(--true)">✓</b>' : '<b style="color:var(--false)">✗</b>';
  const sub = Object.keys(s).length ? ` <span style="color:var(--meta)">${esc(asgStr(s))}</span>` : '';
  switch (f.type) {
    case 'rel': case 'eq': {
      push(`${M_(FOL.show(f))}${sub} ${V}`);
      break;
    }
    case 'not': explain(f.a, M, s, out, d, budget); break;
    case 'bin': {
      const a = FOL.holds(f.a, M, s), b = FOL.holds(f.b, M, s);
      push(`${M_(FOL.show(f))}${sub} ${V}`);
      if (f.op === 'and') { if (val) { explain(f.a, M, s, out, d + 1, budget); explain(f.b, M, s, out, d + 1, budget); } else explain(!a ? f.a : f.b, M, s, out, d + 1, budget); }
      else if (f.op === 'or') { if (val) explain(a ? f.a : f.b, M, s, out, d + 1, budget); else { explain(f.a, M, s, out, d + 1, budget); explain(f.b, M, s, out, d + 1, budget); } }
      else if (f.op === 'imp') { if (val) explain(!a ? f.a : f.b, M, s, out, d + 1, budget); else { explain(f.a, M, s, out, d + 1, budget); explain(f.b, M, s, out, d + 1, budget); } }
      else { explain(f.a, M, s, out, d + 1, budget); explain(f.b, M, s, out, d + 1, budget); }
      break;
    }
    case 'q': {
      const res = [];
      for (let e = 0; e < M.n; e++) res.push(FOL.holds(f.a, M, Object.assign({}, s, { [f.v]: e })));
      const one = (f.q === 'ex') === val; // a single witness / counterexample suffices
      if (one) {
        const e = res.findIndex(r => r === val);
        push(`${M_(FOL.show(f))}${sub} ${V} &nbsp;${f.q === 'ex' ? bil('witness', '证据') : bil('counterexample', '反例')} <b>${f.v} ↦ ${e}</b>`);
        explain(f.a, M, Object.assign({}, s, { [f.v]: e }), out, d + 1, budget);
      } else {
        push(`${M_(FOL.show(f))}${sub} ${V} &nbsp;${f.q === 'all' ? bil(`every choice of ${f.v} works`, `${f.v} 无论取什么都成立`) : bil(`no choice of ${f.v} works`, `${f.v} 无论取什么都不成立`)}:`);
        for (let e = 0; e < M.n; e++) explain(f.a, M, Object.assign({}, s, { [f.v]: e }), out, d + 1, budget);
      }
      break;
    }
  }
  return out;
}
const explainHtml = (f, M, s = {}) => explain(f, M, s).map(l => `<div style="padding-left:${l.d * 18}px" class="tiny">${l.html}</div>`).join('');

/* ================= §1 signature builder ================= */
(function signature() {
  const PRE = {
    graph: { en: 'Graphs', zh: '图', c: [], f: [], r: [['E', 2]] },
    order: { en: 'Orders', zh: '序', c: [], f: [], r: [['<', 2]] },
    arith: { en: 'Arithmetic', zh: '算术', c: ['0'], f: [['S', 1], ['+', 2], ['·', 2]], r: [['<', 2]] },
    group: { en: 'Groups', zh: '群', c: ['e'], f: [['·', 2], ['⁻¹', 1]], r: [] },
    sets: { en: 'Set theory', zh: '集合论', c: [], f: [], r: [['∈', 2]] },
  };
  let sig = null;
  const INFIX_R = ['<', '∈'];
  function load(k) {
    const p = PRE[k];
    sig = { c: [...p.c], f: p.f.map(x => [...x]), r: p.r.map(x => [...x]) };
    document.querySelectorAll('#sigPresets .btn').forEach(b => b.classList.toggle('sel', b.dataset.k === k));
    render();
    gen();
  }
  const logic = ['∀', '∃', '¬', '∧', '∨', '→', '↔', '=', '(', ')', ',', 'x', 'y', 'z', 'x₁', '…'];
  $('sigLogic').innerHTML = logic.map(s => `<span class="sym">${s}</span>`).join('');
  Object.entries(PRE).forEach(([k, p]) => {
    const b = document.createElement('button');
    b.className = 'btn small';
    b.dataset.k = k;
    b.innerHTML = bil(p.en, p.zh);
    b.addEventListener('click', () => load(k));
    $('sigPresets').appendChild(b);
  });
  function render() {
    const chip = (cls, name, ar, kind, idx) => `<span class="sym ${cls}">${esc(name)}${ar ? `<sup>${ar}</sup>` : ''}<span class="x" data-kind="${kind}" data-i="${idx}" title="remove">×</span></span>`;
    let h = `<div class="tiny"><b>${bil('constants', '常元符号')}</b>: ${sig.c.map((c, i) => chip('c', c, 0, 'c', i)).join('') || '<span class="muted">∅</span>'}</div>`;
    h += `<div class="tiny"><b>${bil('functions', '函数符号')}</b>: ${sig.f.map(([n, a], i) => chip('f', n, a, 'f', i)).join('') || '<span class="muted">∅</span>'}</div>`;
    h += `<div class="tiny"><b>${bil('relations', '关系符号')}</b>: ${sig.r.map(([n, a], i) => chip('r', n, a, 'r', i)).join('') || '<span class="muted">∅</span>'}</div>`;
    $('sigNon').innerHTML = h;
    $('sigNon').querySelectorAll('.x').forEach(x => x.addEventListener('click', () => {
      sig[x.dataset.kind].splice(+x.dataset.i, 1);
      render();
      gen();
    }));
    counts();
  }
  function counts() {
    // number of closed terms of height ≤ k
    const c = [BigInt(sig.c.length)];
    for (let k = 1; k <= 4; k++) {
      let s = BigInt(sig.c.length);
      sig.f.forEach(([, a]) => { s += c[k - 1] ** BigInt(a); });
      c.push(s);
    }
    let h = `<b class="tiny">${bil('Closed terms (no variables) of height ≤ k', '高度 ≤ k 的闭项（不含变元）个数')}</b><table class="cmp"><tr><th>k</th>${c.map((_, k) => `<th>${k}</th>`).join('')}</tr><tr><td>#</td>${c.map(v => `<td class="m">${v > 10n ** 12n ? '≈10^' + (v.toString().length - 1) : v.toString()}</td>`).join('')}</tr></table>`;
    if (!sig.c.length) h += `<div class="tiny muted">${bi('No constants, so there are no closed terms at all: every term contains a variable.', '没有常元，就根本没有闭项：每个项都含有变元。')}</div>`;
    else h += `<div class="tiny muted">${bi('Still countable in total: a countable union of finite sets (as in Lesson 1).', '总数仍然可数：可数个有限集之并（同第 1 课）。')}</div>`;
    $('sigCount').innerHTML = h;
  }
  const rnd = a => a[Math.floor(Math.random() * a.length)];
  function rTerm(d) {
    const leaves = [...['x', 'y', 'z'].map(v => ({ type: 'var', name: v })), ...sig.c.map(c => ({ type: 'const', name: c }))];
    if (d === 0 || !sig.f.length || Math.random() < 0.3) return rnd(leaves);
    const [name, ar] = rnd(sig.f);
    return { type: 'fn', name, args: Array.from({ length: ar }, () => rTerm(d - 1)) };
  }
  function rAtom() {
    if (!sig.r.length || Math.random() < 0.25) return `${FOL.showT(rTerm(1))} = ${FOL.showT(rTerm(1))}`;
    const [name, ar] = rnd(sig.r);
    const args = Array.from({ length: ar }, () => FOL.showT(rTerm(1)));
    return INFIX_R.includes(name) && ar === 2 ? `${args[0]} ${name} ${args[1]}` : `${name}(${args.join(',')})`;
  }
  function gen() {
    const ts = new Set();
    for (let k = 0; k < 40 && ts.size < 9; k++) ts.add(FOL.showT(rTerm(2)));
    const as = new Set();
    for (let k = 0; k < 40 && as.size < 7; k++) as.add(rAtom());
    $('sigTerms').innerHTML = [...ts].map((t, i) => `<span class="samp t pop" style="animation-delay:${i * 0.05}s">${esc(t)}</span>`).join('');
    $('sigAtoms').innerHTML = [...as].map((t, i) => `<span class="samp a pop" style="animation-delay:${i * 0.05}s">${esc(t)}</span>`).join('');
  }
  $('sigGen').addEventListener('click', gen);
  $('sigAdd').addEventListener('click', () => {
    const kind = $('sigKind').value, name = $('sigName').value.trim(), ar = Math.max(1, Math.min(3, +$('sigAr').value || 1));
    if (!name || /[\s()=,]/.test(name)) { okBox($('sigMsg'), bi('Choose a name without spaces, parentheses, commas or =.', '名字里不能有空格、括号、逗号或 =。'), 'bad'); return; }
    const taken = [...sig.c, ...sig.f.map(x => x[0]), ...sig.r.map(x => x[0])];
    if (taken.includes(name) || logic.includes(name)) { okBox($('sigMsg'), bi(`“${esc(name)}” is already used.`, `“${esc(name)}”已经被占用了。`), 'bad'); return; }
    if (kind === 'c') sig.c.push(name); else sig[kind].push([name, ar]);
    clearBox($('sigMsg'));
    render();
    gen();
  });
  load('arith');
})();

/* ================= generic tree drawer (terms) ================= */
function drawTree(container, root, kids, labelOf, kindOf) {
  container.innerHTML = '';
  const GX = 62, GY = 66, R = 21;
  let leaf = 0, maxD = 0;
  const nodes = [];
  (function walk(t, d) {
    maxD = Math.max(maxD, d);
    const n = { t, d, ch: [] };
    nodes.push(n);
    const ks = kids(t);
    if (!ks.length) n.x = leaf++;
    else { n.ch = ks.map(k => walk(k, d + 1)); n.x = n.ch.reduce((s, c) => s + c.x, 0) / n.ch.length; }
    return n;
  })(root, 0);
  const W = Math.max(leaf * GX + 40, 200), H = (maxD + 1) * GY + 30;
  const svg = el('svg', { viewBox: `0 0 ${W} ${H}`, width: W, height: H }, container);
  const px = n => 20 + GX / 2 + n.x * GX, py = n => 34 + n.d * GY;
  const gE = el('g', {}, svg), gN = el('g', {}, svg);
  nodes.forEach(n => n.ch.forEach(c => {
    c.up = el('line', { x1: px(n), y1: py(n), x2: px(c), y2: py(c), class: 'tedge fadein' }, gE);
    c.up.style.animationDelay = (c.d * 0.15) + 's';
  }));
  nodes.forEach(n => {
    const g = el('g', { class: 'tnode' + (kindOf(n.t) === 'leaf' ? ' atom' : ''), transform: `translate(${px(n)},${py(n)})` }, gN);
    const inner = el('g', { class: 'pop' }, g);
    inner.style.animationDelay = (n.d * 0.15) + 's';
    el('circle', { r: R }, inner);
    el('text', { class: 'lab' }, inner).textContent = labelOf(n.t);
    const bd = el('g', { class: 'badge', transform: `translate(${R},${-R + 2})` }, inner);
    n.bdRect = el('rect', { x: -4, y: -10, width: 22, height: 20, rx: 10, fill: '#3b5bdb' }, bd);
    n.bdText = el('text', { x: 7, y: 0, fill: '#fff', 'font-size': 12, 'font-weight': 700, 'text-anchor': 'middle', 'dominant-baseline': 'central' }, bd);
    n.g = g;
  });
  return { nodes, svg };
}

/* ================= §2 terms ================= */
(function terms() {
  const asg = { x: 2, y: 1, z: 3 };
  const STRUCTS = {
    N: { en: '𝔑 = (ℕ, 0, S, +, ·)', zh: '𝔑 = (ℕ, 0, S, +, ·)', S: v => v + 1, plus: (a, b) => a + b, times: (a, b) => a * b, c: v => +v },
    Z5: { en: 'ℤ/5ℤ: arithmetic mod 5', zh: 'ℤ/5ℤ：模 5 算术', S: v => (v + 1) % 5, plus: (a, b) => (a + b) % 5, times: (a, b) => (a * b) % 5, c: v => (+v) % 5 },
    W: { en: 'strings: 0 = "", S = append "a", + = concatenate, · undefined', zh: '字符串：0 = 空串，S = 末尾添 a，+ = 连接，· 未定义', S: v => v + 'a', plus: (a, b) => a + b, times: null, c: v => +v === 0 ? '' : null },
  };
  let cur = 'N', ast = null, token = 0;
  function bar() {
    $('termAsg').innerHTML = `<b class="tiny">${bil('assignment s', '赋值 s')}:</b>`;
    ['x', 'y', 'z'].forEach(v => {
      const box = document.createElement('span');
      box.className = 'm';
      const shown = cur === 'W' ? JSON.stringify('a'.repeat(asg[v])) : cur === 'Z5' ? asg[v] % 5 : asg[v];
      box.innerHTML = ` &nbsp;${v} ↦ <button class="btn small" data-d="-1">−</button> <b>${shown}</b> <button class="btn small" data-d="1">+</button>`;
      box.querySelectorAll('button').forEach(b => b.addEventListener('click', () => {
        asg[v] = Math.max(0, Math.min(9, asg[v] + +b.dataset.d));
        bar();
        run();
      }));
      $('termAsg').appendChild(box);
    });
    $('termStruct').innerHTML = `<b class="tiny">${bil('structure', '结构')}:</b>`;
    Object.entries(STRUCTS).forEach(([k, S]) => {
      const b = document.createElement('button');
      b.className = 'btn small' + (k === cur ? ' sel' : '');
      b.innerHTML = S.en === S.zh ? S.en : bil(S.en, S.zh);
      b.addEventListener('click', () => { cur = k; bar(); run(); });
      $('termStruct').appendChild(b);
    });
  }
  function value(t) {
    const S = STRUCTS[cur];
    if (t.type === 'var') {
      if (!(t.name in asg)) throw new FOL.FolError(`Only x, y, z have values here; “${t.name}” has none`, `这里只给 x、y、z 赋了值，“${t.name}”没有值`);
      return cur === 'W' ? 'a'.repeat(asg[t.name]) : cur === 'Z5' ? asg[t.name] % 5 : asg[t.name];
    }
    if (t.type === 'const') {
      if (t.name !== '0') throw new FOL.FolError(`The constant “${t.name}” is not in {0, S, +, ·}; the only constant is 0 (write 2 as S(S(0)))`, `常元“${t.name}”不在 {0, S, +, ·} 中；唯一的常元是 0（2 要写成 S(S(0))）`);
      const v = S.c(t.name);
      if (v === null) throw new FOL.FolError('In the string structure only the constant 0 (the empty string) is interpreted', '字符串结构中只解释了常元 0（空串）');
      return v;
    }
    const args = t.args.map(value);
    if (t.name === 'S' && args.length === 1) return S.S(args[0]);
    if (t.name === '+' && args.length === 2) return S.plus(...args);
    if (t.name === '·' && args.length === 2) {
      if (!S.times) throw new FOL.FolError('This structure does not interpret “·”, so the term has no value here. A structure must interpret every symbol of the language!', '这个结构没有解释“·”，所以该项在此没有值。结构必须解释语言中的每一个符号！');
      return S.times(...args);
    }
    throw new FOL.FolError(`“${t.name}” with ${args.length} argument(s) is not a symbol of {0, S, +, ·}`, `带 ${args.length} 个参数的“${t.name}”不是 {0, S, +, ·} 中的符号`);
  }
  const fmt = v => typeof v === 'string' ? (v === '' ? 'ε' : v.length > 4 ? `a${v.length}` : v) : String(v);
  let view = null;
  async function run() {
    if (!ast || !view) return;
    const my = ++token;
    view.nodes.forEach(n => { n.g.classList.remove('v1', 'active'); n.bdText.textContent = ''; n.g.querySelector('.badge').style.opacity = 0; n.up && n.up.classList.remove('lit1'); });
    let total;
    try { total = value(ast); } catch (e) { okBox($('termOut'), errHtml(e), 'warn'); return; }
    const order = [];
    (function post(n) { n.ch.forEach(post); order.push(n); })(view.nodes[0]);
    for (const n of order) {
      if (my !== token) return;
      const v = fmt(value(n.t));
      n.bdText.textContent = v;
      const w = Math.max(22, 10 + v.length * 8);
      n.bdRect.setAttribute('width', w);
      n.bdText.setAttribute('x', w / 2 - 4);
      n.g.querySelector('.badge').style.opacity = 1;
      n.g.classList.add('active');
      if (n.up) n.up.classList.add('lit1');
      await sleep(260);
      n.g.classList.remove('active');
    }
    const S = STRUCTS[cur];
    okBox($('termOut'), `${M_(FOL.showT(ast))}<sup>𝔐</sup>[s] = <b class="m">${esc(typeof total === 'string' ? JSON.stringify(total) : total)}</b> &nbsp; ${bil('in', '在')} ${S.en === S.zh ? S.en : bil(S.en, S.zh)}`, 'info');
  }
  function grow() {
    try {
      ast = FOL.parseTerm($('termIn').value);
      clearBox($('termErr'));
      view = drawTree($('termStage'), ast, t => t.type === 'fn' ? t.args : [], t => t.name, t => t.type === 'fn' ? 'fn' : 'leaf');
      setTimeout(run, 500);
    } catch (e) { errBox($('termErr'), e); }
  }
  $('termGo').addEventListener('click', grow);
  $('termIn').addEventListener('keydown', e => e.key === 'Enter' && grow());
  document.querySelectorAll('[data-term]').forEach(b => b.addEventListener('click', () => { $('termIn').value = b.dataset.term; grow(); }));
  bar();
  grow();
})();

/* ================= binding view (arcs) ================= */
const bindViews = new Set();
function BindView(container, f, opts = {}) {
  FOL.annotate(f);
  container.innerHTML = '';
  const line = document.createElement('div');
  line.className = 'fline';
  container.appendChild(line);
  const svg = el('svg', { class: 'arcs', width: 0, height: 0 }, container);
  const segs = FOL.fsegs(f);
  const qs = segs.filter(s => s.kind === 'q').map(s => s.node);
  const color = q => PAL[qs.indexOf(q) % PAL.length];
  let revealed = opts.reveal !== false;
  const marks = new Set();
  segs.forEach(sg => {
    const sp = document.createElement('span');
    sp.className = 'seg ' + (sg.kind === 'sym' ? 'sy' : sg.kind);
    sp.textContent = sg.text;
    sg.el = sp;
    if (sg.kind === 'var') {
      if (sg.node.flag === 'sub') sp.classList.add('sub');
      if (opts.clickable) {
        sp.classList.add('click');
        sp.addEventListener('click', () => {
          if (marks.has(sg)) marks.delete(sg); else marks.add(sg);
          sp.classList.toggle('marked', marks.has(sg));
          sp.classList.remove('right', 'wrong');
        });
      }
    }
    line.appendChild(sp);
  });
  function paint() {
    segs.forEach(sg => {
      const sp = sg.el;
      if (sg.kind === 'q') sp.style.color = revealed ? color(sg.node) : '';
      if (sg.kind !== 'var') return;
      const b = sg.node.binder;
      sp.classList.toggle('bound', revealed && !!b);
      sp.classList.toggle('free', revealed && !b);
      sp.style.color = revealed && b ? color(b) : '';
      sp.classList.toggle('cap', revealed && sg.node.flag === 'sub' && !!b);
    });
  }
  function drawArcs() {
    svg.innerHTML = '';
    svg.setAttribute('width', 0);
    svg.setAttribute('height', 0);
    if (!revealed || !container.isConnected) return;
    const c = container.getBoundingClientRect();
    if (!c.width) return;
    svg.setAttribute('width', container.scrollWidth);
    svg.setAttribute('height', container.clientHeight);
    const at = (sp, frac = 0.5) => {
      const r = sp.getBoundingClientRect();
      return { x: r.left - c.left + container.scrollLeft + r.width * frac, y: r.top - c.top, b: r.bottom - c.top };
    };
    segs.forEach(sg => {
      if (sg.kind !== 'var') return;
      const b = sg.node.binder;
      if (!b) return;
      const qs_ = segs.find(s => s.kind === 'q' && s.node === b);
      const p1 = at(qs_.el, 0.72), p2 = at(sg.el);
      const h = Math.min(66, 22 + Math.abs(p2.x - p1.x) * 0.22);
      const col = color(b);
      const path = el('path', { d: `M${p1.x},${p1.y + 3} C${p1.x},${p1.y - h} ${p2.x},${p2.y - h} ${p2.x},${p2.y + 3}`, class: 'arc', stroke: col }, svg);
      el('circle', { cx: p2.x, cy: p2.y + 2, r: 3, fill: col }, svg);
      sg.arc = path;
      if (sg.node.flag === 'sub') {
        const t = el('text', { x: p2.x, y: p2.b + 16, 'text-anchor': 'middle', class: 'caplab' }, svg);
        t.textContent = 'captured! · 被捕获';
      }
    });
  }
  function light(q) {
    container.classList.toggle('dim', !!q);
    segs.forEach(sg => {
      const on = !!q && ((sg.kind === 'q' && sg.node === q) || (sg.kind === 'var' && sg.node.binder === q));
      sg.el.classList.toggle('lit', on);
      if (sg.arc) sg.arc.classList.toggle('lit', on);
    });
  }
  segs.forEach(sg => {
    if (sg.kind === 'q') {
      sg.el.addEventListener('mouseenter', () => revealed && light(sg.node));
      sg.el.addEventListener('mouseleave', () => light(null));
    } else if (sg.kind === 'var') {
      sg.el.addEventListener('mouseenter', () => revealed && sg.node.binder && light(sg.node.binder));
      sg.el.addEventListener('mouseleave', () => light(null));
    }
  });
  paint();
  requestAnimationFrame(() => requestAnimationFrame(drawArcs));
  const api = {
    segs, marks, drawArcs,
    reveal() { revealed = true; paint(); drawArcs(); },
    varSegs: () => segs.filter(s => s.kind === 'var'),
  };
  bindViews.add(api);
  return api;
}
window.addEventListener('resize', () => bindViews.forEach(v => v.drawArcs()));
document.querySelectorAll('.lang-switch button').forEach(b => b.addEventListener('click', () => setTimeout(() => bindViews.forEach(v => v.drawArcs()), 30)));

/* ================= §3 free / bound, substitution ================= */
(function binding() {
  folKeys($('bindKeys'), () => document.activeElement && document.activeElement.classList.contains('formula') ? document.activeElement : $('bindIn'), ['<']);
  function go() {
    try {
      const f = FOL.parseFormula($('bindIn').value);
      clearBox($('bindErr'));
      BindView($('bindStage'), f);
      const fv = [...FOL.freeVars(f)];
      const bound = [...new Set(FOL.fsegs(f).filter(s => s.kind === 'q').map(s => s.node.v))];
      const both = fv.filter(v => bound.includes(v));
      let h = `${M_('FV(φ) = {' + fv.join(', ') + '}')} &nbsp;·&nbsp; ${bil('quantified variables', '被量化的变元')}: ${M_('{' + bound.join(', ') + '}')} &nbsp;·&nbsp; `;
      h += fv.length ? bil('not a sentence (it has free variables)', '不是语句（有自由变元）') : bil('a <b>sentence</b> (no free variables)', '是<b>语句</b>（没有自由变元）');
      if (both.length) h += bi(`<br>Note: ${both.join(', ')} occur(s) <b>both</b> free and bound. “Free” and “bound” are properties of <i>occurrences</i>, not of variables.`, `<br>注意：${both.join(', ')} <b>既有</b>自由出现<b>又有</b>约束出现。“自由”与“约束”说的是变元的<i>出现</i>，而不是变元本身。`);
      okBox($('bindInfo'), h, 'info');
    } catch (e) { errBox($('bindErr'), e); }
  }
  $('bindGo').addEventListener('click', go);
  $('bindIn').addEventListener('keydown', e => e.key === 'Enter' && go());
  document.querySelectorAll('[data-bind]').forEach(b => b.addEventListener('click', () => { $('bindIn').value = b.dataset.bind; go(); }));
  go();

  function sub() {
    try {
      const f = FOL.parseFormula($('subF').value);
      const x = $('subX').value.trim();
      if (!FOL.isVarName(x) || /[^A-Za-z0-9']/.test(x)) throw new FOL.FolError('The thing to replace must be a variable (u, v, w, x, y, z, …)', '被替换的必须是一个变元（u, v, w, x, y, z, …）');
      const t = FOL.parseTerm($('subT').value);
      clearBox($('subErr'));
      const naive = FOL.subst(f, x, t, false), safe = FOL.subst(f, x, t, true);
      const vn = BindView($('subNaive'), naive);
      BindView($('subSafe'), safe);
      const captured = vn.segs.filter(s => s.kind === 'var' && s.node.flag === 'sub' && s.node.binder);
      const nOcc = vn.segs.filter(s => s.kind === 'var' && s.node.flag === 'sub').length;
      const tS = FOL.showT(t);
      if (!nOcc) okBox($('subOut'), bi(`${M_(x)} has no free occurrence in φ, so φ[${esc(tS)}/${x}] = φ. (Bound occurrences are never replaced.)`, `${M_(x)} 在 φ 中没有自由出现，所以 φ[${esc(tS)}/${x}] = φ。（约束出现永远不被替换。）`), 'info');
      else if (captured.length) {
        const vs = [...new Set(captured.map(s => s.node.name))].join(', ');
        let h = bi(`<b>Capture!</b> In the naive result the substituted ${M_(vs)} falls inside a quantifier on ${M_(vs)} and gets bound, so the formula now says something different. ${M_(tS)} is <b>not free for</b> ${M_(x)} in φ. The correct substitution first renames the bound variable (green side), and the meaning is preserved.`,
          `<b>捕获！</b>朴素结果中，代进去的 ${M_(vs)} 落入了量词 ${M_(vs)} 的辖域，被约束了，公式的意思随之改变。${M_(tS)} 对 φ 中的 ${M_(x)} <b>不可代入</b>（不自由）。正确的代入先给约束变元改名（右侧绿色），意思得以保持。`);
        if (FOL.show(f) === '∃y(x < y)' && tS === 'y') h += bi(`<br>In (ℕ,&lt;): φ(x) says “something is bigger than x” (true for every x). The naive ${M_('∃y (y < y)')} says “something is smaller than itself” (false). The correct ${M_(FOL.show(safe))} says “something is bigger than y”.`,
          `<br>在 (ℕ,&lt;) 中：φ(x) 说“有比 x 大的数”（对每个 x 都真）。朴素结果 ${M_('∃y (y < y)')} 说“有数比自己小”（假）。正确结果 ${M_(FOL.show(safe))} 说“有比 y 大的数”。`);
        okBox($('subOut'), h, 'bad');
      } else okBox($('subOut'), bi(`No capture: ${M_(tS)} is free for ${M_(x)} in φ, and both methods give the same result.`, `没有捕获：${M_(tS)} 对 φ 中的 ${M_(x)} 可代入，两种做法结果相同。`), 'ok');
    } catch (e) { errBox($('subErr'), e); }
  }
  $('subGo').addEventListener('click', sub);
  ['subF', 'subX', 'subT'].forEach(id => $(id).addEventListener('keydown', e => e.key === 'Enter' && sub()));
  document.querySelectorAll('[data-sub]').forEach(b => b.addEventListener('click', () => {
    const [f, x, t] = b.dataset.sub.split('|');
    $('subF').value = f; $('subX').value = x; $('subT').value = t;
    sub();
  }));
  sub();
})();

/* ================= §4 structures & Tarski ================= */
(function tarski() {
  const gv = GraphView($('g4'), { editable: true, n: 4, edges: [[0, 1], [1, 2], [2, 0], [2, 3], [3, 3]], onChange: () => start() });
  graphTools($('g4Tools'), gv, [PRESET_GRAPHS.cycle3, PRESET_GRAPHS.path, PRESET_GRAPHS.full]);
  folKeys($('t4Keys'), () => $('t4In'));
  let tr = null, k = 0, timer = null, f = null, M = null;
  function stop() { if (timer) { clearInterval(timer); timer = null; } }
  function start() {
    stop();
    tr = null;
    clearBox($('t4Out'));
    try {
      f = parseGraphSentence($('t4In').value);
      M = gv.struct();
      clearBox($('t4Err'));
      tr = FOL.trace(f, M, {}, 700);
      k = 1;
      render();
    } catch (e) {
      errBox($('t4Err'), e);
      $('t4Trace').innerHTML = '';
      gv.setTags({}); gv.setProbe(null);
    }
  }
  function render() {
    if (!tr) return;
    const lines = [], map = new Map();
    for (let i = 0; i < k; i++) {
      const e = tr.ev[i];
      if (e.kind === 'enter') { const L = { e, res: null }; map.set(e, L); lines.push(L); }
      else map.get(e.enter).res = e;
    }
    const cur = tr.ev[k - 1];
    const curLine = cur.kind === 'enter' ? map.get(cur) : map.get(cur.enter);
    let h = '';
    lines.forEach(L => {
      const e = L.e;
      let res = '<span class="muted">?</span>', why = '';
      if (L.res) {
        res = L.res.v ? '<span class="r1">✓</span>' : '<span class="r0">✗</span>';
        if (e.f.type === 'q') {
          if (L.res.w !== null) why = e.f.q === 'ex' ? bil(`witness ${e.f.v} ↦ ${L.res.w}`, `证据 ${e.f.v} ↦ ${L.res.w}`) : bil(`counterexample ${e.f.v} ↦ ${L.res.w}`, `反例 ${e.f.v} ↦ ${L.res.w}`);
          else why = e.f.q === 'ex' ? bil(`tried all ${M.n}, none works`, `${M.n} 个全试过，都不行`) : bil(`all ${M.n} values checked`, `${M.n} 个值全部检查通过`);
        } else if (e.f.type === 'rel') {
          const a = FOL.evalT(e.f.args[0], M, e.s), b = FOL.evalT(e.f.args[1], M, e.s);
          why = L.res.v ? `(${a},${b}) ∈ E` : `(${a},${b}) ∉ E`;
        }
      }
      h += `<div class="ln${L === curLine ? ' now' : ''}" style="padding-left:${e.d * 16 + 4}px">𝔊 ⊨ ${esc(FOL.show(e.f))} <span class="asg">${esc(asgStr(e.s))}</span> ${res} <span class="why">${why}</span></div>`;
    });
    if (tr.over && k === tr.ev.length) h += `<div class="ln muted">… ${bil('trace truncated', '过程太长，已截断')}</div>`;
    $('t4Trace').innerHTML = h;
    const now = $('t4Trace').querySelector('.now');
    if (now) $('t4Trace').scrollTop = Math.max(0, now.offsetTop - $('t4Trace').clientHeight / 2);
    gv.setTags(cur.s);
    if (cur.f.type === 'rel' && cur.kind === 'exit') {
      gv.setProbe({ a: FOL.evalT(cur.f.args[0], M, cur.s), b: FOL.evalT(cur.f.args[1], M, cur.s), ok: cur.v });
    } else gv.setProbe(null);
    $('g4Asg').innerHTML = `<span class="tiny">${bil('current assignment', '当前赋值')}:</span> ` + (Object.keys(cur.s).map(v => `<span class="pill">${v} ↦ ${cur.s[v]}</span>`).join('') || '<span class="muted">∅</span>');
    if (k === tr.ev.length) {
      stop();
      const val = tr.over ? FOL.holds(f, M) : tr.value;
      okBox($('t4Out'), val ? bi(`𝔊 ⊨ ${esc(FOL.show(f))}: <b>true</b> in this graph.`, `𝔊 ⊨ ${esc(FOL.show(f))}：在这个图中<b>成立</b>。`)
        : bi(`𝔊 ⊭ ${esc(FOL.show(f))}: <b>false</b> in this graph.`, `𝔊 ⊭ ${esc(FOL.show(f))}：在这个图中<b>不成立</b>。`), val ? 'ok' : 'bad');
    }
  }
  const step = () => { if (tr && k < tr.ev.length) { k++; render(); } else stop(); };
  $('t4Start').addEventListener('click', start);
  $('t4Step').addEventListener('click', () => { stop(); if (!tr) start(); else step(); });
  $('t4Play').addEventListener('click', () => { stop(); if (!tr) start(); if (tr && k >= tr.ev.length) k = 1; timer = setInterval(step, 420); });
  $('t4All').addEventListener('click', () => { stop(); if (!tr) start(); if (tr) { k = tr.ev.length; render(); } });
  $('t4In').addEventListener('keydown', e => e.key === 'Enter' && start());
  document.querySelectorAll('[data-t4]').forEach(b => b.addEventListener('click', () => { $('t4In').value = b.dataset.t4; start(); }));
  start();
  timer = setInterval(step, 420);
})();

/* ================= §5 evaluation game ================= */
(function game() {
  let G = null, token = 0;
  const gv = GraphView($('g5'), {
    editable: true, w: 330, h: 280, n: 4, edges: [[0, 1], [1, 2], [2, 0], [3, 3]],
    onChange: () => { G = null; token++; renderCard(); clearBox($('gmStratOut')); },
    onNodeClick: i => {
      if (G && !G.over && G.pending && G.pending.st.kind === 'elem' && G.pending.chooser === G.user) { choose({ elem: i }); return true; }
      return false;
    },
  });
  graphTools($('g5Tools'), gv, [PRESET_GRAPHS.cycle3, PRESET_GRAPHS.star]);
  const other = r => r === 'V' ? 'F' : 'V';
  const ROLE = { V: ['Verifier', '验证者'], F: ['Falsifier', '证伪者'] };
  const who = r => `<span class="who ${r}">${bil(...ROLE[r])}</span>`;
  const claimer = () => G.flip ? 'F' : 'V';
  function begin(user) {
    token++;
    clearBox($('gmStratOut'));
    try {
      const f = parseGraphSentence($('gmIn').value);
      clearBox($('gmErr'));
      G = { f0: f, f, s: {}, flip: false, user, M: gv.struct(), log: [], over: null, pending: null };
      advance();
    } catch (e) { errBox($('gmErr'), e); G = null; renderCard(); }
  }
  function advance() {
    for (;;) {
      const st = FOL.gameStep(G.f);
      if (st.kind === 'atom') {
        const t = FOL.holds(G.f, G.M, G.s);
        G.over = t ? claimer() : other(claimer());
        G.log.push(bi(`Atomic ${M_(FOL.show(G.f))} under ${esc(asgStr(G.s)) || '∅'} is <b>${t ? 'true' : 'false'}</b>.`, `原子公式 ${M_(FOL.show(G.f))} 在 ${esc(asgStr(G.s)) || '∅'} 下为<b>${t ? '真' : '假'}</b>。`));
        break;
      }
      if (st.kind === 'swap') {
        G.flip = !G.flip;
        G.log.push(bi(`¬: roles swap. Now ${ROLE[claimer()][0]} claims ${M_(FOL.show(st.next))} is true.`, `¬：双方互换立场，现在${ROLE[claimer()][1]}主张 ${M_(FOL.show(st.next))} 为真。`));
        G.f = st.next;
        continue;
      }
      const chooser = st.by === 'claim' ? claimer() : other(claimer());
      G.pending = { st, chooser };
      if (chooser !== G.user) {
        const my = token;
        setTimeout(() => { if (my === token) computerMove(); }, 900);
      }
      break;
    }
    renderCard();
  }
  function computerMove() {
    const { st, chooser } = G.pending;
    const want = chooser === claimer(); // the chooser wants the chosen option to be true iff it is the claimant
    if (st.kind === 'elem') {
      let pick = -1;
      for (let a = 0; a < G.M.n; a++) if (FOL.holds(st.body, G.M, Object.assign({}, G.s, { [st.v]: a })) === want) { pick = a; break; }
      if (pick < 0) pick = Math.floor(Math.random() * G.M.n);
      choose({ elem: pick });
    } else {
      let idx = st.opts.findIndex(o => FOL.holds(o, G.M, G.s) === want);
      if (idx < 0) idx = Math.floor(Math.random() * 2);
      choose({ opt: idx });
    }
  }
  function choose(c) {
    const { st, chooser } = G.pending;
    const name = chooser === G.user ? bil('You', '你') : bil('Computer', '电脑');
    if (st.kind === 'elem') {
      G.s = Object.assign({}, G.s, { [st.v]: c.elem });
      G.f = st.body;
      G.log.push(`${name} (${ROLE[chooser][0]} · ${ROLE[chooser][1]}): ${M_(`${st.v} ↦ ${c.elem}`)}`);
    } else {
      G.f = st.opts[c.opt];
      G.log.push(`${name} (${ROLE[chooser][0]} · ${ROLE[chooser][1]}): ${M_(FOL.show(G.f))}`);
    }
    G.pending = null;
    advance();
  }
  function renderCard() {
    const card = $('gmCard');
    if (!G) {
      card.innerHTML = `<div class="muted">${bi('Choose a side to start the game.', '选择一方，开始博弈。')}</div>`;
      gv.setTags({});
      return;
    }
    gv.setTags(G.s);
    let h = `<div class="tiny">${bil('You are', '你是')} ${who(G.user)} &nbsp;·&nbsp; ${bil('computer', '电脑')}: ${who(other(G.user))}</div>`;
    h += `<div class="cur">${esc(FOL.show(G.f))} <span style="color:var(--meta);font-size:15px">${esc(asgStr(G.s))}</span></div>`;
    h += `<div class="tiny">${who(claimer())} ${bil('claims this is <b>true</b>', '主张它<b>为真</b>')}; ${who(other(claimer()))} ${bil('claims it is <b>false</b>', '主张它<b>为假</b>')}.</div>`;
    if (G.over) {
      const won = G.over === G.user;
      h += `<div class="msg ${won ? 'ok' : 'bad'}">${won ? bi('<b>You win!</b>', '<b>你赢了！</b>') : bi('<b>The computer wins.</b>', '<b>电脑赢了。</b>')} ${who(G.over)} ${bil('wins the play.', '赢得本局。')}
        ${FOL.holds(G.f0, G.M) ? bi(`The sentence is true in this graph, so Verifier has a winning strategy${G.user === 'F' ? ': as Falsifier you could not have won against perfect play' : ''}.`, `该语句在此图中为真，所以验证者有必胜策略${G.user === 'F' ? '：作为证伪者，对手不失误时你赢不了' : ''}。`)
          : bi(`The sentence is false in this graph, so Falsifier has a winning strategy${G.user === 'V' ? ': as Verifier you could not have won against perfect play' : ''}.`, `该语句在此图中为假，所以证伪者有必胜策略${G.user === 'V' ? '：作为验证者，对手不失误时你赢不了' : ''}。`)}</div>`;
    } else if (G.pending) {
      const { st, chooser } = G.pending;
      if (chooser === G.user) {
        h += `<div class="tiny" style="margin-top:6px"><b>${bil('Your move', '轮到你')}</b>: ${st.kind === 'elem' ? bil(`choose a value for ${st.v} (click a button or a node)`, `为 ${st.v} 选一个值（点按钮或点图中节点）`) : bil('choose a subformula', '选一个子公式')}</div><div class="opts" id="gmOpts"></div>`;
      } else h += `<div class="tiny muted" style="margin-top:6px">${bil('The computer is choosing…', '电脑正在选择……')}</div>`;
    }
    h += `<div class="glog">${G.log.map(l => `<div>${l}</div>`).join('')}</div>`;
    card.innerHTML = h;
    const box = $('gmOpts');
    if (box) {
      const { st } = G.pending;
      if (st.kind === 'elem') for (let a = 0; a < G.M.n; a++) {
        const b = document.createElement('button');
        b.className = 'btn small';
        b.textContent = `${st.v} ↦ ${a}`;
        b.addEventListener('click', () => choose({ elem: a }));
        box.appendChild(b);
      } else st.opts.forEach((o, i) => {
        const b = document.createElement('button');
        b.className = 'btn small';
        b.textContent = FOL.show(o);
        b.addEventListener('click', () => choose({ opt: i }));
        box.appendChild(b);
      });
    }
  }
  $('gmV').addEventListener('click', () => begin('V'));
  $('gmF').addEventListener('click', () => begin('F'));
  $('gmStrat').addEventListener('click', () => {
    try {
      const f = parseGraphSentence($('gmIn').value), M = gv.struct();
      const t = FOL.holds(f, M);
      okBox($('gmStratOut'), `${t ? bi('True, so <b>Verifier</b> wins by following this strategy:', '为真，所以<b>验证者</b>按以下策略必胜：') : bi('False, so <b>Falsifier</b> wins by following this strategy:', '为假，所以<b>证伪者</b>按以下策略必胜：')}${explainHtml(f, M)}`, 'info');
    } catch (e) { errBox($('gmErr'), e); }
  });
  document.querySelectorAll('[data-gm]').forEach(b => b.addEventListener('click', () => { $('gmIn').value = b.dataset.gm; G = null; token++; renderCard(); clearBox($('gmStratOut')); }));
  renderCard();
})();

/* ================= §6 definable sets ================= */
(function definable() {
  const gv = GraphView($('g6'), { editable: true, w: 340, h: 290, n: 5, edges: [[0, 1], [1, 2], [2, 2], [3, 2], [3, 0], [4, 4]], onChange: () => run() });
  graphTools($('g6Tools'), gv, [PRESET_GRAPHS.cycle3, PRESET_GRAPHS.star]);
  const presets = [
    ['has a loop', '有自环', 'E(x,x)'],
    ['is a sink', '是汇点（无出边）', '∀y ¬E(x,y)'],
    ['points to a looped element', '指向某个有自环的元素', '∃y (E(x,y) ∧ E(y,y))'],
    ['reaches all in ≤ 2 steps', '两步之内可达所有元素', '∀y (x = y ∨ E(x,y) ∨ ∃z (E(x,z) ∧ E(z,y)))'],
    ['x = x', 'x = x', 'x = x'],
  ];
  presets.forEach(([en, zh, f]) => {
    const b = document.createElement('button');
    b.className = 'btn small';
    b.innerHTML = bil(en, zh);
    b.addEventListener('click', () => { $('defIn').value = f; run(); });
    $('defPresets').appendChild(b);
  });
  function run() {
    try {
      const f = parseGraphFormula($('defIn').value);
      const fv = [...FOL.freeVars(f)];
      const bad = fv.filter(v => v !== 'x');
      if (bad.length) throw new FOL.FolError(`Only x may be free; ${bad.join(', ')} is free too.`, `只允许 x 自由出现；但 ${bad.join(', ')} 也是自由的。`);
      clearBox($('defErr'));
      const M = gv.struct();
      const set = [];
      for (let a = 0; a < M.n; a++) if (FOL.holds(f, M, { x: a })) set.push(a);
      gv.setHL(set);
      const cls = {};
      for (let a = 0; a < M.n; a++) if (!set.includes(a)) cls[a] = 'out';
      gv.setCls(cls);
      let h = `${M_('φ(𝔊) = {' + set.join(', ') + '}')} &nbsp; (${set.length} / ${M.n})`;
      if (!fv.length) h += bi('<br>φ has no free variable, so it defines either everything or nothing.', '<br>φ 没有自由变元，所以它定义的要么是全体，要么是空集。');
      okBox($('defOut'), h, 'info');
    } catch (e) { errBox($('defErr'), e); }
  }
  $('defIn').addEventListener('input', run);
  run();
})();

/* ================= §7 number lines ================= */
(function numberLines() {
  const svg = $('nlSvg');
  const ROWS = [
    { k: 'N', name: '(ℕ, <)', y: 95, x: v => 150 + v * 80, lo: 0, hi: 8 },
    { k: 'Z', name: '(ℤ, <)', y: 235, x: v => 470 + v * 80, lo: -4, hi: 4 },
    { k: 'Q', name: '(ℚ, <)', y: 375, x: v => 470 + v * 80, lo: -4, hi: 4 },
  ];
  const T = (x, y, s, a = {}) => { const t = el('text', Object.assign({ x, y, 'text-anchor': 'middle', 'font-size': 13 }, a), svg); t.textContent = s; return t; };
  function base() {
    svg.innerHTML = '';
    ROWS.forEach(r => {
      T(14, r.y + 5, r.name, { 'text-anchor': 'start', 'font-size': 16, 'font-weight': 700 });
      if (r.k === 'Q') {
        el('line', { x1: r.x(-4.4), x2: r.x(4.4), y1: r.y, y2: r.y, stroke: '#1f2430', 'stroke-width': 2.5 }, svg);
        for (let q = -16; q <= 16; q++) el('line', { x1: r.x(q / 4), x2: r.x(q / 4), y1: r.y - (q % 4 ? 4 : 8), y2: r.y + (q % 4 ? 4 : 8), stroke: '#1f2430', 'stroke-width': q % 4 ? 1 : 2 }, svg);
        for (let q = -8; q <= 8; q++) if (q % 2) el('line', { x1: r.x(q / 8), x2: r.x(q / 8), y1: r.y - 2, y2: r.y + 2, stroke: '#888' }, svg);
      } else {
        el('line', { x1: r.x(r.lo) - 10, x2: r.x(r.hi) + 10, y1: r.y, y2: r.y, stroke: '#ddd', 'stroke-width': 1.5, 'stroke-dasharray': '2 5' }, svg);
        for (let v = r.lo; v <= r.hi; v++) el('circle', { cx: r.x(v), cy: r.y, r: 6, fill: '#1f2430' }, svg);
      }
      for (let v = r.lo; v <= r.hi; v++) T(r.x(v), r.y + 24, String(v), { fill: '#666' });
      T(r.x(r.hi) + 30, r.y + 5, '…', { fill: '#999', 'font-size': 18 });
      if (r.k !== 'N') T(r.x(r.lo) - 30, r.y + 5, '…', { fill: '#999', 'font-size': 18 });
    });
  }
  const C = { w: '#2f9e44', c: '#e03131', x: '#3b5bdb' };
  // steps: [kind, value(s), label, color]
  const SENT = [
    { en: 'least element', zh: '有最小元', f: '∃x ∀y (x = y ∨ x < y)', v: { N: 1, Z: 0, Q: 0 },
      st: { N: [['pt', 0, 'x = 0', 'w'], ['arr', 0, 8, 'every y: x ≤ y · 任意 y 都 ≥ x', 'w']],
            Z: [['pt', 1, 'x?', 'x'], ['pt', 0, 'x−1 < x', 'c'], ['pt', -1, 'x = −1?', 'x'], ['pt', -2, 'x−1 < x', 'c']],
            Q: [['pt', 1, 'x?', 'x'], ['pt', 0, 'x−1 < x', 'c'], ['pt', -1.5, 'x = −1.5?', 'x'], ['pt', -2.5, 'x−1 < x', 'c']] },
      en2: 'ℕ has 0 as least element. In ℤ and ℚ any candidate x is beaten by x − 1, so Falsifier always has an answer.',
      zh2: 'ℕ 有最小元 0。在 ℤ 和 ℚ 中，任何候选 x 都会被 x − 1 击败，证伪者总有应对。' },
    { en: 'no greatest element', zh: '没有最大元', f: '∀x ∃y x < y', v: { N: 1, Z: 1, Q: 1 },
      st: { N: [['pt', 3, 'x', 'x'], ['pt', 4, 'y = x+1', 'w']], Z: [['pt', -2, 'x', 'x'], ['pt', -1, 'y = x+1', 'w']], Q: [['pt', 1.5, 'x', 'x'], ['pt', 2.5, 'y = x+1', 'w']] },
      en2: 'True in all three: whatever x Falsifier picks, Verifier answers y = x + 1.',
      zh2: '三者都成立：证伪者无论选哪个 x，验证者都回应 y = x + 1。' },
    { en: 'dense', zh: '稠密', f: '∀x ∀y (x < y → ∃z (x < z ∧ z < y))', v: { N: 0, Z: 0, Q: 1 },
      st: { N: [['pt', 2, 'x', 'x'], ['pt', 3, 'y', 'x'], ['gap', 2, 3, 'no z · 没有 z', 'c']],
            Z: [['pt', 0, 'x', 'x'], ['pt', 1, 'y', 'x'], ['gap', 0, 1, 'no z · 没有 z', 'c']],
            Q: [['pt', 0, 'x', 'x'], ['pt', 1, 'y', 'x'], ['pt', 0.5, 'z = (x+y)/2', 'w'], ['pt', 0.25, '(x+z)/2', 'w']] },
      en2: 'Between consecutive integers there is nothing, so ℕ and ℤ are not dense. In ℚ the midpoint (x+y)/2 always works, and you can keep halving forever.',
      zh2: '相邻整数之间什么也没有，所以 ℕ 和 ℤ 不稠密。在 ℚ 中中点 (x+y)/2 总是可行，而且可以无限地对分下去。' },
    { en: 'immediate successors', zh: '每个元素有直接后继', f: '∀x ∃y (x < y ∧ ¬∃z (x < z ∧ z < y))', v: { N: 1, Z: 1, Q: 0 },
      st: { N: [['pt', 4, 'x', 'x'], ['pt', 5, 'y = x+1', 'w'], ['gap', 4, 5, 'nothing between · 中间无元素', 'w']],
            Z: [['pt', -1, 'x', 'x'], ['pt', 0, 'y = x+1', 'w'], ['gap', -1, 0, 'nothing between · 中间无元素', 'w']],
            Q: [['pt', 0, 'x', 'x'], ['pt', 2, 'y?', 'x'], ['pt', 1, 'z', 'c'], ['pt', 0.5, 'y = 1/2?', 'x'], ['pt', 0.25, 'z', 'c']] },
      en2: 'In ℕ and ℤ, x + 1 is the immediate successor. In ℚ every candidate y > x is spoiled by z = (x+y)/2: density is exactly what rules out immediate successors.',
      zh2: '在 ℕ 和 ℤ 中，x + 1 就是直接后继。在 ℚ 中，任何候选 y > x 都会被 z = (x+y)/2 破坏：正是稠密性排除了直接后继。' },
    { en: 'no least element', zh: '没有最小元', f: '∀x ∃y y < x', v: { N: 0, Z: 1, Q: 1 },
      st: { N: [['pt', 0, 'x = 0', 'c'], ['gap', -0.45, 0, 'nothing below · 下面没有了', 'c']], Z: [['pt', 2, 'x', 'x'], ['pt', 1, 'y = x−1', 'w']], Q: [['pt', 0.5, 'x', 'x'], ['pt', -0.5, 'y = x−1', 'w']] },
      en2: 'Falsifier wins in ℕ by choosing x = 0. Note this is not literally the negation of “least element”, yet over linear orders it is equivalent to it.',
      zh2: '在 ℕ 中，证伪者选 x = 0 即胜。注意它在字面上并不是“有最小元”的否定，但在线序中两者等价。' },
  ];
  let token = 0;
  async function play(k) {
    const my = ++token;
    const S = SENT[k];
    document.querySelectorAll('#nlBtns .btn').forEach((b, i) => b.classList.toggle('sel', i === k));
    $('nlSent').innerHTML = esc(S.f);
    clearBox($('nlOut'));
    base();
    await sleep(200);
    for (const r of ROWS) {
      const steps = S.st[r.k];
      for (let j = 0; j < steps.length; j++) {
        if (my !== token) return;
        const [kind, a, b, c, d] = steps[j];
        const lvl = 18 + j * 17;
        if (kind === 'pt') {
          const col = C[c];
          const g = el('g', { class: 'pop' }, svg);
          el('circle', { cx: r.x(a), cy: r.y, r: 9, fill: 'none', stroke: col, 'stroke-width': 3 }, g);
          el('line', { x1: r.x(a), x2: r.x(a), y1: r.y - 9, y2: r.y - lvl + 4, stroke: col, 'stroke-width': 1.5 }, g);
          const t = el('text', { x: r.x(a), y: r.y - lvl, 'text-anchor': 'middle', 'font-size': 13, 'font-weight': 700, fill: col, stroke: '#fbfaf6', 'stroke-width': 4, 'paint-order': 'stroke' }, g);
          t.textContent = b;
        } else if (kind === 'gap') {
          const col = C[d];
          const g = el('g', { class: 'fadein' }, svg);
          el('rect', { x: r.x(a) + 8, y: r.y - 7, width: r.x(b) - r.x(a) - 16, height: 14, rx: 6, fill: col, opacity: 0.25 }, g);
          const t = el('text', { x: (r.x(a) + r.x(b)) / 2, y: r.y + 42, 'text-anchor': 'middle', 'font-size': 12, 'font-weight': 700, fill: col }, g);
          t.textContent = c;
        } else if (kind === 'arr') {
          const col = C[d];
          const g = el('g', { class: 'fadein' }, svg);
          el('line', { x1: r.x(a) + 12, x2: r.x(b), y1: r.y - 34, y2: r.y - 34, stroke: col, 'stroke-width': 2.5 }, g);
          el('path', { d: `M${r.x(b)},${r.y - 40} L${r.x(b) + 10},${r.y - 34} L${r.x(b)},${r.y - 28} z`, fill: col }, g);
          const t = el('text', { x: (r.x(a) + r.x(b)) / 2, y: r.y - 42, 'text-anchor': 'middle', 'font-size': 12, 'font-weight': 700, fill: col }, g);
          t.textContent = c;
        }
        await sleep(650);
      }
      if (my !== token) return;
      const ok = S.v[r.k];
      const g = el('g', { class: 'pop' }, svg);
      el('rect', { x: 850, y: r.y - 17, width: 76, height: 34, rx: 10, fill: ok ? '#d3f9d8' : '#ffe3e3', stroke: ok ? '#2f9e44' : '#e03131', 'stroke-width': 2 }, g);
      const t = el('text', { x: 888, y: r.y + 6, 'text-anchor': 'middle', 'font-size': 17, 'font-weight': 800, fill: ok ? '#2f9e44' : '#e03131' }, g);
      t.textContent = ok ? '⊨ ✓' : '⊭ ✗';
      await sleep(300);
    }
    okBox($('nlOut'), bi(S.en2, S.zh2), 'info');
  }
  SENT.forEach((S, k) => {
    const b = document.createElement('button');
    b.className = 'btn small';
    b.innerHTML = bil(S.en, S.zh);
    b.addEventListener('click', () => play(k));
    $('nlBtns').appendChild(b);
  });
  play(2);
})();

/* ================= §8 isomorphism ================= */
(function iso() {
  const G1 = { n: 4, edges: [[0, 1], [1, 2], [2, 0], [2, 3], [3, 3]] };
  const PI = [2, 0, 3, 1];
  const G2 = { n: 4, edges: G1.edges.map(([a, b]) => [PI[a], PI[b]]) };
  const LET = i => 'abcd'[i];
  let map = [null, null, null, null], selL = null;
  const L = GraphView($('isoL'), { n: 4, edges: G1.edges, w: 300, h: 260, onNodeClick: i => { selL = i; paint(); return true; } });
  const R = GraphView($('isoR'), {
    n: 4, edges: G2.edges, w: 300, h: 260, label: LET, rot: 0.6,
    onNodeClick: j => {
      if (selL === null) { okBox($('isoMsg'), bi('First click an element of 𝔊 (left), then its image in ℌ.', '先点 𝔊（左边）的一个元素，再点它在 ℌ 中的像。'), 'info'); return true; }
      for (let i = 0; i < 4; i++) if (map[i] === j) map[i] = null;
      map[selL] = j;
      selL = null;
      clearBox($('isoMsg'));
      paint();
      return true;
    },
  });
  function paint() {
    const fl = {}, fr = {};
    map.forEach((j, i) => { if (j !== null) { fl[i] = PAL[i] + '33'; fr[j] = PAL[i] + '33'; } });
    L.setFills(fl); R.setFills(fr);
    L.setSel(selL);
    $('isoMap').innerHTML = 'π: ' + map.map((j, i) => `${i} ↦ ${j === null ? '?' : LET(j)}`).join(', ');
  }
  $('isoCheck').addEventListener('click', () => {
    if (map.some(j => j === null)) { okBox($('isoMsg'), bi('π must be defined on every element of 𝔊 (and be a bijection).', 'π 必须在 𝔊 的每个元素上都有定义（而且是双射）。'), 'warn'); return; }
    const A = FOL.graph(4, G1.edges), B = FOL.graph(4, G2.edges);
    if (FOL.isIso(A, B, map)) { okBox($('isoMsg'), bi('✓ π is an isomorphism: every edge goes to an edge and every non-edge to a non-edge. (It is the only one: element 3 is the only one with a loop, which pins everything down.)', '✓ π 是同构：边映到边，非边映到非边。（而且它是唯一的：3 是唯一带自环的元素，这把其余元素也都定死了。）')); return; }
    const bad = [];
    for (let a = 0; a < 4; a++) for (let b = 0; b < 4; b++) if (A.rels.E(a, b) !== B.rels.E(map[a], map[b]))
      bad.push(A.rels.E(a, b) ? bi(`edge ${a}→${b} goes to ${LET(map[a])}→${LET(map[b])}, which is not an edge`, `边 ${a}→${b} 映成 ${LET(map[a])}→${LET(map[b])}，但后者不是边`)
        : bi(`non-edge ${a}→${b} goes to the edge ${LET(map[a])}→${LET(map[b])}`, `非边 ${a}→${b} 映成了边 ${LET(map[a])}→${LET(map[b])}`));
    okBox($('isoMsg'), bi('✗ Not an isomorphism:', '✗ 不是同构：') + bad.slice(0, 3).map(b => `<div class="tiny">• ${b}</div>`).join(''), 'bad');
  });
  $('isoClear').addEventListener('click', () => { map = [null, null, null, null]; selL = null; clearBox($('isoMsg')); paint(); });
  $('isoShow').addEventListener('click', () => { map = [...PI]; selL = null; paint(); okBox($('isoMsg'), bi('π = (0↦c, 1↦a, 2↦d, 3↦b). Hint for finding it: start with the unique looped element, then follow the edges.', 'π = (0↦c, 1↦a, 2↦d, 3↦b)。找法提示：从唯一带自环的元素入手，再顺着边往下推。'), 'info'); });
  paint();
  // proof steps
  const steps = [...document.querySelectorAll('#isoProof .step')];
  let k = 1;
  steps[0].classList.add('on');
  $('isoNext').addEventListener('click', () => { if (k < steps.length) steps[k++].classList.add('on'); if (k === steps.length) $('isoNext').disabled = true; });
  $('isoAll').addEventListener('click', () => { steps.forEach(s => s.classList.add('on')); k = steps.length; $('isoNext').disabled = true; });

  // four structures
  const H1 = { n: 4, edges: [[0, 1], [1, 2], [2, 3], [3, 0]] }, H2 = { n: 4, edges: [[0, 1], [1, 0], [2, 3], [3, 2]] };
  GraphView($('isoH1'), { n: 4, edges: H1.edges, w: 240, h: 210, pad: 45 });
  GraphView($('isoH2'), { n: 4, edges: H2.edges, w: 240, h: 210, pad: 45 });
  const structs = [['𝔊', G1], ['ℌ', G2], ['𝔎₁', H1], ['𝔎₂', H2]].map(([n, g]) => [n, FOL.graph(g.n, g.edges)]);
  const hist = [];
  function evalAll() {
    try {
      const f = parseGraphSentence($('isoS').value);
      clearBox($('isoErr'));
      const vals = structs.map(([, M]) => FOL.holds(f, M));
      hist.unshift({ s: FOL.show(f), vals });
      if (hist.length > 6) hist.pop();
      let h = `<table class="cmp"><tr><th>σ</th>${structs.map(([n]) => `<th>${n}</th>`).join('')}</tr>`;
      hist.forEach((r, i) => {
        h += `<tr class="${i === 0 ? 'fadein' : ''}"><td class="m">${esc(r.s)}</td>${r.vals.map(v => `<td><span class="verdict ${v ? 't' : 'f'}">${v ? '✓' : '✗'}</span></td>`).join('')}</tr>`;
      });
      h += '</table>';
      const v = hist[0].vals;
      if (v[2] !== v[3]) h += `<div class="msg ok">${bi('This sentence separates 𝔎₁ and 𝔎₂, which proves they are <b>not</b> isomorphic. Meanwhile 𝔊 and ℌ always agree.', '这个语句把 𝔎₁ 和 𝔎₂ 区分开了，这就证明了它们<b>不</b>同构。而 𝔊 与 ℌ 的结果总是一致。')}</div>`;
      else h += `<div class="msg info">${bi('𝔊 and ℌ agree, as the theorem guarantees. 𝔎₁ and 𝔎₂ also agree on this one; try another sentence.', '𝔊 与 ℌ 结果一致，正如定理所保证。𝔎₁ 与 𝔎₂ 在这个语句上也一致，换一个试试。')}</div>`;
      $('isoTable').innerHTML = h;
    } catch (e) { errBox($('isoErr'), e); }
  }
  $('isoEval').addEventListener('click', evalAll);
  $('isoS').addEventListener('keydown', e => e.key === 'Enter' && evalAll());
  document.querySelectorAll('[data-iso]').forEach(b => b.addEventListener('click', () => { $('isoS').value = b.dataset.iso; evalAll(); }));
  $('isoS').value = '∃x E(x,x)';
  evalAll();
  $('isoS').value = '∀x ∃y E(x,y)';
  evalAll();
})();

/* ================= E1 free occurrences ================= */
(function e1() {
  const srcs = ['∀x (E(x,y) → ∃y E(y,x)) ∧ E(x,z)', '∃x (x = y ∧ ∀y (E(y,x) ∨ E(x,y))) ∨ ∀z E(z,y)'];
  const views = srcs.map((s, i) => BindView($(i ? 'e1b' : 'e1a'), FOL.parseFormula(s), { reveal: false, clickable: true }));
  let revealed = false;
  function grade(show) {
    let ok = true, wrongN = 0, missed = 0;
    views.forEach(v => v.varSegs().forEach(sg => {
      const free = !sg.node.binder;
      if (show) { if (free) v.marks.add(sg); else v.marks.delete(sg); sg.el.classList.toggle('marked', free); }
      const m = v.marks.has(sg);
      sg.el.classList.remove('right', 'wrong');
      if (m && free) sg.el.classList.add('right');
      else if (m && !free) { sg.el.classList.add('wrong'); ok = false; wrongN++; }
      else if (!m && free) { ok = false; missed++; }
    }));
    return { ok, wrongN, missed };
  }
  $('e1Check').addEventListener('click', () => {
    const r = grade(false);
    if (r.ok) {
      views.forEach(v => v.reveal());
      okBox($('e1Msg'), bi('✓ Exactly right. The arcs show why: in the first formula the y inside E(x,y) is outside the scope of ∃y, and the last x is outside ∀x. FV = {x, y, z} and {y} respectively.', '✓ 完全正确。弧线说明了原因：第一个公式中 E(x,y) 里的 y 不在 ∃y 的辖域内，最后那个 x 也不在 ∀x 的辖域内。两式的自由变元分别是 {x, y, z} 和 {y}。'));
      if (!revealed) Progress.mark('L3E1');
    } else okBox($('e1Msg'), bi(`Not yet: ${r.wrongN} marked occurrence(s) are actually bound (red), and ${r.missed} free occurrence(s) are still unmarked. For each occurrence, walk outwards: is there a quantifier on the same variable whose scope contains it?`,
      `还不对：有 ${r.wrongN} 个被标记的出现其实是约束的（红色），还有 ${r.missed} 个自由出现没标出来。对每个出现，从里往外看：有没有同名变元的量词，其辖域包含它？`), 'bad');
  });
  $('e1Show').addEventListener('click', () => {
    revealed = true;
    grade(true);
    views.forEach(v => v.reveal());
    okBox($('e1Msg'), bi('Free occurrences are marked. First formula: y in E(x,y), and x, z in the final E(x,z), so FV = {x, y, z}. Second formula: the y in x = y, and the last y, so FV = {y}.', '自由出现已标出。第一个公式：E(x,y) 中的 y，以及末尾 E(x,z) 中的 x、z，所以 FV = {x, y, z}。第二个公式：x = y 中的 y 和最后一个 y，所以 FV = {y}。'), 'info');
  });
})();

/* ================= E2 evaluate on a graph ================= */
(function e2() {
  const G = { n: 4, edges: [[0, 1], [1, 2], [2, 0], [3, 2], [2, 3]] };
  GraphView($('e2G'), { n: 4, edges: G.edges, w: 280, h: 250 });
  const M = FOL.graph(G.n, G.edges);
  const items = ['∀x ∃y E(x,y)', '∃x ∀y E(y,x)', '∃x E(x,x)', '∀x ∀y (E(x,y) → E(y,x))', '∃x ∃y ∃z (E(x,y) ∧ E(y,z) ∧ E(z,x))'];
  const solved = items.map(() => false);
  const revealed = items.map(() => false);
  items.forEach((src, i) => {
    const f = FOL.parseFormula(src), ans = FOL.holds(f, M);
    const row = document.createElement('div');
    row.className = 'tf';
    row.innerHTML = `<div class="stmt">(${'abcde'[i]}) &nbsp;${esc(FOL.show(f))}</div>
      <button class="btn small" data-v="1">${bil('True', '成立')}</button>
      <button class="btn small" data-v="0">${bil('False', '不成立')}</button>
      <button class="btn small ghost" data-v="show">${bil('Show answer', '看答案')}</button>
      <div style="flex-basis:100%"><div class="msg"></div></div>`;
    $('e2List').appendChild(row);
    row.querySelectorAll('button').forEach(b => b.addEventListener('click', () => {
      const show = b.dataset.v === 'show', msg = row.querySelector('.msg');
      if (show) revealed[i] = true;
      const guess = show ? ans : b.dataset.v === '1';
      if (guess === ans) {
        okBox(msg, (show ? '' : '✓ ') + (ans ? bi('<b>True.</b> Verifier\'s strategy:', '<b>成立。</b>验证者的策略：') : bi('<b>False.</b> Falsifier\'s strategy:', '<b>不成立。</b>证伪者的策略：')) + explainHtml(f, M), show ? 'info' : 'ok');
        if (show || revealed[i]) return;
        solved[i] = true;
        if (solved.every(Boolean)) Progress.mark('L3E2');
      } else okBox(msg, bi('✗ Not quite. Play it as a game in your head: who picks first, and what would they pick?', '✗ 不对。在脑子里把它当博弈来下：谁先选？他会选什么？'), 'bad');
    }));
  });
})();

/* ================= E3 separate two structures ================= */
(function e3() {
  const pairs = [
    { A: { n: 3, edges: [[0, 1], [1, 1], [1, 2]] }, B: { n: 3, edges: [[0, 1], [1, 2], [2, 0]] }, ans: '∃x E(x,x)',
      en: 'Warm-up.', zh: '热身。' },
    { A: { n: 3, edges: [[0, 1], [1, 2], [2, 0]] }, B: { n: 3, edges: [[0, 1], [1, 2], [0, 2]] }, ans: '∀x ∃y E(x,y)',
      en: 'Same size, same number of edges, no loops.', zh: '元素个数相同、边数相同、都没有自环。' },
    { A: { n: 2, edges: [] }, B: { n: 3, edges: [] }, ans: '∀x ∀y ∀z (x = y ∨ x = z ∨ y = z)',
      en: 'No edges at all: only = can help.', zh: '根本没有边：只能靠等词 =。' },
  ];
  const solved = pairs.map(() => false);
  const revealed = pairs.map(() => false);
  pairs.forEach((p, i) => {
    const box = document.createElement('div');
    box.className = 'e4item';
    box.innerHTML = `<div class="prompt"><b>(${'abc'[i]})</b> ${bi(p.en, p.zh)}</div>
      <div class="row" style="align-items:center"><div class="mini"><div class="m">𝔄</div><div class="ga"></div></div><div class="mini"><div class="m">𝔅</div><div class="gb"></div></div>
      <div class="col"><div class="toolbar"><input class="formula" style="min-width:260px" placeholder="σ">
      <button class="btn primary small chk">${bil('Check', '检查')}</button><button class="btn ghost small shw">${bil('Show answer', '看答案')}</button></div><div class="msg"></div></div></div>`;
    $('e3Pairs').appendChild(box);
    GraphView(box.querySelector('.ga'), { n: p.A.n, edges: p.A.edges, w: 170, h: 150, pad: 36, r: 15 });
    GraphView(box.querySelector('.gb'), { n: p.B.n, edges: p.B.edges, w: 170, h: 150, pad: 36, r: 15 });
    const inp = box.querySelector('input'), msg = box.querySelector('.msg');
    const A = FOL.graph(p.A.n, p.A.edges), B = FOL.graph(p.B.n, p.B.edges);
    function check() {
      try {
        const f = parseGraphSentence(inp.value);
        const a = FOL.holds(f, A), b = FOL.holds(f, B);
        if (a && !b) {
          okBox(msg, bi('✓ True in 𝔄, false in 𝔅. So 𝔄 ≇ 𝔅.', '✓ 在 𝔄 中为真，在 𝔅 中为假。所以 𝔄 ≇ 𝔅。'));
          if (revealed[i]) return;
          solved[i] = true;
          if (solved.every(Boolean)) Progress.mark('L3E3');
        } else if (!a && b) okBox(msg, bi('Backwards: it is false in 𝔄 and true in 𝔅. Its negation would work!', '反了：它在 𝔄 中为假、在 𝔅 中为真。它的否定就可以！'), 'warn');
        else okBox(msg, bi(`Same verdict in both (${a ? 'true' : 'false'}), so it doesn't separate them.`, `两边结果相同（都${a ? '真' : '假'}），区分不开。`), 'bad');
      } catch (e) { errBox(msg, e); }
    }
    box.querySelector('.chk').addEventListener('click', check);
    inp.addEventListener('keydown', e => e.key === 'Enter' && check());
    box.querySelector('.shw').addEventListener('click', () => {
      revealed[i] = true;
      inp.value = p.ans;
      okBox(msg, bi(`One answer: ${M_(p.ans)}. Many others work too.`, `一个答案：${M_(p.ans)}。别的写法也可以。`), 'info');
    });
  });
})();

/* ================= E4 translations ================= */
(function e4() {
  let focus = null;
  folKeys($('e4Keys'), () => focus);
  const items = [
    ['Every element has a loop.', '每个元素都有自环。', '∀x E(x,x)'],
    ['Some element points to every element (itself included).', '有一个元素指向所有元素（包括它自己）。', '∃x ∀y E(x,y)'],
    ['E is symmetric: whenever x points to y, y points to x.', 'E 是对称的：只要 x 指向 y，y 就指向 x。', '∀x ∀y (E(x,y) → E(y,x))'],
    ['There are at least two elements.', '至少有两个元素。', '∃x ∃y ¬x = y'],
    ['There is a sink: an element with no outgoing edge.', '存在汇点：一个没有出边的元素。', '∃x ∀y ¬E(x,y)'],
    ['No two distinct elements point to each other.', '没有两个不同的元素互相指向。', '∀x ∀y (E(x,y) ∧ E(y,x) → x = y)'],
  ];
  const solved = items.map(() => false);
  const revealed = items.map(() => false);
  items.forEach(([en, zh, ans], i) => {
    const ref = FOL.parseFormula(ans);
    const box = document.createElement('div');
    box.className = 'e4item';
    box.innerHTML = `<div class="prompt"><b>${i + 1}.</b> ${bil(en, zh)}</div>
      <div class="toolbar"><input class="formula" style="min-width:320px"><button class="btn primary small chk">${bil('Check', '检查')}</button>
      <button class="btn ghost small shw">${bil('Show answer', '看答案')}</button></div><div class="msg"></div><div class="cex"></div>`;
    $('e4List').appendChild(box);
    const inp = box.querySelector('input'), msg = box.querySelector('.msg'), cex = box.querySelector('.cex');
    inp.addEventListener('focus', () => { focus = inp; });
    if (!focus) focus = inp;
    function check() {
      cex.innerHTML = '';
      try {
        const f = parseGraphSentence(inp.value);
        const M = FOL.firstDiff(f, ref, FOL.battery());
        if (!M) {
          okBox(msg, bi('✓ Agrees with the intended sentence on every directed graph with at most 4 elements (3,160 graphs up to isomorphism).', '✓ 在所有不超过 4 个元素的有向图上（同构意义下共 3160 个）都与标准答案一致。'));
          if (revealed[i]) return;
          solved[i] = true;
          if (solved.every(Boolean)) Progress.mark('L3E4');
        } else {
          const yours = FOL.holds(f, M);
          okBox(msg, bi(`✗ They disagree on the graph below: your sentence is <b>${yours ? 'true' : 'false'}</b> there, but the statement is <b>${yours ? 'false' : 'true'}</b>.`, `✗ 在下面这个图上两者不一致：你的语句在这里<b>${yours ? '成立' : '不成立'}</b>，而原句<b>${yours ? '不成立' : '成立'}</b>。`), 'bad');
          const edges = [...M.edges].map(e => e.split(',').map(Number));
          GraphView(cex, { n: M.n, edges, w: 190, h: 150, pad: 38, r: 15 });
        }
      } catch (e) { errBox(msg, e); }
    }
    box.querySelector('.chk').addEventListener('click', check);
    inp.addEventListener('keydown', e => e.key === 'Enter' && check());
    box.querySelector('.shw').addEventListener('click', () => {
      revealed[i] = true;
      cex.innerHTML = '';
      inp.value = ans;
      okBox(msg, bi(`Answer: ${M_(ans)}`, `答案：${M_(ans)}`), 'info');
    });
  });
})();

/* ================= E5 substitution ================= */
(function e5() {
  const opts = [
    { f: '∃y E(y,y)', ok: false, en: 'Captured: this says “some element has a loop”.', zh: '被捕获了：它的意思变成了“某个元素有自环”。' },
    { f: '∃z E(y,z)', ok: true, en: 'Correct: rename the bound y to a fresh z first, then substitute.', zh: '正确：先把约束变元 y 换名为新变元 z，再代入。' },
    { f: '∃y E(x,y)', ok: false, en: 'Nothing was substituted; this still talks about x.', zh: '什么也没代入，它谈论的仍然是 x。' },
    { f: '∃x E(y,x)', ok: true, en: 'Also correct! After substitution x is no longer free, so reusing x as the bound variable is harmless. It is α-equivalent to ∃z E(y,z).', zh: '同样正确！代入之后 x 已不再自由出现，所以拿 x 来作约束变元无妨。它与 ∃z E(y,z) 只差一个换名（α-等价）。' },
  ];
  const picked = new Set();
  let revealed = false;
  const box = $('e5Choices');
  opts.forEach((o, i) => {
    const b = document.createElement('button');
    b.className = 'btn choice';
    b.innerHTML = `<span class="m">${esc(o.f)}</span>`;
    b.addEventListener('click', () => { if (picked.has(i)) picked.delete(i); else picked.add(i); b.classList.toggle('sel', picked.has(i)); box.querySelectorAll('.choice').forEach(x => x.classList.remove('right', 'wrongc')); });
    box.appendChild(b);
  });
  const chk = document.createElement('div');
  chk.className = 'toolbar';
  chk.innerHTML = `<span class="tiny muted">${bil('Select all correct options (there may be more than one), then', '选出所有正确选项（可能不止一个），然后')}</span> <button class="btn primary small" id="e5Check">${bil('Check', '检查')}</button>`;
  box.appendChild(chk);
  function demo() {
    $('e5Demo').style.display = '';
    const G = { n: 2, edges: [[0, 1]] };
    const gv = GraphView($('e5G'), { n: 2, edges: G.edges, w: 220, h: 150, pad: 40 });
    const s = { x: 1, y: 0 };
    gv.setTags(s);
    const M = FOL.graph(G.n, G.edges);
    let h = `<div class="tiny">${bi('Test with s = [x↦1, y↦0]. “y has an out-neighbour” is <b>true</b> here (0 → 1).', '用赋值 s = [x↦1, y↦0] 检验。“y 有出邻居”在这里<b>成立</b>（0 → 1）。')}</div><table class="cmp">`;
    opts.forEach(o => {
      const v = FOL.holds(FOL.parseFormula(o.f), M, s);
      h += `<tr><td class="m">${esc(o.f)}</td><td><span class="verdict ${v ? 't' : 'f'}">${v ? '✓' : '✗'}</span></td><td class="tiny" style="text-align:left">${bi(o.en, o.zh)}</td></tr>`;
    });
    $('e5Tab').innerHTML = h + '</table>';
  }
  function mark(reveal) {
    const btns = box.querySelectorAll('.choice');
    opts.forEach((o, i) => {
      btns[i].classList.remove('right', 'wrongc');
      if (reveal) { btns[i].classList.toggle('right', o.ok); return; }
      if (picked.has(i)) btns[i].classList.add(o.ok ? 'right' : 'wrongc');
    });
  }
  $('e5Check').addEventListener('click', () => {
    mark(false);
    const ok = opts.every((o, i) => o.ok === picked.has(i));
    if (ok) {
      okBox($('e5Msg'), bi('✓ Right: both renamings are correct, and the table shows they mean the same thing.', '✓ 对：两种换名都正确，下表说明它们意思相同。'));
      demo();
      if (!revealed) Progress.mark('L3E5');
    } else okBox($('e5Msg'), bi('Not quite. Remember: only <i>free</i> occurrences of x get replaced, and the new y must not fall into the scope of ∃y.', '还不对。记住：只替换 x 的<i>自由</i>出现，而且代入的 y 不能落入 ∃y 的辖域。'), 'bad');
  });
  $('e5Show').addEventListener('click', () => {
    revealed = true;
    mark(true);
    okBox($('e5Msg'), bi('Correct: ∃z E(y,z) and ∃x E(y,x). The table below evaluates every option.', '正确的是 ∃z E(y,z) 和 ∃x E(y,x)。下表给出了每个选项的取值。'), 'info');
    demo();
  });
})();

/* ================= E6 definability ================= */
(function e6() {
  const G = { n: 5, edges: [[0, 1], [1, 2], [2, 2], [3, 2], [3, 4], [0, 4]] };
  const gv = GraphView($('e6G'), { n: 5, edges: G.edges, w: 310, h: 270 });
  const M = FOL.graph(G.n, G.edges);
  const items = [
    { target: [0, 3], en: 'Target {0, 3}', zh: '目标 {0, 3}', ans: '∀y ¬E(y,x)', hint: ['What do 0 and 3 have in common that no other element has? Look at incoming edges.', '0 和 3 有什么共同点是别的元素没有的？看看入边。'] },
    { target: [2, 4], en: 'Target {2, 4}', zh: '目标 {2, 4}', ans: '∃y ∃z (¬y = z ∧ E(y,x) ∧ E(z,x))', hint: ['Count incoming edges. You will need = to say “two different”.', '数一数入边。要说“两个不同的”，得用到 =。'] },
  ];
  const solved = items.map(() => false);
  const revealed = items.map(() => false);
  let active = 0;
  function focusItem(i) { active = i; gv.setRing(items[i].target); }
  items.forEach((it, i) => {
    const box = document.createElement('div');
    box.className = 'e4item';
    box.innerHTML = `<div class="prompt"><b>(${'ab'[i]})</b> ${bil(it.en, it.zh)}</div>
      <div class="toolbar"><span class="m">φ(x) =</span><input class="formula" style="min-width:260px"><button class="btn primary small chk">${bil('Check', '检查')}</button>
      <button class="btn small hnt">${bil('Hint', '提示')}</button><button class="btn ghost small shw">${bil('Show answer', '看答案')}</button></div><div class="msg"></div>`;
    $('e6List').appendChild(box);
    const inp = box.querySelector('input'), msg = box.querySelector('.msg');
    inp.addEventListener('focus', () => focusItem(i));
    function check(silent) {
      focusItem(i);
      try {
        const f = parseGraphFormula(inp.value);
        const bad = [...FOL.freeVars(f)].filter(v => v !== 'x');
        if (bad.length) throw new FOL.FolError(`Only x may be free; ${bad.join(', ')} is free too.`, `只允许 x 自由出现；但 ${bad.join(', ')} 也是自由的。`);
        const set = [];
        for (let a = 0; a < M.n; a++) if (FOL.holds(f, M, { x: a })) set.push(a);
        gv.setHL(set);
        const ok = set.length === it.target.length && set.every(a => it.target.includes(a));
        if (ok) {
          okBox(msg, bi(`✓ φ defines exactly {${set.join(', ')}}.`, `✓ φ 恰好定义了 {${set.join(', ')}}。`), silent ? 'info' : 'ok');
          if (silent || revealed[i]) return;
          solved[i] = true;
          if (solved.every(Boolean)) Progress.mark('L3E6');
        } else okBox(msg, bi(`Your φ defines {${set.join(', ')}} (gold), but the target is {${it.target.join(', ')}} (dashed ring).`, `你的 φ 定义的是 {${set.join(', ')}}（金色），而目标是 {${it.target.join(', ')}}（虚线圈）。`), 'bad');
      } catch (e) { errBox(msg, e); }
    }
    box.querySelector('.chk').addEventListener('click', () => check(false));
    inp.addEventListener('keydown', e => e.key === 'Enter' && check(false));
    box.querySelector('.hnt').addEventListener('click', () => { focusItem(i); okBox(msg, bi(...it.hint), 'info'); });
    box.querySelector('.shw').addEventListener('click', () => { revealed[i] = true; inp.value = it.ans; check(true); okBox(msg, bi(`One answer: ${M_(it.ans)}`, `一个答案：${M_(it.ans)}`), 'info'); });
  });
  focusItem(0);
})();

} // end DOM part
