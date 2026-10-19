/* Shared LaTeX presentation for legacy course notation. The lesson parsers keep
 * their original Unicode strings; only DOM text is typeset. No network needed. */
const CourseMath = (() => {
  'use strict';
  const symbols = {
    '↠':'twoheadrightarrow','⟶':'longrightarrow','▷':'triangleright',
    '≁':'nsim','≇':'ncong','⊋':'supsetneq','≮':'nless','⊈':'nsubseteq',
    '∌':'notni','≢':'not\\equiv','⊮':'nVdash','⇏':'nRightarrow','⋠':'npreceq',
    '∄':'nexists','⨆':'bigsqcup','∸':'mathbin{\\dot{-}}',
    '∛':'sqrt[3]{}','½':'frac{1}{2}','⫽':'mathbin{/\\mkern-5mu/}',
    '⟦':'mathopen{[\\![}','⟧':'mathclose{]\\!]}',
    '∖':'setminus','⟺':'Longleftrightarrow','⟹':'Longrightarrow','⟸':'Longleftarrow',
    '◁':'triangleleft','⊔':'sqcup','⊄':'not\\subset','↛':'nrightarrow','⋆':'star',
    'ϑ':'vartheta','±':'pm','∗':'ast','⊴':'unlhd','≉':'not\\approx','⊀':'nprec',
    '⋀':'bigwedge','⋁':'bigvee','♯':'sharp','＝':'mathrel{=}','＞':'mathrel{>}',
    'ā':'bar{a}','ē':'bar{e}','ȳ':'bar{y}','ẋ':'dot{x}','Ā':'bar{A}',
    '∀':'forall','∃':'exists','¬':'neg','∧':'land','∨':'lor','→':'to','←':'leftarrow',
    '↔':'leftrightarrow','⇒':'Rightarrow','⇐':'Leftarrow','⇔':'Leftrightarrow','↦':'mapsto',
    '⊢':'vdash','⊬':'nvdash','⊨':'models','⊭':'nvDash','⊥':'bot','⊤':'top',
    '∈':'in','∉':'notin','∋':'ni','⊆':'subseteq','⊂':'subset','⊊':'subsetneq',
    '⊇':'supseteq','⊃':'supset','∪':'cup','∩':'cap','⋃':'bigcup','⋂':'bigcap',
    '∅':'varnothing','ℕ':'mathbb{N}','ℤ':'mathbb{Z}','ℚ':'mathbb{Q}',
    'ℝ':'mathbb{R}','ℂ':'mathbb{C}','ℙ':'mathbb{P}','ℵ':'aleph','ℶ':'beth',
    '∞':'infty','≤':'le','≥':'ge','≠':'ne','≡':'equiv','≈':'approx','≅':'cong',
    '≺':'prec','≻':'succ','≼':'preceq','≽':'succeq','≰':'nleq','≱':'ngeq',
    '×':'times','·':'cdot','⋅':'cdot','⊕':'oplus','⊗':'otimes','∘':'circ',
    '∑':'sum','∏':'prod','√':'surd','…':'ldots','⋯':'cdots','⋮':'vdots','⋱':'ddots',
    '⟨':'langle','⟩':'rangle','⌈':'lceil','⌉':'rceil','⌊':'lfloor','⌋':'rfloor',
    '↾':'upharpoonright','↿':'upharpoonleft','↑':'uparrow','↓':'downarrow',
    '∣':'mid','∥':'parallel','∼':'sim','≃':'simeq','∝':'propto','∂':'partial',
    '□':'square','◇':'Diamond','∎':'blacksquare','⊣':'dashv','⊩':'Vdash',
    'α':'alpha','β':'beta','γ':'gamma','δ':'delta','ε':'varepsilon','ζ':'zeta',
    'η':'eta','θ':'theta','ι':'iota','κ':'kappa','λ':'lambda','μ':'mu','ν':'nu',
    'ξ':'xi','π':'pi','ρ':'rho','σ':'sigma','τ':'tau','υ':'upsilon','φ':'varphi',
    'χ':'chi','ψ':'psi','ω':'omega','Γ':'Gamma','Δ':'Delta','Θ':'Theta',
    'Λ':'Lambda','Ξ':'Xi','Π':'Pi','Σ':'Sigma','Υ':'Upsilon','Φ':'Phi','Ψ':'Psi','Ω':'Omega',
  };
  // Unicode styled alphabets also occur in model/forcing notation.
  for (const char of '𝒫𝒞𝒟𝓘𝓜𝓝𝓕𝒲𝒪𝒩𝒰𝔐𝔄𝔊𝔑𝔎𝔅𝔽ℌ𝕋𝟙𝟘𝚺𝚫𝚷') {
    const plain = char.normalize('NFKD');
    const family = '𝒫𝒞𝒟𝓘𝓜𝓝𝓕𝒲𝒪𝒩𝒰'.includes(char) ? 'mathcal' :
      '𝔐𝔄𝔊𝔑𝔎𝔅𝔽ℌ'.includes(char) ? 'mathfrak' :
      '𝕋𝟙𝟘'.includes(char) ? 'mathbb' : 'boldsymbol';
    symbols[char] = family + '{' + (symbols[plain] ? '\\' + symbols[plain] : plain) + '}';
  }
  const subChars = '₀₁₂₃₄₅₆₇₈₉₊₋₌₍₎ₐₑₕᵢⱼₖₗₘₙₒₚᵣₛₜᵤᵥₓ';
  const subPlain = '0123456789+-=()aehijklmnoprstuvx';
  const supChars = '⁰¹²³⁴⁵⁶⁷⁸⁹⁺⁻⁼⁽⁾ⁿⁱᵃᵇᶜᵈᵉᶠᵍʰʲᵏˡᵐᵒᵖʳˢᵗᵘᵛʷˣʸᶻ';
  const supPlain = '0123456789+-=()niabcdefghjklmoprstuvwxyz';
  const functions = new Set(['sin','cos','log','exp','lim','sup','inf','min','max','det','gcd']);
  const names = new Set(['Con','Prov','Prf','PA','ZF','ZFC','CH','GCH','AC','DC','AD','PD',
    'an','lex','trans','code','HOD','OD','HYP','WO','WF','CK','Def','Ord','ON','Card','cf','crit','rank','otp',
    'dom','ran','tr','tc','cl','Th','Sat','Form','Sent','Proof','Halt','BB','TREE','RCA','ACA','ATR']);
  const skip = 'script,style,textarea,input,select,option,pre:not(.m),code,[contenteditable],.no-math,.course-math,.course-math-svg';
  const options = { throwOnError: true, strict: 'ignore', trust: false, output: 'htmlAndMathml' };

  // Converts notation, not prose. Braces in the old course mean literal sets;
  // only braces following ^/_ group scripts. HTML sup/sub use those groups too.
  function toTex(source) {
    let i = 0;
    function scriptArgument() {
      if (source[i] === '{') { i++; return read('}'); }
      if (source[i] === '(') { i++; return '(' + read(')') + ')'; }
      const start = i;
      const word = source.slice(i).match(/^[A-Za-z]+|^\d+(?:\.\d+)?/);
      i += word ? word[0].length : (source.codePointAt(i) > 0xffff ? 2 : 1);
      while (i < source.length && (subChars.includes(source[i]) || supChars.includes(source[i]))) i++;
      let value = toTex(source.slice(start, i));
      // Plain-text ordinal towers use right-associative exponentiation.
      if (source[i] === '^') { i++; value += '^{' + scriptArgument() + '}'; }
      return value;
    }
    function read(until) {
      let out = '';
      while (i < source.length) {
        const c = String.fromCodePoint(source.codePointAt(i));
        i += c.length;
        if (until && c === until) break;
        if (c === '^' || c === '_') {
          out += c + '{' + scriptArgument() + '}';
        } else if (subChars.includes(c) || supChars.includes(c)) {
          const chars = subChars.includes(c) ? subChars : supChars;
          const plain = chars === subChars ? subPlain : supPlain;
          let value = plain[chars.indexOf(c)];
          while (i < source.length && chars.includes(source[i])) value += plain[chars.indexOf(source[i++])];
          out += (chars === subChars ? '_' : '^') + '{' + value + '}';
        } else if (c === '′' || c === '″' || c === '‴' || c === "'") {
          out += c === '″' ? "''" : c === '‴' ? "'''" : "'";
        } else if (symbols[c]) out += '\\' + symbols[c] + ' ';
        else if (/[A-Za-z]/.test(c)) {
          let word = c;
          while (i < source.length && /[A-Za-z]/.test(source[i])) word += source[i++];
          out += functions.has(word) ? '\\' + word + ' ' : (names.has(word) || word.length > 2) ? '\\mathrm{' + word + '}' : word;
        } else if (c === '{' || c === '}' || c === '%' || c === '#' || c === '&' || c === '$') out += '\\' + c;
        else if (c === '\\') out += '\\setminus ';
        else if (c === '−' || c === '–') out += '-';
        else if (c === '~') out += '\\sim ';
        else out += c;
      }
      return out;
    }
    return read();
  }

  // A token boundary keeps English/Chinese prose outside math mode. Delimited
  // LaTeX is always explicit; legacy symbols and short variable expressions
  // are recognized both inside .m and in previously unmarked explanations.
  function segments(text, explicit = false) {
    const pieces = [];
    const token = /\\\([\s\S]*?\\\)|\\\[[\s\S]*?\\\]|\$\$[\s\S]*?\$\$|[A-Za-zÀ-ÖØ-öø-ɏ]+|\d+(?:\.\d+)?|\s+|[^]/gu;
    const raw = [...text.matchAll(token)].map(m => m[0]);
    const tokens = [];
    for (let n = 0; n < raw.length; n++) {
      let value = raw[n];
      if ((value === '^' || value === '_') && raw[n + 1] === '{') {
        let depth = 0;
        do {
          const next = raw[++n];
          value += next;
          if (next === '{') depth++;
          if (next === '}') depth--;
        } while (depth && n + 1 < raw.length);
      }
      tokens.push(value);
    }
    const isWord = t => /^[A-Za-zÀ-ÖØ-öø-ɏ]+$/u.test(t);
    const isMath = (t, n) => t && (/^[_^]\{/.test(t) || symbols[t] || t.length === 1 && ( subChars.includes(t) || supChars.includes(t) || /[=+*/<>^_{}()[\]|−′″‴'~\\-]/.test(t)) ||
      /^\d/.test(t) || isWord(t) && (t.length === 1 || functions.has(t) || names.has(t) || /^[(_^]$/.test(tokens[n + 1] || '')));
    let run = '';
    const flush = () => {
      if (!run) return;
      const match = run.match(/^(\s*)([\s\S]*?)(\s*)$/);
      const value = match[2];
      // Punctuation, counters and English articles alone are not formulas.
      const meaningful = explicit ? /[A-Za-z0-9]/.test(value) || [...value].some(c => symbols[c]) :
        [...value].some(c => symbols[c] && !'·…←→'.includes(c)) ||
        /[=+*/<>^_]/.test(value) && /[A-Za-z0-9]/.test(value) ||
        /[₀-₉⁰¹²³⁴⁵⁶⁷⁸⁹]/.test(value) ||
        /^[b-hj-zB-HJ-Z]$/.test(value) || names.has(value);
      if (meaningful && value) {
        if (match[1]) pieces.push({ text: match[1] });
        pieces.push({ text: value, tex: toTex(value) });
        if (match[3]) pieces.push({ text: match[3] });
      } else pieces.push({ text: run });
      run = '';
    };
    for (let n = 0; n < tokens.length; n++) {
      const t = tokens[n];
      if (/^(\\\(|\\\[|\$\$)/.test(t)) {
        flush(); pieces.push({ text: t, tex: t.slice(2, -2), display: !t.startsWith('\\(') });
      } else if (isMath(t, n) || /^\s+$/.test(t) || (t === ',' || t === ':') && run) {
        // Do not absorb an article immediately before a mathematical noun.
        if (!explicit && /^[aAI]$/.test(t) && !/[=+*/<>^_({[]\s*$/.test(run) &&
            !/^\s*[=+*/<>^_]/.test(tokens.slice(n + 1, n + 3).join(''))) {
          flush(); pieces.push({ text: t });
        } else run += t;
      } else { flush(); pieces.push({ text: t }); }
    }
    flush();
    return pieces;
  }

  function mathSpan(part) {
    const span = document.createElement('span');
    span.className = 'course-math';
    span.dataset.tex = part.tex;
    if (part.display) span.classList.add('course-math-display');
    try { katex.render(part.tex, span, { ...options, displayMode: !!part.display }); }
    catch (error) {
      // Retain readable course content if an author enters invalid TeX.
      span.textContent = part.text;
      span.dataset.mathError = error.message;
    }
    return span;
  }

  function fragment(text, explicit) {
    const parts = segments(text, explicit);
    if (!parts.some(p => p.tex)) return null;
    const frag = document.createDocumentFragment();
    for (const part of parts) frag.append(part.tex ? mathSpan(part) : document.createTextNode(part.text));
    return frag;
  }

  function scriptText(node) {
    return [...node.childNodes].map(n => n.nodeType === 3 ? n.data :
      n.nodeName === 'SUP' ? '^{' + scriptText(n) + '}' :
      n.nodeName === 'SUB' ? '_{' + scriptText(n) + '}' : scriptText(n)).join('');
  }

  function renderText(node) {
    if (!node.isConnected || !node.parentElement || node.parentElement.closest(skip + ',svg,sup,sub')) return;
    let source = node.data;
    const consumed = [];
    let next = node.nextSibling;
    // Collect adjacent HTML scripts and their following text as one expression.
    while (next && (next.nodeName === 'SUP' || next.nodeName === 'SUB')) {
      source += (next.nodeName === 'SUP' ? '^{' : '_{') + scriptText(next) + '}';
      consumed.push(next);
      next = next.nextSibling;
      if (next && next.nodeType === 3) { source += next.data; consumed.push(next); next = next.nextSibling; }
    }
    const frag = fragment(source, !!node.parentElement.closest('.m,.formula-output,.keys,.tt,.sw,.ordin'));
    if (frag) { node.replaceWith(frag); consumed.forEach(n => n.remove()); }
  }

  const svgLabels = new Map();
  function renderSVG(text) {
    if (text.closest(skip) || text.querySelector('tspan')) return;
    let record = svgLabels.get(text);
    const source = text.textContent;
    const parts = segments(source, true);
    if (!parts.some(p => p.tex)) {
      if (record) {
        record.foreign.remove(); svgLabels.delete(text); text.classList.remove('course-math-source');
        if (record.ariaHidden === null) text.removeAttribute('aria-hidden');
        else text.setAttribute('aria-hidden', record.ariaHidden);
      }
      return;
    }
    if (!record) {
      const foreign = document.createElementNS('http://www.w3.org/2000/svg', 'foreignObject');
      foreign.setAttribute('class', 'course-math-svg');
      const label = document.createElementNS('http://www.w3.org/1999/xhtml', 'span');
      foreign.append(label);
      text.after(foreign);
      record = { foreign, label, ariaHidden: text.getAttribute('aria-hidden') };
      svgLabels.set(text, record);
      text.classList.add('course-math-source');
    }
    const { foreign, label } = record;
    if (record.source !== source) {
      label.replaceChildren(fragment(source, true));
      record.source = source;
    }
    const style = getComputedStyle(text);
    label.style.fontSize = style.fontSize;
    label.style.color = style.fill;
    label.style.fontWeight = style.fontWeight;
    foreign.style.opacity = style.opacity;
    foreign.style.visibility = style.visibility;
    const x = Number(text.getAttribute('x') || 0) + Number(text.getAttribute('dx') || 0);
    const y = Number(text.getAttribute('y') || 0) + Number(text.getAttribute('dy') || 0);
    const size = parseFloat(style.fontSize) || 16;
    foreign.setAttribute('x', x);
    foreign.setAttribute('y', y);
    foreign.setAttribute('width', 1);
    foreign.setAttribute('height', 1);
    foreign.setAttribute('transform', text.getAttribute('transform') || '');
    const anchor = style.textAnchor === 'middle' ? '-50%' : style.textAnchor === 'end' ? '-100%' : '0';
    const baseline = ['central','middle'].includes(style.dominantBaseline) ? '-50%' : `calc(-50% - ${size * 0.3}px)`;
    label.style.transform = `translate(${anchor}, ${baseline})`;
    // Retain the original <text> for getBBox(), tooltips and event handlers.
    text.setAttribute('aria-hidden', 'true');
  }

  function render(root = document.body) {
    if (!root.isConnected) return;
    if (root.nodeType === 3) { renderText(root); return; }
    if (root.nodeType !== 1 || root.closest(skip)) return;
    if (root.matches('svg text')) renderSVG(root);
    root.querySelectorAll('svg text').forEach(renderSVG);
    const walker = document.createTreeWalker(root, NodeFilter.SHOW_TEXT);
    const nodes = [];
    while (walker.nextNode()) nodes.push(walker.currentNode);
    nodes.forEach(renderText);
  }

  let observer;
  const pending = new Set();
  let scheduled = false;
  function flush() {
    scheduled = false;
    observer.disconnect();
    for (const [text, { foreign }] of svgLabels) {
      if (!text.isConnected) { foreign.remove(); svgLabels.delete(text); }
    }
    const roots = [...pending];
    pending.clear();
    roots.filter(root => !roots.some(other => other !== root && other.contains(root))).forEach(render);
    observe();
  }
  function observe() {
    observer.observe(document.body, { childList: true, characterData: true, subtree: true,
      attributes: true, attributeFilter: ['class','style','x','y','dx','dy','fill','font-size','transform'] });
  }
  function start() {
    if (typeof katex === 'undefined') return;
    render();
    observer = new MutationObserver(records => {
      for (const record of records) {
        const root = record.target.nodeType === 3 ? record.target.parentElement : record.target;
        if (!root || root.closest(skip)) continue;
        // Class changes on ordinary HTML (e.g. language mode) do not change
        // its math. SVG styles do affect label color and position.
        if (record.type === 'attributes' && !root.closest('svg')) continue;
        pending.add(root);
      }
      if (pending.size && !scheduled) { scheduled = true; requestAnimationFrame(flush); }
    });
    observe();
  }
  if (typeof document !== 'undefined') {
    if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', start, { once: true });
    else start();
  }
  return { toTex, segments, render };
})();
if (typeof module !== 'undefined') module.exports = CourseMath;
