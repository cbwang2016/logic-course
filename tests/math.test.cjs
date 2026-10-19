const { test } = require('node:test');
const assert = require('node:assert/strict');
const math = require('../assets/math.js');
const katex = require('../assets/vendor/katex/katex.min.js');

const cases = [
  ['ω₁^{CK}', '\\omega _{1}^{\\mathrm{CK}}'],
  ['Σ¹ₙ₊₁', '\\Sigma ^{1}_{n+1}'],
  ['H_ω₁', 'H_{\\omega _{1}}'],
  ['Sat_Σₙ', '\\mathrm{Sat}_{\\Sigma _{n}}'],
  ['ω^ω^2', '\\omega ^{\\omega ^{2}}'],
  ['ω^ε₀', '\\omega ^{\\varepsilon _{0}}'],
  ['2^{2^n}', '2^{2^{n}}'],
  ['10^20.55', '10^{20.55}'],
  ['x^{xy}', 'x^{xy}'],
  ['R_{an,exp}', 'R_{\\mathrm{an},\\exp }'],
  ['{x, y}', '\\{x, y\\}'],
  ['𝒫(𝔐) ∖ ∅', '\\mathcal{P} (\\mathfrak{M} ) \\setminus  \\varnothing '],
];
for (const [source, tex] of cases) {
  test(`preserves notation: ${source}`, () => {
    assert.equal(math.toTex(source), tex);
    assert.doesNotThrow(() => katex.renderToString(tex, { throwOnError: true }));
  });
}
test('keeps English, Chinese and accented names out of math mode', () => {
  for (const source of ['Gödel completeness', 'Löwenheim–Skolem', 'Łoś theorem', 'A formula is true', '这是一个公式']) {
    const parts = math.segments(source);
    assert.equal(parts.map(p => p.text).join(''), source);
    assert.equal(parts.filter(p => p.tex).length, 0, source);
  }
  const parts = math.segments('a Σ¹₁ formula');
  assert.deepEqual(parts.filter(p => p.tex).map(p => p.text), ['Σ¹₁']);
});
test('supports explicit inline and display LaTeX without rewriting commands', () => {
  for (const [source, display] of [['\\(\\frac{1}{2}\\)', false], ['\\[\\sum_n x_n\\]', true], ['$$x^2$$', true]]) {
    const [part] = math.segments(source);
    assert.equal(part.tex, source.slice(2, -2));
    assert.equal(part.display, display);
  }
});
test('typesets marked constants and variables without treating counters as formulas', () => {
  assert.equal(math.segments('42')[0].tex, undefined);
  assert.equal(math.segments('42', true)[0].tex, '42');
  assert.equal(math.segments('A', true)[0].tex, 'A');
});

test('keeps named and nested HTML script contents in the same math expression', () => {
  for (const source of ['R_{an,exp}', 'x^{xy}', 'ω^{ω^{ω^{2}}}', 'x^{code(y)}']) {
    const parts = math.segments(source);
    assert.equal(parts.length, 1, source);
    assert.equal(parts[0].tex, math.toTex(source));
    assert.doesNotThrow(() => katex.renderToString(parts[0].tex));
  }
});
