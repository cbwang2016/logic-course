# Logic & Set Theory · 数理逻辑与集合论

An interactive, bilingual (English / 中文) course on mathematical logic and set theory — from "what is a formula?" to large cardinals at the edge of consistency. Every idea is a picture you can touch.

**Prerequisite:** Cantor's theorem and the diagonal method.

## Course map

- **Part I · Logic basics** — propositional logic; soundness, completeness, compactness; first-order logic; Gödel completeness; compactness & Löwenheim–Skolem
- **Part II · Axiomatic set theory** — Russell's paradox & ZF; building ℕ, ℤ, ℚ, ℝ; ordinals & transfinite induction; cardinals; Axiom of Choice, Zorn, Banach–Tarski
- **Part III · Limits of formal systems** — computability & the halting problem; Gödel's incompleteness theorems; Tarski's undefinability of truth
- **Part IV · Independence** — models of ZFC & the cumulative hierarchy V; Gödel's constructible universe L; forcing & the independence of CH
- **Part V · Hierarchies & large cardinals** — arithmetical & analytical hierarchies, Turing degrees; Borel & projective hierarchies; the Lévy hierarchy; fast-growing hierarchies; OD & HOD; inaccessible → measurable → Woodin → rank-into-rank, determinacy
- **Part VI · The big picture & open frontiers** — how the field fits together; CH, Ultimate L, forcing axioms, HOD, pcf; frontiers of model theory, computability & proof theory

That's **28 lessons**, each with worked examples and interactive exercises.

## Features

- 🌐 **Bilingual** — every page renders in English, 中文, or both (toggle in the header)
- 🖱️ **Interactive** — draggable figures, parse trees, truth tables, forcing conditions you can play with
- ✅ **Exercises with instant feedback** — check answers inline as you go
- 📈 **Progress tracking** — solved exercises are remembered locally (browser `localStorage`) and shown on the course map
- 🧮 **LaTeX math** — local KaTeX typesetting for lesson text, exercises, and SVG labels, including live updates
- ⚡ **Zero build step** — plain HTML/CSS/JS, works offline

## Running it

No install, no build. Just open `index.html` in a browser, or serve the folder:

```sh
python3 -m http.server 8000
# → http://localhost:8000
```

## Structure

```
index.html        course map (all 28 lessons)
lessonN.html      lesson N (N = 1…28), with exercises
assets/
  style.css       shared styles
  logic.js        shared code: language switch, progress, SVG helpers
  math.js         Unicode/HTML notation → LaTeX, live DOM typesetting
  vendor/katex/   KaTeX 0.16.22 browser assets, fonts, and license
  lessonN.js      interactive widgets + exercises for lesson N
favicon.ico
```

## Math authoring

All pages load the local KaTeX distribution and `assets/math.js`. Existing course
notation (Unicode operators, styled alphabets, superscript/subscript characters,
and HTML `<sup>`/`<sub>`) is converted to LaTeX for presentation. The exercise
parsers and input values continue to use their original notation.

For new content, explicit LaTeX is supported:

```html
<span>\(\forall x\, (P(x) \to Q(x))\)</span>
<div>\[\frac{a}{b} = c\]</div>
```

In JavaScript strings, escape backslashes or use `String.raw`:

```js
box.textContent = String.raw`\(\omega_1^{\mathrm{CK}}\)`;
```

Use `.m` for legacy formulas, especially standalone numbers or ambiguous variables
such as `A`. Mixed English/Chinese explanations remain ordinary text. Input fields,
code, non-mathematical preformatted text, and `.no-math` regions are left alone.
Native form controls and SVG tooltip text retain plain-text notation.

The shared observer typesets inserted or updated content after widget handlers run.
SVG math is drawn in adjacent `foreignObject` labels; the original text nodes remain
available for the widgets' event handlers and geometry measurements. Rendered HTML
includes MathML for accessibility. There are no CDN requests or build requirements.

## Checking changes

Optional development dependencies are only needed for tests:

```sh
npm ci
npm test
npx playwright install chromium
npm run test:browser
```

The browser check visits all 29 pages offline, rejects math parse errors and external
requests, exercises live formula/table/SVG updates and language switching, and checks
mobile loading under the GitHub Pages `/logic-course/` subpath. To use an existing
Chromium browser, set `PLAYWRIGHT_CHROMIUM_EXECUTABLE_PATH` to its executable.

## License

[MIT](LICENSE)