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
  lessonN.js      interactive widgets + exercises for lesson N
favicon.ico
```

## License

[MIT](LICENSE)