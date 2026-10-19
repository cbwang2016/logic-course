/* npm ci && npx playwright install chromium && npm run test:browser
 * Optional: PLAYWRIGHT_CHROMIUM_EXECUTABLE_PATH=/path/to/chrome */
const { chromium } = require('playwright');
const assert = require('node:assert/strict');
const path = require('node:path');
const { pathToFileURL } = require('node:url');
const { readFile } = require('node:fs/promises');
const http = require('node:http');
const root = path.resolve(__dirname, '..');
const fileURL = name => pathToFileURL(path.join(root, name)).href;

(async () => {
  const browser = await chromium.launch({ executablePath: process.env.PLAYWRIGHT_CHROMIUM_EXECUTABLE_PATH });
  let server;
  try {
    const page = await browser.newPage();
    const errors = [], external = [], failed = [];
    page.on('pageerror', error => errors.push(error.message));
    page.on('requestfailed', request => failed.push(request.url()));
    await page.route(/^https?:\/\//, route => {
      if (new URL(route.request().url()).hostname === '127.0.0.1') return route.continue();
      external.push(route.request().url());
      return route.abort();
    });
    let total = 0;
    for (let n = 0; n <= 28; n++) {
      const name = n ? `lesson${n}.html` : 'index.html';
      await page.goto(fileURL(name));
      await page.evaluate(() => document.fonts.ready);
      const result = await page.evaluate(() => ({
        count: document.querySelectorAll('.katex').length,
        errors: [...document.querySelectorAll('[data-math-error]')].map(e => [e.dataset.tex, e.dataset.mathError]),
        nested: document.querySelectorAll('.course-math .course-math').length,
        inputs: [...document.querySelectorAll('input.formula')].every(e => !e.value.includes('\\mathrm')),
      }));
      assert.ok(result.count > 10, `${name}: math rendered`);
      assert.deepEqual(result.errors, [], name);
      assert.equal(result.nested, 0, `${name}: no recursive rendering`);
      assert.ok(result.inputs, `${name}: parsers retain plain notation`);
      total += result.count;
      console.log(`${name}: ${result.count} formulas`);
    }

    await page.goto(fileURL('lesson1.html'));
    await page.locator('#strictIn').fill('(p∧q)');
    await page.waitForFunction(() => document.querySelector('#strictOut .katex'));
    assert.match(await page.locator('#strictOut').textContent(), /A formula!/);
    await page.locator('#ttIn').fill('p → q');
    await page.locator('#ttGo').click();
    await page.waitForFunction(() => [...document.querySelectorAll('th .course-math')].some(e => e.dataset.tex.includes('\\to')));
    const cell = page.locator('#e1Table td.click').first();
    await cell.click();
    await page.waitForFunction(() => document.querySelector('#e1Table td.click .katex'));
    await cell.click(); // The original event handler must survive typesetting.
    await page.locator('#treeIn').fill('p ∧ q');
    await page.locator('#treeGo').click();
    await page.waitForFunction(() => [...document.querySelectorAll('.course-math-svg .course-math')].some(e => e.dataset.tex.includes('\\land')));
    for (const lang of ['zh','en','both']) {
      await page.locator(`[data-lang="${lang}"]`).click();
      assert.ok(await page.locator('body').evaluate((el, lang) => el.classList.contains('lang-' + lang), lang));
    }

    // Exercise DOM updates, nested HTML scripts, display math, opt-outs and
    // SVG labels whose source text is updated or removed by a widget.
    await page.evaluate(() => {
      const box = document.createElement('div');
      box.id = 'math-regression';
      box.innerHTML = '<span class="m" id="nested">ω<sup>ω<sup>2</sup>+1</sup></span>' +
        '<code>p ∧ q</code><span class="no-math">p ∧ q</span><input value="p ∧ q">' +
        '<span id="display">\\[\\frac{1}{2}\\]</span>' +
        '<svg><text id="svg-source" x="20" y="20">ω₁</text></svg>';
      document.body.append(box);
    });
    await page.waitForFunction(() => document.querySelector('#nested .katex'));
    assert.equal(await page.locator('#nested .course-math').getAttribute('data-tex'), '\\omega ^{\\omega ^{2}+1}');
    assert.equal(await page.locator('#math-regression code .katex, #math-regression .no-math .katex').count(), 0);
    assert.equal(await page.locator('#display .katex-display').count(), 1);
    await page.evaluate(() => {
      document.querySelector('#svg-source').textContent = 'Σ¹₂';
      document.querySelector('#nested').textContent = 'H_ω₁';
    });
    await page.waitForFunction(() => document.querySelector('#nested .course-math')?.dataset.tex === 'H_{\\omega _{1}}');
    await page.waitForFunction(() => document.querySelector('#math-regression .course-math-svg .course-math')?.dataset.tex.includes('\\Sigma'));
    assert.equal(await page.locator('#math-regression .course-math-svg').count(), 1);
    await page.locator('#svg-source').evaluate(e => e.remove());
    await page.waitForFunction(() => !document.querySelector('#math-regression .course-math-svg'));
    assert.equal(await page.locator('[data-math-error]').count(), 0);

    // Verify relative assets at the GitHub Pages subpath on a narrow viewport.
    server = http.createServer(async (req, res) => {
      try {
        const rel = decodeURIComponent(req.url.split('?')[0]).replace(/^\/logic-course\//, '');
        const file = path.resolve(root, rel);
        if (!file.startsWith(root + path.sep)) { res.writeHead(403).end(); return; }
        const mime = { '.html':'text/html', '.js':'text/javascript', '.css':'text/css', '.woff2':'font/woff2' };
        res.setHeader('Content-Type', mime[path.extname(file)] || 'application/octet-stream');
        res.end(await readFile(file));
      } catch { res.writeHead(404).end(); }
    });
    await new Promise(resolve => server.listen(0, '127.0.0.1', resolve));
    await page.setViewportSize({ width: 390, height: 844 });
    await page.goto(`http://127.0.0.1:${server.address().port}/logic-course/lesson18.html`);
    await page.evaluate(() => document.fonts.ready);
    assert.ok(await page.locator('.katex').count() > 100);
    assert.equal(await page.locator('[data-math-error]').count(), 0);
    assert.deepEqual(errors, []);
    assert.deepEqual(external, []);
    assert.deepEqual(failed, []);
    console.log(`Passed: ${total} formulas across 29 offline pages, widgets, languages, and mobile subpath hosting.`);
  } finally {
    if (server) server.close();
    await browser.close();
  }
})().catch(error => { console.error(error); process.exitCode = 1; });
