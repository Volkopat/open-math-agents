// Browser tests: every page renders without JS errors or failed requests, works on a phone, and the
// interactive parts (search, menus, map, copy button) do what they say. Run: BASE=http://localhost:3123 node tests/e2e.mjs
import { createRequire } from "node:module";
const { chromium } = createRequire(import.meta.url)("playwright");

const BASE = process.env.BASE ?? "http://localhost:3123";
const api = async (p) => (await fetch(BASE + p)).json();
let failures = 0;
const ok = (name, cond, extra = "") => { console.log(`${cond ? "PASS" : "FAIL"} ${name}${cond ? "" : " " + extra}`); failures += !cond; };

const sample = async (q) => (await api(`/api/problems?limit=1&${q}`)).items[0].id;
const pages = ["/", "/map", "/board", "/programs", "/programs/Erd%C5%91s%20Problems", "/solved", "/contributors", "/feed", "/calendar", "/live",
  "/graveyard", "/status", "/news", "/news/board-open", "/papers", "/papers/how", "/letters", "/sponsors", "/prizes", "/support", "/verify", "/join", "/a/somebody"];
for (const q of ["kind=open", "kind=known", "kind=warmup", "kind=unformalized&source=Wikipedia%20list%20(not%20formalized)",
  "kind=unformalized&source=OEIS%20conjectures%20(not%20formalized)", "kind=unformalized&source=MathOverflow%20(not%20formalized)"]) {
  pages.push(`/p/${encodeURIComponent(await sample(q))}`);
}

import fs from "node:fs";
// Use a preinstalled Chromium when the environment provides one (CI installs its own with `playwright install`).
const pre = process.env.PW_CHROMIUM ?? "/opt/pw-browsers/chromium";
const browser = await chromium.launch(fs.existsSync(pre) && fs.statSync(pre).isFile() ? { executablePath: pre } : {});
for (const [label, viewport] of [["desktop", { width: 1360, height: 900 }], ["phone", { width: 390, height: 800 }]]) {
  const ctx = await browser.newContext({ viewport });
  for (const path of pages) {
    const page = await ctx.newPage();
    const errors = [];
    page.on("pageerror", (e) => errors.push("pageerror: " + e.message));
    page.on("console", (m) => { if (m.type() === "error" && !/github\.com\/.*\.png|Failed to load resource.*404/.test(m.text())) errors.push("console: " + m.text()); });
    page.on("requestfailed", (r) => { if (!r.url().includes("github.com")) errors.push("requestfailed: " + r.url()); });
    const res = await page.goto(BASE + path, { waitUntil: "networkidle" });
    const overflow = await page.evaluate(() => document.documentElement.scrollWidth - window.innerWidth);
    ok(`${label} ${path} renders`, res.status() === 200 && errors.length === 0, `${res.status()} ${errors.join(" | ")}`);
    if (label === "phone") ok(`phone ${path} has no horizontal scroll`, overflow <= 1, `overflow ${overflow}px`);
    await page.close();
  }
  await ctx.close();
}

const ctx = await browser.newContext({ viewport: { width: 1360, height: 900 }, permissions: ["clipboard-read", "clipboard-write"] });
const page = await ctx.newPage();
await page.goto(BASE + "/", { waitUntil: "networkidle" });
await page.fill("input.q", "Collatz");
await page.waitForFunction(() => document.querySelector(".count")?.textContent?.includes("results") && [...document.querySelectorAll(".row h3")].some((h) => /collatz/i.test(h.textContent)), null, { timeout: 15000 }).catch(() => {});
ok("search finds Collatz", await page.locator(".row h3", { hasText: /Collatz/i }).count() > 0);
await page.click("button.tab:has-text('not yet in Lean')");
await page.waitForTimeout(1500);
ok("tab switches to problems not yet in Lean", (await page.locator(".row .badge.unformalized").count()) > 0);
await page.fill("input.q", "");
await page.selectOption("select[aria-label=Sort]", "easiest");
await page.waitForTimeout(1500);
ok("sort select works", (await page.locator(".row").count()) > 0);
const before = await page.locator(".row").count();
await page.click("button.more");
await page.waitForTimeout(2000);
ok("'show 30 more' loads more", (await page.locator(".row").count()) > before, `${before} -> ${await page.locator(".row").count()}`);
// the three desktop menus (the phone Menu is hidden at this width)
const openMenus = () => page.evaluate(() => [...document.querySelectorAll("details.drop.desk-menu")].map((d) => d.open).join(","));
await page.click("details.drop.desk-menu >> nth=1 >> summary"); await page.waitForTimeout(150);
ok("nav menu opens", await page.locator("details.drop.desk-menu[open] .menu a").first().isVisible());
await page.click("details.drop.desk-menu >> nth=2 >> summary"); await page.waitForTimeout(150);
ok("opening another menu closes the first", (await openMenus()) === "false,false,true", await openMenus());
await page.mouse.click(30, 700); await page.waitForTimeout(150);
ok("a click outside closes the menu", (await openMenus()) === "false,false,false", await openMenus());
await page.click("details.drop.desk-menu >> nth=1 >> summary"); await page.keyboard.press("Escape"); await page.waitForTimeout(150);
ok("Escape closes the menu", (await openMenus()) === "false,false,false", await openMenus());
await page.click("details.drop.desk-menu >> nth=2 >> summary"); await page.waitForTimeout(150);
await page.click("details.drop.desk-menu[open] .menu a >> nth=0"); await page.waitForURL("**/contributors"); await page.waitForTimeout(300);
ok("choosing a link navigates and closes the menu", (await openMenus()) === "false,false,false", await openMenus());
await page.goto(BASE + "/", { waitUntil: "networkidle" });
await page.goto(BASE + "/join", { waitUntil: "networkidle" });
await page.click(".prompt button");
const clip = await page.evaluate(() => navigator.clipboard.readText()).catch(() => "");
ok("copy button copies the join line", clip.includes("join.txt"), clip);
await page.goto(BASE + "/map", { waitUntil: "networkidle" });
await page.waitForTimeout(2500);
const painted = await page.evaluate(() => { const c = document.querySelector("canvas"); if (!c) return 0; const d = c.getContext("2d").getImageData(0, 30, Math.min(300, c.width), 40).data; let n = 0; for (let i = 3; i < d.length; i += 4) n += d[i] > 0; return n; });
ok("map draws squares", painted > 100, `${painted} painted pixels`);
const id = await sample("kind=known");
await page.goto(BASE + `/p/${encodeURIComponent(id)}`, { waitUntil: "networkidle" });
ok("problem page offers the agent brief line", (await page.locator(".prompt code").first().textContent()).includes("/agent.txt"));
ok("problem page renders KaTeX", (await page.locator(".katex").count()) > 0 || !(await page.locator(".statement").textContent()).includes("$"));
await browser.close();
console.log(`\n${failures ? failures + " FAILED" : "ALL PASSED"}`);
process.exit(failures ? 1 : 0);
