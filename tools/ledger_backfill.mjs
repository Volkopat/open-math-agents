#!/usr/bin/env node
// The credit ledger, rebuilt from GitHub: one entry per pull request merged into main that added (or, for proofs,
// modified) a single file under proofs/, reductions/ or statements/. The same entries the merger appends at merge time
// (tools/ledger_entry.py) and posts to /api/ledger; the site computes the leaderboard from them (lib/ledger.ts).
// Read-only on GitHub: the squash commits of main give each pull request's number and file (git log, needs the full
// history: git fetch --unshallow), the REST API gives the author, the body (Agent:/Model: lines) and merged_at.
//
// Usage: node tools/ledger_backfill.mjs OUT_DIR [--prs CACHE.jsonl] [--ref origin/main] [--repo OWNER/NAME]
//   writes OUT_DIR/entries.jsonl, OUT_DIR/s<k>.json (to import as the Workers KV values "ledger:v1:b<k>", 1000 pull
//   requests each) and OUT_DIR/meta.json (as "ledger:v1:bmeta"; lib/ledger.ts). --prs reuses (or creates) a cache.
import { spawnSync } from "node:child_process";
import fs from "node:fs";
import path from "node:path";

const SHARD = 1000;
const args = process.argv.slice(2);
const out = args[0];
if (!out) { console.error("usage: node tools/ledger_backfill.mjs OUT_DIR [--prs CACHE.jsonl] [--ref origin/main]"); process.exit(2); }
const opt = (k, d) => { const i = args.indexOf(k); return i > 0 ? args[i + 1] : d; };
const ref = opt("--ref", "origin/main");
const cache = opt("--prs", path.join(out, "prs.jsonl"));
// The repository (owner/name): --repo, the workflow's GITHUB_REPOSITORY, or the origin remote (wherever it lives now).
const remote = spawnSync("git", ["remote", "get-url", "origin"], { encoding: "utf8" }).stdout?.trim() ?? "";
const REPO = opt("--repo", process.env.GITHUB_REPOSITORY || (remote.match(/github\.com[:/]([^/]+\/[^/]+?)(?:\.git)?\/?$/) ?? [])[1]);
if (!REPO) { console.error("cannot tell the repository: pass --repo OWNER/NAME"); process.exit(2); }
fs.mkdirSync(out, { recursive: true });

const run = (cmd, a, input) => {
  const r = spawnSync(cmd, a, { input, maxBuffer: 1 << 30, encoding: input === undefined ? "utf8" : "buffer" });
  if (r.status !== 0) throw new Error(`${cmd} ${a.join(" ")}: ${r.stderr}`);
  return r.stdout;
};

// Same rules as app/api/verdict/route.ts and lib/steps.ts.
function creditLine(body, key) {
  const m = body.match(new RegExp(`^\\s*${key}\\s*:\\s*(.+)$`, "im"));
  return m ? m[1].replace(/[<>`*_\[\]]/g, "").trim().slice(0, 80) || null : null;
}
function reductionHypotheses(src) {
  const o = [];
  const re = /^def\s+H([1-4])\s*:\s*Prop\s*:=\s*([\s\S]*?)(?=^\s*(?:(?:def|theorem|lemma|end|namespace|open|section|variable)\b|@\[|\/--)|(?![\s\S]))/gm;
  let m;
  while ((m = re.exec(src))) o[Number(m[1]) - 1] = m[2].trim();
  return o.filter((x) => x !== undefined);
}
const FILE_RE = /^(proofs|reductions|statements)\/([A-Za-z0-9_.'\-]+)\.lean$/;

// 1. Squash commits of main: "<title> (#N)" with exactly one file.
const log = run("git", ["log", ref, "--no-renames", "--format=@@%H%x09%s", "--name-status"]);
const commits = [];
for (const line of log.split("\n")) {
  if (line.startsWith("@@")) { const [sha, subj] = line.slice(2).split("\t"); commits.push({ sha, subj, files: [] }); }
  else if (line.trim() && commits.length) { const [st, p] = line.split("\t"); commits[commits.length - 1].files.push({ st, p }); }
}
const cands = new Map();
for (const c of commits) {
  const n = c.subj.match(/\(#(\d+)\)$/);
  if (!n || c.files.length !== 1) continue;
  const { st, p } = c.files[0];
  if (!FILE_RE.test(p) || !(st === "A" || (st === "M" && p.startsWith("proofs/")))) continue;
  if (!cands.has(Number(n[1]))) cands.set(Number(n[1]), { pr: Number(n[1]), sha: c.sha, path: p, status: st });
}

// 2. The merged pull requests (author, body, merged_at), cached.
if (!fs.existsSync(cache)) {
  const s = run("gh", ["api", "--paginate", `repos/${REPO}/pulls?state=closed&per_page=100&sort=created&direction=asc`,
    "--jq", '.[] | select(.merged_at != null) | {number, login: .user.login, merged_at, base: .base.ref, body: (.body // "")} | @json']);
  fs.writeFileSync(cache, s);
}
const prs = new Map();
for (const l of fs.readFileSync(cache, "utf8").split("\n")) if (l.trim()) { const d = JSON.parse(l); prs.set(d.number, d); }

// 3. Each file as merged (git cat-file --batch: one process for every file).
const list = [...cands.values()].filter((c) => prs.get(c.pr)?.base === "main").sort((a, b) => a.pr - b.pr);
const batch = run("git", ["cat-file", "--batch"], Buffer.from(list.map((c) => `${c.sha}:${c.path}\n`).join("")));
const src = [];
for (let i = 0, k = 0; k < list.length; k++) {
  const nl = batch.indexOf(10, i);
  const head = batch.subarray(i, nl).toString();
  if (/ missing$/.test(head)) { src.push(""); i = nl + 1; continue; }
  const size = Number(head.split(" ")[2]);
  src.push(batch.subarray(nl + 1, nl + 1 + size).toString("utf8"));
  i = nl + 1 + size + 1;
}

const entries = list.map((c, k) => {
  const g = prs.get(c.pr);
  const [, dir, id] = c.path.match(FILE_RE);
  const kind = dir === "reductions" ? "reduction" : dir === "statements" ? "statement" : c.status === "M" ? "shorter" : "proof";
  const body = String(g.body ?? "");
  return {
    pr: c.pr, path: c.path, kind, id, handle: String(g.login).slice(0, 39),
    agent: creditLine(body, "Agent"), model: creditLine(body, "Model"), merged_at: new Date(g.merged_at).toISOString(),
    polarity: (kind === "proof" || kind === "shorter") && /\btheorem\s+OMA\.disproof\b/.test(src[k]) ? "disproof" : "proof",
    hyps: kind === "reduction" ? reductionHypotheses(src[k]).length : null,
  };
});

fs.writeFileSync(path.join(out, "entries.jsonl"), entries.map((e) => JSON.stringify(e)).join("\n") + "\n");
const v = `bf${Date.now().toString(36)}`;
const meta = { v: 1, shards: {}, count: entries.length, at: new Date().toISOString() };
for (const e of entries) {
  const s = Math.floor(e.pr / SHARD);
  (meta.shards[s] ??= { n: 0, v }).n++;
}
for (const s of Object.keys(meta.shards)) {
  fs.writeFileSync(path.join(out, `s${s}.json`), JSON.stringify({ v, list: entries.filter((e) => Math.floor(e.pr / SHARD) === Number(s)) }));
}
fs.writeFileSync(path.join(out, "meta.json"), JSON.stringify(meta));
const by = (k) => entries.reduce((a, e) => ((a[e[k]] = (a[e[k]] ?? 0) + 1), a), {});
console.log(JSON.stringify({ entries: entries.length, kinds: by("kind"), polarity: by("polarity"), shards: meta.shards, missingFiles: src.filter((s) => !s).length }));
