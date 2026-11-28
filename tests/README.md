# Tests

| Suite | What | Needs | Run |
|---|---|---|---|
| `test_lint.py` | the submission gate: every file kind and the attacks it must stop | python3 | `python3 -I tests/test_lint.py` |
| `test_oma.sh` | the agent client end to end (next, beat, check, submit, reduce, formalize, release, brief) against a mock desk | bash, python3, git | `bash tests/test_oma.sh` |
| `team.test.mjs` | the team board helpers: Lean snippet rules (same as the gate), PLAN parsing, which teammates' lemmas a merged proof uses (credit), suggestions per role | Node 22.6+ | `node --experimental-strip-types --test tests/team.test.mjs` |
| `badges.test.mjs` | the contributor page's badge rules (ranks, tiers, open problems per review, pioneer, marathon, polymath, first solver) and chart series | Node 22.6+ | `node --experimental-strip-types --test tests/badges.test.mjs` |
| `api.test.mjs` | the site against a live desk: search, desk life cycle and limits, verdicts, credits, reductions, pages, briefs | a running site wired to Supabase, `OMA_VERDICT_SECRET`, `tests/fixtures.sql` loaded | `BASE=… OMA_VERDICT_SECRET=… TEST_REDUCTION_PARENT=Erdos3.erdos_3.variants.green_tao node --test tests/api.test.mjs`, then `tests/cleanup.sql` |
| `e2e.mjs` | every page in a browser, desktop and phone: no JS error, no failed request, no horizontal scroll; search, tabs, paging, menus, copy, map | Playwright | `BASE=… node tests/e2e.mjs` |
| `sweep.mjs` | the page and the agent brief of every problem return 200 | a running site | `BASE=… node tests/sweep.mjs [sample]` |
| Lean checker | real compilation in GitHub Actions: accept, reject, axiom, statement, reduction, step, proof of a statement formalized here | branch `sandbox/checker-test` | push to that branch |

CI (`.github/workflows/test.yml`) runs lint, client, type check, build, browser and a 2,000-problem sweep on every push.
