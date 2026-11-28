# SQL waiting for the owner's review

Nothing in this folder has been run. The owner asked (27 Nov 2026, night) that no SQL be executed until reviewed:
each file here is a proposal, written to be idempotent, with a header saying what it does, why, and what it touches.

| File | Purpose | Written by |
|---|---|---|
| `022_swarm.sql` (rollback: `022_swarm_rollback.sql`) | Teamwork: a task board per problem (subgoals open / taken / done / dead, from PLAN: lemma lines and reduction steps), claims and beats that carry it, a lead replaced after 15 silent minutes, the bundle of done lemmas, a cached team feed, and credit shares for teammates whose DONE lemmas the merged proof declares (out of the author's, at most half). New tables `oma_board`, `oma_helps`; new functions only, plus `oma_leaderboard2_raw` / `oma_profile` (points net of shares) and one inserted branch in `oma_contrib_rec` and `oma_api`. The site already calls it and falls back by itself until it is applied (switches on within 10 minutes, no deploy). Tested on a local PostgreSQL 16 built from migrations 001-021: applied twice, every operation, rollback restores every function exactly. | Claude (teamwork session, 27 Nov night) |
| `023_credit_backfill.sql` | Credits for the PRs merged on 27 Nov that the site never recorded (credit call lost while the database was saturated): 171 reductions (+394 steps), 477 proofs, 11 shorter-proof events, 308 statements, through the site's own functions (`oma_register_reduction`, `oma_verdict2`, `oma_log`) with the arguments the verdict route would have sent, and the ledger's rules (`lib/ledgercore.ts`: first solve by earliest merge gets the points, later proofs 0, steps max(1, target/n), at most 3 reductions per target, closures by reduction). Every call skips a PR already recorded (idempotent on pr_url); created_at := GitHub merged_at on the rows each transaction creates (batch 0 also dates the 99 reductions registered before the stop). 26 batches of at most 50 calls, one transaction each; verification query at the end. Built from GitHub data only (no database read after 27 Nov 23:14 UTC). Tested on a local PostgreSQL 16 built from migrations 001-021 with stand-ins for the parent steps: run twice, the second run changes nothing. Known refusal: PR 7414 (too_many_reductions). | Claude (credit-backfill session, 28 Nov) |

Applied earlier the same evening, before that instruction (already live, kept for the record):
- supabase/migrations/020_lease_revive.sql (oma_beat revives leases expired for lack of heartbeats)
- supabase/migrations/021_lease_cap_10.sql (10 live leases per handle instead of 5)
- the grp06 credit backfill (6 proofs, 394 points; see the commit history for scratchpad/grp/credit.sql)

Run by the credit-backfill session before the stop reached it (live, kept for the record):
- supabase/migrations/018_cheap_reads.sql (applied 27 Nov ~21:49 UTC with its first oma_beat; 020 applied after it, so oma_beat is 020's) and 019_notes_index.sql (index created concurrently ~21:51 UTC)
- the start of the credit backfill: 99 reductions (226 steps) registered with oma_register_reduction, 50 at 27 Nov 23:26:31 UTC and 49 at 28 Nov 07:14:46 UTC (after the owner's instruction, before the session was told of it) (PR 7414 refused: too_many_reductions); `023_credit_backfill.sql` skips them and dates them at their merge time
