-- 023_credit_backfill.sql: credits for pull requests merged on 27 Nov 2026 that the site never recorded.
-- STATUS: NOT RUN. Waiting for the owner's review. Written 28 Nov 2026 by Claude (credit-backfill session, agentB).
--
-- WHY. From about 08:00 UTC on 27 Nov, and completely from 18:30 to 21:39 UTC (database saturated: every oma_api call
-- timed out), the site's POST /api/verdict failed for many merged pull requests. Their files are on main, but there is
-- no oma_reductions row (so the steps <target>.R<n>.H<k> do not exist, their pages 404 and proofs of them cannot be
-- credited), no oma_solutions row, or no 'formalized' / 'shorter' event.
--
-- WHAT. The same SQL functions the site calls, with the same arguments the site would have sent
-- (app/api/verdict/route.ts): oma_register_reduction (id <target>.R<n>, handle = PR author, module
-- 'OMAReductions.R_' + id with non-alphanumerics -> '_', the hypotheses parsed from the merged file as
-- lib/steps.ts reductionHypotheses does, points = pointsFor(difficulty, kind) from data/gen/cards.json or the
-- target step's oma_steps.points); oma_verdict2 (problem, handle, pr, 'accepted', 'disproof' if the file has
-- `theorem OMA.disproof` else 'proof', Agent / Model lines of the PR body, points); oma_log('formalized' | 'shorter').
-- Same rules as the credit ledger (lib/ledgercore.ts computeWorld), so the database ends up agreeing with it:
-- points = pointsFor(difficulty, kind) or the step's points for the first solve of a problem or step (earliest merge);
-- a proof merged after an accepted solution of the same id (another PR or a closure by reduction) gets 0 points
-- (checked at run time against created_at, which this file sets to merged_at); steps worth max(1, target points / n);
-- at most 3 reductions per target; a closure worth max(1, sum of its steps' points / 10), credited to the reduction's
-- author with the step solvers as contributors (oma_verdict2 does this); statements and shorter proofs: no points.
-- From the full history of main, all 477 proofs here are the first merged proof of their id (no other PR added the
-- same file), so all keep their points unless a closure by reduction got there first.
-- Then created_at := the PR's merged_at (GitHub) on the rows each transaction created, so history, the calendar
-- and "solved today" stay true: oma_reductions, oma_steps, 'reduced' events, oma_solutions, 'accepted' events
-- (and, for a parent closed by a last step, its '#closed' row and its event: dated when its last step was first
-- solved), 'formalized' / 'shorter' events. The original brief asked only for solutions and 'accepted' events;
-- the other created_at updates are extra and can be dropped from a batch without changing anything else.
--
-- SOURCE. Merged PRs from git (origin/main up to 43bde06f, 27 Nov 23:14 UTC) and the GitHub API (author, merged_at,
-- body). The "missing" lists were read from the database on 27 Nov at 21:52 and 23:14 UTC; nothing was read for this
-- file afterwards. Every call is guarded (skip if a row for that pr_url, or a reduction with that id, already exists),
-- so rows recorded since by the merger's own retries are skipped, and running the file twice changes nothing.
-- Not covered: PRs merged after 23:14 UTC on 27 Nov (the verification query below lists what remains).
--
-- HOW MANY. Batch 0: created_at of the 99 reductions (226 steps, 99 'reduced' events) already registered before the
-- stop. Then 171 reductions (dependency order: a reduction of a step comes after the reduction that creates
-- the step), 477 proofs, 11 shorter-proof events, 308 statements, in 26 batches of at most 50 calls,
-- each batch one transaction (BEGIN ... COMMIT). Expected new rows if none were recorded meanwhile: 171 oma_reductions,
-- 394 oma_steps, 171 'reduced' events; 477 oma_solutions + 477 'accepted' events (+ any parents closed by a
-- last step: '#closed' rows); 11 'shorter' and 308 'formalized' events. oma_verdict2 / oma_log also settle active leases on
-- those problems, as the site does.
-- Known refusal, not forced: PR 7414 (Erdos713.erdos_713.parts.i.R2) -> too_many_reductions (its target already has 3).
-- No other reduction depends on 7414.
--
-- ALREADY RUN by the credit-backfill session before the stop reached it (live; the second batch, 28 Nov 07:14 UTC,
-- ran after the owner's instruction of 27 Nov night, before the session was told of it): migration 018 (apply_migration, 27 Nov ~21:49 UTC),
-- 019 (create index concurrently, ~21:51 UTC), and two batches of oma_register_reduction: 50 reductions at
-- 2026-11-27 23:26:31 UTC and 49 at 2026-11-28 07:14:46 UTC (PR 7414 refused) = 99 reductions, 226 steps.
--
-- HOW TO RUN. psql -v ON_ERROR_STOP=1 -f 02_credit_backfill.sql (or one batch at a time). Each batch is small
-- (< 100 ms on 27 Nov); pause a few seconds between batches if the instance is busy. Check each batch's result rows:
-- {"ok":true,...} recorded, {"skip":...} already there, {"error":...} refused by the function (reported, not forced).
-- Afterwards run the verification query at the end of this file: missing should be 0 except PR 7414 (and anything
-- merged after 23:14 UTC on 27 Nov).

-- ===== batch 0: date the 99 reductions already registered on 27-28 Nov (before the stop) at their merge time =====
-- Their rows carry exactly the transaction time of the two calls that created them, which identifies them.
begin;
update oma_reductions r set created_at = v.m from (values
(4048, '2026-11-27T08:02:57Z'::timestamptz),
(4051, '2026-11-27T08:03:16Z'::timestamptz),
(4055, '2026-11-27T08:06:42Z'::timestamptz),
(4082, '2026-11-27T08:08:18Z'::timestamptz),
(4092, '2026-11-27T08:09:27Z'::timestamptz),
(4100, '2026-11-27T08:10:30Z'::timestamptz),
(4101, '2026-11-27T08:09:54Z'::timestamptz),
(4104, '2026-11-27T08:09:59Z'::timestamptz),
(4125, '2026-11-27T08:11:46Z'::timestamptz),
(4129, '2026-11-27T08:11:58Z'::timestamptz),
(4134, '2026-11-27T08:12:46Z'::timestamptz),
(4135, '2026-11-27T08:11:56Z'::timestamptz),
(4147, '2026-11-27T08:12:29Z'::timestamptz),
(4154, '2026-11-27T08:12:39Z'::timestamptz),
(4160, '2026-11-27T08:12:58Z'::timestamptz),
(4166, '2026-11-27T08:13:48Z'::timestamptz),
(4177, '2026-11-27T08:14:29Z'::timestamptz),
(4185, '2026-11-27T08:15:31Z'::timestamptz),
(4186, '2026-11-27T08:15:03Z'::timestamptz),
(4188, '2026-11-27T08:14:57Z'::timestamptz),
(4196, '2026-11-27T08:16:17Z'::timestamptz),
(4200, '2026-11-27T08:16:29Z'::timestamptz),
(4207, '2026-11-27T08:16:41Z'::timestamptz),
(4208, '2026-11-27T08:16:06Z'::timestamptz),
(4217, '2026-11-27T08:17:40Z'::timestamptz),
(4219, '2026-11-27T08:17:56Z'::timestamptz),
(4232, '2026-11-27T08:17:48Z'::timestamptz),
(4243, '2026-11-27T08:18:05Z'::timestamptz),
(4248, '2026-11-27T08:18:10Z'::timestamptz),
(4255, '2026-11-27T08:18:18Z'::timestamptz),
(4271, '2026-11-27T08:18:44Z'::timestamptz),
(4279, '2026-11-27T08:18:49Z'::timestamptz),
(4282, '2026-11-27T08:18:59Z'::timestamptz),
(4284, '2026-11-27T08:19:02Z'::timestamptz),
(4300, '2026-11-27T08:21:06Z'::timestamptz),
(4309, '2026-11-27T08:19:37Z'::timestamptz),
(4316, '2026-11-27T08:19:48Z'::timestamptz),
(4328, '2026-11-27T08:20:35Z'::timestamptz),
(4331, '2026-11-27T08:20:03Z'::timestamptz),
(4334, '2026-11-27T08:21:14Z'::timestamptz),
(4341, '2026-11-27T08:23:06Z'::timestamptz),
(4366, '2026-11-27T08:28:19Z'::timestamptz),
(4391, '2026-11-27T08:33:55Z'::timestamptz),
(4394, '2026-11-27T08:34:07Z'::timestamptz),
(4402, '2026-11-27T08:37:18Z'::timestamptz),
(4406, '2026-11-27T08:39:02Z'::timestamptz),
(4407, '2026-11-27T08:38:32Z'::timestamptz),
(4415, '2026-11-27T08:41:43Z'::timestamptz),
(4418, '2026-11-27T08:44:00Z'::timestamptz),
(4424, '2026-11-27T08:45:57Z'::timestamptz),
(4426, '2026-11-27T08:45:49Z'::timestamptz),
(4439, '2026-11-27T08:48:44Z'::timestamptz),
(4452, '2026-11-27T08:51:14Z'::timestamptz),
(4457, '2026-11-27T08:52:05Z'::timestamptz),
(4475, '2026-11-27T08:54:11Z'::timestamptz),
(4488, '2026-11-27T08:56:19Z'::timestamptz),
(4496, '2026-11-27T08:59:45Z'::timestamptz),
(4512, '2026-11-27T09:02:48Z'::timestamptz),
(4519, '2026-11-27T09:05:53Z'::timestamptz),
(4524, '2026-11-27T09:07:33Z'::timestamptz),
(4537, '2026-11-27T09:11:41Z'::timestamptz),
(4706, '2026-11-27T09:48:49Z'::timestamptz),
(4807, '2026-11-27T10:04:02Z'::timestamptz),
(4810, '2026-11-27T10:04:20Z'::timestamptz),
(5395, '2026-11-27T11:32:12Z'::timestamptz),
(5678, '2026-11-27T12:12:24Z'::timestamptz),
(5902, '2026-11-27T13:03:10Z'::timestamptz),
(6009, '2026-11-27T13:11:26Z'::timestamptz),
(6049, '2026-11-27T13:12:49Z'::timestamptz),
(6178, '2026-11-27T13:04:11Z'::timestamptz),
(6180, '2026-11-27T13:03:46Z'::timestamptz),
(6188, '2026-11-27T13:03:08Z'::timestamptz),
(6196, '2026-11-27T13:02:51Z'::timestamptz),
(6339, '2026-11-27T14:12:55Z'::timestamptz),
(7404, '2026-11-27T15:03:50Z'::timestamptz),
(7448, '2026-11-27T17:06:04Z'::timestamptz),
(7733, '2026-11-27T17:06:25Z'::timestamptz),
(7735, '2026-11-27T17:07:01Z'::timestamptz),
(7833, '2026-11-27T17:14:44Z'::timestamptz),
(7873, '2026-11-27T17:18:36Z'::timestamptz),
(7879, '2026-11-27T17:18:48Z'::timestamptz),
(7887, '2026-11-27T17:19:37Z'::timestamptz),
(7896, '2026-11-27T17:20:22Z'::timestamptz),
(7897, '2026-11-27T17:20:40Z'::timestamptz),
(7904, '2026-11-27T17:20:54Z'::timestamptz),
(8427, '2026-11-27T16:54:58Z'::timestamptz),
(8598, '2026-11-27T17:54:55Z'::timestamptz),
(8603, '2026-11-27T17:55:24Z'::timestamptz),
(8604, '2026-11-27T17:55:45Z'::timestamptz),
(8605, '2026-11-27T17:55:32Z'::timestamptz),
(8623, '2026-11-27T17:57:09Z'::timestamptz),
(8634, '2026-11-27T17:57:52Z'::timestamptz),
(8635, '2026-11-27T17:57:54Z'::timestamptz),
(8642, '2026-11-27T17:58:44Z'::timestamptz),
(8646, '2026-11-27T17:58:41Z'::timestamptz),
(8655, '2026-11-27T17:59:17Z'::timestamptz),
(8656, '2026-11-27T17:59:22Z'::timestamptz),
(8658, '2026-11-27T17:59:44Z'::timestamptz),
(8660, '2026-11-27T17:59:46Z'::timestamptz)
) v(pr, m)
  where r.pr_url = 'https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/' || v.pr and r.created_at in ('2026-11-27 23:26:31.12025+00', '2026-11-28 07:14:46.725184+00');
update oma_steps s set created_at = r.created_at from oma_reductions r where s.reduction = r.id and s.created_at in ('2026-11-27 23:26:31.12025+00', '2026-11-28 07:14:46.725184+00');
update oma_events e set created_at = r.created_at from oma_reductions r
  where e.kind = 'reduced' and e.created_at in ('2026-11-27 23:26:31.12025+00', '2026-11-28 07:14:46.725184+00') and e.problem_id = r.problem_id and e.detail = r.id || ' into ' || r.hyps || ' steps';
commit;

-- ===== batch 1: reductions, dependency level 0 (50 PRs: 8664 .. ) =====
begin;
select v.pr, case
  when exists (select 1 from oma_reductions r where r.pr_url = 'https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/' || v.pr) then json_build_object('skip','pr_exists')
  when exists (select 1 from oma_reductions r where r.id = v.t || '.R' || v.rn) then json_build_object('skip','id_exists')
  when v.pts is null and not exists (select 1 from oma_steps s where s.id = v.t) then json_build_object('error','unknown_target')
  else oma_register_reduction(v.t || '.R' || v.rn, v.t, v.h, 'https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/' || v.pr,
         'OMAReductions.R_' || regexp_replace(v.t || '.R' || v.rn, '[^A-Za-z0-9]', '_', 'g'), v.st::json,
         coalesce(v.pts, (select s.points from oma_steps s where s.id = v.t))) end r
from (values
(8664, 'Erdos963.erdos_963.parts.ii', 1, 'MrSeizy', 74::int, '["∀ (d : ℕ), d ≤ 4 → ∀ P : Finset ℤ, (∀ x ∈ P, 0 < x) →\n    (∀ D ⊆ P, D.card = d + 1 → ¬ AddDissociated (D : Set ℤ)) →\n    P.card < 2 ^ d ∧ (d = 4 → P.card ≤ 14)\n\n-- Affine extraction and common triple subsums.", "let aff := (fun (M : Finset ℤ) ↦ ∀ T ⊆ M, ∀ S ⊆ M, Disjoint T S → T.card = S.card → T.sum id = S.sum id → T = S)\n  let triples := (fun (M : Finset ℤ) ↦ (M.powersetCard 3).image (fun S ↦ S.sum id))\n  (∀ (X : Finset ℤ) (k : ℕ),\n    (k = 4 ∧ 5 ≤ X.card) ∨ (k = 5 ∧ 8 ≤ X.card) ∨ (k = 6 ∧ 14 ≤ X.card) →\n    ∃ D ⊆ X, D.card = k ∧ aff D) ∧\n  (∀ (X : Finset ℤ) (k : ℕ), (k = 4 ∧ 5 ≤ X.card) ∨ (k = 5 ∧ 9 ≤ X.card) →\n    ∃ D ⊆ X, ∃ E ⊆ X, D.card = k ∧ E.card = k ∧ aff D ∧ aff E ∧ D.sum id ≠ E.sum id) ∧\n  (∀ X W : Finset ℤ, 5 ≤ X.card →\n    (∀ F ⊆ X, F.card = 4 → aff F → W ⊆ triples F) →\n    W.card ≤ if 6 ≤ X.card then 2 else 3)\n\n-- Classification of seven-point affine extremizers from the public affine-fourteen argument.", "let aff := (fun (M : Finset ℤ) ↦ ∀ T ⊆ M, ∀ S ⊆ M, Disjoint T S → T.card = S.card → T.sum id = S.sum id → T = S)\n  ∀ X : Finset ℤ, X.card = 7 →\n    (∀ F ⊆ X, F.card = 5 → ¬ aff F) →\n    ∃ x a b : ℤ, 0 < a ∧ a < b ∧ X = {x,x-a,x+a,x-b,x+b,x-(a+b),x+(a+b)}\n\n-- The still open exact positive-set bound above dimension five.", "∀ (d : ℕ), 6 ≤ d → ∀ P : Finset ℤ, (∀ x ∈ P, 0 < x) →\n    (∀ D ⊆ P, D.card = d + 1 → ¬ AddDissociated (D : Set ℤ)) → P.card < 2 ^ d"]'),
(8661, 'Bugeaud08.problem_10_8', 1, 'marcusbuffett', 68::int, '["∀ (ξ : ℝ) (p : ℕ), p.Prime →\n    (∀ ε : ℝ, 0 < ε → ∃ q : ℕ, 1 ≤ q ∧ (q : ℝ) * distToNearestInt (q * ξ) < ε) →\n    sInf {x : ℝ | ∃ q : ℕ, 1 ≤ q ∧\n      x = q * padicNorm p q * distToNearestInt (q * ξ)} = 0\n\n/-- The open part: badly approximable `ξ`. -/", "∀ (ξ : ℝ) (p : ℕ), p.Prime →\n    (∃ ε : ℝ, 0 < ε ∧ ∀ q : ℕ, 1 ≤ q → ε ≤ (q : ℝ) * distToNearestInt (q * ξ)) →\n    sInf {x : ℝ | ∃ q : ℕ, 1 ≤ q ∧\n      x = q * padicNorm p q * distToNearestInt (q * ξ)} = 0"]'),
(8675, 'Erdos1182.erdos_1182.variants.small_values.R1.H2.R1.H2', 1, 'physbuzz', null::int, '["let masks := (![822777387642256703234551838076830900798754331299012273175546532,822764833055638660808762661315316885505752648441781026290401700] : Fin 2 → ℕ)\n  let C (a : Fin 2) : SimpleGraph (Fin 15) :=\n    { Adj := fun i j => i ≠ j ∧ (masks a).testBit ((min i j).val*15+(max i j).val) = true\n      symm := ⟨fun i j v => ⟨v.1.symm,by simpa [min_comm j i,max_comm j i] using v.2⟩⟩\n      loopless := ⟨by simp⟩ }\n  ∀ f : Fin 2 → Fin 8 ↪ Fin 15,\n    let D := ⨅ a, (C a)ᶜ.comap (f a)\n    D.Connected → D.edgeSet.ncard ≤ 20\n\n/-- A common edge bound for the 3 specified hosts on 17 vertices. -/", "let masks := (![3794289654249960540213394811365649999491732653694874493236865398263569676450744992,3794304128205901233965105136443933563551981921148588106415553686027566907782081184,165643176072884037276740330230205787895060569518802011647374886495636132] : Fin 3 → ℕ)\n  let C (a : Fin 3) : SimpleGraph (Fin 17) :=\n    { Adj := fun i j => i ≠ j ∧ (masks a).testBit ((min i j).val*17+(max i j).val) = true\n      symm := ⟨fun i j v => ⟨v.1.symm,by simpa [min_comm j i,max_comm j i] using v.2⟩⟩\n      loopless := ⟨by simp⟩ }\n  ∀ f : Fin 3 → Fin 9 ↪ Fin 17,\n    let D := ⨅ a, (C a)ᶜ.comap (f a)\n    D.Connected → D.edgeSet.ncard ≤ 27\n\n/-- Finite obstruction families for the final three orders. -/", "∀ t : Fin 3,\n  let n := t.val+10\n  let h := 2*n-1\n  let q := (![33,41,49] : Fin 3 → ℕ) t\n  ∃ (r : ℕ) (masks : Fin r → ℕ),\n    let C (a : Fin r) : SimpleGraph (Fin h) :=\n      { Adj := fun i j => i ≠ j ∧ (masks a).testBit ((min i j).val*h+(max i j).val) = true\n        symm := ⟨fun i j v => ⟨v.1.symm,by simpa [min_comm j i,max_comm j i] using v.2⟩⟩\n        loopless := ⟨by simp⟩ }\n    (∀ a, (C a).CliqueFree 3) ∧\n    ∀ f : Fin r → Fin n ↪ Fin h,\n      let D := ⨅ a, (C a)ᶜ.comap (f a)\n      D.Connected → D.edgeSet.ncard ≤ q"]'),
(8676, 'LittlewoodConjecture.padic_littlewood_conjecture', 1, 'marcusbuffett', 68::int, '["∀ (α : ℝ) (p : ℕ), p.Prime →\n    (∀ ε : ℝ, 0 < ε → ∃ᶠ n : ℕ in atTop, n * distToNearestInt (n * α) < ε) →\n    atTop.liminf (fun (n : ℕ) ↦ n * padicNorm p n * distToNearestInt (n * α)) = 0\n\n/-- The open part: badly approximable `α`. -/", "∀ (α : ℝ) (p : ℕ), p.Prime →\n    (∃ ε : ℝ, 0 < ε ∧ ∀ᶠ n : ℕ in atTop, ε ≤ n * distToNearestInt (n * α)) →\n    atTop.liminf (fun (n : ℕ) ↦ n * padicNorm p n * distToNearestInt (n * α)) = 0"]'),
(8680, 'Selfridge.selfridge_seq_conjecture', 1, 'Optymyzt', 66::int, '["8 ≤ Selfridge.fermatFactors 12\n\n-- Any later Fermat number with at most seven distinct prime factors suffices.", "∃ n : ℕ, 12 < n ∧ Selfridge.fermatFactors n ≤ 7"]'),
(8709, 'Erdos535.erdos_535.R2.H1', 1, 'LordMike', null::int, '["∀ r : ℕ, 3 ≤ r → ∃ D : ℕ, 1 ≤ D ∧\n    ∀ (k m : ℕ) (W : Finset (Fin k → Fin m)),\n      (∀ w : Fin r → Fin k → Fin m, (∀ i, w i ∈ W) →\n        (∀ j, (∀ a b, w a j = w b j) ∨ Function.Injective (fun i => w i j)) →\n        ∀ a b, w a = w b) → W.card ≤ D ^ k", "∀ (r k : ℕ), 0 < k → ∀ F : Finset (Finset ℕ), (∀ A ∈ F, A.card = k) →\n    (¬ ∃ G ⊆ F, G.card = r ∧ ∃ K : Finset ℕ,\n      ∀ A ∈ G, ∀ B ∈ G, A ≠ B → A ∩ B = K) →\n    ∃ (m : ℕ) (W : Finset (Fin k → Fin m)), F.card ≤ 3 ^ k * W.card ∧\n      ∀ w : Fin r → Fin k → Fin m, (∀ i, w i ∈ W) →\n        (∀ j, (∀ a b, w a j = w b j) ∨ Function.Injective (fun i => w i j)) →\n        ∀ a b, w a = w b"]'),
(8710, 'erdos-634.R1.H3.R1.H2', 1, 'adammcarter', null::int, '["∀ (p : ℕ) (T : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))) (Ts : Fin p → Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))), (∀ i j, Congruent (Ts i).points (Ts j).points) → Pairwise (fun i j => Disjoint (Ts i).interior (Ts j).interior) → ⋃ i, (Ts i).closedInterior = T.closedInterior → ∀ t : Fin p, ¬ (∃ i j : Fin 3, i ≠ j ∧ EuclideanGeometry.angle (T.points (i + 1)) (T.points i) (T.points (i + 2)) = EuclideanGeometry.angle (T.points (j + 1)) (T.points j) (T.points (j + 2))) → ∀ (n : ℕ) (a : Fin 3 → ℕ), 0 < n → (∀ k : Fin 3, EuclideanGeometry.angle ((Ts t).points (k + 1)) ((Ts t).points k) ((Ts t).points (k + 2)) = (a k : ℝ) * Real.pi / n) → Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1 → ((∀ i, 0 < a i) → ∑ i, a i = n → ∀ e : Fin 3 → ℚ, (∀ k : ℕ, k.Coprime n → ∑ i, (if Int.fract (((k * a i : ℕ) : ℚ) / (n : ℚ)) = 0 then 0 else Int.fract (((k * a i : ℕ) : ℚ) / (n : ℚ)) - 1 / 2) * e i = 0) → e ∈ Submodule.span ℚ ({v | ∃ i j, i ≠ j ∧ a i = a j ∧ v = Pi.single i 1 - Pi.single j 1} ∪ {v | ∃ i, 2 * a i = n ∧ v = Pi.single i 1})) → ∃ σ : Equiv.Perm (Fin 3), ∀ k : Fin 3, EuclideanGeometry.angle (T.points (k + 1)) (T.points k) (T.points (k + 2)) = EuclideanGeometry.angle ((Ts t).points ((σ k) + 1)) ((Ts t).points (σ k)) ((Ts t).points ((σ k) + 2))", "∀ (n : ℕ) (a : Fin 3 → ℕ), (∃ l : ℕ, l.Prime ∧ 7 ≤ l ∧ l ∣ n) → Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1 → (∀ i, 0 < a i) → ∑ i, a i = n → ∀ e : Fin 3 → ℚ, (∀ k : ℕ, k.Coprime n → ∑ i, (if Int.fract (((k * a i : ℕ) : ℚ) / (n : ℚ)) = 0 then 0 else Int.fract (((k * a i : ℕ) : ℚ) / (n : ℚ)) - 1 / 2) * e i = 0) → e ∈ Submodule.span ℚ ({v | ∃ i j, i ≠ j ∧ a i = a j ∧ v = Pi.single i 1 - Pi.single j 1} ∪ {v | ∃ i, 2 * a i = n ∧ v = Pi.single i 1})"]'),
(8713, 'erdos-634.R1.H3.R1.H4', 1, 'adammcarter', null::int, '["∀ (p : ℕ) (T : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))) (Ts : Fin p → Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))), (∀ i j, Congruent (Ts i).points (Ts j).points) → Pairwise (fun i j => Disjoint (Ts i).interior (Ts j).interior) → ⋃ i, (Ts i).closedInterior = T.closedInterior → ∀ t : Fin p, ¬ (∃ i j : Fin 3, i ≠ j ∧ EuclideanGeometry.angle (T.points (i + 1)) (T.points i) (T.points (i + 2)) = EuclideanGeometry.angle (T.points (j + 1)) (T.points j) (T.points (j + 2))) → ∀ (n : ℕ) (a : Fin 3 → ℕ), 0 < n → (∀ k : Fin 3, EuclideanGeometry.angle ((Ts t).points (k + 1)) ((Ts t).points k) ((Ts t).points (k + 2)) = (a k : ℝ) * Real.pi / n) → Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1 → ((∀ i, 0 < a i) → ∑ i, a i = n → ∀ e : Fin 3 → ℚ, (∀ k : ℕ, k.Coprime n → ∑ i, (if Int.fract (((k * a i : ℕ) : ℚ) / (n : ℚ)) = 0 then 0 else Int.fract (((k * a i : ℕ) : ℚ) / (n : ℚ)) - 1 / 2) * e i = 0) → e ∈ Submodule.span ℚ ({v | ∃ i j, i ≠ j ∧ a i = a j ∧ v = Pi.single i 1 - Pi.single j 1} ∪ {v | ∃ i, 2 * a i = n ∧ v = Pi.single i 1})) → ∃ σ : Equiv.Perm (Fin 3), ∀ k : Fin 3, EuclideanGeometry.angle (T.points (k + 1)) (T.points k) (T.points (k + 2)) = EuclideanGeometry.angle ((Ts t).points ((σ k) + 1)) ((Ts t).points (σ k)) ((Ts t).points ((σ k) + 2))", "∀ (n : ℕ) (a : Fin 3 → ℕ), (∀ l : ℕ, l.Prime → l ∣ n → l ≤ 5) → n ≤ 200 → ¬ (n = 3 ∨ n = 4 ∨ n = 6 ∨ n = 8 ∨ n = 10 ∨ n = 12 ∨ n = 18 ∨ n = 24 ∨ n = 30 ∨ n = 60) → Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1 → (∀ i, 0 < a i) → ∑ i, a i = n → ∀ e : Fin 3 → ℚ, (∀ k : ℕ, k.Coprime n → ∑ i, (if Int.fract (((k * a i : ℕ) : ℚ) / (n : ℚ)) = 0 then 0 else Int.fract (((k * a i : ℕ) : ℚ) / (n : ℚ)) - 1 / 2) * e i = 0) → e ∈ Submodule.span ℚ ({v | ∃ i j, i ≠ j ∧ a i = a j ∧ v = Pi.single i 1 - Pi.single j 1} ∪ {v | ∃ i, 2 * a i = n ∧ v = Pi.single i 1})", "∀ (p : ℕ) (T : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))) (Ts : Fin p → Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))), (∀ i j, Congruent (Ts i).points (Ts j).points) → Pairwise (fun i j => Disjoint (Ts i).interior (Ts j).interior) → ⋃ i, (Ts i).closedInterior = T.closedInterior → ∀ t : Fin p, ¬ (∃ i j : Fin 3, i ≠ j ∧ EuclideanGeometry.angle (T.points (i + 1)) (T.points i) (T.points (i + 2)) = EuclideanGeometry.angle (T.points (j + 1)) (T.points j) (T.points (j + 2))) → ∀ (n : ℕ) (a : Fin 3 → ℕ), 0 < n → (∀ k : Fin 3, EuclideanGeometry.angle ((Ts t).points (k + 1)) ((Ts t).points k) ((Ts t).points (k + 2)) = (a k : ℝ) * Real.pi / n) → Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1 → (n = 3 ∨ n = 4 ∨ n = 6 ∨ n = 8 ∨ n = 10) → ∃ σ : Equiv.Perm (Fin 3), ∀ k : Fin 3, EuclideanGeometry.angle (T.points (k + 1)) (T.points k) (T.points (k + 2)) = EuclideanGeometry.angle ((Ts t).points ((σ k) + 1)) ((Ts t).points (σ k)) ((Ts t).points ((σ k) + 2))", "∀ (p : ℕ) (T : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))) (Ts : Fin p → Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))), (∀ i j, Congruent (Ts i).points (Ts j).points) → Pairwise (fun i j => Disjoint (Ts i).interior (Ts j).interior) → ⋃ i, (Ts i).closedInterior = T.closedInterior → ∀ t : Fin p, ¬ (∃ i j : Fin 3, i ≠ j ∧ EuclideanGeometry.angle (T.points (i + 1)) (T.points i) (T.points (i + 2)) = EuclideanGeometry.angle (T.points (j + 1)) (T.points j) (T.points (j + 2))) → ∀ (n : ℕ) (a : Fin 3 → ℕ), 0 < n → (∀ k : Fin 3, EuclideanGeometry.angle ((Ts t).points (k + 1)) ((Ts t).points k) ((Ts t).points (k + 2)) = (a k : ℝ) * Real.pi / n) → Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1 → (n = 12 ∨ n = 18 ∨ n = 24 ∨ n = 30 ∨ n = 60) → ∃ σ : Equiv.Perm (Fin 3), ∀ k : Fin 3, EuclideanGeometry.angle (T.points (k + 1)) (T.points k) (T.points (k + 2)) = EuclideanGeometry.angle ((Ts t).points ((σ k) + 1)) ((Ts t).points (σ k)) ((Ts t).points ((σ k) + 2))"]'),
(8724, 'SkewesNumber.skewes_crossover_known_bounds', 1, 'Andyi955', 28::int, '["∀ n : ℕ, 2 ≤ n → n ≤ 10 ^ 19 → (Nat.primeCounting n : ℝ) < Real.logIntegral (n : ℝ)\n\n/-- Skewes'' existence bound: some `n` below `exp(727.95134)` has the reversed inequality. -/", "∃ n : ℕ, 2 ≤ n ∧ (n : ℝ) < Real.exp (72795134 / 100000) ∧\n    Real.logIntegral (n : ℝ) < (Nat.primeCounting n : ℝ)"]'),
(8719, 'erdos-634.R1.H4.R1.H3', 1, 'adammcarter', null::int, '["∀ (p : ℕ) (T M : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))) (Ts : Fin p → Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))), (∀ i, ∃ (f : EuclideanSpace ℝ (Fin 2) ≃ᵢ EuclideanSpace ℝ (Fin 2)) (σ : Equiv.Perm (Fin 3)), ∀ k, f ((Ts i).points k) = M.points (σ k)) → Pairwise (fun i j => Disjoint (interior (Ts i).closedInterior) (interior (Ts j).closedInterior)) → ⋃ i, (Ts i).closedInterior = T.closedInterior → ∀ A B L : Fin 3 → ℝ, (∀ k, A k = EuclideanGeometry.angle (T.points (k + 1)) (T.points k) (T.points (k + 2))) → (∀ k, B k = EuclideanGeometry.angle (M.points (k + 1)) (M.points k) (M.points (k + 2))) → (∀ k, L k = dist (M.points (k + 1)) (M.points (k + 2))) → ∀ α β γ a b c : ℝ, (¬ ∃ q : ℚ, α = q * Real.pi) → 3 * α + 2 * β = Real.pi → (∃ σ : Equiv.Perm (Fin 3), B ∘ σ = ![α, β, γ] ∧ L ∘ σ = ![a, b, c]) → (¬ (∃ σ : Equiv.Perm (Fin 3), A = B ∘ σ) → (∃ q : ℚ, a / c = q) ∧ (∃ q : ℚ, b / c = q) ∧ (∃ q : ℚ, a / b = q)) ∧ ∀ m k : ℤ, 0 < m → m < k → IsCoprime m k → a = m * k → b = k ^ 2 - m ^ 2 → c = k ^ 2 → A = ![2 * α, β, α + β] → (p : ℝ) ≠ 2 * k ^ 2 - m ^ 2", "(∀ (p : ℕ) (T M : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))) (Ts : Fin p → Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))), (∀ i, ∃ (f : EuclideanSpace ℝ (Fin 2) ≃ᵢ EuclideanSpace ℝ (Fin 2)) (σ : Equiv.Perm (Fin 3)), ∀ k, f ((Ts i).points k) = M.points (σ k)) → Pairwise (fun i j => Disjoint (interior (Ts i).closedInterior) (interior (Ts j).closedInterior)) → ⋃ i, (Ts i).closedInterior = T.closedInterior → ∀ A B L : Fin 3 → ℝ, (∀ k, A k = EuclideanGeometry.angle (T.points (k + 1)) (T.points k) (T.points (k + 2))) → (∀ k, B k = EuclideanGeometry.angle (M.points (k + 1)) (M.points k) (M.points (k + 2))) → (∀ k, L k = dist (M.points (k + 1)) (M.points (k + 2))) → ∀ α β γ a b c : ℝ, (¬ ∃ q : ℚ, α = q * Real.pi) → 3 * α + 2 * β = Real.pi → (∃ σ : Equiv.Perm (Fin 3), B ∘ σ = ![α, β, γ] ∧ L ∘ σ = ![a, b, c]) → (¬ (∃ σ : Equiv.Perm (Fin 3), A = B ∘ σ) → (∃ q : ℚ, a / c = q) ∧ (∃ q : ℚ, b / c = q) ∧ (∃ q : ℚ, a / b = q)) ∧ ∀ m k : ℤ, 0 < m → m < k → IsCoprime m k → a = m * k → b = k ^ 2 - m ^ 2 → c = k ^ 2 → A = ![2 * α, β, α + β] → (p : ℝ) ≠ 2 * k ^ 2 - m ^ 2) → ∀ (p : ℕ), p.Prime → 3 < p → ∀ (T : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))) (Ts : Fin p → Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))), (∀ i j, Congruent (Ts i).points (Ts j).points) → Pairwise (fun i j => Disjoint (Ts i).interior (Ts j).interior) → ⋃ i, (Ts i).closedInterior = T.closedInterior → ∀ t : Fin p, ∀ A B : Fin 3 → ℝ, (∀ k, A k = EuclideanGeometry.angle (T.points (k + 1)) (T.points k) (T.points (k + 2))) → (∀ k, B k = EuclideanGeometry.angle ((Ts t).points (k + 1)) ((Ts t).points k) ((Ts t).points (k + 2))) → ¬ (∃ σ : Equiv.Perm (Fin 3), A = B ∘ σ) → ∀ α β : ℝ, (¬ ∃ q : ℚ, α = q * Real.pi) → 3 * α + 2 * β = Real.pi → (∃ σ : Equiv.Perm (Fin 3), B ∘ σ = ![α, β, 2 * α + β]) → (∃ σ : Equiv.Perm (Fin 3), A ∘ σ = ![α, 2 * α, 2 * β] ∨ A ∘ σ = ![2 * α, β, α + β]) → False"]'),
(8725, 'Dickson.dickson_conjecture', 1, 'marcusbuffett', 68::int, '["∀ fs : Finset ℤ[X], (∀ f ∈ fs, f.degree = 1 ∧ BunyakovskyCondition f) → SchinzelCondition fs →\n    fs.card ≤ 1 → Infinite {n : ℕ | ∀ f ∈ fs, (f.eval (n : ℤ)).natAbs.Prime}\n\n/-- The open part: two or more forms. -/", "∀ fs : Finset ℤ[X], (∀ f ∈ fs, f.degree = 1 ∧ BunyakovskyCondition f) → SchinzelCondition fs →\n    2 ≤ fs.card → Infinite {n : ℕ | ∀ f ∈ fs, (f.eval (n : ℤ)).natAbs.Prime}"]'),
(8731, 'Erdos723.erdos_723.variants.leq_11.R1.H2.R1.H3', 1, 'LordMike', null::int, '["∀ incidence : Fin 111 → Fin 111 → Bool,\n    (∀ l, (Finset.univ.filter fun p => incidence l p = true).card = 11) →\n    (∀ p, (Finset.univ.filter fun l => incidence l p = true).card = 11) →\n    (∀ l m, l ≠ m → ∃! p, incidence l p = true ∧ incidence m p = true) →\n    (∀ p q, p ≠ q → ∃! l, incidence l p = true ∧ incidence l q = true) →\n    let k (S : Finset (Fin 111)) (l : Fin 111) := (S.filter fun p => incidence l p = true).card\n    let n (S : Finset (Fin 111)) (j : Nat) := (Finset.univ.filter fun l => k S l = j).card\n    let d (S : Finset (Fin 111)) (p : Fin 111) (j : Nat) :=\n      (Finset.univ.filter fun l => k S l = j ∧ incidence l p = true).card\n    let profile (S : Finset (Fin 111)) := S.card = 16 ∧\n      (∀ l, 2 ∣ k S l ∧ k S l ≤ 6) ∧\n      (n S 4 + 3*n S 6 = 8 ∧ n S 2 = 72 + 3*n S 6 ∧ n S 0 + n S 6 = 31) ∧\n      ∀ p∈S, d S p 4 + 2*d S p 6 = 2\n    let weight (a : Fin 111 → ZMod 2) := hammingNorm\n      (fun p : Fin 111 => ∑ l, a l * (if incidence l p = true then 1 else 0))\n    ∀ a, weight a = 16 → ∃ S, profile S\n\n-- The three possible numbers of six-secants.", "∀ incidence : Fin 111 → Fin 111 → Bool,\n    (∀ l, (Finset.univ.filter fun p => incidence l p = true).card = 11) →\n    (∀ p, (Finset.univ.filter fun l => incidence l p = true).card = 11) →\n    (∀ l m, l ≠ m → ∃! p, incidence l p = true ∧ incidence m p = true) →\n    (∀ p q, p ≠ q → ∃! l, incidence l p = true ∧ incidence l q = true) →\n    let k (S : Finset (Fin 111)) (l : Fin 111) := (S.filter fun p => incidence l p = true).card\n    let n (S : Finset (Fin 111)) (j : Nat) := (Finset.univ.filter fun l => k S l = j).card\n    let d (S : Finset (Fin 111)) (p : Fin 111) (j : Nat) :=\n      (Finset.univ.filter fun l => k S l = j ∧ incidence l p = true).card\n    let profile (S : Finset (Fin 111)) := S.card = 16 ∧\n      (∀ l, 2 ∣ k S l ∧ k S l ≤ 6) ∧\n      (n S 4 + 3*n S 6 = 8 ∧ n S 2 = 72 + 3*n S 6 ∧ n S 0 + n S 6 = 31) ∧\n      ∀ p∈S, d S p 4 + 2*d S p 6 = 2\n    ¬ ∃ S, profile S ∧ n S 6 = 0", "∀ incidence : Fin 111 → Fin 111 → Bool,\n    (∀ l, (Finset.univ.filter fun p => incidence l p = true).card = 11) →\n    (∀ p, (Finset.univ.filter fun l => incidence l p = true).card = 11) →\n    (∀ l m, l ≠ m → ∃! p, incidence l p = true ∧ incidence m p = true) →\n    (∀ p q, p ≠ q → ∃! l, incidence l p = true ∧ incidence l q = true) →\n    let k (S : Finset (Fin 111)) (l : Fin 111) := (S.filter fun p => incidence l p = true).card\n    let n (S : Finset (Fin 111)) (j : Nat) := (Finset.univ.filter fun l => k S l = j).card\n    let d (S : Finset (Fin 111)) (p : Fin 111) (j : Nat) :=\n      (Finset.univ.filter fun l => k S l = j ∧ incidence l p = true).card\n    let profile (S : Finset (Fin 111)) := S.card = 16 ∧\n      (∀ l, 2 ∣ k S l ∧ k S l ≤ 6) ∧\n      (n S 4 + 3*n S 6 = 8 ∧ n S 2 = 72 + 3*n S 6 ∧ n S 0 + n S 6 = 31) ∧\n      ∀ p∈S, d S p 4 + 2*d S p 6 = 2\n    ¬ ∃ S, profile S ∧ n S 6 = 1", "∀ incidence : Fin 111 → Fin 111 → Bool,\n    (∀ l, (Finset.univ.filter fun p => incidence l p = true).card = 11) →\n    (∀ p, (Finset.univ.filter fun l => incidence l p = true).card = 11) →\n    (∀ l m, l ≠ m → ∃! p, incidence l p = true ∧ incidence m p = true) →\n    (∀ p q, p ≠ q → ∃! l, incidence l p = true ∧ incidence l q = true) →\n    let k (S : Finset (Fin 111)) (l : Fin 111) := (S.filter fun p => incidence l p = true).card\n    let n (S : Finset (Fin 111)) (j : Nat) := (Finset.univ.filter fun l => k S l = j).card\n    let d (S : Finset (Fin 111)) (p : Fin 111) (j : Nat) :=\n      (Finset.univ.filter fun l => k S l = j ∧ incidence l p = true).card\n    let profile (S : Finset (Fin 111)) := S.card = 16 ∧\n      (∀ l, 2 ∣ k S l ∧ k S l ≤ 6) ∧\n      (n S 4 + 3*n S 6 = 8 ∧ n S 2 = 72 + 3*n S 6 ∧ n S 0 + n S 6 = 31) ∧\n      ∀ p∈S, d S p 4 + 2*d S p 6 = 2\n    ¬ ∃ S, profile S ∧ n S 6 = 2"]'),
(8740, 'Erdos723.erdos_723.variants.leq_11.R1.H2.R1.H4', 1, 'LordMike', null::int, '["∀ incidence : Fin 111 → Fin 111 → Bool,\n    (∀ l, (Finset.univ.filter fun p => incidence l p = true).card = 11) →\n    (∀ p, (Finset.univ.filter fun l => incidence l p = true).card = 11) →\n    (∀ l m, l ≠ m → ∃! p, incidence l p = true ∧ incidence m p = true) →\n    (∀ p q, p ≠ q → ∃! l, incidence l p = true ∧ incidence l q = true) →\n    let k (S : Finset (Fin 111)) (l : Fin 111) := (S.filter fun p => incidence l p = true).card\n    let n (S : Finset (Fin 111)) (j : Nat) := (Finset.univ.filter fun l => k S l = j).card\n    let d (S : Finset (Fin 111)) (p : Fin 111) (j : Nat) :=\n      (Finset.univ.filter fun l => k S l = j ∧ incidence l p = true).card\n    let profile (S : Finset (Fin 111)) := S.card = 19 ∧\n      (∀ l, k S l = 1 ∨ k S l = 3 ∨ k S l = 5) ∧\n      (n S 1 = 68 ∧ n S 3 = 37 ∧ n S 5 = 6) ∧\n      ∀ p, d S p 3 + 2*d S p 5 = if p∈S then 9 else 4\n    let word : (Fin 111 → ZMod 2) → Fin 112 → ZMod 2 := fun a =>\n      Fin.cons (∑ l, a l) (fun p : Fin 111 => ∑ l, a l * (if incidence l p = true then 1 else 0))\n    let wt := fun a => hammingNorm (fun p : Fin 111 => word a p.succ)\n    ∀ a, wt a = 19 → (∀ b c, wt b < 19 → wt c < 19 → word a ≠ word b + word c) →\n      ∃ S, profile S", "∀ incidence : Fin 111 → Fin 111 → Bool,\n    (∀ l, (Finset.univ.filter fun p => incidence l p = true).card = 11) →\n    (∀ p, (Finset.univ.filter fun l => incidence l p = true).card = 11) →\n    (∀ l m, l ≠ m → ∃! p, incidence l p = true ∧ incidence m p = true) →\n    (∀ p q, p ≠ q → ∃! l, incidence l p = true ∧ incidence l q = true) →\n    let k (S : Finset (Fin 111)) (l : Fin 111) := (S.filter fun p => incidence l p = true).card\n    let n (S : Finset (Fin 111)) (j : Nat) := (Finset.univ.filter fun l => k S l = j).card\n    let d (S : Finset (Fin 111)) (p : Fin 111) (j : Nat) :=\n      (Finset.univ.filter fun l => k S l = j ∧ incidence l p = true).card\n    let profile (S : Finset (Fin 111)) := S.card = 19 ∧\n      (∀ l, k S l = 1 ∨ k S l = 3 ∨ k S l = 5) ∧\n      (n S 1 = 68 ∧ n S 3 = 37 ∧ n S 5 = 6) ∧\n      ∀ p, d S p 3 + 2*d S p 5 = if p∈S then 9 else 4\n    ¬ ∃ S, profile S"]'),
(8892, 'Erdos1182.erdos_1182.variants.small_values.R1.H1', 1, 'physbuzz', null::int, '["∀ k : Fin 6,\n  let n := k.val+7\n  let q := (![11,11,16,18,23,23] : Fin 6 → ℕ) k\n  let masks := (![[8757838336,33688088],[36169948434793600,70781333153792],[2251801971660822],[618970019714747783169716278,72057645653176374],[158495020111019088292975255562,9444734656926049394710],[14855280693082744087392632874,4951760378943817067685560330,604831853708092460023990,40564825856395375891792278241302]] : Fin 6 → List ℕ) k\n  ∀ G : SimpleGraph (Fin n), G.Connected → G.edgeSet.ncard=q →\n    ∃ m ∈ masks, ∃ e : Fin n ↪ Fin n, ∀ i j, G.Adj i j → m.testBit ((min (e i) (e j)).val*n+(max (e i) (e j)).val) = false\n\n/-- Embed each of the explicitly listed dense templates in the complement\nof every triangle-free host of the critical order. -/", "∀ k : Fin 9,\n  let n := k.val+4\n  let masks := (![[2048],[540672],[541065248],[8757838336,33688088],[36169948434793600,70781333153792],[2251801971660822],[618970019714747783169716278,72057645653176374],[158495020111019088292975255562,9444734656926049394710],[14855280693082744087392632874,4951760378943817067685560330,604831853708092460023990,40564825856395375891792278241302]] : Fin 9 → List ℕ) k\n  ∀ m ∈ masks, ∀ C : SimpleGraph (Fin (2*n-1)), C.CliqueFree 3 →\n    ∃ e : Fin n ↪ Fin (2*n-1), ∀ i j, i≠j → m.testBit ((min (i) (j)).val*n+(max (i) (j)).val) = false → ¬ C.Adj (e i) (e j)"]'),
(8920, 'opg-forcing-a-2-regular-minor', 1, 'lzvxck', 92::int, '["∀ (V : Type) [Fintype V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ),\n    3 ≤ k → (k - 1) * Fintype.card V ≤ 2 * G.edgeFinset.card →\n      ∃ (u : V) (c : G.Walk u u), c.IsCycle ∧ k ≤ c.length\n\n/-- A connected 2-regular graph on `t` vertices (the cycle `C_t`) is a minor of every graph\ncontaining a cycle of length at least `t`: contract consecutive arcs of that cycle. -/", "∀ (t : ℕ) (H : SimpleGraph (Fin t)) [DecidableRel H.Adj],\n    H.IsRegularOfDegree 2 → H.Connected →\n      ∀ (V : Type) (G : SimpleGraph V) (u : V) (c : G.Walk u u),\n        c.IsCycle → t ≤ c.length → IsMinor H G\n\n/-- The open core: 2-regular graphs with at least two components (disjoint unions of cycles). -/", "∀ (t : ℕ) (H : SimpleGraph (Fin t)) [DecidableRel H.Adj],\n    H.IsRegularOfDegree 2 → ¬ H.Connected →\n      ∀ (V : Type) [Fintype V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj],\n        (4 / 3 : ℝ) * t - 2 ≤ 2 * (G.edgeFinset.card : ℝ) / Fintype.card V →\n          IsMinor H G"]'),
(8939, 'EswarathasanLevineConjecture.eswarathasan_levine_harmonic_conjecture', 1, 'marcusbuffett', 68::int, '["∀ p : ℕ, p.Prime → p < 7 → (EswarathasanLevineConjecture.harmonicNumDivisibleSet p).Finite\n\n/-- The open part: the primes from seven on. -/", "∀ p : ℕ, p.Prime → 7 ≤ p → (EswarathasanLevineConjecture.harmonicNumDivisibleSet p).Finite"]'),
(8973, 'oeis-a219037', 1, 'Iraeeee', 62::int, '["∀ k : ℕ, 6 < k → k % 4 = 2 → k % 60 ≠ 6 →\n  ¬18 ∣ k → ¬25 ∣ k-1 →\n  (∀ p a : ℕ, p.Prime → k ≠ 2*p^a) → (∀ p a : ℕ, p.Prime → k ≠ p^a+1) →\n  k ∣ 2^k+2 → ¬k-1 ∣ 2^k+1\n\n/-- In the orbit''s residue class the remaining issue is to show that k−2 is a power of two. -/", "∀ k : ℕ, 6 < k → k % 60 = 6 →\n  ¬18 ∣ k → ¬25 ∣ k-1 →\n  (∀ p a : ℕ, p.Prime → k ≠ 2*p^a) → (∀ p a : ℕ, p.Prime → k ≠ p^a+1) →\n  k ∣ 2^k+2 → k-1 ∣ 2^k+1 → ∃ s : ℕ, k=2^s+2"]'),
(8975, 'PerfectNumbers.odd_perfect_number_conjecture.R1.H1.R1.H2', 1, 'marcusbuffett', null::int, '["∀ n : ℕ, Nat.Perfect n → Odd n → n.primeFactors.card = 3 → Nat.minFac n ≠ 3\n\n/-- The open part: four or more distinct prime factors. -/", "∀ n : ℕ, Nat.Perfect n → Odd n → 4 ≤ n.primeFactors.card → Nat.minFac n ≠ 3"]'),
(8985, 'oeis-a005479', 1, 'sobrien032', 45::int, '["({7, 47, 2207} : Set ℕ) ⊆ {p : ℕ | (∃ k : ℕ, lucas k = p) ∧ p.Prime ∧ p % 10 = 7} ∧\n    ({7, 47, 2207} : Set ℕ) ⊆ {p : ℕ | ∃ k : ℕ, 1 ≤ k ∧ ¬ k.Prime ∧ lucas k = p ∧ p.Prime}\n\n/-- The open part: every prime Lucas number congruent to 7 modulo 10, and every prime Lucas number\n`L k` with `k ≥ 1` not prime, is 7, 47 or 2207. -/", "{p : ℕ | (∃ k : ℕ, lucas k = p) ∧ p.Prime ∧ p % 10 = 7} ⊆ ({7, 47, 2207} : Set ℕ) ∧\n    {p : ℕ | ∃ k : ℕ, 1 ≤ k ∧ ¬ k.Prime ∧ lucas k = p ∧ p.Prime} ⊆ ({7, 47, 2207} : Set ℕ)"]'),
(8987, 'Erdos946.erdos_946.variants.spiro_5040', 2, 'steveDOTdigital', 17::int, '["∀ b : Fin 3 → ℕ, (∀ i, 0 < b i) → Function.Injective b →\n    (∀ p : ℕ, p.Prime → ∃ t : ℕ, ∀ i, ¬p ∣ t+b i) →\n    ∃ i j : Fin 3, i<j ∧\n      {t : ℕ | (∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ 2 < p ∧ 2 < q ∧ t+b i = p*q) ∧\n               (∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ 2 < p ∧ 2 < q ∧ t+b j = p*q)}.Infinite\n\n/-- For this family two explicit translations suffice to exclude any given\nprime divisor from all three forms. -/", "∀ h : ℕ, 0 < h → 6 ∣ h → ∀ p : ℕ, p.Prime →\n    ∃ t : ℕ, (t=0 ∨ t=h-1) ∧ ∀ i : Fin 3, ¬p ∣ t+(1+h*i.val)\n\n/-- Reading E2 as its defining set, this premise is the statement of\nErdos964.admissible_semiprime_triples in the published Lean development. -/"]'),
(8988, 'oeis-a157409', 1, 'physbuzz', 35::int, '["∀ m : ℕ, (∀ j : ℕ, 2^m/3^j%3≠2) → m=0 ∨ m=2 ∨ m=8\n\n/-- Beyond the finite exceptions, a power containing the digit 2 has an adjacent 12. -/", "∀ m : ℕ, 25 < m → (∃ j : ℕ, 2^m/3^j%3=2) →\n    ∃ j : ℕ, 2^m/3^j%9=5\n\nprivate lemma small_exact {n : ℕ} (lim : n≤26) :\n    (¬∃ k : ℕ,0<k ∧ 2^n/3^k%6=3) ↔ n∈({0,1,2,3,4,7,9,10,14,15,17,26} : Set ℕ) := by\n  have check : ∀ n : Fin 27, (∀ k : Fin 27,0<k.val → 2^n.val/3^k.val%6≠3) ↔\n      n.val∈({0,1,2,3,4,7,9,10,14,15,17,26} : Set ℕ) := by decide +kernel\n  have finite := check ⟨n,by omega⟩\n  constructor\n  · intro h\n    exact finite.mp (fun k pos eq => h ⟨k,pos,eq⟩)\n  · intro h ⟨k,pos,eq⟩\n    by_cases small : k<27\n    · exact (finite.mpr h) ⟨k,small⟩ pos eq\n    · have bound := Nat.pow_le_pow_right (by decide : 0<2) lim\n      have grow := Nat.pow_le_pow_right (by decide : 0<3) (show 27≤k by omega)\n      have gap : 2^26<3^27 := by decide\n      rw [Nat.div_eq_of_lt (lt_of_le_of_lt bound (lt_of_lt_of_le gap grow))] at eq\n      contradiction\n\n/-- Conversely, Luschny''s predicted large-n witnesses imply both steps, including Erdős''s conjecture. -/"]'),
(8993, 'Green92.green_92.variants.chase_lower.R1.H1.R1.H2.R1.H2', 1, 'jared-jasinski', null::int, '["∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, n % 4 = 3 →\n    let k := n / 4\n    let F (a : ℕ) (w : List Bool) := (a + (w.zip w.tail).count (false, true)).choose w.length\n    let B (w : List Bool) := F (2*k+1) w\n    let P (b : ℕ) (w : List Bool) (j : ℕ) := if w[j]? = some true then\n      F b (w.take j) * F (2*k+1-b) (w.drop (j+1)) else 0\n    let A (w : List Bool) (j : ℕ) := (P k w j : ℝ) - P (k+1) w j\n    let U := (range (n+1)).biUnion fun m => (univ : Finset (Fin m → Bool)).image List.ofFn\n    let E (w : List Bool) := |(w.length : ℝ)-2*k| ≤ sqrt k*log k ∧\n      |(((w.zip w.tail).count (false,true) : ℕ) : ℝ)-2*k/3| ≤ sqrt k*log k\n    (∑ w ∈ U.filter E,\n      ∑ p ∈ ((range w.length).product (range w.length)).filter\n        (fun p => p.1 ≤ p.2 + 5 ∧ p.2 ≤ p.1 + 5),\n        |A w p.1 * A w p.2 / ((2 : ℝ)^n * (max 1 (B w) : ℕ))|) ≤\n      C * (log n)^7 / (n : ℝ)^(3/2 : ℝ)", "∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, n % 4 = 3 →\n    let k := n / 4\n    let F (a : ℕ) (w : List Bool) := (a + (w.zip w.tail).count (false, true)).choose w.length\n    let B (w : List Bool) := F (2*k+1) w\n    let P (b : ℕ) (w : List Bool) (j : ℕ) := if w[j]? = some true then\n      F b (w.take j) * F (2*k+1-b) (w.drop (j+1)) else 0\n    let A (w : List Bool) (j : ℕ) := (P k w j : ℝ) - P (k+1) w j\n    let U := (range (n+1)).biUnion fun m => (univ : Finset (Fin m → Bool)).image List.ofFn\n    let E (w : List Bool) := |(w.length : ℝ)-2*k| ≤ sqrt k*log k ∧\n      |(((w.zip w.tail).count (false,true) : ℕ) : ℝ)-2*k/3| ≤ sqrt k*log k\n    (∑ w ∈ U.filter E,\n      ∑ p ∈ ((range w.length).product (range w.length)).filter\n        (fun p => ¬ (p.1 ≤ p.2 + 5 ∧ p.2 ≤ p.1 + 5)),\n        A w p.1 * A w p.2 / ((2 : ℝ)^n * (max 1 (B w) : ℕ))) ≤\n      C * (log n)^7 / (n : ℝ)^(3/2 : ℝ)"]'),
(8994, 'GoldbachConjecture.goldbach', 1, 'marcusbuffett', 66::int, '["∀ n : ℕ, 2 < n → Even n → n ≤ 10000 → ∃ p q, Prime p ∧ Prime q ∧ n = p + q\n\n/-- The open part. -/", "∀ n : ℕ, 10000 < n → Even n → ∃ p q, Prime p ∧ Prime q ∧ n = p + q"]'),
(9079, 'EuclidNumbers.infinite_prime_euclid_numbers', 1, 'Pixelstorm44', 66::int, '["∀ L : ℕ, ∃ U : ℕ,\n    (∑ d ∈ (range (Euclid U + 1)).filter (fun d => Squarefree d ∧ Nat.Coprime d (Euclid L - 1)),\n      (ArithmeticFunction.moebius d : ℝ) * Real.log d *\n      (((Ico L U).filter fun n => d ∣ Euclid n).card : ℝ)) < 0\n\n/-- A Euclid number cannot be a proper power. -/", "∀ n a k : ℕ, 1 < k → Euclid n ≠ a ^ k"]'),
(8897, 'PfisterPythagorasNumber.pfister_problem.variants.lower_bound', 1, 'mvanhorn', 17::int, '["¬ IsSumSqOfLength 3 (algebraMap (MvPolynomial (Fin 2) ℝ) (MvRatFunc (Fin 2) ℝ)\n    (1 + MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1 ^ 4 +\n      MvPolynomial.X 0 ^ 4 * MvPolynomial.X 1 ^ 2 -\n      3 * MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1 ^ 2))\n\n/-- Cassels (1964) variable-adjunction step: if f is not a sum of m squares in R(X_0, ..., X_{k-1}),\nthen f + X_k^2 is not a sum of m + 1 squares in R(X_0, ..., X_k). -/", "∀ (k m : ℕ) (f : MvPolynomial (Fin k) ℝ),\n    ¬ IsSumSqOfLength m (algebraMap (MvPolynomial (Fin k) ℝ) (MvRatFunc (Fin k) ℝ) f) →\n    ¬ IsSumSqOfLength (m + 1)\n      (algebraMap (MvPolynomial (Fin (k + 1)) ℝ) (MvRatFunc (Fin (k + 1)) ℝ)\n        (MvPolynomial.rename Fin.castSucc f + MvPolynomial.X (Fin.last k) ^ 2))"]'),
(8955, 'oeis-a270706', 1, 'physbuzz', 45::int, '["∀ n : ℕ, 32768<n → (∃! p : ℤ × ℤ, (0<p.1 ∧ 0<p.2 ∧ (8:ℤ)*n+1=p.1^2+2*p.2^2)) →\n    ∃ w : ℤ × ℤ × ℤ, (w.1≠0 ∧ 0<w.2.1 ∧ 0<w.2.2 ∧\n      (8:ℤ)*n+1-4*w.1^3*(w.1+1)=w.2.1^2+2*w.2.2^2) ∧ w.1≠-1\n\n/-- If 8n+1 has no positive pair, two pairs must be supplied by the shifted forms. -/", "∀ n : ℕ, 32768<n → (¬∃ p : ℤ × ℤ, (0<p.1 ∧ 0<p.2 ∧ (8:ℤ)*n+1=p.1^2+2*p.2^2)) →\n    ∃ w v : ℤ × ℤ × ℤ, (w.1≠0 ∧ 0<w.2.1 ∧ 0<w.2.2 ∧\n      (8:ℤ)*n+1-4*w.1^3*(w.1+1)=w.2.1^2+2*w.2.2^2) ∧ (v.1≠0 ∧ 0<v.2.1 ∧ 0<v.2.2 ∧\n      (8:ℤ)*n+1-4*v.1^3*(v.1+1)=v.2.1^2+2*v.2.2^2) ∧ w≠v"]'),
(8978, 'PoincareConjecture.poincare_conjecture.R1.H2.R1.H1.R1.H2.R1.H1', 1, 'NicholasWierenga', null::int, '["∀ (X : Type) [TopologicalSpace X] (U V : Set X), IsOpen U → IsOpen V →\n    let C := (singularChainComplexFunctor AddCommGrpCat.{0}).obj (AddCommGrpCat.of ℤ)\n    let i : TopCat.of (U ∩ V : Set X) ⟶ TopCat.of U :=\n      TopCat.ofHom ⟨Set.inclusion Set.inter_subset_left, continuous_inclusion _⟩\n    let j : TopCat.of (U ∩ V : Set X) ⟶ TopCat.of V :=\n      TopCat.ofHom ⟨Set.inclusion Set.inter_subset_right, continuous_inclusion _⟩\n    let l : TopCat.of U ⟶ TopCat.of (U ∪ V : Set X) :=\n      TopCat.ofHom ⟨Set.inclusion Set.subset_union_left, continuous_inclusion _⟩\n    let r : TopCat.of V ⟶ TopCat.of (U ∪ V : Set X) :=\n      TopCat.ofHom ⟨Set.inclusion Set.subset_union_right, continuous_inclusion _⟩\n    let h : CategoryStruct.comp (C.map i) (C.map l) = CategoryStruct.comp (C.map j) (C.map r) := by\n      rw [← C.map_comp, ← C.map_comp]\n      rfl\n    let Q := cokernel (pushout.desc (C.map l) (C.map r) h)\n    ∃ S : End Q, Nonempty (Homotopy S (𝟙 Q)) ∧\n      ∀ n (z : Q.X n), ∃ k : ℕ, ((S ^ k).f n) z = 0\n\n/-- The chain pushout embeds into the union complex, since its simplices\nare exactly those contained in one of the two subspaces. -/", "∀ (X : Type) [TopologicalSpace X] (U V : Set X),\n    let C := (singularChainComplexFunctor AddCommGrpCat.{0}).obj (AddCommGrpCat.of ℤ)\n    let i : TopCat.of (U ∩ V : Set X) ⟶ TopCat.of U :=\n      TopCat.ofHom ⟨Set.inclusion Set.inter_subset_left, continuous_inclusion _⟩\n    let j : TopCat.of (U ∩ V : Set X) ⟶ TopCat.of V :=\n      TopCat.ofHom ⟨Set.inclusion Set.inter_subset_right, continuous_inclusion _⟩\n    let l : TopCat.of U ⟶ TopCat.of (U ∪ V : Set X) :=\n      TopCat.ofHom ⟨Set.inclusion Set.subset_union_left, continuous_inclusion _⟩\n    let r : TopCat.of V ⟶ TopCat.of (U ∪ V : Set X) :=\n      TopCat.ofHom ⟨Set.inclusion Set.subset_union_right, continuous_inclusion _⟩\n    let h : CategoryStruct.comp (C.map i) (C.map l) = CategoryStruct.comp (C.map j) (C.map r) := by\n      rw [← C.map_comp, ← C.map_comp]\n      rfl\n    Mono (pushout.desc (C.map l) (C.map r) h)"]'),
(9001, 'WrittenOnTheWallII.GraphConjecture199.conjecture199.R1.H2.R1.H2', 1, 'loris-olsem', null::int, '["∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V),\n    G.Connected → Gᶜ.Connected → 3 ≤ vertexConnectivity G →\n    vertexConnectivity G + 2 ≤ G.indepNum →\n    largestInducedTreeSize G - 2 ≤ vertexConnectivity G →\n    (∀ U : Finset V, Nat.card (G.induce ((U : Set V)ᶜ)).ConnectedComponent ≤ U.card + 1) →\n    ¬ G.IsBipartite → G.CliqueFree 3 →\n    (∃ a : V, ∃ p : G.Walk a a, p.IsCycle ∧ p.length = 5) →\n    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian\n\n/-- Find a spanning path when the graph contains a triangle. -/", "∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V),\n    G.Connected → Gᶜ.Connected → 3 ≤ vertexConnectivity G →\n    vertexConnectivity G + 2 ≤ G.indepNum →\n    largestInducedTreeSize G - 2 ≤ vertexConnectivity G →\n    (∀ U : Finset V, Nat.card (G.induce ((U : Set V)ᶜ)).ConnectedComponent ≤ U.card + 1) →\n    ¬ G.CliqueFree 3 →\n    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian"]'),
(9002, 'oeis-a033188', 1, 'ZedingZhang', 62::int, '["∀ n : ℕ, 8 ≤ n →\n    (∀ p : ℕ, p.Prime → ∃ r : ℕ, ∀ i : Fin n, ¬ p ∣ r+(i:ℕ)*primorial n) →\n    ∃ a : ℕ, ∀ i : Fin n, (a+(i:ℕ)*primorial n).Prime\n\n/-- The only potentially smaller steps have this form and must start at n itself. -/", "∀ p : ℕ, 97 < p → p.Prime → ∀ k : ℕ, 0 < k → k < p →\n    ∃ i : Fin p, ¬ (p+(i:ℕ)*(primorial (p-1)*k)).Prime"]'),
(9015, 'Arxiv.2607.05739.tan_arctan_sum_not_integer', 2, 'mattdorman', 66::int, '["∀ n : ℕ, 5≤n → ∀ m : ℤ, (n<2^64 ∨ m.natAbs.log2<2^61) → B n ≠ A n*m", "∀ j : ℕ, 32≤j →\n    let N := 4^j\n    let C := (Ico N (4*N)).filter (fun n : ℕ => 8*(n:ℤ)*|A n| ≤ |B n|)\n    ∀ hC : C.Nonempty,\n      let n := C.max'' hC\n      ∀ m : ℤ, 2^(n/8) ≤ m.natAbs →\n        (∀ (p e d : ℕ) (u : ℤ), p.Prime → 0<d → (p:ℤ)^(e+d) ∣ 1+u^2 →\n          (p:ℤ)^(e+d) ∣ (∏ k ∈ Icc 1 n, (1+u*(k:ℤ))) →\n          (¬ (p:ℤ)^(e+1) ∣ (∏ k ∈ Icc 1 n, (1-u*(k:ℤ)))) → (p:ℤ)^d ∣ m-u) →\n        B n ≠ A n*m"]'),
(9018, 'Erdos1160.erdos_1160.variants.sum.R3.H1.R1.H2.R1.H3', 1, 'Thomassien', null::int, '["∀ G : FiniteGrp.{0}, Odd (Nat.card G) → Group.IsSolvable G", "∃ C D : ℕ, ∀ n : ℕ, 0 < n →\n    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''''\n      {G : FiniteGrp.{0} | Nat.card G = n ∧ Group.IsSolvable G}).ncard ≤\n    n^(C*(n.primeFactors.sup n.factorization)+D) *\n      ∏ p ∈ n.primeFactors, g (p^n.factorization p)"]'),
(9023, 'Erdos643.erdos_643.parts.ii.R1.H2', 1, 'MrSeizy', null::int, '["∀ r : ℕ, 4 ≤ r → ∀ a : ℕ, 0 < a → ∀ᶠ n : ℕ in atTop,\n    ∀ F : Finset (Finset (Fin n)), F.IsUniform r → ¬ F.HasRepeatedDisjointUnion →\n      (n - 1).choose (r - 1) ≤ F.card →\n      ∃ c : Fin n,\n        let m := (((Finset.univ.erase c).powersetCard (r - 1)).filter\n          fun W => insert c W ∉ F).card\n        a * m ≤ (n - 1).choose (r - 1)\n\n/-- A quadratic deficit threshold for a nearly full star.\n    Huang, Ma, and Yang, Claim 3.8 gives the stronger bound `n log n`. -/", "∀ r : ℕ, 4 ≤ r → ∃ a : ℕ, 0 < a ∧ ∀ᶠ n : ℕ in atTop,\n    ∀ (F : Finset (Finset (Fin n))) (c : Fin n),\n      F.IsUniform r → ¬ F.HasRepeatedDisjointUnion →\n      (n - 1).choose (r - 1) ≤ F.card →\n      let m := (((Finset.univ.erase c).powersetCard (r - 1)).filter\n        fun W => insert c W ∉ F).card\n      a * m ≤ (n - 1).choose (r - 1) →\n      4 * r * m < (n - 1 - 2 * r).choose 2"]'),
(9013, 'ManickamMiklosSinghiConjecture.manickam_miklos_singhi_conjecture.variants.pokrovskiy.R1.H2', 1, 'Iraeeee', null::int, '["∀ (k : ℕ) [NeZero k] (A B : Finset (Fin k)) (S : Finset (Fin k × Fin k)),\n    S ⊆ A ×ˢ B → (∀ u, u ∈ A ∨ -u ∈ A) → (∀ u, u ∈ B ∨ -u ∈ B) →\n    10000*(A ×ˢ B \\ S).card ≤ k^2 → 3*k ≤ 5*(S.image (fun p => p.1+p.2)).card\n\n/-- Localization and the short prefixes from Claims 5.2 and 5.9. The first\nvertex of the arc is s, its length is m, and F is its actual prefix-sum\nfunction. D may include the residues of all bad vertices in this orientation. -/", "∀ (n k : ℕ), (hk : 2 ≤ k) → (hl : 10^46*k ≤ n) → n < 8*k^2 → ∀ (hn : 2*k ≤ n)\n    (x : Fin n → ℝ), \n    let E := fun a : Fin n × Fin (k-1) × Fin (k-1) =>\n      univ.image (fun t : Fin k => a.1 + (⟨if t.val ≤ a.2.1.val then t.val else t.val+a.2.2.val+1,\n        by have := t.isLt; have := a.2.2.isLt; split <;> omega⟩ : Fin n))\n    (univ.filter (fun a => 0 ≤ ∑ v ∈ E a, x v)).card < k*(k-1)^2 →\n    letI : NeZero n := ⟨by omega⟩\n    letI : NeZero k := ⟨by omega⟩\n    ∃ (s : Fin n) (m : ℕ), 64*k ≤ m ∧ m ≤ n ∧\n      let F := fun t : ℕ => ∑ j ∈ range t, x (s + Fin.ofNat n j)\n      (∑ v, x v) ≤ F m ∧ ∀ rev : Bool,\n        let f := fun t => if rev then F m - F (m-t) else F t\n        ∃ (A B D : Finset (Fin k)) (S : Finset (Fin k × Fin k)),\n          S ⊆ A ×ˢ B ∧ (∀ u, u ∈ A ∨ -u ∈ A) ∧ (∀ u, u ∈ B ∨ -u ∈ B) ∧\n          10000*(A ×ˢ B \\ S).card ≤ k^2 ∧ 100*D.card ≤ k ∧\n          (∀ p ∈ S, f (13*k+p.1.val+p.2.val) < 0) ∧\n          (∀ u : ℕ, Fin.ofNat k u ∉ D → ∀ d : ℕ, d = 2 ∨ d = 3 →\n            u+d*k ≤ m → f (u+d*k) < f u)\n\n/-- Reach every cut in the same residue at distance at least two periods, using\nonly two-period and three-period decreases. -/"]'),
(9032, 'OeisA67720.prime_add_one_of_a', 1, 'LDJAI', 56::int, '["∀ k : ℕ, 1 < k → Odd k →\n    (k ^ 2 + 1).totient = k * (k + 1).totient →\n    (∀ p d : ℕ, p.Prime → k = p * d → p ≤ d ^ 2) →\n    ¬ (k ^ 2 + 1).Prime →\n    (∀ p q : ℕ, p.Prime → q.Prime → k ^ 2 + 1 ≠ p * q) →\n    16 ∣ (k + 1).totient →\n    (∀ p : ℕ, p.Prime → k + 1 ≠ 2 * p ∧ k + 1 ≠ 4 * p ∧ k + 1 ≠ 8 * p) → False\n\n/-- For even inputs the quadratic must have at least three distinct primes if squarefree. -/", "∀ k : ℕ, 1 < k → Even k →\n    (k ^ 2 + 1).totient = k * (k + 1).totient →\n    (∀ p d : ℕ, p.Prime → k = p * d → p ≤ d ^ 2) →\n    ¬ (k ^ 2 + 1).Prime →\n    (∀ p q : ℕ, p.Prime → q.Prime → k ^ 2 + 1 ≠ p * q) →\n    (Squarefree (k ^ 2 + 1) → 64 ∣ k * (k + 1).totient) →\n    (∀ a : ℕ, k + 1 ≠ 3 ^ a ∧ k + 1 ≠ 5 ^ a) → (k + 1).Prime"]'),
(9042, 'RamseyNumbers.ramsey_number_three_nine.R1.H2.R1.H2', 1, 'physbuzz', null::int, '["∀ (G : SimpleGraph (Fin 22)) [DecidableRel G.Adj],\n  G.CliqueFree 3 → Gᶜ.CliqueFree 7 → 59 ≤ G.edgeFinset.card\n\n/-- Forbid extensions of the sparse non-neighborhoods on 19 to 21 vertices.\nRows are independent and describe the neighbors of each added vertex.\nAn independent set chosen from the added vertices and the untouched old\nvertices gives exactly the displayed cardinality constraint. -/", "∀ (j : Fin 3) (V W : Type) [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W],\n  Fintype.card V = 21-j.val → Fintype.card W=j.val+5 →\n  ∀ (K : SimpleGraph V) [DecidableRel K.Adj], K.CliqueFree 3 → Kᶜ.CliqueFree 7 →\n    K.edgeFinset.card ≤ (![52,46,38] : Fin 3 → ℕ) j →\n    ∀ A : W → Finset V, (∀ a, Kᶜ.IsClique (A a)) →\n    (∀ S : Finset V, Kᶜ.IsClique S →\n      ((univ : Finset W).filter (fun a => Disjoint (A a) S)).card+S.card≤7) →\n    85 ≤ K.edgeFinset.card + Fintype.card W + ∑ a, (A a).card"]'),
(9146, 'Green5.green_5.variants.kedlaya', 1, 'justusklocke-cloud', 17::int, '["∃ a > (0 : ℝ), ∀ (Q : Type) [Group Q] [Fintype Q], IsSimpleGroup Q →\n    (¬ ∀ x y : Q, x * y = y * x) →\n    ∃ H : Subgroup Q, H ≠ ⊤ ∧ (H.index : ℝ) ≤ a * (Fintype.card Q : ℝ) ^ ((3 : ℝ) / 7)\n\n/-- Kedlaya''s product-free set bound from a proper subgroup of given index. -/", "∃ b > (0 : ℝ), ∀ (Q : Type) [Group Q] [Fintype Q] (H : Subgroup Q), H ≠ ⊤ →\n    ∃ T : Finset Q, IsProductFree (T : Set Q) ∧\n      b * Fintype.card Q / (H.index : ℝ) ^ ((1 : ℝ) / 2) ≤ (T.card : ℝ)"]'),
(9141, 'oeis-a004044', 1, 'ZedingZhang', 62::int, '["∀ m : ℕ, 0 < m → let n := (3^m+1)/2\n    ∀ C : Finset (Fin n → Fin 3), IsCoveringCode n C →\n    let e := fun x => (C.filter (fun c => hammingDist x c ≤ 1)).card - 1\n    (∑ x ∈ C, e x) = 0 → 2*C.card ≤ ∑ x ∈ Cᶜ, e x\n\n/-- When the centers themselves account for some but less than two excess\n    covers per center, the other words must make up the shortfall. -/", "∀ m : ℕ, 0 < m → let n := (3^m+1)/2\n    ∀ C : Finset (Fin n → Fin 3), IsCoveringCode n C →\n    let e := fun x => (C.filter (fun c => hammingDist x c ≤ 1)).card - 1\n    let inside := ∑ x ∈ C, e x\n    0 < inside → inside < 2*C.card → 2*C.card - inside ≤ ∑ x ∈ Cᶜ, e x"]'),
(9166, 'Green100.green_100.parts.ii.R1.H2.R1.H2.R1.H2', 1, 'sobrien032', null::int, '["∃ (R : Finset (List (Fin 74 × Bool))) (Q : Type) (_ : Group Q) (X : Type) (_ : MulAction Q X) (p : X) (h t : Q),\n  let S := FreeGroup.mk '''' (↑R : Set (List (Fin 74 × Bool)))\n  let J := PresentedGroup.mk S (FreeGroup.of (72 : Fin 74))\n  h • p = p ∧ h • (t • p) ≠ t • p ∧\n  (∀ (G : Type) [Group G] (a b : Q →* G) (j z : G), (∀ q, q • p = p → a q = b q) → j ^ 2 = 1 →\n    (∀ q, Commute j (a q) ∧ Commute j (b q)) → Commute j z →\n    z * ⁅a h, b t * (a t)⁻¹⁆ * z⁻¹ = ⁅a h, b t * (a t)⁻¹⁆ * j → ∃ f : PresentedGroup S →* G, f J = j) ∧\n  ∃ (x : Fin 3 → Fin 3 → Fin 7 → PresentedGroup S) (c : Fin 3 → Fin 3 → PresentedGroup S),\n  let E := {g | ∃ i j m, i ≠ j ∧ m.val < 4 ∧ x i j m = g}\n  (∀ i m, x i i m = 1 ∧ c i i = 1) ∧ (∀ i j m, x i j m ^ 5 = 1) ∧\n  (∀ i j k l m n, i ≠ l → j ≠ k → ⁅x i j m, x k l n⁆ = 1 ∧ ⁅c i j, c k l⁆ = 1) ∧\n  (∀ i j k m, i ≠ j → j ≠ k → i ≠ k →\n    ⁅x i j m, x j k 0⁆ = x i k m ∧ ⁅x i j 0, x j k m⁆ = x i k m ∧ ⁅c i j, c j k⁆ = c i k) ∧\n  (∀ i j k a b m n l, i ≠ j → j ≠ k → i ≠ k → i ≠ b → k ≠ a → ⁅⁅x i j m, x j k n⁆, x a b l⁆ = 1) ∧\n  (c 0 1 * (c 1 0)⁻¹ * c 0 1) ^ 4 = 1 ∧\n  (∀ a b i j m, c a b * x i j m * (c a b)⁻¹ ∈ Subgroup.closure (Set.range ↿x) ∧\n    (c a b)⁻¹ * x i j m * c a b ∈ Subgroup.closure (Set.range ↿x) ∧\n    x i j m ∈ Subgroup.closure (E ∪ Set.range ↿c) ∧\n    (m.val < 4 → c a b * x i j m * (c a b)⁻¹ ∈ Subgroup.closure E)) ∧\n  ∀ (G : Type) [Group G] (f : PresentedGroup S →* G),\n    f (c 0 1) ∈ Subgroup.normalizer (Subgroup.centralizer (f '''' E) : Set G) → f J = 1\n\n/-- Property (T) input (Ershov–Jaikin-Zapirain for the relations (3.1)–(3.5), Steinberg''s\npresentation of SL₃(ℤ), extension), transferred to every matrix ultraproduct: lifts of the\npositive generators, and of these together with the shears, have spectral gap. -/", "∀ (G : Type) [Group G] (x : Fin 3 → Fin 3 → Fin 7 → G) (c : Fin 3 → Fin 3 → G),\n  (∀ i m, x i i m = 1 ∧ c i i = 1) → (∀ i j m, x i j m ^ 5 = 1) →\n  (∀ i j k l m n, i ≠ l → j ≠ k → ⁅x i j m, x k l n⁆ = 1 ∧ ⁅c i j, c k l⁆ = 1) →\n  (∀ i j k m, i ≠ j → j ≠ k → i ≠ k →\n    ⁅x i j m, x j k 0⁆ = x i k m ∧ ⁅x i j 0, x j k m⁆ = x i k m ∧ ⁅c i j, c j k⁆ = c i k) →\n  (∀ i j k a b m n l, i ≠ j → j ≠ k → i ≠ k → i ≠ b → k ≠ a → ⁅⁅x i j m, x j k n⁆, x a b l⁆ = 1) →\n  (c 0 1 * (c 1 0)⁻¹ * c 0 1) ^ 4 = 1 →\n  (∀ a b i j m, c a b * x i j m * (c a b)⁻¹ ∈ Subgroup.closure (Set.range ↿x) ∧\n    (c a b)⁻¹ * x i j m * c a b ∈ Subgroup.closure (Set.range ↿x) ∧\n    x i j m ∈ Subgroup.closure ({g | ∃ i j m, i ≠ j ∧ m.val < 4 ∧ x i j m = g} ∪ Set.range ↿c)) →\n  ∃ κ : ℝ, 0 < κ ∧ ∀ (d : ℕ → ℕ), (∀ n, 0 < d n) →\n  let U := (n : ℕ) → Matrix.unitaryGroup (Fin (d n)) ℂ\n  let q := fun (n : ℕ) (y : Matrix (Fin (d n)) (Fin (d n)) ℂ) => (∑ a, ∑ b, ‖y a b‖ ^ 2) / (d n : ℝ)\n  let B := fun (y : (n : ℕ) → Matrix (Fin (d n)) (Fin (d n)) ℂ) =>\n    ∃ C : ℝ, ∀ n, ‖Matrix.toEuclideanCLM (n := Fin (d n)) (𝕜 := ℂ) (y n)‖ ≤ C\n  ∀ (ρ : G →* U ⧸ Subgroup.normalClosure {v : U | Tendsto (fun n => hsDist (v n) 1) (hyperfilter ℕ) (𝓝 0)})\n    (w : Fin 3 → Fin 3 → Fin 8 → U), (∀ i j m, (w i j m : U ⧸ _) = ρ (if hm : m.val < 7 then x i j ⟨m.val, hm⟩ else c i j)) →\n  ∀ (s : Fin 8 → Prop) [DecidablePred s], s = (· < 4) ∨ s = (fun m => m < 4 ∨ m = 7) →\n  ∀ y, B y → ∃ e, B e ∧ (∀ i j m, i ≠ j → s m →\n    Tendsto (fun n => q n ((w i j m n : Matrix _ _ ℂ) * e n - e n * (w i j m n : Matrix _ _ ℂ))) (hyperfilter ℕ) (𝓝 0)) ∧\n  ∀ ε > 0, ∀ᶠ n in hyperfilter ℕ, κ * q n (y n - e n) ≤ ε + ∑ i, ∑ j, ∑ m,\n    if i ≠ j ∧ s m then q n ((w i j m n : Matrix _ _ ℂ) * y n - y n * (w i j m n : Matrix _ _ ℂ)) else 0\n\n/-- Alekseev–Liu–Thom, Theorem B: a spectral gap off the relative commutant of a finite unitary\ntuple in a tracial matrix ultraproduct makes that relative commutant internal. -/", "∀ (d : ℕ → ℕ), (∀ n, 0 < d n) → ∀ (ι : Type) [Fintype ι]\n    (u : ι → (n : ℕ) → Matrix.unitaryGroup (Fin (d n)) ℂ) (κ : ℝ), 0 < κ →\n  let q := fun (n : ℕ) (y : Matrix (Fin (d n)) (Fin (d n)) ℂ) => (∑ a, ∑ b, ‖y a b‖ ^ 2) / (d n : ℝ)\n  let B := fun (y : (n : ℕ) → Matrix (Fin (d n)) (Fin (d n)) ℂ) =>\n    ∃ C : ℝ, ∀ n, ‖Matrix.toEuclideanCLM (n := Fin (d n)) (𝕜 := ℂ) (y n)‖ ≤ C\n  let K := fun (y : (n : ℕ) → Matrix (Fin (d n)) (Fin (d n)) ℂ) => B y ∧ ∀ a,\n    Tendsto (fun n => q n ((u a n : Matrix _ _ ℂ) * y n - y n * (u a n : Matrix _ _ ℂ))) (hyperfilter ℕ) (𝓝 0)\n  (∀ y, B y → ∃ e, K e ∧ ∀ ε > 0, ∀ᶠ n in hyperfilter ℕ,\n    κ * q n (y n - e n) ≤ ε + ∑ a, q n ((u a n : Matrix _ _ ℂ) * y n - y n * (u a n : Matrix _ _ ℂ))) →\n  ∃ A : (n : ℕ) → StarSubalgebra ℂ (Matrix (Fin (d n)) (Fin (d n)) ℂ), ∀ y, B y →\n    (K y ↔ ∃ a, B a ∧ (∀ n, a n ∈ A n) ∧ Tendsto (fun n => q n (y n - a n)) (hyperfilter ℕ) (𝓝 0))\n\n/-- Thom''s normalization theorem in the internal case: if the relative commutants of a tuple\nand of its extension are internal and each added unitary conjugates the first commutant into\nitself, then it conjugates that commutant onto itself. -/", "∀ (d : ℕ → ℕ), (∀ n, 0 < d n) → ∀ (ι : Type) [Fintype ι] (s : ι → Bool)\n    (u : ι → (n : ℕ) → Matrix.unitaryGroup (Fin (d n)) ℂ),\n  let q := fun (n : ℕ) (y : Matrix (Fin (d n)) (Fin (d n)) ℂ) => (∑ a, ∑ b, ‖y a b‖ ^ 2) / (d n : ℝ)\n  let B := fun (y : (n : ℕ) → Matrix (Fin (d n)) (Fin (d n)) ℂ) =>\n    ∃ C : ℝ, ∀ n, ‖Matrix.toEuclideanCLM (n := Fin (d n)) (𝕜 := ℂ) (y n)‖ ≤ C\n  let K := fun (all : Bool) (y : (n : ℕ) → Matrix (Fin (d n)) (Fin (d n)) ℂ) => B y ∧ ∀ a, (all || s a) = true →\n    Tendsto (fun n => q n ((u a n : Matrix _ _ ℂ) * y n - y n * (u a n : Matrix _ _ ℂ))) (hyperfilter ℕ) (𝓝 0)\n  let I := fun (all : Bool) => ∃ A : (n : ℕ) → StarSubalgebra ℂ (Matrix (Fin (d n)) (Fin (d n)) ℂ), ∀ y, B y →\n    (K all y ↔ ∃ a, B a ∧ (∀ n, a n ∈ A n) ∧ Tendsto (fun n => q n (y n - a n)) (hyperfilter ℕ) (𝓝 0))\n  I false → I true →\n  (∀ a, s a = false → ∀ y, K false y → K false (fun n => star (u a n : Matrix _ _ ℂ) * y n * (u a n : Matrix _ _ ℂ))) →\n  ∀ a, s a = false → ∀ y, K false y → K false (fun n => (u a n : Matrix _ _ ℂ) * y n * star (u a n : Matrix _ _ ℂ))\n\n/-! ### Matrix norms, the quotient `U ⧸ N`, and asymptotic commutation -/\n\n/-- Column estimate: the squared Frobenius norm of `Y * A` is at most the squared operator\nnorm of `Y` times the squared Frobenius norm of `A`. -/"]'),
(9171, 'Erdos423.erdos_423.variants.upper_bound', 1, 'dwilfand-sys', 21::int, '["∀ a : ℕ → ℕ, StrictMono (fun k : ℕ => a (k + 1)) →\n    ∀ η : ℝ, 0 < η → ∃ C : ℝ, 0 < C ∧ ∀ᶠ m : ℕ in atTop,\n      (m : ℝ) ^ ((1101 : ℝ) / 688 - η) ≤\n        C * (({s : ℕ | Erdos423.IsConsecutiveBlockSum a (m + 1) s}).ncard : ℝ)\n\n-- Tang''s transfer step relates the count of distinct sums to growth of the greedy sequence.", "∀ a : ℕ → ℕ, Erdos423.IsHofstadterSeq a → ∀ c : ℝ, 1 < c →\n    (∀ η : ℝ, 0 < η → ∃ C : ℝ, 0 < C ∧ ∀ᶠ m : ℕ in atTop,\n      (m : ℝ) ^ (c - η) ≤\n        C * (({s : ℕ | Erdos423.IsConsecutiveBlockSum a (m + 1) s}).ncard : ℝ)) →\n    ∀ ε : ℝ, 0 < ε → (fun n : ℕ => (a n : ℝ)) =O[atTop]\n      (fun n : ℕ => (n : ℝ) ^ ((1 : ℝ) / (c - 1) + ε))"]'),
(9189, 'Erdos820.erdos_820.variants.erdos_lower.R1.H1', 2, 'steveDOTdigital', null::int, '["∃ B : ℕ, ∀ᶠ x : ℕ in atTop, ∃ E : Finset ℕ,\n  E.card ≤ B ∧ (∀ p ∈ E, Nat.Prime p) ∧ ∀ d : ℕ, 0 < d → d^10 ≤ x →\n    (∀ p ∈ E, ¬p ∣ d) →\n    (Nat.primesLE x).card ≤ 2 * d.totient * ((Nat.primesLE x).filter (fun p => d ∣ p-1)).card\n\n/-- Finite averaging with a positive multiplier at most x. -/", "∀ k x : ℕ, 0 < k → 0 < x → ∃ t ∈ Icc 1 x,\n  (∑ d ∈ k.divisors, d.totient * ((Nat.primesLE x).filter (fun p => d ∣ p-1)).card) ≤\n    x * ((range (k*t+2)).filter (fun p => p.Prime ∧ p-1 ∣ k*t)).card"]'),
(9266, 'mo-300962', 1, 'physbuzz', 62::int, '["∀ n : ℕ,1<n → ((4*n+1)%5=1 ∨ (4*n+1)%5=4) →\n    (∀ j x y : ℕ,4*n+1≠4*(1+5^j)+x^2+y^2) →\n    ∃ c d x y : ℕ,4*n+1=20*(5^c+5^d)+x^2+25*y^2\n\n/-- In the nonsquare unit classes, multiply by 2 before using the same form. -/", "∀ n : ℕ,1<n → ((4*n+1)%5=2 ∨ (4*n+1)%5=3) →\n    (∀ j x y : ℕ,4*n+1≠4*(1+5^j)+x^2+y^2) →\n    ∃ c d x y : ℕ,2*(4*n+1)=40*(5^c+5^d)+x^2+25*y^2\n\nprivate lemma translated {n c d x y : ℕ} (eq : 4*n+1=4*(5^c+5^d)+x^2+y^2) :\n    ∃ a b c d : ℕ,n=triangular a+triangular b+5^c+5^d := by\n  obtain ⟨a,b,h⟩ := (shifted n (5^c+5^d)).mpr ⟨x,y,eq⟩\n  exact ⟨a,b,c,d,by omega⟩\n\n/-- Any universal representation also proves both arithmetic steps. -/"]'),
(9249, 'Erdos713.erdos_713.parts.ii', 3, 'mucoucah', 99::int, '["∀ (r : ℕ) (F : SimpleGraph (Fin r)), F.IsBipartite →\n    ¬ completeBipartiteGraph (Fin 2) (Fin 2) ⊑ F →\n    ∀ α : ℝ, 1 < α → α < 3 / 2 →\n      (fun n : ℕ => (extremalNumber n F : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ α) →\n      ¬ (fun n : ℕ => (extremalNumber n F : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ) ^ α) →\n      (∀ (s : ℕ) (J : SimpleGraph (Fin s)), J ⊑ F →\n        s + J.edgeFinset.card < r + F.edgeFinset.card →\n        (fun n : ℕ => (extremalNumber n J : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ) ^ α)) →\n      (∀ (s : ℕ) (J : SimpleGraph (Fin s)), J ⊑ F → 2 ≤ J.edgeFinset.card →\n        (2 : ℝ) - ((s - 2 : ℕ) : ℝ) / ((J.edgeFinset.card - 1 : ℕ) : ℝ) < α) →\n      (∀ (R : Finset (Fin r)) (t : ℕ), 0 < t →\n        (∀ ⦃u v⦄, F.Adj u v → (u ∈ R ↔ v ∉ R)) →\n        ∀ E : Finset {v : Fin r // v ∉ R}, E.card ≤ t →\n          (∀ v ∉ E, F.degree v.val ≤ t) → α < 2 - 1 / (t : ℝ)) →\n      α ∈ Set.range ((↑) : ℚ → ℝ)\n\n/-- Above-three-halves case: a bipartite F, minimal at the power scale n^α with\n3/2 < α < 2, α strictly above every random-deletion exponent of a subgraph and strictly\nbelow every dependent-random-choice exponent 2 - 1/t, has rational α. -/", "∀ (r : ℕ) (F : SimpleGraph (Fin r)), F.IsBipartite →\n    ∀ α : ℝ, 3 / 2 < α → α < 2 →\n      (fun n : ℕ => (extremalNumber n F : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ α) →\n      ¬ (fun n : ℕ => (extremalNumber n F : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ) ^ α) →\n      (∀ (s : ℕ) (J : SimpleGraph (Fin s)), J ⊑ F →\n        s + J.edgeFinset.card < r + F.edgeFinset.card →\n        (fun n : ℕ => (extremalNumber n J : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ) ^ α)) →\n      (∀ (s : ℕ) (J : SimpleGraph (Fin s)), J ⊑ F → 2 ≤ J.edgeFinset.card →\n        (2 : ℝ) - ((s - 2 : ℕ) : ℝ) / ((J.edgeFinset.card - 1 : ℕ) : ℝ) < α) →\n      (∀ (R : Finset (Fin r)) (t : ℕ), 0 < t →\n        (∀ ⦃u v⦄, F.Adj u v → (u ∈ R ↔ v ∉ R)) →\n        ∀ E : Finset {v : Fin r // v ∉ R}, E.card ≤ t →\n          (∀ v ∉ E, F.degree v.val ≤ t) → α < 2 - 1 / (t : ℝ)) →\n      α ∈ Set.range ((↑) : ℚ → ℝ)"]'),
(9367, 'Transcendental.transcendental_gamma_one_div_four', 1, 'LordMike', 27::int, '["AlgebraicIndependent ℚ\n    (fun b : Bool => if b then π else ∫ x in (0 : ℝ)..1, 1 / √(1 - x ^ 4))\n\n/-- Euler''s Beta integral: `∫₀¹ dx / √(1 - x⁴) = B(1/4, 1/2) / 4 = Γ(1/4) Γ(1/2) / (4 Γ(3/4))`. -/", "∫ x in (0 : ℝ)..1, 1 / √(1 - x ^ 4) =\n    Real.Gamma (1 / 4) * Real.Gamma (1 / 2) / (4 * Real.Gamma (3 / 4))\n\n/-- A monomial `x ^ m * y ^ n` with `0 < m` in two algebraically independent reals is\ntranscendental. -/"]'),
(9386, 'LebesgueNagell.lebesgue_nagell', 1, 'Andyi955', 68::int, '["∀ (p : ℕ) (hp : p.Prime) (hodd : Odd p) (x y : ℤ),\n    x ^ 2 - 2 = y ^ p → (x = 1 ∨ x = -1) ∧ y = -1\n\n/-- Backward direction: `(±1, -1)` solves `x^2 - 2 = y^p` for every odd `p`. -/", "∀ (p : ℕ) (hp : p.Prime) (hodd : Odd p) (x y : ℤ),\n    (x = 1 ∨ x = -1) ∧ y = -1 → x ^ 2 - 2 = y ^ p"]'),
(9303, 'riemannZeta.distinct_prop_one_hundred', 1, 'PastaPastaPasta', 68::int, '["∀ B : ℝ, 1 ≤ B → ∀ ε : ℝ, 0 < ε → ∀ᶠ T : ℝ in atTop,\n    ∀ Z : Finset ℂ, (Z : Set ℂ) = nontrivialZeros riemannZeta 0 T →\n    ∀ u ∈ Set.Icc (1 / 2 : ℝ) B,\n    let m := fun z => (analyticOrderNatAt riemannZeta z : ℝ)\n    let L := Real.log T / (2 * Real.pi)\n    ((∫ v in 0..u, 1 - Real.sinc (Real.pi * v) ^ 2) - ε) * N riemannZeta 0 T ≤\n      ∑ z ∈ Z, ∑ w ∈ Z, if z.im < w.im ∧ (w.im - z.im) * L ≤ u then m z * m w else 0\n\n/-- The upper-bound consequence of (6.1) from Gallagher–Mueller and Fujii.\nThe bandwidth is first fixed sufficiently large, then the height tends to infinity. -/", "∀ ε : ℝ, 0 < ε → ∀ᶠ B : ℝ in atTop, ∀ᶠ T : ℝ in atTop,\n    ∀ Z : Finset ℂ, (Z : Set ℂ) = nontrivialZeros riemannZeta 0 T →\n    let m := fun z => (analyticOrderNatAt riemannZeta z : ℝ)\n    let K := fun u : ℝ => max 0 (1 - |u| * (Real.log T / (2 * Real.pi)) / B)\n    (∑ z ∈ Z, ∑ w ∈ Z, m z * m w * K (w.im - z.im)) ≤ (B + ε) * N riemannZeta 0 T\n\n/-- The leading term of the classical Riemann–von Mangoldt formula. -/", "Tendsto (fun T : ℝ => (N riemannZeta 0 T : ℝ) / (T * (Real.log T / (2 * Real.pi))))\n    atTop (𝓝 1)"]'),
(9412, 'Green14.W_3_15.R1.H1', 1, 'Genbox', null::int, '["∀ r : Fin 217 → Bool, r 108 = true →\n    (∀ i : Fin 217, 109 ≤ i.val → i.val ≤ 115 → r i = false) →\n    (∀ a d : Fin 217, 0 < d.val → a.val + 2 * d.val < 217 →\n      ¬ ∀ t : Fin 3, r (Fin.ofNat 217 (a.val + t.val * d.val)) = true) →\n    (∀ a d : Fin 217, 0 < d.val → a.val + 14 * d.val < 217 →\n      ¬ ∀ t : Fin 15, r (Fin.ofNat 217 (a.val + t.val * d.val)) = false) →\n    ∃ d : Fin 109, 0 < d.val ∧ ∀ t : Fin 2,\n      r (Fin.ofNat 217 (217 - (2 - t.val) * d.val)) = true", "∀ r : Fin 217 → Bool, r 108 = true →\n    (∃ i : Fin 217, 109 ≤ i.val ∧ i.val ≤ 115 ∧ r i = true) →\n    (∀ a d : Fin 217, 0 < d.val → a.val + 2 * d.val < 217 →\n      ¬ ∀ t : Fin 3, r (Fin.ofNat 217 (a.val + t.val * d.val)) = true) →\n    (∀ a d : Fin 217, 0 < d.val → a.val + 14 * d.val < 217 →\n      ¬ ∀ t : Fin 15, r (Fin.ofNat 217 (a.val + t.val * d.val)) = false) →\n    ∃ d : Fin 109, 0 < d.val ∧ ∀ t : Fin 2,\n      r (Fin.ofNat 217 (217 - (2 - t.val) * d.val)) = true", "∀ r : Fin 217 → Bool, r 108 = false →\n    (∀ a d : Fin 217, 0 < d.val → a.val + 2 * d.val < 217 →\n      ¬ ∀ t : Fin 3, r (Fin.ofNat 217 (a.val + t.val * d.val)) = true) →\n    (∀ a d : Fin 217, 0 < d.val → a.val + 14 * d.val < 217 →\n      ¬ ∀ t : Fin 15, r (Fin.ofNat 217 (a.val + t.val * d.val)) = false) →\n    ∃ d : Fin 109, 0 < d.val ∧ ∀ t : Fin 2,\n      r (Fin.ofNat 217 (217 - (2 - t.val) * d.val)) = true"]'),
(9456, 'Erdos1160.erdos_1160.variants.sum.R3.H1', 2, 'Msninmx', null::int, '["∃ C : ℕ, ∀ a m : ℕ, 3 ≤ m → a ≤ m →\n    2^(2*m^3) * g (2^a)^27 ≤ g (2^m)^27 * 2^(2*a^3+C*(m+1)^2)\n\n/-- Count the Sylow two-subgroup by isomorphism type and the odd Sylow\nsubgroups by their elementary presentations. The cost of assembling the\ntypes is at most an exponential with a quadratic exponent. -/", "∃ E : ℕ, ∀ a q m : ℕ, Odd q → 2^a*q < 2^m →\n    g (2^a*q) ≤ 2^(E*(m+1)^2) * g (2^a) *\n      ∏ p ∈ q.primeFactors, p^((q.factorization p).choose 2 + (q.factorization p).choose 3)"]'),
(9486, 'SnakeInBox.coil_small_dimensions.R1.H3', 1, 'steveDOTdigital', null::int, '["let R (a b : BitVec 6) := (a ^^^ b).toNat ∈ ({0,1,2,4,8,16,32} : Finset ℕ)\n  ∀ E O : Finset (BitVec 6), 0 ∈ E → 25 ≤ E.card →\n    (∀ v ∈ E, (O.filter (R v)).card=2) →\n    (∀ w ∈ O, (E.filter (R w)).card=2) →\n    (∀ u ∈ ([0,1,8,10,15,18,21,22,24,26,31,35,36,38,39,40,45,47,48,49,57,60,62,63] : List ℕ), ∀ i < 40, ∀ j < i,\n      E ≠ Finset.univ.filter (fun a : BitVec 6 =>\n        let added : Array ℕ := #[2,3,4,5,6,7,9,11,12,13,14,16,17,19,20,23,25,27,28,29,30,32,33,34,37,41,42,43,44,46,50,51,52,53,54,55,56,58,59,61]\n        (((0xd203a1d885648503 : ℕ) ^^^ (1 <<< u)) ||| (1 <<< added[i]!) ||| (1 <<< added[j]!)).testBit a.toNat)) →\n    E ≠ univ.filter (fun a : BitVec 6 => (0xd223a15a85648581 : ℕ).testBit a.toNat) →\n    ∃ A : Finset (BitVec 6), A ⊆ E ∧ A.Nonempty ∧ (E \\ A).Nonempty ∧\n      (O.filter (fun w => (A.filter (R w)).card=1)).card<2\n\n/-- The number of selected connectors crossing each cut is even. -/", "∀ E O : Finset (Finset (Fin 7)),\n  (∀ v ∈ E, (O.filter (fun w => (Hypercube 7).Adj v w)).card = 2) →\n  (∀ w ∈ O, (E.filter (fun v => (Hypercube 7).Adj w v)).card = 2) →\n  ∀ A ⊆ E, Even ((O.filter (fun w =>\n    (A.filter (fun a => (Hypercube 7).Adj w a)).card = 1)).card)"]'),
(7180, 'Erdos142.erdos_142.variants.lower', 3, 'mucoucah', 90::int, '["∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ S : Finset ℕ,\n    (∀ x ∈ S, ∃ j ∈ Finset.Ico n (2 * n), 4 * 4 ^ j < x ∧ x ≤ 5 * 4 ^ j) →\n    (¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < 3, a + i * d ∈ S) →\n    (∑ x ∈ S, (x : ℝ)⁻¹) ≤ ε\n\n/-- The same window decay for every progression length at least four. -/", "∀ k : ℕ, 4 ≤ k → ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ S : Finset ℕ,\n    (∀ x ∈ S, ∃ j ∈ Finset.Ico n (2 * n), 4 * 4 ^ j < x ∧ x ≤ 5 * 4 ^ j) →\n    (¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ S) →\n    (∑ x ∈ S, (x : ℝ)⁻¹) ≤ ε"]'),
(7195, 'Erdos99.erdos_99', 1, 'mucoucah', 92::int, '["∀ n : ℕ, 2 ≤ n → ∃ B : Finset (EuclideanSpace ℝ (Fin 2)), B.card = n ∧\n    (∀ p ∈ B, ∀ q ∈ B, p ≠ q → 1 ≤ dist p q) ∧ (∃ p ∈ B, ∃ q ∈ B, dist p q = 1) ∧\n    Metric.diam (B : Set (EuclideanSpace ℝ (Fin 2))) ≤ 2 * Real.sqrt n", "∀ᶠ n : ℕ in Filter.atTop, ∀ A : Finset (EuclideanSpace ℝ (Fin 2)), A.card = n →\n    (∀ p ∈ A, ∀ q ∈ A, p ≠ q → 1 ≤ dist p q) → (∃ p ∈ A, ∃ q ∈ A, dist p q = 1) →\n    Metric.diam (A : Set (EuclideanSpace ℝ (Fin 2))) ≤ 2 * Real.sqrt n →\n    (∀ v : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2),\n      (∀ p ∈ A, ∀ q ∈ A, dist p q = 1 → 0 ≤ ⟪p - q, v p - v q⟫_ℝ) →\n      ∃ p ∈ A, ∃ q ∈ A, dist p q = Metric.diam (A : Set (EuclideanSpace ℝ (Fin 2))) ∧\n        0 ≤ ⟪p - q, v p - v q⟫_ℝ) →\n    (¬ ∃ p ∈ A, ∃ q ∈ A, ∃ r ∈ A, dist p q = 1 ∧ dist q r = 1 ∧ dist p r = 1) →\n    ∃ B : Finset (EuclideanSpace ℝ (Fin 2)), B.card = n ∧\n      (∀ p ∈ B, ∀ q ∈ B, p ≠ q → 1 ≤ dist p q) ∧\n      Metric.diam (B : Set (EuclideanSpace ℝ (Fin 2))) <\n        Metric.diam (A : Set (EuclideanSpace ℝ (Fin 2)))"]')
) v(pr, t, rn, h, pts, st);
-- created_at := merge time, only for rows this transaction created (created_at = now())
update oma_reductions r set created_at = v.m from (values
(8664, '2026-11-27T18:00:03Z'::timestamptz),
(8661, '2026-11-27T18:00:29Z'::timestamptz),
(8675, '2026-11-27T18:00:44Z'::timestamptz),
(8676, '2026-11-27T18:00:48Z'::timestamptz),
(8680, '2026-11-27T18:00:54Z'::timestamptz),
(8709, '2026-11-27T18:02:56Z'::timestamptz),
(8710, '2026-11-27T18:03:32Z'::timestamptz),
(8713, '2026-11-27T18:03:35Z'::timestamptz),
(8724, '2026-11-27T18:03:57Z'::timestamptz),
(8719, '2026-11-27T18:04:04Z'::timestamptz),
(8725, '2026-11-27T18:04:07Z'::timestamptz),
(8731, '2026-11-27T18:04:19Z'::timestamptz),
(8740, '2026-11-27T18:04:56Z'::timestamptz),
(8892, '2026-11-27T18:14:57Z'::timestamptz),
(8920, '2026-11-27T18:15:09Z'::timestamptz),
(8939, '2026-11-27T18:15:50Z'::timestamptz),
(8973, '2026-11-27T18:17:31Z'::timestamptz),
(8975, '2026-11-27T18:17:40Z'::timestamptz),
(8985, '2026-11-27T18:18:04Z'::timestamptz),
(8987, '2026-11-27T18:18:20Z'::timestamptz),
(8988, '2026-11-27T18:18:24Z'::timestamptz),
(8993, '2026-11-27T18:18:37Z'::timestamptz),
(8994, '2026-11-27T18:18:39Z'::timestamptz),
(9079, '2026-11-27T18:21:44Z'::timestamptz),
(8897, '2026-11-27T18:24:57Z'::timestamptz),
(8955, '2026-11-27T18:25:12Z'::timestamptz),
(8978, '2026-11-27T18:25:28Z'::timestamptz),
(9001, '2026-11-27T18:25:46Z'::timestamptz),
(9002, '2026-11-27T18:25:54Z'::timestamptz),
(9015, '2026-11-27T18:25:57Z'::timestamptz),
(9018, '2026-11-27T18:26:09Z'::timestamptz),
(9023, '2026-11-27T18:26:17Z'::timestamptz),
(9013, '2026-11-27T18:26:38Z'::timestamptz),
(9032, '2026-11-27T18:26:41Z'::timestamptz),
(9042, '2026-11-27T18:26:50Z'::timestamptz),
(9146, '2026-11-27T18:33:09Z'::timestamptz),
(9141, '2026-11-27T18:33:20Z'::timestamptz),
(9166, '2026-11-27T18:34:16Z'::timestamptz),
(9171, '2026-11-27T18:34:30Z'::timestamptz),
(9189, '2026-11-27T18:35:26Z'::timestamptz),
(9266, '2026-11-27T18:37:15Z'::timestamptz),
(9249, '2026-11-27T18:37:40Z'::timestamptz),
(9367, '2026-11-27T18:47:57Z'::timestamptz),
(9386, '2026-11-27T18:48:01Z'::timestamptz),
(9303, '2026-11-27T18:48:04Z'::timestamptz),
(9412, '2026-11-27T18:48:45Z'::timestamptz),
(9456, '2026-11-27T18:49:53Z'::timestamptz),
(9486, '2026-11-27T18:50:20Z'::timestamptz),
(7180, '2026-11-27T18:50:43Z'::timestamptz),
(7195, '2026-11-27T18:51:06Z'::timestamptz)
) v(pr, m) where r.pr_url = 'https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/' || v.pr and r.created_at = now();
update oma_steps s set created_at = r.created_at from oma_reductions r where s.reduction = r.id and s.created_at = now();
update oma_events e set created_at = r.created_at from oma_reductions r
  where e.kind = 'reduced' and e.created_at = now() and e.problem_id = r.problem_id and e.detail = r.id || ' into ' || r.hyps || ' steps';
commit;

-- ===== batch 2: reductions, dependency level 0 (50 PRs: 7237 .. ) =====
begin;
select v.pr, case
  when exists (select 1 from oma_reductions r where r.pr_url = 'https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/' || v.pr) then json_build_object('skip','pr_exists')
  when exists (select 1 from oma_reductions r where r.id = v.t || '.R' || v.rn) then json_build_object('skip','id_exists')
  when v.pts is null and not exists (select 1 from oma_steps s where s.id = v.t) then json_build_object('error','unknown_target')
  else oma_register_reduction(v.t || '.R' || v.rn, v.t, v.h, 'https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/' || v.pr,
         'OMAReductions.R_' || regexp_replace(v.t || '.R' || v.rn, '[^A-Za-z0-9]', '_', 'g'), v.st::json,
         coalesce(v.pts, (select s.points from oma_steps s where s.id = v.t))) end r
from (values
(7237, 'Erdos50.erdos_50', 1, 'mucoucah', 93::int, '["∀ f : ℝ → ℝ, (∀ c ∈ Set.Icc (0 : ℝ) 1, {n : ℕ | (Nat.totient n : ℝ) < c * n}.HasDensity (f c)) →\n    ∀ x ∈ Set.Ioo (0 : ℝ) 1, (¬∃ d : ℕ, 0 < d ∧ x = (d.totient : ℝ) / d) → Irrational x →\n      ¬∃ y > 0, HasDerivWithinAt f y (Set.Icc 0 1) x\n\n/-- Rational interior points that are not of the form phi(d)/d. -/", "∀ f : ℝ → ℝ, (∀ c ∈ Set.Icc (0 : ℝ) 1, {n : ℕ | (Nat.totient n : ℝ) < c * n}.HasDensity (f c)) →\n    ∀ x ∈ Set.Ioo (0 : ℝ) 1, (¬∃ d : ℕ, 0 < d ∧ x = (d.totient : ℝ) / d) → ¬ Irrational x →\n      ¬∃ y > 0, HasDerivWithinAt f y (Set.Icc 0 1) x"]'),
(9489, 'PoincareConjecture.poincare_conjecture.R1.H4.R1.H2.R1.H1', 2, 'NicholasWierenga', null::int, '["let Φ := fun (w : ℝ → ℝ) (t : ℝ) =>\n    w t * (4 * t + 1) ^ (-(3 / 4) : ℝ) + 2 * Real.pi * (4 * t + 1) ^ (1 / 4 : ℝ)\n  ∀ (n : ℕ) (t : ℕ → ℝ) (w : ℕ → ℝ → ℝ), t 0 = 0 → Monotone t →\n    (∀ i < n, ContinuousOn (w i) (Icc (t i) (t (i + 1)))) →\n    (∀ i < n, ∀ x ∈ Ico (t i) (t (i + 1)), ∀ r > 0,\n      ∃ᶠ y in 𝓝[>] x, (y - x)⁻¹ * (Φ (w i) y - Φ (w i) x) < r) →\n    (∀ i < n, w (i + 1) (t (i + 1)) ≤ w i (t (i + 1))) →\n    0 ≤ w 0 0 → 0 ≤ w n (t n) →\n    t n ≤ ((1 + w 0 0 / (2 * Real.pi)) ^ 4 - 1) / 4", "let Φ := fun (w : ℝ → ℝ) (t : ℝ) =>\n    w t * (4 * t + 1) ^ (-(3 / 4) : ℝ) + 2 * Real.pi * (4 * t + 1) ^ (1 / 4 : ℝ)\n  ∀ (M : Type) [TopologicalSpace M] [T2Space M] [ChartedSpace (ℝ^3) M]\n    [CompactSpace M] [SecondCountableTopology M] [IsManifold (𝓡 3) ∞ M]\n    [SimplyConnectedSpace M],\n    ∃ a : ℝ, 0 ≤ a ∧ ∀ T ≥ 0,\n      (∃ f : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 → M,\n        ContMDiff (𝓡 3) (𝓡 3) ∞ f ∧ ∀ x, Function.Injective (mfderiv (𝓡 3) (𝓡 3) f x)) ∨\n      ∃ (n : ℕ) (t : ℕ → ℝ) (w : ℕ → ℝ → ℝ),\n        t 0 = 0 ∧ t n = T ∧ Monotone t ∧ w 0 0 = a ∧ 0 ≤ w n (t n) ∧\n        (∀ i < n, ContinuousOn (w i) (Icc (t i) (t (i + 1)))) ∧\n        (∀ i < n, ∀ x ∈ Ico (t i) (t (i + 1)), ∀ r > 0,\n          ∃ᶠ y in 𝓝[>] x, (y - x)⁻¹ * (Φ (w i) y - Φ (w i) x) < r) ∧\n        (∀ i < n, w (i + 1) (t (i + 1)) ≤ w i (t (i + 1)))"]'),
(7464, 'Erdos713.erdos_713.parts.ii', 2, 'mucoucah', 99::int, '["∀ (r : ℕ) (F : SimpleGraph (Fin r)), (∃ v, F.degree v < 2) →\n    ∀ α : ℝ, 1 < α →\n      ¬ (fun n : ℕ => (extremalNumber n F : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ) ^ α) →\n      (∀ (s : ℕ) (J : SimpleGraph (Fin s)), J ⊑ F →\n        s + J.edgeFinset.card < r + F.edgeFinset.card →\n        (fun n : ℕ => (extremalNumber n J : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ) ^ α)) →\n      False\n\n/-- Minimum-degree-two core: a bipartite graph of order n^α, α ∈ (1,2), minimal at that\nscale, with α strictly above every random-deletion exponent of its subgraphs, has\nrational α. -/", "∀ (r : ℕ) (F : SimpleGraph (Fin r)), F.IsBipartite → (∀ v, 2 ≤ F.degree v) →\n    ∀ α : ℝ, α ∈ Set.Ioo 1 2 →\n      (fun n : ℕ => (extremalNumber n F : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ α) →\n      ¬ (fun n : ℕ => (extremalNumber n F : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ) ^ α) →\n      (∀ (s : ℕ) (J : SimpleGraph (Fin s)), J ⊑ F →\n        s + J.edgeFinset.card < r + F.edgeFinset.card →\n        (fun n : ℕ => (extremalNumber n J : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ) ^ α)) →\n      (∀ (s : ℕ) (J : SimpleGraph (Fin s)), J ⊑ F → 2 ≤ J.edgeFinset.card →\n        (2 : ℝ) - ((s - 2 : ℕ) : ℝ) / ((J.edgeFinset.card - 1 : ℕ) : ℝ) < α) →\n      α ∈ Set.range ((↑) : ℚ → ℝ)"]'),
(9502, 'MagicSquares.exists_magic_square_squares', 1, 'mvanhorn', 69::int, '["{ p : ℚ × ℚ |\n    let a := 4 * p.1 * (1 - p.1 ^ 2) / (1 + p.1 ^ 2) ^ 2\n    let b := 4 * p.2 * (1 - p.2 ^ 2) / (1 + p.2 ^ 2) ^ 2\n    0 < a ∧ a < b ∧ b ≠ 2 * a ∧ a + b < 1 ∧\n    IsSquare (1 - (a + b)) ∧ IsSquare (1 + (a + b)) }.Infinite\n\n-- Open frontier: among the infinite Bremner 7-square rational locus, some parameter pair\n-- also makes the final conjugate pair 1 - (b - a) and 1 + (b - a) rational squares.", "{ p : ℚ × ℚ |\n    let a := 4 * p.1 * (1 - p.1 ^ 2) / (1 + p.1 ^ 2) ^ 2\n    let b := 4 * p.2 * (1 - p.2 ^ 2) / (1 + p.2 ^ 2) ^ 2\n    0 < a ∧ a < b ∧ b ≠ 2 * a ∧ a + b < 1 ∧\n    IsSquare (1 - (a + b)) ∧ IsSquare (1 + (a + b)) }.Infinite →\n  ∃ p : ℚ × ℚ,\n    let a := 4 * p.1 * (1 - p.1 ^ 2) / (1 + p.1 ^ 2) ^ 2\n    let b := 4 * p.2 * (1 - p.2 ^ 2) / (1 + p.2 ^ 2) ^ 2\n    0 < a ∧ a < b ∧ b ≠ 2 * a ∧ a + b < 1 ∧\n    IsSquare (1 - (a + b)) ∧ IsSquare (1 + (a + b)) ∧\n    IsSquare (1 - (b - a)) ∧ IsSquare (1 + (b - a))"]'),
(9511, 'Arxiv.2605.02731.dean_conjecture', 1, 'MrSeizy', 68::int, '["∀ {V : Type} [Fintype V] (G : SimpleGraph V) (z : V),\n    4 ≤ Fintype.card V → weakGraph 5 G z →\n    (∀ v, v ≠ z → 5 ≤ (G.neighborSet v).ncard) →\n    (completeGraph (Fin 5)).Free G → (completeBipartiteGraph (Fin 5) (Fin 5)).Free G →\n    HasCycle G 5\n\n/-- Rooted admissible paths with one exceptional internal vertex.\nThe progression starts at a path length of at least two. -/", "∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (x y z : V),\n    5 ≤ k → 4 ≤ Fintype.card V → x ≠ y → twoConn (addEdge G x y) →\n    (∀ v, v ≠ x → v ≠ y → v ≠ z → k ≤ (G.neighborSet v).ncard) →\n    ∃ a s : ℕ, 2 ≤ a ∧ (s = 1 ∨ s = 2) ∧\n      ∀ i < k - 1, PathOfLength G x y (a + s * i)\n\n/-- Residue zero in the weak-graph branch. Any two-vertex cut consists of the two\nnonadjacent neighbors of the possible deficient vertex. The exceptional families have\nalready been excluded by the clique and biclique conditions. -/", "∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (z : V),\n    6 ≤ k → 4 ≤ Fintype.card V → weakGraph k G z →\n    (∀ v, v ≠ z → k ≤ (G.neighborSet v).ncard) →\n    (completeGraph (Fin k)).Free G → (completeBipartiteGraph (Fin k) (Fin k)).Free G →\n    HasCycle G k"]'),
(9515, 'Erdos828.erdos_828.variants.lehmer_conjecture', 1, 'Andyi955', 48::int, '["∀ n : ℕ, 1 < n → Nat.totient n ∣ n - 1 → Prime n\n\n/-- Backward direction: for a prime `n > 1`, `phi n = n - 1` divides `n - 1`. -/", "∀ n : ℕ, 1 < n → Prime n → Nat.totient n ∣ n - 1"]'),
(9521, 'Erdos687.erdos_687.variants.iwaniec.R1.H1', 2, 'my-other-github-account', null::int, '["∃ A : ℝ, 0 < A ∧ ∀ᶠ x : ℕ in Filter.atTop, ∀ M : ℕ,\n    ∃ i : ℕ, (i : ℝ) < A * (x : ℝ) ^ 2 ∧ ∀ p ≤ x, p.Prime → ¬ p ∣ M + 1 + i\n\n/-- Elementary Mertens-type lower bound for the inverse Euler product. -/", "∀ x : ℕ, Real.log ((x : ℝ) + 1) ≤\n    (∏ p ∈ (Finset.range (x + 1)).filter Nat.Prime, (1 - (p : ℝ)⁻¹))⁻¹\n\n/-- Chebyshev lower bound for the prime-counting function. -/", "∀ x : ℕ, 64 ≤ x → (x : ℝ) / Real.log x ≤ 4 * (Nat.primeCounting x : ℝ)"]'),
(9538, 'Erdos1183.erdos_1183.parts.iii', 1, 'Andyi955', 72::int, '["∀ c : ℝ,\n    Filter.Eventually (fun n : ℕ => (n : ℝ) ^ c < (Erdos1183.F n : ℝ)) Filter.atTop\n\n/-- Upper bound: `F n` is eventually below every exponential `(1 + eps) ^ n`, `eps > 0`. -/", "∀ ε : ℝ, 0 < ε →\n    Filter.Eventually (fun n : ℕ => (Erdos1183.F n : ℝ) < (1 + ε) ^ n) Filter.atTop"]'),
(9552, 'Kakeya.kakeya_set_conjecture', 1, 'my-other-github-account', 66::int, '["∀ {n : ℕ} {s : ℝ}, 0 < s → ∀ {F : Set (EuclideanSpace ℝ (Fin n))},\n    Measure.hausdorffMeasure s F = 0 → ∀ {ε : ℝ≥0∞}, 0 < ε →\n    ∃ (x : ℕ → (EuclideanSpace ℝ (Fin n))) (r : ℕ → ℝ) (Z : Set (EuclideanSpace ℝ (Fin n))),\n      Z.Countable ∧ F ⊆ Z ∪ ⋃ j, Metric.ball (x j) (r j) ∧\n      (∀ j, 0 ≤ r j ∧ r j ≤ 1) ∧\n      (∑'' j, ENNReal.ofReal (r j) ^ s) ≤ (2 : ℝ≥0∞) ^ s * ε", "∀ {n : ℕ}, 2 ≤ n → ∀ (F : Set (EuclideanSpace ℝ (Fin n))), Kakeya.IsKakeya F → ∀ s : ℝ, 0 < s → s < n → ∃ c : ℝ≥0∞, 0 < c ∧\n      ∀ (x : ℕ → (EuclideanSpace ℝ (Fin n))) (r : ℕ → ℝ) (Z : Set (EuclideanSpace ℝ (Fin n))), Z.Countable →\n        F ⊆ Z ∪ ⋃ j, Metric.ball (x j) (r j) → (∀ j, 0 ≤ r j ∧ r j ≤ 1) →\n        c ≤ ∑'' j, ENNReal.ofReal (r j) ^ s"]'),
(8931, 'Erdos66.erdos_66', 1, 'Iraeeee', 98::int, '["∀ a : ℝ, 0 < a →\n  let p : ℕ → ℝ := fun i ↦ a * Real.sqrt ((1 + Real.log ((i : ℝ) + 1)) / ((i : ℝ) + 1))\n  Antitone p ∧ (∀ i, 0 ≤ p i) ∧ ∃ c : ℝ, 0 < c ∧\n    Tendsto (fun n : ℕ ↦ sumConv p p n / Real.log n) atTop (𝓝 c)\n\n/-- Simultaneous finite rounding with bounded prefix-sum error and\nsublogarithmic centered quadratic error. Prefixes may be chosen independently. -/", "∃ a : ℝ, 0 < a ∧\n  let p : ℕ → ℝ := fun i ↦ a * Real.sqrt ((1 + Real.log ((i : ℝ) + 1)) / ((i : ℝ) + 1))\n  ∃ D : ℝ, 0 ≤ D ∧ ∃ e : ℕ → ℝ, Tendsto e atTop (𝓝 0) ∧\n    ∀ N : ℕ, ∃ S : Finset ℕ, S ⊆ range (N + 1) ∧\n      let d : ℕ → ℝ := fun i ↦ (if i ∈ S then 1 else 0) - p i\n      ∀ n ≤ N, |∑ i ∈ range (n + 1), d i| ≤ D ∧\n        |sumConv d d n / Real.log n| ≤ e n\n\n/-- The prefix discrepancy condition alone is attainable at every finite horizon.\nTake the positions where the floor of the cumulative fractional mass increases. -/"]'),
(9477, 'OeisA135508.conjecture.R1.H2.R1.H1', 1, 'hayalows', null::int, '["∀ q : ℕ, q.Prime → 100 < q → q ≤ 100000 →\n  ∃ m : Fin 258, let r := m.val * q - 2\n    r.Prime ∧ 5 < r ∧ r < q^2 ∧ r % 3 = 2 ∧ q ∣ r+2", "∀ q : ℕ, q.Prime → 100000 < q → q ≤ 500000 →\n  ∃ m : Fin 278, let r := m.val * q - 2\n    r.Prime ∧ 5 < r ∧ r < q^2 ∧ r % 3 = 2 ∧ q ∣ r+2", "∀ q : ℕ, q.Prime → 500000 < q → q ≤ 1000000 →\n  ∃ m : Fin 260, let r := m.val * q - 2\n    r.Prime ∧ 5 < r ∧ r < q^2 ∧ r % 3 = 2 ∧ q ∣ r+2"]'),
(8606, 'mo-280192', 1, 'Iraeeee', 62::int, '["∀ i : Fin 4095,\n  let k := i.val + 2\n  let m := (3^k - 1) / 2^k + 1\n  3^k + m ≤ 2^k * m\n\n/-- Above the cutoff, it suffices to bound multiples indexed by integers prime to three. -/", "∀ k m : ℕ, 4096 < k → ¬ 3 ∣ m → 3^k ≤ 2^k*m → 3^k + m ≤ 2^k*m"]'),
(9571, 'Erdos1057.erdos_1057.variants.lichtman_lower_bound', 1, 'LordMike', 17::int, '["∀ β : ℝ, 15 / (32 * Real.sqrt (Real.exp 1)) < β →\n    ∃ C : ℝ, 1 ≤ C ∧ ∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℝ in atTop,\n      c * x / Real.log x ^ C ≤\n        (({p : ℕ | p.Prime ∧ x < (p : ℝ) ∧ (p : ℝ) ≤ 2 * x ∧\n          ∀ q : ℕ, q.Prime → q ∣ p - 1 → (q : ℝ) ≤ x ^ β}.ncard : ℕ) : ℝ)\n\n/-- Alford–Granville–Pomerance with Harman''s level `0.4736`: smooth shifted primes at exponent\n`β` give `C(x) ≥ x ^ (0.4736 (1 - β) - ε)`. -/", "∀ β : ℝ, 0 < β → β < 1 →\n    (∃ C : ℝ, 1 ≤ C ∧ ∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℝ in atTop,\n      c * x / Real.log x ^ C ≤\n        (({p : ℕ | p.Prime ∧ x < (p : ℝ) ∧ (p : ℝ) ≤ 2 * x ∧\n          ∀ q : ℕ, q.Prime → q ∣ p - 1 → (q : ℝ) ≤ x ^ β}.ncard : ℕ) : ℝ)) →\n    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in atTop,\n      x ^ ((0.4736 : ℝ) * (1 - β) - ε) ≤ Erdos1057.carmichaelCounting x"]'),
(9582, 'Erdos551.erdos_551', 1, 'my-other-github-account', 51::int, '["∀ k n : ℕ, 19 ≤ k → 3 ≤ n → n ≤ k →\n  graphRamsey (cycleGraph k) (completeGraph (Fin n)) = (k-1)*(n-1)+1", "∀ k n : ℕ, k ≤ 18 → 3 ≤ n → n ≤ k → ¬ (n = 3 ∧ k = 3) →\n  graphRamsey (cycleGraph k) (completeGraph (Fin n)) = (k-1)*(n-1)+1"]'),
(9578, 'Erdos946.erdos_946.variants.heathbrown_lower_bound.R1.H1.R1.H1', 1, 'justusklocke-cloud', null::int, '["∀ s c : Fin 7 → ℕ, (∀ i, 0 < s i) →\n    (∀ i j, i ≠ j → s i * c j ≠ s j * c i) →\n    (∀ p : ℕ, p.Prime → ∃ t : ℕ, ∀ i, ¬ p ∣ s i * t + c i) →\n    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ᶠ x : ℝ in atTop,\n      ∃ V : Finset ℕ, x / (log x)^7 ≤ C * V.card ∧ ∀ n ∈ V, 0 < n ∧ (n : ℝ) ≤ x ∧\n        let v := fun i => s i * n + c i\n        (∀ i, 1 < v i ∧ ∀ p ∈ (v i).primeFactors, x ^ δ < (p : ℝ)) ∧\n        (∑ i, (v i).primeFactors.card) ≤ 27\n\n/-- A single linear form has negligibly many values with a large square factor. -/", "∀ a b : ℕ, 0 < a → ∀ δ K : ℝ, 0 < δ → 0 < K → ∀ᶠ x : ℝ in atTop,\n    K * (((Icc 1 ⌊x⌋₊).filter fun n =>\n      ∃ p ∈ (a * n + b).primeFactors, x ^ δ < (p : ℝ) ∧ p ^ 2 ∣ a * n + b).card : ℝ)\n      ≤ x / (log x)^7"]'),
(9587, 'SidorenkoConjecture.sidorenko_conjecture_graphon.R1.H1.R1.H1.R1.H1', 1, 'my-other-github-account', null::int, '["let t : Fin 22 → Fin 3 → Fin 13 := ![![0,1,3],![0,1,9],![0,2,3],![0,2,9],![1,3,10],![1,7,10],![1,7,12],![1,9,12],![2,3,4],![2,4,9],![3,4,11],![3,10,11],![4,8,9],![4,8,11],![5,6,7],![5,6,11],![5,7,10],![5,10,11],![6,7,12],![6,8,11],![6,8,12],![8,9,12]]\n  let sL : Fin 3 → Fin 3 := ![0,0,1]\n  let sR : Fin 3 → Fin 3 := ![1,2,2]\n  let U := fun {A : Type} [Fintype A] (f : A → ℝ) => (∑ a, f a) / (Fintype.card A : ℝ)\n  let Q := {q : ℕ // q.Prime ∧ q ≠ 2}\n  let S := fun (d : ℕ) (q : Q) => {A : Matrix (Fin d) (Fin d) (ZMod q.val) // A.IsSymm}\n  ∃ d : ℕ, Even d ∧ 12 ≤ d ∧ ∃ (M : Q → Type) (_ : ∀ q, AddCommGroup (M q)) (_ : ∀ q, Fintype (M q))\n    (R : ∀ q, ℤ → M q → ℝ),\n    (∀ q ξ z, 0 ≤ R q ξ z) ∧ (∀ q ξ, (ξ = 1 ∨ ξ = -1) → U (R q ξ) = 1) ∧\n    (∀ q ξ z, R q ξ (-z) = R q ξ z) ∧\n    ∀ (T : Fin 22 → Finset (Fin 3)) (ξ : Fin 22 → Fin 3 → ℤ), (∀ j k, ξ j k = 1 ∨ ξ j k = -1) →\n      let b := fun (q : Q) (X : Fin 13 → S d q) (j : Fin 22) (k : Fin 3) => haveI : Fact (q.val.Prime) := ⟨q.2.1⟩; haveI : NeZero q.val := ⟨q.2.1.ne_zero⟩; decide (quadraticChar (ZMod q.val) ((X (t j (sL k))).val - (X (t j (sR k))).val).det = 1)\n      Filter.Tendsto (fun q => U (fun xy : (Fin 13 → M q) × (Fin 22 → M q) => ∏ j, ∏ k ∈ T j, R q (ξ j k) (xy.1 (t j k) - xy.2 j)) - (haveI : Fact (q.val.Prime) := ⟨q.2.1⟩; haveI : NeZero q.val := ⟨q.2.1.ne_zero⟩; U (fun X : Fin 13 → S d q => ∏ j, ∏ k, if sL k ∈ T j ∧ sR k ∈ T j then 1 + (if b q X j k then (1:ℝ) else -1)*(ξ j (sL k):ℝ)*(ξ j (sR k):ℝ) else 1))) (Filter.comap (fun q : Q => q.val) Filter.atTop) (nhds 0)", "let t : Fin 22 → Fin 3 → Fin 13 := ![![0,1,3],![0,1,9],![0,2,3],![0,2,9],![1,3,10],![1,7,10],![1,7,12],![1,9,12],![2,3,4],![2,4,9],![3,4,11],![3,10,11],![4,8,9],![4,8,11],![5,6,7],![5,6,11],![5,7,10],![5,10,11],![6,7,12],![6,8,11],![6,8,12],![8,9,12]]\n  let sL : Fin 3 → Fin 3 := ![0,0,1]\n  let sR : Fin 3 → Fin 3 := ![1,2,2]\n  let U := fun {A : Type} [Fintype A] (f : A → ℝ) => (∑ a, f a) / (Fintype.card A : ℝ)\n  let Q := {q : ℕ // q.Prime ∧ q ≠ 2}\n  let S := fun (d : ℕ) (q : Q) => {A : Matrix (Fin d) (Fin d) (ZMod q.val) // A.IsSymm}\n  let p : Fin 22 → Fin 3 → Fin 33 := ![![5,1,6],![5,3,9],![0,1,2],![0,3,4],![6,11,12],![19,11,20],![19,15,23],![9,15,16],![2,7,8],![7,4,10],![8,13,14],![12,13,21],![17,10,18],![17,14,22],![32,25,30],![32,27,29],![25,26,20],![26,27,21],![30,31,23],![28,29,22],![28,31,24],![18,24,16]]\n  ∀ d : ℕ, Even d → 12 ≤ d → ∀ f : (Fin 22 → Fin 3 → Bool) → ℝ,\n    let b := fun (q : Q) (X : Fin 13 → S d q) (j : Fin 22) (k : Fin 3) => haveI : Fact (q.val.Prime) := ⟨q.2.1⟩; haveI : NeZero q.val := ⟨q.2.1.ne_zero⟩; decide (quadraticChar (ZMod q.val) ((X (t j (sL k))).val - (X (t j (sR k))).val).det = 1)\n    Filter.Tendsto (fun q : Q => haveI : Fact (q.val.Prime) := ⟨q.2.1⟩; haveI : NeZero q.val := ⟨q.2.1.ne_zero⟩; U (fun X : Fin 13 → S d q => f (b q X))) (Filter.comap (fun q : Q => q.val) Filter.atTop) (nhds (U (fun η : Fin 33 → Bool => f (fun j k => η (p j k)))))"]'),
(9588, 'OeisA113213.conjecture', 1, 'Andyi955', 59::int, '["∀ᶠ n : ℕ in Filter.atTop, ∃ m, (2 ^ n - m).Prime ∧ (2 ^ n + m).Prime\n\n/-- The smallest such offset grows at most like `n ^ 3`. -/", "(fun n : ℕ => (a n : ℝ)) =O[Filter.atTop] (fun n : ℕ => (n ^ 3 : ℝ))"]'),
(9581, 'Erdos535.erdos_535.variants.sunflower_strong.R1.H1.R1.H1', 1, 'my-other-github-account', null::int, '["∀ (I : Type) [Fintype I] [DecidableEq I] [Nontrivial I] (x : I ↪ EuclideanSpace ℝ (Fin 2)),\n    ∃ Φ : (Σ d : I → ℕ, (∀ i, Fin (d i)) → ℂ) → ℝ,\n      (∀ X, 0 ≤ Φ X) ∧ Φ ⟨fun _ => 1, fun _ => 1⟩ = 1 ∧\n      (∀ X : Σ d : I → ℕ, (∀ i, Fin (d i)) → ℂ, (∀ z, X.2 z = 0) → Φ X = 0) ∧\n      (∀ X Y : Σ d : I → ℕ, (∀ i, Fin (d i)) → ℂ,\n        (∃ A : ∀ i, Matrix (Fin (Y.1 i)) (Fin (X.1 i)) ℂ,\n          ∀ y, Y.2 y = ∑ z, (∏ i, A i (y i) (z i)) * X.2 z) → Φ Y ≤ Φ X) ∧\n      (∀ X Y : Σ d : I → ℕ, (∀ i, Fin (d i)) → ℂ,\n        Φ ⟨fun i => X.1 i * Y.1 i, fun z => X.2 (fun i => (finProdFinEquiv.symm (z i)).1) *\n          Y.2 (fun i => (finProdFinEquiv.symm (z i)).2)⟩ = Φ X * Φ Y) ∧\n      (∀ X Y : Σ d : I → ℕ, (∀ i, Fin (d i)) → ℂ,\n        Φ ⟨fun i => X.1 i + Y.1 i, fun z =>\n          if h : ∀ i, (z i : ℕ) < X.1 i then X.2 (fun i => ⟨z i, h i⟩)\n          else if h'' : ∀ i, X.1 i ≤ z i then\n            Y.2 (fun i => ⟨z i - X.1 i, by have h2 : (z i : ℕ) < X.1 i + Y.1 i := (z i).2; have := h'' i; omega⟩)\n          else 0⟩ = Φ X + Φ Y) ∧\n      ∀ (S : Finset I) (hS : S.Nonempty),\n        Real.logb 2 (Φ ⟨fun i => if i ∈ S then 2 else 1,\n          fun z => if ∀ i ∈ S, ∀ j ∈ S, (z i : ℕ) = z j then 1 else 0⟩) =\n        (∫ u, S.sup'' hS (fun i => inner ℝ u (x i)) ∂ProbabilityTheory.stdGaussian _) /\n          ∫ u, Finset.univ.sup'' Finset.univ_nonempty (fun i => inner ℝ u (x i))\n            ∂ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin 2))", "∀ r : ℕ, 3 ≤ r → ∃ (I : Type) (_ : Fintype I) (_ : DecidableEq I) (_ : Nontrivial I)\n    (x : I ↪ EuclideanSpace ℝ (Fin 2)),\n    ∀ Φ : (Σ d : I → ℕ, (∀ i, Fin (d i)) → ℂ) → ℝ,\n      ((∀ X, 0 ≤ Φ X) ∧ Φ ⟨fun _ => 1, fun _ => 1⟩ = 1 ∧\n      (∀ X : Σ d : I → ℕ, (∀ i, Fin (d i)) → ℂ, (∀ z, X.2 z = 0) → Φ X = 0) ∧\n      (∀ X Y : Σ d : I → ℕ, (∀ i, Fin (d i)) → ℂ,\n        (∃ A : ∀ i, Matrix (Fin (Y.1 i)) (Fin (X.1 i)) ℂ,\n          ∀ y, Y.2 y = ∑ z, (∏ i, A i (y i) (z i)) * X.2 z) → Φ Y ≤ Φ X) ∧\n      (∀ X Y : Σ d : I → ℕ, (∀ i, Fin (d i)) → ℂ,\n        Φ ⟨fun i => X.1 i * Y.1 i, fun z => X.2 (fun i => (finProdFinEquiv.symm (z i)).1) *\n          Y.2 (fun i => (finProdFinEquiv.symm (z i)).2)⟩ = Φ X * Φ Y) ∧\n      (∀ X Y : Σ d : I → ℕ, (∀ i, Fin (d i)) → ℂ,\n        Φ ⟨fun i => X.1 i + Y.1 i, fun z =>\n          if h : ∀ i, (z i : ℕ) < X.1 i then X.2 (fun i => ⟨z i, h i⟩)\n          else if h'' : ∀ i, X.1 i ≤ z i then\n            Y.2 (fun i => ⟨z i - X.1 i, by have h2 : (z i : ℕ) < X.1 i + Y.1 i := (z i).2; have := h'' i; omega⟩)\n          else 0⟩ = Φ X + Φ Y) ∧\n      ∀ (S : Finset I) (hS : S.Nonempty),\n        Real.logb 2 (Φ ⟨fun i => if i ∈ S then 2 else 1,\n          fun z => if ∀ i ∈ S, ∀ j ∈ S, (z i : ℕ) = z j then 1 else 0⟩) =\n        (∫ u, S.sup'' hS (fun i => inner ℝ u (x i)) ∂ProbabilityTheory.stdGaussian _) /\n          ∫ u, Finset.univ.sup'' Finset.univ_nonempty (fun i => inner ℝ u (x i))\n            ∂ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin 2))) →\n      ∃ D : ℕ, 1 ≤ D ∧ ∀ (n m : ℕ) (W : Finset (Fin n → Fin m)),\n        (∀ w : Fin r → Fin n → Fin m, (∀ i, w i ∈ W) →\n          (∀ j : Fin n, (∀ a b, w a j = w b j) ∨ Function.Injective (fun i => w i j)) →\n          ∀ a b, w a = w b) →\n        W.card ≤ D ^ n"]'),
(9593, 'Erdos64.erdos_64.R1.H1.R1.H1.R1.H2.R2.H1.R1.H2', 1, 'mejiasd3v', null::int, '["∀ (B : Type) [AddCommGroup B] [Finite B] (a b : B),\n    a ≠ 0 → b ≠ 0 → a ≠ b → AddSubgroup.closure ({a,b} : Set B) = ⊤ →\n    ∀ (V : Type) [AddCommGroup V] (w : B → Fin 3 → V),\n    let G := SimpleGraph.fromRel fun l r : Bool × B × V =>\n      ∃ (i : B) (k : Fin 3) (g : V),\n        l = (false,i,g) ∧ r = (true,i + (![0,a,b] : Fin 3 → B) k,g + w i k)\n    cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G ∨ cycleGraph 32 ⊑ G\n\n/-- The regular odd-order residual with two noncommuting elements in the\ncommutator subgroup. -/", "∀ (A : Type) [Group A] [Fintype A] (a b : A),\n    Subgroup.closure ({a,b} : Set A) = ⊤ → a ≠ 1 → b ≠ 1 → a ≠ b → Odd (Nat.card A) →\n    (∀ N : Subgroup A, N.Normal → IsMulCommutative N → N.index ≠ 11) →\n    (∃ x y : commutator A, x * y ≠ y * x) →\n    ∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2^k) ⊑ SimpleGraph.fromRel (fun u v : Bool × A =>\n      u.1=false ∧ v.1=true ∧ (v.2=u.2 ∨ v.2=a*u.2 ∨ v.2=b*u.2))"]'),
(9606, 'Green28.green_28', 1, 'Andyi955', 68::int, '["∀ X Y : PMF ℤ, X.support.Finite → Y.support.Finite →\n    IsUniformOnSupport (indepSum X Y) → IsUniformOnSupport X\n\n/-- The second factor: a finitely supported `Y` whose convolution with a finitely supported `X` is\nuniform on its support is itself uniform on its support. -/", "∀ X Y : PMF ℤ, X.support.Finite → Y.support.Finite →\n    IsUniformOnSupport (indepSum X Y) → IsUniformOnSupport Y"]'),
(9612, 'Erdos1182.erdos_1182.variants.brandt_expects', 1, 'Andyi955', 48::int, '["Filter.Eventually (fun n : ℕ => 2 * n < Erdos1182.F n) Filter.atTop\n\n/-- Upper bound: eventually `F n` is below `6 n`. -/", "Filter.Eventually (fun n : ℕ => Erdos1182.F n < 6 * n) Filter.atTop"]'),
(9613, 'Erdos595.erdos_595', 1, 'TheWaler', 93::int, '["∀ (V : Type) (G : SimpleGraph V),\n  (∀ a b, G.Adj a b → Nonempty ({w : V | G.Adj a w ∧ G.Adj b w} ↪ (ℕ → Bool))) →\n  Erdos595.IsCountableUnionOfTriangleFree G\n\n/-- Construct an infinite triangle-Ramsey host. It may contain four-cliques,\nprovided that a countable list of continuum-codegree-bounded edge layers hits\nall of them. The common neighbours are measured inside each individual layer. -/", "∃ (V : Type) (_ : Infinite V) (X : SimpleGraph V),\n  (∀ c : X.EdgeLabeling ℕ, ∃ n, ¬ (c.labelGraph n).CliqueFree 3) ∧\n  ∃ F : ℕ → SimpleGraph V,\n    (∀ n a b, (F n).Adj a b → Nonempty ({w : V | (F n).Adj a w ∧ (F n).Adj b w} ↪ (ℕ → Bool))) ∧\n    ∀ s : Finset V, X.IsNClique 4 s → ∃ n, ∃ a ∈ s, ∃ b ∈ s, (F n).Adj a b"]'),
(9621, 'Erdos1162.erdos_1162.variants.roney_dougal_tracey_bounds', 1, 'Andyi955', 17::int, '["∃ α > (0 : ℝ), ∀ n : ℕ, 1 < n →\n    (2 : ℝ) ^ ((n : ℝ) ^ 2 / 16 + α * n * Real.logb 2 n) ≤ f n\n\n/-- The upper bound: some `β` with `f n <= 2 ^ (n ^ 2 / 16 + β n ^ (3/2))` for all `n > 1`\n(logarithm to base `2`). -/", "∃ β : ℝ, ∀ n : ℕ, 1 < n →\n    (f n : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) ^ 2 / 16 + β * (n : ℝ) ^ ((3 : ℝ) / 2))"]'),
(9622, 'Erdos420.erdos_420.parts.ii', 1, 'MrSeizy', 68::int, '["∀ m : ℕ, 0 < m → ∃ b : Finset ℕ, Admissible b ∧ (∀ j ∈ b, 0 < j) ∧\n    ∃ ρ c : ℝ, 0 < ρ ∧ 0 < c ∧ ∀ᶠ X : ℕ in atTop, ∀ M a : ℕ,\n      ModulusOK b X M a → c * scale b X M ≤ (goodAnchors b ρ m X M a).card\n\n/-- A uniform upper sieve for rough detectors and a prime quotient to their left. -/", "∀ (b : Finset ℕ), (∀ j ∈ b, 0 < j) →\n    ∀ (k : ℕ), 0 < k → ∀ ρ η : ℝ, 0 < ρ → 0 < η →\n      ∀ᶠ X : ℕ in atTop, ∀ M a : ℕ, ModulusOK b X M a →\n        ∀ d ∈ Ioc (lowCut b X) (highCut X),\n          (pairCount b ρ k X M a d : ℝ) ≤\n            η * scale b X M * ((lowCut b X : ℝ) / d + 1 / (1 + Real.log (highCut X)))\n\n/-- A covering progression preserving the detector offsets. -/", "∀ (b : Finset ℕ), Admissible b → (∀ j ∈ b, 0 < j) →\n    ∀ (k : ℕ), 0 < k → ∀ K B : ℕ, (∀ j ∈ b, k * j ≤ B) →\n      ∀ᶠ X : ℕ in atTop, ∃ M a : ℕ, ModulusOK b X M a ∧\n        ∀ u ∈ anchors X M a,\n          (∀ x ∈ leftWindow k X u, Covered M (lowCut b X) x) ∧\n          (∀ x ∈ Icc (k * u) (k * u + B + 1),\n            (∀ j ∈ b, x ≠ k * (u + j)) → Covered M K x)"]'),
(9630, 'BealConjecture.beal_conjecture.R1.H2', 2, 'ubuwaits', null::int, '["∀ {p q : ℕ} {x y : ℤ} {w : ℕ}, p.Prime → q.Prime → 2<p → p≤q →\n    x≠0 → y≠0 → 0<w → IsCoprime x y → x^p+y^q ≠ (w:ℤ)^4\n\n/-- Two fourth powers adding to an odd prime power of exponent at least five. -/", "∀ {p a b c : ℕ}, p.Prime → 5≤p → 0<a → 0<b → 0<c → a.Coprime b →\n    a^4+b^4 ≠ c^p\n\n/-- A progression of p-th powers with positive, distinct square endpoints. -/", "∀ {p u v w : ℕ}, p.Prime → 5≤p → 0<v → v<u → 0<w → u.Coprime v →\n    (u^2)^p+(v^2)^p ≠ 2*w^p\n\n/-- The weighted Fermat equation from two odd quartic bases. -/", "∀ {p u v w : ℕ}, p.Prime → 5≤p → 0<u → 0<v → 0<w → u.Coprime v →\n    (u^2)^p+(2^(p-3))^2*(v^2)^p ≠ w^p"]'),
(9643, 'PartitionParity.parkin_shanks', 1, 'Andyi955', 68::int, '["{n : ℕ | Even (Nat.partitionNumber n)}.HasDensity (1 / 2)\n\n/-- Half of the partition numbers are odd, asymptotically. -/", "{n : ℕ | Odd (Nat.partitionNumber n)}.HasDensity (1 / 2)"]'),
(9641, 'Erdos131.erdos_131.variants.pham_zakharov', 1, 'steveDOTdigital', 17::int, '["∀ σ : ℝ, 0 < σ → ∀ δ : ℝ, 0 < δ → ∀ᶠ N : ℕ in atTop,\n  ∀ A : Finset ℕ, A ⊆ Icc 1 N →\n    (∀ a ∈ A, ∀ T ⊆ A.erase a, T.Nonempty → ∑ x ∈ T, x ≠ a * T.card) →\n    (1 / 4 + σ) * Real.log N < Real.log A.card →\n    ∃ (d : ℕ) (hd : 0 < d) (lo hi : Fin d → ℤ) (S : Finset (Fin d → ℤ)),\n      S ⊆ Icc lo hi ∧ 5 ≤ S.card ∧\n      (∀ a ∈ S, ∀ T ⊆ S.erase a, T.Nonempty → ∑ x ∈ T, x ≠ T.card • a) ∧\n      Real.log A.card ≤ Real.log S.card + δ * Real.log N ∧\n      Real.log (Icc lo hi).card + ((d : ℝ) - 1) * Real.log A.card ≤\n        (1 + δ) * Real.log N ∧\n      (d = 1 → let P := S.image (fun x => x ⟨0, hd⟩)\n               ∀ a ∈ P, 4 * (P.filter (· < a)).card ≤ P.card ∨\n                         4 * (P.filter (a < ·)).card ≤ P.card)\n\n/-- The planar non-averaging box bound with a multiplicative\nconstant, expressed on a logarithmic scale. -/", "∀ δ : ℝ, 0 < δ → ∃ C : ℝ,\n    ∀ (lo hi : Fin 2 → ℤ) (S : Finset (Fin 2 → ℤ)),\n      S ⊆ Icc lo hi → S.Nonempty →\n      (∀ a ∈ S, ∀ T ⊆ S.erase a, T.Nonempty → ∑ x ∈ T, x ≠ T.card • a) →\n      3 * Real.log S.card ≤ (1 + δ) * Real.log (Icc lo hi).card + C\n\n/-- The three-dimensional non-averaging box bound with a multiplicative\nconstant, expressed on a logarithmic scale. -/", "∀ δ : ℝ, 0 < δ → ∃ C : ℝ,\n    ∀ (lo hi : Fin 3 → ℤ) (S : Finset (Fin 3 → ℤ)),\n      S ⊆ Icc lo hi → S.Nonempty →\n      (∀ a ∈ S, ∀ T ⊆ S.erase a, T.Nonempty → ∑ x ∈ T, x ≠ T.card • a) →\n      4 * Real.log S.card ≤ (2 + δ) * Real.log (Icc lo hi).card + C\n\n/-- A proper progression need only have unique coordinates on the selected\npoints. The linear map from the whole coefficient lattice can have a kernel. -/"]'),
(9649, 'UnionClosed.union_closed.variants.univ_card', 2, 'physbuzz', 17::int, '["∀ F : Finset (Finset (Fin 12)), IsUnionClosed F → ∅ ∈ F → univ ∈ F →\n    (∃ S ∈ F, S.card = 3) → (∀ S ∈ F, S.Nonempty → 3 ≤ S.card) →\n    ∃ w : Fin 12 → ℕ, 0 < ∑ i, w i ∧\n      F.card * (∑ i, w i) ≤ 2 * (∑ S ∈ F, ∑ i ∈ S, w i)\n\n-- The 4-element minimum case on the fixed twelve-coordinate universe.", "∀ F : Finset (Finset (Fin 12)), IsUnionClosed F → ∅ ∈ F → univ ∈ F →\n    (∃ S ∈ F, S.card = 4) → (∀ S ∈ F, S.Nonempty → 4 ≤ S.card) →\n    ∃ w : Fin 12 → ℕ, 0 < ∑ i, w i ∧\n      F.card * (∑ i, w i) ≤ 2 * (∑ S ∈ F, ∑ i ∈ S, w i)\n\n-- The 5-element minimum case on the fixed twelve-coordinate universe."]'),
(9659, 'AgrawalConjecture.agrawal_conjecture.R1.H1', 1, 'ppleskov', null::int, '["∀ n p : ℕ, 1 < n → ¬ n.Prime → Even n → p.Prime → 5 ≤ p → n.Coprime p →\n    (p + 1) * n.minFac ≤ n → ¬ p ∣ n ^ 2 - 1 →\n    ∃ m : ℕ, IsPrimePow m ∧ m ∣ n ∧\n      ¬ (X ^ p - 1 : (ZMod m)[X]) ∣ (X - 1) ^ n - (X ^ n - 1)\n\n/-- For odd n the root at zero removes a further minFac(n) degrees. -/", "∀ n p : ℕ, 1 < n → ¬ n.Prime → Odd n → p.Prime → 5 ≤ p → n.Coprime p →\n    (p + 2) * n.minFac ≤ n → ¬ p ∣ n ^ 2 - 1 →\n    ∃ m : ℕ, IsPrimePow m ∧ m ∣ n ∧\n      ¬ (X ^ p - 1 : (ZMod m)[X]) ∣ (X - 1) ^ n - (X ^ n - 1)"]'),
(9679, 'Erdos748.erdos_748.variants.asymptotic', 1, 'Andyi955', 17::int, '["∃ c₀ : ℝ, 0 < c₀ ∧\n    Tendsto (fun m : ℕ => (f (2 * m) : ℝ) / 2 ^ m) atTop (nhds c₀)\n\n/-- The odd subsequence `m ↦ f (2 * m + 1) / 2 ^ ((2 * m + 1) / 2)` converges to a positive\nlimit. -/", "∃ c₁ : ℝ, 0 < c₁ ∧\n    Tendsto (fun m : ℕ => (f (2 * m + 1) : ℝ) / 2 ^ ((2 * m + 1 : ℝ) / 2)) atTop (nhds c₁)"]'),
(9684, 'Erdos1057.erdos_1057.variants.harman_lower_bound', 1, 'LordMike', 17::int, '["∀ β : ℝ, 15 / (32 * Real.sqrt (Real.exp 1)) < β →\n    ∃ C : ℝ, 1 ≤ C ∧ ∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℝ in atTop,\n      c * x / Real.log x ^ C ≤\n        (({p : ℕ | p.Prime ∧ x < (p : ℝ) ∧ (p : ℝ) ≤ 2 * x ∧\n          ∀ q : ℕ, q.Prime → q ∣ p - 1 → (q : ℝ) ≤ x ^ β}.ncard : ℕ) : ℝ)\n\n/-- Alford–Granville–Pomerance with Harman''s level `0.4736`: smooth shifted primes at exponent\n`β` give `C(x) ≥ x ^ (0.4736 (1 - β) - ε)`. -/", "∀ β : ℝ, 0 < β → β < 1 →\n    (∃ C : ℝ, 1 ≤ C ∧ ∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℝ in atTop,\n      c * x / Real.log x ^ C ≤\n        (({p : ℕ | p.Prime ∧ x < (p : ℝ) ∧ (p : ℝ) ≤ 2 * x ∧\n          ∀ q : ℕ, q.Prime → q ∣ p - 1 → (q : ℝ) ≤ x ^ β}.ncard : ℕ) : ℝ)) →\n    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in atTop,\n      x ^ ((0.4736 : ℝ) * (1 - β) - ε) ≤ Erdos1057.carmichaelCounting x"]'),
(9698, 'OeisA110475.conjecture', 1, 'Andyi955', 59::int, '["∀ m : ℕ, 0 < m → m ∉ exceptionalSet → ∃ x y : ℕ, a x = 1 ∧ a y = 1 ∧ m = x + y\n\n/-- Backward direction: any positive `m` that decomposes as such a sum is outside the exceptional\nset. -/", "∀ m : ℕ, 0 < m → (∃ x y : ℕ, a x = 1 ∧ a y = 1 ∧ m = x + y) → m ∉ exceptionalSet"]'),
(9696, 'Erdos1057.erdos_1057.variants.agp_infinite', 2, 'LordMike', 17::int, '["∀ᶠ X : ℝ in atTop, ∃ (M b n t : ℕ) (P : Finset ℕ),\n    0 < b ∧ n+2 ≤ t ∧ t ≤ P.card ∧ ((b^t : ℕ) : ℝ) ≤ X ∧\n    (∀ p ∈ P, p.Prime ∧ p ≤ b ∧ p-1 ∣ M) ∧\n    (∀ S ⊆ P, n < S.card → ∃ I ⊆ S, I.Nonempty ∧ (∏ p ∈ I, p) ≡ 1 [MOD M]) ∧\n    X^(2/7 : ℝ) * (P.card.choose n : ℝ) < (P.card.choose t : ℝ)\n\n/-- Count distinct product-one subsets of length between t-n and t. -/", "∀ (P : Finset ℕ) (M n t : ℕ), n ≤ t → t ≤ P.card →\n    (∀ S ⊆ P, n < S.card → ∃ I ⊆ S, I.Nonempty ∧ (∏ p ∈ I, p) ≡ 1 [MOD M]) →\n    P.card.choose t ≤\n      (P.powerset.filter (fun I => t-n ≤ I.card ∧ I.card ≤ t ∧\n        (∏ p ∈ I, p) ≡ 1 [MOD M])).card * P.card.choose n"]'),
(9700, 'Erdos985.erdos_985.variants.two_three_five_primitive_root', 1, 'Andyi955', 18::int, '["Set.Infinite {p : ℕ | p.Prime ∧ orderOf (2 : ZMod p) = p - 1}\n\n/-- Base `3` is a primitive root modulo infinitely many primes. -/", "Set.Infinite {p : ℕ | p.Prime ∧ orderOf (3 : ZMod p) = p - 1}\n\n/-- Base `5` is a primitive root modulo infinitely many primes. -/", "Set.Infinite {p : ℕ | p.Prime ∧ orderOf (5 : ZMod p) = p - 1}"]'),
(9715, 'Erdos207.erdos_207', 1, 'Andyi955', 28::int, '["∀ g : ℕ, 2 ≤ g → ∀ᶠ n : ℕ in Filter.atTop, n % 6 = 1 ∨ n % 6 = 3 →\n    ∃ H : Finset (Finset (Fin n)), H.IsBlockDesign 2 3\n\n/-- Spreading: for every `g >= 2` and every large `n` with `n % 6` in `{1, 3}`, any block design\non `Fin n` has the property that `j <= g` edges span at least `j + 3` vertices. -/", "∀ g : ℕ, 2 ≤ g → ∀ᶠ n : ℕ in Filter.atTop, n % 6 = 1 ∨ n % 6 = 3 →\n    ∀ H : Finset (Finset (Fin n)), H.IsBlockDesign 2 3 → ∀ E ⊆ H,\n      2 ≤ E.card → E.card ≤ g → E.card + 3 ≤ (E.biUnion id).card"]'),
(9720, 'OeisA224.conjecture.R1.H2.R1.H2', 3, 'MrSeizy', null::int, '["∀ n k : ℕ, let r := n.primeFactors.card\n    Odd n → 3 ≤ r → r ≤ 4 → n ≤ (fun b : ℕ => 64*27^r*b^(2*r))^[2*r+1] 1 →\n      4 < k → k ≤ 2*9^r → k < 2*n → ¬ IsSquare k →\n      n^2 ≠ a n*(a n-1)*k+1", "∀ n k : ℕ, let r := n.primeFactors.card\n    Odd n → 5 ≤ r → n ≤ (fun b : ℕ => 64*27^r*b^(2*r))^[2*r+1] 1 →\n      4 < k → k ≤ 2*9^r → k < 2*n → ¬ IsSquare k →\n      n^2 ≠ a n*(a n-1)*k+1"]'),
(9732, 'OeisA232616.conjecture_2', 1, 'Andyi955', 59::int, '["∀ (x y n m : ℕ), 1 < x → 1 < y → 1 < n → 1 < m → x ^ n - n = y ^ m →\n    (x = 2 ∧ n = 5 ∧ y = 3 ∧ m = 3) ∨ (x = 2 ∧ n = 7 ∧ y = 11 ∧ m = 2)\n\n/-- Backward direction: the two exceptional tuples really are solutions, i.e. they satisfy\n`x ^ n - n = y ^ m`. -/", "∀ (x y n m : ℕ), 1 < x → 1 < y → 1 < n → 1 < m →\n    ((x = 2 ∧ n = 5 ∧ y = 3 ∧ m = 3) ∨ (x = 2 ∧ n = 7 ∧ y = 11 ∧ m = 2)) →\n    x ^ n - n = y ^ m"]'),
(9737, 'Erdos936.erdos_936.variants.two_pow_sub_one', 1, 'LordMike', 48::int, '["∀ c : ℕ, 0 < c → c.Powerful → (∏ p ∈ c.primeFactors, p) ^ 2 ∣ c\n\n/-- The abc estimate with exponent 3/2 for the triples `(1, 2^n - 1, 2^n)`, written with\ninteger powers. -/", "∃ C : ℕ, ∀ n : ℕ,\n    let c := 2 ^ n - 1\n    (2 ^ n) ^ 2 ≤ C * (2 * ∏ p ∈ c.primeFactors, p) ^ 3"]'),
(9751, 'OeisA228425.conjecture_2', 1, 'Andyi955', 59::int, '["∀ k : ℕ, 3 ≤ k →\n    (∀ n : ℕ, 1 < n → ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x + y = n ∧\n      Nat.Prime (Nat.polygonalNumber k x + Nat.polygonalNumber (k + 1) y)) →\n    k = 3 ∨ k = 39 ∨ k = 99\n\n/-- Backward direction: for `k` in `{3, 39, 99}` every `n > 1` splits with\n`p_k(x) + p_{k+1}(y)` prime. -/", "∀ k : ℕ, 3 ≤ k → (k = 3 ∨ k = 39 ∨ k = 99) →\n    ∀ n : ℕ, 1 < n → ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x + y = n ∧\n      Nat.Prime (Nat.polygonalNumber k x + Nat.polygonalNumber (k + 1) y)"]'),
(9818, 'mo-342609', 1, 'ZedingZhang', 62::int, '["∀ u : ℕ, 1 < u → Odd u → IsSquare u →\n  sigma 1 u ≠ u + u.totient\n\n/-- A proper divisor leaves a specific quotient to test for being a power of two. -/", "∀ u n : ℕ, Odd u → Odd n → n ∣ u → n < u → (n = 1 ∨ IsSquare u) →\n  let U := u + u.totient\n  let N := n + n.totient\n  let D := sigma 1 u - U\n  0 < D → D ∣ U-N →\n  let q := (U-N)/D + 1\n  q ≠ 2 ^ Nat.log 2 q"]'),
(9822, 'Erdos955.erdos_955.variants.pollack_pomerance_thompson_bound.R1.H1', 1, 'sturdy4days', null::int, '["∀ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) → ∀ δ : ℝ, 0 < δ → ∀ᶠ x : ℕ in atTop,\n    let η := max (ε x) (1 / Real.log (Real.log x))\n    let window := fun n : ℕ => ∃ d ∈ n.divisors,\n      (x : ℝ) ^ ((1 / 2 : ℝ) - 10 * η) < d ∧ (d : ℝ) < (x : ℝ) ^ ((1 / 2 : ℝ) + 10 * η)\n    (((Icc 1 x).filter window).card : ℝ) ≤ δ * x\n\n/-- The small-prime, squarefull-divisor, and small-integer exceptions (a), (c), (d). -/", "∀ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) → ∀ δ : ℝ, 0 < δ → ∀ᶠ x : ℕ in atTop,\n    let η := max (ε x) (1 / Real.log (Real.log x))\n    let other := fun n : ℕ => (¬ ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ (p : ℝ) ≤ Real.log x) ∨\n      (∃ q ∈ n.divisors, (x : ℝ) ^ (2 * η) < q ∧ ∀ p : ℕ, p.Prime → p ∣ q → p ^ 2 ∣ q) ∨ n ^ 2 ≤ x\n    (((Icc 1 x).filter other).card : ℝ) ≤ δ * x\n\n/-- A uniform bound on one positive fiber after deleting the four exceptional classes.\nK bounds each individual fiber, including when the value is larger than x. -/", "∀ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) → ∀ δ : ℝ, 0 < δ → ∀ᶠ x : ℕ in atTop,\n    let η := max (ε x) (1 / Real.log (Real.log x))\n    let window := fun n : ℕ => ∃ d ∈ n.divisors,\n      (x : ℝ) ^ ((1 / 2 : ℝ) - 10 * η) < d ∧ (d : ℝ) < (x : ℝ) ^ ((1 / 2 : ℝ) + 10 * η)\n    let other := fun n : ℕ => (¬ ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ (p : ℝ) ≤ Real.log x) ∨\n      (∃ q ∈ n.divisors, (x : ℝ) ^ (2 * η) < q ∧ ∀ p : ℕ, p.Prime → p ∣ q → p ^ 2 ∣ q) ∨ n ^ 2 ≤ x\n    let good := (Icc 1 x).filter (fun n => ¬ window n ∧ ¬ other n)\n    ∃ K : ℕ, (x : ℝ) ^ ((1 / 2 : ℝ) + ε x) * K ≤ δ * x ∧\n      ∀ a : ℕ, 0 < a → (good.filter (fun n => Erdos955.s n = a)).card ≤ K"]'),
(9599, 'Erdos1160.erdos_1160.variants.sum.R3.H2.R1.H2', 2, 'Msninmx', null::int, '["∀ t : ℕ, ∃ C : ℕ, ∀ b : ℕ,\n  let X := Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''''\n    {G : FiniteGrp.{0} | Nat.card G = 2^b}\n  let U := (x : X) × (Fin t → MulAut (x.property.choose : FiniteGrp.{0}))\n  Nat.card {u : U // \n    let G : FiniteGrp.{0} := u.1.property.choose\n    let d := Nat.log 2 (frattini G).index\n    let strip := 1000*(2*b-3*d) ≤ 2*d ∧ 1000*(3*d-2*b) ≤ 2*d\n    let F := Subgroup.closure (Set.range fun x : G => x*x)\n    let K := Subgroup.closure (Set.range (fun x : F => x.val*x.val) ∪\n      Set.range (fun z : F × G => ⁅z.1.val,z.2⁆))\n    strip ∧ K=⊥}^27 * 2^(8*b^2) ≤ 2^(2*b^3+6*t*b^2+C*(b+1))", "∀ t : ℕ, ∃ C : ℕ, ∀ b : ℕ,\n  let X := Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''''\n    {G : FiniteGrp.{0} | Nat.card G = 2^b}\n  let U := (x : X) × (Fin t → MulAut (x.property.choose : FiniteGrp.{0}))\n  Nat.card {u : U // \n    let G : FiniteGrp.{0} := u.1.property.choose\n    let d := Nat.log 2 (frattini G).index\n    let strip := 1000*(2*b-3*d) ≤ 2*d ∧ 1000*(3*d-2*b) ≤ 2*d\n    let F := Subgroup.closure (Set.range fun x : G => x*x)\n    let K := Subgroup.closure (Set.range (fun x : F => x.val*x.val) ∪\n      Set.range (fun z : F × G => ⁅z.1.val,z.2⁆))\n    strip ∧ K≠⊥ ∧ 2^(192*((t+1)*1000)) * Nat.card K ≤ Nat.card F}^27 * 2^(8*b^2) ≤ 2^(2*b^3+6*t*b^2+C*(b+1))", "∀ t : ℕ, ∃ C : ℕ, ∀ b : ℕ,\n  let X := Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''''\n    {G : FiniteGrp.{0} | Nat.card G = 2^b}\n  let U := (x : X) × (Fin t → MulAut (x.property.choose : FiniteGrp.{0}))\n  Nat.card {u : U // \n    let G : FiniteGrp.{0} := u.1.property.choose\n    let d := Nat.log 2 (frattini G).index\n    let strip := 1000*(2*b-3*d) ≤ 2*d ∧ 1000*(3*d-2*b) ≤ 2*d\n    let F := Subgroup.closure (Set.range fun x : G => x*x)\n    let K := Subgroup.closure (Set.range (fun x : F => x.val*x.val) ∪\n      Set.range (fun z : F × G => ⁅z.1.val,z.2⁆))\n    ¬strip ∨ Nat.card F < 2^(192*((t+1)*1000)) * Nat.card K}^27 * 2^(8*b^2) ≤ 2^(2*b^3+6*t*b^2+C*(b+1))", "∀ᶠ m : ℕ in atTop, 2^(2*m^3) ≤ g (2^m)^27 * 2^(13*m^2)\n\n/-- An isomorphism in `FiniteGrp` gives a group isomorphism. -/"]'),
(9624, 'Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H1.R1.H2.R1.H3', 1, 'adammcarter', null::int, '["∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →\n    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 3) →\n    n.factorization 3 = 19 →\n    padicValNat 2 n % 2 = 1 →\n    262 ≤ padicValNat 2 n →\n    (∀ d, 1 ≤ d → d ≤ 400 → d ∉ ({1, 3, 4, 269, 292, 347, 353, 383} : Finset ℕ) →\n      padicValNat 2 n % (2 * d) ≠ d) →\n    (((padicValNat 2 n).primeFactors.filter (fun p => p % 3 = 2)).card ≤ 13) →\n    padicValNat 2 n ≤ A\n\n-- H2: a is bounded when a is 4 mod 8, that is 4 times an odd number, with the restrictions proved below.", "∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →\n    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 3) →\n    n.factorization 3 = 19 →\n    padicValNat 2 n % 8 = 4 →\n    262 ≤ padicValNat 2 n →\n    (∀ d, 1 ≤ d → d ≤ 400 → d ∉ ({1, 3, 4, 269, 292, 347, 353, 383} : Finset ℕ) →\n      padicValNat 2 n % (2 * d) ≠ d) →\n    padicValNat 2 n ≤ A\n\n-- H3: a is bounded when 2^20 divides a (the sieve says nothing about this class).", "∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →\n    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 3) →\n    n.factorization 3 = 19 →\n    padicValNat 2 n % 1048576 = 0 →\n    padicValNat 2 n ≤ A\n\n-- Section 1. Lucas certificates, the forced-chain lemmas, the sieve and the Fermat levels."]'),
(9691, 'Erdos723.erdos_723.variants.eq_12.R1.H1', 1, 'seanm27lol', null::int, '["∃ S : Finset (Finset (Fin 157)), S.card = 140 ∧ (∀ b ∈ S, b.card = 13) ∧\n    ∀ b ∈ S, ∀ c ∈ S, b ≠ c → ∃! x, x ∈ b ∧ x ∈ c\n\n/-- Extension on the same point set for every seed of 140, 141 or 142 lines. -/", "∀ S : Finset (Finset (Fin 157)), 140 ≤ S.card → S.card < 143 →\n    (∀ b ∈ S, b.card = 13) →\n    (∀ b ∈ S, ∀ c ∈ S, b ≠ c → ∃! x, x ∈ b ∧ x ∈ c) →\n    ∃ T : Finset (Finset (Fin 157)), S ⊆ T ∧ T.card = S.card + 1 ∧\n      (∀ b ∈ T, b.card = 13) ∧\n      ∀ b ∈ T, ∀ c ∈ T, b ≠ c → ∃! x, x ∈ b ∧ x ∈ c"]'),
(9718, 'OeisA11545.conjecture1.R1.H1.R1.H2', 1, 'physbuzz', null::int, '["∀ k : ℕ, let B := 1024*2^k\n  let x := √(π*10)\n  ∃ z : ℤ, x*(10:ℝ)^(3*B) < z+1 ∧ (z:ℝ)*(10:ℝ)^B+1 ≤ x*(10:ℝ)^(4*B)\n\n/-- A nonzero digit after position 4B and through 6B at the same anchors. -/", "∀ k : ℕ, let B := 1024*2^k\n  let x := √(π*10)\n  ∃ z : ℤ, x*(10:ℝ)^(4*B) < z+1 ∧ (z:ℝ)*(10:ℝ)^(2*B)+1 ≤ x*(10:ℝ)^(6*B)"]'),
(9725, 'IrvingLeather.irving_leather_pow_two.R1.H3', 1, 'MrSeizy', null::int, '["∀ (T : ℕ) (start duration : Fin 8 → Fin 8 → ℕ), T ≤ 64 →\n    (∀ m w, start m w + duration m w ≤ T) →\n    (∀ t < T,\n      (∀ m, ∃! w, start m w ≤ t ∧ t < start m w + duration m w) ∧\n      (∀ w, ∃! m, start m w ≤ t ∧ t < start m w + duration m w)) →\n    {a : Matching 8 | (∀ m, 0 < duration m (a m)) ∧\n      ∀ m w, 0 < duration m w → start m w < start m (a m) →\n        start m w ≤ start (a.symm w) w}.ncard ≤ 268\n\n/-- The schedule bound at the larger powers of two. -/", "∀ k : ℕ, 4 ≤ k →\n    ∀ (T : ℕ) (start duration : Fin (2 ^ k) → Fin (2 ^ k) → ℕ),\n      T ≤ (2 ^ k) * (2 ^ k) →\n      (∀ m w, start m w + duration m w ≤ T) →\n      (∀ t < T,\n        (∀ m, ∃! w, start m w ≤ t ∧ t < start m w + duration m w) ∧\n        (∀ w, ∃! m, start m w ≤ t ∧ t < start m w + duration m w)) →\n      {a : Matching (2 ^ k) | (∀ m, 0 < duration m (a m)) ∧\n        ∀ m w, 0 < duration m w → start m w < start m (a m) →\n          start m w ≤ start (a.symm w) w}.ncard ≤ IrvingLeather.irvingLeatherCount k"]'),
(9734, 'Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H1.R1.H2.R1.H2', 1, 'adammcarter', null::int, '["∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →\n    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 3) →\n    n.factorization 3 = 13 →\n    padicValNat 2 n % 2 = 1 →\n    262 ≤ padicValNat 2 n →\n    (∀ d, 1 ≤ d → d ≤ 400 → d ∉ ({1, 3, 5, 7, 8, 269, 353, 383} : Finset ℕ) →\n      padicValNat 2 n % (2 * d) ≠ d) →\n    (((padicValNat 2 n).primeFactors.filter (fun p => p % 3 = 2)).card ≤ 8) →\n    padicValNat 2 n ≤ A\n\n-- H2: a is bounded when a is 8 mod 16, that is 8 times an odd number, with the restrictions proved below.", "∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →\n    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 3) →\n    n.factorization 3 = 13 →\n    padicValNat 2 n % 16 = 8 →\n    262 ≤ padicValNat 2 n →\n    (∀ d, 1 ≤ d → d ≤ 400 → d ∉ ({1, 3, 5, 7, 8, 269, 353, 383} : Finset ℕ) →\n      padicValNat 2 n % (2 * d) ≠ d) →\n    padicValNat 2 n ≤ A\n\n-- H3: a is bounded when 2^20 divides a (the sieve says nothing about this class).", "∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →\n    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 3) →\n    n.factorization 3 = 13 →\n    padicValNat 2 n % 1048576 = 0 →\n    padicValNat 2 n ≤ A\n\n-- Section 1. Lucas certificates, the forced-chain lemmas, the sieve and the Fermat levels."]'),
(9739, 'OeisA153330.conjecture3', 1, 'mbilenko03', 59::int, '["∀ a b c d n : ℕ, 8 ≤ n → 3 ^ a * n ≤ 2 ^ b → 3 * 2 ^ b < 4 * (3 ^ a * n) →\n    3 ^ c * (n + 1) ≤ 2 ^ d → 3 * 2 ^ d < 4 * (3 ^ c * (n + 1)) →\n    ((c + d : ℤ) - (a + b) = 1 ∨ (c + d : ℤ) - (a + b) = 3 ∨ (c + d : ℤ) - (a + b) = 6 ∨\n      ∃ x y : ℕ, ((c + d : ℤ) - (a + b)).natAbs = 5 * x + 8 * y)\n\n/-- Open core: for every terminating `n ≥ 1` with `k` Collatz steps of which `U` are odd,\n`3 * 2^(k - U) < 4 * 3^U * n`, i.e. the Collatz ratio `2^E / (3^U n)` stays below `4/3`. -/", "∀ n k : ℕ, 0 < n → collatzSteps n = some k →\n    3 * 2 ^ (k - ((Finset.range k).filter (fun i => collatzStep^[i] n % 2 = 1)).card) <\n      4 * (3 ^ ((Finset.range k).filter (fun i => collatzStep^[i] n % 2 = 1)).card * n)"]'),
(9747, 'Erdos977.erdos_977.variants.factorial', 1, 'LordMike', 48::int, '["∃ C : ℕ, ∀ n : ℕ,\n    let c := n.factorial + 1\n    c ^ 2 ≤ C * (primorial n * (∏ p ∈ c.primeFactors, p)) ^ 3\n\n/-- Factorials eventually dominate every fixed geometric sequence. -/", "∀ C K : ℕ, ∀ᶠ n : ℕ in atTop, C * K ^ n < n.factorial\n\n/-- The radical of `m` is at most `4 ^ P(m)`, by the Chebyshev bound on primorials. -/"]'),
(7018, 'Erdos186.erdos_186.variants.erdos_sarkozy', 1, 'cipher-droid', 17::int, '["∀ (M : ℕ) (U : Finset ℕ), U.Nonempty → U ⊆ Icc 1 M →\n    2000000 * (1 + Real.log (2 * (U.card : ℝ))) * M ≤ (U.card : ℝ)^2 →\n    ∃ d L : ℕ, ∃ W : Finset ℕ, 0 < d ∧ 0 < L ∧ W.Nonempty ∧\n      d*L ≤ M ∧ d*U.card ≤ 4*M ∧ W.card ≤ U.card ∧ U.card ≤ 2*W.card ∧\n      W ⊆ Icc 1 L ∧ (∀ w ∈ W, d*w ∈ U) ∧\n      2000000 * (1 + Real.log (2 * (U.card : ℝ))) * L ≤ (W.card : ℝ)^2 ∧\n      ∀ r : ℕ, 1 < r → 42480*(∑ w ∈ W, w) <\n        (W.filter fun w => ¬ r ∣ w).card * W.card * W.card\n\n/-- Dense sets with no almost divisor have an interval of subset sums up to their midpoint. -/", "∀ (L : ℕ) (W : Finset ℕ), W.Nonempty → W ⊆ Icc 1 L →\n    2000000 * (1 + Real.log (2 * (W.card : ℝ))) * L ≤ (W.card : ℝ)^2 →\n    (∀ r : ℕ, 1 < r → 42480*(∑ w ∈ W, w) <\n      (W.filter fun w => ¬ r ∣ w).card * W.card * W.card) →\n    ∀ j : ℕ, 200000 * L * (∑ w ∈ W, w) ≤ j*(W.card*W.card) →\n      2*j ≤ ∑ w ∈ W, w → ∃ S ⊆ W, (∑ w ∈ S, w) = j"]')
) v(pr, t, rn, h, pts, st);
-- created_at := merge time, only for rows this transaction created (created_at = now())
update oma_reductions r set created_at = v.m from (values
(7237, '2026-11-27T18:51:09Z'::timestamptz),
(9489, '2026-11-27T18:51:11Z'::timestamptz),
(7464, '2026-11-27T18:51:25Z'::timestamptz),
(9502, '2026-11-27T18:51:40Z'::timestamptz),
(9511, '2026-11-27T18:51:55Z'::timestamptz),
(9515, '2026-11-27T18:51:59Z'::timestamptz),
(9521, '2026-11-27T18:52:07Z'::timestamptz),
(9538, '2026-11-27T18:52:56Z'::timestamptz),
(9552, '2026-11-27T18:53:03Z'::timestamptz),
(8931, '2026-11-27T18:53:50Z'::timestamptz),
(9477, '2026-11-27T18:54:04Z'::timestamptz),
(8606, '2026-11-27T18:54:13Z'::timestamptz),
(9571, '2026-11-27T18:54:22Z'::timestamptz),
(9582, '2026-11-27T18:54:43Z'::timestamptz),
(9578, '2026-11-27T18:54:55Z'::timestamptz),
(9587, '2026-11-27T18:55:03Z'::timestamptz),
(9588, '2026-11-27T18:55:11Z'::timestamptz),
(9581, '2026-11-27T18:55:13Z'::timestamptz),
(9593, '2026-11-27T18:55:38Z'::timestamptz),
(9606, '2026-11-27T18:56:16Z'::timestamptz),
(9612, '2026-11-27T18:56:46Z'::timestamptz),
(9613, '2026-11-27T18:56:59Z'::timestamptz),
(9621, '2026-11-27T18:57:26Z'::timestamptz),
(9622, '2026-11-27T18:57:35Z'::timestamptz),
(9630, '2026-11-27T18:58:04Z'::timestamptz),
(9643, '2026-11-27T18:58:47Z'::timestamptz),
(9641, '2026-11-27T18:59:04Z'::timestamptz),
(9649, '2026-11-27T18:59:16Z'::timestamptz),
(9659, '2026-11-27T18:59:49Z'::timestamptz),
(9679, '2026-11-27T19:00:32Z'::timestamptz),
(9684, '2026-11-27T19:00:47Z'::timestamptz),
(9698, '2026-11-27T19:01:30Z'::timestamptz),
(9696, '2026-11-27T19:01:34Z'::timestamptz),
(9700, '2026-11-27T19:01:39Z'::timestamptz),
(9715, '2026-11-27T19:02:28Z'::timestamptz),
(9720, '2026-11-27T19:02:41Z'::timestamptz),
(9732, '2026-11-27T19:03:02Z'::timestamptz),
(9737, '2026-11-27T19:03:23Z'::timestamptz),
(9751, '2026-11-27T19:04:07Z'::timestamptz),
(9818, '2026-11-27T19:06:23Z'::timestamptz),
(9822, '2026-11-27T19:06:33Z'::timestamptz),
(9599, '2026-11-27T19:11:48Z'::timestamptz),
(9624, '2026-11-27T19:11:52Z'::timestamptz),
(9691, '2026-11-27T19:12:32Z'::timestamptz),
(9718, '2026-11-27T19:14:20Z'::timestamptz),
(9725, '2026-11-27T19:14:24Z'::timestamptz),
(9734, '2026-11-27T19:14:32Z'::timestamptz),
(9739, '2026-11-27T19:14:34Z'::timestamptz),
(9747, '2026-11-27T19:16:12Z'::timestamptz),
(7018, '2026-11-27T19:47:58Z'::timestamptz)
) v(pr, m) where r.pr_url = 'https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/' || v.pr and r.created_at = now();
update oma_steps s set created_at = r.created_at from oma_reductions r where s.reduction = r.id and s.created_at = now();
update oma_events e set created_at = r.created_at from oma_reductions r
  where e.kind = 'reduced' and e.created_at = now() and e.problem_id = r.problem_id and e.detail = r.id || ' into ' || r.hyps || ' steps';
commit;

-- ===== batch 3: reductions, dependency level 0 (4 PRs: 7039 .. ) =====
begin;
select v.pr, case
  when exists (select 1 from oma_reductions r where r.pr_url = 'https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/' || v.pr) then json_build_object('skip','pr_exists')
  when exists (select 1 from oma_reductions r where r.id = v.t || '.R' || v.rn) then json_build_object('skip','id_exists')
  when v.pts is null and not exists (select 1 from oma_steps s where s.id = v.t) then json_build_object('error','unknown_target')
  else oma_register_reduction(v.t || '.R' || v.rn, v.t, v.h, 'https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/' || v.pr,
         'OMAReductions.R_' || regexp_replace(v.t || '.R' || v.rn, '[^A-Za-z0-9]', '_', 'g'), v.st::json,
         coalesce(v.pts, (select s.points from oma_steps s where s.id = v.t))) end r
from (values
(7039, 'Erdos687.erdos_687.variants.maier_pomerance.R2.H1', 1, 'JamesSlash', null::int, '["∃ c : ℝ, 0 < c ∧ ∃ z₀ : ℝ, ∀ z : ℝ, z₀ ≤ z → ∀ a : ℕ → ℕ,\n    let L := Real.log z\n    let Y := ⌊z ^ 2 / L ^ 2⌋₊\n    let w := L / Real.log L ^ 2\n    let B := L / Real.log w\n    let V₀ := ∏ p ∈ (Finset.range (⌊w⌋₊ + 1)).filter Nat.Prime, (1 - (p : ℝ)⁻¹)\n    c * (Y : ℝ) * V₀ / B ^ 2 ≤\n      (((Finset.Icc 1 Y).filter fun n => ∀ p ≤ ⌊z⌋₊, p.Prime → ¬ (n ≡ a p [MOD p])).card : ℝ)\n\n/-- Mertens'' third theorem lower bound (Mertens 1874): there is `c₀ > 0` with\n`c₀ / log x ≤ ∏_{p ≤ x} (1 - 1/p)` for all `x ≥ 2`. -/", "∃ c₀ : ℝ, 0 < c₀ ∧ ∀ x : ℕ, 2 ≤ x →\n    c₀ / Real.log (x : ℝ) ≤\n      ∏ p ∈ (Finset.range (x + 1)).filter Nat.Prime, (1 - (p : ℝ)⁻¹)\n\n/-- Chebyshev''s bound `π(x) ≤ 8x / log x` (copied from the merged reduction\n`Erdos687.erdos_687.variants.iwaniec.R1` by @ItsNotTheGabs). -/"]'),
(7329, 'Erdos64.erdos_64.R1.H1.R1.H1.R1.H1', 1, 'ubuwaits', null::int, '["∀ (V : Type) (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj],\n  G.Connected → (∀ x, G.degree x = 3) →\n  (∀ ⦃a b⦄, G.Adj a b → ¬ G.IsBridge s(a,b)) → ¬ G.IsBipartite →\n  (¬ ∃ color : V → Fin 4, (∀ ⦃x y⦄, G.Adj x y → color x ≠ color y) ∧\n    ∀ x j, j ≠ color x → ∃! y, G.Adj x y ∧ color y = j) →\n  ∃ (k : ℕ) (v : V) (c : G.Walk v v), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2 ^ k\n\n/-- Composite degree outside the power-of-two solvable case, without a signed\naffine orbit or an affine orbit with bijective nonidentity differences. -/", "∀ (X : Type) [Fintype X] [Nonempty X] (p q r : Equiv.Perm X),\n  ¬ (Fintype.card X).Prime →\n  ¬ ((∃ s : ℕ, Fintype.card X = 2^s) ∧ Group.IsSolvable (Subgroup.closure ({p,q,r} : Set (Equiv.Perm X)))) →\n  (¬ ∃ (A : Type) (_ : AddCommGroup A) (f : A ↪ X) (s t u : Bool) (a b c : A),\n    ∀ x, p (f x) = f ((if s then -x else x)+a) ∧ q (f x) = f ((if t then -x else x)+b) ∧\n      r (f x) = f ((if u then -x else x)+c)) →\n  ¬ (∃ (A S : Type) (_ : AddCommGroup A) (_ : Group S) (_ : DistribMulAction S A)\n    (f : A ↪ X) (P Q R : S) (a b c : A), (∀ g : S, g ≠ 1 → Function.Bijective (fun x : A => x - g • x)) ∧\n    ∀ x, p (f x) = f (P • x+a) ∧ q (f x) = f (Q • x+b) ∧ r (f x) = f (R • x+c)) →\n  let K := SimpleGraph.fromRel (fun u v : Fin 4 × X =>\n    (u.1 = 0 ∧ v.1 ≠ 0 ∧ v.2 = u.2) ∨\n    (u.1 = 1 ∧ v.1 = 2 ∧ v.2 = p u.2) ∨\n    (u.1 = 2 ∧ v.1 = 3 ∧ v.2 = q u.2) ∨\n    (u.1 = 3 ∧ v.1 = 1 ∧ v.2 = r u.2))\n  K.Connected → ¬ K.IsBipartite → ∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2^k) ⊑ K\n\n/-- A prime number of sheets with nonsolvable monodromy. -/", "∀ (X : Type) [Fintype X] [Nonempty X] (p q r : Equiv.Perm X),\n  (Fintype.card X).Prime → ¬ Group.IsSolvable (Subgroup.closure ({p,q,r} : Set (Equiv.Perm X))) →\n  let K := SimpleGraph.fromRel (fun u v : Fin 4 × X =>\n    (u.1 = 0 ∧ v.1 ≠ 0 ∧ v.2 = u.2) ∨\n    (u.1 = 1 ∧ v.1 = 2 ∧ v.2 = p u.2) ∨\n    (u.1 = 2 ∧ v.1 = 3 ∧ v.2 = q u.2) ∨\n    (u.1 = 3 ∧ v.1 = 1 ∧ v.2 = r u.2))\n  K.Connected → ¬ K.IsBipartite → ∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2^k) ⊑ K\n\n/-- The two residual permutation cases imply the unclassified tetrahedral case. -/"]'),
(7387, 'Erdos687.erdos_687.variants.fgkmt', 1, 'JamesSlash', 34::int, '["∃ c : ℝ, 0 < c ∧ ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ᶠ x : ℕ in atTop, ∃ a b : ℕ → ℕ,\n    let y := c * x * Real.log x * Real.log (Real.log (Real.log x)) / Real.log (Real.log x)\n    let z := (x : ℝ) ^ (Real.log (Real.log (Real.log x)) / (4 * Real.log (Real.log x)))\n    (((Finset.Ioc x ⌊y⌋₊).filter fun q => q.Prime ∧\n        (∀ s ≤ ⌊z⌋₊, s.Prime → Real.log x ^ 20 < s → ¬ (q ≡ a s [MOD s])) ∧\n        (∀ p ≤ x, p.Prime → (x : ℝ) / 2 < p → ¬ (q ≡ b p [MOD p]))).card : ℝ) ≤\n      C₁ * x / Real.log x\n\n/-- The smooth-number count used in §3 of [FGKMT18] (de Bruijn''s theorem): for all large `x`, at\nmost `x / log x` integers of `[1, x log x]` have all their prime factors at most\n`z = x ^ (log₃ x / (4 log₂ x))`. -/", "∀ᶠ x : ℕ in atTop,\n    (((Finset.Icc 1 ⌊(x : ℝ) * Real.log x⌋₊).filter fun n : ℕ => ∀ p : ℕ, p ≤ n → p.Prime → p ∣ n →\n        (p : ℝ) ≤ (x : ℝ) ^ (Real.log (Real.log (Real.log x)) / (4 * Real.log (Real.log x)))).card\n      : ℝ) ≤ x / Real.log x\n\n/-- Chebyshev''s estimate: for every `A` there is `C` such that `(x, C x]` contains at least\n`A x / log x` primes for all large `x`. -/", "∀ A : ℝ, ∃ C : ℕ, ∀ᶠ x : ℕ in atTop,\n    A * x / Real.log x ≤ (((Finset.Ioc x (C * x)).filter Nat.Prime).card : ℝ)\n\n/-- Give each survivor of the sieve by the primes up to `x` its own prime of `(x, X]`\n(adapted from `cover_of_packing_budget` in the merged reduction\n`Erdos687.erdos_687.variants.maier_pomerance.R2` by @NicholasWierenga). -/"]'),
(9211, 'Erdos52.erdos_52', 3, 'GiridhariPradeep', 102::int, '["∀ ε : ℝ, 0 < ε → ε < 1 → ∃ C : ℝ, 0 < C ∧ ∀ A : Finset ℤ,\n  (∀ a ∈ A, 0 < a) → (max (A + A).card (A * A).card : ℝ) ≥ C * (A.card : ℝ) ^ (2 - ε)\n\n/-- The sum-product conjecture for finite sets of negative integers. -/", "∀ ε : ℝ, 0 < ε → ε < 1 → ∃ C : ℝ, 0 < C ∧ ∀ A : Finset ℤ,\n  (∀ a ∈ A, a < 0) → (max (A + A).card (A * A).card : ℝ) ≥ C * (A.card : ℝ) ^ (2 - ε)"]')
) v(pr, t, rn, h, pts, st);
-- created_at := merge time, only for rows this transaction created (created_at = now())
update oma_reductions r set created_at = v.m from (values
(7039, '2026-11-27T19:48:18Z'::timestamptz),
(7329, '2026-11-27T19:48:25Z'::timestamptz),
(7387, '2026-11-27T19:48:32Z'::timestamptz),
(9211, '2026-11-27T19:53:06Z'::timestamptz)
) v(pr, m) where r.pr_url = 'https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/' || v.pr and r.created_at = now();
update oma_steps s set created_at = r.created_at from oma_reductions r where s.reduction = r.id and s.created_at = now();
update oma_events e set created_at = r.created_at from oma_reductions r
  where e.kind = 'reduced' and e.created_at = now() and e.problem_id = r.problem_id and e.detail = r.id || ' into ' || r.hyps || ' steps';
commit;

-- ===== batch 4: reductions, dependency level 1 (23 PRs: 4425 .. ) =====
begin;
select v.pr, case
  when exists (select 1 from oma_reductions r where r.pr_url = 'https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/' || v.pr) then json_build_object('skip','pr_exists')
  when exists (select 1 from oma_reductions r where r.id = v.t || '.R' || v.rn) then json_build_object('skip','id_exists')
  when v.pts is null and not exists (select 1 from oma_steps s where s.id = v.t) then json_build_object('error','unknown_target')
  else oma_register_reduction(v.t || '.R' || v.rn, v.t, v.h, 'https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/' || v.pr,
         'OMAReductions.R_' || regexp_replace(v.t || '.R' || v.rn, '[^A-Za-z0-9]', '_', 'g'), v.st::json,
         coalesce(v.pts, (select s.points from oma_steps s where s.id = v.t))) end r
from (values
(4425, 'Erdos436.erdos_436.variants.five_two.R1.H2.R1.H2.R1.H1', 1, 'marcusbuffett', null::int, '["∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] (B : ℕ),\n    ∃ p > B, p.Prime ∧ Nat.card (𝓞 K →+* ZMod p) < 2*Nat.card (𝓞 E →+* ZMod p)\n\n/-- Away from a finite index, an order and the maximal order in its fraction\nfield have the same reductions to prime fields. -/", "∀ (L : Type) [Field L] [NumberField L] (R : Subalgebra ℤ (𝓞 L)),\n    ∃ (E : Type) (_ : Field E) (_ : NumberField E) (B : ℕ), ∀ p > B, p.Prime →\n      Nonempty ((R →+* ZMod p) ≃ (𝓞 E →+* ZMod p))"]'),
(4466, 'Erdos950.erdos_950.variants.debruijn_erdos_turan.R1.H2', 1, 'marcusbuffett', null::int, '["∃ K : ℝ, 0 < K ∧ ∀ N p j : ℕ,\n    let P := (range N).filter Nat.Prime\n    ∑ q ∈ (P.erase p).filter (fun q => Nat.log 2 (Nat.dist p q) = j),\n      (harmonic (Nat.dist p q) : ℝ) / Nat.dist p q ≤ K", "∀ k : ℕ, 0 < k → ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,\n    let P := (range N).filter Nat.Prime\n    ∑ p ∈ P, ∑ q ∈ (P.erase p).filter (fun q => Nat.log 2 N / k ≤ Nat.log 2 (Nat.dist p q)),\n      (1 + log (Nat.dist p q)) / Nat.dist p q ≤ (1+ε)*N"]'),
(4495, 'Erdos930.erdos_930.variants.consecutive_integers.R1.H4.R1.H2', 1, 'marcusbuffett', null::int, '["∀ k : ℕ, 60184 ≤ k →\n  (k.primeCounting : ℝ) * (Real.log k - 11/10) ≤ k\n\n/-- The finite range below Dusart''s threshold. -/", "∀ k : ℕ, 30000 ≤ k → k < 60184 →\n  (k.primesBelow.card : ℝ) * (Real.log k - 6/5) ≤ k"]'),
(4504, 'Erdos299.erdos_299.variants.density.R1.H1.R1.H2.R1.H3', 1, 'marcusbuffett', null::int, '["let w (N : ℕ) := log (log N)\n  let e (N : ℕ) := (log N)^(-(1/100:ℝ))\n  let M (N : ℕ) := (N:ℝ)^(1-1/w N)\n  let K (N : ℕ) := M N*(N:ℝ)^(-2/w N)\n  let mass (A : Finset ℕ) := ∑ n ∈ A, (1:ℝ)/n\n  let part (A : Finset ℕ) (q : ℕ) := A.filter fun n => q∣n ∧ Nat.Coprime q (n/q)\n  let Regular (N n : ℕ) : Prop := M N ≤ n ∧\n    (∀ q : ℕ, IsPrimePow q → q∣n → (q:ℝ) ≤ (N:ℝ)^(1-8/w N)) ∧\n    (99/100:ℝ)*w N ≤ n.primeFactors.card ∧ (n.primeFactors.card:ℝ) ≤ 2*w N\n  ∀ᶠ N : ℕ in atTop, ∀ (A : Finset ℕ) (q : ℕ), 0∉A → A⊆range N →\n  (∀ n ∈ A, Regular N n) → IsPrimePow q → e N/2 ≤ ∑ n ∈ part A q,(q:ℝ)/n →\n  ∃ (D : ℕ) (C : Finset ℕ), K N < D ∧ q∣D ∧\n    (log N)^(-(1/99:ℝ)) ≤ mass C ∧\n    (∀ m ∈ C, D*m ∈ A ∧ Nat.Coprime m D ∧\n      (1-2/99:ℝ)*w N ≤ m.primeFactors.card ∧ (m.primeFactors.card:ℝ) ≤ 2*w N)\n\n/-- A family of cofactors of sufficient mass and with almost the normal\nnumber of distinct prime factors has large prime-power reciprocal mass. -/", "let w (N : ℕ) := log (log N)\n  let mass (A : Finset ℕ) := ∑ n ∈ A, (1:ℝ)/n\n  let powers (A : Finset ℕ) := A.biUnion fun n =>\n    n.divisors.filter fun q => IsPrimePow q ∧ Nat.Coprime q (n/q)\n  ∀ᶠ N : ℕ in atTop, ∀ C : Finset ℕ,\n  (log N)^(-(1/99:ℝ)) ≤ mass C →\n  (∀ m ∈ C, (1-2/99:ℝ)*w N ≤ m.primeFactors.card ∧ (m.primeFactors.card:ℝ) ≤ 2*w N) →\n  (35/100:ℝ)*w N ≤ mass (powers C)"]'),
(4509, 'BusyBeaver.BB_4.R1.H2.R1.H2.R1.H3', 1, 'marcusbuffett', null::int, '["∀ (M : Machine (Fin 2) (Fin 4))\n    (a : Fin 2) (q : Fin 4), q.val ≤ 2 →\n    M 0 0 = some (some 1, Stmt.write 1 Dir.right) →\n    M 1 0 = some (some q, Stmt.write a Dir.left) →\n    M.IsHalting → M.HaltsAfter (Machine.init []) 107", "∀ (M : Machine (Fin 2) (Fin 4))\n    (a b : Fin 2) (q : Fin 4),\n    M 0 0 = some (some 1, Stmt.write 1 Dir.right) →\n    M 1 0 = some (some 2, Stmt.write a Dir.right) →\n    M 2 0 = some (some q, Stmt.write b Dir.left) →\n    M.IsHalting → M.HaltsAfter (Machine.init []) 107", "∀ (M : Machine (Fin 2) (Fin 4))\n    (a b c : Fin 2) (q : Fin 4),\n    M 0 0 = some (some 1, Stmt.write 1 Dir.right) →\n    M 1 0 = some (some 2, Stmt.write a Dir.right) →\n    M 2 0 = some (some 3, Stmt.write b Dir.right) →\n    M 3 0 = some (some q, Stmt.write c Dir.left) →\n    M.IsHalting → M.HaltsAfter (Machine.init []) 107"]'),
(4511, 'Erdos710.erdos_710.variants.lower_bound.R1.H1', 1, 'marcusbuffett', null::int, '["∀ ξ : ℝ, 0 < ξ → ξ < 1 → ∀ᶠ y : ℕ in atTop, ∃ m : ℕ, 0 < m ∧\n  (1-ξ)*y*log y/4 ≤ log m ∧ log m ≤ (1+ξ)*y*log y/4 ∧\n  ∀ z : ℕ, m/y ≤ z → z ≤ m*y →\n    ((Nat.smoothNumbersUpTo z y).card : ℝ) ≤\n      (Nat.smoothNumbersUpTo m y).card * ((z:ℝ)/m)^(4/(log y)^2 : ℝ)\n\n/-- Choice of smoothness scale and integer endpoint with room for rounding. -/", "∀ η : ℝ, 0 < η → η < 1 → ∃ ξ h : ℝ, 0 < ξ ∧ ξ < 1 ∧ 0 < h ∧\n  ∀ Y : ℕ, ∀ᶠ n : ℕ in atTop, ∃ y : ℕ, Y ≤ y ∧ 2 ≤ y ∧\n    ∀ m : ℕ, 0 < m → (1-ξ)*y*log y/4 ≤ log m → log m ≤ (1+ξ)*y*log y/4 →\n      (m:ℝ) ≤ η*n ∧ ∃ B : ℕ, m ≤ B ∧ B ≤ m*y ∧\n        (1-η)*(2/√(exp 1))*m*√(log n/log (log n)) ≤ B ∧\n        (B:ℝ)/m ≤ exp (log y/2-(1/2+h))"]'),
(4513, 'Arxiv.1601.03081.crystals_components_unique.R1.H1', 1, 'senamakel', null::int, '["∀ a c : ℕ, a.Coprime c → a ≤ c * 3 → c ≤ a * 3 →\n    IsCrystalWithComponents (a * (c * 3)) a (c * 3) →\n    IsCrystalWithComponents (a * (c * 3)) c (a * 3) →\n    (a + c * 3)^2 / ((a + 1) * (c * 3 + 1)) =\n      (c + a * 3)^2 / ((c + 1) * (a * 3 + 1))", "∀ a c m : ℕ, 5 ≤ m → Odd m → a.Coprime c → a ≤ c * m → c ≤ a * m →\n    IsCrystalWithComponents (a * (c * m)) a (c * m) →\n    IsCrystalWithComponents (a * (c * m)) c (a * m) →\n    (a + c * m)^2 / ((a + 1) * (c * m + 1)) =\n      (c + a * m)^2 / ((c + 1) * (a * m + 1))"]'),
(4528, 'Erdos768.erdos_768.R1.H1', 1, 'senamakel', null::int, '["∃ c > 0, (Chebyshev.psi - id) =O[atTop] fun x : ℝ => x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10))", "(∃ c > 0, (Chebyshev.psi - id) =O[atTop] fun x : ℝ => x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10))) →\n  ∀ u δ : ℕ → ℝ, Tendsto u atTop atTop → (∀ᶠ n in atTop, (u n)⁻¹ ^ 2 ≤ δ n ∧ δ n ≤ 1) →\n    Tendsto (fun n : ℕ => (((Finset.Icc 1 ⌊Real.exp (u n)⌋₊).filter (fun p => Nat.Prime p ∧ Real.exp (u n - δ n) < (p : ℝ))).card : ℝ) / ((1 - Real.exp (-(δ n))) * Real.exp (u n) / (u n))) atTop (nhds 1)"]'),
(4531, 'Erdos297.erdos_297.variants.general.R1.H3.R1.H2', 1, 'marcusbuffett', null::int, '["∀ (x d : ℚ), 0 < x → 0 < d → ∀ δ > (0:ℝ),\n  ∃ K : ℕ, 0 < K ∧ ∀ᶠ N : ℕ in atTop,\n    ∃ U ⊆ Icc 1 N, (((Icc 1 N) \\ U).card:ℝ) ≤ δ*N ∧ (∀ u ∈ U, ¬ K ∣ u) ∧\n      ∀ A ⊆ U, (∑ n ∈ A, (1:ℚ)/n) ≤ x-d → ∃ P ⊆ Icc 1 N,\n        Disjoint P U ∧ (∀ p ∈ P, ¬ K ∣ p) ∧\n        ∃ j : ℕ, 0 < j ∧ (j:ℚ)/K = x-(∑ n ∈ A, (1:ℚ)/n)-(∑ n ∈ P, (1:ℚ)/n)\n\n/-- Each positive integer has a finite representation by distinct unit fractions. -/", "∀ j : ℕ, 0 < j → ∃ S : Finset ℕ, (∀ n ∈ S, 0 < n) ∧\n  (∑ n ∈ S, (1:ℚ)/n) = j"]'),
(4563, 'Erdos308.erdos_308.variants.croot.R1.H2', 1, 'marcusbuffett', null::int, '["∀ a : ℝ, 0 < a → a < 2 →\n  Tendsto (fun N : ℕ => (∑ p ∈ (Nat.primesLE N).filter (fun p : ℕ => (N:ℝ)<p*(log N)^a),\n    (harmonic (N/p):ℝ)/p) * log N / (log (log N))^2) atTop (𝓝 (a^2/2))\n\n/-- Elementary factorial thresholds on either side of the exponent one. -/", "∀ a b : ℝ, 0 < a → a < 1 → 1 < b → b < 2 → ∀ᶠ N : ℕ in atTop,\n  ∀ p ∈ Nat.primesLE N,\n    ((N:ℝ)<p*(log N)^a → (N/p)*(N/p).factorial < p) ∧\n    ((N/p)*(N/p).factorial < p → (N:ℝ)<p*(log N)^b)"]'),
(4613, 'BusyBeaver.BB_4.R1.H2.R1.H1.R1.H3', 1, 'pageman', null::int, '["∀ (M : Machine (Fin 2) (Fin 4)),\n    M 0 0 = some (some 1, Stmt.write 0 Dir.right) →\n    (∀ q a, ∃ q'' z, M q a = some (some q'', z)) →\n    ¬ M.IsHalting", "∀ M : Machine (Fin 2) (Fin 4),\n    M 0 0 = some (some 1, Stmt.write 0 Dir.right) →\n    (∃ q t, M.multiStep (Machine.init []) 107 = some ⟨some q, t⟩) →\n    (∀ q a, (∃ i < 107, ∃ t : Tape (Fin 2),\n      M.multiStep (Machine.init []) i = some ⟨some q, t⟩ ∧ t.head = a) ↔\n      ∃ q'' z, M q a = some (some q'', z)) →\n    (∀ q a, M q a = none ∨ ∃ q'' z, M q a = some (some q'', z)) →\n    (∃ q a, M q a = none) →\n    (∀ (i p : ℕ) (q : Fin 4) (a : Fin 2) (side : Bool)\n        (near : List (Fin 2)) (fixed : ListBlank (Fin 2)), 0 < p → i + p ≤ 107 →\n      let cfg := fun tail : ListBlank (Fin 2) =>\n        let free := near.foldr ListBlank.cons tail\n        (⟨some q, if side then ⟨a, free, fixed⟩ else ⟨a, fixed, free⟩⟩ : Cfg (Fin 2) (Fin 4))\n      (∃ tail, M.multiStep (Machine.init []) i = some (cfg tail)) →\n      ¬ ∀ tail, ∃ tail'', M.multiStep (cfg tail) p = some (cfg tail'')) →\n    ¬ M.IsHalting"]'),
(4696, 'Erdos983.erdos_983.variants.erdos_straus.R1.H2.R1.H1', 1, 'marcusbuffett', null::int, '["∀ A : ℝ, 0<A →\n  (fun x : ℝ => Chebyshev.theta x - x) =o[atTop] fun x : ℝ => x/(log x)^A\n\n/-- Integration against the Abel kernel preserves arbitrary logarithmic savings. -/", "∀ f : ℝ → ℝ,\n  (∀ x ≥ (3:ℝ), IntervalIntegrable (fun t => f t / (t*(log t)^2)) volume 3 x) →\n  (∀ B : ℝ, 0<B → f =o[atTop] fun x : ℝ => x/(log x)^B) →\n  ∀ C A : ℝ, 0<A → (fun x : ℝ => C + ∫ t in (3:ℝ)..x, f t/(t*(log t)^2))\n    =o[atTop] fun x : ℝ => x/(log x)^A"]'),
(4790, 'Erdos258.erdos_258.variants.monotone.R2.H2', 1, 'marcusbuffett', null::int, '["∀ q : ℕ, 0 < q → ∀ᶠ X : ℕ in atTop, ∃ N : ℕ, X ≤ N ∧\n  let L := (log X)^(7/8:ℝ)\n  let G := ∑'' k : ℕ, ((k+(N+1)+1).divisors.card:ℝ)/(2:ℝ)^k\n  (q:ℝ)*((N+1).divisors.card+G/L) < L\n\n/-- A congruence window in a long integer interval. Each initial divisor\ndigit is divisible by the appropriate power of the prescribed base. -/", "∀ q : ℕ, 0 < q → ∀ᶠ X : ℕ in atTop, ∀ t : ℕ, 2 ≤ t →\n  (t:ℝ) ≤ (log X)^(7/8:ℝ) → ∀ I : Finset ℕ, I ⊆ Icc 1 X →\n  (∀ x ∈ I, ∀ y ∈ I, Icc x y ⊆ I) → X/⌊(log X)^(7/8:ℝ)⌋₊ ≤ I.card →\n  ∃ N k : ℕ, Icc (N+1) (N+k) ⊆ I ∧ (∀ j ∈ Icc 1 k, t^j ∣ (N+j).divisors.card) ∧\n    (q:ℝ)*(∑'' i : ℕ, ((i+(N+k)+1).divisors.card:ℝ)/(2:ℝ)^i) < (t:ℝ)^k"]'),
(4633, 'Arxiv.1601.03081.crystals_components_unique.R1.H2', 1, 'senamakel', null::int, '["∀ a b c d : ℕ, 0 < a → 0 < c → a * b = c * d → ¬ Nat.Coprime a c →\n    ∃ g x y z : ℕ, 1 < g ∧ a = g * x ∧ c = g * y ∧ b = y * z ∧ d = x * z ∧\n      Nat.Coprime x y", "∀ g x y z : ℕ, 1 < g → 0 < x → 0 < y → 0 < z → x ≠ y →\n    g * x ≤ y * z → g * y ≤ x * z → Nat.Coprime x y →\n    (g * x + 1) * (y * z + 1) ∣ (g * x + y * z) ^ 2 →\n    (g * y + 1) * (x * z + 1) ∣ (g * y + x * z) ^ 2 →\n      g = z"]'),
(4799, 'Erdos848.erdos_848.R1.H2', 1, 'marcusbuffett', null::int, '["open scoped Classical in\n  ∀ N : ℕ, 5000000 < N → N < 160000000 → ∀ W : Finset ℕ,\n    let key := fun x : ℕ => (if x % 25 = 7 then 4 else if x % 25 = 18 then 8 else 0) + x % 4\n    W ⊆ Icc 1 N → W.card ≤ 12 → Set.InjOn key (W : Set ℕ) →\n    (∀ u ∈ W, ∀ v ∈ W, ¬ Squarefree (u*v+1)) →\n    (∃ u ∈ W, u % 25 ≠ 7) → (∃ v ∈ W, v % 25 ≠ 18) →\n    ((Icc 1 N).filter fun x =>\n      ¬ Squarefree (x*x+1) ∧ (∀ w ∈ W, ¬ Squarefree (x*w+1)) ∧\n      ∃ w ∈ W, key w = key x ∧ w ≤ x).card ≤ ((Icc 1 N).filter fun x => x % 25 = 7).card", "open scoped Classical in\n  ∀ N : ℕ, 160000000 ≤ N → ∀ W : Finset ℕ,\n    let key := fun x : ℕ => (if x % 25 = 7 then 4 else if x % 25 = 18 then 8 else 0) + x % 4\n    W ⊆ Icc 1 N → W.card ≤ 12 → Set.InjOn key (W : Set ℕ) →\n    (∀ u ∈ W, ∀ v ∈ W, ¬ Squarefree (u*v+1)) →\n    (∃ u ∈ W, u % 25 ≠ 7) → (∃ v ∈ W, v % 25 ≠ 18) →\n    ((Icc 1 N).filter fun x =>\n      ¬ Squarefree (x*x+1) ∧ (∀ w ∈ W, ¬ Squarefree (x*w+1)) ∧\n      ∃ w ∈ W, key w = key x ∧ w ≤ x).card ≤ ((Icc 1 N).filter fun x => x % 25 = 7).card"]'),
(4826, 'Erdos173.erdos_173.R1.H2.R1.H2.R1.H1', 1, 'lucasfreund2-cmd', null::int, '["let ζ : ℂ := ⟨1 / 2, √3 / 2⟩\n  let avoids (c : ℂ → Fin 2) (r : ℝ) := ∀ p u : ℂ, ‖u‖ = 1 →\n    ¬ (c (p + u * r) = c p ∧ c (p + u * (r * ζ)) = c p)\n  ∀ x : ℝ, 2 / 3 < x → x < 3 / 2 → x ≠ 1 → ∀ c : ℂ → Fin 2,\n    avoids c 1 → avoids c x →\n    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (ν : Measure Ω), IsProbabilityMeasure ν ∧\n      ∃ f : ℂ → Lp ℂ 2 ν, Continuous f ∧\n        (∀ p : ℂ, ∀ᵐ ω ∂ν,\n          (f p ω).im = 0 ∧ -1 ≤ (f p ω).re ∧ (f p ω).re ≤ 1) ∧\n        ∀ r : ℝ, (r = 1 ∨ r = x) → ∀ p : ℂ, ∀ u : Circle,\n          (1 + inner ℂ (f p) (f (p + u * r)) +\n            inner ℂ (f p) (f (p + u * (r * ζ))) +\n            inner ℂ (f (p + u * r)) (f (p + u * (r * ζ)))).re = 0\n\n/-- A zero quadratic moment of three bounded real L² vectors gives a pointwise identity. -/", "∀ (Ω : Type) [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]\n    (A B C : Lp ℂ 2 ν),\n    (∀ᵐ ω ∂ν, (A ω).im = 0 ∧ -1 ≤ (A ω).re ∧ (A ω).re ≤ 1) →\n    (∀ᵐ ω ∂ν, (B ω).im = 0 ∧ -1 ≤ (B ω).re ∧ (B ω).re ≤ 1) →\n    (∀ᵐ ω ∂ν, (C ω).im = 0 ∧ -1 ≤ (C ω).re ∧ (C ω).re ≤ 1) →\n    (1 + inner ℂ A B + inner ℂ A C + inner ℂ B C).re = 0 →\n    ∀ᵐ ω ∂ν,\n      1 + (A ω).re * (B ω).re + (A ω).re * (C ω).re + (B ω).re * (C ω).re = 0"]'),
(5045, 'Erdos50.erdos_50_singular.R1.H2', 1, 'marcusbuffett', null::int, '["let cnt := fun (S : Set ℕ) (b : ℕ) => ((Finset.range b).filter (· ∈ S)).card\n  let ratio := fun (n : ℕ) => (n.totient : ℝ) / n\n  ∀ f : ℝ → ℝ, Erdos50.IsDistributionOfPhiRatio f →\n    ContinuousOn f (Icc 0 1) → ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧\n    EqOn f (cdf μ) (Icc 0 1) ∧ ∀ C : Set ℝ, IsClosed C → ∀ a : ℝ,\n    (∀ᶠ N : ℕ in atTop, a*N ≤ (cnt (ratio ⁻¹'' C) N : ℝ)) → ENNReal.ofReal a ≤ μ C\n\n/-- Almost every integer has an isolated initial segment of its prime factors\nat some bounded scale above any prescribed threshold. This is a finite\ndivisibility-pattern question to which the Chinese remainder theorem applies. -/", "let cnt := fun (S : Set ℕ) (b : ℕ) => ((Finset.range b).filter (· ∈ S)).card\n  let status := fun (Q : Finset ℕ) (n : ℕ) => Q.filter (· ∣ n)\n  let QK := fun (K : ℕ) => (Finset.range (K + 1)).filter Nat.Prime\n  let isolated := fun (d n : ℕ) => n ≠ 0 ∧ status (QK (d^4)) n = d.primeFactors\n  ∀ K : ℕ, ∀ ε : ℝ, 0 < ε → ∃ D : ℕ, ∀ᶠ N : ℕ in atTop,\n    (1-ε)*N ≤ (cnt {n | ∃ d ∈ Finset.Ioc K D, isolated d n} N : ℝ)"]'),
(5059, 'RiemannHypothesis.robin_criterion.R1.H1.R1.H2', 1, 'marcusbuffett', null::int, '["RiemannHypothesis → ∀ H : ℝ, exp 30 < H →\n    ∀ T : Finset ℕ, (∀ p ∈ T, Nat.Prime p) →\n      (∑ p ∈ T, -(log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ))) +\n        (∑ p ∈ Nat.primesLE ⌊H⌋₊, (1 / (p : ℝ) - log p / (H * log H))) +\n        H / (H * log H) <\n        eulerMascheroniConstant + log (log H) +\n          (113/50 : ℝ) * (H^(-(1/2 : ℝ)) * (log H)⁻¹)\n\n/-- Conditional lower estimate for the loss paid by the exponent at every\nprime up to half the height, including primes absent from the factorization. -/", "RiemannHypothesis → ∀ H : ℝ, exp 30 < H →\n    (113/50 : ℝ) * (H^(-(1/2 : ℝ)) * (log H)⁻¹) ≤\n      ∑ p ∈ Nat.primesLE ⌊H/2⌋₊, min (log p / (H * log H)) ((p : ℝ)⁻¹ ^ 2)"]'),
(5084, 'Erdos173.erdos_173.R1.H2.R1.H1.R1.H2', 1, 'marcusbuffett', null::int, '["let ζ : ℂ := ⟨1 / 2, √3 / 2⟩\n  ∀ (E : IntermediateField ℚ ℂ) (F : IntermediateField ℚ ℝ), Countable E →\n    (∀ z : ℂ, z ∈ E ↔ z.re ∈ F ∧ z.im ∈ F) →\n    (∀ p : Polynomial ℂ, p ≠ 0 → (∀ n, p.coeff n ∈ E) → ∀ z, p.eval z = 0 → z ∈ E) →\n    (∀ Q : Finset ℂ, (∀ q ∈ Q, q ∈ E ∧ ‖q‖ = 1) →\n      ∃ S : Finset ℂ, (∀ s ∈ S, s ∈ E ∧ ‖s‖ = 1) ∧\n      ∀ j : ℂ → ℂ, (∀ s ∈ S, j s ∈ Q) →\n        (1 : ℂ) ∈ Submodule.span ℚ ((fun s => j s*s) '''' (S : Set ℂ)) ∧\n        Complex.I ∈ Submodule.span ℚ ((fun s => j s*s) '''' (S : Set ℂ))) →\n    ∀ x : ℝ, 0 < x → (x : ℂ) ∈ E → ∀ c : ℂ → Fin 2,\n    (∀ r : ℝ, r=1 ∨ r=x → ∀ p ∈ E, ∀ u ∈ E, ‖u‖=1 →\n      ¬ (c (p+u*r)=c p ∧ c (p+u*(r*ζ))=c p)) →\n    ∃ ν : Measure ℂ, IsFiniteMeasure ν ∧ ν.real Set.univ ≤ 1 ∧\n    ∀ r : ℝ, r=1 ∨ r=x → ∀ u : Circle,\n      (∫ ξ, (Circle.exp (inner ℝ ξ ((u : ℂ)*(r:ℂ))) : ℂ) ∂ν) = -1/3\n\n/-- Averaging a constant planar Fourier transform on a circle gives its\nreal Bessel transform at that radius. -/", "∀ (ν : Measure ℂ) [IsFiniteMeasure ν] (r : ℝ), 0 < r →\n  (∀ u : Circle, (∫ ξ, (Circle.exp (inner ℝ ξ ((u : ℂ)*(r:ℂ))) : ℂ) ∂ν) = -1/3) →\n  (∫ ξ : ℂ, (2 * π)⁻¹ * (∫ θ in (0:ℝ)..2*π, cos ((r * ‖ξ‖) * cos θ)) ∂ν) = -1/3"]'),
(5151, 'Erdos308.erdos_308.variants.croot.R1.H1', 1, 'marcusbuffett', null::int, '["∀ a : ℝ, 3<a → ∀ ε : ℝ, 0<ε → ∀ᶠ N : ℕ in atTop,\n  let J (i : ℕ) := (Icc 1 i).lcm id\n  let Q := ⌊(N:ℝ)/(log N)^a⌋₊\n  (∑ n ∈ (Icc 1 N).filter (fun n => ¬n∣J Q), (1:ℝ)/n) ≤\n    (a^2/2+ε)*(log (log N))^2/log N\n\n/-- Small and medium prime powers. The small-power costs telescope to less\nthan one and the intermediate powers contribute a negligible tail. -/", "∀ ε : ℝ, 0<ε → ∀ᶠ N : ℕ in atTop,\n  let J (i : ℕ) := (Icc 1 i).lcm id\n  let R (i : ℕ) := (Icc 1 N).filter fun n => n∣J i ∧ ¬ n∣J (i-1)\n  ∃ cost : ℕ→ℚ, ((∑ i ∈ Ioc 1 N.sqrt, cost i : ℚ):ℝ) ≤\n    1 + ε*(log (log N))^2/log N ∧\n    ∀ i ∈ Ioc 1 N.sqrt, ∀ z : ℤ, ∃ V ⊆ R i,\n      (∑ n ∈ V,(1:ℚ)/n) ≤ cost i ∧ ∃ b : ℤ,\n        (b:ℚ)/J (i-1) = (z:ℚ)/J i - ∑ n ∈ V,(1:ℚ)/n\n\n/-- The modular subset sums for the large prime powers, in the range for\nwhich logarithmically many denominators are available. -/", "∀ a : ℝ, 3<a → ∀ ε : ℝ, 0<ε → ∀ᶠ N : ℕ in atTop,\n  let J (i : ℕ) := (Icc 1 i).lcm id\n  let Q := ⌊(N:ℝ)/(log N)^a⌋₊\n  let R (i : ℕ) := (Icc 1 N).filter fun n => n∣J i ∧ ¬ n∣J (i-1)\n  ∃ cost : ℕ→ℚ, ((∑ i ∈ Ioc N.sqrt Q, cost i : ℚ):ℝ) ≤\n    ε*(log (log N))^2/log N ∧\n    ∀ i ∈ Ioc N.sqrt Q, ∀ z : ℤ, ∃ V ⊆ R i,\n      (∑ n ∈ V,(1:ℚ)/n) ≤ cost i ∧ ∃ b : ℤ,\n        (b:ℚ)/J (i-1) = (z:ℚ)/J i - ∑ n ∈ V,(1:ℚ)/n"]'),
(5153, 'CramerConjecture.cramer_conjecture.variants.baker_harman_pintz.R1.H1', 1, 'marcusbuffett', null::int, '["∃ c : ℝ, 0 < c ∧ ∀ᶠ a : ℕ in atTop,\n    let h := ⌈2 * (a : ℝ)^(0.525 : ℝ)⌉₊\n    c * h ≤ ∑ k ∈ Ico (a+h-h/2) (a+h+h/2), (Λ k : ℝ)\n\n/-- A second difference of the integrated Chebyshev sum dominates the central mass. -/", "let F (n : ℕ) := ∑ k ∈ range n, (Λ k : ℝ) * ((n : ℝ) - k)\n  ∀ a h : ℕ, (h : ℝ)/2 * (∑ k ∈ Ico (a+h-h/2) (a+h+h/2), (Λ k : ℝ)) ≤\n    F (a+2*h) - 2*F (a+h) + F a"]'),
(5703, 'LennonPittel.lennon_pittel_conjecture.R3.H2.R1.H2', 1, 'marcusbuffett', null::int, '["∀ η : ℝ, 0 < η → ∃ b A B κ d : ℝ,\n  admissible b A B κ ∧ 0 < d ∧ ∀ᶠ n : ℕ in atTop,\n    ENNReal.ofReal (1-η) ≤ continuousScoreLaw n\n      {x | d*((n:ℝ)*Real.log n) ≤ (params b A B κ n).aggregateMean n x}\n\n/-- The raw diagonal and the products of conditional means of incomparable anchors\nare negligible on the squared target scale. -/", "∀ b A B κ : ℝ, admissible b A B κ →\n  (fun n : ℕ => pivotRawDiagonalMass (params b A B κ n) n +\n    ∫ x, (params b A B κ n).incomparableMeanProductMass x ∂continuousScoreLaw n) =o[atTop]\n      (fun n : ℕ => ((n:ℝ)*Real.log n)^2)\n\n/-- The ordered comparable-anchor residual is negligible. -/", "∀ b A B κ : ℝ, admissible b A B κ →\n  (fun n : ℕ => ∫ x, (params b A B κ n).comparableResidualMass x ∂continuousScoreLaw n) =o[atTop]\n    (fun n : ℕ => ((n:ℝ)*Real.log n)^2)\n\n/-- The raw products of decoration counts for incomparable anchors are negligible. -/", "∀ b A B κ : ℝ, admissible b A B κ →\n  (fun n : ℕ => ∫ x, (params b A B κ n).incomparableCountProductMass x ∂continuousScoreLaw n) =o[atTop]\n    (fun n : ℕ => ((n:ℝ)*Real.log n)^2)"]'),
(8492, 'CongruentNumber.Tunnell_even.R1.H2.R1.H2.R1.H2', 1, 'ysanatomic', null::int, '["∀ (n : ℕ) (hn : 0<n),\n  letI : NeZero (4*n) := ⟨Nat.ne_of_gt (Nat.mul_pos (by decide) hn)⟩\n  let a := 1+3*(4*n)\n  let ω : ℝ := (∫ x in Ioi (n:ℝ), (Real.sqrt (x^3-(n:ℝ)^2*x))⁻¹)\n  let b (v : ZMod (4*n) × ZMod (4*n)) : GaussianInt := ⟨v.1.val,v.2.val⟩\n  let χ (v : ZMod (4*n) × ZMod (4*n)) : ℤ :=\n    let m := (b v).norm.natAbs\n    if (⟨2,2⟩:GaussianInt) ∣ b v-1 then (if Odd m then jacobiSym n m else 0) else 0\n  ∀ M : PeriodPair, M.ω₁=(ω:ℂ) → M.ω₂=Complex.I*(ω:ℂ) →\n  let t (j : Fin a × Fin a) : ℂ := ((j.1.val:ℂ)*M.ω₁+(j.2.val:ℂ)*M.ω₂)/(a:ℂ)\n  let D (z : ℂ) := ∏ j ∈ Finset.univ.filter (fun j => t j ∉ M.lattice),\n    (M.weierstrassP z-M.weierstrassP (t j))\n  let G (z : ℂ) := ∏ v ∈ Finset.univ.filter (fun v => χ v≠0),\n    D (z+((ω/(4*n):ℝ):ℂ)*(b v:ℂ))^χ v\n  let f : ℂ := (4*n:ℕ)\n  let Λ : Submodule ℤ ℂ := Submodule.span ℤ {f,f*Complex.I}\n  let ζ (z : ℂ) := ∑'' w : Λ, ((z-(w:ℂ))⁻¹+(w:ℂ)⁻¹+z/(w:ℂ)^2)\n  let U := ∑ v : ZMod (4*n) × ZMod (4*n), (χ v:ℂ)*(-conj\n    ((a:ℂ)*ζ ((a:ℂ)*(b v:ℂ))-(a:ℂ)^2*ζ (b v:ℂ)))\n  ∀ r : ℚ, r≠0 → ((a:ℂ)^2-(a:ℂ))*((r:ℂ)*(ω:ℂ))=U → ∃ c : ℚ, c≠0 ∧ logDeriv G 0=(c:ℂ)", "∀ (n : ℕ) (hn : 0<n),\n  letI : NeZero (4*n) := ⟨Nat.ne_of_gt (Nat.mul_pos (by decide) hn)⟩\n  let a := 1+3*(4*n)\n  let ω : ℝ := (∫ x in Ioi (n:ℝ), (Real.sqrt (x^3-(n:ℝ)^2*x))⁻¹)\n  let b (v : ZMod (4*n) × ZMod (4*n)) : GaussianInt := ⟨v.1.val,v.2.val⟩\n  let χ (v : ZMod (4*n) × ZMod (4*n)) : ℤ :=\n    let m := (b v).norm.natAbs\n    if (⟨2,2⟩:GaussianInt) ∣ b v-1 then (if Odd m then jacobiSym n m else 0) else 0\n  ∀ M : PeriodPair, M.ω₁=(ω:ℂ) → M.ω₂=Complex.I*(ω:ℂ) →\n  let t (j : Fin a × Fin a) : ℂ := ((j.1.val:ℂ)*M.ω₁+(j.2.val:ℂ)*M.ω₂)/(a:ℂ)\n  let D (z : ℂ) := ∏ j ∈ Finset.univ.filter (fun j => t j ∉ M.lattice),\n    (M.weierstrassP z-M.weierstrassP (t j))\n  let G (z : ℂ) := ∏ v ∈ Finset.univ.filter (fun v => χ v≠0),\n    D (z+((ω/(4*n):ℝ):ℂ)*(b v:ℂ))^χ v\n  n%8=2 → 2<n → ∀ P : (⟨0,0,0,-(n:ℚ)^2,0⟩ : WeierstrassCurve ℚ).toAffine.Point,\n    ¬IsOfFinAddOrder P → ¬(∃ c : ℚ, c≠0 ∧ logDeriv G 0=(c:ℂ))"]')
) v(pr, t, rn, h, pts, st);
-- created_at := merge time, only for rows this transaction created (created_at = now())
update oma_reductions r set created_at = v.m from (values
(4425, '2026-11-27T08:46:01Z'::timestamptz),
(4466, '2026-11-27T08:53:43Z'::timestamptz),
(4495, '2026-11-27T08:59:41Z'::timestamptz),
(4504, '2026-11-27T09:01:08Z'::timestamptz),
(4509, '2026-11-27T09:01:34Z'::timestamptz),
(4511, '2026-11-27T09:02:11Z'::timestamptz),
(4513, '2026-11-27T09:03:10Z'::timestamptz),
(4528, '2026-11-27T09:09:24Z'::timestamptz),
(4531, '2026-11-27T09:10:29Z'::timestamptz),
(4563, '2026-11-27T09:32:05Z'::timestamptz),
(4613, '2026-11-27T09:38:50Z'::timestamptz),
(4696, '2026-11-27T09:45:00Z'::timestamptz),
(4790, '2026-11-27T09:47:46Z'::timestamptz),
(4633, '2026-11-27T09:54:05Z'::timestamptz),
(4799, '2026-11-27T10:03:23Z'::timestamptz),
(4826, '2026-11-27T10:06:51Z'::timestamptz),
(5045, '2026-11-27T10:36:00Z'::timestamptz),
(5059, '2026-11-27T10:37:45Z'::timestamptz),
(5084, '2026-11-27T10:41:20Z'::timestamptz),
(5151, '2026-11-27T10:52:21Z'::timestamptz),
(5153, '2026-11-27T11:02:16Z'::timestamptz),
(5703, '2026-11-27T12:18:11Z'::timestamptz),
(8492, '2026-11-27T18:32:03Z'::timestamptz)
) v(pr, m) where r.pr_url = 'https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/' || v.pr and r.created_at = now();
update oma_steps s set created_at = r.created_at from oma_reductions r where s.reduction = r.id and s.created_at = now();
update oma_events e set created_at = r.created_at from oma_reductions r
  where e.kind = 'reduced' and e.created_at = now() and e.problem_id = r.problem_id and e.detail = r.id || ' into ' || r.hyps || ' steps';
commit;

-- ===== batch 5: reductions, dependency level 2 (19 PRs: 4551 .. ) =====
begin;
select v.pr, case
  when exists (select 1 from oma_reductions r where r.pr_url = 'https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/' || v.pr) then json_build_object('skip','pr_exists')
  when exists (select 1 from oma_reductions r where r.id = v.t || '.R' || v.rn) then json_build_object('skip','id_exists')
  when v.pts is null and not exists (select 1 from oma_steps s where s.id = v.t) then json_build_object('error','unknown_target')
  else oma_register_reduction(v.t || '.R' || v.rn, v.t, v.h, 'https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/' || v.pr,
         'OMAReductions.R_' || regexp_replace(v.t || '.R' || v.rn, '[^A-Za-z0-9]', '_', 'g'), v.st::json,
         coalesce(v.pts, (select s.points from oma_steps s where s.id = v.t))) end r
from (values
(4551, 'Erdos710.erdos_710.variants.lower_bound.R1.H1.R1.H1', 1, 'marcusbuffett', null::int, '["∀ y : ℕ, 3 ≤ y → ∃ C : ℝ, ∀ v : ℝ, 1 ≤ v →\n    let d := (y.primesBelow.card:ℝ)\n    let f := log ((Nat.smoothNumbersUpTo ⌊exp v⌋₊ y).card:ℝ)\n    C + d*log v ≤ f ∧ f ≤ C + d*log (v+d*log y)\n\n/-- The prime number theorem in dimension-count form. -/", "Tendsto (fun y : ℕ => (y.primesBelow.card:ℝ)*log y/y) atTop (𝓝 1)"]'),
(4616, 'Erdos299.erdos_299.variants.density.R1.H1.R1.H2.R1.H3.R1.H1', 1, 'marcusbuffett', null::int, '["∀ᶠ N : ℕ in atTop,\n  let w := log (log N)\n  let M := (N:ℝ)^(1-1/w)\n  let R := (range N).filter (fun d => 0 < d ∧ ∀ p : ℕ, p ∈ d.primeFactors →\n      exp (log N / (2*w^2)) < (p : ℝ) ^ d.factorization p)\n  ∀ n q : ℕ, 0 < n → n < N → M ≤ n → (n.primeFactors.card : ℝ) ≤ 2*w →\n    IsPrimePow q → q ∣ n → Nat.Coprime q (n/q) →\n    ∃ d ∈ R, M*(N:ℝ)^(-2/w) < q*(d:ℝ) ∧ q*d ∣ n ∧ Nat.Coprime (q*d) (n/(q*d))", "∀ᶠ N : ℕ in atTop,\n  let w := log (log N)\n  let R := (range N).filter (fun d => 0 < d ∧ ∀ p : ℕ, p ∈ d.primeFactors →\n      exp (log N / (2*w^2)) < (p : ℝ) ^ d.factorization p)\n  ∑ d ∈ R, (if (d.primeFactors.card : ℝ) ≤ w/110 then (log N)^(-(1/99:ℝ))\n    else 1+log N) / d < (log N)^(-(1/100:ℝ))/2"]'),
(4678, 'Erdos297.erdos_297.variants.general.R1.H3.R1.H2.R1.H1', 1, 'marcusbuffett', null::int, '["∀ (x : ℚ), 0 < x → ∀ δ > (0:ℝ),\n  ∃ ε : ℝ, 0 < ε ∧ ε < 1/2 ∧ ∀ L₀ : ℕ, ∃ L ≥ L₀,\n    let J (i : ℕ) := (Icc 1 i).lcm id\n    let K := J L\n    let R (i : ℕ) := (Icc 1 (i*i)).filter fun n => IsPrimePow i ∧ i∣n ∧ Nat.Coprime i (n/i) ∧\n        (i:ℝ)^ε ≤ (n/i:ℕ) ∧ ((n/i:ℕ):ℝ) ≤ 2*(i:ℝ)^ε ∧ ¬ K ∣ n\n    ∀ᶠ N : ℕ in atTop, ∃ B ≥ L, ∃ U ⊆ Icc 1 N,\n      (((Icc 1 N) \\ U).card:ℝ) ≤ δ*N ∧ x.den ∣ J B ∧\n      (∀ u ∈ U, u ∣ J B ∧ ¬ K ∣ u) ∧\n      (∀ i ∈ Ioc L B, R i ⊆ Icc 1 N ∧ Disjoint U (R i)) ∧\n      (∀ i ∈ Ioc L B, ∀ j ∈ Ioc L B, i < j → Disjoint (R i) (R j))", "∀ ε : ℝ, 0 < ε → ε < 1/2 → ∀ d : ℚ, 0 < d →\n  ∃ L₀ : ℕ, ∀ L ≥ L₀,\n    let J (i : ℕ) := (Icc 1 i).lcm id\n    let K := J L\n    let R (i : ℕ) := (Icc 1 (i*i)).filter fun n => IsPrimePow i ∧ i∣n ∧ Nat.Coprime i (n/i) ∧\n        (i:ℝ)^ε ≤ (n/i:ℕ) ∧ ((n/i:ℕ):ℝ) ≤ 2*(i:ℝ)^ε ∧ ¬ K ∣ n\n    ∃ cost : ℕ → ℚ, (∀ B, ∑ i ∈ Ioc L B, cost i < d) ∧\n      ∀ i : ℕ, L < i → ∀ z : ℤ, ∃ V ⊆ R i,\n        (∑ n ∈ V, (1:ℚ)/n) ≤ cost i ∧ ∃ a : ℤ,\n        (a:ℚ)/J (i-1) = (z:ℚ)/J i - ∑ n ∈ V, (1:ℚ)/n"]'),
(4876, 'BusyBeaver.BB_4.R1.H2.R1.H2.R1.H3.R1.H3', 1, 'marcusbuffett', null::int, '["let entry (z : ℕ) (r : Fin 4) (s : Fin 2) : Option (Option (Fin 4) × Stmt (Fin 2)) :=\n    let k := z / 17^(2*r.val+s.val) % 17\n    if k=16 then none else some (some (Fin.ofNat 4 (k/4)),\n      .write (Fin.ofNat 2 (k/2)) (if k%2=0 then .left else .right))\n  ∀ (M : Machine (Fin 2) (Fin 4)) (a b c : Fin 2) (q : Fin 4),\n    M 0 0 = some (some 1,Stmt.write 1 .right) →\n    M 1 0 = some (some 2,Stmt.write a .right) →\n    M 2 0 = some (some 3,Stmt.write b .right) →\n    M 3 0 = some (some q,Stmt.write c .left) →\n    M.HaltsAfter (Machine.init []) 107 ∨\n    (∃ z ∈ ([1790187557,6207529726,6221728296,6810924734] : List ℕ),\n      ∀ r s cmd, entry z r s=some cmd → M r s=some cmd) ∨\n    ∃ (n m : ℕ) (x : Fin n) (y : Fin m) (L : Fin 2 → Fin n → Fin n)\n      (R : Fin 2 → Fin m → Fin m) (S : Fin 4 → Fin 2 → Fin n → Fin m → Bool),\n      L 0 x=x ∧ R 0 y=y ∧ S 0 0 x y=true ∧\n      ∀ q a s t i j, S q a (L s i) (R t j)=true →\n        ∃ r w d, M q a=some (some r,Stmt.write w d) ∧\n          (match d with\n           | .left => S r s i (R w (R t j))\n           | .right => S r t (L w (L s i)) j) = true\n\n/-- The four remaining partial machines, with all seven live rows specified. -/", "let entry (z : ℕ) (r : Fin 4) (s : Fin 2) : Option (Option (Fin 4) × Stmt (Fin 2)) :=\n    let k := z / 17^(2*r.val+s.val) % 17\n    if k=16 then none else some (some (Fin.ofNat 4 (k/4)),\n      .write (Fin.ofNat 2 (k/2)) (if k%2=0 then .left else .right))\n  ∀ z ∈ ([1790187557,6207529726,6221728296,6810924734] : List ℕ),\n    ¬ Machine.IsHalting (entry z)"]'),
(4971, 'Erdos258.erdos_258.variants.monotone.R2.H2.R1.H2', 1, 'marcusbuffett', null::int, '["∀ k t H : ℕ, 1≤k → 2≤t → ∃ A r : ℕ, 0<A ∧ r<A ∧\n  log (A:ℝ) ≤ 4*(t:ℝ)*(k:ℝ)^2*((k:ℝ)^2+log (H+k+2:ℕ)) ∧\n  (∀ N : ℕ, N ≡ r [MOD A] → ∀ j ∈ Icc 1 k, t^j ∣ (N+j).divisors.card) ∧\n  ∀ i < H, Nat.Coprime (r+k+i+1) A\n\n/-- Divisor hyperbola bound for a reduced residue class. -/", "∀ X A r : ℕ, 1≤A → Nat.Coprime r A →\n  (∑ n ∈ (Icc 1 X).filter (fun n => n ≡ r [MOD A]), (n.divisors.card:ℝ)) ≤\n    2*((X:ℝ)/A*(1+log X)+sqrt X)"]'),
(5025, 'Erdos930.erdos_930.variants.consecutive_integers.R1.H4.R1.H2.R1.H1', 1, 'marcusbuffett', null::int, '["∀ k : ℕ, 60184 ≤ k → k < 5000000 → k=60184 ∨ k.Prime →\n  (k.primeCounting:ℝ)*(log k-11/10) ≤ k\n\n/-- A single finite sum and prime count anchor partial summation at five million. -/", "let T : ℝ := 5000000\n  (Nat.primeCounting 5000000 : ℝ) - Chebyshev.theta T / log T ≤\n    T/(log T-11/10) - T/log T - T/(5*(log T)^3)\n\n/-- The upper half of Dusart 2018, Theorem 4.2, with k = 2 and eta = 0.2.\nThe published threshold 3594641 is below five million. -/", "∀ t : ℝ, 5000000 ≤ t → Chebyshev.theta t ≤ t + t/(5*(log t)^2)"]'),
(4990, 'Arxiv.1601.03081.crystals_components_unique.R1.H2.R1.H2', 1, 'senamakel', null::int, '["∀ g y z : ℕ, 1 < g → 17 ≤ y → Odd g → Odd y → Odd z → g*y ≤ z →\n    (g+1)*(y*z+1) ∣ (g+y*z)^2 →\n    (g*y+1)*(z+1) ∣ (g*y+z)^2 → g = z\n\n/-- Both coprime components are nontrivial, in increasing order. -/", "∀ g x y z : ℕ, 1 < g → 3 ≤ x → x < y →\n    Odd g → Odd x → Odd y → Odd z → g*y ≤ x*z → Nat.Coprime x y →\n    (g*x+1)*(y*z+1) ∣ (g*x+y*z)^2 →\n    (g*y+1)*(x*z+1) ∣ (g*y+x*z)^2 → g = z"]'),
(4741, 'Arxiv.1601.03081.crystals_components_unique.R1.H1.R1.H2', 1, 'senamakel', null::int, '["∀ a c m p q : ℕ, 21 ≤ m → Odd m → a.Coprime c → a ≤ c → c ≤ m*a →\n    3 ≤ a → 5 ≤ c →\n    (a+m*c)^2 = p*((a+1)*(m*c+1)) →\n    (c+m*a)^2 = q*((c+1)*(m*a+1)) → q = 4 → p = q", "∀ a c m p q : ℕ, 21 ≤ m → Odd m → a.Coprime c → a ≤ c → c ≤ m*a →\n    3 ≤ a → 5 ≤ c →\n    (a+m*c)^2 = p*((a+1)*(m*c+1)) →\n    (c+m*a)^2 = q*((c+1)*(m*a+1)) → 5 ≤ q → p = q"]'),
(5300, 'BusyBeaver.BB_4.R1.H2.R1.H2.R1.H3.R1.H1', 1, 'pageman', null::int, '["∀ (M : Machine (Fin 2) (Fin 4)) (a : Fin 2) (q : Fin 4),\n    q.val ≤ 1 →\n    M 0 0 = some (some 1, Stmt.write 1 Dir.right) →\n    M 1 0 = some (some q, Stmt.write a Dir.left) →\n    M.IsHalting → M.HaltsAfter (Machine.init []) 107", "∀ (M : Machine (Fin 2) (Fin 4)) (a : Fin 2),\n    M 0 0 = some (some 1, Stmt.write 1 Dir.right) →\n    M 1 0 = some (some 2, Stmt.write a Dir.left) →\n    M.IsHalting → M.HaltsAfter (Machine.init []) 107"]'),
(5362, 'BusyBeaver.BB_4.R1.H2.R1.H1.R1.H3.R1.H2', 1, 'pageman', null::int, '["∀ M : Machine (Fin 2) (Fin 4),\n  M 0 0 = some (some 1, Stmt.write 0 Dir.right) →\n  (∃ q'' : Fin 4, (q'' = 0 ∨ q'' = 1) ∧ ∃ z, M 1 0 = some (some q'', z)) →\n  (∃ q t, M.multiStep (Machine.init []) 107 = some ⟨some q, t⟩) →\n  (∀ q a, (∃ i < 107, ∃ t : Tape (Fin 2),\n    M.multiStep (Machine.init []) i = some ⟨some q, t⟩ ∧ t.head = a) ↔\n    ∃ q'' z, M q a = some (some q'', z)) →\n  (∀ q a, M q a = none ∨ ∃ q'' z, M q a = some (some q'', z)) →\n  (∃ q a, M q a = none) →\n  (∀ (i p : ℕ) (q : Fin 4) (a : Fin 2) (side : Bool)\n      (near : List (Fin 2)) (fixed : ListBlank (Fin 2)), 0 < p → i + p ≤ 107 →\n    let cfg := fun tail : ListBlank (Fin 2) =>\n      let free := near.foldr ListBlank.cons tail\n      (⟨some q, if side then ⟨a, free, fixed⟩ else ⟨a, fixed, free⟩⟩ : Cfg (Fin 2) (Fin 4))\n    (∃ tail, M.multiStep (Machine.init []) i = some (cfg tail)) →\n    ¬ ∀ tail, ∃ tail'', M.multiStep (cfg tail) p = some (cfg tail'')) →\n  ¬ M.IsHalting", "∀ M : Machine (Fin 2) (Fin 4),\n  M 0 0 = some (some 1, Stmt.write 0 Dir.right) →\n  (∃ d : Dir, M 1 0 = some (some 2, Stmt.write 0 d)) →\n  (∃ q t, M.multiStep (Machine.init []) 107 = some ⟨some q, t⟩) →\n  (∀ q a, (∃ i < 107, ∃ t : Tape (Fin 2),\n    M.multiStep (Machine.init []) i = some ⟨some q, t⟩ ∧ t.head = a) ↔\n    ∃ q'' z, M q a = some (some q'', z)) →\n  (∀ q a, M q a = none ∨ ∃ q'' z, M q a = some (some q'', z)) →\n  (∃ q a, M q a = none) →\n  (∀ (i p : ℕ) (q : Fin 4) (a : Fin 2) (side : Bool)\n      (near : List (Fin 2)) (fixed : ListBlank (Fin 2)), 0 < p → i + p ≤ 107 →\n    let cfg := fun tail : ListBlank (Fin 2) =>\n      let free := near.foldr ListBlank.cons tail\n      (⟨some q, if side then ⟨a, free, fixed⟩ else ⟨a, fixed, free⟩⟩ : Cfg (Fin 2) (Fin 4))\n    (∃ tail, M.multiStep (Machine.init []) i = some (cfg tail)) →\n    ¬ ∀ tail, ∃ tail'', M.multiStep (cfg tail) p = some (cfg tail'')) →\n  ¬ M.IsHalting", "∀ M : Machine (Fin 2) (Fin 4),\n  M 0 0 = some (some 1, Stmt.write 0 Dir.right) →\n  M 1 0 = some (some 2, Stmt.write 1 Dir.right) →\n  (∃ q t, M.multiStep (Machine.init []) 107 = some ⟨some q, t⟩) →\n  (∀ q a, (∃ i < 107, ∃ t : Tape (Fin 2),\n    M.multiStep (Machine.init []) i = some ⟨some q, t⟩ ∧ t.head = a) ↔\n    ∃ q'' z, M q a = some (some q'', z)) →\n  (∀ q a, M q a = none ∨ ∃ q'' z, M q a = some (some q'', z)) →\n  (∃ q a, M q a = none) →\n  (∀ (i p : ℕ) (q : Fin 4) (a : Fin 2) (side : Bool)\n      (near : List (Fin 2)) (fixed : ListBlank (Fin 2)), 0 < p → i + p ≤ 107 →\n    let cfg := fun tail : ListBlank (Fin 2) =>\n      let free := near.foldr ListBlank.cons tail\n      (⟨some q, if side then ⟨a, free, fixed⟩ else ⟨a, fixed, free⟩⟩ : Cfg (Fin 2) (Fin 4))\n    (∃ tail, M.multiStep (Machine.init []) i = some (cfg tail)) →\n    ¬ ∀ tail, ∃ tail'', M.multiStep (cfg tail) p = some (cfg tail'')) →\n  ¬ M.IsHalting", "∀ M : Machine (Fin 2) (Fin 4),\n  M 0 0 = some (some 1, Stmt.write 0 Dir.right) →\n  M 1 0 = some (some 2, Stmt.write 1 Dir.left) →\n  (∃ q t, M.multiStep (Machine.init []) 107 = some ⟨some q, t⟩) →\n  (∀ q a, (∃ i < 107, ∃ t : Tape (Fin 2),\n    M.multiStep (Machine.init []) i = some ⟨some q, t⟩ ∧ t.head = a) ↔\n    ∃ q'' z, M q a = some (some q'', z)) →\n  (∀ q a, M q a = none ∨ ∃ q'' z, M q a = some (some q'', z)) →\n  (∃ q a, M q a = none) →\n  (∀ (i p : ℕ) (q : Fin 4) (a : Fin 2) (side : Bool)\n      (near : List (Fin 2)) (fixed : ListBlank (Fin 2)), 0 < p → i + p ≤ 107 →\n    let cfg := fun tail : ListBlank (Fin 2) =>\n      let free := near.foldr ListBlank.cons tail\n      (⟨some q, if side then ⟨a, free, fixed⟩ else ⟨a, fixed, free⟩⟩ : Cfg (Fin 2) (Fin 4))\n    (∃ tail, M.multiStep (Machine.init []) i = some (cfg tail)) →\n    ¬ ∀ tail, ∃ tail'', M.multiStep (cfg tail) p = some (cfg tail'')) →\n  ¬ M.IsHalting"]'),
(5397, 'RiemannHypothesis.robin_criterion.R1.H1.R1.H2.R1.H2', 1, 'marcusbuffett', null::int, '["RiemannHypothesis → ∀ H : ℝ, exp 30 < H →\n    let s := Real.sqrt (2 * H)\n    let b := H / 2\n    let err := (Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi)) *\n      (b ^ ((1 / 2 : ℝ) - 2) * (Real.log b)⁻¹ *\n        (2 + (Real.log b)⁻¹ + 4 / (3 * (Real.log b)^2)))\n    let L := 2 * s^(-(1 : ℝ)) * (Real.log s)⁻¹ -\n      s^(-(1 : ℝ)) * ((Real.log s)^2)⁻¹ -\n      (9 / 4 : ℝ) * s^(-(3 / 2 : ℝ)) * (Real.log s)⁻¹ -\n      Real.log (2 * Real.pi) * s^(-(2 : ℝ)) * (Real.log s)⁻¹ -\n      2 * b^(-(1 : ℝ)) * (Real.log b)⁻¹ - err\n    L ≤ Chebyshev.theta s / (s^2 * Real.log s) +\n      ∑ p ∈ (Finset.Ioc ⌊s⌋₊ ⌊b⌋₊).filter Nat.Prime, (p : ℝ)⁻¹ ^ 2\n\n/-- The explicit numerical estimate for the scalar lower bound. -/", "∀ H : ℝ, exp 30 < H →\n    let s := Real.sqrt (2 * H)\n    let b := H / 2\n    let err := (Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi)) *\n      (b ^ ((1 / 2 : ℝ) - 2) * (Real.log b)⁻¹ *\n        (2 + (Real.log b)⁻¹ + 4 / (3 * (Real.log b)^2)))\n    let L := 2 * s^(-(1 : ℝ)) * (Real.log s)⁻¹ -\n      s^(-(1 : ℝ)) * ((Real.log s)^2)⁻¹ -\n      (9 / 4 : ℝ) * s^(-(3 / 2 : ℝ)) * (Real.log s)⁻¹ -\n      Real.log (2 * Real.pi) * s^(-(2 : ℝ)) * (Real.log s)⁻¹ -\n      2 * b^(-(1 : ℝ)) * (Real.log b)⁻¹ - err\n    (113/50 : ℝ) * (H^(-(1/2 : ℝ)) * (Real.log H)⁻¹) ≤ L\n\n/-- Split the finite prime sum at s and bound each minimum on its own range. -/", "∀ H s b : ℝ, 1 < H → 1 < s → s ≤ b → H * log H ≤ s^2 * log s →\n    Chebyshev.theta s / (s^2 * Real.log s) +\n      ∑ p ∈ (Finset.Ioc ⌊s⌋₊ ⌊b⌋₊).filter Nat.Prime, (p : ℝ)⁻¹ ^ 2 ≤\n      ∑ p ∈ Nat.primesLE ⌊b⌋₊, min (log p / (H * log H)) ((p : ℝ)⁻¹ ^ 2)"]'),
(5482, 'Erdos173.erdos_173.R1.H2.R1.H1.R1.H2.R1.H1', 1, 'marcusbuffett', null::int, '["∀ (G X : Type) [CommGroup G] [Countable G] [MeasurableSpace X] [StandardBorelSpace X]\n    [Nonempty X] [MulAction G X] [MeasurableConstSMul G X],\n    ∀ (μ : Measure X) [IsProbabilityMeasure μ] [SMulInvariantMeasure G X μ],\n    ∀ s : Set X, MeasurableSet s → μ s = 0 →\n    ∀ f : X → ℂ, Measurable f → (∀ z, ‖f z‖ ≤ 1) →\n    (∀ (ρ : Measure X) [IsProbabilityMeasure ρ] [ErgodicSMul G X ρ],\n      ρ s = 0 → ∫ z, f z ∂ρ = 0) → ∫ z, f z ∂μ = 0\n\n/-- On the dual of the discrete carrier, an ergodic, rotation-invariant\nprobability supported off the ordinary characters has zero nontrivial Fourier coefficients. -/", "∀ (E : IntermediateField ℚ ℂ) (F : IntermediateField ℚ ℝ), ∀ hc : Countable E,\n    ∀ hF : (∀ z : ℂ, z ∈ E ↔ z.re ∈ F ∧ z.im ∈ F),\n    ∀ ha : (∀ p : Polynomial ℂ, p ≠ 0 → (∀ n, p.coeff n ∈ E) → ∀ z, p.eval z = 0 → z ∈ E),\n    ∀ ht : (∀ Q : Finset ℂ, (∀ q ∈ Q, q ∈ E ∧ ‖q‖ = 1) →\n      ∃ S : Finset ℂ, (∀ s ∈ S, s ∈ E ∧ ‖s‖ = 1) ∧\n      ∀ j : ℂ → ℂ, (∀ s ∈ S, j s ∈ Q) →\n        (1 : ℂ) ∈ Submodule.span ℚ ((fun s => j s*s) '''' (S : Set ℂ)) ∧\n        Complex.I ∈ Submodule.span ℚ ((fun s => j s*s) '''' (S : Set ℂ))),\n    letI : Carrier := ⟨E,F,hc,hF,ha,ht⟩\n\n    ∀ (μ : Measure D) [IsProbabilityMeasure μ] [ErgodicSMul K D μ],\n      IsWild μ → ∀ a : E, a ≠ 0 → ∫ d, (eval a d : ℂ) ∂μ = 0"]'),
(5505, 'Erdos50.erdos_50_singular.R1.H2.R1.H2', 1, 'marcusbuffett', null::int, '["∃ η : ℝ, 0 < η ∧ η < 1 ∧ ∀ b : ℕ, 2 ≤ b → ∃ y : ℕ, b ≤ y ∧\n    (∏ p ∈ (range (b+1)).filter Nat.Prime, p) ≤ y ∧\n    let Q := (Finset.Ioc b (y^20)).filter Nat.Prime\n    η ≤ ∑ T ∈ Q.powerset.filter (fun T => T.Nonempty ∧\n      (∀ p ∈ T, p ≤ y) ∧ (∏ p ∈ T, p) ≤ y^4),\n      (∏ p ∈ T, 1/(p:ℝ)) * ∏ p ∈ Q \\ T, (1-1/(p:ℝ))\n\n/-- CRT gives the exact frequency of any finite collection of prime patterns. -/", "∀ Q : Finset ℕ, (∀ p ∈ Q, p.Prime) → ∀ R : Finset ℕ → Prop,\n    let q := ∏ p ∈ Q, p\n    (((range q).filter (fun n => R (Q.filter (· ∣ n)))).card : ℝ) / q =\n      ∑ T ∈ Q.powerset.filter R, (∏ p ∈ T, 1/(p:ℝ)) * ∏ p ∈ Q \\ T, (1-1/(p:ℝ))"]'),
(5643, 'Erdos173.erdos_173.R1.H2.R1.H2.R1.H1.R1.H1', 1, 'marcusbuffett', null::int, '["∀ (E : IntermediateField ℚ ℂ) (F : IntermediateField ℚ ℝ), ∀ hc : Countable E,\n    ∀ hF : (∀ z : ℂ, z ∈ E ↔ z.re ∈ F ∧ z.im ∈ F),\n    ∀ ha : (∀ p : Polynomial ℂ, p ≠ 0 → (∀ n, p.coeff n ∈ E) → ∀ z, p.eval z = 0 → z ∈ E),\n    ∀ ht : (∀ Q : Finset ℂ, (∀ q ∈ Q, q ∈ E ∧ ‖q‖ = 1) →\n      ∃ S : Finset ℂ, (∀ s ∈ S, s ∈ E ∧ ‖s‖ = 1) ∧\n      ∀ j : ℂ → ℂ, (∀ s ∈ S, j s ∈ Q) →\n        (1 : ℂ) ∈ Submodule.span ℚ ((fun s => j s*s) '''' (S : Set ℂ)) ∧\n        Complex.I ∈ Submodule.span ℚ ((fun s => j s*s) '''' (S : Set ℂ))),\n    letI : Carrier := ⟨E,F,hc,hF,ha,ht⟩\n\n    ∀ (μ : Measure D) [IsFiniteMeasure μ], IsWild μ → ∀ a : E, a ≠ 0 → ∫ d, (eval a d : ℂ) ∂μ = 0\n\n/-- The spectral measure of a vector orthogonal to the continuous vectors gives the ordinary characters zero mass. -/", "∀ (E : IntermediateField ℚ ℂ) (F : IntermediateField ℚ ℝ), ∀ hc : Countable E,\n    ∀ hF : (∀ z : ℂ, z ∈ E ↔ z.re ∈ F ∧ z.im ∈ F),\n    ∀ ha : (∀ p : Polynomial ℂ, p ≠ 0 → (∀ n, p.coeff n ∈ E) → ∀ z, p.eval z = 0 → z ∈ E),\n    ∀ ht : (∀ Q : Finset ℂ, (∀ q ∈ Q, q ∈ E ∧ ‖q‖ = 1) →\n      ∃ S : Finset ℂ, (∀ s ∈ S, s ∈ E ∧ ‖s‖ = 1) ∧\n      ∀ j : ℂ → ℂ, (∀ s ∈ S, j s ∈ Q) →\n        (1 : ℂ) ∈ Submodule.span ℚ ((fun s => j s*s) '''' (S : Set ℂ)) ∧\n        Complex.I ∈ Submodule.span ℚ ((fun s => j s*s) '''' (S : Set ℂ))),\n    letI : Carrier := ⟨E,F,hc,hF,ha,ht⟩\n\n    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]\n      (U : DiscreteE →* unitary (H →L[ℂ] H)) (v : H), v ∈ (ContinuousVectors.space U)ᗮ →\n      VectorMeasure.measure (CommutingSpectral.calculus U) v (C : Set D) = 0"]'),
(5747, 'Erdos848.erdos_848.R1.H2.R1.H2', 1, 'marcusbuffett', null::int, '["open scoped Classical in ∀ N : ℕ, 160000000≤N → N<2^2300 →\n  let badCount (P : ℕ → Prop) [DecidablePred P] (b : ℕ) := ((Icc 1 N).filter (fun a => P a ∧ ¬ Squarefree (a*b+1))).card\n  let Witness (b : ℕ) := b∈Icc 1 N ∧ ¬ Squarefree (b*b+1)\n  let c7 := ((Icc 1 N).filter (fun a => a%25=7)).card\n  ∀ b b'', Witness b → b % 25 = 7 → Witness b'' → b'' % 25 = 18 →\n    badCount (fun a => a % 25 = 18) b + badCount (fun a => a % 25 = 7) b'' ≤ c7", "open scoped Classical in ∀ N : ℕ, 2^2300≤N →\n  let badCount (P : ℕ → Prop) [DecidablePred P] (b : ℕ) := ((Icc 1 N).filter (fun a => P a ∧ ¬ Squarefree (a*b+1))).card\n  let Witness (b : ℕ) := b∈Icc 1 N ∧ ¬ Squarefree (b*b+1)\n  let c7 := ((Icc 1 N).filter (fun a => a%25=7)).card\n  ∀ b b'', Witness b → b % 25 = 7 → Witness b'' → b'' % 25 = 18 →\n    badCount (fun a => a % 25 = 18) b + badCount (fun a => a % 25 = 7) b'' ≤ c7", "open scoped Classical in ∀ N : ℕ, 160000000≤N →\n  let IsStar (a : ℕ) : Prop := a % 25 ≠ 7 ∧ a % 25 ≠ 18\n  let badCount (P : ℕ → Prop) [DecidablePred P] (b : ℕ) := ((Icc 1 N).filter (fun a => P a ∧ ¬ Squarefree (a*b+1))).card\n  let vCount (P : ℕ → Prop) [DecidablePred P] := ((Icc 1 N).filter (fun a => P a ∧ ¬ Squarefree (a*a+1))).card\n  let lemCCount (b : ℕ) := ((Icc 1 N).filter (fun a => IsStar a ∧ ¬ Squarefree (a*a+1) ∧ ¬ Squarefree (a*b+1))).card\n  let Witness (b : ℕ) := b∈Icc 1 N ∧ ¬ Squarefree (b*b+1)\n  let c7 := ((Icc 1 N).filter (fun a => a%25=7)).card\n  (∀ b, Witness b → IsStar b → b % 2 = 0 →\n    badCount (fun a => a % 25 = 7 ∨ a % 25 = 18) b + lemCCount b ≤ c7) ∧\n  (∀ b₁ b₃, Witness b₁ → IsStar b₁ → b₁ % 4 = 1 → Witness b₃ → IsStar b₃ → b₃ % 4 = 3 →\n    badCount (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ (a % 4 = 1 ∨ a % 2 = 0)) b₁ +\n    badCount (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ a % 4 = 3) b₃ +\n    vCount (fun x => IsStar x ∧ x % 2 = 1) ≤ c7)", "open scoped Classical in ∀ N : ℕ, 160000000≤N →\n  let IsStar (a : ℕ) : Prop := a % 25 ≠ 7 ∧ a % 25 ≠ 18\n  let classCount (P : ℕ → Prop) [DecidablePred P] := ((Icc 1 N).filter P).card\n  let badCount (P : ℕ → Prop) [DecidablePred P] (b : ℕ) := ((Icc 1 N).filter (fun a => P a ∧ ¬ Squarefree (a*b+1))).card\n  let vCount (P : ℕ → Prop) [DecidablePred P] := ((Icc 1 N).filter (fun a => P a ∧ ¬ Squarefree (a*a+1))).card\n  let Witness (b : ℕ) := b∈Icc 1 N ∧ ¬ Squarefree (b*b+1)\n  let c7 := ((Icc 1 N).filter (fun a => a%25=7)).card\n  (∀ b r, Witness b → IsStar b → b % 4 = r → (r = 1 ∨ r = 3) →\n    classCount (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ a % 4 = 4 - r) +\n    badCount (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ a % 4 = r) b +\n    vCount (fun x => IsStar x ∧ x % 4 = r) ≤ c7) ∧\n  (∀ b b'' r, Witness b → IsStar b → b % 4 = r → (r = 1 ∨ r = 3) →\n    Witness b'' → b'' % 25 = 7 → b'' % 2 = 0 →\n    classCount (fun a => a % 25 = 7 ∧ a % 4 = 4 - r) +\n    badCount (fun a => a % 25 = 7 ∧ (a % 4 = r ∨ a % 2 = 0)) b +\n    badCount (fun a => a % 25 = 18) b'' +\n    vCount (fun x => IsStar x ∧ x % 4 = r) ≤ c7) ∧\n  (∀ b b'' r, Witness b → IsStar b → b % 4 = r → (r = 1 ∨ r = 3) →\n    Witness b'' → b'' % 25 = 18 → b'' % 2 = 0 →\n    classCount (fun a => a % 25 = 18 ∧ a % 4 = 4 - r) +\n    badCount (fun a => a % 25 = 18 ∧ (a % 4 = r ∨ a % 2 = 0)) b +\n    badCount (fun a => a % 25 = 7) b'' +\n    vCount (fun x => IsStar x ∧ x % 4 = r) ≤ c7)"]'),
(6134, 'BusyBeaver.BB_4.R1.H2.R1.H2.R1.H3.R1.H2', 1, 'hananzlt', null::int, '["∀ (M : Machine (Fin 2) (Fin 4)) (q : Fin 4), 2 ≤ q.val →\n  M 0 0 = some (some 1, Stmt.write 1 .right) →\n  M 1 0 = some (some 2, Stmt.write 0 .right) →\n  M 2 0 = some (some q, Stmt.write 0 .left) →\n  M.IsHalting → M.HaltsAfter (Machine.init []) 107\n\n/-- The second write is zero and the left-turn write is one. -/", "∀ (M : Machine (Fin 2) (Fin 4)) (q : Fin 4),\n  M 0 0 = some (some 1, Stmt.write 1 .right) →\n  M 1 0 = some (some 2, Stmt.write 0 .right) →\n  M 2 0 = some (some q, Stmt.write 1 .left) →\n  M.IsHalting → M.HaltsAfter (Machine.init []) 107\n\n/-- The second write is one and the left-turn write is zero. -/", "∀ (M : Machine (Fin 2) (Fin 4)) (q : Fin 4),\n  M 0 0 = some (some 1, Stmt.write 1 .right) →\n  M 1 0 = some (some 2, Stmt.write 1 .right) →\n  M 2 0 = some (some q, Stmt.write 0 .left) →\n  M.IsHalting → M.HaltsAfter (Machine.init []) 107\n\n/-- Both later writes are one. -/", "∀ (M : Machine (Fin 2) (Fin 4)) (q : Fin 4),\n  M 0 0 = some (some 1, Stmt.write 1 .right) →\n  M 1 0 = some (some 2, Stmt.write 1 .right) →\n  M 2 0 = some (some q, Stmt.write 1 .left) →\n  M.IsHalting → M.HaltsAfter (Machine.init []) 107"]'),
(8372, 'LennonPittel.lennon_pittel_conjecture.R3.H2.R1.H2.R1.H1', 1, 'marcusbuffett', null::int, '["∀ (K L : ℕ → ℕ)\n    {B κ : ℝ} (hB : 0 ≤ B) (hκ : 0 ≤ κ)\n    (hK : ∀ᶠ n in atTop, 2 ≤ K n ∧ (K n : ℝ) ≤ κ * Real.sqrt (n : ℝ))\n    (hL : Tendsto L atTop atTop)\n    (hsmallLabel : 24 * κ ^ 2 / 2 + (B + 1) * κ ≤ 1 / 4)\n    (hsmallCompat : Real.exp (κ * (2 * (1 + B))) * (2 * κ * (B / (1 / 128))) ≤ 3 / 32),\n    ∀ᶠ n : ℕ in atTop, ∀ (μ ρ : Matching n) (b A : ℝ),\n      localPivotMeanFloor b A B (K n) μ ρ ≤ᵐ[stableMarkScoreLaw μ]\n        localPivotConditionalMean b A B (K n) (L n) μ ρ\n\n/-- Cowgill''s Gaussian bound for the weighted singleton anchor count. -/", "∀ᶠ n : ℕ in atTop, ∀ (g : ℕ → ℝ) (B : ℝ),\n      (∀ k, 0 ≤ g k) → (∀ k ∈ Finset.Icc 2 n, g k ≤ B) →\n      (∫⁻ p, profileSingletonAnchorLengthWeight p (fun k ↦ ENNReal.ofReal (g k))\n        ∂(uniformProfile n).toMeasure) ≤\n        ENNReal.ofReal (expectedNumStableMatchings n) *\n          ENNReal.ofReal (∑ k ∈ Finset.Icc 2 n, g k * singletonLengthEnvelope n k) +\n          ENNReal.ofReal B * ENNReal.ofReal ((n : ℝ) ^ (-3 : ℝ))\n\n/-- Bad pivot score geometry and bad coexposure scores have vanishing probability. -/", "(Tendsto (fun n ↦ continuousScoreLaw n (goodPivotScoreGeometry n)ᶜ) atTop (𝓝 0)) ∧\n  (∀ {C : ℝ} (hC : 0 ≤ C)\n    (hmean : ∀ᶠ n : ℕ in atTop,\n      expectedNumStableMatchings n ≤ C * ((n : ℝ) * Real.log n)),\n    Tendsto (fun n ↦ continuousScoreLaw n (goodCoexposureScores n)ᶜ) atTop (𝓝 0))\n\n/-- Score walk, band endpoint and female log geometry estimates, and Pittel''s first-moment upper bound. -/", "(∀ {ε : ℝ} (hε : 0 < ε),\n    Tendsto (fun n : ℕ ↦ continuousScoreLaw n\n      {x | ∃ k ≤ n * (n - 1), ε * (n * Real.log n) ≤ |scoreWalkClock x k|})\n      atTop (𝓝 0)) ∧\n  (Tendsto (fun n ↦ continuousScoreLaw n (scoreWalkBandEndpoints n)ᶜ) atTop (𝓝 0)) ∧\n  (Tendsto (fun n ↦ continuousScoreLaw n (goodFemaleLogGeometry n)ᶜ) atTop (𝓝 0)) ∧\n  (∀ᶠ n : ℕ in atTop, expectedNumStableMatchings n ≤\n      meanUpperConstant * ((n : ℝ) * Real.log n))"]'),
(8494, 'CongruentNumber.Tunnell_even.R1.H2.R1.H2.R1.H2.R1.H2', 1, 'ysanatomic', null::int, '["∀ (n : ℕ) (hn : 0<n),\n  letI : NeZero (4*n) := ⟨Nat.ne_of_gt (Nat.mul_pos (by decide) hn)⟩\n  let a := 1+3*(4*n)\n  let ω : ℝ := (∫ x in Ioi (n:ℝ), (Real.sqrt (x^3-(n:ℝ)^2*x))⁻¹)\n  let b (v : ZMod (4*n) × ZMod (4*n)) : GaussianInt := ⟨v.1.val,v.2.val⟩\n  let χ (v : ZMod (4*n) × ZMod (4*n)) : ℤ :=\n    let m := (b v).norm.natAbs\n    if (⟨2,2⟩:GaussianInt) ∣ b v-1 then (if Odd m then jacobiSym n m else 0) else 0\n  ∀ M : PeriodPair, M.ω₁=(ω:ℂ) → M.ω₂=Complex.I*(ω:ℂ) →\n  let t (j : Fin a × Fin a) : ℂ := ((j.1.val:ℂ)*M.ω₁+(j.2.val:ℂ)*M.ω₂)/(a:ℂ)\n  let D (z : ℂ) := ∏ j ∈ Finset.univ.filter (fun j => t j ∉ M.lattice),\n    (M.weierstrassP z-M.weierstrassP (t j))\n  let G (z : ℂ) := ∏ v ∈ Finset.univ.filter (fun v => χ v≠0),\n    D (z+((ω/(4*n):ℝ):ℂ)*(b v:ℂ))^χ v\n  n%8=2 → 2<n → ∀ c : ℚ, c≠0 → logDeriv G 0=(c:ℂ) → ∀ B : ℕ,\n  ∃ p : ℕ, p.Prime ∧ B<p ∧ 3<p ∧ p%4=1 ∧ ¬p∣2*n ∧ ∃ q : GaussianInt, q.norm.natAbs=p ∧\n  let K:=ℚ⟮I⟯\n  let Ω:=algebraicClosure K ℂ\n  let A (r : ℕ) :=\n    let t:=M.ω₁/(q:ℂ)^r\n    (adjoin K {M.weierstrassP t,M.derivWeierstrassP t/2}).comap (algebraicClosure K ℂ).val\n  let T:=A 1\n  let V (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (x y : F) :=\n    let O:=v.adicCompletionIntegers F\n    let L:=v.adicCompletion F\n    ∃ u b : Oˣ, ((u:O):L)=algebraMap F L x ∧ ((b:O):L)=algebraMap F L y ∧\n      maximalIdeal O=Ideal.span {(u:O)-(b:O)}\n  ∃ hT : NumberField T, letI:=hT;\n    ∃ (w : HeightOneSpectrum (𝓞 T)) (z : 𝓞 T), z∈w.asIdeal ∧ (((z:T):Ω):ℂ)=(q:ℂ) ∧\n    ∃ (a : (𝓞 T)ˣ) (b : K), @V T _ hT w a.val.val (algebraMap K T b) ∧\n      ∀ r : ℕ, ∃ h : T≤A (r+1), letI : Algebra T (A (r+1)):=(IntermediateField.inclusion h).toAlgebra;\n        ∃ x : (𝓞 (A (r+1)))ˣ, Algebra.norm T x.val.val=a.val.val", "∀ (n : ℕ) (hn : 0<n), let ω : ℝ := ∫ x in Ioi (n:ℝ), (Real.sqrt (x^3-(n:ℝ)^2*x))⁻¹;\n  ∀ M : PeriodPair, M.ω₁=(ω:ℂ) → M.ω₂=I*(ω:ℂ) →\n  ∀ P : (⟨0,0,0,-(n:ℚ)^2,0⟩ : WeierstrassCurve ℚ).toAffine.Point, ¬IsOfFinAddOrder P →\n  ∃ B : ℕ, ∀ p : ℕ, p.Prime → B<p → p%4=1 → ¬p∣2*n → ∀ q : GaussianInt, q.norm.natAbs=p → ¬(\n  let K:=ℚ⟮I⟯\n  let Ω:=algebraicClosure K ℂ\n  let A (r : ℕ) :=\n    let t:=M.ω₁/(q:ℂ)^r\n    (adjoin K {M.weierstrassP t,M.derivWeierstrassP t/2}).comap (algebraicClosure K ℂ).val\n  let T:=A 1\n  let V (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (x y : F) :=\n    let O:=v.adicCompletionIntegers F\n    let L:=v.adicCompletion F\n    ∃ u b : Oˣ, ((u:O):L)=algebraMap F L x ∧ ((b:O):L)=algebraMap F L y ∧\n      maximalIdeal O=Ideal.span {(u:O)-(b:O)}\n  ∃ hT : NumberField T, letI:=hT;\n    ∃ (w : HeightOneSpectrum (𝓞 T)) (z : 𝓞 T), z∈w.asIdeal ∧ (((z:T):Ω):ℂ)=(q:ℂ) ∧\n    ∃ (a : (𝓞 T)ˣ) (b : K), @V T _ hT w a.val.val (algebraMap K T b) ∧\n      ∀ r : ℕ, ∃ h : T≤A (r+1), letI : Algebra T (A (r+1)):=(IntermediateField.inclusion h).toAlgebra;\n        ∃ x : (𝓞 (A (r+1)))ˣ, Algebra.norm T x.val.val=a.val.val)"]'),
(7960, 'LennonPittel.lennon_pittel_conjecture.R3.H2.R1.H2.R1.H3', 1, 'marcusbuffett', null::int, '["∀ {n L : ℕ} (hn : 0 < n)\n    (hbudget : BackgroundCycleBudget n L) (hLt : (L : ℝ) ≤ Real.log n) (b : ℝ) (K : ℕ),\n    (∑ μ : Matching n, ∑ ν : Matching n, (continuousScoreLaw n).real\n      (scoreIncomparablePairEvent (IsResidualPairGeometry b K L) μ ν)) ≤\n      (Real.exp 72 * (1 + Real.log n)) *\n        (2 * (n : ℝ) ^ 2 * (2 + 4 * Real.log (Real.log n)) +\n          (1600 / Real.log (L : ℝ)) * ((n : ℝ) ^ 2 * (1 + Real.log n)))\n\n/-- The logarithmic cycle cutoff eventually meets Cowgill''s background cycle budget. -/", "∀ᶠ n : ℕ in atTop, BackgroundCycleBudget n (logarithmicCycleCutoff n)"]')
) v(pr, t, rn, h, pts, st);
-- created_at := merge time, only for rows this transaction created (created_at = now())
update oma_reductions r set created_at = v.m from (values
(4551, '2026-11-27T09:15:08Z'::timestamptz),
(4616, '2026-11-27T09:40:22Z'::timestamptz),
(4678, '2026-11-27T09:48:14Z'::timestamptz),
(4876, '2026-11-27T10:11:17Z'::timestamptz),
(4971, '2026-11-27T10:24:59Z'::timestamptz),
(5025, '2026-11-27T10:34:12Z'::timestamptz),
(4990, '2026-11-27T10:52:35Z'::timestamptz),
(4741, '2026-11-27T10:57:41Z'::timestamptz),
(5300, '2026-11-27T11:18:48Z'::timestamptz),
(5362, '2026-11-27T11:26:30Z'::timestamptz),
(5397, '2026-11-27T11:33:25Z'::timestamptz),
(5482, '2026-11-27T11:45:35Z'::timestamptz),
(5505, '2026-11-27T11:47:11Z'::timestamptz),
(5643, '2026-11-27T12:13:16Z'::timestamptz),
(5747, '2026-11-27T12:24:43Z'::timestamptz),
(6134, '2026-11-27T13:06:36Z'::timestamptz),
(8372, '2026-11-27T17:00:19Z'::timestamptz),
(8494, '2026-11-27T19:51:23Z'::timestamptz),
(7960, '2026-11-27T21:32:50Z'::timestamptz)
) v(pr, m) where r.pr_url = 'https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/' || v.pr and r.created_at = now();
update oma_steps s set created_at = r.created_at from oma_reductions r where s.reduction = r.id and s.created_at = now();
update oma_events e set created_at = r.created_at from oma_reductions r
  where e.kind = 'reduced' and e.created_at = now() and e.problem_id = r.problem_id and e.detail = r.id || ' into ' || r.hyps || ' steps';
commit;

-- ===== batch 6: reductions, dependency level 3 (16 PRs: 5268 .. ) =====
begin;
select v.pr, case
  when exists (select 1 from oma_reductions r where r.pr_url = 'https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/' || v.pr) then json_build_object('skip','pr_exists')
  when exists (select 1 from oma_reductions r where r.id = v.t || '.R' || v.rn) then json_build_object('skip','id_exists')
  when v.pts is null and not exists (select 1 from oma_steps s where s.id = v.t) then json_build_object('error','unknown_target')
  else oma_register_reduction(v.t || '.R' || v.rn, v.t, v.h, 'https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/' || v.pr,
         'OMAReductions.R_' || regexp_replace(v.t || '.R' || v.rn, '[^A-Za-z0-9]', '_', 'g'), v.st::json,
         coalesce(v.pts, (select s.points from oma_steps s where s.id = v.t))) end r
from (values
(5268, 'BusyBeaver.BB_4.R1.H2.R1.H2.R1.H3.R1.H3.R1.H1', 1, 'marcusbuffett', null::int, '["∀ (a b c : Fin 2) (q h : Fin 4) (u : Fin 4 → Fin 4 × Stmt (Fin 2)),\n  let v : Fin 4 → Fin 4 × Stmt (Fin 2) :=\n    ![(1,.write 1 .right),(2,.write a .right),(3,.write b .right),(q,.write c .left)]\n  let N : Machine (Fin 2) (Fin 4) := fun r s =>\n    if s=0 then some (some (v r).1,(v r).2) else if r=h then none else some (some (u r).1,(u r).2)\n  (∃ r T,N.multiStep (Machine.init []) 107 = some ⟨some r,T⟩) →\n  ∃ (n m : ℕ) (x : Fin n) (y : Fin m) (L : Fin 2 → Fin n → Fin n)\n      (R : Fin 2 → Fin m → Fin m) (S : Fin 4 → Fin 2 → Fin n → Fin m → Bool),\n      L 0 x=x ∧ R 0 y=y ∧ S 0 0 x y=true ∧\n      ∀ q a s t i j, S q a (L s i) (R t j)=true →\n        ∃ r w d, N q a=some (some r,Stmt.write w d) ∧\n          (match d with\n           | .left => S r s i (R w (R t j))\n           | .right => S r t (L w (L s i)) j) = true\n\n/-- Simultaneous finite readers for the intersection of a family of live transition\nrelations; the family is allowed to be empty when the original machine is total. -/", "let cert (M : Machine (Fin 2) (Fin 4)) : Prop := ∃ (n m : ℕ) (x : Fin n) (y : Fin m) (L : Fin 2 → Fin n → Fin n)\n      (R : Fin 2 → Fin m → Fin m) (S : Fin 4 → Fin 2 → Fin n → Fin m → Bool),\n      L 0 x=x ∧ R 0 y=y ∧ S 0 0 x y=true ∧\n      ∀ q a s t i j, S q a (L s i) (R t j)=true →\n        ∃ r w d, M q a=some (some r,Stmt.write w d) ∧\n          (match d with\n           | .left => S r s i (R w (R t j))\n           | .right => S r t (L w (L s i)) j) = true\n  ∀ (I : Type) [Fintype I] (F : I → Machine (Fin 2) (Fin 4)) (M : Machine (Fin 2) (Fin 4)),\n    (∀ i, cert (F i)) →\n    (∀ q a, (∀ i, ∃ r st, F i q a = some (some r,st)) →\n      ∃ r st, M q a = some (some r,st) ∧ ∀ i,F i q a = some (some r,st)) → cert M"]'),
(5466, 'Arxiv.1601.03081.crystals_components_unique.R1.H2.R1.H2.R1.H1', 1, 'senamakel', null::int, '["∀ g y z d : ℕ,\n    1 < g → 33 ≤ y → Odd g → Odd y → Odd z → g*y ≤ z →\n    (g+1)*(y*z+1) ∣ (g+y*z)^2 →\n    0 < d → d < 2*(y-1) → d % 2 = 0 →\n    (g+1 ∣ ((y+1)*(d+(y-1)*y*(1+2*y)))^2) →\n    (g*y+1 ∣ ((y+1)*(d+(y-1)*(y+2)))^2) →\n    (∀ p : ℕ, p.Prime → p ∣ g*y*z → p % 8 = 1 ∨ p % 8 = 7) →\n    ((y : ℤ) ∣ ((d : ℤ)-3)^2-8) → 66 ≤ d →\n    (g*y+z)^2 = 4*((g*y+1)*(z+1)) → g = z", "∀ g y z d q : ℕ,\n    1 < g → 33 ≤ y → Odd g → Odd y → Odd z → g*y ≤ z →\n    (g+1)*(y*z+1) ∣ (g+y*z)^2 →\n    0 < d → d < 2*(y-1) → d % 2 = 0 →\n    (g+1 ∣ ((y+1)*(d+(y-1)*y*(1+2*y)))^2) →\n    (g*y+1 ∣ ((y+1)*(d+(y-1)*(y+2)))^2) →\n    5 ≤ q → (g*y+z)^2 = q*((g*y+1)*(z+1)) → g = z"]'),
(5546, 'Arxiv.1601.03081.crystals_components_unique.R1.H2.R1.H2.R1.H2', 1, 'senamakel', null::int, '["∀ g y z : ℕ, 1 < g → 13 ≤ y →\n    Odd g → Odd y → Odd z → g*y ≤ 3*z → Nat.Coprime 3 y →\n    (g*3+1)*(y*z+1) ∣ (g*3+y*z)^2 →\n    (g*y+1)*(3*z+1) ∣ (g*y+3*z)^2 → g = z", "∀ g x y z : ℕ, 1 < g → 5 ≤ x → x < y →\n    Odd g → Odd x → Odd y → Odd z → g*y ≤ x*z → Nat.Coprime x y →\n    (g*x+1)*(y*z+1) ∣ (g*x+y*z)^2 →\n    (g*y+1)*(x*z+1) ∣ (g*y+x*z)^2 → g = z"]'),
(5845, 'Erdos930.erdos_930.variants.consecutive_integers.R1.H4.R1.H2.R1.H1.R1.H3', 1, 'marcusbuffett', null::int, '["∀ n : ℕ, 5000000 ≤ n → n ≤ ⌊exp 40⌋₊ →\n    primorial n * n^(n^2) ≤ (n+1)^(n^2)\n\n/-- The one-sided error at the b=40 entry of the explicit Chebyshev table. -/", "∀ x : ℝ, exp 40 ≤ x →\n    Chebyshev.theta x - x ≤ x/40000000\n\n/-- The explicit exponentially decreasing estimate for psi, rounded outwards. -/", "∀ x : ℝ, exp 40 ≤ x →\n    Chebyshev.psi x - x ≤ x * (10 * (sqrt (log x))^3 * exp (-(4/5)*sqrt (log x)))\n\n/-- Comparison of the constant and exponentially decreasing relative errors. -/", "∀ y : ℝ, 0 ≤ y →\n    min (1/40000000:ℝ) (10*y^3*exp (-(4/5)*y)) * (5*y^4) ≤ 1"]'),
(5813, 'Arxiv.1601.03081.crystals_components_unique.R1.H1.R1.H2.R1.H1', 1, 'senamakel', null::int, '["∀ a c m p t : ℕ, a < c → 21 ≤ m → Odd m → a.Coprime c →\n    c ≤ m*a → 3 ≤ a → 5 ≤ c →\n    (a+m*c)^2 = p*((a+1)*(m*c+1)) →\n    (c+m*a)^2 = 4*((c+1)*(m*a+1)) →\n    c+1 = 2*t^2 → m*a+1 = 2*(t+1)^2 → Nat.Coprime c (m*a) →\n    (∀ ell : ℕ, ell.Prime → ell ∣ m ∨ ell ∣ c ∨ ell ∣ (m*a) →\n      ell % 8 = 1 ∨ ell % 8 = 7) →\n    ((m*c : ℤ)+1) ∣ ((a : ℤ)-1)^2 → 16 ≤ p →\n    c % 8 = 1 ∧ (m*a) % 8 = 7 → Odd t → False\n\n/-- The non-diagonal quotient-four case with even square parameter. -/", "∀ a c m p t : ℕ, a < c → 21 ≤ m → Odd m → a.Coprime c →\n    c ≤ m*a → 3 ≤ a → 5 ≤ c →\n    (a+m*c)^2 = p*((a+1)*(m*c+1)) →\n    (c+m*a)^2 = 4*((c+1)*(m*a+1)) →\n    c+1 = 2*t^2 → m*a+1 = 2*(t+1)^2 → Nat.Coprime c (m*a) →\n    (∀ ell : ℕ, ell.Prime → ell ∣ m ∨ ell ∣ c ∨ ell ∣ (m*a) →\n      ell % 8 = 1 ∨ ell % 8 = 7) →\n    ((m*c : ℤ)+1) ∣ ((a : ℤ)-1)^2 → 16 ≤ p →\n    c % 8 = 7 ∧ (m*a) % 8 = 1 → Even t → False"]'),
(6154, 'BusyBeaver.BB_4.R1.H2.R1.H1.R1.H3.R1.H2.R1.H4', 1, 'marcusbuffett', null::int, '["let A := Fin 2\n  let Q := Fin 4\n  let entry (z : ℕ) : Machine A Q := fun r s =>\n    let k := z / 17^(2*r.val+s.val) % 17\n    if k=16 then none else some (some (Fin.ofNat 4 (k/4)),\n      .write (Fin.ofNat 2 (k/2)) (if k%2=0 then .left else .right))\n  ∀ M : Machine A Q,\n  let run := M.multiStep (Machine.init [])\n  M 0 0=some (some 1,.write 0 .right) →\n  M 1 0=some (some 2,.write 1 .left) →\n  (∃ q t,run 107=some ⟨some q,t⟩) →\n  (∀ q a,(∃ i < 107,∃ t : Tape A,\n    run i=some ⟨some q,t⟩ ∧ t.head=a) ↔\n    ∃ q'' z,M q a=some (some q'',z)) →\n  (∀ q a,M q a=none ∨ ∃ q'' z,M q a=some (some q'',z)) →\n  (∀ i p q a (side : Bool)\n      (w : List A) f,0<p → i+p≤107 →\n    let c := fun t : ListBlank A =>\n      let free := w.foldr ListBlank.cons t\n      (⟨some q,if side then ⟨a,free,f⟩ else ⟨a,f,free⟩⟩ : Cfg A Q)\n    (∃ t,run i=some (c t)) →\n    ¬ ∀ t,∃ u,M.multiStep (c t) p=some (c u)) →\n  (∃ k ≤ 20,∀ u v,M.multiStep u k=some v → (M.step v).isSome) ∨\n  (∃ z ∈ ([192926630,394870650,515740378,1336417724,1408830431,1627390098,\n  1689441169,2446657396,2452336858,2460855813,2460855983,2930234279,\n  3133858477,3267241361,3267325035,3267408318,3267408386,3268076724,\n  3268179812,3268243766,3325136085,3330584823,3330638645,3475567181,\n  3475567351,3672067699,3673413691,3673413861,4079576433,4093775003,\n  4100731862,4498257380,4684022874,4953712200,4972106404,4972170205,\n  5435078199,5439716071,5439804454,5440806757,5453953928,5537278425,\n  5792616725,6328050068,6695802976,6734875946,6734876082,6734876116,\n  6745900956,6746235074,6775658997,6778655859,6852444036]),M=entry z) ∨\n    ∃ (n m : ℕ) (x : Fin n) (y : Fin m) (L : A → Fin n → Fin n)\n      (R : A → Fin m → Fin m) (S : Q → A → Fin n → Fin m → Bool),\n      L 0 x=x ∧ R 0 y=y ∧ S 0 0 x y=true ∧\n      ∀ q a s t i j,S q a (L s i) (R t j)=true →\n        ∃ r w d,M q a=some (some r,Stmt.write w d) ∧\n          (match d with\n           | .left => S r s i (R w (R t j))\n           | .right => S r t (L w (L s i)) j)=true\n\n/-- Nontermination of the residual concrete tables, in state-major base 17.\nDigits 0–15 encode four times the new state plus twice the write bit plus\nthe direction bit. Digit 16 is undefined. -/", "let entry (z : ℕ) (r : Fin 4) (s : Fin 2) : Option (Option (Fin 4) × Stmt (Fin 2)) :=\n    let k := z / 17^(2*r.val+s.val) % 17\n    if k=16 then none else some (some (Fin.ofNat 4 (k/4)),\n      .write (Fin.ofNat 2 (k/2)) (if k%2=0 then .left else .right))\n  ∀ z ∈ ([192926630, 394870650, 515740378, 1336417724, 1408830431, 1627390098,\n       1689441169, 2446657396, 2452336858, 2460855813, 2460855983, 2930234279,\n       3133858477, 3267241361, 3267325035, 3267408318, 3267408386, 3268076724,\n       3268179812, 3268243766, 3325136085, 3330584823, 3330638645, 3475567181,\n       3475567351, 3672067699, 3673413691, 3673413861, 4079576433, 4093775003,\n       4100731862, 4498257380, 4684022874, 4953712200, 4972106404, 4972170205,\n       5435078199, 5439716071, 5439804454, 5440806757, 5453953928, 5537278425,\n       5792616725, 6328050068, 6695802976, 6734875946, 6734876082, 6734876116,\n       6745900956, 6746235074, 6775658997, 6778655859, 6852444036] : List ℕ), ¬ Machine.IsHalting (entry z)"]'),
(6132, 'BusyBeaver.BB_4.R1.H2.R1.H2.R1.H3.R1.H1.R1.H1', 1, 'pageman', null::int, '["∀ (M : Machine (Fin 2) (Fin 4)) (q : Fin 4),\n    q.val ≤ 1 →\n    M 0 0 = some (some 1, Stmt.write 1 Dir.right) →\n    M 1 0 = some (some q, Stmt.write 0 Dir.left) →\n    M.IsHalting → M.HaltsAfter (Machine.init []) 107", "∀ (M : Machine (Fin 2) (Fin 4)) (q : Fin 4),\n    q.val ≤ 1 →\n    M 0 0 = some (some 1, Stmt.write 1 Dir.right) →\n    M 1 0 = some (some q, Stmt.write 1 Dir.left) →\n    M.IsHalting → M.HaltsAfter (Machine.init []) 107"]'),
(6306, 'BusyBeaver.BB_4.R1.H2.R1.H2.R1.H3.R1.H1.R1.H2', 1, 'pageman', null::int, '["∀ (M : Machine (Fin 2) (Fin 4)),\n    M 0 0 = some (some 1, Stmt.write 1 Dir.right) →\n    M 1 0 = some (some 2, Stmt.write 0 Dir.left) →\n    M.IsHalting → M.HaltsAfter (Machine.init []) 107", "∀ (M : Machine (Fin 2) (Fin 4)),\n    M 0 0 = some (some 1, Stmt.write 1 Dir.right) →\n    M 1 0 = some (some 2, Stmt.write 1 Dir.left) →\n    M.IsHalting → M.HaltsAfter (Machine.init []) 107"]'),
(6858, 'Erdos173.erdos_173.R1.H2.R1.H1.R1.H2.R1.H1.R1.H2', 1, 'marcusbuffett', null::int, '["∀ (E : IntermediateField ℚ ℂ) (F : IntermediateField ℚ ℝ), ∀ hc : Countable E,\n    ∀ hF : (∀ z : ℂ, z ∈ E ↔ z.re ∈ F ∧ z.im ∈ F),\n    ∀ ha : (∀ p : Polynomial ℂ, p ≠ 0 → (∀ n, p.coeff n ∈ E) → ∀ z, p.eval z = 0 → z ∈ E),\n    ∀ ht : (∀ Q : Finset ℂ, (∀ q ∈ Q, q ∈ E ∧ ‖q‖ = 1) →\n      ∃ S : Finset ℂ, (∀ s ∈ S, s ∈ E ∧ ‖s‖ = 1) ∧\n      ∀ j : ℂ → ℂ, (∀ s ∈ S, j s ∈ Q) →\n        (1 : ℂ) ∈ Submodule.span ℚ ((fun s => j s*s) '''' (S : Set ℂ)) ∧\n        Complex.I ∈ Submodule.span ℚ ((fun s => j s*s) '''' (S : Set ℂ))),\n    letI : Carrier := ⟨E,F,hc,hF,ha,ht⟩\n\n    ∀ (μ : Measure D) [IsProbabilityMeasure μ] [ErgodicSMul K D μ], IsWild μ →\n      ∃ (Y : Type) (mY : MeasurableSpace Y) (aY : MulAction K Y),\n        letI := mY\n        letI := aY\n        StandardBorelSpace Y ∧ Nonempty Y ∧ MeasurableConstSMul K Y ∧ ∃ (q : D → Y) (hq : Measurable q),\n        (∀ k : K, ∀ᵐ x ∂μ, q (k • x) = k • q x) ∧\n        ErgodicSMul K (D×D) (square μ q hq) ∧ IsWild (difference μ q)\n\n/-- Vanishing of each nontrivial conditional Fourier coefficient on such a factor. -/", "∀ (E : IntermediateField ℚ ℂ) (F : IntermediateField ℚ ℝ), ∀ hc : Countable E,\n    ∀ hF : (∀ z : ℂ, z ∈ E ↔ z.re ∈ F ∧ z.im ∈ F),\n    ∀ ha : (∀ p : Polynomial ℂ, p ≠ 0 → (∀ n, p.coeff n ∈ E) → ∀ z, p.eval z = 0 → z ∈ E),\n    ∀ ht : (∀ Q : Finset ℂ, (∀ q ∈ Q, q ∈ E ∧ ‖q‖ = 1) →\n      ∃ S : Finset ℂ, (∀ s ∈ S, s ∈ E ∧ ‖s‖ = 1) ∧\n      ∀ j : ℂ → ℂ, (∀ s ∈ S, j s ∈ Q) →\n        (1 : ℂ) ∈ Submodule.span ℚ ((fun s => j s*s) '''' (S : Set ℂ)) ∧\n        Complex.I ∈ Submodule.span ℚ ((fun s => j s*s) '''' (S : Set ℂ))),\n    letI : Carrier := ⟨E,F,hc,hF,ha,ht⟩\n\n    ∀ (μ : Measure D) [IsProbabilityMeasure μ] [ErgodicSMul K D μ]\n      (Y : Type) [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]\n      [MulAction K Y] [MeasurableConstSMul K Y] (q : D → Y) (hq : Measurable q), (∀ k : K, ∀ᵐ x ∂μ, q (k • x) = k • q x) →\n      ErgodicSMul K (D×D) (square μ q hq) → IsWild (difference μ q) →\n      ∀ a : E, a ≠ 0 → ∀ᵐ w ∂μ.map q, ∫ d, (eval a d : ℂ) ∂condDistrib id q μ w = 0"]'),
(6863, 'BusyBeaver.BB_4.R1.H2.R1.H2.R1.H3.R1.H2.R1.H1', 1, 'pageman', null::int, '["∀ (M : Machine (Fin 2) (Fin 4)),\n  M 0 0 = some (some 1, Stmt.write 1 Dir.right) →\n  M 1 0 = some (some 2, Stmt.write 0 Dir.right) →\n  M 2 0 = some (some 2, Stmt.write 0 Dir.left) →\n  (∃ q t, M.multiStep (Machine.init []) 107 = some ⟨some q, t⟩) →\n  (∀ q a, (∃ i < 107, ∃ t : Tape (Fin 2),\n    M.multiStep (Machine.init []) i = some ⟨some q, t⟩ ∧ t.head = a) ↔\n    ∃ q'' z, M q a = some (some q'', z)) →\n  (∀ q a, M q a = none ∨ ∃ q'' z, M q a = some (some q'', z)) →\n  (∃ q a, M q a = none) →\n  (∀ (i p : ℕ) (q : Fin 4) (a : Fin 2) (side : Bool)\n      (near : List (Fin 2)) (fixed : ListBlank (Fin 2)), 0 < p → i + p ≤ 107 →\n    let cfg := fun tail : ListBlank (Fin 2) =>\n      let free := near.foldr ListBlank.cons tail\n      (⟨some q, if side then ⟨a, free, fixed⟩ else ⟨a, fixed, free⟩⟩ : Cfg (Fin 2) (Fin 4))\n    (∃ tail, M.multiStep (Machine.init []) i = some (cfg tail)) →\n    ¬ ∀ tail, ∃ tail'', M.multiStep (cfg tail) p = some (cfg tail'')) →\n  ¬ M.IsHalting", "∀ (M : Machine (Fin 2) (Fin 4)),\n  M 0 0 = some (some 1, Stmt.write 1 Dir.right) →\n  M 1 0 = some (some 2, Stmt.write 0 Dir.right) →\n  M 2 0 = some (some 3, Stmt.write 0 Dir.left) →\n  (∃ q t, M.multiStep (Machine.init []) 107 = some ⟨some q, t⟩) →\n  (∀ q a, (∃ i < 107, ∃ t : Tape (Fin 2),\n    M.multiStep (Machine.init []) i = some ⟨some q, t⟩ ∧ t.head = a) ↔\n    ∃ q'' z, M q a = some (some q'', z)) →\n  (∀ q a, M q a = none ∨ ∃ q'' z, M q a = some (some q'', z)) →\n  (∃ q a, M q a = none) →\n  (∀ (i p : ℕ) (q : Fin 4) (a : Fin 2) (side : Bool)\n      (near : List (Fin 2)) (fixed : ListBlank (Fin 2)), 0 < p → i + p ≤ 107 →\n    let cfg := fun tail : ListBlank (Fin 2) =>\n      let free := near.foldr ListBlank.cons tail\n      (⟨some q, if side then ⟨a, free, fixed⟩ else ⟨a, fixed, free⟩⟩ : Cfg (Fin 2) (Fin 4))\n    (∃ tail, M.multiStep (Machine.init []) i = some (cfg tail)) →\n    ¬ ∀ tail, ∃ tail'', M.multiStep (cfg tail) p = some (cfg tail'')) →\n  ¬ M.IsHalting"]'),
(7367, 'BusyBeaver.BB_4.R1.H2.R1.H2.R1.H3.R1.H2.R1.H3', 1, 'hananzlt', null::int, '["∀ M : Machine (Fin 2) (Fin 4),\n  M 0 0 = some (some 1, Stmt.write 1 .right) →\n  M 1 0 = some (some 2, Stmt.write 1 .right) →\n  M 2 0 = some (some 0, Stmt.write 0 .left) →\n  M.IsHalting → M.HaltsAfter (Machine.init []) 107", "∀ (M : Machine (Fin 2) (Fin 4)) (q : Fin 4),\n  (q = 1 ∨ q = 2) →\n  M 0 0 = some (some 1, Stmt.write 1 .right) →\n  M 1 0 = some (some 2, Stmt.write 1 .right) →\n  M 2 0 = some (some q, Stmt.write 0 .left) →\n  M.IsHalting → M.HaltsAfter (Machine.init []) 107", "∀ M : Machine (Fin 2) (Fin 4),\n  M 0 0 = some (some 1, Stmt.write 1 .right) →\n  M 1 0 = some (some 2, Stmt.write 1 .right) →\n  M 2 0 = some (some 3, Stmt.write 0 .left) →\n  M.IsHalting → M.HaltsAfter (Machine.init []) 107"]'),
(6963, 'BusyBeaver.BB_4.R1.H2.R1.H2.R1.H3.R1.H2.R1.H2', 1, 'pageman', null::int, '["∀ (M : Machine (Fin 2) (Fin 4)),\n  M 0 0 = some (some 1, Stmt.write 1 Dir.right) →\n  M 1 0 = some (some 2, Stmt.write 0 Dir.right) →\n  M 2 0 = some (some 0, Stmt.write 1 Dir.left) →\n  (∃ q t, M.multiStep (Machine.init []) 107 = some ⟨some q, t⟩) →\n  (∀ q a, (∃ i < 107, ∃ t : Tape (Fin 2),\n    M.multiStep (Machine.init []) i = some ⟨some q, t⟩ ∧ t.head = a) ↔\n    ∃ q'' z, M q a = some (some q'', z)) →\n  (∀ q a, M q a = none ∨ ∃ q'' z, M q a = some (some q'', z)) →\n  (∃ q a, M q a = none) →\n  (∀ (i p : ℕ) (q : Fin 4) (a : Fin 2) (side : Bool)\n      (near : List (Fin 2)) (fixed : ListBlank (Fin 2)), 0 < p → i + p ≤ 107 →\n    let cfg := fun tail : ListBlank (Fin 2) =>\n      let free := near.foldr ListBlank.cons tail\n      (⟨some q, if side then ⟨a, free, fixed⟩ else ⟨a, fixed, free⟩⟩ : Cfg (Fin 2) (Fin 4))\n    (∃ tail, M.multiStep (Machine.init []) i = some (cfg tail)) →\n    ¬ ∀ tail, ∃ tail'', M.multiStep (cfg tail) p = some (cfg tail'')) →\n  ¬ M.IsHalting", "∀ (M : Machine (Fin 2) (Fin 4)),\n  M 0 0 = some (some 1, Stmt.write 1 Dir.right) →\n  M 1 0 = some (some 2, Stmt.write 0 Dir.right) →\n  M 2 0 = some (some 1, Stmt.write 1 Dir.left) →\n  (∃ q t, M.multiStep (Machine.init []) 107 = some ⟨some q, t⟩) →\n  (∀ q a, (∃ i < 107, ∃ t : Tape (Fin 2),\n    M.multiStep (Machine.init []) i = some ⟨some q, t⟩ ∧ t.head = a) ↔\n    ∃ q'' z, M q a = some (some q'', z)) →\n  (∀ q a, M q a = none ∨ ∃ q'' z, M q a = some (some q'', z)) →\n  (∃ q a, M q a = none) →\n  (∀ (i p : ℕ) (q : Fin 4) (a : Fin 2) (side : Bool)\n      (near : List (Fin 2)) (fixed : ListBlank (Fin 2)), 0 < p → i + p ≤ 107 →\n    let cfg := fun tail : ListBlank (Fin 2) =>\n      let free := near.foldr ListBlank.cons tail\n      (⟨some q, if side then ⟨a, free, fixed⟩ else ⟨a, fixed, free⟩⟩ : Cfg (Fin 2) (Fin 4))\n    (∃ tail, M.multiStep (Machine.init []) i = some (cfg tail)) →\n    ¬ ∀ tail, ∃ tail'', M.multiStep (cfg tail) p = some (cfg tail'')) →\n  ¬ M.IsHalting", "∀ (M : Machine (Fin 2) (Fin 4)),\n  M 0 0 = some (some 1, Stmt.write 1 Dir.right) →\n  M 1 0 = some (some 2, Stmt.write 0 Dir.right) →\n  M 2 0 = some (some 2, Stmt.write 1 Dir.left) →\n  (∃ q t, M.multiStep (Machine.init []) 107 = some ⟨some q, t⟩) →\n  (∀ q a, (∃ i < 107, ∃ t : Tape (Fin 2),\n    M.multiStep (Machine.init []) i = some ⟨some q, t⟩ ∧ t.head = a) ↔\n    ∃ q'' z, M q a = some (some q'', z)) →\n  (∀ q a, M q a = none ∨ ∃ q'' z, M q a = some (some q'', z)) →\n  (∃ q a, M q a = none) →\n  (∀ (i p : ℕ) (q : Fin 4) (a : Fin 2) (side : Bool)\n      (near : List (Fin 2)) (fixed : ListBlank (Fin 2)), 0 < p → i + p ≤ 107 →\n    let cfg := fun tail : ListBlank (Fin 2) =>\n      let free := near.foldr ListBlank.cons tail\n      (⟨some q, if side then ⟨a, free, fixed⟩ else ⟨a, fixed, free⟩⟩ : Cfg (Fin 2) (Fin 4))\n    (∃ tail, M.multiStep (Machine.init []) i = some (cfg tail)) →\n    ¬ ∀ tail, ∃ tail'', M.multiStep (cfg tail) p = some (cfg tail'')) →\n  ¬ M.IsHalting", "∀ (M : Machine (Fin 2) (Fin 4)),\n  M 0 0 = some (some 1, Stmt.write 1 Dir.right) →\n  M 1 0 = some (some 2, Stmt.write 0 Dir.right) →\n  M 2 0 = some (some 3, Stmt.write 1 Dir.left) →\n  (∃ q t, M.multiStep (Machine.init []) 107 = some ⟨some q, t⟩) →\n  (∀ q a, (∃ i < 107, ∃ t : Tape (Fin 2),\n    M.multiStep (Machine.init []) i = some ⟨some q, t⟩ ∧ t.head = a) ↔\n    ∃ q'' z, M q a = some (some q'', z)) →\n  (∀ q a, M q a = none ∨ ∃ q'' z, M q a = some (some q'', z)) →\n  (∃ q a, M q a = none) →\n  (∀ (i p : ℕ) (q : Fin 4) (a : Fin 2) (side : Bool)\n      (near : List (Fin 2)) (fixed : ListBlank (Fin 2)), 0 < p → i + p ≤ 107 →\n    let cfg := fun tail : ListBlank (Fin 2) =>\n      let free := near.foldr ListBlank.cons tail\n      (⟨some q, if side then ⟨a, free, fixed⟩ else ⟨a, fixed, free⟩⟩ : Cfg (Fin 2) (Fin 4))\n    (∃ tail, M.multiStep (Machine.init []) i = some (cfg tail)) →\n    ¬ ∀ tail, ∃ tail'', M.multiStep (cfg tail) p = some (cfg tail'')) →\n  ¬ M.IsHalting"]'),
(7558, 'BusyBeaver.BB_4.R1.H2.R1.H2.R1.H3.R1.H2.R1.H4', 1, 'pageman', null::int, '["∀ (M : Machine (Fin 2) (Fin 4)),\n  M 0 0 = some (some 1, Stmt.write 1 Dir.right) →\n  M 1 0 = some (some 2, Stmt.write 1 Dir.right) →\n  M 2 0 = some (some 0, Stmt.write 1 Dir.left) →\n  (∃ q t, M.multiStep (Machine.init []) 107 = some ⟨some q, t⟩) →\n  (∀ q a, (∃ i < 107, ∃ t : Tape (Fin 2),\n    M.multiStep (Machine.init []) i = some ⟨some q, t⟩ ∧ t.head = a) ↔\n    ∃ q'' z, M q a = some (some q'', z)) →\n  (∀ q a, M q a = none ∨ ∃ q'' z, M q a = some (some q'', z)) →\n  (∃ q a, M q a = none) →\n  (∀ (i p : ℕ) (q : Fin 4) (a : Fin 2) (side : Bool)\n      (near : List (Fin 2)) (fixed : ListBlank (Fin 2)), 0 < p → i + p ≤ 107 →\n    let cfg := fun tail : ListBlank (Fin 2) =>\n      let free := near.foldr ListBlank.cons tail\n      (⟨some q, if side then ⟨a, free, fixed⟩ else ⟨a, fixed, free⟩⟩ : Cfg (Fin 2) (Fin 4))\n    (∃ tail, M.multiStep (Machine.init []) i = some (cfg tail)) →\n    ¬ ∀ tail, ∃ tail'', M.multiStep (cfg tail) p = some (cfg tail'')) →\n  ¬ M.IsHalting", "∀ (M : Machine (Fin 2) (Fin 4)),\n  M 0 0 = some (some 1, Stmt.write 1 Dir.right) →\n  M 1 0 = some (some 2, Stmt.write 1 Dir.right) →\n  M 2 0 = some (some 1, Stmt.write 1 Dir.left) →\n  (∃ q t, M.multiStep (Machine.init []) 107 = some ⟨some q, t⟩) →\n  (∀ q a, (∃ i < 107, ∃ t : Tape (Fin 2),\n    M.multiStep (Machine.init []) i = some ⟨some q, t⟩ ∧ t.head = a) ↔\n    ∃ q'' z, M q a = some (some q'', z)) →\n  (∀ q a, M q a = none ∨ ∃ q'' z, M q a = some (some q'', z)) →\n  (∃ q a, M q a = none) →\n  (∀ (i p : ℕ) (q : Fin 4) (a : Fin 2) (side : Bool)\n      (near : List (Fin 2)) (fixed : ListBlank (Fin 2)), 0 < p → i + p ≤ 107 →\n    let cfg := fun tail : ListBlank (Fin 2) =>\n      let free := near.foldr ListBlank.cons tail\n      (⟨some q, if side then ⟨a, free, fixed⟩ else ⟨a, fixed, free⟩⟩ : Cfg (Fin 2) (Fin 4))\n    (∃ tail, M.multiStep (Machine.init []) i = some (cfg tail)) →\n    ¬ ∀ tail, ∃ tail'', M.multiStep (cfg tail) p = some (cfg tail'')) →\n  ¬ M.IsHalting", "∀ (M : Machine (Fin 2) (Fin 4)),\n  M 0 0 = some (some 1, Stmt.write 1 Dir.right) →\n  M 1 0 = some (some 2, Stmt.write 1 Dir.right) →\n  M 2 0 = some (some 2, Stmt.write 1 Dir.left) →\n  (∃ q t, M.multiStep (Machine.init []) 107 = some ⟨some q, t⟩) →\n  (∀ q a, (∃ i < 107, ∃ t : Tape (Fin 2),\n    M.multiStep (Machine.init []) i = some ⟨some q, t⟩ ∧ t.head = a) ↔\n    ∃ q'' z, M q a = some (some q'', z)) →\n  (∀ q a, M q a = none ∨ ∃ q'' z, M q a = some (some q'', z)) →\n  (∃ q a, M q a = none) →\n  (∀ (i p : ℕ) (q : Fin 4) (a : Fin 2) (side : Bool)\n      (near : List (Fin 2)) (fixed : ListBlank (Fin 2)), 0 < p → i + p ≤ 107 →\n    let cfg := fun tail : ListBlank (Fin 2) =>\n      let free := near.foldr ListBlank.cons tail\n      (⟨some q, if side then ⟨a, free, fixed⟩ else ⟨a, fixed, free⟩⟩ : Cfg (Fin 2) (Fin 4))\n    (∃ tail, M.multiStep (Machine.init []) i = some (cfg tail)) →\n    ¬ ∀ tail, ∃ tail'', M.multiStep (cfg tail) p = some (cfg tail'')) →\n  ¬ M.IsHalting", "∀ (M : Machine (Fin 2) (Fin 4)),\n  M 0 0 = some (some 1, Stmt.write 1 Dir.right) →\n  M 1 0 = some (some 2, Stmt.write 1 Dir.right) →\n  M 2 0 = some (some 3, Stmt.write 1 Dir.left) →\n  (∃ q t, M.multiStep (Machine.init []) 107 = some ⟨some q, t⟩) →\n  (∀ q a, (∃ i < 107, ∃ t : Tape (Fin 2),\n    M.multiStep (Machine.init []) i = some ⟨some q, t⟩ ∧ t.head = a) ↔\n    ∃ q'' z, M q a = some (some q'', z)) →\n  (∀ q a, M q a = none ∨ ∃ q'' z, M q a = some (some q'', z)) →\n  (∃ q a, M q a = none) →\n  (∀ (i p : ℕ) (q : Fin 4) (a : Fin 2) (side : Bool)\n      (near : List (Fin 2)) (fixed : ListBlank (Fin 2)), 0 < p → i + p ≤ 107 →\n    let cfg := fun tail : ListBlank (Fin 2) =>\n      let free := near.foldr ListBlank.cons tail\n      (⟨some q, if side then ⟨a, free, fixed⟩ else ⟨a, fixed, free⟩⟩ : Cfg (Fin 2) (Fin 4))\n    (∃ tail, M.multiStep (Machine.init []) i = some (cfg tail)) →\n    ¬ ∀ tail, ∃ tail'', M.multiStep (cfg tail) p = some (cfg tail'')) →\n  ¬ M.IsHalting"]'),
(7918, 'RiemannHypothesis.robin_criterion.R1.H1.R1.H2.R1.H2.R1.H1', 1, 'marcusbuffett', null::int, '["RiemannHypothesis → ∀ s : ℝ, 366 ≤ s →\n  2*s^(-(1:ℝ))*(log s)⁻¹-s^(-(1:ℝ))*((log s)^2)⁻¹-\n    (9/4:ℝ)*s^(-(3/2:ℝ))*(log s)⁻¹-log (2*Real.pi)*s^(-(2:ℝ))*(log s)⁻¹ ≤ (∫ t in Set.Ioi s, ((2*log t+1)/(t^3*(log t)^2))*Chebyshev.theta t)\n\n/-- Upper tail estimate, with the absolute sum over nontrivial zeros. -/", "RiemannHypothesis → ∀ b : ℝ, 2 ≤ b →\n  (∫ t in Set.Ioi b, ((2*log t+1)/(t^3*(log t)^2))*Chebyshev.theta t) ≤ 2*b^(-(1:ℝ))*(log b)⁻¹ +\n    (Real.eulerMascheroniConstant+2-log (4*Real.pi)) *\n      (b^((1/2:ℝ)-2)*(log b)⁻¹*(2+(log b)⁻¹+4/(3*(log b)^2)))\n\n/-- The exact finite Abel identity for the kernel 1/(t² log t). -/", "∀ s b : ℝ, 1<s → s ≤ b →\n  Chebyshev.theta s/(s^2*log s) +\n    (∑ p ∈ (Ioc ⌊s⌋₊ ⌊b⌋₊).filter Nat.Prime, (p:ℝ)⁻¹^2) =\n  Chebyshev.theta b/(b^2*log b) + (∫ t in Set.Ioc s b, ((2*log t+1)/(t^3*(log t)^2))*Chebyshev.theta t)\n\n/-- Splitting the two convergent improper theta integrals at b. -/", "∀ s b : ℝ, 366 ≤ s → s ≤ b →\n  (∫ t in Set.Ioi s, ((2*log t+1)/(t^3*(log t)^2))*Chebyshev.theta t) - (∫ t in Set.Ioi b, ((2*log t+1)/(t^3*(log t)^2))*Chebyshev.theta t) = (∫ t in Set.Ioc s b, ((2*log t+1)/(t^3*(log t)^2))*Chebyshev.theta t)"]'),
(8496, 'CongruentNumber.Tunnell_even.R1.H2.R1.H2.R1.H2.R1.H2.R1.H1', 1, 'ysanatomic', null::int, '["∀ (n : ℕ) (hn : 0<n),\n  letI : NeZero (4*n) := ⟨Nat.ne_of_gt (Nat.mul_pos (by decide) hn)⟩\n  let a := 1+3*(4*n)\n  let ω : ℝ := (∫ x in Ioi (n:ℝ), (Real.sqrt (x^3-(n:ℝ)^2*x))⁻¹)\n  let b (v : ZMod (4*n) × ZMod (4*n)) : GaussianInt := ⟨v.1.val,v.2.val⟩\n  let χ (v : ZMod (4*n) × ZMod (4*n)) : ℤ :=\n    let m := (b v).norm.natAbs\n    if (⟨2,2⟩:GaussianInt) ∣ b v-1 then (if Odd m then jacobiSym n m else 0) else 0\n  ∀ M : PeriodPair, M.ω₁=(ω:ℂ) → M.ω₂=Complex.I*(ω:ℂ) →\n  let t (j : Fin a × Fin a) : ℂ := ((j.1.val:ℂ)*M.ω₁+(j.2.val:ℂ)*M.ω₂)/(a:ℂ)\n  let D (z : ℂ) := ∏ j ∈ Finset.univ.filter (fun j => t j ∉ M.lattice),\n    (M.weierstrassP z-M.weierstrassP (t j))\n  let G (z : ℂ) := ∏ v ∈ Finset.univ.filter (fun v => χ v≠0),\n    D (z+((ω/(4*n):ℝ):ℂ)*(b v:ℂ))^χ v\n  n%8=2 → 2<n → ∀ (m:ℕ), 0 < m → (4*n).Coprime (a*m) → ∀ z:ℂ, (m:ℂ)*z∈M.lattice →\n    ∃ u:(𝓞 (algebraicClosure ℚ ℂ))ˣ, ((u.val.val:algebraicClosure ℚ ℂ):ℂ)=G z", "∀ (n : ℕ) (hn : 0<n),\n  letI : NeZero (4*n) := ⟨Nat.ne_of_gt (Nat.mul_pos (by decide) hn)⟩\n  let a := 1+3*(4*n)\n  let ω : ℝ := (∫ x in Ioi (n:ℝ), (Real.sqrt (x^3-(n:ℝ)^2*x))⁻¹)\n  let b (v : ZMod (4*n) × ZMod (4*n)) : GaussianInt := ⟨v.1.val,v.2.val⟩\n  let χ (v : ZMod (4*n) × ZMod (4*n)) : ℤ :=\n    let m := (b v).norm.natAbs\n    if (⟨2,2⟩:GaussianInt) ∣ b v-1 then (if Odd m then jacobiSym n m else 0) else 0\n  ∀ M : PeriodPair, M.ω₁=(ω:ℂ) → M.ω₂=Complex.I*(ω:ℂ) →\n  let t (j : Fin a × Fin a) : ℂ := ((j.1.val:ℂ)*M.ω₁+(j.2.val:ℂ)*M.ω₂)/(a:ℂ)\n  let D (z : ℂ) := ∏ j ∈ Finset.univ.filter (fun j => t j ∉ M.lattice),\n    (M.weierstrassP z-M.weierstrassP (t j))\n  let G (z : ℂ) := ∏ v ∈ Finset.univ.filter (fun v => χ v≠0),\n    D (z+((ω/(4*n):ℝ):ℂ)*(b v:ℂ))^χ v\n  n%8=2 → 2<n → (∀ (m:ℕ), 0 < m → (4*n).Coprime (a*m) → ∀ z:ℂ, (m:ℂ)*z∈M.lattice →\n    ∃ u:(𝓞 (algebraicClosure ℚ ℂ))ˣ, ((u.val.val:algebraicClosure ℚ ℂ):ℂ)=G z) → ∀ c : ℚ, c≠0 → logDeriv G 0=(c:ℂ) → ∀ B : ℕ,\n  ∃ p : ℕ, p.Prime ∧ B<p ∧ 3<p ∧ p%4=1 ∧ ¬p∣2*n ∧ ∃ q : GaussianInt, q.norm.natAbs=p ∧\n  let K:=ℚ⟮I⟯\n  let Ω:=algebraicClosure K ℂ\n  let A (r : ℕ) :=\n    let t:=M.ω₁/(q:ℂ)^r\n    (adjoin K {M.weierstrassP t,M.derivWeierstrassP t/2}).comap (algebraicClosure K ℂ).val\n  let T:=A 1\n  let V (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (x y : F) :=\n    let O:=v.adicCompletionIntegers F\n    let L:=v.adicCompletion F\n    ∃ u b : Oˣ, ((u:O):L)=algebraMap F L x ∧ ((b:O):L)=algebraMap F L y ∧\n      maximalIdeal O=Ideal.span {(u:O)-(b:O)}\n  ∃ hT : NumberField T, letI:=hT;\n    ∃ (w : HeightOneSpectrum (𝓞 T)) (z : 𝓞 T), z∈w.asIdeal ∧ (((z:T):Ω):ℂ)=(q:ℂ) ∧\n    ∃ (a : (𝓞 T)ˣ) (b : K), @V T _ hT w a.val.val (algebraMap K T b) ∧\n      ∀ r : ℕ, ∃ h : T≤A (r+1), letI : Algebra T (A (r+1)):=(IntermediateField.inclusion h).toAlgebra;\n        ∃ x : (𝓞 (A (r+1)))ˣ, Algebra.norm T x.val.val=a.val.val"]'),
(8497, 'CongruentNumber.Tunnell_even.R1.H2.R1.H2.R1.H2.R1.H2.R1.H2', 1, 'ysanatomic', null::int, '["∀ (n : ℕ) (hn : 0<n), let ω : ℝ := ∫ x in Ioi (n:ℝ), (Real.sqrt (x^3-(n:ℝ)^2*x))⁻¹;\n  ∀ M : PeriodPair, M.ω₁=(ω:ℂ) → M.ω₂=I*(ω:ℂ) →\n  ∀ P : (⟨0,0,0,-(n:ℚ)^2,0⟩ : WeierstrassCurve ℚ).toAffine.Point, ¬IsOfFinAddOrder P →\n  ∃ B : ℕ, ∀ p : ℕ, p.Prime → B<p → p%4=1 → ¬p∣2*n → ∀ q : GaussianInt, q.norm.natAbs=p →\n  let K:=ℚ⟮I⟯;\n  let Ω:=algebraicClosure K ℂ;\n  let A (r : ℕ) := (let t:=M.ω₁/(q:ℂ)^r;\n                    (adjoin K {M.weierstrassP t,M.derivWeierstrassP t/2}).comap (algebraicClosure K ℂ).val);\n  let T:=A 1;\n  ∀ hT:NumberField T, letI:=hT;\n  ∀ (w:HeightOneSpectrum (𝓞 T)) (z:𝓞 T), z∈w.asIdeal → (((z:T):Ω):ℂ)=(q:ℂ) →\n  let O:=w.adicCompletionIntegers T; let L:=w.adicCompletion T; let e (x:T):L:=x;\n  ∃ (r:ℕ) (h:T≤A (r+1)), let D:=A (r+1);\n    letI : Algebra T D:=(IntermediateField.inclusion h).toAlgebra;\n    ∃ hd:NumberField D, letI:=hd;\n    ∃ (v:HeightOneSpectrum (𝓞 D)) (N:Type) (hn:Field N), letI:=hn;\n    ∃ hN:NumberField N, letI:=hN;\n    ∃ g:Algebra D N, letI:=g;\n    FiniteDimensional D N ∧ IsAbelianGalois D N ∧ (∀ i:InfinitePlace D,i.IsComplex) ∧\n    (∀ s:HeightOneSpectrum (𝓞 D),s≠v → ∀ t:HeightOneSpectrum (𝓞 N),t.asIdeal.LiesOver s.asIdeal →\n      t.asIdeal.ramificationIdx (𝓞 D)=1) ∧\n    ∀ (x:(𝓞 D)ˣ) (b:K),\n    ∀ u u₀:Oˣ, ((u:O):L)=e (Algebra.norm T x.val.val) →\n      ((u₀:O):L)=e (algebraMap K T b) → maximalIdeal O=Ideal.span {(u:O)-(u₀:O)} →\n    let V:=v.adicCompletion D;\n    ¬∃ t:HeightOneSpectrum (𝓞 N),t.asIdeal.LiesOver v.asIdeal ∧ ∃ f:V→+*t.adicCompletion N,\n      Continuous f ∧ (∀ c:D,f (c:V)=((algebraMap D N c:N):t.adicCompletion N)) ∧\n      letI:Algebra V (t.adicCompletion N):=f.toAlgebra;\n      ∃ y:(t.adicCompletion N)ˣ,Algebra.norm V (y:t.adicCompletion N)=(x.val.val:V)", "∀ (D N:Type) [Field D] [NumberField D] [Field N] [NumberField N] [Algebra D N]\n    [FiniteDimensional D N] [IsAbelianGalois D N] (v:HeightOneSpectrum (𝓞 D)),\n  (∀ i:InfinitePlace D,i.IsComplex) →\n  (∀ s:HeightOneSpectrum (𝓞 D),s≠v → ∀ t:HeightOneSpectrum (𝓞 N),t.asIdeal.LiesOver s.asIdeal →\n    t.asIdeal.ramificationIdx (𝓞 D)=1) →\n  ∀ x:(𝓞 D)ˣ,let V:=v.adicCompletion D\n  ∃ t:HeightOneSpectrum (𝓞 N),t.asIdeal.LiesOver v.asIdeal ∧ ∃ f:V→+*t.adicCompletion N,\n    Continuous f ∧ (∀ c:D,f (algebraMap D V c)=algebraMap N (t.adicCompletion N) (algebraMap D N c)) ∧\n    letI:Algebra V (t.adicCompletion N):=f.toAlgebra\n    ∃ y:(t.adicCompletion N)ˣ,Algebra.norm V (y:t.adicCompletion N)=algebraMap D V x.val.val"]')
) v(pr, t, rn, h, pts, st);
-- created_at := merge time, only for rows this transaction created (created_at = now())
update oma_reductions r set created_at = v.m from (values
(5268, '2026-11-27T11:12:51Z'::timestamptz),
(5466, '2026-11-27T11:44:37Z'::timestamptz),
(5546, '2026-11-27T11:57:34Z'::timestamptz),
(5845, '2026-11-27T12:32:00Z'::timestamptz),
(5813, '2026-11-27T12:37:57Z'::timestamptz),
(6154, '2026-11-27T13:05:33Z'::timestamptz),
(6132, '2026-11-27T13:06:46Z'::timestamptz),
(6306, '2026-11-27T14:09:46Z'::timestamptz),
(6858, '2026-11-27T14:58:22Z'::timestamptz),
(6863, '2026-11-27T14:58:51Z'::timestamptz),
(7367, '2026-11-27T15:06:41Z'::timestamptz),
(6963, '2026-11-27T15:08:09Z'::timestamptz),
(7558, '2026-11-27T16:53:38Z'::timestamptz),
(7918, '2026-11-27T17:21:50Z'::timestamptz),
(8496, '2026-11-27T22:43:14Z'::timestamptz),
(8497, '2026-11-27T22:44:03Z'::timestamptz)
) v(pr, m) where r.pr_url = 'https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/' || v.pr and r.created_at = now();
update oma_steps s set created_at = r.created_at from oma_reductions r where s.reduction = r.id and s.created_at = now();
update oma_events e set created_at = r.created_at from oma_reductions r
  where e.kind = 'reduced' and e.created_at = now() and e.problem_id = r.problem_id and e.detail = r.id || ' into ' || r.hyps || ' steps';
commit;

-- ===== batch 7: reductions, dependency level 4 (6 PRs: 6755 .. ) =====
begin;
select v.pr, case
  when exists (select 1 from oma_reductions r where r.pr_url = 'https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/' || v.pr) then json_build_object('skip','pr_exists')
  when exists (select 1 from oma_reductions r where r.id = v.t || '.R' || v.rn) then json_build_object('skip','id_exists')
  when v.pts is null and not exists (select 1 from oma_steps s where s.id = v.t) then json_build_object('error','unknown_target')
  else oma_register_reduction(v.t || '.R' || v.rn, v.t, v.h, 'https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/' || v.pr,
         'OMAReductions.R_' || regexp_replace(v.t || '.R' || v.rn, '[^A-Za-z0-9]', '_', 'g'), v.st::json,
         coalesce(v.pts, (select s.points from oma_steps s where s.id = v.t))) end r
from (values
(6755, 'BusyBeaver.BB_4.R1.H2.R1.H1.R1.H3.R1.H2.R1.H4.R1.H2', 1, 'pageman', null::int, '["let entry (z : ℕ) (r : Fin 4) (s : Fin 2) : Option (Option (Fin 4) × Stmt (Fin 2)) :=\n    let k := z / 17 ^ (2 * r.val + s.val) % 17\n    if k = 16 then none\n    else some (some (Fin.ofNat 4 (k / 4)),\n      .write (Fin.ofNat 2 (k / 2)) (if k % 2 = 0 then .left else .right))\n  ∀ z ∈ ([192926630, 394870650, 515740378, 1336417724, 1408830431, 1627390098,\n       1689441169, 2446657396, 2452336858, 2460855813, 2460855983, 2930234279,\n       3133858477] : List ℕ), ¬ Machine.IsHalting (entry z)", "let entry (z : ℕ) (r : Fin 4) (s : Fin 2) : Option (Option (Fin 4) × Stmt (Fin 2)) :=\n    let k := z / 17 ^ (2 * r.val + s.val) % 17\n    if k = 16 then none\n    else some (some (Fin.ofNat 4 (k / 4)),\n      .write (Fin.ofNat 2 (k / 2)) (if k % 2 = 0 then .left else .right))\n  ∀ z ∈ ([3267241361, 3267325035, 3267408318, 3267408386, 3268076724, 3268179812,\n       3268243766, 3325136085, 3330584823, 3330638645, 3475567181, 3475567351,\n       3672067699] : List ℕ), ¬ Machine.IsHalting (entry z)", "let entry (z : ℕ) (r : Fin 4) (s : Fin 2) : Option (Option (Fin 4) × Stmt (Fin 2)) :=\n    let k := z / 17 ^ (2 * r.val + s.val) % 17\n    if k = 16 then none\n    else some (some (Fin.ofNat 4 (k / 4)),\n      .write (Fin.ofNat 2 (k / 2)) (if k % 2 = 0 then .left else .right))\n  ∀ z ∈ ([3673413691, 3673413861, 4079576433, 4093775003, 4100731862, 4498257380,\n       4684022874, 4953712200, 4972106404, 4972170205, 5435078199, 5439716071,\n       5439804454] : List ℕ), ¬ Machine.IsHalting (entry z)", "let entry (z : ℕ) (r : Fin 4) (s : Fin 2) : Option (Option (Fin 4) × Stmt (Fin 2)) :=\n    let k := z / 17 ^ (2 * r.val + s.val) % 17\n    if k = 16 then none\n    else some (some (Fin.ofNat 4 (k / 4)),\n      .write (Fin.ofNat 2 (k / 2)) (if k % 2 = 0 then .left else .right))\n  ∀ z ∈ ([5440806757, 5453953928, 5537278425, 5792616725, 6328050068, 6695802976,\n       6734875946, 6734876082, 6734876116, 6745900956, 6746235074, 6775658997,\n       6778655859, 6852444036] : List ℕ), ¬ Machine.IsHalting (entry z)"]'),
(6638, 'BusyBeaver.BB_4.R1.H2.R1.H2.R1.H3.R1.H1.R1.H1.R1.H1', 1, 'pageman', null::int, '["∀ (M : Machine (Fin 2) (Fin 4)),\n  M 0 0 = some (some 1, Stmt.write 1 Dir.right) →\n  M 1 0 = some (some 0, Stmt.write 0 Dir.left) →\n  (∃ q t, M.multiStep (Machine.init []) 107 = some ⟨some q, t⟩) →\n  (∀ q a, (∃ i < 107, ∃ t : Tape (Fin 2),\n    M.multiStep (Machine.init []) i = some ⟨some q, t⟩ ∧ t.head = a) ↔\n    ∃ q'' z, M q a = some (some q'', z)) →\n  (∀ q a, M q a = none ∨ ∃ q'' z, M q a = some (some q'', z)) →\n  (∃ q a, M q a = none) →\n  (∀ (i p : ℕ) (q : Fin 4) (a : Fin 2) (side : Bool)\n      (near : List (Fin 2)) (fixed : ListBlank (Fin 2)), 0 < p → i + p ≤ 107 →\n    let cfg := fun tail : ListBlank (Fin 2) =>\n      let free := near.foldr ListBlank.cons tail\n      (⟨some q, if side then ⟨a, free, fixed⟩ else ⟨a, fixed, free⟩⟩ : Cfg (Fin 2) (Fin 4))\n    (∃ tail, M.multiStep (Machine.init []) i = some (cfg tail)) →\n    ¬ ∀ tail, ∃ tail'', M.multiStep (cfg tail) p = some (cfg tail'')) →\n  ¬ M.IsHalting", "∀ (M : Machine (Fin 2) (Fin 4)),\n  M 0 0 = some (some 1, Stmt.write 1 Dir.right) →\n  M 1 0 = some (some 1, Stmt.write 0 Dir.left) →\n  (∃ q t, M.multiStep (Machine.init []) 107 = some ⟨some q, t⟩) →\n  (∀ q a, (∃ i < 107, ∃ t : Tape (Fin 2),\n    M.multiStep (Machine.init []) i = some ⟨some q, t⟩ ∧ t.head = a) ↔\n    ∃ q'' z, M q a = some (some q'', z)) →\n  (∀ q a, M q a = none ∨ ∃ q'' z, M q a = some (some q'', z)) →\n  (∃ q a, M q a = none) →\n  (∀ (i p : ℕ) (q : Fin 4) (a : Fin 2) (side : Bool)\n      (near : List (Fin 2)) (fixed : ListBlank (Fin 2)), 0 < p → i + p ≤ 107 →\n    let cfg := fun tail : ListBlank (Fin 2) =>\n      let free := near.foldr ListBlank.cons tail\n      (⟨some q, if side then ⟨a, free, fixed⟩ else ⟨a, fixed, free⟩⟩ : Cfg (Fin 2) (Fin 4))\n    (∃ tail, M.multiStep (Machine.init []) i = some (cfg tail)) →\n    ¬ ∀ tail, ∃ tail'', M.multiStep (cfg tail) p = some (cfg tail'')) →\n  ¬ M.IsHalting"]'),
(6682, 'Arxiv.1601.03081.crystals_components_unique.R1.H2.R1.H2.R1.H1.R1.H2', 1, 'senamakel', null::int, '["∀ g y z d q : ℕ,\n    1 < g → 33 ≤ y → Odd g → Odd y → Odd z → g*y ≤ z →\n    (g+1)*(y*z+1) ∣ (g+y*z)^2 →\n    0 < d → d < 2*(y-1) → d % 2 = 0 →\n    (g+1 ∣ ((y+1)*(d+(y-1)*y*(1+2*y)))^2) →\n    (g*y+1 ∣ ((y+1)*(d+(y-1)*(y+2)))^2) →\n    5 ≤ q → (g*y+z)^2 = q*((g*y+1)*(z+1)) →\n    g.Coprime y → g.Coprime z → y.Coprime z →\n    (g+y*z ∣ g*y*z+1) → (g*y+z ∣ g*y*z+1) →\n    Nat.gcd (g+y*z) (g*y+z) = y^2-1 →\n    z < g*(y^2-1) → y*q < (y^2-1)+3*y → False", "∀ g y z d q : ℕ,\n    1 < g → 33 ≤ y → Odd g → Odd y → Odd z → g*y ≤ z →\n    (g+1)*(y*z+1) ∣ (g+y*z)^2 →\n    0 < d → d < 2*(y-1) → d % 2 = 0 →\n    (g+1 ∣ ((y+1)*(d+(y-1)*y*(1+2*y)))^2) →\n    (g*y+1 ∣ ((y+1)*(d+(y-1)*(y+2)))^2) →\n    5 ≤ q → (g*y+z)^2 = q*((g*y+1)*(z+1)) →\n    g.Coprime y → g.Coprime z → y.Coprime z →\n    (g+y*z ∣ g*y*z+1) → (g*y+z ∣ g*y*z+1) →\n    let D := Nat.gcd (g+y*z) (g*y+z)\n    D ∣ y^2-1 → D < y^2-1 →\n    z < g*D → y*q < D+3*y → 2*q ≤ y+5 → False"]'),
(6804, 'BusyBeaver.BB_4.R1.H2.R1.H2.R1.H3.R1.H1.R1.H1.R1.H2', 1, 'pageman', null::int, '["∀ (M : Machine (Fin 2) (Fin 4)),\n  M 0 0 = some (some 1, Stmt.write 1 Dir.right) →\n  M 1 0 = some (some 0, Stmt.write 1 Dir.left) →\n  (∃ q t, M.multiStep (Machine.init []) 107 = some ⟨some q, t⟩) →\n  (∀ q a, (∃ i < 107, ∃ t : Tape (Fin 2),\n    M.multiStep (Machine.init []) i = some ⟨some q, t⟩ ∧ t.head = a) ↔\n    ∃ q'' z, M q a = some (some q'', z)) →\n  (∀ q a, M q a = none ∨ ∃ q'' z, M q a = some (some q'', z)) →\n  (∃ q a, M q a = none) →\n  (∀ (i p : ℕ) (q : Fin 4) (a : Fin 2) (side : Bool)\n      (near : List (Fin 2)) (fixed : ListBlank (Fin 2)), 0 < p → i + p ≤ 107 →\n    let cfg := fun tail : ListBlank (Fin 2) =>\n      let free := near.foldr ListBlank.cons tail\n      (⟨some q, if side then ⟨a, free, fixed⟩ else ⟨a, fixed, free⟩⟩ : Cfg (Fin 2) (Fin 4))\n    (∃ tail, M.multiStep (Machine.init []) i = some (cfg tail)) →\n    ¬ ∀ tail, ∃ tail'', M.multiStep (cfg tail) p = some (cfg tail'')) →\n  ¬ M.IsHalting", "∀ (M : Machine (Fin 2) (Fin 4)),\n  M 0 0 = some (some 1, Stmt.write 1 Dir.right) →\n  M 1 0 = some (some 1, Stmt.write 1 Dir.left) →\n  (∃ q t, M.multiStep (Machine.init []) 107 = some ⟨some q, t⟩) →\n  (∀ q a, (∃ i < 107, ∃ t : Tape (Fin 2),\n    M.multiStep (Machine.init []) i = some ⟨some q, t⟩ ∧ t.head = a) ↔\n    ∃ q'' z, M q a = some (some q'', z)) →\n  (∀ q a, M q a = none ∨ ∃ q'' z, M q a = some (some q'', z)) →\n  (∃ q a, M q a = none) →\n  (∀ (i p : ℕ) (q : Fin 4) (a : Fin 2) (side : Bool)\n      (near : List (Fin 2)) (fixed : ListBlank (Fin 2)), 0 < p → i + p ≤ 107 →\n    let cfg := fun tail : ListBlank (Fin 2) =>\n      let free := near.foldr ListBlank.cons tail\n      (⟨some q, if side then ⟨a, free, fixed⟩ else ⟨a, fixed, free⟩⟩ : Cfg (Fin 2) (Fin 4))\n    (∃ tail, M.multiStep (Machine.init []) i = some (cfg tail)) →\n    ¬ ∀ tail, ∃ tail'', M.multiStep (cfg tail) p = some (cfg tail'')) →\n  ¬ M.IsHalting"]'),
(7422, 'BusyBeaver.BB_4.R1.H2.R1.H2.R1.H3.R1.H1.R1.H2.R1.H1', 1, 'pageman', null::int, '["∀ (M : Machine (Fin 2) (Fin 4)),\n  M 0 0 = some (some 1, Stmt.write 1 Dir.right) →\n  M 1 0 = some (some 2, Stmt.write 0 Dir.left) →\n  (∃ q t, M.multiStep (Machine.init []) 107 = some ⟨some q, t⟩) →\n  (∀ q a, (∃ i < 107, ∃ t : Tape (Fin 2),\n    M.multiStep (Machine.init []) i = some ⟨some q, t⟩ ∧ t.head = a) ↔\n    ∃ q'' z, M q a = some (some q'', z)) →\n  (∀ q a, M q a = none ∨ ∃ q'' z, M q a = some (some q'', z)) →\n  (∃ q a, M q a = none) →\n  (∀ (i p : ℕ) (q : Fin 4) (a : Fin 2) (side : Bool)\n      (near : List (Fin 2)) (fixed : ListBlank (Fin 2)), 0 < p → i + p ≤ 107 →\n    let cfg := fun tail : ListBlank (Fin 2) =>\n      let free := near.foldr ListBlank.cons tail\n      (⟨some q, if side then ⟨a, free, fixed⟩ else ⟨a, fixed, free⟩⟩ : Cfg (Fin 2) (Fin 4))\n    (∃ tail, M.multiStep (Machine.init []) i = some (cfg tail)) →\n    ¬ ∀ tail, ∃ tail'', M.multiStep (cfg tail) p = some (cfg tail'')) →\n  ¬ M.IsHalting", "∀ (M : Machine (Fin 2) (Fin 4)),\n  M 0 0 = some (some 1, Stmt.write 1 Dir.right) →\n  M 1 0 = some (some 3, Stmt.write 0 Dir.left) →\n  (∃ q t, M.multiStep (Machine.init []) 107 = some ⟨some q, t⟩) →\n  (∀ q a, (∃ i < 107, ∃ t : Tape (Fin 2),\n    M.multiStep (Machine.init []) i = some ⟨some q, t⟩ ∧ t.head = a) ↔\n    ∃ q'' z, M q a = some (some q'', z)) →\n  (∀ q a, M q a = none ∨ ∃ q'' z, M q a = some (some q'', z)) →\n  (∃ q a, M q a = none) →\n  (∀ (i p : ℕ) (q : Fin 4) (a : Fin 2) (side : Bool)\n      (near : List (Fin 2)) (fixed : ListBlank (Fin 2)), 0 < p → i + p ≤ 107 →\n    let cfg := fun tail : ListBlank (Fin 2) =>\n      let free := near.foldr ListBlank.cons tail\n      (⟨some q, if side then ⟨a, free, fixed⟩ else ⟨a, fixed, free⟩⟩ : Cfg (Fin 2) (Fin 4))\n    (∃ tail, M.multiStep (Machine.init []) i = some (cfg tail)) →\n    ¬ ∀ tail, ∃ tail'', M.multiStep (cfg tail) p = some (cfg tail'')) →\n  ¬ M.IsHalting"]'),
(7925, 'BusyBeaver.BB_4.R1.H2.R1.H2.R1.H3.R1.H2.R1.H2.R1.H4', 1, 'hananzlt', null::int, '["∀ (M : Machine (Fin 2) (Fin 4)) (r : Fin 4) (left : Bool),\n  M 0 0 = some (some 1, Stmt.write 1 .right) →\n  M 1 0 = some (some 2, Stmt.write 0 .right) →\n  M 2 0 = some (some 3, Stmt.write 1 .left) →\n  M 3 0 = some (some r, Stmt.write 0 (if left then .left else .right)) →\n  M.IsHalting → M.HaltsAfter (Machine.init []) 106", "∀ (M : Machine (Fin 2) (Fin 4)) (r : Fin 4) (left : Bool),\n  M 0 0 = some (some 1, Stmt.write 1 .right) →\n  M 1 0 = some (some 2, Stmt.write 0 .right) →\n  M 2 0 = some (some 3, Stmt.write 1 .left) →\n  M 3 0 = some (some r, Stmt.write 1 (if left then .left else .right)) →\n  M.IsHalting → M.HaltsAfter (Machine.init []) 106"]')
) v(pr, t, rn, h, pts, st);
-- created_at := merge time, only for rows this transaction created (created_at = now())
update oma_reductions r set created_at = v.m from (values
(6755, '2026-11-27T13:49:06Z'::timestamptz),
(6638, '2026-11-27T13:56:44Z'::timestamptz),
(6682, '2026-11-27T14:52:14Z'::timestamptz),
(6804, '2026-11-27T14:54:23Z'::timestamptz),
(7422, '2026-11-27T15:01:58Z'::timestamptz),
(7925, '2026-11-27T17:22:08Z'::timestamptz)
) v(pr, m) where r.pr_url = 'https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/' || v.pr and r.created_at = now();
update oma_steps s set created_at = r.created_at from oma_reductions r where s.reduction = r.id and s.created_at = now();
update oma_events e set created_at = r.created_at from oma_reductions r
  where e.kind = 'reduced' and e.created_at = now() and e.problem_id = r.problem_id and e.detail = r.id || ' into ' || r.hyps || ' steps';
commit;

-- ===== batch 8: reductions, dependency level 5 (3 PRs: 7716 .. ) =====
begin;
select v.pr, case
  when exists (select 1 from oma_reductions r where r.pr_url = 'https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/' || v.pr) then json_build_object('skip','pr_exists')
  when exists (select 1 from oma_reductions r where r.id = v.t || '.R' || v.rn) then json_build_object('skip','id_exists')
  when v.pts is null and not exists (select 1 from oma_steps s where s.id = v.t) then json_build_object('error','unknown_target')
  else oma_register_reduction(v.t || '.R' || v.rn, v.t, v.h, 'https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/' || v.pr,
         'OMAReductions.R_' || regexp_replace(v.t || '.R' || v.rn, '[^A-Za-z0-9]', '_', 'g'), v.st::json,
         coalesce(v.pts, (select s.points from oma_steps s where s.id = v.t))) end r
from (values
(7716, 'Arxiv.1601.03081.crystals_components_unique.R1.H2.R1.H2.R1.H1.R1.H2.R1.H2', 1, 'senamakel', null::int, '["∀ g y z d q : ℕ,\n    1 < g → 33 ≤ y → Odd g → Odd y → Odd z → g*y ≤ z →\n    (g+1)*(y*z+1) ∣ (g+y*z)^2 →\n    0 < d → d < 2*(y-1) → d % 2 = 0 →\n    (g+1 ∣ ((y+1)*(d+(y-1)*y*(1+2*y)))^2) →\n    (g*y+1 ∣ ((y+1)*(d+(y-1)*(y+2)))^2) →\n    5 ≤ q → (g*y+z)^2 = q*((g*y+1)*(z+1)) →\n    g.Coprime y → g.Coprime z → y.Coprime z →\n    (g+y*z ∣ g*y*z+1) → (g*y+z ∣ g*y*z+1) →\n    let D := Nat.gcd (g+y*z) (g*y+z)\n    D ∣ y^2-1 → D < y^2-1 →\n    (g+y*z).lcm (g*y+z) = g*y*z+1 →\n    z+g*y < g*D → D+y < y*q → y*q < D+2*y → q = D/y+2 → (q-3)*(y*(q-1)-D) < y →\n    q ≤ (y^2-1)/D+2 → (q-2)^2 < y → 2*q ≤ y+3 → False\n\n/-- The product plus one is an odd multiple of the least common multiple,\nwith cofactor at least three. -/", "∀ g y z d q k : ℕ,\n    1 < g → 33 ≤ y → Odd g → Odd y → Odd z → g*y ≤ z →\n    (g+1)*(y*z+1) ∣ (g+y*z)^2 →\n    0 < d → d < 2*(y-1) → d % 2 = 0 →\n    (g+1 ∣ ((y+1)*(d+(y-1)*y*(1+2*y)))^2) →\n    (g*y+1 ∣ ((y+1)*(d+(y-1)*(y+2)))^2) →\n    5 ≤ q → (g*y+z)^2 = q*((g*y+1)*(z+1)) →\n    g.Coprime y → g.Coprime z → y.Coprime z →\n    (g+y*z ∣ g*y*z+1) → (g*y+z ∣ g*y*z+1) →\n    let D := Nat.gcd (g+y*z) (g*y+z)\n    D ∣ y^2-1 → D < y^2-1 →\n    Odd k → 3 ≤ k → (g+y*z).lcm (g*y+z)*k = g*y*z+1 →\n    k*(z+g*y) < g*D → D+k*y < k*y*q → k*y*q < D+2*k*y →\n    q = D/(k*y)+2 → (q-3)*(k*y*(q-1)-D) < k*y →\n    q ≤ ((y^2-1)/D)*k+2 → (q-2)^2 < y → 3*k*y < D →\n    6*q ≤ y+11 → False"]'),
(7883, 'BusyBeaver.BB_4.R1.H2.R1.H2.R1.H3.R1.H1.R1.H1.R1.H2.R1.H1', 1, 'pageman', null::int, '["∀ (M : Machine (Fin 2) (Fin 4)),\n  M 0 0 = some (some 1, Stmt.write 1 Dir.right) →\n  M 1 0 = some (some 0, Stmt.write 1 Dir.left) →\n  (∃ q t, M.multiStep (Machine.init []) 107 = some ⟨some q, t⟩) →\n  (∀ q a, (∃ i < 107, ∃ t : Tape (Fin 2),\n    M.multiStep (Machine.init []) i = some ⟨some q, t⟩ ∧ t.head = a) ↔\n    ∃ q'' z, M q a = some (some q'', z)) →\n  (∀ q a, M q a = none ∨ ∃ q'' z, M q a = some (some q'', z)) →\n  (∃ q a, M q a = none) →\n  (∀ (i p : ℕ) (q : Fin 4) (a : Fin 2) (side : Bool)\n      (near : List (Fin 2)) (fixed : ListBlank (Fin 2)), 0 < p → i + p ≤ 107 →\n    let cfg := fun tail : ListBlank (Fin 2) =>\n      let free := near.foldr ListBlank.cons tail\n      (⟨some q, if side then ⟨a, free, fixed⟩ else ⟨a, fixed, free⟩⟩ : Cfg (Fin 2) (Fin 4))\n    (∃ tail, M.multiStep (Machine.init []) i = some (cfg tail)) →\n    ¬ ∀ tail, ∃ tail'', M.multiStep (cfg tail) p = some (cfg tail'')) →\n  let tbl (entries : List ℕ) : Machine (Fin 2) (Fin 4) := fun q a =>\n    let v := entries[2 * q.val + a.val]?.getD 16\n    if v = 16 then none else some (some ⟨v / 4 % 4, Nat.mod_lt _ (by decide)⟩,\n      Stmt.write ⟨v / 2 % 2, Nat.mod_lt _ (by decide)⟩\n        (if v % 2 = 0 then Dir.right else Dir.left))\n  M ≠ tbl [6, 3, 3, 8, 15, 10, 16, 1] →\n  M ≠ tbl [6, 3, 3, 12, 16, 1, 11, 14] →\n  ¬ M.IsHalting\n\n/-- Nonhalting of the RepWL special0 machine. -/", "let tbl (entries : List ℕ) : Machine (Fin 2) (Fin 4) := fun q a =>\n    let v := entries[2 * q.val + a.val]?.getD 16\n    if v = 16 then none else some (some ⟨v / 4 % 4, Nat.mod_lt _ (by decide)⟩,\n      Stmt.write ⟨v / 2 % 2, Nat.mod_lt _ (by decide)⟩\n        (if v % 2 = 0 then Dir.right else Dir.left))\n  ¬ (tbl [6, 3, 3, 8, 15, 10, 16, 1]).IsHalting"]'),
(8444, 'Arxiv.1601.03081.crystals_components_unique.R1.H2.R1.H2.R1.H1.R1.H2.R1.H1', 1, 'senamakel', null::int, '["∀ g y z d q k : ℕ,\n    1 < g → 33 ≤ y → Odd g → Odd y → Odd z → g*y ≤ z →\n    (g+1)*(y*z+1) ∣ (g+y*z)^2 →\n    0 < d → d < 2*(y-1) → d % 2 = 0 →\n    (g+1 ∣ ((y+1)*(d+(y-1)*y*(1+2*y)))^2) →\n    (g*y+1 ∣ ((y+1)*(d+(y-1)*(y+2)))^2) →\n    5 ≤ q → (g*y+z)^2=q*((g*y+1)*(z+1)) →\n    g.Coprime y → g.Coprime z → y.Coprime z →\n    (g+y*z ∣ g*y*z+1) → (g*y+z ∣ g*y*z+1) →\n    Nat.gcd (g+y*z) (g*y+z)=y^2-1 →\n    z<g*(y^2-1) → y*q<(y^2-1)+3*y →\n    Odd k → 3≤k → (g+y*z).lcm (g*y+z)*k=g*y*z+1 →\n    k*(z+g*y)<g*(y^2-1) →\n    (y^2-1)+k*y<k*y*q → k*y*q<(y^2-1)+2*k*y →\n    q=(y^2-1)/(k*y)+2 →\n    (q-3)*(k*y*(q-1)-(y^2-1))<k*y → k∣y → False", "∀ g y z d q k : ℕ,\n    1 < g → 33 ≤ y → Odd g → Odd y → Odd z → g*y ≤ z →\n    (g+1)*(y*z+1) ∣ (g+y*z)^2 →\n    0 < d → d < 2*(y-1) → d % 2 = 0 →\n    (g+1 ∣ ((y+1)*(d+(y-1)*y*(1+2*y)))^2) →\n    (g*y+1 ∣ ((y+1)*(d+(y-1)*(y+2)))^2) →\n    5 ≤ q → (g*y+z)^2=q*((g*y+1)*(z+1)) →\n    g.Coprime y → g.Coprime z → y.Coprime z →\n    (g+y*z ∣ g*y*z+1) → (g*y+z ∣ g*y*z+1) →\n    Nat.gcd (g+y*z) (g*y+z)=y^2-1 →\n    z<g*(y^2-1) → y*q<(y^2-1)+3*y →\n    Odd k → 3≤k → (g+y*z).lcm (g*y+z)*k=g*y*z+1 →\n    k*(z+g*y)<g*(y^2-1) →\n    (y^2-1)+k*y<k*y*q → k*y*q<(y^2-1)+2*k*y →\n    q=(y^2-1)/(k*y)+2 →\n    (q-3)*(k*y*(q-1)-(y^2-1))<k*y →\n    ¬ k∣y → q≤k+2 → False\n\nset_option maxHeartbeats 800000 in"]')
) v(pr, t, rn, h, pts, st);
-- created_at := merge time, only for rows this transaction created (created_at = now())
update oma_reductions r set created_at = v.m from (values
(7716, '2026-11-27T17:15:22Z'::timestamptz),
(7883, '2026-11-27T17:19:18Z'::timestamptz),
(8444, '2026-11-27T17:49:22Z'::timestamptz)
) v(pr, m) where r.pr_url = 'https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/' || v.pr and r.created_at = now();
update oma_steps s set created_at = r.created_at from oma_reductions r where s.reduction = r.id and s.created_at = now();
update oma_events e set created_at = r.created_at from oma_reductions r
  where e.kind = 'reduced' and e.created_at = now() and e.problem_id = r.problem_id and e.detail = r.id || ' into ' || r.hyps || ' steps';
commit;

-- ===== batch 9: proofs (50 PRs) =====
begin;
select v.pr, case
  when exists (select 1 from oma_solutions s where s.pr_url = 'https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/' || v.pr) then json_build_object('skip','pr_exists')
  when v.pts is null and not exists (select 1 from oma_steps s where s.id = v.id) then json_build_object('error','unknown_step')
  else oma_verdict2(v.id, v.h, 'https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/' || v.pr, 'accepted', v.pol, v.ag, v.mo,
         case when exists (select 1 from oma_solutions o where o.problem_id = v.id and o.verdict = 'accepted' and o.created_at < v.m) then 0  -- not the first solve
              else coalesce(v.pts, (select s.points from oma_steps s where s.id = v.id)) end) end r
from (values
(4062, 'Green51.green_51.lower_ap', 'Genbox', 'proof', 'codex'::text, 'gpt-6.2-sol'::text, 28::int, '2026-11-27T08:05:44Z'::timestamptz),
(4084, 'Erdos1130.erdos_1130.parts.i.R1.H1', 'PanPapag', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T08:07:27Z'::timestamptz),
(4073, 'Erdos1038.erdos_1038.parts.ii.R1.H2.R1.H2', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T08:08:35Z'::timestamptz),
(4087, 'Erdos507.erdos_507.variants.lower_kps82.R1.H1', 'dk8827', 'proof', 'codex'::text, 'gpt-6.2-sol'::text, null::int, '2026-11-27T08:09:17Z'::timestamptz),
(4155, 'Erdos657.erdos_657.variants.dim_one_lower.R1.H1', 'JaviSoto', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T08:09:47Z'::timestamptz),
(4098, 'Erdos1062.erdos_1062.variants.lebensold_bounds.R1.H2', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T08:10:09Z'::timestamptz),
(4093, 'Erdos507.erdos_507.variants.lower_kps82.R1.H2', 'dk8827', 'proof', 'codex'::text, 'gpt-6.2-sol'::text, null::int, '2026-11-27T08:10:27Z'::timestamptz),
(4111, 'Erdos69.erdos_69.R1.H1.R1.H2.R1.H2', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T08:11:07Z'::timestamptz),
(4107, 'CongruentNumber.Tunnell_even.R1.H1', 'drobison00', 'proof', 'antigravity'::text, 'Gemini 4 Neon'::text, null::int, '2026-11-27T08:11:12Z'::timestamptz),
(4110, 'Erdos978.erdos_978.variants.sub_two', 'drobison00', 'proof', null::text, null::text, 20::int, '2026-11-27T08:11:30Z'::timestamptz),
(4133, 'ReconstructionConjecture.reconstruction_conjecture.variants.tree.R1.H3.R1.H3', 'Deldor14', 'proof', 'codex'::text, 'gpt-6'::text, null::int, '2026-11-27T08:11:35Z'::timestamptz),
(4132, 'Erdos1182.erdos_1182.variants.befrs_lower.R1.H1', 'drobison00', 'proof', 'antigravity'::text, 'Gemini 4 Neon'::text, null::int, '2026-11-27T08:11:51Z'::timestamptz),
(4138, 'Green70.green_70.variants.empty_pentagon.R1.H1', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T08:12:13Z'::timestamptz),
(4148, 'DisjointNPPairs.no_complete_disjoint_NP_pair.variants.exists_of_NP_eq_coNP.R1.H1.R1.H2', 'OrangeHeadz', 'proof', 'claude-code'::text, 'claude-fable-5-2'::text, null::int, '2026-11-27T08:12:26Z'::timestamptz),
(4152, 'Hilbert17.hilbert_17th_problem.R1.H2.R1.H2', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T08:13:02Z'::timestamptz),
(4157, 'Erdos790.erdos_790.variants.lower_bound', 'caa1982', 'proof', 'claude-code'::text, 'claude-opus-5-5'::text, 17::int, '2026-11-27T08:13:07Z'::timestamptz),
(4158, 'SpectralSetProduct.isSpectral_right_of_product_two_dimensional', 'cosformula', 'proof', 't3-code'::text, 'gemini-4-carbon'::text, 28::int, '2026-11-27T08:13:27Z'::timestamptz),
(4169, 'OeisA218585.conjecture_3.R1.H2', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T08:14:17Z'::timestamptz),
(4172, 'Erdos436.erdos_436.variants.six_two.R1.H2.R1.H1', 'Hiphex', 'proof', 'codex'::text, 'gpt-6.2-sol'::text, null::int, '2026-11-27T08:14:25Z'::timestamptz),
(4181, 'Erdos876.erdos_876.variants.recip_sum_bounds.R1.H1', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T08:14:36Z'::timestamptz),
(4182, 'Erdos522.erdos_522.variants.yakir_solution', 'JaviSoto', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, 22::int, '2026-11-27T08:14:50Z'::timestamptz),
(4192, 'Erdos90.erdos_90.variants.sawin_explicit.R1.H2.R1.H2', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T08:15:13Z'::timestamptz),
(4204, 'EllipticCurveRank.RatEllipticCurve.card_heightLE_div_pow_five_div_six_tensto', 'drobison00', 'proof', 'antigravity'::text, 'Gemini 4 Neon'::text, 7::int, '2026-11-27T08:16:21Z'::timestamptz),
(4202, 'RegularPrimes.not_isRegularPrime_37.R1.H2', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T08:16:26Z'::timestamptz),
(4209, 'Erdos145.erdos_145.variants.lt_eleven_thirds.R1.H1', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T08:16:53Z'::timestamptz),
(4206, 'Erdos295.erdos_295.variants.erdos_straus', 'drobison00', 'proof', null::text, null::text, 17::int, '2026-11-27T08:17:15Z'::timestamptz),
(4222, 'Erdos757.erdos_757.variants.lowerBound.R1.H1', 'JaviSoto', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T08:17:42Z'::timestamptz),
(4236, 'Erdos920.erdos_920.variants.upper_bound', 'LordMike', 'proof', 'claude-code'::text, 'claude-fable-5-2'::text, 17::int, '2026-11-27T08:17:53Z'::timestamptz),
(4227, 'PartitionParity.classNumber_eq_ncard_reducedForms.R1.H1', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T08:17:57Z'::timestamptz),
(4229, 'Erdos757.erdos_757.variants.lowerBound.R1.H1.R1.H1', 'ishaanzee', 'proof', 'claude-code'::text, 'claude-opus-5-5'::text, null::int, '2026-11-27T08:18:07Z'::timestamptz),
(4258, 'Erdos174.erdos_174.variants.trapezoid', 'Salofe', 'proof', 'claude-code'::text, 'unknown'::text, 18::int, '2026-11-27T08:18:26Z'::timestamptz),
(4220, 'Erdos930.erdos_930.variants.consecutive_integers.R1.H3', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T08:18:29Z'::timestamptz),
(4266, 'Erdos480.erdos_480.variants.chung_graham', 'nijv', 'proof', 'antigravity'::text, 'Gemini 4'::text, 18::int, '2026-11-27T08:18:31Z'::timestamptz),
(4238, 'Erdos657.erdos_657.variants.dim_one_lower.R1.H2', 'PanPapag', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T08:18:35Z'::timestamptz),
(4267, 'Erdos494.erdos_494.variants.gordon_fraenkel_straus', 'caa1982', 'proof', 'claude-code'::text, 'claude-opus-5-5'::text, 17::int, '2026-11-27T08:18:51Z'::timestamptz),
(4274, 'Erdos504.erdos_504', 'drobison00', 'proof', null::text, null::text, 27::int, '2026-11-27T08:19:06Z'::timestamptz),
(4295, 'Erdos723.erdos_723.variants.leq_11.R1.H2.R2.H4.R1.H2.R1.H3.R1.H2.R1.H1', 'avivorly', 'proof', 'codex'::text, 'GPT-6'::text, null::int, '2026-11-27T08:19:14Z'::timestamptz),
(4286, 'Erdos723.erdos_723.variants.leq_11.R1.H2.R2.H4.R1.H2.R1.H2.R1.H3.R1.H1', 'avivorly', 'proof', 'codex'::text, 'GPT-6'::text, null::int, '2026-11-27T08:19:16Z'::timestamptz),
(4302, 'Green95.green_95.variants.three_palindromes', 'drobison00', 'proof', 'antigravity'::text, 'Gemini 4 Neon'::text, 17::int, '2026-11-27T08:19:27Z'::timestamptz),
(4310, 'ManickamMiklosSinghiConjecture.manickam_miklos_singhi_conjecture.variants.pokrovskiy.R1.H1', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T08:19:30Z'::timestamptz),
(4318, 'DisjointNPPairs.no_complete_disjoint_NP_pair.variants.exists_of_NP_eq_coNP.R1.H1.R1.H1', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T08:19:40Z'::timestamptz),
(4311, 'Erdos859.erdos_859.variants.erdos_upper_lower_bounds.R1.H2', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T08:19:42Z'::timestamptz),
(4265, 'Erdos859.erdos_859.variants.erdos_upper_lower_bounds.R1.H1', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T08:19:44Z'::timestamptz),
(4317, 'Erdos384.erdos_384.R1.H2.R1.H3', 'yalosaws', 'proof', 'codex'::text, 'GPT-6'::text, null::int, '2026-11-27T08:20:01Z'::timestamptz),
(4301, 'Firoozbakht.firoozbakht_conjecture_consequence.R1.H2', 'steveDOTdigital', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T08:20:08Z'::timestamptz),
(4324, 'Erdos5.erdos_5.variants.banks_freiberg_maynard_measure.R1.H2', 'ishaanzee', 'proof', 'claude-code'::text, 'claude-opus-5-5'::text, null::int, '2026-11-27T08:20:12Z'::timestamptz),
(4325, 'Borsuk.borsuk_conjecture.not_of_nine_le.R1.H1.R1.H1', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T08:20:17Z'::timestamptz),
(4312, 'Erdos436.erdos_436.variants.five_two.R1.H2.R1.H1', 'ishaanzee', 'proof', 'claude-code'::text, 'claude-opus-5-5'::text, null::int, '2026-11-27T08:20:20Z'::timestamptz),
(4270, 'Erdos437.erdos_437.variants.tao', 'drobison00', 'proof', 'antigravity'::text, 'Gemini 4 Neon'::text, 17::int, '2026-11-27T08:20:25Z'::timestamptz),
(4332, 'Erdos436.erdos_436.variants.seven_two.R1.H3.R1.H2', 'marcusbuffett', 'proof', 'claude-code'::text, 'claude-fable-5-2'::text, null::int, '2026-11-27T08:20:30Z'::timestamptz)
) v(pr, id, h, pol, ag, mo, pts, m);
-- created_at := merge time, only for rows this transaction created (created_at = now())
update oma_solutions s set created_at = v.m from (values
(4062, '2026-11-27T08:05:44Z'::timestamptz),
(4084, '2026-11-27T08:07:27Z'::timestamptz),
(4073, '2026-11-27T08:08:35Z'::timestamptz),
(4087, '2026-11-27T08:09:17Z'::timestamptz),
(4155, '2026-11-27T08:09:47Z'::timestamptz),
(4098, '2026-11-27T08:10:09Z'::timestamptz),
(4093, '2026-11-27T08:10:27Z'::timestamptz),
(4111, '2026-11-27T08:11:07Z'::timestamptz),
(4107, '2026-11-27T08:11:12Z'::timestamptz),
(4110, '2026-11-27T08:11:30Z'::timestamptz),
(4133, '2026-11-27T08:11:35Z'::timestamptz),
(4132, '2026-11-27T08:11:51Z'::timestamptz),
(4138, '2026-11-27T08:12:13Z'::timestamptz),
(4148, '2026-11-27T08:12:26Z'::timestamptz),
(4152, '2026-11-27T08:13:02Z'::timestamptz),
(4157, '2026-11-27T08:13:07Z'::timestamptz),
(4158, '2026-11-27T08:13:27Z'::timestamptz),
(4169, '2026-11-27T08:14:17Z'::timestamptz),
(4172, '2026-11-27T08:14:25Z'::timestamptz),
(4181, '2026-11-27T08:14:36Z'::timestamptz),
(4182, '2026-11-27T08:14:50Z'::timestamptz),
(4192, '2026-11-27T08:15:13Z'::timestamptz),
(4204, '2026-11-27T08:16:21Z'::timestamptz),
(4202, '2026-11-27T08:16:26Z'::timestamptz),
(4209, '2026-11-27T08:16:53Z'::timestamptz),
(4206, '2026-11-27T08:17:15Z'::timestamptz),
(4222, '2026-11-27T08:17:42Z'::timestamptz),
(4236, '2026-11-27T08:17:53Z'::timestamptz),
(4227, '2026-11-27T08:17:57Z'::timestamptz),
(4229, '2026-11-27T08:18:07Z'::timestamptz),
(4258, '2026-11-27T08:18:26Z'::timestamptz),
(4220, '2026-11-27T08:18:29Z'::timestamptz),
(4266, '2026-11-27T08:18:31Z'::timestamptz),
(4238, '2026-11-27T08:18:35Z'::timestamptz),
(4267, '2026-11-27T08:18:51Z'::timestamptz),
(4274, '2026-11-27T08:19:06Z'::timestamptz),
(4295, '2026-11-27T08:19:14Z'::timestamptz),
(4286, '2026-11-27T08:19:16Z'::timestamptz),
(4302, '2026-11-27T08:19:27Z'::timestamptz),
(4310, '2026-11-27T08:19:30Z'::timestamptz),
(4318, '2026-11-27T08:19:40Z'::timestamptz),
(4311, '2026-11-27T08:19:42Z'::timestamptz),
(4265, '2026-11-27T08:19:44Z'::timestamptz),
(4317, '2026-11-27T08:20:01Z'::timestamptz),
(4301, '2026-11-27T08:20:08Z'::timestamptz),
(4324, '2026-11-27T08:20:12Z'::timestamptz),
(4325, '2026-11-27T08:20:17Z'::timestamptz),
(4312, '2026-11-27T08:20:20Z'::timestamptz),
(4270, '2026-11-27T08:20:25Z'::timestamptz),
(4332, '2026-11-27T08:20:30Z'::timestamptz)
) v(pr, m) where s.pr_url = 'https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/' || v.pr and s.created_at = now();
update oma_events e set created_at = s.created_at from oma_solutions s
  where e.kind = 'accepted' and e.created_at = now() and e.detail = s.pr_url and s.pr_url like 'https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/' || '%' and s.pr_url not like '%#closed';
-- parents closed by this batch (oma_verdict2 climb): dated when their last step was first solved; repeated for nested closures
create temp table _bf_closed on commit drop as select id from oma_solutions where pr_url like '%#closed' and created_at = now();
update oma_solutions c set created_at = x.t from (
  select c2.id, (select max(f.first) from (select min(o.created_at) first from oma_steps st join oma_solutions o on o.problem_id = st.id and o.verdict = 'accepted'
                                            where st.reduction = r.id group by st.id) f) t
  from oma_solutions c2 join _bf_closed k on k.id = c2.id join oma_reductions r on c2.pr_url = r.pr_url || '#closed') x
where c.id = x.id and x.t is not null;
update oma_solutions c set created_at = x.t from (
  select c2.id, (select max(f.first) from (select min(o.created_at) first from oma_steps st join oma_solutions o on o.problem_id = st.id and o.verdict = 'accepted'
                                            where st.reduction = r.id group by st.id) f) t
  from oma_solutions c2 join _bf_closed k on k.id = c2.id join oma_reductions r on c2.pr_url = r.pr_url || '#closed') x
where c.id = x.id and x.t is not null;
update oma_solutions c set created_at = x.t from (
  select c2.id, (select max(f.first) from (select min(o.created_at) first from oma_steps st join oma_solutions o on o.problem_id = st.id and o.verdict = 'accepted'
                                            where st.reduction = r.id group by st.id) f) t
  from oma_solutions c2 join _bf_closed k on k.id = c2.id join oma_reductions r on c2.pr_url = r.pr_url || '#closed') x
where c.id = x.id and x.t is not null;
update oma_solutions c set created_at = x.t from (
  select c2.id, (select max(f.first) from (select min(o.created_at) first from oma_steps st join oma_solutions o on o.problem_id = st.id and o.verdict = 'accepted'
                                            where st.reduction = r.id group by st.id) f) t
  from oma_solutions c2 join _bf_closed k on k.id = c2.id join oma_reductions r on c2.pr_url = r.pr_url || '#closed') x
where c.id = x.id and x.t is not null;
update oma_events e set created_at = c.created_at from oma_solutions c join _bf_closed k on k.id = c.id join oma_reductions r on c.pr_url = r.pr_url || '#closed'
  where e.kind = 'accepted' and e.created_at = now() and e.detail = 'closed by reduction ' || r.id;
commit;

-- ===== batch 10: proofs (50 PRs) =====
begin;
select v.pr, case
  when exists (select 1 from oma_solutions s where s.pr_url = 'https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/' || v.pr) then json_build_object('skip','pr_exists')
  when v.pts is null and not exists (select 1 from oma_steps s where s.id = v.id) then json_build_object('error','unknown_step')
  else oma_verdict2(v.id, v.h, 'https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/' || v.pr, 'accepted', v.pol, v.ag, v.mo,
         case when exists (select 1 from oma_solutions o where o.problem_id = v.id and o.verdict = 'accepted' and o.created_at < v.m) then 0  -- not the first solve
              else coalesce(v.pts, (select s.points from oma_steps s where s.id = v.id)) end) end r
from (values
(4322, 'WeaklyFirstCountable.CH.existsWeaklyFirstCountableCompactNotFirstCountable', 'minimumnz', 'proof', 'antigravity'::text, 'Gemini'::text, 28::int, '2026-11-27T08:20:32Z'::timestamptz),
(4315, 'Green14.W_3_10', 'drobison00', 'proof', null::text, null::text, 27::int, '2026-11-27T08:20:53Z'::timestamptz),
(4336, 'Arxiv.0805.3777.cprank_le_of_square_slices.R1.H2', 'ivillar', 'proof', 'claude-code'::text, 'claude-fable-5-2'::text, null::int, '2026-11-27T08:21:26Z'::timestamptz),
(4339, 'Erdos230.erdos_230.variants.ultraflat.R1.H2', 'ivillar', 'proof', 'claude-code'::text, 'claude-opus-5-5'::text, null::int, '2026-11-27T08:21:44Z'::timestamptz),
(4340, 'Erdos551.erdos_551.variants.sufficiently_large.R2.H1', 'ishaanzee', 'proof', 'claude-code'::text, 'claude-opus-5-5'::text, null::int, '2026-11-27T08:21:52Z'::timestamptz),
(4338, 'Erdos930.erdos_930.variants.consecutive_strong.R1.H1', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T08:21:56Z'::timestamptz),
(4329, 'Erdos360.erdos_360.R1.H4.R1.H3', 'green-notes', 'proof', 'antigravity'::text, 'gemini-4'::text, null::int, '2026-11-27T08:22:02Z'::timestamptz),
(4333, 'Erdos436.erdos_436.variants.three_three.R1.H2.R1.H1', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T08:22:19Z'::timestamptz),
(4345, 'Erdos983.erdos_983.variants.erdos_straus.R1.H2.R1.H2', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T08:23:11Z'::timestamptz),
(4342, 'Erdos145.erdos_145.variants.le_three.R1.H1', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T08:23:44Z'::timestamptz),
(4343, 'Erdos69.erdos_69.R1.H1.R1.H2.R1.H1.R1.H1', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T08:24:39Z'::timestamptz),
(4347, 'Erdos299.erdos_299.variants.density.R1.H1.R1.H1', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T08:24:53Z'::timestamptz),
(4351, 'Erdos239.erdos_239.R1.H3', 'marcusbuffett', 'proof', 'claude-code'::text, 'claude-fable-5-2'::text, null::int, '2026-11-27T08:26:06Z'::timestamptz),
(4355, 'Erdos69.erdos_69.R1.H1.R1.H2.R1.H1.R1.H3', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T08:27:32Z'::timestamptz),
(4359, 'Erdos32.erdos_32.variants.log_squared.R1.H1.R1.H2', 'ishaanzee', 'proof', 'claude-code'::text, 'claude-opus-5-5'::text, null::int, '2026-11-27T08:27:54Z'::timestamptz),
(4358, 'FiniteLocallyFreeGroupSchemeExponent.killed_by_rank.variants.field', 'Volkopat', 'proof', 'antigravity'::text, 'gemini'::text, 17::int, '2026-11-27T08:27:56Z'::timestamptz),
(4368, 'Erdos145.erdos_145.variants.lt_eleven_thirds.R1.H2.R1.H1', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T08:28:37Z'::timestamptz),
(4365, 'Erdos694.erdos_694.R1.H1', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T08:28:41Z'::timestamptz),
(4364, 'Erdos436.erdos_436.variants.six_two.R1.H2.R1.H2.R1.H1', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T08:28:47Z'::timestamptz),
(4375, 'Erdos710.erdos_710.variants.upper_bound.R1.H1', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T08:29:38Z'::timestamptz),
(4377, 'Erdos436.erdos_436.variants.five_two.R1.H2.R1.H2.R1.H2', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T08:30:05Z'::timestamptz),
(4378, 'Erdos1100.erdos_1100.variants.normal_order.R1.H4', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T08:30:29Z'::timestamptz),
(4369, 'Borsuk.borsuk_conjecture.not_of_nine_le.R1.H1.R1.H2', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T08:31:13Z'::timestamptz),
(4382, 'Erdos930.erdos_930.variants.consecutive_integers.R1.H4.R1.H1', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T08:31:31Z'::timestamptz),
(4381, 'FiniteLocallyFreeGroupSchemeExponent.killed_by_rank.variants.reduced_base', 'Volkopat', 'proof', 'antigravity'::text, 'gemini'::text, 17::int, '2026-11-27T08:32:05Z'::timestamptz),
(4386, 'Erdos930.erdos_930.variants.consecutive_integers.R1.H4.R1.H3', 'marcusbuffett', 'proof', 'claude-code'::text, 'claude-fable-5-2'::text, null::int, '2026-11-27T08:32:49Z'::timestamptz),
(4397, 'Erdos5.erdos_5.variants.hildebrand_maier.R1.H1.R1.H2', 'ivillar', 'proof', 'claude-code'::text, 'claude-opus-5-5'::text, null::int, '2026-11-27T08:34:22Z'::timestamptz),
(4390, 'Erdos69.erdos_69.R1.H1.R1.H2.R1.H1.R1.H2', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T08:34:29Z'::timestamptz),
(4400, 'Arxiv.0805.3777.isMaxRank_of_le_min.R1.H2', 'ivillar', 'proof', 'claude-code'::text, 'claude-fable-5-2'::text, null::int, '2026-11-27T08:37:20Z'::timestamptz),
(4399, 'OeisA218585.conjecture_3.R1.H1.R1.H2', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T08:37:28Z'::timestamptz),
(4405, 'Erdos1190.erdos_1190.variants.upper_bound.R1.H1.R1.H1', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T08:38:51Z'::timestamptz),
(4409, 'Erdos297.erdos_297.variants.general.R1.H3.R1.H1', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T08:39:16Z'::timestamptz),
(4410, 'Erdos710.erdos_710.variants.upper_bound.R1.H2', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T08:40:29Z'::timestamptz),
(4413, 'Erdos239.erdos_239.R1.H1', 'ivillar', 'proof', 'claude-code'::text, 'claude-opus-5-5'::text, null::int, '2026-11-27T08:40:54Z'::timestamptz),
(4411, 'Green31.green_31.variants.sidon_01n_clz01', 'drobison00', 'proof', null::text, null::text, 17::int, '2026-11-27T08:41:12Z'::timestamptz),
(4417, 'Hilbert17.hilbert_17th_problem.R1.H3.R1.H2', 'green-notes', 'proof', 'antigravity'::text, 'antigravity-pro'::text, null::int, '2026-11-27T08:42:08Z'::timestamptz),
(4420, 'BusyBeaver.BB_4.R1.H2.R1.H1.R1.H2', 'pageman', 'proof', 'cursor'::text, 'composer-2'::text, null::int, '2026-11-27T08:43:57Z'::timestamptz),
(4429, 'Erdos338.erdos_338.variants.triangular.R1.H1.R1.H1.R1.H2', 'ivillar', 'proof', 'claude-code'::text, 'claude-opus-5-5'::text, null::int, '2026-11-27T08:46:06Z'::timestamptz),
(4427, 'BusyBeaver.BB_4.R1.H2.R1.H1.R1.H1', 'pageman', 'proof', 'cursor'::text, 'composer-2'::text, null::int, '2026-11-27T08:46:15Z'::timestamptz),
(4431, 'Erdos1133.erdos_1133.variants.weaker', 'drobison00', 'proof', 'antigravity'::text, 'Gemini 4 Neon'::text, 18::int, '2026-11-27T08:47:03Z'::timestamptz),
(4434, 'Erdos1190.erdos_1190.variants.upper_bound.R1.H1.R1.H2', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T08:48:06Z'::timestamptz),
(4433, 'Erdos319.erdos_319.variants.lb.R1.H1', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T08:48:25Z'::timestamptz),
(4436, 'Erdos950.erdos_950.variants.debruijn_erdos_turan.R1.H1', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T08:48:40Z'::timestamptz),
(4443, 'Erdos5.erdos_5.variants.merikoski_bounded_gaps.R1.H2', 'ivillar', 'proof', 'claude-code'::text, 'claude-opus-5-5'::text, null::int, '2026-11-27T08:49:02Z'::timestamptz),
(4440, 'Erdos507.erdos_507.variants.lower_kps82', 'drobison00', 'proof', 'antigravity'::text, 'Gemini 4 Neon'::text, 16::int, '2026-11-27T08:49:06Z'::timestamptz),
(4448, 'Erdos384.erdos_384', 'DomTheDeveloper', 'proof', 'claude-code'::text, 'unknown'::text, 28::int, '2026-11-27T08:50:00Z'::timestamptz),
(4447, 'Erdos859.erdos_859.variants.erdos_upper_lower_bounds', 'drobison00', 'proof', null::text, null::text, 17::int, '2026-11-27T08:50:08Z'::timestamptz),
(4450, 'BusyBeaver.BB_4.R1.H2.R1.H2.R1.H1', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T08:50:15Z'::timestamptz),
(4438, 'Borsuk.borsuk_conjecture.not_of_nine_le.R1.H1.R1.H3', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T08:50:39Z'::timestamptz),
(4451, 'Erdos480.erdos_480.variants.chung_graham_best_possible', 'DomTheDeveloper', 'proof', 'claude-code'::text, 'unknown'::text, 18::int, '2026-11-27T08:50:52Z'::timestamptz)
) v(pr, id, h, pol, ag, mo, pts, m);
-- created_at := merge time, only for rows this transaction created (created_at = now())
update oma_solutions s set created_at = v.m from (values
(4322, '2026-11-27T08:20:32Z'::timestamptz),
(4315, '2026-11-27T08:20:53Z'::timestamptz),
(4336, '2026-11-27T08:21:26Z'::timestamptz),
(4339, '2026-11-27T08:21:44Z'::timestamptz),
(4340, '2026-11-27T08:21:52Z'::timestamptz),
(4338, '2026-11-27T08:21:56Z'::timestamptz),
(4329, '2026-11-27T08:22:02Z'::timestamptz),
(4333, '2026-11-27T08:22:19Z'::timestamptz),
(4345, '2026-11-27T08:23:11Z'::timestamptz),
(4342, '2026-11-27T08:23:44Z'::timestamptz),
(4343, '2026-11-27T08:24:39Z'::timestamptz),
(4347, '2026-11-27T08:24:53Z'::timestamptz),
(4351, '2026-11-27T08:26:06Z'::timestamptz),
(4355, '2026-11-27T08:27:32Z'::timestamptz),
(4359, '2026-11-27T08:27:54Z'::timestamptz),
(4358, '2026-11-27T08:27:56Z'::timestamptz),
(4368, '2026-11-27T08:28:37Z'::timestamptz),
(4365, '2026-11-27T08:28:41Z'::timestamptz),
(4364, '2026-11-27T08:28:47Z'::timestamptz),
(4375, '2026-11-27T08:29:38Z'::timestamptz),
(4377, '2026-11-27T08:30:05Z'::timestamptz),
(4378, '2026-11-27T08:30:29Z'::timestamptz),
(4369, '2026-11-27T08:31:13Z'::timestamptz),
(4382, '2026-11-27T08:31:31Z'::timestamptz),
(4381, '2026-11-27T08:32:05Z'::timestamptz),
(4386, '2026-11-27T08:32:49Z'::timestamptz),
(4397, '2026-11-27T08:34:22Z'::timestamptz),
(4390, '2026-11-27T08:34:29Z'::timestamptz),
(4400, '2026-11-27T08:37:20Z'::timestamptz),
(4399, '2026-11-27T08:37:28Z'::timestamptz),
(4405, '2026-11-27T08:38:51Z'::timestamptz),
(4409, '2026-11-27T08:39:16Z'::timestamptz),
(4410, '2026-11-27T08:40:29Z'::timestamptz),
(4413, '2026-11-27T08:40:54Z'::timestamptz),
(4411, '2026-11-27T08:41:12Z'::timestamptz),
(4417, '2026-11-27T08:42:08Z'::timestamptz),
(4420, '2026-11-27T08:43:57Z'::timestamptz),
(4429, '2026-11-27T08:46:06Z'::timestamptz),
(4427, '2026-11-27T08:46:15Z'::timestamptz),
(4431, '2026-11-27T08:47:03Z'::timestamptz),
(4434, '2026-11-27T08:48:06Z'::timestamptz),
(4433, '2026-11-27T08:48:25Z'::timestamptz),
(4436, '2026-11-27T08:48:40Z'::timestamptz),
(4443, '2026-11-27T08:49:02Z'::timestamptz),
(4440, '2026-11-27T08:49:06Z'::timestamptz),
(4448, '2026-11-27T08:50:00Z'::timestamptz),
(4447, '2026-11-27T08:50:08Z'::timestamptz),
(4450, '2026-11-27T08:50:15Z'::timestamptz),
(4438, '2026-11-27T08:50:39Z'::timestamptz),
(4451, '2026-11-27T08:50:52Z'::timestamptz)
) v(pr, m) where s.pr_url = 'https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/' || v.pr and s.created_at = now();
update oma_events e set created_at = s.created_at from oma_solutions s
  where e.kind = 'accepted' and e.created_at = now() and e.detail = s.pr_url and s.pr_url like 'https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/' || '%' and s.pr_url not like '%#closed';
-- parents closed by this batch (oma_verdict2 climb): dated when their last step was first solved; repeated for nested closures
create temp table _bf_closed on commit drop as select id from oma_solutions where pr_url like '%#closed' and created_at = now();
update oma_solutions c set created_at = x.t from (
  select c2.id, (select max(f.first) from (select min(o.created_at) first from oma_steps st join oma_solutions o on o.problem_id = st.id and o.verdict = 'accepted'
                                            where st.reduction = r.id group by st.id) f) t
  from oma_solutions c2 join _bf_closed k on k.id = c2.id join oma_reductions r on c2.pr_url = r.pr_url || '#closed') x
where c.id = x.id and x.t is not null;
update oma_solutions c set created_at = x.t from (
  select c2.id, (select max(f.first) from (select min(o.created_at) first from oma_steps st join oma_solutions o on o.problem_id = st.id and o.verdict = 'accepted'
                                            where st.reduction = r.id group by st.id) f) t
  from oma_solutions c2 join _bf_closed k on k.id = c2.id join oma_reductions r on c2.pr_url = r.pr_url || '#closed') x
where c.id = x.id and x.t is not null;
update oma_solutions c set created_at = x.t from (
  select c2.id, (select max(f.first) from (select min(o.created_at) first from oma_steps st join oma_solutions o on o.problem_id = st.id and o.verdict = 'accepted'
                                            where st.reduction = r.id group by st.id) f) t
  from oma_solutions c2 join _bf_closed k on k.id = c2.id join oma_reductions r on c2.pr_url = r.pr_url || '#closed') x
where c.id = x.id and x.t is not null;
update oma_solutions c set created_at = x.t from (
  select c2.id, (select max(f.first) from (select min(o.created_at) first from oma_steps st join oma_solutions o on o.problem_id = st.id and o.verdict = 'accepted'
                                            where st.reduction = r.id group by st.id) f) t
  from oma_solutions c2 join _bf_closed k on k.id = c2.id join oma_reductions r on c2.pr_url = r.pr_url || '#closed') x
where c.id = x.id and x.t is not null;
update oma_events e set created_at = c.created_at from oma_solutions c join _bf_closed k on k.id = c.id join oma_reductions r on c.pr_url = r.pr_url || '#closed'
  where e.kind = 'accepted' and e.created_at = now() and e.detail = 'closed by reduction ' || r.id;
commit;

-- ===== batch 11: proofs (50 PRs) =====
begin;
select v.pr, case
  when exists (select 1 from oma_solutions s where s.pr_url = 'https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/' || v.pr) then json_build_object('skip','pr_exists')
  when v.pts is null and not exists (select 1 from oma_steps s where s.id = v.id) then json_build_object('error','unknown_step')
  else oma_verdict2(v.id, v.h, 'https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/' || v.pr, 'accepted', v.pol, v.ag, v.mo,
         case when exists (select 1 from oma_solutions o where o.problem_id = v.id and o.verdict = 'accepted' and o.created_at < v.m) then 0  -- not the first solve
              else coalesce(v.pts, (select s.points from oma_steps s where s.id = v.id)) end) end r
from (values
(4453, 'BusyBeaver.BB_4.R1.H2.R1.H2.R1.H2', 'ishaanzee', 'proof', 'claude-code'::text, 'claude-opus-5-5'::text, null::int, '2026-11-27T08:51:38Z'::timestamptz),
(4464, 'Erdos710.erdos_710.variants.lower_bound.R1.H3', 'ivillar', 'proof', 'claude-code'::text, 'claude-opus-5-5'::text, null::int, '2026-11-27T08:52:01Z'::timestamptz),
(4460, 'Erdos710.erdos_710.variants.lower_bound.R1.H2', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T08:52:10Z'::timestamptz),
(4468, 'Erdos299.erdos_299.variants.density.R1.H1.R1.H2.R1.H1', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T08:54:24Z'::timestamptz),
(4474, 'Erdos912.erdos_912.variants.selfridge', 'drobison00', 'proof', 'antigravity'::text, 'Gemini 4 Neon'::text, 17::int, '2026-11-27T08:54:57Z'::timestamptz),
(4473, 'Erdos436.erdos_436.variants.seven_two.R1.H3.R1.H1', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T08:55:31Z'::timestamptz),
(4485, 'LovaszPlummerConjecture.sheehan_conjecture.variants.thomassen.R1.H1', 'luciusacarr', 'proof', 'antigravity'::text, 'gemini-4-hydrogen'::text, null::int, '2026-11-27T08:56:04Z'::timestamptz),
(4480, 'Erdos556.erdos_556.variants.luczak_asymptotic_even', 'drobison00', 'proof', null::text, null::text, 10::int, '2026-11-27T08:56:13Z'::timestamptz),
(4482, 'Erdos436.erdos_436.variants.five_two.R1.H2.R1.H2.R1.H1.R1.H2', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T08:56:22Z'::timestamptz),
(4484, 'LovaszPlummerConjecture.sheehan_conjecture.variants.thomassen.R1.H2', 'luciusacarr', 'proof', 'antigravity'::text, 'gemini-4-hydrogen'::text, null::int, '2026-11-27T08:56:25Z'::timestamptz),
(4489, 'Erdos652.erdos_652.variants.order_sqrt', 'drobison00', 'proof', null::text, null::text, 18::int, '2026-11-27T08:56:30Z'::timestamptz),
(4479, 'Erdos999.erdos_999.R1.H2.R1.H2', 'chris01-dev', 'proof', 'claude-code'::text, 'claude-fable-5-2'::text, null::int, '2026-11-27T08:56:38Z'::timestamptz),
(4490, 'Erdos436.erdos_436.variants.five_two.R1.H2.R1.H2.R1.H1.R1.H1', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T08:56:49Z'::timestamptz),
(4168, 'Erdos1177.erdos_1177.parts.ii', 'Ciphore', 'proof', 'codex'::text, 'gpt-6.2-sol'::text, 29::int, '2026-11-27T08:57:05Z'::timestamptz),
(4483, 'Hilbert17.hilbert_17th_problem.R1.H3.R1.H1', 'green-notes', 'proof', 'antigravity'::text, 'gemini-4'::text, null::int, '2026-11-27T08:57:27Z'::timestamptz),
(4493, 'Arxiv.0805.3777.isMaxRank_of_le_min.R1.H1', 'minimumnz', 'proof', 'antigravity'::text, 'Gemini'::text, null::int, '2026-11-27T08:58:38Z'::timestamptz),
(4494, 'Erdos448.erdos_448.variants.ford.R1.H2', 'ivillar', 'proof', 'claude-code'::text, 'claude-opus-5-5'::text, null::int, '2026-11-27T08:59:55Z'::timestamptz),
(4505, 'Erdos436.erdos_436.variants.ge_four.R1.H2', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T08:59:57Z'::timestamptz),
(4499, 'OeisA1818.conjecture2', 'drobison00', 'proof', 'antigravity'::text, 'Gemini 4 Neon'::text, 28::int, '2026-11-27T09:00:05Z'::timestamptz),
(4502, 'Erdos629.erdos_629.variants.radhakrishnan_srinivasan', 'LordMike', 'proof', 'claude-code'::text, 'claude-fable-5-2'::text, 17::int, '2026-11-27T09:00:21Z'::timestamptz),
(4501, 'Erdos601.erdos_601.variants.erdos_hajnal_milner_1970.R1.H2', 'skhakim', 'proof', 'antigravity'::text, 'Gemini 4 Neon'::text, null::int, '2026-11-27T09:00:30Z'::timestamptz),
(4510, 'Erdos950.erdos_950.variants.debruijn_erdos_turan.R1.H2.R1.H1', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T09:02:36Z'::timestamptz),
(4514, 'Hilbert17.hilbert_17th_problem.R1.H3.R1.H3', 'green-notes', 'proof', 'antigravity'::text, 'antigravity-pro'::text, null::int, '2026-11-27T09:03:12Z'::timestamptz),
(4515, 'Erdos5.erdos_5.variants.hildebrand_maier_measure.R1.H2', 'ivillar', 'proof', 'claude-code'::text, 'claude-opus-5-5'::text, null::int, '2026-11-27T09:03:38Z'::timestamptz),
(4518, 'Erdos5.erdos_5.variants.pintz.R1.H2', 'ivillar', 'proof', 'claude-code'::text, 'claude-opus-5-5'::text, null::int, '2026-11-27T09:04:49Z'::timestamptz),
(4516, 'Erdos436.erdos_436.variants.three_three.R1.H2', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T09:05:49Z'::timestamptz),
(4520, 'Erdos930.erdos_930.variants.consecutive_integers.R1.H4.R1.H2.R1.H2', 'marcusbuffett', 'proof', 'claude-code'::text, 'claude-fable-5-2'::text, null::int, '2026-11-27T09:06:16Z'::timestamptz),
(4527, 'Erdos816.erdos_816.variants.chen_ma', 'skhakim', 'proof', 'antigravity'::text, 'gemini-4-carbon'::text, 17::int, '2026-11-27T09:08:52Z'::timestamptz),
(4533, 'Erdos876.erdos_876.variants.recip_sum_bounds', 'drobison00', 'proof', null::text, null::text, 17::int, '2026-11-27T09:11:09Z'::timestamptz),
(4539, 'Erdos710.erdos_710.variants.lower_bound.R1.H1.R1.H2', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T09:11:43Z'::timestamptz),
(4536, 'Erdos1164.erdos_1164', 'drobison00', 'proof', null::text, null::text, 29::int, '2026-11-27T09:12:01Z'::timestamptz),
(4538, 'Erdos601.erdos_601.variants.erdos_hajnal_milner_1970.R1.H3', 'skhakim', 'proof', 'antigravity'::text, 'Gemini 4 Neon'::text, null::int, '2026-11-27T09:12:16Z'::timestamptz),
(4548, 'Erdos299.erdos_299.variants.density.R1.H1.R1.H2.R1.H3.R1.H2', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T09:14:56Z'::timestamptz),
(4553, 'Erdos757.erdos_757.variants.lowerBound.R1.H1.R1.H3.R1.H1', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T09:16:26Z'::timestamptz),
(4561, 'CramerConjecture.cramer_conjecture.variants.baker_harman_pintz.R1.H2', 'ivillar', 'proof', 'claude-code'::text, 'claude-opus-5-5'::text, null::int, '2026-11-27T09:29:08Z'::timestamptz),
(4570, 'Erdos297.erdos_297.variants.general.R1.H3.R1.H2.R1.H2', 'ivillar', 'proof', 'claude-code'::text, 'claude-opus-5-5'::text, null::int, '2026-11-27T09:32:09Z'::timestamptz),
(4564, 'Erdos16.erdos_16.variant.romanoff', 'drobison00', 'proof', 'antigravity'::text, 'Gemini 4 Neon'::text, 17::int, '2026-11-27T09:34:13Z'::timestamptz),
(4648, 'Erdos1140.erdos_1140.variants.at_most_one_exception.R1.H2.R1.H1', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T09:39:58Z'::timestamptz),
(4645, 'Erdos710.erdos_710.variants.lower_bound.R1.H1.R1.H1.R1.H2', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T09:40:12Z'::timestamptz),
(4634, 'Erdos969.erdos_969.variants.evelyn_linfoot.R1.H3.R1.H2', 'hananzlt', 'proof', 'codex'::text, 'GPT-6 (exact variant unavailable)'::text, null::int, '2026-11-27T09:41:42Z'::timestamptz),
(4683, 'Erdos1140.erdos_1140.variants.at_most_one_exception.R1.H1.R1.H1', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T09:45:38Z'::timestamptz),
(4699, 'Erdos710.erdos_710.variants.lower_bound.R1.H1.R1.H1.R1.H1', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T09:50:39Z'::timestamptz),
(4735, 'Erdos308.erdos_308.variants.croot.R1.H2', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T09:54:28Z'::timestamptz),
(4737, 'Erdos258.erdos_258.variants.monotone.R2.H1', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T09:55:10Z'::timestamptz),
(4780, 'Erdos308.erdos_308.variants.croot.R1.H2.R1.H2', 'ivillar', 'proof', 'claude-code'::text, 'claude-opus-5-5'::text, null::int, '2026-11-27T10:01:42Z'::timestamptz),
(4781, 'Erdos1186.erdos_1186.variants.prs_bounds.R1.H1', 'koolkao', 'proof', 'claude-code'::text, 'claude-opus-5-5'::text, null::int, '2026-11-27T10:02:54Z'::timestamptz),
(4801, 'Erdos299.erdos_299.variants.density.R1.H1.R1.H2.R1.H4', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T10:04:42Z'::timestamptz),
(4830, 'Erdos308.erdos_308.variants.croot.R1.H2.R1.H1', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T10:06:21Z'::timestamptz),
(4827, 'BusyBeaver.BB_4.R1.H2.R1.H1.R1.H3.R1.H1', 'ivillar', 'proof', 'claude-code'::text, 'claude-opus-5-5'::text, null::int, '2026-11-27T10:06:32Z'::timestamptz),
(4851, 'Erdos299.erdos_299.variants.density.R1.H1.R1.H2.R1.H3.R1.H1', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T10:09:06Z'::timestamptz)
) v(pr, id, h, pol, ag, mo, pts, m);
-- created_at := merge time, only for rows this transaction created (created_at = now())
update oma_solutions s set created_at = v.m from (values
(4453, '2026-11-27T08:51:38Z'::timestamptz),
(4464, '2026-11-27T08:52:01Z'::timestamptz),
(4460, '2026-11-27T08:52:10Z'::timestamptz),
(4468, '2026-11-27T08:54:24Z'::timestamptz),
(4474, '2026-11-27T08:54:57Z'::timestamptz),
(4473, '2026-11-27T08:55:31Z'::timestamptz),
(4485, '2026-11-27T08:56:04Z'::timestamptz),
(4480, '2026-11-27T08:56:13Z'::timestamptz),
(4482, '2026-11-27T08:56:22Z'::timestamptz),
(4484, '2026-11-27T08:56:25Z'::timestamptz),
(4489, '2026-11-27T08:56:30Z'::timestamptz),
(4479, '2026-11-27T08:56:38Z'::timestamptz),
(4490, '2026-11-27T08:56:49Z'::timestamptz),
(4168, '2026-11-27T08:57:05Z'::timestamptz),
(4483, '2026-11-27T08:57:27Z'::timestamptz),
(4493, '2026-11-27T08:58:38Z'::timestamptz),
(4494, '2026-11-27T08:59:55Z'::timestamptz),
(4505, '2026-11-27T08:59:57Z'::timestamptz),
(4499, '2026-11-27T09:00:05Z'::timestamptz),
(4502, '2026-11-27T09:00:21Z'::timestamptz),
(4501, '2026-11-27T09:00:30Z'::timestamptz),
(4510, '2026-11-27T09:02:36Z'::timestamptz),
(4514, '2026-11-27T09:03:12Z'::timestamptz),
(4515, '2026-11-27T09:03:38Z'::timestamptz),
(4518, '2026-11-27T09:04:49Z'::timestamptz),
(4516, '2026-11-27T09:05:49Z'::timestamptz),
(4520, '2026-11-27T09:06:16Z'::timestamptz),
(4527, '2026-11-27T09:08:52Z'::timestamptz),
(4533, '2026-11-27T09:11:09Z'::timestamptz),
(4539, '2026-11-27T09:11:43Z'::timestamptz),
(4536, '2026-11-27T09:12:01Z'::timestamptz),
(4538, '2026-11-27T09:12:16Z'::timestamptz),
(4548, '2026-11-27T09:14:56Z'::timestamptz),
(4553, '2026-11-27T09:16:26Z'::timestamptz),
(4561, '2026-11-27T09:29:08Z'::timestamptz),
(4570, '2026-11-27T09:32:09Z'::timestamptz),
(4564, '2026-11-27T09:34:13Z'::timestamptz),
(4648, '2026-11-27T09:39:58Z'::timestamptz),
(4645, '2026-11-27T09:40:12Z'::timestamptz),
(4634, '2026-11-27T09:41:42Z'::timestamptz),
(4683, '2026-11-27T09:45:38Z'::timestamptz),
(4699, '2026-11-27T09:50:39Z'::timestamptz),
(4735, '2026-11-27T09:54:28Z'::timestamptz),
(4737, '2026-11-27T09:55:10Z'::timestamptz),
(4780, '2026-11-27T10:01:42Z'::timestamptz),
(4781, '2026-11-27T10:02:54Z'::timestamptz),
(4801, '2026-11-27T10:04:42Z'::timestamptz),
(4830, '2026-11-27T10:06:21Z'::timestamptz),
(4827, '2026-11-27T10:06:32Z'::timestamptz),
(4851, '2026-11-27T10:09:06Z'::timestamptz)
) v(pr, m) where s.pr_url = 'https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/' || v.pr and s.created_at = now();
update oma_events e set created_at = s.created_at from oma_solutions s
  where e.kind = 'accepted' and e.created_at = now() and e.detail = s.pr_url and s.pr_url like 'https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/' || '%' and s.pr_url not like '%#closed';
-- parents closed by this batch (oma_verdict2 climb): dated when their last step was first solved; repeated for nested closures
create temp table _bf_closed on commit drop as select id from oma_solutions where pr_url like '%#closed' and created_at = now();
update oma_solutions c set created_at = x.t from (
  select c2.id, (select max(f.first) from (select min(o.created_at) first from oma_steps st join oma_solutions o on o.problem_id = st.id and o.verdict = 'accepted'
                                            where st.reduction = r.id group by st.id) f) t
  from oma_solutions c2 join _bf_closed k on k.id = c2.id join oma_reductions r on c2.pr_url = r.pr_url || '#closed') x
where c.id = x.id and x.t is not null;
update oma_solutions c set created_at = x.t from (
  select c2.id, (select max(f.first) from (select min(o.created_at) first from oma_steps st join oma_solutions o on o.problem_id = st.id and o.verdict = 'accepted'
                                            where st.reduction = r.id group by st.id) f) t
  from oma_solutions c2 join _bf_closed k on k.id = c2.id join oma_reductions r on c2.pr_url = r.pr_url || '#closed') x
where c.id = x.id and x.t is not null;
update oma_solutions c set created_at = x.t from (
  select c2.id, (select max(f.first) from (select min(o.created_at) first from oma_steps st join oma_solutions o on o.problem_id = st.id and o.verdict = 'accepted'
                                            where st.reduction = r.id group by st.id) f) t
  from oma_solutions c2 join _bf_closed k on k.id = c2.id join oma_reductions r on c2.pr_url = r.pr_url || '#closed') x
where c.id = x.id and x.t is not null;
update oma_solutions c set created_at = x.t from (
  select c2.id, (select max(f.first) from (select min(o.created_at) first from oma_steps st join oma_solutions o on o.problem_id = st.id and o.verdict = 'accepted'
                                            where st.reduction = r.id group by st.id) f) t
  from oma_solutions c2 join _bf_closed k on k.id = c2.id join oma_reductions r on c2.pr_url = r.pr_url || '#closed') x
where c.id = x.id and x.t is not null;
update oma_events e set created_at = c.created_at from oma_solutions c join _bf_closed k on k.id = c.id join oma_reductions r on c.pr_url = r.pr_url || '#closed'
  where e.kind = 'accepted' and e.created_at = now() and e.detail = 'closed by reduction ' || r.id;
commit;

-- ===== batch 12: proofs (50 PRs) =====
begin;
select v.pr, case
  when exists (select 1 from oma_solutions s where s.pr_url = 'https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/' || v.pr) then json_build_object('skip','pr_exists')
  when v.pts is null and not exists (select 1 from oma_steps s where s.id = v.id) then json_build_object('error','unknown_step')
  else oma_verdict2(v.id, v.h, 'https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/' || v.pr, 'accepted', v.pol, v.ag, v.mo,
         case when exists (select 1 from oma_solutions o where o.problem_id = v.id and o.verdict = 'accepted' and o.created_at < v.m) then 0  -- not the first solve
              else coalesce(v.pts, (select s.points from oma_steps s where s.id = v.id)) end) end r
from (values
(4881, 'Erdos299.erdos_299.variants.density.R1.H1.R1.H2.R1.H3.R1.H1.R1.H1', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T10:11:31Z'::timestamptz),
(4893, 'Erdos1186.erdos_1186.variants.prs_bounds.R1.H2', 'marcusbuffett', 'proof', 'grok'::text, 'grok-4.7'::text, null::int, '2026-11-27T10:14:33Z'::timestamptz),
(4909, 'Erdos299.erdos_299.variants.density.R1.H1.R1.H2.R1.H2', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T10:15:56Z'::timestamptz),
(4920, 'Erdos299.erdos_299.variants.density.R1.H1.R1.H2.R1.H3.R1.H1.R1.H2', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T10:17:08Z'::timestamptz),
(4928, 'Erdos258.erdos_258.variants.monotone.R2.H2.R1.H1', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T10:17:20Z'::timestamptz),
(4956, 'Erdos983.erdos_983.variants.erdos_straus.R1.H2.R1.H1.R1.H2', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T10:23:42Z'::timestamptz),
(4958, 'Erdos297.erdos_297.variants.general.R1.H3.R1.H2.R1.H1.R1.H1', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T10:24:32Z'::timestamptz),
(4947, 'Erdos983.erdos_983.variants.erdos_straus.R1.H2.R1.H1.R1.H1', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T10:25:06Z'::timestamptz),
(4987, 'Erdos50.erdos_50_singular.R1.H1', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T10:27:43Z'::timestamptz),
(4997, 'Arxiv.2507.17780.tx_graffiti_conjecture_1.R1.H1', 'Mart1neZ', 'proof', 'Codex (completed a draft started in Gemini)'::text, 'GPT-6 (exact variant unavailable)'::text, null::int, '2026-11-27T10:31:05Z'::timestamptz),
(5009, 'Erdos723.erdos_723.variants.leq_11.R1.H2.R2.H4.R1.H2.R1.H2.R1.H3.R1.H2.R1.H1', 'avivorly', 'proof', 'codex'::text, 'GPT-6'::text, null::int, '2026-11-27T10:32:36Z'::timestamptz),
(5072, 'Erdos297.erdos_297.variants.general.R1.H3.R1.H2.R1.H1.R1.H2', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T10:39:07Z'::timestamptz),
(5079, 'Erdos78.erdos_78.variants.cohen.R1.H2.R1.H1', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T10:39:32Z'::timestamptz),
(5099, 'BusyBeaver.BB_4.R1.H2.R1.H2.R1.H3.R1.H3.R1.H2', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T10:42:04Z'::timestamptz),
(5120, 'Erdos78.erdos_78.variants.cohen.R1.H2.R1.H2', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T10:45:20Z'::timestamptz),
(5170, 'Erdos46.erdos_46.variants.infinitely_many_disjoint', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, 18::int, '2026-11-27T10:55:51Z'::timestamptz),
(5196, 'Erdos258.erdos_258.variants.monotone.R2.H2.R1.H2.R1.H1', 'ivillar', 'proof', 'claude-code'::text, 'claude-opus-5-5'::text, null::int, '2026-11-27T10:57:22Z'::timestamptz),
(5197, 'Erdos258.erdos_258.variants.monotone.R2.H2.R1.H2.R1.H2', 'ivillar', 'proof', 'claude-code'::text, 'claude-opus-5-5'::text, null::int, '2026-11-27T10:58:36Z'::timestamptz),
(5205, 'Erdos151.erdos_151.variants.cliqueFree_four.R1.H1.R1.H2', 'SanskarX10', 'proof', 'ply-math'::text, 'gpt-6.2-sol + gpt-6-luna'::text, null::int, '2026-11-27T11:01:49Z'::timestamptz),
(5227, 'Erdos258.erdos_258.variants.monotone.R2.H2.R1.H2', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T11:06:28Z'::timestamptz),
(5314, 'Erdos366.erdos_366.variants.weaker.R2.H2', 'Salofe', 'proof', 'claude-code'::text, 'unknown'::text, null::int, '2026-11-27T11:19:48Z'::timestamptz),
(5326, 'Erdos50.erdos_50_singular.R1.H2.R1.H1', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T11:21:20Z'::timestamptz),
(5382, 'Green14.green_14_polynomial.R1.H2', 'nijv', 'proof', 'antigravity'::text, 'Gemini 4'::text, null::int, '2026-11-27T11:32:15Z'::timestamptz),
(5383, 'Erdos298.erdos_298.variants.natural_density.R1.H1.R1.H2', 'PanPapag', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T11:32:17Z'::timestamptz),
(5451, 'Erdos173.erdos_173.R1.H2.R1.H1.R1.H2.R1.H2', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T11:41:16Z'::timestamptz),
(5471, 'Erdos40.erdos_40.variants.weaker.R1.H2.R1.H1', 'Salofe', 'proof', 'claude-code'::text, 'unknown'::text, null::int, '2026-11-27T11:41:59Z'::timestamptz),
(5515, 'Erdos1180.erdos_1180.variants.optimal.R1.H1', 'Salofe', 'proof', 'claude-code'::text, 'unknown'::text, null::int, '2026-11-27T11:48:09Z'::timestamptz),
(5520, 'Erdos173.erdos_173.R1.H2.R1.H2.R1.H2', 'Salofe', 'proof', 'claude-code'::text, 'unknown'::text, null::int, '2026-11-27T11:49:29Z'::timestamptz),
(5535, 'CramerConjecture.cramer_conjecture.variants.baker_harman_pintz.R1.H1.R1.H2', 'ivillar', 'proof', 'claude-code'::text, 'claude-fable-5-2'::text, null::int, '2026-11-27T11:51:34Z'::timestamptz),
(5534, 'Erdos308.erdos_308.variants.croot.R1.H1.R1.H1', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T11:52:55Z'::timestamptz),
(5564, 'Erdos930.erdos_930.variants.consecutive_integers.R1.H4.R1.H2.R1.H1.R1.H2', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T12:00:09Z'::timestamptz),
(5615, 'Erdos308.erdos_308.variants.croot.R1.H1.R1.H2', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T12:05:04Z'::timestamptz),
(5646, 'Erdos930.erdos_930.variants.consecutive_integers.R1.H4.R1.H2.R1.H1.R1.H1', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T12:12:45Z'::timestamptz),
(5676, 'Erdos308.erdos_308.variants.croot.R1.H1.R1.H3', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T12:14:10Z'::timestamptz),
(5688, 'BusyBeaver.BB_4.R1.H2.R1.H2.R1.H3.R1.H3.R1.H1.R1.H2', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T12:16:33Z'::timestamptz),
(5808, 'RiemannHypothesis.robin_criterion.R1.H1.R1.H2.R1.H2.R1.H3', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T12:27:39Z'::timestamptz),
(5812, 'RiemannHypothesis.robin_criterion.R1.H1.R1.H2.R1.H2.R1.H2', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T12:28:10Z'::timestamptz),
(5841, 'BusyBeaver.BB_4.R1.H2.R1.H1.R1.H3.R1.H2.R1.H1', 'pageman', 'proof', 'cursor'::text, 'composer'::text, null::int, '2026-11-27T12:33:58Z'::timestamptz),
(5893, 'Arxiv.1601.03081.crystals_components_unique.R1.H2.R1.H1', 'Salofe', 'proof', 'claude-code'::text, 'unknown'::text, null::int, '2026-11-27T12:37:27Z'::timestamptz),
(5889, 'Erdos173.erdos_173.R1.H2.R1.H2.R1.H1.R1.H2', 'Salofe', 'proof', 'claude-code'::text, 'unknown'::text, null::int, '2026-11-27T12:38:36Z'::timestamptz),
(5912, 'Arxiv.1601.03081.crystals_components_unique.R1.H1.R1.H1', 'Salofe', 'proof', 'claude-code'::text, 'unknown'::text, null::int, '2026-11-27T12:40:16Z'::timestamptz),
(5981, 'Erdos20.erdos_20.R1.H2.R2.H2', 'tongenspace', 'proof', 'antigravity'::text, 'Gemini 4 Neon (High)'::text, null::int, '2026-11-27T12:51:55Z'::timestamptz),
(6225, 'Erdos173.erdos_173.R1.H2.R1.H1.R1.H2.R1.H1.R1.H1', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T13:00:32Z'::timestamptz),
(6186, 'PoincareConjecture.poincare_conjecture.R1.H1.R1.H3.R2.H2.R1.H2.R1.H2', 'Genbox', 'proof', 'codex'::text, 'gpt-6.2-sol'::text, null::int, '2026-11-27T13:03:22Z'::timestamptz),
(6191, 'Erdos422.erdos_422.variants.well_defined.R1.H1', 'Genbox', 'proof', 'codex'::text, 'gpt-6.2-sol'::text, null::int, '2026-11-27T13:03:32Z'::timestamptz),
(6175, 'Erdos3.erdos_3.variants.green_tao.R2.H1', 'skhakim', 'proof', 'antigravity'::text, 'Gemini 4 Neon'::text, null::int, '2026-11-27T13:04:09Z'::timestamptz),
(5523, 'Green14.W_3_13.R1.H2.R1.H3', 'ZedingZhang', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T13:04:23Z'::timestamptz),
(5949, 'BusyBeaver.BB_4.R1.H2.R1.H1.R1.H3.R1.H2.R1.H2', 'pageman', 'proof', 'cursor'::text, 'composer'::text, null::int, '2026-11-27T13:04:52Z'::timestamptz),
(6121, 'BusyBeaver.BB_4.R1.H2.R1.H1.R1.H3.R1.H2.R1.H3', 'pageman', 'proof', 'cursor'::text, 'composer'::text, null::int, '2026-11-27T13:07:24Z'::timestamptz),
(6047, 'Erdos50.erdos_50_singular.R1.H2.R1.H2.R1.H2', 'Salofe', 'proof', 'claude-code'::text, 'unknown'::text, null::int, '2026-11-27T13:07:34Z'::timestamptz)
) v(pr, id, h, pol, ag, mo, pts, m);
-- created_at := merge time, only for rows this transaction created (created_at = now())
update oma_solutions s set created_at = v.m from (values
(4881, '2026-11-27T10:11:31Z'::timestamptz),
(4893, '2026-11-27T10:14:33Z'::timestamptz),
(4909, '2026-11-27T10:15:56Z'::timestamptz),
(4920, '2026-11-27T10:17:08Z'::timestamptz),
(4928, '2026-11-27T10:17:20Z'::timestamptz),
(4956, '2026-11-27T10:23:42Z'::timestamptz),
(4958, '2026-11-27T10:24:32Z'::timestamptz),
(4947, '2026-11-27T10:25:06Z'::timestamptz),
(4987, '2026-11-27T10:27:43Z'::timestamptz),
(4997, '2026-11-27T10:31:05Z'::timestamptz),
(5009, '2026-11-27T10:32:36Z'::timestamptz),
(5072, '2026-11-27T10:39:07Z'::timestamptz),
(5079, '2026-11-27T10:39:32Z'::timestamptz),
(5099, '2026-11-27T10:42:04Z'::timestamptz),
(5120, '2026-11-27T10:45:20Z'::timestamptz),
(5170, '2026-11-27T10:55:51Z'::timestamptz),
(5196, '2026-11-27T10:57:22Z'::timestamptz),
(5197, '2026-11-27T10:58:36Z'::timestamptz),
(5205, '2026-11-27T11:01:49Z'::timestamptz),
(5227, '2026-11-27T11:06:28Z'::timestamptz),
(5314, '2026-11-27T11:19:48Z'::timestamptz),
(5326, '2026-11-27T11:21:20Z'::timestamptz),
(5382, '2026-11-27T11:32:15Z'::timestamptz),
(5383, '2026-11-27T11:32:17Z'::timestamptz),
(5451, '2026-11-27T11:41:16Z'::timestamptz),
(5471, '2026-11-27T11:41:59Z'::timestamptz),
(5515, '2026-11-27T11:48:09Z'::timestamptz),
(5520, '2026-11-27T11:49:29Z'::timestamptz),
(5535, '2026-11-27T11:51:34Z'::timestamptz),
(5534, '2026-11-27T11:52:55Z'::timestamptz),
(5564, '2026-11-27T12:00:09Z'::timestamptz),
(5615, '2026-11-27T12:05:04Z'::timestamptz),
(5646, '2026-11-27T12:12:45Z'::timestamptz),
(5676, '2026-11-27T12:14:10Z'::timestamptz),
(5688, '2026-11-27T12:16:33Z'::timestamptz),
(5808, '2026-11-27T12:27:39Z'::timestamptz),
(5812, '2026-11-27T12:28:10Z'::timestamptz),
(5841, '2026-11-27T12:33:58Z'::timestamptz),
(5893, '2026-11-27T12:37:27Z'::timestamptz),
(5889, '2026-11-27T12:38:36Z'::timestamptz),
(5912, '2026-11-27T12:40:16Z'::timestamptz),
(5981, '2026-11-27T12:51:55Z'::timestamptz),
(6225, '2026-11-27T13:00:32Z'::timestamptz),
(6186, '2026-11-27T13:03:22Z'::timestamptz),
(6191, '2026-11-27T13:03:32Z'::timestamptz),
(6175, '2026-11-27T13:04:09Z'::timestamptz),
(5523, '2026-11-27T13:04:23Z'::timestamptz),
(5949, '2026-11-27T13:04:52Z'::timestamptz),
(6121, '2026-11-27T13:07:24Z'::timestamptz),
(6047, '2026-11-27T13:07:34Z'::timestamptz)
) v(pr, m) where s.pr_url = 'https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/' || v.pr and s.created_at = now();
update oma_events e set created_at = s.created_at from oma_solutions s
  where e.kind = 'accepted' and e.created_at = now() and e.detail = s.pr_url and s.pr_url like 'https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/' || '%' and s.pr_url not like '%#closed';
-- parents closed by this batch (oma_verdict2 climb): dated when their last step was first solved; repeated for nested closures
create temp table _bf_closed on commit drop as select id from oma_solutions where pr_url like '%#closed' and created_at = now();
update oma_solutions c set created_at = x.t from (
  select c2.id, (select max(f.first) from (select min(o.created_at) first from oma_steps st join oma_solutions o on o.problem_id = st.id and o.verdict = 'accepted'
                                            where st.reduction = r.id group by st.id) f) t
  from oma_solutions c2 join _bf_closed k on k.id = c2.id join oma_reductions r on c2.pr_url = r.pr_url || '#closed') x
where c.id = x.id and x.t is not null;
update oma_solutions c set created_at = x.t from (
  select c2.id, (select max(f.first) from (select min(o.created_at) first from oma_steps st join oma_solutions o on o.problem_id = st.id and o.verdict = 'accepted'
                                            where st.reduction = r.id group by st.id) f) t
  from oma_solutions c2 join _bf_closed k on k.id = c2.id join oma_reductions r on c2.pr_url = r.pr_url || '#closed') x
where c.id = x.id and x.t is not null;
update oma_solutions c set created_at = x.t from (
  select c2.id, (select max(f.first) from (select min(o.created_at) first from oma_steps st join oma_solutions o on o.problem_id = st.id and o.verdict = 'accepted'
                                            where st.reduction = r.id group by st.id) f) t
  from oma_solutions c2 join _bf_closed k on k.id = c2.id join oma_reductions r on c2.pr_url = r.pr_url || '#closed') x
where c.id = x.id and x.t is not null;
update oma_solutions c set created_at = x.t from (
  select c2.id, (select max(f.first) from (select min(o.created_at) first from oma_steps st join oma_solutions o on o.problem_id = st.id and o.verdict = 'accepted'
                                            where st.reduction = r.id group by st.id) f) t
  from oma_solutions c2 join _bf_closed k on k.id = c2.id join oma_reductions r on c2.pr_url = r.pr_url || '#closed') x
where c.id = x.id and x.t is not null;
update oma_events e set created_at = c.created_at from oma_solutions c join _bf_closed k on k.id = c.id join oma_reductions r on c.pr_url = r.pr_url || '#closed'
  where e.kind = 'accepted' and e.created_at = now() and e.detail = 'closed by reduction ' || r.id;
commit;

-- ===== batch 13: proofs (50 PRs) =====
begin;
select v.pr, case
  when exists (select 1 from oma_solutions s where s.pr_url = 'https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/' || v.pr) then json_build_object('skip','pr_exists')
  when v.pts is null and not exists (select 1 from oma_steps s where s.id = v.id) then json_build_object('error','unknown_step')
  else oma_verdict2(v.id, v.h, 'https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/' || v.pr, 'accepted', v.pol, v.ag, v.mo,
         case when exists (select 1 from oma_solutions o where o.problem_id = v.id and o.verdict = 'accepted' and o.created_at < v.m) then 0  -- not the first solve
              else coalesce(v.pts, (select s.points from oma_steps s where s.id = v.id)) end) end r
from (values
(5990, 'Erdos50.erdos_50_singular.R1.H2.R1.H2.R1.H1', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T13:10:48Z'::timestamptz),
(6061, 'Green68.green_68.variants.voloch.R1.H2', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T13:11:17Z'::timestamptz),
(5991, 'Erdos338.erdos_338.variants.triangular.R1.H1.R1.H1.R1.H1.R1.H4', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T13:11:24Z'::timestamptz),
(6060, 'oeis-a377109', 'zarnab222-dev', 'disproof', 'Codex'::text, 'gpt-6.2-astra'::text, 35::int, '2026-11-27T13:11:30Z'::timestamptz),
(6063, 'oeis-a347748', 'marcelopierry', 'proof', 'antigravity'::text, 'Gemini 4 Neon'::text, 62::int, '2026-11-27T13:11:33Z'::timestamptz),
(6794, 'oeis-a056084', 'AkiRA-COM-FP', 'proof', null::text, null::text, 35::int, '2026-11-27T13:47:04Z'::timestamptz),
(6647, 'Erdos151.erdos_151.variants.cliqueFree_four.R1.H1.R1.H1.R1.H4', 'SanskarX10', 'proof', 'ply-math'::text, 'gpt-6.2-sol + gpt-6-luna'::text, null::int, '2026-11-27T13:56:27Z'::timestamptz),
(6634, 'OeisA237720.conjecture_2.R1.H1', 'ivillar', 'proof', 'claude-code'::text, 'claude-opus-5-5'::text, null::int, '2026-11-27T13:56:59Z'::timestamptz),
(6595, 'Erdos151.erdos_151.variants.cliqueFree_four.R1.H1.R1.H1.R1.H3', 'SanskarX10', 'proof', 'Antigravity'::text, null::text, null::int, '2026-11-27T13:59:42Z'::timestamptz),
(6563, 'Erdos554.erdos_554.variants.jenssen_skokan.R1.H2', 'marcusbuffett', 'proof', 'claude-code'::text, 'claude-fable-5-2'::text, null::int, '2026-11-27T14:01:52Z'::timestamptz),
(6151, 'BusyBeaver.BB_4.R1.H2.R1.H2.R1.H3.R1.H1.R1.H1', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T14:06:53Z'::timestamptz),
(6276, 'Erdos173.erdos_173.R1.H2.R1.H2.R1.H1.R1.H1.R1.H2', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T14:07:58Z'::timestamptz),
(6290, 'Erdos848.erdos_848.R1.H2.R1.H2.R1.H2', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T14:08:38Z'::timestamptz),
(6350, 'LennonPittel.lennon_pittel_conjecture.R3.H2.R1.H2.R1.H4', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T14:14:41Z'::timestamptz),
(6364, 'mo-204379', 'TheWaler', 'proof', 'codex'::text, 'gpt-6'::text, 62::int, '2026-11-27T14:17:20Z'::timestamptz),
(6875, 'Erdos930.erdos_930.variants.consecutive_integers.R1.H4.R1.H2.R1.H1.R1.H3.R1.H4', 'Salofe', 'proof', 'claude-code'::text, 'unknown'::text, null::int, '2026-11-27T14:59:48Z'::timestamptz),
(7405, 'oeis-a055210', 'caa1982', 'proof', 'claude-code'::text, 'claude-opus-5-5'::text, 45::int, '2026-11-27T15:03:31Z'::timestamptz),
(7403, 'oeis-a038867', 'sntntHb', 'proof', 'claude'::text, 'claude-opus-5-5'::text, 35::int, '2026-11-27T15:03:40Z'::timestamptz),
(7410, 'Erdos10.erdos_10.variants.gallagher.R1.H2.R1.H2', 'JamesSlash', 'proof', 'claude-code'::text, 'claude-opus-5-5'::text, null::int, '2026-11-27T15:03:56Z'::timestamptz),
(7379, 'BusyBeaver.BB_4.R1.H2.R1.H2.R1.H3.R1.H1.R1.H1.R1.H1.R1.H2', 'pageman', 'proof', 'cursor'::text, 'composer'::text, null::int, '2026-11-27T15:05:42Z'::timestamptz),
(7372, 'BusyBeaver.BB_4.R1.H2.R1.H1.R1.H3.R1.H2.R1.H4.R1.H2.R1.H4', 'marcusbuffett', 'proof', 'claude-code'::text, 'claude-opus-5-5'::text, null::int, '2026-11-27T15:06:06Z'::timestamptz),
(7361, 'BusyBeaver.BB_4.R1.H2.R1.H1.R1.H3.R1.H2.R1.H4.R1.H2.R1.H3', 'marcusbuffett', 'proof', 'claude-code'::text, 'claude-opus-5-5'::text, null::int, '2026-11-27T15:08:07Z'::timestamptz),
(6987, 'oeis-a302975', 'Sai-yr', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, 45::int, '2026-11-27T15:10:06Z'::timestamptz),
(7193, 'Erdos86.erdos_86.R1.H1', 'ivillar', 'proof', 'claude-code'::text, 'claude-opus-5-5'::text, null::int, '2026-11-27T15:52:17Z'::timestamptz),
(7248, 'Erdos457.erdos_457.variants.one_sub.R1.H1', 'ivillar', 'proof', 'claude-code'::text, 'claude-opus-5-5'::text, null::int, '2026-11-27T15:54:09Z'::timestamptz),
(7650, 'Erdos173.erdos_173.R1.H2.R1.H1.R1.H2.R1.H1.R1.H2.R1.H1', 'marcusbuffett', 'proof', 'claude-code'::text, 'claude-opus-5-5'::text, null::int, '2026-11-27T16:51:31Z'::timestamptz),
(7662, 'oeis-a301517', 'anmolspace', 'disproof', 'codex'::text, 'gpt-6'::text, 45::int, '2026-11-27T16:54:21Z'::timestamptz),
(8357, 'BusyBeaver.BB_4.R1.H2.R1.H2.R1.H3.R1.H2.R1.H2.R1.H1', 'hananzlt', 'proof', 'codex'::text, 'GPT-6 (exact variant unavailable)'::text, null::int, '2026-11-27T17:00:09Z'::timestamptz),
(8378, 'BusyBeaver.BB_4.R1.H2.R1.H2.R1.H3.R1.H2.R1.H3.R1.H3', 'hananzlt', 'proof', 'codex'::text, 'GPT-6 (exact variant unavailable)'::text, null::int, '2026-11-27T17:00:41Z'::timestamptz),
(7644, 'Erdos173.erdos_173.R1.H2.R1.H1.R1.H2.R1.H1.R1.H2.R1.H2', 'marcusbuffett', 'proof', 'claude-code'::text, 'claude-opus-5-5'::text, null::int, '2026-11-27T17:03:39Z'::timestamptz),
(7636, 'Erdos338.erdos_338.variants.triangular.R1.H1.R1.H1.R1.H1.R1.H1.R1.H2.R1.H3', 'Salofe', 'proof', 'claude-code'::text, 'unknown'::text, null::int, '2026-11-27T17:04:12Z'::timestamptz),
(7711, 'OeisA262813.conjecture_1.R1.H1', 'ivillar', 'proof', 'claude-code'::text, 'claude-opus-5-5'::text, null::int, '2026-11-27T17:04:41Z'::timestamptz),
(2940, 'Erdos252.erdos_252', 'senamakel', 'proof', null::text, null::text, 68::int, '2026-11-27T17:06:10Z'::timestamptz),
(7710, 'OeisA262813.conjecture_1.R1.H2', 'ivillar', 'proof', 'claude-code'::text, 'claude-opus-5-5'::text, null::int, '2026-11-27T17:06:16Z'::timestamptz),
(7731, 'BusyBeaver.BB_4.R1.H2.R1.H2.R1.H3.R1.H1.R1.H1.R1.H2.R1.H2', 'pageman', 'proof', 'cursor'::text, 'composer'::text, null::int, '2026-11-27T17:06:22Z'::timestamptz),
(3413, 'Erdos786.erdos_786.parts.i', 'senamakel', 'disproof', null::text, null::text, 69::int, '2026-11-27T17:06:46Z'::timestamptz),
(3096, 'Erdos895.erdos_895.variants.hindman', 'DavidLi-Waibibabo', 'proof', 'codex'::text, 'GPT-6 (exact variant unavailable)'::text, 50::int, '2026-11-27T17:07:03Z'::timestamptz),
(3550, 'Hadamard.HadamardConjecture.variants.167', 'Hiphex', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, 47::int, '2026-11-27T17:07:21Z'::timestamptz),
(7741, 'Erdos1013.erdos_1013.variants.upper.R1.H1.R1.H2', 'marcusbuffett', 'proof', 'claude-code'::text, 'claude-opus-5-5'::text, null::int, '2026-11-27T17:07:27Z'::timestamptz),
(7792, 'OeisA280831.conjecture.R1.H1', 'ivillar', 'proof', 'claude-code'::text, 'claude-opus-5-5'::text, null::int, '2026-11-27T17:11:08Z'::timestamptz),
(7831, 'BusyBeaver.BB_4.R1.H2.R1.H2.R1.H3.R1.H1.R1.H2.R1.H1.R1.H1', 'pageman', 'proof', 'cursor'::text, 'composer'::text, null::int, '2026-11-27T17:14:34Z'::timestamptz),
(7834, 'oeis-a092506', 'Genbox', 'proof', 'codex'::text, 'gpt-6.2-sol'::text, 62::int, '2026-11-27T17:14:49Z'::timestamptz),
(7836, 'oeis-a071287', 'eliayousf', 'disproof', 'codex'::text, 'unknown'::text, 35::int, '2026-11-27T17:14:59Z'::timestamptz),
(7839, 'oeis-a071281', 'senamakel', 'disproof', 'codex'::text, 'GPT-6 with GPT-6 Luna subagents'::text, 35::int, '2026-11-27T17:15:16Z'::timestamptz),
(7841, 'oeis-a000126', 'ShoQo', 'proof', 'claude-code'::text, 'claude-opus-5-5'::text, 35::int, '2026-11-27T17:15:31Z'::timestamptz),
(7843, 'oeis-a081071', 'sntntHb', 'proof', 'claude-code'::text, 'claude-opus-5-5'::text, 35::int, '2026-11-27T17:15:42Z'::timestamptz),
(7844, 'oeis-a071284', 'senamakel', 'proof', 'codex'::text, 'GPT-6 with GPT-6 Luna subagents'::text, 35::int, '2026-11-27T17:15:49Z'::timestamptz),
(7845, 'oeis-a085781', 'dreamzzz-dev', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, 35::int, '2026-11-27T17:15:59Z'::timestamptz),
(7846, 'oeis-a071285', 'senamakel', 'disproof', 'codex'::text, 'GPT-6 with GPT-6 Luna subagents'::text, 35::int, '2026-11-27T17:16:05Z'::timestamptz),
(7848, 'oeis-a071286', 'senamakel', 'proof', 'codex'::text, 'GPT-6 with GPT-6 Luna subagents'::text, 35::int, '2026-11-27T17:16:17Z'::timestamptz)
) v(pr, id, h, pol, ag, mo, pts, m);
-- created_at := merge time, only for rows this transaction created (created_at = now())
update oma_solutions s set created_at = v.m from (values
(5990, '2026-11-27T13:10:48Z'::timestamptz),
(6061, '2026-11-27T13:11:17Z'::timestamptz),
(5991, '2026-11-27T13:11:24Z'::timestamptz),
(6060, '2026-11-27T13:11:30Z'::timestamptz),
(6063, '2026-11-27T13:11:33Z'::timestamptz),
(6794, '2026-11-27T13:47:04Z'::timestamptz),
(6647, '2026-11-27T13:56:27Z'::timestamptz),
(6634, '2026-11-27T13:56:59Z'::timestamptz),
(6595, '2026-11-27T13:59:42Z'::timestamptz),
(6563, '2026-11-27T14:01:52Z'::timestamptz),
(6151, '2026-11-27T14:06:53Z'::timestamptz),
(6276, '2026-11-27T14:07:58Z'::timestamptz),
(6290, '2026-11-27T14:08:38Z'::timestamptz),
(6350, '2026-11-27T14:14:41Z'::timestamptz),
(6364, '2026-11-27T14:17:20Z'::timestamptz),
(6875, '2026-11-27T14:59:48Z'::timestamptz),
(7405, '2026-11-27T15:03:31Z'::timestamptz),
(7403, '2026-11-27T15:03:40Z'::timestamptz),
(7410, '2026-11-27T15:03:56Z'::timestamptz),
(7379, '2026-11-27T15:05:42Z'::timestamptz),
(7372, '2026-11-27T15:06:06Z'::timestamptz),
(7361, '2026-11-27T15:08:07Z'::timestamptz),
(6987, '2026-11-27T15:10:06Z'::timestamptz),
(7193, '2026-11-27T15:52:17Z'::timestamptz),
(7248, '2026-11-27T15:54:09Z'::timestamptz),
(7650, '2026-11-27T16:51:31Z'::timestamptz),
(7662, '2026-11-27T16:54:21Z'::timestamptz),
(8357, '2026-11-27T17:00:09Z'::timestamptz),
(8378, '2026-11-27T17:00:41Z'::timestamptz),
(7644, '2026-11-27T17:03:39Z'::timestamptz),
(7636, '2026-11-27T17:04:12Z'::timestamptz),
(7711, '2026-11-27T17:04:41Z'::timestamptz),
(2940, '2026-11-27T17:06:10Z'::timestamptz),
(7710, '2026-11-27T17:06:16Z'::timestamptz),
(7731, '2026-11-27T17:06:22Z'::timestamptz),
(3413, '2026-11-27T17:06:46Z'::timestamptz),
(3096, '2026-11-27T17:07:03Z'::timestamptz),
(3550, '2026-11-27T17:07:21Z'::timestamptz),
(7741, '2026-11-27T17:07:27Z'::timestamptz),
(7792, '2026-11-27T17:11:08Z'::timestamptz),
(7831, '2026-11-27T17:14:34Z'::timestamptz),
(7834, '2026-11-27T17:14:49Z'::timestamptz),
(7836, '2026-11-27T17:14:59Z'::timestamptz),
(7839, '2026-11-27T17:15:16Z'::timestamptz),
(7841, '2026-11-27T17:15:31Z'::timestamptz),
(7843, '2026-11-27T17:15:42Z'::timestamptz),
(7844, '2026-11-27T17:15:49Z'::timestamptz),
(7845, '2026-11-27T17:15:59Z'::timestamptz),
(7846, '2026-11-27T17:16:05Z'::timestamptz),
(7848, '2026-11-27T17:16:17Z'::timestamptz)
) v(pr, m) where s.pr_url = 'https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/' || v.pr and s.created_at = now();
update oma_events e set created_at = s.created_at from oma_solutions s
  where e.kind = 'accepted' and e.created_at = now() and e.detail = s.pr_url and s.pr_url like 'https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/' || '%' and s.pr_url not like '%#closed';
-- parents closed by this batch (oma_verdict2 climb): dated when their last step was first solved; repeated for nested closures
create temp table _bf_closed on commit drop as select id from oma_solutions where pr_url like '%#closed' and created_at = now();
update oma_solutions c set created_at = x.t from (
  select c2.id, (select max(f.first) from (select min(o.created_at) first from oma_steps st join oma_solutions o on o.problem_id = st.id and o.verdict = 'accepted'
                                            where st.reduction = r.id group by st.id) f) t
  from oma_solutions c2 join _bf_closed k on k.id = c2.id join oma_reductions r on c2.pr_url = r.pr_url || '#closed') x
where c.id = x.id and x.t is not null;
update oma_solutions c set created_at = x.t from (
  select c2.id, (select max(f.first) from (select min(o.created_at) first from oma_steps st join oma_solutions o on o.problem_id = st.id and o.verdict = 'accepted'
                                            where st.reduction = r.id group by st.id) f) t
  from oma_solutions c2 join _bf_closed k on k.id = c2.id join oma_reductions r on c2.pr_url = r.pr_url || '#closed') x
where c.id = x.id and x.t is not null;
update oma_solutions c set created_at = x.t from (
  select c2.id, (select max(f.first) from (select min(o.created_at) first from oma_steps st join oma_solutions o on o.problem_id = st.id and o.verdict = 'accepted'
                                            where st.reduction = r.id group by st.id) f) t
  from oma_solutions c2 join _bf_closed k on k.id = c2.id join oma_reductions r on c2.pr_url = r.pr_url || '#closed') x
where c.id = x.id and x.t is not null;
update oma_solutions c set created_at = x.t from (
  select c2.id, (select max(f.first) from (select min(o.created_at) first from oma_steps st join oma_solutions o on o.problem_id = st.id and o.verdict = 'accepted'
                                            where st.reduction = r.id group by st.id) f) t
  from oma_solutions c2 join _bf_closed k on k.id = c2.id join oma_reductions r on c2.pr_url = r.pr_url || '#closed') x
where c.id = x.id and x.t is not null;
update oma_events e set created_at = c.created_at from oma_solutions c join _bf_closed k on k.id = c.id join oma_reductions r on c.pr_url = r.pr_url || '#closed'
  where e.kind = 'accepted' and e.created_at = now() and e.detail = 'closed by reduction ' || r.id;
commit;

-- ===== batch 14: proofs (50 PRs) =====
begin;
select v.pr, case
  when exists (select 1 from oma_solutions s where s.pr_url = 'https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/' || v.pr) then json_build_object('skip','pr_exists')
  when v.pts is null and not exists (select 1 from oma_steps s where s.id = v.id) then json_build_object('error','unknown_step')
  else oma_verdict2(v.id, v.h, 'https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/' || v.pr, 'accepted', v.pol, v.ag, v.mo,
         case when exists (select 1 from oma_solutions o where o.problem_id = v.id and o.verdict = 'accepted' and o.created_at < v.m) then 0  -- not the first solve
              else coalesce(v.pts, (select s.points from oma_steps s where s.id = v.id)) end) end r
from (values
(7850, 'oeis-a302706', 'caa1982', 'proof', 'codex'::text, 'gpt-6'::text, 35::int, '2026-11-27T17:16:23Z'::timestamptz),
(7849, 'oeis-a113249', 'dk8827', 'proof', 'codex'::text, 'gpt-6.2-sol'::text, 35::int, '2026-11-27T17:16:34Z'::timestamptz),
(7856, 'oeis-a071288', 'senamakel', 'proof', 'codex'::text, 'GPT-6 with GPT-6 Luna subagents'::text, 35::int, '2026-11-27T17:16:49Z'::timestamptz),
(7859, 'oeis-a276646', 'yuka30240', 'proof', 'codex'::text, 'gpt-6'::text, 45::int, '2026-11-27T17:17:28Z'::timestamptz),
(7868, 'Erdos375.erdos_375.variants.bounded_gap.R1.H1.R1.H2.R1.H2', 'Salofe', 'proof', 'claude-code'::text, 'unknown'::text, null::int, '2026-11-27T17:17:54Z'::timestamptz),
(7870, 'oeis-a243928', 'senamakel', 'proof', 'codex'::text, 'GPT-6 with GPT-6 Luna subagents'::text, 35::int, '2026-11-27T17:18:03Z'::timestamptz),
(7878, 'RegularPrimes.isRegularPrime_iff_Bernoulli.R3.H2.R1.H1', 'hananzlt', 'proof', 'codex'::text, 'GPT-6 (exact variant unavailable)'::text, null::int, '2026-11-27T17:18:55Z'::timestamptz),
(7864, 'oeis-a243925', 'senamakel', 'proof', 'codex'::text, 'GPT-6 with GPT-6 Luna subagents'::text, 35::int, '2026-11-27T17:19:01Z'::timestamptz),
(7880, 'Erdos1109.erdos_1109.variants.konyagin_lower', 'amp2600', 'proof', 'codex'::text, 'gpt-6.2-sol'::text, 17::int, '2026-11-27T17:19:03Z'::timestamptz),
(7882, 'oeis-a061062', 'Solfanbtc', 'disproof', 'antigravity'::text, 'gemini-4-neon-high'::text, 45::int, '2026-11-27T17:19:07Z'::timestamptz),
(7886, 'oeis-a155559', 'dk8827', 'proof', 'codex'::text, 'gpt-6.2-sol'::text, 35::int, '2026-11-27T17:19:29Z'::timestamptz),
(7881, 'oeis-a070247.R1.H1', 'yukimiyazaki', 'proof', 'codex'::text, 'gpt-6'::text, null::int, '2026-11-27T17:19:33Z'::timestamptz),
(7889, 'Green84.green_84.variants.littlewood.R1.H1', 'my-other-github-account', 'proof', 'hermes'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T17:19:43Z'::timestamptz),
(7893, 'oeis-a057923', 'Iraeeee', 'proof', 'codex'::text, 'GPT-6'::text, 35::int, '2026-11-27T17:20:05Z'::timestamptz),
(7894, 'oeis-a073642', 'sntntHb', 'proof', 'claude-code'::text, 'claude-opus-5-5'::text, 35::int, '2026-11-27T17:20:07Z'::timestamptz),
(7903, 'RegularPrimes.infinitude_of_irregularprimes.R1.H3', '2undvierzig', 'proof', 'codex'::text, 'gpt-6.2-sol'::text, null::int, '2026-11-27T17:20:50Z'::timestamptz),
(7908, 'oeis-a102239', 'dk8827', 'proof', 'codex'::text, 'gpt-6.2-sol'::text, 35::int, '2026-11-27T17:21:10Z'::timestamptz),
(7919, 'Erdos338.erdos_338.variants.triangular.R1.H1.R1.H1.R1.H1.R1.H1.R1.H2.R1.H2', 'JamesSlash', 'proof', 'claude-code'::text, 'claude-opus-5-5'::text, null::int, '2026-11-27T17:22:01Z'::timestamptz),
(7932, 'oeis-a325695', 'sntntHb', 'proof', 'claude-code'::text, 'claude-opus-5-5'::text, 45::int, '2026-11-27T17:22:36Z'::timestamptz),
(7934, 'Arxiv.2610.08796.exists_isPolyTime_bayesNash.R1.H1', 'Salofe', 'proof', 'claude-code'::text, 'unknown'::text, null::int, '2026-11-27T17:22:38Z'::timestamptz),
(7935, 'Erdos713.erdos_713.parts.ii.R1.H1', 'Salofe', 'proof', 'claude-code'::text, 'unknown'::text, null::int, '2026-11-27T17:22:40Z'::timestamptz),
(4476, 'LennonPittel.lennon_pittel_conjecture.R3.H2.R1.H1', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T17:47:59Z'::timestamptz),
(4465, 'Erdos173.erdos_173.R1.H2.R1.H1.R1.H1', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T17:48:02Z'::timestamptz),
(4416, 'OeisA69191.conjecture_2.R1.H2', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T17:48:12Z'::timestamptz),
(8406, 'BusyBeaver.BB_4.R1.H2.R1.H2.R1.H3.R1.H2.R1.H2.R1.H3', 'hananzlt', 'proof', 'codex'::text, 'GPT-6 (exact variant unavailable)'::text, null::int, '2026-11-27T17:49:09Z'::timestamptz),
(8521, 'BusyBeaver.BB_4.R1.H2.R1.H2.R1.H3.R1.H1.R1.H2.R1.H1', 'hananzlt', 'proof', 'codex'::text, 'GPT-6 (exact variant unavailable)'::text, null::int, '2026-11-27T17:50:52Z'::timestamptz),
(8617, 'FeitThompsonPrimeConjecture.feit_thompson_primes.R1.H3.R1.H1', 'sebastianbachmaier', 'proof', 'claude-code'::text, 'claude-fable-5-2'::text, null::int, '2026-11-27T17:56:40Z'::timestamptz),
(8619, 'BusyBeaver.BB_4.R1.H2.R1.H2.R1.H3.R1.H2.R1.H2.R1.H2', 'pageman', 'proof', 'cursor'::text, 'composer'::text, null::int, '2026-11-27T17:56:58Z'::timestamptz),
(8622, 'BusyBeaver.BB_4.R1.H2.R1.H2.R1.H3.R1.H2.R1.H2.R1.H4', 'pageman', 'proof', 'cursor'::text, 'composer'::text, null::int, '2026-11-27T17:57:07Z'::timestamptz),
(8625, 'MovingSofa.ambidextrousSofaConstant_eq_romiksSofa_area.R1.H2', 'marcusbuffett', 'proof', 'claude-code'::text, 'claude-opus-5-5'::text, null::int, '2026-11-27T17:57:35Z'::timestamptz),
(8639, 'oeis-a375583', 'physbuzz', 'proof', 'codex'::text, 'gpt-6'::text, 45::int, '2026-11-27T17:58:14Z'::timestamptz),
(8641, 'oeis-a034448', 'carl2sheriff', 'proof', 'claude-code'::text, 'Claude'::text, 35::int, '2026-11-27T17:58:22Z'::timestamptz),
(8648, 'erdos-1112', 'TheWaler', 'disproof', 'antigravity'::text, 'Gemini 4 Neon (XHigh)'::text, 69::int, '2026-11-27T17:58:50Z'::timestamptz),
(7911, 'oeis-a226224', 'eskrishnaram-ai', 'proof', 'codex'::text, 'gpt-6.2-sol'::text, 45::int, '2026-11-27T17:59:30Z'::timestamptz),
(8670, 'oeis-a374416', 'physbuzz', 'proof', 'codex'::text, 'gpt-6'::text, 45::int, '2026-11-27T18:00:21Z'::timestamptz),
(8672, 'oeis-a136433', 'yuka30240', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, 45::int, '2026-11-27T18:00:26Z'::timestamptz),
(8722, 'oeis-a003592', 'Iraeeee', 'proof', 'codex'::text, 'GPT-6'::text, 35::int, '2026-11-27T18:03:39Z'::timestamptz),
(8728, 'erdos-634.R1.H3.R1.H3', 'adammcarter', 'proof', 'Claude Code'::text, 'claude-opus-5-5'::text, null::int, '2026-11-27T18:04:12Z'::timestamptz),
(8732, 'Erdos1070.erdos_1070.parts.ii.R1.H1', 'Genbox', 'proof', 'codex'::text, 'gpt-6.2-sol'::text, null::int, '2026-11-27T18:04:21Z'::timestamptz),
(8734, 'RamseyNumbers.ramsey_number_three_eight.R1.H1', 'Iraeeee', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T18:04:29Z'::timestamptz),
(8736, 'SerreMultiplicityConjectures.supportDim_add_supportDim_le_ringKrullDim.R1.H4', 'mattdorman', 'proof', 'antigravity'::text, 'gemini-pro-orchestrator-neon'::text, null::int, '2026-11-27T18:04:51Z'::timestamptz),
(8918, 'Erdos848.erdos_848.R2.H2.R1.H1', 'steveDOTdigital', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T18:14:59Z'::timestamptz),
(8923, 'Erdos848.erdos_848.R2.H2.R1.H4', 'Deldor14', 'proof', 'codex'::text, 'gpt-6'::text, null::int, '2026-11-27T18:15:12Z'::timestamptz),
(8929, 'oeis-a009388', 'yuka30240', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, 45::int, '2026-11-27T18:15:33Z'::timestamptz),
(8933, 'Erdos470.erdos_470.parts.ii.R3.H1', 'Msninmx', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T18:15:35Z'::timestamptz),
(8936, 'oeis-a111108', 'carl2sheriff', 'proof', 'claude-code'::text, 'Claude'::text, 35::int, '2026-11-27T18:16:00Z'::timestamptz),
(8943, 'Erdos536.erdos_536.R1.H2', 'ivillar', 'proof', 'claude-code'::text, 'claude-opus-5-5'::text, null::int, '2026-11-27T18:16:02Z'::timestamptz),
(8944, 'oeis-a256132', 'Iraeeee', 'proof', 'codex'::text, 'GPT-6'::text, 45::int, '2026-11-27T18:16:04Z'::timestamptz),
(8956, 'Erdos406.erdos_406.variants.one_two.R1.H2.R1.H1', 'ivillar', 'proof', 'claude-code'::text, 'claude-opus-5-5'::text, null::int, '2026-11-27T18:16:35Z'::timestamptz),
(8957, 'PerfectNumbers.odd_perfect_number_conjecture.R1.H1.R1.H1', 'marcusbuffett', 'proof', 'claude-code'::text, 'claude-fable-5-2'::text, null::int, '2026-11-27T18:16:39Z'::timestamptz)
) v(pr, id, h, pol, ag, mo, pts, m);
-- created_at := merge time, only for rows this transaction created (created_at = now())
update oma_solutions s set created_at = v.m from (values
(7850, '2026-11-27T17:16:23Z'::timestamptz),
(7849, '2026-11-27T17:16:34Z'::timestamptz),
(7856, '2026-11-27T17:16:49Z'::timestamptz),
(7859, '2026-11-27T17:17:28Z'::timestamptz),
(7868, '2026-11-27T17:17:54Z'::timestamptz),
(7870, '2026-11-27T17:18:03Z'::timestamptz),
(7878, '2026-11-27T17:18:55Z'::timestamptz),
(7864, '2026-11-27T17:19:01Z'::timestamptz),
(7880, '2026-11-27T17:19:03Z'::timestamptz),
(7882, '2026-11-27T17:19:07Z'::timestamptz),
(7886, '2026-11-27T17:19:29Z'::timestamptz),
(7881, '2026-11-27T17:19:33Z'::timestamptz),
(7889, '2026-11-27T17:19:43Z'::timestamptz),
(7893, '2026-11-27T17:20:05Z'::timestamptz),
(7894, '2026-11-27T17:20:07Z'::timestamptz),
(7903, '2026-11-27T17:20:50Z'::timestamptz),
(7908, '2026-11-27T17:21:10Z'::timestamptz),
(7919, '2026-11-27T17:22:01Z'::timestamptz),
(7932, '2026-11-27T17:22:36Z'::timestamptz),
(7934, '2026-11-27T17:22:38Z'::timestamptz),
(7935, '2026-11-27T17:22:40Z'::timestamptz),
(4476, '2026-11-27T17:47:59Z'::timestamptz),
(4465, '2026-11-27T17:48:02Z'::timestamptz),
(4416, '2026-11-27T17:48:12Z'::timestamptz),
(8406, '2026-11-27T17:49:09Z'::timestamptz),
(8521, '2026-11-27T17:50:52Z'::timestamptz),
(8617, '2026-11-27T17:56:40Z'::timestamptz),
(8619, '2026-11-27T17:56:58Z'::timestamptz),
(8622, '2026-11-27T17:57:07Z'::timestamptz),
(8625, '2026-11-27T17:57:35Z'::timestamptz),
(8639, '2026-11-27T17:58:14Z'::timestamptz),
(8641, '2026-11-27T17:58:22Z'::timestamptz),
(8648, '2026-11-27T17:58:50Z'::timestamptz),
(7911, '2026-11-27T17:59:30Z'::timestamptz),
(8670, '2026-11-27T18:00:21Z'::timestamptz),
(8672, '2026-11-27T18:00:26Z'::timestamptz),
(8722, '2026-11-27T18:03:39Z'::timestamptz),
(8728, '2026-11-27T18:04:12Z'::timestamptz),
(8732, '2026-11-27T18:04:21Z'::timestamptz),
(8734, '2026-11-27T18:04:29Z'::timestamptz),
(8736, '2026-11-27T18:04:51Z'::timestamptz),
(8918, '2026-11-27T18:14:59Z'::timestamptz),
(8923, '2026-11-27T18:15:12Z'::timestamptz),
(8929, '2026-11-27T18:15:33Z'::timestamptz),
(8933, '2026-11-27T18:15:35Z'::timestamptz),
(8936, '2026-11-27T18:16:00Z'::timestamptz),
(8943, '2026-11-27T18:16:02Z'::timestamptz),
(8944, '2026-11-27T18:16:04Z'::timestamptz),
(8956, '2026-11-27T18:16:35Z'::timestamptz),
(8957, '2026-11-27T18:16:39Z'::timestamptz)
) v(pr, m) where s.pr_url = 'https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/' || v.pr and s.created_at = now();
update oma_events e set created_at = s.created_at from oma_solutions s
  where e.kind = 'accepted' and e.created_at = now() and e.detail = s.pr_url and s.pr_url like 'https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/' || '%' and s.pr_url not like '%#closed';
-- parents closed by this batch (oma_verdict2 climb): dated when their last step was first solved; repeated for nested closures
create temp table _bf_closed on commit drop as select id from oma_solutions where pr_url like '%#closed' and created_at = now();
update oma_solutions c set created_at = x.t from (
  select c2.id, (select max(f.first) from (select min(o.created_at) first from oma_steps st join oma_solutions o on o.problem_id = st.id and o.verdict = 'accepted'
                                            where st.reduction = r.id group by st.id) f) t
  from oma_solutions c2 join _bf_closed k on k.id = c2.id join oma_reductions r on c2.pr_url = r.pr_url || '#closed') x
where c.id = x.id and x.t is not null;
update oma_solutions c set created_at = x.t from (
  select c2.id, (select max(f.first) from (select min(o.created_at) first from oma_steps st join oma_solutions o on o.problem_id = st.id and o.verdict = 'accepted'
                                            where st.reduction = r.id group by st.id) f) t
  from oma_solutions c2 join _bf_closed k on k.id = c2.id join oma_reductions r on c2.pr_url = r.pr_url || '#closed') x
where c.id = x.id and x.t is not null;
update oma_solutions c set created_at = x.t from (
  select c2.id, (select max(f.first) from (select min(o.created_at) first from oma_steps st join oma_solutions o on o.problem_id = st.id and o.verdict = 'accepted'
                                            where st.reduction = r.id group by st.id) f) t
  from oma_solutions c2 join _bf_closed k on k.id = c2.id join oma_reductions r on c2.pr_url = r.pr_url || '#closed') x
where c.id = x.id and x.t is not null;
update oma_solutions c set created_at = x.t from (
  select c2.id, (select max(f.first) from (select min(o.created_at) first from oma_steps st join oma_solutions o on o.problem_id = st.id and o.verdict = 'accepted'
                                            where st.reduction = r.id group by st.id) f) t
  from oma_solutions c2 join _bf_closed k on k.id = c2.id join oma_reductions r on c2.pr_url = r.pr_url || '#closed') x
where c.id = x.id and x.t is not null;
update oma_events e set created_at = c.created_at from oma_solutions c join _bf_closed k on k.id = c.id join oma_reductions r on c.pr_url = r.pr_url || '#closed'
  where e.kind = 'accepted' and e.created_at = now() and e.detail = 'closed by reduction ' || r.id;
commit;

-- ===== batch 15: proofs (50 PRs) =====
begin;
select v.pr, case
  when exists (select 1 from oma_solutions s where s.pr_url = 'https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/' || v.pr) then json_build_object('skip','pr_exists')
  when v.pts is null and not exists (select 1 from oma_steps s where s.id = v.id) then json_build_object('error','unknown_step')
  else oma_verdict2(v.id, v.h, 'https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/' || v.pr, 'accepted', v.pol, v.ag, v.mo,
         case when exists (select 1 from oma_solutions o where o.problem_id = v.id and o.verdict = 'accepted' and o.created_at < v.m) then 0  -- not the first solve
              else coalesce(v.pts, (select s.points from oma_steps s where s.id = v.id)) end) end r
from (values
(8962, 'Erdos61.erdos_61.variants.bnss23', 'amp2600', 'proof', 'codex'::text, 'gpt-6.2-sol'::text, 18::int, '2026-11-27T18:16:51Z'::timestamptz),
(8963, 'Erdos980.erdos_980.variants.erdos_two.R1.H2.R1.H2', 'physbuzz', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T18:17:01Z'::timestamptz),
(8968, 'oeis-a203159', 'Raimo33', 'proof', 'claude-code'::text, 'unknown'::text, 45::int, '2026-11-27T18:17:20Z'::timestamptz),
(8979, 'oeis-a003435', 'justusklocke-cloud', 'proof', 'claude-code'::text, 'claude-fable-5-2'::text, 35::int, '2026-11-27T18:17:57Z'::timestamptz),
(8986, 'oeis-a207262', 'justusklocke-cloud', 'proof', 'claude-code'::text, 'claude-fable-5-2'::text, 35::int, '2026-11-27T18:18:16Z'::timestamptz),
(8953, 'Mathoverflow17560.mathoverflow_17560.R1.H1', 'marcusbuffett', 'proof', 'claude-code'::text, 'claude-fable-5-2'::text, null::int, '2026-11-27T18:18:26Z'::timestamptz),
(9005, 'Arxiv.2001.02665.ringel_conjecture_large.R1.H2', 'ivillar', 'proof', 'claude-code'::text, 'claude-opus-5-5'::text, null::int, '2026-11-27T18:19:05Z'::timestamptz),
(9000, 'arxiv-2611.14718', 'coracle-us', 'disproof', 'antigravity'::text, 'Gemini 4 Neon'::text, 89::int, '2026-11-27T18:19:37Z'::timestamptz),
(9006, 'Arxiv.2001.02665.ringel_conjecture_large.R1.H3', 'ivillar', 'proof', 'claude-code'::text, 'claude-opus-5-5'::text, null::int, '2026-11-27T18:20:05Z'::timestamptz),
(9017, 'oeis-a164011', 'marcelopierry', 'proof', 'claude-code'::text, 'claude-opus-5-5'::text, 45::int, '2026-11-27T18:20:22Z'::timestamptz),
(9035, 'oeis-a305503', 'Ciphore', 'proof', 'codex'::text, 'gpt-6.2-sol'::text, 62::int, '2026-11-27T18:20:26Z'::timestamptz),
(9045, 'mo-363072', 'carl2sheriff', 'proof', 'claude-code'::text, 'Claude'::text, 62::int, '2026-11-27T18:20:48Z'::timestamptz),
(9047, 'oeis-a000364', 'carl2sheriff', 'disproof', 'claude-code'::text, 'Claude'::text, 35::int, '2026-11-27T18:20:59Z'::timestamptz),
(9049, 'Green14.W_3_13.R1.H1.R2.H2', 'anmolspace', 'proof', 'codex'::text, 'gpt-6'::text, null::int, '2026-11-27T18:21:03Z'::timestamptz),
(9056, 'LennonPittel.lennon_pittel_conjecture.R3.H2.R1.H2.R1.H1.R1.H2', 'marcusbuffett', 'proof', 'claude-code'::text, 'claude-opus-5-5'::text, null::int, '2026-11-27T18:21:18Z'::timestamptz),
(9059, 'oeis-a191993', 'KoaOkano', 'proof', 'codex'::text, 'gpt-6'::text, 35::int, '2026-11-27T18:21:27Z'::timestamptz),
(9052, 'LennonPittel.lennon_pittel_conjecture.R3.H2.R1.H2.R1.H1.R1.H1', 'marcusbuffett', 'proof', 'claude-code'::text, 'claude-opus-5-5'::text, null::int, '2026-11-27T18:21:30Z'::timestamptz),
(9063, 'oeis-a372991', 'justusklocke-cloud', 'proof', 'claude-code'::text, 'claude-fable-5-2'::text, 45::int, '2026-11-27T18:21:34Z'::timestamptz),
(9061, 'Erdos1191.erdos_1191.parts.ii.R2.H2', 'anmolspace', 'proof', 'Codex'::text, 'gpt-6'::text, null::int, '2026-11-27T18:21:56Z'::timestamptz),
(9118, 'mo-187311', 'zarnab222-dev', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, 62::int, '2026-11-27T18:22:32Z'::timestamptz),
(8950, 'Erdos41.erdos_41.R1.H1', 'Iraeeee', 'proof', 'codex'::text, 'gpt-6'::text, null::int, '2026-11-27T18:25:05Z'::timestamptz),
(8980, 'Erdos522.erdos_522.variants.number_real_roots', 'koolkao', 'proof', 'claude-code'::text, 'claude-opus-5-5'::text, 22::int, '2026-11-27T18:25:31Z'::timestamptz),
(9038, 'oeis-a203165', 'ivillar', 'proof', 'claude-code'::text, 'claude-opus-5-5'::text, 45::int, '2026-11-27T18:26:46Z'::timestamptz),
(9066, 'LennonPittel.lennon_pittel_conjecture.R3.H2.R1.H2.R1.H1.R1.H4', 'marcusbuffett', 'proof', 'claude-code'::text, 'claude-opus-5-5'::text, null::int, '2026-11-27T18:27:18Z'::timestamptz),
(9068, 'BusyBeaver.BB_4.R1.H2.R1.H2.R1.H3.R1.H2.R1.H4.R1.H1', 'pageman', 'proof', 'cursor'::text, 'composer'::text, null::int, '2026-11-27T18:27:30Z'::timestamptz),
(9069, 'BusyBeaver.BB_4.R1.H2.R1.H2.R1.H3.R1.H2.R1.H4.R1.H2', 'pageman', 'proof', 'cursor'::text, 'composer'::text, null::int, '2026-11-27T18:27:35Z'::timestamptz),
(9070, 'BusyBeaver.BB_4.R1.H2.R1.H2.R1.H3.R1.H2.R1.H4.R1.H3', 'pageman', 'proof', 'cursor'::text, 'composer'::text, null::int, '2026-11-27T18:27:40Z'::timestamptz),
(9058, 'oeis-a164008', 'marcelopierry', 'proof', 'claude-code'::text, 'claude-opus-5-5'::text, 45::int, '2026-11-27T18:27:44Z'::timestamptz),
(9075, 'oeis-a203232', 'ivillar', 'proof', 'claude-code'::text, 'claude-fable-5-2'::text, 45::int, '2026-11-27T18:27:53Z'::timestamptz),
(9060, 'LennonPittel.lennon_pittel_conjecture.R3.H2.R1.H2.R1.H1.R1.H3', 'marcusbuffett', 'proof', 'claude-code'::text, 'claude-opus-5-5'::text, null::int, '2026-11-27T18:28:18Z'::timestamptz),
(9097, 'mo-373182', 'ivillar', 'proof', 'claude-code'::text, 'claude-opus-5-5'::text, 62::int, '2026-11-27T18:28:45Z'::timestamptz),
(9098, 'oeis-a267514', 'JamesSlash', 'disproof', 'claude-code'::text, 'claude-opus-5-5'::text, 35::int, '2026-11-27T18:28:52Z'::timestamptz),
(9103, 'oeis-a164012', 'marcelopierry', 'proof', 'claude-code'::text, 'claude-opus-5-5'::text, 45::int, '2026-11-27T18:29:08Z'::timestamptz),
(9111, 'oeis-a174349', 'justusklocke-cloud', 'proof', 'claude-code'::text, 'claude-fable-5-2'::text, 45::int, '2026-11-27T18:29:36Z'::timestamptz),
(9122, 'oeis-a260619', 'anmolspace', 'proof', 'codex'::text, 'gpt-6'::text, 45::int, '2026-11-27T18:30:39Z'::timestamptz),
(8491, 'CongruentNumber.Tunnell_even.R1.H2.R1.H2.R1.H1', 'ysanatomic', 'proof', 'Codex'::text, null::text, null::int, '2026-11-27T18:31:30Z'::timestamptz),
(9132, 'oeis-a086845', 'marcelopierry', 'proof', 'claude-code'::text, 'claude-opus-5-5'::text, 35::int, '2026-11-27T18:31:58Z'::timestamptz),
(7258, 'oeis-a233656', 'xor2k', 'proof', 'claude-code'::text, 'claude-fable-5-2'::text, 35::int, '2026-11-27T18:32:13Z'::timestamptz),
(9134, 'oeis-a233398', 'carl2sheriff', 'proof', 'claude-code'::text, 'Claude'::text, 45::int, '2026-11-27T18:32:15Z'::timestamptz),
(9131, 'WeierstrassCurve.Affine.Rat.weakBSD.R1.H1', 'nijv', 'proof', 'antigravity'::text, 'gemini-4-neon'::text, null::int, '2026-11-27T18:32:25Z'::timestamptz),
(9135, 'oeis-a108475', 'marcelopierry', 'proof', 'claude-code'::text, 'claude-opus-5-5'::text, 35::int, '2026-11-27T18:32:28Z'::timestamptz),
(7279, 'oeis-a337949', 'xor2k', 'proof', 'claude-code'::text, 'claude-fable-5-2'::text, 45::int, '2026-11-27T18:32:38Z'::timestamptz),
(9139, 'oeis-a091540', 'justusklocke-cloud', 'proof', 'claude-code'::text, 'claude-fable-5-2'::text, 35::int, '2026-11-27T18:32:49Z'::timestamptz),
(9140, 'oeis-a071622', 'KoaOkano', 'disproof', 'codex'::text, 'gpt-6'::text, 35::int, '2026-11-27T18:32:52Z'::timestamptz),
(9138, 'oeis-a108476', 'marcelopierry', 'proof', 'claude-code'::text, 'claude-opus-5-5'::text, 35::int, '2026-11-27T18:32:55Z'::timestamptz),
(7250, 'oeis-a337951', 'xor2k', 'proof', 'claude-code'::text, 'claude-fable-5-2'::text, 45::int, '2026-11-27T18:32:58Z'::timestamptz),
(9144, 'mo-479301', 'AkiRA-COM-FP', 'disproof', 'codex'::text, 'GPT-6'::text, 62::int, '2026-11-27T18:33:02Z'::timestamptz),
(9148, 'Erdos184.erdos_184.variants.conlon_fox_sudakov', 'amp2600', 'proof', 'codex'::text, 'gpt-6.2-sol'::text, 18::int, '2026-11-27T18:33:13Z'::timestamptz),
(9149, 'oeis-a120740', 'physbuzz', 'proof', 'codex'::text, 'gpt-6'::text, 45::int, '2026-11-27T18:33:25Z'::timestamptz),
(9147, 'oeis-a051195', 'yuka30240', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, 45::int, '2026-11-27T18:34:05Z'::timestamptz)
) v(pr, id, h, pol, ag, mo, pts, m);
-- created_at := merge time, only for rows this transaction created (created_at = now())
update oma_solutions s set created_at = v.m from (values
(8962, '2026-11-27T18:16:51Z'::timestamptz),
(8963, '2026-11-27T18:17:01Z'::timestamptz),
(8968, '2026-11-27T18:17:20Z'::timestamptz),
(8979, '2026-11-27T18:17:57Z'::timestamptz),
(8986, '2026-11-27T18:18:16Z'::timestamptz),
(8953, '2026-11-27T18:18:26Z'::timestamptz),
(9005, '2026-11-27T18:19:05Z'::timestamptz),
(9000, '2026-11-27T18:19:37Z'::timestamptz),
(9006, '2026-11-27T18:20:05Z'::timestamptz),
(9017, '2026-11-27T18:20:22Z'::timestamptz),
(9035, '2026-11-27T18:20:26Z'::timestamptz),
(9045, '2026-11-27T18:20:48Z'::timestamptz),
(9047, '2026-11-27T18:20:59Z'::timestamptz),
(9049, '2026-11-27T18:21:03Z'::timestamptz),
(9056, '2026-11-27T18:21:18Z'::timestamptz),
(9059, '2026-11-27T18:21:27Z'::timestamptz),
(9052, '2026-11-27T18:21:30Z'::timestamptz),
(9063, '2026-11-27T18:21:34Z'::timestamptz),
(9061, '2026-11-27T18:21:56Z'::timestamptz),
(9118, '2026-11-27T18:22:32Z'::timestamptz),
(8950, '2026-11-27T18:25:05Z'::timestamptz),
(8980, '2026-11-27T18:25:31Z'::timestamptz),
(9038, '2026-11-27T18:26:46Z'::timestamptz),
(9066, '2026-11-27T18:27:18Z'::timestamptz),
(9068, '2026-11-27T18:27:30Z'::timestamptz),
(9069, '2026-11-27T18:27:35Z'::timestamptz),
(9070, '2026-11-27T18:27:40Z'::timestamptz),
(9058, '2026-11-27T18:27:44Z'::timestamptz),
(9075, '2026-11-27T18:27:53Z'::timestamptz),
(9060, '2026-11-27T18:28:18Z'::timestamptz),
(9097, '2026-11-27T18:28:45Z'::timestamptz),
(9098, '2026-11-27T18:28:52Z'::timestamptz),
(9103, '2026-11-27T18:29:08Z'::timestamptz),
(9111, '2026-11-27T18:29:36Z'::timestamptz),
(9122, '2026-11-27T18:30:39Z'::timestamptz),
(8491, '2026-11-27T18:31:30Z'::timestamptz),
(9132, '2026-11-27T18:31:58Z'::timestamptz),
(7258, '2026-11-27T18:32:13Z'::timestamptz),
(9134, '2026-11-27T18:32:15Z'::timestamptz),
(9131, '2026-11-27T18:32:25Z'::timestamptz),
(9135, '2026-11-27T18:32:28Z'::timestamptz),
(7279, '2026-11-27T18:32:38Z'::timestamptz),
(9139, '2026-11-27T18:32:49Z'::timestamptz),
(9140, '2026-11-27T18:32:52Z'::timestamptz),
(9138, '2026-11-27T18:32:55Z'::timestamptz),
(7250, '2026-11-27T18:32:58Z'::timestamptz),
(9144, '2026-11-27T18:33:02Z'::timestamptz),
(9148, '2026-11-27T18:33:13Z'::timestamptz),
(9149, '2026-11-27T18:33:25Z'::timestamptz),
(9147, '2026-11-27T18:34:05Z'::timestamptz)
) v(pr, m) where s.pr_url = 'https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/' || v.pr and s.created_at = now();
update oma_events e set created_at = s.created_at from oma_solutions s
  where e.kind = 'accepted' and e.created_at = now() and e.detail = s.pr_url and s.pr_url like 'https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/' || '%' and s.pr_url not like '%#closed';
-- parents closed by this batch (oma_verdict2 climb): dated when their last step was first solved; repeated for nested closures
create temp table _bf_closed on commit drop as select id from oma_solutions where pr_url like '%#closed' and created_at = now();
update oma_solutions c set created_at = x.t from (
  select c2.id, (select max(f.first) from (select min(o.created_at) first from oma_steps st join oma_solutions o on o.problem_id = st.id and o.verdict = 'accepted'
                                            where st.reduction = r.id group by st.id) f) t
  from oma_solutions c2 join _bf_closed k on k.id = c2.id join oma_reductions r on c2.pr_url = r.pr_url || '#closed') x
where c.id = x.id and x.t is not null;
update oma_solutions c set created_at = x.t from (
  select c2.id, (select max(f.first) from (select min(o.created_at) first from oma_steps st join oma_solutions o on o.problem_id = st.id and o.verdict = 'accepted'
                                            where st.reduction = r.id group by st.id) f) t
  from oma_solutions c2 join _bf_closed k on k.id = c2.id join oma_reductions r on c2.pr_url = r.pr_url || '#closed') x
where c.id = x.id and x.t is not null;
update oma_solutions c set created_at = x.t from (
  select c2.id, (select max(f.first) from (select min(o.created_at) first from oma_steps st join oma_solutions o on o.problem_id = st.id and o.verdict = 'accepted'
                                            where st.reduction = r.id group by st.id) f) t
  from oma_solutions c2 join _bf_closed k on k.id = c2.id join oma_reductions r on c2.pr_url = r.pr_url || '#closed') x
where c.id = x.id and x.t is not null;
update oma_solutions c set created_at = x.t from (
  select c2.id, (select max(f.first) from (select min(o.created_at) first from oma_steps st join oma_solutions o on o.problem_id = st.id and o.verdict = 'accepted'
                                            where st.reduction = r.id group by st.id) f) t
  from oma_solutions c2 join _bf_closed k on k.id = c2.id join oma_reductions r on c2.pr_url = r.pr_url || '#closed') x
where c.id = x.id and x.t is not null;
update oma_events e set created_at = c.created_at from oma_solutions c join _bf_closed k on k.id = c.id join oma_reductions r on c.pr_url = r.pr_url || '#closed'
  where e.kind = 'accepted' and e.created_at = now() and e.detail = 'closed by reduction ' || r.id;
commit;

-- ===== batch 16: proofs (50 PRs) =====
begin;
select v.pr, case
  when exists (select 1 from oma_solutions s where s.pr_url = 'https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/' || v.pr) then json_build_object('skip','pr_exists')
  when v.pts is null and not exists (select 1 from oma_steps s where s.id = v.id) then json_build_object('error','unknown_step')
  else oma_verdict2(v.id, v.h, 'https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/' || v.pr, 'accepted', v.pol, v.ag, v.mo,
         case when exists (select 1 from oma_solutions o where o.problem_id = v.id and o.verdict = 'accepted' and o.created_at < v.m) then 0  -- not the first solve
              else coalesce(v.pts, (select s.points from oma_steps s where s.id = v.id)) end) end r
from (values
(9167, 'oeis-a368773', 'caa1982', 'proof', 'claude-code'::text, 'claude-opus-5-5'::text, 45::int, '2026-11-27T18:34:23Z'::timestamptz),
(9168, 'oeis-a266225', 'justusklocke-cloud', 'proof', 'claude-code'::text, 'claude-fable-5-2'::text, 45::int, '2026-11-27T18:34:37Z'::timestamptz),
(9173, 'oeis-a052183', 'Raimo33', 'proof', 'claude-code'::text, 'unknown'::text, 35::int, '2026-11-27T18:34:42Z'::timestamptz),
(9176, 'OeisA4290.conjecture.R1.H1.R1.H3.R1.H3', 'marcusbuffett', 'proof', 'claude-code'::text, 'claude-fable-5-2'::text, null::int, '2026-11-27T18:34:51Z'::timestamptz),
(9177, 'Arxiv.2208.14736.zariski_cancellation_problem.variants.false_pos_card', 'Volkopat', 'proof', 'antigravity'::text, 'gemini'::text, 17::int, '2026-11-27T18:34:53Z'::timestamptz),
(9179, 'OeisA4290.conjecture.R1.H1.R1.H3.R1.H1', 'marcusbuffett', 'proof', 'claude-code'::text, 'claude-fable-5-2'::text, null::int, '2026-11-27T18:34:59Z'::timestamptz),
(9182, 'oeis-a143310', 'marcelopierry', 'proof', 'claude-code'::text, 'claude-opus-5-5'::text, 45::int, '2026-11-27T18:35:06Z'::timestamptz),
(9185, 'OeisA4290.conjecture.R1.H1.R1.H3.R1.H2', 'marcusbuffett', 'proof', 'claude-code'::text, 'claude-fable-5-2'::text, null::int, '2026-11-27T18:35:10Z'::timestamptz),
(9187, 'mse-5127397', 'carl2sheriff', 'disproof', 'claude-code'::text, 'Claude'::text, 53::int, '2026-11-27T18:35:14Z'::timestamptz),
(9188, 'mse-4190405', 'bluesky314', 'proof', 'antigravity'::text, 'Gemini 4 Carbon'::text, 54::int, '2026-11-27T18:35:18Z'::timestamptz),
(9190, 'oeis-a176328', 'justusklocke-cloud', 'proof', 'claude-code'::text, 'claude-fable-5-2'::text, 45::int, '2026-11-27T18:35:27Z'::timestamptz),
(9192, 'Erdos732.erdos_732.parts.i', 'connoranderson', 'proof', 'codex'::text, 'GPT-6'::text, 45::int, '2026-11-27T18:35:34Z'::timestamptz),
(9186, 'Erdos1160.erdos_1160.variants.sum.R2.H2.R1.H2.R1.H1', 'gertjanvdgoot', 'proof', 'claude-code'::text, 'claude-opus-5-5'::text, null::int, '2026-11-27T18:35:38Z'::timestamptz),
(9199, 'oeis-a134347', 'marcelopierry', 'proof', 'claude-code'::text, 'claude-opus-5-5'::text, 45::int, '2026-11-27T18:35:52Z'::timestamptz),
(9200, 'oeis-a127769', 'KoaOkano', 'proof', 'codex'::text, 'gpt-6'::text, 35::int, '2026-11-27T18:35:55Z'::timestamptz),
(9201, 'LovaszPlummerConjecture.sheehan_conjecture.R1.H2.R1.H2.R1.H1', '27mgz45t8z-svg', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T18:35:59Z'::timestamptz),
(9202, 'opg-circular-flow-numbers-of-r-graphs', 'lzvxck', 'disproof', 'claude-code'::text, 'claude-opus-5-5'::text, 92::int, '2026-11-27T18:36:01Z'::timestamptz),
(9203, 'oeis-a318807', 'anmolspace', 'disproof', 'codex'::text, 'gpt-6'::text, 45::int, '2026-11-27T18:36:03Z'::timestamptz),
(9206, 'oeis-a376868', 'marcelopierry', 'proof', 'claude-code'::text, 'claude-opus-5-5'::text, 35::int, '2026-11-27T18:36:05Z'::timestamptz),
(9208, 'OeisA179537.conjecture2', 'draonbioetl', 'proof', 'antigravity'::text, 'gemini-4-neon'::text, 59::int, '2026-11-27T18:36:11Z'::timestamptz),
(9213, 'erdos-684', 'Salofe', 'proof', 'claude-code'::text, 'unknown'::text, 69::int, '2026-11-27T18:36:21Z'::timestamptz),
(9216, 'oeis-a369871', 'bnb9001', 'proof', 'claude-code'::text, 'claude-opus-5-5'::text, 45::int, '2026-11-27T18:36:36Z'::timestamptz),
(9217, 'Arxiv.1601.03081.crystals_components_unique.R1.H2.R1.H2.R1.H1.R1.H2.R1.H1', 'Salofe', 'proof', 'claude-code'::text, 'unknown'::text, null::int, '2026-11-27T18:36:38Z'::timestamptz),
(9250, 'Erdos946.erdos_946.variants.upper_bound', 'amp2600', 'proof', 'codex'::text, 'gpt-6.2-sol'::text, 17::int, '2026-11-27T18:37:00Z'::timestamptz),
(9071, 'BusyBeaver.BB_4.R1.H2.R1.H2.R1.H3.R1.H2.R1.H4.R1.H4', 'pageman', 'proof', 'cursor'::text, 'composer'::text, null::int, '2026-11-27T18:47:26Z'::timestamptz),
(9345, 'Green14.W_3_14.R1.H2.R1.H2.R1.H1', 'Genbox', 'proof', 'codex'::text, 'gpt-6'::text, null::int, '2026-11-27T18:47:52Z'::timestamptz),
(9390, 'Erdos161.erdos_161.parts.ii.R1.H2.R1.H2', 'TheWaler', 'proof', 'codex'::text, 'unknown'::text, null::int, '2026-11-27T18:48:16Z'::timestamptz),
(9407, 'Erdos977.erdos_977.variants.stewart.R1.H3', 'marcusbuffett', 'proof', 'grok'::text, 'grok-4.7'::text, null::int, '2026-11-27T18:48:39Z'::timestamptz),
(9408, 'oeis-a175784', 'ivillar', 'proof', 'claude-code'::text, 'claude-opus-5-5'::text, 45::int, '2026-11-27T18:48:53Z'::timestamptz),
(9443, 'oeis-a330080', 'ivillar', 'proof', 'claude-code'::text, 'claude-opus-5-5'::text, 45::int, '2026-11-27T18:49:08Z'::timestamptz),
(9459, 'oeis-a005994', 'Need17Bread', 'proof', 'antigravity'::text, 'Gemini 4 Neon'::text, 35::int, '2026-11-27T18:49:34Z'::timestamptz),
(9461, 'oeis-a195915', 'Ksungwon09', 'proof', 'antigravity'::text, 'Claude Opus 5.5'::text, 35::int, '2026-11-27T18:49:36Z'::timestamptz),
(9495, 'Green14.W_3_14.R1.H2.R1.H1.R1.H1', 'Genbox', 'proof', 'codex'::text, 'gpt-6'::text, null::int, '2026-11-27T18:50:58Z'::timestamptz),
(9499, 'Green14.W_3_14.R1.H2.R1.H1.R1.H2', 'Genbox', 'proof', 'codex'::text, 'gpt-6'::text, null::int, '2026-11-27T18:51:29Z'::timestamptz),
(9504, 'Green14.W_3_14.R1.H2.R1.H1.R1.H3', 'Genbox', 'proof', 'codex'::text, 'gpt-6'::text, null::int, '2026-11-27T18:51:43Z'::timestamptz),
(9505, 'Erdos978.erdos_978.variants.sub_one.R1.H1', 'koolkao', 'proof', 'claude-code'::text, 'claude-opus-5-5'::text, null::int, '2026-11-27T18:51:46Z'::timestamptz),
(9507, 'Green14.W_3_14.R1.H2.R1.H2.R1.H2', 'Genbox', 'proof', 'codex'::text, 'gpt-6'::text, null::int, '2026-11-27T18:51:50Z'::timestamptz),
(9531, 'Green14.W_3_14.R1.H2.R1.H4.R1.H2', 'LordMike', 'proof', 'claude-code'::text, 'claude-fable-5-2'::text, null::int, '2026-11-27T18:52:17Z'::timestamptz),
(9540, 'oeis-a000254', 'ivillar', 'proof', 'claude-code'::text, 'claude-fable-5-2'::text, 35::int, '2026-11-27T18:52:40Z'::timestamptz),
(9555, 'mo-263706', 'justusklocke-cloud', 'proof', 'claude-code'::text, 'claude-fable-5-2'::text, 62::int, '2026-11-27T18:53:16Z'::timestamptz),
(9556, 'Erdos375.erdos_375.variants.bounded_gap', 'stevenczp', 'proof', 'codex'::text, 'gpt-6'::text, 10::int, '2026-11-27T18:53:29Z'::timestamptz),
(9560, 'Erdos240.erdos_240.variants.tijdeman_finite', 'nijv', 'proof', 'antigravity'::text, 'gemini-4-neon'::text, 18::int, '2026-11-27T18:53:55Z'::timestamptz),
(9597, 'Erdos617.erdos_617.R1.H1', 'MakisChristou', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T18:55:47Z'::timestamptz),
(9600, 'OeisA245211.conjecture.R2.H2', 'MakisChristou', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T18:55:50Z'::timestamptz),
(9604, 'OeisA63880.mod_216_of_a.R1.H1.R2.H1', 'MakisChristou', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T18:56:51Z'::timestamptz),
(9614, 'mo-228227', 'justusklocke-cloud', 'proof', 'claude-code'::text, 'claude-fable-5-2'::text, 62::int, '2026-11-27T18:57:19Z'::timestamptz),
(9628, 'oeis-a183003', 'caa1982', 'proof', 'claude-code'::text, 'claude-opus-5-5'::text, 35::int, '2026-11-27T18:57:58Z'::timestamptz),
(9646, 'Erdos748.erdos_748.variants.asymptotic', 'nijv', 'proof', 'antigravity'::text, 'gemini-4-neon'::text, 17::int, '2026-11-27T18:59:01Z'::timestamptz),
(9653, 'Green77.green_77', 'my-other-github-account', 'disproof', 'hermes'::text, 'gpt-6.2-astra'::text, 68::int, '2026-11-27T18:59:22Z'::timestamptz),
(9654, 'mo-195959', 'ZedingZhang', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, 62::int, '2026-11-27T18:59:34Z'::timestamptz)
) v(pr, id, h, pol, ag, mo, pts, m);
-- created_at := merge time, only for rows this transaction created (created_at = now())
update oma_solutions s set created_at = v.m from (values
(9167, '2026-11-27T18:34:23Z'::timestamptz),
(9168, '2026-11-27T18:34:37Z'::timestamptz),
(9173, '2026-11-27T18:34:42Z'::timestamptz),
(9176, '2026-11-27T18:34:51Z'::timestamptz),
(9177, '2026-11-27T18:34:53Z'::timestamptz),
(9179, '2026-11-27T18:34:59Z'::timestamptz),
(9182, '2026-11-27T18:35:06Z'::timestamptz),
(9185, '2026-11-27T18:35:10Z'::timestamptz),
(9187, '2026-11-27T18:35:14Z'::timestamptz),
(9188, '2026-11-27T18:35:18Z'::timestamptz),
(9190, '2026-11-27T18:35:27Z'::timestamptz),
(9192, '2026-11-27T18:35:34Z'::timestamptz),
(9186, '2026-11-27T18:35:38Z'::timestamptz),
(9199, '2026-11-27T18:35:52Z'::timestamptz),
(9200, '2026-11-27T18:35:55Z'::timestamptz),
(9201, '2026-11-27T18:35:59Z'::timestamptz),
(9202, '2026-11-27T18:36:01Z'::timestamptz),
(9203, '2026-11-27T18:36:03Z'::timestamptz),
(9206, '2026-11-27T18:36:05Z'::timestamptz),
(9208, '2026-11-27T18:36:11Z'::timestamptz),
(9213, '2026-11-27T18:36:21Z'::timestamptz),
(9216, '2026-11-27T18:36:36Z'::timestamptz),
(9217, '2026-11-27T18:36:38Z'::timestamptz),
(9250, '2026-11-27T18:37:00Z'::timestamptz),
(9071, '2026-11-27T18:47:26Z'::timestamptz),
(9345, '2026-11-27T18:47:52Z'::timestamptz),
(9390, '2026-11-27T18:48:16Z'::timestamptz),
(9407, '2026-11-27T18:48:39Z'::timestamptz),
(9408, '2026-11-27T18:48:53Z'::timestamptz),
(9443, '2026-11-27T18:49:08Z'::timestamptz),
(9459, '2026-11-27T18:49:34Z'::timestamptz),
(9461, '2026-11-27T18:49:36Z'::timestamptz),
(9495, '2026-11-27T18:50:58Z'::timestamptz),
(9499, '2026-11-27T18:51:29Z'::timestamptz),
(9504, '2026-11-27T18:51:43Z'::timestamptz),
(9505, '2026-11-27T18:51:46Z'::timestamptz),
(9507, '2026-11-27T18:51:50Z'::timestamptz),
(9531, '2026-11-27T18:52:17Z'::timestamptz),
(9540, '2026-11-27T18:52:40Z'::timestamptz),
(9555, '2026-11-27T18:53:16Z'::timestamptz),
(9556, '2026-11-27T18:53:29Z'::timestamptz),
(9560, '2026-11-27T18:53:55Z'::timestamptz),
(9597, '2026-11-27T18:55:47Z'::timestamptz),
(9600, '2026-11-27T18:55:50Z'::timestamptz),
(9604, '2026-11-27T18:56:51Z'::timestamptz),
(9614, '2026-11-27T18:57:19Z'::timestamptz),
(9628, '2026-11-27T18:57:58Z'::timestamptz),
(9646, '2026-11-27T18:59:01Z'::timestamptz),
(9653, '2026-11-27T18:59:22Z'::timestamptz),
(9654, '2026-11-27T18:59:34Z'::timestamptz)
) v(pr, m) where s.pr_url = 'https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/' || v.pr and s.created_at = now();
update oma_events e set created_at = s.created_at from oma_solutions s
  where e.kind = 'accepted' and e.created_at = now() and e.detail = s.pr_url and s.pr_url like 'https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/' || '%' and s.pr_url not like '%#closed';
-- parents closed by this batch (oma_verdict2 climb): dated when their last step was first solved; repeated for nested closures
create temp table _bf_closed on commit drop as select id from oma_solutions where pr_url like '%#closed' and created_at = now();
update oma_solutions c set created_at = x.t from (
  select c2.id, (select max(f.first) from (select min(o.created_at) first from oma_steps st join oma_solutions o on o.problem_id = st.id and o.verdict = 'accepted'
                                            where st.reduction = r.id group by st.id) f) t
  from oma_solutions c2 join _bf_closed k on k.id = c2.id join oma_reductions r on c2.pr_url = r.pr_url || '#closed') x
where c.id = x.id and x.t is not null;
update oma_solutions c set created_at = x.t from (
  select c2.id, (select max(f.first) from (select min(o.created_at) first from oma_steps st join oma_solutions o on o.problem_id = st.id and o.verdict = 'accepted'
                                            where st.reduction = r.id group by st.id) f) t
  from oma_solutions c2 join _bf_closed k on k.id = c2.id join oma_reductions r on c2.pr_url = r.pr_url || '#closed') x
where c.id = x.id and x.t is not null;
update oma_solutions c set created_at = x.t from (
  select c2.id, (select max(f.first) from (select min(o.created_at) first from oma_steps st join oma_solutions o on o.problem_id = st.id and o.verdict = 'accepted'
                                            where st.reduction = r.id group by st.id) f) t
  from oma_solutions c2 join _bf_closed k on k.id = c2.id join oma_reductions r on c2.pr_url = r.pr_url || '#closed') x
where c.id = x.id and x.t is not null;
update oma_solutions c set created_at = x.t from (
  select c2.id, (select max(f.first) from (select min(o.created_at) first from oma_steps st join oma_solutions o on o.problem_id = st.id and o.verdict = 'accepted'
                                            where st.reduction = r.id group by st.id) f) t
  from oma_solutions c2 join _bf_closed k on k.id = c2.id join oma_reductions r on c2.pr_url = r.pr_url || '#closed') x
where c.id = x.id and x.t is not null;
update oma_events e set created_at = c.created_at from oma_solutions c join _bf_closed k on k.id = c.id join oma_reductions r on c.pr_url = r.pr_url || '#closed'
  where e.kind = 'accepted' and e.created_at = now() and e.detail = 'closed by reduction ' || r.id;
commit;

-- ===== batch 17: proofs (50 PRs) =====
begin;
select v.pr, case
  when exists (select 1 from oma_solutions s where s.pr_url = 'https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/' || v.pr) then json_build_object('skip','pr_exists')
  when v.pts is null and not exists (select 1 from oma_steps s where s.id = v.id) then json_build_object('error','unknown_step')
  else oma_verdict2(v.id, v.h, 'https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/' || v.pr, 'accepted', v.pol, v.ag, v.mo,
         case when exists (select 1 from oma_solutions o where o.problem_id = v.id and o.verdict = 'accepted' and o.created_at < v.m) then 0  -- not the first solve
              else coalesce(v.pts, (select s.points from oma_steps s where s.id = v.id)) end) end r
from (values
(9656, 'oeis-a227864.R1.H1', 'marcusbuffett', 'proof', 'grok'::text, 'grok-4.7'::text, null::int, '2026-11-27T18:59:40Z'::timestamptz),
(9662, 'opg-jaegers-modular-orientation-conjecture', 'lzvxck', 'disproof', 'claude-code'::text, 'claude-opus-5-5'::text, 104::int, '2026-11-27T18:59:58Z'::timestamptz),
(9689, 'mo-501497', 'physbuzz', 'proof', 'codex'::text, 'gpt-6'::text, 62::int, '2026-11-27T19:01:11Z'::timestamptz),
(9683, 'Mills.exists_least.R2.H2', 'ivillar', 'proof', 'claude-code'::text, 'claude-opus-5-5'::text, null::int, '2026-11-27T19:01:14Z'::timestamptz),
(9705, 'oeis-a058764', 'jleguina', 'proof', 'claude-code'::text, 'claude-fable-5-2'::text, 62::int, '2026-11-27T19:02:14Z'::timestamptz),
(9717, 'oeis-a027424', 'justusklocke-cloud', 'proof', 'claude-code'::text, 'claude-fable-5-2'::text, 45::int, '2026-11-27T19:02:33Z'::timestamptz),
(9727, 'mo-202165', 'LDJAI', 'proof', 'Codex'::text, 'GPT-6.2 Astra'::text, 62::int, '2026-11-27T19:02:46Z'::timestamptz),
(9726, 'oeis-a094822', 'justusklocke-cloud', 'proof', 'claude-code'::text, 'claude-fable-5-2'::text, 45::int, '2026-11-27T19:02:48Z'::timestamptz),
(9728, 'oeis-a370261', 'caa1982', 'proof', 'claude-code'::text, 'claude-opus-5-5'::text, 35::int, '2026-11-27T19:02:55Z'::timestamptz),
(9735, 'Erdos107.variants.hmpt_bound.R1.H2', 'mucoucah', 'proof', null::text, null::text, null::int, '2026-11-27T19:03:14Z'::timestamptz),
(9736, 'oeis-a327836', 'justusklocke-cloud', 'proof', 'claude-code'::text, 'claude-fable-5-2'::text, 45::int, '2026-11-27T19:03:17Z'::timestamptz),
(9157, 'oeis-a052379', 'JamesSlash', 'proof', 'claude-code'::text, 'claude-opus-5-5'::text, 35::int, '2026-11-27T19:03:39Z'::timestamptz),
(9752, 'Erdos364.erdos_364.R1.H1', 'marcusbuffett', 'proof', 'claude-code'::text, 'claude-fable-5-2'::text, null::int, '2026-11-27T19:04:12Z'::timestamptz),
(9753, 'Erdos151.erdos_151.variants.cliqueFree_four.R2.H2.R2.H1', 'mythintios', 'proof', 'codex'::text, 'gpt-6'::text, null::int, '2026-11-27T19:04:30Z'::timestamptz),
(9760, 'oeis-a330715', 'JeremyDevs', 'proof', 'claude-code'::text, 'claude-fable-5-2'::text, 45::int, '2026-11-27T19:04:39Z'::timestamptz),
(9762, 'Erdos364.erdos_364.R1.H2', 'marcusbuffett', 'proof', 'claude-code'::text, 'claude-fable-5-2'::text, null::int, '2026-11-27T19:04:46Z'::timestamptz),
(9761, 'oeis-a221981', 'jleguina', 'proof', 'claude-code'::text, 'claude-fable-5-2'::text, 45::int, '2026-11-27T19:04:59Z'::timestamptz),
(9774, 'oeis-a127771', 'justusklocke-cloud', 'proof', 'claude-code'::text, 'claude-fable-5-2'::text, 45::int, '2026-11-27T19:05:10Z'::timestamptz),
(9777, 'oeis-a045473', 'caa1982', 'proof', 'claude-code'::text, 'claude-opus-5-5'::text, 35::int, '2026-11-27T19:05:20Z'::timestamptz),
(9784, 'oeis-a006579', 'KoaOkano', 'disproof', 'codex'::text, 'gpt-6.2-astra'::text, 45::int, '2026-11-27T19:05:29Z'::timestamptz),
(9767, 'oeis-a247339', 'jleguina', 'proof', 'claude-code'::text, 'claude-fable-5-2'::text, 45::int, '2026-11-27T19:05:44Z'::timestamptz),
(9798, 'oeis-a101918', 'luciusacarr', 'disproof', 'claude-code'::text, 'claude-opus-5-5'::text, 45::int, '2026-11-27T19:05:46Z'::timestamptz),
(9806, 'Erdos1145.erdos_1145', 'dk8827', 'disproof', 'codex'::text, 'gpt-6.2-sol'::text, 68::int, '2026-11-27T19:05:54Z'::timestamptz),
(9810, 'oeis-a329227', 'justusklocke-cloud', 'proof', 'claude-code'::text, 'claude-fable-5-2'::text, 45::int, '2026-11-27T19:05:59Z'::timestamptz),
(9814, 'mo-335876', 'ivillar', 'disproof', 'claude-code'::text, 'claude-opus-5-5'::text, 62::int, '2026-11-27T19:06:09Z'::timestamptz),
(9815, 'oeis-a230044', 'jleguina', 'proof', 'claude-code'::text, 'claude-fable-5-2'::text, 45::int, '2026-11-27T19:06:15Z'::timestamptz),
(9816, 'oeis-a355175', 'justusklocke-cloud', 'proof', 'claude-code'::text, 'claude-fable-5-2'::text, 35::int, '2026-11-27T19:06:19Z'::timestamptz),
(9813, 'mo-401222', 'ivillar', 'proof', 'claude-code'::text, 'claude-fable-5-2'::text, 62::int, '2026-11-27T19:06:25Z'::timestamptz),
(9809, 'oeis-a318291', 'jleguina', 'proof', 'claude-code'::text, 'claude-fable-5-2'::text, 45::int, '2026-11-27T19:06:40Z'::timestamptz),
(9850, 'oeis-a025755', 'justusklocke-cloud', 'proof', 'claude-code'::text, 'claude-fable-5-2'::text, 45::int, '2026-11-27T19:06:48Z'::timestamptz),
(9864, 'oeis-a131418', 'justusklocke-cloud', 'proof', 'claude-code'::text, 'claude-fable-5-2'::text, 35::int, '2026-11-27T19:06:55Z'::timestamptz),
(9843, 'oeis-a372313', 'DomTheDeveloper', 'proof', 'codex'::text, 'GPT-6'::text, 45::int, '2026-11-27T19:07:15Z'::timestamptz),
(1289, 'MonochromaticQuantumGraph.eqSystem6_no_solution_ge3.R1.H2', 'shunyaekam', 'proof', 'Codex'::text, 'GPT-6 Codex'::text, null::int, '2026-11-27T19:07:50Z'::timestamptz),
(1363, 'Erdos107.erdos_107.R1.H2', 'VinnyMo', 'proof', 'codex'::text, 'gpt-6'::text, null::int, '2026-11-27T19:11:16Z'::timestamptz),
(9158, 'Erdos151.erdos_151.variants.cliqueFree_four.R2.H2.R1.H1', 'seanm27lol', 'proof', 'Codex'::text, 'GPT-6'::text, null::int, '2026-11-27T19:11:19Z'::timestamptz),
(9437, 'oeis-a135659', 'Raimo33', 'proof', 'claude-code'::text, 'unknown'::text, 35::int, '2026-11-27T19:11:26Z'::timestamptz),
(9509, 'Green14.W_3_14.R1.H2.R1.H3.R1.H2', 'Genbox', 'proof', 'codex'::text, 'gpt-6'::text, null::int, '2026-11-27T19:11:37Z'::timestamptz),
(9464, 'Green14.W_3_14.R1.H2.R1.H4.R1.H1', 'LordMike', 'proof', 'claude-code'::text, 'claude-fable-5-2'::text, null::int, '2026-11-27T19:11:44Z'::timestamptz),
(9651, 'Green100.green_100.variants.operator_norm.R1.H3.R1.H3', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T19:11:59Z'::timestamptz),
(9669, 'Erdos1189.erdos_1189.parts.iii', 'PetrouilFan', 'proof', 'opencode'::text, 'hy4-flash-free'::text, 69::int, '2026-11-27T19:12:18Z'::timestamptz),
(9697, 'Green54.green_54_known_case', 'Volkopat', 'proof', 'antigravity'::text, 'gemini'::text, 28::int, '2026-11-27T19:12:40Z'::timestamptz),
(9708, 'mo-465929', 'LDJAI', 'proof', 'Codex'::text, 'GPT-6.2 Astra'::text, 62::int, '2026-11-27T19:12:52Z'::timestamptz),
(9711, 'mo-270743', 'justusklocke-cloud', 'proof', 'claude-code'::text, 'claude-fable-5-2'::text, 62::int, '2026-11-27T19:14:13Z'::timestamptz),
(9731, 'oeis-a182206', 'xor2k', 'proof', 'claude-code'::text, 'claude-fable-5-2'::text, 45::int, '2026-11-27T19:14:28Z'::timestamptz),
(1440, 'OeisA224.conjecture.R1.H2.R1.H1.R1.H1', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T19:15:29Z'::timestamptz),
(9745, 'OeisA109074.conjecture', 'nijv', 'proof', 'antigravity'::text, 'gemini-4-neon'::text, 27::int, '2026-11-27T19:16:10Z'::timestamptz),
(1552, 'SumnerUniversalTournamentConjecture.sumner_conjecture.R1.H2', 'iskamag', 'proof', 'antigravity'::text, 'Gemini 4 Neon (XHigh)'::text, null::int, '2026-11-27T19:21:43Z'::timestamptz),
(1581, 'SumnerUniversalTournamentConjecture.sumner_conjecture.R1.H1', 'iskamag', 'proof', 'antigravity'::text, 'Gemini 4 Neon (XHigh)'::text, null::int, '2026-11-27T19:23:00Z'::timestamptz),
(7476, 'oeis-a358696', 'taloscoreagent', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, 45::int, '2026-11-27T19:49:35Z'::timestamptz),
(8493, 'CongruentNumber.Tunnell_even.R1.H2.R1.H2.R1.H2.R1.H1', 'ysanatomic', 'proof', 'Codex'::text, null::text, null::int, '2026-11-27T19:51:21Z'::timestamptz)
) v(pr, id, h, pol, ag, mo, pts, m);
-- created_at := merge time, only for rows this transaction created (created_at = now())
update oma_solutions s set created_at = v.m from (values
(9656, '2026-11-27T18:59:40Z'::timestamptz),
(9662, '2026-11-27T18:59:58Z'::timestamptz),
(9689, '2026-11-27T19:01:11Z'::timestamptz),
(9683, '2026-11-27T19:01:14Z'::timestamptz),
(9705, '2026-11-27T19:02:14Z'::timestamptz),
(9717, '2026-11-27T19:02:33Z'::timestamptz),
(9727, '2026-11-27T19:02:46Z'::timestamptz),
(9726, '2026-11-27T19:02:48Z'::timestamptz),
(9728, '2026-11-27T19:02:55Z'::timestamptz),
(9735, '2026-11-27T19:03:14Z'::timestamptz),
(9736, '2026-11-27T19:03:17Z'::timestamptz),
(9157, '2026-11-27T19:03:39Z'::timestamptz),
(9752, '2026-11-27T19:04:12Z'::timestamptz),
(9753, '2026-11-27T19:04:30Z'::timestamptz),
(9760, '2026-11-27T19:04:39Z'::timestamptz),
(9762, '2026-11-27T19:04:46Z'::timestamptz),
(9761, '2026-11-27T19:04:59Z'::timestamptz),
(9774, '2026-11-27T19:05:10Z'::timestamptz),
(9777, '2026-11-27T19:05:20Z'::timestamptz),
(9784, '2026-11-27T19:05:29Z'::timestamptz),
(9767, '2026-11-27T19:05:44Z'::timestamptz),
(9798, '2026-11-27T19:05:46Z'::timestamptz),
(9806, '2026-11-27T19:05:54Z'::timestamptz),
(9810, '2026-11-27T19:05:59Z'::timestamptz),
(9814, '2026-11-27T19:06:09Z'::timestamptz),
(9815, '2026-11-27T19:06:15Z'::timestamptz),
(9816, '2026-11-27T19:06:19Z'::timestamptz),
(9813, '2026-11-27T19:06:25Z'::timestamptz),
(9809, '2026-11-27T19:06:40Z'::timestamptz),
(9850, '2026-11-27T19:06:48Z'::timestamptz),
(9864, '2026-11-27T19:06:55Z'::timestamptz),
(9843, '2026-11-27T19:07:15Z'::timestamptz),
(1289, '2026-11-27T19:07:50Z'::timestamptz),
(1363, '2026-11-27T19:11:16Z'::timestamptz),
(9158, '2026-11-27T19:11:19Z'::timestamptz),
(9437, '2026-11-27T19:11:26Z'::timestamptz),
(9509, '2026-11-27T19:11:37Z'::timestamptz),
(9464, '2026-11-27T19:11:44Z'::timestamptz),
(9651, '2026-11-27T19:11:59Z'::timestamptz),
(9669, '2026-11-27T19:12:18Z'::timestamptz),
(9697, '2026-11-27T19:12:40Z'::timestamptz),
(9708, '2026-11-27T19:12:52Z'::timestamptz),
(9711, '2026-11-27T19:14:13Z'::timestamptz),
(9731, '2026-11-27T19:14:28Z'::timestamptz),
(1440, '2026-11-27T19:15:29Z'::timestamptz),
(9745, '2026-11-27T19:16:10Z'::timestamptz),
(1552, '2026-11-27T19:21:43Z'::timestamptz),
(1581, '2026-11-27T19:23:00Z'::timestamptz),
(7476, '2026-11-27T19:49:35Z'::timestamptz),
(8493, '2026-11-27T19:51:21Z'::timestamptz)
) v(pr, m) where s.pr_url = 'https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/' || v.pr and s.created_at = now();
update oma_events e set created_at = s.created_at from oma_solutions s
  where e.kind = 'accepted' and e.created_at = now() and e.detail = s.pr_url and s.pr_url like 'https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/' || '%' and s.pr_url not like '%#closed';
-- parents closed by this batch (oma_verdict2 climb): dated when their last step was first solved; repeated for nested closures
create temp table _bf_closed on commit drop as select id from oma_solutions where pr_url like '%#closed' and created_at = now();
update oma_solutions c set created_at = x.t from (
  select c2.id, (select max(f.first) from (select min(o.created_at) first from oma_steps st join oma_solutions o on o.problem_id = st.id and o.verdict = 'accepted'
                                            where st.reduction = r.id group by st.id) f) t
  from oma_solutions c2 join _bf_closed k on k.id = c2.id join oma_reductions r on c2.pr_url = r.pr_url || '#closed') x
where c.id = x.id and x.t is not null;
update oma_solutions c set created_at = x.t from (
  select c2.id, (select max(f.first) from (select min(o.created_at) first from oma_steps st join oma_solutions o on o.problem_id = st.id and o.verdict = 'accepted'
                                            where st.reduction = r.id group by st.id) f) t
  from oma_solutions c2 join _bf_closed k on k.id = c2.id join oma_reductions r on c2.pr_url = r.pr_url || '#closed') x
where c.id = x.id and x.t is not null;
update oma_solutions c set created_at = x.t from (
  select c2.id, (select max(f.first) from (select min(o.created_at) first from oma_steps st join oma_solutions o on o.problem_id = st.id and o.verdict = 'accepted'
                                            where st.reduction = r.id group by st.id) f) t
  from oma_solutions c2 join _bf_closed k on k.id = c2.id join oma_reductions r on c2.pr_url = r.pr_url || '#closed') x
where c.id = x.id and x.t is not null;
update oma_solutions c set created_at = x.t from (
  select c2.id, (select max(f.first) from (select min(o.created_at) first from oma_steps st join oma_solutions o on o.problem_id = st.id and o.verdict = 'accepted'
                                            where st.reduction = r.id group by st.id) f) t
  from oma_solutions c2 join _bf_closed k on k.id = c2.id join oma_reductions r on c2.pr_url = r.pr_url || '#closed') x
where c.id = x.id and x.t is not null;
update oma_events e set created_at = c.created_at from oma_solutions c join _bf_closed k on k.id = c.id join oma_reductions r on c.pr_url = r.pr_url || '#closed'
  where e.kind = 'accepted' and e.created_at = now() and e.detail = 'closed by reduction ' || r.id;
commit;

-- ===== batch 18: proofs (27 PRs) =====
begin;
select v.pr, case
  when exists (select 1 from oma_solutions s where s.pr_url = 'https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/' || v.pr) then json_build_object('skip','pr_exists')
  when v.pts is null and not exists (select 1 from oma_steps s where s.id = v.id) then json_build_object('error','unknown_step')
  else oma_verdict2(v.id, v.h, 'https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/' || v.pr, 'accepted', v.pol, v.ag, v.mo,
         case when exists (select 1 from oma_solutions o where o.problem_id = v.id and o.verdict = 'accepted' and o.created_at < v.m) then 0  -- not the first solve
              else coalesce(v.pts, (select s.points from oma_steps s where s.id = v.id)) end) end r
from (values
(9460, 'Erdos161.erdos_161.parts.ii', 'TheWaler', 'proof', 'codex'::text, 'unknown'::text, 99::int, '2026-11-27T19:53:24Z'::timestamptz),
(9473, 'oeis-a057300', 'Raimo33', 'proof', 'claude-code'::text, 'unknown'::text, 35::int, '2026-11-27T19:54:18Z'::timestamptz),
(9474, 'oeis-a008784', 'Raimo33', 'proof', 'claude-code'::text, 'unknown'::text, 45::int, '2026-11-27T19:54:25Z'::timestamptz),
(9475, 'oeis-a088883', 'Raimo33', 'proof', 'claude-code'::text, 'unknown'::text, 45::int, '2026-11-27T19:54:38Z'::timestamptz),
(9496, 'oeis-a002735', 'JamesSlash', 'proof', 'claude-code'::text, 'claude-opus-5-5'::text, 45::int, '2026-11-27T19:54:45Z'::timestamptz),
(9510, 'oeis-a003500', 'JamesSlash', 'proof', 'claude-code'::text, 'claude-opus-5-5'::text, 35::int, '2026-11-27T19:54:53Z'::timestamptz),
(9522, 'oeis-a016789', 'JamesSlash', 'proof', 'claude-code'::text, 'claude-opus-5-5'::text, 35::int, '2026-11-27T19:56:14Z'::timestamptz),
(4387, 'LennonPittel.lennon_pittel_conjecture.R2.H2.R1.H1', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T21:31:53Z'::timestamptz),
(7967, 'BusyBeaver.BB_4.R1.H2.R1.H2.R1.H3.R1.H1.R1.H2.R1.H2', 'hananzlt', 'proof', 'codex'::text, 'GPT-6 (exact variant unavailable)'::text, null::int, '2026-11-27T21:34:27Z'::timestamptz),
(7984, 'Erdos338.erdos_338.variants.triangular.R1.H1.R1.H1.R1.H1.R1.H1.R1.H2.R1.H4', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T21:35:23Z'::timestamptz),
(8096, 'BusyBeaver.BB_4.R1.H2.R1.H2.R1.H3.R1.H2.R1.H3.R1.H2', 'hananzlt', 'proof', 'codex'::text, 'GPT-6 (exact variant unavailable)'::text, null::int, '2026-11-27T21:43:28Z'::timestamptz),
(8188, 'BusyBeaver.BB_4.R1.H2.R1.H2.R1.H3.R1.H2.R1.H1.R1.H2', 'pageman', 'proof', 'cursor'::text, 'composer'::text, null::int, '2026-11-27T21:50:28Z'::timestamptz),
(8334, 'BusyBeaver.BB_4.R1.H2.R1.H2.R1.H3.R1.H2.R1.H3.R1.H1', 'hananzlt', 'proof', 'codex'::text, 'GPT-6 (exact variant unavailable)'::text, null::int, '2026-11-27T21:58:00Z'::timestamptz),
(9239, 'Erdos165.erdos_165.variants.conjecture.R1.H1.R1.H1.R1.H2', 'ivillar', 'proof', 'claude-code'::text, 'claude-opus-5-5'::text, null::int, '2026-11-27T22:05:44Z'::timestamptz),
(9278, 'BusyBeaver.BB_4.R1.H2.R1.H2.R1.H3.R1.H1.R1.H1.R1.H2.R1.H1.R1.H2', 'pageman', 'proof', 'cursor'::text, 'composer'::text, null::int, '2026-11-27T22:07:15Z'::timestamptz),
(9280, 'BusyBeaver.BB_4.R1.H2.R1.H2.R1.H3.R1.H1.R1.H1.R1.H2.R1.H1.R1.H1', 'pageman', 'proof', 'cursor'::text, 'composer'::text, null::int, '2026-11-27T22:07:18Z'::timestamptz),
(9288, 'RiemannHypothesis.robin_criterion.R1.H1.R1.H2.R1.H2.R1.H1.R1.H3', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T22:08:01Z'::timestamptz),
(9293, 'RiemannHypothesis.robin_criterion.R1.H1.R1.H2.R1.H2.R1.H1.R1.H4', 'marcusbuffett', 'proof', 'codex'::text, 'gpt-6.2-astra'::text, null::int, '2026-11-27T22:08:12Z'::timestamptz),
(9788, 'PerfectNumbers.odd_perfect_number_conjecture.R2.H1', 'ivillar', 'proof', 'claude-code'::text, 'claude-opus-5-5'::text, null::int, '2026-11-27T22:30:52Z'::timestamptz),
(8086, 'BusyBeaver.BB_4.R1.H2.R1.H2.R1.H3.R1.H2.R1.H1.R1.H1', 'pageman', 'proof', 'cursor'::text, 'composer'::text, null::int, '2026-11-27T22:31:24Z'::timestamptz),
(9837, 'Bugeaud08.problem_10_8.R1.H1', 'ivillar', 'proof', 'claude-code'::text, 'claude-opus-5-5'::text, null::int, '2026-11-27T22:33:08Z'::timestamptz),
(9845, 'LittlewoodConjecture.padic_littlewood_conjecture.R1.H1', 'ivillar', 'proof', 'claude-code'::text, 'claude-opus-5-5'::text, null::int, '2026-11-27T22:33:40Z'::timestamptz),
(9902, 'Dickson.dickson_conjecture.R1.H1', 'ivillar', 'proof', 'claude-code'::text, 'claude-opus-5-5'::text, null::int, '2026-11-27T22:34:58Z'::timestamptz),
(10925, 'SidorenkoConjecture.sidorenko_conjecture_graphon.R1.H1.R1.H1.R1.H1.R1.H2', 'nijv', 'proof', 'antigravity'::text, 'gemini-4-carbon-high'::text, null::int, '2026-11-27T22:40:02Z'::timestamptz),
(11885, 'Erdos423.erdos_423.variants.upper_bound.R1.H2', 'Salofe', 'proof', 'claude-code'::text, 'unknown'::text, null::int, '2026-11-27T23:01:59Z'::timestamptz),
(11886, 'Erdos963.erdos_963.parts.ii.R1.H1', 'timlantin', 'proof', 'claude-code'::text, 'claude-fable-5-2'::text, null::int, '2026-11-27T23:06:16Z'::timestamptz),
(11984, 'Erdos955.erdos_955.variants.pollack_pomerance_thompson_bound.R1.H1.R1.H3', 'minimumnz', 'proof', 'antigravity'::text, 'Gemini'::text, null::int, '2026-11-27T23:12:23Z'::timestamptz)
) v(pr, id, h, pol, ag, mo, pts, m);
-- created_at := merge time, only for rows this transaction created (created_at = now())
update oma_solutions s set created_at = v.m from (values
(9460, '2026-11-27T19:53:24Z'::timestamptz),
(9473, '2026-11-27T19:54:18Z'::timestamptz),
(9474, '2026-11-27T19:54:25Z'::timestamptz),
(9475, '2026-11-27T19:54:38Z'::timestamptz),
(9496, '2026-11-27T19:54:45Z'::timestamptz),
(9510, '2026-11-27T19:54:53Z'::timestamptz),
(9522, '2026-11-27T19:56:14Z'::timestamptz),
(4387, '2026-11-27T21:31:53Z'::timestamptz),
(7967, '2026-11-27T21:34:27Z'::timestamptz),
(7984, '2026-11-27T21:35:23Z'::timestamptz),
(8096, '2026-11-27T21:43:28Z'::timestamptz),
(8188, '2026-11-27T21:50:28Z'::timestamptz),
(8334, '2026-11-27T21:58:00Z'::timestamptz),
(9239, '2026-11-27T22:05:44Z'::timestamptz),
(9278, '2026-11-27T22:07:15Z'::timestamptz),
(9280, '2026-11-27T22:07:18Z'::timestamptz),
(9288, '2026-11-27T22:08:01Z'::timestamptz),
(9293, '2026-11-27T22:08:12Z'::timestamptz),
(9788, '2026-11-27T22:30:52Z'::timestamptz),
(8086, '2026-11-27T22:31:24Z'::timestamptz),
(9837, '2026-11-27T22:33:08Z'::timestamptz),
(9845, '2026-11-27T22:33:40Z'::timestamptz),
(9902, '2026-11-27T22:34:58Z'::timestamptz),
(10925, '2026-11-27T22:40:02Z'::timestamptz),
(11885, '2026-11-27T23:01:59Z'::timestamptz),
(11886, '2026-11-27T23:06:16Z'::timestamptz),
(11984, '2026-11-27T23:12:23Z'::timestamptz)
) v(pr, m) where s.pr_url = 'https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/' || v.pr and s.created_at = now();
update oma_events e set created_at = s.created_at from oma_solutions s
  where e.kind = 'accepted' and e.created_at = now() and e.detail = s.pr_url and s.pr_url like 'https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/' || '%' and s.pr_url not like '%#closed';
-- parents closed by this batch (oma_verdict2 climb): dated when their last step was first solved; repeated for nested closures
create temp table _bf_closed on commit drop as select id from oma_solutions where pr_url like '%#closed' and created_at = now();
update oma_solutions c set created_at = x.t from (
  select c2.id, (select max(f.first) from (select min(o.created_at) first from oma_steps st join oma_solutions o on o.problem_id = st.id and o.verdict = 'accepted'
                                            where st.reduction = r.id group by st.id) f) t
  from oma_solutions c2 join _bf_closed k on k.id = c2.id join oma_reductions r on c2.pr_url = r.pr_url || '#closed') x
where c.id = x.id and x.t is not null;
update oma_solutions c set created_at = x.t from (
  select c2.id, (select max(f.first) from (select min(o.created_at) first from oma_steps st join oma_solutions o on o.problem_id = st.id and o.verdict = 'accepted'
                                            where st.reduction = r.id group by st.id) f) t
  from oma_solutions c2 join _bf_closed k on k.id = c2.id join oma_reductions r on c2.pr_url = r.pr_url || '#closed') x
where c.id = x.id and x.t is not null;
update oma_solutions c set created_at = x.t from (
  select c2.id, (select max(f.first) from (select min(o.created_at) first from oma_steps st join oma_solutions o on o.problem_id = st.id and o.verdict = 'accepted'
                                            where st.reduction = r.id group by st.id) f) t
  from oma_solutions c2 join _bf_closed k on k.id = c2.id join oma_reductions r on c2.pr_url = r.pr_url || '#closed') x
where c.id = x.id and x.t is not null;
update oma_solutions c set created_at = x.t from (
  select c2.id, (select max(f.first) from (select min(o.created_at) first from oma_steps st join oma_solutions o on o.problem_id = st.id and o.verdict = 'accepted'
                                            where st.reduction = r.id group by st.id) f) t
  from oma_solutions c2 join _bf_closed k on k.id = c2.id join oma_reductions r on c2.pr_url = r.pr_url || '#closed') x
where c.id = x.id and x.t is not null;
update oma_events e set created_at = c.created_at from oma_solutions c join _bf_closed k on k.id = c.id join oma_reductions r on c.pr_url = r.pr_url || '#closed'
  where e.kind = 'accepted' and e.created_at = now() and e.detail = 'closed by reduction ' || r.id;
commit;

-- ===== batch 19: shorter-proof replacements (11 PRs) =====
begin;
select v.pr, oma_log('shorter', v.id, v.h, 'https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/' || v.pr) r from (values
(7840, 'oeis-a038867', 'caa1982'),
(8638, 'Erdos604.erdos_604.variants.average.R2.H2.R1.H2', 'sturdy4days'),
(8662, 'oeis-a037250', 'Iraeeee'),
(8677, 'Erdos359.erdos_359.variants.isGoodFor_1_low_values', 'jsjhc'),
(8940, 'OeisA189409.conjecture_1', 'eskrishnaram-ai'),
(9341, 'OeisA230718.conjecture.R1.H2', 'Ciphore'),
(3531, 'Erdos835.erdos_835.variants.johnson.R2.H2', 'MakisChristou'),
(9528, 'Erdos338.erdos_338.variants.squares.R1.H1', 'happycamper'),
(9699, 'oeis-a070247.R1.H1', 'dwilfand-sys'),
(9723, 'oeis-a169597', 'dwilfand-sys'),
(9513, 'Firoozbakht.firoozbakht_conjecture_consequence.R1.H2', 'dwilfand-sys')
) v(pr, id, h);
-- created_at := merge time, only for events this transaction created (created_at = now())
update oma_events e set created_at = v.m from (values
(7840, '2026-11-27T17:15:25Z'::timestamptz),
(8638, '2026-11-27T17:58:08Z'::timestamptz),
(8662, '2026-11-27T17:59:54Z'::timestamptz),
(8677, '2026-11-27T18:00:51Z'::timestamptz),
(8940, '2026-11-27T18:15:47Z'::timestamptz),
(9341, '2026-11-27T18:47:42Z'::timestamptz),
(3531, '2026-11-27T18:48:20Z'::timestamptz),
(9528, '2026-11-27T18:52:36Z'::timestamptz),
(9699, '2026-11-27T19:01:33Z'::timestamptz),
(9723, '2026-11-27T19:02:43Z'::timestamptz),
(9513, '2026-11-27T19:56:02Z'::timestamptz)
) v(pr, m) where e.kind = 'shorter' and e.detail = 'https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/' || v.pr and e.created_at = now();
commit;

-- ===== batch 20: statements (50 PRs) =====
begin;
select v.pr, oma_log('formalized', v.id, v.h, 'https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/' || v.pr) r from (values
(5411, 'oeis-a130729', 'AkiRA-COM-FP'),
(6185, 'wp-can-every-integer-be-written-as-a-sum-of-four-perfect-cubes', 'sauronsoul-bit'),
(6176, 'wp-are-there-infinitely-many-newman-shanks-williams-primes', 'LordMike'),
(6173, 'mo-407245', 'TheWaler'),
(6046, 'opg-arc-disjoint-directed-cycles-in-regular-directed-graphs', 'LAPRAI'),
(6057, 'oeis-a342992', 'niclorusso'),
(7416, 'oeis-a302706', 'caa1982'),
(7409, 'oeis-a067576', 'Sai-yr'),
(7408, 'oeis-a081071', 'ShoQo'),
(7413, 'oeis-a140831', 'Sai-yr'),
(6930, 'oeis-a000364', 'justusklocke-cloud'),
(7617, 'mo-501497', 'Sai-yr'),
(7652, 'oeis-a207262', 'KoaOkano'),
(8424, 'oeis-a267514', 'eliayousf'),
(7732, 'oeis-a248054', 'sntntHb'),
(7730, 'wp-erdos-faber-lovasz-conjecture-on-coloring-unions-of-cliques', 'Dugongue'),
(7736, 'oeis-a091540', 'Heart-galaxy'),
(7729, 'oeis-a096127', 'garrytaulu'),
(7737, 'oeis-a239884', 'garrytaulu'),
(7742, 'oeis-a086845', 'marcelopierry'),
(7744, 'oeis-a108475', 'marcelopierry'),
(7748, 'oeis-a108476', 'marcelopierry'),
(7743, 'mo-501259', 'Dugongue'),
(7837, 'oeis-a258803', 'divmxnd0x'),
(1259, 'mo-271503', 'koolkao'),
(1260, 'mo-195959', 'koolkao'),
(7842, 'mo-437849', 'prasledi'),
(7827, 'mo-514879', 'rleshner'),
(7847, 'oeis-a370261', 'marcelopierry'),
(7860, 'oeis-a096306', 'MMexicann'),
(7865, 'oeis-a081670', 'con123-gif'),
(7874, 'oeis-a259492', 'divmxnd0x'),
(7884, 'oeis-a266982', 'LoopsGod'),
(7892, 'oeis-a260113', 'physbuzz'),
(7888, 'mo-342609', 'prasledi'),
(7895, 'oeis-a195915', 'senamakel'),
(7899, 'oeis-a259531', 'divmxnd0x'),
(7900, 'oeis-a273798', 'marcelopierry'),
(7902, 'oeis-a378616', 'marcelopierry'),
(7905, 'oeis-a238952', 'anmolspace'),
(8597, 'oeis-a228410', 'eliayousf'),
(8599, 'oeis-a318291', 'jleguina'),
(8602, 'mo-335694', 'Spinausore'),
(8601, 'mo-302653', 'eliayousf'),
(8585, 'oeis-a002742', 'sntntHb'),
(8609, 'oeis-a369275', 'Heart-galaxy'),
(8611, 'oeis-a352241', 'physbuzz'),
(8612, 'oeis-a035378', 'sntntHb'),
(8613, 'oeis-a111883', 'Heart-galaxy'),
(8615, 'oeis-a274334', 'sntntHb')
) v(pr, id, h);
-- created_at := merge time, only for events this transaction created (created_at = now())
update oma_events e set created_at = v.m from (values
(5411, '2026-11-27T11:33:30Z'::timestamptz),
(6185, '2026-11-27T13:03:50Z'::timestamptz),
(6176, '2026-11-27T13:04:05Z'::timestamptz),
(6173, '2026-11-27T13:04:44Z'::timestamptz),
(6046, '2026-11-27T13:11:14Z'::timestamptz),
(6057, '2026-11-27T13:11:50Z'::timestamptz),
(7416, '2026-11-27T15:02:11Z'::timestamptz),
(7409, '2026-11-27T15:02:54Z'::timestamptz),
(7408, '2026-11-27T15:03:12Z'::timestamptz),
(7413, '2026-11-27T15:03:21Z'::timestamptz),
(6930, '2026-11-27T15:10:03Z'::timestamptz),
(7617, '2026-11-27T16:53:56Z'::timestamptz),
(7652, '2026-11-27T16:54:02Z'::timestamptz),
(8424, '2026-11-27T16:55:10Z'::timestamptz),
(7732, '2026-11-27T17:06:31Z'::timestamptz),
(7730, '2026-11-27T17:06:42Z'::timestamptz),
(7736, '2026-11-27T17:06:53Z'::timestamptz),
(7729, '2026-11-27T17:06:58Z'::timestamptz),
(7737, '2026-11-27T17:07:18Z'::timestamptz),
(7742, '2026-11-27T17:07:29Z'::timestamptz),
(7744, '2026-11-27T17:07:35Z'::timestamptz),
(7748, '2026-11-27T17:07:51Z'::timestamptz),
(7743, '2026-11-27T17:07:54Z'::timestamptz),
(7837, '2026-11-27T17:15:05Z'::timestamptz),
(1259, '2026-11-27T17:15:11Z'::timestamptz),
(1260, '2026-11-27T17:15:28Z'::timestamptz),
(7842, '2026-11-27T17:15:46Z'::timestamptz),
(7827, '2026-11-27T17:16:20Z'::timestamptz),
(7847, '2026-11-27T17:16:32Z'::timestamptz),
(7860, '2026-11-27T17:17:06Z'::timestamptz),
(7865, '2026-11-27T17:17:39Z'::timestamptz),
(7874, '2026-11-27T17:18:31Z'::timestamptz),
(7884, '2026-11-27T17:19:20Z'::timestamptz),
(7892, '2026-11-27T17:19:51Z'::timestamptz),
(7888, '2026-11-27T17:19:54Z'::timestamptz),
(7895, '2026-11-27T17:20:09Z'::timestamptz),
(7899, '2026-11-27T17:20:27Z'::timestamptz),
(7900, '2026-11-27T17:20:38Z'::timestamptz),
(7902, '2026-11-27T17:20:42Z'::timestamptz),
(7905, '2026-11-27T17:20:58Z'::timestamptz),
(8597, '2026-11-27T17:55:00Z'::timestamptz),
(8599, '2026-11-27T17:55:07Z'::timestamptz),
(8602, '2026-11-27T17:55:16Z'::timestamptz),
(8601, '2026-11-27T17:55:21Z'::timestamptz),
(8585, '2026-11-27T17:55:35Z'::timestamptz),
(8609, '2026-11-27T17:55:55Z'::timestamptz),
(8611, '2026-11-27T17:55:59Z'::timestamptz),
(8612, '2026-11-27T17:56:09Z'::timestamptz),
(8613, '2026-11-27T17:56:13Z'::timestamptz),
(8615, '2026-11-27T17:56:27Z'::timestamptz)
) v(pr, m) where e.kind = 'formalized' and e.detail = 'https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/' || v.pr and e.created_at = now();
commit;

-- ===== batch 21: statements (50 PRs) =====
begin;
select v.pr, oma_log('formalized', v.id, v.h, 'https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/' || v.pr) r from (values
(8610, 'wpc-crouzeix-conjecture', 'my-other-github-account'),
(8616, 'oeis-a131418', 'rorcores'),
(8618, 'oeis-a275667', 'eliayousf'),
(8624, 'arxiv-2603.15098', 'my-other-github-account'),
(8628, 'oeis-a397711', 'Heart-galaxy'),
(8629, 'oeis-a126364', 'Heart-galaxy'),
(8627, 'arxiv-2409.19103', 'my-other-github-account'),
(8633, 'mo-62548', 'my-other-github-account'),
(8636, 'mo-335876', 'AkiRA-COM-FP'),
(8637, 'oeis-a387043', 'divmxnd0x'),
(8643, 'oeis-a208658', 'Heart-galaxy'),
(8645, 'mo-401222', 'AkiRA-COM-FP'),
(8647, 'oeis-a236464', 'darealpandaboi'),
(8659, 'oeis-a389789', 'divmxnd0x'),
(8653, 'oeis-a136050', 'rorcores'),
(8657, 'oeis-a002735', 'Heart-galaxy'),
(8667, 'oeis-a057081', 'ecirak42'),
(8668, 'oeis-a246048', 'ecirak42'),
(8669, 'oeis-a081921', 'Heart-galaxy'),
(8673, 'oeis-a232463', 'sntntHb'),
(8674, 'oeis-a290003', 'Heart-galaxy'),
(8684, 'oeis-a158460', 'ShoQo'),
(8715, 'oeis-a067281', 'Heart-galaxy'),
(8718, 'oeis-a088508', 'sntntHb'),
(8723, 'mo-189061', 'eliayousf'),
(8721, 'oeis-a246396', 'rorcores'),
(8726, 'oeis-a344598', 'canneyi'),
(8729, 'oeis-a125189', 'Heart-galaxy'),
(8730, 'oeis-a168147', 'sntntHb'),
(8738, 'oeis-a355326', 'Heart-galaxy'),
(8739, 'oeis-a292082', 'LAPRAI'),
(8745, 'oeis-a387947', 'divmxnd0x'),
(8919, 'oeis-a113256', 'xor2k'),
(8916, 'mo-499788', 'zarnab222-dev'),
(8924, 'oeis-a267262', 'jleguina'),
(8926, 'oeis-a389517', 'divmxnd0x'),
(8927, 'oeis-a034444', 'eliayousf'),
(8928, 'oeis-a267923', 'jleguina'),
(8930, 'mo-217656', 'AkiRA-COM-FP'),
(8937, 'oeis-a364906', 'caa1982'),
(8945, 'oeis-a176268', 'LAPRAI'),
(8946, 'oeis-a038663', 'KoaOkano'),
(8948, 'oeis-a008784', 'ShoQo'),
(8949, 'oeis-a088883', 'LAPRAI'),
(8942, 'oeis-a361904', 'LAPRAI'),
(8954, 'oeis-a382437', 'canneyi'),
(8966, 'oeis-a138904', 'caa1982'),
(8961, 'oeis-a389525', 'divmxnd0x'),
(8969, 'oeis-a057300', 'ecirak42'),
(8976, 'oeis-a225004', 'LAPRAI')
) v(pr, id, h);
-- created_at := merge time, only for events this transaction created (created_at = now())
update oma_events e set created_at = v.m from (values
(8610, '2026-11-27T17:56:50Z'::timestamptz),
(8616, '2026-11-27T17:56:53Z'::timestamptz),
(8618, '2026-11-27T17:56:55Z'::timestamptz),
(8624, '2026-11-27T17:57:12Z'::timestamptz),
(8628, '2026-11-27T17:57:24Z'::timestamptz),
(8629, '2026-11-27T17:57:28Z'::timestamptz),
(8627, '2026-11-27T17:57:32Z'::timestamptz),
(8633, '2026-11-27T17:57:46Z'::timestamptz),
(8636, '2026-11-27T17:57:59Z'::timestamptz),
(8637, '2026-11-27T17:58:05Z'::timestamptz),
(8643, '2026-11-27T17:58:28Z'::timestamptz),
(8645, '2026-11-27T17:58:35Z'::timestamptz),
(8647, '2026-11-27T17:58:53Z'::timestamptz),
(8659, '2026-11-27T17:59:32Z'::timestamptz),
(8653, '2026-11-27T17:59:35Z'::timestamptz),
(8657, '2026-11-27T17:59:48Z'::timestamptz),
(8667, '2026-11-27T18:00:05Z'::timestamptz),
(8668, '2026-11-27T18:00:09Z'::timestamptz),
(8669, '2026-11-27T18:00:18Z'::timestamptz),
(8673, '2026-11-27T18:00:32Z'::timestamptz),
(8674, '2026-11-27T18:00:37Z'::timestamptz),
(8684, '2026-11-27T18:01:14Z'::timestamptz),
(8715, '2026-11-27T18:03:03Z'::timestamptz),
(8718, '2026-11-27T18:03:25Z'::timestamptz),
(8723, '2026-11-27T18:03:42Z'::timestamptz),
(8721, '2026-11-27T18:03:51Z'::timestamptz),
(8726, '2026-11-27T18:03:59Z'::timestamptz),
(8729, '2026-11-27T18:04:14Z'::timestamptz),
(8730, '2026-11-27T18:04:17Z'::timestamptz),
(8738, '2026-11-27T18:04:43Z'::timestamptz),
(8739, '2026-11-27T18:05:05Z'::timestamptz),
(8745, '2026-11-27T18:05:10Z'::timestamptz),
(8919, '2026-11-27T18:15:02Z'::timestamptz),
(8916, '2026-11-27T18:15:07Z'::timestamptz),
(8924, '2026-11-27T18:15:16Z'::timestamptz),
(8926, '2026-11-27T18:15:19Z'::timestamptz),
(8927, '2026-11-27T18:15:21Z'::timestamptz),
(8928, '2026-11-27T18:15:24Z'::timestamptz),
(8930, '2026-11-27T18:15:30Z'::timestamptz),
(8937, '2026-11-27T18:15:43Z'::timestamptz),
(8945, '2026-11-27T18:16:08Z'::timestamptz),
(8946, '2026-11-27T18:16:13Z'::timestamptz),
(8948, '2026-11-27T18:16:19Z'::timestamptz),
(8949, '2026-11-27T18:16:21Z'::timestamptz),
(8942, '2026-11-27T18:16:25Z'::timestamptz),
(8954, '2026-11-27T18:16:33Z'::timestamptz),
(8966, '2026-11-27T18:17:11Z'::timestamptz),
(8961, '2026-11-27T18:17:16Z'::timestamptz),
(8969, '2026-11-27T18:17:26Z'::timestamptz),
(8976, '2026-11-27T18:17:42Z'::timestamptz)
) v(pr, m) where e.kind = 'formalized' and e.detail = 'https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/' || v.pr and e.created_at = now();
commit;

-- ===== batch 22: statements (50 PRs) =====
begin;
select v.pr, oma_log('formalized', v.id, v.h, 'https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/' || v.pr) r from (values
(8977, 'oeis-a084261', 'ecirak42'),
(8983, 'mo-473367', 'AkiRA-COM-FP'),
(8984, 'erdos-550', 'sntntHb'),
(8999, 'oeis-a213203', 'agchua'),
(9004, 'oeis-a336276', 'LAPRAI'),
(9009, 'oeis-a336277', 'LAPRAI'),
(9011, 'oeis-a026008', 'KoaOkano'),
(9012, 'oeis-a336278', 'LAPRAI'),
(9016, 'oeis-a336279', 'LAPRAI'),
(9019, 'oeis-a383377', 'ecirak42'),
(9026, 'oeis-a003325', 'justusklocke-cloud'),
(9037, 'oeis-a255746', 'LAPRAI'),
(9039, 'oeis-a274010', 'rorcores'),
(9041, 'oeis-a182457', 'LAPRAI'),
(9043, 'oeis-a182458', 'LAPRAI'),
(9048, 'oeis-a002467', 'rot13maxi'),
(9054, 'mse-2172922', 'ecirak42'),
(9064, 'mse-2145404', 'ecirak42'),
(9065, 'oeis-a158013', 'LAPRAI'),
(9082, 'oeis-a001076', 'rot13maxi'),
(9113, 'oeis-a385736', 'ecirak42'),
(9092, 'oeis-a134641', 'ShoQo'),
(9083, 'oeis-a036447', 'gblacher2'),
(8896, 'oeis-a267461', 'jleguina'),
(8964, 'oeis-a386580', 'caa1982'),
(8967, 'oeis-a228791', 'ecirak42'),
(8972, 'oeis-a367191', 'rorcores'),
(8981, 'mo-196613', 'PastaPastaPasta'),
(8992, 'oeis-a372430', 'jleguina'),
(8990, 'oeis-a139035', 'ShoQo'),
(9027, 'oeis-a086222', 'Iraeeee'),
(9030, 'oeis-a377119', 'ecirak42'),
(9137, 'oeis-a192205', 'Iraeeee'),
(9151, 'mo-412446', 'AkiRA-COM-FP'),
(9153, 'oeis-a067360', 'JeremyDevs'),
(9159, 'oeis-a384531', 'anmolspace'),
(9161, 'oeis-a151341', 'anmolspace'),
(9165, 'oeis-a392943', 'ecirak42'),
(9169, 'oeis-a265284', 'ecirak42'),
(9175, 'oeis-a076902', 'KoaOkano'),
(9183, 'oeis-a091539', 'eliayousf'),
(9193, 'mse-3400484', 'ecirak42'),
(9196, 'oeis-a006093', 'justusklocke-cloud'),
(9198, 'oeis-a001227', 'rot13maxi'),
(9207, 'oeis-a334765', 'anmolspace'),
(9214, 'oeis-a134119', 'ivillar'),
(9219, 'oeis-a182079', 'ivillar'),
(9251, 'oeis-a001936', 'rot13maxi'),
(9273, 'oeis-a284005', 'eliayousf'),
(9274, 'oeis-a163617', 'JeremyDevs')
) v(pr, id, h);
-- created_at := merge time, only for events this transaction created (created_at = now())
update oma_events e set created_at = v.m from (values
(8977, '2026-11-27T18:17:47Z'::timestamptz),
(8983, '2026-11-27T18:18:02Z'::timestamptz),
(8984, '2026-11-27T18:18:28Z'::timestamptz),
(8999, '2026-11-27T18:18:49Z'::timestamptz),
(9004, '2026-11-27T18:18:59Z'::timestamptz),
(9009, '2026-11-27T18:19:14Z'::timestamptz),
(9011, '2026-11-27T18:19:30Z'::timestamptz),
(9012, '2026-11-27T18:19:44Z'::timestamptz),
(9016, '2026-11-27T18:19:52Z'::timestamptz),
(9019, '2026-11-27T18:20:07Z'::timestamptz),
(9026, '2026-11-27T18:20:18Z'::timestamptz),
(9037, '2026-11-27T18:20:30Z'::timestamptz),
(9039, '2026-11-27T18:20:33Z'::timestamptz),
(9041, '2026-11-27T18:20:41Z'::timestamptz),
(9043, '2026-11-27T18:20:45Z'::timestamptz),
(9048, '2026-11-27T18:21:01Z'::timestamptz),
(9054, '2026-11-27T18:21:15Z'::timestamptz),
(9064, '2026-11-27T18:21:38Z'::timestamptz),
(9065, '2026-11-27T18:21:42Z'::timestamptz),
(9082, '2026-11-27T18:21:53Z'::timestamptz),
(9113, '2026-11-27T18:22:18Z'::timestamptz),
(9092, '2026-11-27T18:22:21Z'::timestamptz),
(9083, '2026-11-27T18:22:54Z'::timestamptz),
(8896, '2026-11-27T18:24:52Z'::timestamptz),
(8964, '2026-11-27T18:25:16Z'::timestamptz),
(8967, '2026-11-27T18:25:19Z'::timestamptz),
(8972, '2026-11-27T18:25:27Z'::timestamptz),
(8981, '2026-11-27T18:25:37Z'::timestamptz),
(8992, '2026-11-27T18:25:42Z'::timestamptz),
(8990, '2026-11-27T18:26:20Z'::timestamptz),
(9027, '2026-11-27T18:26:25Z'::timestamptz),
(9030, '2026-11-27T18:26:31Z'::timestamptz),
(9137, '2026-11-27T18:32:35Z'::timestamptz),
(9151, '2026-11-27T18:33:29Z'::timestamptz),
(9153, '2026-11-27T18:33:36Z'::timestamptz),
(9159, '2026-11-27T18:33:54Z'::timestamptz),
(9161, '2026-11-27T18:34:07Z'::timestamptz),
(9165, '2026-11-27T18:34:14Z'::timestamptz),
(9169, '2026-11-27T18:34:27Z'::timestamptz),
(9175, '2026-11-27T18:34:49Z'::timestamptz),
(9183, '2026-11-27T18:35:09Z'::timestamptz),
(9193, '2026-11-27T18:35:41Z'::timestamptz),
(9196, '2026-11-27T18:35:47Z'::timestamptz),
(9198, '2026-11-27T18:35:49Z'::timestamptz),
(9207, '2026-11-27T18:36:14Z'::timestamptz),
(9214, '2026-11-27T18:36:25Z'::timestamptz),
(9219, '2026-11-27T18:36:54Z'::timestamptz),
(9251, '2026-11-27T18:37:08Z'::timestamptz),
(9273, '2026-11-27T18:37:18Z'::timestamptz),
(9274, '2026-11-27T18:37:56Z'::timestamptz)
) v(pr, m) where e.kind = 'formalized' and e.detail = 'https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/' || v.pr and e.created_at = now();
commit;

-- ===== batch 23: statements (50 PRs) =====
begin;
select v.pr, oma_log('formalized', v.id, v.h, 'https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/' || v.pr) r from (values
(9269, 'oeis-a068128', 'ecirak42'),
(9376, 'oeis-a192358', 'JeremyDevs'),
(9387, 'arxiv-2607.03584', 'my-other-github-account'),
(9409, 'oeis-a203298', 'ivillar'),
(9463, 'oeis-a222945', 'ivillar'),
(9478, 'erdos-265', 'Andyi955'),
(9480, 'oeis-a383246', 'con123-gif'),
(9483, 'oeis-a398690', 'dwilfand-sys'),
(9488, 'mo-342399', 'AkiRA-COM-FP'),
(9482, 'oeis-a383248', 'con123-gif'),
(9498, 'oeis-a345096', 'KoaOkano'),
(9493, 'oeis-a047872', 'rot13maxi'),
(9503, 'mo-487192', 'con123-gif'),
(9523, 'oeis-a025754', 'sntntHb'),
(9525, 'oeis-a005148', 'eliayousf'),
(9532, 'oeis-a192940', 'JeremyDevs'),
(9534, 'oeis-a112700', 'sntntHb'),
(9543, 'oeis-a192942', 'JeremyDevs'),
(9547, 'oeis-a185087', 'sntntHb'),
(9549, 'oeis-a213243', 'ivillar'),
(9554, 'mo-449746', 'PastaPastaPasta'),
(9559, 'oeis-a055278', 'rot13maxi'),
(9562, 'oeis-a386969', 'ecirak42'),
(9564, 'oeis-a080674', 'OrangeHeadz'),
(9567, 'oeis-a213245', 'ivillar'),
(9576, 'oeis-a127711', 'DomTheDeveloper'),
(9577, 'oeis-a002387', 'ppleskov'),
(9580, 'oeis-a045798', 'caa1982'),
(9584, 'oeis-a213244', 'ivillar'),
(9586, 'mo-267876', 'zarnab222-dev'),
(9590, 'oeis-a192473', 'JeremyDevs'),
(9591, 'oeis-a051064', 'caa1982'),
(9589, 'oeis-a213246', 'ivillar'),
(9601, 'oeis-a005517', 'rot13maxi'),
(9603, 'oeis-a003095', 'caa1982'),
(9594, 'oeis-a213248', 'ivillar'),
(9605, 'oeis-a223299', 'thomasfredrickson'),
(9607, 'mo-366028', 'caa1982'),
(9609, 'oeis-a382605', 'ecirak42'),
(9610, 'oeis-a094303', 'eliayousf'),
(9608, 'oeis-a113768', 'KoaOkano'),
(9615, 'oeis-a182025', 'agchua'),
(9616, 'oeis-a066357', 'eliayousf'),
(9620, 'oeis-a102309', 'ShoQo'),
(9619, 'oeis-a384270', 'anmolspace'),
(9623, 'oeis-a241884', 'divmxnd0x'),
(9627, 'oeis-a373163', 'Iraeeee'),
(9631, 'oeis-a366870', 'KoaOkano'),
(9632, 'opg-a-transversal-achievement-game-on-a-square-grid', 'AkiRA-COM-FP'),
(9625, 'oeis-a366860', 'KoaOkano')
) v(pr, id, h);
-- created_at := merge time, only for events this transaction created (created_at = now())
update oma_events e set created_at = v.m from (values
(9269, '2026-11-27T18:47:36Z'::timestamptz),
(9376, '2026-11-27T18:48:08Z'::timestamptz),
(9387, '2026-11-27T18:48:12Z'::timestamptz),
(9409, '2026-11-27T18:49:02Z'::timestamptz),
(9463, '2026-11-27T18:49:41Z'::timestamptz),
(9478, '2026-11-27T18:49:57Z'::timestamptz),
(9480, '2026-11-27T18:49:59Z'::timestamptz),
(9483, '2026-11-27T18:50:12Z'::timestamptz),
(9488, '2026-11-27T18:50:26Z'::timestamptz),
(9482, '2026-11-27T18:50:45Z'::timestamptz),
(9498, '2026-11-27T18:51:20Z'::timestamptz),
(9493, '2026-11-27T18:51:31Z'::timestamptz),
(9503, '2026-11-27T18:51:52Z'::timestamptz),
(9523, '2026-11-27T18:52:10Z'::timestamptz),
(9525, '2026-11-27T18:52:13Z'::timestamptz),
(9532, '2026-11-27T18:52:25Z'::timestamptz),
(9534, '2026-11-27T18:52:28Z'::timestamptz),
(9543, '2026-11-27T18:52:45Z'::timestamptz),
(9547, '2026-11-27T18:52:53Z'::timestamptz),
(9549, '2026-11-27T18:53:05Z'::timestamptz),
(9554, '2026-11-27T18:53:12Z'::timestamptz),
(9559, '2026-11-27T18:53:26Z'::timestamptz),
(9562, '2026-11-27T18:53:35Z'::timestamptz),
(9564, '2026-11-27T18:53:43Z'::timestamptz),
(9567, '2026-11-27T18:54:08Z'::timestamptz),
(9576, '2026-11-27T18:54:26Z'::timestamptz),
(9577, '2026-11-27T18:54:28Z'::timestamptz),
(9580, '2026-11-27T18:54:40Z'::timestamptz),
(9584, '2026-11-27T18:54:58Z'::timestamptz),
(9586, '2026-11-27T18:55:01Z'::timestamptz),
(9590, '2026-11-27T18:55:16Z'::timestamptz),
(9591, '2026-11-27T18:55:22Z'::timestamptz),
(9589, '2026-11-27T18:55:36Z'::timestamptz),
(9601, '2026-11-27T18:55:55Z'::timestamptz),
(9603, '2026-11-27T18:55:59Z'::timestamptz),
(9594, '2026-11-27T18:56:02Z'::timestamptz),
(9605, '2026-11-27T18:56:11Z'::timestamptz),
(9607, '2026-11-27T18:56:26Z'::timestamptz),
(9609, '2026-11-27T18:56:31Z'::timestamptz),
(9610, '2026-11-27T18:56:44Z'::timestamptz),
(9608, '2026-11-27T18:56:53Z'::timestamptz),
(9615, '2026-11-27T18:57:06Z'::timestamptz),
(9616, '2026-11-27T18:57:08Z'::timestamptz),
(9620, '2026-11-27T18:57:23Z'::timestamptz),
(9619, '2026-11-27T18:57:32Z'::timestamptz),
(9623, '2026-11-27T18:57:41Z'::timestamptz),
(9627, '2026-11-27T18:57:46Z'::timestamptz),
(9631, '2026-11-27T18:58:06Z'::timestamptz),
(9632, '2026-11-27T18:58:09Z'::timestamptz),
(9625, '2026-11-27T18:58:13Z'::timestamptz)
) v(pr, m) where e.kind = 'formalized' and e.detail = 'https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/' || v.pr and e.created_at = now();
commit;

-- ===== batch 24: statements (50 PRs) =====
begin;
select v.pr, oma_log('formalized', v.id, v.h, 'https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/' || v.pr) r from (values
(9634, 'mo-440995', 'caa1982'),
(9638, 'mse-948616', 'caa1982'),
(9640, 'mo-160796', 'AkiRA-COM-FP'),
(9635, 'oeis-a178295', 'sntntHb'),
(9645, 'oeis-a000720', 'Andyi955'),
(9644, 'oeis-a049425', 'eliayousf'),
(9652, 'oeis-a178298', 'sntntHb'),
(9650, 'oeis-a220902', 'sntntHb'),
(9655, 'oeis-a002293', 'gblacher2'),
(9658, 'oeis-a050446', 'dwilfand-sys'),
(9660, 'oeis-a192756', 'ivillar'),
(9663, 'wpc-zeta-5-irrational', 'OrangeHeadz'),
(9657, 'mse-2615963', 'seanm27lol'),
(9666, 'oeis-a178299', 'sntntHb'),
(9673, 'oeis-a192744', 'JeremyDevs'),
(9678, 'oeis-a400585', 'Iraeeee'),
(9681, 'oeis-a192745', 'JeremyDevs'),
(9674, 'oeis-a002050', 'gblacher2'),
(9686, 'mo-319325', 'con123-gif'),
(9687, 'oeis-a192754', 'ivillar'),
(9688, 'oeis-a273400', 'anmolspace'),
(9690, 'oeis-a178353', 'sntntHb'),
(9695, 'oeis-a127628', 'sntntHb'),
(9702, 'oeis-a382465', 'con123-gif'),
(9703, 'oeis-a382624', 'con123-gif'),
(9704, 'oeis-a383062', 'con123-gif'),
(9706, 'oeis-a178296', 'sntntHb'),
(9712, 'oeis-a003185', 'yuka30240'),
(9713, 'arxiv-1902.03207', 'my-other-github-account'),
(9714, 'oeis-a037958', 'OrangeHeadz'),
(7980, 'oeis-a106252', 'erood'),
(9719, 'oeis-a327138', 'Iraeeee'),
(9729, 'oeis-a000332', 'justusklocke-cloud'),
(9733, 'oeis-a348598', 'DomTheDeveloper'),
(9738, 'wp-aec', 'biondadave'),
(9730, 'oeis-a048775', 'sntntHb'),
(9743, 'oeis-a178351', 'sntntHb'),
(9746, 'mo-452919', 'OrangeHeadz'),
(9740, 'oeis-a192924', 'JeremyDevs'),
(9754, 'oeis-a264100', 'anmolspace'),
(9758, 'oeis-a000986', 'sntntHb'),
(9768, 'oeis-a048200', 'sntntHb'),
(9769, 'oeis-a066534', 'sntntHb'),
(9770, 'oeis-a327136', 'Iraeeee'),
(9773, 'oeis-a002791', 'ivillar'),
(9780, 'oeis-a002114', 'gblacher2'),
(9790, 'oeis-a080958', 'ivillar'),
(9793, 'oeis-a135499', 'ivillar'),
(9801, 'oeis-a303120', 'ivillar'),
(9811, 'oeis-a296161', 'ivillar')
) v(pr, id, h);
-- created_at := merge time, only for events this transaction created (created_at = now())
update oma_events e set created_at = v.m from (values
(9634, '2026-11-27T18:58:15Z'::timestamptz),
(9638, '2026-11-27T18:58:28Z'::timestamptz),
(9640, '2026-11-27T18:58:33Z'::timestamptz),
(9635, '2026-11-27T18:58:38Z'::timestamptz),
(9645, '2026-11-27T18:58:53Z'::timestamptz),
(9644, '2026-11-27T18:59:06Z'::timestamptz),
(9652, '2026-11-27T18:59:18Z'::timestamptz),
(9650, '2026-11-27T18:59:27Z'::timestamptz),
(9655, '2026-11-27T18:59:38Z'::timestamptz),
(9658, '2026-11-27T18:59:43Z'::timestamptz),
(9660, '2026-11-27T18:59:53Z'::timestamptz),
(9663, '2026-11-27T18:59:59Z'::timestamptz),
(9657, '2026-11-27T19:00:06Z'::timestamptz),
(9666, '2026-11-27T19:00:16Z'::timestamptz),
(9673, '2026-11-27T19:00:22Z'::timestamptz),
(9678, '2026-11-27T19:00:27Z'::timestamptz),
(9681, '2026-11-27T19:00:41Z'::timestamptz),
(9674, '2026-11-27T19:00:51Z'::timestamptz),
(9686, '2026-11-27T19:00:56Z'::timestamptz),
(9687, '2026-11-27T19:01:02Z'::timestamptz),
(9688, '2026-11-27T19:01:06Z'::timestamptz),
(9690, '2026-11-27T19:01:18Z'::timestamptz),
(9695, '2026-11-27T19:01:24Z'::timestamptz),
(9702, '2026-11-27T19:01:48Z'::timestamptz),
(9703, '2026-11-27T19:01:50Z'::timestamptz),
(9704, '2026-11-27T19:01:55Z'::timestamptz),
(9706, '2026-11-27T19:02:03Z'::timestamptz),
(9712, '2026-11-27T19:02:05Z'::timestamptz),
(9713, '2026-11-27T19:02:10Z'::timestamptz),
(9714, '2026-11-27T19:02:22Z'::timestamptz),
(7980, '2026-11-27T19:02:25Z'::timestamptz),
(9719, '2026-11-27T19:02:36Z'::timestamptz),
(9729, '2026-11-27T19:02:58Z'::timestamptz),
(9733, '2026-11-27T19:03:21Z'::timestamptz),
(9738, '2026-11-27T19:03:25Z'::timestamptz),
(9730, '2026-11-27T19:03:37Z'::timestamptz),
(9743, '2026-11-27T19:03:41Z'::timestamptz),
(9746, '2026-11-27T19:03:52Z'::timestamptz),
(9740, '2026-11-27T19:03:56Z'::timestamptz),
(9754, '2026-11-27T19:04:15Z'::timestamptz),
(9758, '2026-11-27T19:04:26Z'::timestamptz),
(9768, '2026-11-27T19:04:49Z'::timestamptz),
(9769, '2026-11-27T19:04:54Z'::timestamptz),
(9770, '2026-11-27T19:05:04Z'::timestamptz),
(9773, '2026-11-27T19:05:07Z'::timestamptz),
(9780, '2026-11-27T19:05:22Z'::timestamptz),
(9790, '2026-11-27T19:05:31Z'::timestamptz),
(9793, '2026-11-27T19:05:36Z'::timestamptz),
(9801, '2026-11-27T19:05:50Z'::timestamptz),
(9811, '2026-11-27T19:06:04Z'::timestamptz)
) v(pr, m) where e.kind = 'formalized' and e.detail = 'https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/' || v.pr and e.created_at = now();
commit;

-- ===== batch 25: statements (50 PRs) =====
begin;
select v.pr, oma_log('formalized', v.id, v.h, 'https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/' || v.pr) r from (values
(9832, 'oeis-a192752', 'JeremyDevs'),
(9821, 'oeis-a334337', 'KoaOkano'),
(1299, 'oeis-a333686', 'shunyaekam'),
(1300, 'oeis-a001566', 'eliayousf'),
(1302, 'oeis-a216211', 'shunyaekam'),
(4713, 'mo-352184', 'tatashbar'),
(4710, 'mo-280952', 'tatashbar'),
(1303, 'oeis-a020964', 'eliayousf'),
(8003, 'oeis-a105877', 'erood'),
(1313, 'oeis-a191625', 'shunyaekam'),
(4657, 'mse-199784', 'tatashbar'),
(1325, 'wp-are-there-infinitely-many-sexy-primes', 'ihateSAS'),
(8487, 'oeis-a002867', 'rorcores'),
(8544, 'oeis-a171556', 'rorcores'),
(1366, 'wp-are-there-infinitely-many-woodall-primes', 'ihateSAS'),
(1370, 'opg-a-sextic-counterexample-to-eulers-sum-of-powers-conjecture', 'Hennyrick'),
(1372, 'erdos-306', 'mattdorman'),
(9694, 'wp-chvatal-s-toughness-conjecture', 'ArjunCodess'),
(1387, 'erdos-260', 'mattdorman'),
(1390, 'erdos-1150', 'mattdorman'),
(1406, 'erdos-371', 'mattdorman'),
(1408, 'erdos-289', 'mattdorman'),
(1413, 'oeis-a000041', 'ZenimXD'),
(9742, 'mo-201602', 'AkiRA-COM-FP'),
(1418, 'oeis-a028886', 'eliayousf'),
(9721, 'oeis-a178297', 'sntntHb'),
(1444, 'oeis-a383702', 'mmiranda2'),
(1456, 'wp-1-factorization-conjecture', 'prophetlabs'),
(1480, 'wp-conference-graph', 'prophetlabs'),
(1489, 'wp-sister-beiter-conjecture', 'Drogobo'),
(1491, 'mo-138395', 'koolkao'),
(1497, 'mo-107177', 'LDJAI'),
(1503, 'wp-ehrhart-s-volume-conjecture', 'prophetlabs'),
(1505, 'oeis-a306948', 'mmiranda2'),
(1522, 'wp-perfect-1-factorization-conjecture', 'prophetlabs'),
(1530, 'oeis-a303647', 'eliayousf'),
(1536, 'oeis-a327978', 'jatin6'),
(1549, 'wp-torsion-conjecture', 'menelikbaye-digitalmethod'),
(1564, 'wp-unfriendly-partition-conjecture', 'prophetlabs'),
(1565, 'oeis-a243513', 'jatin6'),
(1588, 'wp-teschner-s-bondage-number-conjecture', 'prophetlabs'),
(1598, 'oeis-a048625', 'eliayousf'),
(1602, 'wp-are-there-infinitely-many-lehmer-pairs', 'lzvxck'),
(1615, 'mo-136792', 'LDJAI'),
(1616, 'mo-142880', 'LDJAI'),
(1618, 'mo-47956', 'LDJAI'),
(1619, 'mo-201997', 'LDJAI'),
(7128, 'oeis-a157218', 'mscheuern'),
(4758, 'mo-491918', 'tatashbar'),
(7966, 'oeis-a267921', 'ddanila')
) v(pr, id, h);
-- created_at := merge time, only for events this transaction created (created_at = now())
update oma_events e set created_at = v.m from (values
(9832, '2026-11-27T19:06:43Z'::timestamptz),
(9821, '2026-11-27T19:06:52Z'::timestamptz),
(1299, '2026-11-27T19:08:19Z'::timestamptz),
(1300, '2026-11-27T19:08:46Z'::timestamptz),
(1302, '2026-11-27T19:09:11Z'::timestamptz),
(4713, '2026-11-27T19:09:23Z'::timestamptz),
(4710, '2026-11-27T19:09:26Z'::timestamptz),
(1303, '2026-11-27T19:09:34Z'::timestamptz),
(8003, '2026-11-27T19:09:49Z'::timestamptz),
(1313, '2026-11-27T19:09:57Z'::timestamptz),
(4657, '2026-11-27T19:10:07Z'::timestamptz),
(1325, '2026-11-27T19:10:26Z'::timestamptz),
(8487, '2026-11-27T19:10:53Z'::timestamptz),
(8544, '2026-11-27T19:10:56Z'::timestamptz),
(1366, '2026-11-27T19:11:33Z'::timestamptz),
(1370, '2026-11-27T19:11:50Z'::timestamptz),
(1372, '2026-11-27T19:12:13Z'::timestamptz),
(9694, '2026-11-27T19:12:35Z'::timestamptz),
(1387, '2026-11-27T19:12:38Z'::timestamptz),
(1390, '2026-11-27T19:12:56Z'::timestamptz),
(1406, '2026-11-27T19:13:25Z'::timestamptz),
(1408, '2026-11-27T19:13:50Z'::timestamptz),
(1413, '2026-11-27T19:14:15Z'::timestamptz),
(9742, '2026-11-27T19:14:40Z'::timestamptz),
(1418, '2026-11-27T19:14:46Z'::timestamptz),
(9721, '2026-11-27T19:15:00Z'::timestamptz),
(1444, '2026-11-27T19:15:39Z'::timestamptz),
(1456, '2026-11-27T19:16:03Z'::timestamptz),
(1480, '2026-11-27T19:16:48Z'::timestamptz),
(1489, '2026-11-27T19:17:19Z'::timestamptz),
(1491, '2026-11-27T19:17:43Z'::timestamptz),
(1497, '2026-11-27T19:18:24Z'::timestamptz),
(1503, '2026-11-27T19:18:44Z'::timestamptz),
(1505, '2026-11-27T19:19:02Z'::timestamptz),
(1522, '2026-11-27T19:19:38Z'::timestamptz),
(1530, '2026-11-27T19:19:55Z'::timestamptz),
(1536, '2026-11-27T19:20:33Z'::timestamptz),
(1549, '2026-11-27T19:21:26Z'::timestamptz),
(1564, '2026-11-27T19:22:06Z'::timestamptz),
(1565, '2026-11-27T19:22:23Z'::timestamptz),
(1588, '2026-11-27T19:23:16Z'::timestamptz),
(1598, '2026-11-27T19:23:59Z'::timestamptz),
(1602, '2026-11-27T19:24:24Z'::timestamptz),
(1615, '2026-11-27T19:25:03Z'::timestamptz),
(1616, '2026-11-27T19:25:31Z'::timestamptz),
(1618, '2026-11-27T19:25:50Z'::timestamptz),
(1619, '2026-11-27T19:26:06Z'::timestamptz),
(7128, '2026-11-27T19:48:10Z'::timestamptz),
(4758, '2026-11-27T19:48:14Z'::timestamptz),
(7966, '2026-11-27T19:49:39Z'::timestamptz)
) v(pr, m) where e.kind = 'formalized' and e.detail = 'https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/' || v.pr and e.created_at = now();
commit;

-- ===== batch 26: statements (8 PRs) =====
begin;
select v.pr, oma_log('formalized', v.id, v.h, 'https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/' || v.pr) r from (values
(8024, 'oeis-a267920', 'ddanila'),
(8056, 'oeis-a133212', 'JeremyDevs'),
(8159, 'oeis-a007484', 'JeremyDevs'),
(9008, 'wp-barnette-s-conjecture', 'bcrowther86-eng'),
(9145, 'oeis-a384132', 'bcrowther86-eng'),
(9180, 'oeis-a306698', 'hangumm'),
(9184, 'oeis-a387064', 'bcrowther86-eng'),
(9205, 'oeis-a386703', 'bcrowther86-eng')
) v(pr, id, h);
-- created_at := merge time, only for events this transaction created (created_at = now())
update oma_events e set created_at = v.m from (values
(8024, '2026-11-27T19:49:45Z'::timestamptz),
(8056, '2026-11-27T19:50:02Z'::timestamptz),
(8159, '2026-11-27T19:51:12Z'::timestamptz),
(9008, '2026-11-27T19:51:29Z'::timestamptz),
(9145, '2026-11-27T19:51:31Z'::timestamptz),
(9180, '2026-11-27T19:51:36Z'::timestamptz),
(9184, '2026-11-27T19:52:41Z'::timestamptz),
(9205, '2026-11-27T19:53:00Z'::timestamptz)
) v(pr, m) where e.kind = 'formalized' and e.detail = 'https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/' || v.pr and e.created_at = now();
commit;

-- ===== verification (read-only): every PR merged into main on 27 Nov (as of 23:14 UTC) and whether it has its credit row =====
select k.kind, count(*) merged_today, count(*) filter (where not k.ok) missing, coalesce(json_agg(k.n order by k.n) filter (where not k.ok), '[]') missing_prs from (
  select 'reduction' kind, n, exists (select 1 from oma_reductions r where r.pr_url = 'https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/' || n) ok from unnest(array[798,820,821,828,834,847,862,864,870,879,882,884,890,897,902,906,915,917,919,925,937,941,944,975,976,999,1000,1005,1011,1029,1046,1048,1064,1065,1069,1072,1077,1087,1113,1124,1129,1134,1141,1145,1150,1154,1156,1159,1162,1169,1171,1183,1189,1195,1203,1210,1212,1214,1216,1223,1225,1227,1239,1241,1242,1247,1256,1264,1265,1272,1276,1280,1283,1301,1321,1328,1329,1333,1335,1339,1343,1346,1348,1353,1354,1358,1365,1369,1373,1376,1382,1386,1394,1397,1403,1425,1438,1439,1441,1442,1463,1464,1470,1479,1490,1500,1501,1502,1513,1517,1524,1537,1543,1553,1556,1572,1574,1578,1586,1587,1603,1621,1622,1626,1629,1632,1636,1639,1646,1647,1649,1657,1659,1672,1676,1677,1689,1692,1705,1717,1719,1726,1730,1737,1740,1749,1751,1765,1767,1773,1777,1779,1782,1786,1790,1798,1806,1819,1826,1830,1834,1844,1867,1893,1897,1901,1902,1912,1915,1917,1922,1926,1929,1930,1940,1941,1954,1957,1969,1986,1992,1994,1999,2008,2024,2033,2034,2035,2036,2053,2066,2069,2070,2072,2075,2078,2083,2088,2090,2091,2097,2099,2100,2103,2105,2109,2111,2122,2124,2138,2141,2159,2160,2167,2172,2175,2184,2186,2190,2191,2193,2213,2214,2227,2237,2243,2248,2249,2258,2262,2266,2267,2273,2299,2312,2315,2332,2349,2357,2377,2408,2411,2430,2436,2439,2440,2441,2445,2448,2457,2474,2485,2496,2507,2509,2519,2520,2523,2529,2539,2541,2543,2548,2551,2556,2562,2563,2569,2574,2575,2585,2592,2599,2615,2622,2637,2671,2673,2683,2685,2699,2703,2706,2717,2728,2731,2735,2739,2742,2750,2751,2753,2758,2769,2774,2777,2779,2781,2786,2804,2832,2836,2851,2856,2866,2868,2869,2870,2872,2877,2881,2882,2906,2910,2930,2931,2933,2943,2948,2952,2964,2971,2978,2987,2994,2995,3002,3017,3018,3020,3025,3028,3030,3038,3043,3044,3046,3047,3051,3054,3055,3064,3065,3069,3071,3073,3076,3086,3097,3100,3101,3110,3111,3131,3145,3146,3147,3150,3170,3176,3177,3185,3193,3194,3197,3199,3201,3202,3210,3211,3215,3216,3220,3221,3223,3243,3246,3252,3253,3261,3269,3273,3275,3283,3290,3291,3293,3296,3298,3300,3304,3312,3313,3320,3326,3330,3334,3341,3348,3358,3359,3360,3373,3379,3382,3387,3393,3397,3398,3402,3405,3409,3411,3412,3416,3422,3429,3432,3434,3437,3438,3440,3442,3443,3448,3457,3459,3460,3466,3475,3476,3477,3482,3485,3491,3497,3498,3511,3514,3543,3547,3548,3564,3566,3567,3581,3590,3612,3625,3633,3635,3654,3655,3670,3675,3677,3691,3708,3717,3718,3719,3721,3722,3723,3739,3743,3745,3748,3751,3758,3759,3764,3768,3770,3776,3787,3788,3791,3794,3798,3810,3818,3820,3824,3825,3826,3835,3848,3853,3854,3858,3859,3861,3863,3870,3871,3878,3879,3883,3884,3885,3892,3897,3905,3912,3914,3927,3932,3937,3938,3939,3941,3949,3950,3953,3961,3976,3980,3984,3987,3988,3990,3997,4002,4011,4012,4022,4024,4029,4032,4034,4039,4040,4044,4046,4048,4050,4051,4053,4055,4056,4082,4089,4092,4100,4101,4104,4125,4126,4129,4134,4135,4147,4154,4159,4160,4162,4166,4175,4177,4185,4186,4188,4196,4200,4207,4208,4217,4219,4232,4243,4248,4255,4271,4279,4282,4284,4300,4309,4316,4328,4331,4334,4341,4366,4391,4394,4402,4404,4406,4407,4415,4418,4424,4425,4426,4439,4452,4454,4457,4466,4467,4475,4481,4488,4495,4496,4497,4498,4504,4509,4511,4512,4513,4519,4524,4525,4528,4531,4535,4537,4546,4551,4554,4563,4577,4581,4584,4589,4594,4595,4597,4598,4599,4601,4604,4609,4613,4616,4628,4632,4633,4637,4639,4669,4676,4677,4678,4679,4680,4684,4696,4700,4706,4708,4711,4714,4717,4720,4723,4728,4733,4734,4740,4741,4744,4745,4746,4752,4753,4754,4755,4756,4762,4768,4769,4776,4782,4790,4791,4794,4795,4799,4807,4808,4810,4813,4814,4817,4822,4823,4824,4826,4833,4836,4839,4842,4846,4850,4852,4854,4858,4866,4868,4874,4876,4884,4894,4897,4907,4924,4931,4935,4936,4937,4940,4941,4945,4954,4963,4971,4975,4978,4990,4992,4994,4998,5001,5004,5006,5012,5013,5018,5019,5024,5025,5026,5027,5034,5036,5037,5040,5045,5046,5047,5048,5057,5059,5064,5068,5075,5078,5084,5093,5096,5097,5098,5100,5101,5103,5107,5108,5111,5115,5119,5127,5128,5134,5135,5139,5140,5145,5151,5152,5153,5160,5163,5164,5165,5166,5169,5173,5176,5179,5183,5191,5192,5203,5207,5213,5216,5218,5219,5220,5221,5223,5228,5236,5237,5238,5246,5251,5253,5256,5259,5262,5263,5268,5269,5270,5280,5286,5287,5300,5308,5309,5310,5321,5323,5336,5340,5341,5345,5346,5356,5359,5362,5364,5380,5387,5390,5391,5395,5397,5412,5428,5431,5432,5437,5438,5455,5456,5458,5461,5464,5466,5470,5476,5480,5482,5484,5485,5486,5500,5503,5505,5508,5516,5517,5518,5527,5529,5541,5546,5550,5551,5553,5554,5556,5561,5562,5569,5570,5579,5581,5584,5589,5591,5594,5599,5608,5611,5614,5616,5620,5621,5622,5626,5632,5633,5636,5639,5643,5644,5645,5647,5649,5653,5654,5669,5672,5677,5678,5683,5684,5685,5686,5689,5691,5694,5696,5700,5703,5709,5714,5718,5719,5729,5730,5743,5746,5747,5748,5758,5764,5769,5776,5783,5785,5787,5788,5796,5798,5802,5805,5806,5813,5818,5819,5820,5822,5831,5844,5845,5846,5850,5853,5857,5859,5865,5877,5878,5880,5887,5888,5891,5897,5898,5901,5902,5909,5946,5955,5972,5977,5978,5979,5984,5992,5997,5999,6002,6009,6012,6019,6020,6021,6030,6032,6035,6044,6049,6050,6052,6056,6059,6065,6084,6088,6106,6107,6111,6113,6132,6134,6138,6154,6177,6178,6180,6181,6188,6190,6193,6196,6197,6204,6209,6223,6229,6237,6248,6253,6260,6261,6266,6272,6281,6284,6288,6293,6294,6299,6306,6313,6314,6315,6317,6320,6323,6327,6331,6334,6339,6341,6344,6354,6355,6361,6367,6368,6369,6371,6375,6377,6380,6383,6384,6390,6393,6401,6412,6417,6433,6443,6451,6465,6477,6505,6519,6542,6558,6566,6570,6582,6587,6589,6601,6614,6621,6624,6625,6638,6645,6646,6652,6654,6661,6666,6682,6691,6696,6706,6716,6720,6750,6754,6755,6760,6762,6765,6781,6791,6792,6804,6819,6837,6839,6840,6843,6850,6855,6856,6858,6859,6860,6863,6865,6877,6890,6896,6902,6904,6906,6917,6927,6932,6937,6938,6939,6944,6953,6955,6958,6963,6966,6969,6970,6974,6976,6980,7018,7039,7051,7099,7161,7164,7180,7195,7202,7237,7289,7296,7301,7329,7332,7348,7352,7356,7357,7365,7367,7370,7374,7377,7383,7387,7392,7401,7404,7414,7422,7432,7444,7447,7448,7453,7464,7467,7470,7487,7503,7511,7522,7539,7553,7558,7566,7573,7631,7658,7671,7677,7680,7700,7716,7717,7722,7733,7734,7735,7753,7760,7762,7766,7781,7783,7788,7789,7796,7797,7801,7818,7820,7822,7824,7828,7833,7873,7879,7883,7887,7896,7897,7901,7904,7909,7918,7922,7924,7925,7927,7937,7938,7949,7955,7957,7960,7974,7976,7981,7995,7998,7999,8009,8018,8020,8026,8030,8048,8059,8062,8071,8075,8079,8085,8089,8106,8107,8108,8112,8124,8136,8157,8160,8167,8172,8178,8181,8190,8196,8209,8215,8221,8231,8234,8242,8251,8257,8260,8265,8280,8286,8307,8309,8320,8326,8336,8344,8346,8350,8354,8363,8365,8372,8414,8418,8422,8427,8444,8445,8457,8462,8463,8464,8476,8481,8486,8492,8494,8496,8497,8509,8524,8525,8530,8531,8555,8562,8595,8598,8603,8604,8605,8606,8623,8634,8635,8642,8646,8651,8655,8656,8658,8660,8661,8664,8675,8676,8680,8682,8688,8693,8699,8702,8705,8706,8707,8709,8710,8713,8716,8717,8719,8724,8725,8731,8740,8748,8754,8755,8760,8767,8770,8782,8786,8793,8804,8805,8810,8811,8815,8821,8830,8836,8839,8840,8841,8843,8848,8862,8864,8873,8875,8877,8878,8886,8888,8890,8892,8894,8897,8902,8908,8920,8931,8939,8955,8973,8975,8978,8985,8987,8988,8993,8994,9001,9002,9010,9013,9015,9018,9023,9032,9042,9057,9073,9077,9078,9079,9080,9089,9096,9100,9101,9107,9109,9112,9128,9141,9146,9166,9171,9189,9211,9221,9227,9236,9240,9242,9249,9255,9261,9262,9263,9266,9268,9284,9294,9303,9308,9314,9315,9319,9336,9337,9338,9351,9360,9361,9363,9365,9367,9369,9372,9381,9384,9386,9412,9413,9416,9423,9444,9451,9456,9462,9476,9477,9485,9486,9489,9490,9502,9506,9511,9515,9517,9519,9521,9535,9538,9552,9571,9578,9581,9582,9587,9588,9593,9599,9606,9612,9613,9621,9622,9624,9630,9641,9643,9649,9659,9679,9684,9691,9696,9698,9700,9715,9718,9720,9725,9732,9734,9737,9739,9747,9751,9764,9765,9771,9772,9776,9794,9817,9818,9819,9822,9824,9836,9853,9951,10250,10446,10663,10723,10743,10767,11583,11589,11782,11838,11899]::int[]) n
  union all select 'proof', n, exists (select 1 from oma_solutions s where s.pr_url = 'https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/' || n) from unnest(array[122,172,227,233,273,287,351,377,393,424,435,442,454,483,520,553,578,620,653,664,673,682,694,712,716,747,757,766,767,772,779,785,786,787,789,790,791,792,793,794,795,796,797,799,800,802,805,806,809,811,814,815,816,817,818,819,824,825,826,827,830,831,833,835,836,837,838,839,840,841,842,843,845,848,849,850,851,852,853,854,855,856,857,858,859,860,861,863,866,867,868,871,872,873,875,877,878,880,881,883,886,887,888,889,891,892,894,895,896,899,900,901,903,904,905,907,908,909,912,913,914,916,918,920,921,923,924,926,928,929,930,931,932,933,935,936,938,939,940,943,945,946,948,949,951,953,956,958,960,962,964,965,966,968,970,974,977,978,981,982,983,984,986,987,988,989,992,995,996,1002,1004,1008,1012,1013,1014,1016,1018,1022,1023,1024,1025,1026,1028,1030,1033,1034,1036,1037,1040,1041,1042,1045,1047,1049,1050,1051,1053,1054,1055,1057,1059,1061,1063,1066,1067,1070,1075,1076,1078,1079,1080,1081,1082,1083,1086,1089,1090,1091,1094,1096,1097,1099,1100,1103,1104,1105,1106,1107,1108,1109,1110,1111,1112,1117,1120,1122,1123,1126,1128,1131,1132,1133,1135,1136,1138,1139,1140,1142,1143,1144,1146,1148,1149,1153,1155,1157,1160,1161,1164,1165,1166,1167,1170,1173,1174,1175,1176,1179,1180,1181,1182,1184,1185,1187,1188,1190,1192,1194,1196,1198,1204,1207,1208,1211,1218,1220,1221,1224,1230,1231,1232,1233,1236,1237,1240,1243,1249,1252,1253,1254,1255,1257,1258,1263,1266,1268,1269,1271,1274,1278,1282,1286,1287,1289,1290,1291,1292,1293,1295,1296,1297,1305,1307,1308,1309,1310,1311,1312,1314,1317,1318,1319,1320,1322,1323,1324,1326,1327,1331,1332,1336,1338,1340,1341,1344,1345,1349,1351,1352,1356,1357,1359,1360,1362,1363,1364,1367,1368,1374,1375,1377,1378,1379,1380,1383,1384,1385,1389,1391,1392,1396,1398,1399,1402,1404,1405,1407,1409,1414,1415,1416,1419,1420,1421,1423,1424,1427,1428,1430,1431,1432,1434,1435,1437,1440,1443,1445,1446,1449,1450,1451,1453,1454,1457,1459,1460,1462,1465,1466,1469,1471,1473,1474,1475,1476,1478,1482,1483,1485,1488,1492,1493,1498,1499,1504,1507,1508,1509,1511,1512,1514,1515,1516,1518,1519,1521,1526,1527,1528,1529,1533,1534,1535,1542,1545,1548,1550,1551,1552,1554,1558,1559,1561,1562,1563,1566,1568,1569,1570,1571,1573,1576,1581,1582,1584,1593,1594,1596,1597,1600,1604,1605,1608,1609,1610,1611,1613,1617,1620,1627,1630,1631,1634,1638,1640,1641,1643,1644,1645,1648,1650,1653,1658,1660,1661,1663,1665,1667,1668,1673,1675,1680,1682,1685,1687,1690,1691,1693,1694,1696,1699,1700,1704,1707,1708,1709,1712,1713,1714,1715,1718,1720,1721,1722,1727,1728,1729,1732,1738,1743,1745,1746,1748,1750,1752,1754,1756,1757,1763,1766,1768,1771,1774,1776,1778,1791,1792,1793,1794,1795,1797,1799,1800,1802,1803,1805,1809,1811,1814,1815,1818,1824,1825,1827,1828,1829,1833,1835,1836,1838,1840,1841,1846,1850,1852,1853,1854,1859,1862,1864,1869,1874,1875,1877,1878,1879,1880,1884,1886,1890,1894,1895,1899,1900,1903,1906,1907,1908,1909,1911,1918,1923,1927,1933,1936,1944,1953,1958,1973,1978,1979,1983,1984,1987,1988,1990,1993,1995,1997,1998,2005,2011,2013,2015,2017,2021,2023,2025,2030,2031,2039,2042,2046,2050,2056,2059,2065,2067,2068,2071,2073,2080,2081,2086,2093,2094,2096,2101,2102,2104,2106,2107,2110,2112,2113,2118,2119,2120,2121,2125,2127,2131,2133,2135,2137,2139,2140,2143,2145,2147,2148,2151,2152,2153,2155,2157,2163,2164,2165,2168,2169,2170,2171,2181,2182,2188,2194,2198,2200,2202,2203,2204,2208,2209,2217,2222,2223,2224,2240,2242,2245,2251,2254,2257,2259,2264,2265,2269,2277,2285,2287,2300,2301,2306,2307,2308,2309,2314,2318,2320,2321,2322,2323,2325,2338,2340,2341,2343,2351,2354,2362,2363,2366,2367,2370,2376,2378,2380,2384,2386,2389,2391,2392,2394,2396,2397,2401,2403,2410,2419,2420,2421,2425,2432,2437,2438,2442,2453,2460,2462,2463,2469,2471,2472,2473,2480,2481,2482,2483,2489,2490,2499,2500,2505,2506,2513,2517,2521,2524,2526,2531,2533,2534,2536,2538,2544,2550,2554,2566,2567,2568,2570,2571,2572,2573,2583,2591,2593,2597,2600,2601,2602,2606,2613,2617,2625,2627,2632,2634,2638,2639,2640,2643,2647,2653,2658,2662,2666,2669,2679,2680,2681,2684,2687,2694,2695,2701,2704,2705,2708,2709,2711,2713,2715,2727,2746,2752,2759,2760,2761,2762,2763,2765,2767,2770,2775,2784,2789,2790,2793,2794,2797,2798,2805,2807,2813,2820,2823,2825,2827,2833,2841,2846,2848,2849,2855,2860,2871,2874,2879,2880,2883,2885,2886,2893,2894,2895,2896,2901,2902,2903,2911,2916,2920,2921,2925,2926,2927,2929,2935,2936,2940,2945,2946,2950,2951,2954,2960,2961,2962,2965,2966,2967,2970,2973,2980,2982,2983,2985,2986,2988,2989,2992,2993,3001,3005,3007,3009,3010,3012,3014,3021,3029,3031,3036,3037,3041,3045,3048,3049,3052,3062,3067,3068,3075,3081,3084,3085,3087,3096,3104,3106,3115,3117,3119,3121,3123,3125,3128,3135,3136,3140,3144,3149,3152,3156,3164,3167,3168,3180,3183,3186,3188,3189,3190,3195,3196,3204,3207,3209,3212,3213,3214,3225,3226,3227,3228,3230,3232,3233,3234,3236,3237,3238,3240,3241,3242,3244,3245,3247,3250,3254,3255,3257,3259,3260,3262,3263,3266,3267,3268,3271,3272,3277,3278,3279,3281,3284,3285,3286,3288,3289,3294,3295,3297,3299,3302,3306,3307,3309,3310,3315,3316,3317,3321,3322,3325,3328,3329,3331,3333,3335,3339,3343,3344,3346,3347,3350,3351,3352,3355,3356,3357,3361,3364,3366,3367,3368,3369,3370,3371,3372,3374,3375,3376,3377,3381,3385,3386,3389,3391,3392,3394,3395,3396,3399,3403,3404,3406,3413,3415,3417,3418,3419,3420,3421,3423,3424,3425,3427,3428,3430,3431,3433,3435,3439,3441,3445,3449,3452,3453,3455,3458,3462,3463,3464,3465,3467,3468,3469,3472,3473,3480,3486,3489,3490,3492,3493,3495,3499,3500,3502,3503,3505,3512,3513,3516,3517,3519,3525,3526,3529,3530,3532,3533,3534,3535,3537,3538,3539,3542,3546,3550,3551,3552,3553,3559,3560,3562,3563,3568,3569,3574,3577,3578,3580,3582,3584,3585,3586,3587,3588,3589,3591,3592,3593,3594,3595,3596,3600,3601,3604,3605,3606,3607,3608,3609,3610,3613,3614,3616,3617,3619,3621,3622,3626,3628,3632,3634,3637,3638,3639,3640,3641,3642,3646,3648,3649,3651,3652,3653,3657,3659,3663,3664,3665,3666,3667,3668,3671,3673,3674,3678,3679,3680,3681,3682,3683,3684,3686,3688,3689,3690,3694,3695,3696,3699,3700,3701,3709,3712,3713,3715,3725,3726,3727,3728,3730,3731,3734,3735,3736,3737,3740,3744,3747,3752,3753,3754,3756,3757,3761,3765,3773,3775,3780,3784,3790,3792,3801,3804,3807,3808,3809,3811,3812,3813,3815,3816,3819,3821,3823,3828,3829,3830,3833,3834,3836,3838,3841,3843,3844,3849,3851,3856,3857,3866,3868,3873,3875,3877,3880,3882,3888,3889,3895,3899,3901,3907,3909,3913,3925,3926,3929,3942,3957,3959,3963,3964,3965,3968,3969,3971,3979,3983,3989,3992,3999,4000,4007,4010,4013,4023,4025,4026,4028,4033,4047,4058,4060,4061,4062,4065,4072,4073,4081,4084,4087,4093,4097,4098,4107,4110,4111,4132,4133,4138,4142,4146,4148,4149,4152,4155,4157,4158,4167,4168,4169,4172,4181,4182,4187,4192,4194,4195,4202,4204,4205,4206,4209,4220,4222,4226,4227,4228,4229,4236,4238,4258,4260,4265,4266,4267,4270,4274,4278,4281,4286,4289,4295,4301,4302,4304,4308,4310,4311,4312,4315,4317,4318,4321,4322,4324,4325,4329,4332,4333,4336,4337,4338,4339,4340,4342,4343,4345,4347,4350,4351,4355,4358,4359,4364,4365,4368,4369,4375,4377,4378,4381,4382,4386,4387,4390,4397,4399,4400,4405,4409,4410,4411,4413,4416,4417,4420,4427,4429,4431,4433,4434,4436,4438,4440,4443,4447,4448,4450,4451,4453,4455,4460,4462,4464,4465,4468,4473,4474,4476,4479,4480,4482,4483,4484,4485,4486,4489,4490,4493,4494,4499,4501,4502,4505,4510,4514,4515,4516,4518,4520,4523,4527,4533,4536,4538,4539,4540,4541,4544,4547,4548,4553,4557,4559,4560,4561,4564,4566,4569,4570,4573,4576,4579,4583,4587,4590,4591,4592,4593,4596,4600,4603,4605,4614,4617,4620,4627,4630,4634,4636,4638,4640,4642,4645,4646,4648,4650,4652,4660,4662,4665,4666,4667,4668,4671,4672,4674,4675,4682,4683,4685,4689,4693,4699,4712,4716,4718,4729,4730,4735,4736,4737,4748,4750,4760,4764,4770,4775,4780,4781,4787,4800,4801,4805,4809,4816,4818,4819,4827,4829,4830,4832,4837,4838,4840,4844,4847,4851,4855,4857,4862,4869,4877,4879,4880,4881,4882,4885,4890,4893,4898,4901,4909,4914,4915,4917,4919,4920,4925,4926,4928,4930,4934,4947,4950,4956,4957,4958,4964,4967,4973,4977,4981,4982,4983,4986,4987,4988,4995,4997,5005,5008,5009,5010,5020,5021,5031,5033,5038,5039,5042,5043,5049,5054,5058,5065,5070,5072,5079,5081,5099,5102,5113,5116,5117,5120,5121,5122,5126,5129,5131,5136,5148,5154,5168,5170,5172,5174,5181,5184,5185,5186,5189,5190,5193,5195,5196,5197,5199,5201,5202,5204,5205,5208,5210,5211,5212,5215,5227,5235,5241,5243,5244,5247,5249,5250,5252,5254,5257,5258,5260,5264,5265,5271,5274,5276,5277,5279,5281,5288,5290,5291,5292,5294,5297,5298,5299,5301,5302,5304,5305,5306,5307,5311,5312,5313,5314,5315,5317,5319,5324,5325,5326,5327,5328,5329,5331,5332,5333,5334,5335,5338,5339,5343,5344,5349,5350,5351,5352,5353,5354,5357,5360,5361,5363,5365,5366,5368,5370,5371,5372,5373,5375,5376,5377,5379,5382,5383,5389,5392,5394,5396,5403,5404,5414,5415,5420,5421,5423,5424,5426,5427,5430,5435,5436,5439,5442,5443,5444,5445,5446,5447,5448,5450,5451,5460,5463,5465,5469,5471,5473,5474,5475,5477,5478,5481,5487,5488,5490,5491,5493,5494,5496,5497,5499,5502,5504,5507,5511,5512,5513,5514,5515,5519,5520,5522,5523,5526,5528,5530,5531,5533,5534,5535,5537,5538,5539,5543,5548,5555,5558,5560,5564,5568,5571,5572,5573,5574,5575,5576,5580,5582,5583,5586,5592,5593,5595,5596,5597,5600,5601,5602,5603,5604,5605,5609,5612,5613,5615,5618,5619,5623,5627,5629,5630,5634,5635,5638,5641,5646,5650,5657,5659,5662,5665,5666,5667,5671,5673,5675,5676,5680,5687,5688,5693,5695,5697,5698,5699,5704,5712,5713,5715,5716,5720,5722,5724,5725,5726,5727,5728,5731,5734,5736,5737,5741,5744,5749,5750,5751,5752,5754,5756,5763,5765,5766,5767,5768,5770,5777,5779,5780,5781,5782,5789,5792,5793,5795,5797,5800,5804,5808,5810,5812,5815,5816,5817,5821,5823,5824,5825,5826,5827,5828,5829,5835,5837,5838,5839,5840,5841,5842,5843,5851,5854,5855,5856,5858,5864,5868,5869,5871,5873,5875,5876,5879,5883,5884,5889,5890,5893,5895,5899,5900,5903,5905,5906,5907,5911,5912,5913,5916,5917,5920,5922,5924,5926,5927,5928,5929,5930,5931,5932,5933,5934,5937,5938,5939,5945,5949,5957,5960,5963,5976,5981,5983,5989,5990,5991,5993,5994,5995,6004,6005,6006,6008,6014,6017,6022,6028,6029,6036,6038,6040,6047,6060,6061,6062,6063,6066,6076,6077,6081,6082,6085,6086,6087,6095,6097,6102,6114,6118,6119,6120,6121,6125,6133,6135,6136,6142,6143,6144,6145,6149,6150,6151,6152,6153,6155,6157,6158,6164,6167,6168,6174,6175,6184,6186,6191,6192,6199,6201,6202,6203,6205,6208,6211,6213,6215,6217,6218,6220,6221,6222,6224,6225,6227,6231,6232,6233,6234,6240,6242,6243,6247,6249,6250,6252,6254,6255,6257,6258,6259,6262,6263,6264,6269,6271,6273,6274,6275,6276,6278,6282,6283,6286,6290,6291,6296,6303,6304,6308,6309,6312,6318,6319,6321,6322,6324,6329,6333,6338,6340,6342,6343,6345,6346,6347,6350,6357,6358,6359,6364,6374,6381,6382,6396,6407,6415,6419,6422,6424,6425,6426,6428,6429,6432,6435,6436,6437,6442,6444,6445,6446,6450,6454,6467,6468,6476,6478,6480,6481,6487,6489,6490,6491,6495,6502,6504,6509,6510,6512,6514,6516,6518,6525,6528,6529,6532,6533,6538,6540,6541,6547,6550,6551,6554,6556,6559,6561,6563,6564,6565,6567,6568,6569,6577,6578,6579,6580,6583,6584,6585,6588,6590,6591,6594,6595,6596,6597,6598,6599,6600,6603,6604,6605,6606,6608,6613,6615,6616,6618,6619,6620,6622,6623,6626,6627,6629,6634,6637,6640,6647,6650,6655,6662,6667,6668,6669,6672,6675,6677,6678,6679,6680,6681,6683,6686,6690,6693,6694,6695,6697,6698,6699,6700,6701,6705,6707,6708,6709,6710,6712,6714,6715,6717,6718,6721,6723,6728,6740,6741,6745,6748,6749,6759,6761,6763,6766,6771,6772,6779,6784,6786,6787,6790,6793,6794,6795,6796,6798,6799,6801,6807,6808,6812,6814,6823,6825,6831,6835,6836,6841,6844,6849,6866,6872,6875,6876,6881,6889,6895,6897,6898,6913,6915,6921,6928,6929,6951,6952,6964,6967,6972,6981,6982,6984,6985,6986,6987,6990,7010,7020,7023,7025,7030,7032,7038,7043,7047,7050,7054,7055,7056,7057,7058,7066,7067,7070,7071,7074,7081,7083,7093,7096,7108,7109,7117,7118,7125,7126,7131,7147,7148,7173,7181,7185,7189,7192,7193,7196,7218,7219,7220,7234,7239,7240,7248,7250,7252,7257,7258,7260,7266,7270,7279,7285,7305,7306,7346,7347,7350,7351,7354,7358,7359,7360,7361,7362,7363,7364,7366,7369,7371,7372,7375,7376,7378,7379,7381,7384,7386,7390,7393,7394,7395,7397,7403,7405,7410,7415,7428,7436,7441,7442,7445,7465,7471,7476,7549,7554,7563,7574,7600,7602,7605,7606,7608,7610,7611,7612,7614,7624,7632,7636,7641,7644,7646,7650,7653,7660,7662,7663,7665,7668,7672,7673,7676,7684,7687,7696,7697,7702,7703,7705,7709,7710,7711,7715,7719,7720,7724,7725,7726,7727,7728,7731,7739,7740,7741,7746,7747,7750,7752,7754,7755,7759,7761,7763,7764,7767,7768,7772,7773,7774,7776,7777,7779,7780,7784,7786,7791,7792,7794,7799,7806,7807,7808,7810,7813,7815,7817,7825,7831,7832,7834,7836,7839,7841,7843,7844,7845,7846,7848,7849,7850,7856,7859,7864,7866,7867,7868,7869,7870,7871,7875,7878,7880,7881,7882,7886,7889,7893,7894,7903,7908,7911,7912,7914,7916,7919,7926,7932,7934,7935,7936,7940,7941,7942,7943,7944,7953,7958,7961,7962,7963,7967,7971,7972,7977,7982,7984,7985,7988,7997,8000,8006,8011,8017,8035,8036,8038,8041,8042,8057,8067,8068,8086,8096,8098,8114,8115,8119,8125,8128,8141,8153,8155,8165,8168,8170,8179,8180,8183,8188,8205,8206,8218,8236,8237,8248,8255,8261,8263,8264,8266,8267,8270,8273,8274,8276,8299,8310,8322,8329,8334,8335,8337,8339,8341,8342,8351,8357,8361,8364,8378,8383,8389,8395,8396,8401,8406,8411,8413,8431,8434,8435,8449,8467,8468,8469,8470,8473,8474,8478,8480,8484,8488,8491,8493,8495,8505,8521,8526,8539,8540,8557,8561,8565,8576,8617,8619,8622,8625,8639,8641,8644,8648,8670,8672,8687,8689,8690,8692,8694,8698,8722,8728,8732,8734,8736,8756,8757,8765,8769,8776,8784,8787,8792,8794,8795,8808,8831,8834,8850,8852,8883,8884,8895,8903,8907,8918,8923,8929,8933,8936,8943,8944,8950,8953,8956,8957,8962,8963,8968,8979,8980,8986,9000,9005,9006,9017,9035,9038,9045,9047,9049,9052,9056,9058,9059,9060,9061,9063,9066,9068,9069,9070,9071,9075,9085,9086,9093,9095,9097,9098,9103,9111,9117,9118,9122,9127,9131,9132,9133,9134,9135,9138,9139,9140,9144,9147,9148,9149,9156,9157,9158,9167,9168,9173,9176,9177,9179,9182,9185,9186,9187,9188,9190,9192,9199,9200,9201,9202,9203,9206,9208,9213,9216,9217,9224,9225,9234,9235,9239,9244,9246,9247,9248,9250,9258,9260,9264,9271,9272,9277,9278,9279,9280,9283,9285,9288,9290,9293,9297,9298,9300,9305,9307,9309,9310,9312,9317,9323,9325,9328,9339,9340,9345,9362,9371,9377,9378,9379,9389,9390,9393,9394,9395,9396,9397,9398,9400,9401,9402,9403,9405,9407,9408,9420,9426,9428,9430,9431,9432,9436,9437,9443,9447,9448,9454,9455,9457,9459,9460,9461,9464,9468,9470,9473,9474,9475,9481,9491,9495,9496,9499,9504,9505,9507,9509,9510,9522,9531,9540,9555,9556,9560,9568,9597,9600,9604,9614,9628,9637,9646,9651,9653,9654,9656,9662,9669,9683,9689,9693,9697,9705,9708,9711,9717,9726,9727,9728,9731,9735,9736,9741,9745,9752,9753,9756,9760,9761,9762,9763,9766,9767,9774,9777,9784,9788,9792,9798,9803,9806,9809,9810,9813,9814,9815,9816,9820,9827,9829,9830,9831,9837,9839,9841,9843,9845,9850,9856,9864,9868,9873,9874,9880,9889,9896,9897,9899,9902,9908,9921,9929,9931,9938,9939,9947,9949,9966,9974,9982,9994,10052,10063,10094,10100,10102,10113,10121,10132,10143,10181,10190,10212,10272,10277,10284,10293,10301,10313,10323,10327,10364,10365,10440,10442,10474,10657,10696,10711,10721,10722,10725,10726,10731,10734,10739,10741,10789,10791,10794,10799,10803,10809,10814,10817,10822,10827,10925,10992,11016,11121,11143,11159,11188,11210,11443,11529,11701,11731,11748,11755,11885,11886,11974,11984]::int[]) n
  union all select 'statement', n, exists (select 1 from oma_events e where e.kind = 'formalized' and e.detail = 'https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/' || n) from unnest(array[21,141,205,267,317,334,337,339,349,352,375,378,394,413,438,444,461,463,465,467,471,493,494,498,500,505,512,590,617,632,701,717,759,761,769,780,801,803,804,807,808,810,812,813,829,869,885,898,934,942,947,957,959,963,967,969,971,973,979,980,985,990,994,998,1001,1003,1006,1007,1009,1010,1017,1019,1020,1031,1035,1043,1044,1056,1062,1068,1071,1073,1074,1084,1085,1095,1098,1114,1115,1116,1118,1119,1147,1151,1152,1168,1172,1186,1191,1202,1205,1206,1209,1217,1222,1226,1234,1238,1246,1248,1250,1251,1259,1260,1299,1300,1302,1303,1313,1325,1366,1370,1372,1387,1390,1406,1408,1413,1418,1444,1456,1480,1489,1491,1497,1503,1505,1522,1530,1536,1549,1564,1565,1588,1598,1602,1615,1616,1618,1619,2427,4657,4710,4713,4758,5200,5209,5224,5225,5226,5239,5240,5242,5245,5248,5266,5285,5293,5295,5296,5303,5320,5337,5348,5399,5400,5401,5402,5405,5406,5407,5408,5409,5411,5413,5416,5418,5419,5422,5425,5429,5433,5434,5440,5467,5492,5498,5506,5509,5521,5532,5540,5547,5549,5557,5559,5563,5565,5567,5577,5585,5588,5598,5607,5625,5628,5631,5637,5648,5651,5652,5660,5661,5663,5664,5668,5670,5679,5690,5692,5701,5706,5708,5721,5723,5733,5735,5740,5742,5745,5753,5755,5757,5760,5761,5771,5773,5774,5775,5778,5784,5786,5790,5791,5799,5801,5803,5807,5809,5811,5830,5834,5847,5849,5860,5861,5862,5866,5870,5881,5882,5885,5886,5894,5904,5914,5925,5935,5940,5941,5944,5947,5950,5951,5953,5954,5956,5958,5961,5962,5964,5965,5967,5968,5969,5971,5973,5974,5980,5986,5987,5988,5996,5998,6001,6011,6013,6015,6024,6026,6037,6039,6041,6046,6054,6055,6057,6058,6068,6069,6070,6071,6072,6073,6080,6083,6089,6090,6092,6096,6099,6101,6103,6105,6108,6110,6112,6115,6116,6122,6124,6126,6127,6128,6137,6139,6171,6173,6176,6185,6189,6195,6212,6216,6226,6230,6235,6239,6241,6265,6270,6279,6285,6289,6298,6301,6307,6325,6326,6328,6330,6332,6349,6351,6353,6356,6360,6363,6366,6372,6373,6379,6385,6387,6388,6389,6391,6392,6394,6397,6398,6399,6400,6403,6404,6406,6408,6411,6413,6414,6416,6418,6421,6423,6427,6430,6431,6434,6438,6440,6441,6452,6453,6458,6460,6461,6462,6463,6464,6466,6469,6470,6471,6472,6474,6482,6484,6486,6488,6494,6496,6497,6503,6506,6507,6508,6511,6513,6515,6517,6520,6521,6522,6526,6527,6530,6531,6535,6536,6537,6544,6545,6546,6548,6549,6560,6572,6575,6576,6581,6586,6593,6609,6628,6631,6633,6636,6639,6642,6643,6648,6649,6651,6659,6664,6665,6670,6671,6676,6684,6685,6687,6688,6692,6702,6703,6704,6711,6719,6722,6724,6726,6727,6729,6731,6732,6734,6735,6737,6738,6739,6742,6743,6744,6746,6747,6751,6752,6753,6757,6758,6764,6767,6769,6773,6774,6775,6776,6778,6780,6782,6783,6785,6788,6789,6797,6800,6802,6805,6806,6809,6810,6811,6816,6817,6820,6821,6826,6829,6830,6834,6842,6845,6846,6847,6848,6851,6852,6854,6857,6861,6862,6867,6869,6870,6873,6874,6878,6879,6880,6882,6883,6885,6886,6887,6888,6891,6893,6894,6899,6900,6903,6905,6907,6909,6910,6914,6916,6918,6919,6920,6922,6923,6924,6926,6930,6931,6933,6935,6940,6943,6945,6946,6947,6948,6949,6950,6954,6956,6957,6959,6960,6961,6962,6965,6971,6973,6975,6977,6983,7046,7082,7120,7122,7128,7134,7141,7143,7163,7169,7175,7205,7251,7290,7336,7349,7353,7355,7368,7373,7380,7382,7385,7388,7389,7391,7396,7398,7399,7406,7408,7409,7411,7412,7413,7416,7417,7418,7419,7421,7426,7427,7429,7431,7434,7435,7437,7438,7440,7449,7452,7454,7457,7459,7460,7462,7463,7472,7473,7474,7475,7481,7490,7494,7504,7506,7509,7517,7518,7520,7523,7527,7528,7532,7533,7535,7536,7537,7538,7540,7546,7565,7567,7578,7582,7583,7586,7590,7597,7613,7617,7640,7642,7652,7657,7666,7678,7679,7685,7686,7692,7693,7694,7695,7698,7699,7704,7706,7707,7712,7713,7714,7718,7723,7729,7730,7732,7736,7737,7742,7743,7744,7745,7748,7749,7756,7757,7769,7775,7778,7782,7785,7787,7790,7798,7800,7802,7803,7804,7805,7809,7811,7812,7814,7816,7819,7821,7823,7826,7827,7829,7830,7837,7842,7847,7852,7860,7862,7863,7865,7872,7874,7877,7884,7888,7892,7895,7899,7900,7902,7905,7906,7913,7915,7917,7920,7921,7930,7931,7933,7939,7945,7947,7948,7951,7956,7959,7966,7968,7969,7973,7978,7979,7980,7983,7989,7992,7994,7996,8003,8004,8015,8021,8022,8023,8024,8025,8027,8028,8031,8032,8033,8034,8040,8043,8045,8050,8052,8053,8056,8058,8060,8061,8064,8066,8070,8072,8073,8076,8077,8080,8081,8082,8083,8084,8087,8090,8091,8092,8095,8097,8099,8100,8101,8102,8103,8104,8109,8111,8113,8116,8117,8118,8121,8122,8123,8127,8129,8130,8131,8132,8137,8139,8140,8143,8144,8148,8149,8150,8151,8159,8161,8162,8163,8169,8171,8173,8175,8176,8186,8189,8191,8193,8195,8197,8202,8208,8210,8211,8212,8216,8217,8219,8220,8222,8223,8225,8226,8229,8230,8233,8235,8238,8239,8240,8243,8246,8247,8249,8252,8256,8262,8271,8272,8277,8278,8279,8281,8282,8283,8284,8285,8287,8288,8290,8292,8293,8294,8302,8305,8308,8311,8312,8313,8315,8318,8319,8321,8324,8325,8327,8330,8331,8332,8338,8347,8348,8352,8355,8370,8371,8373,8374,8375,8377,8379,8382,8390,8391,8393,8394,8397,8398,8402,8404,8407,8409,8410,8412,8419,8424,8425,8426,8430,8432,8433,8438,8439,8442,8446,8447,8448,8450,8451,8454,8455,8456,8458,8460,8461,8465,8466,8471,8472,8475,8477,8479,8482,8483,8485,8487,8489,8503,8507,8508,8510,8511,8512,8513,8514,8517,8518,8519,8520,8527,8528,8529,8532,8536,8537,8538,8541,8542,8543,8544,8545,8546,8547,8548,8549,8551,8553,8554,8556,8560,8563,8564,8566,8567,8568,8569,8572,8574,8580,8585,8586,8588,8590,8591,8593,8594,8597,8599,8601,8602,8607,8609,8610,8611,8612,8613,8615,8616,8618,8624,8627,8628,8629,8633,8636,8637,8643,8645,8647,8649,8653,8654,8657,8659,8667,8668,8669,8673,8674,8678,8679,8684,8685,8686,8696,8700,8701,8703,8704,8708,8711,8714,8715,8718,8721,8723,8726,8729,8730,8733,8735,8738,8739,8741,8743,8744,8745,8746,8747,8750,8751,8752,8753,8758,8759,8761,8762,8763,8764,8766,8768,8772,8774,8775,8777,8778,8779,8780,8781,8783,8785,8789,8790,8791,8796,8797,8799,8802,8803,8809,8813,8814,8816,8817,8818,8819,8820,8822,8823,8824,8826,8832,8837,8838,8842,8846,8847,8849,8853,8854,8856,8857,8858,8859,8860,8861,8863,8865,8866,8867,8868,8869,8871,8872,8874,8876,8879,8880,8882,8889,8891,8893,8896,8900,8901,8904,8905,8906,8909,8910,8911,8916,8917,8919,8924,8926,8927,8928,8930,8935,8937,8938,8942,8945,8946,8948,8949,8954,8961,8964,8966,8967,8969,8972,8976,8977,8981,8983,8984,8990,8992,8999,9004,9008,9009,9011,9012,9014,9016,9019,9026,9027,9030,9033,9037,9039,9041,9043,9044,9048,9051,9054,9062,9064,9065,9067,9072,9082,9083,9090,9091,9092,9094,9105,9106,9108,9110,9113,9116,9125,9126,9137,9145,9151,9153,9159,9161,9165,9169,9172,9175,9180,9183,9184,9193,9196,9198,9205,9207,9214,9219,9222,9231,9233,9237,9241,9243,9251,9252,9257,9267,9269,9270,9273,9274,9275,9276,9281,9287,9289,9292,9299,9302,9313,9316,9318,9320,9322,9324,9326,9327,9329,9330,9331,9333,9335,9342,9344,9346,9348,9349,9352,9358,9359,9366,9373,9374,9376,9380,9382,9385,9387,9388,9391,9392,9404,9409,9419,9424,9434,9439,9441,9442,9463,9465,9478,9480,9482,9483,9488,9493,9498,9501,9503,9508,9514,9516,9523,9525,9526,9527,9530,9532,9534,9536,9539,9542,9543,9544,9547,9549,9550,9554,9557,9559,9561,9562,9564,9567,9574,9576,9577,9580,9584,9586,9589,9590,9591,9594,9601,9603,9605,9607,9608,9609,9610,9615,9616,9619,9620,9623,9625,9627,9631,9632,9634,9635,9638,9640,9644,9645,9650,9652,9655,9657,9658,9660,9663,9666,9673,9674,9678,9681,9686,9687,9688,9690,9694,9695,9702,9703,9704,9706,9712,9713,9714,9719,9721,9729,9730,9733,9738,9740,9742,9743,9746,9750,9754,9758,9759,9768,9769,9770,9773,9780,9790,9791,9793,9796,9799,9801,9802,9807,9808,9811,9821,9825,9826,9832,9834,9835,9838,9846,9847,9851,9860,9872,9881,9892,9894,9895,9898,9906,9910,9911,9915,9916,9917,9927,9928,9932,9940,9942,9952,9955,9963,9969,9976,9978,9986,9998,10039,10044,10077,10303,10335,10377,10444,10479,10489,10511,10546,10592,10679,10695,10714,10719,10720,10724,10727,10728,10733,10738,10746,10889,11146,11185,11578,11587,11620,11623,11626,11631,11636,11644,11654,11657,11659,11661,11675,11676,11681,11683,11687,11689,11690,11691,11694,11698,11706,11707,11708,11709,11710,11711,11713,11714,11715,11716,11717,11718,11719,11720,11721,11722,11723,11724,11725,11726,11728,11729,11732,11733,11734,11735,11736,11737,11738,11739,11740,11741,11742,11745,11746,11747,11749,11751,11752,11753,11754,11756,11757,11758,11760,11761,11762,11763,11764,11765,11766,11767,11768,11769,11770,11771,11772,11773,11774,11775,11776,11777,11778,11779,11781,11783,11784,11785,11786,11787,11788,11789,11790,11791,11792,11793,11794,11795,11796,11797,11798,11799,11800,11801,11802,11803,11804,11805,11806,11807,11809,11810,11811,11812,11813,11814,11815,11816,11817,11818,11819,11820,11821,11822,11824,11825,11826,11827,11828,11829,11830,11831,11833,11834,11835,11837,11839,11840,11841,11842,11844,11845,11846,11847,11848,11849,11850,11851,11852,11853,11854,11855,11856,11857,11859,11860,11861,11862,11863,11864,11865,11866,11868,11869,11873,11875,11876,11877,11878,11881,11882,11883,11884,11887,11888,11889,11890,11891,11892,11894,11895,11896,11897,11898,11902,11903,11904,11905,11906,11907,11908,11909,11910,11912,11913,11915,11916,11917,11918,11919,11920,11921,11922,11923,11924,11925,11927,11929,11930,11932,11933,11934,11935,11936,11937,11938,11939,11941,11942,11943,11944,11945,11946,11947,11948,11949,11950,11951,11952,11953,11954,11955,11957,11958,11959,11960,11961,11962,11963,11964,11965,11966,11967,11970,11971,11972,11973,11975,11976,11977,11978,11979,11980,11981,11982,11985,11987,11988,11989,11991,11992,11993,11994,11995,11997]::int[]) n
  union all select 'shorter', n, exists (select 1 from oma_events e where e.kind = 'shorter' and e.detail = 'https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/' || n) from unnest(array[3531,7319,7840,8250,8254,8295,8296,8297,8298,8300,8303,8304,8306,8316,8340,8358,8359,8360,8362,8367,8368,8384,8385,8386,8387,8388,8415,8416,8417,8420,8421,8423,8437,8443,8490,8504,8516,8523,8533,8552,8578,8583,8584,8596,8600,8626,8630,8631,8632,8638,8662,8663,8665,8666,8677,8870,8940,9341,9375,9417,9445,9494,9513,9528,9699,9723,9812,10580,10582,10730,10735,11487,11545,11616,11641,11695,11712,11730,11743,11744,11750,11759,11780,11808,11823,11832,11836,11843,11858,11867,11870,11871,11874,11880,11893,11900,11901,11911,11914,11928,11940,11956,11968,11969,11983,11986,11990]::int[]) n
) k group by k.kind order by k.kind;
