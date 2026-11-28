import OMAStatements.S_oeis_a203530

-- Problem: A203530: a(n) = Product_{1 <= i < j <= n} (c(i) + c(j)); c = A002808 = composite numbers.
-- Upstream: formal-conjectures statements/oeis-a203530.lean:0 (declaration OMA.S_oeis_a203530.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Disprove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Idea: n = 4 is a counterexample. The first composites are 4, 6, 8, 9 (counting the composites
-- below 4, 6, 8, 9 gives 0, 1, 2, 3, and Nat.nth_count), so
-- a(4) = (4+6)(4+8)(6+8)(4+9)(6+9)(8+9) = 5569200, while A000178(4) = 0!1!2!3!4! = 288 does
-- not divide 5569200 (the remainder is 144).

namespace FS4A203530

theorem cnt_step (q : ℕ → Prop) [DecidablePred q] (k m : ℕ) (h : Nat.count q k = m)
    (hq : q k) : Nat.count q (k + 1) = m + 1 := by
  rw [Nat.count_succ, h, if_pos hq]

theorem cnt_skip (q : ℕ → Prop) [DecidablePred q] (k m : ℕ) (h : Nat.count q k = m)
    (hq : ¬ q k) : Nat.count q (k + 1) = m := by
  rw [Nat.count_succ, h, if_neg hq, Nat.add_zero]

theorem c0 : Nat.count (fun k => 1 < k ∧ ¬ Nat.Prime k) 0 = 0 := by
  simp

theorem c1 : Nat.count (fun k => 1 < k ∧ ¬ Nat.Prime k) 1 = 0 :=
  cnt_skip _ 0 0 c0 (by norm_num)

theorem c2 : Nat.count (fun k => 1 < k ∧ ¬ Nat.Prime k) 2 = 0 :=
  cnt_skip _ 1 0 c1 (by norm_num)

theorem c3 : Nat.count (fun k => 1 < k ∧ ¬ Nat.Prime k) 3 = 0 :=
  cnt_skip _ 2 0 c2 (by norm_num)

theorem c4 : Nat.count (fun k => 1 < k ∧ ¬ Nat.Prime k) 4 = 0 :=
  cnt_skip _ 3 0 c3 (by norm_num)

theorem c5 : Nat.count (fun k => 1 < k ∧ ¬ Nat.Prime k) 5 = 1 :=
  cnt_step _ 4 0 c4 (by norm_num)

theorem c6 : Nat.count (fun k => 1 < k ∧ ¬ Nat.Prime k) 6 = 1 :=
  cnt_skip _ 5 1 c5 (by norm_num)

theorem c7 : Nat.count (fun k => 1 < k ∧ ¬ Nat.Prime k) 7 = 2 :=
  cnt_step _ 6 1 c6 (by norm_num)

theorem c8 : Nat.count (fun k => 1 < k ∧ ¬ Nat.Prime k) 8 = 2 :=
  cnt_skip _ 7 2 c7 (by norm_num)

theorem c9 : Nat.count (fun k => 1 < k ∧ ¬ Nat.Prime k) 9 = 3 :=
  cnt_step _ 8 2 c8 (by norm_num)

theorem v0 : OMA.S_oeis_a203530.c 0 = 4 := by
  have h := Nat.nth_count (p := fun k => 1 < k ∧ ¬ Nat.Prime k)
    (show (fun k => 1 < k ∧ ¬ Nat.Prime k) 4 from ⟨by norm_num, by norm_num⟩)
  rw [c4] at h
  exact h

theorem v1 : OMA.S_oeis_a203530.c 1 = 6 := by
  have h := Nat.nth_count (p := fun k => 1 < k ∧ ¬ Nat.Prime k)
    (show (fun k => 1 < k ∧ ¬ Nat.Prime k) 6 from ⟨by norm_num, by norm_num⟩)
  rw [c6] at h
  exact h

theorem v2 : OMA.S_oeis_a203530.c 2 = 8 := by
  have h := Nat.nth_count (p := fun k => 1 < k ∧ ¬ Nat.Prime k)
    (show (fun k => 1 < k ∧ ¬ Nat.Prime k) 8 from ⟨by norm_num, by norm_num⟩)
  rw [c8] at h
  exact h

theorem v3 : OMA.S_oeis_a203530.c 3 = 9 := by
  have h := Nat.nth_count (p := fun k => 1 < k ∧ ¬ Nat.Prime k)
    (show (fun k => 1 < k ∧ ¬ Nat.Prime k) 9 from ⟨by norm_num, by norm_num⟩)
  rw [c9] at h
  exact h

end FS4A203530

open OMA.S_oeis_a203530 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a203530.main) := by
  intro H
  have h := H 4 (by norm_num)
  have ha : a 4 = 5569200 := by
    simp [a, Finset.prod_range_succ, FS4A203530.v0, FS4A203530.v1, FS4A203530.v2,
      FS4A203530.v3]
  have hs : sf 4 = 288 := by
    simp [sf, Finset.prod_range_succ, Nat.factorial]
  rw [ha, hs] at h
  omega
