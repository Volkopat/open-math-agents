import OMAStatements.S_oeis_a082381

-- Problem: A082381: Sequence of the squared digital root of a number until 1 or 4 is reached. The initial numbers 1,2,..n are not output.
-- Upstream: formal-conjectures statements/oeis-a082381.lean:0 (declaration OMA.S_oeis_a082381.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: f n = (n mod 10)^2 + f (n / 10). Below 1000, f is the three-digit formula g8381,
-- whose values are at most 243. For n >= 100, f n < n: with digits a >= 1, b, c of a three-digit
-- n, a^2 + b^2 + c^2 <= 9a + 9b + 9c < 100a + 10b + c, and for n >= 1000, f n <= 81 + f (n / 10).
-- Also f n >= 1 for n >= 1. So by strong induction it suffices to check 1 <= n <= 99, where at
-- most 14 steps reach 1 or 4 (a finite check by decide).

def g8381 (n : ℕ) : ℕ := (n % 10) ^ 2 + (n / 10 % 10) ^ 2 + (n / 10 / 10 % 10) ^ 2

set_option maxRecDepth 20000 in
lemma small8381 : ∀ n < 100, 1 ≤ n → ∃ k < 20, g8381^[k + 1] n = 1 ∨ g8381^[k + 1] n = 4 := by
  decide

open OMA.S_oeis_a082381 in
theorem OMA.solution : type_of% @OMA.S_oeis_a082381.main := by
  have hstep : ∀ n : ℕ, f n = (n % 10) ^ 2 + f (n / 10) := by
    intro n
    rcases Nat.eq_zero_or_pos n with h | h
    · rw [h]
      simp
    · unfold f
      rw [Nat.digits_def' (by norm_num : 1 < 10) h]
      simp only [List.map_cons, List.sum_cons]
  have hf0 : f 0 = 0 := by
    unfold f
    simp
  have hfg : ∀ m : ℕ, m < 1000 → f m = g8381 m := by
    intro m hm
    have h1 := hstep m
    have h2 := hstep (m / 10)
    have h3 := hstep (m / 10 / 10)
    have h4 : m / 10 / 10 / 10 = 0 := by omega
    rw [h4, hf0] at h3
    unfold g8381
    omega
  have hd : ∀ m : ℕ, (m % 10) ^ 2 ≤ 81 := by
    intro m
    have h9 : m % 10 ≤ 9 := by omega
    calc (m % 10) ^ 2 ≤ 9 ^ 2 := Nat.pow_le_pow_left h9 2
      _ = 81 := by norm_num
  have hgb : ∀ m : ℕ, g8381 m ≤ 243 := by
    intro m
    have e1 := hd m
    have e2 := hd (m / 10)
    have e3 := hd (m / 10 / 10)
    unfold g8381
    omega
  have hit : ∀ k m : ℕ, m < 1000 → f^[k] m = g8381^[k] m := by
    intro k
    induction k with
    | zero =>
      intro m _
      rfl
    | succ k ih =>
      intro m hm
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, hfg m hm]
      have hb := hgb m
      exact ih (g8381 m) (by omega)
  have hpos : ∀ n : ℕ, 1 ≤ n → 1 ≤ f n := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn
      rw [hstep n]
      by_cases h : n % 10 = 0
      · have h' := ih (n / 10) (by omega) (by omega)
        omega
      · have h' : 1 ≤ (n % 10) ^ 2 := Nat.one_le_pow _ _ (by omega)
        omega
  have hsq : ∀ m : ℕ, (m % 10) ^ 2 ≤ 9 * (m % 10) := by
    intro m
    rw [sq]
    exact Nat.mul_le_mul (show m % 10 ≤ 9 by omega) (le_refl (m % 10))
  have hlt : ∀ n : ℕ, 100 ≤ n → f n < n := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn
      by_cases hbig : n < 1000
      · rw [hfg n hbig]
        have c1 := hsq n
        have c2 := hsq (n / 10)
        have c3 := hsq (n / 10 / 10)
        unfold g8381
        omega
      · rw [hstep n]
        have d1 := hd n
        by_cases hm : n / 10 < 1000
        · have e1 := hfg (n / 10) hm
          have e2 := hgb (n / 10)
          omega
        · have e1 := ih (n / 10) (by omega) (by omega)
          omega
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [hfg 4 (by norm_num)]
    rfl
  · rw [hfg 16 (by norm_num)]
    rfl
  · rw [hfg 37 (by norm_num)]
    rfl
  · rw [hfg 58 (by norm_num)]
    rfl
  · rw [hfg 89 (by norm_num)]
    rfl
  · rw [hfg 145 (by norm_num)]
    rfl
  · rw [hfg 42 (by norm_num)]
    rfl
  · rw [hfg 20 (by norm_num)]
    rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    by_cases h100 : 100 ≤ n
    · obtain ⟨k, _, hk⟩ := ih (f n) (hlt n h100) (hpos n hn)
      refine ⟨k + 1, by omega, ?_⟩
      rw [Function.iterate_succ_apply]
      exact hk
    · obtain ⟨k, _, hr⟩ := small8381 n (by omega) hn
      refine ⟨k + 1, by omega, ?_⟩
      rw [hit (k + 1) n (by omega)]
      exact hr
