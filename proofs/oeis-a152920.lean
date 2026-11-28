import OMAStatements.S_oeis_a152920

-- Problem oeis-a152920: (Sum_{k=0..n+1} C(p+k, p) * 2^k * (n + 1 - k/2)) / (n + p + 2) equals the coefficient
-- of x^p in Sum_{j=0..n+p} (x + 2)^j.
-- Upstream: statements/oeis-a152920.lean (declaration OMA.S_oeis_a152920.main)
-- Credit: @cclyles (the owner of the agent is credited as the solver)
--
-- Proof: the coefficient of x^p in (x + 2)^j is C(j, p) * 2^(j - p), so the right-hand side is
-- T(n) = Sum_{i=0..n} C(p+i, p) * 2^i (induction on n; for n = 0 only j = p contributes).
-- The weighted sum S(n) = Sum_{k=0..n+1} C(p+k, p) * 2^k * (n + 1 - k/2) satisfies S(n) = (n + p + 2) * T(n),
-- by induction on n using C(p+n+2, p) * (n + 2) = (p + n + 2) * C(p+n+1, p).

open Finset Polynomial OMA.S_oeis_a152920

private lemma rect_eq_a152920 (p : ℕ) : ∀ n : ℕ,
    rectangular n p = ∑ i ∈ range (n + 1), ((p + i).choose p : ℚ) * 2 ^ i := by
  intro n
  induction n with
  | zero =>
    unfold rectangular
    rw [finset_sum_coeff]
    simp only [coeff_X_add_C_pow, zero_add]
    rw [sum_range_succ, sum_eq_zero, sum_range_one]
    · simp
    · intro j hj
      rw [mem_range] at hj
      rw [Nat.choose_eq_zero_of_lt hj]
      simp
  | succ n ih =>
    have e : n + 1 + p + 1 = (n + p + 1) + 1 := by ring
    unfold rectangular at ih ⊢
    have eT : ∑ i ∈ range (n + 1 + 1), ((p + i).choose p : ℚ) * 2 ^ i
        = ∑ i ∈ range (n + 1), ((p + i).choose p : ℚ) * 2 ^ i + ((p + (n + 1)).choose p : ℚ) * 2 ^ (n + 1) :=
      sum_range_succ _ _
    rw [e, sum_range_succ, coeff_add, ih, coeff_X_add_C_pow, eT]
    congr 1
    rw [show n + p + 1 - p = n + 1 by omega, show n + p + 1 = p + (n + 1) by ring]
    ring

private lemma main_sum_a152920 (p : ℕ) : ∀ n : ℕ,
    ∑ k ∈ range (n + 1 + 1), ((p + k).choose p : ℚ) * (2 ^ k * (((n : ℚ) + 1) - (k : ℚ) / 2))
      = ((n : ℚ) + p + 2) * ∑ i ∈ range (n + 1), ((p + i).choose p : ℚ) * 2 ^ i := by
  intro n
  induction n with
  | zero =>
    have h1 : (p + 1).choose p = p + 1 := Nat.choose_succ_self_right p
    simp only [zero_add, sum_range_succ, sum_range_zero, add_zero, Nat.choose_self, h1]
    push_cast
    ring
  | succ n ih =>
    have hq : ((p + (n + 1)).choose p : ℚ) * ((p : ℚ) + ((n : ℚ) + 2))
        = ((p + (n + 2)).choose p : ℚ) * ((n : ℚ) + 2) := by
      have h := Nat.choose_mul_succ_eq (p + (n + 1)) p
      rw [show p + (n + 1) + 1 - p = n + 2 by omega, show p + (n + 1) + 1 = p + (n + 2) by ring] at h
      exact_mod_cast h
    have eT : ∑ i ∈ range (n + 1 + 1), ((p + i).choose p : ℚ) * 2 ^ i
        = ∑ i ∈ range (n + 1), ((p + i).choose p : ℚ) * 2 ^ i + ((p + (n + 1)).choose p : ℚ) * 2 ^ (n + 1) :=
      sum_range_succ _ _
    have eS : ∑ k ∈ range (n + 1 + 1 + 1),
          ((p + k).choose p : ℚ) * (2 ^ k * ((((n + 1 : ℕ) : ℚ) + 1) - (k : ℚ) / 2))
        = ∑ k ∈ range (n + 1 + 1),
            ((p + k).choose p : ℚ) * (2 ^ k * ((((n + 1 : ℕ) : ℚ) + 1) - (k : ℚ) / 2))
          + ((p + (n + 1 + 1)).choose p : ℚ)
            * (2 ^ (n + 1 + 1) * ((((n + 1 : ℕ) : ℚ) + 1) - ((n + 1 + 1 : ℕ) : ℚ) / 2)) :=
      sum_range_succ _ _
    have hsplit : ∑ k ∈ range (n + 1 + 1),
          ((p + k).choose p : ℚ) * (2 ^ k * ((((n + 1 : ℕ) : ℚ) + 1) - (k : ℚ) / 2))
        = ∑ k ∈ range (n + 1 + 1), ((p + k).choose p : ℚ) * (2 ^ k * (((n : ℚ) + 1) - (k : ℚ) / 2))
          + ∑ k ∈ range (n + 1 + 1), ((p + k).choose p : ℚ) * 2 ^ k := by
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro k _
      push_cast
      ring
    rw [eS, hsplit, ih, eT]
    push_cast
    linear_combination (-(2 : ℚ) ^ (n + 1)) * hq

theorem OMA.solution : type_of% @OMA.S_oeis_a152920.main := by
  intro n p
  rw [rect_eq_a152920]
  unfold weighted
  simp only [triangle]
  have h := main_sum_a152920 p n
  have hne : (((n + 1 : ℕ) : ℚ) + (p : ℚ) + 1) ≠ 0 := by positivity
  rw [div_eq_iff hne]
  push_cast at h ⊢
  rw [h]
  ring
