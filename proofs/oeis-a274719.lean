import OMAStatements.S_oeis_a274719

-- Problem: A274719: Expansion of Product_{k >= 1} (1-q^(2*k)).
-- Upstream: formal-conjectures statements/oeis-a274719.lean:0 (declaration OMA.S_oeis_a274719.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: the product over k < n of (1 - X^(2(k+1))) is the expansion (X -> X^2) of the
-- product of (1 - X^(k+1)), so a(n) = 0 for odd n and a(2m) is the coefficient of X^m in the
-- product of (1 - X^(k+1)) over k < 2m, which by the pentagonal number theorem
-- (PowerSeries.coeff_prod_one_sub_X_pow_eventually_eq, plus stabilisation of the coefficients)
-- is (-1)^k if m = pentagonal k and 0 otherwise. Next, 24m + 1 is a square iff m is a pentagonal
-- number (24 pentagonal(k) + 1 = (6k - 1)^2), and 24m + 13 is never a square (mod 8). Finally,
-- for M prime to 3, b(M) = 1 if M is a square and 0 otherwise (b(M) = 0 iff some prime has an odd
-- exponent in M).

/-- Coefficient m of the product of (1 - X^(k+1)) over k < N does not change for N >= m. -/
theorem a274719_stab (m N : ℕ) (hmN : m ≤ N) : ∀ j : ℕ,
    PowerSeries.coeff m
        (∏ k ∈ Finset.range (N + j), (1 - PowerSeries.X ^ (k + 1) : PowerSeries ℤ)) =
      PowerSeries.coeff m
        (∏ k ∈ Finset.range N, (1 - PowerSeries.X ^ (k + 1) : PowerSeries ℤ)) := by
  intro j
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [← Nat.add_assoc, Finset.prod_range_succ, mul_sub, mul_one, map_sub,
      PowerSeries.coeff_mul_X_pow', if_neg (show ¬ (N + j + 1 ≤ m) by omega), sub_zero, ih]

/-- The pentagonal number theorem for the truncated products. -/
theorem a274719_pent (m N : ℕ) (hmN : m ≤ N) :
    PowerSeries.coeff m
        (∏ k ∈ Finset.range N, (1 - PowerSeries.X ^ (k + 1) : PowerSeries ℤ)) =
      PowerSeries.coeff m (PowerSeries.pentagonalSeries ℤ) := by
  obtain ⟨s0, hs0⟩ :=
    Filter.eventually_atTop.mp (PowerSeries.coeff_prod_one_sub_X_pow_eventually_eq ℤ m)
  obtain ⟨M, hM1, hM2⟩ : ∃ M, N ≤ M ∧ (s0.sup id).succ ≤ M :=
    ⟨max N (s0.sup id).succ, le_max_left _ _, le_max_right _ _⟩
  have hsub : s0 ⊆ Finset.range M :=
    (Finset.subset_range_sup_succ s0).trans (Finset.range_subset_range.mpr hM2)
  have h1 := hs0 (Finset.range M) hsub
  have h2 := a274719_stab m N hmN (M - N)
  rw [show N + (M - N) = M by omega] at h2
  rw [← h2, h1]

/-- Expanding X -> X^2. -/
theorem a274719_expand (N : ℕ) :
    PowerSeries.expand 2 two_ne_zero
        (∏ k ∈ Finset.range N, (1 - PowerSeries.X ^ (k + 1) : PowerSeries ℤ)) =
      ∏ k ∈ Finset.range N, (1 - PowerSeries.X ^ (2 * (k + 1)) : PowerSeries ℤ) := by
  rw [map_prod]
  refine Finset.prod_congr rfl (fun k _ => ?_)
  rw [map_sub, map_one, map_pow, PowerSeries.expand_X, ← pow_mul]

/-- 24 pentagonal(k) + 1 = (6k - 1)^2. -/
theorem a274719_sq (k : ℤ) : IsSquare (24 * pentagonal k + 1) := by
  refine ⟨(6 * k - 1).natAbs, ?_⟩
  have h1 := two_mul_natCast_pentagonal k
  have h3 : ((24 * pentagonal k + 1 : ℕ) : ℤ) =
      (((6 * k - 1).natAbs * (6 * k - 1).natAbs : ℕ) : ℤ) := by
    rw [Int.natAbs_mul_self, Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat]
    linear_combination 12 * h1
  exact Nat.cast_injective h3

/-- If 24m + 1 is a square, then m is a pentagonal number. -/
theorem a274719_pent_of_sq (m : ℕ) (h : IsSquare (24 * m + 1)) : ∃ k, pentagonal k = m := by
  obtain ⟨r, hr⟩ := h
  obtain ⟨q, s, hs, rfl⟩ : ∃ q s, s < 6 ∧ r = 6 * q + s :=
    ⟨r / 6, r % 6, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod r 6).symm⟩
  interval_cases s
  · exfalso
    have hz := congrArg (Nat.cast : ℕ → ℤ) hr
    push_cast at hz
    have e : (24 * (m : ℤ) + 1) = 12 * (3 * ((q : ℤ) * (q : ℤ))) := by linear_combination hz
    omega
  · refine ⟨-(q : ℤ), ?_⟩
    have hz := congrArg (Nat.cast : ℕ → ℤ) hr
    push_cast at hz
    have hp := two_mul_natCast_pentagonal_neg (q : ℤ)
    have h24 : (24 : ℤ) * (pentagonal (-(q : ℤ)) : ℤ) = 24 * (m : ℤ) := by
      linear_combination 12 * hp - hz
    have h' : (pentagonal (-(q : ℤ)) : ℤ) = (m : ℤ) := by linarith
    exact_mod_cast h'
  · exfalso
    have hz := congrArg (Nat.cast : ℕ → ℤ) hr
    push_cast at hz
    have e : (24 * (m : ℤ) + 1) = 12 * (3 * ((q : ℤ) * (q : ℤ)) + 2 * (q : ℤ)) + 4 := by
      linear_combination hz
    omega
  · exfalso
    have hz := congrArg (Nat.cast : ℕ → ℤ) hr
    push_cast at hz
    have e : (24 * (m : ℤ) + 1) = 12 * (3 * ((q : ℤ) * (q : ℤ)) + 3 * (q : ℤ)) + 9 := by
      linear_combination hz
    omega
  · exfalso
    have hz := congrArg (Nat.cast : ℕ → ℤ) hr
    push_cast at hz
    have e : (24 * (m : ℤ) + 1) = 12 * (3 * ((q : ℤ) * (q : ℤ)) + 4 * (q : ℤ) + 1) + 4 := by
      linear_combination hz
    omega
  · refine ⟨(q : ℤ) + 1, ?_⟩
    have hz := congrArg (Nat.cast : ℕ → ℤ) hr
    push_cast at hz
    have hp := two_mul_natCast_pentagonal ((q : ℤ) + 1)
    have h24 : (24 : ℤ) * (pentagonal ((q : ℤ) + 1) : ℤ) = 24 * (m : ℤ) := by
      linear_combination 12 * hp - hz
    have h' : (pentagonal ((q : ℤ) + 1) : ℤ) = (m : ℤ) := by linarith
    exact_mod_cast h'

/-- 24m + 13 is never a square. -/
theorem a274719_odd (m : ℕ) : ¬ IsSquare (12 * (2 * m + 1) + 1) := by
  rintro ⟨r, hr⟩
  obtain ⟨q, s, hs, rfl⟩ : ∃ q s, s < 4 ∧ r = 4 * q + s :=
    ⟨r / 4, r % 4, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod r 4).symm⟩
  interval_cases s
  · have hz := congrArg (Nat.cast : ℕ → ℤ) hr
    push_cast at hz
    have e : (24 * (m : ℤ) + 13) = 8 * (2 * ((q : ℤ) * (q : ℤ))) := by linear_combination hz
    omega
  · have hz := congrArg (Nat.cast : ℕ → ℤ) hr
    push_cast at hz
    have e : (24 * (m : ℤ) + 13) = 8 * (2 * ((q : ℤ) * (q : ℤ)) + (q : ℤ)) + 1 := by
      linear_combination hz
    omega
  · have hz := congrArg (Nat.cast : ℕ → ℤ) hr
    push_cast at hz
    have e : (24 * (m : ℤ) + 13) = 8 * (2 * ((q : ℤ) * (q : ℤ)) + 2 * (q : ℤ)) + 4 := by
      linear_combination hz
    omega
  · have hz := congrArg (Nat.cast : ℕ → ℤ) hr
    push_cast at hz
    have e : (24 * (m : ℤ) + 13) = 8 * (2 * ((q : ℤ) * (q : ℤ)) + 3 * (q : ℤ) + 1) + 1 := by
      linear_combination hz
    omega

/-- For M prime to 3, every prime factor of M is different from 3. -/
theorem a274719_b_eq (M : ℕ) (h3 : ¬ 3 ∣ M) :
    OMA.S_oeis_a274719.b M = ∏ p ∈ M.primeFactors, (1 + (-1) ^ (M.factorization p)) / 2 := by
  have hne : ∀ p ∈ M.primeFactors, p ≠ 3 := fun p hp h =>
    h3 (h ▸ Nat.dvd_of_mem_primeFactors hp)
  exact Finset.prod_congr rfl (fun p hp => if_neg (hne p hp))

/-- b(M) = 1 for a square M prime to 3. -/
theorem a274719_b_sq (M : ℕ) (hM : M ≠ 0) (h3 : ¬ 3 ∣ M) (hs : IsSquare M) :
    OMA.S_oeis_a274719.b M = 1 := by
  rw [a274719_b_eq M h3]
  obtain ⟨r, rfl⟩ := hs
  have hr : r ≠ 0 := by
    rintro rfl
    exact hM rfl
  apply Finset.prod_eq_one
  intro p _
  rw [Nat.factorization_mul hr hr, Finsupp.add_apply, ← two_mul, pow_mul]
  norm_num

/-- b(M) = 0 for a non-square M prime to 3. -/
theorem a274719_b_nsq (M : ℕ) (hM : M ≠ 0) (h3 : ¬ 3 ∣ M) (hs : ¬ IsSquare M) :
    OMA.S_oeis_a274719.b M = 0 := by
  rw [a274719_b_eq M h3]
  have hex : ∃ p ∈ M.primeFactors, ¬ Even (M.factorization p) := by
    by_contra hcon
    apply hs
    have hall : ∀ p ∈ M.primeFactors, Even (M.factorization p) := fun p hp => by
      by_contra hodd
      exact hcon ⟨p, hp, hodd⟩
    refine ⟨M.factorization.prod (fun p e => p ^ (e / 2)), ?_⟩
    rw [← Finsupp.prod_mul]
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hM]
    apply Finsupp.prod_congr
    intro p hp
    rw [← pow_add]
    congr 1
    obtain ⟨t, ht⟩ := hall p hp
    omega
  obtain ⟨p, hp, hodd⟩ := hex
  apply Finset.prod_eq_zero hp
  rw [Nat.not_even_iff_odd] at hodd
  rw [hodd.neg_one_pow]
  norm_num

open OMA.S_oeis_a274719 in
theorem OMA.solution : type_of% @OMA.S_oeis_a274719.main := by
  intro n
  have ha : a n = if 2 ∣ n then PowerSeries.coeff (n / 2)
      (∏ k ∈ Finset.range n, (1 - PowerSeries.X ^ (k + 1) : PowerSeries ℤ)) else 0 := by
    show PowerSeries.coeff n
      (∏ k ∈ Finset.range n, (1 - PowerSeries.X ^ (2 * (k + 1)) : PowerSeries ℤ)) = _
    rw [← a274719_expand n, PowerSeries.coeff_expand]
  have hA : A089806 n = b (12 * n + 1) := rfl
  rw [ha, hA]
  rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
  · rw [if_pos (dvd_mul_right 2 m), show 2 * m / 2 = m by omega,
      a274719_pent m (2 * m) (by omega), show 12 * (2 * m) + 1 = 24 * m + 1 by ring]
    by_cases hs : IsSquare (24 * m + 1)
    · obtain ⟨k, hk⟩ := a274719_pent_of_sq m hs
      rw [a274719_b_sq (24 * m + 1) (by omega) (by omega) hs, ← hk,
        PowerSeries.coeff_pentagonalSeries_pentagonal]
      rcases Int.units_eq_one_or (Int.negOnePow k) with h1 | h1 <;> simp [h1]
    · have hn : ¬ ∃ k, pentagonal k = m := by
        rintro ⟨k, rfl⟩
        exact hs (a274719_sq k)
      rw [a274719_b_nsq (24 * m + 1) (by omega) (by omega) hs,
        PowerSeries.coeff_pentagonalSeries_eq_zero ℤ hn, abs_zero]
  · rw [if_neg (show ¬ 2 ∣ 2 * m + 1 by omega), abs_zero,
      a274719_b_nsq (12 * (2 * m + 1) + 1) (by omega) (by omega) (a274719_odd m)]
