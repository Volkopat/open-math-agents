import OMAStatements.S_oeis_a274039

-- Problem: A274039: Expansion of (x^4 + x^10) / (1 - 2*x + x^2).
-- Upstream: formal-conjectures statements/oeis-a274039.lean:0 (declaration OMA.S_oeis_a274039.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: N(4,1..4) = 4, 6, 20, 60 from the divisors and the mobius values, and N(4,k) >= 0
-- for all k >= 1 because the sum over the proper divisors d of k of |mobius(k/d)| 4^d is at most
-- 1 + 4 + ... + 4^(k-1) = (4^k - 1)/3 < 4^k. So M(4,.) is monotone with M(4,2) = 10,
-- M(4,3) = 30, M(4,4) = 90, which gives rmax(4,29) = 2 and rmax(4,30) = rmax(4,31) = 3, hence
-- A005377(29, 30, 31) = 44, 46, 49. The coefficient of X^30 in (sum A005377(n+1) X^n)(1 - 2X + X^2)
-- is 49 - 92 + 44 = 1, while that of X^4 + X^10 is 0.

open OMA.S_oeis_a274039 in
theorem OMA.solution : type_of% @OMA.S_oeis_a274039.main := by
  -- mobius values
  have mu1 : ArithmeticFunction.moebius 1 = 1 := ArithmeticFunction.moebius_apply_one
  have mu2 : ArithmeticFunction.moebius 2 = -1 :=
    ArithmeticFunction.moebius_apply_prime Nat.prime_two
  have mu3 : ArithmeticFunction.moebius 3 = -1 :=
    ArithmeticFunction.moebius_apply_prime Nat.prime_three
  have mu4 : ArithmeticFunction.moebius 4 = 0 := by
    apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
    intro h
    have h2 := h 2 ⟨1, by norm_num⟩
    rw [Nat.isUnit_iff] at h2
    omega
  -- N(4, 1), ..., N(4, 4)
  have N1 : N 4 1 = 4 := by
    rw [N, Nat.divisors_one, Finset.sum_singleton, Nat.div_one, mu1]
    norm_num
  have N2 : N 4 2 = 6 := by
    rw [N, Nat.Prime.divisors Nat.prime_two, Finset.sum_pair (by norm_num : (1 : ℕ) ≠ 2),
      Nat.div_one, Nat.div_self (by norm_num : 0 < 2), mu2, mu1]
    norm_num
  have N3 : N 4 3 = 20 := by
    rw [N, Nat.Prime.divisors Nat.prime_three, Finset.sum_pair (by norm_num : (1 : ℕ) ≠ 3),
      Nat.div_one, Nat.div_self (by norm_num : 0 < 3), mu3, mu1]
    norm_num
  have N4 : N 4 4 = 60 := by
    rw [N, show Nat.divisors 4 = {1, 2, 4} by decide,
      Finset.sum_insert (show (1 : ℕ) ∉ ({2, 4} : Finset ℕ) by decide),
      Finset.sum_pair (by norm_num : (2 : ℕ) ≠ 4), Nat.div_one,
      show (4 : ℕ) / 2 = 2 by norm_num, Nat.div_self (by norm_num : 0 < 4), mu4, mu2, mu1]
    norm_num
  -- N(4, k) >= 0
  have hc4 : ((4 : ℕ) : ℚ) = 4 := by norm_num
  have Npos : ∀ k : ℕ, 1 ≤ k → 0 ≤ N 4 k := by
    intro k hk
    have hgeom : ∀ j : ℕ, 3 * ∑ d ∈ Finset.range j, (4 : ℚ) ^ d + 1 = 4 ^ j := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        rw [Finset.sum_range_succ, pow_succ]
        linarith
    have hlow : ∀ d ∈ k.properDivisors, -((4 : ℚ) ^ d) ≤
        ((ArithmeticFunction.moebius (k / d) : ℤ) : ℚ) * (4 : ℚ) ^ d := by
      intro d _
      have h1 : -1 ≤ ArithmeticFunction.moebius (k / d) :=
        (abs_le.mp ArithmeticFunction.abs_moebius_le_one).1
      have hm : (-1 : ℚ) ≤ ((ArithmeticFunction.moebius (k / d) : ℤ) : ℚ) := by
        exact_mod_cast h1
      have hp : (0 : ℚ) ≤ 4 ^ d := by positivity
      linarith [mul_le_mul_of_nonneg_right hm hp]
    have hsub : ∑ d ∈ k.properDivisors, (4 : ℚ) ^ d ≤ ∑ d ∈ Finset.range k, (4 : ℚ) ^ d := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro d hd
        rw [Nat.mem_properDivisors] at hd
        exact Finset.mem_range.mpr hd.2
      · intro d _ _
        positivity
    have hS : -(∑ d ∈ k.properDivisors, (4 : ℚ) ^ d) ≤
        ∑ d ∈ k.properDivisors, ((ArithmeticFunction.moebius (k / d) : ℤ) : ℚ) * (4 : ℚ) ^ d := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_le_sum hlow
    have hg := hgeom k
    have hp : (0 : ℚ) ≤ 4 ^ k := by positivity
    rw [N, ← Nat.insert_self_properDivisors (by omega : k ≠ 0),
      Finset.sum_insert Nat.self_notMem_properDivisors, Nat.div_self (by omega : 0 < k), mu1,
      Int.cast_one, one_mul, hc4]
    apply mul_nonneg
    · positivity
    · linarith
  -- M(4, .)
  have M0 : M 4 0 = 0 := by
    simp [M]
  have Msucc : ∀ k k' : ℕ, k + 1 = k' → M 4 k' = M 4 k + N 4 k' := by
    intro k k' hk
    subst hk
    rw [M, M]
    exact Finset.sum_Icc_succ_top (Nat.le_add_left 1 k) _
  have M1 : M 4 1 = 4 := by linarith [Msucc 0 1 rfl, M0, N1]
  have M2 : M 4 2 = 10 := by linarith [Msucc 1 2 rfl, M1, N2]
  have M3 : M 4 3 = 30 := by linarith [Msucc 2 3 rfl, M2, N3]
  have M4 : M 4 4 = 90 := by linarith [Msucc 3 4 rfl, M3, N4]
  have Mmono : ∀ x y : ℕ, x ≤ y → M 4 x ≤ M 4 y := by
    intro x y hxy
    unfold M
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right hxy)
    intro k hk _
    exact Npos k (Finset.mem_Icc.mp hk).1
  -- rmax(4, n)
  have R : ∀ (n t t' : ℕ), t + 1 = t' → M 4 t ≤ (n : ℚ) → (n : ℚ) < M 4 t' → rmax 4 n = t := by
    intro n t t' ht h1 h2
    subst ht
    unfold rmax
    apply IsGreatest.csSup_eq
    refine ⟨h1, ?_⟩
    intro x hx
    have hx' : M 4 x ≤ (n : ℚ) := hx
    by_contra hcon
    have h3 := Mmono (t + 1) x (by omega)
    linarith
  have r29 : rmax 4 29 = 2 := R 29 2 3 rfl (by rw [M2]; norm_num) (by rw [M3]; norm_num)
  have r30 : rmax 4 30 = 3 := R 30 3 4 rfl (by rw [M3]; norm_num) (by rw [M4]; norm_num)
  have r31 : rmax 4 31 = 3 := R 31 3 4 rfl (by rw [M3]; norm_num) (by rw [M4]; norm_num)
  -- sums over Icc 1 k
  have Ssucc : ∀ (g : ℕ → ℚ) (k k' : ℕ), k + 1 = k' →
      ∑ h ∈ Finset.Icc 1 k', g h = ∑ h ∈ Finset.Icc 1 k, g h + g k' := by
    intro g k k' hk
    subst hk
    exact Finset.sum_Icc_succ_top (Nat.le_add_left 1 k) g
  have S0 : ∀ g : ℕ → ℚ, ∑ h ∈ Finset.Icc 1 0, g h = 0 := by
    intro g
    simp
  -- A005377(29), A005377(30), A005377(31)
  have A29 : A005377 29 = 44 := by
    rw [A005377, r29, M2, Ssucc _ 1 2 rfl, Ssucc _ 0 1 rfl, S0, N1, N2]
    norm_num
  have A30 : A005377 30 = 46 := by
    rw [A005377, r30, M3, Ssucc _ 2 3 rfl, Ssucc _ 1 2 rfl, Ssucc _ 0 1 rfl, S0, N1, N2, N3]
    norm_num
  have A31 : A005377 31 = 49 := by
    rw [A005377, r31, M3, Ssucc _ 2 3 rfl, Ssucc _ 1 2 rfl, Ssucc _ 0 1 rfl, S0, N1, N2, N3]
    norm_num
  -- the coefficient of X^30
  intro h
  have eL : PowerSeries.mk (fun n => A005377 (n + 1)) *
      (1 - 2 * PowerSeries.X + PowerSeries.X ^ 2) =
      PowerSeries.mk (fun n => A005377 (n + 1)) -
        (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2 *
          (PowerSeries.mk (fun n => A005377 (n + 1)) * PowerSeries.X ^ 1) +
        PowerSeries.mk (fun n => A005377 (n + 1)) * PowerSeries.X ^ 2 := by
    rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2]
    ring
  rw [eL] at h
  have h30 := congrArg (fun p : PowerSeries ℚ => PowerSeries.coeff 30 p) h
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow',
    PowerSeries.coeff_mk, PowerSeries.coeff_X_pow] at h30
  norm_num [A29, A30, A31] at h30
