import OMAStatements.S_oeis_a345013

namespace OMA.P_oeis_a345013

open OMA.S_oeis_a345013

/-! ### Part 1: Exact simplification `T345013 (m + 1) k = C(m, k) * C(2m + 2 - k, m)` -/

private lemma T345013_eq (m k : ℕ) (hk : k ≤ m) :
    T345013 (m + 1) k = Nat.choose m k * Nat.choose (2 * (m + 1) - k) m := by
  unfold T345013
  rw [Nat.add_sub_cancel]
  have h1 : (m + 1 - k) * Nat.choose (m + 1) k = (m + 1) * Nat.choose m k := by
    have hc1 := Nat.choose_mul_factorial_mul_factorial (show k ≤ m + 1 by omega)
    have hc2 := Nat.choose_mul_factorial_mul_factorial hk
    have hf1 : (m + 1).factorial = (m + 1) * m.factorial := Nat.factorial_succ m
    have hf2 : (m + 1 - k).factorial = (m + 1 - k) * (m - k).factorial := by
      rw [show m + 1 - k = (m - k) + 1 by omega, Nat.factorial_succ]
    have hpos : 0 < k.factorial * (m - k).factorial := by positivity
    apply Nat.eq_of_mul_eq_mul_right hpos
    calc
      (m + 1 - k) * Nat.choose (m + 1) k * (k.factorial * (m - k).factorial)
        = Nat.choose (m + 1) k * k.factorial * (m + 1 - k).factorial := by rw [hf2]; ring
      _ = (m + 1).factorial := hc1
      _ = (m + 1) * m.factorial := hf1
      _ = (m + 1) * (Nat.choose m k * k.factorial * (m - k).factorial) := by rw [hc2]
      _ = (m + 1) * Nat.choose m k * (k.factorial * (m - k).factorial) := by ring
  rw [h1, mul_assoc, Nat.mul_div_cancel_left _ (Nat.succ_pos m)]

/-! ### Part 2: Polynomial identity `(1 + t)^(m + 2) * (t + x)^m` -> Identity 1 -/

private lemma coeff_one_add_X_pow (a b : ℕ) :
    ((1 + Polynomial.X : Polynomial ℤ) ^ a).coeff b = (Nat.choose a b : ℤ) := by
  have hbin : (1 + Polynomial.X : Polynomial ℤ) ^ a =
      ∑ j ∈ Finset.range (a + 1), Polynomial.C (Nat.choose a j : ℤ) * Polynomial.X ^ j := by
    rw [add_comm, add_pow]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [one_pow, mul_one, map_natCast, mul_comm]
  rw [hbin, Polynomial.finsetSum_coeff]
  by_cases hba : b ≤ a
  · rw [Finset.sum_eq_single b]
    · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_self, mul_one]
    · intro j _ hne
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg hne.symm, mul_zero]
    · intro h; exfalso; exact h (Finset.mem_range.mpr (by omega))
  · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]
    refine Finset.sum_eq_zero (fun j hj => ?_)
    have hjle : j ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (by omega), mul_zero]

private lemma poly_coeff_mul_eq_sum_range (f g : Polynomial ℤ) (n : ℕ) :
    (f * g).coeff n = ∑ i ∈ Finset.range (n + 1), f.coeff i * g.coeff (n - i) := by
  rw [Polynomial.coeff_mul]
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => f.coeff i * g.coeff j) n

private lemma identity1_succ (m : ℕ) (x : ℤ) :
    (∑ k ∈ Finset.range (m + 1), (T345013 (m + 1) k : ℤ) * (x - 1) ^ k) =
      ∑ k ∈ Finset.range (m + 1), (A062196 m k : ℤ) * x ^ k := by
  -- Evaluate coeff m of (1 + X)^(m + 2) * (X + C x)^m in two ways!
  have hway1 :
      (((1 + Polynomial.X : Polynomial ℤ) ^ (m + 2) * (Polynomial.X + Polynomial.C x) ^ m).coeff m) =
        ∑ k ∈ Finset.range (m + 1), (A062196 m k : ℤ) * x ^ k := by
    rw [poly_coeff_mul_eq_sum_range]
    have hX : ∀ r : ℕ, ((Polynomial.X + Polynomial.C x : Polynomial ℤ) ^ m).coeff r =
        if r ≤ m then (Nat.choose m r : ℤ) * x ^ (m - r) else 0 := by
      intro r
      rw [add_pow, Polynomial.finsetSum_coeff]
      by_cases hrm : r ≤ m
      · rw [if_pos hrm, Finset.sum_eq_single r]
        · rw [← map_pow, ← map_natCast Polynomial.C,
            show Polynomial.X ^ r * Polynomial.C (x ^ (m - r)) * Polynomial.C (Nat.choose m r : ℤ) =
              Polynomial.C ((Nat.choose m r : ℤ) * x ^ (m - r)) * Polynomial.X ^ r by rw [map_mul]; ring,
            Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_self, mul_one]
        · intro j _ hjne
          rw [← map_pow, ← map_natCast Polynomial.C,
            show Polynomial.X ^ j * Polynomial.C (x ^ (m - j)) * Polynomial.C (Nat.choose m j : ℤ) =
              Polynomial.C (x ^ (m - j) * (Nat.choose m j : ℤ)) * Polynomial.X ^ j by rw [map_mul]; ring,
            Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg hjne.symm, mul_zero]
        · intro h; exfalso; exact h (Finset.mem_range.mpr (by omega))
      · rw [if_neg hrm]
        refine Finset.sum_eq_zero (fun j hj => ?_)
        have hjle : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        rw [← map_pow, ← map_natCast Polynomial.C,
          show Polynomial.X ^ j * Polynomial.C (x ^ (m - j)) * Polynomial.C (Nat.choose m j : ℤ) =
            Polynomial.C (x ^ (m - j) * (Nat.choose m j : ℤ)) * Polynomial.X ^ j by rw [map_mul]; ring,
          Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (by omega), mul_zero]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have hkle : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [coeff_one_add_X_pow, hX (m - k), if_pos (by omega), show m - (m - k) = k by omega,
      Nat.choose_symm hkle]
    unfold A062196
    push_cast
    ring
  have hway2 :
      (((1 + Polynomial.X : Polynomial ℤ) ^ (m + 2) * (Polynomial.X + Polynomial.C x) ^ m).coeff m) =
        ∑ k ∈ Finset.range (m + 1), (T345013 (m + 1) k : ℤ) * (x - 1) ^ k := by
    have hsplit : (Polynomial.X + Polynomial.C x : Polynomial ℤ) =
        Polynomial.C (x - 1) + (1 + Polynomial.X) := by
      rw [map_sub, map_one]; ring
    rw [hsplit, add_pow (Polynomial.C (x - 1)) (1 + Polynomial.X) m, Finset.mul_sum, Polynomial.finsetSum_coeff]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have hkle : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hterm : (1 + Polynomial.X : Polynomial ℤ) ^ (m + 2) *
          (Polynomial.C (x - 1) ^ k * (1 + Polynomial.X) ^ (m - k) * (Nat.choose m k : Polynomial ℤ)) =
        Polynomial.C ((Nat.choose m k : ℤ) * (x - 1) ^ k) *
          (1 + Polynomial.X : Polynomial ℤ) ^ (2 * (m + 1) - k) := by
      rw [← map_pow, ← map_natCast Polynomial.C, map_mul]
      calc
        (1 + Polynomial.X : Polynomial ℤ) ^ (m + 2) *
            (Polynomial.C ((x - 1) ^ k) * (1 + Polynomial.X) ^ (m - k) * Polynomial.C (Nat.choose m k : ℤ))
          = Polynomial.C (Nat.choose m k : ℤ) * Polynomial.C ((x - 1) ^ k) *
              ((1 + Polynomial.X : Polynomial ℤ) ^ (m + 2) * (1 + Polynomial.X) ^ (m - k)) := by ring
        _ = Polynomial.C (Nat.choose m k : ℤ) * Polynomial.C ((x - 1) ^ k) *
              (1 + Polynomial.X : Polynomial ℤ) ^ (2 * (m + 1) - k) := by
            rw [← pow_add, show m + 2 + (m - k) = 2 * (m + 1) - k by omega]
    rw [hterm, Polynomial.coeff_C_mul, coeff_one_add_X_pow, T345013_eq m k hkle]
    push_cast
    ring
  rw [← hway2, hway1]

/-! ### Part 3: Specialization `x = -1` -> Identity 2 (`A089849`) -/

private lemma coeff_one_sub_X_sq_pow (m k : ℕ) :
    ((1 - Polynomial.X ^ 2 : Polynomial ℤ) ^ m).coeff k =
      if k % 2 = 0 then (-1 : ℤ) ^ (k / 2) * (Nat.choose m (k / 2) : ℤ) else 0 := by
  have hbin : (1 - Polynomial.X ^ 2 : Polynomial ℤ) ^ m =
      ∑ j ∈ Finset.range (m + 1),
        Polynomial.C ((-1 : ℤ) ^ j * (Nat.choose m j : ℤ)) * Polynomial.X ^ (2 * j) := by
    have h := add_pow (-(Polynomial.X ^ 2) : Polynomial ℤ) 1 m
    have hsub : (1 - Polynomial.X ^ 2 : Polynomial ℤ) = -(Polynomial.X ^ 2) + 1 := by ring
    rw [hsub, h]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [one_pow, mul_one, neg_pow, ← pow_mul, map_mul, map_pow, map_neg, map_one, map_natCast]
    ring
  rw [hbin, Polynomial.finsetSum_coeff]
  by_cases hev : k % 2 = 0
  · rw [if_pos hev]
    by_cases hkm : k / 2 ≤ m
    · rw [Finset.sum_eq_single (k / 2)]
      · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos (by omega), mul_one]
      · intro j _ hne
        rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (by omega), mul_zero]
      · intro h; exfalso; exact h (Finset.mem_range.mpr (by omega))
    · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, mul_zero]
      refine Finset.sum_eq_zero (fun j hj => ?_)
      have hjle : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (by omega), mul_zero]
  · rw [if_neg hev]
    refine Finset.sum_eq_zero (fun j _ => ?_)
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (by omega), mul_zero]

private lemma choose_two_mul_eq (r : ℕ) :
    2 * Nat.choose (2 * r + 1) r = Nat.choose (2 * r + 2) (r + 1) := by
  have h1 := Nat.choose_succ_succ (2 * r + 1) r
  have hsym : Nat.choose (2 * r + 1) (r + 1) = Nat.choose (2 * r + 1) r := by
    rw [← Nat.choose_symm (show r + 1 ≤ 2 * r + 1 by omega), show 2 * r + 1 - (r + 1) = r by omega]
  rw [show 2 * r + 2 = (2 * r + 1) + 1 by omega, h1, hsym]
  omega

private lemma catalan_eq_diff (r : ℕ) (hr : 1 ≤ r) :
    (Nat.choose (2 * r) r : ℤ) - (Nat.choose (2 * r) (r - 1) : ℤ) =
      ((Nat.choose (2 * r) r / (r + 1) : ℕ) : ℤ) := by
  have hdvd : (r + 1) ∣ Nat.choose (2 * r) r := by
    have hmul : (r + 1) * (Nat.choose (2 * r) r - Nat.choose (2 * r) (r - 1)) = Nat.choose (2 * r) r := by
      have h1 : (r + 1) * Nat.choose (2 * r) (r - 1) = r * Nat.choose (2 * r) r := by
        have hc1 := Nat.choose_mul_factorial_mul_factorial (show r ≤ 2 * r by omega)
        have hc2 := Nat.choose_mul_factorial_mul_factorial (show r - 1 ≤ 2 * r by omega)
        rw [show 2 * r - r = r by omega] at hc1
        rw [show 2 * r - (r - 1) = r + 1 by omega] at hc2
        have hf1 : r.factorial = r * (r - 1).factorial := by
          rw [show r = (r - 1) + 1 by omega, Nat.factorial_succ]; simp
        have hf2 : (r + 1).factorial = (r + 1) * r.factorial := Nat.factorial_succ r
        have hpos : 0 < (r - 1).factorial * r.factorial := by positivity
        apply Nat.eq_of_mul_eq_mul_right hpos
        calc
          (r + 1) * Nat.choose (2 * r) (r - 1) * ((r - 1).factorial * r.factorial)
            = Nat.choose (2 * r) (r - 1) * (r - 1).factorial * (r + 1).factorial := by rw [hf2]; ring
          _ = (2 * r).factorial := hc2
          _ = Nat.choose (2 * r) r * r.factorial * r.factorial := hc1.symm
          _ = r * Nat.choose (2 * r) r * ((r - 1).factorial * r.factorial) := by rw [hf1]; ring
      have hle : Nat.choose (2 * r) (r - 1) ≤ Nat.choose (2 * r) r := by
        have : r * Nat.choose (2 * r) (r - 1) ≤ r * Nat.choose (2 * r) r := by nlinarith
        exact Nat.le_of_mul_le_mul_left this (by omega)
      zify [hle] at h1 ⊢
      linarith
    exact ⟨Nat.choose (2 * r) r - Nat.choose (2 * r) (r - 1), hmul.symm⟩
  have hmul_z : ((r + 1 : ℕ) : ℤ) * ((Nat.choose (2 * r) r : ℤ) - (Nat.choose (2 * r) (r - 1) : ℤ)) =
      (Nat.choose (2 * r) r : ℤ) := by
    have h1 : (r + 1) * Nat.choose (2 * r) (r - 1) = r * Nat.choose (2 * r) r := by
      have hc1 := Nat.choose_mul_factorial_mul_factorial (show r ≤ 2 * r by omega)
      have hc2 := Nat.choose_mul_factorial_mul_factorial (show r - 1 ≤ 2 * r by omega)
      rw [show 2 * r - r = r by omega] at hc1
      rw [show 2 * r - (r - 1) = r + 1 by omega] at hc2
      have hf1 : r.factorial = r * (r - 1).factorial := by
        rw [show r = (r - 1) + 1 by omega, Nat.factorial_succ]; simp
      have hf2 : (r + 1).factorial = (r + 1) * r.factorial := Nat.factorial_succ r
      have hpos : 0 < (r - 1).factorial * r.factorial := by positivity
      apply Nat.eq_of_mul_eq_mul_right hpos
      calc
        (r + 1) * Nat.choose (2 * r) (r - 1) * ((r - 1).factorial * r.factorial)
          = Nat.choose (2 * r) (r - 1) * (r - 1).factorial * (r + 1).factorial := by rw [hf2]; ring
        _ = (2 * r).factorial := hc2
        _ = Nat.choose (2 * r) r * r.factorial * r.factorial := hc1.symm
        _ = r * Nat.choose (2 * r) r * ((r - 1).factorial * r.factorial) := by rw [hf1]; ring
    have h1z : ((r + 1 : ℕ) : ℤ) * (Nat.choose (2 * r) (r - 1) : ℤ) =
        (r : ℤ) * (Nat.choose (2 * r) r : ℤ) := by exact_mod_cast h1
    push_cast at h1z ⊢
    linarith
  have hdiv : ((r + 1 : ℕ) : ℤ) * ((Nat.choose (2 * r) r / (r + 1) : ℕ) : ℤ) =
      (Nat.choose (2 * r) r : ℤ) := by
    exact_mod_cast Nat.mul_div_cancel' hdvd
  have hne : ((r + 1 : ℕ) : ℤ) ≠ 0 := by positivity
  exact mul_left_cancel₀ hne (hmul_z.trans hdiv.symm)

private lemma identity2_succ (m : ℕ) :
    (∑ k ∈ Finset.range (m + 1), (T345013 (m + 1) k : ℤ) * (-2 : ℤ) ^ k) =
      (-1 : ℤ) ^ ((m + 1) / 2) * (A089849 (m + 1) : ℤ) := by
  have h1 := identity1_succ m (-1)
  have hm2 : (-1 : ℤ) - 1 = -2 := by norm_num
  rw [hm2] at h1
  rw [h1]
  -- Evaluate coeff m of (1 + X)^(m + 2) * (X - 1)^m in two ways!
  have hpoly_lhs :
      (((1 + Polynomial.X : Polynomial ℤ) ^ (m + 2) * (Polynomial.X + Polynomial.C (-1 : ℤ)) ^ m).coeff m) =
        ∑ k ∈ Finset.range (m + 1), (A062196 m k : ℤ) * (-1 : ℤ) ^ k := by
    -- Reuse the exact same coeff_mul expansion at x = -1!
    have hspec : (∑ k ∈ Finset.range (m + 1), (T345013 (m + 1) k : ℤ) * ((-1 : ℤ) - 1) ^ k) =
        (((1 + Polynomial.X : Polynomial ℤ) ^ (m + 2) * (Polynomial.X + Polynomial.C (-1 : ℤ)) ^ m).coeff m) := by
      have hsplit : (Polynomial.X + Polynomial.C (-1 : ℤ) : Polynomial ℤ) =
          Polynomial.C ((-1 : ℤ) - 1) + (1 + Polynomial.X) := by
        rw [map_sub, map_one]; ring
      rw [hsplit, add_pow (Polynomial.C ((-1 : ℤ) - 1)) (1 + Polynomial.X) m, Finset.mul_sum, Polynomial.finsetSum_coeff]
      refine Finset.sum_congr rfl (fun k hk => ?_)
      have hkle : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have hterm : (1 + Polynomial.X : Polynomial ℤ) ^ (m + 2) *
            (Polynomial.C ((-1 : ℤ) - 1) ^ k * (1 + Polynomial.X) ^ (m - k) * (Nat.choose m k : Polynomial ℤ)) =
          Polynomial.C ((Nat.choose m k : ℤ) * ((-1 : ℤ) - 1) ^ k) *
            (1 + Polynomial.X : Polynomial ℤ) ^ (2 * (m + 1) - k) := by
        rw [← map_pow, ← map_natCast Polynomial.C, map_mul]
        calc
          _ = Polynomial.C (Nat.choose m k : ℤ) * Polynomial.C (((-1 : ℤ) - 1) ^ k) *
                ((1 + Polynomial.X : Polynomial ℤ) ^ (m + 2) * (1 + Polynomial.X) ^ (m - k)) := by ring
          _ = _ := by rw [← pow_add, show m + 2 + (m - k) = 2 * (m + 1) - k by omega]
      rw [hterm, Polynomial.coeff_C_mul, coeff_one_add_X_pow, T345013_eq m k hkle]
      push_cast; ring
    rw [← hspec, hm2, h1]
  rw [← hpoly_lhs]
  have hfac : (1 + Polynomial.X : Polynomial ℤ) ^ (m + 2) * (Polynomial.X + Polynomial.C (-1 : ℤ)) ^ m =
      Polynomial.C ((-1 : ℤ) ^ m) * ((1 + Polynomial.C 2 * Polynomial.X + Polynomial.X ^ 2) *
        (1 - Polynomial.X ^ 2) ^ m) := by
    have hneg : (Polynomial.X + Polynomial.C (-1 : ℤ) : Polynomial ℤ) = -(1 - Polynomial.X) := by
      rw [map_neg, map_one]; ring
    rw [hneg, neg_pow, show m + 2 = 2 + m by omega, pow_add]
    have hmul : (1 + Polynomial.X : Polynomial ℤ) ^ m * (1 - Polynomial.X) ^ m = (1 - Polynomial.X ^ 2) ^ m := by
      rw [← mul_pow]; congr 1; ring
    have hsq : (1 + Polynomial.X : Polynomial ℤ) ^ 2 = 1 + Polynomial.C 2 * Polynomial.X + Polynomial.X ^ 2 := by
      have hc2 : Polynomial.C (2 : ℤ) = 1 + 1 := by rw [← map_one Polynomial.C, ← map_add]; norm_num
      rw [hc2]; ring
    rw [map_pow, map_neg, map_one]
    calc
      (1 + Polynomial.X : Polynomial ℤ) ^ 2 * (1 + Polynomial.X) ^ m * ((-1) ^ m * (1 - Polynomial.X) ^ m)
        = (-1 : Polynomial ℤ) ^ m * ((1 + Polynomial.X) ^ 2 * ((1 + Polynomial.X) ^ m * (1 - Polynomial.X) ^ m)) := by ring
      _ = (-1 : Polynomial ℤ) ^ m * ((1 + Polynomial.C 2 * Polynomial.X + Polynomial.X ^ 2) * (1 - Polynomial.X ^ 2) ^ m) := by
          rw [hmul, hsq]
  rw [hfac, Polynomial.coeff_C_mul]
  have hexp : ((1 + Polynomial.C 2 * Polynomial.X + Polynomial.X ^ 2) * (1 - Polynomial.X ^ 2 : Polynomial ℤ) ^ m) =
      (1 - Polynomial.X ^ 2) ^ m + Polynomial.C 2 * (Polynomial.X * (1 - Polynomial.X ^ 2) ^ m) +
        Polynomial.X ^ 2 * (1 - Polynomial.X ^ 2) ^ m := by ring
  rw [hexp, Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_C_mul]
  rcases Nat.even_or_odd' m with ⟨r, rfl | rfl⟩
  · -- m = 2*r, so m + 1 = 2*r + 1 (odd), (m + 1) / 2 = r
    have hneg2r : (-1 : ℤ) ^ (2 * r) = 1 := by rw [pow_mul]; norm_num
    rw [hneg2r, one_mul, coeff_one_sub_X_sq_pow, if_pos (by omega), show (2 * r) / 2 = r by omega]
    unfold A089849
    rw [if_neg (by omega : ¬ (2 * r + 1) % 2 = 0), show (2 * r + 1) / 2 = r by omega]
    cases r with
    | zero =>
      simp
    | succ r' =>
      have hX1 : (Polynomial.X * (1 - Polynomial.X ^ 2 : Polynomial ℤ) ^ (2 * (r' + 1))).coeff (2 * (r' + 1)) = 0 := by
        rw [show 2 * (r' + 1) = (2 * r' + 1) + 1 by omega, Polynomial.coeff_X_mul,
          coeff_one_sub_X_sq_pow, if_neg (by omega)]
      have hX2 : (Polynomial.X ^ 2 * (1 - Polynomial.X ^ 2 : Polynomial ℤ) ^ (2 * (r' + 1))).coeff (2 * (r' + 1)) =
          (-1 : ℤ) ^ r' * (Nat.choose (2 * (r' + 1)) r' : ℤ) := by
        rw [show 2 * (r' + 1) = 2 * r' + 2 by omega, Polynomial.coeff_X_pow_mul,
          coeff_one_sub_X_sq_pow, if_pos (by omega), show (2 * r') / 2 = r' by omega]
      rw [hX1, mul_zero, add_zero, hX2]
      have hcat := catalan_eq_diff (r' + 1) (by omega)
      rw [Nat.add_sub_cancel] at hcat
      rw [← hcat, pow_succ]
      ring
  · -- m = 2*r + 1, so m + 1 = 2*r + 2 (even), (m + 1) / 2 = r + 1
    have hneg2r1 : (-1 : ℤ) ^ (2 * r + 1) = -1 := by rw [pow_succ, pow_mul]; norm_num
    rw [hneg2r1, coeff_one_sub_X_sq_pow, if_neg (by omega), zero_add]
    have hX1 : (Polynomial.X * (1 - Polynomial.X ^ 2 : Polynomial ℤ) ^ (2 * r + 1)).coeff (2 * r + 1) =
        (-1 : ℤ) ^ r * (Nat.choose (2 * r + 1) r : ℤ) := by
      rw [Polynomial.coeff_X_mul, coeff_one_sub_X_sq_pow, if_pos (by omega), show (2 * r) / 2 = r by omega]
    have hX2 : (Polynomial.X ^ 2 * (1 - Polynomial.X ^ 2 : Polynomial ℤ) ^ (2 * r + 1)).coeff (2 * r + 1) = 0 := by
      cases r with
      | zero =>
        rw [sq, mul_assoc, Polynomial.coeff_X_mul, Polynomial.coeff_X_mul_zero]
      | succ r' =>
        rw [show 2 * (r' + 1) + 1 = (2 * r' + 1) + 2 by omega, Polynomial.coeff_X_pow_mul,
          coeff_one_sub_X_sq_pow, if_neg (by omega)]
    rw [hX1, hX2, add_zero]
    unfold A089849
    rw [if_pos (by omega : (2 * r + 1 + 1) % 2 = 0), show (2 * r + 1 + 1) / 2 = r + 1 by omega,
      show 2 * r + 1 + 1 = 2 * r + 2 by omega, ← choose_two_mul_eq r]
    push_cast
    rw [pow_succ]
    ring

theorem solution :
    (∀ (n : ℕ), 1 ≤ n → ∀ x : ℤ,
      (∑ k ∈ Finset.range n, (T345013 n k : ℤ) * (x - 1) ^ k) =
        ∑ k ∈ Finset.range n, (A062196 (n - 1) k : ℤ) * x ^ k) ∧
    (∀ (n : ℕ), 1 ≤ n →
      (∑ k ∈ Finset.range n, (T345013 n k : ℤ) * (-2 : ℤ) ^ k) =
        (-1 : ℤ) ^ (n / 2) * (A089849 n : ℤ)) := by
  constructor
  · intro n hn x
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    exact identity1_succ m x
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact identity2_succ m

end OMA.P_oeis_a345013

theorem OMA.solution : type_of% @OMA.S_oeis_a345013.main :=
  OMA.P_oeis_a345013.solution
