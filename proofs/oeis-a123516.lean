import OMAStatements.S_oeis_a123516

namespace OMA.P_oeis_a123516

open OMA.S_oeis_a123516

/-! ### Part 1: Three-term recurrence for `P(n, x)` from `T(n, k)` -/

private lemma T_zero_zero : T 0 0 = 1 := by
  simp [T]

private lemma T_one_zero : T 1 0 = 2 := by
  simp [T]

private lemma T_one_one : T 1 1 = -1 := by
  unfold T
  norm_num [Nat.choose]

private lemma T_gt (n k : ℕ) (h : n < k) : T n k = 0 := by
  unfold T
  rw [Nat.choose_eq_zero_of_lt h]
  simp

private lemma T_rec_zero (n : ℕ) :
    T (n + 2) 0 =
      2 * (2 * ((n + 2 : ℕ) : ℝ) - 1) * T (n + 1) 0 -
        4 * ((n + 1 : ℕ) : ℝ) ^ 2 * T n 0 := by
  unfold T
  simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, mul_one, one_mul, Nat.cast_zero,
    mul_zero, sub_zero, zpow_natCast]
  rw [Nat.factorial_succ (n + 1), Nat.factorial_succ n]
  push_cast
  have h1 : (2 : ℝ) ^ (n + 2) = 4 * (2 : ℝ) ^ n := by rw [pow_succ, pow_succ]; ring
  have h2 : (2 : ℝ) ^ (n + 1) = 2 * (2 : ℝ) ^ n := by rw [pow_succ]; ring
  rw [h1, h2]
  ring

private lemma T_rec_succ (n k : ℕ) :
    T (n + 2) (k + 1) =
      2 * (2 * ((n + 2 : ℕ) : ℝ) - 1) * T (n + 1) (k + 1) -
        (2 * ((n + 2 : ℕ) : ℝ) - 1) * T (n + 1) k +
        4 * ((n + 1 : ℕ) : ℝ) ^ 2 * T n k -
        4 * ((n + 1 : ℕ) : ℝ) ^ 2 * T n (k + 1) := by
  by_cases hk : n + 2 < k + 1
  · rw [T_gt (n + 2) (k + 1) hk, T_gt (n + 1) (k + 1) (by omega),
      T_gt (n + 1) k (by omega), T_gt n k (by omega), T_gt n (k + 1) (by omega)]
    ring
  · have hkle : k + 1 ≤ n + 2 := by omega
    -- Clear factorials using exact binomial-factorial identities
    have hC2 : (k + 1) * Nat.choose (2 * (k + 1)) (k + 1) =
        2 * (2 * k + 1) * Nat.choose (2 * k) k := by
      have h1 := Nat.choose_mul_factorial_mul_factorial (show k + 1 ≤ 2 * (k + 1) by omega)
      have h2 := Nat.choose_mul_factorial_mul_factorial (show k ≤ 2 * k by omega)
      rw [show 2 * (k + 1) - (k + 1) = k + 1 by omega] at h1
      rw [show 2 * k - k = k by omega] at h2
      have hf1 : (2 * (k + 1)).factorial = (2 * k + 2) * ((2 * k + 1) * (2 * k).factorial) := by
        rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega, Nat.factorial_succ, Nat.factorial_succ]
      have hf2 : (k + 1).factorial = (k + 1) * k.factorial := Nat.factorial_succ k
      have hpos : 0 < (k + 1).factorial * k.factorial := by positivity
      apply Nat.eq_of_mul_eq_mul_right hpos
      calc
        (k + 1) * Nat.choose (2 * (k + 1)) (k + 1) * ((k + 1).factorial * k.factorial)
          = Nat.choose (2 * (k + 1)) (k + 1) * (k + 1).factorial * (k + 1).factorial := by
              rw [hf2]; ring
        _ = (2 * (k + 1)).factorial := h1
        _ = (2 * k + 2) * ((2 * k + 1) * (2 * k).factorial) := hf1
        _ = (2 * k + 2) * ((2 * k + 1) * (Nat.choose (2 * k) k * k.factorial * k.factorial)) := by
              rw [← h2]
        _ = 2 * (2 * k + 1) * Nat.choose (2 * k) k * ((k + 1).factorial * k.factorial) := by
              rw [hf2]; ring
    have hC2r : ((k + 1 : ℕ) : ℝ) * (Nat.choose (2 * (k + 1)) (k + 1) : ℝ) =
        2 * (2 * (k : ℝ) + 1) * (Nat.choose (2 * k) k : ℝ) := by
      exact_mod_cast hC2
    -- Express every term in terms of A = (-1)^k * n! * 2^(n - 2k) * C(2k, k)
    -- and binomials C(n+2, k+1), C(n+1, k+1), C(n+1, k), C(n, k), C(n, k+1)!
    have hB1 : (k + 1) * Nat.choose (n + 2) (k + 1) = (n + 2) * Nat.choose (n + 1) k := by
      rw [mul_comm]; exact (Nat.add_one_mul_choose_eq (n + 1) k).symm
    have hB2 : (n + 2) * Nat.choose (n + 1) (k + 1) = (n + 1 - k) * Nat.choose (n + 2) (k + 1) := by
      by_cases h1 : k + 1 ≤ n + 1
      · have hc1 := Nat.choose_mul_factorial_mul_factorial hkle
        have hc2 := Nat.choose_mul_factorial_mul_factorial h1
        rw [show n + 2 - (k + 1) = (n + 1 - k) by omega] at hc1
        rw [show n + 1 - (k + 1) = n - k by omega] at hc2
        have hf1 : (n + 2).factorial = (n + 2) * (n + 1).factorial := Nat.factorial_succ (n + 1)
        have hf2 : (n + 1 - k).factorial = (n + 1 - k) * (n - k).factorial := by
          rw [show n + 1 - k = (n - k) + 1 by omega, Nat.factorial_succ]
        have hpos : 0 < (k + 1).factorial * (n - k).factorial := by positivity
        apply Nat.eq_of_mul_eq_mul_right hpos
        calc
          (n + 2) * Nat.choose (n + 1) (k + 1) * ((k + 1).factorial * (n - k).factorial)
            = (n + 2) * (Nat.choose (n + 1) (k + 1) * (k + 1).factorial * (n - k).factorial) := by ring
          _ = (n + 2) * (n + 1).factorial := by rw [hc2]
          _ = (n + 2).factorial := hf1.symm
          _ = Nat.choose (n + 2) (k + 1) * (k + 1).factorial * (n + 1 - k).factorial := hc1.symm
          _ = (n + 1 - k) * Nat.choose (n + 2) (k + 1) * ((k + 1).factorial * (n - k).factorial) := by
                rw [hf2]; ring
      · have hkeq : k = n + 1 := by omega
        subst hkeq
        simp
    have hB3 : (n + 1) * Nat.choose n k = (n + 1 - k) * Nat.choose (n + 1) k := by
      by_cases h1 : k ≤ n
      · have hc1 := Nat.choose_mul_factorial_mul_factorial (show k ≤ n + 1 by omega)
        have hc2 := Nat.choose_mul_factorial_mul_factorial h1
        have hf1 : (n + 1).factorial = (n + 1) * n.factorial := Nat.factorial_succ n
        have hf2 : (n + 1 - k).factorial = (n + 1 - k) * (n - k).factorial := by
          rw [show n + 1 - k = (n - k) + 1 by omega, Nat.factorial_succ]
        have hpos : 0 < k.factorial * (n - k).factorial := by positivity
        apply Nat.eq_of_mul_eq_mul_right hpos
        calc
          (n + 1) * Nat.choose n k * (k.factorial * (n - k).factorial)
            = (n + 1) * (Nat.choose n k * k.factorial * (n - k).factorial) := by ring
          _ = (n + 1) * n.factorial := by rw [hc2]
          _ = (n + 1).factorial := hf1.symm
          _ = Nat.choose (n + 1) k * k.factorial * (n + 1 - k).factorial := hc1.symm
          _ = (n + 1 - k) * Nat.choose (n + 1) k * (k.factorial * (n - k).factorial) := by
                rw [hf2]; ring
      · have hkeq : k = n + 1 := by omega
        subst hkeq
        simp
    have hB4 : (n + 1) * Nat.choose n (k + 1) = (n - k) * Nat.choose (n + 1) (k + 1) := by
      by_cases h1 : k + 1 ≤ n
      · have hc1 := Nat.choose_mul_factorial_mul_factorial (show k + 1 ≤ n + 1 by omega)
        have hc2 := Nat.choose_mul_factorial_mul_factorial h1
        rw [show n + 1 - (k + 1) = n - k by omega] at hc1
        have hf1 : (n + 1).factorial = (n + 1) * n.factorial := Nat.factorial_succ n
        have hf2 : (n - k).factorial = (n - k) * (n - (k + 1)).factorial := by
          rw [show n - k = (n - (k + 1)) + 1 by omega, Nat.factorial_succ]
        have hpos : 0 < (k + 1).factorial * (n - (k + 1)).factorial := by positivity
        apply Nat.eq_of_mul_eq_mul_right hpos
        calc
          (n + 1) * Nat.choose n (k + 1) * ((k + 1).factorial * (n - (k + 1)).factorial)
            = (n + 1) * (Nat.choose n (k + 1) * (k + 1).factorial * (n - (k + 1)).factorial) := by ring
          _ = (n + 1) * n.factorial := by rw [hc2]
          _ = (n + 1).factorial := hf1.symm
          _ = Nat.choose (n + 1) (k + 1) * (k + 1).factorial * (n - k).factorial := hc1.symm
          _ = (n - k) * Nat.choose (n + 1) (k + 1) * ((k + 1).factorial * (n - (k + 1)).factorial) := by
                rw [hf2]; ring
      · by_cases h2 : k = n
        · rw [h2]; simp
        · have hkeq : k = n + 1 := by omega
          rw [hkeq]
          simp [Nat.choose_eq_zero_of_lt (by omega : n < n + 2)]
    -- Cast hB1..hB4 to ℝ
    have hB1r : ((k + 1 : ℕ) : ℝ) * (Nat.choose (n + 2) (k + 1) : ℝ) =
        ((n + 2 : ℕ) : ℝ) * (Nat.choose (n + 1) k : ℝ) := by exact_mod_cast hB1
    have hB2r : ((n + 2 : ℕ) : ℝ) * (Nat.choose (n + 1) (k + 1) : ℝ) =
        ((n + 1 : ℕ) - (k : ℝ)) * (Nat.choose (n + 2) (k + 1) : ℝ) := by
      have h : ((n + 2 : ℕ) : ℝ) * (Nat.choose (n + 1) (k + 1) : ℝ) =
          ((n + 1 - k : ℕ) : ℝ) * (Nat.choose (n + 2) (k + 1) : ℝ) := by exact_mod_cast hB2
      rw [Nat.cast_sub (by omega : k ≤ n + 1)] at h
      exact h
    have hB3r : ((n + 1 : ℕ) : ℝ) * (Nat.choose n k : ℝ) =
        ((n + 1 : ℕ) - (k : ℝ)) * (Nat.choose (n + 1) k : ℝ) := by
      have h : ((n + 1 : ℕ) : ℝ) * (Nat.choose n k : ℝ) =
          ((n + 1 - k : ℕ) : ℝ) * (Nat.choose (n + 1) k : ℝ) := by exact_mod_cast hB3
      rw [Nat.cast_sub (by omega : k ≤ n + 1)] at h
      exact h
    have hB4r : ((n + 1 : ℕ) : ℝ) * (Nat.choose n (k + 1) : ℝ) =
        ((n : ℝ) - (k : ℝ)) * (Nat.choose (n + 1) (k + 1) : ℝ) := by
      by_cases hkn : k ≤ n
      · have h : ((n + 1 : ℕ) : ℝ) * (Nat.choose n (k + 1) : ℝ) =
            ((n - k : ℕ) : ℝ) * (Nat.choose (n + 1) (k + 1) : ℝ) := by exact_mod_cast hB4
        rw [Nat.cast_sub hkn] at h
        exact h
      · have hkeq : k = n + 1 := by omega
        rw [hkeq]
        simp [Nat.choose_eq_zero_of_lt (by omega : n < n + 2)]
    -- Unfold T and normalize powers of 2, (-1), and factorials
    unfold T
    set z0 : ℤ := (n : ℤ) - 2 * (k : ℤ)
    have hz1 : ((n + 2 : ℕ) : ℤ) - 2 * ((k + 1 : ℕ) : ℤ) = z0 := by omega
    have hz2 : ((n + 1 : ℕ) : ℤ) - 2 * ((k + 1 : ℕ) : ℤ) = z0 - 1 := by omega
    have hz3 : ((n + 1 : ℕ) : ℤ) - 2 * (k : ℤ) = z0 + 1 := by omega
    have hz4 : (n : ℤ) - 2 * ((k + 1 : ℕ) : ℤ) = z0 - 2 := by omega
    rw [hz1, hz2, hz3, hz4]
    have hp_m1 : (2 : ℝ) ^ (z0 - 1) = (2 : ℝ) ^ z0 / 2 := by
      rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]
    have hp_p1 : (2 : ℝ) ^ (z0 + 1) = 2 * (2 : ℝ) ^ z0 := by
      rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]; ring
    have hp_m2 : (2 : ℝ) ^ (z0 - 2) = (2 : ℝ) ^ z0 / 4 := by
      rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]; norm_num
    rw [hp_m1, hp_p1, hp_m2]
    rw [pow_succ (-1 : ℝ) k, Nat.factorial_succ (n + 1), Nat.factorial_succ n]
    -- Multiply by (k+1) * (n+2) * (n+1) ≠ 0 or factor directly via linear_combination!
    have hne_k1 : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    have hne_n1 : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    have hne_n2 : ((n + 2 : ℕ) : ℝ) ≠ 0 := by positivity
    -- Express C(n+2, k+1), C(n+1, k+1), C(n, k), C(n, k+1) in terms of C(n+1, k), and C(2k+2, k+1) in terms of C(2k, k)!
    have hch1 : (Nat.choose (n + 2) (k + 1) : ℝ) =
        ((n + 2 : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ) * (Nat.choose (n + 1) k : ℝ) := by
      rw [div_mul_eq_mul_div, eq_div_iff hne_k1]; linarith
    have hch2 : (Nat.choose (n + 1) (k + 1) : ℝ) =
        ((n + 1 : ℕ) - (k : ℝ)) / ((k + 1 : ℕ) : ℝ) * (Nat.choose (n + 1) k : ℝ) := by
      have := hB2r
      rw [hch1] at this
      have hmul : ((n + 2 : ℕ) : ℝ) * (Nat.choose (n + 1) (k + 1) : ℝ) =
          ((n + 2 : ℕ) : ℝ) * (((n + 1 : ℕ) - (k : ℝ)) / ((k + 1 : ℕ) : ℝ) * (Nat.choose (n + 1) k : ℝ)) := by
        field_simp [hne_k1] at this ⊢; linarith
      exact mul_left_cancel₀ hne_n2 hmul
    have hch3 : (Nat.choose n k : ℝ) =
        ((n + 1 : ℕ) - (k : ℝ)) / ((n + 1 : ℕ) : ℝ) * (Nat.choose (n + 1) k : ℝ) := by
      rw [div_mul_eq_mul_div, eq_div_iff hne_n1]; linarith
    have hch4 : (Nat.choose n (k + 1) : ℝ) =
        ((n : ℝ) - (k : ℝ)) * ((n + 1 : ℕ) - (k : ℝ)) / (((n + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ)) *
          (Nat.choose (n + 1) k : ℝ) := by
      have := hB4r
      rw [hch2] at this
      field_simp [hne_n1, hne_k1] at this ⊢
      linarith
    have hch2k : (Nat.choose (2 * (k + 1)) (k + 1) : ℝ) =
        2 * (2 * (k : ℝ) + 1) / ((k + 1 : ℕ) : ℝ) * (Nat.choose (2 * k) k : ℝ) := by
      rw [div_mul_eq_mul_div, eq_div_iff hne_k1]; linarith
    rw [hch1, hch2, hch3, hch4, hch2k]
    push_cast
    field_simp [hne_k1, hne_n1, hne_n2]
    ring

private lemma P_zero : P 0 = 1 := by
  simp [P, T_zero_zero]

private lemma P_one : P 1 = Polynomial.C 2 * Polynomial.X - 1 := by
  unfold P
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  simp only [Nat.sub_zero, Nat.sub_self, pow_one, pow_zero, mul_one, T_one_zero, T_one_one, map_neg,
    map_one]
  ring

private lemma P_rec (n : ℕ) :
    P (n + 2) =
      Polynomial.C (2 * ((n + 2 : ℕ) : ℝ) - 1) * (Polynomial.C 2 * Polynomial.X - 1) * P (n + 1) +
        Polynomial.C (4 * ((n + 1 : ℕ) : ℝ) ^ 2) * Polynomial.X * (1 - Polynomial.X) * P n := by
  ext m
  have hPcoeff : ∀ (r j : ℕ), (P r).coeff j = if j ≤ r then T r (r - j) else 0 := by
    intro r j
    unfold P
    rw [Polynomial.finsetSum_coeff]
    by_cases hj : j ≤ r
    · rw [if_pos hj, Finset.sum_eq_single (r - j)]
      · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos (by omega), mul_one]
      · intro k hk hkne
        have hkle : k ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (by omega), mul_zero]
      · intro h; exfalso; exact h (Finset.mem_range.mpr (by omega))
    · rw [if_neg hj]
      refine Finset.sum_eq_zero (fun k hk => ?_)
      have hkle : k ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (by omega), mul_zero]
  have hrhs :
      Polynomial.C (2 * ((n + 2 : ℕ) : ℝ) - 1) * (Polynomial.C 2 * Polynomial.X - 1) * P (n + 1) +
        Polynomial.C (4 * ((n + 1 : ℕ) : ℝ) ^ 2) * Polynomial.X * (1 - Polynomial.X) * P n =
      Polynomial.C (2 * (2 * ((n + 2 : ℕ) : ℝ) - 1)) * (Polynomial.X * P (n + 1)) -
        Polynomial.C (2 * ((n + 2 : ℕ) : ℝ) - 1) * P (n + 1) +
        Polynomial.C (4 * ((n + 1 : ℕ) : ℝ) ^ 2) * (Polynomial.X * P n) -
        Polynomial.C (4 * ((n + 1 : ℕ) : ℝ) ^ 2) * (Polynomial.X ^ 2 * P n) := by
    have hc : Polynomial.C (2 * (2 * ((n + 2 : ℕ) : ℝ) - 1)) =
        Polynomial.C 2 * Polynomial.C (2 * ((n + 2 : ℕ) : ℝ) - 1) := by rw [← map_mul]
    rw [hc]
    ring
  rw [hrhs]
  simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul]
  have hXm : ∀ (f : Polynomial ℝ) (j : ℕ), (Polynomial.X * f).coeff j = if j = 0 then 0 else f.coeff (j - 1) := by
    intro f j
    cases j with
    | zero => simp
    | succ j' => simp [Polynomial.coeff_X_mul]
  have hX2m : ∀ (f : Polynomial ℝ) (j : ℕ),
      (Polynomial.X ^ 2 * f).coeff j = if j ≤ 1 then 0 else f.coeff (j - 2) := by
    intro f j
    cases j with
    | zero => rw [sq, mul_assoc, Polynomial.coeff_X_mul_zero]; simp
    | succ j' =>
      cases j' with
      | zero => rw [sq, mul_assoc, Polynomial.coeff_X_mul, Polynomial.coeff_X_mul_zero]; simp
      | succ r => rw [sq, mul_assoc, Polynomial.coeff_X_mul, Polynomial.coeff_X_mul]; simp
  rw [hXm, hXm, hX2m, hPcoeff, hPcoeff, hPcoeff, hPcoeff, hPcoeff]
  by_cases hm : m ≤ n + 2
  · rw [if_pos hm]
    by_cases htop : m = n + 2
    · subst htop
      simp only [Nat.sub_self, show n + 2 ≠ 0 by omega, ite_false, show n + 2 - 1 = n + 1 by omega,
        le_rfl, ite_true, show ¬ n + 2 ≤ n + 1 by omega, show ¬ n + 2 ≤ 1 by omega,
        show n + 2 - 2 = n by omega, show ¬ n + 1 ≤ n by omega]
      rw [T_rec_zero n]
      ring
    · obtain ⟨k, hk⟩ : ∃ k, n + 2 - m = k + 1 := ⟨n + 1 - m, by omega⟩
      rw [hk]
      have hrec := T_rec_succ n k
      -- Check all boundary cases uniformly using T_gt when index > degree!
      have h1 : (if m = 0 then 0 else if m - 1 ≤ n + 1 then T (n + 1) (n + 1 - (m - 1)) else 0) =
          T (n + 1) (k + 1) := by
        by_cases hm0 : m = 0
        · subst hm0
          rw [if_pos rfl, T_gt (n + 1) (k + 1) (by omega)]
        · rw [if_neg hm0, if_pos (by omega), show n + 1 - (m - 1) = k + 1 by omega]
      have h2 : (if m ≤ n + 1 then T (n + 1) (n + 1 - m) else 0) = T (n + 1) k := by
        rw [if_pos (by omega), show n + 1 - m = k by omega]
      have h3 : (if m = 0 then 0 else if m - 1 ≤ n then T n (n - (m - 1)) else 0) = T n k := by
        by_cases hm0 : m = 0
        · subst hm0
          rw [if_pos rfl, T_gt n k (by omega)]
        · rw [if_neg hm0, if_pos (by omega), show n - (m - 1) = k by omega]
      have h4 : (if m ≤ 1 then 0 else if m - 2 ≤ n then T n (n - (m - 2)) else 0) = T n (k + 1) := by
        by_cases hm1 : m ≤ 1
        · rw [if_pos hm1, T_gt n (k + 1) (by omega)]
        · rw [if_neg hm1, if_pos (by omega), show n - (m - 2) = k + 1 by omega]
      rw [h1, h2, h3, h4, hrec]
  · rw [if_neg hm]
    simp only [show m ≠ 0 by omega, show ¬ m - 1 ≤ n + 1 by omega, show ¬ m ≤ n + 1 by omega,
      show ¬ m - 1 ≤ n by omega, show ¬ m ≤ 1 by omega, show ¬ m - 2 ≤ n by omega, ite_false]
    ring

/-! ### Part 2: Link between `P(n, 1/2 + x)` and `pPoly n (x^2)` -/

private lemma P_eval_shift (n : ℕ) :
    ∀ x : ℝ, (P n).eval (1 / 2 + x) =
      if Even n then (pPoly n).eval (x ^ 2) else x * (pPoly n).eval (x ^ 2) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro x
    match n with
    | 0 =>
      simp [P_zero, pPoly]
    | 1 =>
      simp only [P_one, pPoly, Nat.not_even_one, ite_false, Polynomial.eval_sub,
        Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one]
      ring
    | n + 2 =>
      rw [P_rec n]
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
        Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one]
      rw [ih (n + 1) (by omega) x, ih n (by omega) x]
      by_cases hev : Even (n + 2)
      · have hev0 : Even n := by rcases hev with ⟨k, hk⟩; exact ⟨k - 1, by omega⟩
        have hodd1 : ¬ Even (n + 1) := by
          intro h; rcases hev0 with ⟨k, rfl⟩; rcases h with ⟨j, hj⟩; omega
        rw [if_pos hev, if_neg hodd1, if_pos hev0]
        conv_rhs => unfold pPoly
        rw [if_pos hev]
        simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
          Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one]
        ring
      · have hodd0 : ¬ Even n := by
          intro h; apply hev; rcases h with ⟨k, rfl⟩; exact ⟨k + 1, by omega⟩
        have hev1 : Even (n + 1) := by
          rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
          · exfalso; exact hodd0 ⟨k, by omega⟩
          · exact ⟨k + 1, by omega⟩
        rw [if_neg hev, if_pos hev1, if_neg hodd0]
        conv_rhs => unfold pPoly
        rw [if_neg hev]
        simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
          Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one]
        ring

private lemma PComplex_eval_shift (n : ℕ) (z : ℂ) :
    (PComplex n).eval (1 / 2 + z) =
      if Even n then ((pPoly n).map (algebraMap ℝ ℂ)).eval (z ^ 2)
      else z * ((pPoly n).map (algebraMap ℝ ℂ)).eval (z ^ 2) := by
  have hpoly :
      (P n).comp (Polynomial.C (1 / 2 : ℝ) + Polynomial.X) =
        if Even n then (pPoly n).comp (Polynomial.X ^ 2)
        else Polynomial.X * (pPoly n).comp (Polynomial.X ^ 2) := by
    apply Polynomial.funext
    intro x
    rw [Polynomial.eval_comp]
    simp only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X]
    rw [P_eval_shift n x]
    split_ifs <;> simp [Polynomial.eval_comp]
  have hmap := congr_arg (Polynomial.map (algebraMap ℝ ℂ)) hpoly
  have hev := congr_arg (fun q => q.eval z) hmap
  simp only [Polynomial.map_comp, Polynomial.map_add, Polynomial.map_C, Polynomial.map_X,
    Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X] at hev
  have hhalf : (algebraMap ℝ ℂ) (1 / 2 : ℝ) = (1 / 2 : ℂ) := by
    simp
  unfold PComplex
  rw [hhalf] at hev
  split_ifs at hev ⊢ <;> simpa [Polynomial.map_comp, Polynomial.eval_comp] using hev

/-! ### Part 3: Degree, leading coefficient, and evaluation at `0` of `pPoly n` -/

private lemma pPoly_two : pPoly 2 = Polynomial.C 8 * Polynomial.X + 1 := by
  apply Polynomial.funext; intro x
  unfold pPoly; rw [if_pos (by decide : Even 2)]; unfold pPoly
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one]
  norm_num; ring

private lemma pPoly_three : pPoly 3 = Polynomial.C 48 * Polynomial.X + Polynomial.C 18 := by
  apply Polynomial.funext; intro x
  conv_lhs => unfold pPoly
  rw [if_neg (by decide : ¬ Even 3), pPoly_two]
  unfold pPoly
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one]
  norm_num; ring

private lemma pPoly_deg_and_lead (n : ℕ) :
    (pPoly n).natDegree = n / 2 ∧ (pPoly n).leadingCoeff = (n.factorial : ℝ) * (2 : ℝ) ^ n := by
  have hcomp : ∀ k : ℕ,
      (P k).comp (Polynomial.C (1 / 2 : ℝ) + Polynomial.X) =
        if Even k then (pPoly k).comp (Polynomial.X ^ 2)
        else Polynomial.X * (pPoly k).comp (Polynomial.X ^ 2) := by
    intro k
    apply Polynomial.funext
    intro x
    rw [Polynomial.eval_comp]
    simp only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X]
    rw [P_eval_shift k x]
    split_ifs <;> simp [Polynomial.eval_comp]
  have hP_deg_lead : (P n).natDegree = n ∧ (P n).leadingCoeff = (n.factorial : ℝ) * (2 : ℝ) ^ n := by
    have hcoeff : ∀ j : ℕ, (P n).coeff j = if j ≤ n then T n (n - j) else 0 := by
      intro j
      unfold P
      rw [Polynomial.finsetSum_coeff]
      by_cases hj : j ≤ n
      · rw [if_pos hj, Finset.sum_eq_single (n - j)]
        · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos (by omega), mul_one]
        · intro k hk hkne
          have hkle : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
          rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (by omega), mul_zero]
        · intro h; exfalso; exact h (Finset.mem_range.mpr (by omega))
      · rw [if_neg hj]
        refine Finset.sum_eq_zero (fun k hk => ?_)
        have hkle : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (by omega), mul_zero]
    have hTn0 : T n 0 = (n.factorial : ℝ) * (2 : ℝ) ^ n := by
      unfold T
      simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, mul_one, one_mul, Nat.cast_zero,
        mul_zero, sub_zero, zpow_natCast]
    have hcn : (P n).coeff n = (n.factorial : ℝ) * (2 : ℝ) ^ n := by
      rw [hcoeff n, if_pos le_rfl, Nat.sub_self, hTn0]
    have hne : (P n).coeff n ≠ 0 := by rw [hcn]; positivity
    have hle : (P n).natDegree ≤ n := by
      rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro j hj
      rw [hcoeff j, if_neg (by omega)]
    have hge : n ≤ (P n).natDegree := Polynomial.le_natDegree_of_ne_zero hne
    have hdeg : (P n).natDegree = n := le_antisymm hle hge
    exact ⟨hdeg, by rw [Polynomial.leadingCoeff, hdeg, hcn]⟩
  have hshift_deg : ((P n).comp (Polynomial.C (1 / 2 : ℝ) + Polynomial.X)).natDegree = n := by
    rw [Polynomial.natDegree_comp, hP_deg_lead.1]
    have hlin : (Polynomial.C (1 / 2 : ℝ) + Polynomial.X).natDegree = 1 := by
      rw [add_comm]; exact Polynomial.natDegree_X_add_C _
    rw [hlin, mul_one]
  have hshift_lead : ((P n).comp (Polynomial.C (1 / 2 : ℝ) + Polynomial.X)).leadingCoeff =
      (n.factorial : ℝ) * (2 : ℝ) ^ n := by
    have hlin_deg : (Polynomial.C (1 / 2 : ℝ) + Polynomial.X).natDegree = 1 := by
      rw [add_comm]; exact Polynomial.natDegree_X_add_C _
    have hlin_lead : (Polynomial.C (1 / 2 : ℝ) + Polynomial.X).leadingCoeff = 1 := by
      rw [add_comm]; exact Polynomial.leadingCoeff_X_add_C _
    rw [Polynomial.leadingCoeff_comp (by rw [hlin_deg]; omega), hP_deg_lead.2, hlin_lead, one_pow, mul_one]
  have hp_ne : pPoly n ≠ 0 := by
    intro h0
    have hc := hcomp n
    rw [h0] at hc
    have hzero : (P n).comp (Polynomial.C (1 / 2 : ℝ) + Polynomial.X) = 0 := by
      split_ifs at hc
      · rw [hc]; simp
      · rw [hc]; simp
    rw [hzero, Polynomial.leadingCoeff_zero] at hshift_lead
    have hpos : (0 : ℝ) < (n.factorial : ℝ) * (2 : ℝ) ^ n := by positivity
    linarith
  have hX2_deg : ((Polynomial.X : Polynomial ℝ) ^ 2).natDegree = 2 := Polynomial.natDegree_X_pow 2
  have hX2_lead : ((Polynomial.X : Polynomial ℝ) ^ 2).leadingCoeff = 1 := by
    rw [Polynomial.leadingCoeff_X_pow]
  have hcomp_p_deg : ((pPoly n).comp (Polynomial.X ^ 2)).natDegree = (pPoly n).natDegree * 2 := by
    rw [Polynomial.natDegree_comp, hX2_deg]
  have hcomp_p_lead : ((pPoly n).comp (Polynomial.X ^ 2)).leadingCoeff = (pPoly n).leadingCoeff := by
    rw [Polynomial.leadingCoeff_comp (by rw [hX2_deg]; omega), hX2_lead, one_pow, mul_one]
  have hcomp_p_ne : (pPoly n).comp (Polynomial.X ^ 2) ≠ 0 := by
    intro h0
    rw [h0, Polynomial.leadingCoeff_zero] at hcomp_p_lead
    exact hp_ne (Polynomial.leadingCoeff_eq_zero.mp hcomp_p_lead.symm)
  have hc := hcomp n
  by_cases hev : Even n
  · rw [if_pos hev] at hc
    rw [hc, hcomp_p_deg] at hshift_deg
    rw [hc, hcomp_p_lead] at hshift_lead
    rcases hev with ⟨m, rfl⟩
    exact ⟨by omega, hshift_lead⟩
  · rw [if_neg hev] at hc
    have hdeg_mul : (Polynomial.X * (pPoly n).comp (Polynomial.X ^ 2)).natDegree =
        (pPoly n).natDegree * 2 + 1 := by
      rw [Polynomial.natDegree_mul Polynomial.X_ne_zero hcomp_p_ne, Polynomial.natDegree_X,
        hcomp_p_deg, add_comm]
    have hlead_mul : (Polynomial.X * (pPoly n).comp (Polynomial.X ^ 2)).leadingCoeff =
        (pPoly n).leadingCoeff := by
      rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_X, one_mul, hcomp_p_lead]
    rw [hc, hdeg_mul] at hshift_deg
    rw [hc, hlead_mul] at hshift_lead
    rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
    · exfalso; exact hev ⟨m, by omega⟩
    · exact ⟨by omega, hshift_lead⟩

private lemma pPoly_eval_zero_pos (n : ℕ) : 0 < (pPoly n).eval 0 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 => simp [pPoly]
    | 1 => simp [pPoly]
    | n + 2 =>
      have h1 := ih (n + 1) (by omega)
      have h0 := ih n (by omega)
      unfold pPoly
      split_ifs
      · simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
          Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one]
        have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) ^ 2 := by positivity
        nlinarith
      · simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
          Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one]
        have ha : (0 : ℝ) < 2 * (2 * ((n + 2 : ℕ) : ℝ) - 1) := by
          have : (2 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ n + 2)
          linarith
        have hb : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) ^ 2 := by positivity
        nlinarith

/-! ### Part 4: Factorization and sign structure of real polynomials with `d` distinct roots -/

private lemma poly_eq_C_mul_prod_of_roots (q : Polynomial ℝ) (d : ℕ)
    (hdeg : q.natDegree = d) (hlead : 0 < q.leadingCoeff)
    (r : Fin d → ℝ) (hmono : StrictMono r) (hroot : ∀ i : Fin d, q.eval (r i) = 0) :
    q = Polynomial.C q.leadingCoeff * ∏ i : Fin d, (Polynomial.X - Polynomial.C (r i)) := by
  have hne : q ≠ 0 := by
    intro h0; rw [h0, Polynomial.leadingCoeff_zero] at hlead; linarith
  have hprod_dvd : ∀ s : Finset (Fin d),
      (∏ i ∈ s, (Polynomial.X - Polynomial.C (r i))) ∣ q := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      rw [Finset.prod_insert ha]
      have hdvd_a : (Polynomial.X - Polynomial.C (r a)) ∣ q :=
        Polynomial.dvd_iff_isRoot.mpr (hroot a)
      have hcop : IsCoprime (Polynomial.X - Polynomial.C (r a))
          (∏ i ∈ s, (Polynomial.X - Polynomial.C (r i))) := by
        refine IsCoprime.prod_right (fun i hi => ?_)
        have hne_ai : r a ≠ r i := by
          intro heq
          exact ha (hmono.injective heq ▸ hi)
        refine ⟨Polynomial.C ((r i - r a)⁻¹), Polynomial.C ((r a - r i)⁻¹), ?_⟩
        have h1 : r i - r a ≠ 0 := sub_ne_zero.mpr hne_ai.symm
        have h2 : r a - r i ≠ 0 := sub_ne_zero.mpr hne_ai
        ext k
        cases k with
        | zero =>
          simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul,
            Polynomial.coeff_sub, Polynomial.coeff_X_zero, Polynomial.coeff_C_zero,
            Polynomial.coeff_one_zero]
          field_simp [h1, h2]
          ring
        | succ k' =>
          cases k' with
          | zero =>
            simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_sub,
              Polynomial.coeff_C_succ, Polynomial.coeff_one]
            rw [if_neg (by omega)]
            field_simp [h1, h2]
            ring
          | succ m =>
            simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_sub,
              Polynomial.coeff_X, Polynomial.coeff_C_succ, Polynomial.coeff_one]
            rw [if_neg (by omega), if_neg (by omega)]
            ring
      exact hcop.mul_dvd hdvd_a ih
  obtain ⟨c, hc⟩ := hprod_dvd Finset.univ
  have hmonic : (∏ i : Fin d, (Polynomial.X - Polynomial.C (r i))).Monic :=
    Polynomial.monic_prod_of_monic _ _ (fun i _ => Polynomial.monic_X_sub_C (r i))
  have hdeg_p : (∏ i : Fin d, (Polynomial.X - Polynomial.C (r i))).natDegree = d := by
    rw [Polynomial.natDegree_prod_of_monic _ _ (fun i _ => Polynomial.monic_X_sub_C (r i))]
    simp
  have hc_ne : c ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hc; exact hne hc
  have hc_deg : c.natDegree = 0 := by
    have h1 := congr_arg Polynomial.natDegree hc
    rw [hdeg, Polynomial.natDegree_mul hmonic.ne_zero hc_ne, hdeg_p] at h1
    omega
  have hc_eq : c = Polynomial.C c.leadingCoeff := by
    calc
      c = Polynomial.C (c.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hc_deg
      _ = Polynomial.C c.leadingCoeff := by rw [Polynomial.leadingCoeff, hc_deg]
  have hc_lead : c.leadingCoeff = q.leadingCoeff := by
    have h1 := congr_arg Polynomial.leadingCoeff hc
    rw [Polynomial.leadingCoeff_mul, hmonic.leadingCoeff, one_mul] at h1
    exact h1.symm
  conv_lhs => rw [hc, hc_eq, hc_lead, mul_comm]

private lemma eval_sign_of_roots (q : Polynomial ℝ) (d : ℕ)
    (hdeg : q.natDegree = d) (hlead : 0 < q.leadingCoeff)
    (r : Fin d → ℝ) (hmono : StrictMono r) (hroot : ∀ i : Fin d, q.eval (r i) = 0)
    (u : ℝ) (k : ℕ) (_hk : k ≤ d)
    (hlt : ∀ i : Fin d, i.val < k → r i < u)
    (hgt : ∀ i : Fin d, k ≤ i.val → u < r i) :
    0 < (-1 : ℝ) ^ (d - k) * q.eval u := by
  rw [poly_eq_C_mul_prod_of_roots q d hdeg hlead r hmono hroot]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod, Polynomial.eval_sub,
    Polynomial.eval_X]
  have hprod : (-1 : ℝ) ^ (d - k) * ∏ i : Fin d, (u - r i) =
      ∏ i : Fin d, (if i.val < k then (u - r i) else (r i - u)) := by
    have h1 : ∏ i : Fin d, (if i.val < k then (u - r i) else (r i - u)) =
        ∏ i : Fin d, ((if i.val < k then (1 : ℝ) else (-1 : ℝ)) * (u - r i)) := by
      refine Finset.prod_congr rfl (fun i _ => ?_)
      split_ifs <;> ring
    rw [h1, Finset.prod_mul_distrib]
    congr 1
    have hcard : (Finset.univ.filter (fun i : Fin d => ¬ i.val < k)).card = d - k := by
      have hbij : (Finset.univ.filter (fun i : Fin d => ¬ i.val < k)).card =
          (Finset.Ico k d).card := by
        refine Finset.card_bij (fun i _ => i.val) ?_ ?_ ?_
        · intro i hi
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
          simp only [Finset.mem_Ico]
          exact ⟨by omega, i.isLt⟩
        · intro i1 _ i2 _ h; exact Fin.ext h
        · intro j hj
          simp only [Finset.mem_Ico] at hj
          exact ⟨⟨j, hj.2⟩, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega, rfl⟩
      rw [hbij, Nat.card_Ico]
    have hprod_neg : ∏ i : Fin d, (if i.val < k then (1 : ℝ) else (-1 : ℝ)) = (-1 : ℝ) ^ (d - k) := by
      rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i : Fin d => i.val < k)]
      have hp1 : ∏ i ∈ Finset.univ.filter (fun i : Fin d => i.val < k),
          (if i.val < k then (1 : ℝ) else (-1 : ℝ)) = 1 := by
        refine Finset.prod_eq_one (fun i hi => ?_)
        simp only [Finset.mem_filter] at hi
        rw [if_pos hi.2]
      have hp2 : ∏ i ∈ Finset.univ.filter (fun i : Fin d => ¬ i.val < k),
          (if i.val < k then (1 : ℝ) else (-1 : ℝ)) = (-1 : ℝ) ^ (d - k) := by
        have : ∏ i ∈ Finset.univ.filter (fun i : Fin d => ¬ i.val < k),
            (if i.val < k then (1 : ℝ) else (-1 : ℝ)) =
            ∏ _i ∈ Finset.univ.filter (fun i : Fin d => ¬ i.val < k), (-1 : ℝ) := by
          refine Finset.prod_congr rfl (fun i hi => ?_)
          simp only [Finset.mem_filter] at hi
          rw [if_neg hi.2]
        rw [this, Finset.prod_const, hcard]
      rw [hp1, hp2, one_mul]
    exact hprod_neg.symm
  have hprod_pos : 0 < ∏ i : Fin d, (if i.val < k then (u - r i) else (r i - u)) := by
    refine Finset.prod_pos (fun i _ => ?_)
    split_ifs with h
    · linarith [hlt i h]
    · linarith [hgt i (by omega)]
  have heq : (-1 : ℝ) ^ (d - k) * (q.leadingCoeff * ∏ i : Fin d, (u - r i)) =
      q.leadingCoeff * ((-1 : ℝ) ^ (d - k) * ∏ i : Fin d, (u - r i)) := by ring
  rw [heq, hprod]
  exact mul_pos hlead hprod_pos

private lemma exists_neg_sign_at_neg_inf (q : Polynomial ℝ) (d : ℕ)
    (hdeg : q.natDegree = d) (hlead : 0 < q.leadingCoeff) (B : ℝ) :
    ∃ M : ℝ, M < B ∧ 0 < (-1 : ℝ) ^ d * q.eval M := by
  -- Use elementary Cauchy bound: for M < min(B, -1 - sum |c_j| / lead), leading term dominates!
  set S : ℝ := ∑ j ∈ Finset.range d, |q.coeff j|
  set M : ℝ := min (B - 1) (-(1 + S / q.leadingCoeff + 1))
  refine ⟨M, by exact lt_of_le_of_lt (min_le_left _ _) (by linarith), ?_⟩
  have hM_le1 : M ≤ -(1 + S / q.leadingCoeff + 1) := min_le_right _ _
  have hM_lt_neg1 : M < -1 := by
    have : (0 : ℝ) ≤ S / q.leadingCoeff := div_nonneg (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) hlead.le
    linarith
  have hnegM_gt1 : 1 < -M := by linarith
  have hnegM_pos : 0 < -M := by linarith
  have heval : q.eval M = q.leadingCoeff * M ^ d + ∑ j ∈ Finset.range d, q.coeff j * M ^ j := by
    rw [Polynomial.eval_eq_sum_range, hdeg, Finset.sum_range_succ, Polynomial.leadingCoeff, hdeg,
      add_comm]
  rw [heval, mul_add]
  have hmain : (-1 : ℝ) ^ d * (q.leadingCoeff * M ^ d) = q.leadingCoeff * (-M) ^ d := by
    have : (-1 : ℝ) ^ d * M ^ d = (-M) ^ d := by
      rw [← mul_pow]; ring_nf
    calc
      (-1 : ℝ) ^ d * (q.leadingCoeff * M ^ d) = q.leadingCoeff * ((-1 : ℝ) ^ d * M ^ d) := by ring
      _ = q.leadingCoeff * (-M) ^ d := by rw [this]
  rw [hmain]
  -- Bound the tail: |(-1)^d * ∑_{j<d} c_j * M^j| ≤ S * (-M)^(d-1) < lead * (-M)^d!
  cases d with
  | zero =>
    simp [hlead]
  | succ d' =>
    have htail : |(-1 : ℝ) ^ (d' + 1) * ∑ j ∈ Finset.range (d' + 1), q.coeff j * M ^ j| ≤
        S * (-M) ^ d' := by
      rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      calc
        |∑ j ∈ Finset.range (d' + 1), q.coeff j * M ^ j|
          ≤ ∑ j ∈ Finset.range (d' + 1), |q.coeff j * M ^ j| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j ∈ Finset.range (d' + 1), |q.coeff j| * (-M) ^ d' := by
            refine Finset.sum_le_sum (fun j hj => ?_)
            have hjle : j ≤ d' := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
            rw [abs_mul, abs_pow, abs_of_neg (by linarith : M < 0)]
            have hpow : (-M) ^ j ≤ (-M) ^ d' := pow_le_pow_right₀ hnegM_gt1.le hjle
            exact mul_le_mul_of_nonneg_left hpow (abs_nonneg _)
        _ = S * (-M) ^ d' := by rw [← Finset.sum_mul]
    have hdom : S * (-M) ^ d' < q.leadingCoeff * (-M) ^ (d' + 1) := by
      rw [pow_succ]
      have h1 : S < q.leadingCoeff * (-M) := by
        have h2 : S / q.leadingCoeff + 1 < -M := by linarith
        have h3 := mul_lt_mul_of_pos_left h2 hlead
        have h4 : q.leadingCoeff * (S / q.leadingCoeff + 1) = S + q.leadingCoeff := by
          field_simp [hlead.ne']
        linarith
      have hpow_pos : (0 : ℝ) < (-M) ^ d' := pow_pos hnegM_pos d'
      nlinarith
    have hlower : -(S * (-M) ^ d') ≤ (-1 : ℝ) ^ (d' + 1) * ∑ j ∈ Finset.range (d' + 1), q.coeff j * M ^ j :=
      (abs_le.mp htail).1
    linarith

private lemma exists_root_between (q : Polynomial ℝ) {a b : ℝ} (hab : a < b)
    (hsign : q.eval a * q.eval b < 0) :
    ∃ x : ℝ, a < x ∧ x < b ∧ q.eval x = 0 := by
  have hcont : ContinuousOn (fun x => q.eval x) (Set.Icc a b) := q.continuous.continuousOn
  by_cases ha : q.eval a < 0
  · have hb : 0 < q.eval b := by nlinarith
    have hmem : (0 : ℝ) ∈ Set.Ioo (q.eval a) (q.eval b) := ⟨ha, hb⟩
    obtain ⟨x, hx, hfx⟩ := intermediate_value_Ioo hab.le hcont hmem
    exact ⟨x, hx.1, hx.2, hfx⟩
  · have ha' : 0 < q.eval a := by
      rcases lt_or_eq_of_le (not_lt.mp ha) with h | h
      · exact h
      · rw [← h, zero_mul] at hsign; linarith
    have hb : q.eval b < 0 := by nlinarith
    have hmem : (0 : ℝ) ∈ Set.Ioo (q.eval b) (q.eval a) := ⟨hb, ha'⟩
    obtain ⟨x, hx, hfx⟩ := intermediate_value_Ioo' hab.le hcont hmem
    exact ⟨x, hx.1, hx.2, hfx⟩

/-! ### Part 5: Inductive construction of negative interlacing roots of `pPoly n` -/

private structure InterlacePair (m : ℕ) where
  a : Fin m → ℝ
  b : Fin m → ℝ
  ha_mono : StrictMono a
  hb_mono : StrictMono b
  ha_neg : ∀ i : Fin m, a i < 0
  hb_neg : ∀ i : Fin m, b i < 0
  ha_root : ∀ i : Fin m, (pPoly (2 * m)).eval (a i) = 0
  hb_root : ∀ i : Fin m, (pPoly (2 * m + 1)).eval (b i) = 0
  hlt : ∀ i : Fin m, b i < a i
  hgt : ∀ (i : ℕ) (hi : i + 1 < m), a ⟨i, by omega⟩ < b ⟨i + 1, by omega⟩

private noncomputable def basePair : InterlacePair 1 where
  a := fun _ => -(1 / 8 : ℝ)
  b := fun _ => -(3 / 8 : ℝ)
  ha_mono := fun i j hij => by omega
  hb_mono := fun i j hij => by omega
  ha_neg := fun _ => by norm_num
  hb_neg := fun _ => by norm_num
  ha_root := fun _ => by rw [pPoly_two]; simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one]; norm_num
  hb_root := fun _ => by rw [pPoly_three]; simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]; norm_num
  hlt := fun _ => by norm_num
  hgt := fun i hi => by omega

private lemma pPoly_even_at_prev_root (m : ℕ) (u : ℝ) (hu : (pPoly (2 * m + 1)).eval u = 0) :
    (pPoly (2 * m + 2)).eval u =
      ((2 * m + 1 : ℕ) : ℝ) ^ 2 * (1 - 4 * u) * (pPoly (2 * m)).eval u := by
  have h : pPoly (2 * m + 2) =
      Polynomial.C (2 * (2 * ((2 * m + 2 : ℕ) : ℝ) - 1)) * Polynomial.X * pPoly (2 * m + 1) +
        Polynomial.C (((2 * m + 1 : ℕ) : ℝ) ^ 2) * (1 - Polynomial.C 4 * Polynomial.X) * pPoly (2 * m) := by
    conv_lhs => unfold pPoly
    rw [if_pos ⟨m + 1, by omega⟩]
  rw [h]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_one, hu, mul_zero, zero_add]

private lemma pPoly_odd_at_prev_root (m : ℕ) (u : ℝ) (hu : (pPoly (2 * m + 2)).eval u = 0) :
    (pPoly (2 * m + 3)).eval u =
      ((2 * m + 2 : ℕ) : ℝ) ^ 2 * (1 - 4 * u) * (pPoly (2 * m + 1)).eval u := by
  have h : pPoly (2 * m + 3) =
      Polynomial.C (2 * (2 * ((2 * m + 3 : ℕ) : ℝ) - 1)) * pPoly (2 * m + 2) +
        Polynomial.C (((2 * m + 2 : ℕ) : ℝ) ^ 2) * (1 - Polynomial.C 4 * Polynomial.X) * pPoly (2 * m + 1) := by
    conv_lhs => unfold pPoly
    rw [if_neg (by rintro ⟨k, hk⟩; omega)]
  rw [h]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_one, hu, mul_zero, zero_add]

private lemma mul_lt_zero_of_opp_sign (k : ℕ) (x y : ℝ)
    (hx : 0 < (-1 : ℝ) ^ (k + 1) * x) (hy : 0 < (-1 : ℝ) ^ k * y) : x * y < 0 := by
  have hsq : (-1 : ℝ) ^ (k + 1) * (-1 : ℝ) ^ k = -1 := by
    rw [← pow_add, show k + 1 + k = 2 * k + 1 by omega, pow_succ, pow_mul]; norm_num
  have hprod : 0 < ((-1 : ℝ) ^ (k + 1) * x) * ((-1 : ℝ) ^ k * y) := mul_pos hx hy
  have heq : ((-1 : ℝ) ^ (k + 1) * x) * ((-1 : ℝ) ^ k * y) = -(x * y) := by
    calc
      ((-1 : ℝ) ^ (k + 1) * x) * ((-1 : ℝ) ^ k * y)
        = ((-1 : ℝ) ^ (k + 1) * (-1 : ℝ) ^ k) * (x * y) := by ring
      _ = -(x * y) := by rw [hsq]; ring
  linarith

private structure EvenStepRes (m : ℕ) (P_prev : InterlacePair m) where
  a' : Fin (m + 1) → ℝ
  ha'_mono : StrictMono a'
  ha'_neg : ∀ j : Fin (m + 1), a' j < 0
  ha'_root : ∀ j : Fin (m + 1), (pPoly (2 * m + 2)).eval (a' j) = 0
  ha'_inter : ∀ i : Fin m, a' ⟨i.val, by omega⟩ < P_prev.b i ∧ P_prev.b i < a' ⟨i.val + 1, by omega⟩

private noncomputable def stepEven (m : ℕ) (hm : 1 ≤ m) (P_prev : InterlacePair m) :
    EvenStepRes m P_prev := by
  have ⟨hd2m, hl2m⟩ := pPoly_deg_and_lead (2 * m)
  have ⟨hd2m2, hl2m2⟩ := pPoly_deg_and_lead (2 * m + 2)
  have hl2m_pos : 0 < (pPoly (2 * m)).leadingCoeff := by rw [hl2m]; positivity
  have hl2m2_pos : 0 < (pPoly (2 * m + 2)).leadingCoeff := by rw [hl2m2]; positivity
  have hd2m' : (pPoly (2 * m)).natDegree = m := by omega
  have hd2m2' : (pPoly (2 * m + 2)).natDegree = m + 1 := by omega
  have hsign_a' : ∀ j : Fin m, 0 < (-1 : ℝ) ^ (m - j.val) * (pPoly (2 * m + 2)).eval (P_prev.b j) := by
    intro j
    rw [pPoly_even_at_prev_root m (P_prev.b j) (P_prev.hb_root j)]
    have hfac : 0 < ((2 * m + 1 : ℕ) : ℝ) ^ 2 * (1 - 4 * P_prev.b j) := by
      have hneg := P_prev.hb_neg j
      have hsq : (0 : ℝ) < ((2 * m + 1 : ℕ) : ℝ) ^ 2 := by positivity
      nlinarith
    have hprev := eval_sign_of_roots (pPoly (2 * m)) m hd2m' hl2m_pos P_prev.a P_prev.ha_mono
      P_prev.ha_root (P_prev.b j) j.val (by omega)
      (fun i hi => by
        have h1 : P_prev.a i ≤ P_prev.a ⟨j.val - 1, by omega⟩ :=
          P_prev.ha_mono.monotone (by show i.val ≤ j.val - 1; omega)
        have h2 := P_prev.hgt (j.val - 1) (by omega)
        have hidx : (⟨j.val - 1 + 1, by omega⟩ : Fin m) = j := Fin.ext (by dsimp; omega)
        rw [hidx] at h2
        linarith)
      (fun i hi => by
        have h1 := P_prev.hlt j
        have h2 : P_prev.a j ≤ P_prev.a i := P_prev.ha_mono.monotone hi
        linarith)
    have hmul : (-1 : ℝ) ^ (m - j.val) * (((2 * m + 1 : ℕ) : ℝ) ^ 2 * (1 - 4 * P_prev.b j) * (pPoly (2 * m)).eval (P_prev.b j)) =
        (((2 * m + 1 : ℕ) : ℝ) ^ 2 * (1 - 4 * P_prev.b j)) * ((-1 : ℝ) ^ (m - j.val) * (pPoly (2 * m)).eval (P_prev.b j)) := by
      ring
    rw [hmul]
    exact mul_pos hfac hprev
  have hM_ex := exists_neg_sign_at_neg_inf (pPoly (2 * m + 2)) (m + 1) hd2m2' hl2m2_pos
    (P_prev.b ⟨0, by omega⟩)
  let M : ℝ := Classical.choose hM_ex
  have hM_spec : M < P_prev.b ⟨0, by omega⟩ ∧ 0 < (-1 : ℝ) ^ (m + 1) * (pPoly (2 * m + 2)).eval M :=
    Classical.choose_spec hM_ex
  have ha'_ex : ∀ j : Fin (m + 1),
      ∃ x : ℝ,
        (if _ : j.val = 0 then M else P_prev.b ⟨j.val - 1, by omega⟩) < x ∧
        x < (if _ : j.val = m then 0 else P_prev.b ⟨j.val, by omega⟩) ∧
        (pPoly (2 * m + 2)).eval x = 0 := by
    intro j
    by_cases h0 : j.val = 0
    · rw [dif_pos h0, dif_neg (by omega : ¬ j.val = m)]
      have h2 := hsign_a' ⟨0, by omega⟩
      simp only [Nat.sub_zero] at h2
      have hidx : (⟨j.val, by omega⟩ : Fin m) = ⟨0, by omega⟩ := Fin.ext h0
      rw [hidx]
      exact exists_root_between (pPoly (2 * m + 2)) hM_spec.1 (mul_lt_zero_of_opp_sign m _ _ hM_spec.2 h2)
    · by_cases hm' : j.val = m
      · rw [dif_neg h0, dif_pos hm']
        have h1 := hsign_a' ⟨m - 1, by omega⟩
        rw [show m - (m - 1) = 1 by omega, pow_one] at h1
        have h2 := pPoly_eval_zero_pos (2 * m + 2)
        have hidx : (⟨j.val - 1, by omega⟩ : Fin m) = ⟨m - 1, by omega⟩ := Fin.ext (by dsimp; omega)
        rw [hidx]
        exact exists_root_between (pPoly (2 * m + 2)) (P_prev.hb_neg ⟨m - 1, by omega⟩) (by nlinarith)
      · rw [dif_neg h0, dif_neg hm']
        have h1 := hsign_a' ⟨j.val - 1, by omega⟩
        rw [show m - (j.val - 1) = (m - j.val) + 1 by omega] at h1
        have h2 := hsign_a' ⟨j.val, by omega⟩
        have hlt_b : P_prev.b ⟨j.val - 1, by omega⟩ < P_prev.b ⟨j.val, by omega⟩ :=
          P_prev.hb_mono (by show j.val - 1 < j.val; omega)
        exact exists_root_between (pPoly (2 * m + 2)) hlt_b (mul_lt_zero_of_opp_sign (m - j.val) _ _ h1 h2)
  let a' : Fin (m + 1) → ℝ := fun j => Classical.choose (ha'_ex j)
  have ha'_spec : ∀ j : Fin (m + 1),
      (if _ : j.val = 0 then M else P_prev.b ⟨j.val - 1, by omega⟩) < a' j ∧
      a' j < (if _ : j.val = m then 0 else P_prev.b ⟨j.val, by omega⟩) ∧
      (pPoly (2 * m + 2)).eval (a' j) = 0 :=
    fun j => Classical.choose_spec (ha'_ex j)
  have ha'_inter : ∀ i : Fin m, a' ⟨i.val, by omega⟩ < P_prev.b i ∧ P_prev.b i < a' ⟨i.val + 1, by omega⟩ := by
    intro i
    constructor
    · have h := (ha'_spec ⟨i.val, by omega⟩).2.1
      rw [dif_neg (by omega : ¬ i.val = m)] at h
      exact h
    · have h := (ha'_spec ⟨i.val + 1, by omega⟩).1
      rw [dif_neg (by omega : ¬ i.val + 1 = 0)] at h
      have hidx : (⟨i.val + 1 - 1, by omega⟩ : Fin m) = i := Fin.ext rfl
      rwa [hidx] at h
  have ha'_mono : StrictMono a' := by
    intro i j hij
    have h1 := (ha'_inter ⟨i.val, by omega⟩).1
    have h2 : P_prev.b ⟨i.val, by omega⟩ ≤ P_prev.b ⟨j.val - 1, by omega⟩ :=
      P_prev.hb_mono.monotone (by show i.val ≤ j.val - 1; omega)
    have h3 := (ha'_inter ⟨j.val - 1, by omega⟩).2
    have hidx : (⟨j.val - 1 + 1, by omega⟩ : Fin (m + 1)) = j := Fin.ext (by dsimp; omega)
    rw [hidx] at h3
    linarith
  have ha'_neg : ∀ j : Fin (m + 1), a' j < 0 := by
    intro j
    have h := (ha'_spec j).2.1
    split_ifs at h with hm'
    · exact h
    · exact lt_trans h (P_prev.hb_neg _)
  exact ⟨a', ha'_mono, ha'_neg, fun j => (ha'_spec j).2.2, ha'_inter⟩

private noncomputable def stepOdd (m : ℕ) (_hm : 1 ≤ m) (P_prev : InterlacePair m)
    (E : EvenStepRes m P_prev) : { P_next : InterlacePair (m + 1) // P_next.a = E.a' } := by
  have ⟨hd2m1, hl2m1⟩ := pPoly_deg_and_lead (2 * m + 1)
  have ⟨hd2m3, hl2m3⟩ := pPoly_deg_and_lead (2 * m + 3)
  have hl2m1_pos : 0 < (pPoly (2 * m + 1)).leadingCoeff := by rw [hl2m1]; positivity
  have hl2m3_pos : 0 < (pPoly (2 * m + 3)).leadingCoeff := by rw [hl2m3]; positivity
  have hd2m1' : (pPoly (2 * m + 1)).natDegree = m := by omega
  have hd2m3' : (pPoly (2 * m + 3)).natDegree = m + 1 := by omega
  have hsign_b' : ∀ j : Fin (m + 1), 0 < (-1 : ℝ) ^ (m - j.val) * (pPoly (2 * m + 3)).eval (E.a' j) := by
    intro j
    rw [pPoly_odd_at_prev_root m (E.a' j) (E.ha'_root j)]
    have hfac : 0 < ((2 * m + 2 : ℕ) : ℝ) ^ 2 * (1 - 4 * E.a' j) := by
      have hneg := E.ha'_neg j
      have hsq : (0 : ℝ) < ((2 * m + 2 : ℕ) : ℝ) ^ 2 := by positivity
      nlinarith
    have hprev := eval_sign_of_roots (pPoly (2 * m + 1)) m hd2m1' hl2m1_pos P_prev.b P_prev.hb_mono
      P_prev.hb_root (E.a' j) j.val (by omega)
      (fun i hi => by
        have h1 : P_prev.b i ≤ P_prev.b ⟨j.val - 1, by omega⟩ :=
          P_prev.hb_mono.monotone (by show i.val ≤ j.val - 1; omega)
        have h2 := (E.ha'_inter ⟨j.val - 1, by omega⟩).2
        have hidx : (⟨j.val - 1 + 1, by omega⟩ : Fin (m + 1)) = j := Fin.ext (by dsimp; omega)
        rw [hidx] at h2
        linarith)
      (fun i hi => by
        have h1 := (E.ha'_inter ⟨j.val, by omega⟩).1
        have h2 : P_prev.b ⟨j.val, by omega⟩ ≤ P_prev.b i := P_prev.hb_mono.monotone hi
        linarith)
    have hmul : (-1 : ℝ) ^ (m - j.val) * (((2 * m + 2 : ℕ) : ℝ) ^ 2 * (1 - 4 * E.a' j) * (pPoly (2 * m + 1)).eval (E.a' j)) =
        (((2 * m + 2 : ℕ) : ℝ) ^ 2 * (1 - 4 * E.a' j)) * ((-1 : ℝ) ^ (m - j.val) * (pPoly (2 * m + 1)).eval (E.a' j)) := by
      ring
    rw [hmul]
    exact mul_pos hfac hprev
  have hM'_ex := exists_neg_sign_at_neg_inf (pPoly (2 * m + 3)) (m + 1) hd2m3' hl2m3_pos
    (E.a' ⟨0, by omega⟩)
  let M' : ℝ := Classical.choose hM'_ex
  have hM'_spec : M' < E.a' ⟨0, by omega⟩ ∧ 0 < (-1 : ℝ) ^ (m + 1) * (pPoly (2 * m + 3)).eval M' :=
    Classical.choose_spec hM'_ex
  have hb'_ex : ∀ j : Fin (m + 1),
      ∃ x : ℝ,
        (if _ : j.val = 0 then M' else E.a' ⟨j.val - 1, by omega⟩) < x ∧
        x < E.a' j ∧
        (pPoly (2 * m + 3)).eval x = 0 := by
    intro j
    by_cases h0 : j.val = 0
    · rw [dif_pos h0]
      have hidx : j = ⟨0, by omega⟩ := Fin.ext h0
      rw [hidx]
      have h2 := hsign_b' ⟨0, by omega⟩
      simp only [Nat.sub_zero] at h2
      exact exists_root_between (pPoly (2 * m + 3)) hM'_spec.1 (mul_lt_zero_of_opp_sign m _ _ hM'_spec.2 h2)
    · rw [dif_neg h0]
      have h1 := hsign_b' ⟨j.val - 1, by omega⟩
      rw [show m - (j.val - 1) = (m - j.val) + 1 by omega] at h1
      have h2 := hsign_b' j
      have hlt_a : E.a' ⟨j.val - 1, by omega⟩ < E.a' j := E.ha'_mono (by show j.val - 1 < j.val; omega)
      exact exists_root_between (pPoly (2 * m + 3)) hlt_a (mul_lt_zero_of_opp_sign (m - j.val) _ _ h1 h2)
  let b' : Fin (m + 1) → ℝ := fun j => Classical.choose (hb'_ex j)
  have hb'_spec : ∀ j : Fin (m + 1),
      (if _ : j.val = 0 then M' else E.a' ⟨j.val - 1, by omega⟩) < b' j ∧
      b' j < E.a' j ∧
      (pPoly (2 * m + 3)).eval (b' j) = 0 :=
    fun j => Classical.choose_spec (hb'_ex j)
  have hb'_gt : ∀ (i : ℕ) (hi : i + 1 < m + 1), E.a' ⟨i, by omega⟩ < b' ⟨i + 1, by omega⟩ := by
    intro i hi
    have h := (hb'_spec ⟨i + 1, by omega⟩).1
    rw [dif_neg (by omega : ¬ i + 1 = 0)] at h
    have hidx : (⟨i + 1 - 1, by omega⟩ : Fin (m + 1)) = ⟨i, by omega⟩ := Fin.ext rfl
    rwa [hidx] at h
  have hb'_mono : StrictMono b' := by
    intro i j hij
    have h1 := (hb'_spec i).2.1
    have h2 : E.a' i ≤ E.a' ⟨j.val - 1, by omega⟩ := E.ha'_mono.monotone (by show i.val ≤ j.val - 1; omega)
    have h3 := hb'_gt (j.val - 1) (by omega)
    have hidx : (⟨j.val - 1 + 1, by omega⟩ : Fin (m + 1)) = j := Fin.ext (by dsimp; omega)
    rw [hidx] at h3
    linarith
  exact ⟨⟨E.a', b', E.ha'_mono, hb'_mono, E.ha'_neg,
    fun j => lt_trans (hb'_spec j).2.1 (E.ha'_neg j),
    E.ha'_root, fun j => (hb'_spec j).2.2,
    fun j => (hb'_spec j).2.1, hb'_gt⟩, rfl⟩

private noncomputable def stepPair (m : ℕ) (hm : 1 ≤ m) (P_prev : InterlacePair m) :
    { P_next : InterlacePair (m + 1) //
      ∀ i : Fin m,
        P_next.a ⟨i.val, by omega⟩ < P_prev.b i ∧ P_prev.b i < P_next.a ⟨i.val + 1, by omega⟩ } :=
  let E := stepEven m hm P_prev
  let O := stepOdd m hm P_prev E
  ⟨O.1, by rw [O.2]; exact E.ha'_inter⟩

private noncomputable def pairSeq : ∀ m : ℕ, 1 ≤ m → InterlacePair m
  | 0, h => absurd h (by omega)
  | 1, _ => basePair
  | m + 2, _ => (stepPair (m + 1) (by omega) (pairSeq (m + 1) (by omega))).1

private lemma pairSeq_interlace_even_succ (m : ℕ) (hm : 1 ≤ m) (i : Fin m) :
    (pairSeq (m + 1) (by omega)).a ⟨i.val, by omega⟩ < (pairSeq m hm).b i ∧
    (pairSeq m hm).b i < (pairSeq (m + 1) (by omega)).a ⟨i.val + 1, by omega⟩ := by
  cases m with
  | zero => omega
  | succ m' =>
    exact (stepPair (m' + 1) (by omega) (pairSeq (m' + 1) (by omega))).2 i

private noncomputable def allRoots (n : ℕ) : Fin (n / 2) → ℝ :=
  if h0 : n / 2 = 0 then
    fun i => absurd i.isLt (by omega)
  else
    if hev : Even n then
      fun i => (pairSeq (n / 2) (by omega)).a i
    else
      fun i => (pairSeq (n / 2) (by omega)).b i

private lemma allRoots_even (m : ℕ) (hm : 1 ≤ m) (i : Fin m) :
    allRoots (2 * m) ⟨i.val, by omega⟩ = (pairSeq m hm).a i := by
  unfold allRoots
  rw [dif_neg (by omega : ¬ (2 * m) / 2 = 0), dif_pos ⟨m, by omega⟩]
  have hdiv : (2 * m) / 2 = m := by omega
  generalize_proofs h1 h2
  have : ∀ (k : ℕ) (hk : k = m) (h1' : 1 ≤ k) (j : Fin k) (hj : j.val = i.val),
      (pairSeq k h1').a j = (pairSeq m hm).a i := by
    rintro _ rfl h1' j hj
    congr 1
    exact Fin.ext hj
  exact this ((2 * m) / 2) hdiv h1 ⟨i.val, h2⟩ rfl

private lemma allRoots_odd (m : ℕ) (hm : 1 ≤ m) (i : Fin m) :
    allRoots (2 * m + 1) ⟨i.val, by omega⟩ = (pairSeq m hm).b i := by
  unfold allRoots
  rw [dif_neg (by omega : ¬ (2 * m + 1) / 2 = 0), dif_neg (by rintro ⟨k, hk⟩; omega)]
  have hdiv : (2 * m + 1) / 2 = m := by omega
  generalize_proofs h1 h2
  have : ∀ (k : ℕ) (hk : k = m) (h1' : 1 ≤ k) (j : Fin k) (hj : j.val = i.val),
      (pairSeq k h1').b j = (pairSeq m hm).b i := by
    rintro _ rfl h1' j hj
    congr 1
    exact Fin.ext hj
  exact this ((2 * m + 1) / 2) hdiv h1 ⟨i.val, h2⟩ rfl

private lemma allRoots_mono (n : ℕ) : StrictMono (allRoots n) := by
  by_cases h0 : n / 2 = 0
  · intro i j hij; exfalso; omega
  · rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
    · have hm : 1 ≤ m := by omega
      intro i j hij
      have hi : i = ⟨i.val, by omega⟩ := Fin.ext rfl
      have hj : j = ⟨j.val, by omega⟩ := Fin.ext rfl
      rw [allRoots_even m hm ⟨i.val, by omega⟩, allRoots_even m hm ⟨j.val, by omega⟩]
      exact (pairSeq m hm).ha_mono hij
    · have hm : 1 ≤ m := by omega
      intro i j hij
      rw [allRoots_odd m hm ⟨i.val, by omega⟩, allRoots_odd m hm ⟨j.val, by omega⟩]
      exact (pairSeq m hm).hb_mono hij

private lemma allRoots_neg (n : ℕ) (i : Fin (n / 2)) : allRoots n i < 0 := by
  rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
  · have hm : 1 ≤ m := by have := i.isLt; omega
    rw [allRoots_even m hm ⟨i.val, by omega⟩]
    exact (pairSeq m hm).ha_neg _
  · have hm : 1 ≤ m := by have := i.isLt; omega
    rw [allRoots_odd m hm ⟨i.val, by omega⟩]
    exact (pairSeq m hm).hb_neg _

private lemma allRoots_isRoot (n : ℕ) (i : Fin (n / 2)) : (pPoly n).eval (allRoots n i) = 0 := by
  rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
  · have hm : 1 ≤ m := by have := i.isLt; omega
    rw [allRoots_even m hm ⟨i.val, by omega⟩]
    exact (pairSeq m hm).ha_root _
  · have hm : 1 ≤ m := by have := i.isLt; omega
    rw [allRoots_odd m hm ⟨i.val, by omega⟩]
    exact (pairSeq m hm).hb_root _

private lemma pPoly_eq_factorized (n : ℕ) :
    pPoly n = Polynomial.C (pPoly n).leadingCoeff *
      ∏ i : Fin (n / 2), (Polynomial.X - Polynomial.C (allRoots n i)) := by
  have ⟨hd, hl⟩ := pPoly_deg_and_lead n
  have hl_pos : 0 < (pPoly n).leadingCoeff := by rw [hl]; positivity
  exact poly_eq_C_mul_prod_of_roots (pPoly n) (n / 2) hd hl_pos (allRoots n)
    (allRoots_mono n) (allRoots_isRoot n)

private lemma pPoly_eval_eq_zero_iff (n : ℕ) (u : ℝ) :
    (pPoly n).eval u = 0 ↔ ∃ i : Fin (n / 2), u = allRoots n i := by
  rw [pPoly_eq_factorized n]
  have ⟨_, hl⟩ := pPoly_deg_and_lead n
  have hl_ne : (pPoly n).leadingCoeff ≠ 0 := by rw [hl]; positivity
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod, Polynomial.eval_sub,
    Polynomial.eval_X, mul_eq_zero, hl_ne, false_or, Finset.prod_eq_zero_iff, Finset.mem_univ,
    true_and, sub_eq_zero]

private lemma riemann_hypothesis (n : ℕ) (_hn : 1 ≤ n) (z : ℂ) (hz : (PComplex n).eval z = 0) :
    z.re = 1 / 2 := by
  set w : ℂ := z - 1 / 2
  have hzw : z = 1 / 2 + w := by dsimp only [w]; ring
  rw [hzw, PComplex_eval_shift n w] at hz
  have hwp : ((pPoly n).map (algebraMap ℝ ℂ)).eval (w ^ 2) = 0 ∨ w = 0 := by
    split_ifs at hz
    · exact Or.inl hz
    · exact (mul_eq_zero.mp hz).symm
  rcases hwp with hp | hw0
  · rw [pPoly_eq_factorized n] at hp
    simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_prod, Polynomial.map_sub,
      Polynomial.map_X, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod,
      Polynomial.eval_sub, Polynomial.eval_X] at hp
    have ⟨_, hl⟩ := pPoly_deg_and_lead n
    have hl_ne : ((pPoly n).leadingCoeff : ℂ) ≠ 0 := by
      exact_mod_cast (by rw [hl]; positivity : (pPoly n).leadingCoeff ≠ 0)
    have hprod0 : (∏ i : Fin (n / 2), (w ^ 2 - (allRoots n i : ℂ))) = 0 := by
      rcases mul_eq_zero.mp hp with h1 | h2
      · exact absurd h1 hl_ne
      · exact h2
    obtain ⟨i, _, hi⟩ := Finset.prod_eq_zero_iff.mp hprod0
    have hw2 : w ^ 2 = (allRoots n i : ℂ) := sub_eq_zero.mp hi
    have hre := congr_arg Complex.re hw2
    have him := congr_arg Complex.im hw2
    simp only [sq, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im] at hre him
    have hneg : allRoots n i < 0 := allRoots_neg n i
    have hwre : w.re = 0 := by
      by_contra hne
      have h2 : (2 * w.re) * w.im = 0 := by linarith
      have hwim : w.im = 0 := by
        rcases mul_eq_zero.mp h2 with h1 | h1
        · exfalso; apply hne; linarith
        · exact h1
      rw [hwim] at hre
      nlinarith
    rw [hzw]
    simp only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re, hwre, add_zero]
  · rw [hzw, hw0, add_zero]
    norm_num

theorem solution :
    (∀ (n : ℕ) (x : ℝ),
      (P n).eval (1 / 2 + x) =
        if Even n then (pPoly n).eval (x ^ 2) else x * (pPoly n).eval (x ^ 2)) ∧
    (∀ (n : ℕ), 1 ≤ n → ∀ z : ℂ, (PComplex n).eval z = 0 → z.re = 1 / 2) ∧
    (∃ roots : ∀ n : ℕ, Fin (n / 2) → ℝ,
      (∀ n : ℕ, StrictMono (roots n)) ∧
      (∀ (n : ℕ) (i : Fin (n / 2)), roots n i < 0) ∧
      (∀ (n : ℕ) (u : ℝ), (pPoly n).eval u = 0 ↔ ∃ i : Fin (n / 2), u = roots n i) ∧
      (∀ (m : ℕ), 1 ≤ m →
        (∀ (i : Fin m),
          roots (2 * m + 1) ⟨i.val, by omega⟩ < roots (2 * m) ⟨i.val, by omega⟩) ∧
        (∀ (i : ℕ) (hi : i + 1 < m),
          roots (2 * m) ⟨i, by omega⟩ < roots (2 * m + 1) ⟨i + 1, by omega⟩) ∧
        (∀ (i : Fin m),
          roots (2 * m + 2) ⟨i.val, by omega⟩ < roots (2 * m + 1) ⟨i.val, by omega⟩ ∧
          roots (2 * m + 1) ⟨i.val, by omega⟩ < roots (2 * m + 2) ⟨i.val + 1, by omega⟩))) := by
  refine ⟨P_eval_shift, riemann_hypothesis, allRoots, allRoots_mono, allRoots_neg,
    pPoly_eval_eq_zero_iff, ?_⟩
  intro m hm
  refine ⟨fun i => ?_, fun i hi => ?_, fun i => ?_⟩
  · rw [allRoots_odd m hm i, allRoots_even m hm i]
    exact (pairSeq m hm).hlt i
  · rw [allRoots_even m hm ⟨i, by omega⟩, allRoots_odd m hm ⟨i + 1, by omega⟩]
    exact (pairSeq m hm).hgt i hi
  · have h2m2 : 2 * m + 2 = 2 * (m + 1) := by omega
    have h := pairSeq_interlace_even_succ m hm i
    have he1 : allRoots (2 * m + 2) ⟨i.val, by omega⟩ = (pairSeq (m + 1) (by omega)).a ⟨i.val, by omega⟩ := by
      have := allRoots_even (m + 1) (by omega) ⟨i.val, by omega⟩
      have hcast : ∀ (k : ℕ) (hk : k = 2 * (m + 1)) (j : Fin (k / 2)) (hj : j.val = i.val),
          allRoots k j = allRoots (2 * (m + 1)) ⟨i.val, by omega⟩ := by
        rintro _ rfl j hj; congr 1; exact Fin.ext hj
      rw [hcast (2 * m + 2) h2m2 ⟨i.val, by omega⟩ rfl, this]
    have he2 : allRoots (2 * m + 2) ⟨i.val + 1, by omega⟩ = (pairSeq (m + 1) (by omega)).a ⟨i.val + 1, by omega⟩ := by
      have := allRoots_even (m + 1) (by omega) ⟨i.val + 1, by omega⟩
      have hcast : ∀ (k : ℕ) (hk : k = 2 * (m + 1)) (j : Fin (k / 2)) (hj : j.val = i.val + 1),
          allRoots k j = allRoots (2 * (m + 1)) ⟨i.val + 1, by omega⟩ := by
        rintro _ rfl j hj; congr 1; exact Fin.ext hj
      rw [hcast (2 * m + 2) h2m2 ⟨i.val + 1, by omega⟩ rfl, this]
    rw [he1, he2, allRoots_odd m hm i]
    exact h

end OMA.P_oeis_a123516

theorem OMA.solution : type_of% @OMA.S_oeis_a123516.main :=
  OMA.P_oeis_a123516.solution
