import OMAStatements.S_oeis_a051286

open Finset PowerSeries

namespace OMA.S_oeis_a051286_Proof

private def b (m : ℤ) (k : ℕ) : ℤ :=
  if 0 ≤ m then ((m.toNat).choose k : ℤ) else 0

private lemma b_neg {m : ℤ} (hm : m < 0) (k : ℕ) : b m k = 0 := by
  rw [b, if_neg (not_le.mpr hm)]

private lemma b_nonneg {m : ℤ} (hm : 0 ≤ m) (k : ℕ) : b m k = ((m.toNat).choose k : ℤ) := by
  rw [b, if_pos hm]

private lemma b_absorb (m : ℤ) (k : ℕ) : (m - k) * b m k = m * b (m - 1) k := by
  by_cases hm : 0 ≤ m
  · rcases eq_or_lt_of_le hm with rfl | hpos
    · cases k <;> simp [b]
    · set t : ℕ := (m - 1).toNat
      have hm_eq : m = (t + 1 : ℕ) := by omega
      have hbm : b m k = ((t + 1).choose k : ℤ) := by
        rw [b_nonneg hm, show m.toNat = t + 1 by omega]
      have hbm1 : b (m - 1) k = (t.choose k : ℤ) := by
        rw [b_nonneg (by omega), show (m - 1).toNat = t by omega]
      rw [hbm, hbm1, hm_eq]
      cases k with
      | zero => simp
      | succ k =>
        have h1 : ((t + 1).choose (k + 1) : ℤ) = (t.choose k : ℤ) + (t.choose (k + 1) : ℤ) := by
          exact_mod_cast Nat.choose_succ_succ t k
        have h2 : ((t + 1 : ℕ) : ℤ) * (t.choose k : ℤ) =
            ((t + 1).choose (k + 1) : ℤ) * ((k + 1 : ℕ) : ℤ) := by
          exact_mod_cast Nat.add_one_mul_choose_eq t k
        have h1' : ((t + 1 : ℕ) : ℤ) * ((t + 1).choose (k + 1) : ℤ) =
            ((t + 1 : ℕ) : ℤ) * (t.choose k : ℤ) + ((t + 1 : ℕ) : ℤ) * (t.choose (k + 1) : ℤ) := by
          rw [h1]; ring
        push_cast at h1' h2 ⊢
        linarith
  · rw [b_neg (not_le.mp hm), b_neg (by omega)]
    ring

private lemma b_pascal (m : ℤ) (k : ℕ) : b m k = b (m + 1) (k + 1) - b m (k + 1) := by
  by_cases hm : 0 ≤ m
  · set t : ℕ := m.toNat
    have h1 : ((t + 1).choose (k + 1) : ℤ) = (t.choose k : ℤ) + (t.choose (k + 1) : ℤ) := by
      exact_mod_cast Nat.choose_succ_succ t k
    have hbm : b m k = (t.choose k : ℤ) := by rw [b_nonneg hm]
    have hbm1 : b (m + 1) (k + 1) = ((t + 1).choose (k + 1) : ℤ) := by
      rw [b_nonneg (by omega), show (m + 1).toNat = t + 1 by omega]
    have hbm2 : b m (k + 1) = (t.choose (k + 1) : ℤ) := by rw [b_nonneg hm]
    rw [hbm, hbm1, hbm2]
    linarith
  · by_cases hm1 : 0 ≤ m + 1
    · have hm_eq : m = -1 := by omega
      subst hm_eq
      simp [b]
    · rw [b_neg (not_le.mp hm), b_neg (not_le.mp hm1), b_neg (not_le.mp hm)]
      ring

private def L (n : ℤ) (k : ℕ) : ℤ :=
  (n + 4) * (b (n + 4 - k) k) ^ 2
  - (2 * n + 7) * (b (n + 3 - k) k) ^ 2
  - (n + 3) * (b (n + 2 - k) k) ^ 2
  - (2 * n + 5) * (b (n + 1 - k) k) ^ 2
  + (n + 2) * (b (n - k) k) ^ 2

private def G (n : ℤ) : ℕ → ℤ
  | 0 => 0
  | k + 1 =>
    let c0 := b (n - (k + 1 : ℤ)) k
    let c1 := b (n + 1 - (k + 1 : ℤ)) k
    let c2 := b (n + 2 - (k + 1 : ℤ)) k
    let c3 := b (n + 3 - (k + 1 : ℤ)) k
    (1 - n) * c0 * c2 - c0 * c1 + (4 + 2 * n) * c1 ^ 2 + 2 * n * c1 * c3
      - (9 + 3 * n) * c2 ^ 2 - 2 * n * c2 * c3 - (4 + n) * c3 ^ 2

private lemma b_zero_of_nonneg {m : ℤ} (hm : 0 ≤ m) : b m 0 = 1 := by
  rw [b_nonneg hm, Nat.choose_zero_right, Nat.cast_one]

private lemma telescope_zero (n : ℤ) : L n 0 = G n 1 - G n 0 := by
  by_cases h1 : 1 ≤ n
  · simp only [L, G, Nat.cast_zero, sub_zero]
    rw [b_zero_of_nonneg (show (0 : ℤ) ≤ n + 4 by omega),
      b_zero_of_nonneg (show (0 : ℤ) ≤ n + 3 by omega),
      b_zero_of_nonneg (show (0 : ℤ) ≤ n + 2 by omega),
      b_zero_of_nonneg (show (0 : ℤ) ≤ n + 1 by omega),
      b_zero_of_nonneg (show (0 : ℤ) ≤ n by omega),
      b_zero_of_nonneg (show (0 : ℤ) ≤ n - (0 + 1) by omega),
      b_zero_of_nonneg (show (0 : ℤ) ≤ n + 1 - (0 + 1) by omega),
      b_zero_of_nonneg (show (0 : ℤ) ≤ n + 2 - (0 + 1) by omega),
      b_zero_of_nonneg (show (0 : ℤ) ≤ n + 3 - (0 + 1) by omega)]
    ring
  · by_cases h2 : n < -4
    · simp only [L, G, Nat.cast_zero, sub_zero]
      rw [b_neg (show n + 4 < (0 : ℤ) by omega),
        b_neg (show n + 3 < (0 : ℤ) by omega),
        b_neg (show n + 2 < (0 : ℤ) by omega),
        b_neg (show n + 1 < (0 : ℤ) by omega),
        b_neg (show n < (0 : ℤ) by omega),
        b_neg (show n - (0 + 1) < (0 : ℤ) by omega),
        b_neg (show n + 1 - (0 + 1) < (0 : ℤ) by omega),
        b_neg (show n + 2 - (0 + 1) < (0 : ℤ) by omega),
        b_neg (show n + 3 - (0 + 1) < (0 : ℤ) by omega)]
      ring
    · have hcases : n = -4 ∨ n = -3 ∨ n = -2 ∨ n = -1 ∨ n = 0 := by omega
      rcases hcases with rfl | rfl | rfl | rfl | rfl <;> decide

private lemma telescope (n : ℤ) (k : ℕ) : L n k = G n (k + 1) - G n k := by
  cases k with
  | zero => exact telescope_zero n
  | succ k =>
    set K : ℕ := k + 1 with hK_def
    set m : ℤ := n - (K : ℤ)
    have hn : n = m + (K : ℤ) := by omega
    set dm1 : ℤ := b (m - 1) K
    set d0 : ℤ := b m K
    set d1 : ℤ := b (m + 1) K
    set d2 : ℤ := b (m + 2) K
    set d3 : ℤ := b (m + 3) K
    set d4 : ℤ := b (m + 4) K
    have hr0 : (m - (K : ℤ)) * d0 - m * dm1 = 0 := by
      have := b_absorb m K; linarith
    have hr1 : (m + 1 - (K : ℤ)) * d1 - (m + 1) * d0 = 0 := by
      have h := b_absorb (m + 1) K
      rw [show m + 1 - 1 = m by ring] at h
      linarith
    have hr2 : (m + 2 - (K : ℤ)) * d2 - (m + 2) * d1 = 0 := by
      have h := b_absorb (m + 2) K
      rw [show m + 2 - 1 = m + 1 by ring] at h
      linarith
    have hr3 : (m + 3 - (K : ℤ)) * d3 - (m + 3) * d2 = 0 := by
      have h := b_absorb (m + 3) K
      rw [show m + 3 - 1 = m + 2 by ring] at h
      linarith
    have hr4 : (m + 4 - (K : ℤ)) * d4 - (m + 4) * d3 = 0 := by
      have h := b_absorb (m + 4) K
      rw [show m + 4 - 1 = m + 3 by ring] at h
      linarith
    have hc0 : b m k = d1 - d0 := b_pascal m k
    have hc1 : b (m + 1) k = d2 - d1 := by
      have := b_pascal (m + 1) k
      rw [show m + 1 + 1 = m + 2 by ring] at this
      exact this
    have hc2 : b (m + 2) k = d3 - d2 := by
      have := b_pascal (m + 2) k
      rw [show m + 2 + 1 = m + 3 by ring] at this
      exact this
    have hc3 : b (m + 3) k = d4 - d3 := by
      have := b_pascal (m + 3) k
      rw [show m + 3 + 1 = m + 4 by ring] at this
      exact this
    have hL : L n (k + 1) =
        (n + 4) * d4 ^ 2 - (2 * n + 7) * d3 ^ 2 - (n + 3) * d2 ^ 2
        - (2 * n + 5) * d1 ^ 2 + (n + 2) * d0 ^ 2 := by
      simp only [L]
      have e0 : n - ((k + 1 : ℕ) : ℤ) = m := by omega
      have e1 : n + 1 - ((k + 1 : ℕ) : ℤ) = m + 1 := by omega
      have e2 : n + 2 - ((k + 1 : ℕ) : ℤ) = m + 2 := by omega
      have e3 : n + 3 - ((k + 1 : ℕ) : ℤ) = m + 3 := by omega
      have e4 : n + 4 - ((k + 1 : ℕ) : ℤ) = m + 4 := by omega
      rw [e0, e1, e2, e3, e4]
    have hGk : G n (k + 1) =
        (1 - n) * (d1 - d0) * (d3 - d2) - (d1 - d0) * (d2 - d1)
        + (4 + 2 * n) * (d2 - d1) ^ 2 + 2 * n * (d2 - d1) * (d4 - d3)
        - (9 + 3 * n) * (d3 - d2) ^ 2 - 2 * n * (d3 - d2) * (d4 - d3)
        - (4 + n) * (d4 - d3) ^ 2 := by
      dsimp only [G]
      have e0 : n - (k + 1 : ℤ) = m := by omega
      have e1 : n + 1 - (k + 1 : ℤ) = m + 1 := by omega
      have e2 : n + 2 - (k + 1 : ℤ) = m + 2 := by omega
      have e3 : n + 3 - (k + 1 : ℤ) = m + 3 := by omega
      rw [e0, e1, e2, e3, hc0, hc1, hc2, hc3]
    have hGk1 : G n (k + 1 + 1) =
        (1 - n) * dm1 * d1 - dm1 * d0 + (4 + 2 * n) * d0 ^ 2 + 2 * n * d0 * d2
        - (9 + 3 * n) * d1 ^ 2 - 2 * n * d1 * d2 - (4 + n) * d2 ^ 2 := by
      dsimp only [G]
      have e0 : n - (((k + 1 : ℕ) : ℤ) + 1) = m - 1 := by omega
      have e1 : n + 1 - (((k + 1 : ℕ) : ℤ) + 1) = m := by omega
      have e2 : n + 2 - (((k + 1 : ℕ) : ℤ) + 1) = m + 1 := by omega
      have e3 : n + 3 - (((k + 1 : ℕ) : ℤ) + 1) = m + 2 := by omega
      rw [e0, e1, e2, e3]
    rw [hL, hGk1, hGk, hn]
    have hident :
        ((m + (K : ℤ) + 4) * d4 ^ 2 - (2 * (m + (K : ℤ)) + 7) * d3 ^ 2
          - (m + (K : ℤ) + 3) * d2 ^ 2 - (2 * (m + (K : ℤ)) + 5) * d1 ^ 2
          + (m + (K : ℤ) + 2) * d0 ^ 2)
        - (((1 - (m + (K : ℤ))) * dm1 * d1 - dm1 * d0
            + (4 + 2 * (m + (K : ℤ))) * d0 ^ 2 + 2 * (m + (K : ℤ)) * d0 * d2
            - (9 + 3 * (m + (K : ℤ))) * d1 ^ 2 - 2 * (m + (K : ℤ)) * d1 * d2
            - (4 + (m + (K : ℤ))) * d2 ^ 2)
          - ((1 - (m + (K : ℤ))) * (d1 - d0) * (d3 - d2) - (d1 - d0) * (d2 - d1)
            + (4 + 2 * (m + (K : ℤ))) * (d2 - d1) ^ 2
            + 2 * (m + (K : ℤ)) * (d2 - d1) * (d4 - d3)
            - (9 + 3 * (m + (K : ℤ))) * (d3 - d2) ^ 2
            - 2 * (m + (K : ℤ)) * (d3 - d2) * (d4 - d3)
            - (4 + (m + (K : ℤ))) * (d4 - d3) ^ 2))
        = (d0 - 2 * d1) * ((m - (K : ℤ)) * d0 - m * dm1)
          + (- dm1 + 2 * d0 - 3 * d1 + 7 * d2 - 2 * d3) * ((m + 1 - (K : ℤ)) * d1 - (m + 1) * d0)
          + (3 * d0 - 6 * d1 + d2 - 4 * d3 + 4 * d4) * ((m + 2 - (K : ℤ)) * d2 - (m + 2) * d1)
          + (- d0 + d1 + 2 * d2 + 4 * d3 - 8 * d4) * ((m + 3 - (K : ℤ)) * d3 - (m + 3) * d2)
          + (2 * d1 - 8 * d2 + 8 * d3) * ((m + 4 - (K : ℤ)) * d4 - (m + 4) * d3) := by
      ring
    rw [hr0, hr1, hr2, hr3, hr4] at hident
    linarith

private def aa (n : ℤ) : ℤ :=
  if 0 ≤ n then (OMA.S_oeis_a051286.a n.toNat : ℤ) else 0

private lemma aa_neg {n : ℤ} (hn : n < 0) : aa n = 0 := by
  rw [aa, if_neg (not_le.mpr hn)]

private lemma aa_eq_sum (m : ℤ) (N : ℕ) (hN : m < N) :
    aa m = ∑ k ∈ range N, (b (m - k) k) ^ 2 := by
  by_cases hm : 0 ≤ m
  · have hsub : range (m.toNat + 1) ⊆ range N := by
      intro k hk
      simp only [mem_range] at hk ⊢
      omega
    have hzero : ∀ k ∈ range N, k ∉ range (m.toNat + 1) → (b (m - k) k) ^ 2 = 0 := by
      intro k _ hk
      simp only [mem_range, not_lt] at hk
      rw [b_neg (by omega)]
      ring
    rw [← Finset.sum_subset hsub hzero]
    rw [aa, if_pos hm]
    simp only [OMA.S_oeis_a051286.a, Nat.cast_sum, Nat.cast_pow]
    refine Finset.sum_congr rfl fun k hk => ?_
    simp only [mem_range] at hk
    have hmk : 0 ≤ m - (k : ℤ) := by omega
    have htn : (m - (k : ℤ)).toNat = m.toNat - k := by omega
    rw [b_nonneg hmk, htn]
  · rw [aa_neg (not_le.mp hm)]
    symm
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [b_neg (by omega)]
    ring

private lemma G_eq_zero_of_large (n : ℤ) (N : ℕ) (hN : n + 4 ≤ N) : G n N = 0 := by
  cases N with
  | zero => rfl
  | succ N =>
    have h0 : b (n - (N + 1 : ℤ)) N = 0 := b_neg (by omega) N
    have h1 : b (n + 1 - (N + 1 : ℤ)) N = 0 := b_neg (by omega) N
    have h2 : b (n + 2 - (N + 1 : ℤ)) N = 0 := b_neg (by omega) N
    have h3 : b (n + 3 - (N + 1 : ℤ)) N = 0 := b_neg (by omega) N
    dsimp only [G]
    rw [h0, h1, h2, h3]
    ring

private lemma aa_rec (n : ℤ) :
    (n + 4) * aa (n + 4) - (2 * n + 7) * aa (n + 3) - (n + 3) * aa (n + 2)
      - (2 * n + 5) * aa (n + 1) + (n + 2) * aa n = 0 := by
  set N : ℕ := (n + 5).toNat
  have h4 : aa (n + 4) = ∑ k ∈ range N, (b (n + 4 - k) k) ^ 2 := aa_eq_sum (n + 4) N (by omega)
  have h3 : aa (n + 3) = ∑ k ∈ range N, (b (n + 3 - k) k) ^ 2 := aa_eq_sum (n + 3) N (by omega)
  have h2 : aa (n + 2) = ∑ k ∈ range N, (b (n + 2 - k) k) ^ 2 := aa_eq_sum (n + 2) N (by omega)
  have h1 : aa (n + 1) = ∑ k ∈ range N, (b (n + 1 - k) k) ^ 2 := aa_eq_sum (n + 1) N (by omega)
  have h0 : aa n = ∑ k ∈ range N, (b (n - k) k) ^ 2 := aa_eq_sum n N (by omega)
  rw [h4, h3, h2, h1, h0]
  have hcomb :
      (n + 4) * (∑ k ∈ range N, (b (n + 4 - k) k) ^ 2)
      - (2 * n + 7) * (∑ k ∈ range N, (b (n + 3 - k) k) ^ 2)
      - (n + 3) * (∑ k ∈ range N, (b (n + 2 - k) k) ^ 2)
      - (2 * n + 5) * (∑ k ∈ range N, (b (n + 1 - k) k) ^ 2)
      + (n + 2) * (∑ k ∈ range N, (b (n - k) k) ^ 2)
      = ∑ k ∈ range N, L n k := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, L]
  rw [hcomb]
  have htel : ∑ k ∈ range N, L n k = ∑ k ∈ range N, (G n (k + 1) - G n k) :=
    Finset.sum_congr rfl fun k _ => telescope n k
  rw [htel, Finset.sum_range_sub (G n) N, G_eq_zero_of_large n N (by omega)]
  rfl

private lemma coeff_A (m : ℕ) : coeff m OMA.S_oeis_a051286.A = (aa (m : ℤ) : ℚ) := by
  simp [OMA.S_oeis_a051286.A, aa]

private lemma coeff_X_pow_mul_A (r m : ℕ) :
    coeff m (X ^ r * OMA.S_oeis_a051286.A) = (aa ((m : ℤ) - r) : ℚ) := by
  rw [coeff_X_pow_mul']
  split_ifs with h
  · rw [coeff_A]
    have h1 : ((m - r : ℕ) : ℤ) = (m : ℤ) - r := by omega
    rw [h1]
  · rw [aa_neg (by omega), Int.cast_zero]

private lemma coeff_X_pow_mul_deriv_A (r m : ℕ) :
    coeff m (X ^ r * derivative ℚ OMA.S_oeis_a051286.A) =
      ((((m : ℤ) - r + 1) * aa ((m : ℤ) - r + 1) : ℤ) : ℚ) := by
  rw [coeff_X_pow_mul']
  split_ifs with h
  · rw [coeff_derivative, coeff_A]
    have h1 : ((m - r + 1 : ℕ) : ℤ) = (m : ℤ) - r + 1 := by omega
    rw [← h1]
    push_cast
    ring
  · by_cases hlt : (m : ℤ) - r + 1 < 0
    · rw [aa_neg hlt, mul_zero, Int.cast_zero]
    · have heq : (m : ℤ) - r + 1 = 0 := by omega
      rw [heq, zero_mul, Int.cast_zero]

end OMA.S_oeis_a051286_Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a051286.main := by
  open OMA.S_oeis_a051286 OMA.S_oeis_a051286_Proof in
  ext m
  have h1 :
      (1 - C (2 : ℚ) * X - X ^ 2 - C (2 : ℚ) * X ^ 3 + X ^ 4) * derivative ℚ A =
        X ^ 0 * derivative ℚ A
        - C (2 : ℚ) * (X ^ 1 * derivative ℚ A)
        - X ^ 2 * derivative ℚ A
        - C (2 : ℚ) * (X ^ 3 * derivative ℚ A)
        + X ^ 4 * derivative ℚ A := by
    ring
  have h2 :
      (1 + X + C (3 : ℚ) * X ^ 2 - C (2 : ℚ) * X ^ 3) * A =
        X ^ 0 * A
        + X ^ 1 * A
        + C (3 : ℚ) * (X ^ 2 * A)
        - C (2 : ℚ) * (X ^ 3 * A) := by
    ring
  rw [h1, h2]
  simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow_mul_deriv_A, coeff_X_pow_mul_A]
  have hrec := aa_rec ((m : ℤ) - 3)
  have hrecQ :
      ((((m : ℤ) - 3 + 4) * aa ((m : ℤ) - 3 + 4)
        - (2 * ((m : ℤ) - 3) + 7) * aa ((m : ℤ) - 3 + 3)
        - ((m : ℤ) - 3 + 3) * aa ((m : ℤ) - 3 + 2)
        - (2 * ((m : ℤ) - 3) + 5) * aa ((m : ℤ) - 3 + 1)
        + ((m : ℤ) - 3 + 2) * aa ((m : ℤ) - 3) : ℤ) : ℚ) = 0 := by
    exact_mod_cast hrec
  have e4 : (m : ℤ) - 3 + 4 = (m : ℤ) + 1 := by ring
  have e3 : (m : ℤ) - 3 + 3 = (m : ℤ) := by ring
  have e2 : (m : ℤ) - 3 + 2 = (m : ℤ) - 1 := by ring
  have e1 : (m : ℤ) - 3 + 1 = (m : ℤ) - 2 := by ring
  rw [e4, e3, e2, e1] at hrecQ
  have s0 : (m : ℤ) - (0 : ℕ) + 1 = (m : ℤ) + 1 := by ring
  have s1 : (m : ℤ) - (1 : ℕ) + 1 = (m : ℤ) := by ring
  have s2 : (m : ℤ) - (2 : ℕ) + 1 = (m : ℤ) - 1 := by ring
  have s3 : (m : ℤ) - (3 : ℕ) + 1 = (m : ℤ) - 2 := by ring
  have s4 : (m : ℤ) - (4 : ℕ) + 1 = (m : ℤ) - 3 := by ring
  have t0 : (m : ℤ) - (0 : ℕ) = (m : ℤ) := by ring
  have t1 : (m : ℤ) - (1 : ℕ) = (m : ℤ) - 1 := by ring
  have t2 : (m : ℤ) - (2 : ℕ) = (m : ℤ) - 2 := by ring
  have t3 : (m : ℤ) - (3 : ℕ) = (m : ℤ) - 3 := by ring
  rw [s0, s1, s2, s3, s4, t0, t1, t2, t3]
  push_cast at hrecQ ⊢
  linarith
