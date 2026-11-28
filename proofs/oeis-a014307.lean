import OMAStatements.S_oeis_a014307
import Mathlib

namespace OMA.P_oeis_a014307

open OMA.S_oeis_a014307

private lemma kurkovR_step (m : ℚ) (n k : ℕ) :
    kurkovR m (n + 1) (k + 2) = kurkovR m (n + 1) (k + 1) - kurkovR m n (k + 1) := by
  simp only [kurkovR, Finset.sum_range_succ]
  ring

private lemma kurkovR_one (m : ℚ) (n : ℕ) :
    kurkovR m (n + 1) 1 = m * kurkovR m (n + 1) 0 - kurkovR m n 0 := by
  simp [kurkovR]

private lemma kurkovR_diag (m : ℚ) (n : ℕ) :
    kurkovR m (n + 1) (n + 1) = (m - 1) * kurkovR m (n + 1) 0 := by
  simp only [kurkovR]
  ring

-- Key finite-difference formula: for all k >= 1 and n >= k,
-- R(n, k) = ∑_{j=0}^{k-1} (-1)^j * C(k-1, j) * (m * R(n-j, 0) - R(n-1-j, 0))!
private lemma kurkovR_diff (m : ℚ) :
    ∀ (k : ℕ) (n : ℕ), k + 1 ≤ n →
      kurkovR m n (k + 1) =
        ∑ j ∈ Finset.range (k + 1),
          (-1 : ℚ) ^ j * (Nat.choose k j : ℚ) *
            (m * kurkovR m (n - j) 0 - kurkovR m (n - 1 - j) 0) := by
  intro k
  induction k with
  | zero =>
    intro n hn
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    simp [kurkovR_one]
  | succ k ih =>
    intro n hn
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    rw [kurkovR_step, ih (n' + 1) (by omega), ih n' (by omega)]
    -- Combine via Pascal's identity C(k+1, j) = C(k, j) + C(k, j-1)!
    let f : ℕ → ℚ := fun j => m * kurkovR m (n' + 1 - j) 0 - kurkovR m (n' - j) 0
    have h1 : ∑ j ∈ Finset.range (k + 1), (-1 : ℚ) ^ j * (Nat.choose k j : ℚ) *
          (m * kurkovR m (n' + 1 - j) 0 - kurkovR m (n' + 1 - 1 - j) 0) =
        ∑ j ∈ Finset.range (k + 1), (-1 : ℚ) ^ j * (Nat.choose k j : ℚ) * f j := by
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [f]
    have h2 : ∑ j ∈ Finset.range (k + 1), (-1 : ℚ) ^ j * (Nat.choose k j : ℚ) *
          (m * kurkovR m (n' - j) 0 - kurkovR m (n' - 1 - j) 0) =
        ∑ j ∈ Finset.range (k + 1), (-1 : ℚ) ^ j * (Nat.choose k j : ℚ) * f (j + 1) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [f, show n' + 1 - (j + 1) = n' - j by omega, show n' - (j + 1) = n' - 1 - j by omega]
    have h3 : ∑ j ∈ Finset.range (k + 2), (-1 : ℚ) ^ j * (Nat.choose (k + 1) j : ℚ) *
          (m * kurkovR m (n' + 1 - j) 0 - kurkovR m (n' + 1 - 1 - j) 0) =
        ∑ j ∈ Finset.range (k + 2), (-1 : ℚ) ^ j * (Nat.choose (k + 1) j : ℚ) * f j := by
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [f]
    rw [h1, h2, h3]
    conv_rhs => rw [Finset.sum_range_succ']
    have hsplit : ∑ j ∈ Finset.range (k + 1), (-1 : ℚ) ^ (j + 1) * (Nat.choose (k + 1) (j + 1) : ℚ) * f (j + 1) =
        (∑ j ∈ Finset.range (k + 1), (-1 : ℚ) ^ (j + 1) * (Nat.choose k (j + 1) : ℚ) * f (j + 1)) -
        (∑ j ∈ Finset.range (k + 1), (-1 : ℚ) ^ j * (Nat.choose k j : ℚ) * f (j + 1)) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Nat.choose_succ_succ, Nat.cast_add, pow_succ]
      ring
    rw [hsplit]
    have hshift : (∑ j ∈ Finset.range (k + 1), (-1 : ℚ) ^ (j + 1) * (Nat.choose k (j + 1) : ℚ) * f (j + 1)) +
        (-1 : ℚ) ^ 0 * (Nat.choose (k + 1) 0 : ℚ) * f 0 =
        ∑ j ∈ Finset.range (k + 1), (-1 : ℚ) ^ j * (Nat.choose k j : ℚ) * f j := by
      rw [Finset.sum_range_succ, Nat.choose_eq_zero_of_lt (Nat.lt_succ_self k), Nat.cast_zero,
        mul_zero, zero_mul, add_zero]
      conv_rhs => rw [Finset.sum_range_succ']
      simp only [Nat.choose_zero_right]
    linarith

private lemma deriv_expSeries : PowerSeries.derivative ℚ expSeries = expSeries := by
  ext n
  rw [PowerSeries.coeff_derivative]
  simp only [expSeries, PowerSeries.coeff_mk, Nat.factorial_succ, Nat.cast_mul, mul_inv]
  have hn1 : ((n : ℚ) + 1) ≠ 0 := by positivity
  push_cast
  field_simp [hn1]

private noncomputable def expNegSeries : PowerSeries ℚ :=
  PowerSeries.mk (fun k => (-1 : ℚ) ^ k / (k.factorial : ℚ))

private lemma deriv_expNegSeries : PowerSeries.derivative ℚ expNegSeries = -expNegSeries := by
  ext n
  rw [PowerSeries.coeff_derivative, map_neg]
  simp only [expNegSeries, PowerSeries.coeff_mk, Nat.factorial_succ, Nat.cast_mul, pow_succ]
  have hn1 : ((n : ℚ) + 1) ≠ 0 := by positivity
  push_cast
  field_simp [hn1]

private lemma eq_of_deriv_eq_zero (F : PowerSeries ℚ) (h0 : PowerSeries.coeff 0 F = 0)
    (hd : PowerSeries.derivative ℚ F = 0) : F = 0 := by
  ext n
  cases n with
  | zero => simp [h0]
  | succ n =>
    have hc := congr_arg (PowerSeries.coeff n) hd
    rw [PowerSeries.coeff_derivative, map_zero] at hc
    have hn1 : ((n : ℚ) + 1) ≠ 0 := by positivity
    exact (mul_eq_zero.mp hc).resolve_right hn1

private lemma expSeries_mul_expNegSeries : expSeries * expNegSeries = 1 := by
  have hsub : expSeries * expNegSeries - 1 = 0 := by
    apply eq_of_deriv_eq_zero
    · simp [expSeries, expNegSeries, PowerSeries.coeff_zero_eq_constantCoeff]
    · rw [map_sub, Derivation.map_one_eq_zero, sub_zero, Derivation.leibniz,
        deriv_expSeries, deriv_expNegSeries, smul_eq_mul, smul_eq_mul]
      ring
  exact sub_eq_zero.mp hsub

private theorem main_proved :
    ∀ A : PowerSeries ℚ,
      (∀ n : ℕ, PowerSeries.coeff n A = kurkovR 2 n 0 / (n.factorial : ℚ)) →
      A ^ 2 * (2 - expSeries) = expSeries := by
  intro A hA
  -- Step 1: Prove A' = expNegSeries * (2 * A' - A) by comparing coeff n for all n >= 0!
  have hode1 : PowerSeries.derivative ℚ A = expNegSeries * (2 * PowerSeries.derivative ℚ A - A) := by
    ext n
    have hdiag := kurkovR_diag 2 n
    have hdiff := kurkovR_diff 2 n (n + 1) (le_refl _)
    rw [hdiag] at hdiff
    have hlhs : PowerSeries.coeff n (PowerSeries.derivative ℚ A) =
        kurkovR 2 (n + 1) 0 / (n.factorial : ℚ) := by
      rw [PowerSeries.coeff_derivative, hA (n + 1), Nat.factorial_succ, Nat.cast_mul]
      have hn1 : ((n : ℚ) + 1) ≠ 0 := by positivity
      push_cast
      field_simp [hn1]
    have hrhs : PowerSeries.coeff n (expNegSeries * (2 * PowerSeries.derivative ℚ A - A)) =
        (∑ j ∈ Finset.range (n + 1),
          (-1 : ℚ) ^ j * (Nat.choose n j : ℚ) *
            (2 * kurkovR 2 (n + 1 - j) 0 - kurkovR 2 (n - j) 0)) / (n.factorial : ℚ) := by
      rw [PowerSeries.coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ
          (f := fun i j => PowerSeries.coeff i expNegSeries * PowerSeries.coeff j (2 * PowerSeries.derivative ℚ A - A)),
        Finset.sum_div]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      rw [map_sub, show (2 : PowerSeries ℚ) * PowerSeries.derivative ℚ A =
          PowerSeries.C (2 : ℚ) * PowerSeries.derivative ℚ A by
            rw [show (2 : PowerSeries ℚ) = PowerSeries.C (2 : ℚ) from (map_ofNat PowerSeries.C 2).symm],
        PowerSeries.coeff_C_mul, PowerSeries.coeff_derivative, hA (n - j + 1), hA (n - j)]
      simp only [expNegSeries, PowerSeries.coeff_mk]
      have hsub1 : n + 1 - j = n - j + 1 := by omega
      rw [hsub1]
      have hch : (Nat.choose n j : ℚ) * (j.factorial : ℚ) * ((n - j).factorial : ℚ) = (n.factorial : ℚ) := by
        exact_mod_cast Nat.choose_mul_factorial_mul_factorial hjn
      have hfact_nj : ((n - j + 1).factorial : ℚ) = ((n - j + 1 : ℕ) : ℚ) * ((n - j).factorial : ℚ) := by
        rw [Nat.factorial_succ, Nat.cast_mul]
      have hne_n : (n.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
      have hne_j : (j.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
      have hne_nj : ((n - j).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (n - j))
      have hne_nj1 : ((n - j + 1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)
      rw [hfact_nj]
      have hch_div : (Nat.choose n j : ℚ) / (n.factorial : ℚ) =
          1 / ((j.factorial : ℚ) * ((n - j).factorial : ℚ)) := by
        field_simp [hne_n, hne_j, hne_nj]
        linarith
      calc (-1 : ℚ) ^ j / (j.factorial : ℚ) *
              (2 * (kurkovR 2 (n - j + 1) 0 / (((n - j + 1 : ℕ) : ℚ) * ((n - j).factorial : ℚ)) * ((n - j : ℕ) + 1 : ℚ)) -
                kurkovR 2 (n - j) 0 / ((n - j).factorial : ℚ))
          = (-1 : ℚ) ^ j * (2 * kurkovR 2 (n - j + 1) 0 - kurkovR 2 (n - j) 0) *
              (1 / ((j.factorial : ℚ) * ((n - j).factorial : ℚ))) := by
            have hcast : ((n - j + 1 : ℕ) : ℚ) = ((n - j : ℕ) : ℚ) + 1 := by push_cast; ring
            rw [hcast]
            have hne' : ((n - j : ℕ) : ℚ) + 1 ≠ 0 := by positivity
            field_simp [hne_j, hne_nj, hne']
        _ = (-1 : ℚ) ^ j * (2 * kurkovR 2 (n - j + 1) 0 - kurkovR 2 (n - j) 0) *
              ((Nat.choose n j : ℚ) / (n.factorial : ℚ)) := by rw [← hch_div]
        _ = (-1 : ℚ) ^ j * (Nat.choose n j : ℚ) * (2 * kurkovR 2 (n - j + 1) 0 - kurkovR 2 (n - j) 0) /
              (n.factorial : ℚ) := by ring
    rw [hlhs, hrhs]
    have hdiff' : kurkovR 2 (n + 1) 0 =
        ∑ j ∈ Finset.range (n + 1),
          (-1 : ℚ) ^ j * (Nat.choose n j : ℚ) *
            (2 * kurkovR 2 (n + 1 - j) 0 - kurkovR 2 (n - j) 0) := by
      have h21 : (2 : ℚ) - 1 = 1 := by norm_num
      rw [h21, one_mul] at hdiff
      simpa using hdiff
    rw [hdiff']
  -- Step 2: Multiply by expSeries => (2 - expSeries) * A' = A!
  have hode2 : (2 - expSeries) * PowerSeries.derivative ℚ A = A := by
    have hmul := congr_arg (expSeries * ·) hode1
    rw [← mul_assoc, expSeries_mul_expNegSeries, one_mul] at hmul
    linear_combination -hmul
  -- Step 3: Derivative of (A^2 * (2 - expSeries) * expNegSeries - 1) is 0!
  have hconst : A ^ 2 * (2 - expSeries) * expNegSeries - 1 = 0 := by
    apply eq_of_deriv_eq_zero
    · simp only [map_sub, PowerSeries.coeff_zero_eq_constantCoeff, map_mul, map_pow, map_one,
        show PowerSeries.constantCoeff (2 : PowerSeries ℚ) = 2 from map_ofNat _ 2,
        show PowerSeries.constantCoeff A = 1 by rw [← PowerSeries.coeff_zero_eq_constantCoeff, hA 0]; simp [kurkovR],
        show PowerSeries.constantCoeff expSeries = 1 by rw [← PowerSeries.coeff_zero_eq_constantCoeff]; simp [expSeries],
        show PowerSeries.constantCoeff expNegSeries = 1 by rw [← PowerSeries.coeff_zero_eq_constantCoeff]; simp [expNegSeries]]
      norm_num
    · rw [map_sub, Derivation.map_one_eq_zero, sub_zero, Derivation.leibniz, Derivation.leibniz,
        PowerSeries.derivative_pow, map_sub, deriv_expSeries,
        deriv_expNegSeries, smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul]
      have hd2 : PowerSeries.derivative ℚ (2 : PowerSeries ℚ) = 0 := by
        rw [show (2 : PowerSeries ℚ) = PowerSeries.C (2 : ℚ) from (map_ofNat PowerSeries.C 2).symm,
          PowerSeries.derivative_C]
      rw [hd2, zero_sub]
      calc A ^ 2 * (2 - expSeries) * -expNegSeries +
              expNegSeries * (A ^ 2 * -expSeries + (2 - expSeries) * ((2 : PowerSeries ℚ) * A ^ (2 - 1) * PowerSeries.derivative ℚ A))
          = expNegSeries * A * (2 * ((2 - expSeries) * PowerSeries.derivative ℚ A) - 2 * A) := by
              simp only [show 2 - 1 = 1 by rfl, pow_one]; ring
        _ = expNegSeries * A * (2 * A - 2 * A) := by rw [hode2]
        _ = 0 := by ring
  have h1 : A ^ 2 * (2 - expSeries) * expNegSeries = 1 := sub_eq_zero.mp hconst
  have h2 := congr_arg (· * expSeries) h1
  rw [mul_assoc, mul_comm expNegSeries expSeries, expSeries_mul_expNegSeries, mul_one, one_mul] at h2
  exact h2

end OMA.P_oeis_a014307

theorem OMA.solution : type_of% @OMA.S_oeis_a014307.main :=
  OMA.P_oeis_a014307.main_proved
