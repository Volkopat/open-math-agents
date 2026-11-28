import OMAStatements.S_oeis_a288234
import Mathlib

namespace OMA.S_oeis_a288234

open Finset PowerSeries

private noncomputable def ratio : ℝ := -1 + Real.sqrt 7

private noncomputable def seq (n : ℕ) : ℚ := a ratio n

private theorem ratio_bounds : (41 : ℝ) / 25 < ratio ∧ ratio < 5 / 3 := by
  have hl : (66 : ℝ) / 25 < Real.sqrt 7 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  have hu : Real.sqrt 7 < (8 : ℝ) / 3 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  unfold ratio
  constructor <;> linarith

private theorem weight_increments (k : ℕ) :
    1 ≤ weight ratio (k + 1) - weight ratio k ∧ weight ratio (k + 1) - weight ratio k ≤ 2 := by
  let t := ((k : ℝ) + 1) * ratio
  obtain ⟨hl, hu⟩ := ratio_bounds
  have h1 : ⌊t + 1⌋ ≤ ⌊t + ratio⌋ := Int.floor_mono (by linarith)
  have h2 : ⌊t + ratio⌋ ≤ ⌊t + 2⌋ := Int.floor_mono (by linarith)
  have hfloor1 : ⌊t + 1⌋ = ⌊t⌋ + 1 := by exact_mod_cast Int.floor_add_intCast t 1
  have hfloor2 : ⌊t + 2⌋ = ⌊t⌋ + 2 := by exact_mod_cast Int.floor_add_intCast t 2
  rw [hfloor1] at h1
  rw [hfloor2] at h2
  have he : (((k + 1 : ℕ) : ℝ) + 1) * ratio = t + ratio := by
    dsimp [t]
    push_cast
    ring
  simp only [weight, he]
  change 1 ≤ (⌊t + ratio⌋ : ℚ) - (⌊t⌋ : ℚ) ∧ (⌊t + ratio⌋ : ℚ) - (⌊t⌋ : ℚ) ≤ 2
  have hb1 : (⌊t⌋ : ℚ) + 1 ≤ (⌊t + ratio⌋ : ℚ) := by exact_mod_cast h1
  have hb2 : (⌊t + ratio⌋ : ℚ) ≤ (⌊t⌋ : ℚ) + 2 := by exact_mod_cast h2
  constructor <;> linarith

private theorem initial_weight :
    weight ratio 0 = 1 ∧
    weight ratio 1 = 3 ∧
    weight ratio 2 = 4 ∧
    weight ratio 3 = 6 ∧
    weight ratio 4 = 8 ∧
    weight ratio 5 = 9 ∧
    weight ratio 6 = 11 ∧
    weight ratio 7 = 13 ∧
    weight ratio 8 = 14 ∧
    weight ratio 9 = 16 ∧
    weight ratio 10 = 18 ∧
    weight ratio 11 = 19 ∧
    weight ratio 12 = 21 := by
  obtain ⟨hl, hu⟩ := ratio_bounds
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h : ⌊ratio⌋ = (1 : ℤ) :=
      Int.floor_eq_iff.mpr (by constructor <;> norm_num <;> linarith)
    norm_num [weight, h]
  · have h : ⌊(2 : ℝ) * ratio⌋ = (3 : ℤ) :=
      Int.floor_eq_iff.mpr (by constructor <;> norm_num <;> linarith)
    norm_num [weight, h]
  · have h : ⌊(3 : ℝ) * ratio⌋ = (4 : ℤ) :=
      Int.floor_eq_iff.mpr (by constructor <;> norm_num <;> linarith)
    norm_num [weight, h]
  · have h : ⌊(4 : ℝ) * ratio⌋ = (6 : ℤ) :=
      Int.floor_eq_iff.mpr (by constructor <;> norm_num <;> linarith)
    norm_num [weight, h]
  · have h : ⌊(5 : ℝ) * ratio⌋ = (8 : ℤ) :=
      Int.floor_eq_iff.mpr (by constructor <;> norm_num <;> linarith)
    norm_num [weight, h]
  · have h : ⌊(6 : ℝ) * ratio⌋ = (9 : ℤ) :=
      Int.floor_eq_iff.mpr (by constructor <;> norm_num <;> linarith)
    norm_num [weight, h]
  · have h : ⌊(7 : ℝ) * ratio⌋ = (11 : ℤ) :=
      Int.floor_eq_iff.mpr (by constructor <;> norm_num <;> linarith)
    norm_num [weight, h]
  · have h : ⌊(8 : ℝ) * ratio⌋ = (13 : ℤ) :=
      Int.floor_eq_iff.mpr (by constructor <;> norm_num <;> linarith)
    norm_num [weight, h]
  · have h : ⌊(9 : ℝ) * ratio⌋ = (14 : ℤ) :=
      Int.floor_eq_iff.mpr (by constructor <;> norm_num <;> linarith)
    norm_num [weight, h]
  · have h : ⌊(10 : ℝ) * ratio⌋ = (16 : ℤ) :=
      Int.floor_eq_iff.mpr (by constructor <;> norm_num <;> linarith)
    norm_num [weight, h]
  · have h : ⌊(11 : ℝ) * ratio⌋ = (18 : ℤ) :=
      Int.floor_eq_iff.mpr (by constructor <;> norm_num <;> linarith)
    norm_num [weight, h]
  · have h : ⌊(12 : ℝ) * ratio⌋ = (19 : ℤ) :=
      Int.floor_eq_iff.mpr (by constructor <;> norm_num <;> linarith)
    norm_num [weight, h]
  · have h : ⌊(13 : ℝ) * ratio⌋ = (21 : ℤ) :=
      Int.floor_eq_iff.mpr (by constructor <;> norm_num <;> linarith)
    norm_num [weight, h]

private noncomputable def polynomial : ℚ⟦X⟧ := 1 + X ^ 1 * C 2 + X ^ 2

private noncomputable def adjusted (n : ℕ) : ℚ := coeff n (denominator ratio * polynomial)

private theorem coeff_polynomial (n : ℕ) :
    coeff n polynomial = (if n = 0 then 1 else 0) +
      (if n = 1 then 1 else 0) * 2 + (if n = 2 then 1 else 0) := by
  simp only [polynomial, map_add, coeff_one, coeff_mul_C, coeff_X_pow]

private theorem adjusted_formula (n : ℕ) :
    adjusted n = (-1 : ℚ) ^ n * weight ratio n +
      (if 1 ≤ n then (-1 : ℚ) ^ (n - 1) * weight ratio (n - 1) else 0) * 2 +
      (if 2 ≤ n then (-1 : ℚ) ^ (n - 2) * weight ratio (n - 2) else 0) := by
  simp only [adjusted, polynomial, mul_add, mul_one, ← mul_assoc, map_add, coeff_mul_C,
    coeff_mul_X_pow', denominator, coeff_mk]

private theorem adjusted_initial :
    adjusted 0 = 1 ∧
    adjusted 1 = -1 ∧
    adjusted 2 = -1 ∧
    adjusted 3 = -1 ∧
    adjusted 4 = 0 ∧
    adjusted 5 = 1 ∧
    adjusted 6 = 1 ∧
    adjusted 7 = 0 ∧
    adjusted 8 = -1 ∧
    adjusted 9 = -1 ∧
    adjusted 10 = 0 ∧
    adjusted 11 = 1 ∧
    adjusted 12 = 1 := by
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12⟩ := initial_weight
  norm_num [adjusted_formula, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12]

private theorem adjusted_bound (n : ℕ) (hn : 2 ≤ n) : |adjusted n| ≤ 1 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  have he : adjusted (2 + k) = (-1 : ℚ) ^ k *
      (weight ratio (k + 2) - 2 * weight ratio (k + 1) + weight ratio k) := by
    rw [show 2 + k = k + 2 by omega, adjusted_formula, if_pos (by omega), if_pos (by omega),
      show k + 2 - 1 = k + 1 by omega, show k + 2 - 2 = k by omega, pow_succ, pow_succ]
    ring
  have h1 := weight_increments k
  have h2 : 1 ≤ weight ratio (k + 2) - weight ratio (k + 1) ∧
      weight ratio (k + 2) - weight ratio (k + 1) ≤ 2 := weight_increments (k + 1)
  rw [he, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_le]
  constructor <;> linarith

private theorem coefficient_equation (n : ℕ) :
    (∑ j ∈ range (n + 1), seq j * adjusted (n - j)) = coeff n polynomial := by
  obtain ⟨h0, _⟩ := initial_weight
  have hc : constantCoeff (denominator ratio) ≠ 0 := by norm_num [denominator, h0]
  have hp : (denominator ratio)⁻¹ * (denominator ratio * polynomial) = polynomial := by
    rw [← mul_assoc, PowerSeries.inv_mul_cancel _ hc, one_mul]
  have hh := congrArg (coeff n) hp
  rw [coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hh
  exact hh

private theorem initial_seq :
    seq 0 = 1 ∧
    seq 1 = 3 ∧
    seq 2 = 5 ∧
    seq 3 = 9 ∧
    seq 4 = 17 ∧
    seq 5 = 30 ∧
    seq 6 = 52 ∧
    seq 7 = 91 ∧
    seq 8 = 160 ∧
    seq 9 = 281 ∧
    seq 10 = 493 ∧
    seq 11 = 865 ∧
    seq 12 = 1518 := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12⟩ := adjusted_initial
  have h0 : seq 0 = 1 := by
    have he := coefficient_equation 0
    norm_num [Finset.sum_range_succ, coeff_polynomial, b0] at he
    exact he
  have h1 : seq 1 = 3 := by
    have he := coefficient_equation 1
    norm_num [Finset.sum_range_succ, coeff_polynomial, b0, b1, h0] at he
    linarith
  have h2 : seq 2 = 5 := by
    have he := coefficient_equation 2
    norm_num [Finset.sum_range_succ, coeff_polynomial, b0, b1, b2, h0, h1] at he
    linarith
  have h3 : seq 3 = 9 := by
    have he := coefficient_equation 3
    norm_num [Finset.sum_range_succ, coeff_polynomial, b0, b1, b2, b3, h0, h1, h2] at he
    linarith
  have h4 : seq 4 = 17 := by
    have he := coefficient_equation 4
    norm_num [Finset.sum_range_succ, coeff_polynomial, b0, b1, b2, b3, b4, h0, h1, h2, h3] at he
    linarith
  have h5 : seq 5 = 30 := by
    have he := coefficient_equation 5
    norm_num [Finset.sum_range_succ, coeff_polynomial, b0, b1, b2, b3, b4, b5, h0, h1, h2, h3, h4] at he
    linarith
  have h6 : seq 6 = 52 := by
    have he := coefficient_equation 6
    norm_num [Finset.sum_range_succ, coeff_polynomial, b0, b1, b2, b3, b4, b5, b6, h0, h1, h2, h3, h4, h5] at he
    linarith
  have h7 : seq 7 = 91 := by
    have he := coefficient_equation 7
    norm_num [Finset.sum_range_succ, coeff_polynomial, b0, b1, b2, b3, b4, b5, b6, b7, h0, h1, h2, h3, h4, h5, h6] at he
    linarith
  have h8 : seq 8 = 160 := by
    have he := coefficient_equation 8
    norm_num [Finset.sum_range_succ, coeff_polynomial, b0, b1, b2, b3, b4, b5, b6, b7, b8, h0, h1, h2, h3, h4, h5, h6, h7] at he
    linarith
  have h9 : seq 9 = 281 := by
    have he := coefficient_equation 9
    norm_num [Finset.sum_range_succ, coeff_polynomial, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, h0, h1, h2, h3, h4, h5, h6, h7, h8] at he
    linarith
  have h10 : seq 10 = 493 := by
    have he := coefficient_equation 10
    norm_num [Finset.sum_range_succ, coeff_polynomial, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9] at he
    linarith
  have h11 : seq 11 = 865 := by
    have he := coefficient_equation 11
    norm_num [Finset.sum_range_succ, coeff_polynomial, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10] at he
    linarith
  have h12 : seq 12 = 1518 := by
    have he := coefficient_equation 12
    norm_num [Finset.sum_range_succ, coeff_polynomial, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11] at he
    linarith
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩

private noncomputable def tailSum (m : ℕ) : ℚ :=
  ∑ j ∈ range (m + 1), seq j * adjusted (m + 13 - j)

private theorem recent_terms (m : ℕ) :
    seq (m + 13) =
      seq (m + 12) + seq (m + 11) + seq (m + 10) - seq (m + 8) - seq (m + 7) +
        seq (m + 5) + seq (m + 4) - seq (m + 2) - seq (m + 1) - tailSum m := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12⟩ := adjusted_initial
  have h := coefficient_equation (m + 13)
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ] at h
  simp only [
    show m + 13 - (m + 1) = 12 by omega,
    show m + 13 - (m + 2) = 11 by omega,
    show m + 13 - (m + 3) = 10 by omega,
    show m + 13 - (m + 4) = 9 by omega,
    show m + 13 - (m + 5) = 8 by omega,
    show m + 13 - (m + 6) = 7 by omega,
    show m + 13 - (m + 7) = 6 by omega,
    show m + 13 - (m + 8) = 5 by omega,
    show m + 13 - (m + 9) = 4 by omega,
    show m + 13 - (m + 10) = 3 by omega,
    show m + 13 - (m + 11) = 2 by omega,
    show m + 13 - (m + 12) = 1 by omega,
    show m + 13 - (m + 13) = 0 by omega,
    b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, mul_one, mul_zero, mul_neg, add_zero,
    coeff_polynomial, if_neg (show m + 13 ≠ 0 by omega), if_neg (show m + 13 ≠ 1 by omega),
    if_neg (show m + 13 ≠ 2 by omega), zero_mul] at h
  unfold tailSum
  linarith only [h]

private theorem tail_estimate (m : ℕ) (hp : ∀ j ≤ m, 0 ≤ seq j) :
    -(∑ j ∈ range (m + 1), seq j) ≤ tailSum m ∧
      tailSum m ≤ ∑ j ∈ range (m + 1), seq j := by
  have hb (j : ℕ) (hj : j ∈ range (m + 1)) :
      -1 ≤ adjusted (m + 13 - j) ∧ adjusted (m + 13 - j) ≤ 1 := by
    have := mem_range.mp hj
    exact abs_le.mp (adjusted_bound _ (by omega))
  unfold tailSum
  constructor
  · rw [← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro j hj
    have hj' := mem_range.mp hj
    simpa using mul_le_mul_of_nonneg_left (hb j hj).1 (hp j (by omega))
  · apply Finset.sum_le_sum
    intro j hj
    have hj' := mem_range.mp hj
    simpa using mul_le_mul_of_nonneg_left (hb j hj).2 (hp j (by omega))

set_option maxHeartbeats 1500000 in
private theorem bounds (n : ℕ) :
    0 < seq n ∧ (∑ j ∈ range (n + 1), seq j) ≤ 3 * seq n ∧
    (∀ k, n = k + 1 → 3 * seq k ≤ 2 * seq n) ∧
    (∀ k, n = k + 3 → seq n ≤ seq (k + 2) + seq (k + 1) + seq k) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n ≤ 12
    · obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := initial_seq
      interval_cases n <;>
        refine ⟨by norm_num [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12],
          by norm_num [Finset.sum_range_succ, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12],
          ?_, ?_⟩ <;>
        intro k hk <;>
        first
        | omega
        | have hkn : k ≤ 12 := by omega
          interval_cases k <;> first | omega | norm_num [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le (show 13 ≤ n by omega)
      rw [show 13 + m = m + 13 by omega] at ih ⊢
      have nonneg (j : ℕ) (hj : j < m + 13) : 0 ≤ seq j := (ih j hj).1.le
      have scale (k d : ℕ) (hd : k + d < m + 13) :
          seq k ≤ ((2 : ℚ) / 3) ^ d * seq (k + d) := by
        induction d with
        | zero => simp
        | succ d haux =>
          have hprev := haux (by omega)
          have hstep := (ih (k + d + 1) (by omega)).2.2.1 (k + d) rfl
          calc
            seq k ≤ ((2 : ℚ) / 3) ^ d * seq (k + d) := hprev
            _ ≤ ((2 : ℚ) / 3) ^ d * (((2 : ℚ) / 3) * seq (k + d + 1)) :=
              mul_le_mul_of_nonneg_left (by linarith only [hstep]) (by positivity)
            _ = _ := by simp only [pow_succ, mul_assoc, Nat.add_assoc]
      have hTail := tail_estimate m (fun j hj => nonneg j (by omega))
      have hPrefix := (ih m (by omega)).2.1
      have hTailU : tailSum m ≤ 3 * seq m := hTail.2.trans hPrefix
      have hTailL : -(3 * seq m) ≤ tailSum m := (neg_le_neg hPrefix).trans hTail.1
      have h58 := scale (m + 5) 3 (by omega)
      have h47 := scale (m + 4) 3 (by omega)
      have h07 := scale m 7 (by omega)
      have h811 := scale (m + 8) 3 (by omega)
      have h710 := scale (m + 7) 3 (by omega)
      have h25 := scale (m + 2) 3 (by omega)
      have h14 := scale (m + 1) 3 (by omega)
      have h9a := scale (m + 9) 1 (by omega)
      have ha11 := scale (m + 10) 1 (by omega)
      have h012 := scale m 12 (by omega)
      norm_num at h58 h47 h07 h811 h710 h25 h14 h9a ha11 h012
      have hPrev := (ih (m + 12) (by omega)).2.2.2 (m + 9) (by omega)
      change seq (m + 12) ≤ seq (m + 11) + seq (m + 10) + seq (m + 9) at hPrev
      have hEq := recent_terms m
      have hLower : 3 * seq (m + 12) ≤ 2 * seq (m + 13) := by
        linarith only [hEq, hTailU, h811, h710, h25, h14, h9a, ha11, h012, hPrev,
          nonneg (m + 5) (by omega), nonneg (m + 4) (by omega), nonneg (m + 12) (by omega)]
      have hUpper : seq (m + 13) ≤ seq (m + 12) + seq (m + 11) + seq (m + 10) := by
        linarith only [hEq, hTailL, h58, h47, h07, nonneg (m + 8) (by omega),
          nonneg (m + 7) (by omega), nonneg (m + 2) (by omega), nonneg (m + 1) (by omega)]
      refine ⟨?_, ?_, ?_, ?_⟩
      · have hpos := (ih (m + 12) (by omega)).1
        linarith only [hLower, hpos]
      · rw [Finset.sum_range_succ]
        have hprev := (ih (m + 12) (by omega)).2.1
        linarith only [hLower, hprev]
      · intro k hk
        have h : k = m + 12 := by omega
        simpa only [h] using hLower
      · intro k hk
        have h : k = m + 10 := by omega
        simpa only [h] using hUpper

end OMA.S_oeis_a288234

open OMA.S_oeis_a288234 in
theorem OMA.solution : type_of% @OMA.S_oeis_a288234.main := by
  change StrictMono seq
  apply strictMono_nat_of_lt_succ
  intro n
  have hpos := (bounds n).1
  have hg := (bounds (n + 1)).2.2.1 n rfl
  linarith only [hpos, hg]