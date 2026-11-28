import OMAStatements.S_oeis_a289246
import Mathlib

namespace OMA.S_oeis_a289246

open Finset PowerSeries

private theorem golden_bounds : (3 : ℝ) / 2 < golden ∧ golden < 5 / 3 := by
  have hlow : (2 : ℝ) < Real.sqrt 5 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  have hhigh : Real.sqrt 5 < (7 : ℝ) / 3 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  unfold golden
  constructor <;> linarith

private theorem golden_inv : golden⁻¹ = golden - 1 := by
  apply inv_eq_of_mul_eq_one_right
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  unfold golden
  nlinarith

private theorem weight_floor (k : ℕ) :
    weight k = 2 * ⌊((k : ℝ) + 1) * golden⌋ - ((k : ℤ) + 1) := by
  rw [weight, golden_inv]
  have h : ((k : ℝ) + 1) * (golden - 1) =
      ((k : ℝ) + 1) * golden + (((-((k : ℤ) + 1) : ℤ) : ℝ)) := by
    push_cast
    ring
  rw [h, Int.floor_add_intCast]
  ring

private theorem weight_initial : weight 0 = 1 ∧ weight 1 = 4 ∧ weight 2 = 5 := by
  obtain ⟨hl, hu⟩ := golden_bounds
  have h0 : ⌊golden⌋ = 1 := Int.floor_eq_iff.mpr (by constructor <;> norm_num <;> linarith)
  have h1 : ⌊2 * golden⌋ = 3 := Int.floor_eq_iff.mpr (by constructor <;> norm_num <;> linarith)
  have h2 : ⌊3 * golden⌋ = 4 := Int.floor_eq_iff.mpr (by constructor <;> norm_num <;> linarith)
  simp [weight_floor, h0]
  norm_num [h1, h2]

private theorem weight_difference (k : ℕ) : 1 ≤ weight (k + 1) - weight k ∧
    weight (k + 1) - weight k ≤ 3 := by
  let t : ℝ := ((k : ℝ) + 1) * golden
  obtain ⟨hl, hu⟩ := golden_bounds
  have h1 : ⌊t + 1⌋ ≤ ⌊t + golden⌋ := Int.floor_mono (by linarith)
  have h2 : ⌊t + golden⌋ ≤ ⌊t + 2⌋ := Int.floor_mono (by linarith)
  have hf1 : ⌊t + 1⌋ = ⌊t⌋ + 1 := by exact_mod_cast Int.floor_add_intCast t 1
  have hf2 : ⌊t + 2⌋ = ⌊t⌋ + 2 := by exact_mod_cast Int.floor_add_intCast t 2
  rw [hf1] at h1
  rw [hf2] at h2
  have he : (((k + 1 : ℕ) : ℝ) + 1) * golden = t + golden := by
    dsimp [t]
    push_cast
    ring
  rw [weight_floor, weight_floor, he]
  change 1 ≤ 2 * ⌊t + golden⌋ - ((↑(k + 1) : ℤ) + 1) -
      (2 * ⌊t⌋ - ((k : ℤ) + 1)) ∧
    2 * ⌊t + golden⌋ - ((↑(k + 1) : ℤ) + 1) -
      (2 * ⌊t⌋ - ((k : ℤ) + 1)) ≤ 3
  push_cast
  omega

private noncomputable def polynomial : ℤ⟦X⟧ := 1 + X ^ 1 * C 2 + X ^ 2

private noncomputable def adjusted (n : ℕ) : ℤ := coeff n (denominator * polynomial)

private theorem coeff_polynomial (n : ℕ) :
    coeff n polynomial = (if n = 0 then 1 else 0) +
      (if n = 1 then 1 else 0) * 2 + (if n = 2 then 1 else 0) := by
  simp only [polynomial, map_add, coeff_one, coeff_mul_C, coeff_X_pow]

private theorem adjusted_formula (n : ℕ) :
    adjusted n = (-1 : ℤ) ^ n * weight n +
      (if 1 ≤ n then (-1 : ℤ) ^ (n - 1) * weight (n - 1) else 0) * 2 +
      (if 2 ≤ n then (-1 : ℤ) ^ (n - 2) * weight (n - 2) else 0) := by
  simp only [adjusted, polynomial, mul_add, mul_one, ← mul_assoc, map_add, coeff_mul_C,
    coeff_mul_X_pow', denominator, coeff_mk]

private theorem adjusted_initial : adjusted 0 = 1 ∧ adjusted 1 = -2 ∧ adjusted 2 = -2 := by
  obtain ⟨h0, h1, h2⟩ := weight_initial
  norm_num [adjusted_formula, h0, h1, h2]

private theorem adjusted_le (n : ℕ) (hn : 2 ≤ n) : adjusted n ≤ 2 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  have he : adjusted (2 + k) = (-1 : ℤ) ^ k *
      (weight (k + 2) - 2 * weight (k + 1) + weight k) := by
    rw [show 2 + k = k + 2 by omega, adjusted_formula, if_pos (by omega), if_pos (by omega),
      show k + 2 - 1 = k + 1 by omega, show k + 2 - 2 = k by omega, pow_succ, pow_succ]
    ring
  have h1 := weight_difference k
  have h2 : 1 ≤ weight (k + 2) - weight (k + 1) ∧
      weight (k + 2) - weight (k + 1) ≤ 3 := weight_difference (k + 1)
  rw [he]
  apply (le_abs_self _).trans
  rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_le]
  omega

private theorem coefficient_equation (n : ℕ) :
    (∑ j ∈ range (n + 1), a j * adjusted (n - j)) = coeff n polynomial := by
  obtain ⟨h0, _, _⟩ := weight_initial
  have hc : constantCoeff denominator = (↑(1 : ℤˣ) : ℤ) := by
    norm_num [denominator, h0]
  have hp : generating * (denominator * polynomial) = polynomial := by
    rw [← mul_assoc, generating, invOfUnit_mul _ _ hc, one_mul]
  have hh := congrArg (coeff n) hp
  rw [coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hh
  exact hh

private theorem initial : a 0 = 1 ∧ a 1 = 4 ∧ a 2 = 11 := by
  obtain ⟨b0, b1, b2⟩ := adjusted_initial
  have h0 := coefficient_equation 0
  have h1 := coefficient_equation 1
  have h2 := coefficient_equation 2
  norm_num [Finset.sum_range_succ, coeff_polynomial, b0, b1, b2] at h0 h1 h2
  omega

private theorem growth (n : ℕ) : 0 < a n ∧ (∑ j ∈ range n, a j) ≤ a n ∧
    (∀ m, n = m + 1 → 2 * a m ≤ a n) := by
  obtain ⟨h0, h1, h2⟩ := initial
  induction n using Nat.strong_induction_on with
  | h n ih =>
    obtain (_ | _ | _ | k) := n
    · simp [h0]
    · simp [h0, h1]
    · simp [h0, h1, h2, Finset.sum_range_succ]
    · change 0 < a (k + 3) ∧ (∑ j ∈ range (k + 3), a j) ≤ a (k + 3) ∧
        (∀ m, k + 3 = m + 1 → 2 * a m ≤ a (k + 3))
      obtain ⟨b0, b1, b2⟩ := adjusted_initial
      have hsum := coefficient_equation (k + 3)
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ] at hsum
      simp only [show k + 3 - (k + 3) = 0 by omega, show k + 3 - (k + 2) = 1 by omega,
        show k + 3 - (k + 1) = 2 by omega, b0, b1, b2, mul_one, coeff_polynomial,
        if_neg (show k + 3 ≠ 0 by omega), if_neg (show k + 3 ≠ 1 by omega),
        if_neg (show k + 3 ≠ 2 by omega), zero_mul, add_zero] at hsum
      have hb : (∑ j ∈ range (k + 1), a j * adjusted (k + 3 - j)) ≤
          (∑ j ∈ range (k + 1), a j) * 2 := by
        rw [Finset.sum_mul]
        refine Finset.sum_le_sum fun j hj => ?_
        have hj' := Finset.mem_range.mp hj
        exact mul_le_mul_of_nonneg_left (adjusted_le _ (by omega)) (ih j (by omega)).1.le
      have hc := (ih (k + 1) (by omega)).2.1
      have hd := ih (k + 2) (by omega)
      have hdouble : 2 * a (k + 2) ≤ a (k + 3) := by linarith
      refine ⟨by omega, ?_, ?_⟩
      · rw [Finset.sum_range_succ]
        linarith [hd.2.1]
      · intro m hm
        rw [show m = k + 2 by omega]
        exact hdouble

end OMA.S_oeis_a289246

open OMA.S_oeis_a289246 in
theorem OMA.solution : type_of% @OMA.S_oeis_a289246.main := by
  apply strictMono_nat_of_lt_succ
  intro n
  have hn := (growth n).1
  have hnext := (growth (n + 1)).2.2 n rfl
  omega