import OMAStatements.S_oeis_a303647
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination

open OMA.S_oeis_a303647

private noncomputable def q : ℝ := (2 : ℝ) ^ ((1 : ℝ) / 3) - 1

private theorem cube : (q + 1) ^ 3 = 2 := by
  unfold q
  rw [sub_add_cancel, ← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

private theorem q_range : 20 / 77 < q ∧ q < 25 / 96 := by
  have h : 0 ≤ q + 1 := by
    unfold q
    rw [sub_add_cancel]
    positivity
  constructor
  · by_contra! hn
    have hp := pow_le_pow_left₀ h (by linarith : q + 1 ≤ 1 + 20 / 77) 3
    rw [cube] at hp
    norm_num at hp
  · by_contra! hn
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 + 25 / 96)
      (by linarith : 1 + 25 / 96 ≤ q + 1) 3
    rw [cube] at hp
    norm_num at hp

private theorem ratio_range : 96 / 25 < ratio ∧ ratio < 77 / 20 := by
  change 96 / 25 < 1 / q ∧ 1 / q < 77 / 20
  obtain ⟨h₁, h₂⟩ := q_range
  have hq : 0 < q := by linarith
  exact ⟨(lt_div_iff₀ hq).2 (by linarith), (div_lt_iff₀ hq).2 (by linarith)⟩

private theorem ratio_mul_q : ratio * q = 1 := by
  change 1 / q * q = 1
  exact div_mul_cancel₀ _ (ne_of_gt (by linarith [q_range.1] : 0 < q))

private theorem q_poly : q = ratio ^ 2 - 3 * ratio - 3 := by
  have he : ratio + 1 = ratio * (q + 1) := by linarith only [ratio_mul_q, mul_add ratio q 1, mul_one ratio]
  have hc : (ratio + 1) ^ 3 = ratio ^ 3 * 2 := by rw [he, mul_pow, cube]
  apply mul_left_cancel₀ (ne_of_gt (by linarith [ratio_range.1] : 0 < ratio))
  linear_combination ratio_mul_q + hc

-- The index of each model is one less than the index of the rounded sequence.
private def model (v w c : ℤ) : ℕ → ℤ
  | 0 => 1
  | 1 => v
  | 2 => w
  | n + 3 => 3 * model v w c (n + 2) + 3 * model v w c (n + 1) + model v w c n + c

private noncomputable def gap (f : ℕ → ℤ) (n : ℕ) : ℝ := f (n + 1) - ratio * f n

private theorem gap_two (v w c : ℤ) (n : ℕ) :
    gap (model v w c) (n + 2) =
      (3 - ratio) * gap (model v w c) (n + 1) - q * gap (model v w c) n + c := by
  unfold gap
  rw [show model v w c (n + 2 + 1) =
    3 * model v w c (n + 2) + 3 * model v w c (n + 1) + model v w c n + c from model.eq_4 ..]
  push_cast
  linear_combination (model v w c (n + 1) : ℝ) * q_poly - (model v w c n : ℝ) * ratio_mul_q

-- Iterating the second-order error recurrence makes both coefficients positive.
private theorem gap_three (v w c : ℤ) (n : ℕ) :
    gap (model v w c) (n + 3) =
      3 * (4 - ratio) * gap (model v w c) (n + 1) +
      (1 - 3 * q) * gap (model v w c) n + (4 - ratio) * c := by
  rw [gap_two v w c (n + 1), gap_two v w c n]
  linear_combination -gap (model v w c) (n + 1) * q_poly + gap (model v w c) n * ratio_mul_q

private theorem gap_bounds (v w c : ℤ) (l : ℝ)
    (init : ∀ i < 3, l < gap (model v w c) i ∧ gap (model v w c) i < l + 1)
    (low : l ≤ 3 * (4 - ratio) * l + (1 - 3 * q) * l + (4 - ratio) * c)
    (high : 3 * (4 - ratio) * (l + 1) + (1 - 3 * q) * (l + 1) + (4 - ratio) * c ≤ l + 1)
    (n : ℕ) : l < gap (model v w c) n ∧ gap (model v w c) n < l + 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < 3
    · exact init n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' (by omega : 3 ≤ n)
    obtain ⟨h₀, h₁⟩ := ih m (by omega)
    obtain ⟨h₂, h₃⟩ := ih (m + 1) (by omega)
    have hA : 0 < 3 * (4 - ratio) := by linarith [ratio_range.2]
    have hB : 0 < 1 - 3 * q := by linarith [q_range.2]
    rw [gap_three]
    exact ⟨low.trans_lt (add_lt_add_of_lt_of_le (add_lt_add
      (mul_lt_mul_of_pos_left h₂ hA) (mul_lt_mul_of_pos_left h₀ hB)) (le_refl _)),
      (add_lt_add_of_lt_of_le (add_lt_add
      (mul_lt_mul_of_pos_left h₃ hA) (mul_lt_mul_of_pos_left h₁ hB)) (le_refl _)).trans_le high⟩

private abbrev upper := model 5 21 3
private abbrev lower := model 3 11 (-1)

private theorem upper_gap (n : ℕ) : 1 < gap upper n ∧ gap upper n < 1 + 1 := by
  apply gap_bounds
  · intro i hi
    interval_cases i <;> norm_num [gap, upper, model] <;>
      constructor <;> linarith [ratio_range.1, ratio_range.2]
  · norm_num
    linarith [ratio_range.2, q_range.2]
  · norm_num
    linarith [ratio_range.1, q_range.1]

private theorem lower_gap (n : ℕ) : -1 < gap lower n ∧ gap lower n < -1 + 1 := by
  apply gap_bounds
  · intro i hi
    interval_cases i <;> norm_num [gap, lower, model] <;>
      constructor <;> linarith [ratio_range.1, ratio_range.2]
  · norm_num
    linarith [ratio_range.1, q_range.1]
  · norm_num
    linarith [ratio_range.2]

private theorem upper_eq (n : ℕ) : a (n + 1) = upper n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [a, ih, Int.ceil_eq_iff]
    obtain ⟨h₁, h₂⟩ := upper_gap n
    unfold gap at h₁ h₂
    constructor <;> linarith

private theorem lower_eq (n : ℕ) : a301483 (n + 1) = lower n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [a301483, ih, Int.floor_eq_iff]
    obtain ⟨h₁, h₂⟩ := lower_gap n
    unfold gap at h₁ h₂
    constructor <;> linarith

private theorem model_four (v w c : ℤ) (n : ℕ) :
    model v w c (n + 4) = 4 * model v w c (n + 3) -
      2 * model v w c (n + 1) - model v w c n := by
  linarith only [model.eq_4 v w c (n + 1), model.eq_4 v w c n]

private theorem companion (n : ℕ) :
    upper (n + 2) = lower (n + 4) - a195350 (n + 5) + a195339 n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < 4
    · interval_cases n <;> decide
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' (by omega : 4 ≤ n)
    linarith only [ih m (by omega), ih (m + 1) (by omega), ih (m + 3) (by omega),
      model_four 5 21 3 (m + 2), model_four 3 11 (-1) (m + 4),
      a195350.eq_5 (m + 5), a195339.eq_5 m]

private theorem barker (n : ℕ) : a (n + 5) = 4 * a (n + 4) - 2 * a (n + 2) - a (n + 1) := by
  simpa only [upper_eq] using model_four 5 21 3 n

open PowerSeries in
private theorem generating :
    (1 - X) * (1 - 3 * X - 3 * X ^ 2 - X ^ 3) * mk a =
      X * (1 + X + X ^ 2) := by
  let f := mk a
  have hL : (1 - X) * (1 - 3 * X - 3 * X ^ 2 - X ^ 3) * f =
      f - (4 • f - ((2 • f + f * X) * X) * X) * X := by
    simp only [nsmul_eq_mul]
    ring
  have hR : (X : ℤ⟦X⟧) * (1 + X + X ^ 2) = X + X ^ 2 + X ^ 3 := by ring
  rw [hL, hR]
  apply PowerSeries.ext
  intro n
  by_cases hn : n < 5
  · interval_cases n <;>
      simp only [map_sub, map_add, map_nsmul, coeff_succ_mul_X, coeff_zero_mul_X,
        f, coeff_mk, coeff_X, coeff_X_pow] <;>
      norm_num [upper_eq, upper, model, a.eq_1]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' (by omega : 5 ≤ n)
  simp only [map_sub, map_add, map_nsmul, coeff_succ_mul_X, f, coeff_mk, coeff_X, coeff_X_pow]
  simp [show m + 5 ≠ 1 by omega, show m + 5 ≠ 2 by omega, show m + 5 ≠ 3 by omega]
  linarith only [barker m]

theorem OMA.solution : type_of% @OMA.S_oeis_a303647.main := by
  refine ⟨?_, generating, ?_⟩
  · intro n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' (by omega : 3 ≤ n)
    rw [Nat.add_sub_cancel, upper_eq, lower_eq]
    exact companion m
  · intro n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' (by omega : 5 ≤ n)
    rw [show m + 5 - 1 = m + 4 by omega, show m + 5 - 3 = m + 2 by omega,
      show m + 5 - 4 = m + 1 by omega]
    exact barker m
