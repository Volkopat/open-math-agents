import OMAStatements.S_mo_182345
import Mathlib

open MeasureTheory

open OMA.S_mo_182345



theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_182345.main) := by
  intro h
  let Z : ℝ → ℝ →L[ℝ] ℝ := fun t => Real.exp (-2 * t) • ContinuousLinearMap.id ℝ ℝ
  have hZ (t f : ℝ) : Z t f = Real.exp (-2 * t) * f := by simp [Z]
  have hzero : Z 0 = ContinuousLinearMap.id ℝ ℝ := by simp [Z]
  have hsemigroup (t u : ℝ) (_ : 0 ≤ t) (_ : 0 ≤ u) : Z (t + u) = (Z t).comp (Z u) := by
    apply ContinuousLinearMap.ext
    intro x
    rw [ContinuousLinearMap.comp_apply,hZ,hZ,hZ,show -2 * (t+u) = -2*t + -2*u by ring,Real.exp_add]
    ring
  have hpositive (t : ℝ) (_ : 0 ≤ t) (f : ℝ) (hf : 0 ≤ f) : 0 ≤ Z t f := by
    rw [hZ]
    exact mul_nonneg (Real.exp_pos _).le hf
  let g : ℝ → ℝ := fun s => Real.exp (-2 * (1 - s)) + Real.exp (-2 * (1 + s))
  have hg : Continuous g := by unfold g; fun_prop
  have hEq : (fun s : ℝ => Z (1-s) 1 + Z (1+s) 1) = g := by
    funext s
    simp only [g, hZ, mul_one]
  have hInt : IntervalIntegrable (fun s : ℝ => Z (1-s) 1 + Z (1+s) 1) volume 0 1 :=
    hEq ▸ hg.intervalIntegrable 0 1
  have hBad := h ℝ (fun x y hxy => by simpa only [Real.norm_eq_abs] using hxy)
    Z hzero hsemigroup hpositive 1 zero_le_one hInt
  let B : ℝ → ℝ := fun t => Real.exp (-2*t)
  have hB : Continuous B := by unfold B; fun_prop
  have hMinus : Continuous (fun s : ℝ => B (1-s)) := hB.comp (continuous_const.sub continuous_id)
  have hPlus : Continuous (fun s : ℝ => B (1+s)) := hB.comp (continuous_const.add continuous_id)
  rw [hEq] at hBad
  change 0 ≤ (∫ s in (0 : ℝ)..1, B (1-s) + B (1+s)) - 1 at hBad
  rw [intervalIntegral.integral_add (hMinus.intervalIntegrable 0 1) (hPlus.intervalIntegrable 0 1),
    intervalIntegral.integral_comp_sub_left B 1, intervalIntegral.integral_comp_add_left B 1] at hBad
  norm_num at hBad
  rw [intervalIntegral.integral_add_adjacent_intervals
    (hB.intervalIntegrable 0 1) (hB.intervalIntegrable 1 2)] at hBad
  unfold B at hBad
  rw [intervalIntegral.integral_comp_mul_left Real.exp (by norm_num : (-2 : ℝ) ≠ 0), integral_exp] at hBad
  norm_num at hBad
  linarith [Real.exp_pos (-4)]
