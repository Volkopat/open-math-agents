import OMAStatements.S_mo_343927
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open scoped BigOperators

namespace OMA.SparsePerturbation

open OMA.S_mo_343927

private theorem supported_bound {n : ℕ} (s : Finset (Fin n))
    (v : EuclideanSpace ℝ (Fin n)) : ∑ i ∈ s, |v i| ≤ Real.sqrt (s.card : ℝ) * ‖v‖ := by
  have h := Real.sum_mul_le_sqrt_mul_sqrt s (fun _ => 1) (fun i => |v i|)
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at h
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _))
  rw [EuclideanSpace.norm_eq]
  simp only [Real.norm_eq_abs]
  exact Real.sqrt_le_sqrt
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => sq_nonneg |v i|))

private theorem support_sum {n : ℕ} (v : EuclideanSpace ℝ (Fin n)) :
    (∑ i ∈ support v, |v i|) = oneNorm v := by
  classical
  unfold support oneNorm
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : v i = 0 <;> simp [h]

private theorem triangle_on_support {n : ℕ} (x x₀ : EuclideanSpace ℝ (Fin n)) :
    oneNorm (x-x₀) ≤ oneNorm x - oneNorm x₀ + 2 * (∑ i ∈ support x₀, |(x-x₀) i|) := by
  classical
  unfold oneNorm support
  rw [Finset.sum_filter, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  change |x i - x₀ i| ≤ |x i| - |x₀ i| + 2 * (if x₀ i ≠ 0 then |x i - x₀ i| else 0)
  by_cases h : x₀ i = 0
  · simp [h]
  simp only [h, ne_eq, not_false_eq_true, if_true]
  have ht := abs_add_le (x i) (-(x i-x₀ i))
  rw [abs_neg, show x i + -(x i-x₀ i) = x₀ i by ring] at ht
  linarith only [ht]

theorem bound {n : ℕ} (x x₀ : EuclideanSpace ℝ (Fin n)) (hx : x ≠ 0) (h₀ : x₀ ≠ 0)
    (hne : x ≠ x₀) (hratio : oneNorm x / ‖x‖ ≤ oneNorm x₀ / ‖x₀‖) :
    oneNorm (x-x₀) / ‖x-x₀‖ ≤ 3 * Real.sqrt ((support x₀).card : ℝ) := by
  have hxpos := norm_pos_iff.mpr hx
  have h₀pos := norm_pos_iff.mpr h₀
  have hdiffpos := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  let r := oneNorm x₀ / ‖x₀‖
  let s := support x₀
  have hr₀ : 0 ≤ r :=
    div_nonneg (Finset.sum_nonneg (fun i _ => abs_nonneg (x₀ i))) (norm_nonneg x₀)
  have hr : r ≤ Real.sqrt (s.card : ℝ) := by
    apply (div_le_iff₀ h₀pos).mpr
    rw [← support_sum]
    exact supported_bound s x₀
  have hA : oneNorm x ≤ r * ‖x‖ := (div_le_iff₀ hxpos).mp hratio
  have hB : r * ‖x₀‖ = oneNorm x₀ := div_mul_cancel₀ _ h₀pos.ne'
  have hdiff : oneNorm x - oneNorm x₀ ≤ r * ‖x-x₀‖ := calc
    _ ≤ r * (‖x‖ - ‖x₀‖) := by
      rw [mul_sub, hB]
      exact sub_le_sub_right hA _
    _ ≤ _ := mul_le_mul_of_nonneg_left (norm_sub_norm_le x x₀) hr₀
  apply (div_le_iff₀ hdiffpos).mpr
  calc
    _ ≤ oneNorm x - oneNorm x₀ + 2 * (∑ i ∈ s, |(x-x₀) i|) := triangle_on_support x x₀
    _ ≤ Real.sqrt (s.card : ℝ) * ‖x-x₀‖ + 2 * (Real.sqrt (s.card : ℝ) * ‖x-x₀‖) :=
      add_le_add (hdiff.trans (mul_le_mul_of_nonneg_right hr (norm_nonneg _)))
        (mul_le_mul_of_nonneg_left (supported_bound s (x-x₀)) (by norm_num))
    _ = _ := by
      change _ = 3 * Real.sqrt (s.card : ℝ) * ‖x-x₀‖
      ring

end OMA.SparsePerturbation

theorem OMA.solution : type_of% @OMA.S_mo_343927.main := by
  refine ⟨3, by norm_num, ?_⟩
  intro n x x₀ hx h₀ hne hratio
  exact OMA.SparsePerturbation.bound x x₀ hx h₀ hne hratio