import OMAStatements.S_mo_304392
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

open OMA.S_mo_304392

private def ceMetric (i j : Fin 3) : ℝ :=
  match i.val, j.val with
  | 0, 0 => 11504
  | 0, 1 => -5740
  | 0, 2 => -2500
  | 1, 0 => -5740
  | 1, 1 => 8039
  | 1, 2 => -7675
  | 2, 0 => -2500
  | 2, 1 => -7675
  | 2, 2 => 20351
  | _, _ => 0

private noncomputable def ceT (i j : Fin 4) : ℝ :=
  match i.val, j.val with
  | 0, 1 => 2 / 3
  | 0, 2 => 2 / 3
  | 0, 3 => 3 / 5
  | 1, 0 => 1 / 3
  | 1, 2 => 1 / 3
  | 1, 3 => 2 / 5
  | 2, 0 => 1 / 3
  | 2, 1 => 2 / 3
  | 2, 3 => 1 / 2
  | 3, 0 => 2 / 5
  | 3, 1 => 3 / 5
  | 3, 2 => 1 / 2
  | _, _ => 0

private def ceNormal (i : Fin 4) (k : Fin 3) : ℝ :=
  match i.val, k.val with
  | 0, 0 => 45
  | 0, 1 => 61
  | 0, 2 => 29
  | 1, 0 => 332
  | 1, 1 => 585
  | 1, 2 => 253
  | 2, 0 => 119
  | 2, 1 => 238
  | 2, 2 => 138
  | 3, 0 => -7210
  | 3, 1 => -10815
  | 3, 2 => -5267
  | _, _ => 0

private def ceOffset (i : Fin 4) : ℝ :=
  match i.val with
  | 0 => 38016
  | 1 => 513216
  | 2 => 342144
  | 3 => -3079296
  | _ => 0

private lemma pairing_ceMetric_expand (x y : Fin 3 → ℝ) :
    pairing ceMetric x y =
      x 0 * (11504 * y 0 + (-5740) * y 1 + (-2500) * y 2) +
      x 1 * ((-5740) * y 0 + 8039 * y 1 + (-7675) * y 2) +
      x 2 * ((-2500) * y 0 + (-7675) * y 1 + 20351 * y 2) := by
  simp only [pairing, Fin.sum_univ_three, ceMetric]
  norm_num
  ring

private lemma vertex_eq_val (i : Fin 4) (k : Fin 3) :
    vertex i k = if k.val = i.val then 1 else 0 := by
  simp only [vertex, Fin.ext_iff, Fin.val_castSucc]

private lemma ceMetric_symm : ∀ j k : Fin 3, ceMetric j k = ceMetric k j := by
  intro j k
  fin_cases j <;> fin_cases k <;> rfl

private lemma ceMetric_pos : ∀ x : Fin 3 → ℝ, x ≠ 0 → 0 < pairing ceMetric x x := by
  intro x hx
  have hsos :
      (20851 : ℝ) * pairing ceMetric x x =
        29 * (2876 * x 0 - 1435 * x 1 - 625 * x 2) ^ 2 +
        128304 * (29 * x 1 - 50 * x 2) ^ 2 +
        92250576 * (x 2) ^ 2 := by
    rw [pairing_ceMetric_expand]
    ring
  by_contra hnot
  have hle : pairing ceMetric x x ≤ 0 := le_of_not_gt hnot
  have h0 : 2876 * x 0 - 1435 * x 1 - 625 * x 2 = 0 := by nlinarith
  have h1 : 29 * x 1 - 50 * x 2 = 0 := by nlinarith
  have h2 : x 2 = 0 := by nlinarith
  apply hx
  funext i
  fin_cases i <;> dsimp [Pi.zero_apply] <;> linarith

private lemma ceT_props :
    ∀ i j : Fin 4, i ≠ j → 0 ≤ ceT i j ∧ ceT i j ≤ 1 ∧ ceT i j + ceT j i = 1 := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    (try exact absurd rfl hij) <;>
    (simp only [ceT]; norm_num)

private lemma ceNormal_ne_zero : ∀ i : Fin 4, ceNormal i ≠ 0 := by
  intro i
  fin_cases i <;>
    (intro h; have h0 := congrFun h 0; simp only [ceNormal, Pi.zero_apply] at h0; norm_num at h0)

private lemma ceHyperplane :
    ∀ i j : Fin 4, i ≠ j →
      pairing ceMetric (ceNormal i) (segmentPoint i j (ceT i j)) = ceOffset i := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    (try exact absurd rfl hij) <;>
    (rw [pairing_ceMetric_expand];
     simp only [segmentPoint, vertex_eq_val, ceT, ceNormal, ceOffset, Fin.isValue];
     norm_num)

private lemma ceReflection :
    ∀ i : Fin 4,
      faceCoordinate i (reflected ceMetric (ceNormal i) (ceOffset i) (vertex i)) = 0 := by
  intro i
  fin_cases i <;>
    (simp only [faceCoordinate, Fin.sum_univ_three, reflected, Fin.isValue];
     rw [pairing_ceMetric_expand, pairing_ceMetric_expand];
     simp only [vertex_eq_val, ceNormal, ceOffset, Fin.isValue];
     norm_num)

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_304392.main) := by
  intro hmain
  have h01 := hmain 3 ceMetric ceMetric_symm ceMetric_pos ceT ceNormal ceOffset
    ceT_props ceNormal_ne_zero ceHyperplane ceReflection 0 1 (by decide)
  simp only [ceT] at h01
  norm_num at h01
