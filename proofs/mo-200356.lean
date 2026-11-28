import OMAStatements.S_mo_200356
import Mathlib

/-!
# MathOverflow 200356: the total variation of a product is not a function of that of the factors

Retains the counterexample and two-point formulas of @rexmhall09, PR #30824.
Statement: @koolkao, PR #29393, following Aryeh Kontorovich’s answer.
The direct arithmetic normalization was compared with @koolkao #34351 and @Genbox #33018.

Take `k = 2` and `n = 2`.  The pairs

* `P = (1/2, 1/2)`, `Q = (3/5, 2/5)` and
* `P' = (1/10, 9/10)`, `Q' = (1/5, 4/5)`

both have total variation distance `1/10`, but the two-fold products have distances `11/100` and
`17/100` respectively.  So no function `φ` of `(k, n, tv)` can give both values.
-/

namespace OMA.S_mo_200356

/-- Total variation on two points. -/
lemma tv_two (P Q : Fin 2 → ℝ) : tv P Q = (|P 0 - Q 0| + |P 1 - Q 1|) / 2 := by
  unfold tv
  rw [Fin.sum_univ_two]

/-- Total variation of the two-fold products on two points. -/
lemma tv_prod_two (P Q : Fin 2 → ℝ) : tv (prodDist 2 P) (prodDist 2 Q) =
    (|P 0 * P 0 - Q 0 * Q 0| + |P 0 * P 1 - Q 0 * Q 1| + |P 1 * P 0 - Q 1 * Q 0| +
      |P 1 * P 1 - Q 1 * Q 1|) / 2 := by
  unfold tv prodDist
  rw [← (finTwoArrowEquiv (Fin 2)).symm.sum_comp, Fintype.sum_prod_type]
  simp [Fin.sum_univ_two, Fin.prod_univ_two, finTwoArrowEquiv]
  ring

end OMA.S_mo_200356

open OMA.S_mo_200356 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_200356.main) := by
  rintro ⟨φ, h⟩
  have h1 := h 2 2 ![1 / 2, 1 / 2] ![3 / 5, 2 / 5]
    (by norm_num [IsDist, Fin.forall_fin_two, Fin.sum_univ_two])
    (by norm_num [IsDist, Fin.forall_fin_two, Fin.sum_univ_two])
  have h2 := h 2 2 ![1 / 10, 9 / 10] ![1 / 5, 4 / 5]
    (by norm_num [IsDist, Fin.forall_fin_two, Fin.sum_univ_two])
    (by norm_num [IsDist, Fin.forall_fin_two, Fin.sum_univ_two])
  norm_num [tv_prod_two, tv_two] at h1 h2
  linarith
