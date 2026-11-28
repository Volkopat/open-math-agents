import OMAStatements.S_mo_67775
import Mathlib.Tactic.Ring

/-!
# Moment-curve counterexample

Retains @Genbox's proof from PR #27062. The registered statement and earlier
moment-curve formalization are credited to @etaubman (statement PR #21164).
Injectivity and its non-equality consequences use the standard function APIs.
-/

open OMA.S_mo_67775

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_67775.main) := by
  intro h
  let t (i : Fin 6) : ℤ := i.val
  let u (i : Fin 6) : Fin 3 → ℤ := ![1, t i, t i ^ 2]
  have hinj : Function.Injective t := Nat.cast_injective.comp Fin.val_injective
  have hpos : GeneralPosition u := by
    intro i j k hij hik hjk
    have hdet : (tripleMatrix u i j k).det =
        (t j - t i) * (t k - t i) * (t k - t j) := by
      rw [Matrix.det_fin_three]
      simp [tripleMatrix, u]
      ring
    rw [hdet]
    simpa only [mul_ne_zero_iff, sub_ne_zero, hinj.ne_iff] using
      And.intro (And.intro hij.symm hik.symm) hjk.symm
  apply h u hpos
  apply Matrix.det_zero_of_column_eq (i := 1) (j := 4) (by decide)
  intro i
  simp [quadraticMatrix, quadratic, u]