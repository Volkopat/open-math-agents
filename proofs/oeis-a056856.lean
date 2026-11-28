import OMAStatements.S_oeis_a056856
import Mathlib

/-!
# A056856 from A130534: substituting `X ↦ n X`

The product `∏ (j + n X)` is obtained from `∏ (j + X)` by the substitution `X ↦ n X`, and that
substitution multiplies the coefficient of `X ^ m` by `n ^ m`.
-/

open Polynomial in
theorem OMA.solution : type_of% @OMA.S_oeis_a056856.main := by
  intro n k _ _
  unfold OMA.S_oeis_a056856.a056856 OMA.S_oeis_a056856.a130534
  have h : (∏ j ∈ Finset.Icc 1 (n - 1), (C j + C n * X : ℕ[X])) =
      (∏ j ∈ Finset.Icc 1 (n - 1), (C j + X : ℕ[X])).comp (C n * X) := by
    rw [Polynomial.prod_comp]
    refine Finset.prod_congr rfl fun j _ => ?_
    simp
  rw [h, Polynomial.comp_C_mul_X_coeff]
