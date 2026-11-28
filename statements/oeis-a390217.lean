import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Complex.Basic

/-!
# OEIS A390217

Source: https://oeis.org/A390217 (Thomas Hutton)

A colored partition is specified by the multiplicity of each size and color.
At degree n, only sizes and multiplicities at most n contribute to the
formal products. We take coefficients over the complex numbers.
-/

namespace OMA.S_oeis_a390217

def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun m : Fin n → Fin 4 → Fin (n + 1) =>
    (∑ j : Fin n, ∑ c : Fin 4, (j.val + 1) * (m j c).val) = n ∧
    (∑ j : Fin n, ∑ c : Fin 4, c.val * (m j c).val) % 4 = 0)).card

theorem main : ∀ n : ℕ,
    (a n : ℂ) = (1 / 4 : ℂ) * PowerSeries.coeff n
      ((∏ j ∈ Finset.range n, ((1 - (PowerSeries.X : PowerSeries ℂ) ^ (j + 1))⁻¹) ^ 4) +
       (∏ j ∈ Finset.range n, ((1 - (PowerSeries.X : PowerSeries ℂ) ^ (2 * (j + 1)))⁻¹) ^ 2) +
       2 * (∏ j ∈ Finset.range n, (1 - (PowerSeries.X : PowerSeries ℂ) ^ (4 * (j + 1)))⁻¹)) := by
  sorry

end OMA.S_oeis_a390217
