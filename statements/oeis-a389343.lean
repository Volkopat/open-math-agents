import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Complex.Basic

/-!
# OEIS A389343

Source: https://oeis.org/A389343 (Thomas Hutton)

A colored partition is specified by the multiplicity of each size and color.
At degree n, only sizes and multiplicities at most n contribute to the
formal products. We take coefficients over the complex numbers.
-/

namespace OMA.S_oeis_a389343

def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun m : Fin n → Fin 3 → Fin (n + 1) =>
    (∑ j : Fin n, ∑ c : Fin 3, (j.val + 1) * (m j c).val) = n ∧
    (∑ j : Fin n, ∑ c : Fin 3, c.val * (m j c).val) % 3 = 0)).card

theorem main : ∀ n : ℕ,
    (a n : ℂ) = (1 / 3 : ℂ) * PowerSeries.coeff n
      ((∏ j ∈ Finset.range n, ((1 - (PowerSeries.X : PowerSeries ℂ) ^ (j + 1))⁻¹) ^ 3) +
       2 * (∏ j ∈ Finset.range n, (1 - (PowerSeries.X : PowerSeries ℂ) ^ (3 * (j + 1)))⁻¹)) := by
  sorry

end OMA.S_oeis_a389343
