import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Algebra.BigOperators.Fin

/-!
# OEIS A392002

Source: https://oeis.org/A392002 (Thomas Hutton)
Credit: @AShahver

A partition of weight n is specified by its multiplicities for each positive
size and each of the two colours. The coefficient of degree n uses only
sizes and multiplicities at most n, so the products may stop at that size.
-/

namespace OMA.S_oeis_a392002

def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun m : Fin n → Fin 2 → Fin (n + 1) =>
    (∑ j : Fin n, ∑ c : Fin 2, (j.val + 1) * (m j c).val) = n ∧
    (∑ j : Fin n, ∑ c : Fin 2, c.val * (m j c).val) % 2 = 1)).card

theorem main : ∀ n : ℕ,
    (a n : ℚ) = (1 / 2 : ℚ) * PowerSeries.coeff n
      ((∏ j ∈ Finset.range n, ((1 - (PowerSeries.X : PowerSeries ℚ) ^ (j + 1))⁻¹) ^ 2) -
       (∏ j ∈ Finset.range n, (1 - (PowerSeries.X : PowerSeries ℚ) ^ (2 * (j + 1)))⁻¹)) := by
  sorry

end OMA.S_oeis_a392002
