import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.RingTheory.PowerSeries.Basic

open scoped BigOperators

namespace OMA.S_oeis_a002376

/-- `n` can be expressed as a sum of `k` positive integer cubes. -/
def IsSumOfCubes (n k : ℕ) : Prop :=
  ∃ f : Fin k → ℕ, (∀ i, 1 ≤ f i) ∧ ∑ i : Fin k, (f i) ^ 3 = n

/-- OEIS A002376(n): Least number of positive cubes needed to sum to `n` (for `n ≥ 1`). -/
noncomputable def A002376 (n : ℕ) : ℕ :=
  sInf { k : ℕ | IsSumOfCubes n k }

/-- Conjecture (Simon Plouffe, 1992; OEIS A002376, offset 1): The ordinary generating function
of `A002376(k + 1)` equals `-(-1 - z - z^2 - z^3 - z^4 - z^5 - z^6 + 6*z^7) /
((z + 1) * (z^2 + 1) * (z^4 + 1) * (z - 1)^2)`, i.e.
`((X + 1) * (X^2 + 1) * (X^4 + 1) * (X - 1)^2) * (∑_{k ≥ 0} A002376(k + 1) * X^k) =
-(-1 - X - X^2 - X^3 - X^4 - X^5 - X^6 + 6*X^7)` in `ℤ⟦X⟧`. -/
theorem main :
    ((PowerSeries.X + 1) * (PowerSeries.X ^ 2 + 1) * (PowerSeries.X ^ 4 + 1) *
        (PowerSeries.X - 1) ^ 2) *
      PowerSeries.mk (fun k => (A002376 (k + 1) : ℤ)) =
      -(-1 - PowerSeries.X - PowerSeries.X ^ 2 - PowerSeries.X ^ 3 - PowerSeries.X ^ 4 -
        PowerSeries.X ^ 5 - PowerSeries.X ^ 6 + PowerSeries.C (6 : ℤ) * PowerSeries.X ^ 7) := by
  sorry

end OMA.S_oeis_a002376
