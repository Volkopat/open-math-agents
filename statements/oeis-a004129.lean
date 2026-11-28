import Mathlib.Data.Finset.Card
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.RingTheory.PowerSeries.Basic

namespace OMA.S_oeis_a004129

/-- There exists an `n`-element subset `S ⊆ ℕ` such that every integer in `{1, ..., m}`
is a sum of two distinct elements of `S`. -/
def CoversDistinctTwoSum (n m : ℕ) : Prop :=
  ∃ S : Finset ℕ, S.card = n ∧
    ∀ k : ℕ, 1 ≤ k → k ≤ m → ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ a + b = k

/-- OEIS A004129(n): Largest `m` such that there exists an `n`-subset `S ⊆ ℕ` whose sums of
two distinct elements cover `1, ..., m` (offset 2). -/
noncomputable def A004129 (n : ℕ) : ℕ :=
  sSup { m : ℕ | CoversDistinctTwoSum n m }

/-- Conjecture (Simon Plouffe, 1992; OEIS A004129, offset 2): The ordinary generating function
of `A004129(k + 2)` equals `(z^4 + z^3 + 2*z^2 + 2*z + 1) * (z^2 + z + 1) /
((z - 1) * (z^5 + z^4 + z^3 - z - 1))`, i.e.
`((X - 1) * (X^5 + X^4 + X^3 - X - 1)) * (∑_{k ≥ 0} A004129(k + 2) * X^k) =
(X^4 + X^3 + 2*X^2 + 2*X + 1) * (X^2 + X + 1)` in `ℤ⟦X⟧`. -/
theorem main :
    ((PowerSeries.X - 1) *
        (PowerSeries.X ^ 5 + PowerSeries.X ^ 4 + PowerSeries.X ^ 3 - PowerSeries.X - 1)) *
      PowerSeries.mk (fun k => (A004129 (k + 2) : ℤ)) =
      (PowerSeries.X ^ 4 + PowerSeries.X ^ 3 + PowerSeries.C (2 : ℤ) * PowerSeries.X ^ 2 +
        PowerSeries.C (2 : ℤ) * PowerSeries.X + 1) *
      (PowerSeries.X ^ 2 + PowerSeries.X + 1) := by
  sorry

end OMA.S_oeis_a004129
