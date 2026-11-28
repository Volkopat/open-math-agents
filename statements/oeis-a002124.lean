import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Set.Card
import Mathlib.RingTheory.PowerSeries.Basic

namespace OMA.S_oeis_a002124

/-- A composition of `n` into odd primes is a list of odd primes whose sum is `n`. -/
def IsOddPrimeComp (n : ℕ) (l : List ℕ) : Prop :=
  l.sum = n ∧ ∀ p ∈ l, Nat.Prime p ∧ p % 2 = 1

/-- OEIS A002124(n): Number of compositions of `n` into odd primes. -/
noncomputable def A002124 (n : ℕ) : ℕ :=
  Set.ncard { l : List ℕ | IsOddPrimeComp n l }

/-- Conjecture (Simon Plouffe, 1992; OEIS A002124): The ordinary generating function of
`A002124(n)` equals `-(z-1)*(z+1)*(z^2+z+1)*(z^2-z+1) / (1 - z^3 - z^5 - z^6 - z^7 + z^9)`,
i.e. `(1 - X^3 - X^5 - X^6 - X^7 + X^9) * (∑_{n ≥ 0} A002124(n) * X^n) =
-(X - 1) * (X + 1) * (X^2 + X + 1) * (X^2 - X + 1)` in `ℤ⟦X⟧`. -/
theorem main :
    (1 - PowerSeries.X ^ 3 - PowerSeries.X ^ 5 - PowerSeries.X ^ 6 - PowerSeries.X ^ 7 +
        PowerSeries.X ^ 9) *
      PowerSeries.mk (fun n => (A002124 n : ℤ)) =
      -(PowerSeries.X - 1) * (PowerSeries.X + 1) * (PowerSeries.X ^ 2 + PowerSeries.X + 1) *
        (PowerSeries.X ^ 2 - PowerSeries.X + 1) := by
  sorry

end OMA.S_oeis_a002124
