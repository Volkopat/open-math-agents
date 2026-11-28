import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.RingTheory.PowerSeries.WellKnown

/-! Source: https://oeis.org/A005867 -/

open scoped BigOperators

namespace OMA.S_oeis_a005867

noncomputable def primePrefix (n : ℕ) : ℕ :=
  ∏ i ∈ Finset.range n, Nat.nth Nat.Prime i

noncomputable def period (n : ℕ) : ℕ :=
  ∏ i ∈ Finset.range n, (Nat.nth Nat.Prime i - 1)

/-- The enumerated positive rough numbers, with the common factor X removed from the series.
At n = 0, these are all positive integers, as in the listed sequence A000027. -/
noncomputable def roughSeries (n : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk fun k => (Nat.nth (fun m => 0 < m ∧ m.Coprime (primePrefix n)) k : ℤ)

theorem main :
    ∀ n : ℕ, ∃ P : Polynomial ℤ,
      P.natDegree = period n ∧
      (∀ i ≤ period n, P.coeff i = P.coeff (period n - i)) ∧
      (1 - PowerSeries.X) * (1 - PowerSeries.X ^ period n) * roughSeries n =
        (P : PowerSeries ℤ) := by
  sorry

end OMA.S_oeis_a005867
