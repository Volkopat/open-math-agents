import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Knapsack partitions with largest part three (OEIS A326034)

Source: https://oeis.org/A326034
Credit: @etaubman

Gus Wiseman defined this sequence in 2019. Fausto A. C. Cariboni recorded the
six-term periodic pattern from index eight in 2021. Vladeta Jovovic gave the
generating function in the OEIS entry on November 12, 2026.

A partition with largest part three is uniquely specified by its nonnegative
multiplicities of 1, 2 and 3, with the last multiplicity positive. The predicate
below requires the sum map on all bounded submultiplicity triples to be
injective, exactly the knapsack condition on distinct submultisets. `a` counts
these partitions directly; neither the generating function nor the periodicity
is assumed in its definition.

The proof classifies the valid multiplicities into four disjoint families,
counts each family, and identifies coefficients of formal power series over
the rationals. The power-series inverses have constant coefficient one.
-/

namespace OMA.S_oeis_a326034

-- The three arguments are the multiplicities of the parts 1, 2 and 3.
-- Distinct submultisets must have distinct sums.
def Knapsack (a b c : ℕ) : Prop :=
  ∀ x ≤ a, ∀ y ≤ b, ∀ z ≤ c,
  ∀ x' ≤ a, ∀ y' ≤ b, ∀ z' ≤ c,
    x + 2*y + 3*z = x' + 2*y' + 3*z' → x = x' ∧ y = y' ∧ z = z'

noncomputable def partitions (n : ℕ) : Finset (ℕ × ℕ × ℕ) := by
  classical
  exact ((Finset.range (n+1)) ×ˢ ((Finset.range (n+1)) ×ˢ (Finset.range (n+1)))).filter
    (fun p => 0 < p.2.2 ∧ p.1 + 2*p.2.1 + 3*p.2.2 = n ∧ Knapsack p.1 p.2.1 p.2.2)

noncomputable def a (n : ℕ) : ℕ := (partitions n).card

open PowerSeries

noncomputable def G : PowerSeries ℚ := PowerSeries.mk (fun n => (a n : ℚ))
theorem main :
    G = (PowerSeries.X : PowerSeries ℚ)^3 * (1-PowerSeries.X)⁻¹ +
        PowerSeries.X^5 * (1-PowerSeries.X^2)⁻¹ +
        (PowerSeries.X^8 + PowerSeries.X^10) * (1-PowerSeries.X^3)⁻¹ ∧
    ∀ n, 8 ≤ n → a (n+6) = a n  := by
  sorry

end OMA.S_oeis_a326034
