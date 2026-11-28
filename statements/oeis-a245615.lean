import Mathlib

/-!
# Nonnegativity of a rarefied binary digit sum

Source: https://oeis.org/A245615.

Vladimir Shevelev (2014) sums over j>11 whose least prime factor is 11,
ending at eleven times the n-th prime. The first index of the entry is n=5.
The sum of the binary digits gives the Hamming weight.
-/

namespace OMA.S_oeis_a245615

/-- The signed sum through an arbitrary cutoff. -/
def rareSum (N : ℕ) : ℤ :=
  ∑ j ∈ Finset.Ioc 11 N with j.minFac=11, (-1:ℤ)^((Nat.digits 2 j).sum+1)

/-- The OEIS index uses 2 as the first prime. -/
noncomputable def a (n : ℕ) : ℤ := rareSum (11 * Nat.nth Nat.Prime (n-1))

theorem main : ∀ n : ℕ, 5 ≤ n → 0 ≤ a n := by
  sorry

end OMA.S_oeis_a245615
