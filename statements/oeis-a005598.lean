import Mathlib

/-!
# OEIS A005598: regions of a Farey fan

Sources: https://oeis.org/A005598 and https://oeis.org/A360042
-/

open scoped BigOperators

namespace OMA.S_oeis_a005598

/-- The open parameter square with the fan lines b + i * m = k removed.
For each i from 1 to n, exactly the integers k from 1 to i give lines
meeting the open square. The two coordinates are slope and intercept. -/
def fanComplement (n : ℕ) : Set (ℝ × ℝ) :=
  {p | 0 < p.1 ∧ p.1 < 1 ∧ 0 < p.2 ∧ p.2 < 1 ∧
    ∀ i k : ℕ, 1 ≤ i → i ≤ n → 1 ≤ k → k ≤ i →
      p.2 + (i : ℝ) * p.1 ≠ (k : ℝ)}

/-- Each region is the connected component of any one of its points. -/
def fanRegions (n : ℕ) : Set (Set (ℝ × ℝ)) :=
  connectedComponentIn (fanComplement n) '' fanComplement n

theorem main : ∀ n : ℕ,
    (fanRegions n).ncard =
      1 + ∑ j ∈ Finset.range n, (n - j) * Nat.totient (j + 1) := by
  sorry

end OMA.S_oeis_a005598
