import Mathlib

/-!
# OEIS A387864: indices r with two integers between prime(r) and prime(r+1) having all prime factors < the gap

Source: https://oeis.org/A387864
Credit: @unserus

OEIS: "Erdős (1976) conjectured that there are infinitely many numbers with this
property, but this remains unsolved."

`prime(r)` is the `r`-th prime, 1-indexed, i.e. `Nat.nth Nat.Prime (r - 1)`, so
`prime(r + 1) = Nat.nth Nat.Prime r`. The terms are the `r ≥ 1` such that at
least two integers `n` with `prime(r) < n < prime(r+1)` have all their prime
factors less than `prime(r+1) - prime(r)`. (Example: r = 4, with 8 and 9 between
7 and 11.) The conjecture is that there are infinitely many such `r`.
-/

namespace OMA.S_oeis_a387864

/-- The terms of A387864. -/
def a387864Set : Set ℕ :=
  {r | 1 ≤ r ∧
    2 ≤ ((Finset.Ioo (Nat.nth Nat.Prime (r - 1)) (Nat.nth Nat.Prime r)).filter fun n =>
      ∀ q ∈ n.primeFactors, q < Nat.nth Nat.Prime r - Nat.nth Nat.Prime (r - 1)).card}

/-- A387864 is infinite. -/
theorem main : a387864Set.Infinite := by
  sorry

end OMA.S_oeis_a387864
