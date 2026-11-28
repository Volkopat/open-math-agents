import Mathlib

/-!
# OEIS A399743: Fibonacci numbers as short signed sums from Pascal's triangle

Source: https://oeis.org/A399743
Credit: @gblacher2
-/

namespace OMA.S_oeis_a399743

/-- The positive and negative positions are disjoint, so each position is used at most once.
For a natural number `n`, `(n + 2) / 3` is the ceiling of `n / 3`. -/
theorem main : ∀ n : ℕ, ∃ positive negative : Finset (Fin (n + 1)),
    Disjoint positive negative ∧
      (∑ k ∈ positive, (n.choose k.val : ℤ)) -
        (∑ k ∈ negative, (n.choose k.val : ℤ)) = (Nat.fib n : ℤ) ∧
      positive.card + negative.card ≤ (n + 2) / 3 + 2 := by
  sorry

end OMA.S_oeis_a399743
