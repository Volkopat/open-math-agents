import Mathlib

/-!
# Near-perfect numbers with more than four distinct prime divisors

Source: qian feng, https://mathoverflow.net/questions/235733.
For a positive integer `n`, the excess of its divisor sum over `2 * n`
must be a positive proper divisor of `n`.
-/

namespace OMA.S_mo_235733

open scoped BigOperators

/-- The divisor sum of `n` is `2 * n` plus one of its proper divisors. -/
def IsNearPerfect (n : ℕ) : Prop :=
  0 < n ∧ ∃ d ∈ n.properDivisors, (∑ a ∈ n.divisors, a) = 2 * n + d

theorem main : {n : ℕ | IsNearPerfect n ∧ 4 < n.primeFactors.card}.Finite := by
  sorry

end OMA.S_mo_235733
