import Mathlib

/-!
# A306238: Smallest positive integer k such that floor(n! / k) is odd

Source: https://oeis.org/A306238

Conjecture (OEIS A306238):
For every `n > 1`, `a(n)` is prime, where `a(n)` is the smallest positive integer `k`
such that `⌊n! / k⌋` is odd.

Conventions:
- Offset: `1`; first terms: `a(1) = 1`, `a(2) = 2`, `a(3) = 2`, `a(4) = 7`, `a(5) = 7`,
  `a(6) = 11`, `a(7) = 13`, `a(8) = 11`, `a(9) = 11`, `a(10) = 19`, `a(11) = 13`, `a(12) = 37`, ...
- We express minimality via the predicate `IsLeastOddQuotient` without `Nat.find`.
-/

namespace OMA.S_oeis_a306238

/-- Predicate stating that `k = a(n)` is the smallest positive integer such that
`⌊n! / k⌋` is odd (OEIS A306238). -/
def IsLeastOddQuotient (n k : ℕ) : Prop :=
  1 ≤ k ∧ Odd (n.factorial / k) ∧ ∀ j : ℕ, 1 ≤ j → Odd (n.factorial / j) → k ≤ j

/-- Conjecture: for every `n > 1`, the term `a(n)` of OEIS A306238 is prime. -/
theorem main :
    ∀ n k : ℕ, 1 < n → IsLeastOddQuotient n k → Nat.Prime k := by
  sorry

end OMA.S_oeis_a306238
