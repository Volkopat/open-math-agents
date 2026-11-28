import Mathlib

/-!
# A281158: Least prime p such that n^2 + (n - p)^2 is prime

Source: https://oeis.org/A281158

Conjecture (OEIS A281158):
For every `n > 3`, `a(n) < n`, where `a(n)` is the least prime `p` such that
`n^2 + (n - p)^2` is prime.

Conventions:
- Offset: `1`; first terms: `a(1) = 2`, `a(2) = 3`, `a(3) = 5`, `a(4) = 3`, `a(5) = 3`,
  `a(6) = 5`, `a(7) = 5`, `a(8) = 3`, `a(9) = 5`, `a(10) = 3`, ...
- We use `Int.natAbs ((n : ℤ) - (p : ℤ)) ^ 2` so that `(n - p)^2` is exact for all `n, p : ℕ`,
  and express minimality via `IsLeastPrimeSumSq` without `Nat.find`.
-/

namespace OMA.S_oeis_a281158

/-- Predicate stating that `p` is prime and `n^2 + (n - p)^2` is prime. -/
def IsPrimeSumSq (n p : ℕ) : Prop :=
  Nat.Prime p ∧ Nat.Prime (n ^ 2 + Int.natAbs ((n : ℤ) - (p : ℤ)) ^ 2)

/-- Predicate stating that `p = a(n)` is the least prime with `n^2 + (n - p)^2` prime (OEIS A281158). -/
def IsLeastPrimeSumSq (n p : ℕ) : Prop :=
  IsPrimeSumSq n p ∧ ∀ q : ℕ, IsPrimeSumSq n q → p ≤ q

/-- Conjecture: for every `n > 3`, `a(n)` exists and satisfies `a(n) < n`. -/
theorem main :
    ∀ n : ℕ, 3 < n → ∃ p : ℕ, IsLeastPrimeSumSq n p ∧ p < n := by
  sorry

end OMA.S_oeis_a281158
