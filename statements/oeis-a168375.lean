import Mathlib

/-!
# A168375: Natural numbers n for which the concatenation "1 n^3" is prime

Source: https://oeis.org/A168375

Conjecture (OEIS A168375):
There are infinitely many natural numbers `n` such that the base-10
concatenation `1 || n^3` (OEIS A168327) is prime.

Conventions:
- Offset: `1`; first terms: `1, 3, 13, 33, 39, ...`
  (giving primes `11, 127, 12197, 135937, 159319, ...`).
- `concat10 1 (n ^ 3)` handles `n = 0` explicitly as `10` (not prime) and
  `n ≥ 1` as `10 ^ (Nat.digits 10 (n ^ 3)).length + n ^ 3`.
-/

namespace OMA.S_oeis_a168375

/-- Base-10 concatenation `a || b`, handling `b = 0` as `10 * a`. -/
def concat10 (a b : ℕ) : ℕ :=
  if b = 0 then 10 * a else a * 10 ^ (Nat.digits 10 b).length + b

/-- The set of natural numbers `n` such that `1 || n^3` is prime (OEIS A168375). -/
def S : Set ℕ :=
  {n : ℕ | Nat.Prime (concat10 1 (n ^ 3))}

/-- Conjecture: the sequence A168375 is infinite. -/
theorem main : Set.Infinite S := by
  sorry

end OMA.S_oeis_a168375
