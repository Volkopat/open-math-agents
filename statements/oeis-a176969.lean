import Mathlib

/-!
# A176969: Numbers n such that n^2 + 13^2 is prime

Source: https://oeis.org/A176969

Conjecture (OEIS A176969, special case of the n^2 + d conjecture):
There are infinitely many natural numbers `n` such that `n^2 + 169` is prime.

Conventions:
- Offset: `1`; first terms: `2, 8, 10, 12, 20, 22, 28, 30, 32, 38, ...`.
-/

namespace OMA.S_oeis_a176969

/-- The set of natural numbers `n` such that `n^2 + 13^2` is prime (OEIS A176969). -/
def S : Set ℕ :=
  {n : ℕ | Nat.Prime (n ^ 2 + 13 ^ 2)}

/-- Conjecture: there are infinitely many `n` such that `n^2 + 13^2` is prime. -/
theorem main : Set.Infinite S := by
  sorry

end OMA.S_oeis_a176969
