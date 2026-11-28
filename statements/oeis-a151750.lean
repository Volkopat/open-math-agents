import Mathlib

/-!
# A151750: Numbers n such that gcd(binomial(2*n, n), 3*5*7*11) = 1

Source: https://oeis.org/A151750

Conjecture (OEIS A151750):
The only nonnegative integers `n` satisfying `gcd(C(2*n, n), 3 * 5 * 7 * 11) = 1`
are `0`, `1`, and `3160`.

Conventions:
- Offset: `1`; known terms: `0, 1, 3160`.
- `3 * 5 * 7 * 11 = 1155`.
-/

namespace OMA.S_oeis_a151750

/-- Membership predicate for OEIS A151750: `gcd(binomial(2*n, n), 3*5*7*11) = 1`. -/
def IsTerm (n : ℕ) : Prop :=
  Nat.gcd (Nat.choose (2 * n) n) (3 * 5 * 7 * 11) = 1

/-- Conjecture: `0`, `1`, and `3160` are the only terms of OEIS A151750. -/
theorem main :
    ∀ n : ℕ, IsTerm n ↔ n = 0 ∨ n = 1 ∨ n = 3160 := by
  sorry

end OMA.S_oeis_a151750
