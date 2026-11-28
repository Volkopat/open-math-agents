import Mathlib

/-!
# A228558: Numbers k such that (17^k + 4^k) / 21 is prime

Source: https://oeis.org/A228558

Conjecture (OEIS A228558):
Every natural number `k` such that `(17^k + 4^k) / 21` is an integer and prime
is itself prime.

Conventions:
- Offset: `1`; first terms: `13, 61, 67, 107, 383, 647, 3571, 37967, ...`.
- Integrality of `(17^k + 4^k) / 21` is expressed explicitly by `21 ∣ 17 ^ k + 4 ^ k`.
-/

namespace OMA.S_oeis_a228558

/-- Membership predicate for OEIS A228558: `21 ∣ 17^k + 4^k` and `(17^k + 4^k) / 21` is prime. -/
def IsTerm (k : ℕ) : Prop :=
  21 ∣ 17 ^ k + 4 ^ k ∧ Nat.Prime ((17 ^ k + 4 ^ k) / 21)

/-- Conjecture: all terms of OEIS A228558 are prime. -/
theorem main :
    ∀ k : ℕ, IsTerm k → Nat.Prime k := by
  sorry

end OMA.S_oeis_a228558
