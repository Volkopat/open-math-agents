import Mathlib

/-!
# A231329: Numbers n such that (19^n + 4^n) / 23 is prime

Source: https://oeis.org/A231329

Conjecture (OEIS A231329):
Every natural number `n` such that `(19^n + 4^n) / 23` is an integer and prime
is itself prime.

Conventions:
- Offset: `1`; first terms: `7, 11, ...`.
- Integrality of `(19^n + 4^n) / 23` is expressed explicitly by `23 ∣ 19 ^ n + 4 ^ n`.
-/

namespace OMA.S_oeis_a231329

/-- Membership predicate for OEIS A231329: `23 ∣ 19^n + 4^n` and `(19^n + 4^n) / 23` is prime. -/
def IsTerm (n : ℕ) : Prop :=
  23 ∣ 19 ^ n + 4 ^ n ∧ Nat.Prime ((19 ^ n + 4 ^ n) / 23)

/-- Conjecture: all terms of OEIS A231329 are prime. -/
theorem main :
    ∀ n : ℕ, IsTerm n → Nat.Prime n := by
  sorry

end OMA.S_oeis_a231329
