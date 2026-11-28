import Mathlib

/-!
# A059455: Safe primes which are also Sophie Germain primes

Source: https://oeis.org/A059455

Conjecture (OEIS A059455, implied by Dickson's conjecture):
There are infinitely many primes `p` such that both `(p - 1) / 2` and `2 * p + 1` are prime.

Conventions:
- Offset: `1`; first terms: `5, 11, 23, 83, 179, 359, 719, ...`.
- Requiring `2 ∣ (p - 1)` together with `Nat.Prime ((p - 1) / 2)` expresses exactly that
  `p` is a safe prime (`p = 2 * q + 1` with `q` prime).
-/

namespace OMA.S_oeis_a059455

/-- The set of primes `p` that are both safe primes and Sophie Germain primes (OEIS A059455). -/
def S : Set ℕ :=
  {p : ℕ | Nat.Prime p ∧ 2 ∣ (p - 1) ∧ Nat.Prime ((p - 1) / 2) ∧ Nat.Prime (2 * p + 1)}

/-- Conjecture: there are infinitely many safe primes that are also Sophie Germain primes. -/
theorem main : Set.Infinite S := by
  sorry

end OMA.S_oeis_a059455
