import Mathlib

/-!
# A109994: Chen primes p such that p + 2 is a Sarrus number (base-2 pseudoprime)

Source: https://oeis.org/A109994

Conjecture (OEIS A109994):
There are infinitely many Chen primes `p` such that `p + 2` is a Sarrus number
(a composite Fermat pseudoprime to base `2`).

Conventions:
- Offset: `1`; first terms: `2699, 4679, 10259, 14489, 18719, 19949, ...`.
- A prime `p` is a Chen prime if `p + 2` is prime or a semiprime (product of
  two not necessarily distinct primes). Since a Sarrus number is composite,
  `p + 2` is specifically a semiprime satisfying `2 ^ (p + 1) ≡ 1 [MOD p + 2]`.
-/

namespace OMA.S_oeis_a109994

/-- Predicate stating that `m` is a Sarrus number (base-2 Fermat pseudoprime). -/
def IsSarrus (m : ℕ) : Prop :=
  2 ≤ m ∧ ¬ Nat.Prime m ∧ 2 ^ (m - 1) % m = 1

/-- Predicate stating that `m` is a semiprime (product of two primes). -/
def IsSemiprime (m : ℕ) : Prop :=
  ∃ q r : ℕ, Nat.Prime q ∧ Nat.Prime r ∧ m = q * r

/-- The set of Chen primes `p` whose counterpart `p + 2` is a Sarrus number (OEIS A109994). -/
def S : Set ℕ :=
  {p : ℕ | Nat.Prime p ∧ IsSemiprime (p + 2) ∧ IsSarrus (p + 2)}

/-- Conjecture: the sequence A109994 is infinite. -/
theorem main : Set.Infinite S := by
  sorry

end OMA.S_oeis_a109994
