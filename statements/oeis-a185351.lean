import Mathlib

/-!
# A185351: Sums of distinct perfect numbers

Source: https://oeis.org/A185351

Conjecture (OEIS A185351):
Every sum of distinct perfect numbers is even. (Equivalently, there are no odd
perfect numbers.)

Conventions:
- A positive integer `m` is perfect iff the sum of all its positive divisors
  equals `2 * m` (`0 < m ∧ (Nat.divisors m).sum id = 2 * m`).
- First terms (nonempty sums): `6, 28, 34, 496, 502, 524, 530, 8128, ...`.
-/

namespace OMA.S_oeis_a185351

/-- Predicate stating that `m` is a perfect number (OEIS A000396). -/
def IsPerfect (m : ℕ) : Prop :=
  0 < m ∧ (Nat.divisors m).sum id = 2 * m

/-- The set of sums of distinct perfect numbers (OEIS A185351). -/
def S : Set ℕ :=
  {n : ℕ | ∃ s : Finset ℕ, (∀ m ∈ s, IsPerfect m) ∧ s.sum id = n}

/-- Conjecture: every term of A185351 is even. -/
theorem main : ∀ n ∈ S, Even n := by
  sorry

end OMA.S_oeis_a185351
