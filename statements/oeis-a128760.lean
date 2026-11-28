import Mathlib

/-!
# A128760: Number of ways to write n as the absolute difference of a power of 2 and a power of 3.

Source: https://oeis.org/A128760
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A128760 (Reinhard Zumkeller, Mar 25 2007): there exists
c>=23 such that a(n)<2 for n>c.

Conventions:
* The sequence has offset 0 (data 1, 4, 1, 1, 0, 3, 0, 3, 1, 0, 0, 1, ...).
* a(n) is the number of pairs (i, j) of natural numbers with |2^i - 3^j| = n (the difference is
  computed in `ℤ` and `Int.natAbs` is its absolute value); for n > 0 this set is finite and
  `Set.ncard` is its number of elements. This reproduces the OEIS examples (a(1) = 4 from 2^1 -
  3^0, 2^2 - 3^1, 3^1 - 2^1, 3^2 - 2^3).
* The condition c >= 23 is kept as in the entry (a(23) = 2).
-/

namespace OMA.S_oeis_a128760

/-- A128760: the number of ways to write n as |2^i - 3^j|. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ | Int.natAbs ((2 : ℤ) ^ t.1 - 3 ^ t.2) = n}

/-- The conjecture recorded in A128760. -/
theorem main : ∃ c : ℕ, 23 ≤ c ∧ ∀ n : ℕ, c < n → a n < 2 := by
  sorry

end OMA.S_oeis_a128760
