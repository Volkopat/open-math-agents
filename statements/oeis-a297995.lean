import Mathlib

/-!
# A297995: Number of ways to write n as 4*u + v^2 + x^3 + y^4 + 2*z^8, where u is 0 or 1, v is a positive integer and x,y,z are nonnegative integers.

Source: https://oeis.org/A297995
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A297995 (Zhi-Wei Sun, Jan 10 2018), part (i): a(n) > 0
for all n > 0, and a(n) = 1 only for n = 1, 398, 496, 498, 500, 1507, 6419, 7843, 7983, 8688,
8947, 9175, 9251, 12923, 12976, 48381.

Conventions:
* The sequence has offset 1 (data 1, 2, 2, 3, 4, 4, 4, 4, 5, 5, 5, 5, ...). `a n` is the number of
  quintuples (u, v, x, y, z) of natural numbers with u equal to 0 or 1, v > 0 and n = 4*u + v^2 +
  x^3 + y^4 + 2*z^8, exactly as in the OEIS name.
* Only part (i) of the conjecture is formalized; part (ii) is a different statement.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
* The `a(n) = 1 only for` part is rendered literally as an only-if: a(n) = 1 implies that n is one
  of the listed values.
-/

namespace OMA.S_oeis_a297995

/-- The condition in the name of A297995 on a tuple, for a given n. -/
def P (n : ℕ) (u v x y z : ℕ) : Prop :=
  u ≤ 1 ∧ 0 < v ∧ 4 * u + v ^ 2 + x ^ 3 + y ^ 4 + 2 * z ^ 8 = n

/-- A297995: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℕ × ℕ × ℕ | P n t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2}

/-- The conjecture recorded in A297995. -/
theorem main : ∀ n : ℕ, 0 < n → (0 < a n ∧ (a n = 1 →
      n ∈ ({1, 398, 496, 498, 500, 1507, 6419, 7843, 7983, 8688, 8947, 9175, 9251, 12923,
        12976, 48381} : Finset ℕ))) := by
  sorry

end OMA.S_oeis_a297995
