import Mathlib

/-!
# A271510: Number of ordered ways to write n as x^2 + y^2 + z^2 + w^2 with x >= y >= 0, z >= 0 and w >= 0 such that x^2 + 8*y^2 + 16*z^2 is a square.

Source: https://oeis.org/A271510
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A271510 (Zhi-Wei Sun, Apr 09 2016), part (i): a(n) > 0
for all n = 0,1,2,..., and a(n) = 1 only for n = 0, 7, 23, 71, 77, 105, 191, 215, 311, 335, 2903,
4^k*q (k = 0,1,2,... and q = 6, 15, 47, 138).

Conventions:
* The sequence has offset 0 (data 1, 3, 3, 2, 4, 4, 1, 1, 3, 4, 5, 2, ...). `a n` is the number of
  quadruples (x, y, z, w) of natural numbers with x >= y, x^2 + 8*y^2 + 16*z^2 a square and n =
  x^2 + y^2 + z^2 + w^2, exactly as in the OEIS name.
* `a square` means the square of an integer (0 included), which is Mathlib's `IsSquare`.
* Only part (i) of the conjecture is formalized; parts (ii)-(iv) concern other quadratic forms.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
* The `a(n) = 1 only for` part is rendered literally as an only-if: a(n) = 1 implies that n is one
  of the listed values.
-/

namespace OMA.S_oeis_a271510

/-- The condition in the name of A271510 on a tuple, for a given n. -/
def P (n : ℕ) (x y z w : ℕ) : Prop :=
  y ≤ x ∧ IsSquare (x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2) ∧ x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n

/-- A271510: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℕ × ℕ | P n t.1 t.2.1 t.2.2.1 t.2.2.2}

/-- The conjecture recorded in A271510. -/
theorem main : ∀ n : ℕ, 0 < a n ∧ (a n = 1 →
      n ∈ ({0, 7, 23, 71, 77, 105, 191, 215, 311, 335, 2903} : Finset ℕ) ∨
      (∃ k m : ℕ, m ∈ ({6, 15, 47, 138} : Finset ℕ) ∧ n = 4 ^ k * m)) := by
  sorry

end OMA.S_oeis_a271510
