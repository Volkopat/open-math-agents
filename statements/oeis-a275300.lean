import Mathlib

/-!
# A275300: Number of ordered ways to write n as x^2 + y^2 + z^2 + w^3 with x + y + z a square, where x,y,z are integers with x >= |y| <= |z|, and w is a nonnegative integer.

Source: https://oeis.org/A275300
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A275300 (Zhi-Wei Sun, Jul 22 2016): a(n) > 0 for all n
= 0,1,2,..., and a(n) = 1 only for n = 0, 5, 12, 20, 23, 31, 47, 71, 103, 148, 164.

Conventions:
* The sequence has offset 0 (data 1, 3, 3, 3, 2, 1, 5, 4, 3, 5, 4, 5, ...). `a n` is the number of
  quadruples (x, y, z, w) with x, y, z integers, w a natural number, x >= |y| <= |z|, n = x^2 +
  y^2 + z^2 + w^3 and x + y + z a square, exactly as in the OEIS name.
* x, y, z range over `ℤ` and the equation is stated in `ℤ` with w and n cast. The chain x >= |y|
  <= |z| is the two conditions |y| <= x and |y| <= |z|.
* `a square` is `IsSquare` in `ℤ`, i.e. the square of an integer (a negative integer is never a
  square).
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
* The `a(n) = 1 only for` part is rendered literally as an only-if: a(n) = 1 implies that n is one
  of the listed values.
-/

namespace OMA.S_oeis_a275300

/-- The condition in the name of A275300 on a tuple, for a given n. -/
def P (n : ℕ) (x y z : ℤ) (w : ℕ) : Prop :=
  x ^ 2 + y ^ 2 + z ^ 2 + (w : ℤ) ^ 3 = n ∧ |y| ≤ x ∧ |y| ≤ |z| ∧ IsSquare (x + y + z)

/-- A275300: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℤ × ℤ × ℤ × ℕ | P n t.1 t.2.1 t.2.2.1 t.2.2.2}

/-- The conjecture recorded in A275300. -/
theorem main : ∀ n : ℕ, 0 < a n ∧ (a n = 1 →
      n ∈ ({0, 5, 12, 20, 23, 31, 47, 71, 103, 148, 164} : Finset ℕ)) := by
  sorry

end OMA.S_oeis_a275300
