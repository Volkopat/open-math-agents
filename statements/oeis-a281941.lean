import Mathlib

/-!
# A281941: Number of ways to write n as w^2 + x^2 + y^2 + z^2 with w and w + x + y + z both squares, where w,x,y,z are integers with |x| <= |y| <= |z|.

Source: https://oeis.org/A281941
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A281941 (Zhi-Wei Sun, Feb 02 2017), part (i): a(n) > 0
for all n = 0,1,2,....

Conventions:
* The sequence has offset 0 (data 1, 2, 3, 5, 4, 1, 5, 2, 3, 4, 5, 1, ...). `a n` is the number of
  quadruples (w, x, y, z) of integers with |x| <= |y| <= |z|, n = w^2 + x^2 + y^2 + z^2 and w and
  w + x + y + z both squares, exactly as in the OEIS name.
* w, x, y, z range over `ℤ` and the equation is stated in `ℤ` with n cast. `a square` is
  `IsSquare` in `ℤ`, i.e. the square of an integer; in particular w is nonnegative.
* Only part (i) of the conjecture is formalized; the other parts are different statements.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
-/

namespace OMA.S_oeis_a281941

/-- The condition in the name of A281941 on a tuple, for a given n. -/
def P (n : ℕ) (w x y z : ℤ) : Prop :=
  w ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 = n ∧ |x| ≤ |y| ∧ |y| ≤ |z| ∧ IsSquare w ∧ IsSquare (w + x + y + z)

/-- A281941: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℤ × ℤ × ℤ × ℤ | P n t.1 t.2.1 t.2.2.1 t.2.2.2}

/-- The conjecture recorded in A281941. -/
theorem main : ∀ n : ℕ, 0 < a n := by
  sorry

end OMA.S_oeis_a281941
