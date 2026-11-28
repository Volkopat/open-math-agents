import Mathlib

/-!
# A279522: Number of ways to write n as w^2 + x^2 + y^2 + z^2 with w + 2*x + 3*y + 5*z a square, where w,x,y,z are nonnegative integers.

Source: https://oeis.org/A279522
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A279522 (Zhi-Wei Sun, Dec 14 2016), part (i): a(n) = 0
if and only if n = 16^k*28 for some k = 0,1,2,....

Conventions:
* The sequence has offset 0 (data 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, ...). `a n` is the number of
  quadruples (w, x, y, z) of natural numbers with n = w^2 + x^2 + y^2 + z^2 and w + 2*x + 3*y +
  5*z a square, exactly as in the OEIS name.
* `a square` is the Mathlib predicate `IsSquare` (0 included).
* Only part (i) of the conjecture is formalized; the other parts are different statements.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
-/

namespace OMA.S_oeis_a279522

/-- The condition in the name of A279522 on a tuple, for a given n. -/
def P (n : ℕ) (w x y z : ℕ) : Prop :=
  w ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 = n ∧ IsSquare (w + 2 * x + 3 * y + 5 * z)

/-- A279522: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℕ × ℕ | P n t.1 t.2.1 t.2.2.1 t.2.2.2}

/-- The conjecture recorded in A279522. -/
theorem main : ∀ n : ℕ, a n = 0 ↔ ∃ k : ℕ, n = 16 ^ k * 28 := by
  sorry

end OMA.S_oeis_a279522
