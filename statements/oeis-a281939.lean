import Mathlib

/-!
# A281939: Number of ways to write n as x^2 + y^2 + z^2 + w^2 with x - y and 3*z + w both squares, where x,y,z are nonnegative integers and w is an integer.

Source: https://oeis.org/A281939
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A281939 (Zhi-Wei Sun, Feb 02 2017), part (i): a(n) > 0
for all n = 0,1,2,....

Conventions:
* The sequence has offset 0 (data 1, 2, 3, 2, 1, 2, 2, 2, 2, 3, 5, 2, ...). `a n` is the number of
  quadruples (x, y, z, w) with x, y, z natural numbers, w an integer, x - y and 3*z + w both
  squares and n = x^2 + y^2 + z^2 + w^2, exactly as in the OEIS name.
* Integer variables range over `ℤ`; the equation and the side conditions involving them are stated
  in `ℤ`, with the natural variables and n cast.
* `a square` means the square of an integer (0 included), which is Mathlib's `IsSquare`; the
  quantity is computed in `ℤ` (with the natural variables cast), where a negative value is never a
  square.
* Only part (i) of the conjecture is formalized; parts (ii)-(iv) are different statements.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
-/

namespace OMA.S_oeis_a281939

/-- The condition in the name of A281939 on a tuple, for a given n. -/
def P (n : ℕ) (x y z : ℕ) (w : ℤ) : Prop :=
  IsSquare ((x : ℤ) - (y : ℤ)) ∧ IsSquare (3 * (z : ℤ) + w) ∧
    (x : ℤ) ^ 2 + (y : ℤ) ^ 2 + (z : ℤ) ^ 2 + w ^ 2 = (n : ℤ)

/-- A281939: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℕ × ℤ | P n t.1 t.2.1 t.2.2.1 t.2.2.2}

/-- The conjecture recorded in A281939. -/
theorem main : ∀ n : ℕ, 0 < a n := by
  sorry

end OMA.S_oeis_a281939
