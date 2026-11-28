import Mathlib

/-!
# A281975: Number of ways to write n as x^2 + y^2 + z^2 + w^2 with x,y,z,w nonnegative integers and z <= w such that both x and |x-y| are squares.

Source: https://oeis.org/A281975
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A281975 (Zhi-Wei Sun, Feb 03 2017), part (i): a(n) > 0
for all n = 0,1,2,....

Conventions:
* The sequence has offset 0 (data 1, 3, 4, 3, 2, 4, 4, 2, 1, 4, 5, 3, ...). `a n` is the number of
  quadruples (x, y, z, w) of natural numbers with z <= w, both x and |x-y| squares, and n = x^2 +
  y^2 + z^2 + w^2, exactly as in the OEIS name.
* `a square` means the square of an integer (0 included), which is Mathlib's `IsSquare`.
* The absolute value |x-y| is computed in `ℤ`.
* Only part (i) of the conjecture is formalized; parts (ii) and (iii) are different statements.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
-/

namespace OMA.S_oeis_a281975

/-- The condition in the name of A281975 on a tuple, for a given n. -/
def P (n : ℕ) (x y z w : ℕ) : Prop :=
  z ≤ w ∧ IsSquare x ∧ IsSquare |(x : ℤ) - (y : ℤ)| ∧ x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n

/-- A281975: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℕ × ℕ | P n t.1 t.2.1 t.2.2.1 t.2.2.2}

/-- The conjecture recorded in A281975. -/
theorem main : ∀ n : ℕ, 0 < a n := by
  sorry

end OMA.S_oeis_a281975
