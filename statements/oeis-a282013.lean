import Mathlib

/-!
# A282013: Number of ways to write n as x^2 + y^2 + z^2 + w^2 with x,y,z,w nonnegative integers such that both x and 49*x + 48*(y-z) are squares.

Source: https://oeis.org/A282013
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A282013 (Zhi-Wei Sun, Feb 04 2017): a(n) > 0 for all n
= 0,1,2,..., and a(n) = 1 only for n = 0, 16^k*m (k = 0,1,2,... and m = 5, 8, 14, 31, 47, 71, 79,
143, 248, 463, 1039).

Conventions:
* The sequence has offset 0 (data 1, 2, 3, 3, 2, 1, 3, 2, 1, 4, 4, 2, ...). `a n` is the number of
  quadruples (x, y, z, w) of natural numbers with both x and 49*x + 48*(y-z) squares, and n = x^2
  + y^2 + z^2 + w^2, exactly as in the OEIS name.
* `a square` means the square of an integer (0 included), which is Mathlib's `IsSquare`; the
  quantity is computed in `ℤ` (with the natural variables cast), where a negative value is never a
  square.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
* The `a(n) = 1 only for` part is rendered literally as an only-if: a(n) = 1 implies that n is one
  of the listed values.
-/

namespace OMA.S_oeis_a282013

/-- The condition in the name of A282013 on a tuple, for a given n. -/
def P (n : ℕ) (x y z w : ℕ) : Prop :=
  IsSquare x ∧ IsSquare (49 * (x : ℤ) + 48 * ((y : ℤ) - (z : ℤ))) ∧
  x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n

/-- A282013: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℕ × ℕ | P n t.1 t.2.1 t.2.2.1 t.2.2.2}

/-- The conjecture recorded in A282013. -/
theorem main : ∀ n : ℕ, 0 < a n ∧ (a n = 1 →
      n = 0 ∨
      (∃ k m : ℕ, m ∈ ({5, 8, 14, 31, 47, 71, 79, 143, 248, 463, 1039} : Finset ℕ) ∧ n = 16 ^ k * m)) := by
  sorry

end OMA.S_oeis_a282013
