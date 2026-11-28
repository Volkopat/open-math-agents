import Mathlib

/-!
# A282561: Number of ways to write n as x^2 + y^2 + z^2 + w^2 with x,y,z,w nonnegative integers such that both 2*x - y and 4*z^2 + 724*z*w + w^2 are squares.

Source: https://oeis.org/A282561
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A282561 (Zhi-Wei Sun, Feb 18 2017): a(n) > 0 for all n
= 0,1,2,..., and a(n) = 1 only for n = 0, 16^k*m (k = 0,1,2,... and m = 7, 19, 67, 191, 235, 265,
347, 888, 2559).

Conventions:
* The sequence has offset 0 (data 1, 2, 2, 2, 4, 3, 5, 1, 3, 4, 2, 2, ...). `a n` is the number of
  quadruples (x, y, z, w) of natural numbers with n = x^2 + y^2 + z^2 + w^2 such that both 2*x - y
  and 4*z^2 + 724*z*w + w^2 are squares, exactly as in the OEIS name.
* `a square` means the square of an integer (0 included), which is Mathlib's `IsSquare`; 2*x - y
  is computed in `ℤ` (with x and y cast), where a negative value is never a square.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
* The `a(n) = 1 only for` part is rendered literally as an only-if: a(n) = 1 implies that n is one
  of the listed values.
-/

namespace OMA.S_oeis_a282561

/-- The condition in the name of A282561 on a tuple, for a given n. -/
def P (n : ℕ) (x y z w : ℕ) : Prop :=
  x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n ∧ IsSquare (2 * (x : ℤ) - y) ∧
  IsSquare (4 * z ^ 2 + 724 * z * w + w ^ 2)

/-- A282561: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℕ × ℕ | P n t.1 t.2.1 t.2.2.1 t.2.2.2}

/-- The conjecture recorded in A282561. -/
theorem main : ∀ n : ℕ, 0 < a n ∧ (a n = 1 →
      n ∈ ({0} : Finset ℕ) ∨
      (∃ k m : ℕ, m ∈ ({7, 19, 67, 191, 235, 265, 347, 888, 2559} : Finset ℕ) ∧
      n = 16 ^ k * m)) := by
  sorry

end OMA.S_oeis_a282561
