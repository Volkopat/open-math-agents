import Mathlib

/-!
# A281659: Number of ways to write n as x^2 + y^2 + z^2 + w^2 with 9*x^2 + 16*y^2 + 24*z^2 + 48*w^2 a square, where x,y,z,w are nonnegative integers.

Source: https://oeis.org/A281659
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A281659 (Zhi-Wei Sun, Jan 26 2017), part (i): a(n) > 0
except for n = 71, 85.

Conventions:
* The sequence has offset 0 (data 1, 2, 2, 2, 2, 1, 4, 1, 2, 3, 4, 1, ...). `a n` is the number of
  quadruples (x, y, z, w) of natural numbers with 9*x^2 + 16*y^2 + 24*z^2 + 48*w^2 a square and n
  = x^2 + y^2 + z^2 + w^2, exactly as in the OEIS name.
* `a square` means the square of an integer (0 included), which is Mathlib's `IsSquare`.
* The statement `a(n) > 0 except for n = 71, 85` is rendered as an equivalence for every n >= 0:
  a(n) > 0 if and only if n is neither 71 nor 85.
* Only part (i) of the conjecture is formalized; parts (ii)-(iv) concern other forms.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
-/

namespace OMA.S_oeis_a281659

/-- The condition in the name of A281659 on a tuple, for a given n. -/
def P (n : ℕ) (x y z w : ℕ) : Prop :=
  IsSquare (9 * x ^ 2 + 16 * y ^ 2 + 24 * z ^ 2 + 48 * w ^ 2) ∧ x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n

/-- A281659: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℕ × ℕ | P n t.1 t.2.1 t.2.2.1 t.2.2.2}

/-- The conjecture recorded in A281659. -/
theorem main : ∀ n : ℕ, 0 < a n ↔ (n ≠ 71 ∧ n ≠ 85) := by
  sorry

end OMA.S_oeis_a281659
