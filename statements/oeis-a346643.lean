import Mathlib

/-!
# A346643: Number of ways to write n as w^2 + 2*x^2 + 3*y^4 + 4*z^4, where w,x,y,z are nonnegative integers.

Source: https://oeis.org/A346643
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A346643 (Zhi-Wei Sun, Jan 24 2022): 1-2-3-4 Conjecture:
a(n) > 0 except for n = 158.

Conventions:
* The sequence has offset 0 (data 1, 1, 1, 2, 3, 2, 3, 3, 3, 4, 2, 3, ...). `a n` is the number of
  quadruples (w, x, y, z) of natural numbers with n = w^2 + 2*x^2 + 3*y^4 + 4*z^4, exactly as in
  the OEIS name.
* The statement `a(n) > 0 except for n = 158` is rendered as an equivalence for every n >= 0: a(n)
  > 0 if and only if n is not 158.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
-/

namespace OMA.S_oeis_a346643

/-- The condition in the name of A346643 on a tuple, for a given n. -/
def P (n : ℕ) (w x y z : ℕ) : Prop :=
  w ^ 2 + 2 * x ^ 2 + 3 * y ^ 4 + 4 * z ^ 4 = n

/-- A346643: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℕ × ℕ | P n t.1 t.2.1 t.2.2.1 t.2.2.2}

/-- The conjecture recorded in A346643. -/
theorem main : ∀ n : ℕ, 0 < a n ↔ n ≠ 158 := by
  sorry

end OMA.S_oeis_a346643
