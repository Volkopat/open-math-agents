import Mathlib

/-!
# A347865: Number of ways to write n as w^2 + 2*x^2 + y^4 + 3*z^4, where w,x,y,z are nonnegative integers.

Source: https://oeis.org/A347865
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A347865 (Zhi-Wei Sun, Jan 24 2022), Conjecture 1: a(n)
> 0 except for n = 744.

Conventions:
* The sequence has offset 0 (data 1, 2, 2, 3, 4, 3, 3, 3, 2, 4, 3, 2, ...). `a n` is the number of
  quadruples (w, x, y, z) of natural numbers with n = w^2 + 2*x^2 + y^4 + 3*z^4, exactly as in the
  OEIS name.
* The statement `a(n) > 0 except for n = 744` is rendered as an equivalence for every n >= 0: a(n)
  > 0 if and only if n is not 744.
* Only Conjecture 1 of the entry is formalized; Conjecture 2 is a different statement.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
-/

namespace OMA.S_oeis_a347865

/-- The condition in the name of A347865 on a tuple, for a given n. -/
def P (n : ℕ) (w x y z : ℕ) : Prop :=
  w ^ 2 + 2 * x ^ 2 + y ^ 4 + 3 * z ^ 4 = n

/-- A347865: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℕ × ℕ | P n t.1 t.2.1 t.2.2.1 t.2.2.2}

/-- The conjecture recorded in A347865. -/
theorem main : ∀ n : ℕ, 0 < a n ↔ n ≠ 744 := by
  sorry

end OMA.S_oeis_a347865
