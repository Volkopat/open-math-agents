import Mathlib

/-!
# A347824: Number of ways to write n as x^4 + y^4 + (z^2 + 23*w^2)/16, where x,y,z,w are nonnegative integers with x <= y.

Source: https://oeis.org/A347824
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A347824 (Zhi-Wei Sun, Jan 23 2022): a(n) > 0 for all n
= 0,1,2,....

Conventions:
* The sequence has offset 0 (data 1, 2, 3, 3, 3, 2, 2, 1, 2, 3, 3, 2, ...). `a n` is the number of
  quadruples (x, y, z, w) of natural numbers with x <= y and n = x^4 + y^4 + (z^2 + 23*w^2)/16,
  exactly as in the OEIS name.
* The quotient (z^2 + 23*w^2)/16 is required to be an integer: the divisibility by 16 is a
  separate conjunct, and the natural-number division is then exact.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
-/

namespace OMA.S_oeis_a347824

/-- The condition in the name of A347824 on a tuple, for a given n. -/
def P (n : ℕ) (x y z w : ℕ) : Prop :=
  x ≤ y ∧ 16 ∣ z ^ 2 + 23 * w ^ 2 ∧ x ^ 4 + y ^ 4 + (z ^ 2 + 23 * w ^ 2) / 16 = n

/-- A347824: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℕ × ℕ | P n t.1 t.2.1 t.2.2.1 t.2.2.2}

/-- The conjecture recorded in A347824. -/
theorem main : ∀ n : ℕ, 0 < a n := by
  sorry

end OMA.S_oeis_a347824
