import Mathlib

/-!
# A349957: Number of ways to write n as x^4 + y^2 + (z^2 + 11*16^w)/60, where x,y,z are nonnegative integers, and w is 0 or 1.

Source: https://oeis.org/A349957
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A349957 (Zhi-Wei Sun, Dec 06 2021), Conjecture 1: a(n)
> 0 for all n > 0.

Conventions:
* The sequence has offset 1 (data 1, 2, 3, 5, 6, 4, 3, 3, 3, 4, 3, 4, ...). `a n` is the number of
  quadruples (x, y, z, w) of natural numbers with w equal to 0 or 1 and n = x^4 + y^2 + (z^2 +
  11*16^w)/60, exactly as in the OEIS name.
* The quotient (z^2 + 11*16^w)/60 must be an integer: this is stated as 60 dividing z^2 + 11*16^w,
  together with the (then exact) natural-number division.
* Only Conjecture 1 is formalized; Conjectures 2-4 are different statements.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
-/

namespace OMA.S_oeis_a349957

/-- The condition in the name of A349957 on a tuple, for a given n. -/
def P (n : ℕ) (x y z w : ℕ) : Prop :=
  (w = 0 ∨ w = 1) ∧ 60 ∣ z ^ 2 + 11 * 16 ^ w ∧
  x ^ 4 + y ^ 2 + (z ^ 2 + 11 * 16 ^ w) / 60 = n

/-- A349957: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℕ × ℕ | P n t.1 t.2.1 t.2.2.1 t.2.2.2}

/-- The conjecture recorded in A349957. -/
theorem main : ∀ n : ℕ, 0 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a349957
