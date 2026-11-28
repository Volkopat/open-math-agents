import Mathlib

/-!
# A347827: Number of ways to write n as w^4 + x^4 + (y^2 + 23*z^2)/16, where w is zero or a power of two (including 2^0 = 1), and x,y,z are nonnegative integers.

Source: https://oeis.org/A347827
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A347827 (Zhi-Wei Sun, Jan 23 2022), the 23-Conjecture:
a(n) > 0 for all n = 0,1,2,....

Conventions:
* The sequence has offset 0 (data 1, 3, 4, 4, 4, 3, 2, 2, 2, 4, 5, 2, ...). `a n` is the number of
  quadruples (w, x, y, z) of natural numbers with w zero or a power of two (including 2^0 = 1) and
  n = w^4 + x^4 + (y^2 + 23*z^2)/16, exactly as in the OEIS name.
* The quotient (y^2 + 23*z^2)/16 must be an integer: this is stated as 16 dividing y^2 + 23*z^2,
  together with the (then exact) natural-number division.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
-/

namespace OMA.S_oeis_a347827

/-- The condition in the name of A347827 on a tuple, for a given n. -/
def P (n : ℕ) (w x y z : ℕ) : Prop :=
  (w = 0 ∨ ∃ k : ℕ, w = 2 ^ k) ∧ 16 ∣ y ^ 2 + 23 * z ^ 2 ∧
  w ^ 4 + x ^ 4 + (y ^ 2 + 23 * z ^ 2) / 16 = n

/-- A347827: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℕ × ℕ | P n t.1 t.2.1 t.2.2.1 t.2.2.2}

/-- The conjecture recorded in A347827. -/
theorem main : ∀ n : ℕ, 0 < a n := by
  sorry

end OMA.S_oeis_a347827
