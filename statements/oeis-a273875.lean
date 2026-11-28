import Mathlib

/-!
# A273875: Number of ordered ways to write n as w^2 + x^2 + y^2 + z^2 with x*y + 2*y*z + 4*z*x a nonnegative cube, where w,x,y,z are integers with w >= 0 and x > 0.

Source: https://oeis.org/A273875
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A273875 (Zhi-Wei Sun, Jun 02 2016), part (i): a(n) > 0
for all n > 0.

Conventions:
* The sequence has offset 1 (data 1, 2, 2, 2, 4, 3, 1, 1, 4, 3, 1, 1, ...). `a n` is the number of
  quadruples (w, x, y, z) of integers with w >= 0, x > 0, x*y + 2*y*z + 4*z*x a nonnegative cube
  and n = w^2 + x^2 + y^2 + z^2, exactly as in the OEIS name.
* All four variables range over `ℤ` and the equation is stated in `ℤ` with n cast.
* A nonnegative cube is c^3 with c a natural number.
* Only part (i) of the conjecture is formalized; parts (ii) and (iii) are different statements.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
-/

namespace OMA.S_oeis_a273875

/-- The condition in the name of A273875 on a tuple, for a given n. -/
def P (n : ℕ) (w x y z : ℤ) : Prop :=
  0 ≤ w ∧ 0 < x ∧ (∃ c : ℕ, x * y + 2 * y * z + 4 * z * x = (c : ℤ) ^ 3) ∧
    w ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 = (n : ℤ)

/-- A273875: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℤ × ℤ × ℤ × ℤ | P n t.1 t.2.1 t.2.2.1 t.2.2.2}

/-- The conjecture recorded in A273875. -/
theorem main : ∀ n : ℕ, 0 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a273875
