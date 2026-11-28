import Mathlib

/-!
# A351617: Number of ways to write n as 11^w + x^2 + 2*y^2 + 3*z^2 + x*y*z, where w,x,y,z are nonnegative integers.

Source: https://oeis.org/A351617
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A351617 (Zhi-Wei Sun, Mar 10 2022), part (i): a(n) > 0
for all n > 0.

Conventions:
* The sequence has offset 1 (data 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, ...). `a n` is the number of
  quadruples (w, x, y, z) of natural numbers with n = 11^w + x^2 + 2*y^2 + 3*z^2 + x*y*z, exactly
  as in the OEIS name.
* Only part (i) of the conjecture is formalized; part (ii) concerns other bases.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
-/

namespace OMA.S_oeis_a351617

/-- The condition in the name of A351617 on a tuple, for a given n. -/
def P (n : ℕ) (w x y z : ℕ) : Prop :=
  11 ^ w + x ^ 2 + 2 * y ^ 2 + 3 * z ^ 2 + x * y * z = n

/-- A351617: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℕ × ℕ | P n t.1 t.2.1 t.2.2.1 t.2.2.2}

/-- The conjecture recorded in A351617. -/
theorem main : ∀ n : ℕ, 0 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a351617
