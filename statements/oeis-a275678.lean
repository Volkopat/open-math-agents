import Mathlib

/-!
# A275678: Number of ordered ways to write n as 4^k*(1+4*x^2+y^2) + z^2, where k,x,y,z are nonnegative integers with x <= y.

Source: https://oeis.org/A275678
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A275678 (Zhi-Wei Sun, Aug 05 2016), part (i): a(n) > 0
for all n > 0.

Conventions:
* The sequence has offset 1 (data 1, 2, 1, 1, 3, 3, 1, 2, 3, 4, 2, 1, ...). `a n` is the number of
  quadruples (k, x, y, z) of natural numbers with x <= y and n = 4^k*(1+4*x^2+y^2) + z^2, exactly
  as in the OEIS name.
* Only part (i) of the conjecture is formalized; part (ii) uses a different side condition.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
-/

namespace OMA.S_oeis_a275678

/-- The condition in the name of A275678 on a tuple, for a given n. -/
def P (n : ℕ) (k x y z : ℕ) : Prop :=
  x ≤ y ∧ 4 ^ k * (1 + 4 * x ^ 2 + y ^ 2) + z ^ 2 = n

/-- A275678: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℕ × ℕ | P n t.1 t.2.1 t.2.2.1 t.2.2.2}

/-- The conjecture recorded in A275678. -/
theorem main : ∀ n : ℕ, 0 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a275678
