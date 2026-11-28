import Mathlib

/-!
# A306249: Number of ways to write n as x*(2x-1) + y*(3y-1) + z*(4z-1) + w*(5w-1), where x,y,z are nonnegative integers and w is 0 or 1.

Source: https://oeis.org/A306249
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A306249 (Zhi-Wei Sun, Jan 31 2019): a(n) > 0 for any
nonnegative integer n.

Conventions:
* The sequence has offset 0 (data 1, 1, 1, 2, 2, 2, 3, 2, 2, 2, 3, 2, ...). `a n` is the number of
  quadruples (x, y, z, w) of natural numbers with w equal to 0 or 1 and n = x*(2x-1) + y*(3y-1) +
  z*(4z-1) + w*(5w-1), exactly as in the OEIS name.
* The subtractions such as 2*x - 1 are natural-number subtractions; they are truncated only when
  the variable is 0, where the corresponding product is 0 in any case.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
-/

namespace OMA.S_oeis_a306249

/-- The condition in the name of A306249 on a tuple, for a given n. -/
def P (n : ℕ) (x y z w : ℕ) : Prop :=
  w ≤ 1 ∧ x * (2 * x - 1) + y * (3 * y - 1) + z * (4 * z - 1) + w * (5 * w - 1) = n

/-- A306249: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℕ × ℕ | P n t.1 t.2.1 t.2.2.1 t.2.2.2}

/-- The conjecture recorded in A306249. -/
theorem main : ∀ n : ℕ, 0 < a n := by
  sorry

end OMA.S_oeis_a306249
