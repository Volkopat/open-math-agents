import Mathlib

/-!
# A306460: Number of ways to write n as x*(2x-1) + y*(y+1)/2 + z*(z+1)*(z+2)/6, where x,y,z are nonnegative integers with x > 0.

Source: https://oeis.org/A306460
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A306460 (Zhi-Wei Sun, Feb 17 2019), Conjecture 1: a(n)
> 0 for all n > 0. In other words, any positive integer n can be written as the sum of a positive
hexagonal number, a triangular number and a tetrahedral number.

Conventions:
* The sequence has offset 1 (data 1, 2, 1, 1, 2, 2, 3, 3, 1, 2, 4, 3, ...). `a n` is the number of
  triples (x, y, z) of natural numbers with x > 0 and n = x*(2x-1) + y*(y+1)/2 + z*(z+1)*(z+2)/6,
  exactly as in the OEIS name.
* The natural-number subtraction 2*x - 1 is exact since x > 0, and the divisions by 2 and 6 are
  exact (products of two, respectively three, consecutive integers).
* Only Conjecture 1 of the entry is formalized.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
-/

namespace OMA.S_oeis_a306460

/-- The condition in the name of A306460 on a tuple, for a given n. -/
def P (n : ℕ) (x y z : ℕ) : Prop :=
  0 < x ∧ x * (2 * x - 1) + y * (y + 1) / 2 + z * (z + 1) * (z + 2) / 6 = n

/-- A306460: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℕ | P n t.1 t.2.1 t.2.2}

/-- The conjecture recorded in A306460. -/
theorem main : ∀ n : ℕ, 0 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a306460
