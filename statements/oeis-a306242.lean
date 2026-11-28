import Mathlib

/-!
# A306242: Number of ways to write n as x*(3x+1) + y*(3y-1) + z*(3z+2) + w*(3w-2), where x,y,z,w are nonnegative integers.

Source: https://oeis.org/A306242
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A306242 (Zhi-Wei Sun, Jan 31 2019): a(n) > 0 for all n
>= 0, and a(n) = 1 only for n = 0, 1, 2, 3, 4, 9, 13. Moreover, any nonnegative integer n can be
written as x*(3x+1) + y*(3y-1) + z*(3z+2) + w*(3w-2), where x,y,z,w are nonnegative integers with
x or y even.

Conventions:
* The sequence has offset 0 (data 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 3, 2, ...). `a n` is the number of
  quadruples (x, y, z, w) of natural numbers with n = x*(3x+1) + y*(3y-1) + z*(3z+2) + w*(3w-2),
  exactly as in the OEIS name.
* The subtractions 3*y - 1 and 3*w - 2 are natural-number subtractions; they are truncated only at
  y = 0 and w = 0, where the products y*(3y-1) and w*(3w-2) are 0 in any case.
* Both sentences are formalized, as a conjunction.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
* The `a(n) = 1 only for` part is rendered literally as an only-if: a(n) = 1 implies that n is one
  of the listed values.
-/

namespace OMA.S_oeis_a306242

/-- The condition in the name of A306242 on a tuple, for a given n. -/
def P (n : ℕ) (x y z w : ℕ) : Prop :=
  x * (3 * x + 1) + y * (3 * y - 1) + z * (3 * z + 2) + w * (3 * w - 2) = n

/-- A306242: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℕ × ℕ | P n t.1 t.2.1 t.2.2.1 t.2.2.2}

/-- The conjecture recorded in A306242. -/
theorem main : (∀ n : ℕ, 0 < a n ∧ (a n = 1 →
      n ∈ ({0, 1, 2, 3, 4, 9, 13} : Finset ℕ))) ∧
    (∀ n : ℕ, ∃ x y z w : ℕ, (Even x ∨ Even y) ∧
      x * (3 * x + 1) + y * (3 * y - 1) + z * (3 * z + 2) + w * (3 * w - 2) = n) := by
  sorry

end OMA.S_oeis_a306242
