import Mathlib

/-!
# A303428: Number of ways to write n as x*(3*x-2) + y*(3*y-2) + 3^u + 3^v, where x,y,u,v are integers with x <= y and 0 <= u <= v.

Source: https://oeis.org/A303428
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A303428 (Zhi-Wei Sun, Apr 23 2018): a(n) > 0 for all n
> 1. Moreover, any integer n > 1 can be written as x*(3*x+2) + y*(3*y+2) + 3^z + 3^w, where x is
an integer and y,z,w are nonnegative integers.

Conventions:
* The sequence has offset 1 (data 0, 1, 1, 2, 1, 2, 2, 2, 1, 3, 3, 5, ...). `a n` is the number of
  quadruples (x, y, u, v) with x, y integers, u, v natural numbers, x <= y, u <= v and n =
  x*(3*x-2) + y*(3*y-2) + 3^u + 3^v, exactly as in the OEIS name.
* Integer variables range over `ℤ`; the equation and the side conditions involving them are stated
  in `ℤ`, with the natural variables and n cast.
* Both sentences of the conjecture are formalized, as a conjunction.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
-/

namespace OMA.S_oeis_a303428

/-- The condition in the name of A303428 on a tuple, for a given n. -/
def P (n : ℕ) (x y : ℤ) (u v : ℕ) : Prop :=
  x ≤ y ∧ u ≤ v ∧ x * (3 * x - 2) + y * (3 * y - 2) + 3 ^ u + 3 ^ v = (n : ℤ)

/-- A303428: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℤ × ℤ × ℕ × ℕ | P n t.1 t.2.1 t.2.2.1 t.2.2.2}

/-- The conjecture recorded in A303428. -/
theorem main : (∀ n : ℕ, 1 < n → 0 < a n) ∧
    (∀ n : ℕ, 1 < n → ∃ (x : ℤ) (y z w : ℕ),
      x * (3 * x + 2) + (y : ℤ) * (3 * (y : ℤ) + 2) + 3 ^ z + 3 ^ w = (n : ℤ)) := by
  sorry

end OMA.S_oeis_a303428
