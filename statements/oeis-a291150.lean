import Mathlib

/-!
# A291150: Number of ways to write 2*n+1 as x^2 + y^2 + z^2 + 4*w^2, where x,y,z,w are nonnegative integers with x <= y <= z such that 2^x + 2^y + 2^z + 1 is prime.

Source: https://oeis.org/A291150
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A291150 (Zhi-Wei Sun, Aug 19 2017), part (i): a(n) > 0
for all n = 0,1,2,..., and a(n) = 1 only for n = 0, 1, 2, 3, 5, 7, 11, 14, 15, 21, 23, 35, 41, 43,
59, 71, 309, 435.

Conventions:
* The sequence has offset 0 (data 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, ...). `a n` is the number of
  quadruples (x, y, z, w) of natural numbers with 2*n+1 = x^2 + y^2 + z^2 + 4*w^2, x <= y <= z and
  2^x + 2^y + 2^z + 1 prime, exactly as in the OEIS name.
* Only part (i) of the conjecture is formalized; the other parts are different statements.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
* The `a(n) = 1 only for` part is rendered literally as an only-if: a(n) = 1 implies that n is one
  of the listed values.
-/

namespace OMA.S_oeis_a291150

/-- The condition in the name of A291150 on a tuple, for a given n. -/
def P (n : ℕ) (x y z w : ℕ) : Prop :=
  x ^ 2 + y ^ 2 + z ^ 2 + 4 * w ^ 2 = 2 * n + 1 ∧ x ≤ y ∧ y ≤ z ∧
  (2 ^ x + 2 ^ y + 2 ^ z + 1).Prime

/-- A291150: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℕ × ℕ | P n t.1 t.2.1 t.2.2.1 t.2.2.2}

/-- The conjecture recorded in A291150. -/
theorem main : ∀ n : ℕ, 0 < a n ∧ (a n = 1 →
      n ∈ ({0, 1, 2, 3, 5, 7, 11, 14, 15, 21, 23, 35, 41, 43, 59, 71, 309, 435} : Finset ℕ)) := by
  sorry

end OMA.S_oeis_a291150
