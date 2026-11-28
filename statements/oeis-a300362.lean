import Mathlib

/-!
# A300362: Number of ways to write n^2 as x^2 + y^2 + z^2 + w^2 with x,y,z,w nonnegative integers such that x + 2*y and (z + 2*w)/3 are squares and w is even.

Source: https://oeis.org/A300362
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A300362 (Zhi-Wei Sun, Mar 04 2018): a(n) > 0 for all n
= 0,1,2,..., and a(n) = 1 only for n = 0, 7, 9, 14, 19, 22, 26, 34, 41, 4^k*m (k = 0,1,... and m =
1, 2, 3, 5, 10, 11, 13, 15).

Conventions:
* The sequence has offset 0 (data 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, ...). `a n` is the number of
  quadruples (x, y, z, w) of natural numbers with n^2 = x^2 + y^2 + z^2 + w^2 such that x + 2*y
  and (z + 2*w)/3 are squares and w is even, exactly as in the OEIS name.
* `a square` is the Mathlib predicate `IsSquare` (0 included).
* `(z + 2*w)/3 is a square` requires the quotient to be an integer: it is stated as 3 dividing z +
  2*w together with the (then exact) quotient being a square.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
* The `a(n) = 1 only for` part is rendered literally as an only-if: a(n) = 1 implies that n is one
  of the listed values.
-/

namespace OMA.S_oeis_a300362

/-- The condition in the name of A300362 on a tuple, for a given n. -/
def P (n : ℕ) (x y z w : ℕ) : Prop :=
  x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n ^ 2 ∧ IsSquare (x + 2 * y) ∧ 3 ∣ z + 2 * w ∧
  IsSquare ((z + 2 * w) / 3) ∧ Even w

/-- A300362: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℕ × ℕ | P n t.1 t.2.1 t.2.2.1 t.2.2.2}

/-- The conjecture recorded in A300362. -/
theorem main : ∀ n : ℕ, 0 < a n ∧ (a n = 1 →
      n ∈ ({0, 7, 9, 14, 19, 22, 26, 34, 41} : Finset ℕ) ∨
      (∃ k m : ℕ, m ∈ ({1, 2, 3, 5, 10, 11, 13, 15} : Finset ℕ) ∧ n = 4 ^ k * m)) := by
  sorry

end OMA.S_oeis_a300362
