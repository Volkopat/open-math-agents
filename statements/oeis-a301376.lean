import Mathlib

/-!
# A301376: Number of ways to write n^2 as x^2 + y^2 + z^2 + w^2 with x,y,z,w nonnegative integers and z <= w such that x^2-(3*y)^2 = 4^k for some k = 0,1,2,....

Source: https://oeis.org/A301376
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A301376 (Zhi-Wei Sun, Mar 19 2018), first sentence:
a(n) > 0 for all n > 0.

Conventions:
* The sequence has offset 1 (data 1, 1, 2, 1, 1, 3, 1, 1, 4, 2, 2, 3, ...). `a n` is the number of
  quadruples (x, y, z, w) of natural numbers with n^2 = x^2 + y^2 + z^2 + w^2, z <= w, such that
  x^2 - (3*y)^2 = 4^k for some k = 0,1,2,..., exactly as in the OEIS name.
* The equation x^2 - (3*y)^2 = 4^k is written without subtraction as x^2 = (3*y)^2 + 4^k.
* Only the first sentence of the conjecture is formalized; its `Moreover` sentence is a different
  statement.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
-/

namespace OMA.S_oeis_a301376

/-- The condition in the name of A301376 on a tuple, for a given n. -/
def P (n : ℕ) (x y z w : ℕ) : Prop :=
  x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n ^ 2 ∧ z ≤ w ∧ ∃ k : ℕ, x ^ 2 = (3 * y) ^ 2 + 4 ^ k

/-- A301376: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℕ × ℕ | P n t.1 t.2.1 t.2.2.1 t.2.2.2}

/-- The conjecture recorded in A301376. -/
theorem main : ∀ n : ℕ, 0 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a301376
