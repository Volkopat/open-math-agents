import Mathlib

/-!
# A338162: Number of ways to write 4*n + 1 as x^2 + y^2 + z^2 + w^2 with x^2 + 7*y^2 = 2^k for some k = 0,1,2,..., where x, y, z, w are nonnegative integers with z <= w.

Source: https://oeis.org/A338162
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A338162 (Zhi-Wei Sun, Oct 14 2020), first sentence:
a(n) > 0 for all n >= 0.

Conventions:
* The sequence has offset 0 (data 1, 2, 3, 2, 4, 4, 2, 3, 6, 3, 7, 6, ...). `a n` is the number of
  quadruples (x, y, z, w) of natural numbers with 4*n+1 = x^2 + y^2 + z^2 + w^2, z <= w and x^2 +
  7*y^2 = 2^k for some k = 0,1,2,..., exactly as in the OEIS name.
* Only the first sentence of the conjecture is formalized; its `Moreover` sentence is a different
  statement.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
-/

namespace OMA.S_oeis_a338162

/-- The condition in the name of A338162 on a tuple, for a given n. -/
def P (n : ℕ) (x y z w : ℕ) : Prop :=
  x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = 4 * n + 1 ∧ z ≤ w ∧ ∃ k : ℕ, x ^ 2 + 7 * y ^ 2 = 2 ^ k

/-- A338162: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℕ × ℕ | P n t.1 t.2.1 t.2.2.1 t.2.2.2}

/-- The conjecture recorded in A338162. -/
theorem main : ∀ n : ℕ, 0 < a n := by
  sorry

end OMA.S_oeis_a338162
