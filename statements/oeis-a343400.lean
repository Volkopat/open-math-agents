import Mathlib

/-!
# A343400: Number of ways to write n as 3^x + [y^2/3] + [z^2/4], where [.] is the floor function, x is a nonnegative integer, and y and z are positive integers.

Source: https://oeis.org/A343400
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A343400 (Zhi-Wei Sun, Apr 13 2021): a(n) > 0 for all n
> 0.

Conventions:
* The sequence has offset 1 (data 1, 2, 3, 4, 4, 5, 4, 6, 4, 9, 5, 7, ...). `a n` is the number of
  triples (x, y, z) of natural numbers with y > 0, z > 0 and n = 3^x + [y^2/3] + [z^2/4], exactly
  as in the OEIS name.
* The floor brackets [y^2/3] and [z^2/4] are the natural-number divisions `y ^ 2 / 3` and `z ^ 2 /
  4`.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
-/

namespace OMA.S_oeis_a343400

/-- The condition in the name of A343400 on a tuple, for a given n. -/
def P (n : ℕ) (x y z : ℕ) : Prop :=
  0 < y ∧ 0 < z ∧ 3 ^ x + y ^ 2 / 3 + z ^ 2 / 4 = n

/-- A343400: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℕ | P n t.1 t.2.1 t.2.2}

/-- The conjecture recorded in A343400. -/
theorem main : ∀ n : ℕ, 0 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a343400
