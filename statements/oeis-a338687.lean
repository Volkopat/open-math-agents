import Mathlib

/-!
# A338687: Number of ways to write n as x^4 + y^2 + floor(z^2/7), where x,y,z are integers with x >= 0, y >= 1 and z >= 2.

Source: https://oeis.org/A338687
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A338687 (Zhi-Wei Sun, Apr 23 2021): a(n) > 0 for all n
> 0.

Conventions:
* The sequence has offset 1 (data 1, 2, 2, 3, 3, 3, 3, 2, 3, 4, 4, 4, ...). `a n` is the number of
  triples (x, y, z) of natural numbers with y >= 1, z >= 2 and n = x^4 + y^2 + floor(z^2/7),
  exactly as in the OEIS name.
* floor(z^2/7) is the natural-number division `z ^ 2 / 7`.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
-/

namespace OMA.S_oeis_a338687

/-- The condition in the name of A338687 on a tuple, for a given n. -/
def P (n : ℕ) (x y z : ℕ) : Prop :=
  1 ≤ y ∧ 2 ≤ z ∧ x ^ 4 + y ^ 2 + z ^ 2 / 7 = n

/-- A338687: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℕ | P n t.1 t.2.1 t.2.2}

/-- The conjecture recorded in A338687. -/
theorem main : ∀ n : ℕ, 0 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a338687
