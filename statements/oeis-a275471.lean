import Mathlib

/-!
# A275471: Number of ordered ways to write n as 4^k*(1+x^2+y^2)+z^2, where k,x,y,z are nonnegative integers with x <= y and x == y (mod 2).

Source: https://oeis.org/A275471
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A275471 (Zhi-Wei Sun, Aug 11 2016): a(n) > 0 except for
n = 449.

Conventions:
* The sequence has offset 1 (data 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 3, ...). `a n` is the number of
  quadruples (k, x, y, z) of natural numbers with x <= y, x == y (mod 2) and n = 4^k*(1+x^2+y^2) +
  z^2, exactly as in the OEIS name.
* The statement `a(n) > 0 except for n = 449` is rendered as an equivalence for every n >= 1 (the
  offset): a(n) > 0 if and only if n is not 449.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
-/

namespace OMA.S_oeis_a275471

/-- The condition in the name of A275471 on a tuple, for a given n. -/
def P (n : ℕ) (k x y z : ℕ) : Prop :=
  x ≤ y ∧ x % 2 = y % 2 ∧ 4 ^ k * (1 + x ^ 2 + y ^ 2) + z ^ 2 = n

/-- A275471: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℕ × ℕ | P n t.1 t.2.1 t.2.2.1 t.2.2.2}

/-- The conjecture recorded in A275471. -/
theorem main : ∀ n : ℕ, 0 < n → (0 < a n ↔ n ≠ 449) := by
  sorry

end OMA.S_oeis_a275471
