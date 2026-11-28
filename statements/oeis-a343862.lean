import Mathlib

/-!
# A343862: Number of ways to write n as x + y + z with x, y, z positive integers such that x^2*y^2 + 5*y^2*z^2 + 10*z^2*x^2 is a square.

Source: https://oeis.org/A343862
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A343862 (Zhi-Wei Sun, May 02 2021), Conjecture 1: a(n)
> 0 for all n > 2.

Conventions:
* The sequence has offset 1 (data 0, 0, 1, 1, 1, 2, 2, 1, 1, 4, 2, 4, ...). `a n` is the number of
  triples (x, y, z) of positive integers with x^2*y^2 + 5*y^2*z^2 + 10*z^2*x^2 a square and n = x
  + y + z, exactly as in the OEIS name.
* `a square` means the square of an integer (0 included), which is Mathlib's `IsSquare`.
* Only Conjecture 1 of the entry is formalized.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
-/

namespace OMA.S_oeis_a343862

/-- The condition in the name of A343862 on a tuple, for a given n. -/
def P (n : ℕ) (x y z : ℕ) : Prop :=
  0 < x ∧ 0 < y ∧ 0 < z ∧ IsSquare (x ^ 2 * y ^ 2 + 5 * y ^ 2 * z ^ 2 + 10 * z ^ 2 * x ^ 2) ∧
    x + y + z = n

/-- A343862: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℕ | P n t.1 t.2.1 t.2.2}

/-- The conjecture recorded in A343862. -/
theorem main : ∀ n : ℕ, 2 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a343862
