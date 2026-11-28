import Mathlib

/-!
# A272620: Number of ordered ways to write n as w^2 + x^2 + y^2 + z^2 with w + x + y - z a square, where w is an integer and x,y,z are nonnegative integers with |w| <= x >= y <= z < x + y.

Source: https://oeis.org/A272620
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A272620 (Zhi-Wei Sun, May 03 2016): a(n) > 0 for all n
> 0.

Conventions:
* The sequence has offset 1 (data 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, ...). `a n` is the number of
  quadruples (w, x, y, z) with w an integer, x, y, z natural numbers, |w| <= x >= y <= z < x + y,
  w + x + y - z a square and n = w^2 + x^2 + y^2 + z^2, exactly as in the OEIS name.
* Integer variables range over `ℤ`; the equation and the side conditions involving them are stated
  in `ℤ`, with the natural variables and n cast.
* `a square` means the square of an integer (0 included), which is Mathlib's `IsSquare`; the
  quantity is computed in `ℤ` (with the natural variables cast), where a negative value is never a
  square.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
-/

namespace OMA.S_oeis_a272620

/-- The condition in the name of A272620 on a tuple, for a given n. -/
def P (n : ℕ) (w : ℤ) (x y z : ℕ) : Prop :=
  |w| ≤ (x : ℤ) ∧ y ≤ x ∧ y ≤ z ∧ z < x + y ∧ IsSquare (w + (x : ℤ) + (y : ℤ) - (z : ℤ)) ∧
    w ^ 2 + (x : ℤ) ^ 2 + (y : ℤ) ^ 2 + (z : ℤ) ^ 2 = (n : ℤ)

/-- A272620: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℤ × ℕ × ℕ × ℕ | P n t.1 t.2.1 t.2.2.1 t.2.2.2}

/-- The conjecture recorded in A272620. -/
theorem main : ∀ n : ℕ, 0 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a272620
