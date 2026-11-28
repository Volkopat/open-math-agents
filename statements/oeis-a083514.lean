import Mathlib

/-!
# A083514: Number of steps for iteration of map x -> (4/3)*ceiling(x) to reach an integer > 3n+1 when started at 3n+1, or -1 if no such integer is ever reached.

Source: https://oeis.org/A083514
Credit: @gblacher2

Conjecture (comment section of A083514):
"It is conjectured that an integer is always reached."

The sequence has offset 0: 3, 2, 8, 7, 2, 3, 5, 2, 6, 3, 2, 5, ... (Benoit Cloitre, Sep 28 2003).
For example, for n = 0: 1 -> 4/3 -> 8/3 -> 4, so a(0) = 3.

Modelling choices:
* The map is `f x = (4/3) * ⌈x⌉` on the rationals, iterated from x = 3n+1 as in the PARI
  program of the entry (`c=(3*n+1)*4/3; ... while(frac(c)>0, c=4/3*ceil(c); ...)`).
* "An integer is reached" means that some iterate `f^[k] (3n+1)` with k ≥ 1 is an integer.
  The name asks for an integer > 3n+1; this is stated explicitly. (Every iterate with k ≥ 1
  is > 3n+1 anyway, since f x ≥ (4/3) x > x for x > 0.)
* The conjecture is that this holds for every n ≥ 0, i.e. that the value -1 never occurs.
-/

namespace OMA.S_oeis_a083514

/-- The map x ↦ (4/3) * ⌈x⌉ on the rationals. -/
def f (x : ℚ) : ℚ := 4 / 3 * (⌈x⌉ : ℚ)

/-- The conjecture: for every n ≥ 0, iterating `f` from 3n+1 reaches an integer > 3n+1. -/
theorem main : ∀ n : ℕ, ∃ k : ℕ, 1 ≤ k ∧ ∃ m : ℤ,
    f^[k] ((3 * n + 1 : ℕ) : ℚ) = (m : ℚ) ∧ ((3 * n + 1 : ℕ) : ℤ) < m := by
  sorry

end OMA.S_oeis_a083514
