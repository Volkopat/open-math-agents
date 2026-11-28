import Mathlib

/-!
# A197879: no three consecutive equal terms in the parity of floor(n*sqrt(8))

Source: https://oeis.org/A197879
Credit: @ivillar

A197879 is the parity of floor(n*sqrt(8)) (offset 1; data 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 1, ...).
Andres Cicuttin (Jul 09 2019) comments: if the fractional part of sqrt(2)*n is > 1/2 then
a(n) = 1, otherwise a(n) = 0; it is possible to see from this that, since
5/4 < sqrt(2) < 7/4, there are no more than two consecutive 0's or 1's.

Status: known result (Andres Cicuttin, Jul 09 2019, with the argument sketched in the entry).

Formalization notes:
* `a n` is `floor(n * sqrt 8) mod 2`, with the natural-number floor (the argument is
  nonnegative).
* The first claim is stated with `Int.fract (sqrt 2 * n)` for the fractional part. "No more than
  two consecutive 0's or 1's" is stated as: there is no n >= 1 with a(n) = a(n+1) = a(n+2).
-/

namespace OMA.S_oeis_a197879

/-- A197879(n): the parity of `floor(n * sqrt 8)`. -/
noncomputable def a (n : ℕ) : ℕ := ⌊(n : ℝ) * Real.sqrt 8⌋₊ % 2

/-- Cicuttin's description of `a` by the fractional part of `sqrt 2 * n`, and the absence of
three consecutive equal terms. -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → a n = if 1 / 2 < Int.fract (Real.sqrt 2 * n) then 1 else 0) ∧
    (∀ n : ℕ, 1 ≤ n → ¬ (a n = a (n + 1) ∧ a (n + 1) = a (n + 2))) := by
  sorry

end OMA.S_oeis_a197879
