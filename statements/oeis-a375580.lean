import Mathlib

/-!
# A375580: a(n) is the number of partitions n = x + y + z of positive integers such that x*y*z is a perfect cube

Source: https://oeis.org/A375580
Credit: @ceejcake

OEIS A375580 (offset 0) counts unordered partitions `n = x + y + z` into three positive
integers (`1 ≤ x ≤ y ≤ z`) such that `x * y * z` is a perfect cube.
The condition `1 ≤ x ≤ y ≤ z` with `x + y + z = n` is equivalent to
`1 ≤ x ≤ n / 3`, `x ≤ y ≤ (n - x) / 2`, and `z = n - x - y` (with no underflow since
`x + 2 * y ≤ n`). Moreover `1 ≤ x * y * z ≤ n ^ 3`, so `x * y * z` is a perfect cube
if and only if `∃ k ≤ n, x * y * z = k ^ 3`.

Initial values: `a(0)..a(25) = 0, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 2, 3, 0, 1, 1, 1`,
and `a(176) = 0`.

Conjecture (Charles R Greathouse IV, OEIS A375580):
For all `n > 176`, `a(n) > 0`.
-/

namespace OMA.S_oeis_a375580

/-- The sequence OEIS A375580: the number of partitions `n = x + y + z` of positive integers
(`1 ≤ x ≤ y ≤ z`) such that `x * y * z` is a perfect cube. -/
def a (n : ℕ) : ℕ :=
  ∑ x ∈ Finset.Icc 1 (n / 3),
    ((Finset.Icc x ((n - x) / 2)).filter fun y =>
      ∃ k ≤ n, x * y * (n - x - y) = k ^ 3).card

/-- Conjecture (Charles R Greathouse IV, OEIS A375580):
for every `n > 176`, `a(n) > 0`. -/
theorem main : ∀ n : ℕ, 176 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a375580
