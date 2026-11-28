import Mathlib

/-!
# A389852: n + d^3 as a sum of three positive cubes

Source: https://oeis.org/A389852

A389852 (Zhining Yang), offset 1: a(n) is the least positive integer d such that n + d^3 is the
sum of 3 positive cubes. Conjecture (in the entry): a(n) exists for all positive integers n.

Conventions:
* Existence of a(n) means: some positive d and positive x, y, z with n + d^3 = x^3 + y^3 + z^3
  (the least such d then exists automatically).
-/

namespace OMA.S_oeis_a389852

/-- For every `n ≥ 1` there is `d ≥ 1` with `n + d^3` a sum of three positive cubes. -/
theorem main : ∀ n : ℕ, 0 < n → ∃ d x y z : ℕ, 0 < d ∧ 0 < x ∧ 0 < y ∧ 0 < z ∧
    n + d ^ 3 = x ^ 3 + y ^ 3 + z ^ 3 := by
  sorry

end OMA.S_oeis_a389852
