import Mathlib

/-!
# A383131: a negating Collatz map on the integers

Source: https://oeis.org/A383131

A383131 (Ya-Ping Lu): a(n) is the number of iterations that n requires to reach 1 under the map
x -> -x/2 if x is even, 3x + 1 if x is odd; a(n) = -1 if 1 is never reached.
Conjecture (in the entry): a(n) != -1 for any positive or negative integer n.

Conventions:
* The map acts on `ℤ`; for even x the quotient x/2 is exact.
* Reaching 1 means `f^[k] n = 1` for some k >= 0; n ranges over all nonzero integers
  (0 is a fixed point and is excluded by the conjecture's wording).
-/

namespace OMA.S_oeis_a383131

/-- The map `x ↦ -x/2` for even `x` and `x ↦ 3x + 1` for odd `x`. -/
def f (x : ℤ) : ℤ := if Even x then -(x / 2) else 3 * x + 1

/-- Every nonzero integer eventually reaches `1`. -/
theorem main : ∀ n : ℤ, n ≠ 0 → ∃ k : ℕ, f^[k] n = 1 := by
  sorry

end OMA.S_oeis_a383131
