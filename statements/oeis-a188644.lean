import Mathlib

/-!
# A188644: Array of (k^n + k^(-n))/2 where k = (sqrt(x^2-1) + x)^2 for integers x >= 1.

Source: https://oeis.org/A188644
Credit: @agchua

Comment of A188644 (unsigned; the entry is by Charles L. Hohn, Apr 06 2011):
  Conjecture: Given the function f(x,y) = (sqrt(x^2+y) + x)^2 and constant k=f(x,y), then for all
  integers x >= 1 and y=[+-]1, k may be irrational, but (k^n + k^(-n))/2 always produces integer
  sequences; y=-1 results shown here; y=1 results are A188645.
The sequences are indexed by n >= 0 (the columns of the array start at 0). For x >= 1 and
y = 1 or y = -1 the radicand x^2 + y is nonnegative, so Real.sqrt is the usual square root, and
k >= 1, so k^(-n) is the inverse of k^n (an integer power with negative exponent).
-/

namespace OMA.S_oeis_a188644

/-- f(x,y) = (sqrt(x^2+y) + x)^2, a real number. -/
noncomputable def f (x y : ℤ) : ℝ := (Real.sqrt ((x : ℝ) ^ 2 + y) + x) ^ 2

/-- The comment's conjecture: for all integers x >= 1 and y = 1 or y = -1, with k = f(x,y),
every value (k^n + k^(-n))/2, n >= 0, is an integer. -/
theorem main : ∀ x y : ℤ, 1 ≤ x → (y = 1 ∨ y = -1) → ∀ n : ℕ,
    ∃ m : ℤ, (f x y ^ n + f x y ^ (-(n : ℤ))) / 2 = (m : ℝ) := by
  sorry

end OMA.S_oeis_a188644
