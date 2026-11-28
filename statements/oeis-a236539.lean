import Mathlib

/-!
# Fibonacci-sided triangles of integer area (OEIS A236539)

Michel Lagneau conjectures that (5, 5, 8), of area 12, is the only such
triangle (OEIS A236539, 28 January 2014). Sorting the side lengths counts
triangles up to congruence. For positive sides in increasing order, the
strict inequality `c < a + b` excludes degenerate triangles. Heron's
formula in the form `16 * A^2 = (a+b+c)*(a+b-c)*(a+c-b)*(b+c-a)` tests
the area without taking a square root. All four factors are positive here.

Source: https://oeis.org/A236539
Credit: @Aryan-Poonacha
-/

namespace OMA.S_oeis_a236539

/-- Integer-area triangles whose three side lengths are Fibonacci numbers. -/
theorem main : ∀ a b c A : ℕ,
    (0 < a ∧ a ≤ b ∧ b ≤ c ∧ c < a + b ∧ 0 < A ∧
      (∃ i, Nat.fib i = a) ∧ (∃ j, Nat.fib j = b) ∧ (∃ k, Nat.fib k = c) ∧
      16 * A ^ 2 = (a+b+c) * (a+b-c) * (a+c-b) * (b+c-a)) ↔
    a = 5 ∧ b = 5 ∧ c = 8 ∧ A = 12 := by
  sorry

end OMA.S_oeis_a236539
