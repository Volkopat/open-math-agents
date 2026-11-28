import Mathlib

/-!
# A297830: Solution of the complementary equation a(n) = a(1)*b(n-1) - a(0)*b(n-2) + 2*n, where a(0) = 1, a(1) = 2, b(0) = 3, b(1) = 4, and (b(n)) is the increasing sequence of positive integers not in (a(n)).  See Comments.

Source: https://oeis.org/A297830
Credit: @agchua

Comment of A297830 (entry by Clark Kimberling, Feb 04 2018):
  The increasing complementary sequences a() and b() are uniquely determined by the titular equation and initial values. Conjecture: a(n) - (2 +sqrt(2))*n < 3 for n >= 1.
Offset is 0; data 1, 2, 9, 12, 15, 18, 21, 26, 28, 33, ... (b(n) is A298003). IsSolution states
the defining conditions: the initial values a(0) = 1, a(1) = 2, b(0) = 3, b(1) = 4, the equation
for n >= 2 (the lowest index where n - 2 >= 0), both sequences strictly increasing, and b the
increasing sequence of positive integers not in a. The conjecture is stated for every pair
satisfying them, for all n >= 1.
-/

namespace OMA.S_oeis_a297830

/-- The defining conditions of the pair (a, b) = (A297830, A298003). -/
def IsSolution (a b : ℕ → ℕ) : Prop :=
  a 0 = 1 ∧ a 1 = 2 ∧ b 0 = 3 ∧ b 1 = 4 ∧
  (∀ n : ℕ, 2 ≤ n → (a n : ℤ) = a 1 * b (n - 1) - a 0 * b (n - 2) + 2 * n) ∧
  StrictMono a ∧ StrictMono b ∧
  (∀ m : ℕ, 1 ≤ m → (m ∈ Set.range b ↔ m ∉ Set.range a))

/-- The comment's conjecture for a(n) = A297830(n): a(n) - (2 + sqrt 2) * n < 3 for n >= 1. -/
theorem main : ∀ a b : ℕ → ℕ, IsSolution a b → ∀ n : ℕ, 1 ≤ n →
    (a n : ℝ) - (2 + Real.sqrt 2) * n < 3 := by
  sorry

end OMA.S_oeis_a297830
