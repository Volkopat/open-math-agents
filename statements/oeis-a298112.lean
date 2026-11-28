import Mathlib

/-!
# A298112: Solution b( ) of the complementary equation a(n) = a(1)*b(n) - a(0)*b(n-1) + 3*n, where a(0) = 1, a(1) = 2, b(0) = 3, b(1) = 4, b(2) = 5, and (b(n)) is the increasing sequence of positive integers not in (a(n)).  See Comments.

Source: https://oeis.org/A298112
Credit: @agchua

Comment of A298112 (unsigned; the entry is by Clark Kimberling):
  Conjecture:  2/5 < a(n) - n*sqrt(2) < 3 for n >= 1.
In the comment a(n) is the term of this entry, A298112(n), which is b(n) of the name (offset 0;
data 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 17, ...). The entry says that the increasing
complementary sequences a() (A298001) and b() are uniquely determined by the equation and the
initial values. IsSolution states these defining conditions: the initial values, the equation for
n >= 2 (for n = 1 it would give a(1) = 2*4 - 3 + 3 = 8, not 2), both sequences strictly increasing,
and b the increasing sequence of the positive integers not in a. The conjecture is stated for every
pair satisfying them, for n >= 1.
-/

namespace OMA.S_oeis_a298112

/-- The defining conditions of the pair (a, b) = (A298001, A298112). -/
def IsSolution (a b : ℕ → ℕ) : Prop :=
  a 0 = 1 ∧ a 1 = 2 ∧ b 0 = 3 ∧ b 1 = 4 ∧ b 2 = 5 ∧
  (∀ n : ℕ, 2 ≤ n → (a n : ℤ) = a 1 * b n - a 0 * b (n - 1) + 3 * n) ∧
  StrictMono a ∧ StrictMono b ∧
  (∀ m : ℕ, 1 ≤ m → (m ∈ Set.range b ↔ m ∉ Set.range a))

/-- The comment's conjecture for the terms b(n) = A298112(n): 2/5 < b(n) - n sqrt 2 < 3 for
n >= 1. -/
theorem main : ∀ a b : ℕ → ℕ, IsSolution a b → ∀ n : ℕ, 1 ≤ n →
    (2 : ℝ) / 5 < (b n : ℝ) - n * Real.sqrt 2 ∧ (b n : ℝ) - n * Real.sqrt 2 < 3 := by
  sorry

end OMA.S_oeis_a298112
