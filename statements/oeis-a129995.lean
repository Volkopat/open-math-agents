import Mathlib

/-!
# A129995: An integer-valued factorial quotient

Source: https://oeis.org/A129995
Formalization: AI-generated with Codex, submitted by @Genbox.

The entry defines a(n) as the product of n + 1, n² + 2, n³ + 3, and n⁴ + 4,
divided by 4!. Its comment records that the factorial-quotient integrality
property holds for four factors. The offset is zero, so the statement includes
all nonnegative integers n. The first three values are 1, 5, and 165.
-/

namespace OMA.S_oeis_a129995

def numerator (n : ℕ) : ℕ := (n + 1) * (n ^ 2 + 2) * (n ^ 3 + 3) * (n ^ 4 + 4)

def a (n : ℕ) : ℚ := (numerator n : ℚ) / (Nat.factorial 4 : ℚ)

theorem main : ∀ n : ℕ, ∃ z : ℤ, a n = (z : ℚ) := by
  sorry

end OMA.S_oeis_a129995