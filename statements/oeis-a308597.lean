import Mathlib

/-!
# Sun's representation conjecture for A308597

Source: https://oeis.org/A308597.
The conjecture says every positive n is the sum of two triangular
numbers and a term 2^c·5^d with c nonnegative and d equal to 0 or 1.
The two triangular indices are nonnegative and nondecreasing.
-/

namespace OMA.S_oeis_a308597

def triangular (a : ℕ) : ℕ := a*(a+1)/2

theorem main : ∀ n : ℕ, 0 < n → ∃ a b c d : ℕ, a ≤ b ∧ d ≤ 1 ∧
    n = triangular a + triangular b + 2^c * 5^d := by
  sorry

end OMA.S_oeis_a308597
