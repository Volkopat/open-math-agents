import Mathlib

/-!
# The linear search bound conjecture in A085427

Source: https://oeis.org/A085427.
The conjecture asserts that for every positive exponent n there
is a positive multiplier k strictly below 3n for which k·2^n−1
is prime.
-/

namespace OMA.S_oeis_a085427

theorem main : ∀ n : ℕ, 0 < n → ∃ k : ℕ, 0 < k ∧ k < 3*n ∧ (k*2^n-1).Prime := by
  sorry

end OMA.S_oeis_a085427
