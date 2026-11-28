import Mathlib

/-!
# Primes between consecutive real powers

T. D. Noe's conjecture in OEIS A144256 uses the closed interval. At
the threshold exponent, 127 is a shared endpoint for n = 15 and n = 16.

Source: https://oeis.org/A144256
Credit: @jacklarmer
-/

namespace OMA.S_oeis_a144256

theorem main : ∀ n : ℕ, 0 < n → ∀ k : ℝ, Real.log 127 / Real.log 16 ≤ k →
    ∃ p : ℕ, p.Prime ∧ (n : ℝ) ^ k ≤ (p : ℝ) ∧ (p : ℝ) ≤ ((n : ℝ) + 1) ^ k := by
  sorry

end OMA.S_oeis_a144256
