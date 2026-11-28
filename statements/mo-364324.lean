import Mathlib

/-!
# GCDs of two sequences of integer parts

Source: https://mathoverflow.net/q/364324

The question asks whether every positive integer occurs infinitely often as the GCD
of the integer parts of `n * √2` and `n * √3`, for positive integers `n`.
-/

namespace OMA.S_mo_364324

theorem main : ∀ m : ℕ, 0 < m →
    {n : ℕ | 0 < n ∧ Nat.gcd ⌊(n : ℝ) * Real.sqrt 2⌋₊ ⌊(n : ℝ) * Real.sqrt 3⌋₊ = m}.Infinite := by
  sorry

end OMA.S_mo_364324
