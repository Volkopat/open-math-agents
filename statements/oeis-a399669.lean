import Mathlib

/-!
# Goldbach partitions in OEIS A399669

Jaspal Gupta's conjecture in OEIS A399669 (November 14, 2026).
Source: https://oeis.org/A399669 (OEIS Foundation, CC BY-SA 4.0).
Formalization: @sturdy4days.

For a prime p below an even integer, its only possible partner in a
Goldbach partition is the difference between the integer and p.
-/

namespace OMA.S_oeis_a399669

theorem main : ∀ n : ℕ, 105 < n → ∃ p : ℕ, p.Prime ∧ p < 2 * n ∧
    ¬ (2 * n - p).Prime ∧ (2 * n + 2 - p).Prime := by
  sorry

end OMA.S_oeis_a399669
