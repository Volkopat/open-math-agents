import Mathlib

/-!
# A020735: Odd numbers >= 5.

Source: https://oeis.org/A020735
Credit: @Nealanio

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_oeis_a020735

theorem main : ∀ n : ℕ, n % 2 = 1 → 5 ≤ n →
    ∃ m p : ℕ, Nat.Prime p ∧ n = m ^ 2 + m + p := by
  sorry

end OMA.S_oeis_a020735
