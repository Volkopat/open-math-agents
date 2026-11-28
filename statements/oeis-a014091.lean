import Mathlib

/-!
# A014091: Numbers that are the sum of 2 primes.

Source: https://oeis.org/A014091
Credit: @Nealanio

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_oeis_a014091

theorem main : ∀ n : ℕ, 2 < n → n % 2 = 0 →
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ n = p + q := by
  sorry

end OMA.S_oeis_a014091
