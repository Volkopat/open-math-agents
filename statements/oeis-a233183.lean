import Mathlib

/-!
# OEIS A233183

Zhi-Wei Sun conjectures that every term with index greater than two is positive.
The sequence counts decompositions, so positivity means that a pair exists.
OEIS numbers the primes starting at one, while `Nat.nth` starts at zero.

Source: https://oeis.org/A233183
Credit: @baejh3333-del
-/

namespace OMA.S_oeis_a233183

theorem main : ∀ n : ℕ, 2 < n →
    ∃ k m : ℕ, 0 < k ∧ k < m ∧ n = k + m ∧
      Nat.Prime (Nat.choose (2 * k) k + Nat.nth Nat.Prime (m - 1)) := by
  sorry

end OMA.S_oeis_a233183
