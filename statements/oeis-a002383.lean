import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# A002383: Primes of the form `k^2 + k + 1`

Source: https://oeis.org/A002383
Related sequences: https://oeis.org/A085104 and https://oeis.org/A059055
Credit: @MMexicann
-/

open scoped BigOperators

namespace OMA.S_oeis_a002383

/-- A002383 with 3 removed equals the intersection of A085104 and A059055.
The quotient in the definition of A059055 is an exact quotient. -/
theorem main :
    ∀ p : ℕ,
      (Nat.Prime p ∧ p ≠ 3 ∧ ∃ k : ℕ, p = k ^ 2 + k + 1) ↔
        ((Nat.Prime p ∧ ∃ b k : ℕ, 1 < b ∧ 1 < k ∧
            p = ∑ i ∈ Finset.range (k + 1), b ^ i) ∧
          (Nat.Prime p ∧ ∃ b k : ℕ, 0 < b ∧ 0 < k ∧ p * (b + 1) = b ^ k + 1)) := by
  sorry

end OMA.S_oeis_a002383
