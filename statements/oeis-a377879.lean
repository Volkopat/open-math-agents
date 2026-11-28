import Mathlib

/-!
# OEIS A377879

Source: https://oeis.org/A377879
Credit: @sassmama27

The sequence starts at n = 1. Here sigma(n²) is the sum of the positive
divisors of n², and the deficiency is computed in the integers.
-/

namespace OMA.S_oeis_a377879

open scoped BigOperators

def deficiency (n : ℕ) : ℤ :=
  2 * (n : ℤ) ^ 2 - ∑ d ∈ (n ^ 2).divisors, (d : ℤ)

theorem main : ∀ n : ℕ, 0 < n →
    (deficiency n = 1 → ∃ k : ℕ, n = 2 ^ k) ∧ deficiency n ≠ -1 := by
  sorry

end OMA.S_oeis_a377879
