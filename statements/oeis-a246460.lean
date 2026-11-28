import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Integrality of OEIS A246460

For each positive n the sequence divides a weighted sum of squared binomial
coefficients by n². Since the numerator is a natural number, its divisibility
by n² expresses exactly that the quotient is an integer.

The OEIS entry credits Zhi-Wei Sun with a proof in arXiv:1408.5381.
Source: https://oeis.org/A246460 (OEIS Foundation, CC BY-SA 4.0).
-/

namespace OMA.S_oeis_a246460

theorem main : ∀ n : ℕ, 0 < n →
    n ^ 2 ∣ ∑ k ∈ Finset.range n,
      (2 * k + 1) * ((n - 1).choose k) ^ 2 * ((n + k).choose k) ^ 2 := by
  sorry

end OMA.S_oeis_a246460
