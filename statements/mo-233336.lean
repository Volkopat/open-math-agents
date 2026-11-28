import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Field.Rat

/-!
# Bounds for an Egyptian Fraction Inequality

Source: https://mathoverflow.net/questions/233336
Question author: Paul. Credit for formalization: @etaubman.

This is the assertion that a finite upper bound always exists, with the length,
rational endpoints, index, and all preceding denominators fixed. The prefix is
specified by `p`; its entries at and after `j` impose no conditions on `x`.
Denominators are positive integers, the usual Egyptian-fraction convention.
The answer is negative even with that additional positivity restriction.
-/

namespace OMA.S_mo_233336

open scoped BigOperators

theorem main :
    ∀ (n : ℕ) (A B : ℚ), 0 < B → B ≤ A →
      ∀ (j : Fin n) (p : Fin n → ℕ),
        ∃ bound : ℕ, ∀ x : Fin n → ℕ,
          (∀ i, 0 < x i) →
          Monotone x →
          (∀ i, i < j → x i = p i) →
          B ≤ ∑ i, (1 : ℚ) / (x i : ℚ) →
          (∑ i, (1 : ℚ) / (x i : ℚ)) ≤ A →
          x j ≤ bound := by
  sorry

end OMA.S_mo_233336
