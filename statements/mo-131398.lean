import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Order.Interval.Finset.Nat

/-! Source: https://mathoverflow.net/questions/131398 -/

open scoped BigOperators
open Polynomial

namespace OMA.S_mo_131398

/-- Shifting each partial degree by one turns the degree condition into
a coefficient at degree k * d, including the case of negative original degree. -/
noncomputable def boundedMonomialCount (d n k : ℕ) : ℕ :=
  ((∑ j ∈ Finset.Icc 1 (d - 1), (X : ℕ[X]) ^ j) ^ (n + 1)).coeff (k * d)

/-- The proposed monomial-count recurrence for positive k ≤ n. -/
theorem main : ∀ d n k : ℕ, 2 ≤ d → 1 ≤ k → k ≤ n →
    boundedMonomialCount d n k =
      (d - 1).choose n +
        ∑ j ∈ Finset.Icc 1 (n - k),
          ∑ m ∈ Finset.Icc j (j + k - 2),
            boundedMonomialCount d m j * d.choose (n - m) := by
  sorry

end OMA.S_mo_131398
