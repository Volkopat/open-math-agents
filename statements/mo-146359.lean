import Mathlib

/-!
# Signed product for unrestricted partitions

Source: David S. Newman, https://mathoverflow.net/questions/146359/a-product-related-to-unrestricted-partitions
Credit: @wtho704

The factor for part size `k` has constant term `1`. For each positive `m`,
the coefficient of `x ^ (k * m)` can be chosen independently in `{−1, 1}`.
A partition contributes the product of the chosen signs for its nonzero
multiplicities, one sign from each part size that occurs.
-/

open Finset
open scoped BigOperators

namespace OMA.S_mo_146359

/-- The coefficient of degree `n` in the product with the chosen signs. -/
noncomputable def signedCoefficient (signs : ℕ → ℕ → Bool) (n : ℕ) : ℤ :=
  ∑ p : Nat.Partition n, ∏ k ∈ p.parts.toFinset,
    if signs k (p.parts.count k) then (1 : ℤ) else -1

/-- Can the entire product have all coefficients in `{-1, 0, 1}`? -/
theorem main : ∃ signs : ℕ → ℕ → Bool, ∀ n : ℕ,
    signedCoefficient signs n ∈ ({-1, 0, 1} : Finset ℤ) := by
  sorry

end OMA.S_mo_146359
