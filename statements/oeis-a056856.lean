import Mathlib

/-!
# OEIS A056856 and A130534

Sources: https://oeis.org/A056856 and https://oeis.org/A130534
Credit: @siddsg7

Mathar's identity uses one-based coordinates for A056856. The corresponding
A130534 entry is at row `n - 1`, column `k - 1` in its published zero-based
coordinates. For example, the third A056856 row is `2, 9, 9`, obtained from
A130534's row `2, 3, 1` by multiplying by `1, 3, 9` respectively.
-/

namespace OMA.S_oeis_a056856

open Polynomial

/-- The A056856 entry in one-based row `n` and one-based column `k`. -/
noncomputable def a056856 (n k : ℕ) : ℕ :=
  (∏ j ∈ Finset.Icc 1 (n - 1), (C j + C n * X : ℕ[X])).coeff (k - 1)

/-- The A130534 entry in zero-based row `r` and zero-based column `c`. -/
noncomputable def a130534 (r c : ℕ) : ℕ :=
  (∏ j ∈ Finset.Icc 1 r, (C j + X : ℕ[X])).coeff c

theorem main : ∀ n k : ℕ, 1 ≤ k → k ≤ n →
    a056856 n k = a130534 (n - 1) (k - 1) * n ^ (k - 1) := by
  sorry

end OMA.S_oeis_a056856
