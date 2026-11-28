import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Interval
import Mathlib.RingTheory.PowerSeries.Basic

open scoped BigOperators

namespace OMA.S_oeis_a005310

/-- Formal power series `(1 + X^k) / (1 - X^k) = 1 + 2*X^k + 2*X^(2k) + ...` for `k ≥ 1`. -/
noncomputable def fermionicFactor (k : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk fun m => if m = 0 then 1 else if k ∣ m then 2 else 0

/-- OEIS A005309(n): Coefficient of `x^n` in `∏_{k ≥ 1} ((1 + x^k) / (1 - x^k))^(k - 1)`. -/
noncomputable def A005309 (n : ℕ) : ℤ :=
  PowerSeries.coeff n (∏ k ∈ Finset.Icc 1 n, (fermionicFactor k) ^ (k - 1))

/-- OEIS A005310(n): Fermionic string states, equal to `2 * ∑_{j=0}^n A005309(j)`
(ordinary generating function `(2 / (1 - x)) * ∏_{k ≥ 1} ((1 + x^k) / (1 - x^k))^(k - 1)`). -/
noncomputable def A005310 (n : ℕ) : ℤ :=
  2 * ∑ j ∈ Finset.range (n + 1), A005309 j

/-- Conjecture (Simon Plouffe, 1992; OEIS A005310, offset 0): The ordinary generating function
of `A005310(n)` equals `2 * (1 - 2*z + 2*z^2) / ((-1 + 2*z) * (z - 1))`, i.e.
`((-1 + 2*X) * (X - 1)) * (∑_{n ≥ 0} A005310(n) * X^n) = 2 * (1 - 2*X + 2*X^2)` in `ℤ⟦X⟧`. -/
theorem main :
    ((-1 + PowerSeries.C (2 : ℤ) * PowerSeries.X) * (PowerSeries.X - 1)) *
      PowerSeries.mk A005310 =
      PowerSeries.C (2 : ℤ) *
        (1 - PowerSeries.C (2 : ℤ) * PowerSeries.X + PowerSeries.C (2 : ℤ) * PowerSeries.X ^ 2) := by
  sorry

end OMA.S_oeis_a005310
