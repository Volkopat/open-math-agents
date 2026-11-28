import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Interval
import Mathlib.RingTheory.PowerSeries.Basic

open scoped BigOperators

namespace OMA.S_oeis_a005309

/-- Formal power series `(1 + X^k) / (1 - X^k) = 1 + 2*X^k + 2*X^(2k) + ...` for `k ≥ 1`. -/
noncomputable def fermionicFactor (k : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk fun m => if m = 0 then 1 else if k ∣ m then 2 else 0

/-- OEIS A005309(n): Fermionic string states, coefficient of `x^n` in
`∏_{k ≥ 1} ((1 + x^k) / (1 - x^k))^(k - 1)` (the finite product over `1 ≤ k ≤ n` gives
the exact `x^n` coefficient). -/
noncomputable def A005309 (n : ℕ) : ℤ :=
  PowerSeries.coeff n (∏ k ∈ Finset.Icc 1 n, (fermionicFactor k) ^ (k - 1))

/-- Conjecture (Simon Plouffe, 1992; OEIS A005309, offset 0): The ordinary generating function
of `A005309(n)` equals `-(1 - 2*z + 2*z^2) / (-1 + 2*z)`, i.e.
`(-1 + 2*X) * (∑_{n ≥ 0} A005309(n) * X^n) = -(1 - 2*X + 2*X^2)` in `ℤ⟦X⟧`. -/
theorem main :
    (-1 + PowerSeries.C (2 : ℤ) * PowerSeries.X) * PowerSeries.mk A005309 =
      -(1 - PowerSeries.C (2 : ℤ) * PowerSeries.X + PowerSeries.C (2 : ℤ) * PowerSeries.X ^ 2) := by
  sorry

end OMA.S_oeis_a005309
