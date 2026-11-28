import Mathlib

namespace OMA.S_oeis_a167894

open PowerSeries BigOperators

/-- Formal power series `E(x) = ∑_{k ≥ 0} k! * x^k`. -/
noncomputable def factorialSeries : PowerSeries ℚ :=
  PowerSeries.mk fun k => (Nat.factorial k : ℚ)

/-- OEIS A167894 generating function: `1 / (∑_{k ≥ 0} k! * x^k)`. -/
noncomputable def a167894Series : PowerSeries ℚ :=
  factorialSeries⁻¹

/-- Depth-`d` continued fraction convergent starting at index `k`:
`cfConv k 0 = 1`,
`cfConv k (d + 1) = 1 + k * x - (k + 1) * x / cfConv (k + 1) d`. -/
noncomputable def cfConv : ℕ → ℕ → PowerSeries ℚ
  | _, 0 => 1
  | k, d + 1 =>
      1 + PowerSeries.C (k : ℚ) * PowerSeries.X -
        PowerSeries.C ((k + 1 : ℕ) : ℚ) * PowerSeries.X * (cfConv (k + 1) d)⁻¹

/-- Conjecture on OEIS A167894:
1. There exists a sequence of formal power series `Q : ℕ → PowerSeries ℚ` with constant term `1`
   satisfying the continued fraction recurrence `Q k = 1 + k * x - (k + 1) * x / Q (k + 1)`
   for all `k : ℕ`, such that `Q 0 = 1 / (∑_{k ≥ 0} k! * x^k)`.
2. Moreover, the finite continued fraction convergents `cfConv 0 d` converge formally to
   `a167894Series`: for every `n ≤ d`, `coeff n (cfConv 0 d) = coeff n a167894Series`. -/
theorem main :
    (∃ Q : ℕ → PowerSeries ℚ,
      Q 0 = a167894Series ∧
      ∀ k : ℕ,
        PowerSeries.constantCoeff (Q k) = 1 ∧
        Q k = 1 + PowerSeries.C (k : ℚ) * PowerSeries.X -
          PowerSeries.C ((k + 1 : ℕ) : ℚ) * PowerSeries.X * (Q (k + 1))⁻¹) ∧
    (∀ d n : ℕ, n ≤ d → PowerSeries.coeff n (cfConv 0 d) = PowerSeries.coeff n a167894Series) := by
  sorry

end OMA.S_oeis_a167894
