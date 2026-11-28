import Mathlib

/-!
# Integrality of OEIS A300589

Source: https://oeis.org/A300589
Defining series: https://oeis.org/A300617
Credit: @HBreitkreutz
-/

namespace OMA.S_oeis_a300589

/-- For `p` with zero constant term, this finite sum gives the coefficient of
degree `j` in the formal exponential of `n * p`. -/
noncomputable def expCoeff (p : Polynomial ℚ) (n j : ℕ) : ℚ :=
  ∑ i ∈ Finset.range (j + 1), (n : ℚ) ^ i / (i.factorial : ℚ) * (p ^ i).coeff j

/-- The degree-`n` truncation of the series in A300617. Adding `c * X^k` to
`p` increases the degree-`k` coefficient of `exp(k * p)` by `k * c` and
preserves its lower coefficients. -/
noncomputable def truncation : ℕ → Polynomial ℚ
  | 0 => 0
  | n + 1 =>
    let k := n + 1
    let p := truncation n
    let c := ((k : ℚ) ^ 2 * expCoeff p k n - expCoeff p k k) / (k : ℚ)
    p + Polynomial.monomial k c

/-- Each coefficient of A300617 divided by its triangular number is an integer. -/
theorem main : ∀ n : ℕ, 0 < n → ∃ z : ℤ,
    (truncation n).coeff n / ((n : ℚ) * ((n : ℚ) + 1) / 2) = (z : ℚ) := by
  sorry

end OMA.S_oeis_a300589
