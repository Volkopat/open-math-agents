import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Odd coefficients of A303563

Paul D. Hanna's generating series A starts with 1+X. Its reciprocal R
therefore starts with 1-X. Substituting m=n-1 in the defining diagonal
condition gives [Xᵐ]R^(m²+m+1)=0 for m>1. At each such m, the new
coefficient of R occurs with multiplier m²+m+1. This gives the integer
recursion below and then A=1/R.

Source: https://oeis.org/A303563 (OEIS Foundation, CC BY-SA 4.0).
Credit: @Solitude1312
-/

namespace OMA.S_oeis_a303563

open PowerSeries

noncomputable def recipCoeff (n : ℕ) : ℤ :=
  if n < 2 then (-1) ^ n else
    let earlier : PowerSeries ℤ := PowerSeries.mk fun k =>
      if _h : k < n then recipCoeff k else 0
    Int.ediv (-((earlier ^ (n ^ 2 + n + 1)).coeff n)) ((n : ℤ) ^ 2 + n + 1)
termination_by n

noncomputable def series : PowerSeries ℤ := (PowerSeries.mk recipCoeff).invOfUnit 1

theorem main : ∀ n : ℕ, Odd (series.coeff n) ↔ ∃ k : ℕ, n = 2 ^ k - 1 := by
  sorry

end OMA.S_oeis_a303563
