import Mathlib

namespace OMA.S_oeis_a181070

open PowerSeries BigOperators

/-- The truncated logarithm series `∑_{n=1}^{N} (∑_{k=0}^{n} C(n,k)^(k+1) * x^k) * x^n / n`
for OEIS A181070. -/
noncomputable def logSeriesTrunc (N : ℕ) : PowerSeries ℚ :=
  ∑ n ∈ Finset.Icc 1 N,
    PowerSeries.C ((1 : ℚ) / (n : ℚ)) *
      ((∑ k ∈ Finset.range (n + 1),
          PowerSeries.C (((Nat.choose n k : ℕ) : ℚ) ^ (k + 1)) * PowerSeries.X ^ k) *
        PowerSeries.X ^ n)

/-- The `n`-th coefficient `a(n)` of
`A(x) = exp(∑_{n ≥ 1} (∑_{k=0}^{n} C(n,k)^(k+1) * x^k) * x^n / n)` (OEIS A181070). -/
noncomputable def a181070 : ℕ → ℚ
  | 0 => 1
  | n + 1 =>
      (1 / ((n + 1 : ℕ) : ℚ)) *
        ∑ j : Fin (n + 1),
          ((j.val + 1 : ℕ) : ℚ) *
            PowerSeries.coeff (j.val + 1) (logSeriesTrunc (n + 1)) *
            a181070 (n - j.val)

/-- OEIS A181070 conjecture:
"Expansion of G.f.: A(x) = exp( Sum_{n>=1} (Sum_{k=0..n} C(n,k)^(k+1)*x^k)*x^n/n ).
Conjecture: this sequence consists entirely of integers." -/
theorem main : ∀ n : ℕ, ∃ z : ℤ, a181070 n = (z : ℚ) := by sorry

end OMA.S_oeis_a181070
