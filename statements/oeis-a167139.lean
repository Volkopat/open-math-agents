import Mathlib

namespace OMA.S_oeis_a167139

open PowerSeries BigOperators

/-- The formal power series `log(1 + x) = ∑_{k ≥ 1} (-1)^(k-1) * x^k / k` over `ℚ`. -/
noncomputable def logOneAddX : PowerSeries ℚ :=
  PowerSeries.mk fun k => if k = 0 then 0 else ((-1 : ℚ) ^ (k - 1)) / (k : ℚ)

/-- The `k`-th coefficient of `∑_{n ≥ 0} L(n) * log(1 + x)^n / n!` over `ℚ`
(terms with `n > k` contribute `0` since `log(1 + x)` has zero constant term). -/
noncomputable def logSeriesCoeff (L : ℕ → ℚ) (k : ℕ) : ℚ :=
  ∑ n ∈ Finset.range (k + 1),
    L n / ((Nat.factorial n : ℕ) : ℚ) * PowerSeries.coeff k (logOneAddX ^ n)

/-- OEIS A167139 conjecture:
"Conjecture: For all integers m > 0, Sum_{n>=0} L(n)^m * log(1+x)^n/n! is an integer series
whenever Sum_{n>=0} L(n)*log(1+x)^n/n! is an integer series." -/
theorem main :
    ∀ (L : ℕ → ℚ) (m : ℕ), 1 ≤ m →
      (∀ k : ℕ, ∃ z : ℤ, logSeriesCoeff L k = (z : ℚ)) →
      ∀ k : ℕ, ∃ z : ℤ, logSeriesCoeff (fun n => (L n) ^ m) k = (z : ℚ) := by sorry

end OMA.S_oeis_a167139
