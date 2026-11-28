import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Analysis.Real.Sqrt

namespace OMA.S_oeis_a363561

/-- Positive-index summand `x^n * (c + x^n)^(2n)` for `n ≥ 1`. -/
noncomputable def posTerm (c : ℝ) (n : ℕ) : PowerSeries ℝ :=
  PowerSeries.X ^ n * (PowerSeries.C c + PowerSeries.X ^ n) ^ (2 * n)

/-- Geometric series `(1 + c * x^j)^(-1) = ∑_{r ≥ 0} (-c)^r * x^(j*r)`. -/
noncomputable def invGeom (c : ℝ) (j : ℕ) : PowerSeries ℝ :=
  PowerSeries.mk fun k => if j ∣ k then (-c) ^ (k / j) else 0

/-- Negative-index summand `x^(-j) * (c + x^(-j))^(-2j) = x^(2j^2 - j) * (1 + c * x^j)^(-2j)` for `j ≥ 1`. -/
noncomputable def negTerm (c : ℝ) (j : ℕ) : PowerSeries ℝ :=
  PowerSeries.X ^ (2 * j ^ 2 - j) * (invGeom c j) ^ (2 * j)

/-- Generating function `A(x) = ∑_{n = -∞}^{+∞} x^n * ((sqrt(2)) + x^n)^(2n)` of OEIS A363561. -/
noncomputable def A : PowerSeries ℝ :=
  PowerSeries.mk fun N =>
    (if N = 0 then (1 : ℝ) else 0) +
      ∑ n ∈ Finset.Icc 1 N, (PowerSeries.coeff N (posTerm (Real.sqrt 2) n) + PowerSeries.coeff N (negTerm (Real.sqrt 2) n))

/-- Both conjectures on OEIS A363561:
1. `a(2^m) = (2 : ℝ) ^ (2 ^ m)` for all `m > 0`;
2. `a(p) = (p : ℝ) * (2 : ℝ) ^ ((p - 1) / 2) + (2 : ℝ) ^ p` for all primes `p > 3`. -/
theorem main :
    (∀ m : ℕ, 0 < m → PowerSeries.coeff (2 ^ m) A = (2 : ℝ) ^ (2 ^ m)) ∧
    (∀ p : ℕ, Nat.Prime p → 3 < p → PowerSeries.coeff p A = (p : ℝ) * (2 : ℝ) ^ ((p - 1) / 2) + (2 : ℝ) ^ p) := by
  sorry

end OMA.S_oeis_a363561
