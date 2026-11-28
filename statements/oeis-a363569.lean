import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Complex.Basic

namespace OMA.S_oeis_a363569

/-- Positive-index summand `x^n * (c + x^n)^(2n)` for `n ≥ 1`. -/
noncomputable def posTerm (c : ℂ) (n : ℕ) : PowerSeries ℂ :=
  PowerSeries.X ^ n * (PowerSeries.C c + PowerSeries.X ^ n) ^ (2 * n)

/-- Geometric series `(1 + c * x^j)^(-1) = ∑_{r ≥ 0} (-c)^r * x^(j*r)`. -/
noncomputable def invGeom (c : ℂ) (j : ℕ) : PowerSeries ℂ :=
  PowerSeries.mk fun k => if j ∣ k then (-c) ^ (k / j) else 0

/-- Negative-index summand `x^(-j) * (c + x^(-j))^(-2j) = x^(2j^2 - j) * (1 + c * x^j)^(-2j)` for `j ≥ 1`. -/
noncomputable def negTerm (c : ℂ) (j : ℕ) : PowerSeries ℂ :=
  PowerSeries.X ^ (2 * j ^ 2 - j) * (invGeom c j) ^ (2 * j)

/-- Generating function `A(x) = ∑_{n = -∞}^{+∞} x^n * ((i) + x^n)^(2n)` of OEIS A363569. -/
noncomputable def A : PowerSeries ℂ :=
  PowerSeries.mk fun N =>
    (if N = 0 then (1 : ℂ) else 0) +
      ∑ n ∈ Finset.Icc 1 N, (PowerSeries.coeff N (posTerm Complex.I n) + PowerSeries.coeff N (negTerm Complex.I n))

/-- Both conjectures on OEIS A363569:
1. `a(2^m) = (1 : ℂ)` for all `m > 0`;
2. `a(p) = (p : ℂ) * (-1 : ℂ) ^ ((p - 1) / 2) - 1` for all primes `p > 3`. -/
theorem main :
    (∀ m : ℕ, 0 < m → PowerSeries.coeff (2 ^ m) A = (1 : ℂ)) ∧
    (∀ p : ℕ, Nat.Prime p → 3 < p → PowerSeries.coeff p A = (p : ℂ) * (-1 : ℂ) ^ ((p - 1) / 2) - 1) := by
  sorry

end OMA.S_oeis_a363569
