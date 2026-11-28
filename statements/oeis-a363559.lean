import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Nat.Prime.Basic

namespace OMA.S_oeis_a363559

/-- Positive-index summand `x^n * (c + x^n)^(2n)` for `n ≥ 1`. -/
noncomputable def posTerm (c : ℤ) (n : ℕ) : PowerSeries ℤ :=
  PowerSeries.X ^ n * (PowerSeries.C c + PowerSeries.X ^ n) ^ (2 * n)

/-- Geometric series `(1 + c * x^j)^(-1) = ∑_{r ≥ 0} (-c)^r * x^(j*r)`. -/
noncomputable def invGeom (c : ℤ) (j : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk fun k => if j ∣ k then (-c) ^ (k / j) else 0

/-- Negative-index summand `x^(-j) * (c + x^(-j))^(-2j) = x^(2j^2 - j) * (1 + c * x^j)^(-2j)` for `j ≥ 1`. -/
noncomputable def negTerm (c : ℤ) (j : ℕ) : PowerSeries ℤ :=
  PowerSeries.X ^ (2 * j ^ 2 - j) * (invGeom c j) ^ (2 * j)

/-- Generating function `A(x) = ∑_{n = -∞}^{+∞} x^n * ((3) + x^n)^(2n)` of OEIS A363559. -/
noncomputable def A : PowerSeries ℤ :=
  PowerSeries.mk fun N =>
    (if N = 0 then (1 : ℤ) else 0) +
      ∑ n ∈ Finset.Icc 1 N, (PowerSeries.coeff N (posTerm (3 : ℤ) n) + PowerSeries.coeff N (negTerm (3 : ℤ) n))

/-- Both conjectures on OEIS A363559:
1. `a(2^m) = (9 : ℤ) ^ (2 ^ m)` for all `m > 0`;
2. `a(p) = (p : ℤ) * (3 : ℤ) ^ (p - 1) + (9 : ℤ) ^ p` for all primes `p > 3`. -/
theorem main :
    (∀ m : ℕ, 0 < m → PowerSeries.coeff (2 ^ m) A = (9 : ℤ) ^ (2 ^ m)) ∧
    (∀ p : ℕ, Nat.Prime p → 3 < p → PowerSeries.coeff p A = (p : ℤ) * (3 : ℤ) ^ (p - 1) + (9 : ℤ) ^ p) := by
  sorry

end OMA.S_oeis_a363559
