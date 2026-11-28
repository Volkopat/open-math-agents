import Mathlib

namespace OMA.S_oeis_a066108

open PowerSeries BigOperators

/-- OEIS A066108: for `n ≥ 1`, `a(n) = ∑_{d ∣ n} n^d` (and `a(0) = 0`). -/
def a066108 (n : ℕ) : ℕ :=
  if n = 0 then 0 else ∑ d ∈ Nat.divisors n, n ^ d

/-- Eulerian numbers `A(m, k)` (OEIS A008292) as given by the explicit alternating sum
`∑_{j=0}^k (-1)^j * (k - j)^m * C(m + 1, j)`. -/
def eulerian (m k : ℕ) : ℚ :=
  ∑ j ∈ Finset.range (k + 1),
    (-1 : ℚ) ^ j * ((k - j : ℕ) : ℚ) ^ m * (Nat.choose (m + 1) j : ℚ)

/-- The `m`-th summand of the conjectured generating function for A066108:
`m^m * (∑_{k=1}^m A(m, k) * X^(k * m)) / (1 - X^m)^(m + 1)`. -/
noncomputable def a066108Term (m : ℕ) : PowerSeries ℚ :=
  PowerSeries.C ((m : ℚ) ^ m) *
    (∑ k ∈ Finset.Icc 1 m, PowerSeries.C (eulerian m k) * PowerSeries.X ^ (k * m)) *
    ((1 - PowerSeries.X ^ m) ^ (m + 1))⁻¹

/-- Conjecture on OEIS A066108:
the ordinary generating function of `a(n) = ∑_{d ∣ n} n^d` is
`∑_{m ≥ 1} m^m * (∑_{k=1}^m A(m, k) * x^(k * m)) / (1 - x^m)^(m + 1)`.
Equivalently, for every `n : ℕ` and every truncation bound `M ≥ n`,
the `x^n` coefficient of `∑_{m=1}^M a066108Term m` equals `a066108 n`. -/
theorem main :
    ∀ n M : ℕ, n ≤ M →
      PowerSeries.coeff n (∑ m ∈ Finset.Icc 1 M, a066108Term m) = (a066108 n : ℚ) := by
  sorry

end OMA.S_oeis_a066108
