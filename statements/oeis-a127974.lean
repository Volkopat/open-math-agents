import Mathlib

/-!
# A127974: Numerators in expansion of (1-x)^(-2/3).

Source: https://oeis.org/A127974
Credit: @bmendonca3

[Lean proof of this statement](https://github.com/bmendonca3/open-math-agents/blob/f5b84522329d2f50466241787254d5bf4b0fafe1/proofs/oeis-a127974.lean)

Entry A127974 (Paul Barry, Feb 09 2007), offset 0, data 1, 2, 5, 40, 110, 308, 2618, 7480, ...
Formula section:
Conjecture: a(n-1) = the numerator of (1/(2*sqrt(3)*Pi)) * Integral_{x >= 0} 1/(1 + x^3)^n.
- Peter Bala, Jun 11 2024

Formalization notes:
* The expansion of (1-x)^(-2/3) is a formal power series over the rationals. It is taken from
  Mathlib: `PowerSeries.binomialSeries ℚ r` is the series of (1 + X)^r, with coefficients the
  generalized binomial coefficients `Ring.choose r m`, and `PowerSeries.rescale (-1)` substitutes
  -X for X. So the coefficient of x^m is (-1)^m * binomial(-2/3, m)
  = (2/3)(5/3)...(2/3 + m - 1) / m!.
* `a m` is the numerator of that coefficient in lowest terms (`Rat.num`, with a positive
  denominator). The coefficients are positive, so this is the positive integer of the entry.
* The source speaks of the numerator of a real number. This says that the real number is rational
  and gives the numerator of that rational in lowest terms. `main` states exactly this: there is a
  rational q equal to the real number, with numerator a(n-1). Such a q is unique.
* Range: n >= 1. The sequence has offset 0, so a(n-1) needs n >= 1, and the integral converges for
  n >= 1.
* Integral_{x >= 0} is the Lebesgue integral over `Set.Ioi 0`, Mathlib's usual form of an integral
  from 0 to infinity. The single point 0 does not change the value.
-/

namespace OMA.S_oeis_a127974

/-- The formal power series `(1 - x)^(-2/3)` over the rationals: the binomial series
`(1 + X)^(-2/3)` with `-X` in place of `X`. -/
noncomputable def series : PowerSeries ℚ :=
  PowerSeries.rescale (-1 : ℚ) (PowerSeries.binomialSeries ℚ (-2 / 3 : ℚ))

/-- A127974: `a(m)` is the numerator of the coefficient of `x^m` in `(1 - x)^(-2/3)`. -/
noncomputable def a (m : ℕ) : ℤ :=
  (PowerSeries.coeff m series).num

/-- Bala's conjecture: for `n ≥ 1` the number `(1/(2*sqrt(3)*Pi)) * Integral_{x >= 0} 1/(1 + x^3)^n`
is rational and its numerator is `a(n-1)`. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n → ∃ q : ℚ,
      (q : ℝ) = (1 / (2 * Real.sqrt 3 * Real.pi)) * ∫ x in Set.Ioi (0 : ℝ), 1 / (1 + x ^ 3) ^ n ∧
      q.num = a (n - 1) := by
  sorry

end OMA.S_oeis_a127974
