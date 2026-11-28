import Mathlib

/-!
# OEIS A008485: a supercongruence for the coefficient of x^n in Product 1/(1-x^k)^n

Source: https://oeis.org/A008485
Credit: @sntntHb

A008485: `a(n)` is the coefficient of `x^n` in `Product_{k>=1} 1/(1-x^k)^n`.

Conjecture (Peter Bala, Apr 18 2023): the supercongruence `a(p) == p + 1 (mod p^2)` holds for
all primes `p >= 3`.

Formalized: factors with `k > n` do not affect the coefficient of `x^n`, so `a n` is the
coefficient of `X^n` in `((Product_{k=1..n} (1 - X^k))^(-1))^n` in `ℚ[[X]]` (an integer). The
congruence is expressed as `a p - (p + 1) = p^2 * m` for an integer `m`, for every prime `p >= 3`.
-/

namespace OMA.S_oeis_a008485

open PowerSeries

/-- `a(n) = [x^n] Product_{k>=1} 1/(1-x^k)^n` (only `k <= n` matter). -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff n (((∏ k ∈ Finset.Icc 1 n, (1 - X ^ k : PowerSeries ℚ))⁻¹) ^ n)

theorem main :
    ∀ p : ℕ, p.Prime → 3 ≤ p → ∃ m : ℤ, a p - ((p : ℚ) + 1) = (p : ℚ) ^ 2 * m := by
  sorry

end OMA.S_oeis_a008485
