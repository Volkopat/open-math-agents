import Mathlib

/-!
# A270922: coefficient of x^n in Product_{k>=1} (1+x^k)^(k*n)

Source: https://oeis.org/A270922

`a(n) = [x^n] Product_{k>=1} (1 + x^k)^(k*n)`, offset 0. A factor `(1 + x^k)^(k*n)` with `k > n` is `1`
up to terms of degree above `n`, so the coefficient of `x^n` is that of the finite product over
`1 <= k <= n`, taken in the integer power series.

The entry (Peter Bala, Apr 18 2023) states the Gauss congruences `a(n*p^k) == a(n*p^(k-1)) (mod p^k)`
as a fact, and conjectures the supercongruences `a(n*p^k) == a(n*p^(k-1)) (mod p^(2*k))` for all primes
`p >= 3` and all positive integers `n` and `k`. This file states that conjecture.
Formalized: `a n : ℤ`; the congruence is divisibility of the difference in `ℤ`; `n >= 1`, `k >= 1`.
-/

namespace OMA.S_oeis_a270922

/-- A270922: `a(n) = [x^n] Product_{k=1..n} (1 + x^k)^(k*n)`. -/
noncomputable def a (n : ℕ) : ℤ :=
  PowerSeries.coeff n (∏ k ∈ Finset.Icc 1 n, (1 + PowerSeries.X ^ k : PowerSeries ℤ) ^ (k * n))

/-- Bala's conjectured supercongruences: `a(n*p^k) == a(n*p^(k-1)) (mod p^(2k))` for primes `p >= 3`. -/
theorem main : ∀ p : ℕ, p.Prime → 3 ≤ p → ∀ n k : ℕ, 1 ≤ n → 1 ≤ k →
    ((p : ℤ) ^ (2 * k)) ∣ (a (n * p ^ k) - a (n * p ^ (k - 1))) := by
  sorry

end OMA.S_oeis_a270922
