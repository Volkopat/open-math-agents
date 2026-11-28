import Mathlib

/-!
# A255672: coefficient of x^n in Product_{k>=1} 1/(1-x^k)^(k*n)

Source: https://oeis.org/A255672

`a(n) = [x^n] Product_{k>=1} 1/(1 - x^k)^(k*n)`, offset 0. A factor with `k > n` is `1` up to terms of
degree above `n`, so the coefficient of `x^n` is that of the finite product over `1 <= k <= n`.

The entry (Peter Bala, Apr 18 2023) states the Gauss congruences `a(n p^k) == a(n p^(k-1)) (mod p^k)`
as a fact, and conjectures the supercongruences `a(n p^k) == a(n p^(k-1)) (mod p^(2k))` for all primes
`p >= 3` and all positive integers `n` and `k`. This file states that conjecture.

Formalized: `a(n)` is an integer, the coefficient in `PowerSeries ℤ`; the inverse `1/(1 - x^k)` is written
as the geometric series `Sum_{j>=0} x^(k j)`, i.e. the power series whose `i`-th coefficient is `1` if
`k ∣ i` and `0` otherwise. The congruence is divisibility of the difference in `ℤ`; `k >= 1`, so
`p^(k-1)` involves no truncated subtraction issue.
-/

namespace OMA.S_oeis_a255672

/-- The power series `1/(1 - x^k) = Sum_{j>=0} x^(k j)`. -/
noncomputable def geom (k : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk fun i => if k ∣ i then 1 else 0

/-- A255672: `a(n) = [x^n] Product_{k=1..n} (1/(1 - x^k))^(k n)`. -/
noncomputable def a (n : ℕ) : ℤ :=
  PowerSeries.coeff n (∏ k ∈ Finset.Icc 1 n, geom k ^ (k * n))

/-- Bala's conjectured supercongruences: for primes `p >= 3` and `n, k >= 1`,
`a(n p^k) == a(n p^(k-1)) (mod p^(2k))`. -/
theorem main : ∀ p : ℕ, p.Prime → 3 ≤ p → ∀ n k : ℕ, 1 ≤ n → 1 ≤ k →
    ((p : ℤ) ^ (2 * k)) ∣ (a (n * p ^ k) - a (n * p ^ (k - 1))) := by
  sorry

end OMA.S_oeis_a255672
