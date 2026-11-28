import Mathlib

/-!
# A168597: Squares of the central trinomial coefficients (A002426)

Source: https://oeis.org/A168597

`a(n) = A002426(n)^2`, offset 0, where `A002426(n)` is the central trinomial coefficient: the
coefficient of `x^n` in `(1 + x + x^2)^n` (the largest coefficient of that polynomial).
Data: 1, 1, 9, 49, 361, 2601, 19881, 154449, ...

In the formula section (Peter Bala, Feb 08 2022) the entry gives a binomial sum, a recurrence, a
generating function and the Gauss congruences `a(n*p^k) == a(n*p^(k-1)) (mod p^k)` for all primes `p`,
all as facts; these are not part of the target. It then says:

  Conjecture: The stronger congruences `a(n*p^k) == a(n*p^(k-1)) (mod p^(2*k))` hold for all primes
  `p >= 5` and positive integers `n` and `k`.

This file states that conjecture (one claim).

Status: not open. A later formula line of the entry (Andrew R. Epstein, Jul 18 2026) says that the
conjecture follows from the theorem of Hao Pan and Zhi-Wei Sun (arXiv:2012.05121; Frontiers in
Combinatorics and Number Theory 2 (2026), 55-62) applied to A002426, because
`a(n*p^k) - a(n*p^(k-1))` is the product of `A002426(n*p^k) - A002426(n*p^(k-1))` and
`A002426(n*p^k) + A002426(n*p^(k-1))`.

Formalized: `T n` is the coefficient of `x^n` in the integer polynomial `(1 + x + x^2)^n`, and
`a n = T n ^ 2`, both integers. The congruence `x == y (mod N)` is written as `N ∣ x - y` in `ℤ`.
The variables `p`, `n`, `k` are natural numbers with `p` prime, `5 <= p`, `0 < n` and `0 < k`, so the
exponent `k - 1` is an ordinary subtraction.
-/

namespace OMA.S_oeis_a168597

/-- A002426, the central trinomial coefficient: the coefficient of `x^n` in `(1 + x + x^2)^n`. -/
noncomputable def T (n : ℕ) : ℤ :=
  ((1 + Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ) ^ n).coeff n

/-- A168597: `a(n) = A002426(n)^2`. -/
noncomputable def a (n : ℕ) : ℤ :=
  T n ^ 2

/-- Bala's conjectured supercongruence: `a(n*p^k) == a(n*p^(k-1)) (mod p^(2*k))` for every prime
`p >= 5` and all positive integers `n` and `k`. -/
theorem main :
    ∀ p n k : ℕ, p.Prime → 5 ≤ p → 0 < n → 0 < k →
      ((p : ℤ) ^ (2 * k)) ∣ (a (n * p ^ k) - a (n * p ^ (k - 1))) := by
  sorry

end OMA.S_oeis_a168597
