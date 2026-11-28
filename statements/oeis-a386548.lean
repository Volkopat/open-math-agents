import Mathlib

/-!
# A386548: a(n) = [x^n] ((1 - x)/(1 - x + x^2))^n

Source: https://oeis.org/A386548

`a(n) = [x^n] ((1 - x)/(1 - x + x^2))^n`, offset 0; the first terms are
`1, 0, -2, -3, 6, 25, 1, -147, -218, 591, 2223, -484, ...`.

The entry (Peter Bala, Jul 25 2025) first states as a fact that the Gauss congruences
`a(n*p^k) == a(n*p^(k-1)) (mod p^k)` hold for all primes `p` and all positive integers `n` and `k`;
that sentence is not part of the target. It then conjectures:

  the stronger supercongruences `a(n*p^k) == a(n*p^(k-1)) (mod p^(2*k))` hold for all primes
  `p >= 5` and all positive integers `n` and `k`.

This file states that conjecture (one claim).

Formalized: the quotient is taken in the integer power series, where `1 - x + x^2` is invertible
(its constant coefficient is 1), so `Ring.inverse` is the true inverse; `a(n)` is an integer (the
sequence has negative terms). A congruence `x == y (mod N)` between integers is written as
`N ∣ x - y`. The range is all primes `p` with `5 ≤ p` and all `n`, `k` with `0 < n`, `0 < k`;
because `0 < k`, the natural-number subtraction `k - 1` is the true `k - 1`.
-/

namespace OMA.S_oeis_a386548

/-- The integer power series `(1 - x)/(1 - x + x^2)`. -/
noncomputable def f : PowerSeries ℤ :=
  (1 - PowerSeries.X) * Ring.inverse (1 - PowerSeries.X + PowerSeries.X ^ 2)

/-- A386548: `a(n) = [x^n] f(x)^n`. -/
noncomputable def a (n : ℕ) : ℤ :=
  PowerSeries.coeff n (f ^ n)

/-- Bala's conjectured supercongruences: `a(n*p^k) == a(n*p^(k-1)) (mod p^(2*k))` for all primes
`p >= 5` and all positive integers `n` and `k`. -/
theorem main :
    ∀ p n k : ℕ, p.Prime → 5 ≤ p → 0 < n → 0 < k →
      ((p : ℤ) ^ (2 * k)) ∣ (a (n * p ^ k) - a (n * p ^ (k - 1))) := by
  sorry

end OMA.S_oeis_a386548
