import Mathlib

/-!
# A350406: a(n) = [x^n] 1/(1 + x + x^2 + x^3)^n

Source: https://oeis.org/A350406

`a(n)` is the coefficient of `x^n` in the power series `1/(1 + x + x^2 + x^3)^n`, offset 0:
1, -1, 1, -1, 5, -26, 91, -246, 597, -1540, 4576, ...

The entry (Peter Bala, Mar 17 2023) gives a binomial sum and a recurrence for `a(n)` as formulas and
then conjectures: the supercongruence `a(n*p^r) == a(n*p^(r-1)) (mod p^(2*r))` holds for positive
integers `n` and `r` and all primes `p >= 5`. This file states that conjecture; the two formulas
before it are presented by the entry as facts and are not part of the target.

Formalized: the reciprocal is taken in the integer power series, where `(1 + x + x^2 + x^3)^n` is
invertible (its constant coefficient is 1), so `Ring.inverse` is the true inverse; `a(n)` is an
integer. A congruence `x == y (mod N)` between integers is written as `N ∣ x - y`. Positive `n` and
`r` are `0 < n` and `0 < r`, so the exponent `r - 1` is an honest natural-number subtraction.
-/

namespace OMA.S_oeis_a350406

/-- A350406: `a(n) = [x^n] 1/(1 + x + x^2 + x^3)^n`. -/
noncomputable def a (n : ℕ) : ℤ :=
  PowerSeries.coeff n
    (Ring.inverse ((1 + PowerSeries.X + PowerSeries.X ^ 2 + PowerSeries.X ^ 3 : PowerSeries ℤ) ^ n))

/-- Bala's conjectured supercongruence: `a(n*p^r) == a(n*p^(r-1)) (mod p^(2*r))` for positive
integers `n`, `r` and every prime `p >= 5`. -/
theorem main : ∀ p n r : ℕ, p.Prime → 5 ≤ p → 0 < n → 0 < r →
    ((p : ℤ) ^ (2 * r)) ∣ (a (n * p ^ r) - a (n * p ^ (r - 1))) := by
  sorry

end OMA.S_oeis_a350406
