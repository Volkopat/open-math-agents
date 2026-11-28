import Mathlib

/-!
# A372611: Expansion of (1 + 3*x) / ((1 - 2*x)*sqrt(1 - 4*x))

Source: https://oeis.org/A372611

`a(n) = [x^n] (1 + 3*x) / ((1 - 2*x)*sqrt(1 - 4*x))`, offset 0; first terms
1, 7, 26, 90, 310, 1082, 3844, 13892, 50950, 189130.

The entry (Mélika Tebni, May 07 2024) makes two conjectures, stated together here in the order
of the entry:

1. for `p` a Pythagorean prime (A002144, the primes of the form `4*k + 1`),
   `a(p) - 7 == 0 (mod p)`;
2. for `p` a prime of the form `4*k + 3` (A002145), `a(p) + 3 == 0 (mod p)`.

Formalized: the series is taken in the integer power series.
* `1/(1 - 2*x)` is `Ring.inverse (1 - 2*x)`, the inverse of a series with constant coefficient 1
  (it is `Sum_{k>=0} 2^k x^k`).
* `1/sqrt(1 - 4*x)` is the series `Sum_{k>=0} binomial(2*k, k) x^k` (the generating function of
  the central binomial coefficients A000984): it is the power series `S` with constant
  coefficient 1 and `S^2 * (1 - 4*x) = 1`, which is the identity
  `Sum_{i+j=n} binomial(2*i, i) * binomial(2*j, j) = 4^n`.
* `a(n)` is an integer; with these definitions `a(n) = binomial(2*n, n) +
  5 * Sum_{k=0..n-1} 2^(n-k-1) * binomial(2*k, k)`, the formula given in the entry.
* A congruence `x == 0 (mod p)` between integers is written as `(p : ℤ) ∣ x`; the two classes of
  primes are `p % 4 = 1` and `p % 4 = 3`.
-/

namespace OMA.S_oeis_a372611

/-- The integer power series `1/sqrt(1 - 4x) = Sum_{k>=0} binomial(2k, k) x^k`. -/
noncomputable def invSqrt : PowerSeries ℤ :=
  PowerSeries.mk fun k => (k.centralBinom : ℤ)

/-- The integer power series `(1 + 3x)/((1 - 2x) sqrt(1 - 4x))`. -/
noncomputable def f : PowerSeries ℤ :=
  (1 + 3 * PowerSeries.X) * Ring.inverse (1 - 2 * PowerSeries.X) * invSqrt

/-- A372611: `a(n) = [x^n] (1 + 3x)/((1 - 2x) sqrt(1 - 4x))`. -/
noncomputable def a (n : ℕ) : ℤ :=
  PowerSeries.coeff n f

/-- The two conjectures of the entry: `a(p) == 7 (mod p)` for primes `p = 4k + 1` and
`a(p) == -3 (mod p)` for primes `p = 4k + 3`. -/
theorem main :
    (∀ p : ℕ, p.Prime → p % 4 = 1 → (p : ℤ) ∣ (a p - 7)) ∧
    (∀ p : ℕ, p.Prime → p % 4 = 3 → (p : ℤ) ∣ (a p + 3)) := by
  sorry

end OMA.S_oeis_a372611
