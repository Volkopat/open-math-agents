import Mathlib

/-!
# A372211: a(n) = [x^n] f(x)^n, where f(x) = (1 - x^5)^5/((1 - x^2)^2 * (1 - x^3)^3).

Source: https://oeis.org/A372211
Credit: @azmiozgen

Conjecture (Peter Bala, from the entry): the stronger supercongruences
a(n*p^r) == a(n*p^(r-1)) (mod p^(3*r)) hold for all primes p >= 5 and positive integers n and r.

Formalization notes:
* f is a power series over ℚ (the denominator has constant term 1, so its inverse exists);
  a(n) is the coefficient of x^n in f^n (offset 0). The values are integers.
* "x == y (mod p^(3r))" for these values is stated as: x - y = p^(3r) * z for an integer z.
* Controls (computed with exact rational power series): a(0..9) = 1, 0, 4, 9, 36, 125, 535, 1715, 7716, 26739, as in the
  entry; the congruence holds for the two smallest admissible primes, n = 1, 2, r = 1 (n*p ≤ 40).
-/

namespace OMA.S_oeis_a372211

open PowerSeries

/-- `f(x) = (1 - x^5)^5 / ((1 - x^2)^2 (1 - x^3)^3)`. -/
noncomputable def f : PowerSeries ℚ :=
  (1 - X ^ 5) ^ 5 * ((1 - X ^ 2) ^ 2 * (1 - X ^ 3) ^ 3)⁻¹

/-- A372211(n) = [x^n] f(x)^n. -/
noncomputable def a (n : ℕ) : ℚ := coeff n (f ^ n)

/-- The conjecture of the entry. -/
theorem main :
    ∀ p : ℕ, p.Prime → 5 ≤ p → ∀ n r : ℕ, 1 ≤ n → 1 ≤ r →
      ∃ z : ℤ, a (n * p ^ r) - a (n * p ^ (r - 1)) = (p : ℚ) ^ (3 * r) * z := by
  sorry

end OMA.S_oeis_a372211
