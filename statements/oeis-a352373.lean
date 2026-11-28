import Mathlib

/-!
# A352373: a(n) = [x^n] ( 1/((1 - x)^2*(1 - x^2)) )^n for n >= 1.

Source: https://oeis.org/A352373
Credit: @azmiozgen

Conjecture (from the entry): the supercongruences a(n*p^k) == a(n*p^(k-1)) (mod p^(3*k)) hold
for all primes p >= 5 and positive integers n and k.

Formalization notes:
* 1/((1 - x)^2*(1 - x^2)) = Sum_{k>=0} floor((k+2)^2/4) x^k (A002620(k+2)): the power series
  `f` below has these coefficients, and a(n) is the coefficient of x^n in f^n (offset 1).
* The congruence is stated in ℤ as divisibility of the difference by p^(3k).
* Controls (computed): a(1..7) = 2, 12, 74, 484, 3252, 22260, 154352, as in the entry; the
  congruence holds for p = 5, 7, 11, n = 1, 2, k = 1.
-/

namespace OMA.S_oeis_a352373

/-- The power series `1/((1-x)^2 (1-x^2)) = ∑ ⌊(k+2)^2/4⌋ x^k`. -/
def f : PowerSeries ℤ := PowerSeries.mk fun k => (((k + 2) ^ 2 / 4 : ℕ) : ℤ)

/-- A352373(n) = [x^n] f(x)^n. -/
noncomputable def a (n : ℕ) : ℤ := PowerSeries.coeff n (f ^ n)

/-- The supercongruences `a(n p^k) ≡ a(n p^(k-1)) (mod p^(3k))` for primes `p ≥ 5`. -/
theorem main :
    ∀ p : ℕ, p.Prime → 5 ≤ p → ∀ n k : ℕ, 1 ≤ n → 1 ≤ k →
      ((p : ℤ) ^ (3 * k) ∣ a (n * p ^ k) - a (n * p ^ (k - 1))) := by
  sorry

end OMA.S_oeis_a352373
