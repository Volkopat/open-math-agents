import Mathlib

/-!
# A333715: a(n) = [x^(3*n)] ( (1 + x)/(1 - x) )^n.

Source: https://oeis.org/A333715
Credit: @azmiozgen

Conjecture (Peter Bala, from the entry): a(n) satisfies the stronger supercongruences
a(n*p^k) == a(n*p^(k-1)) (mod p^(3*k)) for prime p >= 5 and positive integers n and k.

Formalization notes:
* (1 + x)/(1 - x) is the power series (1 + X) * Sum_{j>=0} X^j over ℤ (`PowerSeries.mk 1` is
  1/(1 - X)); a(n) is the coefficient of X^(3n) in its n-th power (offset 0).
* The congruence is stated in ℤ as divisibility of the difference by p^(3k).
* Controls (computed with the entry's formula a(n) = Sum_{k=0..n} C(n,k) C(3n+k-1,n-1)):
  a(0..7) = 1, 2, 24, 326, 4672, 69002, 1038984, 15856206, as in the entry; the congruence holds
  for p = 5, 7 and n = 1, 2 with k = 1.
-/

namespace OMA.S_oeis_a333715

/-- A333715(n) = [x^(3n)] ((1 + x)/(1 - x))^n. -/
noncomputable def a (n : ℕ) : ℤ :=
  PowerSeries.coeff (3 * n) (((1 + PowerSeries.X) * PowerSeries.mk 1 : PowerSeries ℤ) ^ n)

/-- The supercongruences `a(n p^k) ≡ a(n p^(k-1)) (mod p^(3k))` for primes `p ≥ 5`. -/
theorem main :
    ∀ p : ℕ, p.Prime → 5 ≤ p → ∀ n k : ℕ, 1 ≤ n → 1 ≤ k →
      ((p : ℤ) ^ (3 * k) ∣ a (n * p ^ k) - a (n * p ^ (k - 1))) := by
  sorry

end OMA.S_oeis_a333715
