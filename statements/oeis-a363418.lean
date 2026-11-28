import Mathlib

/-!
# A363418: Square array read by ascending antidiagonals: T(n,k) = [x^(n*k)] ((1 + x)/(1 - x))^k for n, k >= 1.

Source: https://oeis.org/A363418
Credit: @azmiozgen

Conjecture (Peter Bala, from the entry): each row sequence satisfies the stronger
supercongruences T(n, m*p^r) == T(n, m*p^(r-1)) (mod p^(3*r)) for all primes p >= 5 and positive
integers m and r.

Formalization notes:
* (1 + x)/(1 - x) is the power series (1 + X) * Sum_{j>=0} X^j over ℤ (`mk 1` is 1/(1 - X)).
* The conjecture is stated for every row n ≥ 1.
* Controls (computed with the entry's formula T(n,k) = Sum_{j=0..k} C(k,j) C((n+1)k-j-1, nk-j)):
  rows n = 1, 2, 3 begin 2, 8, 38, 192, 1002 / 2, 16, 146, 1408, 14002 / 2, 24, 326, 4672, 69002,
  matching the antidiagonals 2; 2, 8; 2, 16, 38; 2, 24, 146, 192; the congruence holds for n = 1, 2, 3,
  p = 5, 7, m = 1, 2 with r = 1.
-/

namespace OMA.S_oeis_a363418

open PowerSeries

/-- `T(n, k) = [x^(nk)] ((1 + x)/(1 - x))^k`. -/
noncomputable def T (n k : ℕ) : ℤ := coeff (n * k) (((1 + X) * mk 1 : PowerSeries ℤ) ^ k)

/-- The conjecture of the entry. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n → ∀ p : ℕ, p.Prime → 5 ≤ p → ∀ m r : ℕ, 1 ≤ m → 1 ≤ r →
      ((p : ℤ) ^ (3 * r) ∣ T n (m * p ^ r) - T n (m * p ^ (r - 1))) := by
  sorry

end OMA.S_oeis_a363418
