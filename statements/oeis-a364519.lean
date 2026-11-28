import Mathlib

/-!
# A364519: Square array T(n,k) = [x^(3k)] ((1+x)^(n+3)/(1-x)^(n-3))^k

Source: https://oeis.org/A364519

Definition: T(n,k) = [x^(3*k)] ( (1 + x)^(n+3)/(1 - x)^(n-3) )^k for n, k >= 0,
read by ascending antidiagonals (offset 0).

Claim (Peter Bala, comment of the entry): each row sequence k -> T(n,k) satisfies
the supercongruences u(m*p^r) == u(m*p^(r-1)) (mod p^(3*r)) for all primes p >= 5
and all positive integers m and r. (For row 1, the unsigned A005810, this is stated
in the entry as known; the conjecture is the claim for every row.)

Formalized: the series (1+x)^(n+3)/(1-x)^(n-3) is written in ℤ⟦X⟧ as
(1+X)^(n+3) * (1-X)^3 * (1/(1-X))^n, with 1/(1-X) = PowerSeries.invUnitsSub 1,
so negative exponents never occur. T(n,k) is the coefficient of X^(3k) of its k-th
power, an integer. The congruence is divisibility in ℤ of the difference by p^(3r),
for every row n : ℕ, every prime p >= 5, every m >= 1 and r >= 1.
-/

namespace OMA.S_oeis_a364519

/-- The series (1+x)^(n+3)/(1-x)^(n-3) in ℤ⟦X⟧. -/
noncomputable def series (n : ℕ) : PowerSeries ℤ :=
  (1 + PowerSeries.X) ^ (n + 3) * (1 - PowerSeries.X) ^ 3 *
    (PowerSeries.invUnitsSub (1 : ℤˣ)) ^ n

/-- T(n,k) = [x^(3k)] (series n)^k. -/
noncomputable def T (n k : ℕ) : ℤ :=
  PowerSeries.coeff (3 * k) (series n ^ k)

theorem main :
    ∀ n : ℕ, ∀ p : ℕ, p.Prime → 5 ≤ p → ∀ m r : ℕ, 1 ≤ m → 1 ≤ r →
      ((p : ℤ) ^ (3 * r)) ∣ (T n (m * p ^ r) - T n (m * p ^ (r - 1))) := by
  sorry

end OMA.S_oeis_a364519
