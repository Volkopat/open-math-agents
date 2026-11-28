import Mathlib

/-!
# A364506: Square array read by ascending antidiagonals:
T(n,k) = (2*k)!/k! * ( (2*n*k)! * ((2*n+1)*k)! )/( (n*k)!^2 * ((n+1)*k)!^2 ).

Source: https://oeis.org/A364506

Offset 0 (both indices start at 0); the data is read by ascending antidiagonals
T(d,0), T(d-1,1), ..., T(0,d). Row 0 is binomial(2k,k), row 1 the de Bruijn numbers.

The entry (Peter Bala) states as known that rows 0 and 1 satisfy
u(m*p^r) == u(m*p^(r-1)) (mod p^(3r)) for all primes p >= 5 and all positive integers m, r,
and conjectures that every row of the table satisfies the same supercongruences.
This file states that conjecture (for every row n >= 0, rows 0 and 1 included).

Formalized: T(n,k) is the natural number obtained by dividing the product of the numerator
factorials (2k)! (2nk)! ((2n+1)k)! by the product of the denominator factorials
k! (nk)!^2 ((n+1)k)!^2. The ratio is an integer (the entry gives the integer formula
Sum_{i=-k..k} (-1)^i binomial(2k,k+i) binomial(2nk,nk+i)^2), so the natural-number division
is exact. The congruence is stated in the integers as divisibility of the difference by p^(3r).
The row index of the entry's u is called m here.
-/

namespace OMA.S_oeis_a364506

/-- A364506: `T(n,k) = (2k)! (2nk)! ((2n+1)k)! / (k! (nk)!^2 ((n+1)k)!^2)`. -/
def T (n k : ℕ) : ℕ :=
  (Nat.factorial (2 * k) * Nat.factorial (2 * n * k) * Nat.factorial ((2 * n + 1) * k)) /
    (Nat.factorial k * Nat.factorial (n * k) ^ 2 * Nat.factorial ((n + 1) * k) ^ 2)

/-- Bala's conjecture: every row `u(m) = T(n,m)` satisfies
`u(m p^r) == u(m p^(r-1)) (mod p^(3r))` for all primes `p >= 5` and all `m, r >= 1`. -/
theorem main : ∀ n p m r : ℕ, p.Prime → 5 ≤ p → 1 ≤ m → 1 ≤ r →
    ((p : ℤ) ^ (3 * r)) ∣ ((T n (m * p ^ r) : ℤ) - (T n (m * p ^ (r - 1)) : ℤ)) := by
  sorry

end OMA.S_oeis_a364506
