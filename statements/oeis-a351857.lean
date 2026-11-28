import Mathlib

/-!
# A351857: Number of nonnegative integer solutions to n = x_1 + ... + x_(2*n) + 2*y_1 + ... + 2*y_(2*n)

Source: https://oeis.org/A351857

Offset 1. The entry gives a(n) = [x^n] ( 1/((1 - x)*(1 - x^2)) )^(2*n) (formula line, equivalent to
the counting definition: the generating function of the solutions is that power).
The Gauss congruences a(n*p^k) == a(n*p^(k-1)) (mod p^k) are stated in the entry as a known fact and
are not part of the target.

Conjecture (Peter Bala, 2022): the supercongruences a(n*p^k) == a(n*p^(k-1)) (mod p^(3*k)) hold for
all primes p >= 5 and positive integers n and k.

Formalized: a(n) is the integer coefficient of x^n in g^(2n), where g is the inverse in the integer
power series of (1 - x)*(1 - x^2) (constant coefficient 1, so invertible). The congruence
x == y (mod N) is written as N ∣ x - y in ℤ. Both n and k range over positive integers, so
n*p^(k-1) >= 1 stays inside the offset.
-/

namespace OMA.S_oeis_a351857

/-- The integer power series `1/((1 - x)*(1 - x^2))`. -/
noncomputable def g : PowerSeries ℤ :=
  Ring.inverse ((1 - PowerSeries.X) * (1 - PowerSeries.X ^ 2))

/-- A351857: `a(n) = [x^n] g(x)^(2n)`. -/
noncomputable def a (n : ℕ) : ℤ :=
  PowerSeries.coeff n (g ^ (2 * n))

/-- The conjectured supercongruences. -/
theorem main :
    ∀ p n k : ℕ, p.Prime → 5 ≤ p → 1 ≤ n → 1 ≤ k →
      ((p : ℤ) ^ (3 * k)) ∣ (a (n * p ^ k) - a (n * p ^ (k - 1))) := by
  sorry

end OMA.S_oeis_a351857
