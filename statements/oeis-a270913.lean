import Mathlib

/-!
# A270913: coefficient of x^n in Product_{k>=1} (1+x^k)^n

Source: https://oeis.org/A270913

`a(n) = [x^n] Product_{k>=1} (1 + x^k)^n`, offset 0. A factor `(1 + x^k)^n` with `k > n` is `1` up to
terms of degree above `n`, so the coefficient of `x^n` is that of the finite product over `1 <= k <= n`,
taken in the integer power series.

The entry (Peter Bala, Apr 18 2023) first states the Gauss congruences as a fact and then conjectures:
the supercongruence `a(p) == p + 1 (mod p^2)` holds for all primes `p`. This file states that conjecture.
-/

namespace OMA.S_oeis_a270913

/-- A270913: `a(n) = [x^n] Product_{k=1..n} (1 + x^k)^n`. -/
noncomputable def a (n : ℕ) : ℤ :=
  PowerSeries.coeff n (∏ k ∈ Finset.Icc 1 n, (1 + PowerSeries.X ^ k : PowerSeries ℤ) ^ n)

/-- Bala's conjectured supercongruence: `a(p) == p + 1 (mod p^2)` for every prime `p`. -/
theorem main : ∀ p : ℕ, p.Prime → ((p : ℤ) ^ 2) ∣ (a p - ((p : ℤ) + 1)) := by
  sorry

end OMA.S_oeis_a270913
