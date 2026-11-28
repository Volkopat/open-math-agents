import Mathlib

/-!
# A291697: a(n) = [x^n] Product_{k>=0} ((1 + x^(2*k+1))/(1 - x^(2*k+1)))^n

Source: https://oeis.org/A291697

Offset 0. The quotient `(1 + x^m)/(1 - x^m)` is taken in the integer power series, where `1 - x^m` is
invertible for `m >= 1` (its constant coefficient is 1). A factor with `2*k+1 > n` is `1` up to terms of
degree above `n`, so the coefficient of `x^n` is that of the finite product over the odd `m = 2*k+1 <= n`,
that is over `k < (n+1)/2`.

The entry (Peter Bala, Apr 18 2023) first states the Gauss congruences as a fact and then conjectures:
the supercongruence `a(p) == 2*p + 2 (mod p^3)` holds for all primes `p >= 5`. This file states that conjecture.
-/

namespace OMA.S_oeis_a291697

/-- The integer power series `(1 + x^m)/(1 - x^m)`. -/
noncomputable def factor (m : ℕ) : PowerSeries ℤ :=
  (1 + PowerSeries.X ^ m) * Ring.inverse (1 - PowerSeries.X ^ m)

/-- A291697: `a(n) = [x^n] Product_{k=0..(n-1)/2} ((1 + x^(2*k+1))/(1 - x^(2*k+1)))^n`. -/
noncomputable def a (n : ℕ) : ℤ :=
  PowerSeries.coeff n (∏ k ∈ Finset.range ((n + 1) / 2), (factor (2 * k + 1)) ^ n)

/-- Bala's conjectured supercongruence: `a(p) == 2*p + 2 (mod p^3)` for every prime `p >= 5`. -/
theorem main : ∀ p : ℕ, p.Prime → 5 ≤ p → ((p : ℤ) ^ 3) ∣ (a p - (2 * (p : ℤ) + 2)) := by
  sorry

end OMA.S_oeis_a291697
