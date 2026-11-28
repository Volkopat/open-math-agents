import Mathlib

/-!
# A333579: a(n) = [x^n] ( (1 + x + x^2)/(1 - x + x^2) )^n

Source: https://oeis.org/A333579

The quotient is taken in the integer power series, where `1 - x + x^2` is invertible (its constant
coefficient is 1).

The entry makes two conjectural statements, stated together here:

1. `a(p) == 2 (mod p^3)` for prime `p >= 5` (checked up to `p = 499`);
2. calculation suggests that `a(p^k) == a(p^(k-1)) (mod p^(2*k))` for prime `p >= 5` and `k > 1`.

A congruence `x == y (mod N)` between integers is written as `N ∣ x - y`.
-/

namespace OMA.S_oeis_a333579

/-- The integer power series `(1 + x + x^2)/(1 - x + x^2)`. -/
noncomputable def f : PowerSeries ℤ :=
  (1 + PowerSeries.X + PowerSeries.X ^ 2) * Ring.inverse (1 - PowerSeries.X + PowerSeries.X ^ 2)

/-- A333579: `a(n) = [x^n] f(x)^n`. -/
noncomputable def a (n : ℕ) : ℤ :=
  PowerSeries.coeff n (f ^ n)

/-- The two conjectured congruences of the entry. -/
theorem main :
    (∀ p : ℕ, p.Prime → 5 ≤ p → ((p : ℤ) ^ 3) ∣ (a p - 2)) ∧
    (∀ p k : ℕ, p.Prime → 5 ≤ p → 1 < k →
      ((p : ℤ) ^ (2 * k)) ∣ (a (p ^ k) - a (p ^ (k - 1)))) := by
  sorry

end OMA.S_oeis_a333579
