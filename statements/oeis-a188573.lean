import Mathlib

/-!
# A188573: a(n) = coefficient of the sqrt(6) term in (1 + sqrt(2) + sqrt(3))^n.

Source: https://oeis.org/A188573
Credit: @ShoQo

Conjecture (Clark Kimberling, Oct 23 2024): "every prime divides a(n) for infinitely many n, and
if K(p) = (k(1), k(2),...) is the maximal subsequence of indices n such that p divides a(n), then
the difference sequence of K(p) is eventually periodic".

Formalization notes:
* Since 1, √2, √3, √6 are linearly independent over ℚ, (1 + √2 + √3)^n = A + B√2 + C√3 + D√6
  for unique integers A, B, C, D, and multiplying A + B√2 + C√3 + D√6 by 1 + √2 + √3 gives
  (A + 2B + 3C) + (A + B + 3D)√2 + (A + C + 2D)√3 + (B + C + D)√6. So the coefficient vectors are
  the iterates of `step` from (1, 0, 0, 0), and a(n) is the last coordinate (offset 0; data:
  0, 0, 2, 6, 32, 120, 528, ...).
* K(p) is the set {n | p ∣ a(n)}. Once it is infinite, its difference sequence is eventually
  periodic exactly when its indicator is eventually periodic, which is how the second part is
  stated: there are N and T > 0 with p ∣ a(n + T) ↔ p ∣ a(n) for all n ≥ N.
* The entry's listed periods for the first primes are data, not part of the general claim, and
  are not stated.
-/

namespace OMA.S_oeis_a188573

/-- Multiplication by 1 + √2 + √3 on coefficient vectors in the basis 1, √2, √3, √6. -/
def step (x : ℤ × ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ × ℤ :=
  (x.1 + 2 * x.2.1 + 3 * x.2.2.1, x.1 + x.2.1 + 3 * x.2.2.2, x.1 + x.2.2.1 + 2 * x.2.2.2,
    x.2.1 + x.2.2.1 + x.2.2.2)

/-- The coefficients of (1 + √2 + √3)^n. -/
def coeffs (n : ℕ) : ℤ × ℤ × ℤ × ℤ := step^[n] (1, 0, 0, 0)

/-- A188573: the coefficient of √6. -/
def a (n : ℕ) : ℤ := (coeffs n).2.2.2

theorem main : ∀ p : ℕ, p.Prime →
    {n : ℕ | (p : ℤ) ∣ a n}.Infinite ∧
      ∃ N T : ℕ, 0 < T ∧ ∀ n, N ≤ n → ((p : ℤ) ∣ a (n + T) ↔ (p : ℤ) ∣ a n) := by
  sorry

end OMA.S_oeis_a188573
