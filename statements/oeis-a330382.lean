import Mathlib

/-!
# A330382: k-1 | 2^k-2 at cubes of Mersenne numbers

Source: https://oeis.org/A330382

A330382 (Amiram Eldar and Thomas Ordowski) lists the composite numbers k such that
k-1 divides 2^k-2. Its comments state the conjecture:
k-1 | 2^k-2 for k = (2^n-1)^3 if and only if n(n-1) | 2^n-2, for n > 2.

Conventions:
* All quantities are natural numbers; for n > 2 both `(2^n-1)^3 - 1` and `2^n - 2` are positive,
  so truncated subtraction does not occur.
-/

namespace OMA.S_oeis_a330382

/-- For `n > 2`, with `k = (2^n-1)^3`: `k - 1 ∣ 2^k - 2` iff `n(n-1) ∣ 2^n - 2`. -/
theorem main : ∀ n : ℕ, 2 < n →
    ((2 ^ n - 1) ^ 3 - 1 ∣ 2 ^ ((2 ^ n - 1) ^ 3) - 2 ↔ n * (n - 1) ∣ 2 ^ n - 2) := by
  sorry

end OMA.S_oeis_a330382
