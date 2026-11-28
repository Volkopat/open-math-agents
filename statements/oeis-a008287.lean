import Mathlib

/-!
# A008287: a binomial sum for the quadrinomial coefficients

Source: https://oeis.org/A008287 (OEIS Foundation, CC BY-SA 4.0).

T(n, k) is the coefficient of x^k in (1 + x + x^2 + x^3)^n. Werner Schulte
(Sep 09 2015) conjectured that
T(n, k) = Sum_{j=0..k} (-2)^j * binomial(n, j) * binomial(3n - 2j, k - j)
for n >= 0 and 0 <= k <= 3n.

Whenever j > n the factor binomial(n, j) vanishes, so the truncated natural
subtraction 3n - 2j only matters in terms that are zero anyway.
-/

namespace OMA.S_oeis_a008287

open Polynomial

/-- The quadrinomial coefficient: the coefficient of `x^k` in `(1 + x + x^2 + x^3)^n`. -/
noncomputable def T (n k : ℕ) : ℤ := ((1 + X + X ^ 2 + X ^ 3 : ℤ[X]) ^ n).coeff k

theorem main : ∀ n k : ℕ, k ≤ 3 * n →
    T n k = ∑ j ∈ Finset.range (k + 1),
      (-2 : ℤ) ^ j * (n.choose j : ℤ) * ((3 * n - 2 * j).choose (k - j) : ℤ) := by
  sorry

end OMA.S_oeis_a008287
