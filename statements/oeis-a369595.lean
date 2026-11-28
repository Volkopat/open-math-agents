import Mathlib

/-!
# A369595: Array read by downward antidiagonals: A(n,k) = A(n-1,k+2) + Sum_{j=0..k} binomial(k,j)*A(n-1,j)
with A(0,k) = 1, n >= 0, k >= 0.

Source: https://oeis.org/A369595. Related: https://oeis.org/A135920
Credit: @Squee451

Data, by antidiagonals: 1; 1, 2; 1, 3, 7; 1, 5, 14, 37; 1, 9, 30, 89, 264; ...
(so A(0,0) = 1, A(1,0) = 2, A(2,0) = 7, A(3,0) = 37, A(4,0) = 264).

The entry's formula line: Conjecture: A(n,0) = A135920(n+1). (Mikhail Kurkov, 27 October 2024)

A135920 (offset 0; data 1, 1, 2, 7, 37, 264, 2433, 27913, ...) is defined by its ordinary generating
function: A(x) = Sum_{n>=0} x^n / Product_{k=0..n} (1 - k^2*x).

Conventions.
* `A135920 m` is the coefficient of `x^m` in that series, taken in the formal power series over ℚ.
  The summand with index `n` is divisible by `x^n`, so only the summands with `n ≤ m` contribute to
  the coefficient of `x^m`; the finite sum over `n ≤ m` is used.
-/

namespace OMA.S_oeis_a369595

open PowerSeries

/-- The array A369595. -/
def A : ℕ → ℕ → ℕ
  | 0, _ => 1
  | n + 1, k => A n (k + 2) + ∑ j ∈ Finset.range (k + 1), k.choose j * A n j

/-- A135920: the coefficient of `x^m` in `Sum_{n>=0} x^n / Product_{k=0..n} (1 - k^2*x)`. -/
noncomputable def A135920 (m : ℕ) : ℚ :=
  coeff m (∑ n ∈ Finset.range (m + 1),
    (X : PowerSeries ℚ) ^ n * ∏ k ∈ Finset.range (n + 1), (1 - C ((k : ℚ) ^ 2) * X)⁻¹)

theorem main : ∀ n : ℕ, (A n 0 : ℚ) = A135920 (n + 1) := by
  sorry

end OMA.S_oeis_a369595
