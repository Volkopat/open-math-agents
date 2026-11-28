import Mathlib

/-!
# A380191: Triangle read by rows: Riordan array (2 - D(x), x * D(x)) where D(x) is g.f. of A001764.

Source: https://oeis.org/A380191
Credit: @agchua

Formula section of A380191 (by Werner Schulte, Jan 15 2025):
  Conjecture: Sum_{i=0..n-k} binomial(2*i, i) * T(n, i+k) = A110616(n, k).

Both triangles A380191 and A110616 have offset 0 (0 <= k <= n). Here D(x) is the ordinary
generating function of A001764, whose n-th coefficient is binomial(3*n, n) / (2*n + 1).
A380191 is defined directly from its name line as the Riordan array (2 - D(x), x * D(x)),
meaning T(n, k) = [x^n] ((2 - D(x)) * (x * D(x))^k). A110616 is the convolution triangle
based on A001764, i.e., the Riordan array (D(x), x * D(x)), meaning
A110616(n, k) = [x^n] (D(x) * (x * D(x))^k). The conjecture is stated for all 0 <= k <= n.
-/

namespace OMA.S_oeis_a380191

/-- Ordinary generating function D(x) of A001764: a(n) = binomial(3*n, n) / (2*n + 1). -/
noncomputable def D : PowerSeries ℚ :=
  PowerSeries.mk (fun n => (Nat.choose (3 * n) n : ℚ) / ((2 * n + 1 : ℕ) : ℚ))

/-- A380191 triangle T(n, k): Riordan array (2 - D(x), x * D(x)). -/
noncomputable def T (n k : ℕ) : ℚ :=
  PowerSeries.coeff n ((2 - D) * (PowerSeries.X * D) ^ k)

/-- A110616 triangle: convolution triangle of A001764, Riordan array (D(x), x * D(x)). -/
noncomputable def A110616 (n k : ℕ) : ℚ :=
  PowerSeries.coeff n (D * (PowerSeries.X * D) ^ k)

/-- Conjecture of A380191: Sum_{i=0..n-k} binomial(2*i, i) * T(n, i+k) = A110616(n, k)
    for all 0 <= k <= n. -/
theorem main : ∀ n k : ℕ, k ≤ n →
    ∑ i ∈ Finset.range (n - k + 1), (Nat.choose (2 * i) i : ℚ) * T n (i + k) = A110616 n k := by
  sorry

end OMA.S_oeis_a380191
