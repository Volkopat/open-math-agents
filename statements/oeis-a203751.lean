import Mathlib

/-!
# A203751: Square root of v(2*n+1)/(3*v(2*n)), where v = A203748.

Source: https://oeis.org/A203751 (v: https://oeis.org/A203748)
Credit: @agchua

Peter Bala (Dec 01 2025), in the formula section of A203751:
  Conjecture: a(n) = n^2/(n-1)! * Product_{k = 1..n-1} (n^3 - k^3). - _Peter Bala_, Dec 01 2025
A203751 has offset 1, so the claim is stated for n >= 1 (for n = 1 the product is empty).

A203748 (offset 1): Vandermonde sequence using x^2 + xy + y^2 applied to (0,1,1,2,2,...,floor(n/2)).
Its Mathematica program, with f(j) = floor(j/2), reads
  u := Product[f[j]^2 + f[j] f[k] + f[k]^2, {j, 1, k - 1}],  v[n_] := Product[u, {k, 2, n}],
that is v(n) = Product_{k=2..n} Product_{j=1..k-1} (f(j)^2 + f(j) f(k) + f(k)^2). This gives the
listed terms 1, 1, 3, 588, 1382976, ...; every factor is positive, since f(k) >= 1 for k >= 2.
A203751 is the square root of v(2n+1)/(3 v(2n)), taken below in the reals.
-/

namespace OMA.S_oeis_a203751

/-- A203748: v(n) = Product_{k=2..n} Product_{j=1..k-1} (f(j)^2 + f(j) f(k) + f(k)^2),
with f(j) = floor(j/2). -/
def v (n : ℕ) : ℕ :=
  ∏ k ∈ Finset.Icc 2 n, ∏ j ∈ Finset.Icc 1 (k - 1),
    ((j / 2) ^ 2 + (j / 2) * (k / 2) + (k / 2) ^ 2)

/-- A203751: the square root of v(2n+1)/(3 v(2n)). -/
noncomputable def a (n : ℕ) : ℝ :=
  Real.sqrt ((v (2 * n + 1) : ℝ) / (3 * (v (2 * n) : ℝ)))

/-- Bala's conjecture: a(n) = n^2/(n-1)! * Product_{k = 1..n-1} (n^3 - k^3) for n >= 1. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    a n = (n : ℝ) ^ 2 / ((n - 1).factorial : ℝ) *
      ∏ k ∈ Finset.Icc 1 (n - 1), ((n : ℝ) ^ 3 - (k : ℝ) ^ 3) := by
  sorry

end OMA.S_oeis_a203751
