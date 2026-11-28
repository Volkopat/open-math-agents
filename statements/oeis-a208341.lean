import Mathlib

/-!
# A208341: T(n,k) = hypergeometric_2F1([n-k+1, -k], [1], -1)
Source: https://oeis.org/A208341 (Werner Schulte, Mar 20 2026)

T(n,k) = 2F1([n-k+1, -k], [1], -1) for 0 <= k <= n, where
2F1([a, b], [c], z) = Sum_{j >= 0} (a)_j (b)_j / ((c)_j j!) z^j with (x)_j the rising factorial
(ascPochhammer in Mathlib). Since b = -k is a nonpositive integer, (b)_j = 0 for j > k, so the
series terminates and equals its partial sum over j = 0..k. Values are taken in the rationals.

Conjecture: T(n,k) * 2^(n-2k) = T(n,n-k) for 0 <= k <= n (the power 2^(n-2k) is an integer
power of 2, possibly with negative exponent).
-/

namespace OMA.S_oeis_a208341

open Polynomial

/-- The terminating Gauss hypergeometric series, summed over j = 0..N. -/
noncomputable def hyp2F1 (a b c z : ℚ) (N : ℕ) : ℚ :=
  ∑ j ∈ Finset.range (N + 1), (ascPochhammer ℚ j).eval a * (ascPochhammer ℚ j).eval b /
    ((ascPochhammer ℚ j).eval c * (j.factorial : ℚ)) * z ^ j

/-- A208341: T(n,k) = 2F1([n-k+1, -k], [1], -1); the series terminates at j = k. -/
noncomputable def T (n k : ℕ) : ℚ := hyp2F1 ((n : ℚ) - k + 1) (-(k : ℚ)) 1 (-1) k

theorem main : ∀ n k : ℕ, k ≤ n → T n k * (2 : ℚ) ^ ((n : ℤ) - 2 * k) = T n (n - k) := by
  sorry

end OMA.S_oeis_a208341
