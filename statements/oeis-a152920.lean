import Mathlib

/-!
# Schulte's conjectured transform of OEIS A152920

For rows n and columns 0 ≤ k ≤ n, A152920 has entries
2^k (n − k/2). Schulte's B(n,p) is the weighted sum of this row
divided by n+p+1. He conjectured B(n+1,p) = A(n,p) for all n,p ≥ 0.

Coquereaux reads the rectangular A(n,p) along the antidiagonals
of A193844. Row r of that triangle gives the coefficients, from
highest degree to lowest, of the sum of (X+2)^j for 0 ≤ j ≤ r.
Thus A(n,p) is the coefficient of X^p in the row n+p polynomial.

Sources: https://oeis.org/A152920 and https://oeis.org/A193844
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a152920
open Finset Polynomial

def triangle (n k : ℕ) : ℚ := 2^k * ((n:ℚ) - (k:ℚ)/2)

def weighted (n p : ℕ) : ℚ :=
  (∑ k ∈ range (n+1), (Nat.choose (p+k) p:ℚ) * triangle n k) / (n+p+1:ℚ)

noncomputable def rectangular (n p : ℕ) : ℚ :=
  (∑ j ∈ range (n+p+1), (X + C (2:ℚ))^j).coeff p

theorem main : ∀ n p : ℕ, weighted (n+1) p = rectangular n p := by
  sorry

end OMA.S_oeis_a152920
