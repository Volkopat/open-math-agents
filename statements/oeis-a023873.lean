import Mathlib

/-!
# Peter Bala's supercongruence for OEIS A023873

Source: https://oeis.org/A023873 (Peter Bala, 21 January 2025).
Credit: @Hennyrick.
For an integer m, take the coefficient of degree n in A(X)^(m*n),
where A(X) is the product of (1-X^k)^(-k^4) over all positive k.
-/

namespace OMA.S_oeis_a023873

open Polynomial

/-- The base for the k-th factor, up to degree n. For positive m the
geometric sum agrees with the inverse of 1-X^k through that degree.
For negative m the base is 1-X^k itself. -/
noncomputable def factorBase (m : ℤ) (n k : ℕ) : Polynomial ℤ :=
  if 0 ≤ m then ∑ j ∈ Finset.range (n + 1), X ^ (k * j)
  else 1 - X ^ k

/-- Factors with k > n have no effect on the requested coefficient.
The absolute exponent is |m| * n * k^4, including when m is zero. -/
noncomputable def u (m : ℤ) (n : ℕ) : ℤ :=
  (∏ k ∈ Finset.Icc 1 n, (factorBase m n k) ^ (m.natAbs * n * k ^ 4)).coeff n

theorem main :
    ∀ (m : ℤ) (p n r : ℕ), p.Prime → 7 ≤ p → 0 < n → 0 < r →
      Int.ModEq ((p : ℤ) ^ (3 * r)) (u m (n * p ^ r)) (u m (n * p ^ (r - 1))) := by
  sorry

end OMA.S_oeis_a023873
