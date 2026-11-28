import Mathlib

/-!
# A355007: Triangle read by rows. T(n, k) = n^k * |Stirling1(n, k)|

Source: https://oeis.org/A355007
Auxiliary sequence: https://oeis.org/A056856
Credit: @jagong-cmu

Formalizes the conjecture of R. J. Mathar (Mar 31 2023):
T(n,k) = A056856(n,k)*n.

Conventions:
* `T n k` follows the OEIS name literally. `Nat.stirlingFirst n k` is Mathlib's unsigned
  Stirling number of the first kind, which is `|Stirling1(n, k)|`.
* A056856 (offset 1, triangle with rows `n >= 1` and columns `1 <= k <= n`, as in its
  Mathematica programs and its data) has the vague name: Triangle of numbers related to rooted
  trees and unrooted planar trees. Its explicit row formula in OEIS is
  `Sum_{k = 0..n-1} T(n,k)*y^k = Product_{k = 1..n-1} (k + n*y)` (also the Maple program of
  Peter Bala). The row formula uses a zero-based column index, while the data and the other
  programs use `k = 1..n`; so entry `(n,k)` with `1 <= k <= n` is the coefficient of `y^(k-1)`
  in `Product_{j = 1..n-1} (j + n*y)`. With this convention row 3 is `2, 9, 9`, as in the
  OEIS data. The polynomial is taken in `ℕ[X]`.
* The conjecture is stated where both triangles have entries: `1 <= k <= n`. (For `k = 0`,
  A355007 has `T(n,0) = 0` for `n >= 1`, but A056856 has no column 0.)
-/

namespace OMA.S_oeis_a355007

open Polynomial

/-- `T(n, k) = n^k * |Stirling1(n, k)|`. -/
def T (n k : ℕ) : ℕ := n ^ k * Nat.stirlingFirst n k

/-- A056856(n, k) for `1 <= k <= n`: the coefficient of `y^(k-1)` in
`Product_{j = 1..n-1} (j + n*y)`. -/
noncomputable def A056856 (n k : ℕ) : ℕ :=
  (∏ j ∈ Finset.Icc 1 (n - 1), (C (j : ℕ) + C n * X)).coeff (k - 1)

/-- For `1 <= k <= n`: `T(n,k) = A056856(n,k)*n`. -/
theorem main : ∀ n k : ℕ, 1 ≤ k → k ≤ n → T n k = A056856 n k * n := by
  sorry

end OMA.S_oeis_a355007
