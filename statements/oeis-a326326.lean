import Mathlib

/-!
# A326326: coefficients of sums of rising factorials via Stirling numbers

Source: https://oeis.org/A326326 (conjecture by Werner Schulte, Mar 30 2022)

`T(n, k) = [x^k] Sum_{j=0..n} Pochhammer(x, j)` for `0 <= k <= n` (offset 0), where
`Pochhammer(x, j) = x (x+1) ... (x+j-1)` is the rising factorial, here Mathlib's
`ascPochhammer ℕ j`.

A132393 is the triangle of unsigned Stirling numbers of the first kind, `T(n, k)` for
`0 <= k <= n`, with `T(n,k) = T(n-1,k-1) + (n-1) T(n-1,k)`, `T(n,0) = [n = 0]`;
this is Mathlib's `Nat.stirlingFirst n k` (permutations of `n` elements with `k` cycles).

The conjecture: `T(n,k) = Sum_{i=0..n} A132393(i,k)` for `0 <= k <= n`.
-/

namespace OMA.S_oeis_a326326

open Polynomial

/-- OEIS A326326. -/
noncomputable def T (n k : ℕ) : ℕ := (∑ j ∈ Finset.range (n + 1), ascPochhammer ℕ j).coeff k

/-- OEIS A132393: unsigned Stirling numbers of the first kind. -/
def A132393 (n k : ℕ) : ℕ := Nat.stirlingFirst n k

theorem main : ∀ n k : ℕ, k ≤ n → T n k = ∑ i ∈ Finset.range (n + 1), A132393 i k := by
  sorry

end OMA.S_oeis_a326326
