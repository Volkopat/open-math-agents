import Mathlib

/-!
# A345754: 2 X 2 matrices over Z_n whose permanent equals their determinant

Source: https://oeis.org/A345754 (conjectured formula in the entry, Jul 2021)

`a(n)` (offset 1) is the number of `2 X 2` matrices `M` over `ZMod n` with
`permanent M = det M`, using Mathlib's `Matrix.permanent` and `Matrix.det`. The hypothesis
`NeZero n` (that is, `n >= 1`) makes `ZMod n` finite.

A344372 is `a(n) = Sum_{k=1..n} gcd(2k, n)`.

The conjecture: `a(n) = A344372(n) * n^2` for all `n >= 1`.
-/

namespace OMA.S_oeis_a345754

/-- OEIS A345754. -/
def a (n : ℕ) [NeZero n] : ℕ :=
  (Finset.univ.filter (fun M : Matrix (Fin 2) (Fin 2) (ZMod n) => M.permanent = M.det)).card

/-- OEIS A344372. -/
def A344372 (n : ℕ) : ℕ := ∑ k ∈ Finset.Icc 1 n, Nat.gcd (2 * k) n

theorem main : ∀ (n : ℕ) [NeZero n], a n = A344372 n * n ^ 2 := by
  sorry

end OMA.S_oeis_a345754
