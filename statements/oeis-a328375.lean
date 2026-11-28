import Mathlib

/-!
# A328375: Numbers k such that the decimal expansion of 2^k contains the substring 777.

Source: https://oeis.org/A328375
Credit: @eltociear

The sequence (offset 1) lists, in increasing order, the `k` such that the decimal expansion of
`2^k` contains three consecutive digits `7` (`a(1) = 24`, `a(2) = 40`, `a(3) = 75`). It is
infinite (`2^k` ends in `7776` when `k ≡ 40 (mod 500)`). The entry records the conjecture
(Chai Wah Wu, Oct 26 2019):

  if n > 30536, then a(n) = n + 3623.

`a(n)` is `Nat.nth Has777 (n - 1)` (`Nat.nth` counts from `0`). The decimal expansion of `m`
read from the most significant digit is `(Nat.digits 10 m).reverse`, and "contains the
substring 777" is `List.IsInfix` (`<:+:`) of `[7, 7, 7]`.
-/

namespace OMA.S_oeis_a328375

/-- The decimal expansion of `2 ^ k` contains the substring `777`. -/
def Has777 (k : ℕ) : Prop := [7, 7, 7] <:+: (Nat.digits 10 (2 ^ k)).reverse

/-- The conjecture in OEIS A328375: for `n > 30536`, the `n`-th term (1-indexed) is `n + 3623`. -/
theorem main : ∀ n : ℕ, 30536 < n → Nat.nth Has777 (n - 1) = n + 3623 := by
  sorry

end OMA.S_oeis_a328375
-- ci: re-run check-proof
