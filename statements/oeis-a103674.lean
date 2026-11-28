import Mathlib

/-!
# A103674: If in binary representation n! contains 6! then 1 else 0.

Source: https://oeis.org/A103674
Credit: @eltociear

`a(n)` (offset 0) is `1` if the binary representation of `n!` contains the binary representation
of `6! = 720` (`1011010000`) as a block of consecutive digits, and `0` otherwise. The entry
records (Charles R Greathouse IV, checked to `5·10^5` by Giovanni Resta):

  Conjecture: a(n) = 1 for n > 802.

`main` states that for every `n > 802` the binary digits of `720` occur consecutively in those of
`n!`. Binary representations are read from the most significant digit, `(Nat.digits 2 m).reverse`,
and "contains" is `List.IsInfix` (`<:+:`).
-/

namespace OMA.S_oeis_a103674


/-- The conjecture in OEIS A103674: for `n > 802`, the binary expansion of `n!` contains that of
`6!`. -/
theorem main : ∀ n : ℕ, 802 < n → (Nat.digits 2 720).reverse <:+: (Nat.digits 2 n.factorial).reverse := by
  sorry

end OMA.S_oeis_a103674
