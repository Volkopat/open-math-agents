import Mathlib

/-!
# A277028: Numbers that are never pandigital for any base b > 1.

Source: https://oeis.org/A277028
Credit: @keiichisince1986-bot

A277028 lists the numbers that are not pandigital in any base `b > 1`:
`0, 1, 3, 7, 31, 255, 32767`.
Here, as the entry says, a number is pandigital in base `b` if every digit from `0` to `b - 1`
appears at least once in its base-`b` representation (ignoring leading zeros).
The entry states: This is a subsequence of A000225, conjectured to be finite (no other term below
2^1000000; none below 2^10^10 either).

Conventions:
- `IsPandigital b n`: every `d < b` occurs in `Nat.digits b n`, the base-`b` digit list of `n`
  without leading zeros.
- For `n = 0` the digit list is empty, so `0` is not pandigital in any base, matching the data
  (whose first term is `0`).
- The conjecture says that the set of natural numbers that are not pandigital in any base
  `b > 1` is finite.
-/

namespace OMA.S_oeis_a277028

/-- `n` is pandigital in base `b`: every digit `0, …, b - 1` occurs among its base-`b` digits. -/
def IsPandigital (b n : ℕ) : Prop :=
  ∀ d < b, d ∈ Nat.digits b n

theorem main : {n : ℕ | ∀ b : ℕ, 1 < b → ¬ IsPandigital b n}.Finite := by
  sorry

end OMA.S_oeis_a277028
