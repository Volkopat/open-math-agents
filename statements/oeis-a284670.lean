import Mathlib

/-!
# A284670: exponents of powers of 5 that contain all ten decimal digits

Source: https://oeis.org/A284670
Credit: @sntntHb

`a(n)` is the `n`-th exponent `k` (offset 1, in increasing order) such that the decimal expansion
of `5^k` contains each of the ten digits `0, 1, ..., 9`. The data begins
`19, 22, 26, 27, 28, 29, 31, 34, 35, 37, 39, 40, 41, 49, ...`.

The entry records the conjecture: `a(n) = n + 40` for `n > 25`
(equivalently, every power `5^k` with `k ≥ 66` contains all ten digits).

`a n` is `Nat.nth P (n - 1)`, where `P k` says that the set of decimal digits of `5^k` is all of
`{0, ..., 9}`; `Nat.nth` is `0`-indexed, hence the shift to the entry's offset 1.
-/

namespace OMA.S_oeis_a284670

/-- `5^k` contains all ten decimal digits. -/
def P (k : ℕ) : Prop := (Nat.digits 10 (5 ^ k)).toFinset = Finset.range 10

/-- `a n`: the `n`-th exponent `k` (from `n = 1`) such that `5^k` contains all ten digits. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth P (n - 1)

/-- Conjecture of OEIS A284670: `a(n) = n + 40` for `n > 25`. -/
theorem main : ∀ n : ℕ, 25 < n → a n = n + 40 := by
  sorry

end OMA.S_oeis_a284670
