import Mathlib

/-!
# A249969: Numbers whose squares remain squares when prepended with 3 and appended with 25 in base 10

Source: https://oeis.org/A249969
Credit: @xor2k

Formalizes the OEIS A249969 conjecture: squares of numbers in the sequence end in either 00 or 56.

Conventions:
* A term is a positive integer `k` such that the base-10 number whose digit string is `3`,
  followed by the decimal digits of `k ^ 2`, followed by `25`, is a square.
  (Positivity matches the OEIS data, which starts at 84.)
* That number is built with `Nat.ofDigits 10` from the little-endian digit list
  `[5, 2] ++ Nat.digits 10 (k ^ 2) ++ [3]` (least significant digit first), i.e. it equals
  `(3 * 10 ^ (number of digits of k ^ 2) + k ^ 2) * 100 + 25`.
* Ending in 00 or 56 in base 10 means `k ^ 2 % 100 = 0` or `k ^ 2 % 100 = 56`.
-/

namespace OMA.S_oeis_a249969

/-- The decimal concatenation of `3`, the digits of `s`, and `25`. -/
def extend (s : ℕ) : ℕ :=
  Nat.ofDigits 10 ([5, 2] ++ Nat.digits 10 s ++ [3])

/-- Membership in A249969: a positive `k` whose square stays a square after the extension. -/
def InSeq (k : ℕ) : Prop :=
  0 < k ∧ IsSquare (extend (k ^ 2))

/-- For every term `k` of A249969, `k ^ 2` ends in 00 or 56 in base 10. -/
theorem main :
    ∀ k : ℕ, InSeq k → k ^ 2 % 100 = 0 ∨ k ^ 2 % 100 = 56 := by
  sorry

end OMA.S_oeis_a249969
