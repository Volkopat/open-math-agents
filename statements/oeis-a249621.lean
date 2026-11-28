import Mathlib

/-!
# A249621: Squares that remain squares when prepended with 1 and appended with 25 in base 10

Source: https://oeis.org/A249621
Credit: @xor2k

Formalizes the OEIS A249621 conjecture: all the numbers in the sequence end in either 00 or 56.

Conventions:
* A term is a positive square `s` such that the base-10 number whose digit string is
  `1`, followed by the decimal digits of `s`, followed by `25`, is again a square.
* That number is built with `Nat.ofDigits 10` from the little-endian digit list
  `[5, 2] ++ Nat.digits 10 s ++ [1]` (least significant digit first), i.e. it equals
  `(10 ^ (number of digits of s) + s) * 100 + 25`.
* Ending in 00 or 56 in base 10 means `s % 100 = 0` or `s % 100 = 56`.
-/

namespace OMA.S_oeis_a249621

/-- The decimal concatenation of `1`, the digits of `s`, and `25`. -/
def extend (s : ℕ) : ℕ :=
  Nat.ofDigits 10 ([5, 2] ++ Nat.digits 10 s ++ [1])

/-- Membership in A249621: a positive square that stays a square after the extension. -/
def InSeq (s : ℕ) : Prop :=
  0 < s ∧ IsSquare s ∧ IsSquare (extend s)

/-- Every term of A249621 ends in 00 or 56 in base 10. -/
theorem main :
    ∀ s : ℕ, InSeq s → s % 100 = 0 ∨ s % 100 = 56 := by
  sorry

end OMA.S_oeis_a249621
