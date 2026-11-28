import Mathlib

/-!
# A174525: Bases N in which ab and ba are different squares, for some a and b

Source: https://oeis.org/A174525
Credit: @xor2k

Formalizes the OEIS A174525 conjecture (from Robert Israel, Mar 14 2016):
Conjecture: all odd squares (A016754) except 1 are terms of the sequence.

Conventions:
* `N` is a term iff there are base-`N` digits `a`, `b` with `1 ≤ a < N` and `1 ≤ b < N`
  (leading 0's are not allowed, as the entry says, so neither digit is 0) such that the two-digit
  numerals `ab` and `ba`, i.e. the numbers `a * N + b` and `b * N + a`, are both perfect squares
  (`IsSquare`) and are different numbers.
* Odd squares except 1 are the natural numbers `N` with `IsSquare N`, `Odd N` and `N ≠ 1`.
-/

namespace OMA.S_oeis_a174525

/-- `N` is a term of A174525: some two-digit base-`N` numerals `ab` and `ba` with nonzero digits
are different perfect squares. -/
def IsTerm (N : ℕ) : Prop :=
  ∃ a b : ℕ, 1 ≤ a ∧ a < N ∧ 1 ≤ b ∧ b < N ∧
    IsSquare (a * N + b) ∧ IsSquare (b * N + a) ∧ a * N + b ≠ b * N + a

/-- Every odd square other than `1` is a term of A174525. -/
theorem main :
    ∀ N : ℕ, IsSquare N → Odd N → N ≠ 1 → IsTerm N := by
  sorry

end OMA.S_oeis_a174525
