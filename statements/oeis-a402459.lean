import Mathlib

/-!
# A402459: no base-three solution

Source: https://oeis.org/A402459
Credit: @rodolfoquint

OEIS conjectures that no positive square without the digit 2 in base 3 remains
square after every digit is increased by 1. The reported search through 16
digits is evidence for the conjecture, not a restriction on its quantifiers.

The source uses positive squares (its search requires x >= 1). `Nat.digits`
gives the canonical representation without leading zeros; both it and
`Nat.ofDigits` use least-significant-digit-first order. Excluding digit 2
ensures that increasing each digit by 1 causes no carries.
-/

namespace OMA.S_oeis_a402459

theorem main :
    ¬ ∃ m : ℕ, 0 < m ∧ IsSquare m ∧
      2 ∉ Nat.digits 3 m ∧
      IsSquare (Nat.ofDigits (3 : ℕ) ((Nat.digits 3 m).map (fun d => d + 1))) := by
  sorry

end OMA.S_oeis_a402459
