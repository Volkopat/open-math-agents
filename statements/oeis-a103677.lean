import Mathlib

/-!
# A103677: Numbers m such that in binary representation m! doesn't contain 5!.

Source: https://oeis.org/A103677
Credit: @azmiozgen

Conjecture (from the entry): there are no further terms (beyond the 30 listed, the last being 65).

Formalization notes:
* 5! = 120 = 1111000 in binary; "m! contains 5!" means the binary digit string of 120 occurs as a
  contiguous block of the binary digits of m! (`List.IsInfix` on `Nat.digits 2`, least significant
  first; reversing both lists preserves the relation).
* Stated as equality of the set of terms with the 30 listed values.
* Controls (computed): the m < 2500 whose factorial does not contain 1111000 in binary are exactly
  the listed values.
-/

namespace OMA.S_oeis_a103677



/-- The conjecture of the entry. -/
theorem main :
    {m : ℕ | ¬ (Nat.digits 2 120).IsInfix (Nat.digits 2 m.factorial)} =
      ({0, 1, 2, 3, 4, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 24, 26, 28, 30, 31, 32, 36,
        46, 53, 58, 65} : Set ℕ) := by
  sorry

end OMA.S_oeis_a103677
