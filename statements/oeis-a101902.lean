import Mathlib

/-!
# A101902: Numbers n that are not of the form ab+bc+cd+de+ea with 1<=a<=b<=c<=d<=e.

Source: https://oeis.org/A101902
Credit: @azmiozgen

Conjecture (from the entry; a later comment states that the sequence is indeed complete): the sequence is complete.

Formalization notes:
* Stated as equality of the set of positive n not of this form with the 13 listed values.
* Controls (computed): the 1 ≤ n < 3000 not of this form are exactly 1, 2, 3, 4, 6, 8, 12, 14, 18,
  30, 38, 42, 62.
-/

namespace OMA.S_oeis_a101902



/-- The conjecture of the entry. -/
theorem main :
    {n : ℕ | 0 < n ∧ ¬ ∃ a b c d e : ℕ, 1 ≤ a ∧ a ≤ b ∧ b ≤ c ∧ c ≤ d ∧ d ≤ e ∧
        a * b + b * c + c * d + d * e + e * a = n} =
      ({1, 2, 3, 4, 6, 8, 12, 14, 18, 30, 38, 42, 62} : Set ℕ) := by
  sorry

end OMA.S_oeis_a101902
