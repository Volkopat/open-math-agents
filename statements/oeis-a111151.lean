import Mathlib

/-!
# A111151: Numbers not of the form a^2 + b^3 + c^4 + d^5 for a,b,c,d >= 0.

Source: https://oeis.org/A111151
Credit: @azmiozgen

Conjecture (from the entry): this list is complete.

Formalization notes:
* Stated as equality of the set of non-represented numbers with the 22 listed values.
* Controls (computed): the n < 200000 not of this form are exactly the listed 22 numbers.
-/

namespace OMA.S_oeis_a111151



/-- The conjecture of the entry. -/
theorem main :
    {n : ℕ | ¬ ∃ a b c d : ℕ, a ^ 2 + b ^ 3 + c ^ 4 + d ^ 5 = n} =
      ({15, 23, 55, 62, 71, 471, 478, 510, 646, 806, 839, 879, 939, 1023, 1063, 1287, 2127, 5135, 6811,
        7499, 9191, 26471} : Set ℕ) := by
  sorry

end OMA.S_oeis_a111151
