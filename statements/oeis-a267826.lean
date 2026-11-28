import Mathlib

/-!
# A267826: Numbers not of the form w^3 + 2*x^3 + 3*y^3 + 4*z^3, where w, x, y and z are nonnegative integers.

Source: https://oeis.org/A267826
Credit: @azmiozgen

Conjecture (Zhi-Wei Sun, from the entry): the sequence has exactly 122 terms, the last of which is
a(122) = 41405. (Further implications stated in the entry are not part of this statement.)

Formalization notes:
* The set of non-represented n is stated to be finite with exactly 122 elements, 41405 not
  represented, and every n > 41405 represented.
* Controls (computed): below 50000 exactly 122 numbers are not represented, the last three being
  29137, 34974, 41405.
-/

namespace OMA.S_oeis_a267826

/-- `n` has the form `w³ + 2x³ + 3y³ + 4z³`. -/
def Rep (n : ℕ) : Prop := ∃ w x y z : ℕ, w ^ 3 + 2 * x ^ 3 + 3 * y ^ 3 + 4 * z ^ 3 = n

/-- The conjecture of the entry. -/
theorem main :
    {n : ℕ | ¬ Rep n}.ncard = 122 ∧ ¬ Rep 41405 ∧ ∀ n : ℕ, 41405 < n → Rep n := by
  sorry

end OMA.S_oeis_a267826
