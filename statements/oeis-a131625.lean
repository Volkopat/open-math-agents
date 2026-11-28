import Mathlib

/-!
# A131625: Numbers k such that decimal expansion of 3^k contains no 2.

Source: https://oeis.org/A131625
Credit: @azmiozgen

Conjecture (from the entry): 59 is the last term.

Formalization notes:
* "59 is the last term" is stated as: 59 is a term, and for every k > 59 the digit 2 occurs in the
  decimal digits of 3^k (`Nat.digits 10`).
* Controls (computed): among k < 3000 there are 17 terms, the largest being 59.
-/

namespace OMA.S_oeis_a131625



/-- The conjecture of the entry. -/
theorem main :
    (¬ 2 ∈ Nat.digits 10 (3 ^ 59)) ∧ ∀ k : ℕ, 59 < k → 2 ∈ Nat.digits 10 (3 ^ k) := by
  sorry

end OMA.S_oeis_a131625
