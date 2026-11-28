import Mathlib

/-!
# A131627: Numbers k such that the decimal expansion of 3^k contains no 1.

Source: https://oeis.org/A131627
Credit: @azmiozgen

Conjecture (from the entry): 43 is the last term.

Formalization notes:
* "43 is the last term" is stated as: 43 is a term, and for every k > 43 the digit 1 occurs in the
  decimal digits of 3^k (`Nat.digits 10`).
* Controls (computed): among k < 3000 there are 14 terms, the largest being 43.
-/

namespace OMA.S_oeis_a131627



/-- The conjecture of the entry. -/
theorem main :
    (¬ 1 ∈ Nat.digits 10 (3 ^ 43)) ∧ ∀ k : ℕ, 43 < k → 1 ∈ Nat.digits 10 (3 ^ k) := by
  sorry

end OMA.S_oeis_a131627
