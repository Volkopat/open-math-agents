import Mathlib

/-!
# A131629: Numbers k such that the decimal expansion of 3^k contains no 3.

Source: https://oeis.org/A131629
Credit: @azmiozgen

Conjecture (from the entry): 84 is the last term.

Formalization notes:
* "84 is the last term" is stated as: 84 is a term, and for every k > 84 the digit 3 occurs in the
  decimal digits of 3^k (`Nat.digits 10`).
* Controls (computed): among k < 3000 there are 18 terms, the largest being 84.
-/

namespace OMA.S_oeis_a131629



/-- The conjecture of the entry. -/
theorem main :
    (¬ 3 ∈ Nat.digits 10 (3 ^ 84)) ∧ ∀ k : ℕ, 84 < k → 3 ∈ Nat.digits 10 (3 ^ k) := by
  sorry

end OMA.S_oeis_a131629
