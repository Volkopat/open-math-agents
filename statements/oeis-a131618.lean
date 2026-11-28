import Mathlib

/-!
# A131618: Numbers k such that the decimal expansion of 3^k contains no 4.

Source: https://oeis.org/A131618
Credit: @azmiozgen

Conjecture (from the entry): 106 is the last term.

Formalization notes:
* "106 is the last term" is stated as: 106 is a term, and for every k > 106 the digit 4 occurs in the
  decimal digits of 3^k (`Nat.digits 10`).
* Controls (computed): among k < 3000 there are 17 terms, the largest being 106.
-/

namespace OMA.S_oeis_a131618



/-- The conjecture of the entry. -/
theorem main :
    (¬ 4 ∈ Nat.digits 10 (3 ^ 106)) ∧ ∀ k : ℕ, 106 < k → 4 ∈ Nat.digits 10 (3 ^ k) := by
  sorry

end OMA.S_oeis_a131618
