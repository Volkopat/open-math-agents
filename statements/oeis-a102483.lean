import Mathlib

/-!
# A102483: Numbers k such that 2^k contains no zeros in base 3.

Source: https://oeis.org/A102483
Credit: @azmiozgen

Conjecture (from the entry, posed in 1973; still open): there are no further terms beyond 0, 1, 2, 3, 4, 15.

Formalization notes:
* Stated as equality of the set of terms with {0, 1, 2, 3, 4, 15}; base-3 digits are `Nat.digits 3`.
* Controls (computed): the k < 4000 with no digit 0 in base 3 are exactly 0, 1, 2, 3, 4, 15.
-/

namespace OMA.S_oeis_a102483



/-- The conjecture of the entry. -/
theorem main :
    {k : ℕ | 0 ∉ Nat.digits 3 (2 ^ k)} = ({0, 1, 2, 3, 4, 15} : Set ℕ) := by
  sorry

end OMA.S_oeis_a102483
