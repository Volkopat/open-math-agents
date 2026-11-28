import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Order.Bounds.Basic

/-!
# OEIS A131614

Shyam Sunder Gupta conjectures that 100 is the last exponent whose power of three
omits the decimal digit 8. The sequence lists these exponents in increasing order,
with its first term at index 1 and equal to 0.

Source: https://oeis.org/A131614
Credit: @pyaf
-/

namespace OMA.S_oeis_a131614

theorem main : IsGreatest {k : ℕ | 8 ∉ Nat.digits 10 (3 ^ k)} 100 := by
  sorry

end OMA.S_oeis_a131614
