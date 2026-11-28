import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Order.Bounds.Basic

/-!
# OEIS A131613

Shyam Sunder Gupta conjectures that 56 is the last exponent whose power of three
omits the decimal digit 9. The sequence lists these exponents in increasing order,
with its first term at index 1 and equal to 0.

Source: https://oeis.org/A131613
Credit: @pyaf
-/

namespace OMA.S_oeis_a131613

theorem main : IsGreatest {k : ℕ | 9 ∉ Nat.digits 10 (3 ^ k)} 56 := by
  sorry

end OMA.S_oeis_a131613
