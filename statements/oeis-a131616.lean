import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Order.Bounds.Basic

/-!
# OEIS A131616

Shyam Sunder Gupta conjectures that 104 is the last exponent whose power of three
omits the decimal digit 6. The sequence lists these exponents in increasing order,
with its first term at index 1 and equal to 0.

Source: https://oeis.org/A131616
Credit: @pyaf
-/

namespace OMA.S_oeis_a131616

theorem main : IsGreatest {k : ℕ | 6 ∉ Nat.digits 10 (3 ^ k)} 104 := by
  sorry

end OMA.S_oeis_a131616
