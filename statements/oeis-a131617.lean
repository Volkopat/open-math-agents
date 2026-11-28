import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Order.Bounds.Basic

/-!
# OEIS A131617

Shyam Sunder Gupta conjectures that 91 is the last exponent whose power of three
omits the decimal digit 5. The sequence lists these exponents in increasing order,
with its first term at index 1 and equal to 0.

Source: https://oeis.org/A131617
Credit: @pyaf
-/

namespace OMA.S_oeis_a131617

theorem main : IsGreatest {k : ℕ | 5 ∉ Nat.digits 10 (3 ^ k)} 91 := by
  sorry

end OMA.S_oeis_a131617
