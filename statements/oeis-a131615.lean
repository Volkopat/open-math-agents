import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Order.Bounds.Basic

/-!
# OEIS A131615

Shyam Sunder Gupta conjectures that 101 is the last exponent whose power of three
omits the decimal digit 7. The sequence lists these exponents in increasing order,
with its first term at index 1 and equal to 0.

Source: https://oeis.org/A131615
Credit: @pyaf
-/

namespace OMA.S_oeis_a131615

theorem main : IsGreatest {k : ℕ | 7 ∉ Nat.digits 10 (3 ^ k)} 101 := by
  sorry

end OMA.S_oeis_a131615
