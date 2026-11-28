import Mathlib.Data.ZMod.Basic
import Mathlib.Order.Bounds.Defs

/-!
# A289760: 13 is the largest prime modulus with a missing sum of four sixth powers

Source: https://oeis.org/A289760 (Jon E. Schoenfield)
Credit: @Alienchisel

The sequence includes prime powers. The conjecture takes the greatest prime
among its terms. A missing residue is a class modulo the given modulus that
cannot be written as a sum of four sixth powers.
-/

namespace OMA.S_oeis_a289760

/-- Some residue modulo the given modulus is absent from the four-term sums. -/
def HasMissingResidue (modulus : ℕ) : Prop :=
  ∃ r : ZMod modulus, ¬ ∃ a b c d : ZMod modulus, a ^ 6 + b ^ 6 + c ^ 6 + d ^ 6 = r

theorem main : IsGreatest {p : ℕ | p.Prime ∧ HasMissingResidue p} 13 := by
  sorry

end OMA.S_oeis_a289760
