import Mathlib.Data.ZMod.Basic
import Mathlib.Order.Bounds.Defs

/-!
# A289740: 31 is the largest prime modulus with a missing sum of three sixth powers

Source: https://oeis.org/A289740 (Jon E. Schoenfield)
Credit: @Alienchisel

The sequence includes prime powers. The conjecture takes the greatest prime
among its terms. A residue is missing when it has no representation as a sum
of three sixth powers, with zero allowed as a summand.
-/

namespace OMA.S_oeis_a289740

/-- Some residue modulo the given modulus is absent from the three-term sums. -/
def HasMissingResidue (modulus : ℕ) : Prop :=
  ∃ r : ZMod modulus, ¬ ∃ a b c : ZMod modulus, a ^ 6 + b ^ 6 + c ^ 6 = r

theorem main : IsGreatest {p : ℕ | p.Prime ∧ HasMissingResidue p} 31 := by
  sorry

end OMA.S_oeis_a289740
