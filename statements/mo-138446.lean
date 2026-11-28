import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Rat.Cast.Lemmas

/-!
# Square residues on Mordell curves

Source: https://mathoverflow.net/questions/138446
Credit: @etaubman

The source concerns rational points, as clarified in Noam D. Elkies's comment
357272. Reduction of a rational coordinate modulo k means numerator times the
inverse of its reduced denominator; that denominator must be coprime to k.
Using the natural absolute value gives the same residue ring for either sign
of the integer k. The original squarefree and modulo-24 hypotheses are kept.
-/

namespace OMA.S_mo_138446

theorem main : ∀ (k : ℤ) (x y : ℚ),
    Squarefree k.natAbs → Int.ModEq 24 (k ^ 2) 1 →
    y ^ 2 = x ^ 3 + (k : ℚ) → x.den.Coprime k.natAbs →
    IsSquare ((x.num : ZMod k.natAbs) * (x.den : ZMod k.natAbs)⁻¹) := by
  sorry

end OMA.S_mo_138446
