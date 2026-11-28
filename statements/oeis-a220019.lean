import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic

/-!
# Barker’s cyclotomic-coset formulas for multiplier 7

Source: https://oeis.org/A220019
Credit: @blakestone-x

Count multiplication orbits of all residues, including zero, modulo powers of ten.
The OEIS offset is one.
-/

namespace OMA.S_oeis_a220019

noncomputable def a (n : ℕ) : ℤ := Nat.cast
  (Nat.card (MulAction.orbitRel.Quotient
    (Subgroup.zpowers (ZMod.unitOfCoprime 7 ((by decide : Nat.Coprime 7 10).pow_right n)))
    (ZMod (10^n))))

theorem main : 
    (∀ n : ℕ, 3 < n → a n = 5*(16*(n:ℤ)^2-60*n+37)) ∧
    (∀ n : ℕ, 6 < n → a n = 3*a (n-1)-3*a (n-2)+a (n-3)) := by
  sorry

end OMA.S_oeis_a220019
