import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Barker’s cyclotomic-coset formulas for multiplier 9

Source: https://oeis.org/A220020
Credit: @blakestone-x

Count multiplication orbits of all residues, including zero, modulo powers of ten.
The OEIS offset is one.
-/

namespace OMA.S_oeis_a220020

noncomputable def a (n : ℕ) : ℤ := Nat.cast
  (Nat.card (MulAction.orbitRel.Quotient
    (Subgroup.zpowers (ZMod.unitOfCoprime 9 ((by decide : Nat.Coprime 9 10).pow_right n)))
    (ZMod (10^n))))

noncomputable def series : PowerSeries ℤ :=
  PowerSeries.mk (fun n => if n = 0 then 0 else a n)

open PowerSeries

theorem main : 
    (∀ n : ℕ, 2 < n → a n = 4*(4*(n:ℤ)^2-7*n-1)) ∧
    (∀ n : ℕ, 5 < n → a n = 3*a (n-1)-3*a (n-2)+a (n-3)) ∧
    ((X-1)^3 : PowerSeries ℤ) * series = 2*X*(8*X^4-13*X^3-7*X^2-X-3) := by
  sorry

end OMA.S_oeis_a220020
