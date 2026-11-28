import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Prime.Basic

/-! Source: https://mathoverflow.net/questions/432164 -/

open Polynomial

namespace OMA.S_mo_432164

def imageSet (P : ℤ[X]) (m : ℕ) [NeZero m] : Finset (ZMod m) :=
  Finset.univ.image (P.eval₂ (Int.castRingHom (ZMod m)))

def unitsInImage (P : ℤ[X]) (p n : ℕ) [NeZero (p ^ n)] : ℕ :=
  ((imageSet P (p ^ n)).filter fun y => y.val.Coprime p).card

/-- Bounds for image sizes under reduction and failure of unit-image divisibility in general. -/
theorem main :
    (∀ (P : ℤ[X]) (m p : ℕ) [NeZero m] [NeZero p],
      (imageSet P m).card ≤ (imageSet P (m * p)).card ∧
      (imageSet P (m * p)).card ≤ p * (imageSet P m).card) ∧
    (∃ (P : ℤ[X]) (p n : ℕ) (hp : p.Prime), 0 < n ∧
      letI : NeZero p := ⟨hp.ne_zero⟩
      ¬ unitsInImage P p n ∣ unitsInImage P p (n + 1)) := by
  sorry

end OMA.S_mo_432164
