import OMAReductions.R_mo_438166_R1
import Mathlib

/- Level-1 recursive split of H1 for mo-438166 (private helper for t_6f5bccc8).
Both leaves are stated over Mathlib only. Proofs of the leaves reuse the port of
OpenAI, openai/math at 3344da59 (Apache-2.0); MathOverflow question 438166 by
Finitistic dimension (CC BY-SA). -/
namespace OMA.R_mo_438166_R1_H1_R1
open CategoryTheory CategoryTheory.Limits

/-- Generic leaf: restriction along any complex algebra map has a left adjoint. -/
def H1 : Prop := ∀ (A D : Type) [Ring A] [Algebra ℂ A] [Ring D] [Algebra ℂ D] (e : A →ₐ[ℂ] D),
  (ModuleCat.restrictScalars.{0} e.toRingHom).IsRightAdjoint

/-- Existence leaf, uniform in the choice of left adjoint. -/
def H2 : Prop := ∃ (A : Type) (_ : Ring A) (_ : Algebra ℂ A) (D : Type) (_ : Ring D)
    (_ : Algebra ℂ D) (e : A →ₐ[ℂ] D) (g : ℕ),
    Module.Finite ℂ A ∧ Function.Surjective e ∧
    (∀ x y : A, e x = 0 → e y = 0 → x*y = 0) ∧
    (∀ V : ModuleCat.{0} D, HasProjectiveDimensionLE V g) ∧
    ∀ (F : ModuleCat.{0} A ⥤ ModuleCat.{0} D) [F.Additive],
      Nonempty (F ⊣ ModuleCat.restrictScalars e.toRingHom) →
    ∀ m : ℕ, ∃ N : ModuleCat.{0} A, Module.Finite A N ∧
      (∃ b : ℕ, ∀ n > b, IsZero ((F.leftDerived n).obj N)) ∧
      ∃ n ≥ m, ¬ IsZero ((F.leftDerived n).obj N)

/-- Kernel-checked reduction: the two leaves imply H1. -/
theorem main : H1 → H2 → OMA.R_mo_438166_R1.H1 := by
  rintro adj ⟨A, rA, aA, D, rD, aD, e, g, fin, surj, sq, gd, fam⟩
  let := rA; let := aA; let := rD; let := aD
  have := adj A D e
  let a := Adjunction.ofIsRightAdjoint (ModuleCat.restrictScalars.{0} e.toRingHom)
  have hF : (ModuleCat.restrictScalars.{0} e.toRingHom).leftAdjoint.Additive :=
    a.left_adjoint_additive
  exact ⟨A, rA, aA, D, rD, e.toRingHom, g, _, hF, fin, surj, sq, gd, ⟨a⟩, fam _ ⟨a⟩⟩
end OMA.R_mo_438166_R1_H1_R1
