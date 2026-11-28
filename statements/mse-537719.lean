import Mathlib

/-!
# Characterization of Henselian Local Rings via Finite Etale Algebras

Source: https://math.stackexchange.com/questions/537719/a-characterization-of-henselian-rings
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

## Problem Statement
If `(A, m)` is a Henselian local ring with residue field `κ = A / m`, then
base-change `B ↦ B ⊗_A κ` induces an equivalence of categories between finite
étale `A`-algebras and finite étale `κ`-algebras.

Question: Is there a local commutative ring `(A, m)` with residue field `κ` such
that base-change `B ↦ κ ⊗_A B` induces an equivalence of categories from finite
étale `A`-algebras to finite étale `κ`-algebras, yet `A` is not Henselian?

## Formalization Notes
We define `IsHenselianLocal A` directly via Hensel's lemma for simple roots of
monic polynomials over `A`. Base-change `B ↦ κ ⊗[A] B` being an equivalence of
categories is expressed by essential surjectivity (every finite étale `κ`-algebra
is isomorphic to `κ ⊗[A] B` for some finite étale `A`-algebra `B`) together with
full faithfulness (for any finite étale `A`-algebras `B, C`, base-change induces
a bijection `(B →ₐ[A] C) ≃ ((κ ⊗[A] B) →ₐ[κ] (κ ⊗[A] C))`).
-/

namespace OMA.S_mse_537719

open scoped TensorProduct

def IsHenselianLocal (A : Type) [CommRing A] [IsLocalRing A] : Prop :=
  ∀ (f : Polynomial A) (a₀ : A),
    f.Monic →
    IsLocalRing.residue A (f.eval a₀) = 0 →
    IsLocalRing.residue A (f.derivative.eval a₀) ≠ 0 →
    ∃ a : A, f.eval a = 0 ∧ IsLocalRing.residue A a = IsLocalRing.residue A a₀

def BaseChangeEquiv (A : Type) [CommRing A] [IsLocalRing A] : Prop :=
  let κ := IsLocalRing.ResidueField A
  (∀ (C : Type) [CommRing C] [Algebra κ C],
    Module.Finite κ C → Algebra.Etale κ C →
    ∃ (B : Type) (_ : CommRing B) (_ : Algebra A B),
      Module.Finite A B ∧ Algebra.Etale A B ∧
      Nonempty ((κ ⊗[A] B) ≃ₐ[κ] C)) ∧
  (∀ (B₁ B₂ : Type) [CommRing B₁] [CommRing B₂] [Algebra A B₁] [Algebra A B₂],
    Module.Finite A B₁ → Algebra.Etale A B₁ →
    Module.Finite A B₂ → Algebra.Etale A B₂ →
    Function.Bijective (fun (φ : B₁ →ₐ[A] B₂) =>
      Algebra.TensorProduct.map (AlgHom.id κ κ) φ))

theorem main :
    ∃ (A : Type) (_ : CommRing A) (_ : IsLocalRing A),
      BaseChangeEquiv A ∧ ¬ IsHenselianLocal A := by
  sorry

end OMA.S_mse_537719
