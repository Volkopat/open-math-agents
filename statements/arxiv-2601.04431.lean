import Mathlib

/-! Alec Gow, “On the Quasitrace Problem and a Characterization of W*-algebras”,
arXiv:2601.04431v2, Conjecture 1.3. Credit: @my-other-github-account
-/
namespace OMA.S_arxiv_2601_04431

/-- Sakai's intrinsic characterization: the Banach space is a dual isometrically. -/
def HasPredual (A : Type) [NormedAddCommGroup A] [NormedSpace ℂ A] : Prop :=
  ∃ (E : Type) (_ : NormedAddCommGroup E) (_ : NormedSpace ℂ E) (_ : CompleteSpace E),
    Nonempty (A ≃ₗᵢ[ℂ] (E →L[ℂ] ℂ))

/-- Commutativity, and maximality under inclusion among abelian star subalgebras. -/
def IsMASA {A : Type} [CStarAlgebra A] (S : StarSubalgebra ℂ A) : Prop :=
  IsClosed (S : Set A) ∧ (∀ a b : S, a * b = b * a) ∧
    ∀ T : StarSubalgebra ℂ A, S ≤ T → (∀ a b : T, a * b = b * a) → T ≤ S

/-- The abstract, not fixed-representation, W*-Pedersen conjecture. -/
theorem main : ∀ (A : Type) [CStarAlgebra A], HasPredual A ↔
    ∀ S : StarSubalgebra ℂ A, IsMASA S → HasPredual S := by
  sorry

end OMA.S_arxiv_2601_04431
