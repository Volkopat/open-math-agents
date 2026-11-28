import Mathlib

/-!
# On invariants of Modular categories beyond modular data

Source: https://arxiv.org/abs/1805.05736
Credit: @ZenimXD

Bonderson, Delaney, Galindo, Rowell, Tran, and Wang (2018) study quantum link invariants of
modular tensor categories beyond the modular data `(S, T)`, focusing on the `W`-matrix — a
symmetrized version of the quantum invariant of the colored framed Whitehead link — and ask:

> Whether or not the triple `(S, T, W)` constitutes a complete invariant of modular categories
> remains an open question.

Conventions:
- A modular category over `ℂ` is a `ℂ`-linear, abelian, finite semisimple, rigid, braided,
  ribbon tensor category with simple tensor unit `𝟙_ C`, finite-dimensional Hom-spaces, and
  invertible un-normalized `S`-matrix `S̃_{ij} = tr(β_{X_j, X_i} ∘ β_{X_i, X_j})`.
- The ribbon twist `θ_X : X ≅ X` acts on each simple object `X_i` as a scalar `θ_i ∈ ℂ`
  (giving the diagonal `T`-matrix `T = diag(θ_i)`).
- Following Section 2.1 and Appendix B of arXiv:1805.05736, the Whitehead link is presented as
  the closure of the 3-strand braid `b₅ = σ₂⁻² σ₁ σ₂⁻¹ σ₁` on `X_i ⊗ (X_j ⊗ X_i)` (which
  represents the Whitehead link with an extra twist on the `X_i`-component), and the symmetric
  `W`-matrix is `W_{ij} = (θ_i / θ_j) * W̃_{ij}`.
- Equivalence of modular categories is `ℂ`-linear braided ribbon monoidal equivalence.
- The statement formalizes the positive direction of the open question: whether equality of
  `(S, T, W)` up to a bijection of simple objects implies braided ribbon equivalence.
-/

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.BraidedCategory
open CategoryTheory.Limits

namespace OMA.S_arxiv_1805_05736

/-- A ribbon structure on a braided rigid monoidal category: a natural automorphism `θ` (the twist)
compatible with the braiding and with duals. -/
class RibbonCategory (C : Type*) [Category C] [MonoidalCategory C] [BraidedCategory C]
    [RigidCategory C] where
  twist (X : C) : X ≅ X
  twist_natural : ∀ {X Y : C} (f : X ⟶ Y), (twist X).hom ≫ f = f ≫ (twist Y).hom
  twist_tensor : ∀ (X Y : C),
    (twist (X ⊗ Y)).hom =
      ((twist X).hom ⊗ₘ (twist Y).hom) ≫ (β_ X Y).hom ≫ (β_ Y X).hom
  twist_rightDual : ∀ (X : C),
    (twist (Xᘁ)).hom = rightAdjointMate (twist X).hom

/-- The categorical (ribbon) trace of an endomorphism `f : X ⟶ X` in a ribbon category,
valued in `End(𝟙_ C)`. -/
def ribbonEndTrace {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C]
    [RigidCategory C] [RibbonCategory C] {X : C} (f : X ⟶ X) : 𝟙_ C ⟶ 𝟙_ C :=
  ExactPairing.coevaluation X (Xᘁ) ≫
    ((f ≫ (RibbonCategory.twist X).hom) ▷ (Xᘁ)) ≫
    (β_ X (Xᘁ)).hom ≫
    ExactPairing.evaluation X (Xᘁ)

/-- The 3-strand Whitehead braid `b₅ = σ₂⁻² ∘ σ₁ ∘ σ₂⁻¹ ∘ σ₁` acting as an endomorphism of
`X ⊗ (Y ⊗ X)` in a braided monoidal category (Appendix B of arXiv:1805.05736). -/
def whiteheadBraid {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C]
    (X Y : C) : X ⊗ (Y ⊗ X) ⟶ X ⊗ (Y ⊗ X) :=
  -- σ₁ on (X ⊗ Y) ⊗ X → (Y ⊗ X) ⊗ X
  (α_ X Y X).inv ≫
  ((β_ X Y).hom ▷ X) ≫
  (α_ Y X X).hom ≫
  -- σ₂⁻¹ on Y ⊗ (X ⊗ X) → Y ⊗ (X ⊗ X)
  (Y ◁ (β_ X X).inv) ≫
  -- σ₁ on (Y ⊗ X) ⊗ X → (X ⊗ Y) ⊗ X
  (α_ Y X X).inv ≫
  ((β_ Y X).hom ▷ X) ≫
  (α_ X Y X).hom ≫
  -- σ₂⁻² on X ⊗ (Y ⊗ X) → X ⊗ (Y ⊗ X)
  (X ◁ (β_ X Y).inv) ≫
  (X ◁ (β_ Y X).inv)

/-- A modular (tensor) category over `ℂ` (as a small category). -/
structure ModularCategory where
  C : Type
  [cat : Category.{0} C]
  [preadd : Preadditive C]
  [lin : Linear ℂ C]
  [abelian : Abelian C]
  [hasFiniteBiproducts : HasFiniteBiproducts C]
  [monoidal : MonoidalCategory C]
  [monPreadd : MonoidalPreadditive C]
  [monLin : MonoidalLinear ℂ C]
  [braided : BraidedCategory C]
  [rigid : RigidCategory C]
  [ribbon : RibbonCategory C]
  /-- Hom-spaces are finite-dimensional over `ℂ`. -/
  hom_finDim : ∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)
  /-- The tensor unit is simple and `End(𝟙_ C) ≃ₗ[ℂ] ℂ` via `𝟙 (𝟙_ C) ↦ 1`. -/
  unitEndEquiv : (𝟙_ C ⟶ 𝟙_ C) ≃ₗ[ℂ] ℂ
  unitEndEquiv_id : unitEndEquiv (𝟙 (𝟙_ C)) = 1
  /-- Complete finite set of representatives of isomorphism classes of simple objects. -/
  rank : ℕ
  simpleObj : Fin rank → C
  simpleObj_simple : ∀ i, Simple (simpleObj i)
  simpleObj_inj : ∀ i j, Nonempty (simpleObj i ≅ simpleObj j) → i = j
  simpleObj_complete : ∀ X : C, Simple X → ∃ i, Nonempty (X ≅ simpleObj i)
  /-- Semisimplicity: every object is isomorphic to a finite biproduct of simple objects. -/
  semisimple : ∀ X : C, ∃ (k : ℕ) (idx : Fin k → Fin rank),
    Nonempty (X ≅ ⨁ fun m => simpleObj (idx m))
  /-- Each simple object has a scalar twist eigenvalue `θ_i ∈ ℂ`. -/
  twistVal : Fin rank → ℂ
  twist_simpleObj : ∀ i, (RibbonCategory.twist (simpleObj i)).hom = twistVal i • 𝟙 (simpleObj i)
  /-- Modularity: the un-normalized `S`-matrix `S̃_{ij} = tr(β_{X_j, X_i} ∘ β_{X_i, X_j})` is
  invertible. -/
  sMatrix_invertible :
    IsUnit (Matrix.of fun i j : Fin rank =>
      unitEndEquiv (ribbonEndTrace ((β_ (simpleObj i) (simpleObj j)).hom ≫
        (β_ (simpleObj j) (simpleObj i)).hom))).det

instance (B : ModularCategory) : Category.{0} B.C := B.cat
instance (B : ModularCategory) : Preadditive B.C := B.preadd
instance (B : ModularCategory) : Linear ℂ B.C := B.lin
instance (B : ModularCategory) : Abelian B.C := B.abelian
instance (B : ModularCategory) : MonoidalCategory B.C := B.monoidal
instance (B : ModularCategory) : MonoidalPreadditive B.C := B.monPreadd
instance (B : ModularCategory) : MonoidalLinear ℂ B.C := B.monLin
instance (B : ModularCategory) : BraidedCategory B.C := B.braided
instance (B : ModularCategory) : RigidCategory B.C := B.rigid
instance (B : ModularCategory) : RibbonCategory B.C := B.ribbon

/-- The un-normalized modular `S`-matrix of a modular category `B`. -/
def unnormS (B : ModularCategory) : Matrix (Fin B.rank) (Fin B.rank) ℂ :=
  Matrix.of fun i j =>
    B.unitEndEquiv (ribbonEndTrace ((β_ (B.simpleObj i) (B.simpleObj j)).hom ≫
      (β_ (B.simpleObj j) (B.simpleObj i)).hom))

/-- The modular `T`-matrix (diagonal matrix of twists) of a modular category `B`. -/
def TMatrix (B : ModularCategory) : Matrix (Fin B.rank) (Fin B.rank) ℂ :=
  Matrix.diagonal B.twistVal

/-- The symmetrized Whitehead link `W`-matrix of a modular category `B`
(Definition 2.1 and Appendix B of arXiv:1805.05736). -/
noncomputable def WMatrix (B : ModularCategory) : Matrix (Fin B.rank) (Fin B.rank) ℂ :=
  Matrix.of fun i j =>
    (B.twistVal i / B.twistVal j) *
      (B.twistVal i * B.unitEndEquiv (ribbonEndTrace (whiteheadBraid (B.simpleObj i) (B.simpleObj j))))

/-- A `ℂ`-linear braided ribbon monoidal equivalence between two modular categories. -/
structure ModularEquiv (B₁ B₂ : ModularCategory) where
  equiv : B₁.C ≌ B₂.C
  [braided : equiv.functor.Braided]
  [linear : equiv.functor.Linear ℂ]
  preserves_twist : ∀ X : B₁.C,
    equiv.functor.map (RibbonCategory.twist X).hom =
      (RibbonCategory.twist (equiv.functor.obj X)).hom

theorem main :
    ∀ (B₁ B₂ : ModularCategory),
      (∃ σ : Fin B₁.rank ≃ Fin B₂.rank,
        (∀ i j, unnormS B₂ (σ i) (σ j) = unnormS B₁ i j) ∧
        (∀ i, B₂.twistVal (σ i) = B₁.twistVal i) ∧
        (∀ i j, WMatrix B₂ (σ i) (σ j) = WMatrix B₁ i j)) →
      Nonempty (ModularEquiv B₁ B₂) := by
  sorry

end OMA.S_arxiv_1805_05736
