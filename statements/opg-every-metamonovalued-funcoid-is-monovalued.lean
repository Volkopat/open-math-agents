import Mathlib

/-!
# Every metamonovalued funcoid is monovalued

Source: https://www.openproblemgarden.org/op/every_metamonovalued_funcoid_is_monovalued
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (Porton): every metamonovalued funcoid is monovalued.

Conventions (Porton, *Algebraic General Topology*, vol. 1):
* A funcoid `f` from `A` to `B` is encoded by its relation `X [f] Y` on subsets (Porton's theorem
  identifies funcoids with such relations): it fails when `X` or `Y` is empty and it is
  binary-additive in each argument. Funcoids are ordered by inclusion of relations; a union of
  funcoid relations is a funcoid relation, so the meet `⊓ G` of a set `G` of funcoids is the
  union of all funcoids below every member of `G`.
* `f⁻¹` swaps the arguments. Composition: `X [g ∘ f] Z ↔ ⟨f⟩ X ⊓ ⟨g⁻¹⟩ Z ≠ ⊥`, where
  `⟨f⟩ X = {Y | ¬ X [f] Yᶜ}` and `⟨g⁻¹⟩ Z = {Y | ¬ Yᶜ [g] Z}`; unfolded,
  `X [g ∘ f] Z ↔ ∀ Y, X [f] Yᶜ ∨ Y [g] Z`. The identity funcoid has `X [id] Y ↔ X ∩ Y ≠ ∅`.
* `f : A → B` is monovalued when `f ∘ f⁻¹ ⊑ id_B`; it is metamonovalued when
  `(⊓ G) ∘ f = ⊓ {g ∘ f | g ∈ G}` for every set `G` of funcoids from `B` to any `C`.
-/

namespace OMA.S_opg_every_metamonovalued_funcoid_is_monovalued

/-- `δ` is (the relation of) a funcoid from `A` to `B`. -/
def IsFuncoid {A B : Type} (δ : Set A → Set B → Prop) : Prop :=
  (∀ Y, ¬ δ ∅ Y) ∧ (∀ X, ¬ δ X ∅) ∧
    (∀ X X' Y, δ (X ∪ X') Y ↔ δ X Y ∨ δ X' Y) ∧
    (∀ X Y Y', δ X (Y ∪ Y') ↔ δ X Y ∨ δ X Y')

/-- The reverse funcoid `f⁻¹`. -/
def rev {A B : Type} (δ : Set A → Set B → Prop) : Set B → Set A → Prop := fun Y X => δ X Y

/-- Composition `g ∘ f` of funcoids `f : A → B` and `g : B → C`. -/
def comp {A B C : Type} (g : Set B → Set C → Prop) (f : Set A → Set B → Prop) :
    Set A → Set C → Prop :=
  fun X Z => ∀ Y : Set B, f X Yᶜ ∨ g Y Z

/-- The meet of a set of funcoids, in the lattice of funcoids. -/
def meet {A B : Type} (G : Set (Set A → Set B → Prop)) : Set A → Set B → Prop :=
  fun X Y => ∃ h : Set A → Set B → Prop, IsFuncoid h ∧
    (∀ g ∈ G, ∀ X Y, h X Y → g X Y) ∧ h X Y

/-- `f : A → B` is monovalued: `f ∘ f⁻¹ ⊑ id_B`. -/
def Monovalued {A B : Type} (f : Set A → Set B → Prop) : Prop :=
  ∀ Y Y' : Set B, comp f (rev f) Y Y' → (Y ∩ Y').Nonempty

/-- `f : A → B` is metamonovalued. -/
def Metamonovalued {A B : Type} (f : Set A → Set B → Prop) : Prop :=
  ∀ (C : Type) (G : Set (Set B → Set C → Prop)), (∀ g ∈ G, IsFuncoid g) →
    comp (meet G) f = meet {k | ∃ g ∈ G, k = comp g f}

theorem main :
    ∀ (A B : Type) (f : Set A → Set B → Prop),
      IsFuncoid f → Metamonovalued f → Monovalued f := by
  sorry

end OMA.S_opg_every_metamonovalued_funcoid_is_monovalued
