import Mathlib

/-!
# Outer reloid of restricted funcoid

Source: https://www.openproblemgarden.org/op/outer_reloid_of_restricted_funcoid
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Question (Porton): is
`(RLD)_out (f ⊓^FCD (𝒜 ×^FCD ℬ)) = ((RLD)_out f) ⊓^RLD (𝒜 ×^RLD ℬ)`
for all filters `𝒜`, `ℬ` and every funcoid `f`? The source asks a yes/no question; `main`
states the answer yes.

Conventions (Porton, *Algebraic General Topology*):
* A funcoid `f` from `A` to `B` is encoded by its relation `X [f] Y` on subsets (Porton's
  theorem identifies funcoids with such relations): it fails when `X` or `Y` is empty and it is
  binary-additive in each argument. Funcoids are ordered by inclusion of these relations; a union
  of funcoid relations is again one, so `f ⊓^FCD g` is the union of all funcoids below both.
* `X [𝒜 ×^FCD ℬ] Y ↔ 𝒜 ⊓ 𝓟 X ≠ ⊥ ∧ ℬ ⊓ 𝓟 Y ≠ ⊥`.
* A reloid from `A` to `B` is a filter on `A × B`; Porton's order `⊑` is Mathlib's `≤`, so
  `⊓^RLD` is `⊓` and `𝒜 ×^RLD ℬ` is `𝒜 ×ˢ ℬ`.
* `(RLD)_out f = ⋂^RLD up f`, where `up f` is the set of relations `K ⊆ A × B` with `f ⊑ K` as
  funcoids, i.e. `X [f] Y → (X × Y) ∩ K ≠ ∅`.
-/

namespace OMA.S_opg_outer_reloid_of_restricted_funcoid

/-- `δ` is (the relation of) a funcoid from `A` to `B`. -/
def IsFuncoid {A B : Type} (δ : Set A → Set B → Prop) : Prop :=
  (∀ Y, ¬ δ ∅ Y) ∧ (∀ X, ¬ δ X ∅) ∧
    (∀ X X' Y, δ (X ∪ X') Y ↔ δ X Y ∨ δ X' Y) ∧
    (∀ X Y Y', δ X (Y ∪ Y') ↔ δ X Y ∨ δ X Y')

/-- The meet `f ⊓^FCD g` of two funcoids. -/
def fcdMeet {A B : Type} (f g : Set A → Set B → Prop) : Set A → Set B → Prop :=
  fun X Y => ∃ h : Set A → Set B → Prop, IsFuncoid h ∧ (∀ X Y, h X Y → f X Y) ∧
    (∀ X Y, h X Y → g X Y) ∧ h X Y

/-- The funcoidal product `𝒜 ×^FCD ℬ` of filters. -/
def fcdProd {A B : Type} (𝒜 : Filter A) (ℬ : Filter B) : Set A → Set B → Prop :=
  fun X Y => 𝒜 ⊓ Filter.principal X ≠ ⊥ ∧ ℬ ⊓ Filter.principal Y ≠ ⊥

/-- `(RLD)_out f`. -/
def rldOut {A B : Type} (δ : Set A → Set B → Prop) : Filter (A × B) :=
  Filter.generate {K | ∀ X Y, δ X Y → (X ×ˢ Y ∩ K).Nonempty}

theorem main :
    ∀ (A B : Type) (f : Set A → Set B → Prop) (𝒜 : Filter A) (ℬ : Filter B),
      IsFuncoid f → rldOut (fcdMeet f (fcdProd 𝒜 ℬ)) = rldOut f ⊓ 𝒜 ×ˢ ℬ := by
  sorry

end OMA.S_opg_outer_reloid_of_restricted_funcoid
