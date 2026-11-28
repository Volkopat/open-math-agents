import Mathlib

/-!
# A funcoid related to directed topological spaces

Source: https://www.openproblemgarden.org/op/a_funcoid_related_to_directed_topological_spaces
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (Porton): let `R` be the complete funcoid of the usual topology on the extended real
line and `≥` its order. Then `R ⊓^FCD (≥)` is a complete funcoid.

Conventions (Porton, *Algebraic General Topology*):
* A funcoid from `A` to `B` is encoded by its relation `X [f] Y` on subsets (Porton's
  theorem identifies funcoids with such relations): `X [f] Y` fails when `X` or `Y` is empty,
  and it is binary-additive in each argument. Funcoids are ordered by inclusion of these
  relations. A union of funcoid relations is again one, so joins are unions and the meet
  `f ⊓^FCD g` is the union of all funcoids below both `f` and `g`.
* `f` is complete when `⟨f⟩` preserves arbitrary unions: `(⋃ S) [f] Y ↔ ∃ X ∈ S, X [f] Y`.
* The complete funcoid of a topology has `⟨R⟩{x} = 𝓝 x`, so `X [R] Y ↔ ∃ x ∈ X, x ∈ closure Y`.
* The relation `≥` is taken as the principal funcoid with `⟨≥⟩{x} = {y | y ≥ x}`, i.e.
  `X [≥] Y ↔ ∃ x ∈ X, ∃ y ∈ Y, x ≤ y`; this is the orientation for which the source's
  proposition holds (`⟨R ⊓ ≥⟩{x}` is the right-neighbourhood filter of `x`).
-/

namespace OMA.S_opg_a_funcoid_related_to_directed_topological_spaces

/-- `δ` is (the relation of) a funcoid from `A` to `B`. -/
def IsFuncoid {A B : Type*} (δ : Set A → Set B → Prop) : Prop :=
  (∀ Y, ¬ δ ∅ Y) ∧ (∀ X, ¬ δ X ∅) ∧
    (∀ X X' Y, δ (X ∪ X') Y ↔ δ X Y ∨ δ X' Y) ∧
    (∀ X Y Y', δ X (Y ∪ Y') ↔ δ X Y ∨ δ X Y')

/-- The meet of two funcoids in the lattice of funcoids. -/
def funcoidMeet {A B : Type*} (f g : Set A → Set B → Prop) : Set A → Set B → Prop :=
  fun X Y => ∃ h : Set A → Set B → Prop, IsFuncoid h ∧ (∀ X Y, h X Y → f X Y) ∧
    (∀ X Y, h X Y → g X Y) ∧ h X Y

/-- A complete funcoid. -/
def IsCompleteFuncoid {A B : Type*} (δ : Set A → Set B → Prop) : Prop :=
  IsFuncoid δ ∧ ∀ (S : Set (Set A)) (Y : Set B), δ (⋃₀ S) Y ↔ ∃ X ∈ S, δ X Y

/-- The complete funcoid of the topology of `[-∞, +∞]`. -/
def R : Set EReal → Set EReal → Prop := fun X Y => ∃ x ∈ X, x ∈ closure Y

/-- The order `≥` as a principal funcoid. -/
def ge : Set EReal → Set EReal → Prop := fun X Y => ∃ x ∈ X, ∃ y ∈ Y, x ≤ y

theorem main : IsCompleteFuncoid (funcoidMeet R ge) := by
  sorry

end OMA.S_opg_a_funcoid_related_to_directed_topological_spaces
