import Mathlib

/-!
# Funcoidal products inside an inward reloid

Source: https://www.openproblemgarden.org/op/funcolidal_products_inside_an_inward_reloid
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (Porton, the stronger, open one on the page; the version for atomic `a`, `b` is
marked solved): if `𝒜 ×^RLD ℬ ⊑ (RLD)_in f` then `𝒜 ×^FCD ℬ ⊑ f`, for every funcoid `f` and
all filters `𝒜` on `Src f`, `ℬ` on `Dst f`.

Conventions (Porton, *Algebraic General Topology*), as in the statement
`opg-another-conjecture-about-reloids-and-funcoids` of this repository:
* A reloid from `A` to `B` is a filter on `A × B` (Mathlib's order on filters agrees with
  Porton's); `𝒜 ×^RLD ℬ` is the product filter `𝒜 ×ˢ ℬ`.
* A funcoid from `A` to `B` is encoded by its relation `X [f] Y` on subsets: it fails when `X`
  or `Y` is empty and it is binary-additive in each argument; `f ⊑ g` is inclusion of relations.
* `X [𝒜 ×^FCD ℬ] Y` iff `X` meets every member of `𝒜` and `Y` meets every member of `ℬ`
  (`𝒜 ⊓ 𝓟 X ≠ ⊥` and `ℬ ⊓ 𝓟 Y ≠ ⊥`).
* `(RLD)_in f = ⨆ {a ×^RLD b | a, b ultrafilters, a ×^FCD b ⊑ f}`.
-/

namespace OMA.S_opg_funcolidal_products_inside_an_inward_reloid

open Filter

variable {A B : Type*}

/-- `δ` is (the relation of) a funcoid from `A` to `B`. -/
def IsFuncoid (δ : Set A → Set B → Prop) : Prop :=
  (∀ Y, ¬ δ ∅ Y) ∧ (∀ X, ¬ δ X ∅) ∧
    (∀ X X' Y, δ (X ∪ X') Y ↔ δ X Y ∨ δ X' Y) ∧
    (∀ X Y Y', δ X (Y ∪ Y') ↔ δ X Y ∨ δ X Y')

/-- The funcoidal product `𝒜 ×^FCD ℬ`, as a relation on subsets. -/
def fcdProd (𝒜 : Filter A) (ℬ : Filter B) : Set A → Set B → Prop :=
  fun X Y => (𝒜 ⊓ 𝓟 X).NeBot ∧ (ℬ ⊓ 𝓟 Y).NeBot

/-- `(RLD)_in f` for a funcoid `f`. -/
def rldIn (δ : Set A → Set B → Prop) : Filter (A × B) :=
  ⨆ (a : Ultrafilter A) (b : Ultrafilter B) (_ : ∀ X Y, fcdProd (a : Filter A) (b : Filter B) X Y → δ X Y),
    (a : Filter A) ×ˢ (b : Filter B)

theorem main :
    ∀ (A B : Type) (δ : Set A → Set B → Prop), IsFuncoid δ →
      ∀ (𝒜 : Filter A) (ℬ : Filter B), 𝒜 ×ˢ ℬ ≤ rldIn δ →
        ∀ X Y, fcdProd 𝒜 ℬ X Y → δ X Y := by
  sorry

end OMA.S_opg_funcolidal_products_inside_an_inward_reloid
