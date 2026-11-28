import Mathlib

/-!
# Infinite distributivity of meet over join for a principal funcoid

Source: https://www.openproblemgarden.org/op/infinite_distributivity_of_meet_over_join_for_a_principal_funcoid
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (Porton): `f ⊓ ⨆ S = ⨆ ⟨f ⊓⟩* S` for a principal funcoid `f` and a set `S` of
funcoids with the same source and destination.

Definitions (Porton, "Algebraic General Topology").
* A funcoid `A → B` is determined by its relation `[f]*` on sets; the relations that arise are
  exactly those with `¬ ∅ [f]* Y`, `¬ X [f]* ∅` and binary-union additivity in each argument,
  and we use that characterization as the definition.
* Order: `f ⊑ g` iff `[f]* ⊆ [g]*`. Funcoids form a complete lattice; the join of a set is
  given by the union of the relations (`X [⨆ S]* Y ↔ ∃ g ∈ S, X [g]* Y`), and the meet
  `f ⊓ g` is the join of all common lower bounds.
* The principal funcoid of a relation `R ⊆ A × B`: `X [R]* Y ↔ (X × Y) ∩ R ≠ ∅`.
* `⟨f ⊓⟩* S = {f ⊓ g | g ∈ S}`.
-/

namespace OMA.S_opg_infinite_distributivity_of_meet_over_join_for_a_principal_funcoid

/-- A funcoid from `A` to `B`, given by its relation on sets. -/

structure Funcoid (A B : Type) where
  rel : Set A → Set B → Prop
  empty_left : ∀ Y, ¬ rel ∅ Y
  empty_right : ∀ X, ¬ rel X ∅
  union_left : ∀ I J Y, rel (I ∪ J) Y ↔ rel I Y ∨ rel J Y
  union_right : ∀ X I J, rel X (I ∪ J) ↔ rel X I ∨ rel X J

variable {A B : Type}

/-- The order on funcoids. -/
def Funcoid.le (f g : Funcoid A B) : Prop := ∀ X Y, f.rel X Y → g.rel X Y

/-- Join of a set of funcoids. -/
def sup (S : Set (Funcoid A B)) : Funcoid A B where
  rel X Y := ∃ g ∈ S, g.rel X Y
  empty_left Y := fun ⟨g, _, h⟩ => g.empty_left Y h
  empty_right X := fun ⟨g, _, h⟩ => g.empty_right X h
  union_left I J Y := by
    constructor
    · rintro ⟨g, hg, h⟩
      rcases (g.union_left I J Y).1 h with h | h
      · exact Or.inl ⟨g, hg, h⟩
      · exact Or.inr ⟨g, hg, h⟩
    · rintro (⟨g, hg, h⟩ | ⟨g, hg, h⟩)
      · exact ⟨g, hg, (g.union_left I J Y).2 (Or.inl h)⟩
      · exact ⟨g, hg, (g.union_left I J Y).2 (Or.inr h)⟩
  union_right X I J := by
    constructor
    · rintro ⟨g, hg, h⟩
      rcases (g.union_right X I J).1 h with h | h
      · exact Or.inl ⟨g, hg, h⟩
      · exact Or.inr ⟨g, hg, h⟩
    · rintro (⟨g, hg, h⟩ | ⟨g, hg, h⟩)
      · exact ⟨g, hg, (g.union_right X I J).2 (Or.inl h)⟩
      · exact ⟨g, hg, (g.union_right X I J).2 (Or.inr h)⟩

/-- Binary meet: the join of all common lower bounds. -/
def meet (f g : Funcoid A B) : Funcoid A B := sup {h | h.le f ∧ h.le g}

/-- The principal funcoid of a relation. -/
def principal (R : Set (A × B)) : Funcoid A B where
  rel X Y := (X ×ˢ Y ∩ R).Nonempty
  empty_left Y := by simp
  empty_right X := by simp
  union_left I J Y := by
    rw [Set.union_prod, Set.union_inter_distrib_right, Set.union_nonempty]
  union_right X I J := by
    rw [Set.prod_union, Set.union_inter_distrib_right, Set.union_nonempty]

/-- Porton's conjecture. -/
theorem main :
    ∀ (A B : Type) (R : Set (A × B)) (S : Set (Funcoid A B)),
      meet (principal R) (sup S) = sup ((fun g => meet (principal R) g) '' S) := by
  sorry

end OMA.S_opg_infinite_distributivity_of_meet_over_join_for_a_principal_funcoid
