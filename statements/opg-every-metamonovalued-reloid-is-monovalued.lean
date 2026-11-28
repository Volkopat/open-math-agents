import Mathlib

/-!
# Every metamonovalued reloid is monovalued

Source: https://www.openproblemgarden.org/op/every_metamonovalued_reloid_is_monovalued
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (Porton): every metamonovalued reloid is monovalued.

Definitions follow Porton, "Algebraic General Topology".
* A reloid from `A` to `B` is a filter on `A × B`; the order is the filter order (Mathlib's
  `≤`, under which `𝓟 X ≤ 𝓟 Y ↔ X ⊆ Y`, matching Porton's `⊑`).
* Composition: `g ∘ f = ⨅ {↑(G ∘ F) | F ∈ f, G ∈ g}` with `G ∘ F` relational composition.
* Inverse: image of the filter under `(a, b) ↦ (b, a)`. Identity `id_B`: principal filter of
  the diagonal.
* `f` is monovalued iff `f ∘ f⁻¹ ⊑ id_B`.
* `f : A → B` is metamonovalued iff `(⋀ G) ∘ f = ⋀_{g ∈ G} (g ∘ f)` for every set `G` of
  reloids from `B` (to any `C`).
-/

namespace OMA.S_opg_every_metamonovalued_reloid_is_monovalued

open Filter

/-- Relational composition: first `F`, then `G`. -/
def relComp {A B C : Type} (F : Set (A × B)) (G : Set (B × C)) : Set (A × C) :=
  {p | ∃ b, (p.1, b) ∈ F ∧ (b, p.2) ∈ G}

/-- Reloid composition `g ∘ f`. -/
def comp {A B C : Type} (g : Filter (B × C)) (f : Filter (A × B)) : Filter (A × C) :=
  ⨅ F ∈ f, ⨅ G ∈ g, 𝓟 (relComp F G)

/-- Reloid inverse. -/
def inv {A B : Type} (f : Filter (A × B)) : Filter (B × A) := f.map Prod.swap

/-- Identity reloid. -/
def idRLD (B : Type) : Filter (B × B) := 𝓟 {p | p.1 = p.2}

/-- Monovalued reloid. -/
def Monovalued {A B : Type} (f : Filter (A × B)) : Prop := comp f (inv f) ≤ idRLD B

/-- Metamonovalued reloid. -/
def Metamonovalued {A B : Type} (f : Filter (A × B)) : Prop :=
  ∀ (C : Type) (G : Set (Filter (B × C))), comp (sInf G) f = ⨅ g ∈ G, comp g f

/-- Porton's conjecture. -/
theorem main : ∀ (A B : Type) (f : Filter (A × B)), Metamonovalued f → Monovalued f := by
  sorry

end OMA.S_opg_every_metamonovalued_reloid_is_monovalued
