import Mathlib

/-!
# Another conjecture about reloids and funcoids

Source: https://www.openproblemgarden.org/op/another_conjecture_about_reloids_and_funcoids
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Definition: `□ f = ⋂^RLD up^Γ(Src f; Dst f) f` for a reloid `f`.
Conjecture (Porton): `(RLD)_Γ f = □ (RLD)_in f` for every funcoid `f`.

Conventions (Porton, *Algebraic General Topology*):
* A reloid from `A` to `B` is a filter on `A × B` (Mathlib's order on filters agrees with
  Porton's). Meets of principal reloids are generated filters; joins are filter suprema.
* A funcoid from `A` to `B` is encoded by its relation `X [f] Y` on subsets (Porton's theorem
  identifies funcoids with such relations): it fails when `X` or `Y` is empty and it is
  binary-additive in each argument. A relation `K ⊆ A × B` is the principal funcoid with
  `X [K] Y ↔ (X × Y) ∩ K ≠ ∅`, and `f ⊑ g` is inclusion of relations.
* `Γ(A; B)` is the set of finite unions of Cartesian products `X × Y`. `up^Γ g` is the set of
  `Γ`-elements in the filter `g` (for a reloid), and the set of `Γ`-elements `K` with `f ⊑ K` (for a
  funcoid). `(RLD)_Γ f = ⋂^RLD up^Γ f`.
* `(RLD)_in f = ⨆ {a ×^RLD b | a, b ultrafilters, a ×^FCD b ⊑ f}`; for ultrafilters,
  `a ×^FCD b ⊑ f` means `X [f] Y` for all `X ∈ a`, `Y ∈ b`.
-/

namespace OMA.S_opg_another_conjecture_about_reloids_and_funcoids

variable {A B : Type*}

/-- `δ` is (the relation of) a funcoid from `A` to `B`. -/
def IsFuncoid (δ : Set A → Set B → Prop) : Prop :=
  (∀ Y, ¬ δ ∅ Y) ∧ (∀ X, ¬ δ X ∅) ∧
    (∀ X X' Y, δ (X ∪ X') Y ↔ δ X Y ∨ δ X' Y) ∧
    (∀ X Y Y', δ X (Y ∪ Y') ↔ δ X Y ∨ δ X Y')

/-- `K ∈ Γ(A; B)`: a finite union of Cartesian products. -/
def IsGamma (K : Set (A × B)) : Prop :=
  ∃ s : Finset (Set A × Set B), K = ⋃ p ∈ s, p.1 ×ˢ p.2

/-- `□ g` for a reloid `g`. -/
def box (g : Filter (A × B)) : Filter (A × B) :=
  Filter.generate {K | IsGamma K ∧ K ∈ g}

/-- `(RLD)_Γ f` for a funcoid `f`. -/
def rldGamma (δ : Set A → Set B → Prop) : Filter (A × B) :=
  Filter.generate {K | IsGamma K ∧ ∀ X Y, δ X Y → (X ×ˢ Y ∩ K).Nonempty}

/-- `(RLD)_in f` for a funcoid `f`. -/
def rldIn (δ : Set A → Set B → Prop) : Filter (A × B) :=
  ⨆ (a : Ultrafilter A) (b : Ultrafilter B) (_ : ∀ X ∈ a, ∀ Y ∈ b, δ X Y),
    (a : Filter A) ×ˢ (b : Filter B)

theorem main :
    ∀ (A B : Type) (δ : Set A → Set B → Prop), IsFuncoid δ → rldGamma δ = box (rldIn δ) := by
  sorry

end OMA.S_opg_another_conjecture_about_reloids_and_funcoids
