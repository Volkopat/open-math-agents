import Mathlib

/-!
# Generalized path-connectedness in proximity spaces

Source: https://www.openproblemgarden.org/op/generalized_path_connectedness_in_proximity_spaces
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (Porton): for every endofuncoid `μ` and set `U`, the following are equivalent:
1. `U` is connected regarding `μ`;
2. for all `a, b ∈ U` there is a totally ordered set `P ⊆ U` with `min P = a`, `max P = b`,
   such that for every partition `{X, Y}` of `P` with `x < y` for all `x ∈ X`, `y ∈ Y`,
   we have `X [μ]* Y`.

Definitions (Porton, "Algebraic General Topology").
* A funcoid `A → B` is determined by its relation `[f]*` on sets, and the relations that arise
  are exactly those with `¬ ∅ [f]* Y`, `¬ X [f]* ∅`, and binary-union additivity in each
  argument; we use that characterization as the definition. An endofuncoid is `A → A`.
* `U` is connected regarding `μ` iff for all nonempty `X, Y` with `X ∪ Y = U`, `X ∩ Y = ∅`:
  `X [μ ⊔ μ⁻¹]* Y`, i.e. `X [μ]* Y ∨ Y [μ]* X`.
* "Totally ordered set `P ⊆ U`": a subset with some linear order (not inherited); a partition
  of `P` has two nonempty blocks; the order on `P` is given as a strict linear order `lt`.
-/

namespace OMA.S_opg_generalized_path_connectedness_in_proximity_spaces

/-- A funcoid from `A` to `B`, given by its relation on sets. -/
structure Funcoid (A B : Type) where
  rel : Set A → Set B → Prop
  empty_left : ∀ Y, ¬ rel ∅ Y
  empty_right : ∀ X, ¬ rel X ∅
  union_left : ∀ I J Y, rel (I ∪ J) Y ↔ rel I Y ∨ rel J Y
  union_right : ∀ X I J, rel X (I ∪ J) ↔ rel X I ∨ rel X J

/-- `U` is connected regarding `μ`. -/
def ConnectedRegarding {A : Type} (μ : Funcoid A A) (U : Set A) : Prop :=
  ∀ X Y : Set A, X.Nonempty → Y.Nonempty → X ∪ Y = U → X ∩ Y = ∅ →
    μ.rel X Y ∨ μ.rel Y X

/-- Condition 2 of the conjecture. -/
def OrderedPathCondition {A : Type} (μ : Funcoid A A) (U : Set A) : Prop :=
  ∀ a ∈ U, ∀ b ∈ U, ∃ (P : Set A) (lt : A → A → Prop),
    P ⊆ U ∧ IsStrictTotalOrder P (fun x y : P => lt x y) ∧
    a ∈ P ∧ b ∈ P ∧ (∀ x ∈ P, x ≠ a → lt a x) ∧ (∀ x ∈ P, x ≠ b → lt x b) ∧
    ∀ X Y : Set A, X.Nonempty → Y.Nonempty → X ∪ Y = P → X ∩ Y = ∅ →
      (∀ x ∈ X, ∀ y ∈ Y, lt x y) → μ.rel X Y

/-- Porton's conjecture. -/
theorem main :
    ∀ (A : Type) (μ : Funcoid A A) (U : Set A),
      ConnectedRegarding μ U ↔ OrderedPathCondition μ U := by
  sorry

end OMA.S_opg_generalized_path_connectedness_in_proximity_spaces
