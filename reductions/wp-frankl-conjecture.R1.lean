import OMAStatements.S_wp_frankl_conjecture
import Mathlib

/-!
Classical slice of Frankl's union-closed sets conjecture (Wikipedia formalization, arbitrary
subsets of a type).

H1 is the classical small-member case (Sarvate and Renaud, 1989, and the folklore singleton
case): if the family has a member `{x, y}` (a singleton when `x = y`), then `x` or `y` lies in at
least half of the members. Proof: `A ↦ A ∪ {x, y}` maps the members containing neither point
injectively to the members containing both, and inclusion-exclusion finishes. This is a known
case, not progress on the conjecture.

H2 is the open rest: union-closed families with a non-empty member and no member of size one or
two.
-/

namespace OMA.R_wp_frankl_conjecture_R1

open Classical in
/-- A union-closed family with a member of at most two points has a frequent element. -/
def H1 : Prop :=
  ∀ (α : Type) (F : Finset (Set α)),
    (∀ A ∈ F, ∀ B ∈ F, A ∪ B ∈ F) →
    (∃ S ∈ F, ∃ x y : α, S = {x, y}) →
    ∃ a : α, F.card ≤ 2 * (F.filter (fun A => a ∈ A)).card

open Classical in
/-- Open rest: no member is a singleton or a two-point set. -/
def H2 : Prop :=
  ∀ (α : Type) (F : Finset (Set α)),
    (∀ A ∈ F, ∀ B ∈ F, A ∪ B ∈ F) →
    (∃ A ∈ F, A.Nonempty) →
    (∀ S ∈ F, ∀ x y : α, S ≠ {x, y}) →
    ∃ a : α, F.card ≤ 2 * (F.filter (fun A => a ∈ A)).card

theorem main : H1 → H2 → type_of% @OMA.S_wp_frankl_conjecture.main := by
  intro h1 h2 α F huc hne
  by_cases hs : ∃ S ∈ F, ∃ x y : α, S = {x, y}
  · exact h1 α F huc hs
  · exact h2 α F huc hne (fun S hS x y hxy => hs ⟨S, hS, x, y, hxy⟩)

end OMA.R_wp_frankl_conjecture_R1
