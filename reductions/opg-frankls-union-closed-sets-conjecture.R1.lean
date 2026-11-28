import OMAStatements.S_opg_frankls_union_closed_sets_conjecture
import Mathlib

-- Reduction opg-frankls-union-closed-sets-conjecture.R1 of Frankl's union-closed sets conjecture
-- Credit: @marcusbuffett

/-!
# Frankl's union-closed sets conjecture: families with a small member, and the open rest

The conjecture says that a finite union-closed family of finite sets, not all empty, has an
element lying in at least half of its members. This splits off the classical case of Sarvate and
Renaud (On the union-closed sets conjecture, Ars Combin. 27 (1989)): a family with a member of
size one or two. This is a classical partial result, not progress on the conjecture itself.

* `H1`: if the family has a member of size one or two, some element of that member lies in at
  least half of the members. For a singleton `{x}`, adding `x` maps the members without `x`
  injectively to the members with `x`; for a pair `{x, y}`, adding both maps the members with
  neither injectively to the members with both, and a counting argument finishes.
* `H2`: the families with no member of size one or two. This is the open conjecture.
-/

namespace OMA.R_opg_frankls_union_closed_sets_conjecture_R1

/-- A union-closed family with a member of size one or two has a frequent element. -/
def H1 : Prop :=
  ∀ (α : Type) [DecidableEq α] (F : Finset (Finset α)),
    (∀ A ∈ F, ∀ B ∈ F, A ∪ B ∈ F) → (∃ S ∈ F, S.card = 1 ∨ S.card = 2) →
      ∃ x : α, F.card ≤ 2 * (F.filter (fun A => x ∈ A)).card

/-- The open part: no member has one or two elements. -/
def H2 : Prop :=
  ∀ (α : Type) [DecidableEq α] (F : Finset (Finset α)),
    (∃ A ∈ F, A.Nonempty) → (∀ A ∈ F, ∀ B ∈ F, A ∪ B ∈ F) →
      (∀ S ∈ F, S.card ≠ 1 ∧ S.card ≠ 2) →
      ∃ x : α, F.card ≤ 2 * (F.filter (fun A => x ∈ A)).card

theorem main : H1 → H2 → type_of% @OMA.S_opg_frankls_union_closed_sets_conjecture.main := by
  intro h1 h2 α _ F hne huc
  by_cases hs : ∃ S ∈ F, S.card = 1 ∨ S.card = 2
  · exact h1 α F huc hs
  · push_neg at hs
    exact h2 α F hne huc hs

end OMA.R_opg_frankls_union_closed_sets_conjecture_R1
