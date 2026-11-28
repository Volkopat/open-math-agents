import Mathlib

/-!
# GCH below a strongly compact cardinal (Woodin)

Source: https://en.wikipedia.org/wiki/W._Hugh_Woodin
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Question (Woodin): does the generalized continuum hypothesis below a strongly compact cardinal
imply the generalized continuum hypothesis everywhere?

Conventions:
* `κ` is strongly compact if it is uncountable and every `κ`-complete filter (closed under
  intersections of fewer than `κ` members) on any set extends to a `κ`-complete ultrafilter.
  "Any set" ranges over the types of the universe in which `κ` lives.
* GCH below `κ`: `2^λ = λ⁺` for every infinite cardinal `λ < κ`; GCH everywhere: for every
  infinite cardinal `λ` (of the same universe).
* The source asks a yes/no question; `main` states the answer yes, and a disproof would answer
  no.
-/

namespace OMA.S_wp_woodin

universe u

/-- A filter `F` on `α` is `κ`-complete. -/
def KComplete {α : Type u} (κ : Cardinal.{u}) (F : Filter α) : Prop :=
  ∀ S : Set (Set α), Cardinal.mk S < κ → S ⊆ F.sets → ⋂₀ S ∈ F

/-- `κ` is a strongly compact cardinal. -/
def StronglyCompact (κ : Cardinal.{u}) : Prop :=
  Cardinal.aleph0 < κ ∧
    ∀ (α : Type u) (F : Filter α), KComplete κ F →
      ∃ U : Ultrafilter α, (U : Filter α) ≤ F ∧ KComplete κ (U : Filter α)

theorem main :
    ∀ κ : Cardinal.{u}, StronglyCompact κ →
      (∀ μ : Cardinal.{u}, Cardinal.aleph0 ≤ μ → μ < κ → 2 ^ μ = Order.succ μ) →
      ∀ μ : Cardinal.{u}, Cardinal.aleph0 ≤ μ → 2 ^ μ = Order.succ μ := by
  sorry

end OMA.S_wp_woodin
