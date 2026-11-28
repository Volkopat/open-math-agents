import Mathlib

/-!
# Continuous sections of linear projections on compact sets

Source: gondolier, https://mathoverflow.net/questions/20466 (CC BY-SA).
The questioner's comment gives two disjoint compact segments with no
continuous section and suggests imposing convexity. Even compact convex sets
can fail for a planar projection, whereas projection to a line admits a
continuous section for every nonempty compact convex set.
Credit: @connoranderson.
-/
namespace OMA.S_mo_20466
open Set

def HasSection {E F : Type*} [TopologicalSpace E] [TopologicalSpace F] (S : Set E) (f : E → F) : Prop :=
  ∃ g : (f '' S) → E, Continuous g ∧ ∀ y, g y ∈ S ∧ f (g y) = (y:F)

theorem main :
    (∃ K : Set ((ℝ × ℝ) × ℝ), K.Nonempty ∧ IsCompact K ∧ Convex ℝ K ∧
      ¬ HasSection K Prod.fst) ∧
    (∀ n : ℕ, ∀ S : Set (Fin n → ℝ), S.Nonempty → IsCompact S → Convex ℝ S →
      ∀ f : (Fin n → ℝ) →L[ℝ] ℝ, HasSection S f) := by
  sorry
end OMA.S_mo_20466
