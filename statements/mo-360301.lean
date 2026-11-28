import Mathlib

/-!
# Hausdorff metric selectors on bounded regular open subsets of the real line

Source: Wlod AA, https://mathoverflow.net/questions/360301 (CC BY-SA).
Credit: @connoranderson. Ethan Dlugie gave a direct obstruction for a
nonexpansive selector, and Ville Salo gave a topological obstruction. A
continuously moving gap rules out even a continuous selector when every set
is a union of at most two bounded open intervals.
-/
namespace OMA.S_mo_360301
open Set Metric
def Family (G : Set ℝ) : Prop :=
  G.Nonempty ∧ Bornology.IsBounded G ∧ IsOpen G ∧ interior (closure G) = G ∧
  ∃ a b c d : ℝ, G=Ioo a b ∪ Ioo c d

theorem main :
    ∀ s : Set ℝ → ℝ, (∀ G, Family G → s G∈G) →
      (∃ G, Family G ∧ ∃ ε : ℝ, 0<ε ∧ ∀ δ : ℝ, 0<δ →
        ∃ H, Family H ∧ hausdorffDist (closure G) (closure H)<δ ∧ ε≤dist (s G) (s H)) ∧
      (∀ C : ℝ, 0≤C → ∃ G H, Family G ∧ Family H ∧
        C*hausdorffDist (closure G) (closure H) < dist (s G) (s H)) := by
  sorry
end OMA.S_mo_360301
