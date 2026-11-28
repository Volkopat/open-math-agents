import Mathlib

/-!
# Exact sublevel-set inclusion from a distance-function approximation

Source: AB_IM, https://mathoverflow.net/questions/426045 (CC BY-SA).
Credit: @connoranderson. The question gives an open distance tube as a
sufficient condition. Its inclusion is also necessary for uniform guarantees,
even if approximants are nonnegative 1-Lipschitz functions vanishing on K.
-/
namespace OMA.S_mo_426045
open Metric Set

def UniformError {X : Type*} [MetricSpace X] (K : Set X) (ε : ℝ) (f : X → ℝ) : Prop :=
  ∃ δ : ℝ, δ<ε ∧ ∀ x, |f x-infDist x K| ≤ δ

def Safe {X : Type*} [MetricSpace X] (K Y : Set X) (s ε : ℝ) : Prop :=
  ∀ f : X → ℝ, LowerSemicontinuous f → (∀ x,0 ≤ f x) → UniformError K ε f →
    {x | f x ≤ s}.Nonempty → {x | f x ≤ s} ⊆ Y

theorem main : ∀ (X : Type) [MetricSpace X] (K : Set X) (s ε : ℝ), 0 ≤ s → 0<ε →
    (∀ x : X, infDist x K < s+ε ↔ ∃ f : X → ℝ,
      LipschitzWith 1 f ∧ (∀ y,0 ≤ f y) ∧ (∀ y∈K,f y=0) ∧ UniformError K ε f ∧ f x ≤ s) ∧
    (∀ Y : Set X, Safe K Y s ε ↔ {x | infDist x K < s+ε} ⊆ Y) ∧
    (∀ Y : Set X, let r := sSup ((fun y => infDist y K) '' Y)
      0<r → (Safe K Y (r/2) (r/2) ↔ {x | infDist x K < r} ⊆ Y)) := by
  sorry
end OMA.S_mo_426045
