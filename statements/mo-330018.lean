import Mathlib

/-!
# MathOverflow 330018

Source: https://mathoverflow.net/questions/330018
-/

namespace OMA.S_mo_330018

open Set Metric

def isFortTopology {X : Type} [TopologicalSpace X] (b : X) : Prop :=
  ∀ U : Set X, IsOpen U ↔ b ∉ U ∨ Uᶜ.Finite

theorem main : ∀ (X : Type) [TopologicalSpace X] [Infinite X] (b : X), isFortTopology b →
      ∀ f : X → Icc (0 : ℝ) 1,
        Bornology.IsBounded (range fun x => (f x : ℝ)) ∧
        (Continuous f ↔ ∀ ε > (0 : ℝ), {x | ε ≤ dist (f x) (f b)}.Finite) := by
  sorry

end OMA.S_mo_330018
