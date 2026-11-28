import Mathlib

/-!
# MathOverflow 453358

Source: https://mathoverflow.net/questions/453358
-/

namespace OMA.S_mo_453358

open Set Metric
open scoped ENat BigOperators

def distSeparated {X : Type} [MetricSpace X] (δ : ℝ) (S : Set X) : Prop :=
  S.Pairwise (fun u v => δ ≤ dist u v)

def doublingByPacking (X : Type) [MetricSpace X] (N : ℕ) : Prop :=
  1 ≤ N ∧ ∀ x : X, ∀ r > 0, ∀ S : Set X, S ⊆ ball x r →
    distSeparated (r/2) S → S.encard ≤ N

def coversByHalfBalls (X : Type) [MetricSpace X] (M : ℕ) : Prop :=
  ∀ x : X, ∀ r > 0, ∃ C : Finset X, C.card ≤ M ∧ ball x r ⊆ ⋃ c ∈ C, ball c (r/2)

theorem main : ∀ (X : Type) [MetricSpace X],
      (∀ M : ℕ, 1 ≤ M → coversByHalfBalls X M → doublingByPacking X (M^2)) ∧
      (∀ (N : ℕ), doublingByPacking X N → ∀ k : ℕ, 1 ≤ k →
        ∀ x : X, ∀ r > 0, ∀ S : Set X, S ⊆ ball x r →
          distSeparated (r/(2:ℝ)^k) S → S.encard ≤ (N^k : ℕ)) := by
  sorry

end OMA.S_mo_453358
