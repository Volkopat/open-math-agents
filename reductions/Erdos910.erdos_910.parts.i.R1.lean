import FormalConjectures.ErdosProblems.«910»
import Mathlib

/-! Reduction Erdos910.erdos_910.parts.i.R1. Erdos asked whether every connected set X in R^n with
more than one point contains a connected subset with more than one point that is not homeomorphic
to X. H1 is the classical case of connected sets that contain a nondegenerate line segment [a, b]
(every convex set, every open connected set, every polygonally connected set, every connected
subset of the line): if X is compact, the open segment (a, b) is connected and not compact; if X
is not compact, the closed segment [a, b] is connected and compact. Either way compactness tells
the two apart. H2 is the open rest: connected sets containing no nondegenerate segment, where
Rudin's set (under CH) lives. -/

namespace OMA.R_Erdos910_erdos_910_parts_i_R1

/-- Connected sets that contain a nondegenerate line segment. -/
def H1 : Prop :=
  ∀ (n : ℕ) (X : Set (EuclideanSpace ℝ (Fin n))), IsConnected X → X.Nontrivial →
    (∃ a b : EuclideanSpace ℝ (Fin n), a ≠ b ∧ segment ℝ a b ⊆ X) →
      ∃ Y ⊆ X, IsConnected Y ∧ Y.Nontrivial ∧ ¬ Nonempty (Y ≃ₜ X)

/-- The open core: connected sets that contain no nondegenerate line segment. -/
def H2 : Prop :=
  ∀ (n : ℕ) (X : Set (EuclideanSpace ℝ (Fin n))), IsConnected X → X.Nontrivial →
    ¬ (∃ a b : EuclideanSpace ℝ (Fin n), a ≠ b ∧ segment ℝ a b ⊆ X) →
      ∃ Y ⊆ X, IsConnected Y ∧ Y.Nontrivial ∧ ¬ Nonempty (Y ≃ₜ X)

theorem main : H1 → H2 → type_of% @Erdos910.erdos_910.parts.i := by
  intro h1 h2 n X hX hXn
  by_cases hs : ∃ a b : EuclideanSpace ℝ (Fin n), a ≠ b ∧ segment ℝ a b ⊆ X
  · exact h1 n X hX hXn hs
  · exact h2 n X hX hXn hs

end OMA.R_Erdos910_erdos_910_parts_i_R1
