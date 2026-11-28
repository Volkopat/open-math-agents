import FormalConjectures.ErdosProblems.«910»
import Mathlib

/-! Reduction Erdos910.erdos_910.parts.ii.R1. Erdos asked whether every connected set X in R^n of
dimension greater than one has more than continuum many connected subsets with more than one point.
H1 is the classical case of connected sets with an interior point, for n at least 2 (every
domain, every convex body): a small ball in X contains the combs made of a segment (the spine) and
one perpendicular segment (a tooth) at each point of an arbitrary set S of positions on the spine.
Each comb is connected, and S can be read off from the comb, so there are 2^c of them. H1 does not
need the dimension hypothesis. H2 is the open rest: connected sets of dimension greater than one
with empty interior (or n at most 1, where the dimension hypothesis cannot hold). -/

namespace OMA.R_Erdos910_erdos_910_parts_ii_R1

open scoped Cardinal

/-- Connected sets with an interior point in dimension at least 2. -/
def H1 : Prop :=
  ∀ (n : ℕ) (X : Set (EuclideanSpace ℝ (Fin n))), IsConnected X → 2 ≤ n →
    (interior X).Nonempty →
      𝔠 < Cardinal.mk {Y : Set (EuclideanSpace ℝ (Fin n)) |
        Y ⊆ X ∧ IsConnected Y ∧ Y.Nontrivial}

/-- The open core: connected sets of dimension greater than one without interior points. -/
def H2 : Prop :=
  ∀ (n : ℕ) (X : Set (EuclideanSpace ℝ (Fin n))), IsConnected X →
    1 < smallInductiveDimension X → ¬ (2 ≤ n ∧ (interior X).Nonempty) →
      𝔠 < Cardinal.mk {Y : Set (EuclideanSpace ℝ (Fin n)) |
        Y ⊆ X ∧ IsConnected Y ∧ Y.Nontrivial}

theorem main : H1 → H2 → type_of% @Erdos910.erdos_910.parts.ii := by
  intro h1 h2 n X hX hd
  by_cases hi : 2 ≤ n ∧ (interior X).Nonempty
  · exact h1 n X hX hi.1 hi.2
  · exact h2 n X hX hd hi

end OMA.R_Erdos910_erdos_910_parts_ii_R1
