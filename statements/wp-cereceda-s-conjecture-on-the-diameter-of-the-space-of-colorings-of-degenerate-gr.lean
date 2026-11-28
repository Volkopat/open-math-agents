import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Set.Card

/-!
# Cereceda's conjecture

Source: https://en.wikipedia.org/wiki/Cereceda's_conjecture
Credit: @SubhanAfz

The quadratic constant may depend on the degeneracy bound `d`, as in the
conjecture stated by Bousquet and Heinrich in https://arxiv.org/abs/1903.05619.
-/

namespace OMA.S_wp_cereceda_s_conjecture_on_the_diameter_of_the_space_of_colorings_of_degenerate_gr

/-- Every nonempty induced subgraph has a vertex of degree at most `d`. -/
def IsDegenerate {V : Type*} (G : SimpleGraph V) (d : ℕ) : Prop :=
  ∀ S : Finset V, S.Nonempty → ∃ v ∈ S, ((S : Set V) ∩ G.neighborSet v).ncard ≤ d

/-- Adjacent proper colorings differ at exactly one vertex. -/
def recoloringGraph {V : Type*} (G : SimpleGraph V) (k : ℕ) :
    SimpleGraph (G.Coloring (Fin k)) :=
  SimpleGraph.fromRel fun a b ↦ ∃ v : V, a v ≠ b v ∧ ∀ w ≠ v, a w = b w

/-- The extended distance counts single-vertex recolorings and is infinite if no walk exists. -/
theorem main :
    ∀ d : ℕ, ∃ C : ℕ, 0 < C ∧
      ∀ (V : Type*) [Fintype V] (G : SimpleGraph V), IsDegenerate G d →
        ∀ a b : G.Coloring (Fin (d + 2)),
          (recoloringGraph G (d + 2)).edist a b ≤ (C * (Fintype.card V) ^ 2 : ℕ) := by
  sorry

end OMA.S_wp_cereceda_s_conjecture_on_the_diameter_of_the_space_of_colorings_of_degenerate_gr
