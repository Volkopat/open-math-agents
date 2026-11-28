import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# Vertex coloring game

Source: https://en.wikipedia.org/wiki/graph_coloring_game
Credit: @SubhanAfz
-/

namespace OMA.S_wp_vertex_coloring_game

inductive Player where
  | alice
  | bob

/-- A player may color an uncolored vertex with a color absent from its neighbors. -/
def LegalMove {V : Type*} {k : ℕ} (G : SimpleGraph V) (colors : V → Option (Fin k))
    (v : V) (c : Fin k) : Prop :=
  colors v = none ∧ ∀ w, G.Adj v w → colors w ≠ some c

/-- Bob wins as soon as an uncolored vertex has no legal color. -/
def NoBlockedVertex {V : Type*} {k : ℕ} (G : SimpleGraph V)
    (colors : V → Option (Fin k)) : Prop :=
  ∀ v, colors v = none → ∃ c, LegalMove G colors v c

/-- Winning positions for Alice in the vertex coloring game. Alice needs one winning move
on her turn and must be able to respond to every legal move on Bob's turn. -/
inductive AliceWinsFrom {V : Type*} [DecidableEq V] (G : SimpleGraph V) (k : ℕ) :
    Player → (V → Option (Fin k)) → Prop where
  | complete (turn : Player) (colors : V → Option (Fin k))
      (full : ∀ v, ∃ c, colors v = some c) : AliceWinsFrom G k turn colors
  | alice (colors : V → Option (Fin k)) (ready : NoBlockedVertex G colors)
      (v : V) (c : Fin k) (legal : LegalMove G colors v c)
      (win : AliceWinsFrom G k .bob (Function.update colors v (some c))) :
      AliceWinsFrom G k .alice colors
  | bob (colors : V → Option (Fin k)) (ready : NoBlockedVertex G colors)
      (win : ∀ v c, LegalMove G colors v c →
        AliceWinsFrom G k .alice (Function.update colors v (some c))) :
      AliceWinsFrom G k .bob colors

/-- Does one extra color preserve a winning strategy when Alice starts on an uncolored graph? -/
theorem main :
    ∀ (V : Type*) [Finite V] [DecidableEq V] (G : SimpleGraph V) (k : ℕ),
      AliceWinsFrom G k .alice (fun _ ↦ none) →
      AliceWinsFrom G (k + 1) .alice (fun _ ↦ none) := by
  sorry

end OMA.S_wp_vertex_coloring_game
