import Mathlib

/-!
# Counterexamples to Thomassen's conjecture on decomposition of cubic graphs

Source: https://arxiv.org/abs/1908.06697 (Bellitto, Klimošová, Merker, Witkowski, Yuditsky,
"Counterexamples to Thomassen's conjecture on decomposition of cubic graphs", 2019)
Credit: Sudharsan Rajendiran

Thomassen conjectured that the vertices of every 3-connected cubic graph on at least `8`
vertices can be coloured blue and red so that the blue subgraph has maximum degree at most `1`
and the red subgraph has minimum degree at least `1` and contains no path on `4` vertices. The
paper constructs an infinite family of counterexamples. We state this theorem: there are
counterexamples with arbitrarily many vertices.

Conventions:
- Graphs are `SimpleGraph V` on a finite vertex type; cubic means every vertex has degree `3`.
- `3`-connected: more than `3` vertices, and deleting any set of at most `2` vertices leaves a
  connected graph (the standard definition of `k`-vertex-connectivity).
- A colouring is `c : V → Bool` (`true` = blue, `false` = red). The blue (red) subgraph is the
  subgraph induced by the blue (red) vertices.
- Blue subgraph of maximum degree at most `1`: every blue vertex has at most one blue neighbour.
- Red subgraph of minimum degree at least `1`: every red vertex has a red neighbour.
- A path on `4` vertices in the red subgraph: four distinct red vertices `v₀, v₁, v₂, v₃` with
  `v₀ ~ v₁ ~ v₂ ~ v₃` (not necessarily induced).
-/

namespace OMA.S_arxiv_1908_06697

/-- `G` is `3`-vertex-connected. -/
def ThreeConnected {V : Type} [Fintype V] (G : SimpleGraph V) : Prop :=
  3 < Fintype.card V ∧
    ∀ S : Set V, S.ncard ≤ 2 → (G.induce Sᶜ).Connected

/-- The colouring `c` has the properties required by Thomassen's conjecture. -/
def GoodColouring {V : Type} (G : SimpleGraph V) (c : V → Bool) : Prop :=
  (∀ v, c v = true → {w | G.Adj v w ∧ c w = true}.ncard ≤ 1) ∧
  (∀ v, c v = false → ∃ w, G.Adj v w ∧ c w = false) ∧
  ¬ ∃ v : Fin 4 → V, Function.Injective v ∧ (∀ i, c (v i) = false) ∧
      G.Adj (v 0) (v 1) ∧ G.Adj (v 1) (v 2) ∧ G.Adj (v 2) (v 3)

/-- Thomassen's conjecture fails, for 3-connected cubic graphs with arbitrarily many vertices. -/
theorem main : ∀ N : ℕ, ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V)
    (_ : DecidableRel G.Adj), N ≤ Fintype.card V ∧ 8 ≤ Fintype.card V ∧
    G.IsRegularOfDegree 3 ∧ ThreeConnected G ∧ ∀ c : V → Bool, ¬ GoodColouring G c := by
  sorry

end OMA.S_arxiv_1908_06697
