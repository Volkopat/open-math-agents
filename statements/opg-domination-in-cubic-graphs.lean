import Mathlib

/-!
# Domination in cubic graphs

Source: https://www.openproblemgarden.org/op/domination_in_cubic_graphs
Credit: @ishaanzee

**Problem** (B. Reed). Does every 3-connected cubic graph `G` satisfy `γ(G) ≤ ⌈|G|/3⌉`?

Here `γ(G)` is the domination number: the least size of a set `D` of vertices such that every
vertex is in `D` or adjacent to a vertex of `D`. (Reed's original conjecture for all connected
cubic graphs was disproved by Kostochka and Stodolsky; the problem asks about 3-connected
cubic graphs.) We state the affirmative answer.

Formalization:
* Graphs are finite simple graphs; cubic means 3-regular (`IsRegularOfDegree 3`).
* `k`-connected (vertex connectivity): `G` has more than `k` vertices and deleting any set of
  fewer than `k` vertices leaves a connected graph (`G.induce` on the remaining vertices).
* `γ(G) ≤ ⌈|G|/3⌉` means some dominating set has at most `⌈|G|/3⌉ = (|G| + 2) / 3` vertices
  (natural-number division).
-/

namespace OMA.S_opg_domination_in_cubic_graphs

/-- `G` is `k`-connected: it has more than `k` vertices and stays connected after deleting any
fewer than `k` vertices. -/
def IsKConnected {V : Type*} [Fintype V] (G : SimpleGraph V) (k : ℕ) : Prop :=
  k < Fintype.card V ∧ ∀ S : Finset V, S.card < k → (G.induce (↑S : Set V)ᶜ).Connected

/-- `D` is a dominating set of `G`: every vertex is in `D` or adjacent to a vertex of `D`. -/
def IsDominating {V : Type*} (G : SimpleGraph V) (D : Finset V) : Prop :=
  ∀ v : V, v ∈ D ∨ ∃ u ∈ D, G.Adj v u

/-- **Reed's question**, affirmative form: every 3-connected cubic graph on `n` vertices has a
dominating set with at most `⌈n/3⌉` vertices. -/
theorem main : ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    G.IsRegularOfDegree 3 → IsKConnected G 3 →
      ∃ D : Finset V, IsDominating G D ∧ D.card ≤ (Fintype.card V + 2) / 3 := by
  sorry

end OMA.S_opg_domination_in_cubic_graphs
