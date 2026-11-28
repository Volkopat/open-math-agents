import Mathlib

/-!
# 4-flow conjecture

Source: https://www.openproblemgarden.org/op/4_flow_conjecture
Credit: @pyaf

Conjecture (Tutte): Every bridgeless graph with no Petersen minor has a nowhere-zero 4-flow.

Conventions (standard in flow theory, as in the merged 3- and 5-flow statements):
- A graph is a finite multigraph: loops and parallel edges are allowed. It is given by finite
  types `V` (vertices) and `E` (edges) with endpoint maps `tail head : E → V`, which also fix a
  reference orientation. Whether a nowhere-zero `k`-flow exists does not depend on that
  orientation: reversing an edge corresponds to negating its flow value.
- An edge `e` is a bridge if `tail e` and `head e` are not joined by a walk avoiding `e`.
  A loop is never a bridge. A graph is bridgeless if it has no bridge.
- A nowhere-zero `k`-flow is an integer edge labelling `f` with `0 < |f e| < k` for every edge
  and with flow conservation at every vertex: total inflow equals total outflow.
- The Petersen graph is the Kneser graph `K(5,2)`: vertices are the 2-element subsets of a
  5-element set, adjacent when disjoint.
- Since the Petersen graph is simple, `G` has a Petersen minor iff there are pairwise disjoint
  nonempty vertex sets `B p` (one per Petersen vertex `p`), each inducing a connected subgraph
  of `G`, with an edge of `G` between `B p` and `B q` whenever `p` and `q` are adjacent.
-/

namespace OMA.S_opg_4_flow_conjecture

/-- `u` and `w` are joined by an edge other than `e` (in either direction). -/
def AdjWithout {V E : Type} (tail head : E → V) (e : E) (u w : V) : Prop :=
  ∃ e' : E, e' ≠ e ∧ ((tail e' = u ∧ head e' = w) ∨ (tail e' = w ∧ head e' = u))

/-- The multigraph has no bridge: the endpoints of every edge stay connected without it. -/
def Bridgeless {V E : Type} (tail head : E → V) : Prop :=
  ∀ e : E, Relation.ReflTransGen (AdjWithout tail head e) (tail e) (head e)

/-- `f` is a nowhere-zero `k`-flow for the oriented multigraph `(tail, head)`. -/
def IsNowhereZeroFlow {V E : Type} [Fintype E] [DecidableEq V] (tail head : E → V)
    (k : ℕ) (f : E → ℤ) : Prop :=
  (∀ e, 0 < |f e| ∧ |f e| < k) ∧
  ∀ v : V, (∑ e ∈ Finset.univ.filter (fun e => head e = v), f e) =
    ∑ e ∈ Finset.univ.filter (fun e => tail e = v), f e

/-- The Petersen graph, as the Kneser graph `K(5,2)`. -/
def petersen : SimpleGraph {s : Finset (Fin 5) // s.card = 2} :=
  SimpleGraph.fromRel fun s t => Disjoint s.1 t.1

/-- Some edge of the multigraph has one endpoint in `A` and the other in `B`. -/
def EdgeBetween {V E : Type} (tail head : E → V) (A B : Set V) : Prop :=
  ∃ e : E, (tail e ∈ A ∧ head e ∈ B) ∨ (tail e ∈ B ∧ head e ∈ A)

/-- `B` induces a connected subgraph: any two of its vertices are joined by a walk inside `B`. -/
def InducesConnected {V E : Type} (tail head : E → V) (B : Set V) : Prop :=
  ∀ u ∈ B, ∀ w ∈ B,
    Relation.ReflTransGen (fun x y => x ∈ B ∧ y ∈ B ∧ EdgeBetween tail head {x} {y}) u w

/-- The multigraph has a minor isomorphic to the simple graph `H`, given by branch sets. -/
def HasMinor {V E P : Type} (tail head : E → V) (H : SimpleGraph P) : Prop :=
  ∃ B : P → Set V, (∀ p, (B p).Nonempty) ∧ (∀ p q, p ≠ q → Disjoint (B p) (B q)) ∧
    (∀ p, InducesConnected tail head (B p)) ∧
    ∀ p q, H.Adj p q → EdgeBetween tail head (B p) (B q)

theorem main :
    ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] (tail head : E → V),
      Bridgeless tail head → ¬ HasMinor tail head petersen →
        ∃ f : E → ℤ, IsNowhereZeroFlow tail head 4 f := by
  sorry

end OMA.S_opg_4_flow_conjecture
