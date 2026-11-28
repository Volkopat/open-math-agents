import Mathlib

/-!
# Extension of Erdős-Gallai (s,t)-path theorem to directed graphs

Source: https://mathoverflow.net/questions/442518
Credit: @zarnab222-dev

Question: given a 2-strongly-connected directed unweighted graph with minimum in- and out-degree
at least `d`, is it the case that for every pair of vertices `s`, `t` there is an `(s,t)`-path of
length at least `d`? We state the affirmative claim, for every `d`; a disproof of `main` answers
the question negatively.

Translation choices:
* A directed graph is a finite Mathlib `Digraph V`: no parallel arcs, and we assume no loops.
  Opposite arcs `u → v`, `v → u` are allowed (the undirected Erdős-Gallai theorem is the case
  where every arc comes with its opposite).
* 2-strongly-connected is the standard notion of a 2-strong digraph (`k`-strong with `k = 2`):
  at least `k + 1` vertices, and deleting any set of fewer than `k` vertices leaves a strongly
  connected digraph (any two remaining vertices are joined by a directed walk through remaining
  vertices).
* Minimum in- and out-degree at least `d`: every vertex has at least `d` out-neighbours and at
  least `d` in-neighbours.
* A pair of vertices `s`, `t` means two distinct vertices; the path is directed from `s` to `t`.
* An `(s,t)`-path of length `ℓ` has `ℓ` arcs: an injective sequence `p 0, …, p ℓ` of vertices
  with `p 0 = s`, `p ℓ = t` and an arc from `p i` to `p (i + 1)` for every `i < ℓ`.
-/

namespace OMA.S_mo_442518

/-- The out-degree of `v`: the number of out-neighbours. -/
def outdegree {V : Type} [Fintype V] (G : Digraph V) [DecidableRel G.Adj] (v : V) : ℕ :=
  (Finset.univ.filter (fun w => G.Adj v w)).card

/-- The in-degree of `v`: the number of in-neighbours. -/
def indegree {V : Type} [Fintype V] (G : Digraph V) [DecidableRel G.Adj] (v : V) : ℕ :=
  (Finset.univ.filter (fun w => G.Adj w v)).card

/-- `G - S` is strongly connected: any two vertices outside `S` are joined by a directed walk
all of whose vertices lie outside `S`. -/
def IsStrongAfterDeleting {V : Type} (G : Digraph V) (S : Finset V) : Prop :=
  ∀ u v, u ∉ S → v ∉ S → Relation.ReflTransGen (fun a b => G.Adj a b ∧ a ∉ S ∧ b ∉ S) u v

/-- `G` is `k`-strong (`k`-strongly-connected): it has at least `k + 1` vertices and deleting any
set of fewer than `k` vertices leaves a strongly connected digraph. -/
def IsKStrong {V : Type} [Fintype V] (G : Digraph V) (k : ℕ) : Prop :=
  k + 1 ≤ Fintype.card V ∧ ∀ S : Finset V, S.card < k → IsStrongAfterDeleting G S

/-- `G` has a directed path from `s` to `t` of length (number of arcs) at least `d`. -/
def HasPathOfLengthAtLeast {V : Type} (G : Digraph V) (s t : V) (d : ℕ) : Prop :=
  ∃ ℓ : ℕ, d ≤ ℓ ∧ ∃ p : Fin (ℓ + 1) → V, Function.Injective p ∧ p 0 = s ∧ p (Fin.last ℓ) = t ∧
    ∀ i : Fin ℓ, G.Adj (p i.castSucc) (p i.succ)

/-- The directed analogue of the Erdős-Gallai `(s,t)`-path theorem asked about in the question. -/
theorem main : ∀ (V : Type) [Fintype V] (G : Digraph V) [DecidableRel G.Adj] (d : ℕ),
    (∀ v, ¬ G.Adj v v) → IsKStrong G 2 → (∀ v, d ≤ outdegree G v ∧ d ≤ indegree G v) →
    ∀ s t : V, s ≠ t → HasPathOfLengthAtLeast G s t d := by
  sorry

end OMA.S_mo_442518
