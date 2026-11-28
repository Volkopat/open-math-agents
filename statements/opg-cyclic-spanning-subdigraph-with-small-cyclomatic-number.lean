import Mathlib

/-!
# Cyclic spanning subdigraph with small cyclomatic number

Source: https://www.openproblemgarden.org/op/cyclic_spanning_subdigraph_with_small_cyclomatic_number
Credit: @sntntHb

Conjecture (J. A. Bondy, as stated in the source): let `D` be a digraph all of whose strong
components are nontrivial. Then `D` contains a cyclic spanning subdigraph with cyclomatic number at
most `α(D)`.

The source's definitions: `α(D)` is the stability number of `D` (the maximum number of pairwise
non-adjacent vertices); a digraph is cyclic when every arc lies on a directed cycle, so that a cyclic
spanning subdigraph is a disjoint union of strong digraphs; the cyclomatic number of a digraph
`(V, A)` is `|A| - |V| + 1`, which for a strong digraph is the number of ears of a directed ear
decomposition. Camion's theorem is the case `α(D) = 1` (a strong tournament has a Hamilton cycle).

## Encoding

* Digraphs are finite loopless `Digraph V` (`[Fintype V]`, no arc `v → v`).
* `u` and `v` are in the same strong component when each is reachable from the other by a directed
  walk (`Relation.ReflTransGen`). A strong component is nontrivial when it has at least two vertices.
* A spanning subdigraph `H` of `D` has the same vertex set and a subset of the arcs. It is cyclic:
  every arc `u → v` of `H` lies on a directed cycle (`u` is reachable from `v` in `H`), and, as a
  disjoint union of (nontrivial) strong digraphs spanning `V`, all strong components of `H` are
  nontrivial. (Without this the empty subdigraph would make the statement trivial.)
* The cyclomatic number of `H` is the sum over its strong components of `|A_i| - |V_i| + 1`,
  i.e. `|A(H)| - |V| + c(H)` with `c(H)` the number of strong components of `H` (for cyclic `H`
  these are also its connected components); for a strong `H` this is the source's `|A| - |V| + 1`.
  It is computed in `ℤ`.
* `α(D)` is the largest size of a set of vertices with no arc between any two of them.
-/

namespace OMA.S_opg_cyclic_spanning_subdigraph_with_small_cyclomatic_number

open Classical

variable {V : Type} [Fintype V]

/-- `u` and `v` lie in the same strong component of `D`. -/
def SameStrongComponent (D : Digraph V) (u v : V) : Prop :=
  Relation.ReflTransGen D.Adj u v ∧ Relation.ReflTransGen D.Adj v u

/-- Every strong component of `D` is nontrivial (has at least two vertices). -/
def AllStrongComponentsNontrivial (D : Digraph V) : Prop :=
  ∀ v : V, ∃ u : V, u ≠ v ∧ SameStrongComponent D v u

/-- `D` is cyclic: every arc lies on a directed cycle. -/
def IsCyclic (D : Digraph V) : Prop :=
  ∀ u v : V, D.Adj u v → Relation.ReflTransGen D.Adj v u

/-- The number of arcs of `D`. -/
noncomputable def numArcs (D : Digraph V) : ℕ :=
  (Finset.univ.filter fun p : V × V => D.Adj p.1 p.2).card

/-- The number of strong components of `D`. -/
noncomputable def numStrongComponents (D : Digraph V) : ℕ :=
  (Finset.univ.image fun v : V => Finset.univ.filter fun u : V => SameStrongComponent D v u).card

/-- The cyclomatic number `|A| - |V| + c` (sum of `|A_i| - |V_i| + 1` over strong components). -/
noncomputable def cyclomaticNumber (D : Digraph V) : ℤ :=
  (numArcs D : ℤ) - (Fintype.card V : ℤ) + (numStrongComponents D : ℤ)

/-- `S` is a stable set: no arc joins two of its vertices. -/
def IsStable (D : Digraph V) (S : Finset V) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, u ≠ v → ¬ D.Adj u v

/-- The stability number `α(D)`. -/
noncomputable def stabilityNumber (D : Digraph V) : ℕ :=
  sSup {k : ℕ | ∃ S : Finset V, S.card = k ∧ IsStable D S}

/-- **Bondy's conjecture.** A finite loopless digraph all of whose strong components are nontrivial
has a cyclic spanning subdigraph (with nontrivial strong components) of cyclomatic number at most
`α(D)`. -/
theorem main : ∀ (V : Type) [Fintype V] (D : Digraph V), (∀ v : V, ¬ D.Adj v v) →
    AllStrongComponentsNontrivial D →
    ∃ H : Digraph V, (∀ u v : V, H.Adj u v → D.Adj u v) ∧ IsCyclic H ∧
      AllStrongComponentsNontrivial H ∧ cyclomaticNumber H ≤ (stabilityNumber D : ℤ) := by
  sorry

end OMA.S_opg_cyclic_spanning_subdigraph_with_small_cyclomatic_number
