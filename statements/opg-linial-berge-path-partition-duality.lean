import Mathlib

/-!
# Linial-Berge path partition duality

Source: https://www.openproblemgarden.org/op/linial_berge_path_partition_duality
Credit: @Mapika

Conjecture (Berge; Linial): for a directed graph `D` and a positive integer `k`, the minimum
`k`-norm of a path partition of `D` is at most the maximum size of an induced `k`-colourable
subgraph of `D`. Here a path partition is a set of vertex-disjoint directed paths (single
vertices allowed) covering all vertices, and its `k`-norm is `∑_P min (|V(P)|, k)`.

## Encoding

* `D` is a Mathlib `Digraph` on a finite vertex type, without loops. Loops cannot lie on a
  path, and a looped vertex is in no independent set, so allowing them would make the
  statement false for trivial reasons (one looped vertex: minimum `k`-norm `1`, no nonempty
  induced `k`-colourable subgraph); directed graphs in this conjecture are loopless.
  Parallel arcs do not arise in `Digraph` and do not matter for paths or colourings.
* A directed path with `ℓ + 1 ≥ 1` vertices is an injective sequence `p 0, …, p ℓ` with an arc
  `p i → p (i + 1)` for every `i < ℓ`; `ℓ = 0` is a single-vertex path.
* A path partition is a finite family of `N` such paths in which every vertex occurs exactly
  once (as a pair: which path, which position). This gives vertex-disjointness and covering.
* The `k`-norm of the partition is `∑_j min (ℓ_j + 1, k)`.
* An induced subgraph on `S` is `k`-colourable if some `c : V → Fin k` gives different colours
  to the two ends of every arc with both ends in `S` (arcs in either direction).
* *Minimum `k`-norm ≤ maximum size*: both extrema are attained on a finite vertex set (the
  partition into single vertices exists, and `S = ∅` is `k`-colourable), so the inequality is
  equivalent to: some path partition and some induced `k`-colourable `S` satisfy
  `k`-norm `≤ |S|`. `main` states this form.
* `k ≥ 1` as in the source.
-/

namespace OMA.S_opg_linial_berge_path_partition_duality

/-- `p` is a directed path of `D` with `ℓ + 1` vertices `p 0, …, p ℓ`. -/
def IsDirectedPath {V : Type} (D : Digraph V) {ℓ : ℕ} (p : Fin (ℓ + 1) → V) : Prop :=
  Function.Injective p ∧ ∀ i : Fin ℓ, D.Adj (p i.castSucc) (p i.succ)

/-- `c` restricted to `S` is a proper colouring of the subgraph of `D` induced by `S`. -/
def IsProperOn {V : Type} (D : Digraph V) {k : ℕ} (S : Finset V) (c : V → Fin k) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, D.Adj u v → c u ≠ c v

/-- **Berge's path partition conjecture**: the minimum `k`-norm of a path partition is at most
the maximum size of an induced `k`-colourable subgraph. -/
theorem main : ∀ (V : Type) [Fintype V] (D : Digraph V), (∀ v, ¬ D.Adj v v) →
    ∀ k : ℕ, 1 ≤ k →
    ∃ (N : ℕ) (len : Fin N → ℕ) (p : ∀ j, Fin (len j + 1) → V),
      (∀ j, IsDirectedPath D (p j)) ∧
      (∀ v, ∃! x : (Σ j, Fin (len j + 1)), p x.1 x.2 = v) ∧
      ∃ (S : Finset V) (c : V → Fin k), IsProperOn D S c ∧
        ∑ j, min (len j + 1) k ≤ S.card := by
  sorry

end OMA.S_opg_linial_berge_path_partition_duality
