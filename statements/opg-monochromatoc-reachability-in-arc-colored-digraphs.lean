import Mathlib

/-!
# Monochromatic reachability in arc-colored digraphs

Source: https://www.openproblemgarden.org/op/monochromatoc_reachability_in_arc_colored_digraphs
Credit: @Mapika

Conjecture (Sands, Sauer, Woodrow). For every `k`, there exists an integer `f(k)` such that if
`D` is a digraph whose arcs are colored with `k` colors, then `D` has a set `S` which is the
union of `f(k)` stable sets so that every vertex has a monochromatic path to some vertex in `S`.

The source records that the case of tournaments, and more generally of digraphs of bounded
stability number, was proved by Bousquet, Lochet and Thomassé (arXiv:1703.08123). The related
problem "Monochromatic reachability vs rainbow triangles" is
`OMA.S_opg_monochromatic_reachability_vs_rainbow_triangles.main`; we use the same encoding.
No statement of this problem was found in formal-conjectures.

## Encoding

* Digraphs are finite: the vertex type `V` is a `Fintype` (for infinite digraphs the statement
  is false already for `k = 1`, e.g. the transitive tournament on `ℕ` with arcs `i → j` for
  `i < j`, so the finite reading is the intended one). The digraph is a Mathlib `Digraph`: at
  most one arc `u → v` for each ordered pair, opposite arcs `u → v`, `v → u` allowed.
* Mathlib's `Digraph` may have loops. A loop neither helps reach another vertex nor is an arc
  between two vertices of a set, so loops are ignored: a set is stable if no arc joins two
  distinct members of it. This makes the statement the same as for loopless digraphs.
* A coloring of the arcs with `k` colors is `col : V → V → Fin k`; only its values on arcs
  matter.
* `S` is the union of a family `I : Fin n → Set V` of `n = f(k)` stable sets (empty members
  allowed, so "at most `f(k)`" and "exactly `f(k)`" agree).
* "`v` has a monochromatic path to some vertex in `S`": either `v ∈ S` (the path of length
  zero) or for some color `c` there is a directed walk from `v` to a vertex of `S` using only
  arcs of color `c` (`Relation.TransGen`); a shortest such walk is a path.
* "For every `k` there exists `f(k)`" is stated as `∀ k, ∃ n`, with `n` independent of the
  digraph.
-/

namespace OMA.S_opg_monochromatoc_reachability_in_arc_colored_digraphs

/-- `I` is a stable (independent) set of the digraph `G`: no arc joins two distinct vertices
of `I`. -/
def IsStable {V : Type} (G : Digraph V) (I : Set V) : Prop :=
  ∀ u ∈ I, ∀ v ∈ I, u ≠ v → ¬ G.Adj u v

/-- **Sands–Sauer–Woodrow conjecture** on monochromatic reachability in arc-colored digraphs. -/
theorem main : ∀ k : ℕ, ∃ n : ℕ, ∀ (V : Type) [Fintype V] (G : Digraph V) (col : V → V → Fin k),
    ∃ I : Fin n → Set V, (∀ i, IsStable G (I i)) ∧
      ∀ v : V, v ∈ (⋃ i, I i) ∨
        ∃ s ∈ (⋃ i, I i), ∃ c : Fin k,
          Relation.TransGen (fun x y => G.Adj x y ∧ col x y = c) v s := by
  sorry

end OMA.S_opg_monochromatoc_reachability_in_arc_colored_digraphs
