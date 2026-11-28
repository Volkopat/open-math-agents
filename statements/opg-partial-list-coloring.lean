import Mathlib

/-!
# Partial List Coloring

Source: http://www.openproblemgarden.org/op/partial_list_coloring
Credit: @shc261392

Conjecture (Albertson, Grossman and Haas): let `G` be a simple graph with `n` vertices and list
chromatic number `χ_ℓ(G)`. Suppose that `0 ≤ t ≤ χ_ℓ(G)` and each vertex of `G` is assigned a
list of `t` colors. Then at least `t n / χ_ℓ(G)` vertices of `G` can be colored from these lists.

Reading used here:
* `G` is a finite simple graph. Colors are natural numbers: for a finite graph any lists of
  colors can be relabelled injectively into `ℕ`, so nothing is lost.
* `listChromatic G` is the least `k` such that every assignment of lists of at least `k` colors
  admits a proper coloring choosing each vertex's color from its list (lists of exactly `k`
  colors give the same number).
* "At least `t n / χ_ℓ` vertices can be colored" means: there is a set `S` of vertices and a
  coloring of `S` from the lists that is proper on `S`, with `|S| ≥ t n / χ_ℓ`, written without
  division as `t * n ≤ |S| * χ_ℓ`.
-/

namespace OMA.S_opg_partial_list_coloring

/-- The list chromatic number (choice number) of `G`. -/
noncomputable def listChromatic {V : Type} (G : SimpleGraph V) : ℕ :=
  sInf {k : ℕ | ∀ L : V → Finset ℕ, (∀ v, k ≤ (L v).card) →
    ∃ c : V → ℕ, (∀ v, c v ∈ L v) ∧ ∀ u v, G.Adj u v → c u ≠ c v}

theorem main :
    ∀ (V : Type) [Fintype V] (G : SimpleGraph V) (t : ℕ), t ≤ listChromatic G →
      ∀ L : V → Finset ℕ, (∀ v, (L v).card = t) →
        ∃ (S : Finset V) (c : V → ℕ), (∀ v ∈ S, c v ∈ L v) ∧
          (∀ u ∈ S, ∀ v ∈ S, G.Adj u v → c u ≠ c v) ∧
          t * Fintype.card V ≤ S.card * listChromatic G := by
  sorry

end OMA.S_opg_partial_list_coloring
