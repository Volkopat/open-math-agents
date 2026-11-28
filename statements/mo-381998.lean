import Mathlib

/-!
# Increasing the Hadwiger number by making any pair of non-adjacent points adjacent

Source: https://mathoverflow.net/questions/381998
Credit: @koolkao

Question (Dominic van der Zypen, MathOverflow 381998, 2021; CC BY-SA 4.0). Let `G = (V, E)` be a
finite, simple, undirected graph. The Hadwiger number `η(G)` is the largest positive integer `n`
such that the complete graph `K_n` is a minor of `G`. A graph is vertex-critical if removing any
vertex reduces the chromatic number. What is an example of a connected, non-complete
vertex-critical graph `G = (V, E)` such that adding any edge increases the Hadwiger number, that
is, for `v ≠ w ∈ V` with `{v, w} ∉ E`, `η((V, E ∪ {{v, w}})) > η((V, E))`?

The question asks for an example, so `main` states that one exists.

Translation choices:
* a finite simple graph is a `SimpleGraph (Fin n)`, with `n` existentially quantified (every finite
  graph is isomorphic to one on `Fin n`);
* connected: Mathlib's `SimpleGraph.Connected` (this also makes the graph nonempty);
* non-complete: `G ≠ ⊤`;
* vertex-critical: for every vertex `v`, the chromatic number of `G - v` (the subgraph induced on
  the other vertices) is strictly less than that of `G`; chromatic numbers are Mathlib's
  `SimpleGraph.chromaticNumber`, finite here;
* `K_t` is a minor of `G` when there are `t` pairwise disjoint branch sets, each inducing a
  connected (hence nonempty) subgraph, with an edge of `G` between any two of them (the same
  definition as in `statements/opg-forcing-a-k-6-minor.lean`);
* `η(G)` is `sSup` of the `t` such that `K_t` is a minor of `G`. On `Fin n` this set contains `0`
  and is bounded by `n` (the branch sets are disjoint and nonempty), so the `sSup` is its largest
  element; for a nonempty graph it is at least `1`, so it is the largest positive such `t`, as in
  the source;
* adding the edge `{v, w}` is `G ⊔ SimpleGraph.edge v w`, for `v ≠ w` not adjacent in `G`.
-/

namespace OMA.S_mo_381998

/-- `G` has a `K_t`-minor: `t` pairwise disjoint branch sets, each inducing a connected (hence
nonempty) subgraph, with an edge of `G` between any two of them. -/
def HasCompleteMinor {V : Type*} (G : SimpleGraph V) (t : ℕ) : Prop :=
  ∃ B : Fin t → Set V, (∀ i, (G.induce (B i)).Connected) ∧
    (Pairwise fun i j => Disjoint (B i) (B j)) ∧
    ∀ i j, i ≠ j → ∃ x ∈ B i, ∃ y ∈ B j, G.Adj x y

/-- The Hadwiger number: the largest `t` such that `K_t` is a minor of `G` (a maximum for finite
graphs). -/
noncomputable def hadwigerNumber {V : Type*} (G : SimpleGraph V) : ℕ :=
  sSup {t | HasCompleteMinor G t}

/-- There is a finite, connected, non-complete, vertex-critical graph in which adding any missing
edge increases the Hadwiger number. -/
theorem main :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)),
      G.Connected ∧ G ≠ ⊤ ∧
      (∀ v : Fin n, (G.induce ({v}ᶜ : Set (Fin n))).chromaticNumber < G.chromaticNumber) ∧
      ∀ v w : Fin n, v ≠ w → ¬ G.Adj v w →
        hadwigerNumber G < hadwigerNumber (G ⊔ SimpleGraph.edge v w) := by
  sorry

end OMA.S_mo_381998
