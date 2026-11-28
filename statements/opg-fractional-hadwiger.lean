import Mathlib

/-!
# Fractional Hadwiger

Source: https://www.openproblemgarden.org/op/fractional_hadwiger
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (Reed–Seymour; Harvey–Wood; Pedersen): for every graph `G`,
(a) `χ_f(G) ≤ had(G)`, (b) `χ(G) ≤ had_f(G)`, (c) `χ_f(G) ≤ had_f(G)`.

Conventions (Harvey–Wood, *Parameters tied to treewidth*, following Fox and Pedersen):
* Graphs are finite simple graphs. `had(G)` is the largest `t` such that `G` has a `K_t` minor,
  i.e. `t` pairwise disjoint vertex sets, each inducing a connected subgraph, with an edge between
  every two of them.
* A bramble is a family of vertex sets, each inducing a connected subgraph, any two of which
  touch (share a vertex or are joined by an edge). `had_f(G)` is the maximum of `∑ w(X)` over
  brambles with non-negative weights `w` such that every vertex lies in sets of total weight at
  most `1`.
* `χ_f(G)` is the fractional chromatic number, taken as the linear-programming value: the
  minimum total weight of a non-negative weighting of independent sets covering every vertex
  with weight at least `1` (equal to `lim_b χ_b(G) / b` for `b`-fold colourings).
* `main` states all three parts; (a) and (b) each imply (c).
-/

namespace OMA.S_opg_fractional_hadwiger

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `X` induces a connected (in particular nonempty) subgraph of `G`. -/
def IsConn (G : SimpleGraph V) (X : Finset V) : Prop :=
  (G.induce (X : Set V)).Connected

/-- `X` and `Y` touch: they share a vertex or some edge joins them. -/
def Touch (G : SimpleGraph V) (X Y : Finset V) : Prop :=
  (X ∩ Y).Nonempty ∨ ∃ x ∈ X, ∃ y ∈ Y, G.Adj x y

/-- A bramble of `G`. -/
def IsBramble (G : SimpleGraph V) (B : Finset (Finset V)) : Prop :=
  (∀ X ∈ B, IsConn G X) ∧ ∀ X ∈ B, ∀ Y ∈ B, Touch G X Y

/-- The Hadwiger number `had(G)`: the largest order of a complete minor. -/
noncomputable def had (G : SimpleGraph V) : ℕ :=
  sSup {t : ℕ | ∃ f : Fin t → Finset V, (∀ i, IsConn G (f i)) ∧
    ∀ i j, i ≠ j → Disjoint (f i) (f j) ∧ ∃ x ∈ f i, ∃ y ∈ f j, G.Adj x y}

/-- The fractional Hadwiger number `had_f(G)`. -/
noncomputable def hadf (G : SimpleGraph V) : ℝ :=
  sSup {h : ℝ | ∃ (B : Finset (Finset V)) (w : Finset V → ℝ), IsBramble G B ∧
    (∀ X, 0 ≤ w X) ∧ (∀ v : V, ∑ X ∈ B.filter (fun X => v ∈ X), w X ≤ 1) ∧
    h = ∑ X ∈ B, w X}

/-- The fractional chromatic number `χ_f(G)`. -/
noncomputable def chif (G : SimpleGraph V) : ℝ :=
  sInf {s : ℝ | ∃ w : Finset V → ℝ, (∀ I, 0 ≤ w I) ∧
    (∀ I, w I ≠ 0 → G.IsIndepSet (I : Set V)) ∧
    (∀ v : V, 1 ≤ ∑ I ∈ Finset.univ.filter (fun I : Finset V => v ∈ I), w I) ∧
    s = ∑ I, w I}

/-- The chromatic number `χ(G)` of a finite graph, as a real number. -/
noncomputable def chi (G : SimpleGraph V) : ℝ :=
  (G.chromaticNumber.toNat : ℝ)

/-- Parts (a), (b) and (c) of the fractional Hadwiger conjecture. -/
theorem main : ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    chif G ≤ (had G : ℝ) ∧ chi G ≤ hadf G ∧ chif G ≤ hadf G := by
  sorry

end OMA.S_opg_fractional_hadwiger
