import Mathlib

/-!
# Minimum total dominating sets of trees

Source: https://arxiv.org/abs/1804.10476 (Michael A. Henning, Elena Mohr and Dieter Rautenbach,
On the maximum number of minimum total dominating sets in forests), the conjecture of the
abstract.
Credit: @JamesSlash

A set `D` of vertices of a graph `G` is a total dominating set if every vertex of `G` has a
neighbour in `D`. The total domination number `γ_t(G)` is the minimum size of a total dominating
set, and a minimum total dominating set is a total dominating set of size `γ_t(G)`.

The conjecture: every tree `T` of order `n ≥ 2` with total domination number `γ_t` has at most
`((n - γ_t / 2) / (γ_t / 2)) ^ (γ_t / 2)` minimum total dominating sets.

Formalization notes: the tree is a Mathlib `SimpleGraph` on a finite vertex type `V` with
`IsTree`, and `n` is the number of vertices. A tree of order at least 2 has no isolated vertex, so
`V` itself is a total dominating set and the infimum defining `γ_t` is a minimum. The bound is a
real number (`γ_t / 2` need not be an integer) and the power is `Real.rpow`.
-/

namespace OMA.S_arxiv_1804_10476

variable {V : Type} [Fintype V]

/-- `D` is a total dominating set of `G`: every vertex has a neighbour in `D`. -/
def IsTotalDominating (G : SimpleGraph V) (D : Finset V) : Prop :=
  ∀ v, ∃ w ∈ D, G.Adj v w

/-- The total domination number `γ_t(G)`: the least size of a total dominating set. -/
noncomputable def totalDominationNumber (G : SimpleGraph V) : ℕ :=
  sInf {k : ℕ | ∃ D : Finset V, IsTotalDominating G D ∧ D.card = k}

/-- The number of minimum total dominating sets of `G`. -/
noncomputable def numMinTotalDominating (G : SimpleGraph V) : ℕ :=
  {D : Finset V | IsTotalDominating G D ∧ D.card = totalDominationNumber G}.ncard

theorem main : ∀ (V : Type) [Fintype V] (T : SimpleGraph V), T.IsTree → 2 ≤ Fintype.card V →
    (numMinTotalDominating T : ℝ) ≤
      (((Fintype.card V : ℝ) - (totalDominationNumber T : ℝ) / 2) /
        ((totalDominationNumber T : ℝ) / 2)) ^ ((totalDominationNumber T : ℝ) / 2) := by
  sorry

end OMA.S_arxiv_1804_10476
