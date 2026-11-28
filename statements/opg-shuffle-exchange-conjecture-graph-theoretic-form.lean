import Mathlib

/-!
# Shuffle-Exchange Conjecture (graph-theoretic form)

Source: https://www.openproblemgarden.org/op/shuffle_exchange_conjecture_graph_theoretic_form
Credit: @lzvxck

The source: given integers `k, n ≥ 2`, the 2-stage Shuffle-Exchange graph `SE(k, n)` is the
simple `k`-regular bipartite graph with linearly labeled parts `U = {u_0, ..., u_{t-1}}` and
`V = {v_0, ..., v_{t-1}}`, where `t = k^{n-1}`, in which `u_i` and `v_j` are adjacent iff
`(j - k i) mod t < k`. For `r ≥ 2`, the `r`-stage graph `(SE(k, n))^{r-1}` is the proper
(order-respecting) concatenation of `r - 1` copies of `SE(k, n)`. Let `r(k, n)` be the smallest
`r ≥ 2` such that `(SE(k, n))^{r-1}` is rearrangeable. Conjecture: `r(k, n) = 2n - 1`.
A mask for `G = (SE(k, n))^{r-1}` is a `k`-regular bipartite multigraph with bipartition
`{U, V}` (the two end parts), and `G` is rearrangeable if for every mask there is a routing:
a collection of mutually edge-disjoint paths in `G` connecting its end parts, one for each edge
of the mask, joining the ends of that edge. (Any routing consists of exactly `k^n` paths.)

Conventions: the vertices of the `r`-stage graph are pairs `(s, i)` with stage `s : Fin r` and
label `i : Fin t`, and `(s, i)`, `(s + 1, j)` are adjacent iff `(j - k i) mod t < k`. A path
between the end parts goes through each stage once, so it is a map `P : Fin r → Fin t` with
consecutive entries adjacent. A mask is a list of `k t = k^n` pairs `(u, v)` (its edges, with
multiplicity) in which every label occurs exactly `k` times as a first entry and exactly `k`
times as a second entry. Two paths are edge-disjoint when they never use the same edge
between consecutive stages. `r(k, n) = 2n - 1` is stated as: the `(2n-1)`-stage graph is
rearrangeable, and no `r`-stage graph with `2 ≤ r < 2n - 1` is.
-/

namespace OMA.S_opg_shuffle_exchange_conjecture_graph_theoretic_form

/-- Adjacency in `SE(k, n)` between label `i` of one stage and label `j` of the next, for
`t = k^{n-1}`. -/
def SEAdj (k t : ℕ) (i j : Fin t) : Prop := ((j : ℤ) - k * i) % t < k

/-- `m` is a mask: each label is the first entry of exactly `k` pairs and the second entry of
exactly `k` pairs. -/
def IsMask (k t : ℕ) (m : Fin (k * t) → Fin t × Fin t) : Prop :=
  ∀ u : Fin t, (Finset.univ.filter fun e => (m e).1 = u).card = k ∧
    (Finset.univ.filter fun e => (m e).2 = u).card = k

/-- The `r`-stage Shuffle-Exchange graph `(SE(k, n))^{r-1}` is rearrangeable. -/
def IsRearrangeable (k n r : ℕ) : Prop :=
  ∀ m : Fin (k * k ^ (n - 1)) → Fin (k ^ (n - 1)) × Fin (k ^ (n - 1)),
    IsMask k (k ^ (n - 1)) m →
      ∃ P : Fin (k * k ^ (n - 1)) → Fin r → Fin (k ^ (n - 1)),
        (∀ e (h : 0 < r), P e ⟨0, h⟩ = (m e).1 ∧ P e ⟨r - 1, by omega⟩ = (m e).2) ∧
        (∀ e (s : ℕ) (h : s + 1 < r),
          SEAdj k (k ^ (n - 1)) (P e ⟨s, by omega⟩) (P e ⟨s + 1, h⟩)) ∧
        ∀ e e', e ≠ e' → ∀ (s : ℕ) (h : s + 1 < r),
          ¬ (P e ⟨s, by omega⟩ = P e' ⟨s, by omega⟩ ∧ P e ⟨s + 1, h⟩ = P e' ⟨s + 1, h⟩)

/-- **Shuffle-Exchange conjecture (graph-theoretic form; Beneš, Stone).** For all `k, n ≥ 2`,
the smallest `r ≥ 2` for which `(SE(k, n))^{r-1}` is rearrangeable is `2n - 1`. -/
theorem main : ∀ k n : ℕ, 2 ≤ k → 2 ≤ n →
    IsRearrangeable k n (2 * n - 1) ∧ ∀ r, 2 ≤ r → r < 2 * n - 1 → ¬ IsRearrangeable k n r := by
  sorry

end OMA.S_opg_shuffle_exchange_conjecture_graph_theoretic_form
