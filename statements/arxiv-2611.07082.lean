import Mathlib

/-!
# Seeking the dense half in `K₄`-free graphs: the conjectured tight bound

Source: arXiv:2611.07082, I. Buczek, A. Grzesik and P. Kuc, "Seeking the dense half in
`K₄`-free graphs", Conjecture 2.3.
Credit: @jagraj28

For a graph `G`, a bipartition `V(G) = A₁ ∪ A₂` is *balanced* if `||A₁| - |A₂|| ≤ 1`, and
`e(A)` is the number of edges of `G` with both endpoints in `A`. The paper defines
`D^b_{2,∞}(G) = min max(e(A₁), e(A₂))` over all balanced bipartitions (the `ℓ∞`-norm case of
`D^b_{k,p}` in the introduction). It proves `D^b_{2,∞}(G) ≤ 0.0671 n² + o(n²)` for `K₄`-free
graphs on `n` vertices, gives a construction with `D^b_{2,∞} = (425/6498) n² + o(n²)`, and
states:

  Conjecture 2.3. If `G` is a `K₄`-free graph on `n` vertices, then
  `D^b_{2,∞}(G) ≤ (425/6498) n² + o(n²)`.

(Conjecture 1.4 of the paper, the bound `n²/16`, is false by a construction of Xu and Zhang.)

Conventions.
* Graphs on `n` vertices are `SimpleGraph (Fin n)`; `K₄`-free is `CliqueFree 4`.
* A balanced bipartition is given by one part `A : Finset (Fin n)`; the other part is `Aᶜ`, and
  balance is `|A| ≤ |Aᶜ| + 1 ∧ |Aᶜ| ≤ |A| + 1`.
* `e(A)` counts the edges `s ∈ G.edgeFinset` with both endpoints in `A`.
* The `o(n²)` term is uniform over all `K₄`-free graphs on `n` vertices, as usual: for every
  `ε > 0` there is `N` such that for all `n ≥ N` and all such `G` the bound holds with
  `(425/6498 + ε) n²`.
-/

namespace OMA.S_arxiv_2611_07082

/-- The number of edges of `G` with both endpoints in `A`. -/
def edgesIn {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)) : ℕ :=
  (G.edgeFinset.filter fun s => ∀ v ∈ s, v ∈ A).card

/-- Conjecture 2.3: every `K₄`-free graph on `n` vertices has a balanced bipartition in which
each part spans at most `(425/6498) n² + o(n²)` edges. -/
theorem main : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj], G.CliqueFree 4 →
      ∃ A : Finset (Fin n), A.card ≤ Aᶜ.card + 1 ∧ Aᶜ.card ≤ A.card + 1 ∧
        (edgesIn G A : ℝ) ≤ (425 / 6498 + ε) * n ^ 2 ∧
        (edgesIn G Aᶜ : ℝ) ≤ (425 / 6498 + ε) * n ^ 2 := by
  sorry

end OMA.S_arxiv_2611_07082
