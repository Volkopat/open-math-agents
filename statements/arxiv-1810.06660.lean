import Mathlib

/-!
# Connected strongly regular graphs of even order are class 1

Source: https://arxiv.org/abs/1810.06660, Conjecture 1.2 (Cioabă, Guo and Haemers)
Credit: @pyaf

An SRG with parameters (n, k, λ, μ) has n vertices, is k-regular with
0 < k < n − 1, adjacent vertices have λ common neighbours and distinct
non-adjacent vertices have μ common neighbours. The chromatic index of G is
the chromatic number of its line graph. The conjecture: except for the
Petersen graph, every connected SRG of even order has chromatic index equal
to its degree k. The Petersen graph is the Kneser graph on the 2-subsets of
a 5-set, two subsets being adjacent when disjoint.
-/

namespace OMA.S_arxiv_1810_06660

def petersen : SimpleGraph {s : Finset (Fin 5) // s.card = 2} :=
  SimpleGraph.fromRel (fun s t => Disjoint s.1 t.1)

theorem main : ∀ (n k ℓ μ : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    G.IsSRGWith n k ℓ μ → 0 < k → k < n - 1 → G.Connected → Even n →
    IsEmpty (G ≃g petersen) → G.lineGraph.chromaticNumber = k := by
  sorry

end OMA.S_arxiv_1810_06660
