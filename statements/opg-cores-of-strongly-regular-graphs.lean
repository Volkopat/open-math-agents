import Mathlib

/-!
# Cores of strongly regular graphs

Source: http://www.openproblemgarden.org/op/cores_of_strongly_regular_graphs
Credit: @shc261392

Question (Cameron and Kazanidis): does every strongly regular graph have either itself or a
complete graph as a core?

Reading used here:
* Graphs are finite simple graphs; strongly regular is Mathlib's `SimpleGraph.IsSRGWith n k ℓ μ`
  for some parameters.
* The core of a finite graph `G` is its smallest subgraph `H` admitting a homomorphism `G → H`;
  it is unique up to isomorphism. Two standard facts turn the question into homomorphism
  language:
  - `G` is its own core iff every homomorphism `G → G` is a bijection.
  - The core of `G` is a complete graph `K_m` iff `G → K_m` and `K_m ⊆ G`, i.e. iff
    `χ(G) ≤ m ≤ ω(G)`, i.e. iff `G.chromaticNumber = G.cliqueNum`.
* The statement is the affirmative answer; a proof of its negation answers the question in the
  negative.
-/

namespace OMA.S_opg_cores_of_strongly_regular_graphs

theorem main :
    ∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (n k ℓ μ : ℕ),
      G.IsSRGWith n k ℓ μ →
        (∀ f : G →g G, Function.Bijective f) ∨ G.chromaticNumber = (G.cliqueNum : ℕ∞) := by
  sorry

end OMA.S_opg_cores_of_strongly_regular_graphs
