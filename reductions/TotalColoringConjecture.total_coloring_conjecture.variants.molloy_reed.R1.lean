import FormalConjectures.Wikipedia.TotalColoringConjecture

/-!
# Reduction of the Molloy-Reed total colouring bound

Reduction `TotalColoringConjecture.total_coloring_conjecture.variants.molloy_reed.R1`.

The target asks for an absolute constant `C` with `chi''(G) <= Delta(G) + C` for every finite
simple graph `G`. The reduction splits the degree range at an absolute threshold `Delta0`:

* `H1` is the Molloy-Reed (1998) theorem itself, restricted to the large-degree regime
  `Delta0 <= Delta(G)`: a probabilistic total colouring with an absolute additive constant `C1`.
  This is the whole mathematical content of the published result and the only part that is not
  elementary.
* `H2` is the universal greedy total colouring bound `chi''(G) <= 2 * Delta(G) + 1`, valid for
  every graph with no hypothesis on the degree. It follows from a greedy colouring of the total
  graph on `V (+) E(G)`, whose maximum degree is at most `2 * Delta(G)`.

`main` sets `C = max C1 (Delta0 + 1)` and splits on `Delta0 <= Delta(G)`:
in the large-degree regime `H1` gives `chi'' <= Delta + C1 <= Delta + C`; in the
bounded-degree regime `Delta(G) < Delta0` the greedy bound gives
`chi'' <= 2 * Delta + 1 <= Delta + (Delta0 + 1) <= Delta + C`.
Hence a single absolute constant works for all graphs, which is the target.
-/

namespace OMA.R_TotalColoringConjecture_total_coloring_conjecture_variants_molloy_reed_R1

/-- Molloy-Reed (1998) in the large-degree regime: above an absolute threshold `Delta0` the total
chromatic number exceeds the maximum degree by at most an absolute constant `C1`. -/
def H1 : Prop :=
  ∃ Delta0 C1 : Nat,
    ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      Delta0 ≤ G.maxDegree →
        G.totalChromaticNumber ≤ G.maxDegree + C1

/-- Universal greedy total colouring bound: the total graph on `V (+) E(G)` has maximum degree at
most `2 * Delta(G)`, so a greedy colouring uses at most `2 * Delta(G) + 1` colours. -/
def H2 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    G.totalChromaticNumber ≤ 2 * G.maxDegree + 1

theorem main :
    H1 → H2 → type_of% @TotalColoringConjecture.total_coloring_conjecture.variants.molloy_reed := by
  intro hLarge hGreedy
  obtain ⟨Delta0, C1, hBound⟩ := hLarge
  refine ⟨max C1 (Delta0 + 1), ?_⟩
  intro V _ _ G _
  by_cases hdeg : Delta0 ≤ G.maxDegree
  · exact le_trans (hBound G hdeg)
      (Nat.add_le_add_left (Nat.le_max_left C1 (Delta0 + 1)) _)
  · have hlt : G.maxDegree < Delta0 := Nat.lt_of_not_le hdeg
    have hle : Delta0 + 1 ≤ max C1 (Delta0 + 1) := Nat.le_max_right C1 (Delta0 + 1)
    exact le_trans (hGreedy G) (by omega)

end OMA.R_TotalColoringConjecture_total_coloring_conjecture_variants_molloy_reed_R1
