import FormalConjectures.Wikipedia.TotalColoringConjecture

/-!
# Reduction R1 of the total colouring conjecture
Credit: @sntntHb

Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

Split by the maximum degree of the graph:
* H1: maximum degree at most 1 (elementary: explicit colourings with 2 or 3 colours).
* H2: maximum degree between 2 and 5 (known: Rosenfeld and Vijayaditya (1971) for degree 3,
  cycles and paths for degree 2, Kostochka (1996) for degrees 4 and 5; not in Mathlib).
* H3: maximum degree at least 6 (the open core of the conjecture).
No implication runs between the degree classes: putting a graph next to a component of larger
degree raises the number of colours allowed, so the classes are independent cases.
-/

namespace OMA.R_TotalColoringConjecture_total_coloring_conjecture_R1

open SimpleGraph

/-- Graphs of maximum degree at most 1. -/
def H1 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    G.maxDegree ≤ 1 → G.totalChromaticNumber ≤ G.maxDegree + 2

/-- Graphs of maximum degree 2 to 5 (Rosenfeld, Vijayaditya, Kostochka). -/
def H2 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    2 ≤ G.maxDegree → G.maxDegree ≤ 5 → G.totalChromaticNumber ≤ G.maxDegree + 2

/-- Graphs of maximum degree at least 6 (open). -/
def H3 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    6 ≤ G.maxDegree → G.totalChromaticNumber ≤ G.maxDegree + 2

theorem main : H1 → H2 → H3 →
    type_of% @TotalColoringConjecture.total_coloring_conjecture := by
  intro h1 h2 h3 V _ _ G _
  by_cases ha : G.maxDegree ≤ 1
  · exact h1 G ha
  · by_cases hb : G.maxDegree ≤ 5
    · exact h2 G (by omega) hb
    · exact h3 G (by omega)

end OMA.R_TotalColoringConjecture_total_coloring_conjecture_R1
