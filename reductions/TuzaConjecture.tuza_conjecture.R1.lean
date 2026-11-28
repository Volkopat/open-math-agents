import FormalConjectures.Wikipedia.TuzaConjecture
import Mathlib

-- Reduction TuzaConjecture.tuza_conjecture.R1 of Tuza's conjecture: every finite graph satisfies
-- tau(G) ≤ 2 nu(G), where tau is the least number of edges meeting every triangle and nu the
-- largest number of pairwise edge-disjoint triangles.
-- Credit: @marcusbuffett
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- This is a classical slice, not progress on the conjecture itself. H1 is the case nu(G) ≤ 1:
-- a triangle-free graph needs no edge, and a graph whose triangles pairwise share an edge can be
-- covered by two edges (Tuza 1990). It also follows from the known general bound
-- tau ≤ (66/23) nu (Haxell 1999; the catalogue variant tuza_conjecture.variants.haxell, merged
-- upstream with the bound 165/59), because 66/23 < 3 and tau is an integer. That route gives
-- nothing for nu ≥ 2, so H2, the conjecture for graphs with at least two edge-disjoint
-- triangles, carries the whole open difficulty.

namespace OMA.R_TuzaConjecture_tuza_conjecture_R1

open TuzaConjecture

/-- Tuza's conjecture for graphs with at most one edge-disjoint triangle. -/
def H1 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), trianglePackingNumber G ≤ 1 →
    triangleCoverNumber G ≤ 2 * trianglePackingNumber G

/-- Tuza's conjecture for graphs with at least two edge-disjoint triangles. -/
def H2 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), 2 ≤ trianglePackingNumber G →
    triangleCoverNumber G ≤ 2 * trianglePackingNumber G

theorem main : H1 → H2 → type_of% @TuzaConjecture.tuza_conjecture := by
  intro h1 h2 V _ G
  rcases Nat.lt_or_ge (trianglePackingNumber G) 2 with h | h
  · exact h1 V G (by omega)
  · exact h2 V G h

end OMA.R_TuzaConjecture_tuza_conjecture_R1
