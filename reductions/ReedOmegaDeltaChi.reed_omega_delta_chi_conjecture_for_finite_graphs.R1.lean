import FormalConjectures.Paper.ReedOmegaDeltaChi
import Mathlib

-- Reduction ReedOmegaDeltaChi.reed_omega_delta_chi_conjecture_for_finite_graphs.R1 of Reed's omega, delta and chi conjecture (finite graphs)
-- Credit: @marcusbuffett

/-!
# Reed's conjecture for finite graphs: the greedy slice, and the open rest

Reed's conjecture says `2 * χ(G) ≤ ω(G) + Δ(G) + 2` for every finite graph `G`
(B. Reed, J. Graph Theory 27 (1998) 177-212). Every finite graph has `ω(G) ≤ Δ(G) + 1`.
This reduction splits by the size of the largest clique compared with the maximum degree.

* `H1`: graphs with `Δ(G) ≤ ω(G)`, that is the graphs that contain a clique on `Δ(G)`
  vertices (this covers every graph with `Δ(G) ≤ 2`). Here the classical greedy bound
  `χ(G) ≤ Δ(G) + 1` gives `2 * χ ≤ 2 * Δ + 2 ≤ ω + Δ + 2`. This is the classical case, not
  progress on the conjecture.
* `H2`: graphs with `ω(G) < Δ(G)`. This is the open part of Reed's conjecture (already the
  case `ω = Δ - 1` needs Brooks' theorem, and the case `Δ = 6, ω = 2` is open). It stays open.
-/

namespace OMA.R_ReedOmegaDeltaChi_reed_omega_delta_chi_conjecture_for_finite_graphs_R1

/-- The greedy slice: graphs containing a clique on `Δ(G)` vertices. -/
def H1 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    G.maxDegree ≤ G.cliqueNum →
      2 * G.chromaticNumber ≤ (G.cliqueNum : ℕ∞) + (G.maxDegree : ℕ∞) + 2

/-- The open part: graphs whose largest clique is smaller than their maximum degree. -/
def H2 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    G.cliqueNum < G.maxDegree →
      2 * G.chromaticNumber ≤ (G.cliqueNum : ℕ∞) + (G.maxDegree : ℕ∞) + 2

theorem main : H1 → H2 →
    type_of% @ReedOmegaDeltaChi.reed_omega_delta_chi_conjecture_for_finite_graphs := by
  intro h1 h2 V _ _ G _
  by_cases h : G.maxDegree ≤ G.cliqueNum
  · exact h1 G h
  · exact h2 G (by omega)

end OMA.R_ReedOmegaDeltaChi_reed_omega_delta_chi_conjecture_for_finite_graphs_R1
