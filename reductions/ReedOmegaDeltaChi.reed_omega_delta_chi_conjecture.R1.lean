import FormalConjectures.Paper.ReedOmegaDeltaChi

-- Reduction ReedOmegaDeltaChi.reed_omega_delta_chi_conjecture.R1 of Reed's omega, delta and chi conjecture
-- Credit: @marcusbuffett

/-!
# Reed's conjecture for arbitrary graphs: the greedy slice, and the open rest

Reed's conjecture says `2 * χ(G) ≤ ω(G) + Δ(G) + 2`, here for every simple graph on an arbitrary
(possibly infinite) vertex type, with `ℕ∞`-valued clique number and maximum degree.

* `H1` (classical, provable): graphs with `Δ(G) ≤ ω(G)`. If `Δ(G)` is infinite the bound is
  trivial; otherwise the transfinite greedy colouring along a well-order of the vertices uses at
  most `Δ(G) + 1` colours (each vertex sees at most `Δ(G)` earlier neighbours), so
  `2 * χ ≤ 2 * Δ + 2 ≤ ω + Δ + 2`. This covers every graph with `Δ(G) ≤ 2` that has an edge.
* `H2` (open): graphs with `ω(G) < Δ(G)`, which contains the open case `Δ = 6, ω = 2`.

This is the classical case of the conjecture, not progress on it.
-/

namespace OMA.R_ReedOmegaDeltaChi_reed_omega_delta_chi_conjecture_R1

/-- Classical: the conjecture for graphs whose maximum degree is at most their clique number. -/
def H1 : Prop :=
  ∀ {V : Type} (G : SimpleGraph V), G.emaxDegree ≤ G.ecliqueNum →
    2 * G.chromaticNumber ≤ G.ecliqueNum + G.emaxDegree + 2

/-- Open: the conjecture for graphs whose clique number is below their maximum degree. -/
def H2 : Prop :=
  ∀ {V : Type} (G : SimpleGraph V), G.ecliqueNum < G.emaxDegree →
    2 * G.chromaticNumber ≤ G.ecliqueNum + G.emaxDegree + 2

theorem main : H1 → H2 → type_of% @ReedOmegaDeltaChi.reed_omega_delta_chi_conjecture := by
  intro h1 h2 V G
  rcases le_or_gt G.emaxDegree G.ecliqueNum with h | h
  · exact h1 G h
  · exact h2 G h

end OMA.R_ReedOmegaDeltaChi_reed_omega_delta_chi_conjecture_R1
