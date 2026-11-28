import FormalConjectures.Arxiv.«2607.06396».AlonTarsi

-- Reduction Arxiv.2607.06396.alon_tarsi_short_cycle_cover.R1 of the Alon-Tarsi conjecture
-- Credit: @marcusbuffett

/-!
# Alon-Tarsi short cycle cover: Veblen's theorem for even graphs, and the open rest

* `H1` (classical, provable): Veblen's theorem (1912). A finite simple graph in which every
  vertex has even degree is an edge-disjoint union of cycles, so it has a cycle cover whose
  total length is at most its number of edges, far below the `7/5` bound. The proof finds a
  cycle (a longest path in an acyclic graph would end in a vertex of degree one, which is odd),
  deletes its edges (every vertex loses an even number of them), and inducts on the edges.
* `H2` (open): the conjecture for bridgeless graphs with at least one vertex of odd degree.

`main` splits on whether every degree is even. This is the standard classical case of the
conjecture, not progress on it.
-/

open Finset SimpleGraph

namespace OMA.R_Arxiv_2607_06396_alon_tarsi_short_cycle_cover_R1

/-- Classical (Veblen): a graph with all degrees even has a cycle cover of total length at most
its number of edges. -/
def H1 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    (∀ v, Even (G.degree v)) →
      ∃ C : Multiset (Cycle G), Arxiv.«2607.06396».IsCycleCover G C ∧
        Arxiv.«2607.06396».totalLength C ≤ #G.edgeFinset

/-- Open: the Alon-Tarsi bound for bridgeless graphs that have a vertex of odd degree. -/
def H2 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    G.IsBridgeless → (∃ v, Odd (G.degree v)) →
      ∃ C : Multiset (Cycle G), Arxiv.«2607.06396».IsCycleCover G C ∧
        (Arxiv.«2607.06396».totalLength C : ℚ) ≤ 7 / 5 * #G.edgeFinset

theorem main : H1 → H2 → type_of% @Arxiv.«2607.06396».alon_tarsi_short_cycle_cover := by
  intro h1 h2 V _ _ G _ hbr
  by_cases hev : ∀ v, Even (G.degree v)
  · obtain ⟨C, hC, hlen⟩ := h1 V G hev
    refine ⟨C, hC, ?_⟩
    have : (Arxiv.«2607.06396».totalLength C : ℚ) ≤ #G.edgeFinset := by exact_mod_cast hlen
    have h0 : (0 : ℚ) ≤ #G.edgeFinset := by positivity
    linarith
  · push Not at hev
    obtain ⟨v, hv⟩ := hev
    exact h2 V G hbr ⟨v, Nat.not_even_iff_odd.mp hv⟩

end OMA.R_Arxiv_2607_06396_alon_tarsi_short_cycle_cover_R1
