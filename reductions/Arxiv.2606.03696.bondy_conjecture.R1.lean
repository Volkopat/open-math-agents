import FormalConjectures.Arxiv.«2606.03696».BondyLongestCycles

-- Credit: @PetrouilFan
-- Reduction of Bondy's conjecture.  Ma-Ning-Zhao proved the conjecture once
-- n >= 5*k^2 + 7*k; the bounded range n < 5*k^2 + 7*k is the open core.
-- Each hypothesis is stated inline so it is self-contained.

namespace OMA.R_Arxiv_2606_03696_bondy_conjecture_R1

open SimpleGraph
open Arxiv.«2606.03696»

-- Open core: bounded number of vertices.
def H1 : Prop :=
  ∀ (k : ℕ), 1 ≤ k → ∀ (V : Type) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj], IsKConnected G k →
    ((Fintype.card V : ℝ) + k * (k - 1)) / (k + 1) ≤ G.minDegree →
    Fintype.card V < 5 * k ^ 2 + 7 * k →
    ∀ (a : V) (C : G.Walk a a), C.IsCycle → C.length = G.circumference →
    ∀ (u v : offWalk C) (P : (G.induce (offWalk C)).Walk u v), P.IsPath →
      P.support.length + 1 ≤ k

-- Proved large-n theorem of Ma-Ning-Zhao.
def H2 : Prop :=
  ∀ (k : ℕ), 1 ≤ k → ∀ (V : Type) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj],
    5 * k ^ 2 + 7 * k ≤ Fintype.card V → IsKConnected G k →
    ((Fintype.card V : ℝ) + k * (k - 1)) / (k + 1) ≤ G.minDegree →
    ∀ (a : V) (C : G.Walk a a), C.IsCycle → C.length = G.circumference →
    ∀ (u v : offWalk C) (P : (G.induce (offWalk C)).Walk u v), P.IsPath →
      P.support.length + 1 ≤ k

theorem main : H1 → H2 → type_of% @Arxiv.«2606.03696».bondy_conjecture := by
  intro hsmall hlarge k hk V _ _ G _ hconn hdeg a C hC hlong u v P hP
  by_cases h : 5 * k ^ 2 + 7 * k ≤ Fintype.card V
  · exact hlarge k hk V G h hconn hdeg a C hC hlong u v P hP
  · exact hsmall k hk V G hconn hdeg (by omega) a C hC hlong u v P hP

end OMA.R_Arxiv_2606_03696_bondy_conjecture_R1
