import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-!
Source: https://math.stackexchange.com/questions/3117996
The exact reduction of minimum-spread perfect matching to finitely many interval graphs.
Nonempty vertices ensure a perfect matching has minimum and maximum edge weights.
-/

namespace OMA.S_mse_3117996

def intervalGraph {V : Type*} (G : SimpleGraph V) (w : Sym2 V → ℝ)
    (lo hi : ℝ) : SimpleGraph V where
  Adj v u := G.Adj v u ∧ lo ≤ w s(v, u) ∧ w s(v, u) ≤ hi
  symm := by
    constructor
    intro v u h
    simpa only [Sym2.eq_swap] using And.intro h.1.symm h.2
  loopless := by
    constructor
    intro v h
    exact G.loopless.irrefl v h.1

noncomputable def weightSpread {V : Type*} {G : SimpleGraph V}
    (M : G.Subgraph) (w : Sym2 V → ℝ) : ℝ :=
  sSup (w '' M.edgeSet) - sInf (w '' M.edgeSet)

def hasPerfectMatching {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ M : G.Subgraph, M.IsPerfectMatching

noncomputable def candidatePairs {V : Type*} [Fintype V] (G : SimpleGraph V) :
    Finset (Sym2 V × Sym2 V) := by
  classical
  exact G.edgeSet.toFinset ×ˢ G.edgeSet.toFinset

def matchingSpreads {V : Type*} (G : SimpleGraph V) (w : Sym2 V → ℝ) : Set ℝ :=
  {d | ∃ M : G.Subgraph, M.IsPerfectMatching ∧ weightSpread M w = d}

def feasibleWidths {V : Type*} (G : SimpleGraph V) (w : Sym2 V → ℝ) : Set ℝ :=
  {d | ∃ lo ∈ G.edgeSet, ∃ hi ∈ G.edgeSet,
    w lo ≤ w hi ∧ w hi - w lo = d ∧
    hasPerfectMatching (intervalGraph G w (w lo) (w hi))}

theorem main : ∀ {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (w : Sym2 V → ℝ),
    (∀ budget : ℝ,
      (∃ M : G.Subgraph, M.IsPerfectMatching ∧ weightSpread M w ≤ budget) ↔
      ∃ lo ∈ G.edgeSet, ∃ hi ∈ G.edgeSet,
        w lo ≤ w hi ∧ w hi - w lo ≤ budget ∧
        hasPerfectMatching (intervalGraph G w (w lo) (w hi))) ∧
    (candidatePairs G).card = G.edgeSet.ncard ^ 2 ∧
    (hasPerfectMatching G →
      ∃ optimum : ℝ, IsLeast (matchingSpreads G w) optimum ∧
        IsLeast (feasibleWidths G w) optimum) := by
  sorry

end OMA.S_mse_3117996
