import OMAStatements.S_mse_3117996
import Mathlib.Order.ConditionallyCompleteLattice.Finset

/-!
Balanced weight perfect matching
Source problem by illigrad:
https://math.stackexchange.com/questions/3117996/balanced-weight-perfect-matching
Credit: @grp06
-/

open OMA.S_mse_3117996

private theorem matchingWeightsNonempty {V : Type*} [Nonempty V]
    {G : SimpleGraph V} {M : G.Subgraph} (hM : M.IsPerfectMatching)
    (w : Sym2 V → ℝ) : (w '' M.edgeSet).Nonempty := by
  obtain ⟨v⟩ := ‹Nonempty V›
  obtain ⟨u, hvu, _⟩ := SimpleGraph.Subgraph.isPerfectMatching_iff.mp hM v
  exact ⟨w s(v, u), s(v, u), SimpleGraph.Subgraph.mem_edgeSet.mpr hvu, rfl⟩

private theorem intervalOfMatchingExtrema {V : Type*} [Fintype V] [Nonempty V]
    {G : SimpleGraph V} {M : G.Subgraph} (hM : M.IsPerfectMatching)
    (w : Sym2 V → ℝ) :
    ∃ lo ∈ G.edgeSet, ∃ hi ∈ G.edgeSet,
      w lo ≤ w hi ∧ w hi - w lo = weightSpread M w ∧
      hasPerfectMatching (intervalGraph G w (w lo) (w hi)) := by
  have hFinite : (w '' M.edgeSet).Finite := (Set.toFinite M.edgeSet).image w
  have hNonempty := matchingWeightsNonempty hM w
  obtain ⟨lo, hlo, hLo⟩ := hNonempty.csInf_mem hFinite
  obtain ⟨hi, hhi, hHi⟩ := hNonempty.csSup_mem hFinite
  have hLower (e : Sym2 V) (he : e ∈ M.edgeSet) : w lo ≤ w e := by
    rw [hLo]
    exact csInf_le hFinite.bddBelow ⟨e, he, rfl⟩
  have hUpper (e : Sym2 V) (he : e ∈ M.edgeSet) : w e ≤ w hi := by
    rw [hHi]
    exact le_csSup hFinite.bddAbove ⟨e, he, rfl⟩
  have hSub : M.spanningCoe ≤ intervalGraph G w (w lo) (w hi) := by
    rw [SimpleGraph.le_iff_adj]
    intro v u hvu
    have he : s(v, u) ∈ M.edgeSet := SimpleGraph.Subgraph.mem_edgeSet.mpr hvu
    exact ⟨M.spanningCoe_le hvu, hLower _ he, hUpper _ he⟩
  refine ⟨lo, M.edgeSet_subset hlo, hi, M.edgeSet_subset hhi,
    hLower hi hhi, ?_, (intervalGraph G w (w lo) (w hi)).toSubgraph M.spanningCoe hSub, ?_⟩
  · rw [weightSpread, hLo, hHi]
  · exact (SimpleGraph.Subgraph.IsPerfectMatching.toSubgraph_iff hSub).mpr hM

private theorem matchingOfInterval {V : Type*} [Nonempty V]
    {G : SimpleGraph V} {w : Sym2 V → ℝ} {a b : ℝ}
    (h : hasPerfectMatching (intervalGraph G w a b)) :
    ∃ M : G.Subgraph, M.IsPerfectMatching ∧ weightSpread M w ≤ b - a := by
  obtain ⟨N, hN⟩ := h
  have hInterval : intervalGraph G w a b ≤ G := by
    rw [SimpleGraph.le_iff_adj]
    intro v u hAdj
    exact hAdj.1
  have hSub : N.spanningCoe ≤ G := N.spanningCoe_le.trans hInterval
  let M := G.toSubgraph N.spanningCoe hSub
  have hM : M.IsPerfectMatching :=
    (SimpleGraph.Subgraph.IsPerfectMatching.toSubgraph_iff hSub).mpr hN
  have hEdges : M.edgeSet = N.edgeSet := by
    change N.spanningCoe.edgeSet = N.edgeSet
    exact N.edgeSet_spanningCoe
  have hBounds (e : Sym2 V) (he : e ∈ N.edgeSet) : a ≤ w e ∧ w e ≤ b := by
    induction e using Sym2.ind with
    | h v u =>
      have hAdj : N.Adj v u := SimpleGraph.Subgraph.mem_edgeSet.mp he
      have hRange : G.Adj v u ∧ a ≤ w s(v, u) ∧ w s(v, u) ≤ b := N.adj_sub hAdj
      exact hRange.2
  have hNonempty := matchingWeightsNonempty hN w
  have hSup : sSup (w '' N.edgeSet) ≤ b := by
    apply csSup_le hNonempty
    rintro _ ⟨e, he, rfl⟩
    exact (hBounds e he).2
  have hInf : a ≤ sInf (w '' N.edgeSet) := by
    apply le_csInf hNonempty
    rintro _ ⟨e, he, rfl⟩
    exact (hBounds e he).1
  refine ⟨M, hM, ?_⟩
  rw [weightSpread, hEdges]
  exact sub_le_sub hSup hInf

theorem OMA.solution : type_of% @OMA.S_mse_3117996.main := by
  classical
  intro V _ _ G w
  have hBudget (budget : ℝ) :
      (∃ M : G.Subgraph, M.IsPerfectMatching ∧ weightSpread M w ≤ budget) ↔
        ∃ lo ∈ G.edgeSet, ∃ hi ∈ G.edgeSet,
          w lo ≤ w hi ∧ w hi - w lo ≤ budget ∧
          hasPerfectMatching (intervalGraph G w (w lo) (w hi)) := by
    constructor
    · rintro ⟨M, hM, hSpread⟩
      obtain ⟨lo, hlo, hi, hhi, hOrder, hWidth, hMatching⟩ :=
        intervalOfMatchingExtrema hM w
      exact ⟨lo, hlo, hi, hhi, hOrder, (le_of_eq hWidth).trans hSpread, hMatching⟩
    · rintro ⟨lo, _, hi, _, _, hWidth, hMatching⟩
      obtain ⟨M, hM, hSpread⟩ := matchingOfInterval hMatching
      exact ⟨M, hM, hSpread.trans hWidth⟩
  refine ⟨hBudget, ?_, ?_⟩
  · rw [candidatePairs, Finset.card_product, ← Set.ncard_eq_toFinset_card', pow_two]
  · rintro ⟨N, hN⟩
    have hFinite : (matchingSpreads G w).Finite := by
      change ((fun M : G.Subgraph => weightSpread M w) ''
        {M : G.Subgraph | M.IsPerfectMatching}).Finite
      exact (Set.toFinite {M : G.Subgraph | M.IsPerfectMatching}).image _
    have hNonempty : (matchingSpreads G w).Nonempty :=
      ⟨weightSpread N w, N, hN, rfl⟩
    let d := sInf (matchingSpreads G w)
    have hd : d ∈ matchingSpreads G w := hNonempty.csInf_mem hFinite
    have hLeast : IsLeast (matchingSpreads G w) d :=
      ⟨hd, fun _ hu => csInf_le hFinite.bddBelow hu⟩
    obtain ⟨M, hM, hMd⟩ := hd
    obtain ⟨lo, hlo, hi, hhi, hOrder, hWidth, hMatching⟩ :=
      intervalOfMatchingExtrema hM w
    refine ⟨d, hLeast, ⟨⟨lo, hlo, hi, hhi, hOrder, hWidth.trans hMd, hMatching⟩, ?_⟩⟩
    intro u hu
    obtain ⟨lo', hlo', hi', hhi', hOrder', hWidth', hMatching'⟩ := hu
    have hWithinBudget : w hi' - w lo' ≤ u := le_of_eq hWidth'
    obtain ⟨K, hK, hKu⟩ :=
      (hBudget u).mpr ⟨lo', hlo', hi', hhi', hOrder', hWithinBudget, hMatching'⟩
    have hKMem : weightSpread K w ∈ matchingSpreads G w := ⟨K, hK, rfl⟩
    exact (hLeast.2 hKMem).trans hKu
