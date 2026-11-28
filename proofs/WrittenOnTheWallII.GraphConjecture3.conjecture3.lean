import FormalConjectures.WrittenOnTheWallII.GraphConjecture3
import Mathlib.Combinatorics.SimpleGraph.Star

/-! Shorter proof of `WrittenOnTheWallII.GraphConjecture3.conjecture3`. -/

open SimpleGraph Finset

theorem OMA.solution : type_of% @WrittenOnTheWallII.GraphConjecture3.conjecture3 := by
  intro V _ _ G _ _ hc
  classical
  obtain ⟨v, -, hv⟩ := mem_image.mp (max'_mem (univ.image (temp_v G)) (image_nonempty.mpr univ_nonempty))
  have h1 : (G.degree v : ℝ) ≤ Ls G := by
    obtain ⟨T, hHT, hTG, ht⟩ := hc.exists_isTree_le_of_le_of_isAcyclic
      (H := G ⊓ starGraph v) inf_le_left ((isTree_starGraph v).isAcyclic.anti inf_le_right)
    have hdeg : G.degree v ≤ T.degree v := card_le_card fun w hw =>
      (T.mem_neighborFinset v w).mpr (hHT ⟨(G.mem_neighborFinset v w).mp hw,
        starGraph_center_adj ((G.mem_neighborFinset v w).mp hw).ne⟩)
    have hw (u : V) : 2 + (if u = v then T.degree v else 0) ≤
        T.degree u + (if T.degree u = 1 then 1 else 0) + (if u = v then 2 else 0) := by
      have := ht.connected.preconnected.degree_pos_of_nontrivial u
      by_cases hu : u = v
      · subst u; simp; split <;> omega
      · by_cases h1 : T.degree u = 1 <;> simp [hu, h1]
        omega
    have hsum := sum_le_sum (s := univ) fun u _ => hw u
    simp only [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, sum_ite_eq', mem_univ,
      if_true, sum_boole] at hsum
    have := T.sum_degrees_eq_twice_card_edges; have := ht.card_edgeFinset
    simp at hsum
    let S := G.toSubgraph T hTG
    have iso : S.coe ≃g T := { toEquiv := Equiv.Set.univ V, map_rel_iff' := by intros; rfl }
    have hS : S.IsSpanning ∧ S.coe.IsTree := ⟨toSubgraph.isSpanning T hTG, iso.isTree_iff.mpr ht⟩
    have hj : (univ.filter fun x => T.degree x = 1) ⊆ S.verts.toFinset.filter (fun x => S.degree x = 1) :=
      fun w hw => mem_filter.mpr ⟨by simp [S], by rw [degree_toSubgraph]; exact (mem_filter.mp hw).2⟩
    have hcard : G.degree v ≤ (S.verts.toFinset.filter fun x => S.degree x = 1).card :=
      le_trans (by omega) (card_le_card hj)
    refine le_trans (Nat.cast_le.mpr hcard) ?_
    exact le_csSup ⟨Fintype.card V, by rintro _ ⟨Z, _, rfl⟩; exact Nat.cast_le.mpr (card_le_univ _)⟩
      ⟨S, hS, rfl⟩
  have h2 : (G.indepDominationNumber : ℝ) + G.degree v ≤ Fintype.card V := by
    let A := univ.filter fun s : Finset V => G.IsIndepSet s
    obtain ⟨s, hvs, hmax⟩ := A.exists_le_maximal (a := {v}) (by simp [A, SimpleGraph.IsIndepSet])
    have hs : G.IsIndepSet s := (mem_filter.mp hmax.prop).2
    have hdom : G.IsDominating s := fun x => by
      by_contra! h
      refine h.1 (hmax.2 (mem_filter.mpr ⟨mem_univ _, ?_⟩)
        (subset_insert _ _) (mem_insert_self ..))
      rw [coe_insert]
      exact hs.insert fun a ha _ => ⟨h.2 a ha, fun h' => h.2 a ha h'.symm⟩
    have hsmall : G.indepDominationNumber ≤ s.card := Nat.sInf_le ⟨s, hs, hdom, rfl⟩
    have hd : Disjoint s (G.neighborFinset v) := disjoint_left.mpr fun w hw hw' =>
      hs (hvs (by simp)) hw ((G.mem_neighborFinset v w).mp hw').ne ((G.mem_neighborFinset v w).mp hw')
    have hcu := (s ∪ G.neighborFinset v).card_le_univ
    rw [card_union_of_disjoint hd, card_neighborFinset_eq_degree] at hcu
    exact_mod_cast (by omega : G.indepDominationNumber + G.degree v ≤ Fintype.card V)
  have hn := G.degree_lt_card_verts v
  have hn' : (0 : ℝ) < Fintype.card V - G.degree v := sub_pos.mpr (by exact_mod_cast hn)
  have hv' : temp_v G v = MaxTemp G := hv
  rw [← hv']
  refine le_trans ?_ h1
  rw [temp_v, if_neg hn.ne', ← mul_div_assoc, div_le_iff₀ hn']
  nlinarith [mul_le_mul_of_nonneg_right h2 (Nat.cast_nonneg (α := ℝ) (G.degree v))]
