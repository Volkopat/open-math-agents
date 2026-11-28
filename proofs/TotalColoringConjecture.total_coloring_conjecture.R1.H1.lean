import OMAReductions.R_TotalColoringConjecture_total_coloring_conjecture_R1

/-! Maximum-degree-one total colouring, following @Raimo33 (#19019).
Use incidence-set cardinalities for the edge conditions. -/

namespace OMAE_TC
open SimpleGraph

theorem uniq {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : G.maxDegree ≤ 1) {v a b : V} (ha : G.Adj v a) (hb : G.Adj v b) : a = b := by
  have hd := G.degree_le_maxDegree v
  rw [← card_neighborFinset_eq_degree] at hd
  exact (Finset.card_le_one (s := G.neighborFinset v)).mp (by omega) a (by simpa using ha) b (by simpa using hb)

theorem colorable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : G.maxDegree ≤ 1) : G.TotalColorable (G.maxDegree + 2) := by
  classical
  let e := Fintype.equivFin V
  let c : V ⊕ G.edgeSet → Fin (G.maxDegree + 2) := Sum.elim
    (fun v => if ∃ w, G.Adj v w ∧ e w < e v then ⟨1, by omega⟩ else ⟨0, by omega⟩)
    (fun _ => ⟨G.maxDegree + 1, by omega⟩)
  refine ⟨c, ?_, ?_, ?_⟩
  · intro u v huv hc
    have hne : e u ≠ e v := fun h' => G.ne_of_adj huv (e.injective h')
    rcases lt_or_gt_of_ne hne with hl | hl
    · have h1 : ∃ w, G.Adj v w ∧ e w < e v := ⟨u, huv.symm, hl⟩
      have h0 : ¬ ∃ w, G.Adj u w ∧ e w < e u := by
        rintro ⟨w, hw, hwl⟩
        have := uniq G h hw huv
        subst this; exact absurd hl (not_lt.mpr hwl.le)
      simp only [c, Sum.elim_inl, h1, h0, if_true, if_false] at hc
      exact absurd (congrArg Fin.val hc) (by simp)
    · have h1 : ∃ w, G.Adj u w ∧ e w < e u := ⟨v, huv, hl⟩
      have h0 : ¬ ∃ w, G.Adj v w ∧ e w < e v := by
        rintro ⟨w, hw, hwl⟩
        have := uniq G h hw huv.symm
        subst this; exact absurd hl (not_lt.mpr hwl.le)
      simp only [c, Sum.elim_inl, h1, h0, if_true, if_false] at hc
      exact absurd (congrArg Fin.val hc) (by simp)
  · rintro ⟨f1, hf1⟩ ⟨f2, hf2⟩ hne ⟨v, hv1, hv2⟩ -
    apply hne
    apply Subtype.ext
    have hd : (G.incidenceFinset v).card ≤ 1 := by
      rw [G.card_incidenceFinset_eq_degree]
      exact (G.degree_le_maxDegree v).trans h
    exact Finset.card_le_one.mp hd f1 ((G.mem_incidenceFinset _ _).mpr ⟨hf1, hv1⟩)
      f2 ((G.mem_incidenceFinset _ _).mpr ⟨hf2, hv2⟩)
  · rintro v ⟨f, hf⟩ hv hc
    have hdeg : 1 ≤ G.maxDegree := by
      have hpos : 0 < (G.incidenceFinset v).card :=
        Finset.card_pos.mpr ⟨f, (G.mem_incidenceFinset _ _).mpr ⟨hf, hv⟩⟩
      rw [G.card_incidenceFinset_eq_degree] at hpos
      exact hpos.trans_le (G.degree_le_maxDegree v)
    have hv' := congrArg Fin.val hc
    simp only [c, Sum.elim_inl, Sum.elim_inr] at hv'
    by_cases hp : ∃ w, G.Adj v w ∧ e w < e v
    · simp only [hp, if_true] at hv'; omega
    · simp only [hp, if_false] at hv'; omega

end OMAE_TC

theorem OMA.solution : OMA.R_TotalColoringConjecture_total_coloring_conjecture_R1.H1 := by
  intro V _ _ G _ h
  exact Nat.sInf_le (OMAE_TC.colorable G h)
