import FormalConjectures.ErdosProblems.«767»

/-! Czipszer bound: a longest-path argument yields a vertex of degree ≤ k+1 in every nonempty subset. -/

open SimpleGraph Erdos767

theorem OMA.solution : type_of% @Erdos767.erdos_767.variants.czipszer := by
  classical
  intro k n
  unfold Erdos767.g
  refine csSup_le' ?_
  rintro _ ⟨G, hG, rfl⟩
  have hedge : ∀ S : Finset (Fin n),
      (G.edgeFinset.filter fun e => ∀ z ∈ e, z ∈ S).card ≤ (k + 1) * S.card := by
    intro S; induction S using Finset.strongInduction with
    | H S ih =>
      rcases S.eq_empty_or_nonempty with rfl | ⟨s, hs⟩
      · simp only [Finset.card_empty, mul_zero, nonpos_iff_eq_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro e _ h; induction e using Sym2.ind with | h a b => simpa using h a (Sym2.mem_mk_left a b)
      · have hdeg : ∃ v ∈ S, (S.filter (G.Adj v)).card ≤ k + 1 := by
          let P (m : ℕ) := ∃ (u w : Fin n) (p : G.Walk u w), p.IsPath ∧ (∀ z ∈ p.support, z ∈ S) ∧ p.length = m
          have hP0 : P 0 := ⟨s, s, .nil, by simp, by simp [hs], rfl⟩
          have hPb (m) (hm : P m) : m ≤ n := by obtain ⟨_, _, p, hp, -, rfl⟩ := hm; simpa using hp.length_lt.le
          obtain ⟨u, w, p, hp, hpS, hpl⟩ : P (Nat.findGreatest P n) := Nat.findGreatest_spec (Nat.zero_le _) hP0
          refine ⟨u, hpS u p.start_mem_support, by_contra fun hlt => ?_⟩
          push Not at hlt
          set N := S.filter (G.Adj u)
          have hN : ∀ y ∈ N, y ∈ p.support := fun y hy => by_contra fun hyp => by
            rw [Finset.mem_filter] at hy
            have hP : P (Nat.findGreatest P n + 1) := ⟨y, w, .cons hy.2.symm p, hp.cons hyp, fun z hz => by
              rw [Walk.support_cons, List.mem_cons] at hz; exact hz.elim (· ▸ hy.1) (hpS z), by simp [hpl]⟩
            have := Nat.le_findGreatest (hPb _ hP) hP; omega
          obtain ⟨x, hxN, hxmax⟩ := N.exists_max_image (p.support.idxOf ·) (Finset.card_pos.1 (by omega))
          have hxp := hN x hxN
          have hux : G.Adj u x := (Finset.mem_filter.mp hxN).2
          have hxu : x ≠ u := hux.ne.symm
          set q := p.takeUntil x hxp with hqdef
          have hqpath : q.IsPath := hp.takeUntil hxp
          have hqedge {y} (r : G.Walk u x) (hr : r.IsPath) (he : s(u, y) ∈ r.edges) : y = r.snd := by
            cases r with
            | nil => simp at he
            | cons _ r =>
              rw [Walk.cons_isPath_iff] at hr; rw [Walk.edges_cons, List.mem_cons] at he
              rcases he with he | he
              · rcases Sym2.eq_iff.1 he with ⟨-, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
              · exact absurd (r.fst_mem_support_of_mem_edges he) hr.2
          have hyq : ∀ y ∈ N, y ∈ q.support := fun y hy => by
            rw [hqdef, Walk.takeUntil_eq_take, Walk.support_copy, Walk.support_take, List.mem_take_iff_getElem]
            have hyl := List.idxOf_lt_length_iff.2 (hN y hy)
            have := hxmax y hy
            exact ⟨p.support.idxOf y, by omega, List.getElem_idxOf hyl⟩
          obtain ⟨y0, hy0N, hy0x⟩ : ∃ y ∈ N, y ≠ x := by_contra fun hc => by
            push Not at hc; have := Finset.card_le_card (fun y hy => Finset.mem_singleton.2 (hc y hy)); simp at this; omega
          have hlt0 : p.support.idxOf y0 < p.support.idxOf x :=
            (hxmax y0 hy0N).lt_of_ne fun h => hy0x ((List.idxOf_inj (hN y0 hy0N)).1 h)
          have hidx0 : 1 ≤ p.support.idxOf y0 := by
            have hyu : y0 ≠ u := (Finset.mem_filter.mp hy0N).2.ne.symm
            rw [← Walk.cons_tail_support, List.idxOf_cons_ne _ hyu.symm]; omega
          have hqlen : 2 ≤ q.length := by rw [hqdef, Walk.length_takeUntil]; omega
          have hsnd : q.snd ≠ x := by
            rw [hqdef, Walk.snd_takeUntil hxu]
            exact Walk.getVert_lt_length_takeUntil_ne hxp (by rw [← hqdef]; omega)
          let c : G.Walk u u := .cons hux q.reverse
          have hc : c.IsCycle := (Walk.cons_isCycle_iff q.reverse hux).2 ⟨hqpath.reverse, fun he => by
            rw [Walk.edges_reverse, List.mem_reverse] at he; exact hsnd (hqedge q hqpath he).symm⟩
          set T := (N.erase x).erase q.snd with hT
          have hTcard : k ≤ T.card := by
            have := Finset.pred_card_le_card_erase (s := N) (a := x)
            have := Finset.pred_card_le_card_erase (s := N.erase x) (a := q.snd); rw [hT]; omega
          obtain ⟨T', hT'T, hT'c⟩ := Finset.exists_subset_card_eq hTcard
          refine hG ⟨u, c, hc, fun i => (T'.equivFin.symm (Fin.cast hT'c.symm i)).1,
            fun _ _ h => by simpa using Subtype.val_injective h, fun i => ?_⟩
          set y := (T'.equivFin.symm (Fin.cast hT'c.symm i)).1
          have hyT := hT'T (T'.equivFin.symm (Fin.cast hT'c.symm i)).2
          rw [Finset.mem_erase, Finset.mem_erase] at hyT
          obtain ⟨hysnd, hyx, hyN⟩ := hyT
          rw [Walk.isChord_sym2Mk]
          refine ⟨(Finset.mem_filter.mp hyN).2, ?_, by simp [c], ?_⟩
          · simp only [c, Walk.edges_cons, Walk.edges_reverse, List.mem_cons, List.mem_reverse]
            rintro (h | h)
            · rcases Sym2.eq_iff.1 h with ⟨-, h⟩ | ⟨h, -⟩; exacts [hyx h, hxu h.symm]
            · exact hysnd (hqedge q hqpath h)
          · simp only [c, Walk.support_cons, Walk.support_reverse, List.mem_cons, List.mem_reverse]
            exact Or.inr (hyq y hyN)
        obtain ⟨v, hvS, hv⟩ := hdeg
        have hsub : G.edgeFinset.filter (fun e => ∀ z ∈ e, z ∈ S) ⊆
            G.edgeFinset.filter (fun e => ∀ z ∈ e, z ∈ S.erase v) ∪ (S.filter (G.Adj v)).image (s(v, ·)) := by
          intro e he; induction e using Sym2.ind with
          | h a b =>
            rw [Finset.mem_filter, mem_edgeFinset, mem_edgeSet] at he
            have ha := he.2 a (Sym2.mem_mk_left a b); have hb := he.2 b (Sym2.mem_mk_right a b)
            rw [Finset.mem_union, Finset.mem_filter, Finset.mem_image, mem_edgeFinset, mem_edgeSet]
            by_cases hav : a = v; · subst hav; exact Or.inr ⟨b, Finset.mem_filter.2 ⟨hb, he.1⟩, rfl⟩
            by_cases hbv : b = v; · subst hbv; exact Or.inr ⟨a, Finset.mem_filter.2 ⟨ha, he.1.symm⟩, Sym2.eq_swap⟩
            exact Or.inl ⟨he.1, fun z hz => (Sym2.mem_iff.1 hz).elim
              (fun h => h ▸ Finset.mem_erase.2 ⟨hav, ha⟩) (fun h => h ▸ Finset.mem_erase.2 ⟨hbv, hb⟩)⟩
        have h1 := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
        have h2 := Finset.card_image_le (s := S.filter (G.Adj v)) (f := (s(v, ·)))
        have h3 := ih (S.erase v) (Finset.erase_ssubset hvS)
        rw [Finset.card_erase_of_mem hvS] at h3
        have : 1 ≤ S.card := Finset.card_pos.2 ⟨s, hs⟩
        have : (k + 1) * (S.card - 1) + (k + 1) = (k + 1) * S.card := by rw [← Nat.mul_succ]; congr 1; omega
        omega
  have := hedge Finset.univ
  rw [Finset.card_univ, Fintype.card_fin] at this
  exact (le_of_eq (by congr 1; ext e; simp)).trans this
