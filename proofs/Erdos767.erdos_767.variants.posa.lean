import FormalConjectures.ErdosProblems.«767»
import Mathlib.Tactic

open SimpleGraph Walk Erdos767 Finset

theorem OMA.solution : type_of% @Erdos767.erdos_767.variants.posa := fun n hn => by
  classical
  have h (G : SimpleGraph (Fin n)) (hG : ¬HasCycleWithIncidentChords G 1) : #G.edgeFinset ≤ 2 * n - 4 := by
    have L : ∀ {u x y} (q : G.Walk u x), q.IsPath → G.Adj u x → G.Adj u y → y ∈ q.support → y ≠ x →
        y ≠ q.snd → x ≠ q.snd → False := fun {u x y} q hq h h' hy h1 h2 h3 => by
      have F (z) (he : s(u, z) ∈ q.edges) : z = q.snd := by
        cases q <;> simp_all
        grind [fst_mem_support_of_mem_edges]
      exact hG ⟨u, .cons h q.reverse, (cons_isCycle_iff _ _).2 ⟨hq.reverse, by simpa using h3 ∘ F x⟩,
        fun _ => y, fun _ _ _ => Subsingleton.elim .., fun _ => ⟨h', by simpa [h1, h.ne] using h2 ∘ F y, by simp, by simp [hy]⟩⟩
    have U : ∀ S : Finset _, #(G.edgeFinset ∩ S.sym2) ≤ 2 * #S - 3 - min 1 (#S / 4) :=
      strongInduction fun S ih => by
      rcases S.eq_empty_or_nonempty with rfl | ⟨s, hs⟩
      · simp
      have P : ∀ S : Finset _, ∀ v ∈ S, #(G.edgeFinset ∩ S.sym2) ≤
          #(G.edgeFinset ∩ (S.erase v).sym2) + #(S.filter (G.Adj v)) := fun S v hv => by
        refine (card_le_card fun e he => ?_).trans ((card_union_le _
          ((S.filter (G.Adj v)).image (s(v, ·)))).trans (Nat.add_le_add_left card_image_le _))
        induction e using Sym2.ind
        simp at he ⊢
        grind [adj_comm]
      obtain ⟨v, hv, h2⟩ : ∃ v ∈ S, #(S.filter (G.Adj v)) ≤ 2 := by
        by_contra! h
        obtain ⟨⟨u, w, p, hp⟩, hS, hm⟩ := (univ.filter fun q : Σ u w, G.Path u w =>
          ∀ z ∈ q.2.2.1.support, z ∈ S).exists_max_image (·.2.2.1.length) ⟨⟨s, s, .nil, .nil⟩, by simp [hs]⟩
        simp at hS
        have hN : ∀ y ∈ S, G.Adj u y → y ∈ p.support := fun y hy ha => by_contra fun hn => by
          simpa using hm ⟨y, w, .cons ha.symm p, hp.cons hn⟩ (by simp [hy]; exact hS)
        have := (lt_tsub_iff_right.2 (h u (hS u p.start_mem_support))).trans_le
          (pred_card_le_card_erase (a := p.snd))
        obtain ⟨x, hx, hm⟩ := exists_max_image _ (p.support.idxOf ·) (card_pos.1 (Nat.zero_lt_of_lt this))
        obtain ⟨y, hy, hyx⟩ := exists_mem_ne this x
        simp at hx hy
        have hxp := hN x hx.2.1 hx.2.2
        have e := snd_takeUntil hx.2.2.ne' p hxp
        exact L _ (hp.takeUntil hxp) hx.2.2 hy.2.2 (by
          grind [takeUntil_eq_take, support_copy, support_take,
            List.mem_take_iff_idxOf_lt]) hyx (e ▸ hy.1) (e ▸ hx.1)
      have := P S v hv
      have := ih _ (erase_ssubset hv)
      have N : ∀ (T : Finset _) v, T.filter (G.Adj v) ⊆ T.erase v := fun _ _ _ => by grind [Adj.ne]
      have h3 := card_le_card (N S v)
      have := card_erase_of_mem hv
      by_contra hc
      have T : ∀ p ∈ S.erase v, ∀ q ∈ S.erase v, q ≠ p → G.Adj p q := fun p hp q hq h => by
        have := P _ p hp
        have := ih _ ((erase_ssubset hp).trans (erase_ssubset hv))
        have := card_erase_of_mem hp
        exact (mem_filter.1 ((eq_of_subset_of_card_le (N _ p) (by omega)).ge (mem_erase.2 ⟨h, hq⟩))).2
      obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.1 (by omega : 1 < #(S.filter (G.Adj v)))
      obtain ⟨c, hc, hc'⟩ := exists_mem_notMem_of_card_lt_card (h3.lt_of_ne (by omega))
      have ha' := N _ _ ha
      have hb' := N _ _ hb
      have hac := ne_of_mem_of_not_mem ha hc'
      have hbc := ne_of_mem_of_not_mem hb hc'
      simp at ha hb
      have hcv := (mem_erase.1 hc).1
      exact L (.cons (T a ha' c hc hac.symm) (.cons (T c hc b hb' hbc) (.cons hb.2.symm .nil)))
        (by simp [hab, hac, hbc.symm, ha.2.ne', hb.2.ne', hcv]) ha.2.symm (T a ha' b hb' hab.symm)
        (by simp) hb.2.ne' hbc hcv.symm
    have := U univ
    simp at this
    omega
  let K : SimpleGraph (Fin n) := { Adj a b := (a.1 < 2) ≠ (b.1 < 2) }
  have hK : ¬HasCycleWithIncidentChords K 1 := by
    rintro ⟨v, c, hc, f, -, hf⟩
    have key : ∀ a b, K.Adj b a → 2 ≤ b.1 → b ∈ c.support → c.toSubgraph.Adj b a := fun a b h hb hs => by
      by_contra hne
      have := (hc.ncard_neighborSet_toSubgraph_eq_two hs).symm.trans_le <| Set.ncard_le_ncard
        (t := {(⟨1 - a.1, by omega⟩ : Fin n)}) fun x (hx : c.toSubgraph.Adj b x) => by
        have h1 := c.toSubgraph.adj_sub hx
        have h2 : x ≠ a := fun e => hne (e ▸ hx)
        simp [K, Fin.ext_iff] at h h1 h2 ⊢
        omega
      simp at this
    obtain ⟨h, h', hv, hw⟩ := hf 0
    refine h' (adj_toSubgraph_iff_mem_edges.1 ?_)
    by_cases hb : 2 ≤ v.1
    · exact key _ _ h hb hv
    · exact (key v (f 0) h.symm (by simp [K] at h; omega) hw).symm
  have hE : 2 * n - 4 ≤ #K.edgeFinset := (card_le_card_of_injOn (t := K.edgeFinset) (s := univ)
    (fun p : Fin 2 × Fin (n - 2) => s(⟨p.1, by omega⟩, ⟨p.2.1 + 2, by omega⟩))
    (fun p _ => by simp [K]; omega) fun p _ q _ h => by grind).trans' (by simp; omega)
  exact IsGreatest.csSup_eq ⟨⟨K, hK, (h _ hK).antisymm (by convert hE; rfl)⟩, fun m ⟨G, hG, e⟩ => e ▸ h G hG⟩

