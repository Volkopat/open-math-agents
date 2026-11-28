import FormalConjectures.WrittenOnTheWallII.GraphConjecture6

-- Problem: Written on the Wall II - Conjecture 6
-- Upstream: formal-conjectures FormalConjectures/WrittenOnTheWallII/GraphConjecture6.lean:42 (declaration WrittenOnTheWallII.GraphConjecture6.conjecture6)
-- Credit: @senamakel (the owner of the agent is credited as the solver)
-- Reference: E. DeLaVina, Written on the Wall II (1996): the bound follows from Ls ≥ n + 1 - 2α and Ls ≥ n - 2μ type bounds.

/-!
# A spanning tree with at least 1 + n - μ - α leaves

A connected dominating set `D` gives a spanning tree in which every vertex outside `D` is a leaf,
so `Ls G ≥ n - |D|`. Two greedy constructions give connected dominating sets:
one of size `2k` carrying a matching with `k` edges, one of size at most `2|M| - 1` for an
independent set `M`. If `α ≤ μ` the second gives `Ls ≥ n + 1 - 2α ≥ 1 + n - μ - α`;
otherwise `k ≤ μ < α`, so `k + 1 ≤ α` and the first gives `Ls ≥ n - 2k ≥ 1 + n - μ - α`.
-/

open SimpleGraph Finset

namespace OMAWowii6
variable {α : Type*} [Fintype α] [DecidableEq α]


/-- Steps inside `D`. -/
def RD (G : SimpleGraph α) (D : Finset α) (a b : α) : Prop := a ∈ D ∧ b ∈ D ∧ G.Adj a b

/-- `D` is a connected dominating set. -/
def IsCDS (G : SimpleGraph α) (D : Finset α) : Prop :=
  D.Nonempty ∧ (∀ x ∈ D, ∀ y ∈ D, Relation.ReflTransGen (RD G D) x y) ∧
    ∀ w ∉ D, ∃ d ∈ D, G.Adj w d

lemma ls_ge_of_cds [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (D : Finset α)
    (hD : IsCDS G D) : (Fintype.card α : ℝ) - D.card ≤ Ls G := by
  classical
  obtain ⟨⟨d0, hd0⟩, hconn, hdom⟩ := hD
  choose! f hfD hfadj using hdom
  let r : α → α → Prop := fun x y => (x ∈ D ∧ y ∈ D ∧ G.Adj x y) ∨ (x ∉ D ∧ y = f x)
  let H : SimpleGraph α := SimpleGraph.fromRel r
  have hHG : H ≤ G := by
    intro x y h
    simp only [H, fromRel_adj, r] at h
    obtain ⟨_, h | h⟩ := h
    · rcases h with ⟨_, _, h⟩ | ⟨hx, rfl⟩
      · exact h
      · exact hfadj x hx
    · rcases h with ⟨_, _, h⟩ | ⟨hy, rfl⟩
      · exact h.symm
      · exact (hfadj y hy).symm
  have hHadjD : ∀ x y, x ∈ D → y ∈ D → G.Adj x y → H.Adj x y := by
    intro x y hx hy h
    simp only [H, fromRel_adj, r]
    exact ⟨G.ne_of_adj h, Or.inl (Or.inl ⟨hx, hy, h⟩)⟩
  have key : ∀ y, Relation.ReflTransGen (RD G D) d0 y → H.Reachable d0 y := by
    intro y h
    induction h with
    | refl => exact Reachable.refl _
    | tail _ hbc ih =>
      obtain ⟨hb, hc, hbc'⟩ := hbc
      exact ih.trans (hHadjD _ _ hb hc hbc').reachable
  have hreachD : ∀ x ∈ D, H.Reachable d0 x := fun x hx => key x (hconn d0 hd0 x hx)
  have hHconn : H.Connected := by
    have hpre : ∀ x, H.Reachable d0 x := by
      intro x
      by_cases hx : x ∈ D
      · exact hreachD x hx
      · have hadj : H.Adj (f x) x := by
          simp only [H, fromRel_adj, r]
          refine ⟨fun h => hx (h ▸ hfD x hx), Or.inr (Or.inr ⟨hx, trivial⟩)⟩
        exact (hreachD _ (hfD x hx)).trans hadj.reachable
    have : Nonempty α := ⟨d0⟩
    exact ⟨fun x y => (hpre x).symm.trans (hpre y)⟩
  have hnbr : ∀ w, w ∉ D → ∀ y, H.Adj w y → y = f w := by
    intro w hw y h
    simp only [H, fromRel_adj, r] at h
    obtain ⟨_, h | h⟩ := h
    · rcases h with ⟨h1, _, _⟩ | ⟨_, rfl⟩
      · exact absurd h1 hw
      · rfl
    · rcases h with ⟨_, h1, _⟩ | ⟨hy, h2⟩
      · exact absurd h1 hw
      · exact absurd (h2 ▸ hfD y hy) hw
  obtain ⟨T, hTH, hT⟩ := hHconn.exists_isTree_le
  have hTG : T ≤ G := hTH.trans hHG
  let S : G.Subgraph := toSubgraph T hTG
  have hSspan : S.IsSpanning := toSubgraph.isSpanning T hTG
  have hStree : S.coe.IsTree := by
    have e := S.spanningCoeEquivCoeOfSpanning hSspan
    exact e.isTree_iff.mp hT
  have hdeg : ∀ w, w ∉ D → S.degree w = 1 := by
    intro w hw
    rw [degree_toSubgraph]
    have hle : T.degree w ≤ 1 := by
      rw [← card_neighborFinset_eq_degree]
      apply Finset.card_le_one.mpr
      intro a ha b hb
      rw [mem_neighborFinset] at ha hb
      rw [hnbr w hw a (hTH ha), hnbr w hw b (hTH hb)]
    have hpos := hT.connected.preconnected.degree_pos_of_nontrivial w
    omega
  have hmem : (Fintype.card α : ℝ) - D.card ≤
      ((S.verts.toFinset.filter (fun v => S.degree v = 1)).card : ℝ) := by
    have hsub : Dᶜ ⊆ S.verts.toFinset.filter (fun v => S.degree v = 1) := by
      intro w hw
      rw [mem_compl] at hw
      simp only [mem_filter, Set.mem_toFinset]
      exact ⟨hSspan w, hdeg w hw⟩
    have := Finset.card_le_card hsub
    rw [card_compl] at this
    have h2 : D.card ≤ Fintype.card α := card_le_univ D
    have h3 : ((Fintype.card α - D.card : ℕ) : ℝ) ≤
        ((S.verts.toFinset.filter (fun v => S.degree v = 1)).card : ℝ) := by exact_mod_cast this
    rw [Nat.cast_sub h2] at h3
    exact h3
  unfold Ls
  refine le_trans hmem (le_csSup ?_ ⟨S, ⟨hSspan, hStree⟩, ?_⟩)
  · refine ⟨Fintype.card α, ?_⟩
    rintro _ ⟨T', _, rfl⟩
    simp only
    exact_mod_cast card_le_univ _
  · simp only


lemma exists_cross (G : SimpleGraph α) (hG : G.Connected) (S : Finset α) (s w : α)
    (hs : s ∈ S) (hw : w ∉ S) : ∃ u ∈ S, ∃ v ∉ S, G.Adj u v := by
  obtain ⟨p⟩ := hG.preconnected s w
  obtain ⟨d, _, h1, h2⟩ := p.exists_boundary_dart (S : Set α) hs hw
  exact ⟨d.fst, h1, d.snd, h2, d.adj⟩

lemma exists_grow (G : SimpleGraph α) (hG : G.Connected) {T : Finset α}
    (hne : T.Nonempty) (hnd : ¬ ∀ w ∉ T, ∃ d ∈ T, G.Adj w d) :
    ∃ u v d, d ∈ T ∧ u ∉ T ∧ v ∉ T ∧ (∀ y ∈ T, ¬ G.Adj v y) ∧ G.Adj u d ∧ G.Adj u v := by
  classical
  push_neg at hnd
  obtain ⟨w, hw, hn⟩ := hnd
  obtain ⟨a, ha⟩ := hne
  let S := univ.filter (fun x => x ∈ T ∨ ∃ d ∈ T, G.Adj x d)
  obtain ⟨u, hu, v, hv, h⟩ := exists_cross G hG S a w (by simp [S, ha])
    (by simpa [S, hw, not_exists, not_and] using hn)
  simp only [S, mem_filter, mem_univ, true_and, not_or, not_exists, not_and] at hu hv
  have hnu : u ∉ T := fun mem => hv.2 u mem h.symm
  obtain ⟨d, hd, hadj⟩ := hu.resolve_left hnu
  exact ⟨u, v, d, hd, hnu, hv.1, hv.2, hadj, h⟩

lemma rtg_mono (G : SimpleGraph α) {D D' : Finset α} (h : D ⊆ D') {x y : α}
    (hxy : Relation.ReflTransGen (RD G D) x y) : Relation.ReflTransGen (RD G D') x y :=
  by
    induction hxy with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hab ih => exact ih.tail ⟨h hab.1, h hab.2.1, hab.2.2⟩

lemma conn_insert (G : SimpleGraph α) {D : Finset α} (hD : ∀ x ∈ D, ∀ y ∈ D,
    Relation.ReflTransGen (RD G D) x y) {u d : α} (hd : d ∈ D) (hud : G.Adj u d) :
    ∀ x ∈ insert u D, ∀ y ∈ insert u D, Relation.ReflTransGen (RD G (insert u D)) x y := by
  have hsub : D ⊆ insert u D := subset_insert _ _
  have h1 : Relation.ReflTransGen (RD G (insert u D)) u d :=
    Relation.ReflTransGen.single ⟨mem_insert_self _ _, hsub hd, hud⟩
  have h2 : Relation.ReflTransGen (RD G (insert u D)) d u :=
    Relation.ReflTransGen.single ⟨hsub hd, mem_insert_self _ _, hud.symm⟩
  intro x hx y hy
  rw [mem_insert] at hx hy
  rcases hx with rfl | hx <;> rcases hy with rfl | hy
  · exact Relation.ReflTransGen.refl
  · exact h1.trans (rtg_mono G hsub (hD d hd y hy))
  · exact (rtg_mono G hsub (hD x hx d hd)).trans h2
  · exact rtg_mono G hsub (hD x hx y hy)

/-- Greedy growth of a connected set together with an independent set. -/
lemma greedy_indep (G : SimpleGraph α) (hG : G.Connected) : ∀ t : ℕ, ∀ T M : Finset α,
    Fintype.card α - T.card ≤ t → M ⊆ T → M.Nonempty → G.IsIndepSet (M : Set α) →
    (∀ x ∈ T, x ∈ M ∨ ∃ m ∈ M, G.Adj x m) →
    (∀ x ∈ T, ∀ y ∈ T, Relation.ReflTransGen (RD G T) x y) → T.card + 1 ≤ 2 * M.card →
    ∃ D N : Finset α, IsCDS G D ∧ G.IsIndepSet (N : Set α) ∧ D.card + 1 ≤ 2 * N.card := by
  intro t
  induction t with
  | zero =>
    intro T M ht hMT hMne hind hcov hconn hcard
    have hT : T = univ := by
      apply Finset.eq_univ_of_card
      have := card_le_univ T
      omega
    refine ⟨T, M, ⟨hMne.mono hMT, hconn, ?_⟩, hind, hcard⟩
    intro w hw; exact absurd (hT ▸ mem_univ w) hw
  | succ t ih =>
    intro T M ht hMT hMne hind hcov hconn hcard
    classical
    by_cases hdom : ∀ w ∉ M, ∃ m ∈ M, G.Adj w m
    · refine ⟨T, M, ⟨hMne.mono hMT, hconn, ?_⟩, hind, hcard⟩
      intro w hw
      obtain ⟨m, hm, h⟩ := hdom w (fun h => hw (hMT h))
      exact ⟨m, hMT hm, h⟩
    obtain ⟨u, v, m, hm, _, hvM, hvadj, hum, huv⟩ := exists_grow G hG hMne hdom
    have hvT : v ∉ T := by
      intro h
      rcases hcov v h with h' | ⟨m', hm', h'⟩
      · exact hvM h'
      · exact hvadj m' hm' h'
    let T' := insert v (insert u T)
    let M' := insert v M
    apply ih T' M'
    · have : T.card < T'.card := by
        apply Finset.card_lt_card
        exact ⟨fun x hx => mem_insert_of_mem (mem_insert_of_mem hx),
          fun h => hvT (h (mem_insert_self v _))⟩
      omega
    · intro x hx
      rw [mem_insert] at hx
      rcases hx with rfl | hx
      · exact mem_insert_self _ _
      · exact mem_insert_of_mem (mem_insert_of_mem (hMT hx))
    · exact ⟨v, mem_insert_self _ _⟩
    · rw [coe_insert]
      refine hind.insert ?_
      intro b hb _
      exact ⟨hvadj b hb, fun h => hvadj b hb h.symm⟩
    · intro x hx
      rw [mem_insert, mem_insert] at hx
      rcases hx with rfl | rfl | hx
      · exact Or.inl (mem_insert_self _ _)
      · exact Or.inr ⟨m, mem_insert_of_mem hm, hum⟩
      · rcases hcov x hx with h | ⟨m', hm', h⟩
        · exact Or.inl (mem_insert_of_mem h)
        · exact Or.inr ⟨m', mem_insert_of_mem hm', h⟩
    · have h1 := conn_insert G hconn (hMT hm) hum
      exact conn_insert G h1 (mem_insert_self u T) huv.symm
    · have h1 : T'.card ≤ T.card + 2 := by
        calc T'.card ≤ (insert u T).card + 1 := card_insert_le _ _
          _ ≤ T.card + 1 + 1 := by gcongr; exact card_insert_le _ _
      have h2 : M'.card = M.card + 1 := card_insert_of_notMem hvM
      omega


lemma greedy_match (G : SimpleGraph α) (hG : G.Connected) : ∀ t : ℕ, ∀ (T : Finset α)
    (P : G.Subgraph), Fintype.card α - T.card ≤ t → T.Nonempty → P.IsMatching →
    P.verts = (T : Set α) → 2 * P.edgeSet.ncard = T.card →
    (∀ x ∈ T, ∀ y ∈ T, Relation.ReflTransGen (RD G T) x y) →
    ∃ (D : Finset α) (Q : G.Subgraph), IsCDS G D ∧ Q.IsMatching ∧ 2 * Q.edgeSet.ncard = D.card := by
  intro t
  induction t with
  | zero =>
    intro T P ht hTne hP hPv hPe hconn
    have hT : T = univ := by
      apply Finset.eq_univ_of_card
      have := card_le_univ T
      omega
    refine ⟨T, P, ⟨hTne, hconn, ?_⟩, hP, hPe⟩
    intro w hw; exact absurd (hT ▸ mem_univ w) hw
  | succ t ih =>
    intro T P ht hTne hP hPv hPe hconn
    classical
    by_cases hdom : ∀ w ∉ T, ∃ d ∈ T, G.Adj w d
    · exact ⟨T, P, ⟨hTne, hconn, hdom⟩, hP, hPe⟩
    obtain ⟨u, v, d, hd, huT, hvT, _, hud, huv⟩ := exists_grow G hG hTne hdom
    let T' := insert v (insert u T)
    let P' := P ⊔ G.subgraphOfAdj huv
    have hne : u ≠ v := G.ne_of_adj huv
    have hcard : T.card + 2 = T'.card := by
      rw [card_insert_of_notMem, card_insert_of_notMem huT]
      rw [mem_insert]; push_neg; exact ⟨hne.symm, hvT⟩
    apply ih T' P'
    · omega
    · exact ⟨v, mem_insert_self _ _⟩
    · apply hP.sup (Subgraph.IsMatching.subgraphOfAdj huv)
      rw [support_subgraphOfAdj, hP.support_eq_verts, hPv]
      rw [Set.disjoint_left]
      intro x hx hx'
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx'
      rcases hx' with rfl | rfl
      · exact huT hx
      · exact hvT hx
    · simp only [P', T', Subgraph.verts_sup, hPv, coe_insert]
      ext x
      simp only [subgraphOfAdj, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,
        mem_coe]
      tauto
    · have hnot : s(u, v) ∉ P.edgeSet := by
        intro h
        have := P.mem_verts_of_mem_edge h (Sym2.mem_mk_left u v)
        rw [hPv] at this
        exact huT this
      have : P'.edgeSet = insert s(u, v) P.edgeSet := by
        simp only [P', Subgraph.edgeSet_sup, edgeSet_subgraphOfAdj, Set.union_singleton]
      rw [this, Set.ncard_insert_of_notMem hnot (Set.toFinite _)]
      omega
    · have h1 := conn_insert G (hconn) hd hud
      exact conn_insert G h1 (mem_insert_self u T) huv.symm

lemma exists_cds_match [Nontrivial α] (G : SimpleGraph α) (hG : G.Connected) :
    ∃ (D : Finset α) (Q : G.Subgraph), IsCDS G D ∧ Q.IsMatching ∧
      2 * Q.edgeSet.ncard = D.card := by
  classical
  obtain ⟨u⟩ : Nonempty α := inferInstance
  obtain ⟨v, huv⟩ := hG.preconnected.exists_adj_of_nontrivial u
  have hne : u ≠ v := G.ne_of_adj huv
  apply greedy_match G hG (Fintype.card α) {u, v} (G.subgraphOfAdj huv)
  · omega
  · exact ⟨u, by simp⟩
  · exact Subgraph.IsMatching.subgraphOfAdj huv
  · simp [subgraphOfAdj]
  · rw [edgeSet_subgraphOfAdj, Set.ncard_singleton, card_pair hne]
  · intro a ha b hb
    simp only [mem_insert, mem_singleton] at ha hb
    have h1 : Relation.ReflTransGen (RD G {u, v}) u v :=
      Relation.ReflTransGen.single ⟨by simp, by simp, huv⟩
    have h2 : Relation.ReflTransGen (RD G {u, v}) v u :=
      Relation.ReflTransGen.single ⟨by simp, by simp, huv.symm⟩
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact Relation.ReflTransGen.refl
    · exact h1
    · exact h2
    · exact Relation.ReflTransGen.refl

lemma exists_cds_indep [Nontrivial α] (G : SimpleGraph α) (hG : G.Connected) :
    ∃ D N : Finset α, IsCDS G D ∧ G.IsIndepSet (N : Set α) ∧ D.card + 1 ≤ 2 * N.card := by
  classical
  obtain ⟨x⟩ : Nonempty α := inferInstance
  apply greedy_indep G hG (Fintype.card α) {x} {x}
  · omega
  · exact subset_refl _
  · exact ⟨x, mem_singleton_self x⟩
  · simp
  · intro y hy; exact Or.inl hy
  · intro a ha b hb
    rw [mem_singleton] at ha hb
    subst ha; subst hb
    exact Relation.ReflTransGen.refl
  · simp


lemma le_matchingNumber (G : SimpleGraph α) [DecidableRel G.Adj] (Q : G.Subgraph)
    (hQ : Q.IsMatching) : (Q.edgeSet.ncard : ℝ) ≤ matchingNumber G := by
  classical
  unfold matchingNumber
  apply le_csSup
  · refine ⟨Fintype.card (Sym2 α), ?_⟩
    rintro _ ⟨M, _, rfl⟩
    simp only
    exact_mod_cast card_le_univ _
  · refine ⟨Q, hQ, ?_⟩
    simp only
    rw [Set.ncard_eq_toFinset_card']

theorem main [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    1 + (Fintype.card α : ℝ) - matchingNumber G - G.indepNum ≤ Ls G := by
  classical
  obtain ⟨D1, Q, hD1, hQ, hQe⟩ := exists_cds_match G h
  obtain ⟨D2, N, hD2, hN, hNc⟩ := exists_cds_indep G h
  have L1 := ls_ge_of_cds G D1 hD1
  have L2 := ls_ge_of_cds G D2 hD2
  have hμ := le_matchingNumber G Q hQ
  have hα : N.card ≤ G.indepNum := hN.card_le_indepNum
  have hα' : (N.card : ℝ) ≤ G.indepNum := by exact_mod_cast hα
  have hNc' : (D2.card : ℝ) + 1 ≤ 2 * N.card := by exact_mod_cast hNc
  have hQe' : 2 * (Q.edgeSet.ncard : ℝ) = D1.card := by exact_mod_cast hQe
  by_cases hc : (G.indepNum : ℝ) ≤ matchingNumber G
  · linarith
  · push_neg at hc
    have hk : Q.edgeSet.ncard < G.indepNum := by
      have : (Q.edgeSet.ncard : ℝ) < G.indepNum := lt_of_le_of_lt hμ hc
      exact_mod_cast this
    have hk' : (Q.edgeSet.ncard : ℝ) + 1 ≤ G.indepNum := by exact_mod_cast hk
    linarith

end OMAWowii6

theorem OMA.solution : type_of% @WrittenOnTheWallII.GraphConjecture6.conjecture6 := by
  intro α _ _ _ G _ h
  exact OMAWowii6.main G h
