import OMAReductions.R_Erdos151_erdos_151_R2

/-!
# Removing edges from four-cliques in Erdős Problem 151

Separate the case where every four-clique has two edges with no external common
neighbor from the case where three vertices of a four-clique have overlapping
external neighborhoods.
-/

open Finset SimpleGraph
open scoped Classical

namespace OMA.R_Erdos151_erdos_151_R2_H3_R1

private lemma clique_subset_of_pair {V : Type*} (G : SimpleGraph V)
    {K e L : Finset V} (he : e ⊆ K)
    (hclose : ∀ z, (∀ u ∈ e, G.Adj u z) → z ∈ K)
    (hL : G.IsClique (L : Set V)) (heL : e ⊆ L) : L ⊆ K := by
  intro z hz
  by_contra hzK
  refine hzK (hclose z ?_)
  intro u hu
  exact hL (heL hu) hz (fun h => hzK (h ▸ he hu))

private lemma two_pairs {V : Type*} (G : SimpleGraph V)
    (hlocal : ∀ K T : Finset V, G.IsNClique 4 K → T ⊆ K → T.card = 3 →
      ∃ e ⊆ T, e.card = 2 ∧ ∀ z, (∀ u ∈ e, G.Adj u z) → z ∈ K)
    (K : Finset V) (hK : G.IsNClique 4 K) :
    ∃ e : Finset V, e ⊆ K ∧ e.card = 2 ∧
      (∀ z, (∀ u ∈ e, G.Adj u z) → z ∈ K) ∧
      ∃ f : Finset V, f ⊆ K ∧ f.card = 2 ∧ f ≠ e ∧
        ∀ z, (∀ u ∈ f, G.Adj u z) → z ∈ K := by
  classical
  obtain ⟨T, hTK, hT⟩ := exists_subset_card_eq (show 3 ≤ K.card by rw [hK.card_eq]; decide)
  obtain ⟨e, heT, he, heclose⟩ := hlocal K T hK hTK hT
  obtain ⟨x, hx⟩ := card_pos.mp (show 0 < e.card by omega)
  have hxK := hTK (heT hx)
  have hcard : (K.erase x).card = 3 := by rw [card_erase_of_mem hxK, hK.card_eq]
  obtain ⟨f, hfK, hf, hfclose⟩ := hlocal K (K.erase x) hK (erase_subset _ _) hcard
  refine ⟨e, heT.trans hTK, he, heclose, f, hfK.trans (erase_subset _ _), hf, ?_, hfclose⟩
  rintro rfl
  exact (notMem_erase x K) (hfK hx)

private lemma delete_pairs {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : ¬ G.CliqueFree 4)
    (hlocal : ∀ K T : Finset V, G.IsNClique 4 K → T ⊆ K → T.card = 3 →
      ∃ e ⊆ T, e.card = 2 ∧ ∀ z, (∀ u ∈ e, G.Adj u z) → z ∈ K) :
    ∃ F : SimpleGraph V, F ≤ G ∧ F.CliqueFree 4 ∧
      (∀ L, G.IsBigMaximalClique L → ∃ U ⊆ L, F.IsBigMaximalClique U) ∧
      (∃ K e : Finset V, K.card = 4 ∧ e ⊆ K ∧ e.card = 2 ∧
        (∀ x ∈ K, ∀ y ∈ K, x ≠ y → (F.Adj x y ↔ ({x, y} : Finset _) ≠ e)) ∧
        ∀ z, (∀ u ∈ e, F.Adj u z) → z ∈ K) := by
  classical
  let E (K : Finset V) (hK : G.IsNClique 4 K) := (two_pairs G hlocal K hK).choose
  have hE (K : Finset V) (hK : G.IsNClique 4 K) :
      E K hK ⊆ K ∧ (E K hK).card = 2 ∧
      (∀ z, (∀ u ∈ E K hK, G.Adj u z) → z ∈ K) ∧
      ∃ f ⊆ K, f.card = 2 ∧ f ≠ E K hK ∧
        ∀ z, (∀ u ∈ f, G.Adj u z) → z ∈ K :=
    (two_pairs G hlocal K hK).choose_spec
  let F : SimpleGraph V :=
    { Adj := fun x y => G.Adj x y ∧ ∀ K (hK : G.IsNClique 4 K), ({x, y} : Finset V) ≠ E K hK
      symm := ⟨fun x y h => ⟨h.1.symm, fun K hK => by
        simpa only [Finset.pair_comm x y] using h.2 K hK⟩⟩
      loopless := ⟨fun _ h => G.irrefl h.1⟩ }
  have hfG : F ≤ G := fun _ _ h => h.1
  have hkeep {K : Finset V} (hK : G.IsNClique 4 K) {x y : V}
      (hx : x ∈ K) (hy : y ∈ K) (hne : x ≠ y) :
      F.Adj x y ↔ ({x, y} : Finset V) ≠ E K hK := by
    refine ⟨fun h => h.2 K hK, fun h => ⟨hK.1 hx hy hne, ?_⟩⟩
    intro J hJ heq
    have hJK : E J hJ ⊆ K := by rw [← heq]; simp [Finset.insert_subset_iff, hx, hy]
    have hsub : K ⊆ J :=
      clique_subset_of_pair G (hE J hJ).1 (hE J hJ).2.2.1 hK.1 hJK
    have hKJ : K = J := eq_of_subset_of_card_le hsub (by rw [hK.card_eq, hJ.card_eq])
    subst J
    exact h heq
  have hnoPair {K L : Finset V} (hK : G.IsNClique 4 K)
      (hL : F.IsClique (L : Set V)) : ¬ E K hK ⊆ L := by
    intro hs
    obtain ⟨x, y, hxy, heq⟩ := card_eq_two.mp (hE K hK).2.1
    have hx : x ∈ E K hK := by rw [heq]; simp
    have hy : y ∈ E K hK := by rw [heq]; simp
    exact (hL (hs hx) (hs hy) hxy).2 K hK heq.symm
  refine ⟨F, hfG, ?_, ?_, ?_⟩
  · intro K hK
    have hKG : G.IsNClique 4 K :=
      ⟨fun _ hx _ hy hne => hfG (hK.1 hx hy hne), hK.card_eq⟩
    exact hnoPair hKG hK.1 (hE K hKG).1
  · intro L hL
    by_cases hLC : F.IsClique (L : Set V)
    · refine ⟨L, Subset.rfl, ⟨hLC, ?_⟩, hL.2⟩
      intro W hW hLW v hv
      exact hL.1.2 (fun _ hx _ hy hne => hfG (hW hx hy hne)) hLW hv
    · have hmissing : ∃ (K : Finset V) (hK : G.IsNClique 4 K), E K hK ⊆ L := by
        by_contra! hn
        apply hLC
        intro x hx y hy hxy
        refine ⟨hL.1.1 hx hy hxy, ?_⟩
        intro K hK heq
        apply hn K hK
        rw [← heq, Finset.insert_subset_iff, Finset.singleton_subset_iff]
        exact ⟨hx, hy⟩
      obtain ⟨K, hK, heL⟩ := hmissing
      obtain ⟨heK, hecard, heclose, f, hfK, hfcard, hfne, hfclose⟩ := hE K hK
      have hLK := clique_subset_of_pair G heK heclose hL.1.1 heL
      have hEq : K = L := Subset.antisymm
        (fun v hv => hL.1.2 hK.1 hLK hv) hLK
      have hnot : ¬ E K hK ⊆ f := by
        intro hs
        exact hfne (eq_of_subset_of_card_le hs (by omega)).symm
      obtain ⟨x, hx, hxf⟩ := not_subset.mp hnot
      let U := K.erase x
      have hUK : U ⊆ K := erase_subset _ _
      have hUcard : U.card = 3 := by
        rw [card_erase_of_mem (heK hx), hK.card_eq]
      have hU : F.IsClique (U : Set V) := by
        intro a ha b hb hab
        refine (hkeep hK (hUK ha) (hUK hb) hab).mpr ?_
        intro heq
        have hx' : x ∈ ({a, b} : Finset V) := heq.symm ▸ hx
        rcases mem_insert.mp hx' with h | h
        · exact (ne_of_mem_erase ha) h.symm
        · exact (ne_of_mem_erase hb) (mem_singleton.mp h).symm
      refine ⟨U, (by simpa only [hEq] using hUK), ⟨hU, ?_⟩, by omega⟩
      intro W hW hUW z hz
      have hfU : f ⊆ U := fun a ha => mem_erase.mpr
        ⟨fun h => hxf (h ▸ ha), hfK ha⟩
      have hWK := clique_subset_of_pair G hfK hfclose
        (fun _ ha _ hb hab => hfG (hW ha hb hab)) (hfU.trans hUW)
      refine mem_erase.mpr ⟨?_, hWK hz⟩
      intro h
      subst z
      apply hnoPair hK hW
      intro a ha
      by_cases haeq : a = x
      · simpa only [haeq] using hz
      · exact hUW (mem_erase.mpr ⟨haeq, heK ha⟩)
  · obtain ⟨K, hnK⟩ := not_forall.mp hG
    have hK := not_not.mp hnK
    refine ⟨K, E K hK, hK.card_eq, (hE K hK).1, (hE K hK).2.1,
      fun _ hx _ hy hxy => hkeep hK hx hy hxy, ?_⟩
    exact fun z hz => (hE K hK).2.2.1 z (fun u hu => hfG (hz u hu))

private lemma transversal_le_of_refinement {n : ℕ} (G F : SimpleGraph (Fin n))
    (href : ∀ L, G.IsBigMaximalClique L → ∃ U ⊆ L, F.IsBigMaximalClique U) :
    G.cliqueTransversalNumber ≤ F.cliqueTransversalNumber := by
  classical
  have hn : {k | ∃ T : Finset (Fin n), F.IsCliqueTransversal T ∧ T.card = k}.Nonempty := by
    refine ⟨univ.card, univ, ?_, rfl⟩
    intro L hL
    obtain ⟨x, _, hx, _, _⟩ := one_lt_card_iff.mp hL.2
    exact ⟨x, hx, mem_univ x⟩
  obtain ⟨T, hT, hcard⟩ := Nat.sInf_mem hn
  change T.card = F.cliqueTransversalNumber at hcard
  refine csInf_le' ⟨T, ?_, hcard⟩
  intro L hL
  obtain ⟨U, hUL, hU⟩ := href L hL
  obtain ⟨x, hx, hxT⟩ := hT U hU
  exact ⟨x, hUL hx, hxT⟩

private lemma ramsey_mono {a b : ℕ} (hab : a ≤ b) : Erdos151.H a ≤ Erdos151.H b := by
  apply le_csSup
  · refine ⟨b, ?_⟩
    intro j hj
    obtain ⟨S, hS⟩ := hj (⊥ : SimpleGraph (Fin b)) (cliqueFree_bot (by decide))
    simpa only [hS.card_eq, Fintype.card_fin] using card_le_univ S
  · intro G hG
    let e := Fin.castLEEmb hab
    have ht : (G.comap e).CliqueFree 3 := by
      intro T hT
      apply hG (T.map e)
      refine ⟨?_, by rw [card_map, hT.card_eq]⟩
      intro x hx y hy hxy
      obtain ⟨u, hu, rfl⟩ := mem_map.mp hx
      obtain ⟨v, hv, rfl⟩ := mem_map.mp hy
      exact hT.1 hu hv (fun h => hxy (congrArg e h))
    obtain ⟨S, hS⟩ := OMA.R_Erdos151_erdos_151_R2.H_attained (G.comap e) ht
    refine ⟨S.map e, ?_, by rw [card_map, hS.card_eq]⟩
    intro x hx y hy hxy hAdj
    obtain ⟨u, hu, rfl⟩ := mem_map.mp hx
    obtain ⟨v, hv, rfl⟩ := mem_map.mp hy
    exact hS.isIndepSet hu hv (fun h => hxy (congrArg e h)) hAdj

private lemma neighborhood_union_bound {m k : ℕ} (G : SimpleGraph (Fin m))
    (hd : ∀ v, (univ.filter (G.Adj v)).card < k)
    {K T : Finset (Fin m)} (hK : G.IsNClique 4 K) (hTK : T ⊆ K) (hT : T.card = 3)
    (hcommon : ∀ e ⊆ T, e.card = 2 → ∃ z ∉ K, ∀ u ∈ e, G.Adj u z) :
    (K ∪ T.biUnion (fun v => univ.filter (G.Adj v))).card ≤ 3 * k - 10 := by
  classical
  obtain ⟨x, y, w, hxy, hxw, hyw, rfl⟩ := card_eq_three.mp hT
  let N (v : Fin m) := univ.filter (G.Adj v) \ K
  have hN {v : Fin m} (hv : v ∈ K) : (N v).card + 4 ≤ k := by
    have hsub : K.erase v ⊆ (univ.filter (G.Adj v)) ∩ K := by
      intro z hz
      have hzK := mem_of_mem_erase hz
      exact mem_inter.mpr ⟨mem_filter.mpr ⟨mem_univ z,
        hK.1 hv hzK (ne_of_mem_erase hz).symm⟩, hzK⟩
    have hcards := card_le_card hsub
    rw [card_erase_of_mem hv, hK.card_eq] at hcards
    have hsum := card_sdiff_add_card_inter (univ.filter (G.Adj v)) K
    have hdeg := hd v
    dsimp only [N]
    omega
  have hxK : x ∈ K := hTK (by simp)
  have hyK : y ∈ K := hTK (by simp)
  have hwK : w ∈ K := hTK (by simp)
  obtain ⟨a, haK, ha⟩ := hcommon {x, y} (by simp) (by simp [hxy])
  obtain ⟨b, hbK, hb⟩ := hcommon {x, w} (by simp) (by simp [hxw])
  have haX : a ∈ N x := by simpa [N, haK] using ha x (by simp)
  have haY : a ∈ N y := by simpa [N, haK] using ha y (by simp)
  have hbX : b ∈ N x := by simpa [N, hbK] using hb x (by simp)
  have hbW : b ∈ N w := by simpa [N, hbK] using hb w (by simp)
  have hsub : K ∪ ({x, y, w} : Finset _).biUnion (fun v => univ.filter (G.Adj v)) ⊆
      K ∪ (N x ∪ ((N y).erase a ∪ (N w).erase b)) := by
    intro z hz
    rcases mem_union.mp hz with hzK | hzN
    · exact mem_union_left _ hzK
    by_cases hzK : z ∈ K
    · exact mem_union_left _ hzK
    apply mem_union_right
    obtain ⟨v, hv, hzv⟩ := mem_biUnion.mp hzN
    have hmem : z ∈ N v := mem_sdiff.mpr ⟨hzv, hzK⟩
    simp only [mem_insert, mem_singleton] at hv
    rcases hv with rfl | rfl | rfl
    · exact mem_union_left _ hmem
    · by_cases hza : z = a
      · exact mem_union_left _ (hza.symm ▸ haX)
      · exact mem_union_right _ (mem_union_left _ (mem_erase.mpr ⟨hza, hmem⟩))
    · by_cases hzb : z = b
      · exact mem_union_left _ (hzb.symm ▸ hbX)
      · exact mem_union_right _ (mem_union_right _ (mem_erase.mpr ⟨hzb, hmem⟩))
  have houter := (card_le_card hsub).trans
    (card_union_le K (N x ∪ ((N y).erase a ∪ (N w).erase b)))
  have hmid := card_union_le (N x) ((N y).erase a ∪ (N w).erase b)
  have hinner := card_union_le ((N y).erase a) ((N w).erase b)
  rw [card_erase_of_mem haY, card_erase_of_mem hbW] at hinner
  rw [hK.card_eq] at houter
  have hypos := card_pos.mpr ⟨a, haY⟩
  have hwpos := card_pos.mpr ⟨b, hbW⟩
  have hxsize := hN hxK
  have hysize := hN hyK
  have hwsize := hN hwK
  omega

/-- A K₄-free graph left by deleting one edge of each K₄. The missing edge in
one of the resulting diamonds has no common neighbor outside that diamond. -/
def H1 : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin (n + 1))),
    6 ≤ Erdos151.H (n + 1) → Erdos151.H n < Erdos151.H (n + 1) →
    G.CliqueFree 4 →
    (∀ v, (univ.filter (G.Adj v)).card < Erdos151.H (n + 1)) →
    (¬ ∃ F : SimpleGraph (Fin (n + 1)), F.CliqueFree 3 ∧
      ∀ s, G.IsBigMaximalClique s → ∃ u ∈ s, ∃ v ∈ s, F.Adj u v) →
    (∃ K e : Finset (Fin (n + 1)), K.card = 4 ∧ e ⊆ K ∧ e.card = 2 ∧
      (∀ x ∈ K, ∀ y ∈ K, x ≠ y → (G.Adj x y ↔ ({x, y} : Finset _) ≠ e)) ∧
      ∀ z, (∀ u ∈ e, G.Adj u z) → z ∈ K) →
    cliqueTransversalNumber G ≤ (n + 1) - Erdos151.H (n + 1)

/-- A K₄ contains a triangle each of whose edges has an external common neighbor. -/
def H2 : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin (n + 1))),
    6 ≤ Erdos151.H (n + 1) → Erdos151.H n < Erdos151.H (n + 1) →
    (∀ v, (univ.filter (G.Adj v)).card < Erdos151.H (n + 1)) →
    (¬ ∃ F : SimpleGraph (Fin (n + 1)), F.CliqueFree 3 ∧
      ∀ s, G.IsBigMaximalClique s → ∃ u ∈ s, ∃ v ∈ s, F.Adj u v) →
    (∀ K A : Finset (Fin (n + 1)), G.IsClique (K : Set (Fin (n + 1))) → A ⊂ K →
      A.card + Erdos151.H (n + 1 -
        (K ∪ A.biUnion (fun x => univ.filter (G.Adj x))).card) <
        Erdos151.H (n + 1)) →
    (3 + Erdos151.H (n + 1 - (3 * Erdos151.H (n + 1) - 10)) < Erdos151.H (n + 1)) →
    (∃ K T : Finset (Fin (n + 1)), G.IsNClique 4 K ∧ T ⊆ K ∧ T.card = 3 ∧
      ∀ e ⊆ T, e.card = 2 → ∃ z ∉ K, ∀ u ∈ e, G.Adj u z) →
    cliqueTransversalNumber G ≤ (n + 1) - Erdos151.H (n + 1)

theorem main : H1 → H2 → OMA.R_Erdos151_erdos_151_R2.H3 := by
  classical
  intro h1 h2 n G h6 hjump hG hdegree hhitting hexpand
  by_cases hlocal : ∀ K T : Finset (Fin (n + 1)), G.IsNClique 4 K → T ⊆ K → T.card = 3 →
      ∃ e ⊆ T, e.card = 2 ∧ ∀ z, (∀ u ∈ e, G.Adj u z) → z ∈ K
  · obtain ⟨F, hFG, hF, href, hdiamond⟩ := delete_pairs G hG hlocal
    refine (transversal_le_of_refinement G F href).trans
      (h1 n F h6 hjump hF (fun v => ?_) ?_ hdiamond)
    · refine lt_of_le_of_lt (card_le_card ?_) (hdegree v)
      exact fun x hx => mem_filter.mpr ⟨mem_univ x, hFG (mem_filter.mp hx).2⟩
    · rintro ⟨Q, hQ, hhit⟩
      apply hhitting
      refine ⟨Q, hQ, fun L hL => ?_⟩
      obtain ⟨U, hUL, hU⟩ := href L hL
      obtain ⟨x, hx, y, hy, hxy⟩ := hhit U hU
      exact ⟨x, hUL hx, y, hUL hy, hxy⟩
  · push Not at hlocal
    obtain ⟨K, T, hK, hTK, hT, hlocal⟩ := hlocal
    have hdirty (e : Finset (Fin (n + 1))) (heT : e ⊆ T) (he : e.card = 2) :
        ∃ z ∉ K, ∀ u ∈ e, G.Adj u z := by
      obtain ⟨z, hz, hzK⟩ := hlocal e heT he
      exact ⟨z, hzK, hz⟩
    have hproper : T ⊂ K := Finset.ssubset_iff_subset_ne.mpr ⟨hTK, fun h => by
      have hc := congrArg Finset.card h
      rw [hT, hK.card_eq] at hc
      omega⟩
    have hsize := neighborhood_union_bound G hdegree hK hTK hT hdirty
    have hramsey := ramsey_mono (Nat.sub_le_sub_left hsize (n + 1))
    have hstrict := hexpand K T hK.1 hproper
    rw [hT] at hstrict
    exact h2 n G h6 hjump hdegree hhitting hexpand (by omega) ⟨K, T, hK, hTK, hT, hdirty⟩

end OMA.R_Erdos151_erdos_151_R2_H3_R1
