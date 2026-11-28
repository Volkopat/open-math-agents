import OMAReductions.R_ReconstructionConjecture_edge_reconstruction_conjecture_R1

/-!
Proof of Pillar 1 (`OMA.R_ReconstructionConjecture_edge_reconstruction_conjecture_R1.H1`):
Greenwell-Hemminger (1969), Greenwell (1971), and Kelly (1957).
-/

namespace OMA.H1Proof

open Classical SimpleGraph ReconstructionConjecture

section Helpers

private lemma ncard_edgeSet_eq_card_edgeFinset {V : Type*} [Fintype V] (G : SimpleGraph V) :
    G.edgeSet.ncard = G.edgeFinset.card := by
  rw [← G.coe_edgeFinset, Set.ncard_coe_finset]

private lemma four_le_card_of_four_le_edgeFinset {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hE : 4 ≤ G.edgeFinset.card) : 4 ≤ Fintype.card V := by
  have hle : 4 ≤ (Fintype.card V).choose 2 := hE.trans G.card_edgeFinset_le_card_choose_two
  by_contra hlt
  have hlt' : Fintype.card V < 4 := Nat.lt_of_not_le hlt
  interval_cases h : Fintype.card V <;> simp_all [Nat.choose]

private lemma card_edgeFinset_eq_of_iso {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (φ : G ≃g H) :
    G.edgeFinset.card = H.edgeFinset.card := by
  rw [← G.card_edgeSet, ← H.card_edgeSet]
  exact Fintype.card_congr φ.mapEdgeSet

private def iso_deleteEdges_singleton {U V : Type*} {G : SimpleGraph U} {H : SimpleGraph V}
    (φ : G ≃g H) (e : Sym2 U) :
    G.deleteEdges {e} ≃g H.deleteEdges {e.map φ} where
  __ := φ.toEquiv
  map_rel_iff' := fun {a b} => by
    simp only [RelIso.coe_fn_toEquiv, deleteEdges_adj, Set.mem_singleton_iff, φ.map_rel_iff]
    constructor
    · rintro ⟨hadj, hne⟩
      refine ⟨hadj, fun h => hne ?_⟩
      rw [← h, Sym2.map_mk]
    · rintro ⟨hadj, hne⟩
      refine ⟨hadj, fun h => hne ?_⟩
      exact (Sym2.map.injective φ.injective) (by rw [Sym2.map_mk, h])

private def iso_induce_compl_singleton {U V : Type*} {G : SimpleGraph U} {H : SimpleGraph V}
    (φ : G ≃g H) (v : U) :
    G.induce ({v}ᶜ : Set U) ≃g H.induce ({φ v}ᶜ : Set V) where
  __ := Equiv.subtypeEquiv φ.toEquiv (fun x => by simp [φ.injective.eq_iff])
  map_rel_iff' := fun {_ _} => φ.map_rel_iff

private lemma neighborFinset_deleteEdges_singleton {V : Type*} [Fintype V] (G : SimpleGraph V)
    {u v : V} (x : V) :
    (G.deleteEdges {s(u, v)}).neighborFinset x =
      if x = u then (G.neighborFinset u).erase v
      else if x = v then (G.neighborFinset v).erase u
      else G.neighborFinset x := by
  by_cases hxu : x = u
  · subst hxu
    rw [if_pos rfl]
    ext y
    simp only [mem_neighborFinset, deleteEdges_adj, Set.mem_singleton_iff, Finset.mem_erase,
      ne_eq]
    constructor
    · rintro ⟨hadj, hne⟩
      refine ⟨fun hy => hne (by rw [hy]), hadj⟩
    · rintro ⟨hy, hadj⟩
      refine ⟨hadj, fun h => ?_⟩
      rw [Sym2.eq_iff] at h
      rcases h with ⟨_, hyx⟩ | ⟨_, hyx⟩
      · exact hy hyx
      · exact hadj.ne hyx.symm
  · rw [if_neg hxu]
    by_cases hxv : x = v
    · subst hxv
      rw [if_pos rfl]
      ext y
      simp only [mem_neighborFinset, deleteEdges_adj, Set.mem_singleton_iff, Finset.mem_erase,
        ne_eq]
      constructor
      · rintro ⟨hadj, hne⟩
        refine ⟨fun hy => hne (by rw [hy, Sym2.eq_swap]), hadj⟩
      · rintro ⟨hy, hadj⟩
        refine ⟨hadj, fun h => ?_⟩
        rw [Sym2.eq_iff] at h
        rcases h with ⟨hvu, _⟩ | ⟨_, hyu⟩
        · exact hxu hvu
        · exact hy hyu
    · rw [if_neg hxv]
      ext y
      simp only [mem_neighborFinset, deleteEdges_adj, Set.mem_singleton_iff]
      constructor
      · exact fun h => h.1
      · intro hadj
        refine ⟨hadj, fun h => ?_⟩
        rw [Sym2.eq_iff] at h
        rcases h with ⟨hx, _⟩ | ⟨hx, _⟩
        · exact hxu hx
        · exact hxv hx

private lemma degree_deleteEdges_singleton_of_mem {V : Type*} [Fintype V] (G : SimpleGraph V)
    {e : Sym2 V} (he : e ∈ G.edgeFinset) (x : V) :
    (G.deleteEdges {e}).degree x = if x ∈ e then G.degree x - 1 else G.degree x := by
  obtain ⟨u, v, rfl⟩ : ∃ u v, e = s(u, v) := Sym2.ind (fun u v => ⟨u, v, rfl⟩) e
  have hadj : G.Adj u v := (G.mem_edgeFinset).mp he
  have hmemu : v ∈ G.neighborFinset u := (G.mem_neighborFinset u v).mpr hadj
  have hmemv : u ∈ G.neighborFinset v := (G.mem_neighborFinset v u).mpr hadj.symm
  rw [degree, neighborFinset_deleteEdges_singleton]
  by_cases hxu : x = u
  · subst hxu
    rw [if_pos rfl, if_pos (Sym2.mem_mk_left x v), Finset.card_erase_of_mem hmemu,
      card_neighborFinset_eq_degree]
  · rw [if_neg hxu]
    by_cases hxv : x = v
    · subst hxv
      rw [if_pos rfl, if_pos (Sym2.mem_mk_right u x), Finset.card_erase_of_mem hmemv,
        card_neighborFinset_eq_degree]
    · have hnot : x ∉ s(u, v) := by
        rw [Sym2.mem_iff]
        tauto
      rw [if_neg hxv, if_neg hnot, card_neighborFinset_eq_degree]

private lemma degree_eq_zero_iff_not_adj {V : Type*} [Fintype V] (G : SimpleGraph V) (v : V)
    [Fintype (G.neighborSet v)] :
    G.degree v = 0 ↔ ∀ u : V, ¬ G.Adj v u := by
  rw [← G.card_neighborFinset_eq_degree, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  simp only [mem_neighborFinset]

private lemma degree_pos_iff_exists_adj {V : Type*} [Fintype V] (G : SimpleGraph V) (v : V)
    [Fintype (G.neighborSet v)] :
    0 < G.degree v ↔ ∃ u : V, G.Adj v u := by
  have := degree_eq_zero_iff_not_adj G v
  constructor
  · intro h
    by_contra hno
    push Not at hno
    have := this.mpr hno
    omega
  · rintro ⟨u, hu⟩
    by_contra h0
    have hle : G.degree v = 0 := by omega
    exact (this.mp hle u) hu

private lemma exists_bij_of_rel_counts {α β : Type*} [Fintype α] [Fintype β]
    (s : Finset α) (t : Finset β)
    (EA : α → α → Prop) (EB : β → β → Prop) (E : α → β → Prop)
    (hEA_refl : ∀ a, EA a a)
    (hEB_refl : ∀ b, EB b b)
    (hEA_symm : ∀ {a1 a2}, EA a1 a2 → EA a2 a1)
    (hEB_symm : ∀ {b1 b2}, EB b1 b2 → EB b2 b1)
    (h_tr1 : ∀ {a1 a2 b}, EA a1 a2 → E a2 b → E a1 b)
    (h_tr2 : ∀ {a b1 b2}, E a b1 → EB b1 b2 → E a b2)
    (h_tr3 : ∀ {a1 a2 b}, E a1 b → E a2 b → EA a1 a2)
    (h_tr4 : ∀ {a b1 b2}, E a b1 → E a b2 → EB b1 b2)
    (h_leA : ∀ a ∈ s, (s.filter (fun a' => EA a a')).card ≤ (t.filter (fun b => E a b)).card)
    (h_leB : ∀ b ∈ t, (t.filter (fun b' => EB b b')).card ≤ (s.filter (fun a => E a b)).card) :
    ∃ f : s ≃ t, ∀ x : s, E x.1 (f x).1 := by
  have main : ∀ n : ℕ, ∀ (s : Finset α) (t : Finset β), s.card = n →
      (∀ a ∈ s, (s.filter (fun a' => EA a a')).card ≤ (t.filter (fun b => E a b)).card) →
      (∀ b ∈ t, (t.filter (fun b' => EB b b')).card ≤ (s.filter (fun a => E a b)).card) →
      ∃ f : s ≃ t, ∀ x : s, E x.1 (f x).1 := by
    intro n
    induction n with
    | zero =>
      intro s t hs_card _ hB
      have hs_empty : s = ∅ := Finset.card_eq_zero.mp hs_card
      have ht_empty : t = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro b hb
        have hpos : 1 ≤ (t.filter (fun b' => EB b b')).card :=
          Finset.card_pos.mpr ⟨b, Finset.mem_filter.mpr ⟨hb, hEB_refl b⟩⟩
        have hle := hB b hb
        rw [hs_empty, Finset.filter_empty, Finset.card_empty] at hle
        omega
      subst hs_empty ht_empty
      exact ⟨Equiv.equivOfIsEmpty _ _, fun x => False.elim (Finset.notMem_empty x.1 x.2)⟩
    | succ n ih =>
      intro s t hs_card hA hB
      have hs_ne : s.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨a, ha⟩ := hs_ne
      have hpos : 1 ≤ (t.filter (fun b => E a b)).card := by
        have ha1 : 1 ≤ (s.filter (fun a' => EA a a')).card :=
          Finset.card_pos.mpr ⟨a, Finset.mem_filter.mpr ⟨ha, hEA_refl a⟩⟩
        exact ha1.trans (hA a ha)
      obtain ⟨b, hb_mem⟩ := Finset.card_pos.mp hpos
      rw [Finset.mem_filter] at hb_mem
      obtain ⟨hb, hab⟩ := hb_mem
      let s' := s.erase a
      let t' := t.erase b
      have hs'_card : s'.card = n := by
        rw [Finset.card_erase_of_mem ha, hs_card]
        simp
      have hA' : ∀ a' ∈ s', (s'.filter (fun x => EA a' x)).card ≤ (t'.filter (fun y => E a' y)).card := by
        intro a' ha'
        have ha'_s : a' ∈ s := Finset.mem_of_mem_erase ha'
        have h_orig := hA a' ha'_s
        by_cases hrel : EA a a'
        · have ha_in : a ∈ s.filter (fun x => EA a' x) :=
            Finset.mem_filter.mpr ⟨ha, hEA_symm hrel⟩
          have hb_in : b ∈ t.filter (fun y => E a' y) :=
            Finset.mem_filter.mpr ⟨hb, h_tr1 (hEA_symm hrel) hab⟩
          have hs_eq : s'.filter (fun x => EA a' x) = (s.filter (fun x => EA a' x)).erase a := by
            ext x
            simp only [s', Finset.mem_filter, Finset.mem_erase]
            tauto
          have ht_eq : t'.filter (fun y => E a' y) = (t.filter (fun y => E a' y)).erase b := by
            ext y
            simp only [t', Finset.mem_filter, Finset.mem_erase]
            tauto
          rw [hs_eq, ht_eq, Finset.card_erase_of_mem ha_in, Finset.card_erase_of_mem hb_in]
          omega
        · have ha_not : a ∉ s.filter (fun x => EA a' x) := by
            intro hmem
            exact hrel (hEA_symm (Finset.mem_filter.mp hmem).2)
          have hb_not : b ∉ t.filter (fun y => E a' y) := by
            intro hmem
            exact hrel (h_tr3 hab (Finset.mem_filter.mp hmem).2)
          have hs_eq : s'.filter (fun x => EA a' x) = s.filter (fun x => EA a' x) := by
            ext x
            simp only [s', Finset.mem_filter, Finset.mem_erase]
            constructor
            · rintro ⟨⟨_, hx⟩, hrel'⟩; exact ⟨hx, hrel'⟩
            · rintro ⟨hx, hrel'⟩
              refine ⟨⟨fun hxa => ha_not (Finset.mem_filter.mpr ⟨ha, hxa ▸ hrel'⟩), hx⟩, hrel'⟩
          have ht_eq : t'.filter (fun y => E a' y) = t.filter (fun y => E a' y) := by
            ext y
            simp only [t', Finset.mem_filter, Finset.mem_erase]
            constructor
            · rintro ⟨⟨_, hy⟩, hrel'⟩; exact ⟨hy, hrel'⟩
            · rintro ⟨hy, hrel'⟩
              refine ⟨⟨fun hyb => hb_not (Finset.mem_filter.mpr ⟨hb, hyb ▸ hrel'⟩), hy⟩, hrel'⟩
          rw [hs_eq, ht_eq]
          exact h_orig
      have hB' : ∀ b' ∈ t', (t'.filter (fun y => EB b' y)).card ≤ (s'.filter (fun x => E x b')).card := by
        intro b' hb'
        have hb'_t : b' ∈ t := Finset.mem_of_mem_erase hb'
        have h_orig := hB b' hb'_t
        by_cases hrel : EB b b'
        · have hb_in : b ∈ t.filter (fun y => EB b' y) :=
            Finset.mem_filter.mpr ⟨hb, hEB_symm hrel⟩
          have ha_in : a ∈ s.filter (fun x => E x b') :=
            Finset.mem_filter.mpr ⟨ha, h_tr2 hab hrel⟩
          have ht_eq : t'.filter (fun y => EB b' y) = (t.filter (fun y => EB b' y)).erase b := by
            ext y
            simp only [t', Finset.mem_filter, Finset.mem_erase]
            tauto
          have hs_eq : s'.filter (fun x => E x b') = (s.filter (fun x => E x b')).erase a := by
            ext x
            simp only [s', Finset.mem_filter, Finset.mem_erase]
            tauto
          rw [ht_eq, hs_eq, Finset.card_erase_of_mem hb_in, Finset.card_erase_of_mem ha_in]
          omega
        · have hb_not : b ∉ t.filter (fun y => EB b' y) := by
            intro hmem
            exact hrel (hEB_symm (Finset.mem_filter.mp hmem).2)
          have ha_not : a ∉ s.filter (fun x => E x b') := by
            intro hmem
            exact hrel (h_tr4 hab (Finset.mem_filter.mp hmem).2)
          have ht_eq : t'.filter (fun y => EB b' y) = t.filter (fun y => EB b' y) := by
            ext y
            simp only [t', Finset.mem_filter, Finset.mem_erase]
            constructor
            · rintro ⟨⟨_, hy⟩, hrel'⟩; exact ⟨hy, hrel'⟩
            · rintro ⟨hy, hrel'⟩
              refine ⟨⟨fun hyb => hb_not (Finset.mem_filter.mpr ⟨hb, hyb ▸ hrel'⟩), hy⟩, hrel'⟩
          have hs_eq : s'.filter (fun x => E x b') = s.filter (fun x => E x b') := by
            ext x
            simp only [s', Finset.mem_filter, Finset.mem_erase]
            constructor
            · rintro ⟨⟨_, hx⟩, hrel'⟩; exact ⟨hx, hrel'⟩
            · rintro ⟨hx, hrel'⟩
              refine ⟨⟨fun hxa => ha_not (Finset.mem_filter.mpr ⟨ha, hxa ▸ hrel'⟩), hx⟩, hrel'⟩
          rw [ht_eq, hs_eq]
          exact h_orig
      obtain ⟨f', hf'⟩ := ih s' t' hs'_card hA' hB'
      refine ⟨{
        toFun := fun x =>
          if hxa : x.1 = a then ⟨b, hb⟩
          else ⟨(f' ⟨x.1, Finset.mem_erase.mpr ⟨hxa, x.2⟩⟩).1,
            Finset.mem_of_mem_erase (f' ⟨x.1, Finset.mem_erase.mpr ⟨hxa, x.2⟩⟩).2⟩
        invFun := fun y =>
          if hyb : y.1 = b then ⟨a, ha⟩
          else ⟨(f'.symm ⟨y.1, Finset.mem_erase.mpr ⟨hyb, y.2⟩⟩).1,
            Finset.mem_of_mem_erase (f'.symm ⟨y.1, Finset.mem_erase.mpr ⟨hyb, y.2⟩⟩).2⟩
        left_inv := fun x => by
          by_cases hxa : x.1 = a
          · simp only [dif_pos hxa]
            exact Subtype.ext hxa.symm
          · simp only [dif_neg hxa]
            have hne : (f' ⟨x.1, Finset.mem_erase.mpr ⟨hxa, x.2⟩⟩).1 ≠ b :=
              (Finset.mem_erase.mp (f' ⟨x.1, Finset.mem_erase.mpr ⟨hxa, x.2⟩⟩).2).1
            simp only [dif_neg hne, Subtype.coe_eta, Equiv.symm_apply_apply]
        right_inv := fun y => by
          by_cases hyb : y.1 = b
          · simp only [dif_pos hyb]
            exact Subtype.ext hyb.symm
          · simp only [dif_neg hyb]
            have hne : (f'.symm ⟨y.1, Finset.mem_erase.mpr ⟨hyb, y.2⟩⟩).1 ≠ a :=
              (Finset.mem_erase.mp (f'.symm ⟨y.1, Finset.mem_erase.mpr ⟨hyb, y.2⟩⟩).2).1
            simp only [dif_neg hne, Subtype.coe_eta, Equiv.apply_symm_apply]
      }, fun x => ?_⟩
      by_cases hxa : x.1 = a
      · simp only [Equiv.coe_fn_mk, dif_pos hxa, hxa]
        exact hab
      · simp only [Equiv.coe_fn_mk, dif_neg hxa]
        exact hf' ⟨x.1, Finset.mem_erase.mpr ⟨hxa, x.2⟩⟩
  exact main s.card s t rfl h_leA h_leB

end Helpers

section DegreeSequence

private noncomputable def degCount {V : Type*} [Fintype V] (G : SimpleGraph V) (k : ℕ) : ℕ :=
  (Finset.univ.filter fun v : V => G.degree v = k).card

private lemma degCount_eq_of_iso {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (φ : G ≃g H) (k : ℕ) :
    degCount G k = degCount H k := by
  unfold degCount
  refine Finset.card_bij (fun v _ => φ v) (fun v hv => ?_) (fun _ _ _ _ h => φ.injective h) ?_
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    rw [φ.degree_eq v, hv]
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
    refine ⟨φ.symm w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, φ.apply_symm_apply w⟩
    rw [φ.symm.degree_eq w, hw]

private lemma degree_le_card_edgeFinset {V : Type*} [Fintype V] (G : SimpleGraph V) (v : V) :
    G.degree v ≤ G.edgeFinset.card := by
  rw [← G.card_incidenceFinset_eq_degree]
  exact Finset.card_le_card (G.incidenceFinset_subset v)

private lemma degCount_eq_zero_of_lt {V : Type*} [Fintype V] (G : SimpleGraph V) {k : ℕ}
    (hk : G.edgeFinset.card < k) : degCount G k = 0 := by
  rw [degCount, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro v hv
  rw [Finset.mem_filter] at hv
  have hle := degree_le_card_edgeFinset G v
  omega

private lemma sum_degCount_deleteEdges {V : Type*} [Fintype V] (G : SimpleGraph V) (k : ℕ) :
    ∑ e ∈ G.edgeFinset, degCount (G.deleteEdges {e}) k =
      (G.edgeFinset.card - k) * degCount G k + (k + 1) * degCount G (k + 1) := by
  have hswap : ∑ e ∈ G.edgeFinset, degCount (G.deleteEdges {e}) k =
      ∑ v : V, ∑ e ∈ G.edgeFinset, (if (G.deleteEdges {e}).degree v = k then (1 : ℕ) else 0) := by
    simp_rw [degCount, Finset.card_filter]
    convert Finset.sum_comm (s := G.edgeFinset) (t := (Finset.univ : Finset V))
      (f := fun e v => if (G.deleteEdges {e}).degree v = k then (1 : ℕ) else 0)
  rw [hswap]
  have hterm : ∀ v : V,
      ∑ e ∈ G.edgeFinset, (if (G.deleteEdges {e}).degree v = k then (1 : ℕ) else 0) =
        (if G.degree v = k then G.edgeFinset.card - k else 0) +
        (if G.degree v = k + 1 then k + 1 else 0) := by
    intro v
    have hsdiff := Finset.sum_sdiff (G.incidenceFinset_subset v)
      (f := fun e => if (G.deleteEdges {e}).degree v = k then (1 : ℕ) else 0)
    rw [← hsdiff]
    have h1 : ∑ e ∈ G.edgeFinset \ G.incidenceFinset v,
        (if (G.deleteEdges {e}).degree v = k then (1 : ℕ) else 0) =
        (G.edgeFinset.card - G.degree v) * (if G.degree v = k then 1 else 0) := by
      have hcongr : ∀ e ∈ G.edgeFinset \ G.incidenceFinset v,
          (if (G.deleteEdges {e}).degree v = k then (1 : ℕ) else 0) =
            (if G.degree v = k then 1 else 0) := by
        intro e he
        rw [Finset.mem_sdiff] at he
        rw [degree_deleteEdges_singleton_of_mem G he.1 v]
        have hnot : v ∉ e := by
          intro hv
          apply he.2
          rw [G.incidenceFinset_eq_filter]
          exact Finset.mem_filter.mpr ⟨he.1, hv⟩
        rw [if_neg hnot]
      rw [Finset.sum_congr rfl hcongr, Finset.sum_const, smul_eq_mul,
        Finset.card_sdiff_of_subset (G.incidenceFinset_subset v), G.card_incidenceFinset_eq_degree]
    have h2 : ∑ e ∈ G.incidenceFinset v,
        (if (G.deleteEdges {e}).degree v = k then (1 : ℕ) else 0) =
        G.degree v * (if G.degree v - 1 = k then 1 else 0) := by
      have hcongr : ∀ e ∈ G.incidenceFinset v,
          (if (G.deleteEdges {e}).degree v = k then (1 : ℕ) else 0) =
            (if G.degree v - 1 = k then 1 else 0) := by
        intro e he
        have heE : e ∈ G.edgeFinset := G.incidenceFinset_subset v he
        rw [degree_deleteEdges_singleton_of_mem G heE v]
        rw [G.incidenceFinset_eq_filter, Finset.mem_filter] at he
        rw [if_pos he.2]
      rw [Finset.sum_congr rfl hcongr, Finset.sum_const, smul_eq_mul, G.card_incidenceFinset_eq_degree]
    rw [h1, h2]
    split_ifs <;> (try simp only [mul_one, mul_zero, add_zero, zero_add]) <;> omega
  simp_rw [hterm, Finset.sum_add_distrib]
  have ha : ∑ v : V, (if G.degree v = k then G.edgeFinset.card - k else 0) =
      (G.edgeFinset.card - k) * degCount G k := by
    rw [degCount, Finset.card_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    split_ifs <;> simp
  have hb : ∑ v : V, (if G.degree v = k + 1 then k + 1 else 0) =
      (k + 1) * degCount G (k + 1) := by
    rw [degCount, Finset.card_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    split_ifs <;> simp
  rw [ha, hb]

private lemma degCount_pred_lt {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hm : 4 ≤ G.edgeFinset.card) : degCount G (G.edgeFinset.card - 1) < G.edgeFinset.card := by
  let m := G.edgeFinset.card
  have hsum : (m - 1) * degCount G (m - 1) ≤ 2 * m := by
    calc (m - 1) * degCount G (m - 1)
        = ∑ _v ∈ Finset.univ.filter (fun v : V => G.degree v = m - 1), (m - 1) := by
            rw [degCount, Finset.sum_const, smul_eq_mul, mul_comm]
      _ = ∑ v ∈ Finset.univ.filter (fun v : V => G.degree v = m - 1), G.degree v := by
            refine Finset.sum_congr rfl fun v hv => ?_
            rw [(Finset.mem_filter.mp hv).2]
      _ ≤ ∑ v : V, G.degree v := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      _ = 2 * m := G.sum_degrees_eq_twice_card_edges
  by_contra hge
  have hge' : m ≤ degCount G (m - 1) := Nat.le_of_not_lt hge
  have hmul : (m - 1) * m ≤ (m - 1) * degCount G (m - 1) := Nat.mul_le_mul_left _ hge'
  have hm4 : 4 ≤ m := hm
  have h3m : 3 * m ≤ (m - 1) * m := Nat.mul_le_mul_right m (by omega)
  omega

private lemma degCount_eq_of_edgeHypomorphic {V : Type*} [Fintype V]
    (G H : SimpleGraph V) (hE : 4 ≤ G.edgeFinset.card) (hEH : EdgeHypomorphic G H) :
    ∀ k : ℕ, degCount G k = degCount H k := by
  obtain ⟨σ, hσ⟩ := hEH
  have hm_eq : G.edgeFinset.card = H.edgeFinset.card := by
    rw [← G.card_edgeSet, ← H.card_edgeSet]
    exact Fintype.card_congr σ
  let m := G.edgeFinset.card
  have hsum_eq : ∀ k : ℕ,
      (m - k) * degCount G k + (k + 1) * degCount G (k + 1) =
        (m - k) * degCount H k + (k + 1) * degCount H (k + 1) := by
    intro k
    have h1 := sum_degCount_deleteEdges G k
    have h2 := sum_degCount_deleteEdges H k
    rw [← hm_eq] at h2
    rw [← h1, ← h2]
    refine Finset.sum_bij (fun e _ => (σ ⟨e, (G.mem_edgeFinset).mp ‹_›⟩).val) ?_ ?_ ?_ ?_
    · intro e he
      exact (H.mem_edgeFinset).mpr (σ ⟨e, (G.mem_edgeFinset).mp he⟩).prop
    · intro e1 he1 e2 he2 heq
      have hinj : (⟨e1, (G.mem_edgeFinset).mp he1⟩ : G.edgeSet) = ⟨e2, (G.mem_edgeFinset).mp he2⟩ :=
        σ.injective (Subtype.ext heq)
      exact congrArg Subtype.val hinj
    · intro e' he'
      let e'sub : H.edgeSet := ⟨e', (H.mem_edgeFinset).mp he'⟩
      refine ⟨(σ.symm e'sub).val, (G.mem_edgeFinset).mpr (σ.symm e'sub).prop, ?_⟩
      change (σ (σ.symm e'sub)).val = e'
      rw [σ.apply_symm_apply]
    · intro e he
      obtain ⟨φ⟩ := hσ ⟨e, (G.mem_edgeFinset).mp he⟩
      exact degCount_eq_of_iso φ k
  have htop := hsum_eq (m - 1)
  have hm1 : (m - (m - 1)) = 1 := by omega
  have hm2 : m - 1 + 1 = m := by omega
  rw [hm1, hm2, one_mul, one_mul] at htop
  have hltG : degCount G (m - 1) < m := degCount_pred_lt G hE
  have hltH : degCount H (m - 1) < m := by
    have := degCount_pred_lt H (hm_eq ▸ hE)
    rwa [← hm_eq] at this
  have hm_top : degCount G m = degCount H m := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have : degCount G (m - 1) + m * degCount G m < m * (degCount G m + 1) := by nlinarith
      have : m * (degCount G m + 1) ≤ m * degCount H m := Nat.mul_le_mul_left m hlt
      omega
    · have : degCount H (m - 1) + m * degCount H m < m * (degCount H m + 1) := by nlinarith
      have : m * (degCount H m + 1) ≤ m * degCount G m := Nat.mul_le_mul_left m hgt
      omega
  have hm_pred : degCount G (m - 1) = degCount H (m - 1) := by
    rw [hm_top] at htop
    omega
  have hdown : ∀ j : ℕ, ∀ k : ℕ, m - 1 - j ≤ k → degCount G k = degCount H k := by
    intro j
    induction j with
    | zero =>
      intro k hk
      by_cases h1 : k = m - 1
      · exact h1 ▸ hm_pred
      · by_cases h2 : k = m
        · exact h2 ▸ hm_top
        · have hgt : m < k := by omega
          rw [degCount_eq_zero_of_lt G hgt, degCount_eq_zero_of_lt H (hm_eq ▸ hgt)]
    | succ j ih =>
      intro k hk
      by_cases h1 : m - 1 - j ≤ k
      · exact ih k h1
      · have hkeq : k = m - 1 - (j + 1) := by omega
        have hklt : k < m := by omega
        have hk1 : m - 1 - j ≤ k + 1 := by omega
        have ih_next := ih (k + 1) hk1
        have heq := hsum_eq k
        rw [ih_next] at heq
        have hmul_eq : (m - k) * degCount G k = (m - k) * degCount H k := by omega
        exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < m - k) hmul_eq
  intro k
  exact hdown (m - 1) k (by omega)

end DegreeSequence

section StripIsolates

private lemma edgeSet_equiv_induce_posDeg {V : Type*} [Fintype V] (G : SimpleGraph V) :
    ∃ ι : (G.induce {v : V | 0 < G.degree v}).edgeSet ≃ G.edgeSet,
      ∀ e', (ι e').val = e'.val.map Subtype.val := by
  let S : Set V := {v : V | 0 < G.degree v}
  let f : (G.induce S).edgeSet → G.edgeSet := fun e' => ⟨e'.val.map Subtype.val, by
    obtain ⟨e', he'⟩ := e'
    obtain ⟨a, b, rfl⟩ : ∃ a b, e' = s(a, b) := Sym2.ind (fun a b => ⟨a, b, rfl⟩) e'
    exact he'⟩
  have hbij : Function.Bijective f := by
    constructor
    · intro e1 e2 heq
      apply Subtype.ext
      exact (Sym2.map.injective Subtype.val_injective) (congrArg Subtype.val heq)
    · intro e
      obtain ⟨e_val, he⟩ := e
      obtain ⟨a, b, rfl⟩ : ∃ a b, e_val = s(a, b) := Sym2.ind (fun a b => ⟨a, b, rfl⟩) e_val
      have hadj : G.Adj a b := he
      have ha : a ∈ S := (degree_pos_iff_exists_adj G a).mpr ⟨b, hadj⟩
      have hb : b ∈ S := (degree_pos_iff_exists_adj G b).mpr ⟨a, hadj.symm⟩
      refine ⟨⟨s(⟨a, ha⟩, ⟨b, hb⟩), hadj⟩, rfl⟩
  exact ⟨Equiv.ofBijective f hbij, fun _ => rfl⟩

private lemma strip_isolated_vertices {V : Type} [Fintype V]
    (G H : SimpleGraph V) (hE : 4 ≤ G.edgeFinset.card) (hEH : EdgeHypomorphic G H) :
    ∃ (W : Type) (_ : Fintype W) (G' H' : SimpleGraph W),
      4 ≤ Fintype.card W ∧ 4 ≤ G'.edgeFinset.card ∧
      (∀ w : W, ∃ u : W, G'.Adj w u) ∧ (∀ w : W, ∃ u : W, H'.Adj w u) ∧
      EdgeHypomorphic G' H' ∧ (Nonempty (G' ≃g H') → Nonempty (G ≃g H)) := by
  have hdeg := degCount_eq_of_edgeHypomorphic G H hE hEH
  let SG : Set V := {v : V | 0 < G.degree v}
  let SH : Set V := {v : V | 0 < H.degree v}
  let WG : Finset V := Finset.univ.filter fun v : V => 0 < G.degree v
  let WH : Finset V := Finset.univ.filter fun v : V => 0 < H.degree v
  let XG : Finset V := Finset.univ.filter fun v : V => G.degree v = 0
  let XH : Finset V := Finset.univ.filter fun v : V => H.degree v = 0
  have hX_card : XG.card = XH.card := hdeg 0
  have hWG_part : WG.card + XG.card = Fintype.card V := by
    have hdisj : Disjoint WG XG := by
      rw [Finset.disjoint_left]
      intro v hv1 hv2
      rw [Finset.mem_filter] at hv1 hv2
      omega
    have hunion : WG ∪ XG = Finset.univ := by
      ext v
      simp only [WG, XG, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      omega
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ]
  have hWH_part : WH.card + XH.card = Fintype.card V := by
    have hdisj : Disjoint WH XH := by
      rw [Finset.disjoint_left]
      intro v hv1 hv2
      rw [Finset.mem_filter] at hv1 hv2
      omega
    have hunion : WH ∪ XH = Finset.univ := by
      ext v
      simp only [WH, XH, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      omega
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ]
  have hW_card : WG.card = WH.card := by omega
  let W : Type := {v : V // v ∈ SG}
  have hcard_SG : Fintype.card W = WG.card := by
    rw [Fintype.card_subtype]
    congr 1
  have hcard_SH : Fintype.card {v : V // v ∈ SH} = WH.card := by
    rw [Fintype.card_subtype]
    congr 1
  have eW : W ≃ {v : V // v ∈ SH} := Fintype.equivOfCardEq (by rw [hcard_SG, hcard_SH, hW_card])
  let G' : SimpleGraph W := G.induce SG
  let Hsub : SimpleGraph {v : V // v ∈ SH} := H.induce SH
  let H' : SimpleGraph W := Hsub.comap eW
  have hG'_iso_free : ∀ w : W, ∃ u : W, G'.Adj w u := by
    intro w
    obtain ⟨u, hu⟩ := (degree_pos_iff_exists_adj G w.1).mp w.2
    have hupos : u ∈ SG := (degree_pos_iff_exists_adj G u).mpr ⟨w.1, hu.symm⟩
    exact ⟨⟨u, hupos⟩, hu⟩
  have hH'_iso_free : ∀ w : W, ∃ u : W, H'.Adj w u := by
    intro w
    obtain ⟨u, hu⟩ := (degree_pos_iff_exists_adj H (eW w).1).mp (eW w).2
    have hupos : u ∈ SH := (degree_pos_iff_exists_adj H u).mpr ⟨(eW w).1, hu.symm⟩
    let u' : {v : V // v ∈ SH} := ⟨u, hupos⟩
    refine ⟨eW.symm u', ?_⟩
    change H.Adj (eW w).1 (eW (eW.symm u')).1
    rw [Equiv.apply_symm_apply]
    exact hu
  obtain ⟨ιG, hιG⟩ := edgeSet_equiv_induce_posDeg G
  obtain ⟨ιH0, hιH0⟩ := edgeSet_equiv_induce_posDeg H
  let φH : H' ≃g Hsub := Iso.comap eW Hsub
  let ιH : H'.edgeSet ≃ H.edgeSet := φH.mapEdgeSet.trans ιH0
  have hιH : ∀ f' : H'.edgeSet, (ιH f').val = (f'.val.map eW).map Subtype.val := by
    intro f'
    change (ιH0 (φH.mapEdgeSet f')).val = _
    rw [hιH0]
    rfl
  have hG'_edge : G'.edgeFinset.card = G.edgeFinset.card := by
    rw [← G'.card_edgeSet, ← G.card_edgeSet]
    exact Fintype.card_congr ιG
  have hE' : 4 ≤ G'.edgeFinset.card := hG'_edge ▸ hE
  have h4W : 4 ≤ Fintype.card W := four_le_card_of_four_le_edgeFinset G' hE'
  have hEH' : EdgeHypomorphic G' H' := by
    obtain ⟨σ, hσ⟩ := hEH
    let σ' : G'.edgeSet ≃ H'.edgeSet := ιG.trans (σ.trans ιH.symm)
    refine ⟨σ', fun e' => ?_⟩
    let e : G.edgeSet := ιG e'
    let f : H.edgeSet := σ e
    let f' : H'.edgeSet := σ' e'
    have hf'_eq : ιH f' = f := by
      change ιH (ιH.symm (σ (ιG e'))) = σ (ιG e')
      exact ιH.apply_symm_apply _
    obtain ⟨ψ⟩ := hσ e
    let Gd := G.deleteEdges {e.val}
    let Hd := H.deleteEdges {f.val}
    let IG : Finset V := Finset.univ.filter fun v : V => Gd.degree v = 0
    let IH : Finset V := Finset.univ.filter fun v : V => Hd.degree v = 0
    have hI_card : IG.card = IH.card := by
      refine Finset.card_bij (fun v _ => ψ v) (fun v hv => ?_)
        (fun _ _ _ _ h => ψ.injective h) (fun w hw => ?_)
      · simp only [IG, IH, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
        have hdeg : Gd.degree v = Hd.degree (ψ v) := by convert (ψ.degree_eq v).symm
        rw [← hdeg, hv]
      · simp only [IG, IH, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
        refine ⟨ψ.symm w, ?_, ψ.apply_symm_apply w⟩
        have hdeg : Gd.degree (ψ.symm w) = Hd.degree w := by
          have h1 := ψ.degree_eq (ψ.symm w)
          rw [ψ.apply_symm_apply] at h1
          convert h1.symm
        rw [hdeg, hw]
    have hXG_sub : XG ⊆ IG := by
      intro v hv
      rw [Finset.mem_filter] at hv ⊢
      refine ⟨Finset.mem_univ v, ?_⟩
      have h0 : G.degree v = 0 := hv.2
      have hle : Gd.degree v ≤ G.degree v := degree_le_of_le (deleteEdges_le _)
      omega
    have hXH_sub : XH ⊆ IH := by
      intro v hv
      rw [Finset.mem_filter] at hv ⊢
      refine ⟨Finset.mem_univ v, ?_⟩
      have h0 : H.degree v = 0 := hv.2
      have hle : Hd.degree v ≤ H.degree v := degree_le_of_le (deleteEdges_le _)
      omega
    have hDiff_card : (IG \ XG).card = (IH \ XH).card := by
      rw [Finset.card_sdiff_of_subset hXG_sub, Finset.card_sdiff_of_subset hXH_sub, hI_card, hX_card]
    let β : {v : V // v ∈ IG \ XG} ≃ {v : V // v ∈ IH \ XH} :=
      Fintype.equivOfCardEq (by simp only [Fintype.card_coe]; exact hDiff_card)
    have hψ_mem_IH : ∀ v : V, v ∈ IG ↔ ψ v ∈ IH := by
      intro v
      simp only [IG, IH, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [ψ.degree_eq v]
    have hw_not_XG : ∀ w : W, w.1 ∉ XG := by
      intro w hmem
      have h1 : 0 < G.degree w.1 := w.2
      have h2 := (Finset.mem_filter.mp hmem).2
      omega
    have hu_not_XH : ∀ u : {v : V // v ∈ SH}, u.1 ∉ XH := by
      intro u hmem
      have h1 : 0 < H.degree u.1 := u.2
      have h2 := (Finset.mem_filter.mp hmem).2
      omega
    have hXH_iff : ∀ v : V, v ∉ XH ↔ v ∈ SH := by
      intro v
      simp only [XH, SH, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
      omega
    have hXG_iff : ∀ v : V, v ∉ XG ↔ v ∈ SG := by
      intro v
      simp only [XG, SG, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
      omega
    let toHsub : W → {v : V // v ∈ SH} := fun w =>
      if h : w.1 ∈ IG then
        ⟨(β ⟨w.1, Finset.mem_sdiff.mpr ⟨h, hw_not_XG w⟩⟩).1,
          (hXH_iff _).mp (Finset.mem_sdiff.mp (β ⟨w.1, Finset.mem_sdiff.mpr ⟨h, hw_not_XG w⟩⟩).2).2⟩
      else
        ⟨ψ w.1, (hXH_iff _).mp fun hmem => h ((hψ_mem_IH w.1).mpr (hXH_sub hmem))⟩
    let ofHsub : {v : V // v ∈ SH} → W := fun u =>
      if h : u.1 ∈ IH then
        ⟨(β.symm ⟨u.1, Finset.mem_sdiff.mpr ⟨h, hu_not_XH u⟩⟩).1,
          (hXG_iff _).mp (Finset.mem_sdiff.mp (β.symm ⟨u.1, Finset.mem_sdiff.mpr ⟨h, hu_not_XH u⟩⟩).2).2⟩
      else
        ⟨ψ.symm u.1, (hXG_iff _).mp fun hmem => h (by
          have h1 := (hψ_mem_IH (ψ.symm u.1)).mp (hXG_sub hmem)
          rwa [ψ.apply_symm_apply] at h1)⟩
    have h_left : Function.LeftInverse ofHsub toHsub := by
      intro w
      dsimp only [toHsub, ofHsub]
      by_cases h : w.1 ∈ IG
      · rw [dif_pos h]
        let bw := β ⟨w.1, Finset.mem_sdiff.mpr ⟨h, hw_not_XG w⟩⟩
        have hmem : bw.1 ∈ IH := (Finset.mem_sdiff.mp bw.2).1
        have hnotX : bw.1 ∉ XH := (Finset.mem_sdiff.mp bw.2).2
        rw [dif_pos hmem]
        apply Subtype.ext
        have hsub : (⟨bw.1, Finset.mem_sdiff.mpr ⟨hmem, hnotX⟩⟩ : {v : V // v ∈ IH \ XH}) = bw :=
          Subtype.ext rfl
        rw [hsub, β.symm_apply_apply]
      · rw [dif_neg h]
        have hnot : ψ w.1 ∉ IH := fun hm => h ((hψ_mem_IH w.1).mpr hm)
        rw [dif_neg hnot]
        exact Subtype.ext (ψ.symm_apply_apply w.1)
    have h_right : Function.RightInverse ofHsub toHsub := by
      intro u
      dsimp only [toHsub, ofHsub]
      by_cases h : u.1 ∈ IH
      · rw [dif_pos h]
        let bu := β.symm ⟨u.1, Finset.mem_sdiff.mpr ⟨h, hu_not_XH u⟩⟩
        have hmem : bu.1 ∈ IG := (Finset.mem_sdiff.mp bu.2).1
        have hnotX : bu.1 ∉ XG := (Finset.mem_sdiff.mp bu.2).2
        rw [dif_pos hmem]
        apply Subtype.ext
        have hsub : (⟨bu.1, Finset.mem_sdiff.mpr ⟨hmem, hnotX⟩⟩ : {v : V // v ∈ IG \ XG}) = bu :=
          Subtype.ext rfl
        rw [hsub, β.apply_symm_apply]
      · rw [dif_neg h]
        have hnot : ψ.symm u.1 ∉ IG := fun hm => by
          have := (hψ_mem_IH (ψ.symm u.1)).mp hm
          rw [ψ.apply_symm_apply] at this
          exact h this
        rw [dif_neg hnot]
        exact Subtype.ext (ψ.apply_symm_apply u.1)
    let isoW : W ≃ W := (⟨toHsub, ofHsub, h_left, h_right⟩ : W ≃ {v : V // v ∈ SH}).trans eW.symm
    refine ⟨⟨isoW, fun {x y} => ?_⟩⟩
    have hG'_adj : (G'.deleteEdges {e'.val}).Adj x y ↔ Gd.Adj x.1 y.1 := by
      simp only [Gd, deleteEdges_adj, Set.mem_singleton_iff, G', induce_adj]
      constructor
      · rintro ⟨hadj, hne⟩
        refine ⟨hadj, fun h => hne ?_⟩
        rw [show e.val = e'.val.map Subtype.val from hιG e'] at h
        have hinj : Function.Injective (Sym2.map (Subtype.val : W → V)) :=
          Sym2.map.injective Subtype.val_injective
        exact hinj (by simpa [Sym2.map_mk] using h)
      · rintro ⟨hadj, hne⟩
        refine ⟨hadj, fun h => hne ?_⟩
        rw [show e.val = e'.val.map Subtype.val from hιG e', ← h, Sym2.map_mk]
    have hH'_adj : (H'.deleteEdges {f'.val}).Adj (isoW x) (isoW y) ↔
        Hd.Adj (toHsub x).1 (toHsub y).1 := by
      have hew_x : eW (isoW x) = toHsub x := eW.apply_symm_apply (toHsub x)
      have hew_y : eW (isoW y) = toHsub y := eW.apply_symm_apply (toHsub y)
      simp only [Hd, deleteEdges_adj, Set.mem_singleton_iff, H', Hsub, comap_adj, induce_adj,
        hew_x, hew_y]
      constructor
      · rintro ⟨hadj, hne⟩
        refine ⟨hadj, fun h => hne ?_⟩
        rw [← hf'_eq, hιH f'] at h
        have hmap : s((toHsub x).1, (toHsub y).1) = (s(isoW x, isoW y).map eW).map Subtype.val := by
          simp [Sym2.map_mk, hew_x, hew_y]
        rw [hmap] at h
        have hinj1 : Function.Injective (Sym2.map (Subtype.val : {v : V // v ∈ SH} → V)) :=
          Sym2.map.injective Subtype.val_injective
        have hinj2 : Function.Injective (Sym2.map eW) := Sym2.map.injective eW.injective
        exact hinj2 (hinj1 h)
      · rintro ⟨hadj, hne⟩
        refine ⟨hadj, fun h => hne ?_⟩
        rw [← hf'_eq, hιH f', ← h]
        simp [Sym2.map_mk, hew_x, hew_y]
    rw [hG'_adj, hH'_adj]
    by_cases hx : x.1 ∈ IG
    · have hdx : Gd.degree x.1 = 0 := (Finset.mem_filter.mp hx).2
      have hnoG : ¬ Gd.Adj x.1 y.1 := (degree_eq_zero_iff_not_adj Gd x.1).mp hdx y.1
      have hmem_to : (toHsub x).1 ∈ IH := by
        dsimp only [toHsub]
        rw [dif_pos hx]
        exact (Finset.mem_sdiff.mp (β ⟨x.1, Finset.mem_sdiff.mpr ⟨hx, hw_not_XG x⟩⟩).2).1
      have hdh : Hd.degree (toHsub x).1 = 0 := (Finset.mem_filter.mp hmem_to).2
      have hnoH : ¬ Hd.Adj (toHsub x).1 (toHsub y).1 :=
        (degree_eq_zero_iff_not_adj Hd (toHsub x).1).mp hdh (toHsub y).1
      exact iff_of_false hnoH hnoG
    · by_cases hy : y.1 ∈ IG
      · have hdy : Gd.degree y.1 = 0 := (Finset.mem_filter.mp hy).2
        have hnoG : ¬ Gd.Adj x.1 y.1 := fun h =>
          (degree_eq_zero_iff_not_adj Gd y.1).mp hdy x.1 h.symm
        have hmem_to : (toHsub y).1 ∈ IH := by
          dsimp only [toHsub]
          rw [dif_pos hy]
          exact (Finset.mem_sdiff.mp (β ⟨y.1, Finset.mem_sdiff.mpr ⟨hy, hw_not_XG y⟩⟩).2).1
        have hdh : Hd.degree (toHsub y).1 = 0 := (Finset.mem_filter.mp hmem_to).2
        have hnoH : ¬ Hd.Adj (toHsub x).1 (toHsub y).1 := fun h =>
          (degree_eq_zero_iff_not_adj Hd (toHsub y).1).mp hdh (toHsub x).1 h.symm
        exact iff_of_false hnoH hnoG
      · have htx : (toHsub x).1 = ψ x.1 := by dsimp only [toHsub]; rw [dif_neg hx]
        have hty : (toHsub y).1 = ψ y.1 := by dsimp only [toHsub]; rw [dif_neg hy]
        rw [htx, hty]
        exact ψ.map_rel_iff
  have hLift : Nonempty (G' ≃g H') → Nonempty (G ≃g H) := by
    rintro ⟨α⟩
    let βX : {v : V // v ∈ XG} ≃ {v : V // v ∈ XH} :=
      Fintype.equivOfCardEq (by simp only [Fintype.card_coe]; exact hX_card)
    have hXG_iff : ∀ v : V, v ∈ XG ↔ ¬ v ∈ SG := by
      intro v
      simp only [XG, SG, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
      omega
    have hXH_iff : ∀ v : V, v ∈ XH ↔ ¬ v ∈ SH := by
      intro v
      simp only [XH, SH, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
      omega
    let toV : V → V := fun v =>
      if hv : v ∈ SG then (eW (α ⟨v, hv⟩)).1
      else (βX ⟨v, (hXG_iff v).mpr hv⟩).1
    let ofV : V → V := fun v =>
      if hv : v ∈ SH then (α.symm (eW.symm ⟨v, hv⟩)).1
      else (βX.symm ⟨v, (hXH_iff v).mpr hv⟩).1
    have h_left : Function.LeftInverse ofV toV := by
      intro v
      dsimp only [toV, ofV]
      by_cases hv : v ∈ SG
      · rw [dif_pos hv, dif_pos (eW (α ⟨v, hv⟩)).2]
        simp only [Subtype.coe_eta, Equiv.symm_apply_apply, RelIso.symm_apply_apply]
      · rw [dif_neg hv]
        have hnot : (βX ⟨v, (hXG_iff v).mpr hv⟩).1 ∉ SH :=
          (hXH_iff _).mp (βX ⟨v, (hXG_iff v).mpr hv⟩).2
        rw [dif_neg hnot]
        simp only [Subtype.coe_eta, Equiv.symm_apply_apply]
    have h_right : Function.RightInverse ofV toV := by
      intro v
      dsimp only [toV, ofV]
      by_cases hv : v ∈ SH
      · rw [dif_pos hv, dif_pos (α.symm (eW.symm ⟨v, hv⟩)).2]
        simp only [Subtype.coe_eta, RelIso.apply_symm_apply, Equiv.apply_symm_apply]
      · rw [dif_neg hv]
        have hnot : (βX.symm ⟨v, (hXH_iff v).mpr hv⟩).1 ∉ SG :=
          (hXG_iff _).mp (βX.symm ⟨v, (hXH_iff v).mpr hv⟩).2
        rw [dif_neg hnot]
        simp only [Subtype.coe_eta, Equiv.apply_symm_apply]
    refine ⟨⟨⟨toV, ofV, h_left, h_right⟩, fun {x y} => ?_⟩⟩
    dsimp only [Equiv.coe_fn_mk, toV]
    by_cases hx : x ∈ SG
    · by_cases hy : y ∈ SG
      · rw [dif_pos hx, dif_pos hy]
        have h1 : H.Adj (eW (α ⟨x, hx⟩)).1 (eW (α ⟨y, hy⟩)).1 ↔ H'.Adj (α ⟨x, hx⟩) (α ⟨y, hy⟩) :=
          Iff.rfl
        rw [h1, α.map_rel_iff]
        rfl
      · have hdy : G.degree y = 0 := (Finset.mem_filter.mp ((hXG_iff y).mpr hy)).2
        have hnoG : ¬ G.Adj x y := fun h => (degree_eq_zero_iff_not_adj G y).mp hdy x h.symm
        rw [dif_pos hx, dif_neg hy]
        have hdh : H.degree (βX ⟨y, (hXG_iff y).mpr hy⟩).1 = 0 :=
          (Finset.mem_filter.mp (βX ⟨y, (hXG_iff y).mpr hy⟩).2).2
        have hnoH : ¬ H.Adj (eW (α ⟨x, hx⟩)).1 (βX ⟨y, (hXG_iff y).mpr hy⟩).1 := fun h =>
          (degree_eq_zero_iff_not_adj H _).mp hdh _ h.symm
        exact iff_of_false hnoH hnoG
    · have hdx : G.degree x = 0 := (Finset.mem_filter.mp ((hXG_iff x).mpr hx)).2
      have hnoG : ¬ G.Adj x y := (degree_eq_zero_iff_not_adj G x).mp hdx y
      rw [dif_neg hx]
      have hdh : H.degree (βX ⟨x, (hXG_iff x).mpr hx⟩).1 = 0 :=
        (Finset.mem_filter.mp (βX ⟨x, (hXG_iff x).mpr hx⟩).2).2
      have hnoH : ¬ H.Adj (βX ⟨x, (hXG_iff x).mpr hx⟩).1
          (if hy : y ∈ SG then (eW (α ⟨y, hy⟩)).1 else (βX ⟨y, (hXG_iff y).mpr hy⟩).1) :=
        (degree_eq_zero_iff_not_adj H _).mp hdh _
      exact iff_of_false hnoH hnoG
  exact ⟨W, inferInstance, G', H', h4W, hE', hG'_iso_free, hH'_iso_free, hEH', hLift⟩

end StripIsolates

section DisconnectedCase

private lemma component_iso_of_graph_iso {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (φ : G ≃g H) (C : G.ConnectedComponent) :
    Nonempty (C.toSimpleGraph ≃g (φ.connectedComponentEquiv C).toSimpleGraph) :=
  ⟨⟨ConnectedComponent.isoEquivSupp φ C, fun {_ _} => φ.map_rel_iff⟩⟩

private noncomputable def compCount {U : Type*} [Fintype U] {k : ℕ} (T : SimpleGraph (Fin k))
    (X : SimpleGraph U) : ℕ :=
  (Finset.univ.filter fun C : X.ConnectedComponent => Nonempty (C.toSimpleGraph ≃g T)).card

private lemma compCount_eq_card {U : Type*} [Fintype U] {k : ℕ} (T : SimpleGraph (Fin k))
    (X : SimpleGraph U) :
    compCount T X = Fintype.card {C : X.ConnectedComponent // Nonempty (C.toSimpleGraph ≃g T)} := by
  unfold compCount
  rw [← Fintype.card_subtype]

private lemma compCount_eq_of_iso {U V : Type*} [Fintype U] [Fintype V]
    {X : SimpleGraph U} {Y : SimpleGraph V} (φ : X ≃g Y) {k : ℕ} (T : SimpleGraph (Fin k)) :
    compCount T X = compCount T Y := by
  unfold compCount
  refine Finset.card_bij (fun C _ => φ.connectedComponentEquiv C) ?_ ?_ ?_
  · intro C hC
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hC ⊢
    obtain ⟨ψ⟩ := hC
    obtain ⟨ι⟩ := component_iso_of_graph_iso φ C
    exact ⟨ι.symm.trans ψ⟩
  · intro C1 _ C2 _ h
    exact φ.connectedComponentEquiv.injective h
  · intro D hD
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hD
    obtain ⟨ψ⟩ := hD
    let C := φ.connectedComponentEquiv.symm D
    refine ⟨C, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, φ.connectedComponentEquiv.apply_symm_apply D⟩
    obtain ⟨ι⟩ := component_iso_of_graph_iso φ C
    rw [φ.connectedComponentEquiv.apply_symm_apply D] at ι
    exact ⟨ι.trans ψ⟩

private lemma exists_comp_of_edge {U : Type*} (X : SimpleGraph U) (e : X.edgeSet) :
    ∃ C : X.ConnectedComponent, ∀ x ∈ e.val, x ∈ C.supp := by
  obtain ⟨e_val, he⟩ := e
  obtain ⟨a, b, rfl⟩ : ∃ a b, e_val = s(a, b) := Sym2.ind (fun a b => ⟨a, b, rfl⟩) e_val
  refine ⟨X.connectedComponentMk a, fun x hx => ?_⟩
  rw [Sym2.mem_iff] at hx
  rw [ConnectedComponent.mem_supp_iff]
  rcases hx with rfl | rfl
  · rfl
  · exact (ConnectedComponent.connectedComponentMk_eq_of_adj he).symm

private noncomputable def edgeComp {U : Type*} (X : SimpleGraph U) (e : X.edgeSet) :
    X.ConnectedComponent :=
  Classical.choose (exists_comp_of_edge X e)

private lemma mem_supp_of_edgeComp {U : Type*} (X : SimpleGraph U) (e : X.edgeSet)
    {x : U} (hx : x ∈ e.val) : x ∈ (edgeComp X e).supp :=
  Classical.choose_spec (exists_comp_of_edge X e) x hx

private noncomputable def compEdgeSet_equiv {U : Type*} (X : SimpleGraph U) (C : X.ConnectedComponent) :
    {e : X.edgeSet // edgeComp X e = C} ≃ C.toSimpleGraph.edgeSet :=
  let g : C.toSimpleGraph.edgeSet → {e : X.edgeSet // edgeComp X e = C} := fun e' =>
    ⟨⟨e'.val.map Subtype.val, by
      obtain ⟨e'_val, he'⟩ := e'
      obtain ⟨a, b, rfl⟩ : ∃ a b, e'_val = s(a, b) := Sym2.ind (fun a b => ⟨a, b, rfl⟩) e'_val
      exact he'⟩, by
      obtain ⟨e'_val, he'⟩ := e'
      obtain ⟨a, b, rfl⟩ : ∃ a b, e'_val = s(a, b) := Sym2.ind (fun a b => ⟨a, b, rfl⟩) e'_val
      have ha_supp : a.1 ∈ (edgeComp X ⟨s(a.1, b.1), he'⟩).supp :=
        mem_supp_of_edgeComp X ⟨s(a.1, b.1), he'⟩ (Sym2.mem_mk_left a.1 b.1)
      exact ConnectedComponent.eq_of_common_vertex ha_supp a.2⟩
  have hbij : Function.Bijective g := by
    constructor
    · intro e1 e2 heq
      apply Subtype.ext
      exact (Sym2.map.injective Subtype.val_injective) (congrArg (fun x => x.1.val) heq)
    · rintro ⟨⟨e_val, he⟩, heC⟩
      obtain ⟨a, b, rfl⟩ : ∃ a b, e_val = s(a, b) := Sym2.ind (fun a b => ⟨a, b, rfl⟩) e_val
      have ha : a ∈ C.supp := heC ▸ mem_supp_of_edgeComp X ⟨s(a, b), he⟩ (Sym2.mem_mk_left a b)
      have hb : b ∈ C.supp := heC ▸ mem_supp_of_edgeComp X ⟨s(a, b), he⟩ (Sym2.mem_mk_right a b)
      refine ⟨⟨s(⟨a, ha⟩, ⟨b, hb⟩), he⟩, ?_⟩
      ext
      rfl
  (Equiv.ofBijective g hbij).symm

private lemma compEdgeSet_equiv_symm_val {U : Type*} (X : SimpleGraph U) (C : X.ConnectedComponent)
    (e' : C.toSimpleGraph.edgeSet) :
    ((compEdgeSet_equiv X C).symm e').1.val = e'.val.map Subtype.val := by
  rfl

private lemma sum_comp_card_supp {U : Type*} [Fintype U] (X : SimpleGraph U) :
    ∑ C : X.ConnectedComponent, Fintype.card C.supp = Fintype.card U := by
  have h1 : ∀ C : X.ConnectedComponent, Fintype.card C.supp =
      Fintype.card {v : U // X.connectedComponentMk v = C} := by
    intro C
    refine Fintype.card_congr ?_
    exact Equiv.subtypeEquivRight (fun v => ConnectedComponent.mem_supp_iff C v)
  simp_rw [h1]
  exact Fintype.card_sigma.symm.trans (Fintype.card_congr (Equiv.sigmaFiberEquiv X.connectedComponentMk))

private lemma sum_comp_card_edgeFinset {U : Type*} [Fintype U] (X : SimpleGraph U) :
    ∑ C : X.ConnectedComponent, C.toSimpleGraph.edgeFinset.card = X.edgeFinset.card := by
  have h1 : ∀ C : X.ConnectedComponent, C.toSimpleGraph.edgeFinset.card =
      Fintype.card {e : X.edgeSet // edgeComp X e = C} := by
    intro C
    rw [← C.toSimpleGraph.card_edgeSet]
    exact Fintype.card_congr (compEdgeSet_equiv X C).symm
  simp_rw [h1]
  rw [← X.card_edgeSet]
  exact Fintype.card_sigma.symm.trans (Fintype.card_congr (Equiv.sigmaFiberEquiv (edgeComp X)))

private lemma not_connected_of_edgeHypomorphic_not_connected {W : Type*} [Fintype W]
    (G' H' : SimpleGraph W) (hW : 4 ≤ Fintype.card W) (hE : 4 ≤ G'.edgeFinset.card)
    (hisoG : ∀ w : W, ∃ u : W, G'.Adj w u)
    (hEH : EdgeHypomorphic G' H') (hNotConn : ¬ G'.Connected) :
    ¬ H'.Connected := by
  intro hConnH
  obtain ⟨σ, hσ⟩ := hEH
  have hNonemptyW : Nonempty W := Fintype.card_pos_iff.mp (by omega)
  have hm_eq : G'.edgeFinset.card = H'.edgeFinset.card := by
    rw [← G'.card_edgeSet, ← H'.card_edgeSet]
    exact Fintype.card_congr σ
  have hH_del_not_conn : ∀ e' : H'.edgeSet, ¬ (H'.deleteEdges {e'.val}).Connected := by
    intro e' hconn
    have hsim : Nonempty (G'.deleteEdges {(σ.symm e').val} ≃g H'.deleteEdges {e'.val}) := by
      simpa only [Equiv.apply_symm_apply] using hσ (σ.symm e')
    obtain ⟨ψ⟩ := hsim
    have hG_del : (G'.deleteEdges {(σ.symm e').val}).Connected := (Iso.connected_iff ψ).mpr hconn
    have hG_conn : G'.Connected := ⟨hG_del.preconnected.mono (deleteEdges_le _)⟩
    exact hNotConn hG_conn
  have hH_bridge : ∀ ⦃u v : W⦄, H'.Adj u v → H'.IsBridge s(u, v) := by
    intro u v hadj
    by_contra hnbr
    exact hH_del_not_conn ⟨s(u, v), hadj⟩ (hConnH.connected_delete_edge_of_not_isBridge hnbr)
  have hH_acyc : H'.IsAcyclic := isAcyclic_iff_forall_adj_isBridge.mpr hH_bridge
  have hH_tree : H'.IsTree := ⟨hConnH, hH_acyc⟩
  have hW_eq : H'.edgeFinset.card + 1 = Fintype.card W := hH_tree.card_edgeFinset
  have hW_eq_G : G'.edgeFinset.card + 1 = Fintype.card W := hm_eq ▸ hW_eq
  have hH_comp2 : ∀ e' : H'.edgeSet, Fintype.card (H'.deleteEdges {e'.val}).ConnectedComponent = 2 := by
    intro e'
    obtain ⟨e'_val, he'⟩ := e'
    obtain ⟨u, v, huv⟩ : ∃ u v, e'_val = s(u, v) := Sym2.ind (fun u v => ⟨u, v, rfl⟩) e'_val
    have hadj : H'.Adj u v := by
      rw [huv] at he'
      exact he'
    let Hdel := H'.deleteEdges {s(u, v)}
    have hcard_del : Fintype.card (H'.deleteEdges {e'_val}).ConnectedComponent =
        Fintype.card Hdel.ConnectedComponent := by
      rw [huv]
    rw [hcard_del]
    have hle2 : Fintype.card Hdel.ConnectedComponent ≤ 2 := by
      have hsub : (Finset.univ : Finset Hdel.ConnectedComponent) ⊆
          {Hdel.connectedComponentMk u, Hdel.connectedComponentMk v} := by
        intro c _
        obtain ⟨x, hx⟩ := c.exists_rep
        have hcx : Hdel.connectedComponentMk x = c := hx
        rw [← hcx]
        obtain ⟨P, hP⟩ := hConnH.exists_isPath x u
        by_cases heP : s(u, v) ∈ P.edges
        · have hvP : v ∈ P.support := by
            have heP' : s(v, u) ∈ P.edges := by simpa [Sym2.eq_swap] using heP
            exact P.fst_mem_support_of_mem_edges heP'
          let P₁ := P.takeUntil v hvP
          have huP₁ : u ∉ P₁.support := Walk.endpoint_notMem_support_takeUntil hP hvP hadj.ne
          have heP₁ : s(u, v) ∉ P₁.edges := fun h => huP₁ (P₁.fst_mem_support_of_mem_edges h)
          have hreach : Hdel.Reachable x v := reachable_deleteEdges_iff_exists_walk.mpr ⟨P₁, heP₁⟩
          rw [ConnectedComponent.sound hreach]
          simp
        · have hreach : Hdel.Reachable x u := reachable_deleteEdges_iff_exists_walk.mpr ⟨P, heP⟩
          rw [ConnectedComponent.sound hreach]
          simp
      calc Fintype.card Hdel.ConnectedComponent
          = (Finset.univ : Finset Hdel.ConnectedComponent).card := (Finset.card_univ).symm
        _ ≤ ({Hdel.connectedComponentMk u, Hdel.connectedComponentMk v} : Finset _).card :=
            Finset.card_le_card hsub
        _ ≤ 2 := Finset.card_le_two
    have hne : Hdel.connectedComponentMk u ≠ Hdel.connectedComponentMk v := by
      intro heq
      have hbr : H'.IsBridge s(u, v) := hH_bridge hadj
      exact hbr (ConnectedComponent.exact heq)
    have hge2 : 2 ≤ Fintype.card Hdel.ConnectedComponent := by
      have hcard : ({Hdel.connectedComponentMk u, Hdel.connectedComponentMk v} : Finset _).card = 2 :=
        Finset.card_pair hne
      rw [← hcard]
      exact Finset.card_le_card (Finset.subset_univ _)
    omega
  have hG_comp_ge2 : 2 ≤ Fintype.card G'.ConnectedComponent := by
    by_contra hlt
    have hle1 : Fintype.card G'.ConnectedComponent ≤ 1 := by omega
    have hsub : Subsingleton G'.ConnectedComponent := Fintype.card_le_one_iff_subsingleton.mp hle1
    apply hNotConn
    refine ⟨fun a b => ?_⟩
    exact ConnectedComponent.exact (Subsingleton.elim (G'.connectedComponentMk a) (G'.connectedComponentMk b))
  by_cases hG_comp_ge3 : 3 ≤ Fintype.card G'.ConnectedComponent
  · obtain ⟨e₀_val, he₀⟩ := Finset.card_pos.mp (by omega : 0 < G'.edgeFinset.card)
    let e₀ : G'.edgeSet := ⟨e₀_val, (G'.mem_edgeFinset).mp he₀⟩
    have hle3 : 3 ≤ Fintype.card (G'.deleteEdges {e₀.val}).ConnectedComponent := by
      rw [← Nat.card_eq_fintype_card]
      exact (Nat.card_eq_fintype_card (α := G'.ConnectedComponent) ▸ hG_comp_ge3).trans
        (ConnectedComponent.card_le_card_of_le (deleteEdges_le {e₀.val}))
    obtain ⟨φ⟩ := hσ e₀
    have hcard_eq : Fintype.card (G'.deleteEdges {e₀.val}).ConnectedComponent =
        Fintype.card (H'.deleteEdges {(σ e₀).val}).ConnectedComponent :=
      Fintype.card_congr φ.connectedComponentEquiv
    rw [hH_comp2 (σ e₀)] at hcard_eq
    omega
  · have hex_tree : ∃ C₀ : G'.ConnectedComponent, C₀.toSimpleGraph.edgeFinset.card < Fintype.card C₀.supp := by
      by_contra hno
      push Not at hno
      have hsum_le : ∑ C : G'.ConnectedComponent, Fintype.card C.supp ≤
          ∑ C : G'.ConnectedComponent, C.toSimpleGraph.edgeFinset.card :=
        Finset.sum_le_sum fun C _ => hno C
      rw [sum_comp_card_supp, sum_comp_card_edgeFinset] at hsum_le
      omega
    obtain ⟨C₀, hC₀_lt⟩ := hex_tree
    have hC₀_conn : C₀.toSimpleGraph.Connected := C₀.connected_toSimpleGraph
    have hcard_coe : Fintype.card ↥C₀ = Fintype.card C₀.supp :=
      Fintype.card_congr (Equiv.subtypeEquivRight fun _ => Iff.rfl)
    have hC₀_card : Fintype.card C₀.supp ≤ C₀.toSimpleGraph.edgeFinset.card + 1 := by
      have h1 := hC₀_conn.card_vert_le_card_edgeSet_add_one
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet, hcard_coe] at h1
      exact h1
    have hC₀_eq : C₀.toSimpleGraph.edgeFinset.card + 1 = Fintype.card C₀.supp := by omega
    have hC₀_tree : C₀.toSimpleGraph.IsTree := isTree_iff_connected_and_card.mpr ⟨hC₀_conn, by
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet, hcard_coe]
      exact hC₀_eq⟩
    obtain ⟨a, ha⟩ := C₀.nonempty_supp
    obtain ⟨b, hab⟩ := hisoG a
    have hb : b ∈ C₀.supp := C₀.mem_supp_of_adj_mem_supp ha hab
    have hadj_C₀ : C₀.toSimpleGraph.Adj ⟨a, ha⟩ ⟨b, hb⟩ := hab
    have hbr_C₀ : C₀.toSimpleGraph.IsBridge s(⟨a, ha⟩, ⟨b, hb⟩) :=
      isAcyclic_iff_forall_adj_isBridge.mp hC₀_tree.isAcyclic hadj_C₀
    let e₀ : G'.edgeSet := ⟨s(a, b), hab⟩
    let Gdel := G'.deleteEdges {e₀.val}
    have hnab_Gdel : ¬ Gdel.Reachable a b := by
      rintro ⟨p⟩
      have hmem_p : ∀ x ∈ p.support, x ∈ C₀.supp := by
        intro x hx
        have hrx : Gdel.Reachable a x := ⟨p.takeUntil x hx⟩
        have hrx' : G'.Reachable a x := hrx.mono' (deleteEdges_le _)
        exact (ConnectedComponent.mem_supp_iff C₀ x).mpr (
          ((ConnectedComponent.mem_supp_iff C₀ a).mp ha).symm ▸ (ConnectedComponent.sound hrx').symm)
      let C₀del := C₀.toSimpleGraph.deleteEdges {s(⟨a, ha⟩, ⟨b, hb⟩)}
      have hwalk_C₀ : C₀del.Walk ⟨a, ha⟩ ⟨b, hb⟩ := by
        let rec liftWalk : ∀ {x y : W} (hx : x ∈ C₀.supp) (hy : y ∈ C₀.supp) (q : Gdel.Walk x y),
            (∀ z ∈ q.support, z ∈ C₀.supp) → C₀del.Walk ⟨x, hx⟩ ⟨y, hy⟩
          | _, _, _, _, .nil, _ => Walk.nil
          | x, y, hx, hy, @Walk.cons _ _ _ z _ hadj_q q', hsupp =>
            have hz : z ∈ C₀.supp := hsupp z (by simp)
            have hq'supp : ∀ w ∈ q'.support, w ∈ C₀.supp := fun w hw => hsupp w (by simp [hw])
            have hadj_del : C₀del.Adj ⟨x, hx⟩ ⟨z, hz⟩ := by
              rw [deleteEdges_adj] at hadj_q ⊢
              refine ⟨hadj_q.1, fun heq => hadj_q.2 ?_⟩
              rw [Set.mem_singleton_iff] at heq ⊢
              have h := congrArg (Sym2.map Subtype.val) heq
              simp only [Sym2.map_mk] at h
              exact h
            Walk.cons hadj_del (liftWalk hz hy q' hq'supp)
        exact liftWalk ha hb p hmem_p
      exact hbr_C₀ ⟨hwalk_C₀⟩
    have hex_C₁ : ∃ C₁ : G'.ConnectedComponent, C₁ ≠ C₀ := by
      by_contra hno
      push Not at hno
      have hsub : Subsingleton G'.ConnectedComponent := ⟨fun x y => (hno x).trans (hno y).symm⟩
      have hle1 : Fintype.card G'.ConnectedComponent ≤ 1 := Fintype.card_le_one_iff_subsingleton.mpr hsub
      omega
    obtain ⟨C₁, hC₁_ne⟩ := hex_C₁
    obtain ⟨z, hz⟩ := C₁.nonempty_supp
    have hnaz : ¬ Gdel.Reachable a z := by
      intro hrz
      have hrz' : G'.Reachable a z := hrz.mono' (deleteEdges_le _)
      have hcomp := ConnectedComponent.sound hrz'
      rw [(ConnectedComponent.mem_supp_iff C₀ a).mp ha, (ConnectedComponent.mem_supp_iff C₁ z).mp hz] at hcomp
      exact hC₁_ne hcomp.symm
    have hnbz : ¬ Gdel.Reachable b z := by
      intro hrz
      have hrz' : G'.Reachable b z := hrz.mono' (deleteEdges_le _)
      have hcomp := ConnectedComponent.sound hrz'
      rw [(ConnectedComponent.mem_supp_iff C₀ b).mp hb, (ConnectedComponent.mem_supp_iff C₁ z).mp hz] at hcomp
      exact hC₁_ne hcomp.symm
    have h3 : ({Gdel.connectedComponentMk a, Gdel.connectedComponentMk b,
        Gdel.connectedComponentMk z} : Finset Gdel.ConnectedComponent).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_pair]
      · exact fun h => hnbz (ConnectedComponent.exact h)
      · simp only [Finset.mem_insert, Finset.mem_singleton]
        rintro (h | h)
        · exact hnab_Gdel (ConnectedComponent.exact h)
        · exact hnaz (ConnectedComponent.exact h)
    have hge3 : 3 ≤ Fintype.card Gdel.ConnectedComponent := by
      rw [← h3]
      exact Finset.card_le_card (Finset.subset_univ _)
    obtain ⟨φ⟩ := hσ e₀
    have hcard_eq : Fintype.card Gdel.ConnectedComponent =
        Fintype.card (H'.deleteEdges {(σ e₀).val}).ConnectedComponent :=
      Fintype.card_congr φ.connectedComponentEquiv
    rw [hH_comp2 (σ e₀)] at hcard_eq
    omega

private lemma deleteEdges_comp_decomposition {U : Type*} [Fintype U] (X : SimpleGraph U)
    (e : X.edgeSet) {k : ℕ} (T : SimpleGraph (Fin k)) :
    compCount T (X.deleteEdges {e.val}) =
      (∑ C : X.ConnectedComponent, if C = edgeComp X e then 0 else
        if Nonempty (C.toSimpleGraph ≃g T) then 1 else 0) +
      compCount T ((edgeComp X e).toSimpleGraph.deleteEdges
        {((compEdgeSet_equiv X (edgeComp X e)) ⟨e, rfl⟩).val}) := by
  let X' := X.deleteEdges {e.val}
  let C₀ := edgeComp X e
  let e_sub := ((compEdgeSet_equiv X C₀) ⟨e, rfl⟩).val
  let Y := C₀.toSimpleGraph.deleteEdges {e_sub}
  let mapC : X'.ConnectedComponent → X.ConnectedComponent :=
    ConnectedComponent.map (Hom.ofLE (deleteEdges_le {e.val}))
  have he_sub_val : e_sub.map Subtype.val = e.val := by
    have h1 := compEdgeSet_equiv_symm_val X C₀ ((compEdgeSet_equiv X C₀) ⟨e, rfl⟩)
    rw [Equiv.symm_apply_apply] at h1
    exact h1.symm
  have hreach_other : ∀ {C : X.ConnectedComponent}, C ≠ C₀ →
      ∀ {x y : U}, x ∈ C.supp → y ∈ C.supp → X'.Reachable x y := by
    intro C hC x y hx hy
    obtain ⟨p⟩ := C.reachable_of_mem_supp hx hy
    obtain ⟨e_val, he⟩ := e
    obtain ⟨u, v, huv⟩ : ∃ u v, e_val = s(u, v) := Sym2.ind (fun a b => ⟨a, b, rfl⟩) e_val
    have hnot_mem : s(u, v) ∉ p.edges := by
      intro he_mem
      have hu_p : u ∈ p.support := p.fst_mem_support_of_mem_edges he_mem
      have hrx : X.Reachable x u := ⟨p.takeUntil u hu_p⟩
      have hu_C : u ∈ C.supp := (ConnectedComponent.mem_supp_iff C u).mpr (
        ((ConnectedComponent.mem_supp_iff C x).mp hx).symm ▸ (ConnectedComponent.sound hrx).symm)
      have hu_C₀ : u ∈ C₀.supp := mem_supp_of_edgeComp X ⟨e_val, he⟩ (huv ▸ Sym2.mem_mk_left u v)
      exact hC (ConnectedComponent.eq_of_common_vertex hu_C hu_C₀)
    have hX'_eq : X' = X.deleteEdges {s(u, v)} := by simp only [X', huv]
    rw [hX'_eq]
    exact reachable_deleteEdges_iff_exists_walk.mpr ⟨p, hnot_mem⟩
  have hfiber_other : ∀ {C : X.ConnectedComponent}, C ≠ C₀ →
      ∃! D : X'.ConnectedComponent, mapC D = C := by
    intro C hC
    obtain ⟨x₀, hx₀⟩ := C.nonempty_supp
    refine ⟨X'.connectedComponentMk x₀, ?_, ?_⟩
    · simp only [mapC, ConnectedComponent.map_mk, Hom.ofLE_apply]
      exact (ConnectedComponent.mem_supp_iff C x₀).mp hx₀
    · intro D hD
      obtain ⟨y, rfl⟩ := D.exists_rep
      have hyC : y ∈ C.supp := by
        simp only [mapC, ConnectedComponent.map_mk, Hom.ofLE_apply] at hD
        exact (ConnectedComponent.mem_supp_iff C y).mpr hD
      exact ConnectedComponent.sound (hreach_other hC hyC hx₀)
  have hiso_other : ∀ {C : X.ConnectedComponent} (_ : C ≠ C₀) (D : X'.ConnectedComponent),
      mapC D = C → Nonempty (D.toSimpleGraph ≃g C.toSimpleGraph) := by
    intro C hC D hD
    have hsupp_eq : D.supp = C.supp := by
      ext x
      constructor
      · intro hx
        have hdx : X'.connectedComponentMk x = D := (ConnectedComponent.mem_supp_iff D x).mp hx
        have hmk : X.connectedComponentMk x = C := by
          rw [← hD, ← hdx]
          rfl
        exact (ConnectedComponent.mem_supp_iff C x).mpr hmk
      · intro hx
        obtain ⟨y, hy_eq⟩ := D.exists_rep
        have hyC : y ∈ C.supp := by
          rw [← hy_eq] at hD
          change mapC (X'.connectedComponentMk y) = C at hD
          exact (ConnectedComponent.mem_supp_iff C y).mpr hD
        have hreach : X'.Reachable y x := hreach_other hC hyC hx
        exact (ConnectedComponent.mem_supp_iff D x).mpr (hy_eq ▸ ConnectedComponent.sound hreach.symm)
    refine ⟨⟨Equiv.subtypeEquivRight (fun x => by change x ∈ D.supp ↔ x ∈ C.supp; rw [hsupp_eq]), fun {a b} => ?_⟩⟩
    dsimp only [ConnectedComponent.toSimpleGraph, induce_adj, Equiv.subtypeEquivRight]
    change X.Adj a.1 b.1 ↔ X'.Adj a.1 b.1
    rw [deleteEdges_adj, Set.mem_singleton_iff]
    constructor
    · intro hadj
      have hne_e : s(a.1, b.1) ≠ e.val := by
        intro heq
        have ha_C₀ : a.1 ∈ C₀.supp := mem_supp_of_edgeComp X e (heq ▸ Sym2.mem_mk_left a.1 b.1)
        have ha_C : a.1 ∈ C.supp := hsupp_eq ▸ a.2
        exact hC (ConnectedComponent.eq_of_common_vertex ha_C ha_C₀)
      exact ⟨hadj, hne_e⟩
    · intro hadj
      exact hadj.1
  have hsplit : compCount T X' =
      (Finset.univ.filter fun D : X'.ConnectedComponent => mapC D ≠ C₀ ∧ Nonempty (D.toSimpleGraph ≃g T)).card +
      (Finset.univ.filter fun D : X'.ConnectedComponent => mapC D = C₀ ∧ Nonempty (D.toSimpleGraph ≃g T)).card := by
    unfold compCount
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      ext D
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      tauto
    · rw [Finset.disjoint_left]
      intro D h1 h2
      rw [Finset.mem_filter] at h1 h2
      exact h1.2.1 h2.2.1
  rw [hsplit]
  congr 1
  · let t := Finset.univ.filter fun C : X.ConnectedComponent => C ≠ C₀ ∧ Nonempty (C.toSimpleGraph ≃g T)
    have hcard_t : t.card = ∑ C : X.ConnectedComponent, if C = C₀ then 0 else
        if Nonempty (C.toSimpleGraph ≃g T) then 1 else 0 := by
      rw [Finset.card_filter]
      refine Finset.sum_congr rfl fun C _ => ?_
      by_cases h : C = C₀ <;> simp [h]
    rw [← hcard_t]
    refine Finset.card_bij (fun D _ => mapC D) ?_ ?_ ?_
    · intro D hD
      dsimp only [t]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hD ⊢
      obtain ⟨hneq, ⟨ψ⟩⟩ := hD
      obtain ⟨ι⟩ := hiso_other hneq D rfl
      exact ⟨hneq, ⟨ι.symm.trans ψ⟩⟩
    · intro D1 hD1 D2 hD2 heq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hD1 hD2
      have huniq := hfiber_other hD1.1
      exact huniq.unique (rfl : mapC D1 = mapC D1) heq.symm
    · intro C hC
      dsimp only [t] at hC
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hC
      obtain ⟨hneq, ⟨ψ⟩⟩ := hC
      obtain ⟨D, hD, _⟩ := hfiber_other hneq
      obtain ⟨ι⟩ := hiso_other hneq D hD
      refine ⟨D, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hD ▸ hneq, ⟨ι.trans ψ⟩⟩, hD⟩
  · have h_equiv_sub : ∀ {a b : C₀.supp}, Y.Reachable a b ↔ X'.Reachable a.1 b.1 := by
      intro a b
      constructor
      · rintro ⟨q⟩
        refine ⟨q.map ⟨Subtype.val, fun {x y} hadj => ?_⟩⟩
        rw [deleteEdges_adj] at hadj ⊢
        refine ⟨hadj.1, fun heq => hadj.2 ?_⟩
        rw [Set.mem_singleton_iff] at heq ⊢
        have hmap : s(x.1, y.1) = s(x, y).map Subtype.val := (Sym2.map_mk Subtype.val x y).symm
        rw [heq] at hmap
        have h2 : (s(x, y).map Subtype.val : Sym2 U) = e_sub.map Subtype.val := by rw [← hmap, he_sub_val]
        exact (Sym2.map.injective Subtype.val_injective) h2
      · rintro ⟨p⟩
        have hmem_p : ∀ z ∈ p.support, z ∈ C₀.supp := by
          intro z hz
          have hrx : X'.Reachable a.1 z := ⟨p.takeUntil z hz⟩
          have hrz : X.Reachable a.1 z := hrx.mono' (deleteEdges_le _)
          exact (ConnectedComponent.mem_supp_iff C₀ z).mpr (
            ((ConnectedComponent.mem_supp_iff C₀ a.1).mp a.2).symm ▸ (ConnectedComponent.sound hrz).symm)
        let rec liftWalk : ∀ {x y : U} (hx : x ∈ C₀.supp) (hy : y ∈ C₀.supp) (q : X'.Walk x y),
            (∀ z ∈ q.support, z ∈ C₀.supp) → Y.Walk ⟨x, hx⟩ ⟨y, hy⟩
          | _, _, _, _, .nil, _ => Walk.nil
          | x, y, hx, hy, @Walk.cons _ _ _ z _ hadj_q q', hsupp =>
            have hz : z ∈ C₀.supp := hsupp z (by simp)
            have hq'supp : ∀ w ∈ q'.support, w ∈ C₀.supp := fun w hw => hsupp w (by simp [hw])
            have hadj_y : Y.Adj ⟨x, hx⟩ ⟨z, hz⟩ := by
              rw [deleteEdges_adj] at hadj_q ⊢
              refine ⟨hadj_q.1, fun heq => hadj_q.2 ?_⟩
              rw [Set.mem_singleton_iff] at heq ⊢
              simpa [Sym2.map_mk, he_sub_val] using congrArg (Sym2.map Subtype.val) heq
            Walk.cons hadj_y (liftWalk hz hy q' hq'supp)
        exact ⟨liftWalk a.2 b.2 p hmem_p⟩
    let compMap : Y.ConnectedComponent → {D : X'.ConnectedComponent // mapC D = C₀} := fun E =>
      ⟨X'.connectedComponentMk E.out.1, by
        simp only [mapC, ConnectedComponent.map_mk, Hom.ofLE_apply]
        exact (ConnectedComponent.mem_supp_iff C₀ E.out.1).mp E.out.2⟩
    have hcomp_inj : Function.Injective compMap := by
      intro E1 E2 heq
      have hreach : X'.Reachable E1.out.1 E2.out.1 :=
        ConnectedComponent.exact (congrArg Subtype.val heq)
      have hreachY : Y.Reachable E1.out E2.out := h_equiv_sub.mpr hreach
      have hE1 : Y.connectedComponentMk E1.out = E1 := E1.out_eq
      have hE2 : Y.connectedComponentMk E2.out = E2 := E2.out_eq
      rw [← hE1, ← hE2]
      exact ConnectedComponent.sound hreachY
    have hcomp_iso : ∀ E : Y.ConnectedComponent,
        Nonempty (E.toSimpleGraph ≃g (compMap E).1.toSimpleGraph) := by
      intro E
      have hbij : ∀ x : C₀.supp, x ∈ E.supp ↔ x.1 ∈ (compMap E).1.supp := by
        intro x
        rw [ConnectedComponent.mem_supp_iff E x, ConnectedComponent.mem_supp_iff (compMap E).1 x.1]
        constructor
        · intro hx
          have hreachY : Y.Reachable x E.out := ConnectedComponent.exact (hx.trans E.out_eq.symm)
          exact ConnectedComponent.sound (h_equiv_sub.mp hreachY)
        · intro hx
          have hreachX : X'.Reachable x.1 E.out.1 := ConnectedComponent.exact hx
          have hreachY : Y.Reachable x E.out := h_equiv_sub.mpr hreachX
          exact (ConnectedComponent.sound hreachY).trans E.out_eq
      let toSupp : E.supp → (compMap E).1.supp := fun x => ⟨x.1.1, (hbij x.1).mp x.2⟩
      let ofSupp : (compMap E).1.supp → E.supp := fun x =>
        let hxC₀ : x.1 ∈ C₀.supp := (ConnectedComponent.mem_supp_iff C₀ x.1).mpr (by
          change mapC (X'.connectedComponentMk x.1) = C₀
          rw [(ConnectedComponent.mem_supp_iff (compMap E).1 x.1).mp x.2, (compMap E).2])
        ⟨⟨x.1, hxC₀⟩, (hbij ⟨x.1, hxC₀⟩).mpr x.2⟩
      refine ⟨⟨⟨toSupp, ofSupp, fun x => Subtype.ext (Subtype.ext rfl),
          fun x => Subtype.ext rfl⟩, fun {a b} => ?_⟩⟩
      dsimp only [Equiv.coe_fn_mk, toSupp]
      change X'.Adj a.1.1 b.1.1 ↔ Y.Adj a.1 b.1
      rw [deleteEdges_adj, deleteEdges_adj]
      constructor
      · rintro ⟨hadj, hne⟩
        refine ⟨hadj, fun heq => hne ?_⟩
        rw [Set.mem_singleton_iff] at heq ⊢
        simpa [Sym2.map_mk, he_sub_val] using congrArg (Sym2.map Subtype.val) heq
      · rintro ⟨hadj, hne⟩
        refine ⟨hadj, fun heq => hne ?_⟩
        rw [Set.mem_singleton_iff] at heq ⊢
        have hinj : Function.Injective (Sym2.map (Subtype.val : C₀.supp → U)) :=
          Sym2.map.injective Subtype.val_injective
        apply hinj
        have hsub_val : Sym2.map (Subtype.val : C₀.supp → U) e_sub = e.val := he_sub_val
        rw [Sym2.map_mk, hsub_val]
        exact heq
    have hcomp_Y : compCount T Y =
        (Finset.univ.filter fun E : Y.ConnectedComponent => Nonempty (E.toSimpleGraph ≃g T)).card := by
      unfold compCount
      congr 1
      ext E
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hcomp_Y]
    symm
    refine Finset.card_bij (fun E _ => (compMap E).1) ?_ ?_ ?_
    · intro E hE
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hE ⊢
      obtain ⟨ψ⟩ := hE
      obtain ⟨ι⟩ := hcomp_iso E
      exact ⟨(compMap E).2, ⟨ι.symm.trans ψ⟩⟩
    · intro E1 _ E2 _ heq
      exact hcomp_inj (Subtype.ext heq)
    · intro D hD
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hD
      obtain ⟨hmap, ⟨ψ⟩⟩ := hD
      let x₀ : U := Classical.choose D.nonempty_supp
      have hx₀ : x₀ ∈ D.supp := Classical.choose_spec D.nonempty_supp
      have hdx : X'.connectedComponentMk x₀ = D := (ConnectedComponent.mem_supp_iff D x₀).mp hx₀
      have hx₀C₀ : x₀ ∈ C₀.supp := (ConnectedComponent.mem_supp_iff C₀ x₀).mpr (by
        change mapC (X'.connectedComponentMk x₀) = C₀
        rw [hdx, hmap])
      let E : Y.ConnectedComponent := Y.connectedComponentMk ⟨x₀, hx₀C₀⟩
      have hED : (compMap E).1 = D := by
        have hreachY : Y.Reachable E.out ⟨x₀, hx₀C₀⟩ := ConnectedComponent.exact E.out_eq
        have hreachX : X'.Reachable E.out.1 x₀ := h_equiv_sub.mp hreachY
        exact (ConnectedComponent.sound hreachX).trans hdx
      let ι2 : (compMap E).1.toSimpleGraph ≃g D.toSimpleGraph :=
        ⟨Equiv.subtypeEquivRight (fun x => by change x ∈ (compMap E).1.supp ↔ x ∈ D.supp; rw [hED]),
          fun {_ _} => Iff.rfl⟩
      obtain ⟨ι1⟩ := hcomp_iso E
      refine ⟨E, ?_, hED⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨ι1.trans (ι2.trans ψ)⟩

private lemma sum_compCount_deleteEdges {U : Type*} [Fintype U] (X : SimpleGraph U)
    {k : ℕ} (T : SimpleGraph (Fin k)) (hTpos : 1 ≤ T.edgeFinset.card) :
    ∑ e ∈ X.edgeFinset, compCount T (X.deleteEdges {e}) =
      (X.edgeFinset.card - T.edgeFinset.card) * compCount T X +
      ∑ C ∈ Finset.univ.filter (fun C : X.ConnectedComponent =>
          T.edgeFinset.card < C.toSimpleGraph.edgeFinset.card),
        ∑ e ∈ C.toSimpleGraph.edgeFinset, compCount T (C.toSimpleGraph.deleteEdges {e}) := by
  have hcoe : ∑ e ∈ X.edgeFinset, compCount T (X.deleteEdges {e}) =
      ∑ e : X.edgeSet, compCount T (X.deleteEdges {e.val}) := by
    symm
    refine Finset.sum_bij (fun e _ => e.val) (fun e _ => (X.mem_edgeFinset).mpr e.prop)
      (fun _ _ _ _ h => Subtype.ext h) ?_ (fun _ _ => rfl)
    intro e he
    exact ⟨⟨e, (X.mem_edgeFinset).mp he⟩, Finset.mem_univ _, rfl⟩
  rw [hcoe]
  simp_rw [deleteEdges_comp_decomposition X _ T, Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_comm]
    have hterm : ∀ C : X.ConnectedComponent,
        (∑ e : X.edgeSet, if C = edgeComp X e then 0 else
          if Nonempty (C.toSimpleGraph ≃g T) then 1 else 0) =
        (X.edgeFinset.card - T.edgeFinset.card) *
          (if Nonempty (C.toSimpleGraph ≃g T) then 1 else 0) := by
      intro C
      by_cases hC : Nonempty (C.toSimpleGraph ≃g T)
      · rw [if_pos hC, mul_one]
        obtain ⟨ψ⟩ := hC
        have hC_ne : Nonempty (C.toSimpleGraph ≃g T) := ⟨ψ⟩
        have hC_card : C.toSimpleGraph.edgeFinset.card = T.edgeFinset.card :=
          card_edgeFinset_eq_of_iso ψ
        have hfilt_eq : (Finset.univ.filter fun e : X.edgeSet => edgeComp X e = C).card =
            T.edgeFinset.card := by
          rw [← hC_card, ← C.toSimpleGraph.card_edgeSet]
          refine Finset.card_bij (fun e he => (compEdgeSet_equiv X C) ⟨e, (Finset.mem_filter.mp he).2⟩)
            (fun _ _ => Finset.mem_univ _) ?_ ?_
          · intro e1 he1 e2 he2 heq
            have h1 := (compEdgeSet_equiv X C).injective heq
            exact congrArg Subtype.val h1
          · intro e' _
            let p := (compEdgeSet_equiv X C).symm e'
            refine ⟨p.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, p.2⟩, ?_⟩
            exact (compEdgeSet_equiv X C).apply_symm_apply e'
        have hcomp_card : (Finset.univ.filter fun e : X.edgeSet => C ≠ edgeComp X e).card =
            X.edgeFinset.card - T.edgeFinset.card := by
          have hdisj : Disjoint
              (Finset.univ.filter fun e : X.edgeSet => C ≠ edgeComp X e)
              (Finset.univ.filter fun e : X.edgeSet => edgeComp X e = C) := by
            rw [Finset.disjoint_left]
            intro e h1 h2
            rw [Finset.mem_filter] at h1 h2
            exact h1.2 h2.2.symm
          have hunion : (Finset.univ.filter fun e : X.edgeSet => C ≠ edgeComp X e) ∪
              (Finset.univ.filter fun e : X.edgeSet => edgeComp X e = C) = Finset.univ := by
            ext e
            simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
            tauto
          have hsum := congrArg Finset.card hunion
          rw [Finset.card_union_of_disjoint hdisj, Finset.card_univ, X.card_edgeSet, hfilt_eq] at hsum
          omega
        rw [← hcomp_card]
        trans ∑ e : X.edgeSet, if C ≠ edgeComp X e then (1 : ℕ) else 0
        · refine Finset.sum_congr rfl fun e _ => ?_
          by_cases he : C = edgeComp X e <;> simp [he, hC_ne]
        · rw [Finset.card_filter]
      · rw [if_neg hC, mul_zero]
        apply Finset.sum_eq_zero
        intro e _
        by_cases he : C = edgeComp X e <;> simp [he, hC]
    simp_rw [hterm, ← Finset.mul_sum, compCount, Finset.card_filter]
  · let term : X.ConnectedComponent → X.edgeSet → ℕ := fun C e =>
      if h : edgeComp X e = C then
        compCount T (C.toSimpleGraph.deleteEdges {((compEdgeSet_equiv X C) ⟨e, h⟩).val})
      else 0
    have hfib : ∑ e : X.edgeSet, compCount T ((edgeComp X e).toSimpleGraph.deleteEdges
        {((compEdgeSet_equiv X (edgeComp X e)) ⟨e, rfl⟩).val}) =
        ∑ C : X.ConnectedComponent, ∑ e ∈ Finset.univ.filter (fun e : X.edgeSet => edgeComp X e = C),
          term C e := by
      have h1 := Finset.sum_fiberwise (Finset.univ : Finset X.edgeSet) (edgeComp X)
        (fun e => compCount T ((edgeComp X e).toSimpleGraph.deleteEdges
          {((compEdgeSet_equiv X (edgeComp X e)) ⟨e, rfl⟩).val}))
      rw [← h1]
      refine Finset.sum_congr rfl fun C _ => ?_
      refine Finset.sum_congr rfl fun e he => ?_
      have heC : edgeComp X e = C := (Finset.mem_filter.mp he).2
      dsimp only [term]
      rw [dif_pos heC]
      subst heC
      rfl
    have hinner : ∀ C : X.ConnectedComponent,
        (∑ e ∈ Finset.univ.filter (fun e : X.edgeSet => edgeComp X e = C), term C e) =
        ∑ e ∈ C.toSimpleGraph.edgeFinset, compCount T (C.toSimpleGraph.deleteEdges {e}) := by
      intro C
      refine Finset.sum_bij
        (fun e he => ((compEdgeSet_equiv X C) ⟨e, (Finset.mem_filter.mp he).2⟩).val)
        (fun e he => (C.toSimpleGraph.mem_edgeFinset).mpr
          ((compEdgeSet_equiv X C) ⟨e, (Finset.mem_filter.mp he).2⟩).prop)
        (fun e1 he1 e2 he2 heq => by
          have hinj := (compEdgeSet_equiv X C).injective (Subtype.ext heq)
          exact congrArg Subtype.val hinj)
        ?_ (fun e he => by
          dsimp only [term]
          rw [dif_pos (Finset.mem_filter.mp he).2])
      intro e' he'
      let p := (compEdgeSet_equiv X C).symm ⟨e', (C.toSimpleGraph.mem_edgeFinset).mp he'⟩
      refine ⟨p.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, p.2⟩, ?_⟩
      exact congrArg Subtype.val ((compEdgeSet_equiv X C).apply_symm_apply _)
    have hzero : ∀ C : X.ConnectedComponent,
        C.toSimpleGraph.edgeFinset.card ≤ T.edgeFinset.card →
        ∑ e ∈ C.toSimpleGraph.edgeFinset, compCount T (C.toSimpleGraph.deleteEdges {e}) = 0 := by
      intro C hle
      apply Finset.sum_eq_zero
      intro e he
      rw [compCount, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro D hD
      rw [Finset.mem_filter] at hD
      obtain ⟨ψ⟩ := hD.2
      have hcardD : D.toSimpleGraph.edgeFinset.card = T.edgeFinset.card :=
        card_edgeFinset_eq_of_iso ψ
      have hD_le : D.toSimpleGraph.edgeFinset.card ≤ (C.toSimpleGraph.deleteEdges {e}).edgeFinset.card := by
        rw [← SimpleGraph.card_edgeSet, ← SimpleGraph.card_edgeSet]
        refine Fintype.card_le_of_injective
          (fun x => ⟨Sym2.map Subtype.val x.1, by
            refine Sym2.ind (fun a b h => ?_) x.1 x.2
            rw [mem_edgeSet] at h
            rw [Sym2.map_mk, mem_edgeSet]
            exact h⟩) ?_
        intro ⟨x₁, hx₁⟩ ⟨x₂, hx₂⟩ h
        exact Subtype.ext (Sym2.map.injective Subtype.val_injective (congrArg Subtype.val h))
      have hdel_lt : (C.toSimpleGraph.deleteEdges {e}).edgeFinset.card < C.toSimpleGraph.edgeFinset.card := by
        apply Finset.card_lt_card
        rw [Finset.ssubset_iff_subset_ne]
        refine ⟨fun x hx => ?_, fun heq => ?_⟩
        · rw [mem_edgeFinset, edgeSet_deleteEdges] at hx
          rw [mem_edgeFinset]
          exact hx.1
        · have he' : e ∈ (C.toSimpleGraph.deleteEdges {e}).edgeFinset := heq.symm ▸ he
          rw [mem_edgeFinset, edgeSet_deleteEdges] at he'
          exact he'.2 rfl
      omega
    have hsum_filt : ∑ C : X.ConnectedComponent,
        ∑ e ∈ C.toSimpleGraph.edgeFinset, compCount T (C.toSimpleGraph.deleteEdges {e}) =
        ∑ C ∈ Finset.univ.filter (fun C : X.ConnectedComponent =>
          T.edgeFinset.card < C.toSimpleGraph.edgeFinset.card),
        ∑ e ∈ C.toSimpleGraph.edgeFinset, compCount T (C.toSimpleGraph.deleteEdges {e}) := by
      rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
        (p := fun C : X.ConnectedComponent => T.edgeFinset.card < C.toSimpleGraph.edgeFinset.card)]
      have hz : ∑ C ∈ Finset.univ.filter (fun C : X.ConnectedComponent =>
          ¬ T.edgeFinset.card < C.toSimpleGraph.edgeFinset.card),
          ∑ e ∈ C.toSimpleGraph.edgeFinset, compCount T (C.toSimpleGraph.deleteEdges {e}) = 0 := by
        apply Finset.sum_eq_zero
        intro C hC
        rw [Finset.mem_filter] at hC
        exact hzero C (Nat.le_of_not_lt hC.2)
      rw [hz, add_zero]
    calc ∑ e : X.edgeSet, compCount T ((edgeComp X e).toSimpleGraph.deleteEdges
          {((compEdgeSet_equiv X (edgeComp X e)) ⟨e, rfl⟩).val})
        = ∑ C : X.ConnectedComponent, ∑ e ∈ Finset.univ.filter (fun e : X.edgeSet => edgeComp X e = C),
            term C e := hfib
      _ = ∑ C : X.ConnectedComponent, ∑ e ∈ C.toSimpleGraph.edgeFinset,
            compCount T (C.toSimpleGraph.deleteEdges {e}) := Finset.sum_congr rfl (fun C _ => hinner C)
      _ = _ := hsum_filt

private lemma iso_of_not_connected_isolateFree {W : Type} [Fintype W]
    (G' H' : SimpleGraph W) (hW : 4 ≤ Fintype.card W) (hE : 4 ≤ G'.edgeFinset.card)
    (hisoG : ∀ w : W, ∃ u : W, G'.Adj w u) (hisoH : ∀ w : W, ∃ u : W, H'.Adj w u)
    (hEH : EdgeHypomorphic G' H') (hNotConn : ¬ G'.Connected) :
    Nonempty (G' ≃g H') := by
  have hNotConnH : ¬ H'.Connected :=
    not_connected_of_edgeHypomorphic_not_connected G' H' hW hE hisoG hEH hNotConn
  obtain ⟨σ, hσ⟩ := hEH
  have hm_eq : G'.edgeFinset.card = H'.edgeFinset.card := by
    rw [← G'.card_edgeSet, ← H'.card_edgeSet]
    exact Fintype.card_congr σ
  let m := G'.edgeFinset.card
  have hcomp_bounds : ∀ (X : SimpleGraph W), (∀ w : W, ∃ u : W, X.Adj w u) →
      ¬ X.Connected → ∀ C : X.ConnectedComponent,
        1 ≤ C.toSimpleGraph.edgeFinset.card ∧ C.toSimpleGraph.edgeFinset.card < X.edgeFinset.card := by
    intro X hisoX hncX C
    have hpos : ∀ D : X.ConnectedComponent, 1 ≤ D.toSimpleGraph.edgeFinset.card := by
      intro D
      obtain ⟨a, ha⟩ := D.nonempty_supp
      obtain ⟨b, hab⟩ := hisoX a
      have hb : b ∈ D.supp := D.mem_supp_of_adj_mem_supp ha hab
      exact Finset.card_pos.mpr ⟨s(⟨a, ha⟩, ⟨b, hb⟩), (D.toSimpleGraph.mem_edgeFinset).mpr hab⟩
    have hex_other : ∃ D : X.ConnectedComponent, D ≠ C := by
      by_contra hno
      push Not at hno
      have hNon : Nonempty W := Fintype.card_pos_iff.mp (by omega)
      apply hncX
      refine ⟨fun a b => ?_⟩
      have ha : X.connectedComponentMk a = C := hno _
      have hb : X.connectedComponentMk b = C := hno _
      exact ConnectedComponent.exact (ha.trans hb.symm)
    obtain ⟨D, hDC⟩ := hex_other
    have h1 := hpos C
    have h2 := hpos D
    have hsum := sum_comp_card_edgeFinset X
    have hpair : C.toSimpleGraph.edgeFinset.card + D.toSimpleGraph.edgeFinset.card ≤ X.edgeFinset.card := by
      rw [← hsum]
      calc C.toSimpleGraph.edgeFinset.card + D.toSimpleGraph.edgeFinset.card
          = ∑ E ∈ ({C, D} : Finset X.ConnectedComponent), E.toSimpleGraph.edgeFinset.card := by
              rw [Finset.sum_pair hDC.symm]
        _ ≤ ∑ E : X.ConnectedComponent, E.toSimpleGraph.edgeFinset.card :=
            Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    omega
  have hG_bounds := hcomp_bounds G' hisoG hNotConn
  have hH_bounds := hcomp_bounds H' hisoH hNotConnH
  have hsum_del_eq : ∀ {k : ℕ} (T : SimpleGraph (Fin k)),
      ∑ e ∈ G'.edgeFinset, compCount T (G'.deleteEdges {e}) =
        ∑ e' ∈ H'.edgeFinset, compCount T (H'.deleteEdges {e'}) := by
    intro k T
    refine Finset.sum_bij (fun e _ => (σ ⟨e, (G'.mem_edgeFinset).mp ‹_›⟩).val) ?_ ?_ ?_ ?_
    · intro e he
      exact (H'.mem_edgeFinset).mpr (σ ⟨e, (G'.mem_edgeFinset).mp he⟩).prop
    · intro e1 he1 e2 he2 heq
      exact congrArg Subtype.val (σ.injective (Subtype.ext heq))
    · intro e' he'
      let e'sub : H'.edgeSet := ⟨e', (H'.mem_edgeFinset).mp he'⟩
      refine ⟨(σ.symm e'sub).val, (G'.mem_edgeFinset).mpr (σ.symm e'sub).prop, ?_⟩
      change (σ (σ.symm e'sub)).val = e'
      rw [σ.apply_symm_apply]
    · intro e he
      obtain ⟨φ⟩ := hσ ⟨e, (G'.mem_edgeFinset).mp he⟩
      exact compCount_eq_of_iso φ T
  have hdown : ∀ j : ℕ, ∀ k₀ : ℕ, m - j ≤ k₀ → 1 ≤ k₀ →
      ∀ {k : ℕ} (T : SimpleGraph (Fin k)), T.edgeFinset.card = k₀ →
      compCount T G' = compCount T H' := by
    intro j
    induction j with
    | zero =>
      intro k₀ hk₀ _ k T hTk
      have hk₀' : G'.edgeFinset.card ≤ k₀ := by simpa [m] using hk₀
      have hzG : compCount T G' = 0 := by
        rw [compCount, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
        intro C hC
        obtain ⟨ψ⟩ := (Finset.mem_filter.mp hC).2
        have heq : C.toSimpleGraph.edgeFinset.card = k₀ := (card_edgeFinset_eq_of_iso ψ).trans hTk
        have hlt := (hG_bounds C).2
        omega
      have hzH : compCount T H' = 0 := by
        rw [compCount, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
        intro D hD
        obtain ⟨ψ⟩ := (Finset.mem_filter.mp hD).2
        have heq : D.toSimpleGraph.edgeFinset.card = k₀ := (card_edgeFinset_eq_of_iso ψ).trans hTk
        have hlt := (hH_bounds D).2
        omega
      rw [hzG, hzH]
    | succ j ih =>
      intro k₀ hk₀ hk₀pos k T hTk
      by_cases hprev : m - j ≤ k₀
      · exact ih k₀ hprev hk₀pos T hTk
      · have hk₀lt : k₀ < m := by omega
        have hTpos : 1 ≤ T.edgeFinset.card := hTk ▸ hk₀pos
        have hG_sum := sum_compCount_deleteEdges G' T hTpos
        have hH_sum := sum_compCount_deleteEdges H' T hTpos
        let SG := Finset.univ.filter fun C : G'.ConnectedComponent =>
          T.edgeFinset.card < C.toSimpleGraph.edgeFinset.card
        let SH := Finset.univ.filter fun D : H'.ConnectedComponent =>
          T.edgeFinset.card < D.toSimpleGraph.edgeFinset.card
        have hSG_le : ∀ C ∈ SG, (SG.filter fun C' => Nonempty (C.toSimpleGraph ≃g C'.toSimpleGraph)).card ≤
            (SH.filter fun D => Nonempty (C.toSimpleGraph ≃g D.toSimpleGraph)).card := by
          intro C hC
          have hC_gt : m - j ≤ C.toSimpleGraph.edgeFinset.card := by
            have := (Finset.mem_filter.mp hC).2
            omega
          let eC : Fin (Fintype.card C.supp) ≃ C.supp := (Fintype.equivFin C.supp).symm
          let TC : SimpleGraph (Fin (Fintype.card C.supp)) := C.toSimpleGraph.comap eC
          have hTC_iso : TC ≃g C.toSimpleGraph := Iso.comap eC C.toSimpleGraph
          have hTC_card : TC.edgeFinset.card = C.toSimpleGraph.edgeFinset.card :=
            card_edgeFinset_eq_of_iso hTC_iso
          have hcnt_eq : compCount TC G' = compCount TC H' :=
            ih C.toSimpleGraph.edgeFinset.card hC_gt (hG_bounds C).1 TC hTC_card
          have h_left : (SG.filter fun C' => Nonempty (C.toSimpleGraph ≃g C'.toSimpleGraph)).card =
              compCount TC G' := by
            unfold compCount
            congr 1
            ext C'
            simp only [SG, Finset.mem_filter, Finset.mem_univ, true_and]
            constructor
            · rintro ⟨_, ⟨ψ⟩⟩
              exact ⟨ψ.symm.trans hTC_iso.symm⟩
            · rintro ⟨ψ⟩
              have hcard_eq := card_edgeFinset_eq_of_iso (ψ.trans hTC_iso)
              have hC_lt := (Finset.mem_filter.mp hC).2
              exact ⟨hcard_eq ▸ hC_lt, ⟨(ψ.trans hTC_iso).symm⟩⟩
          have h_right : (SH.filter fun D => Nonempty (C.toSimpleGraph ≃g D.toSimpleGraph)).card =
              compCount TC H' := by
            unfold compCount
            congr 1
            ext D
            simp only [SH, Finset.mem_filter, Finset.mem_univ, true_and]
            constructor
            · rintro ⟨_, ⟨ψ⟩⟩
              exact ⟨ψ.symm.trans hTC_iso.symm⟩
            · rintro ⟨ψ⟩
              have hcard_eq := card_edgeFinset_eq_of_iso (ψ.trans hTC_iso)
              have hC_lt := (Finset.mem_filter.mp hC).2
              exact ⟨hcard_eq ▸ hC_lt, ⟨(ψ.trans hTC_iso).symm⟩⟩
          rw [h_left, h_right, hcnt_eq]
        have hSH_le : ∀ D ∈ SH, (SH.filter fun D' => Nonempty (D.toSimpleGraph ≃g D'.toSimpleGraph)).card ≤
            (SG.filter fun C => Nonempty (C.toSimpleGraph ≃g D.toSimpleGraph)).card := by
          intro D hD
          have hD_gt : m - j ≤ D.toSimpleGraph.edgeFinset.card := by
            have := (Finset.mem_filter.mp hD).2
            omega
          let eD : Fin (Fintype.card D.supp) ≃ D.supp := (Fintype.equivFin D.supp).symm
          let TD : SimpleGraph (Fin (Fintype.card D.supp)) := D.toSimpleGraph.comap eD
          have hTD_iso : TD ≃g D.toSimpleGraph := Iso.comap eD D.toSimpleGraph
          have hTD_card : TD.edgeFinset.card = D.toSimpleGraph.edgeFinset.card :=
            card_edgeFinset_eq_of_iso hTD_iso
          have hcnt_eq : compCount TD G' = compCount TD H' :=
            ih D.toSimpleGraph.edgeFinset.card hD_gt (hH_bounds D).1 TD hTD_card
          have h_left : (SH.filter fun D' => Nonempty (D.toSimpleGraph ≃g D'.toSimpleGraph)).card =
              compCount TD H' := by
            unfold compCount
            congr 1
            ext D'
            simp only [SH, Finset.mem_filter, Finset.mem_univ, true_and]
            constructor
            · rintro ⟨_, ⟨ψ⟩⟩
              exact ⟨ψ.symm.trans hTD_iso.symm⟩
            · rintro ⟨ψ⟩
              have hcard_eq := card_edgeFinset_eq_of_iso (ψ.trans hTD_iso)
              have hD_lt := (Finset.mem_filter.mp hD).2
              exact ⟨hcard_eq ▸ hD_lt, ⟨(ψ.trans hTD_iso).symm⟩⟩
          have h_right : (SG.filter fun C => Nonempty (C.toSimpleGraph ≃g D.toSimpleGraph)).card =
              compCount TD G' := by
            unfold compCount
            congr 1
            ext C
            simp only [SG, Finset.mem_filter, Finset.mem_univ, true_and]
            constructor
            · rintro ⟨_, ⟨ψ⟩⟩
              exact ⟨ψ.trans hTD_iso.symm⟩
            · rintro ⟨ψ⟩
              have hcard_eq := card_edgeFinset_eq_of_iso (ψ.trans hTD_iso)
              have hD_lt := (Finset.mem_filter.mp hD).2
              exact ⟨hcard_eq ▸ hD_lt, ⟨ψ.trans hTD_iso⟩⟩
          rw [h_left, h_right, hcnt_eq]
        obtain ⟨f_big, hf_big⟩ := exists_bij_of_rel_counts SG SH
          (fun C1 C2 => Nonempty (C1.toSimpleGraph ≃g C2.toSimpleGraph))
          (fun D1 D2 => Nonempty (D1.toSimpleGraph ≃g D2.toSimpleGraph))
          (fun C D => Nonempty (C.toSimpleGraph ≃g D.toSimpleGraph))
          (fun C => ⟨Iso.refl⟩) (fun D => ⟨Iso.refl⟩)
          (fun ⟨h⟩ => ⟨h.symm⟩) (fun ⟨h⟩ => ⟨h.symm⟩)
          (fun ⟨h1⟩ ⟨h2⟩ => ⟨h1.trans h2⟩) (fun ⟨h1⟩ ⟨h2⟩ => ⟨h1.trans h2⟩)
          (fun ⟨h1⟩ ⟨h2⟩ => ⟨h1.trans h2.symm⟩) (fun ⟨h1⟩ ⟨h2⟩ => ⟨h1.symm.trans h2⟩)
          hSG_le hSH_le
        have hbig_sum : ∑ C ∈ SG, ∑ e ∈ C.toSimpleGraph.edgeFinset, compCount T (C.toSimpleGraph.deleteEdges {e}) =
            ∑ D ∈ SH, ∑ e ∈ D.toSimpleGraph.edgeFinset, compCount T (D.toSimpleGraph.deleteEdges {e}) := by
          have hG_att : ∑ C ∈ SG, ∑ e ∈ C.toSimpleGraph.edgeFinset, compCount T (C.toSimpleGraph.deleteEdges {e}) =
              ∑ C : SG, ∑ e ∈ C.1.toSimpleGraph.edgeFinset, compCount T (C.1.toSimpleGraph.deleteEdges {e}) :=
            (Finset.sum_coe_sort SG (fun C => ∑ e ∈ C.toSimpleGraph.edgeFinset,
              compCount T (C.toSimpleGraph.deleteEdges {e}))).symm
          have hH_att : ∑ D ∈ SH, ∑ e ∈ D.toSimpleGraph.edgeFinset, compCount T (D.toSimpleGraph.deleteEdges {e}) =
              ∑ D : SH, ∑ e ∈ D.1.toSimpleGraph.edgeFinset, compCount T (D.1.toSimpleGraph.deleteEdges {e}) :=
            (Finset.sum_coe_sort SH (fun D => ∑ e ∈ D.toSimpleGraph.edgeFinset,
              compCount T (D.toSimpleGraph.deleteEdges {e}))).symm
          rw [hG_att, hH_att]
          refine Fintype.sum_equiv f_big _ _ fun C => ?_
          obtain ⟨ψ⟩ := hf_big C
          refine Finset.sum_bij (fun e _ => e.map ψ) ?_ ?_ ?_ ?_
          · intro e he
            exact (f_big C).1.toSimpleGraph.mem_edgeFinset.mpr
              (ψ.map_mem_edgeSet_iff.mpr (C.1.toSimpleGraph.mem_edgeFinset.mp he))
          · intro e1 _ e2 _ heq
            exact (Sym2.map.injective ψ.injective) heq
          · intro e' he'
            refine ⟨e'.map ψ.symm, C.1.toSimpleGraph.mem_edgeFinset.mpr
              (ψ.symm.map_mem_edgeSet_iff.mpr ((f_big C).1.toSimpleGraph.mem_edgeFinset.mp he')), ?_⟩
            rw [Sym2.map_map]
            have hcomp : (ψ.toEquiv ∘ ψ.symm.toEquiv) = id :=
              funext (fun x => ψ.apply_symm_apply x)
            simp [hcomp]
          · intro e _
            exact compCount_eq_of_iso (iso_deleteEdges_singleton ψ e) T
        have heq_all := hsum_del_eq T
        rw [hG_sum, hH_sum] at heq_all
        change (m - T.edgeFinset.card) * compCount T G' +
            ∑ C ∈ SG, ∑ e ∈ C.toSimpleGraph.edgeFinset, compCount T (C.toSimpleGraph.deleteEdges {e}) =
            (H'.edgeFinset.card - T.edgeFinset.card) * compCount T H' +
            ∑ D ∈ SH, ∑ e ∈ D.toSimpleGraph.edgeFinset, compCount T (D.toSimpleGraph.deleteEdges {e}) at heq_all
        rw [← hm_eq, hbig_sum] at heq_all
        have hmul_eq : (m - T.edgeFinset.card) * compCount T G' =
            (m - T.edgeFinset.card) * compCount T H' := Nat.add_right_cancel heq_all
        exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < m - T.edgeFinset.card) hmul_eq
  have hall_comp : ∀ C : G'.ConnectedComponent,
      ((Finset.univ : Finset G'.ConnectedComponent).filter
        fun C' => Nonempty (C.toSimpleGraph ≃g C'.toSimpleGraph)).card ≤
      ((Finset.univ : Finset H'.ConnectedComponent).filter
        fun D => Nonempty (C.toSimpleGraph ≃g D.toSimpleGraph)).card := by
    intro C
    let eC : Fin (Fintype.card C.supp) ≃ C.supp := (Fintype.equivFin C.supp).symm
    let TC : SimpleGraph (Fin (Fintype.card C.supp)) := C.toSimpleGraph.comap eC
    have hTC_iso : TC ≃g C.toSimpleGraph := Iso.comap eC C.toSimpleGraph
    have hTC_card : TC.edgeFinset.card = C.toSimpleGraph.edgeFinset.card :=
      card_edgeFinset_eq_of_iso hTC_iso
    have hcnt := hdown m C.toSimpleGraph.edgeFinset.card (by omega) (hG_bounds C).1 TC hTC_card
    have h1 : ((Finset.univ : Finset G'.ConnectedComponent).filter
        fun C' => Nonempty (C.toSimpleGraph ≃g C'.toSimpleGraph)).card = compCount TC G' := by
      unfold compCount
      congr 1
      ext C'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨ψ⟩; exact ⟨ψ.symm.trans hTC_iso.symm⟩
      · rintro ⟨ψ⟩; exact ⟨(ψ.trans hTC_iso).symm⟩
    have h2 : ((Finset.univ : Finset H'.ConnectedComponent).filter
        fun D => Nonempty (C.toSimpleGraph ≃g D.toSimpleGraph)).card = compCount TC H' := by
      unfold compCount
      congr 1
      ext D
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨ψ⟩; exact ⟨ψ.symm.trans hTC_iso.symm⟩
      · rintro ⟨ψ⟩; exact ⟨(ψ.trans hTC_iso).symm⟩
    rw [h1, h2, hcnt]
  have hall_compH : ∀ D : H'.ConnectedComponent,
      ((Finset.univ : Finset H'.ConnectedComponent).filter
        fun D' => Nonempty (D.toSimpleGraph ≃g D'.toSimpleGraph)).card ≤
      ((Finset.univ : Finset G'.ConnectedComponent).filter
        fun C => Nonempty (C.toSimpleGraph ≃g D.toSimpleGraph)).card := by
    intro D
    let eD : Fin (Fintype.card D.supp) ≃ D.supp := (Fintype.equivFin D.supp).symm
    let TD : SimpleGraph (Fin (Fintype.card D.supp)) := D.toSimpleGraph.comap eD
    have hTD_iso : TD ≃g D.toSimpleGraph := Iso.comap eD D.toSimpleGraph
    have hTD_card : TD.edgeFinset.card = D.toSimpleGraph.edgeFinset.card :=
      card_edgeFinset_eq_of_iso hTD_iso
    have hcnt := hdown m D.toSimpleGraph.edgeFinset.card (by omega) (hH_bounds D).1 TD hTD_card
    have h1 : ((Finset.univ : Finset H'.ConnectedComponent).filter
        fun D' => Nonempty (D.toSimpleGraph ≃g D'.toSimpleGraph)).card = compCount TD H' := by
      unfold compCount
      congr 1
      ext D'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨ψ⟩; exact ⟨ψ.symm.trans hTD_iso.symm⟩
      · rintro ⟨ψ⟩; exact ⟨(ψ.trans hTD_iso).symm⟩
    have h2 : ((Finset.univ : Finset G'.ConnectedComponent).filter
        fun C => Nonempty (C.toSimpleGraph ≃g D.toSimpleGraph)).card = compCount TD G' := by
      unfold compCount
      congr 1
      ext C
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨ψ⟩; exact ⟨ψ.trans hTD_iso.symm⟩
      · rintro ⟨ψ⟩; exact ⟨ψ.trans hTD_iso⟩
    rw [h1, h2, hcnt]
  obtain ⟨f_sub, hf_sub⟩ := exists_bij_of_rel_counts
    (Finset.univ : Finset G'.ConnectedComponent) (Finset.univ : Finset H'.ConnectedComponent)
    (fun C1 C2 => Nonempty (C1.toSimpleGraph ≃g C2.toSimpleGraph))
    (fun D1 D2 => Nonempty (D1.toSimpleGraph ≃g D2.toSimpleGraph))
    (fun C D => Nonempty (C.toSimpleGraph ≃g D.toSimpleGraph))
    (fun C => ⟨Iso.refl⟩) (fun D => ⟨Iso.refl⟩)
    (fun ⟨h⟩ => ⟨h.symm⟩) (fun ⟨h⟩ => ⟨h.symm⟩)
    (fun ⟨h1⟩ ⟨h2⟩ => ⟨h1.trans h2⟩) (fun ⟨h1⟩ ⟨h2⟩ => ⟨h1.trans h2⟩)
    (fun ⟨h1⟩ ⟨h2⟩ => ⟨h1.trans h2.symm⟩) (fun ⟨h1⟩ ⟨h2⟩ => ⟨h1.symm.trans h2⟩)
    (fun C _ => hall_comp C) (fun D _ => hall_compH D)
  let α : G'.ConnectedComponent ≃ H'.ConnectedComponent := {
    toFun := fun C => (f_sub ⟨C, Finset.mem_univ C⟩).1
    invFun := fun D => (f_sub.symm ⟨D, Finset.mem_univ D⟩).1
    left_inv := fun C => congrArg Subtype.val (f_sub.symm_apply_apply ⟨C, Finset.mem_univ C⟩)
    right_inv := fun D => congrArg Subtype.val (f_sub.apply_symm_apply ⟨D, Finset.mem_univ D⟩)
  }
  have hα : ∀ C : G'.ConnectedComponent, C.toSimpleGraph ≃g (α C).toSimpleGraph :=
    fun C => Classical.choice (hf_sub ⟨C, Finset.mem_univ C⟩)
  let toW_in : ∀ C : G'.ConnectedComponent, ∀ v : W, v ∈ C.supp → W :=
    fun C v hv => (hα C ⟨v, hv⟩).1
  let toW : W → W := fun v => toW_in (G'.connectedComponentMk v) v ConnectedComponent.connectedComponentMk_mem
  have hto_in_comp : ∀ C v hv, H'.connectedComponentMk (toW_in C v hv) = α C := by
    intro C v hv
    exact (ConnectedComponent.mem_supp_iff (α C) (toW_in C v hv)).mp (hα C ⟨v, hv⟩).2
  have hto_comp : ∀ v : W, H'.connectedComponentMk (toW v) = α (G'.connectedComponentMk v) :=
    fun v => hto_in_comp _ _ _
  have hto_eq : ∀ C v hv, toW v = toW_in C v hv := by
    intro C v hv
    have hC : G'.connectedComponentMk v = C := (ConnectedComponent.mem_supp_iff C v).mp hv
    subst hC
    rfl
  have hbij : Function.Bijective toW := by
    constructor
    · intro u v heq
      have hcompH : H'.connectedComponentMk (toW u) = H'.connectedComponentMk (toW v) :=
        congrArg H'.connectedComponentMk heq
      rw [hto_comp u, hto_comp v] at hcompH
      have hcompG : G'.connectedComponentMk u = G'.connectedComponentMk v := α.injective hcompH
      let C := G'.connectedComponentMk u
      have hu : u ∈ C.supp := ConnectedComponent.connectedComponentMk_mem
      have hv : v ∈ C.supp := (ConnectedComponent.mem_supp_iff C v).mpr hcompG.symm
      rw [hto_eq C u hu, hto_eq C v hv] at heq
      have hinj := (hα C).injective (Subtype.ext heq)
      exact congrArg Subtype.val hinj
    · intro w
      let C := α.symm (H'.connectedComponentMk w)
      have hw : w ∈ (α C).supp := by
        rw [α.apply_symm_apply]
        exact ConnectedComponent.connectedComponentMk_mem
      let u := (hα C).symm ⟨w, hw⟩
      refine ⟨u.1, ?_⟩
      rw [hto_eq C u.1 u.2]
      change ((hα C) u).1 = w
      rw [(hα C).apply_symm_apply]
  refine ⟨⟨Equiv.ofBijective toW hbij, fun {x y} => ?_⟩⟩
  change H'.Adj (toW x) (toW y) ↔ G'.Adj x y
  constructor
  · intro hadjH
    have hcompH : H'.connectedComponentMk (toW x) = H'.connectedComponentMk (toW y) :=
      ConnectedComponent.connectedComponentMk_eq_of_adj hadjH
    rw [hto_comp x, hto_comp y] at hcompH
    have hcompG : G'.connectedComponentMk x = G'.connectedComponentMk y := α.injective hcompH
    let C := G'.connectedComponentMk x
    have hx : x ∈ C.supp := ConnectedComponent.connectedComponentMk_mem
    have hy : y ∈ C.supp := (ConnectedComponent.mem_supp_iff C y).mpr hcompG.symm
    rw [hto_eq C x hx, hto_eq C y hy] at hadjH
    exact (hα C).map_rel_iff.mp hadjH
  · intro hadjG
    have hcompG : G'.connectedComponentMk x = G'.connectedComponentMk y :=
      ConnectedComponent.connectedComponentMk_eq_of_adj hadjG
    let C := G'.connectedComponentMk x
    have hx : x ∈ C.supp := ConnectedComponent.connectedComponentMk_mem
    have hy : y ∈ C.supp := (ConnectedComponent.mem_supp_iff C y).mpr hcompG.symm
    rw [hto_eq C x hx, hto_eq C y hy]
    exact (hα C).map_rel_iff.mpr hadjG

end DisconnectedCase

section ConnectedCase

private noncomputable def subCardCount {W : Type*} [Fintype W] {k : ℕ} (F : SimpleGraph (Fin k))
    (X : SimpleGraph W) : ℕ :=
  ∑ v : W, (Finset.univ.filter fun K : SimpleGraph ({v}ᶜ : Set W) =>
    K ≤ X.induce {v}ᶜ ∧ Nonempty (K ≃g F)).card

private noncomputable def cardCount {W : Type*} [Fintype W] {k : ℕ} (F : SimpleGraph (Fin k))
    (X : SimpleGraph W) : ℕ :=
  (Finset.univ.filter fun v : W => Nonempty (X.induce {v}ᶜ ≃g F)).card

private lemma subCardCount_eq_of_iso {W U : Type*} [Fintype W] [Fintype U]
    {X : SimpleGraph W} {Y : SimpleGraph U} (φ : X ≃g Y) {k : ℕ} (F : SimpleGraph (Fin k)) :
    subCardCount F X = subCardCount F Y := by
  unfold subCardCount
  refine Fintype.sum_equiv φ.toEquiv _ _ fun v => ?_
  let e_v : ({v}ᶜ : Set W) ≃ ({φ v}ᶜ : Set U) :=
    Equiv.subtypeEquiv φ.toEquiv (fun x => by simp [φ.injective.eq_iff])
  refine Finset.card_bij (fun K _ => K.comap e_v.symm) ?_ ?_ ?_
  · intro K hK
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hK ⊢
    obtain ⟨hK_le, ⟨ψ⟩⟩ := hK
    have h_iso : K.comap e_v.symm ≃g K := Iso.comap e_v.symm K
    refine ⟨fun a b hab => ?_, ⟨h_iso.trans ψ⟩⟩
    change Y.Adj a.1 b.1
    have h1 : X.Adj (e_v.symm a).1 (e_v.symm b).1 := hK_le hab
    have h2 : Y.Adj (φ (e_v.symm a).1) (φ (e_v.symm b).1) := φ.map_rel_iff.mpr h1
    have ha : φ (e_v.symm a).1 = a.1 := by
      change (e_v (e_v.symm a)).1 = a.1
      rw [e_v.apply_symm_apply]
    have hb : φ (e_v.symm b).1 = b.1 := by
      change (e_v (e_v.symm b)).1 = b.1
      rw [e_v.apply_symm_apply]
    rwa [ha, hb] at h2
  · intro K1 _ K2 _ heq
    have h1 := congrArg (SimpleGraph.comap e_v) heq
    have hcomp : ∀ K : SimpleGraph ({v}ᶜ : Set W), (K.comap e_v.symm).comap e_v = K := by
      intro K
      ext a b
      simp
    simpa [hcomp] using h1
  · intro K' hK'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hK'
    obtain ⟨hK'_le, ⟨ψ⟩⟩ := hK'
    let K := K'.comap e_v
    have h_iso : K ≃g K' := Iso.comap e_v K'
    have hK_le : K ≤ X.induce {v}ᶜ := by
      intro a b hab
      change X.Adj a.1 b.1
      exact φ.map_rel_iff.mp (hK'_le hab)
    have hback : K.comap e_v.symm = K' := by
      ext a b
      simp [K]
    exact ⟨K, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hK_le, ⟨h_iso.trans ψ⟩⟩, hback⟩

private lemma sum_subCardCount_deleteEdges {W : Type*} [Fintype W] (X : SimpleGraph W)
    {k : ℕ} (F : SimpleGraph (Fin k)) :
    ∑ e ∈ X.edgeFinset, subCardCount F (X.deleteEdges {e}) =
      (X.edgeFinset.card - F.edgeFinset.card) * subCardCount F X := by
  unfold subCardCount
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp_rw [Finset.card_filter]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun K _ => ?_
  by_cases hK : K ≤ X.induce {v}ᶜ ∧ Nonempty (K ≃g F)
  · rw [if_pos hK, mul_one]
    obtain ⟨hK_le, ⟨ψ⟩⟩ := hK
    let EK : Finset (Sym2 W) := K.edgeFinset.image (Sym2.map Subtype.val)
    have hEK_sub : EK ⊆ X.edgeFinset := by
      intro e he
      rw [Finset.mem_image] at he
      obtain ⟨e', he', rfl⟩ := he
      obtain ⟨a, b, rfl⟩ : ∃ a b, e' = s(a, b) := Sym2.ind (fun a b => ⟨a, b, rfl⟩) e'
      rw [Sym2.map_mk]
      exact (X.mem_edgeFinset).mpr (hK_le ((K.mem_edgeFinset).mp he'))
    have hEK_card : EK.card = F.edgeFinset.card := by
      rw [Finset.card_image_of_injective _ (Sym2.map.injective Subtype.val_injective)]
      exact card_edgeFinset_eq_of_iso ψ
    have hiff : ∀ e ∈ X.edgeFinset,
        (K ≤ (X.deleteEdges {e}).induce {v}ᶜ ∧ Nonempty (K ≃g F)) ↔ e ∉ EK := by
      intro e _
      constructor
      · rintro ⟨hle, _⟩ he_mem
        rw [Finset.mem_image] at he_mem
        obtain ⟨e', he', rfl⟩ := he_mem
        obtain ⟨a, b, rfl⟩ : ∃ a b, e' = s(a, b) := Sym2.ind (fun a b => ⟨a, b, rfl⟩) e'
        have hadjK : K.Adj a b := (K.mem_edgeFinset).mp he'
        have hadj_del := hle hadjK
        rw [induce_adj, deleteEdges_adj, Set.mem_singleton_iff, Sym2.map_mk] at hadj_del
        exact hadj_del.2 rfl
      · intro hnot
        refine ⟨fun {a b} hab => ?_, ⟨ψ⟩⟩
        rw [induce_adj, deleteEdges_adj, Set.mem_singleton_iff]
        refine ⟨hK_le hab, fun heq => hnot ?_⟩
        rw [Finset.mem_image]
        exact ⟨s(a, b), (K.mem_edgeFinset).mpr hab, by rw [Sym2.map_mk, heq]⟩
    trans ∑ e ∈ X.edgeFinset, (if e ∈ X.edgeFinset \ EK then (1 : ℕ) else 0)
    · refine Finset.sum_congr rfl fun e he => ?_
      by_cases h : K ≤ (X.deleteEdges {e}).induce {v}ᶜ ∧ Nonempty (K ≃g F)
      · have hne : e ∉ EK := (hiff e he).mp h
        simp [h, he, hne]
      · have hne : e ∈ EK := by
          by_contra hn
          exact h ((hiff e he).mpr hn)
        simp [h, hne]
    · rw [← Finset.card_filter]
      calc (X.edgeFinset.filter fun e => e ∈ X.edgeFinset \ EK).card
          = (X.edgeFinset \ EK).card := by
            congr 1
            ext e
            simp only [Finset.mem_filter, Finset.mem_sdiff]
            tauto
        _ = X.edgeFinset.card - F.edgeFinset.card := by
            rw [Finset.card_sdiff_of_subset hEK_sub, hEK_card]
  · rw [if_neg hK, mul_zero]
    apply Finset.sum_eq_zero
    intro e _
    have hnot : ¬ (K ≤ (X.deleteEdges {e}).induce {v}ᶜ ∧ Nonempty (K ≃g F)) := by
      rintro ⟨hle, hψ⟩
      exact hK ⟨fun {a b} hab => (deleteEdges_le {e}) (hle hab), hψ⟩
    rw [if_neg hnot]

private lemma subCardCount_decomp {W : Type*} [Fintype W] {k : ℕ}
    (F : SimpleGraph (Fin k)) (X : SimpleGraph W) :
    subCardCount F X = cardCount F X +
      ∑ v ∈ Finset.univ.filter (fun v : W => F.edgeFinset.card < (X.induce {v}ᶜ).edgeFinset.card),
        (Finset.univ.filter fun K : SimpleGraph ({v}ᶜ : Set W) =>
          K ≤ X.induce {v}ᶜ ∧ Nonempty (K ≃g F)).card := by
  unfold subCardCount cardCount
  let sEq := Finset.univ.filter fun v : W => (X.induce {v}ᶜ).edgeFinset.card = F.edgeFinset.card
  let sGt := Finset.univ.filter fun v : W => F.edgeFinset.card < (X.induce {v}ᶜ).edgeFinset.card
  let sLt := Finset.univ.filter fun v : W => (X.induce {v}ᶜ).edgeFinset.card < F.edgeFinset.card
  have hpart : ∑ v : W, (Finset.univ.filter fun K : SimpleGraph ({v}ᶜ : Set W) =>
      K ≤ X.induce {v}ᶜ ∧ Nonempty (K ≃g F)).card =
      (∑ v ∈ sEq, (Finset.univ.filter fun K : SimpleGraph ({v}ᶜ : Set W) =>
        K ≤ X.induce {v}ᶜ ∧ Nonempty (K ≃g F)).card) +
      (∑ v ∈ sGt, (Finset.univ.filter fun K : SimpleGraph ({v}ᶜ : Set W) =>
        K ≤ X.induce {v}ᶜ ∧ Nonempty (K ≃g F)).card) +
      (∑ v ∈ sLt, (Finset.univ.filter fun K : SimpleGraph ({v}ᶜ : Set W) =>
        K ≤ X.induce {v}ᶜ ∧ Nonempty (K ≃g F)).card) := by
    have hdisj1 : Disjoint sEq sGt := by
      rw [Finset.disjoint_left]
      intro v h1 h2
      dsimp only [sEq, sGt] at h1 h2
      rw [Finset.mem_filter] at h1 h2
      omega
    have hdisj2 : Disjoint (sEq ∪ sGt) sLt := by
      rw [Finset.disjoint_left]
      intro v h1 h2
      dsimp only [sEq, sGt, sLt] at h1 h2
      simp only [Finset.mem_union, Finset.mem_filter] at h1 h2
      omega
    have hunion : (sEq ∪ sGt) ∪ sLt = Finset.univ := by
      ext v
      dsimp only [sEq, sGt, sLt]
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      omega
    rw [← hunion, Finset.sum_union hdisj2, Finset.sum_union hdisj1]
  have hLt_zero : ∑ v ∈ sLt, (Finset.univ.filter fun K : SimpleGraph ({v}ᶜ : Set W) =>
      K ≤ X.induce {v}ᶜ ∧ Nonempty (K ≃g F)).card = 0 := by
    apply Finset.sum_eq_zero
    intro v hv
    dsimp only [sLt] at hv
    rw [Finset.mem_filter] at hv
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro K hK
    rw [Finset.mem_filter] at hK
    obtain ⟨hK_le, ⟨ψ⟩⟩ := hK.2
    have hle : K.edgeFinset.card ≤ (X.induce {v}ᶜ).edgeFinset.card := by
      apply Finset.card_le_card
      intro e he
      rw [mem_edgeFinset] at he ⊢
      obtain ⟨a, b, rfl⟩ : ∃ a b, e = s(a, b) := Sym2.ind (fun a b => ⟨a, b, rfl⟩) e
      exact hK_le he
    have heq := card_edgeFinset_eq_of_iso ψ
    omega
  have hEq_eq : ∑ v ∈ sEq, (Finset.univ.filter fun K : SimpleGraph ({v}ᶜ : Set W) =>
      K ≤ X.induce {v}ᶜ ∧ Nonempty (K ≃g F)).card =
      (Finset.univ.filter fun v : W => Nonempty (X.induce {v}ᶜ ≃g F)).card := by
    have hterm : ∀ v ∈ sEq, (Finset.univ.filter fun K : SimpleGraph ({v}ᶜ : Set W) =>
        K ≤ X.induce {v}ᶜ ∧ Nonempty (K ≃g F)).card =
        if Nonempty (X.induce {v}ᶜ ≃g F) then 1 else 0 := by
      intro v hv
      have hcardv : (X.induce {v}ᶜ).edgeFinset.card = F.edgeFinset.card :=
        (Finset.mem_filter.mp hv).2
      by_cases hiso : Nonempty (X.induce {v}ᶜ ≃g F)
      · rw [if_pos hiso]
        have huniq : Finset.univ.filter (fun K : SimpleGraph ({v}ᶜ : Set W) =>
            K ≤ X.induce {v}ᶜ ∧ Nonempty (K ≃g F)) = {X.induce {v}ᶜ} := by
          ext K
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
          constructor
          · rintro ⟨hK_le, ⟨ψ⟩⟩
            have hsub : K.edgeFinset ⊆ (X.induce {v}ᶜ).edgeFinset := by
              intro e he
              rw [mem_edgeFinset] at he ⊢
              obtain ⟨a, b, rfl⟩ : ∃ a b, e = s(a, b) := Sym2.ind (fun a b => ⟨a, b, rfl⟩) e
              exact hK_le he
            have hcard_eq : K.edgeFinset.card = (X.induce {v}ᶜ).edgeFinset.card :=
              (card_edgeFinset_eq_of_iso ψ).trans hcardv.symm
            have heq_set : K.edgeFinset = (X.induce {v}ᶜ).edgeFinset :=
              Finset.eq_of_subset_of_card_le hsub (by omega)
            ext a b
            have := congrArg (fun S : Finset (Sym2 ({v}ᶜ : Set W)) => s(a, b) ∈ S) heq_set
            simpa only [mem_edgeFinset, mem_edgeSet, eq_iff_iff] using this
          · rintro rfl
            exact ⟨le_rfl, hiso⟩
        rw [huniq, Finset.card_singleton]
      · rw [if_neg hiso, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
        intro K hK
        rw [Finset.mem_filter] at hK
        obtain ⟨hK_le, ⟨ψ⟩⟩ := hK.2
        have hsub : K.edgeFinset ⊆ (X.induce {v}ᶜ).edgeFinset := by
          intro e he
          rw [mem_edgeFinset] at he ⊢
          obtain ⟨a, b, rfl⟩ : ∃ a b, e = s(a, b) := Sym2.ind (fun a b => ⟨a, b, rfl⟩) e
          exact hK_le he
        have hcard_eq : K.edgeFinset.card = (X.induce {v}ᶜ).edgeFinset.card :=
          (card_edgeFinset_eq_of_iso ψ).trans hcardv.symm
        have heq_set : K.edgeFinset = (X.induce {v}ᶜ).edgeFinset :=
          Finset.eq_of_subset_of_card_le hsub (by omega)
        have hK_eq : K = X.induce {v}ᶜ := by
          ext a b
          have := congrArg (fun S : Finset (Sym2 ({v}ᶜ : Set W)) => s(a, b) ∈ S) heq_set
          simpa only [mem_edgeFinset, mem_edgeSet, eq_iff_iff] using this
        exact hiso ⟨hK_eq ▸ ψ⟩
    rw [Finset.sum_congr rfl hterm, ← Finset.card_filter]
    congr 1
    ext v
    simp only [sEq, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨_, h⟩; exact h
    · intro ⟨ψ⟩; exact ⟨card_edgeFinset_eq_of_iso ψ, ⟨ψ⟩⟩
  rw [hpart, hLt_zero, add_zero, hEq_eq]

private lemma hypomorphic_of_isolateFree {W : Type} [Fintype W]
    (G' H' : SimpleGraph W) (hW : 4 ≤ Fintype.card W) (hE : 4 ≤ G'.edgeFinset.card)
    (hisoG : ∀ w : W, ∃ u : W, G'.Adj w u) (hisoH : ∀ w : W, ∃ u : W, H'.Adj w u)
    (hEH : EdgeHypomorphic G' H') :
    Hypomorphic G' H' := by
  obtain ⟨σ, hσ⟩ := hEH
  have hm_eq : G'.edgeFinset.card = H'.edgeFinset.card := by
    rw [← G'.card_edgeSet, ← H'.card_edgeSet]
    exact Fintype.card_congr σ
  let m := G'.edgeFinset.card
  let n := Fintype.card W
  have hcard_compl : ∀ v : W, Fintype.card ({v}ᶜ : Set W) = n - 1 := by
    intro v
    rw [Fintype.card_compl_set]
    have h1 : Fintype.card ({v} : Set W) = 1 := Fintype.card_unique
    rw [h1]
  have hinduce_lt : ∀ (X : SimpleGraph W), (∀ w : W, ∃ u : W, X.Adj w u) →
      ∀ v : W, (X.induce {v}ᶜ).edgeFinset.card < X.edgeFinset.card := by
    intro X hisoX v
    rw [X.card_edgeFinset_induce_compl_singleton v, X.card_edgeFinset_deleteIncidenceSet v]
    have hdpos : 0 < X.degree v := (degree_pos_iff_exists_adj X v).mpr (hisoX v)
    have hdle : X.degree v ≤ X.edgeFinset.card := degree_le_card_edgeFinset X v
    omega
  have hsum_del_eq : ∀ F : SimpleGraph (Fin (n - 1)),
      ∑ e ∈ G'.edgeFinset, subCardCount F (G'.deleteEdges {e}) =
        ∑ e' ∈ H'.edgeFinset, subCardCount F (H'.deleteEdges {e'}) := by
    intro F
    refine Finset.sum_bij (fun e _ => (σ ⟨e, (G'.mem_edgeFinset).mp ‹_›⟩).val) ?_ ?_ ?_ ?_
    · intro e he
      exact (H'.mem_edgeFinset).mpr (σ ⟨e, (G'.mem_edgeFinset).mp he⟩).prop
    · intro e1 he1 e2 he2 heq
      exact congrArg Subtype.val (σ.injective (Subtype.ext heq))
    · intro e' he'
      let e'sub : H'.edgeSet := ⟨e', (H'.mem_edgeFinset).mp he'⟩
      refine ⟨(σ.symm e'sub).val, (G'.mem_edgeFinset).mpr (σ.symm e'sub).prop, ?_⟩
      change (σ (σ.symm e'sub)).val = e'
      rw [σ.apply_symm_apply]
    · intro e he
      obtain ⟨φ⟩ := hσ ⟨e, (G'.mem_edgeFinset).mp he⟩
      exact subCardCount_eq_of_iso φ F
  have hdown : ∀ j : ℕ, ∀ k₀ : ℕ, m - j ≤ k₀ →
      ∀ F : SimpleGraph (Fin (n - 1)), F.edgeFinset.card = k₀ →
      cardCount F G' = cardCount F H' := by
    intro j
    induction j with
    | zero =>
      intro k₀ hk₀ F hFk
      have hk₀' : G'.edgeFinset.card ≤ k₀ := by simpa [m] using hk₀
      have hzG : cardCount F G' = 0 := by
        rw [cardCount, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
        intro v hv
        obtain ⟨ψ⟩ := (Finset.mem_filter.mp hv).2
        have hlt := hinduce_lt G' hisoG v
        have heq : (G'.induce {v}ᶜ).edgeFinset.card = k₀ := by
          rw [← SimpleGraph.card_edgeSet]
          exact (Fintype.card_congr (Equiv.refl _)).trans
            (SimpleGraph.card_edgeSet.trans ((card_edgeFinset_eq_of_iso ψ).trans hFk))
        omega
      have hzH : cardCount F H' = 0 := by
        rw [cardCount, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
        intro w hw
        obtain ⟨ψ⟩ := (Finset.mem_filter.mp hw).2
        have hlt := hinduce_lt H' hisoH w
        have heq : (H'.induce {w}ᶜ).edgeFinset.card = k₀ := by
          rw [← SimpleGraph.card_edgeSet]
          exact (Fintype.card_congr (Equiv.refl _)).trans
            (SimpleGraph.card_edgeSet.trans ((card_edgeFinset_eq_of_iso ψ).trans hFk))
        omega
      rw [hzG, hzH]
    | succ j ih =>
      intro k₀ hk₀ F hFk
      by_cases hprev : m - j ≤ k₀
      · exact ih k₀ hprev F hFk
      · have hk₀lt : k₀ < m := by omega
        have hsub_eq : subCardCount F G' = subCardCount F H' := by
          have heq := hsum_del_eq F
          rw [sum_subCardCount_deleteEdges G' F, sum_subCardCount_deleteEdges H' F, ← hm_eq] at heq
          exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < m - F.edgeFinset.card) heq
        let SG := Finset.univ.filter fun v : W => F.edgeFinset.card < (G'.induce {v}ᶜ).edgeFinset.card
        let SH := Finset.univ.filter fun w : W => F.edgeFinset.card < (H'.induce {w}ᶜ).edgeFinset.card
        have hSG_le : ∀ v ∈ SG, (SG.filter fun v' => Nonempty (G'.induce {v}ᶜ ≃g G'.induce {v'}ᶜ)).card ≤
            (SH.filter fun w => Nonempty (G'.induce {v}ᶜ ≃g H'.induce {w}ᶜ)).card := by
          intro v hv
          have hv_gt : m - j ≤ (G'.induce {v}ᶜ).edgeFinset.card := by
            have := (Finset.mem_filter.mp hv).2
            omega
          let e_v : Fin (n - 1) ≃ ({v}ᶜ : Set W) := Fintype.equivOfCardEq (by simp [hcard_compl v])
          let Fv : SimpleGraph (Fin (n - 1)) := (G'.induce {v}ᶜ).comap e_v
          have hFv_iso : Fv ≃g G'.induce {v}ᶜ := Iso.comap e_v (G'.induce {v}ᶜ)
          have hFv_card : Fv.edgeFinset.card = (G'.induce {v}ᶜ).edgeFinset.card :=
            card_edgeFinset_eq_of_iso hFv_iso
          have hcnt_eq : cardCount Fv G' = cardCount Fv H' :=
            ih (G'.induce {v}ᶜ).edgeFinset.card hv_gt Fv hFv_card
          have h1 : (SG.filter fun v' => Nonempty (G'.induce {v}ᶜ ≃g G'.induce {v'}ᶜ)).card =
              cardCount Fv G' := by
            unfold cardCount
            congr 1
            ext v'
            simp only [SG, Finset.mem_filter, Finset.mem_univ, true_and]
            constructor
            · rintro ⟨_, ⟨ψ⟩⟩; exact ⟨ψ.symm.trans hFv_iso.symm⟩
            · rintro ⟨ψ⟩
              have heq := card_edgeFinset_eq_of_iso (ψ.trans hFv_iso)
              have hv_lt := (Finset.mem_filter.mp hv).2
              exact ⟨heq ▸ hv_lt, ⟨(ψ.trans hFv_iso).symm⟩⟩
          have h2 : (SH.filter fun w => Nonempty (G'.induce {v}ᶜ ≃g H'.induce {w}ᶜ)).card =
              cardCount Fv H' := by
            unfold cardCount
            congr 1
            ext w
            simp only [SH, Finset.mem_filter, Finset.mem_univ, true_and]
            constructor
            · rintro ⟨_, ⟨ψ⟩⟩; exact ⟨ψ.symm.trans hFv_iso.symm⟩
            · rintro ⟨ψ⟩
              have heq := card_edgeFinset_eq_of_iso (ψ.trans hFv_iso)
              have hv_lt := (Finset.mem_filter.mp hv).2
              exact ⟨heq ▸ hv_lt, ⟨(ψ.trans hFv_iso).symm⟩⟩
          rw [h1, h2, hcnt_eq]
        have hSH_le : ∀ w ∈ SH, (SH.filter fun w' => Nonempty (H'.induce {w}ᶜ ≃g H'.induce {w'}ᶜ)).card ≤
            (SG.filter fun v => Nonempty (G'.induce {v}ᶜ ≃g H'.induce {w}ᶜ)).card := by
          intro w hw
          have hw_gt : m - j ≤ (H'.induce {w}ᶜ).edgeFinset.card := by
            have := (Finset.mem_filter.mp hw).2
            omega
          let e_w : Fin (n - 1) ≃ ({w}ᶜ : Set W) := Fintype.equivOfCardEq (by simp [hcard_compl w])
          let Fw : SimpleGraph (Fin (n - 1)) := (H'.induce {w}ᶜ).comap e_w
          have hFw_iso : Fw ≃g H'.induce {w}ᶜ := Iso.comap e_w (H'.induce {w}ᶜ)
          have hFw_card : Fw.edgeFinset.card = (H'.induce {w}ᶜ).edgeFinset.card :=
            card_edgeFinset_eq_of_iso hFw_iso
          have hcnt_eq : cardCount Fw G' = cardCount Fw H' :=
            ih (H'.induce {w}ᶜ).edgeFinset.card hw_gt Fw hFw_card
          have h1 : (SH.filter fun w' => Nonempty (H'.induce {w}ᶜ ≃g H'.induce {w'}ᶜ)).card =
              cardCount Fw H' := by
            unfold cardCount
            congr 1
            ext w'
            simp only [SH, Finset.mem_filter, Finset.mem_univ, true_and]
            constructor
            · rintro ⟨_, ⟨ψ⟩⟩; exact ⟨ψ.symm.trans hFw_iso.symm⟩
            · rintro ⟨ψ⟩
              have heq := card_edgeFinset_eq_of_iso (ψ.trans hFw_iso)
              have hw_lt := (Finset.mem_filter.mp hw).2
              exact ⟨heq ▸ hw_lt, ⟨(ψ.trans hFw_iso).symm⟩⟩
          have h2 : (SG.filter fun v => Nonempty (G'.induce {v}ᶜ ≃g H'.induce {w}ᶜ)).card =
              cardCount Fw G' := by
            unfold cardCount
            congr 1
            ext v
            simp only [SG, Finset.mem_filter, Finset.mem_univ, true_and]
            constructor
            · rintro ⟨_, ⟨ψ⟩⟩; exact ⟨ψ.trans hFw_iso.symm⟩
            · rintro ⟨ψ⟩
              have heq := card_edgeFinset_eq_of_iso (ψ.trans hFw_iso)
              have hw_lt := (Finset.mem_filter.mp hw).2
              exact ⟨heq ▸ hw_lt, ⟨ψ.trans hFw_iso⟩⟩
          rw [h1, h2, hcnt_eq]
        obtain ⟨f_big, hf_big⟩ := exists_bij_of_rel_counts SG SH
          (fun v1 v2 => Nonempty (G'.induce {v1}ᶜ ≃g G'.induce {v2}ᶜ))
          (fun w1 w2 => Nonempty (H'.induce {w1}ᶜ ≃g H'.induce {w2}ᶜ))
          (fun v w => Nonempty (G'.induce {v}ᶜ ≃g H'.induce {w}ᶜ))
          (fun _ => ⟨Iso.refl⟩) (fun _ => ⟨Iso.refl⟩)
          (fun ⟨h⟩ => ⟨h.symm⟩) (fun ⟨h⟩ => ⟨h.symm⟩)
          (fun ⟨h1⟩ ⟨h2⟩ => ⟨h1.trans h2⟩) (fun ⟨h1⟩ ⟨h2⟩ => ⟨h1.trans h2⟩)
          (fun ⟨h1⟩ ⟨h2⟩ => ⟨h1.trans h2.symm⟩) (fun ⟨h1⟩ ⟨h2⟩ => ⟨h1.symm.trans h2⟩)
          hSG_le hSH_le
        have hbig_sum :
            (∑ v ∈ SG, (Finset.univ.filter fun K : SimpleGraph ({v}ᶜ : Set W) =>
              K ≤ G'.induce {v}ᶜ ∧ Nonempty (K ≃g F)).card) =
            (∑ w ∈ SH, (Finset.univ.filter fun K : SimpleGraph ({w}ᶜ : Set W) =>
              K ≤ H'.induce {w}ᶜ ∧ Nonempty (K ≃g F)).card) := by
          have hG_att :
              (∑ v ∈ SG, (Finset.univ.filter fun K : SimpleGraph ({v}ᶜ : Set W) =>
                K ≤ G'.induce {v}ᶜ ∧ Nonempty (K ≃g F)).card) =
              ∑ v : SG, (Finset.univ.filter fun K : SimpleGraph ({v.1}ᶜ : Set W) =>
                K ≤ G'.induce {v.1}ᶜ ∧ Nonempty (K ≃g F)).card :=
            (Finset.sum_coe_sort SG _).symm
          have hH_att :
              (∑ w ∈ SH, (Finset.univ.filter fun K : SimpleGraph ({w}ᶜ : Set W) =>
                K ≤ H'.induce {w}ᶜ ∧ Nonempty (K ≃g F)).card) =
              ∑ w : SH, (Finset.univ.filter fun K : SimpleGraph ({w.1}ᶜ : Set W) =>
                K ≤ H'.induce {w.1}ᶜ ∧ Nonempty (K ≃g F)).card :=
            (Finset.sum_coe_sort SH _).symm
          rw [hG_att, hH_att]
          refine Fintype.sum_equiv f_big _ _ fun v => ?_
          obtain ⟨ψ⟩ := hf_big v
          refine Finset.card_bij (fun K _ => K.comap ψ.symm.toEquiv) ?_ ?_ ?_
          · intro K hK
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hK ⊢
            obtain ⟨hK_le, ⟨χ⟩⟩ := hK
            have hiso : K.comap ψ.symm.toEquiv ≃g K := Iso.comap ψ.symm.toEquiv K
            refine ⟨fun {a b} hab => ?_, ⟨hiso.trans χ⟩⟩
            simpa only [RelIso.coe_fn_toEquiv, RelIso.apply_symm_apply] using ψ.map_rel_iff.mpr (hK_le hab)
          · intro K1 _ K2 _ heq
            have h1 := congrArg (SimpleGraph.comap ψ.toEquiv) heq
            have hcomp : ∀ K : SimpleGraph ({v.1}ᶜ : Set W), (K.comap ψ.symm.toEquiv).comap ψ.toEquiv = K := by
              intro K; ext a b; simp
            simpa [hcomp] using h1
          · intro K' hK'
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hK'
            obtain ⟨hK'_le, ⟨χ⟩⟩ := hK'
            let K := K'.comap ψ.toEquiv
            have hiso : K ≃g K' := Iso.comap ψ.toEquiv K'
            have hK_le : K ≤ G'.induce {v.1}ᶜ := fun {a b} hab => ψ.map_rel_iff.mp (hK'_le hab)
            have hback : K.comap ψ.symm.toEquiv = K' := by ext a b; simp [K]
            exact ⟨K, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hK_le, ⟨hiso.trans χ⟩⟩, hback⟩
        rw [subCardCount_decomp F G', subCardCount_decomp F H'] at hsub_eq
        change cardCount F G' + ∑ v ∈ SG, _ = cardCount F H' + ∑ w ∈ SH, _ at hsub_eq
        rw [hbig_sum] at hsub_eq
        omega
  have hall_v : ∀ v : W,
      ((Finset.univ : Finset W).filter fun v' => Nonempty (G'.induce {v}ᶜ ≃g G'.induce {v'}ᶜ)).card ≤
      ((Finset.univ : Finset W).filter fun w => Nonempty (G'.induce {v}ᶜ ≃g H'.induce {w}ᶜ)).card := by
    intro v
    let e_v : Fin (n - 1) ≃ ({v}ᶜ : Set W) := Fintype.equivOfCardEq (by simp [hcard_compl v])
    let Fv : SimpleGraph (Fin (n - 1)) := (G'.induce {v}ᶜ).comap e_v
    have hFv_iso : Fv ≃g G'.induce {v}ᶜ := Iso.comap e_v (G'.induce {v}ᶜ)
    have hcnt := hdown m Fv.edgeFinset.card (by omega) Fv rfl
    have h1 : ((Finset.univ : Finset W).filter fun v' => Nonempty (G'.induce {v}ᶜ ≃g G'.induce {v'}ᶜ)).card =
        cardCount Fv G' := by
      unfold cardCount
      congr 1
      ext v'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨ψ⟩; exact ⟨ψ.symm.trans hFv_iso.symm⟩
      · rintro ⟨ψ⟩; exact ⟨(ψ.trans hFv_iso).symm⟩
    have h2 : ((Finset.univ : Finset W).filter fun w => Nonempty (G'.induce {v}ᶜ ≃g H'.induce {w}ᶜ)).card =
        cardCount Fv H' := by
      unfold cardCount
      congr 1
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨ψ⟩; exact ⟨ψ.symm.trans hFv_iso.symm⟩
      · rintro ⟨ψ⟩; exact ⟨(ψ.trans hFv_iso).symm⟩
    rw [h1, h2, hcnt]
  have hall_w : ∀ w : W,
      ((Finset.univ : Finset W).filter fun w' => Nonempty (H'.induce {w}ᶜ ≃g H'.induce {w'}ᶜ)).card ≤
      ((Finset.univ : Finset W).filter fun v => Nonempty (G'.induce {v}ᶜ ≃g H'.induce {w}ᶜ)).card := by
    intro w
    let e_w : Fin (n - 1) ≃ ({w}ᶜ : Set W) := Fintype.equivOfCardEq (by simp [hcard_compl w])
    let Fw : SimpleGraph (Fin (n - 1)) := (H'.induce {w}ᶜ).comap e_w
    have hFw_iso : Fw ≃g H'.induce {w}ᶜ := Iso.comap e_w (H'.induce {w}ᶜ)
    have hcnt := hdown m Fw.edgeFinset.card (by omega) Fw rfl
    have h1 : ((Finset.univ : Finset W).filter fun w' => Nonempty (H'.induce {w}ᶜ ≃g H'.induce {w'}ᶜ)).card =
        cardCount Fw H' := by
      unfold cardCount
      congr 1
      ext w'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨ψ⟩; exact ⟨ψ.symm.trans hFw_iso.symm⟩
      · rintro ⟨ψ⟩; exact ⟨(ψ.trans hFw_iso).symm⟩
    have h2 : ((Finset.univ : Finset W).filter fun v => Nonempty (G'.induce {v}ᶜ ≃g H'.induce {w}ᶜ)).card =
        cardCount Fw G' := by
      unfold cardCount
      congr 1
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨ψ⟩; exact ⟨ψ.trans hFw_iso.symm⟩
      · rintro ⟨ψ⟩; exact ⟨ψ.trans hFw_iso⟩
    rw [h1, h2, hcnt]
  obtain ⟨f_sub, hf_sub⟩ := exists_bij_of_rel_counts (Finset.univ : Finset W) (Finset.univ : Finset W)
    (fun v1 v2 => Nonempty (G'.induce {v1}ᶜ ≃g G'.induce {v2}ᶜ))
    (fun w1 w2 => Nonempty (H'.induce {w1}ᶜ ≃g H'.induce {w2}ᶜ))
    (fun v w => Nonempty (G'.induce {v}ᶜ ≃g H'.induce {w}ᶜ))
    (fun _ => ⟨Iso.refl⟩) (fun _ => ⟨Iso.refl⟩)
    (fun ⟨h⟩ => ⟨h.symm⟩) (fun ⟨h⟩ => ⟨h.symm⟩)
    (fun ⟨h1⟩ ⟨h2⟩ => ⟨h1.trans h2⟩) (fun ⟨h1⟩ ⟨h2⟩ => ⟨h1.trans h2⟩)
    (fun ⟨h1⟩ ⟨h2⟩ => ⟨h1.trans h2.symm⟩) (fun ⟨h1⟩ ⟨h2⟩ => ⟨h1.symm.trans h2⟩)
    (fun v _ => hall_v v) (fun w _ => hall_w w)
  refine ⟨{
    toFun := fun v => (f_sub ⟨v, Finset.mem_univ v⟩).1
    invFun := fun w => (f_sub.symm ⟨w, Finset.mem_univ w⟩).1
    left_inv := fun v => congrArg Subtype.val (f_sub.symm_apply_apply ⟨v, Finset.mem_univ v⟩)
    right_inv := fun w => congrArg Subtype.val (f_sub.apply_symm_apply ⟨w, Finset.mem_univ w⟩)
  }, fun v => hf_sub ⟨v, Finset.mem_univ v⟩⟩

end ConnectedCase

end OMA.H1Proof

open Classical in
theorem OMA.solution : OMA.R_ReconstructionConjecture_edge_reconstruction_conjecture_R1.H1 := by
  intro V _ G H hE hEH
  have hE_fin : 4 ≤ G.edgeFinset.card := by
    rwa [← OMA.H1Proof.ncard_edgeSet_eq_card_edgeFinset]
  obtain ⟨W, _, G', H', h4W, hE', hG'_iso, hH'_iso, hEH', hLift⟩ :=
    OMA.H1Proof.strip_isolated_vertices G H hE_fin hEH
  by_cases hConn : G'.Connected
  · refine Or.inr ⟨W, inferInstance, G', H', h4W, ?_, hConn, hG'_iso, hEH',
      OMA.H1Proof.hypomorphic_of_isolateFree G' H' h4W hE' hG'_iso hH'_iso hEH', hLift⟩
    rwa [OMA.H1Proof.ncard_edgeSet_eq_card_edgeFinset]
  · exact Or.inl (hLift (OMA.H1Proof.iso_of_not_connected_isolateFree G' H' h4W hE'
      hG'_iso hH'_iso hEH' hConn))
