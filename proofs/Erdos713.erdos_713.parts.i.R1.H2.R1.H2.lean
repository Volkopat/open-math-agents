import OMAReductions.R_Erdos713_erdos_713_parts_i_R1_H2_R1

/-!
Star forests: the extremal number is c*n + O(1), which gives the threshold transfer.
Upper bound: reserve the vertices of host degree at least 3q for some stars and embed the
others greedily; where the greedy step fails a degree count bounds the edges.
Lower bound: s universal vertices plus disjoint cliques of order d.
See Lidicky, Liu and Palmer, On the Turan number of forests, EJC 20 (2013), P62, Theorem 3.
-/

-- Credit: @bedecarroll

open SimpleGraph Finset Filter
open scoped Classical

namespace E713Star

variable {q : ℕ}

def IsC (G : SimpleGraph (Fin q)) (v : Fin q) : Prop :=
  2 ≤ G.degree v ∨ ∃ w, G.Adj v w ∧ G.degree w ≤ 1 ∧ v < w

theorem uniq (G : SimpleGraph (Fin q)) {v a b : Fin q} (h : G.degree v ≤ 1)
    (ha : G.Adj v a) (hb : G.Adj v b) : a = b := by
  rw [← card_neighborFinset_eq_degree] at h
  exact Finset.card_le_one.mp h a ((G.mem_neighborFinset v a).mpr ha) b
    ((G.mem_neighborFinset v b).mpr hb)

theorem leaf_deg (G : SimpleGraph (Fin q)) {v : Fin q} (h : ¬ IsC G v) : G.degree v ≤ 1 := by
  unfold IsC at h
  push Not at h
  omega

theorem leaf_nbr (G : SimpleGraph (Fin q)) (active : ∀ v, ¬ G.IsIsolated v) {v : Fin q}
    (h : ¬ IsC G v) : ∃ w, G.Adj v w ∧ IsC G w := by
  have hd := leaf_deg G h
  have iso := active v
  unfold IsIsolated at iso
  push Not at iso
  obtain ⟨w, hw⟩ := iso
  refine ⟨w, hw, ?_⟩
  by_cases h2 : 2 ≤ G.degree w
  · exact Or.inl h2
  · right
    refine ⟨v, hw.symm, hd, ?_⟩
    rcases lt_trichotomy v w with lt | eq | gt
    · exact absurd (Or.inr ⟨w, hw, by omega, lt⟩) h
    · exact absurd eq hw.ne
    · exact gt

theorem not_both (G : SimpleGraph (Fin q))
    (star : ∀ v w, G.Adj v w → G.degree v ≤ 1 ∨ G.degree w ≤ 1) {v w : Fin q}
    (hvw : G.Adj v w) (hv : IsC G v) (hw : IsC G w) : False := by
  have key : ∀ v w, G.Adj v w → IsC G v → IsC G w → G.degree v ≤ 1 → False := by
    intro v w hvw hv hw hd
    rcases hv with h | ⟨w', a1, d1, l1⟩
    · omega
    have e : w' = w := uniq G hd a1 hvw
    subst e
    rcases hw with h | ⟨v', a2, d2, l2⟩
    · omega
    have e : v' = v := uniq G d1 a2 hvw.symm
    subst e
    exact lt_asymm l1 l2
  rcases star v w hvw with h | h
  · exact key v w hvw hv hw h
  · exact key w v hvw.symm hw hv h

theorem one_centre (G : SimpleGraph (Fin q)) (active : ∀ v, ¬ G.IsIsolated v) {v w : Fin q}
    (hvw : G.Adj v w) : IsC G v ∨ IsC G w := by
  by_contra h
  push Not at h
  obtain ⟨w', a, c⟩ := leaf_nbr G active h.1
  have e := uniq G (leaf_deg G h.1) a hvw
  subst e
  exact h.2 c

theorem inj_into {α β : Type*} [Nonempty β] (A : Finset α) (B : Finset β) (h : A.card ≤ B.card) :
    ∃ g : α → β, Set.InjOn g A ∧ ∀ a ∈ A, g a ∈ B := by
  obtain ⟨f, hf, hi⟩ := (A.finite_toSet).exists_injOn_of_encard_le (t := (B : Set β)) (by
    rw [Set.encard_coe_eq_coe_finsetCard, Set.encard_coe_eq_coe_finsetCard]
    exact_mod_cast h)
  exact ⟨f, hi, fun a ha => by simpa using hf ha⟩

noncomputable def st (G : SimpleGraph (Fin q)) (Z : Finset (Fin q)) : Finset (Fin q) :=
  univ.filter (fun v => ∃ z ∈ Z, v = z ∨ G.Adj z v)

theorem embed (G : SimpleGraph (Fin q)) (active : ∀ v, ¬ G.IsIsolated v)
    (star : ∀ v w, G.Adj v w → G.degree v ≤ 1 ∨ G.degree w ≤ 1)
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) (S : Finset V) (T : Finset (Fin q))
    (hTC : ∀ t ∈ T, IsC G t) (hTS : T.card ≤ S.card)
    (hS : ∀ x ∈ S, 3 * q ≤ H.degree x)
    (hQ : ∀ z, IsC G z → z ∉ T → ∀ W : Finset V, W.card ≤ q →
      ∃ x, x ∉ S ∧ x ∉ W ∧ G.degree z ≤ ((H.neighborFinset x) \ (S ∪ W)).card) :
    G.IsContained H := by
  rcases isEmpty_or_nonempty V with hV | hV
  · have noV : Fin q → False := by
      intro v
      obtain ⟨z, hz⟩ : ∃ z, IsC G z := by
        by_cases h : IsC G v
        · exact ⟨v, h⟩
        · obtain ⟨w, _, hw⟩ := leaf_nbr G active h
          exact ⟨w, hw⟩
      by_cases hT : z ∈ T
      · have pos : 0 < S.card := lt_of_lt_of_le (Finset.card_pos.mpr ⟨z, hT⟩) hTS
        obtain ⟨x, _⟩ := Finset.card_pos.mp pos
        exact hV.false x
      · obtain ⟨x, _⟩ := hQ z hz hT ∅ (by simp)
        exact hV.false x
    exact ⟨⟨⟨fun v => (noV v).elim, fun {a} => (noV a).elim⟩, fun a => (noV a).elim⟩⟩
  obtain ⟨ι, ιinj, ιS⟩ := inj_into T S hTS
  have claim : ∀ Z : Finset (Fin q), (∀ z ∈ Z, IsC G z) → ∃ f : Fin q → V,
      Set.InjOn f (st G Z) ∧ (∀ z ∈ Z, ∀ l, G.Adj z l → H.Adj (f z) (f l)) ∧
      (∀ v ∈ st G Z, v ∈ T → f v = ι v) ∧ (∀ v ∈ st G Z, v ∉ T → f v ∉ T.image ι) := by
    intro Z
    induction Z using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨ι, by simp [st], by simp, by simp [st], by simp [st]⟩
    | insert z Z hzZ ih =>
      intro hC
      have hz : IsC G z := hC z (mem_insert_self z Z)
      obtain ⟨f, finj, fadj, fT, fnT⟩ := ih (fun y hy => hC y (mem_insert_of_mem hy))
      have mem_st : ∀ v, v ∈ st G (insert z Z) ↔ v = z ∨ G.Adj z v ∨ v ∈ st G Z := by
        intro v
        simp only [st, mem_filter, mem_univ, true_and, mem_insert]
        constructor
        · rintro ⟨y, rfl | hy, h⟩
          · rcases h with h | h
            · exact Or.inl h
            · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr ⟨y, hy, h⟩)
        · rintro (h | h | ⟨y, hy, h⟩)
          · exact ⟨z, Or.inl rfl, Or.inl h⟩
          · exact ⟨z, Or.inl rfl, Or.inr h⟩
          · exact ⟨y, Or.inr hy, h⟩
      have old : ∀ v ∈ st G Z, v ≠ z ∧ ¬ G.Adj z v := by
        intro v hv
        simp only [st, mem_filter, mem_univ, true_and] at hv
        obtain ⟨y, hy, h⟩ := hv
        have hyC := hC y (mem_insert_of_mem hy)
        constructor
        · intro e
          subst e
          rcases h with h | h
          · exact hzZ (h ▸ hy)
          · exact not_both G star h hyC hz
        · intro a
          rcases h with h | h
          · subst h
            exact not_both G star a hz hyC
          · have hv : ¬ IsC G v := fun c => not_both G star a hz c
            have e := uniq G (leaf_deg G hv) a.symm h.symm
            exact hzZ (e ▸ hy)
      let W : Finset V := (st G Z).image f
      have hW : W.card ≤ q := by
        calc W.card ≤ (st G Z).card := card_image_le
          _ ≤ (univ : Finset (Fin q)).card := card_le_card (subset_univ _)
          _ = q := by simp
      have hTq : (T.image ι).card ≤ q := by
        calc (T.image ι).card ≤ T.card := card_image_le
          _ ≤ (univ : Finset (Fin q)).card := card_le_card (subset_univ _)
          _ = q := by simp
      have hdeg : G.degree z < q := by simpa using G.degree_lt_card_verts z
      obtain ⟨x, avail, hxW, hsub, hdW, hdT, hcard, hxT, hxnT⟩ : ∃ (x : V) (avail : Finset V),
          x ∉ W ∧ avail ⊆ H.neighborFinset x ∧ (∀ y ∈ avail, y ∉ W) ∧
          (∀ y ∈ avail, y ∉ T.image ι) ∧ G.degree z ≤ avail.card ∧ (z ∈ T → x = ι z) ∧
          (z ∉ T → x ∉ T.image ι) := by
        by_cases hT : z ∈ T
        · refine ⟨ι z, H.neighborFinset (ι z) \ (W ∪ T.image ι), ?_, sdiff_subset, ?_, ?_, ?_,
            fun _ => rfl, fun h => absurd hT h⟩
          · intro hx
            obtain ⟨v, hv, e⟩ := mem_image.mp hx
            by_cases hvT : v ∈ T
            · rw [fT v hv hvT] at e
              exact (old v hv).1 (ιinj hvT hT e)
            · exact fnT v hv hvT (e ▸ mem_image_of_mem ι hT)
          · intro y hy
            simp only [Finset.mem_sdiff, mem_union, not_or] at hy
            exact hy.2.1
          · intro y hy
            simp only [Finset.mem_sdiff, mem_union, not_or] at hy
            exact hy.2.2
          · have h1 := le_card_sdiff (W ∪ T.image ι) (H.neighborFinset (ι z))
            have h2 : (W ∪ T.image ι).card ≤ q + q := (card_union_le _ _).trans (add_le_add hW hTq)
            have h3 := hS _ (ιS z hT)
            rw [← card_neighborFinset_eq_degree] at h3
            omega
        · obtain ⟨x, hxS, hxW, hc⟩ := hQ z hz hT W hW
          refine ⟨x, H.neighborFinset x \ (S ∪ W), hxW, sdiff_subset, ?_, ?_, hc,
            fun h => absurd h hT, ?_⟩
          · intro y hy
            simp only [Finset.mem_sdiff, mem_union, not_or] at hy
            exact hy.2.2
          · intro y hy h
            simp only [Finset.mem_sdiff, mem_union, not_or] at hy
            obtain ⟨t, ht, e⟩ := mem_image.mp h
            exact hy.2.1 (e ▸ ιS t ht)
          · intro _ h
            obtain ⟨t, ht, e⟩ := mem_image.mp h
            exact hxS (e ▸ ιS t ht)
      obtain ⟨e, einj, eav⟩ := inj_into (G.neighborFinset z) avail
        (by rwa [card_neighborFinset_eq_degree])
      let F : Fin q → V := fun v => if v = z then x else if G.Adj z v then e v else f v
      have Fz : F z = x := by simp [F]
      have Fn : ∀ v, G.Adj z v → F v = e v ∧ e v ∈ avail := by
        intro v hv
        have ne : v ≠ z := fun h => G.loopless.irrefl z (h ▸ hv)
        exact ⟨by simp [F, ne, hv], eav v ((G.mem_neighborFinset z v).mpr hv)⟩
      have Fo : ∀ v ∈ st G Z, F v = f v ∧ f v ∈ W := by
        intro v hv
        obtain ⟨h1, h2⟩ := old v hv
        exact ⟨by simp [F, h1, h2], mem_image_of_mem f hv⟩
      have avadj : ∀ y ∈ avail, H.Adj x y := fun y hy => (H.mem_neighborFinset x y).mp (hsub hy)
      have avx : ∀ y ∈ avail, y ≠ x := by
        intro y hy h
        exact H.loopless.irrefl x (h ▸ avadj y hy)
      refine ⟨F, ?_, ?_, ?_, ?_⟩
      · intro a ha b hb hab
        rw [mem_coe, mem_st] at ha hb
        rcases ha with ha | ha | ha <;> rcases hb with hb | hb | hb
        · rw [ha, hb]
        · rw [ha, Fz, (Fn b hb).1] at hab
          exact absurd hab.symm (avx _ (Fn b hb).2)
        · rw [ha, Fz, (Fo b hb).1] at hab
          exact absurd (hab ▸ (Fo b hb).2) hxW
        · rw [hb, Fz, (Fn a ha).1] at hab
          exact absurd hab (avx _ (Fn a ha).2)
        · rw [(Fn a ha).1, (Fn b hb).1] at hab
          exact einj ((G.mem_neighborFinset z a).mpr ha) ((G.mem_neighborFinset z b).mpr hb) hab
        · rw [(Fn a ha).1, (Fo b hb).1] at hab
          exact absurd (hab ▸ (Fo b hb).2) (hdW _ (Fn a ha).2)
        · rw [hb, Fz, (Fo a ha).1] at hab
          exact absurd (hab ▸ (Fo a ha).2) hxW
        · rw [(Fn b hb).1, (Fo a ha).1] at hab
          exact absurd (hab ▸ (Fo a ha).2) (hdW _ (Fn b hb).2)
        · rw [(Fo a ha).1, (Fo b hb).1] at hab
          exact finj ha hb hab
      · intro y hy l hl
        rcases mem_insert.mp hy with rfl | hy
        · rw [Fz, (Fn l hl).1]
          exact avadj _ (Fn l hl).2
        · have m1 : y ∈ st G Z := by
            simp only [st, mem_filter, mem_univ, true_and]
            exact ⟨y, hy, Or.inl rfl⟩
          have m2 : l ∈ st G Z := by
            simp only [st, mem_filter, mem_univ, true_and]
            exact ⟨y, hy, Or.inr hl⟩
          rw [(Fo y m1).1, (Fo l m2).1]
          exact fadj y hy l hl
      · intro v hv hvT
        rcases (mem_st v).mp hv with h | h | h
        · rw [h, Fz]
          exact hxT (h ▸ hvT)
        · exact absurd (hTC v hvT) (fun c => not_both G star h hz c)
        · rw [(Fo v h).1]
          exact fT v h hvT
      · intro v hv hvT
        rcases (mem_st v).mp hv with h | h | h
        · rw [h, Fz]
          exact hxnT (h ▸ hvT)
        · rw [(Fn v h).1]
          exact hdT _ (Fn v h).2
        · rw [(Fo v h).1]
          exact fnT v h hvT
  obtain ⟨f, finj, fadj, -, -⟩ := claim (univ.filter (IsC G)) (by simp)
  have all : ∀ v, v ∈ st G (univ.filter (IsC G)) := by
    intro v
    simp only [st, mem_filter, mem_univ, true_and]
    by_cases h : IsC G v
    · exact ⟨v, h, Or.inl rfl⟩
    · obtain ⟨w, a, c⟩ := leaf_nbr G active h
      exact ⟨w, c, Or.inr a.symm⟩
  refine ⟨⟨⟨f, ?_⟩, ?_⟩⟩
  · intro a b hab
    rcases one_centre G active hab with h | h
    · exact fadj a (by simp [h]) b hab
    · exact (fadj b (by simp [h]) a hab.symm).symm
  · intro a b hab
    exact finj (all a) (all b) hab

theorem count {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) (D d c : ℕ) (S W : Finset V)
    (hS : ∀ y, y ∉ S → H.degree y < D) (hW : W.card ≤ c)
    (hfail : ∀ x, x ∉ S → x ∉ W → ((H.neighborFinset x) \ (S ∪ W)).card < d) :
    2 * H.edgeFinset.card + Fintype.card V ≤
      2 * S.card * Fintype.card V + d * Fintype.card V + 2 * c * D + S.card + c := by
  have hdegn : ∀ y, H.degree y ≤ Fintype.card V := fun y => (H.degree_lt_card_verts y).le
  have sumB : ∑ y ∈ S ∪ W, H.degree y ≤ S.card * Fintype.card V + c * D := by
    have e : S ∪ W = S ∪ (W \ S) := (union_sdiff_self_eq_union).symm
    rw [e, sum_union disjoint_sdiff]
    have h1 : ∑ y ∈ S, H.degree y ≤ S.card * Fintype.card V := by
      simpa using sum_le_card_nsmul S _ (Fintype.card V) (fun y _ => hdegn y)
    have h2 : ∑ y ∈ W \ S, H.degree y ≤ (W \ S).card * D := by
      simpa using sum_le_card_nsmul (W \ S) _ D
        (fun y hy => (hS y (Finset.mem_sdiff.mp hy).2).le)
    have h3 : (W \ S).card * D ≤ c * D :=
      Nat.mul_le_mul_right D ((card_le_card sdiff_subset).trans hW)
    omega
  have cross : ∑ x ∈ (S ∪ W)ᶜ, ((S ∪ W).filter (fun y => H.Adj x y)).card ≤
      ∑ y ∈ S ∪ W, H.degree y := by
    have dc := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (s := (S ∪ W)ᶜ) (t := S ∪ W)
      (r := H.Adj)
    unfold bipartiteAbove bipartiteBelow at dc
    rw [dc]
    apply sum_le_sum
    intro y _
    rw [← card_neighborFinset_eq_degree]
    apply card_le_card
    intro x hx
    rw [mem_filter] at hx
    exact (H.mem_neighborFinset y x).mpr hx.2.symm
  have each : ∀ x ∈ (S ∪ W)ᶜ, H.degree x + 1 ≤
      ((S ∪ W).filter (fun y => H.Adj x y)).card + d := by
    intro x hx
    have hx' : x ∉ S ∪ W := by simpa using hx
    have hxS : x ∉ S := fun h => hx' (mem_union_left _ h)
    have hxW : x ∉ W := fun h => hx' (mem_union_right _ h)
    have f := hfail x hxS hxW
    have sp := card_sdiff_add_card_inter (H.neighborFinset x) (S ∪ W)
    have e : H.neighborFinset x ∩ (S ∪ W) = (S ∪ W).filter (fun y => H.Adj x y) := by
      ext y
      simp only [mem_inter, mem_neighborFinset, mem_filter]
      tauto
    rw [e, card_neighborFinset_eq_degree] at sp
    omega
  have tot := sum_le_sum each
  rw [sum_add_distrib, sum_add_distrib] at tot
  simp only [sum_const, smul_eq_mul, mul_one] at tot
  have deg2 := H.sum_degrees_eq_twice_card_edges
  rw [← sum_add_sum_compl (S ∪ W)] at deg2
  have cB : (S ∪ W)ᶜ.card + (S ∪ W).card = Fintype.card V := by
    rw [card_compl]
    have := card_le_univ (S ∪ W)
    omega
  have cB2 : (S ∪ W).card ≤ S.card + c := (card_union_le _ _).trans (by omega)
  have hm : (S ∪ W)ᶜ.card * d ≤ Fintype.card V * d := Nat.mul_le_mul_right d (by omega)
  nlinarith

def P (G : SimpleGraph (Fin q)) (s d : ℕ) : Prop :=
  ∀ A : Finset (Fin q), A.card ≤ s → ∃ z, z ∉ A ∧ (∀ w, G.Adj z w → w ∉ A) ∧ d ≤ G.degree z

theorem lower (G : SimpleGraph (Fin q)) (s d t r : ℕ) (hd : 1 ≤ d) (hP : P G s d) :
    t * d * (2 * s + d - 1) ≤ 2 * extremalNumber (s + (t * d + r)) G := by
  let V := Fin s ⊕ (Fin t × Fin d ⊕ Fin r)
  let X : SimpleGraph V := {
    Adj := fun x y => x ≠ y ∧ (x.isLeft = true ∨ y.isLeft = true ∨
      ∃ a b b', x = Sum.inr (Sum.inl (a, b)) ∧ y = Sum.inr (Sum.inl (a, b')))
    symm := ⟨fun x y h => ⟨h.1.symm, by
      rcases h.2 with h | h | ⟨a, b, b', h1, h2⟩
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr ⟨a, b', b, h2, h1⟩)⟩⟩
    loopless := ⟨fun x h => h.1 rfl⟩ }
  have free : G.Free X := by
    rintro ⟨f⟩
    let A : Finset (Fin q) := univ.filter (fun v => (f v).isLeft = true)
    have hA : A.card ≤ s := by
      have h1 : (A.image f).card = A.card := card_image_of_injective A f.injective
      have h2 : A.image f ⊆ (univ : Finset (Fin s)).image (Sum.inl : Fin s → V) := by
        intro y hy
        obtain ⟨v, hv, rfl⟩ := mem_image.mp hy
        have il := (mem_filter.mp hv).2
        obtain ⟨i, hi⟩ := Sum.isLeft_iff.mp il
        exact mem_image.mpr ⟨i, mem_univ _, hi.symm⟩
      have h3 := card_le_card h2
      have h4 : ((univ : Finset (Fin s)).image (Sum.inl : Fin s → V)).card ≤ s :=
        card_image_le.trans (by simp)
      omega
    obtain ⟨z, hzA, hnb, hdz⟩ := hP A hA
    have nl : ∀ v, v ∉ A → (f v).isLeft = false := by
      intro v hv
      simpa [A] using hv
    have adjX : ∀ w, G.Adj z w → X.Adj (f z) (f w) := fun w hw => f.toHom.map_adj hw
    have shape : ∀ w, G.Adj z w → ∃ a b b', f z = Sum.inr (Sum.inl (a, b)) ∧
        f w = Sum.inr (Sum.inl (a, b')) := by
      intro w hw
      rcases (adjX w hw).2 with h | h | h
      · rw [nl z hzA] at h
        cases h
      · rw [nl w (hnb w hw)] at h
        cases h
      · exact h
    have pos : 0 < G.degree z := by omega
    obtain ⟨w0, hw0⟩ := (G.degree_pos_iff_exists_adj z).mp pos
    obtain ⟨a, b, -, hfz, -⟩ := shape w0 hw0
    let g : Fin q → Fin d := fun w => match f w with
      | Sum.inr (Sum.inl (_, b')) => b'
      | _ => b
    have key : ∀ w, G.Adj z w → f w = Sum.inr (Sum.inl (a, g w)) ∧ g w ≠ b := by
      intro w hw
      obtain ⟨a1, b1, b2, h1, h2⟩ := shape w hw
      rw [hfz] at h1
      obtain ⟨ea, eb⟩ := Prod.mk.inj (Sum.inl.inj (Sum.inr.inj h1))
      subst ea
      subst eb
      have gw : g w = b2 := by simp only [g, h2]
      refine ⟨by rw [gw, h2], ?_⟩
      intro e
      have ne := (adjX w hw).1
      rw [hfz, h2, ← gw, e] at ne
      exact ne rfl
    have le : (G.neighborFinset z).card ≤ ((univ : Finset (Fin d)).erase b).card := by
      apply card_le_card_of_injOn g
      · intro w hw
        have k := key w ((G.mem_neighborFinset z w).mp hw)
        simp [k.2]
      · intro w1 h1 w2 h2 e
        have k1 := key w1 ((G.mem_neighborFinset z w1).mp h1)
        have k2 := key w2 ((G.mem_neighborFinset z w2).mp h2)
        have fe : f w1 = f w2 := by rw [k1.1, k2.1, e]
        exact f.injective fe
    rw [card_neighborFinset_eq_degree, card_erase_of_mem (mem_univ b)] at le
    simp only [card_univ, Fintype.card_fin] at le
    omega
  have lbU : ∀ i : Fin s, t * d ≤ X.degree (Sum.inl i) := by
    intro i
    rw [← card_neighborFinset_eq_degree]
    have c0 : ((univ : Finset (Fin t × Fin d)).image
        (fun y => (Sum.inr (Sum.inl y) : V))).card = t * d := by
      rw [card_image_of_injective _ (fun a b h => Sum.inl.inj (Sum.inr.inj h))]
      simp
    rw [← c0]
    apply card_le_card
    intro y hy
    obtain ⟨c, -, rfl⟩ := mem_image.mp hy
    rw [mem_neighborFinset]
    exact ⟨by simp, Or.inl rfl⟩
  have lbR : ∀ (a : Fin t) (b : Fin d), s + (d - 1) ≤ X.degree (Sum.inr (Sum.inl (a, b))) := by
    intro a b
    rw [← card_neighborFinset_eq_degree]
    let N1 := (univ : Finset (Fin s)).image (fun i => (Sum.inl i : V))
    let N2 := ((univ : Finset (Fin d)).erase b).image
      (fun b' => (Sum.inr (Sum.inl (a, b')) : V))
    have c1 : N1.card = s := by
      rw [card_image_of_injective _ Sum.inl_injective]
      simp
    have c2 : N2.card = d - 1 := by
      rw [card_image_of_injective _
        (fun x y h => (Prod.mk.inj (Sum.inl.inj (Sum.inr.inj h))).2)]
      simp
    have dis : Disjoint N1 N2 := by
      rw [Finset.disjoint_left]
      intro y h1 h2
      obtain ⟨i, -, rfl⟩ := mem_image.mp h1
      obtain ⟨b', -, h⟩ := mem_image.mp h2
      cases h
    have cu : s + (d - 1) = (N1 ∪ N2).card := by
      rw [card_union_of_disjoint dis, c1, c2]
    rw [cu]
    apply card_le_card
    intro y hy
    rw [mem_neighborFinset]
    rcases mem_union.mp hy with h | h
    · obtain ⟨i, -, rfl⟩ := mem_image.mp h
      exact ⟨by simp, Or.inr (Or.inl rfl)⟩
    · obtain ⟨b', hb', rfl⟩ := mem_image.mp h
      refine ⟨?_, Or.inr (Or.inr ⟨a, b, b', rfl, rfl⟩)⟩
      intro e
      have e2 := (Prod.mk.inj (Sum.inl.inj (Sum.inr.inj e))).2
      exact (mem_erase.mp hb').1 e2.symm
  have sum := X.sum_degrees_eq_twice_card_edges
  have big : s * (t * d) + t * d * (s + (d - 1)) ≤ ∑ v, X.degree v := by
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_prod_type]
    have h1 : s * (t * d) ≤ ∑ i : Fin s, X.degree (Sum.inl i) := by
      simpa using card_nsmul_le_sum univ (fun i : Fin s => X.degree (Sum.inl i)) (t * d)
        (fun i _ => lbU i)
    have h2 : t * d * (s + (d - 1)) ≤
        ∑ a : Fin t, ∑ b : Fin d, X.degree (Sum.inr (Sum.inl (a, b))) := by
      have h := sum_le_sum (s := (univ : Finset (Fin t)))
        (fun a _ => sum_le_sum (s := (univ : Finset (Fin d))) (fun b _ => lbR a b))
      simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at h
      calc t * d * (s + (d - 1)) = t * (d * (s + (d - 1))) := by ring
        _ ≤ _ := h
    omega
  have e := card_edgeFinset_le_extremalNumber free
  have card : Fintype.card V = s + (t * d + r) := by simp [V]
  rw [card] at e
  have split : 2 * s + d - 1 = s + (s + (d - 1)) := by omega
  rw [split]
  calc t * d * (s + (s + (d - 1))) = s * (t * d) + t * d * (s + (d - 1)) := by ring
    _ ≤ ∑ v, X.degree v := big
    _ = 2 * X.edgeFinset.card := by convert sum
    _ ≤ _ := by omega

theorem P_bound (G : SimpleGraph (Fin q)) {s d : ℕ} (h : P G s d) : s < q ∧ d < q := by
  constructor
  · by_contra hs
    obtain ⟨z, hz, -⟩ := h univ (by simp; omega)
    exact hz (mem_univ z)
  · obtain ⟨z, -, -, hd⟩ := h ∅ (by simp)
    have dz : G.degree z < q := by simpa using G.degree_lt_card_verts z
    omega

theorem upper (G : SimpleGraph (Fin q)) (active : ∀ v, ¬ G.IsIsolated v)
    (star : ∀ v w, G.Adj v w → G.degree v ≤ 1 ∨ G.degree w ≤ 1)
    {n : ℕ} (H : SimpleGraph (Fin n)) (free : G.Free H) :
    ∃ s d, 1 ≤ d ∧ P G s d ∧
      2 * H.edgeFinset.card + n ≤ 2 * s * n + d * n + (6 * q * q + 2 * q) := by
  set S : Finset (Fin n) := univ.filter (fun y => 3 * q ≤ H.degree y) with hSdef
  have ex : ∃ d', ¬ P G S.card d' := ⟨q, fun h => by
    have hb := (P_bound G h).2
    omega⟩
  obtain ⟨d', hspec, hmin⟩ : ∃ d', ¬ P G S.card d' ∧ ∀ m, m < d' → P G S.card m :=
    ⟨Nat.find ex, Nat.find_spec ex, fun m hm => not_not.mp (Nat.find_min ex hm)⟩
  have hspec' := hspec
  unfold P at hspec
  push Not at hspec
  obtain ⟨A, hA, hAz⟩ := hspec
  let p : Fin q → Fin q := fun v =>
    if h : IsC G v then v else Classical.choose (leaf_nbr G active h)
  let T := (A.image p).filter (IsC G)
  have hTcard : T.card ≤ S.card := ((card_filter_le _ _).trans card_image_le).trans hA
  have hTdeg : ∀ z, IsC G z → z ∉ T → G.degree z < d' := by
    intro z hz hzT
    apply hAz z
    · intro hzA
      apply hzT
      exact mem_filter.mpr ⟨mem_image.mpr ⟨z, hzA, by simp [p, hz]⟩, hz⟩
    · intro w hw hwA
      apply hzT
      have hwC : ¬ IsC G w := fun c => not_both G star hw hz c
      refine mem_filter.mpr ⟨mem_image.mpr ⟨w, hwA, ?_⟩, hz⟩
      have sp := (Classical.choose_spec (leaf_nbr G active hwC)).1
      have pw : p w = Classical.choose (leaf_nbr G active hwC) := by simp [p, hwC]
      rw [pw]
      exact uniq G (leaf_deg G hwC) sp hw.symm
  have hTC : ∀ t ∈ T, IsC G t := fun t ht => (mem_filter.mp ht).2
  have hSdeg : ∀ x ∈ S, 3 * q ≤ H.degree x := fun x hx => (mem_filter.mp hx).2
  have hSout : ∀ y, y ∉ S → H.degree y < 3 * q := by
    intro y hy
    by_contra h
    exact hy (mem_filter.mpr ⟨mem_univ y, by omega⟩)
  rcases Nat.eq_zero_or_pos d' with h0 | hpos
  · exfalso
    apply free
    apply embed G active star H S T hTC hTcard hSdeg
    intro z hz hzT
    have hlt := hTdeg z hz hzT
    omega
  obtain ⟨d, hd⟩ : ∃ d, d' = d + 1 := ⟨d' - 1, by omega⟩
  subst hd
  have hPd : P G S.card d := hmin d (by omega)
  have d1 : 1 ≤ d := by
    by_contra h0
    have d0 : d = 0 := by omega
    subst d0
    apply hspec'
    intro A' hA'
    obtain ⟨z, h1, h2, -⟩ := hPd A' hA'
    refine ⟨z, h1, h2, ?_⟩
    have iso := active z
    unfold IsIsolated at iso
    push Not at iso
    exact (G.degree_pos_iff_exists_adj z).mpr iso
  refine ⟨S.card, d, d1, hPd, ?_⟩
  by_cases Q : ∀ W : Finset (Fin n), W.card ≤ q →
      ∃ x, x ∉ S ∧ x ∉ W ∧ d ≤ ((H.neighborFinset x) \ (S ∪ W)).card
  · exfalso
    apply free
    apply embed G active star H S T hTC hTcard hSdeg
    intro z hz hzT W hW
    obtain ⟨x, h1, h2, h3⟩ := Q W hW
    have hlt := hTdeg z hz hzT
    exact ⟨x, h1, h2, by omega⟩
  · push Not at Q
    obtain ⟨W, hW, hfail⟩ := Q
    have c := count H (3 * q) d q S W hSout hW hfail
    simp only [Fintype.card_fin] at c
    have sq := (P_bound G hPd).1
    nlinarith

theorem ub (G : SimpleGraph (Fin q)) (active : ∀ v, ¬ G.IsIsolated v)
    (star : ∀ v w, G.Adj v w → G.degree v ≤ 1 ∨ G.degree w ≤ 1) (hne : G ≠ ⊥) (n : ℕ) :
    ∃ s d, 1 ≤ d ∧ P G s d ∧
      2 * extremalNumber n G + n ≤ 2 * s * n + d * n + (6 * q * q + 2 * q) := by
  obtain ⟨H, inst, hH⟩ := exists_isExtremal_free (V := Fin n) hne
  have hfree := hH.1
  have hcard := card_edgeFinset_of_isExtremal_free hH
  rw [Fintype.card_fin] at hcard
  obtain ⟨s, d, h1, h2, h3⟩ := upper G active star H hfree
  refine ⟨s, d, h1, h2, ?_⟩
  rw [← hcard]
  convert h3

theorem lb (G : SimpleGraph (Fin q)) {s d : ℕ} (hd : 1 ≤ d) (hP : P G s d) (m : ℕ)
    (hm : q ≤ m) : (2 * s + d - 1) * m ≤ 2 * extremalNumber m G + 6 * q * q := by
  obtain ⟨hs, hdq⟩ := P_bound G hP
  have key := lower G s d ((m - s) / d) ((m - s) % d) hd hP
  have e : s + ((m - s) / d * d + (m - s) % d) = m := by
    rw [Nat.div_add_mod']
    omega
  rw [e] at key
  have r : (m - s) % d < d := Nat.mod_lt _ (by omega)
  have small : (2 * s + d - 1) * (s + (m - s) % d) ≤ (3 * q) * (2 * q) :=
    Nat.mul_le_mul (by omega) (by omega)
  have split : (2 * s + d - 1) * m =
      (m - s) / d * d * (2 * s + d - 1) + (2 * s + d - 1) * (s + (m - s) % d) := by
    conv_lhs => rw [← e]
    ring
  nlinarith

end E713Star

theorem OMA.solution : OMA.R_Erdos713_erdos_713_parts_i_R1_H2_R1.H2 := by
  intro q G _ _ _ active _ _ hub star a b hab often
  have hne : G ≠ ⊥ := by
    obtain ⟨v, hv⟩ := hub
    rintro rfl
    simp at hv
  have UB : ∀ n, ∃ K, K < 3 * q ∧ (∃ s d, 1 ≤ d ∧ E713Star.P G s d ∧ K = 2 * s + d - 1) ∧
      2 * extremalNumber n G ≤ K * n + (6 * q * q + 2 * q) := by
    intro n
    obtain ⟨s, d, h1, h2, h3⟩ := E713Star.ub G active star hne n
    obtain ⟨hs, hd⟩ := E713Star.P_bound G h2
    refine ⟨2 * s + d - 1, by omega, ⟨s, d, h1, h2, rfl⟩, ?_⟩
    have e1 : 2 * s + d - 1 + 1 = 2 * s + d := by omega
    have e2 : (2 * s + d - 1) * n + n = 2 * s * n + d * n := by
      calc (2 * s + d - 1) * n + n = (2 * s + d - 1 + 1) * n := by ring
        _ = 2 * s * n + d * n := by rw [e1]; ring
    omega
  have LB : ∀ K, (∃ s d, 1 ≤ d ∧ E713Star.P G s d ∧ K = 2 * s + d - 1) → ∀ m, q ≤ m →
      K * m ≤ 2 * extremalNumber m G + (6 * q * q + 2 * q) := by
    rintro K ⟨s, d, h1, h2, rfl⟩ m hm
    have h := E713Star.lb G h1 h2 m hm
    omega
  obtain ⟨K, hK, hbK⟩ : ∃ K : ℕ, (∃ s d, 1 ≤ d ∧ E713Star.P G s d ∧ K = 2 * s + d - 1) ∧
      2 * b ≤ (K : ℚ) := by
    by_contra hcon
    push Not at hcon
    have ev : ∀ᶠ n : ℕ in atTop, ∀ K ∈ range (3 * q),
        (∃ s d, 1 ≤ d ∧ E713Star.P G s d ∧ K = 2 * s + d - 1) →
        (K : ℚ) * n + ((6 * q * q + 2 * q : ℕ) : ℚ) ≤ 2 * b * n := by
      rw [eventually_all_finset]
      intro K _
      by_cases hK : ∃ s d, 1 ≤ d ∧ E713Star.P G s d ∧ K = 2 * s + d - 1
      · have gap := hcon K hK
        filter_upwards [eventually_ge_atTop
          (Nat.ceil (((6 * q * q + 2 * q : ℕ) : ℚ) / (2 * b - K)))] with n hn _
        have pos : 0 < 2 * b - K := by linarith
        have h1 : ((6 * q * q + 2 * q : ℕ) : ℚ) / (2 * b - K) ≤ n :=
          (Nat.le_ceil _).trans (by exact_mod_cast hn)
        have h2 := (div_le_iff₀ pos).mp h1
        linarith
      · exact Eventually.of_forall (fun n h => absurd h hK)
    obtain ⟨N, hN⟩ := eventually_atTop.mp ev
    obtain ⟨n, hn, big⟩ := often N
    obtain ⟨K, hKq, hK, hub'⟩ := UB n
    have h1 := hN n hn K (mem_range.mpr hKq) hK
    have h2 : (2 : ℚ) * extremalNumber n G ≤ K * n + ((6 * q * q + 2 * q : ℕ) : ℚ) := by
      exact_mod_cast hub'
    linarith
  refine ⟨max q (Nat.ceil (((6 * q * q + 2 * q : ℕ) : ℚ) / (K - 2 * a))), ?_⟩
  intro m hm
  have pos : (0 : ℚ) < K - 2 * a := by linarith
  have hmq : q ≤ m := le_trans (le_max_left _ _) hm
  have h1 : ((6 * q * q + 2 * q : ℕ) : ℚ) / (K - 2 * a) ≤ m :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_trans (le_max_right _ _) hm)
  have h2 := (div_le_iff₀ pos).mp h1
  have h3 : (K : ℚ) * m ≤ 2 * extremalNumber m G + ((6 * q * q + 2 * q : ℕ) : ℚ) := by
    exact_mod_cast LB K hK m hmq
  linarith
