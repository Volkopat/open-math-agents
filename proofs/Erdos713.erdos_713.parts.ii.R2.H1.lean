import OMAReductions.R_Erdos713_erdos_713_parts_ii_R2

/-!
Proof of `Erdos713.erdos_713.parts.ii.R2.H1`: a graph with a vertex of degree at most one
cannot be minimal at a superlinear extremal power scale `n^α` (`α > 1`).
-/

-- Problem: Erdos713.erdos_713.parts.ii.R2.H1
-- Upstream: reductions/Erdos713.erdos_713.parts.ii.R2.lean
-- Credit: @ppleskov

namespace OMA.P_Erdos713_ii_R2_H1

open Filter Asymptotics SimpleGraph Finset
open scoped Classical Topology

private def keepEdgesOn {V : Type*} (X : SimpleGraph V) (S : Finset V) : SimpleGraph V where
  Adj a b := a ∈ S ∧ b ∈ S ∧ X.Adj a b
  symm := ⟨fun _ _ h => ⟨h.2.1, h.1, h.2.2.symm⟩⟩
  loopless := ⟨fun _ h => X.irrefl h.2.2⟩

private lemma keepEdgesOn_adj {V : Type*} (X : SimpleGraph V) (S : Finset V) (a b : V) :
    (keepEdgesOn X S).Adj a b ↔ a ∈ S ∧ b ∈ S ∧ X.Adj a b := Iff.rfl

private lemma keepEdgesOn_le {V : Type*} (X : SimpleGraph V) (S : Finset V) :
    keepEdgesOn X S ≤ X :=
  fun _ _ h => h.2.2

private lemma card_edgeFinset_keepEdgesOn_erase {V : Type*} [Fintype V]
    (X : SimpleGraph V) (S : Finset V) (x : V) (_hx : x ∈ S) :
    (keepEdgesOn X S).edgeFinset.card ≤
      (keepEdgesOn X (S.erase x)).edgeFinset.card + (keepEdgesOn X S).degree x := by
  have heq : keepEdgesOn X (S.erase x) = (keepEdgesOn X S).deleteIncidenceSet x := by
    ext a b
    simp only [keepEdgesOn_adj, mem_erase, deleteIncidenceSet_adj]
    constructor
    · rintro ⟨⟨hax, ha⟩, ⟨hbx, hb⟩, hab⟩
      exact ⟨⟨ha, hb, hab⟩, hax, hbx⟩
    · rintro ⟨⟨ha, hb, hab⟩, hax, hbx⟩
      exact ⟨⟨hax, ha⟩, ⟨hbx, hb⟩, hab⟩
  have hdel : ((keepEdgesOn X S).deleteIncidenceSet x).edgeFinset.card =
      (keepEdgesOn X S).edgeFinset.card - (keepEdgesOn X S).degree x := by
    convert card_edgeFinset_deleteIncidenceSet (keepEdgesOn X S) x
  have hcard_eq : (keepEdgesOn X (S.erase x)).edgeFinset.card =
      ((keepEdgesOn X S).deleteIncidenceSet x).edgeFinset.card := by
    congr 1
    ext e
    simp [heq]
  omega

private lemma free_keepEdgesOn_of_copy_extend {r s n : ℕ}
    (F : SimpleGraph (Fin r)) (v : Fin r) (hv : F.degree v < 2)
    (e : Fin s ≃ {w : Fin r // w ≠ v})
    (J : SimpleGraph (Fin s))
    (hJ : ∀ a b, J.Adj a b ↔ F.Adj (e a).val (e b).val)
    (hs : s + 1 = r)
    (X : SimpleGraph (Fin n)) (hfree : F.Free X)
    (S : Finset (Fin n)) (hS : r ≤ S.card)
    (hdeg : ∀ x ∈ S, r ≤ (keepEdgesOn X S).degree x) :
    J.Free (keepEdgesOn X S) := by
  rintro ⟨f⟩
  let Z := keepEdgesOn X S
  -- First re-route any isolated vertices of J so all vertices of J map into S.
  let supp : Finset (Fin s) := univ.filter fun a => ∃ b, J.Adj a b
  have hsupp_in : ∀ a ∈ supp, f a ∈ S := by
    intro a ha
    obtain ⟨b, hab⟩ := (mem_filter.mp ha).2
    exact (f.toHom.map_adj hab).1
  let imgSupp : Finset (Fin n) := supp.image f
  have himg_sub : imgSupp ⊆ S := by
    intro y hy
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hy
    exact hsupp_in a ha
  have himg_card : imgSupp.card = supp.card :=
    card_image_of_injective supp f.injective
  let restJ : Finset (Fin s) := univ \ supp
  let restS : Finset (Fin n) := S \ imgSupp
  have hrest_le : restJ.card ≤ restS.card := by
    have h1 : restJ.card + supp.card = s := by
      have := card_sdiff_add_card_eq_card (subset_univ supp)
      simpa [restJ] using this
    have h2 : restS.card + imgSupp.card = S.card :=
      card_sdiff_add_card_eq_card himg_sub
    omega
  let embRest : restJ ↪ restS :=
    restJ.equivFin.toEmbedding.trans ((Fin.castLEEmb hrest_le).trans restS.equivFin.symm.toEmbedding)
  let g : Fin s → Fin n := fun a =>
    if ha : a ∈ supp then f a else (embRest ⟨a, mem_sdiff.mpr ⟨mem_univ _, ha⟩⟩).val
  have hg_mem : ∀ a, g a ∈ S := by
    intro a
    by_cases ha : a ∈ supp
    · simp only [g, dif_pos ha]; exact hsupp_in a ha
    · simp only [g, dif_neg ha]
      exact (mem_sdiff.mp (embRest ⟨a, mem_sdiff.mpr ⟨mem_univ _, ha⟩⟩).property).1
  have hg_inj : Function.Injective g := by
    intro a b hab
    by_cases ha : a ∈ supp <;> by_cases hb : b ∈ supp
    · simp only [g, dif_pos ha, dif_pos hb] at hab
      exact f.injective hab
    · simp only [g, dif_pos ha, dif_neg hb] at hab
      have hnot : (embRest ⟨b, mem_sdiff.mpr ⟨mem_univ _, hb⟩⟩).val ∉ imgSupp :=
        (mem_sdiff.mp (embRest ⟨b, mem_sdiff.mpr ⟨mem_univ _, hb⟩⟩).property).2
      rw [← hab] at hnot
      exact (hnot (mem_image.mpr ⟨a, ha, rfl⟩)).elim
    · simp only [g, dif_neg ha, dif_pos hb] at hab
      have hnot : (embRest ⟨a, mem_sdiff.mpr ⟨mem_univ _, ha⟩⟩).val ∉ imgSupp :=
        (mem_sdiff.mp (embRest ⟨a, mem_sdiff.mpr ⟨mem_univ _, ha⟩⟩).property).2
      rw [hab] at hnot
      exact (hnot (mem_image.mpr ⟨b, hb, rfl⟩)).elim
    · simp only [g, dif_neg ha, dif_neg hb] at hab
      have hsub := embRest.injective (Subtype.ext hab)
      exact congrArg Subtype.val hsub
  have hg_adj : ∀ {a b}, J.Adj a b → Z.Adj (g a) (g b) := by
    intro a b hab
    have ha : a ∈ supp := mem_filter.mpr ⟨mem_univ _, b, hab⟩
    have hb : b ∈ supp := mem_filter.mpr ⟨mem_univ _, a, hab.symm⟩
    simp only [g, dif_pos ha, dif_pos hb]
    exact f.toHom.map_adj hab
  let used : Finset (Fin n) := univ.image g
  have hused_card : used.card = s := by
    rw [card_image_of_injective _ hg_inj, card_univ, Fintype.card_fin]
  -- Pick a fresh vertex y outside `used`, adjacent to `g (e.symm ⟨u, _⟩)` if `v` has a neighbor `u`.
  have hy_exists : ∃ y : Fin n, y ∉ used ∧
      ∀ w : Fin r, (hw : w ≠ v) → F.Adj v w → X.Adj y (g (e.symm ⟨w, hw⟩)) := by
    by_cases hdeg0 : F.degree v = 0
    · have hlt : used.card < S.card := by omega
      have hne : (S \ used).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro hemp
        have hsub : S ⊆ used := sdiff_eq_empty_iff_subset.mp hemp
        have := card_le_card hsub
        omega
      obtain ⟨y, hy⟩ := hne
      refine ⟨y, (mem_sdiff.mp hy).2, fun w _ hvw => ?_⟩
      have hpos : 0 < F.degree v := (F.degree_pos_iff_exists_adj v).mpr ⟨w, hvw⟩
      omega
    · have hdeg1 : F.degree v = 1 := by omega
      obtain ⟨u, huv, huniq⟩ := degree_eq_one_iff_existsUnique_adj.mp hdeg1
      have huv_ne : u ≠ v := huv.ne.symm
      let u' : Fin s := e.symm ⟨u, huv_ne⟩
      let x : Fin n := g u'
      have hxS : x ∈ S := hg_mem u'
      have hnbr : r ≤ (Z.neighborFinset x).card := by
        rw [card_neighborFinset_eq_degree]
        exact hdeg x hxS
      have hne : (Z.neighborFinset x \ used).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro hemp
        have hsub : Z.neighborFinset x ⊆ used := sdiff_eq_empty_iff_subset.mp hemp
        have := card_le_card hsub
        omega
      obtain ⟨y, hy⟩ := hne
      have hy_not : y ∉ used := (mem_sdiff.mp hy).2
      have hy_adj : Z.Adj x y := (mem_neighborFinset Z x y).mp (mem_sdiff.mp hy).1
      refine ⟨y, hy_not, fun w hw hvw => ?_⟩
      have hwu : w = u := huniq w hvw
      subst hwu
      exact ((keepEdgesOn_adj X S x y).mp hy_adj).2.2.symm
  obtain ⟨y, hy_not, hy_adj⟩ := hy_exists
  let h : Fin r → Fin n := fun w => if hw : w = v then y else g (e.symm ⟨w, hw⟩)
  have hh_inj : Function.Injective h := by
    intro a b hab
    by_cases ha : a = v <;> by_cases hb : b = v
    · exact ha.trans hb.symm
    · simp only [h, dif_pos ha, dif_neg hb] at hab
      exact (hy_not (mem_image.mpr ⟨e.symm ⟨b, hb⟩, mem_univ _, hab.symm⟩)).elim
    · simp only [h, dif_neg ha, dif_pos hb] at hab
      exact (hy_not (mem_image.mpr ⟨e.symm ⟨a, ha⟩, mem_univ _, hab⟩)).elim
    · simp only [h, dif_neg ha, dif_neg hb] at hab
      have h1 := e.symm.injective (hg_inj hab)
      exact congrArg Subtype.val h1
  have hh_adj : ∀ {a b}, F.Adj a b → X.Adj (h a) (h b) := by
    intro a b hab
    by_cases ha : a = v
    · have hb : b ≠ v := by rw [← ha]; exact hab.ne.symm
      simp only [h, dif_pos ha, dif_neg hb]
      exact hy_adj b hb (ha ▸ hab)
    · by_cases hb : b = v
      · simp only [h, dif_neg ha, dif_pos hb]
        exact (hy_adj a ha (hb ▸ hab.symm)).symm
      · simp only [h, dif_neg ha, dif_neg hb]
        have hJadj : J.Adj (e.symm ⟨a, ha⟩) (e.symm ⟨b, hb⟩) := by
          rw [hJ]
          simpa using hab
        exact ((keepEdgesOn_adj X S _ _).mp (hg_adj hJadj)).2.2
  exact hfree ⟨⟨⟨h, hh_adj⟩, hh_inj⟩⟩

private lemma extremalNumber_le_pruned {r s : ℕ}
    (F : SimpleGraph (Fin r)) (v : Fin r) (hv : F.degree v < 2)
    (e : Fin s ≃ {w : Fin r // w ≠ v})
    (J : SimpleGraph (Fin s))
    (hJ : ∀ a b, J.Adj a b ↔ F.Adj (e a).val (e b).val)
    (hs : s + 1 = r)
    (n : ℕ) :
    extremalNumber n F ≤ extremalNumber n J + r * n := by
  rw [← Fintype.card_fin n, extremalNumber_le_iff (V := Fin n)]
  intro X _ hfree
  rw [Fintype.card_fin]
  let P (k : ℕ) : Prop :=
    ∃ S : Finset (Fin n), S.card = k ∧
      X.edgeFinset.card ≤ (keepEdgesOn X S).edgeFinset.card + r * (n - S.card)
  have hex : ∃ k, P k := by
    refine ⟨n, univ, by simp, ?_⟩
    simp only [card_univ, Fintype.card_fin, Nat.sub_self, Nat.mul_zero, Nat.add_zero]
    apply Finset.card_le_card
    intro x hx
    induction x using Sym2.ind with
    | _ a b =>
      rw [mem_edgeFinset, mem_edgeSet] at hx ⊢
      exact (keepEdgesOn_adj X univ a b).mpr ⟨mem_univ _, mem_univ _, hx⟩
  obtain ⟨S, hScard, hSbound⟩ := Nat.find_spec hex
  by_cases hSr : S.card < r
  · have hYedges : (keepEdgesOn X S).edgeFinset.card ≤ r * S.card := by
      have hdeg_le : ∀ x : Fin n, (keepEdgesOn X S).degree x ≤ if x ∈ S then S.card else 0 := by
        intro x
        rw [← card_neighborFinset_eq_degree]
        by_cases hx : x ∈ S
        · rw [if_pos hx]
          exact card_le_card fun y hy =>
            ((keepEdgesOn_adj X S x y).mp ((mem_neighborFinset _ _ _).mp hy)).2.1
        · rw [if_neg hx]
          apply le_of_eq
          rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
          intro y hy
          exact hx ((keepEdgesOn_adj X S x y).mp ((mem_neighborFinset _ _ _).mp hy)).1
      have hhand := (keepEdgesOn X S).sum_degrees_eq_twice_card_edges
      have hsum : ∑ x : Fin n, (keepEdgesOn X S).degree x ≤ S.card * S.card := by
        calc ∑ x : Fin n, (keepEdgesOn X S).degree x
            ≤ ∑ x : Fin n, (if x ∈ S then S.card else 0) :=
              sum_le_sum fun x _ => hdeg_le x
          _ = ∑ _x ∈ S, S.card := by rw [sum_ite_mem, univ_inter]
          _ = S.card * S.card := by simp
      have hle1 : (keepEdgesOn X S).edgeFinset.card ≤ S.card * S.card := by omega
      have hle2 : S.card * S.card ≤ r * S.card := Nat.mul_le_mul_right S.card hSr.le
      exact hle1.trans hle2
    have hSn : S.card ≤ n := by simpa using card_le_univ S
    have hlin : r * S.card + r * (n - S.card) = r * n := by
      rw [← Nat.mul_add, Nat.add_sub_cancel' hSn]
    omega
  · push Not at hSr
    have hdeg : ∀ x ∈ S, r ≤ (keepEdgesOn X S).degree x := by
      intro x hx
      by_contra! hlt
      have hlt_card : (S.erase x).card < Nat.find hex := by
        rw [card_erase_of_mem hx, hScard]
        have : 0 < S.card := Finset.card_pos.mpr ⟨x, hx⟩
        omega
      have hSn : S.card ≤ n := by simpa using card_le_univ S
      have hSpos : 1 ≤ S.card := Finset.card_pos.mpr ⟨x, hx⟩
      have hsub : n - (S.erase x).card = (n - S.card) + 1 := by
        rw [card_erase_of_mem hx]
        omega
      have herase := card_edgeFinset_keepEdgesOn_erase X S x hx
      have hnew : X.edgeFinset.card ≤
          (keepEdgesOn X (S.erase x)).edgeFinset.card + r * (n - (S.erase x).card) := by
        rw [hsub, Nat.mul_add, Nat.mul_one]
        have hstep1 : (keepEdgesOn X S).edgeFinset.card ≤
            (keepEdgesOn X (S.erase x)).edgeFinset.card + r := by
          have : (keepEdgesOn X S).degree x ≤ r := hlt.le
          have h1 : (keepEdgesOn X S).edgeFinset.card ≤
              (keepEdgesOn X (S.erase x)).edgeFinset.card + (keepEdgesOn X S).degree x := by
            convert herase
          exact h1.trans (Nat.add_le_add_left this _)
        exact hSbound.trans (by
          calc (keepEdgesOn X S).edgeFinset.card + r * (n - S.card)
              ≤ ((keepEdgesOn X (S.erase x)).edgeFinset.card + r) + r * (n - S.card) :=
                Nat.add_le_add_right hstep1 _
            _ = (keepEdgesOn X (S.erase x)).edgeFinset.card + (r * (n - S.card) + r) := by omega)
      exact Nat.find_min hex hlt_card ⟨S.erase x, rfl, hnew⟩
    have hJfree : J.Free (keepEdgesOn X S) :=
      free_keepEdgesOn_of_copy_extend F v hv e J hJ hs X hfree S hSr hdeg
    have hZle : (keepEdgesOn X S).edgeFinset.card ≤ extremalNumber n J := by
      simpa using card_edgeFinset_le_extremalNumber hJfree
    have hsub_le : r * (n - S.card) ≤ r * n := Nat.mul_le_mul_left r (Nat.sub_le n S.card)
    omega

private lemma isLittleO_linear_rpow {r : ℕ} {α : ℝ} (hα : 1 < α) :
    (fun n : ℕ => (r : ℝ) * (n : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ) ^ α) := by
  have h1 : (fun n : ℕ => (n : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ) ^ α) := by
    apply (isLittleO_iff_tendsto' _).2
    · have hneg : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(α - 1))) atTop (𝓝 0) :=
        (tendsto_rpow_neg_atTop (sub_pos.mpr hα)).comp tendsto_natCast_atTop_atTop
      refine hneg.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
      have hnpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
      rw [neg_sub, Real.rpow_sub hnpos, Real.rpow_one]
    · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn hzero
      exact ((Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) α).ne' hzero).elim
  exact h1.const_mul_left (r : ℝ)

end OMA.P_Erdos713_ii_R2_H1

open Filter Asymptotics SimpleGraph Finset
open scoped Classical Topology

theorem OMA.solution : OMA.R_Erdos713_erdos_713_parts_ii_R2.H1 := by
  intro r F ⟨v, hv⟩ α hα hnot hmin
  have hr : 1 ≤ r := Nat.pos_of_ne_zero (fun h0 => by subst h0; exact Fin.elim0 v)
  let s : ℕ := r - 1
  have hs : s + 1 = r := Nat.sub_add_cancel hr
  have hcardU : Fintype.card {w : Fin r // w ≠ v} = s := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_unique]
  let e : Fin s ≃ {w : Fin r // w ≠ v} := (Fintype.equivFinOfCardEq hcardU).symm
  let J : SimpleGraph (Fin s) := (F.induce {w : Fin r | w ≠ v}).comap e
  have hJadj : ∀ a b, J.Adj a b ↔ F.Adj (e a).val (e b).val := fun _ _ => Iff.rfl
  have hJF : J ⊑ F := ⟨⟨⟨fun a => (e a).val, fun hab => (hJadj _ _).mp hab⟩,
    fun _ _ h => e.injective (Subtype.ext h)⟩⟩
  have hJedges : J.edgeFinset.card ≤ F.edgeFinset.card := by
    let emb : Fin s ↪ Fin r := ⟨fun a => (e a).val, fun _ _ h => e.injective (Subtype.ext h)⟩
    have hsub : J.edgeFinset.map emb.sym2Map ⊆ F.edgeFinset := by
      intro x hx
      obtain ⟨a, ha, rfl⟩ := mem_map.mp hx
      induction a using Sym2.inductionOn with
      | hf p q =>
        rw [mem_edgeFinset, mem_edgeSet] at ha
        rw [mem_edgeFinset]
        exact (hJadj p q).mp ha
    simpa [card_map] using card_le_card hsub
  have hsmall : s + J.edgeFinset.card < r + F.edgeFinset.card := by omega
  have hJo : (fun n : ℕ => (extremalNumber n J : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ) ^ α) :=
    hmin s J hJF hsmall
  have hlin : (fun n : ℕ => (r : ℝ) * (n : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ) ^ α) :=
    OMA.P_Erdos713_ii_R2_H1.isLittleO_linear_rpow hα
  have hsum : (fun n : ℕ => (extremalNumber n J : ℝ) + (r : ℝ) * (n : ℝ)) =o[atTop]
      (fun n : ℕ => (n : ℝ) ^ α) := hJo.add hlin
  have hFo : (fun n : ℕ => (extremalNumber n F : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ) ^ α) := by
    refine IsBigO.trans_isLittleO ?_ hsum
    refine IsBigO.of_bound 1 (Eventually.of_forall fun n => ?_)
    have hle := OMA.P_Erdos713_ii_R2_H1.extremalNumber_le_pruned F v hv e J hJadj hs n
    have hleR : (extremalNumber n F : ℝ) ≤ (extremalNumber n J : ℝ) + (r : ℝ) * (n : ℝ) := by
      exact_mod_cast hle
    rw [Real.norm_natCast, Real.norm_of_nonneg (by positivity), one_mul]
    exact hleR
  exact hnot hFo
