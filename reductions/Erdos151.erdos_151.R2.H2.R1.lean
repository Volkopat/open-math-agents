import OMAReductions.R_Erdos151_erdos_151_R2

-- Reduction of the guarded K₄-free Ramsey-jump case of Erdős Problem 151.
-- Credit: @Alewawa
-- @princek0 proved the bound through threshold nine in the K₄-free variant.
-- The additional restriction at higher thresholds comes from incidence-matrix rank.

open Finset SimpleGraph
open scoped Classical

namespace OMA.R_Erdos151_erdos_151_R2_H2_R1

/-- The previously proved small-threshold bound, specialized to K₄-free graphs. -/
def H1 : Prop :=
  ∀ m, Erdos151.H m ≤ 9 → ∀ G : SimpleGraph (Fin m), G.CliqueFree 4 →
    cliqueTransversalNumber G ≤ m - Erdos151.H m

/-- A family of triangles in a K₄-free graph with each participating edge used
exactly three times admits a bichromatic edge coloring. This is the graph
triangle instance of Choi, Kwon and Park, arXiv:2609.33902, Corollary 6.2. -/
def H2 : Prop :=
  ∀ (m : ℕ) (G : SimpleGraph (Fin m)) (T : Finset (Finset (Fin m))),
    G.CliqueFree 4 → (∀ t ∈ T, G.IsNClique 3 t) →
    let edges := fun t : Finset (Fin m) => t.sym2.filter (fun e => ¬ e.IsDiag)
    (∀ e ∈ T.biUnion edges, (T.filter (fun t => e ∈ edges t)).card = 3) →
    ∃ c : Sym2 (Fin m) → Bool, ∀ t ∈ T,
      (∃ e ∈ edges t, c e = true) ∧ (∃ e ∈ edges t, c e = false)

/-- The remaining guarded jumps contain a family of triangles with an incidence matching
covering its edges, strict incidence expansion on nonempty proper edge sets,
and one participating edge used at least four times. -/
def H3 : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin (n + 1))),
    10 ≤ Erdos151.H (n + 1) → Erdos151.H n < Erdos151.H (n + 1) →
    G.CliqueFree 4 →
    (∀ v, (univ.filter (G.Adj v)).card < Erdos151.H (n + 1)) →
    (¬ ∃ F : SimpleGraph (Fin (n + 1)), F.CliqueFree 3 ∧
      ∀ t, G.IsBigMaximalClique t → ∃ x ∈ t, ∃ y ∈ t, F.Adj x y) →
    (∀ A B : Finset (Fin (n + 1)), B.Nonempty → A ⊆ B →
      (∀ t, G.IsBigMaximalClique t → (∃ x ∈ t, x ∈ A) → ∃ y ∈ t, y ∈ B \ A) →
      A.card + Erdos151.H (n + 1 - B.card) < Erdos151.H (n + 1)) →
    (∃ T : Finset (Finset (Fin (n + 1))), T.Nonempty ∧
      (∀ t ∈ T, G.IsNClique 3 t) ∧
      let edges := fun t : Finset (Fin (n + 1)) => t.sym2.filter (fun e => ¬ e.IsDiag)
      (∀ S ⊆ T.biUnion edges, S.card ≤ (T.filter (fun t => ∃ e ∈ S, e ∈ edges t)).card) ∧
      (∀ S ⊂ T.biUnion edges, S.Nonempty →
        S.card < (T.filter (fun t => ∃ e ∈ S, e ∈ edges t)).card) ∧
      (∃ e ∈ T.biUnion edges, 4 ≤ (T.filter (fun t => e ∈ edges t)).card)) →
    cliqueTransversalNumber G ≤ (n + 1) - Erdos151.H (n + 1)

section Proof

variable {ι α : Type*}

private lemma opposite_signs (s : Finset α) (w : α → ℚ)
    (hzero : ∑ e ∈ s, w e = 0) (hsome : ∃ e ∈ s, w e ≠ 0) :
    (∃ e ∈ s, 0 < w e) ∧ (∃ e ∈ s, w e < 0) := by
  obtain ⟨e, he, hne⟩ := hsome
  constructor
  · by_contra! hp
    have hlt := sum_neg' hp ⟨e, he, lt_of_le_of_ne (hp e he) hne⟩
    exact (ne_of_lt hlt) hzero
  · by_contra! hn
    have hlt := sum_pos' hn ⟨e, he, lt_of_le_of_ne (hn e he) (Ne.symm hne)⟩
    exact (ne_of_gt hlt) hzero

/-- A partial signed coloring can be extended over constraints whose weights all vanish. -/
private lemma weights_impossible [DecidableEq α] (T : Finset ι) (E : ι → Finset α)
    (hbad : ¬ ∃ c : α → Bool, ∀ t ∈ T,
      (∃ e ∈ E t, c e = true) ∧ (∃ e ∈ E t, c e = false))
    (minimal : ∀ U ⊂ T, ∃ c : α → Bool, ∀ t ∈ U,
      (∃ e ∈ E t, c e = true) ∧ (∃ e ∈ E t, c e = false))
    (w : α → ℚ) (hw : ∃ e ∈ T.biUnion E, w e ≠ 0)
    (mixed : ∀ t ∈ T, (∃ e ∈ E t, w e ≠ 0) →
      (∃ e ∈ E t, 0 < w e) ∧ (∃ e ∈ E t, w e < 0)) : False := by
  let Z := T.filter (fun t => ∀ e ∈ E t, w e = 0)
  have hZ : Z ⊂ T := by
    obtain ⟨e, he, hne⟩ := hw
    obtain ⟨t, ht, het⟩ := mem_biUnion.mp he
    refine Finset.ssubset_iff_subset_ne.mpr ⟨filter_subset _ _, fun heq => ?_⟩
    have htZ : t ∈ Z := by simpa only [heq] using ht
    exact hne ((mem_filter.mp htZ).2 e het)
  obtain ⟨base, hbase⟩ := minimal Z hZ
  let c (e : α) : Bool := if w e = 0 then base e else decide (0 < w e)
  apply hbad
  refine ⟨c, ?_⟩
  intro t ht
  by_cases htZ : t ∈ Z
  · obtain ⟨⟨p, hp, hcp⟩, ⟨q, hq, hcq⟩⟩ := hbase t htZ
    have hz := (mem_filter.mp htZ).2
    exact ⟨⟨p, hp, by simpa only [c, if_pos (hz p hp)] using hcp⟩,
      ⟨q, hq, by simpa only [c, if_pos (hz q hq)] using hcq⟩⟩
  · have hsome : ∃ e ∈ E t, w e ≠ 0 := by
      by_contra! hz
      exact htZ (mem_filter.mpr ⟨ht, hz⟩)
    obtain ⟨⟨p, hp, hwp⟩, ⟨q, hq, hwq⟩⟩ := mixed t ht hsome
    exact ⟨⟨p, hp, by simp [c, ne_of_gt hwp, hwp]⟩,
      ⟨q, hq, by simp [c, ne_of_lt hwq, not_lt_of_gt hwq]⟩⟩

/-- The incidence map on a selected edge set is injective. For a nonempty proper
set it cannot be surjective: that would extend any coloring from untouched
constraints using rational weights of prescribed signs on the outside. -/
private lemma incidence_bounds [DecidableEq ι] [DecidableEq α] (T : Finset ι) (E : ι → Finset α)
    (hbad : ¬ ∃ c : α → Bool, ∀ t ∈ T,
      (∃ e ∈ E t, c e = true) ∧ (∃ e ∈ E t, c e = false))
    (minimal : ∀ U ⊂ T, ∃ c : α → Bool, ∀ t ∈ U,
      (∃ e ∈ E t, c e = true) ∧ (∃ e ∈ E t, c e = false))
    (S : Finset α) (hS : S ⊆ T.biUnion E) :
    S.card ≤ (T.filter (fun t => ∃ e ∈ S, e ∈ E t)).card ∧
    (S ⊂ T.biUnion E → S.Nonempty →
      S.card < (T.filter (fun t => ∃ e ∈ S, e ∈ E t)).card) := by
  let U := T.filter (fun t => ∃ e ∈ S, e ∈ E t)
  let extend (w : ↥S → ℚ) (e : α) : ℚ := if h : e ∈ S then w ⟨e, h⟩ else 0
  let f : (↥S → ℚ) →ₗ[ℚ] (↥U → ℚ) :=
    { toFun := fun w t => ∑ e ∈ E t.val, extend w e
      map_add' := by
        intro x y
        funext t
        change (∑ e ∈ E t.val, extend (x + y) e) =
          (∑ e ∈ E t.val, extend x e) + (∑ e ∈ E t.val, extend y e)
        rw [← sum_add_distrib]
        apply sum_congr rfl
        intro e _
        by_cases he : e ∈ S <;> simp [extend, he, Pi.add_apply]
      map_smul' := by
        intro a x
        funext t
        change (∑ e ∈ E t.val, extend (a • x) e) = a * (∑ e ∈ E t.val, extend x e)
        rw [mul_sum]
        apply sum_congr rfl
        intro e _
        by_cases he : e ∈ S <;> simp [extend, he, Pi.smul_apply, smul_eq_mul] }
  have hinj : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro w hfw
    by_contra hn
    have hsome : ∃ e : ↥S, w e ≠ 0 := by
      by_contra! hw
      exact hn (funext hw)
    obtain ⟨e, hne⟩ := hsome
    refine weights_impossible T E hbad minimal (extend w)
      ⟨e.val, hS e.property, by simpa [extend, e.property] using hne⟩ ?_
    intro t ht ⟨a, hat, hwa⟩
    have haS : a ∈ S := by
      by_contra ha
      simp [extend, ha] at hwa
    have htU : t ∈ U := mem_filter.mpr ⟨ht, a, haS, hat⟩
    exact opposite_signs (E t) (extend w) (congrFun hfw ⟨t, htU⟩) ⟨a, hat, hwa⟩
  have hdim : S.card ≤ U.card := by
    simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] using
      LinearMap.finrank_le_finrank_of_injective hinj
  change S.card ≤ U.card ∧ (S ⊂ T.biUnion E → S.Nonempty → S.card < U.card)
  refine ⟨hdim, ?_⟩
  intro hproper hnonempty
  by_contra! hle
  have heq : Module.finrank ℚ (↥S → ℚ) = Module.finrank ℚ (↥U → ℚ) := by
    simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] using le_antisymm hdim hle
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := f) heq).mp hinj
  have hTouch : U.Nonempty := by
    obtain ⟨e, he⟩ := hnonempty
    obtain ⟨t, ht, het⟩ := mem_biUnion.mp (hS he)
    exact ⟨t, mem_filter.mpr ⟨ht, e, he, het⟩⟩
  have hRest : T \ U ⊂ T := by
    obtain ⟨t, ht⟩ := hTouch
    refine Finset.ssubset_iff_subset_ne.mpr ⟨sdiff_subset, fun heq => ?_⟩
    have htT := (mem_filter.mp ht).1
    have htRest : t ∈ T \ U := by simpa only [heq] using htT
    exact (mem_sdiff.mp htRest).2 ht
  obtain ⟨base, hbase⟩ := minimal (T \ U) hRest
  let outside (e : α) : ℚ := if e ∈ S then 0 else if base e = true then 1 else -1
  let rhs (t : ↥U) : ℚ := -(∑ e ∈ E t.val, outside e)
  obtain ⟨w, hw⟩ := hsurj rhs
  let all (e : α) := extend w e + outside e
  obtain ⟨a, ha, haS⟩ := exists_of_ssubset hproper
  refine weights_impossible T E hbad minimal all ⟨a, ha, ?_⟩ ?_
  · cases hc : base a <;> simp [all, extend, outside, haS, hc]
  · intro t ht hsome
    by_cases htU : t ∈ U
    · have hrow : ∑ e ∈ E t, extend w e = -(∑ e ∈ E t, outside e) :=
        congrFun hw ⟨t, htU⟩
      have hzero : ∑ e ∈ E t, all e = 0 := by simp only [all, sum_add_distrib, hrow, neg_add_cancel]
      exact opposite_signs (E t) all hzero hsome
    · have hnot {e : α} (he : e ∈ E t) : e ∉ S :=
        fun heS => htU (mem_filter.mpr ⟨ht, e, heS, he⟩)
      obtain ⟨⟨p, hp, hcp⟩, ⟨q, hq, hcq⟩⟩ := hbase t (mem_sdiff.mpr ⟨ht, htU⟩)
      exact ⟨⟨p, hp, by simp [all, extend, outside, hnot hp, hcp]⟩,
        ⟨q, hq, by simp [all, extend, outside, hnot hq, hcq]⟩⟩

private lemma hitting_of_bichromatic {m : ℕ} (G : SimpleGraph (Fin m))
    (c : Sym2 (Fin m) → Bool)
    (hc : ∀ t, G.IsNClique 3 t →
      (∃ e ∈ t.sym2.filter (fun e => ¬ e.IsDiag), c e = true) ∧
      (∃ e ∈ t.sym2.filter (fun e => ¬ e.IsDiag), c e = false)) :
    ∃ F : SimpleGraph (Fin m), F.CliqueFree 3 ∧
      ∀ t, G.IsBigMaximalClique t → ∃ x ∈ t, ∃ y ∈ t, F.Adj x y := by
  let F : SimpleGraph (Fin m) := {
    Adj := fun x y => G.Adj x y ∧ (c s(x, y) = true ∨ ¬ ∃ z, G.Adj x z ∧ G.Adj y z)
    symm := ⟨fun x y h => ⟨h.1.symm,
      h.2.elim (fun h => Or.inl ((congrArg c (Sym2.eq_swap (a := y) (b := x))).trans h))
        (fun h => Or.inr (fun ⟨z, hy, hx⟩ => h ⟨z, hx, hy⟩))⟩⟩
    loopless := ⟨fun _ h => G.irrefl h.1⟩ }
  refine ⟨F, ?_, ?_⟩
  · intro t ht
    have hcl : G.IsNClique 3 t := ⟨fun _ hx _ hy hne => (ht.1 hx hy hne).1, ht.2⟩
    obtain ⟨a, ha, hca⟩ := (hc t hcl).2
    induction a using Sym2.ind with
    | h x y =>
      have ⟨hxy, hne⟩ := mem_filter.mp ha
      have ⟨hx, hy⟩ := mk_mem_sym2_iff.mp hxy
      have hxyne : x ≠ y := fun heq => hne (Sym2.mk_isDiag_iff.mpr heq)
      have hzcard : (t.erase x |>.erase y).card = 1 := by
        rw [card_erase_of_mem (mem_erase.mpr ⟨hxyne.symm, hy⟩), card_erase_of_mem hx, ht.2]
      obtain ⟨z, hz⟩ := card_pos.mp (show 0 < (t.erase x |>.erase y).card by omega)
      obtain ⟨hzy, hzx, hzt⟩ := show z ≠ y ∧ z ≠ x ∧ z ∈ t by
        simpa only [mem_erase] using hz
      have hfxz : F.Adj x z := ht.1 hx hzt hzx.symm
      have hfyz : F.Adj y z := ht.1 hy hzt hzy.symm
      have hfxy : F.Adj x y := ht.1 hx hy hxyne
      exact Bool.false_ne_true (hca.symm.trans
        (hfxy.2.resolve_right (fun h => h ⟨z, hfxz.1, hfyz.1⟩)))
  · intro t ht
    by_cases hcard : 3 ≤ t.card
    · obtain ⟨u, hu, huc⟩ := exists_subset_card_eq hcard
      have hcl : G.IsNClique 3 u := ⟨fun _ hx _ hy hne => ht.1.1 (hu hx) (hu hy) hne, huc⟩
      obtain ⟨a, ha, hca⟩ := (hc u hcl).1
      induction a using Sym2.ind with
      | h x y =>
        have ⟨hxy, hne⟩ := mem_filter.mp ha
        have ⟨hx, hy⟩ := mk_mem_sym2_iff.mp hxy
        exact ⟨x, hu hx, y, hu hy,
          hcl.1 hx hy (fun heq => hne (Sym2.mk_isDiag_iff.mpr heq)), Or.inl hca⟩
    · have htwo : t.card = 2 := by have := ht.2; omega
      obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.mp htwo
      refine ⟨x, by simp, y, by simp, ht.1.1 (by simp) (by simp) hxy, Or.inr ?_⟩
      rintro ⟨z, hxz, hyz⟩
      have hcl : G.IsClique (↑(insert z ({x, y} : Finset (Fin m))) : Set (Fin m)) := by
        rw [coe_insert]
        apply ht.1.1.insert
        intro a ha _
        simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at ha
        rcases ha with rfl | rfl
        · exact hxz.symm
        · exact hyz.symm
      have hz := ht.1.2 hcl (subset_insert _ _) (mem_insert_self _ _)
      simp only [mem_insert, mem_singleton] at hz
      exact hz.elim hxz.ne.symm hyz.ne.symm

/-- When there are at least as many triangles as participating edges, a family
with at most three occurrences per edge has exactly three per edge. -/
private lemma regular_or_large_occurrence [DecidableEq α] (T : Finset ι) (E : ι → Finset α)
    (three : ∀ t ∈ T, (E t).card = 3) (dense : (T.biUnion E).card ≤ T.card) :
    (∀ e ∈ T.biUnion E, (T.filter (fun t => e ∈ E t)).card = 3) ∨
    (∃ e ∈ T.biUnion E, 4 ≤ (T.filter (fun t => e ∈ E t)).card) := by
  let U := T.biUnion E
  let degree (e : α) := (T.filter (fun t => e ∈ E t)).card
  change (∀ e ∈ U, degree e = 3) ∨ (∃ e ∈ U, 4 ≤ degree e)
  by_cases hlarge : ∃ e ∈ U, 4 ≤ degree e
  · exact Or.inr hlarge
  left
  have hle (e : α) (he : e ∈ U) : degree e ≤ 3 := by
    by_contra! h
    exact hlarge ⟨e, he, h⟩
  have total : T.card * 3 = ∑ e ∈ U, degree e := by
    calc
      T.card * 3 = ∑ t ∈ T, (E t).card := (sum_const_nat three).symm
      _ = ∑ t ∈ T, ∑ e ∈ U, if e ∈ E t then 1 else 0 := by
        apply sum_congr rfl
        intro t ht
        have heq : U.filter (fun e => e ∈ E t) = E t := by
          ext e
          exact mem_filter.trans ⟨And.right, fun h => ⟨mem_biUnion.mpr ⟨t, ht, h⟩, h⟩⟩
        rw [← sum_filter, heq]
        simp
      _ = ∑ e ∈ U, ∑ t ∈ T, if e ∈ E t then 1 else 0 := sum_comm
      _ = ∑ e ∈ U, degree e := by
        apply sum_congr rfl
        intro e _
        rw [← sum_filter]
        simp [degree]
  intro e he
  by_contra hne
  have hlt : ∑ a ∈ U, degree a < ∑ a ∈ U, (3 : ℕ) :=
    sum_lt_sum hle ⟨e, he, lt_of_le_of_ne (hle e he) hne⟩
  have hright : (∑ _ ∈ U, (3 : ℕ)) = U.card * 3 := sum_const_nat (fun _ _ => rfl)
  rw [← total, hright] at hlt
  change U.card ≤ T.card at dense
  omega

private lemma triangle_edge_count {m : ℕ} {G : SimpleGraph (Fin m)}
    {t : Finset (Fin m)} (ht : G.IsNClique 3 t) :
    (t.sym2.filter (fun e => ¬ e.IsDiag)).card = 3 := by
  have hd : t.sym2.filter Sym2.IsDiag = t.image (fun x => s(x, x)) := by
    ext e
    induction e using Sym2.ind with
    | h x y =>
      simp only [mem_filter, mk_mem_sym2_iff, Sym2.mk_isDiag_iff, mem_image, Sym2.eq_iff]
      constructor
      · rintro ⟨⟨hx, _⟩, rfl⟩
        exact ⟨x, hx, Or.inl ⟨rfl, rfl⟩⟩
      · rintro ⟨a, ha, h | h⟩
        · exact ⟨⟨h.1 ▸ ha, h.2 ▸ ha⟩, h.1.symm.trans h.2⟩
        · exact ⟨⟨h.2 ▸ ha, h.1 ▸ ha⟩, h.2.symm.trans h.1⟩
  have hinj : Function.Injective (fun x : Fin m => s(x, x)) :=
    fun _ _ h => (Sym2.eq_iff.mp h).elim And.left And.left
  have htotal : t.sym2.card = 6 := by
    rw [card_sym2, ht.2]
    decide
  have hparts := card_filter_add_card_filter_not (s := t.sym2) Sym2.IsDiag
  rw [hd, card_image_of_injective _ hinj, ht.2, htotal] at hparts
  omega

lemma dense_triangle_family (cube : H2) {m : ℕ} (G : SimpleGraph (Fin m))
    (four : G.CliqueFree 4)
    (hno : ¬ ∃ F : SimpleGraph (Fin m), F.CliqueFree 3 ∧
      ∀ t, G.IsBigMaximalClique t → ∃ x ∈ t, ∃ y ∈ t, F.Adj x y) :
    ∃ T : Finset (Finset (Fin m)), T.Nonempty ∧
      (∀ t ∈ T, G.IsNClique 3 t) ∧
      let E := fun t : Finset (Fin m) => t.sym2.filter (fun e => ¬ e.IsDiag)
      (∀ S ⊆ T.biUnion E, S.card ≤ (T.filter (fun t => ∃ e ∈ S, e ∈ E t)).card) ∧
      (∀ S ⊂ T.biUnion E, S.Nonempty →
        S.card < (T.filter (fun t => ∃ e ∈ S, e ∈ E t)).card) ∧
      (∃ e ∈ T.biUnion E, 4 ≤ (T.filter (fun t => e ∈ E t)).card) := by
  let E := fun t : Finset (Fin m) => t.sym2.filter (fun e => ¬ e.IsDiag)
  let triangles := (univ : Finset (Finset (Fin m))).filter (G.IsNClique 3)
  let good (T : Finset (Finset (Fin m))) := ∃ c : Sym2 (Fin m) → Bool,
    ∀ t ∈ T, (∃ e ∈ E t, c e = true) ∧ (∃ e ∈ E t, c e = false)
  have hbad : ¬ good triangles := by
    rintro ⟨c, hc⟩
    exact hno (hitting_of_bichromatic G c
      (fun t ht => hc t (mem_filter.mpr ⟨mem_univ _, ht⟩)))
  let bad := triangles.powerset.filter (fun T => ¬ good T)
  have hbadmem : triangles ∈ bad := mem_filter.mpr ⟨mem_powerset.mpr Subset.rfl, hbad⟩
  obtain ⟨T, hT, hmin⟩ := exists_min_image bad card ⟨triangles, hbadmem⟩
  have hsub := mem_powerset.mp (mem_filter.mp hT).1
  have hTbad := (mem_filter.mp hT).2
  have hgood (U : Finset (Finset (Fin m))) (hU : U ⊂ T) : good U := by
    by_contra hn
    exact (not_le_of_gt (card_lt_card hU))
      (hmin U (mem_filter.mpr ⟨mem_powerset.mpr (hU.subset.trans hsub), hn⟩))
  have hTtri t (ht : t ∈ T) := (mem_filter.mp (hsub ht)).2
  have hne : T.Nonempty := by
    by_contra h
    exact hTbad ⟨fun _ => false, by simp [not_nonempty_iff_eq_empty.mp h]⟩
  have hdense (S : Finset (Sym2 (Fin m))) (hS : S ⊆ T.biUnion E) :=
    (incidence_bounds T E hTbad hgood S hS).1
  have hstrict (S : Finset (Sym2 (Fin m))) (hS : S ⊂ T.biUnion E) :=
    (incidence_bounds T E hTbad hgood S hS.subset).2 hS
  have htotal : (T.biUnion E).card ≤ T.card :=
    (hdense _ Subset.rfl).trans (filter_subset _ _ |> card_le_card)
  have hthree : ∀ t ∈ T, (E t).card = 3 := fun t ht => triangle_edge_count (hTtri t ht)
  rcases regular_or_large_occurrence T E hthree htotal with hregular | hlarge
  · exact (hTbad (cube m G T four hTtri hregular)).elim
  · exact ⟨T, hne, hTtri, hdense, hstrict, hlarge⟩

theorem main : H1 → H2 → H3 → OMA.R_Erdos151_erdos_151_R2.H2 := by
  intro small cube large n G _ hjump hK4 hdeg hno hguard
  by_cases hsmall : Erdos151.H (n + 1) ≤ 9
  · exact small (n + 1) hsmall G hK4
  · exact large n G (by omega) hjump hK4 hdeg hno hguard (dense_triangle_family cube G hK4 hno)

end Proof
end OMA.R_Erdos151_erdos_151_R2_H2_R1
