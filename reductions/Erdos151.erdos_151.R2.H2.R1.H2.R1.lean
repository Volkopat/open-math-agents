import OMAReductions.R_Erdos151_erdos_151_R2_H2_R1
import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

-- Reduction Erdos151.erdos_151.R2.H2.R1.H2.R1 of step Erdos151.erdos_151.R2.H2.R1.H2
-- Credit: @theterabites
--
-- The step asks for a bichromatic edge colouring of a family T of triangles of a K4-free graph in
-- which every participating edge lies in exactly three triangles of T. Reading edges as points and
-- triangles as lines gives a 3-uniform hypergraph of maximum degree 3. This file proves, in Lean,
-- everything except the two published hypergraph facts below:
--   * a minimal non-2-colourable subfamily exists; Seymour's rank bound (proved here, adapted from
--     reduction Erdos151.erdos_151.R2.H2.R1 by @Alewawa) and double counting make it 3-regular;
--   * two distinct triangles share at most one edge, and three triangles pairwise meeting in three
--     distinct edges force a K4 (both proved here).
-- The hypotheses split the remaining theorem of Choi, Kwon and Park (arXiv:2609.33902) along its
-- proof: H1 is Theorem 3.5 (Seymour 1974, Vazirani-Yannakakis, Henning-Yeo), H2 is Lemma 5.5
-- (McCuaig; Funk-Jackson-Labbate-Sheehan): a connected det-extremal cubic bipartite graph has girth 6.

open Finset SimpleGraph
open scoped Classical

namespace OMA.R_Erdos151_erdos_151_R2_H2_R1_H2_R1

/-- Seymour (1974) with Vazirani-Yannakakis and Henning-Yeo, see Choi-Kwon-Park, arXiv:2609.33902,
Theorem 3.4, Proposition 3.3 and Theorem 3.5: the incidence matrix of a minimally non-2-colourable
3-uniform 3-regular hypergraph with distinct lines is det-extremal, i.e. its determinant has absolute
value equal to its permanent (for any matching of points with lines). -/
def H1 : Prop :=
  ∀ (α : Type) [DecidableEq α] (L : Finset (Finset α)),
    (∀ l ∈ L, l.card = 3) →
    (∀ x ∈ L.biUnion id, (L.filter (fun l => x ∈ l)).card = 3) →
    (¬ ∃ c : α → Bool, ∀ l ∈ L, (∃ x ∈ l, c x = true) ∧ (∃ x ∈ l, c x = false)) →
    (∀ L' ⊂ L, ∃ c : α → Bool, ∀ l ∈ L', (∃ x ∈ l, c x = true) ∧ (∃ x ∈ l, c x = false)) →
    ∀ e : (L : Type) ≃ ((L.biUnion id : Finset α) : Type),
      |(Matrix.of fun i j : (L : Type) => if ((e i : α)) ∈ (j : Finset α) then (1 : ℤ) else 0).det| =
        (Matrix.of fun i j : (L : Type) =>
          if ((e i : α)) ∈ (j : Finset α) then (1 : ℤ) else 0).permanent

/-- McCuaig's theorem via Choi-Kwon-Park, arXiv:2609.33902, Lemma 5.5 (a connected det-extremal
cubic bipartite graph has girth exactly 6), read in the incidence graph of a minimally
non-2-colourable (hence connected) 3-uniform 3-regular hypergraph: two lines share two points, or
three distinct lines meet pairwise in three distinct points. -/
def H2 : Prop :=
  ∀ (α : Type) [DecidableEq α] (L : Finset (Finset α)),
    (∀ l ∈ L, l.card = 3) →
    (∀ x ∈ L.biUnion id, (L.filter (fun l => x ∈ l)).card = 3) →
    (¬ ∃ c : α → Bool, ∀ l ∈ L, (∃ x ∈ l, c x = true) ∧ (∃ x ∈ l, c x = false)) →
    (∀ L' ⊂ L, ∃ c : α → Bool, ∀ l ∈ L', (∃ x ∈ l, c x = true) ∧ (∃ x ∈ l, c x = false)) →
    (∀ e : (L : Type) ≃ ((L.biUnion id : Finset α) : Type),
      |(Matrix.of fun i j : (L : Type) => if ((e i : α)) ∈ (j : Finset α) then (1 : ℤ) else 0).det| =
        (Matrix.of fun i j : (L : Type) =>
          if ((e i : α)) ∈ (j : Finset α) then (1 : ℤ) else 0).permanent) →
    (∃ a ∈ L, ∃ b ∈ L, a ≠ b ∧ 2 ≤ (a ∩ b).card) ∨
    (∃ a ∈ L, ∃ b ∈ L, ∃ c ∈ L, a ≠ b ∧ b ≠ c ∧ a ≠ c ∧
      ∃ p ∈ a ∩ b, ∃ q ∈ b ∩ c, ∃ r ∈ a ∩ c, p ≠ q ∧ q ≠ r ∧ p ≠ r)

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


private lemma mem_edges_iff {m : ℕ} (t : Finset (Fin m)) (x y : Fin m) :
    s(x, y) ∈ t.sym2.filter (fun e => ¬ e.IsDiag) ↔ x ∈ t ∧ y ∈ t ∧ x ≠ y := by
  simp only [mem_filter, mk_mem_sym2_iff, Sym2.mk_isDiag_iff, and_assoc]

private lemma inter_card_le_two {m : ℕ} {t₁ t₂ : Finset (Fin m)} (h₁ : t₁.card = 3)
    (h₂ : t₂.card = 3) (hne : t₁ ≠ t₂) : (t₁ ∩ t₂).card ≤ 2 := by
  by_contra h
  have e₁ : t₁ ∩ t₂ = t₁ := eq_of_subset_of_card_le inter_subset_left (by omega)
  have e₂ : t₁ ∩ t₂ = t₂ := eq_of_subset_of_card_le inter_subset_right (by omega)
  exact hne (e₁.symm.trans e₂)

/-- Two distinct triangles have at most one edge in common. -/
private lemma pair_unique {m : ℕ} {t₁ t₂ : Finset (Fin m)} (h₁ : t₁.card = 3)
    (h₂ : t₂.card = 3) (hne : t₁ ≠ t₂) {x y w z : Fin m} (hx : x ∈ t₁ ∩ t₂) (hy : y ∈ t₁ ∩ t₂)
    (hxy : x ≠ y) (hw : w ∈ t₁ ∩ t₂) (hz : z ∈ t₁ ∩ t₂) (hwz : w ≠ z) : s(w, z) = s(x, y) := by
  have hle := inter_card_le_two h₁ h₂ hne
  have key : ∀ u ∈ t₁ ∩ t₂, u = x ∨ u = y := by
    intro u hu
    by_contra hu'
    push Not at hu'
    have hsub : ({x, y, u} : Finset (Fin m)) ⊆ t₁ ∩ t₂ := by
      intro v hv
      simp only [mem_insert, mem_singleton] at hv
      rcases hv with rfl | rfl | rfl <;> assumption
    have hc : ({x, y, u} : Finset (Fin m)).card = 3 :=
      card_eq_three.mpr ⟨x, y, u, hxy, hu'.1.symm, hu'.2.symm, rfl⟩
    have := card_le_card hsub
    omega
  rcases key w hw with hw' | hw' <;> rcases key z hz with hz' | hz' <;> subst hw' <;> subst hz'
  · exact absurd rfl hwz
  · rfl
  · exact Sym2.eq_swap
  · exact absurd rfl hwz

private lemma not_two_common {m : ℕ} {G : SimpleGraph (Fin m)} {t₁ t₂ : Finset (Fin m)}
    (ht₁ : G.IsNClique 3 t₁) (ht₂ : G.IsNClique 3 t₂) (hne : t₁ ≠ t₂) :
    ((t₁.sym2.filter (fun e => ¬ e.IsDiag)) ∩ (t₂.sym2.filter (fun e => ¬ e.IsDiag))).card ≤ 1 := by
  rw [card_le_one]
  intro a ha b hb
  rw [mem_inter] at ha hb
  induction a using Sym2.ind with
  | h x y =>
    induction b using Sym2.ind with
    | h w z =>
      rw [mem_edges_iff, mem_edges_iff] at ha hb
      exact pair_unique ht₁.2 ht₂.2 hne (mem_inter.mpr ⟨hb.1.1, hb.2.1⟩)
        (mem_inter.mpr ⟨hb.1.2.1, hb.2.2.1⟩) hb.1.2.2 (mem_inter.mpr ⟨ha.1.1, ha.2.1⟩)
        (mem_inter.mpr ⟨ha.1.2.1, ha.2.2.1⟩) ha.1.2.2

/-- Three triangles meeting pairwise in three distinct edges force a K4. -/
private lemma no_berge_triangle {m : ℕ} {G : SimpleGraph (Fin m)} (hK4 : G.CliqueFree 4)
    {t₁ t₂ t₃ : Finset (Fin m)} (ht₁ : G.IsNClique 3 t₁) (ht₂ : G.IsNClique 3 t₂)
    (ht₃ : G.IsNClique 3 t₃) (h12 : t₁ ≠ t₂) {p q r : Sym2 (Fin m)}
    (hp₁ : p ∈ t₁.sym2.filter (fun e => ¬ e.IsDiag)) (hp₂ : p ∈ t₂.sym2.filter (fun e => ¬ e.IsDiag))
    (hq₂ : q ∈ t₂.sym2.filter (fun e => ¬ e.IsDiag)) (hq₃ : q ∈ t₃.sym2.filter (fun e => ¬ e.IsDiag))
    (hr₁ : r ∈ t₁.sym2.filter (fun e => ¬ e.IsDiag)) (hr₃ : r ∈ t₃.sym2.filter (fun e => ¬ e.IsDiag))
    (hpq : p ≠ q) (hpr : p ≠ r) : False := by
  induction p using Sym2.ind with
  | h x y =>
  induction q using Sym2.ind with
  | h u v =>
  induction r using Sym2.ind with
  | h w z =>
  rw [mem_edges_iff] at hp₁ hp₂ hq₂ hq₃ hr₁ hr₃
  have hx : x ∈ t₁ ∩ t₂ := mem_inter.mpr ⟨hp₁.1, hp₂.1⟩
  have hy : y ∈ t₁ ∩ t₂ := mem_inter.mpr ⟨hp₁.2.1, hp₂.2.1⟩
  have hA : ∃ a, a ∈ t₁ ∧ a ∉ t₂ ∧ a ∈ t₃ := by
    by_cases hw : w ∈ t₂
    · by_cases hz : z ∈ t₂
      · exact absurd (pair_unique ht₁.2 ht₂.2 h12 hx hy hp₁.2.2 (mem_inter.mpr ⟨hr₁.1, hw⟩)
          (mem_inter.mpr ⟨hr₁.2.1, hz⟩) hr₁.2.2).symm hpr
      · exact ⟨z, hr₁.2.1, hz, hr₃.2.1⟩
    · exact ⟨w, hr₁.1, hw, hr₃.1⟩
  have hB : ∃ b, b ∈ t₂ ∧ b ∉ t₁ ∧ b ∈ t₃ := by
    by_cases hu : u ∈ t₁
    · by_cases hv : v ∈ t₁
      · exact absurd (pair_unique ht₁.2 ht₂.2 h12 hx hy hp₁.2.2 (mem_inter.mpr ⟨hu, hq₂.1⟩)
          (mem_inter.mpr ⟨hv, hq₂.2.1⟩) hq₂.2.2).symm hpq
      · exact ⟨v, hq₂.2.1, hv, hq₃.2.1⟩
    · exact ⟨u, hq₂.1, hu, hq₃.1⟩
  obtain ⟨a, ha₁, ha₂, ha₃⟩ := hA
  obtain ⟨b, hb₂, hb₁, hb₃⟩ := hB
  have hab : a ≠ b := fun h => ha₂ (h ▸ hb₂)
  have hadj : G.Adj a b := ht₃.1 (mem_coe.mpr ha₃) (mem_coe.mpr hb₃) hab
  have hI : (t₁ ∩ t₂).card = 2 := by
    have hle := inter_card_le_two ht₁.2 ht₂.2 h12
    have hsub : ({x, y} : Finset (Fin m)) ⊆ t₁ ∩ t₂ := by
      intro v hv
      simp only [mem_insert, mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact hx
      · exact hy
    have := card_le_card hsub
    rw [card_pair hp₁.2.2] at this
    omega
  have hD : (t₁ \ t₂).card = 1 := by
    have := card_sdiff_add_card_inter t₁ t₂
    rw [ht₁.2, hI] at this
    omega
  have hD' : (t₂ \ t₁).card = 1 := by
    have := card_sdiff_add_card_inter t₂ t₁
    rw [ht₂.2, inter_comm, hI] at this
    omega
  have hcl : G.IsClique ((t₁ ∪ t₂ : Finset (Fin m)) : Set (Fin m)) := by
    intro i hi j hj hij
    rw [mem_coe, mem_union] at hi hj
    by_cases hi₂ : i ∈ t₂
    · by_cases hj₂ : j ∈ t₂
      · exact ht₂.1 (mem_coe.mpr hi₂) (mem_coe.mpr hj₂) hij
      · have hj₁ : j ∈ t₁ := hj.resolve_right hj₂
        by_cases hi₁ : i ∈ t₁
        · exact ht₁.1 (mem_coe.mpr hi₁) (mem_coe.mpr hj₁) hij
        · have hja : j = a := card_le_one.mp hD.le j (mem_sdiff.mpr ⟨hj₁, hj₂⟩) a
            (mem_sdiff.mpr ⟨ha₁, ha₂⟩)
          have hib : i = b := card_le_one.mp hD'.le i (mem_sdiff.mpr ⟨hi₂, hi₁⟩) b
            (mem_sdiff.mpr ⟨hb₂, hb₁⟩)
          rw [hja, hib]
          exact hadj.symm
    · have hi₁ : i ∈ t₁ := hi.resolve_right hi₂
      by_cases hj₁ : j ∈ t₁
      · exact ht₁.1 (mem_coe.mpr hi₁) (mem_coe.mpr hj₁) hij
      · have hj₂ : j ∈ t₂ := hj.resolve_left hj₁
        have hia : i = a := card_le_one.mp hD.le i (mem_sdiff.mpr ⟨hi₁, hi₂⟩) a
          (mem_sdiff.mpr ⟨ha₁, ha₂⟩)
        have hjb : j = b := card_le_one.mp hD'.le j (mem_sdiff.mpr ⟨hj₂, hj₁⟩) b
          (mem_sdiff.mpr ⟨hb₂, hb₁⟩)
        rw [hia, hjb]
        exact hadj
  have hcard : (t₁ ∪ t₂).card = 4 := by
    have := card_union_add_card_inter t₁ t₂
    rw [ht₁.2, ht₂.2, hI] at this
    omega
  exact hK4 (t₁ ∪ t₂) ⟨hcl, hcard⟩

private lemma core (h1 : H1) (h2 : H2) {m : ℕ} {G : SimpleGraph (Fin m)}
    {T : Finset (Finset (Fin m))} (hK4 : G.CliqueFree 4) (hT : ∀ t ∈ T, G.IsNClique 3 t)
    (hreg : ∀ e ∈ T.biUnion (fun t => t.sym2.filter (fun e => ¬ e.IsDiag)),
      (T.filter (fun t => e ∈ t.sym2.filter (fun e => ¬ e.IsDiag))).card = 3) :
    ∃ c : Sym2 (Fin m) → Bool, ∀ t ∈ T,
      (∃ e ∈ t.sym2.filter (fun e => ¬ e.IsDiag), c e = true) ∧
      (∃ e ∈ t.sym2.filter (fun e => ¬ e.IsDiag), c e = false) := by
  by_contra hbad
  set E : Finset (Fin m) → Finset (Sym2 (Fin m)) :=
    fun t => t.sym2.filter (fun e => ¬ e.IsDiag) with hE
  let L := T.image E
  let good (S : Finset (Finset (Sym2 (Fin m)))) : Prop := ∃ c : Sym2 (Fin m) → Bool,
    ∀ l ∈ S, (∃ x ∈ l, c x = true) ∧ (∃ x ∈ l, c x = false)
  have hLbad : ¬ good L := by
    rintro ⟨c, hc⟩
    exact hbad ⟨c, fun t ht => hc (E t) (mem_image_of_mem E ht)⟩
  let bad := L.powerset.filter (fun S => ¬ good S)
  have hLmem : L ∈ bad := mem_filter.mpr ⟨mem_powerset.mpr Subset.rfl, hLbad⟩
  obtain ⟨S, hS, hmin⟩ := exists_min_image bad card ⟨L, hLmem⟩
  have hSL : S ⊆ L := mem_powerset.mp (mem_filter.mp hS).1
  have hSbad : ¬ good S := (mem_filter.mp hS).2
  have hSgood : ∀ U ⊂ S, good U := by
    intro U hU
    by_contra hn
    exact (not_le_of_gt (card_lt_card hU))
      (hmin U (mem_filter.mpr ⟨mem_powerset.mpr (hU.subset.trans hSL), hn⟩))
  have hline : ∀ l ∈ S, ∃ t ∈ T, E t = l := fun l hl => mem_image.mp (hSL hl)
  have hthree : ∀ l ∈ S, l.card = 3 := by
    intro l hl
    obtain ⟨t, ht, rfl⟩ := hline l hl
    exact triangle_edge_count (hT t ht)
  have hdense : (S.biUnion id).card ≤ S.card :=
    (incidence_bounds S id hSbad hSgood (S.biUnion id) Subset.rfl).1.trans
      (card_le_card (filter_subset _ _))
  have hdeg : ∀ x ∈ S.biUnion id, (S.filter (fun l => x ∈ l)).card ≤ 3 := by
    intro x hx
    obtain ⟨l, hl, hxl⟩ := mem_biUnion.mp hx
    obtain ⟨t, ht, rfl⟩ := hline l hl
    have hxT : x ∈ T.biUnion E := mem_biUnion.mpr ⟨t, ht, hxl⟩
    calc (S.filter (fun l => x ∈ l)).card
        ≤ ((T.filter (fun t => x ∈ E t)).image E).card := by
          apply card_le_card
          intro l' hl'
          obtain ⟨hl'S, hxl'⟩ := mem_filter.mp hl'
          obtain ⟨t', ht', rfl⟩ := hline l' hl'S
          exact mem_image_of_mem E (mem_filter.mpr ⟨ht', hxl'⟩)
      _ ≤ (T.filter (fun t => x ∈ E t)).card := card_image_le
      _ = 3 := hreg x hxT
  have hregS : ∀ x ∈ S.biUnion id, (S.filter (fun l => x ∈ l)).card = 3 := by
    rcases regular_or_large_occurrence S id hthree hdense with h | ⟨x, hx, h4⟩
    · exact h
    · have h3 := hdeg x hx
      change 4 ≤ (S.filter (fun l => x ∈ l)).card at h4
      omega
  have hdet := h1 (Sym2 (Fin m)) S hthree hregS hSbad hSgood
  rcases h2 (Sym2 (Fin m)) S hthree hregS hSbad hSgood hdet with
    ⟨a, ha, b, hb, hab, h2c⟩ |
      ⟨a, ha, b, hb, c, hc, hab, _, _, p, hp, q, hq, r, hr, hpq, _, hpr⟩
  · obtain ⟨t₁, ht₁, rfl⟩ := hline a ha
    obtain ⟨t₂, ht₂, rfl⟩ := hline b hb
    have hne : t₁ ≠ t₂ := fun h => hab (by rw [h])
    have h1c := not_two_common (hT t₁ ht₁) (hT t₂ ht₂) hne
    change (E t₁ ∩ E t₂).card ≤ 1 at h1c
    omega
  · obtain ⟨t₁, ht₁, rfl⟩ := hline a ha
    obtain ⟨t₂, ht₂, rfl⟩ := hline b hb
    obtain ⟨t₃, ht₃, rfl⟩ := hline c hc
    have hne : t₁ ≠ t₂ := fun h => hab (by rw [h])
    rw [mem_inter] at hp hq hr
    exact no_berge_triangle hK4 (hT t₁ ht₁) (hT t₂ ht₂) (hT t₃ ht₃) hne hp.1 hp.2 hq.1 hq.2
      hr.1 hr.2 hpq hpr

theorem main : H1 → H2 → OMA.R_Erdos151_erdos_151_R2_H2_R1.H2 := by
  intro h1 h2 m G T hK4 hT edges hreg
  exact core h1 h2 hK4 hT hreg

end Proof
end OMA.R_Erdos151_erdos_151_R2_H2_R1_H2_R1
