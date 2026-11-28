import OMAReductions.R_WrittenOnTheWallII_GraphConjecture40_conjecture40_R1_H1_R2_H1_R1
import Mathlib

/-!
# Step `R1.H1.R2.H1.R1.H1` of Written on the Wall II - Conjecture 40

Proof of the hypothesis `H1` of the reduction `R1.H1.R2.H1.R1`: graphs having a maximum induced
forest `U` with at most three outside neighbours at every vertex and at most two bad vertices of
each colour. Set-system core: Theorem GL2 (HP, every element in at most two sets except two
elements in at most three sets ⟹ P1) and Theorem BL2 (block condition except at two elements,
cut-element induction). Graph part as in `R1.H1.R2.H1.R1`, with two exceptions per colour.
-/

namespace OMA.W40B0

open OMA.R_WrittenOnTheWallII_GraphConjecture40_conjecture40_R1_H1_R2 (lc_of_hp lemma_LT
  biUnion_union_eq biUnion_inter_sub theorem_RF1 lovasz_pairs theorem_GL theorem_CE hp_sub bridge)

section fam

variable {T B : Type} [Fintype T] [DecidableEq T] [DecidableEq B]

/-- Deletion of the element `z` from the set `s` of a family. -/
def dl (F : T → Finset B) (z : B) (s : T) : T → Finset B :=
  fun t => (F t).filter (fun w => ¬ (w = z ∧ t = s))

theorem mem_dl (F : T → Finset B) (z : B) (s t : T) (w : B) :
    w ∈ dl F z s t ↔ w ∈ F t ∧ ¬ (w = z ∧ t = s) := Finset.mem_filter

theorem dl_sub (F : T → Finset B) (z : B) (s t : T) : dl F z s t ⊆ F t :=
  Finset.filter_subset _ _

theorem biU_mono (F G : T → Finset B) (h : ∀ t, F t ⊆ G t) (X : Finset T) :
    X.biUnion F ⊆ X.biUnion G := by
  intro w hw
  obtain ⟨t, ht, hwt⟩ := Finset.mem_biUnion.mp hw
  exact Finset.mem_biUnion.mpr ⟨t, ht, h t hwt⟩

theorem biU_dl_sup (F : T → Finset B) (z : B) (s : T) (X : Finset T) :
    X.biUnion F ⊆ insert z (X.biUnion (dl F z s)) := by
  intro w hw
  by_cases hwz : w = z
  · rw [hwz]; exact Finset.mem_insert_self _ _
  · apply Finset.mem_insert_of_mem
    obtain ⟨t, ht, hwt⟩ := Finset.mem_biUnion.mp hw
    exact Finset.mem_biUnion.mpr ⟨t, ht, (mem_dl F z s t w).mpr ⟨hwt, fun e => hwz e.1⟩⟩

theorem biU_sup_v (A C : T → Finset B) (v : B) (hlost : ∀ t, A t ⊆ insert v (C t))
    (X : Finset T) : X.biUnion A ⊆ insert v (X.biUnion C) := by
  intro w hw
  obtain ⟨t, ht, hwt⟩ := Finset.mem_biUnion.mp hw
  rcases Finset.mem_insert.mp (hlost t hwt) with h | h
  · rw [h]; exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨t, ht, h⟩)

theorem mem_biU {F : T → Finset B} {X : Finset T} {t : T} {w : B} (ht : t ∈ X) (hw : w ∈ F t) :
    w ∈ X.biUnion F := Finset.mem_biUnion.mpr ⟨t, ht, hw⟩

/-- A failed single deletion: witness tight set. -/
theorem wit (F : T → Finset B)
    (hF : ∀ X : Finset T, X.Nonempty → X.card + 1 ≤ (X.biUnion F).card) (z : B) (s : T)
    (h : ¬ ∀ X : Finset T, X.Nonempty → X.card + 1 ≤ (X.biUnion (dl F z s)).card) :
    ∃ W : Finset T, s ∈ W ∧ (W.biUnion F).card ≤ W.card + 1 ∧ ∀ t ∈ W, z ∈ F t → t = s := by
  push Not at h
  obtain ⟨X, hX, hlt⟩ := h
  have h1 := hF X hX
  have h2 := Finset.card_le_card (biU_dl_sup F z s X)
  have h3 := Finset.card_insert_le z (X.biUnion (dl F z s))
  have hsub := biU_mono (dl F z s) F (dl_sub F z s) X
  have hex : ∃ w ∈ X.biUnion F, w ∉ X.biUnion (dl F z s) := by
    by_contra hno
    push Not at hno
    have := Finset.card_le_card (fun w hw => hno w hw)
    omega
  obtain ⟨w, hw, hwn⟩ := hex
  obtain ⟨t, ht, hwt⟩ := Finset.mem_biUnion.mp hw
  have hts : w = z ∧ t = s := by
    by_contra hc
    exact hwn (mem_biU ht ((mem_dl F z s t w).mpr ⟨hwt, hc⟩))
  refine ⟨X, hts.2 ▸ ht, by omega, ?_⟩
  intro t' ht' hzt'
  by_contra hne
  apply hwn
  rw [hts.1]
  exact mem_biU ht' ((mem_dl F z s t' z).mpr ⟨hzt', fun e => hne e.2⟩)

/-- A witness tight set makes the single deletion fail. -/
theorem not_lc_of_wit (F : T → Finset B) (z : B) (s : T) (hz : z ∈ F s) (W : Finset T)
    (hs : s ∈ W) (hW : (W.biUnion F).card ≤ W.card + 1) (hu : ∀ t ∈ W, z ∈ F t → t = s) :
    ¬ ∀ X : Finset T, X.Nonempty → X.card + 1 ≤ (X.biUnion (dl F z s)).card := by
  intro hL
  have h1 := hL W ⟨s, hs⟩
  have hsub : W.biUnion (dl F z s) ⊆ (W.biUnion F).erase z := by
    intro w hw
    obtain ⟨t, ht, hwt⟩ := Finset.mem_biUnion.mp hw
    rw [mem_dl] at hwt
    refine Finset.mem_erase.mpr ⟨?_, mem_biU ht hwt.1⟩
    rintro rfl
    exact hwt.2 ⟨rfl, hu t ht hwt.1⟩
  have h2 := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem (mem_biU hs hz)] at h2
  omega

/-- Submodularity of `|F(·)|`. -/
theorem submod (F : T → Finset B) (X Y : Finset T) :
    ((X ∪ Y).biUnion F).card + ((X ∩ Y).biUnion F).card ≤
      (X.biUnion F).card + (Y.biUnion F).card := by
  rw [biUnion_union_eq]
  have h1 := Finset.card_union_add_card_inter (X.biUnion F) (Y.biUnion F)
  have h2 := Finset.card_le_card (biUnion_inter_sub F X Y)
  omega

/-- Strict submodularity with a common element missing from the meet. -/
theorem SM (F : T → Finset B)
    (hF : ∀ X : Finset T, X.Nonempty → X.card + 1 ≤ (X.biUnion F).card) (X Y : Finset T)
    (hne : (X ∩ Y).Nonempty) (e : B) (hX : e ∈ X.biUnion F) (hY : e ∈ Y.biUnion F)
    (hn : e ∉ (X ∩ Y).biUnion F) : X.card + Y.card + 3 ≤ (X.biUnion F).card + (Y.biUnion F).card := by
  have h1 := hF (X ∪ Y) (hne.mono (Finset.inter_subset_left.trans Finset.subset_union_left))
  have h2 := hF (X ∩ Y) hne
  rw [biUnion_union_eq] at h1
  have h3 := Finset.card_union_add_card_inter (X.biUnion F) (Y.biUnion F)
  have hsub : (X ∩ Y).biUnion F ⊆ (X.biUnion F ∩ Y.biUnion F).erase e := by
    intro w hw
    refine Finset.mem_erase.mpr ⟨?_, biUnion_inter_sub F X Y hw⟩
    rintro rfl; exact hn hw
  have h4 := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem (Finset.mem_inter.mpr ⟨hX, hY⟩)] at h4
  have h5 := Finset.card_union_add_card_inter X Y
  have h6 : 0 < (X.biUnion F ∩ Y.biUnion F).card := Finset.card_pos.mpr ⟨e, Finset.mem_inter.mpr ⟨hX, hY⟩⟩
  omega

/-- Two disjoint tight sets sharing `e`: their neighbourhoods meet only in `e`. -/
theorem meet_only (F : T → Finset B)
    (hF : ∀ X : Finset T, X.Nonempty → X.card + 1 ≤ (X.biUnion F).card) (X Y : Finset T)
    (hd : Disjoint X Y) (hXn : X.Nonempty) (hX : (X.biUnion F).card ≤ X.card + 1)
    (hY : (Y.biUnion F).card ≤ Y.card + 1) (e : B) (heX : e ∈ X.biUnion F)
    (heY : e ∈ Y.biUnion F) (w : B) (hwX : w ∈ X.biUnion F) (hwY : w ∈ Y.biUnion F) : w = e := by
  by_contra hwe
  have h1 := hF (X ∪ Y) (hXn.mono Finset.subset_union_left)
  rw [biUnion_union_eq, Finset.card_union_of_disjoint hd] at h1
  have h3 := Finset.card_union_add_card_inter (X.biUnion F) (Y.biUnion F)
  have hsub : ({e, w} : Finset B) ⊆ X.biUnion F ∩ Y.biUnion F := by
    intro u hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl
    · exact Finset.mem_inter.mpr ⟨heX, heY⟩
    · exact Finset.mem_inter.mpr ⟨hwX, hwY⟩
  have h4 := Finset.card_le_card hsub
  rw [Finset.card_pair (Ne.symm hwe)] at h4
  omega

/-- Union bound with a common element. -/
theorem union_le (F : T → Finset B) (X Y : Finset T) (e : B) (heX : e ∈ X.biUnion F)
    (heY : e ∈ Y.biUnion F) : ((X ∪ Y).biUnion F).card + 1 ≤ (X.biUnion F).card + (Y.biUnion F).card := by
  rw [biUnion_union_eq]
  have h3 := Finset.card_union_add_card_inter (X.biUnion F) (Y.biUnion F)
  have h6 : 0 < (X.biUnion F ∩ Y.biUnion F).card := Finset.card_pos.mpr ⟨e, Finset.mem_inter.mpr ⟨heX, heY⟩⟩
  omega

/-- Packing bound from HP. -/
theorem PACK (A : T → Finset B)
    (h : ∀ hpS : Finset B, (Finset.univ.filter (fun hpt => (A hpt \ hpS).card ≤ 1)).card ≤ hpS.card)
    (Q : Finset T) (R : Finset B) (hR : R ⊆ Q.biUnion A) (hpk : ∀ t ∈ Q, (A t ∩ R).card ≤ 1) :
    Q.card + R.card ≤ (Q.biUnion A).card := by
  classical
  have hQ : Q ⊆ Finset.univ.filter (fun t => (A t \ (Q.biUnion A \ R)).card ≤ 1) := by
    intro t ht
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_trans (Finset.card_le_card ?_) (hpk t ht)⟩
    intro w hw
    rw [Finset.mem_sdiff, Finset.mem_sdiff, not_and, not_not] at hw
    exact Finset.mem_inter.mpr ⟨hw.1, hw.2 (mem_biU ht hw.1)⟩
  have h1 := Finset.card_le_card hQ
  have h2 := h (Q.biUnion A \ R)
  rw [Finset.card_sdiff_of_subset hR] at h2
  have := Finset.card_le_card hR
  omega

/-- Packing criterion: no set of `Q` contains two distinct elements of `R`. -/
theorem pack_of (A : T → Finset B) (Q : Finset T) (R : Finset B)
    (hp : ∀ t ∈ Q, ∀ p ∈ R, ∀ q ∈ R, p ∈ A t → q ∈ A t → p = q) :
    ∀ t ∈ Q, (A t ∩ R).card ≤ 1 := by
  intro t ht
  rw [Finset.card_le_one]
  intro p hp' q hq'
  rw [Finset.mem_inter] at hp' hq'
  exact hp t ht p hp'.2 q hq'.2 hp'.1 hq'.1

/-- RF2 (general `v`): under HP for `A`, if `C ⊆ A` has LC and `A(X) ⊆ C(X) + v`, and `x ≠ v`
lies in three sets of `C`, deleting `x` from one of them keeps LC. -/
theorem rf2 (A C : T → Finset B)
    (h : ∀ hpS : Finset B, (Finset.univ.filter (fun hpt => (A hpt \ hpS).card ≤ 1)).card ≤ hpS.card)
    (hC : ∀ X : Finset T, X.Nonempty → X.card + 1 ≤ (X.biUnion C).card)
    (hsub : ∀ t, C t ⊆ A t) (v : B) (hlost : ∀ t, A t ⊆ insert v (C t)) (x : B) (hxv : x ≠ v)
    (s1 s2 s3 : T) (h12 : s1 ≠ s2) (h13 : s1 ≠ s3) (h23 : s2 ≠ s3)
    (hx1 : x ∈ C s1) (hx2 : x ∈ C s2) (hx3 : x ∈ C s3) :
    ∃ s, (s = s1 ∨ s = s2 ∨ s = s3) ∧
      ∀ X : Finset T, X.Nonempty → X.card + 1 ≤ (X.biUnion (dl C x s)).card := by
  by_contra hcon
  push Not at hcon
  have hw : ∀ s, (s = s1 ∨ s = s2 ∨ s = s3) → ∃ W : Finset T, s ∈ W ∧
      (W.biUnion C).card ≤ W.card + 1 ∧ ∀ t ∈ W, x ∈ C t → t = s := by
    intro s hs
    apply wit C hC x s
    intro hL
    obtain ⟨X, hX, hlt⟩ := hcon s hs
    have := hL X hX
    omega
  obtain ⟨W1, a1, b1, c1⟩ := hw s1 (Or.inl rfl)
  obtain ⟨W2, a2, b2, c2⟩ := hw s2 (Or.inr (Or.inl rfl))
  obtain ⟨W3, a3, b3, c3⟩ := hw s3 (Or.inr (Or.inr rfl))
  have m1 : x ∈ W1.biUnion C := mem_biU a1 hx1
  have m2 : x ∈ W2.biUnion C := mem_biU a2 hx2
  have m3 : x ∈ W3.biUnion C := mem_biU a3 hx3
  -- pairwise disjoint
  have dsj : ∀ (Wi Wj : Finset T) (si sj : T), si ≠ sj → (Wi.biUnion C).card ≤ Wi.card + 1 →
      (Wj.biUnion C).card ≤ Wj.card + 1 → (∀ t ∈ Wi, x ∈ C t → t = si) →
      (∀ t ∈ Wj, x ∈ C t → t = sj) → x ∈ Wi.biUnion C → x ∈ Wj.biUnion C → Disjoint Wi Wj := by
    intro Wi Wj si sj hij bi bj ci cj mi mj
    rw [Finset.disjoint_iff_inter_eq_empty, ← Finset.not_nonempty_iff_eq_empty]
    intro hne
    have hn : x ∉ (Wi ∩ Wj).biUnion C := by
      intro hm
      obtain ⟨t, ht, hxt⟩ := Finset.mem_biUnion.mp hm
      rw [Finset.mem_inter] at ht
      exact hij ((ci t ht.1 hxt).symm.trans (cj t ht.2 hxt))
    have := SM C hC Wi Wj hne x mi mj hn
    omega
  have d12 := dsj W1 W2 s1 s2 h12 b1 b2 c1 c2 m1 m2
  have d13 := dsj W1 W3 s1 s3 h13 b1 b3 c1 c3 m1 m3
  have d23 := dsj W2 W3 s2 s3 h23 b2 b3 c2 c3 m2 m3
  have o12 := meet_only C hC W1 W2 d12 ⟨s1, a1⟩ b1 b2 x m1 m2
  have o13 := meet_only C hC W1 W3 d13 ⟨s1, a1⟩ b1 b3 x m1 m3
  have o23 := meet_only C hC W2 W3 d23 ⟨s2, a2⟩ b2 b3 x m2 m3
  set Q := W1 ∪ W2 ∪ W3 with hQ
  have hQc : Q.card = W1.card + W2.card + W3.card := by
    rw [hQ, Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨d13, d23⟩),
      Finset.card_union_of_disjoint d12]
  have hCQ : (Q.biUnion C).card ≤ Q.card + 1 := by
    have u1 := union_le C W1 W2 x m1 m2
    have u2 := union_le C (W1 ∪ W2) W3 x (by rw [biUnion_union_eq]; exact Finset.mem_union_left _ m1) m3
    rw [← hQ] at u2
    omega
  have hAQ : (Q.biUnion A).card ≤ (Q.biUnion C).card + 1 :=
    (Finset.card_le_card (biU_sup_v A C v hlost Q)).trans (Finset.card_insert_le _ _)
  have inQ1 : W1 ⊆ Q := Finset.subset_union_left.trans Finset.subset_union_left
  have inQ2 : W2 ⊆ Q := Finset.subset_union_right.trans Finset.subset_union_left
  have inQ3 : W3 ⊆ Q := Finset.subset_union_right
  have parts : ∀ t ∈ Q, t ∈ W1 ∨ t ∈ W2 ∨ t ∈ W3 := by
    intro t ht
    rw [hQ, Finset.mem_union, Finset.mem_union] at ht
    tauto
  -- an element of `C(W)` other than `x`
  have other : ∀ (W : Finset T) (s : T), s ∈ W → (W.biUnion C).card ≤ W.card + 1 →
      ∃ y ∈ W.biUnion C, y ≠ x := by
    intro W s hs _
    have := hC W ⟨s, hs⟩
    by_contra hno
    push Not at hno
    have hs1 : W.biUnion C ⊆ {x} := fun y hy => Finset.mem_singleton.mpr (hno y hy)
    have := Finset.card_le_card hs1
    rw [Finset.card_singleton] at this
    have := Finset.card_pos.mpr ⟨s, hs⟩
    omega
  have hCA : ∀ (W : Finset T), W.biUnion C ⊆ W.biUnion A := fun W => biU_mono C A hsub W
  -- the location of a non-`v` element of `A t` for `t ∈ Q`
  have loc : ∀ t ∈ Q, ∀ y, y ≠ v → y ∈ A t →
      (y ∈ W1.biUnion C ∧ t ∈ W1) ∨ (y ∈ W2.biUnion C ∧ t ∈ W2) ∨ (y ∈ W3.biUnion C ∧ t ∈ W3) := by
    intro t ht y hyv hyt
    have hyC : y ∈ C t := by
      rcases Finset.mem_insert.mp (hlost t hyt) with e | e
      · exact absurd e hyv
      · exact e
    rcases parts t ht with h1 | h1 | h1
    · exact Or.inl ⟨mem_biU h1 hyC, h1⟩
    · exact Or.inr (Or.inl ⟨mem_biU h1 hyC, h1⟩)
    · exact Or.inr (Or.inr ⟨mem_biU h1 hyC, h1⟩)
  have o21 : ∀ w, w ∈ W2.biUnion C → w ∈ W1.biUnion C → w = x := fun w a b => o12 w b a
  have o31 : ∀ w, w ∈ W3.biUnion C → w ∈ W1.biUnion C → w = x := fun w a b => o13 w b a
  have o32 : ∀ w, w ∈ W3.biUnion C → w ∈ W2.biUnion C → w = x := fun w a b => o23 w b a
  have vin : ∀ (W : Finset T) (s : T), s ∈ W → (W.biUnion C).card ≤ W.card + 1 →
      ¬ (∃ y ∈ W.biUnion C, y ≠ x ∧ y ≠ v) → v ∈ W.biUnion C := by
    intro W s hs hW hno
    obtain ⟨y, hy, hyx⟩ := other W s hs hW
    by_contra hvn
    exact hno ⟨y, hy, hyx, fun e => hvn (e ▸ hy)⟩
  by_cases P1 : ∃ y ∈ W1.biUnion C, y ≠ x ∧ y ≠ v <;>
    by_cases P2 : ∃ y ∈ W2.biUnion C, y ≠ x ∧ y ≠ v <;>
    by_cases P3 : ∃ y ∈ W3.biUnion C, y ≠ x ∧ y ≠ v
  · obtain ⟨y1, k1, n1, v1⟩ := P1
    obtain ⟨y2, k2, n2, v2⟩ := P2
    obtain ⟨y3, k3, n3, v3⟩ := P3
    have e12 : y1 ≠ y2 := fun e => n1 (o12 y1 k1 (e ▸ k2))
    have e13 : y1 ≠ y3 := fun e => n1 (o13 y1 k1 (e ▸ k3))
    have e23 : y2 ≠ y3 := fun e => n2 (o23 y2 k2 (e ▸ k3))
    have hR : ({y1, y2, y3} : Finset B) ⊆ Q.biUnion A := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl
      · exact Finset.biUnion_subset_biUnion_of_subset_left A inQ1 (hCA W1 k1)
      · exact Finset.biUnion_subset_biUnion_of_subset_left A inQ2 (hCA W2 k2)
      · exact Finset.biUnion_subset_biUnion_of_subset_left A inQ3 (hCA W3 k3)
    have hpk := pack_of A Q {y1, y2, y3} (by
      intro t ht p hp q hq hpt hqt
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq
      have lp := loc t ht p (by rcases hp with rfl | rfl | rfl <;> assumption) hpt
      have lq := loc t ht q (by rcases hq with rfl | rfl | rfl <;> assumption) hqt
      rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl <;>
        rcases lp with ⟨lp1, lp2⟩ | ⟨lp1, lp2⟩ | ⟨lp1, lp2⟩ <;>
        rcases lq with ⟨lq1, lq2⟩ | ⟨lq1, lq2⟩ | ⟨lq1, lq2⟩ <;>
        first
        | rfl
        | exact absurd (o12 _ k1 lp1) n1 | exact absurd (o13 _ k1 lp1) n1
        | exact absurd (o21 _ k2 lp1) n2 | exact absurd (o23 _ k2 lp1) n2
        | exact absurd (o31 _ k3 lp1) n3 | exact absurd (o32 _ k3 lp1) n3
        | exact absurd (o12 _ k1 lq1) n1 | exact absurd (o13 _ k1 lq1) n1
        | exact absurd (o21 _ k2 lq1) n2 | exact absurd (o23 _ k2 lq1) n2
        | exact absurd (o31 _ k3 lq1) n3 | exact absurd (o32 _ k3 lq1) n3
        | exact absurd (Finset.disjoint_left.mp d12 lp2 lq2) id
        | exact absurd (Finset.disjoint_left.mp d13 lp2 lq2) id
        | exact absurd (Finset.disjoint_left.mp d23 lp2 lq2) id
        | exact absurd (Finset.disjoint_left.mp d12 lq2 lp2) id
        | exact absurd (Finset.disjoint_left.mp d13 lq2 lp2) id
        | exact absurd (Finset.disjoint_left.mp d23 lq2 lp2) id)
    have hP := PACK A h Q {y1, y2, y3} hR hpk
    have h3 : ({y1, y2, y3} : Finset B).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_pair e23]
      simp [e12, e13]
    omega
  · obtain ⟨y1, k1, n1, v1⟩ := P1
    obtain ⟨y2, k2, n2, v2⟩ := P2
    have hv3 := vin W3 s3 a3 b3 P3
    have hvQ : v ∈ Q.biUnion C := Finset.biUnion_subset_biUnion_of_subset_left C inQ3 hv3
    have hAQ' : (Q.biUnion A).card ≤ (Q.biUnion C).card := by
      have := Finset.card_le_card (biU_sup_v A C v hlost Q)
      rw [Finset.insert_eq_of_mem hvQ] at this
      exact this
    have e12 : y1 ≠ y2 := fun e => n1 (o12 y1 k1 (e ▸ k2))
    have hR : ({y1, y2} : Finset B) ⊆ Q.biUnion A := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact Finset.biUnion_subset_biUnion_of_subset_left A inQ1 (hCA W1 k1)
      · exact Finset.biUnion_subset_biUnion_of_subset_left A inQ2 (hCA W2 k2)
    have hpk := pack_of A Q {y1, y2} (by
      intro t ht p hp q hq hpt hqt
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq
      have lp := loc t ht p (by rcases hp with rfl | rfl <;> assumption) hpt
      have lq := loc t ht q (by rcases hq with rfl | rfl <;> assumption) hqt
      rcases hp with rfl | rfl <;> rcases hq with rfl | rfl <;>
        rcases lp with ⟨lp1, lp2⟩ | ⟨lp1, lp2⟩ | ⟨lp1, lp2⟩ <;>
        rcases lq with ⟨lq1, lq2⟩ | ⟨lq1, lq2⟩ | ⟨lq1, lq2⟩ <;>
        first
        | rfl
        | exact absurd (o12 _ k1 lp1) n1 | exact absurd (o13 _ k1 lp1) n1
        | exact absurd (o21 _ k2 lp1) n2 | exact absurd (o23 _ k2 lp1) n2
        | exact absurd (o31 _ k3 lp1) n3 | exact absurd (o32 _ k3 lp1) n3
        | exact absurd (o12 _ k1 lq1) n1 | exact absurd (o13 _ k1 lq1) n1
        | exact absurd (o21 _ k2 lq1) n2 | exact absurd (o23 _ k2 lq1) n2
        | exact absurd (o31 _ k3 lq1) n3 | exact absurd (o32 _ k3 lq1) n3
        | exact absurd (Finset.disjoint_left.mp d12 lp2 lq2) id
        | exact absurd (Finset.disjoint_left.mp d13 lp2 lq2) id
        | exact absurd (Finset.disjoint_left.mp d23 lp2 lq2) id
        | exact absurd (Finset.disjoint_left.mp d12 lq2 lp2) id
        | exact absurd (Finset.disjoint_left.mp d13 lq2 lp2) id
        | exact absurd (Finset.disjoint_left.mp d23 lq2 lp2) id)
    have hP := PACK A h Q {y1, y2} hR hpk
    rw [Finset.card_pair e12] at hP
    omega
  · obtain ⟨y1, k1, n1, v1⟩ := P1
    obtain ⟨y3, k3, n3, v3⟩ := P3
    have hv2 := vin W2 s2 a2 b2 P2
    have hvQ : v ∈ Q.biUnion C := Finset.biUnion_subset_biUnion_of_subset_left C inQ2 hv2
    have hAQ' : (Q.biUnion A).card ≤ (Q.biUnion C).card := by
      have := Finset.card_le_card (biU_sup_v A C v hlost Q)
      rw [Finset.insert_eq_of_mem hvQ] at this
      exact this
    have e13 : y1 ≠ y3 := fun e => n1 (o13 y1 k1 (e ▸ k3))
    have hR : ({y1, y3} : Finset B) ⊆ Q.biUnion A := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact Finset.biUnion_subset_biUnion_of_subset_left A inQ1 (hCA W1 k1)
      · exact Finset.biUnion_subset_biUnion_of_subset_left A inQ3 (hCA W3 k3)
    have hpk := pack_of A Q {y1, y3} (by
      intro t ht p hp q hq hpt hqt
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq
      have lp := loc t ht p (by rcases hp with rfl | rfl <;> assumption) hpt
      have lq := loc t ht q (by rcases hq with rfl | rfl <;> assumption) hqt
      rcases hp with rfl | rfl <;> rcases hq with rfl | rfl <;>
        rcases lp with ⟨lp1, lp2⟩ | ⟨lp1, lp2⟩ | ⟨lp1, lp2⟩ <;>
        rcases lq with ⟨lq1, lq2⟩ | ⟨lq1, lq2⟩ | ⟨lq1, lq2⟩ <;>
        first
        | rfl
        | exact absurd (o12 _ k1 lp1) n1 | exact absurd (o13 _ k1 lp1) n1
        | exact absurd (o21 _ k2 lp1) n2 | exact absurd (o23 _ k2 lp1) n2
        | exact absurd (o31 _ k3 lp1) n3 | exact absurd (o32 _ k3 lp1) n3
        | exact absurd (o12 _ k1 lq1) n1 | exact absurd (o13 _ k1 lq1) n1
        | exact absurd (o21 _ k2 lq1) n2 | exact absurd (o23 _ k2 lq1) n2
        | exact absurd (o31 _ k3 lq1) n3 | exact absurd (o32 _ k3 lq1) n3
        | exact absurd (Finset.disjoint_left.mp d12 lp2 lq2) id
        | exact absurd (Finset.disjoint_left.mp d13 lp2 lq2) id
        | exact absurd (Finset.disjoint_left.mp d23 lp2 lq2) id
        | exact absurd (Finset.disjoint_left.mp d12 lq2 lp2) id
        | exact absurd (Finset.disjoint_left.mp d13 lq2 lp2) id
        | exact absurd (Finset.disjoint_left.mp d23 lq2 lp2) id)
    have hP := PACK A h Q {y1, y3} hR hpk
    rw [Finset.card_pair e13] at hP
    omega
  · exact absurd (o23 v (vin W2 s2 a2 b2 P2) (vin W3 s3 a3 b3 P3)).symm hxv
  · obtain ⟨y2, k2, n2, v2⟩ := P2
    obtain ⟨y3, k3, n3, v3⟩ := P3
    have hv1 := vin W1 s1 a1 b1 P1
    have hvQ : v ∈ Q.biUnion C := Finset.biUnion_subset_biUnion_of_subset_left C inQ1 hv1
    have hAQ' : (Q.biUnion A).card ≤ (Q.biUnion C).card := by
      have := Finset.card_le_card (biU_sup_v A C v hlost Q)
      rw [Finset.insert_eq_of_mem hvQ] at this
      exact this
    have e23 : y2 ≠ y3 := fun e => n2 (o23 y2 k2 (e ▸ k3))
    have hR : ({y2, y3} : Finset B) ⊆ Q.biUnion A := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact Finset.biUnion_subset_biUnion_of_subset_left A inQ2 (hCA W2 k2)
      · exact Finset.biUnion_subset_biUnion_of_subset_left A inQ3 (hCA W3 k3)
    have hpk := pack_of A Q {y2, y3} (by
      intro t ht p hp q hq hpt hqt
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq
      have lp := loc t ht p (by rcases hp with rfl | rfl <;> assumption) hpt
      have lq := loc t ht q (by rcases hq with rfl | rfl <;> assumption) hqt
      rcases hp with rfl | rfl <;> rcases hq with rfl | rfl <;>
        rcases lp with ⟨lp1, lp2⟩ | ⟨lp1, lp2⟩ | ⟨lp1, lp2⟩ <;>
        rcases lq with ⟨lq1, lq2⟩ | ⟨lq1, lq2⟩ | ⟨lq1, lq2⟩ <;>
        first
        | rfl
        | exact absurd (o12 _ k1 lp1) n1 | exact absurd (o13 _ k1 lp1) n1
        | exact absurd (o21 _ k2 lp1) n2 | exact absurd (o23 _ k2 lp1) n2
        | exact absurd (o31 _ k3 lp1) n3 | exact absurd (o32 _ k3 lp1) n3
        | exact absurd (o12 _ k1 lq1) n1 | exact absurd (o13 _ k1 lq1) n1
        | exact absurd (o21 _ k2 lq1) n2 | exact absurd (o23 _ k2 lq1) n2
        | exact absurd (o31 _ k3 lq1) n3 | exact absurd (o32 _ k3 lq1) n3
        | exact absurd (Finset.disjoint_left.mp d12 lp2 lq2) id
        | exact absurd (Finset.disjoint_left.mp d13 lp2 lq2) id
        | exact absurd (Finset.disjoint_left.mp d23 lp2 lq2) id
        | exact absurd (Finset.disjoint_left.mp d12 lq2 lp2) id
        | exact absurd (Finset.disjoint_left.mp d13 lq2 lp2) id
        | exact absurd (Finset.disjoint_left.mp d23 lq2 lp2) id)
    have hP := PACK A h Q {y2, y3} hR hpk
    rw [Finset.card_pair e23] at hP
    omega
  · exact absurd (o13 v (vin W1 s1 a1 b1 P1) (vin W3 s3 a3 b3 P3)).symm hxv
  · exact absurd (o12 v (vin W1 s1 a1 b1 P1) (vin W2 s2 a2 b2 P2)).symm hxv
  · exact absurd (o12 v (vin W1 s1 a1 b1 P1) (vin W2 s2 a2 b2 P2)).symm hxv


/-- Disjointness of two tight-ish sets sharing an element whose sets in them differ. -/
theorem disj_of (F : T → Finset B)
    (hF : ∀ X : Finset T, X.Nonempty → X.card + 1 ≤ (X.biUnion F).card) (X Y : Finset T) (e : B)
    (a b : T) (hab : a ≠ b) (heX : e ∈ X.biUnion F) (heY : e ∈ Y.biUnion F)
    (huX : ∀ t ∈ X, e ∈ F t → t = a) (huY : ∀ t ∈ Y, e ∈ F t → t = b)
    (hc : (X.biUnion F).card + (Y.biUnion F).card ≤ X.card + Y.card + 2) : Disjoint X Y := by
  rw [Finset.disjoint_iff_inter_eq_empty, ← Finset.not_nonempty_iff_eq_empty]
  intro hne
  have hn : e ∉ (X ∩ Y).biUnion F := by
    intro hm
    obtain ⟨t, ht, het⟩ := Finset.mem_biUnion.mp hm
    rw [Finset.mem_inter] at ht
    exact hab ((huX t ht.1 het).symm.trans (huY t ht.2 het))
  have := SM F hF X Y hne e heX heY hn
  omega

theorem dl_comm (C : T → Finset B) (x y : B) (s r : T) :
    dl (dl C x s) y r = dl (dl C y r) x s := by
  funext t
  ext w
  simp only [mem_dl]
  tauto

/-- A failed `y`-deletion after a good `x`-deletion, with `r` good for `y`: the witness loses both. -/
theorem lost_both (C : T → Finset B) (x y : B) (hxy : x ≠ y) (s r : T) (hyr : y ∈ C r)
    (hgr : ∀ X : Finset T, X.Nonempty → X.card + 1 ≤ (X.biUnion (dl C y r)).card)
    (W : Finset T) (hrW : r ∈ W) (hW : (W.biUnion (dl C x s)).card ≤ W.card + 1)
    (hu : ∀ t ∈ W, y ∈ dl C x s t → t = r) :
    s ∈ W ∧ (∀ t ∈ W, x ∈ C t → t = s) ∧ (∀ t ∈ W, y ∈ C t → t = r) ∧
      (W.biUnion C).card ≤ W.card + 2 := by
  have yu : ∀ t ∈ W, y ∈ C t → t = r :=
    fun t ht hyt => hu t ht ((mem_dl C x s t y).mpr ⟨hyt, fun e => hxy e.1.symm⟩)
  have hxs : s ∈ W ∧ ∀ t ∈ W, x ∈ C t → t = s := by
    by_contra hn
    have hsub : W.biUnion C ⊆ W.biUnion (dl C x s) := by
      intro w hw
      obtain ⟨t, ht, hwt⟩ := Finset.mem_biUnion.mp hw
      by_cases hc : w = x ∧ t = s
      · obtain ⟨rfl, rfl⟩ := hc
        have : ∃ t' ∈ W, w ∈ C t' ∧ t' ≠ t := by
          by_contra hno
          push Not at hno
          exact hn ⟨ht, fun t' ht' hx' => hno t' ht' hx'⟩
        obtain ⟨t', ht', hx', hne⟩ := this
        exact mem_biU ht' ((mem_dl C w t t' w).mpr ⟨hx', fun e => hne e.2⟩)
      · exact mem_biU ht ((mem_dl C x s t w).mpr ⟨hwt, hc⟩)
    exact not_lc_of_wit C y r hyr W hrW ((Finset.card_le_card hsub).trans hW) yu hgr
  refine ⟨hxs.1, hxs.2, yu, ?_⟩
  have := Finset.card_le_card (biU_dl_sup C x s W)
  have := Finset.card_insert_le x (W.biUnion (dl C x s))
  omega

/-- Claim A: a good `x`-set and two good `y`-sets; one of the two joint deletions keeps LC. -/
theorem claimA (C : T → Finset B)
    (x y : B) (hxy : x ≠ y) (s r r' : T) (hrr : r ≠ r') (hyr : y ∈ C r) (hyr' : y ∈ C r')
    (hgs : ∀ X : Finset T, X.Nonempty → X.card + 1 ≤ (X.biUnion (dl C x s)).card)
    (hgr : ∀ X : Finset T, X.Nonempty → X.card + 1 ≤ (X.biUnion (dl C y r)).card)
    (hgr' : ∀ X : Finset T, X.Nonempty → X.card + 1 ≤ (X.biUnion (dl C y r')).card) :
    (∀ X : Finset T, X.Nonempty → X.card + 1 ≤ (X.biUnion (dl (dl C x s) y r)).card) ∨
      (∀ X : Finset T, X.Nonempty → X.card + 1 ≤ (X.biUnion (dl (dl C x s) y r')).card) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  have n1 : ¬ ∀ X : Finset T, X.Nonempty → X.card + 1 ≤ (X.biUnion (dl (dl C x s) y r)).card := by
    push Not; exact h1
  have n2 : ¬ ∀ X : Finset T, X.Nonempty → X.card + 1 ≤ (X.biUnion (dl (dl C x s) y r')).card := by
    push Not; exact h2
  obtain ⟨W, a1, b1, c1⟩ := wit (dl C x s) hgs y r n1
  obtain ⟨W', a2, b2, c2⟩ := wit (dl C x s) hgs y r' n2
  obtain ⟨s1, -, -, -⟩ := lost_both C x y hxy s r hyr hgr W a1 b1 c1
  obtain ⟨s2, -, -, -⟩ := lost_both C x y hxy s r' hyr' hgr' W' a2 b2 c2
  have hy1 : y ∈ dl C x s r := (mem_dl C x s r y).mpr ⟨hyr, fun e => hxy e.1.symm⟩
  have hy2 : y ∈ dl C x s r' := (mem_dl C x s r' y).mpr ⟨hyr', fun e => hxy e.1.symm⟩
  have hd := disj_of (dl C x s) hgs W W' y r r' hrr (mem_biU a1 hy1) (mem_biU a2 hy2) c1 c2 (by omega)
  exact Finset.disjoint_left.mp hd s1 s2


/-- Core of the unique case of GL2 (after normalisation): `X2`, `Y2` dirty, `a ∈ C(X3) - {x,y}`. -/
theorem uniq_core (A C : T → Finset B)
    (h : ∀ hpS : Finset B, (Finset.univ.filter (fun hpt => (A hpt \ hpS).card ≤ 1)).card ≤ hpS.card)
    (hC : ∀ X : Finset T, X.Nonempty → X.card + 1 ≤ (X.biUnion C).card)
    (hsub : ∀ t, C t ⊆ A t) (v : B) (hlost : ∀ t, A t ⊆ insert v (C t)) (sv : T)
    (hvs : ∀ t, v ∈ A t → v ∉ C t → t = sv) (x y : B) (hxy : x ≠ y)
    (s1 s2 r1 r2 : T) (hx1 : x ∈ C s1) (hx2 : x ∈ C s2) (hy1 : y ∈ C r1) (hy2 : y ∈ C r2)
    (Z X2 X3 Y2 Y3 : Finset T) (zs : s1 ∈ Z) (zr : r1 ∈ Z)
    (zc : (Z.biUnion C).card ≤ Z.card + 2) (zlow : Z.card + 2 ≤ (Z.biUnion C).card)
    (x2s : s2 ∈ X2) (x2c : (X2.biUnion C).card ≤ X2.card + 1) (x3c : (X3.biUnion C).card ≤ X3.card + 1)
    (y2r : r2 ∈ Y2) (y2c : (Y2.biUnion C).card ≤ Y2.card + 1) (y3c : (Y3.biUnion C).card ≤ Y3.card + 1)
    (hxX3 : x ∈ X3.biUnion C) (hyY3 : y ∈ Y3.biUnion C)
    (dX : Disjoint X2 X3) (oX : ∀ w ∈ X2.biUnion C, w ∈ X3.biUnion C → w = x)
    (dY : Disjoint Y2 Y3)
    (dZX2 : Disjoint Z X2) (dZX3 : Disjoint Z X3) (dZY2 : Disjoint Z Y2) (dZY3 : Disjoint Z Y3)
    (dirX : v ∈ X2.biUnion A ∧ v ∉ X2.biUnion C) (dirY : v ∈ Y2.biUnion A ∧ v ∉ Y2.biUnion C)
    (a : B) (haX : a ∈ X3.biUnion C) (hax : a ≠ x) (hay : a ≠ y) : False := by
  -- the dirty sets contain `sv`
  have sv_of : ∀ X : Finset T, v ∈ X.biUnion A → v ∉ X.biUnion C → sv ∈ X := by
    intro X hA hCn
    obtain ⟨t, ht, hvt⟩ := Finset.mem_biUnion.mp hA
    have := hvs t hvt (fun hc => hCn (mem_biU ht hc))
    exact this ▸ ht
  have svX := sv_of X2 dirX.1 dirX.2
  have svY := sv_of Y2 dirY.1 dirY.2
  have hPc : ((X2 ∪ X3).biUnion C).card ≤ (X2 ∪ X3).card + 1 := by
    have := union_le C X2 X3 x (mem_biU x2s hx2) hxX3
    rw [Finset.card_union_of_disjoint dX]
    omega
  have hRc : ((Y2 ∪ Y3).biUnion C).card ≤ (Y2 ∪ Y3).card + 1 := by
    have := union_le C Y2 Y3 y (mem_biU y2r hy2) hyY3
    rw [Finset.card_union_of_disjoint dY]
    omega
  set P := X2 ∪ X3 with hP
  set R := Y2 ∪ Y3 with hR
  set N := P ∪ R with hN
  have hPR : (P ∩ R).Nonempty :=
    ⟨sv, Finset.mem_inter.mpr ⟨Finset.mem_union_left _ svX, Finset.mem_union_left _ svY⟩⟩
  have hNc : (N.biUnion C).card ≤ N.card + 1 := by
    have h1 := submod C P R
    have h2 := hC (P ∩ R) hPR
    have h3 := Finset.card_union_add_card_inter P R
    rw [← hN] at h1 h3
    omega
  have dZN : Disjoint Z N := by
    rw [hN, hP, hR]
    exact Finset.disjoint_union_right.mpr ⟨Finset.disjoint_union_right.mpr ⟨dZX2, dZX3⟩,
      Finset.disjoint_union_right.mpr ⟨dZY2, dZY3⟩⟩
  have X2N : X2 ⊆ N := Finset.subset_union_left.trans Finset.subset_union_left
  have X3N : X3 ⊆ N := Finset.subset_union_right.trans Finset.subset_union_left
  have Y2N : Y2 ⊆ N := Finset.subset_union_left.trans Finset.subset_union_right
  have xZ : x ∈ Z.biUnion C := mem_biU zs hx1
  have yZ : y ∈ Z.biUnion C := mem_biU zr hy1
  have xN : x ∈ N.biUnion C := mem_biU (X2N x2s) hx2
  have yN : y ∈ N.biUnion C := mem_biU (Y2N y2r) hy2
  set Q := Z ∪ N with hQ
  have hQc : Q.card = Z.card + N.card := by rw [hQ, Finset.card_union_of_disjoint dZN]
  have hZne : Z.Nonempty := ⟨s1, zs⟩
  have hLQ := hC Q (hZne.mono Finset.subset_union_left)
  have hCQ : Q.biUnion C = Z.biUnion C ∪ N.biUnion C := by rw [hQ, biUnion_union_eq]
  have hi := Finset.card_union_add_card_inter (Z.biUnion C) (N.biUnion C)
  have hxy2 : ({x, y} : Finset B) ⊆ Z.biUnion C ∩ N.biUnion C := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact Finset.mem_inter.mpr ⟨xZ, xN⟩
    · exact Finset.mem_inter.mpr ⟨yZ, yN⟩
  have hc2 := Finset.card_le_card hxy2
  rw [Finset.card_pair hxy] at hc2
  have ZN : ∀ w ∈ Z.biUnion C, w ∈ N.biUnion C → w = x ∨ w = y := by
    intro w hwZ hwN
    by_contra hw
    push Not at hw
    have hs3 : ({w, x, y} : Finset B) ⊆ Z.biUnion C ∩ N.biUnion C := by
      intro u hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl | rfl
      · exact Finset.mem_inter.mpr ⟨hwZ, hwN⟩
      · exact Finset.mem_inter.mpr ⟨xZ, xN⟩
      · exact Finset.mem_inter.mpr ⟨yZ, yN⟩
    have h3 := Finset.card_le_card hs3
    rw [Finset.card_insert_of_notMem (by simp [hw.1, hw.2]), Finset.card_pair hxy] at h3
    rw [hCQ] at hLQ
    omega
  have hCQc : (Q.biUnion C).card ≤ Q.card + 1 := by rw [hCQ]; omega
  have hAQ : (Q.biUnion A).card ≤ (Q.biUnion C).card + 1 :=
    (Finset.card_le_card (biU_sup_v A C v hlost Q)).trans (Finset.card_insert_le _ _)
  -- the element `a`
  have aN : a ∈ N.biUnion C := Finset.biUnion_subset_biUnion_of_subset_left C X3N haX
  have aZ : a ∉ Z.biUnion C := fun hm => by
    rcases ZN a hm aN with e | e
    · exact hax e
    · exact hay e
  have aX2 : a ∉ X2.biUnion C := fun hm => hax (oX a hm haX)
  -- the element `z`
  obtain ⟨z, hzZ, hzx, hzy⟩ : ∃ z ∈ Z.biUnion C, z ≠ x ∧ z ≠ y := by
    by_contra hno
    push Not at hno
    have hs : Z.biUnion C ⊆ {x, y} := by
      intro w hw
      by_cases hwx : w = x
      · rw [hwx]; exact Finset.mem_insert_self _ _
      · rw [hno w hw hwx]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have := Finset.card_le_card hs
    have := Finset.card_le_two (a := x) (b := y)
    have := hZne.card_pos
    omega
  have zN : z ∉ N.biUnion C := fun hm => by
    rcases ZN z hzZ hm with e | e
    · exact hzx e
    · exact hzy e
  have hza : z ≠ a := fun e => aZ (e ▸ hzZ)
  -- localisation of `z` and `a` in the sets of `Q`
  have tZN : ∀ t ∈ Q, t ∈ Z ∨ t ∈ N := fun t ht => Finset.mem_union.mp (hQ ▸ ht)
  have zloc : ∀ t ∈ Q, z ∈ C t → t ∈ Z := by
    intro t ht hzt
    rcases tZN t ht with h1 | h1
    · exact h1
    · exact absurd (mem_biU h1 hzt) zN
  have aloc : ∀ t ∈ Q, a ∈ C t → t ∈ N := by
    intro t ht hat
    rcases tZN t ht with h1 | h1
    · exact absurd (mem_biU h1 hat) aZ
    · exact h1
  have vloc : ∀ t ∈ Q, v ∈ A t → v ∈ C t ∨ t = sv := by
    intro t _ hvt
    by_cases hc : v ∈ C t
    · exact Or.inl hc
    · exact Or.inr (hvs t hvt hc)
  have svN : sv ∈ N := X2N svX
  have svZ : sv ∉ Z := fun hm => Finset.disjoint_left.mp dZN hm svN
  have aC_sv : a ∉ C sv := fun hm => aX2 (mem_biU svX hm)
  -- no set of `Q` contains both `z` and `a`
  have za : ∀ t ∈ Q, z ∈ A t → a ∈ A t → False := by
    intro t ht hzt hat
    rcases Finset.mem_insert.mp (hlost t hzt) with ez | hzC <;>
      rcases Finset.mem_insert.mp (hlost t hat) with ea | haC
    · exact hza (ez.trans ea.symm)
    · -- z = v
      have htN := aloc t ht haC
      rcases vloc t ht (ez ▸ hzt) with hvC | hsv
      · rcases ZN v (ez ▸ hzZ) (mem_biU htN hvC) with e | e
        · exact hzx (ez.trans e)
        · exact hzy (ez.trans e)
      · exact aC_sv (hsv ▸ haC)
    · -- a = v
      have htZ := zloc t ht hzC
      rcases vloc t ht (ea ▸ hat) with hvC | hsv
      · rcases ZN v (mem_biU htZ hvC) (ea ▸ aN) with e | e
        · exact hax (ea.trans e)
        · exact hay (ea.trans e)
      · exact svZ (hsv ▸ htZ)
    · exact Finset.disjoint_left.mp dZN (zloc t ht hzC) (aloc t ht haC)
  have zQ : z ∈ Q.biUnion A :=
    Finset.biUnion_subset_biUnion_of_subset_left A Finset.subset_union_left (biU_mono C A hsub Z hzZ)
  have aQ : a ∈ Q.biUnion A :=
    Finset.biUnion_subset_biUnion_of_subset_left A Finset.subset_union_right (biU_mono C A hsub N aN)
  by_cases hvQ : v ∈ Q.biUnion C
  · have hAQ' : (Q.biUnion A).card ≤ (Q.biUnion C).card := by
      have := Finset.card_le_card (biU_sup_v A C v hlost Q)
      rwa [Finset.insert_eq_of_mem hvQ] at this
    have hpk := pack_of A Q {z, a} (by
      intro t ht p hp q hq hpt hqt
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq
      rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
      · rfl
      · exact (za t ht hpt hqt).elim
      · exact (za t ht hqt hpt).elim
      · rfl)
    have hR2 : ({z, a} : Finset B) ⊆ Q.biUnion A := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact zQ
      · exact aQ
    have hPk := PACK A h Q {z, a} hR2 hpk
    rw [Finset.card_pair hza] at hPk
    omega
  · have hzv : z ≠ v := fun e => hvQ (e ▸ (hCQ ▸ Finset.mem_union_left _ hzZ))
    have hav : a ≠ v := fun e => hvQ (e ▸ (hCQ ▸ Finset.mem_union_right _ aN))
    have vQ : v ∈ Q.biUnion A :=
      Finset.biUnion_subset_biUnion_of_subset_left A (X2N.trans Finset.subset_union_right) dirX.1
    have vsv : ∀ t ∈ Q, v ∈ A t → t = sv := by
      intro t ht hvt
      rcases vloc t ht hvt with hvC | hsv
      · exact absurd (mem_biU ht hvC) hvQ
      · exact hsv
    have hpk := pack_of A Q {z, a, v} (by
      intro t ht p hp q hq hpt hqt
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq
      have zv : z ∈ A t → v ∈ A t → False := by
        intro hzt hvt
        have e := vsv t ht hvt
        rcases Finset.mem_insert.mp (hlost t hzt) with ez | hzC
        · exact hzv ez
        · exact svZ (e ▸ zloc t ht hzC)
      have av : a ∈ A t → v ∈ A t → False := by
        intro hat hvt
        have e := vsv t ht hvt
        rcases Finset.mem_insert.mp (hlost t hat) with ea | haC
        · exact hav ea
        · exact aC_sv (e ▸ haC)
      rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl <;>
        first
        | rfl
        | exact (za t ht hpt hqt).elim | exact (za t ht hqt hpt).elim
        | exact (zv hpt hqt).elim | exact (zv hqt hpt).elim
        | exact (av hpt hqt).elim | exact (av hqt hpt).elim)
    have hR3 : ({z, a, v} : Finset B) ⊆ Q.biUnion A := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl
      · exact zQ
      · exact aQ
      · exact vQ
    have hPk := PACK A h Q {z, a, v} hR3 hpk
    rw [Finset.card_insert_of_notMem (by simp [hza, hzv]), Finset.card_pair hav] at hPk
    omega


/-- Unique case after normalisation (`X2`, `Y2` dirty). -/
theorem uniq_mid (A C : T → Finset B)
    (h : ∀ hpS : Finset B, (Finset.univ.filter (fun hpt => (A hpt \ hpS).card ≤ 1)).card ≤ hpS.card)
    (hC : ∀ X : Finset T, X.Nonempty → X.card + 1 ≤ (X.biUnion C).card)
    (hsub : ∀ t, C t ⊆ A t) (v : B) (hlost : ∀ t, A t ⊆ insert v (C t)) (sv : T)
    (hvs : ∀ t, v ∈ A t → v ∉ C t → t = sv) (x y : B) (hxy : x ≠ y)
    (s1 s2 s3 r1 r2 r3 : T) (hx1 : x ∈ C s1) (hx2 : x ∈ C s2) (hx3 : x ∈ C s3)
    (hy1 : y ∈ C r1) (hy2 : y ∈ C r2) (hy3 : y ∈ C r3)
    (Z X2 X3 Y2 Y3 : Finset T) (zs : s1 ∈ Z) (zr : r1 ∈ Z)
    (zc : (Z.biUnion C).card ≤ Z.card + 2) (zlow : Z.card + 2 ≤ (Z.biUnion C).card)
    (x2s : s2 ∈ X2) (x3s : s3 ∈ X3) (x2c : (X2.biUnion C).card ≤ X2.card + 1)
    (x3c : (X3.biUnion C).card ≤ X3.card + 1)
    (y2r : r2 ∈ Y2) (y3r : r3 ∈ Y3) (y2c : (Y2.biUnion C).card ≤ Y2.card + 1)
    (y3c : (Y3.biUnion C).card ≤ Y3.card + 1)
    (dX : Disjoint X2 X3) (oX : ∀ w ∈ X2.biUnion C, w ∈ X3.biUnion C → w = x)
    (dY : Disjoint Y2 Y3) (oY : ∀ w ∈ Y2.biUnion C, w ∈ Y3.biUnion C → w = y)
    (dZX2 : Disjoint Z X2) (dZX3 : Disjoint Z X3) (dZY2 : Disjoint Z Y2) (dZY3 : Disjoint Z Y3)
    (dirX : v ∈ X2.biUnion A ∧ v ∉ X2.biUnion C) (dirY : v ∈ Y2.biUnion A ∧ v ∉ Y2.biUnion C) :
    False := by
  by_cases ha : ∃ a ∈ X3.biUnion C, a ≠ x ∧ a ≠ y
  · obtain ⟨a, haX, hax, hay⟩ := ha
    exact uniq_core A C h hC hsub v hlost sv hvs x y hxy s1 s2 r1 r2 hx1 hx2 hy1 hy2 Z X2 X3 Y2 Y3
      zs zr zc zlow x2s x2c x3c y2r y2c y3c (mem_biU x3s hx3) (mem_biU y3r hy3) dX oX dY
      dZX2 dZX3 dZY2 dZY3 dirX dirY a haX hax hay
  by_cases hb : ∃ a ∈ Y3.biUnion C, a ≠ y ∧ a ≠ x
  · obtain ⟨a, haY, hay, hax⟩ := hb
    exact uniq_core A C h hC hsub v hlost sv hvs y x hxy.symm r1 r2 s1 s2 hy1 hy2 hx1 hx2 Z Y2 Y3 X2 X3
      zr zs zc zlow y2r y2c y3c x2s x2c x3c (mem_biU y3r hy3) (mem_biU x3s hx3) dY oY dX
      dZY2 dZY3 dZX2 dZX3 dirY dirX a haY hay hax
  -- degenerate case
  push Not at ha hb
  have sv_of : ∀ X : Finset T, v ∈ X.biUnion A → v ∉ X.biUnion C → sv ∈ X := by
    intro X hA hCn
    obtain ⟨t, ht, hvt⟩ := Finset.mem_biUnion.mp hA
    have := hvs t hvt (fun hc => hCn (mem_biU ht hc))
    exact this ▸ ht
  have svX := sv_of X2 dirX.1 dirX.2
  have svY := sv_of Y2 dirY.1 dirY.2
  have hMc : ((X2 ∪ Y2).biUnion C).card ≤ (X2 ∪ Y2).card + 1 := by
    have h1 := submod C X2 Y2
    have h2 := hC (X2 ∩ Y2) ⟨sv, Finset.mem_inter.mpr ⟨svX, svY⟩⟩
    have h3 := Finset.card_union_add_card_inter X2 Y2
    omega
  have hsubM : ((X2 ∪ Y2) ∪ X3).biUnion C ⊆ (X2 ∪ Y2).biUnion C := by
    intro w hw
    rw [biUnion_union_eq, Finset.mem_union] at hw
    rcases hw with hw | hw
    · exact hw
    · by_cases hwx : w = x
      · rw [hwx, biUnion_union_eq]; exact Finset.mem_union_left _ (mem_biU x2s hx2)
      · rw [ha w hw hwx, biUnion_union_eq]; exact Finset.mem_union_right _ (mem_biU y2r hy2)
  have hs3M : s3 ∈ X2 ∪ Y2 := by
    by_contra hn
    have hss : insert s3 (X2 ∪ Y2) ⊆ (X2 ∪ Y2) ∪ X3 := by
      intro t ht
      rcases Finset.mem_insert.mp ht with rfl | ht
      · exact Finset.mem_union_right _ x3s
      · exact Finset.mem_union_left _ ht
    have h1 := Finset.card_le_card hss
    rw [Finset.card_insert_of_notMem hn] at h1
    have h2 := hC ((X2 ∪ Y2) ∪ X3) ⟨s3, Finset.mem_union_right _ x3s⟩
    have h3 := Finset.card_le_card hsubM
    omega
  have hs3Y : s3 ∈ Y2 := by
    rcases Finset.mem_union.mp hs3M with h1 | h1
    · exact absurd x3s (Finset.disjoint_left.mp dX h1)
    · exact h1
  have hxY3 : x ∈ Y3.biUnion C := by
    by_contra hn
    have hs : Y3.biUnion C ⊆ {y} := by
      intro w hw
      rcases eq_or_ne w y with e | e
      · exact Finset.mem_singleton.mpr e
      · exact absurd ((hb w hw e) ▸ hw) hn
    have h1 := Finset.card_le_card hs
    have h2 := hC Y3 ⟨r3, y3r⟩
    have h3 := Finset.card_pos.mpr ⟨r3, y3r⟩
    rw [Finset.card_singleton] at h1
    omega
  exact hxy (oY x (mem_biU hs3Y hx3) hxY3)

/-- Deleting an element from its unique set inside `Z` lowers `|C(Z)|`. -/
theorem lost_card (C : T → Finset B) (e : B) (a : T) (Z : Finset T) (ha : a ∈ Z) (he : e ∈ C a)
    (hu : ∀ t ∈ Z, e ∈ C t → t = a) :
    (Z.biUnion (dl C e a)).card + 1 ≤ (Z.biUnion C).card := by
  have hsub : Z.biUnion (dl C e a) ⊆ (Z.biUnion C).erase e := by
    intro w hw
    obtain ⟨t, ht, hwt⟩ := Finset.mem_biUnion.mp hw
    rw [mem_dl] at hwt
    refine Finset.mem_erase.mpr ⟨?_, mem_biU ht hwt.1⟩
    rintro rfl
    exact hwt.2 ⟨rfl, hu t ht hwt.1⟩
  have := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem (mem_biU ha he)] at this
  have := Finset.card_pos.mpr ⟨e, mem_biU ha he⟩
  omega

/-- The unique case of GL2 is contradictory. -/
theorem uniq (A C : T → Finset B)
    (h : ∀ hpS : Finset B, (Finset.univ.filter (fun hpt => (A hpt \ hpS).card ≤ 1)).card ≤ hpS.card)
    (hC : ∀ X : Finset T, X.Nonempty → X.card + 1 ≤ (X.biUnion C).card)
    (hsub : ∀ t, C t ⊆ A t) (v : B) (hlost : ∀ t, A t ⊆ insert v (C t)) (sv : T)
    (hvs : ∀ t, v ∈ A t → v ∉ C t → t = sv) (x y : B) (hxy : x ≠ y)
    (s1 s2 s3 r1 r2 r3 : T) (hs12 : s1 ≠ s2) (hs13 : s1 ≠ s3) (hs23 : s2 ≠ s3)
    (hr12 : r1 ≠ r2) (hr13 : r1 ≠ r3) (hr23 : r2 ≠ r3)
    (hx1 : x ∈ C s1) (hx2 : x ∈ C s2) (hx3 : x ∈ C s3)
    (hy1 : y ∈ C r1) (hy2 : y ∈ C r2) (hy3 : y ∈ C r3)
    (hg1 : ∀ X : Finset T, X.Nonempty → X.card + 1 ≤ (X.biUnion (dl C x s1)).card)
    (hh1 : ∀ X : Finset T, X.Nonempty → X.card + 1 ≤ (X.biUnion (dl C y r1)).card)
    (Z : Finset T) (zs : s1 ∈ Z) (zr : r1 ∈ Z) (zx : ∀ t ∈ Z, x ∈ C t → t = s1)
    (zy : ∀ t ∈ Z, y ∈ C t → t = r1) (zc : (Z.biUnion C).card ≤ Z.card + 2)
    (X2 X3 Y2 Y3 : Finset T)
    (x2s : s2 ∈ X2) (x2c : (X2.biUnion C).card ≤ X2.card + 1) (x2u : ∀ t ∈ X2, x ∈ C t → t = s2)
    (x3s : s3 ∈ X3) (x3c : (X3.biUnion C).card ≤ X3.card + 1) (x3u : ∀ t ∈ X3, x ∈ C t → t = s3)
    (y2r : r2 ∈ Y2) (y2c : (Y2.biUnion C).card ≤ Y2.card + 1) (y2u : ∀ t ∈ Y2, y ∈ C t → t = r2)
    (y3r : r3 ∈ Y3) (y3c : (Y3.biUnion C).card ≤ Y3.card + 1) (y3u : ∀ t ∈ Y3, y ∈ C t → t = r3) :
    False := by
  have dX := disj_of C hC X2 X3 x s2 s3 hs23 (mem_biU x2s hx2) (mem_biU x3s hx3) x2u x3u (by omega)
  have oX := meet_only C hC X2 X3 dX ⟨s2, x2s⟩ x2c x3c x (mem_biU x2s hx2) (mem_biU x3s hx3)
  have dY := disj_of C hC Y2 Y3 y r2 r3 hr23 (mem_biU y2r hy2) (mem_biU y3r hy3) y2u y3u (by omega)
  have oY := meet_only C hC Y2 Y3 dY ⟨r2, y2r⟩ y2c y3c y (mem_biU y2r hy2) (mem_biU y3r hy3)
  have lx := lost_card C x s1 Z zs hx1 zx
  have ly := lost_card C y r1 Z zr hy1 zy
  have zlow : Z.card + 2 ≤ (Z.biUnion C).card := by
    have := hg1 Z ⟨s1, zs⟩
    omega
  -- disjointness of `Z` from the `y`-witnesses (in `C - x@s1`) and the `x`-witnesses (in `C - y@r1`)
  have ydl : ∀ t, y ∈ C t → y ∈ dl C x s1 t := fun t hyt => (mem_dl C x s1 t y).mpr ⟨hyt, fun e => hxy e.1.symm⟩
  have xdl : ∀ t, x ∈ C t → x ∈ dl C y r1 t := fun t hxt => (mem_dl C y r1 t x).mpr ⟨hxt, fun e => hxy e.1⟩
  have dlsx : ∀ W : Finset T, (W.biUnion (dl C x s1)).card ≤ (W.biUnion C).card :=
    fun W => Finset.card_le_card (biU_mono _ _ (dl_sub C x s1) W)
  have dlsy : ∀ W : Finset T, (W.biUnion (dl C y r1)).card ≤ (W.biUnion C).card :=
    fun W => Finset.card_le_card (biU_mono _ _ (dl_sub C y r1) W)
  have dZY : ∀ (Y : Finset T) (r : T), r1 ≠ r → r ∈ Y → y ∈ C r → (Y.biUnion C).card ≤ Y.card + 1 →
      (∀ t ∈ Y, y ∈ C t → t = r) → Disjoint Z Y := by
    intro Y r hr hrY hyr hYc hYu
    have := dlsx Y
    exact disj_of (dl C x s1) hg1 Z Y y r1 r hr (mem_biU zr (ydl r1 hy1)) (mem_biU hrY (ydl r hyr))
      (fun t ht hyt => zy t ht ((mem_dl C x s1 t y).mp hyt).1)
      (fun t ht hyt => hYu t ht ((mem_dl C x s1 t y).mp hyt).1) (by omega)
  have dZX : ∀ (X : Finset T) (s : T), s1 ≠ s → s ∈ X → x ∈ C s → (X.biUnion C).card ≤ X.card + 1 →
      (∀ t ∈ X, x ∈ C t → t = s) → Disjoint Z X := by
    intro X s hs hsX hxs hXc hXu
    have := dlsy X
    exact disj_of (dl C y r1) hh1 Z X x s1 s hs (mem_biU zs (xdl s1 hx1)) (mem_biU hsX (xdl s hxs))
      (fun t ht hxt => zx t ht ((mem_dl C y r1 t x).mp hxt).1)
      (fun t ht hxt => hXu t ht ((mem_dl C y r1 t x).mp hxt).1) (by omega)
  have dZX2 := dZX X2 s2 hs12 x2s hx2 x2c x2u
  have dZX3 := dZX X3 s3 hs13 x3s hx3 x3c x3u
  have dZY2 := dZY Y2 r2 hr12 y2r hy2 y2c y2u
  have dZY3 := dZY Y3 r3 hr13 y3r hy3 y3c y3u
  -- clean witnesses are tight in `A`
  have ct : ∀ (X : Finset T) (t : T), t ∈ X → (X.biUnion C).card ≤ X.card + 1 →
      ¬ (v ∈ X.biUnion A ∧ v ∉ X.biUnion C) → (X.Nonempty ∧ (X.biUnion A).card = X.card + 1) := by
    intro X t ht hc hcl
    have hs : X.biUnion A ⊆ X.biUnion C := by
      intro w hw
      rcases Finset.mem_insert.mp (biU_sup_v A C v hlost X hw) with e | e
      · by_contra hn
        exact hcl ⟨e ▸ hw, e ▸ hn⟩
      · exact e
    exact ⟨⟨t, ht⟩, le_antisymm ((Finset.card_le_card hs).trans hc) (lc_of_hp A h X ⟨t, ht⟩)⟩
  have hdX : (v ∈ X2.biUnion A ∧ v ∉ X2.biUnion C) ∨ (v ∈ X3.biUnion A ∧ v ∉ X3.biUnion C) := by
    by_contra hn
    push Not at hn
    have hd := lemma_LT A h X2 X3 (ct X2 s2 x2s x2c (fun hh => hh.2 (hn.1 hh.1)))
      (ct X3 s3 x3s x3c (fun hh => hh.2 (hn.2 hh.1))) dX
    exact Finset.disjoint_left.mp hd (mem_biU x2s (hsub s2 hx2)) (mem_biU x3s (hsub s3 hx3))
  have hdY : (v ∈ Y2.biUnion A ∧ v ∉ Y2.biUnion C) ∨ (v ∈ Y3.biUnion A ∧ v ∉ Y3.biUnion C) := by
    by_contra hn
    push Not at hn
    have hd := lemma_LT A h Y2 Y3 (ct Y2 r2 y2r y2c (fun hh => hh.2 (hn.1 hh.1)))
      (ct Y3 r3 y3r y3c (fun hh => hh.2 (hn.2 hh.1))) dY
    exact Finset.disjoint_left.mp hd (mem_biU y2r (hsub r2 hy2)) (mem_biU y3r (hsub r3 hy3))
  have oX' : ∀ w ∈ X3.biUnion C, w ∈ X2.biUnion C → w = x := fun w a b => oX w b a
  have oY' : ∀ w ∈ Y3.biUnion C, w ∈ Y2.biUnion C → w = y := fun w a b => oY w b a
  rcases hdX with dx | dx <;> rcases hdY with dy | dy
  · exact uniq_mid A C h hC hsub v hlost sv hvs x y hxy s1 s2 s3 r1 r2 r3 hx1 hx2 hx3 hy1 hy2 hy3
      Z X2 X3 Y2 Y3 zs zr zc zlow x2s x3s x2c x3c y2r y3r y2c y3c dX oX dY oY dZX2 dZX3 dZY2 dZY3 dx dy
  · exact uniq_mid A C h hC hsub v hlost sv hvs x y hxy s1 s2 s3 r1 r3 r2 hx1 hx2 hx3 hy1 hy3 hy2
      Z X2 X3 Y3 Y2 zs zr zc zlow x2s x3s x2c x3c y3r y2r y3c y2c dX oX dY.symm oY' dZX2 dZX3 dZY3 dZY2 dx dy
  · exact uniq_mid A C h hC hsub v hlost sv hvs x y hxy s1 s3 s2 r1 r2 r3 hx1 hx3 hx2 hy1 hy2 hy3
      Z X3 X2 Y2 Y3 zs zr zc zlow x3s x2s x3c x2c y2r y3r y2c y3c dX.symm oX' dY oY dZX3 dZX2 dZY2 dZY3 dx dy
  · exact uniq_mid A C h hC hsub v hlost sv hvs x y hxy s1 s3 s2 r1 r3 r2 hx1 hx3 hx2 hy1 hy3 hy2
      Z X3 X2 Y3 Y2 zs zr zc zlow x3s x2s x3c x2c y3r y2r y3c y2c dX.symm oX' dY.symm oY' dZX3 dZX2 dZY3 dZY2 dx dy


/-- The unique case, from the failures. -/
theorem uniq_wrap (A C : T → Finset B)
    (h : ∀ hpS : Finset B, (Finset.univ.filter (fun hpt => (A hpt \ hpS).card ≤ 1)).card ≤ hpS.card)
    (hC : ∀ X : Finset T, X.Nonempty → X.card + 1 ≤ (X.biUnion C).card)
    (hsub : ∀ t, C t ⊆ A t) (v : B) (hlost : ∀ t, A t ⊆ insert v (C t)) (sv : T)
    (hvs : ∀ t, v ∈ A t → v ∉ C t → t = sv) (x y : B) (hxy : x ≠ y)
    (s1 s2 s3 r1 r2 r3 : T) (hs12 : s1 ≠ s2) (hs13 : s1 ≠ s3) (hs23 : s2 ≠ s3)
    (hr12 : r1 ≠ r2) (hr13 : r1 ≠ r3) (hr23 : r2 ≠ r3)
    (hx1 : x ∈ C s1) (hx2 : x ∈ C s2) (hx3 : x ∈ C s3)
    (hy1 : y ∈ C r1) (hy2 : y ∈ C r2) (hy3 : y ∈ C r3)
    (hg1 : ∀ X : Finset T, X.Nonempty → X.card + 1 ≤ (X.biUnion (dl C x s1)).card)
    (hh1 : ∀ X : Finset T, X.Nonempty → X.card + 1 ≤ (X.biUnion (dl C y r1)).card)
    (b2 : ¬ ∀ X : Finset T, X.Nonempty → X.card + 1 ≤ (X.biUnion (dl C x s2)).card)
    (b3 : ¬ ∀ X : Finset T, X.Nonempty → X.card + 1 ≤ (X.biUnion (dl C x s3)).card)
    (c2 : ¬ ∀ X : Finset T, X.Nonempty → X.card + 1 ≤ (X.biUnion (dl C y r2)).card)
    (c3 : ¬ ∀ X : Finset T, X.Nonempty → X.card + 1 ≤ (X.biUnion (dl C y r3)).card)
    (hfail : ¬ ∀ X : Finset T, X.Nonempty → X.card + 1 ≤ (X.biUnion (dl (dl C x s1) y r1)).card) :
    False := by
  obtain ⟨W, wa, wb, wc⟩ := wit (dl C x s1) hg1 y r1 hfail
  obtain ⟨zs, zx, zy, zc⟩ := lost_both C x y hxy s1 r1 hy1 hh1 W wa wb wc
  obtain ⟨X2, x2s, x2c, x2u⟩ := wit C hC x s2 b2
  obtain ⟨X3, x3s, x3c, x3u⟩ := wit C hC x s3 b3
  obtain ⟨Y2, y2r, y2c, y2u⟩ := wit C hC y r2 c2
  obtain ⟨Y3, y3r, y3c, y3u⟩ := wit C hC y r3 c3
  exact uniq A C h hC hsub v hlost sv hvs x y hxy s1 s2 s3 r1 r2 r3 hs12 hs13 hs23 hr12 hr13 hr23
    hx1 hx2 hx3 hy1 hy2 hy3 hg1 hh1 W zs wa zx zy zc X2 X3 Y2 Y3 x2s x2c x2u x3s x3c x3u
    y2r y2c y2u y3r y3c y3u

/-- GL2 joint deletion: one deleted occurrence of each of `x`, `y` keeps LC. -/
theorem gl2_joint (A C : T → Finset B)
    (h : ∀ hpS : Finset B, (Finset.univ.filter (fun hpt => (A hpt \ hpS).card ≤ 1)).card ≤ hpS.card)
    (hC : ∀ X : Finset T, X.Nonempty → X.card + 1 ≤ (X.biUnion C).card)
    (hsub : ∀ t, C t ⊆ A t) (v : B) (hlost : ∀ t, A t ⊆ insert v (C t)) (sv : T)
    (hvs : ∀ t, v ∈ A t → v ∉ C t → t = sv) (x y : B) (hxy : x ≠ y) (hxv : x ≠ v) (hyv : y ≠ v)
    (s1 s2 s3 r1 r2 r3 : T) (hs12 : s1 ≠ s2) (hs13 : s1 ≠ s3) (hs23 : s2 ≠ s3)
    (hr12 : r1 ≠ r2) (hr13 : r1 ≠ r3) (hr23 : r2 ≠ r3)
    (hx1 : x ∈ C s1) (hx2 : x ∈ C s2) (hx3 : x ∈ C s3)
    (hy1 : y ∈ C r1) (hy2 : y ∈ C r2) (hy3 : y ∈ C r3) :
    ∃ s r, (s = s1 ∨ s = s2 ∨ s = s3) ∧ (r = r1 ∨ r = r2 ∨ r = r3) ∧
      ∀ X : Finset T, X.Nonempty → X.card + 1 ≤ (X.biUnion (dl (dl C x s) y r)).card := by
  obtain ⟨s, hs, hgs⟩ := rf2 A C h hC hsub v hlost x hxv s1 s2 s3 hs12 hs13 hs23 hx1 hx2 hx3
  obtain ⟨r, hr, hgr⟩ := rf2 A C h hC hsub v hlost y hyv r1 r2 r3 hr12 hr13 hr23 hy1 hy2 hy3
  have hys : ∀ r', (r' = r1 ∨ r' = r2 ∨ r' = r3) → y ∈ C r' := by
    intro r' hr'; rcases hr' with rfl | rfl | rfl <;> assumption
  have hxs : ∀ s', (s' = s1 ∨ s' = s2 ∨ s' = s3) → x ∈ C s' := by
    intro s' hs'; rcases hs' with rfl | rfl | rfl <;> assumption
  by_cases hr2 : ∃ r', (r' = r1 ∨ r' = r2 ∨ r' = r3) ∧ r' ≠ r ∧
      ∀ X : Finset T, X.Nonempty → X.card + 1 ≤ (X.biUnion (dl C y r')).card
  · obtain ⟨r', hr', hne, hgr'⟩ := hr2
    rcases claimA C x y hxy s r r' (Ne.symm hne) (hys r hr) (hys r' hr') hgs hgr hgr' with h1 | h1
    · exact ⟨s, r, hs, hr, h1⟩
    · exact ⟨s, r', hs, hr', h1⟩
  by_cases hs2 : ∃ s', (s' = s1 ∨ s' = s2 ∨ s' = s3) ∧ s' ≠ s ∧
      ∀ X : Finset T, X.Nonempty → X.card + 1 ≤ (X.biUnion (dl C x s')).card
  · obtain ⟨s', hs', hne, hgs'⟩ := hs2
    rcases claimA C y x (Ne.symm hxy) r s s' (Ne.symm hne) (hxs s hs) (hxs s' hs') hgr hgs hgs' with h1 | h1
    · exact ⟨s, r, hs, hr, by rw [dl_comm]; exact h1⟩
    · exact ⟨s', r, hs', hr, by rw [dl_comm]; exact h1⟩
  push Not at hr2 hs2
  by_contra hno
  have hfail : ¬ ∀ X : Finset T, X.Nonempty → X.card + 1 ≤ (X.biUnion (dl (dl C x s) y r)).card :=
    fun hL => hno ⟨s, r, hs, hr, hL⟩
  have bx : ∀ s', (s' = s1 ∨ s' = s2 ∨ s' = s3) → s' ≠ s →
      ¬ ∀ X : Finset T, X.Nonempty → X.card + 1 ≤ (X.biUnion (dl C x s')).card := by
    intro s' h1 h2 hL
    obtain ⟨X, hX, hlt⟩ := hs2 s' h1 h2
    have := hL X hX
    omega
  have by' : ∀ r', (r' = r1 ∨ r' = r2 ∨ r' = r3) → r' ≠ r →
      ¬ ∀ X : Finset T, X.Nonempty → X.card + 1 ≤ (X.biUnion (dl C y r')).card := by
    intro r' h1 h2 hL
    obtain ⟨X, hX, hlt⟩ := hr2 r' h1 h2
    have := hL X hX
    omega
  rcases hs with hs | hs | hs <;> rcases hr with hr | hr | hr <;> subst s <;> subst r
  · exact uniq_wrap A C h hC hsub v hlost sv hvs x y hxy s1 s2 s3 r1 r2 r3
      hs12 hs13 hs23 hr12 hr13 hr23
      hx1 hx2 hx3 hy1 hy2 hy3 hgs hgr
      (bx s2 (by simp) (Ne.symm hs12)) (bx s3 (by simp) (Ne.symm hs13))
      (by' r2 (by simp) (Ne.symm hr12)) (by' r3 (by simp) (Ne.symm hr13)) hfail
  · exact uniq_wrap A C h hC hsub v hlost sv hvs x y hxy s1 s2 s3 r2 r1 r3
      hs12 hs13 hs23 (Ne.symm hr12) hr23 hr13
      hx1 hx2 hx3 hy2 hy1 hy3 hgs hgr
      (bx s2 (by simp) (Ne.symm hs12)) (bx s3 (by simp) (Ne.symm hs13))
      (by' r1 (by simp) hr12) (by' r3 (by simp) (Ne.symm hr23)) hfail
  · exact uniq_wrap A C h hC hsub v hlost sv hvs x y hxy s1 s2 s3 r3 r1 r2
      hs12 hs13 hs23 (Ne.symm hr13) (Ne.symm hr23) hr12
      hx1 hx2 hx3 hy3 hy1 hy2 hgs hgr
      (bx s2 (by simp) (Ne.symm hs12)) (bx s3 (by simp) (Ne.symm hs13))
      (by' r1 (by simp) hr13) (by' r2 (by simp) hr23) hfail
  · exact uniq_wrap A C h hC hsub v hlost sv hvs x y hxy s2 s1 s3 r1 r2 r3
      (Ne.symm hs12) hs23 hs13 hr12 hr13 hr23
      hx2 hx1 hx3 hy1 hy2 hy3 hgs hgr
      (bx s1 (by simp) hs12) (bx s3 (by simp) (Ne.symm hs23))
      (by' r2 (by simp) (Ne.symm hr12)) (by' r3 (by simp) (Ne.symm hr13)) hfail
  · exact uniq_wrap A C h hC hsub v hlost sv hvs x y hxy s2 s1 s3 r2 r1 r3
      (Ne.symm hs12) hs23 hs13 (Ne.symm hr12) hr23 hr13
      hx2 hx1 hx3 hy2 hy1 hy3 hgs hgr
      (bx s1 (by simp) hs12) (bx s3 (by simp) (Ne.symm hs23))
      (by' r1 (by simp) hr12) (by' r3 (by simp) (Ne.symm hr23)) hfail
  · exact uniq_wrap A C h hC hsub v hlost sv hvs x y hxy s2 s1 s3 r3 r1 r2
      (Ne.symm hs12) hs23 hs13 (Ne.symm hr13) (Ne.symm hr23) hr12
      hx2 hx1 hx3 hy3 hy1 hy2 hgs hgr
      (bx s1 (by simp) hs12) (bx s3 (by simp) (Ne.symm hs23))
      (by' r1 (by simp) hr13) (by' r2 (by simp) hr23) hfail
  · exact uniq_wrap A C h hC hsub v hlost sv hvs x y hxy s3 s1 s2 r1 r2 r3
      (Ne.symm hs13) (Ne.symm hs23) hs12 hr12 hr13 hr23
      hx3 hx1 hx2 hy1 hy2 hy3 hgs hgr
      (bx s1 (by simp) hs13) (bx s2 (by simp) hs23)
      (by' r2 (by simp) (Ne.symm hr12)) (by' r3 (by simp) (Ne.symm hr13)) hfail
  · exact uniq_wrap A C h hC hsub v hlost sv hvs x y hxy s3 s1 s2 r2 r1 r3
      (Ne.symm hs13) (Ne.symm hs23) hs12 (Ne.symm hr12) hr23 hr13
      hx3 hx1 hx2 hy2 hy1 hy3 hgs hgr
      (bx s1 (by simp) hs13) (bx s2 (by simp) hs23)
      (by' r1 (by simp) hr12) (by' r3 (by simp) (Ne.symm hr23)) hfail
  · exact uniq_wrap A C h hC hsub v hlost sv hvs x y hxy s3 s1 s2 r3 r1 r2
      (Ne.symm hs13) (Ne.symm hs23) hs12 (Ne.symm hr13) (Ne.symm hr23) hr12
      hx3 hx1 hx2 hy3 hy1 hy2 hgs hgr
      (bx s1 (by simp) hs13) (bx s2 (by simp) hs23)
      (by' r1 (by simp) hr13) (by' r2 (by simp) hr23) hfail


omit [DecidableEq T] in
theorem mult_sub (D A : T → Finset B) (hs : ∀ t, D t ⊆ A t) (b : B) :
    (Finset.univ.filter (fun t => b ∈ D t)).card ≤ (Finset.univ.filter (fun t => b ∈ A t)).card := by
  apply Finset.card_le_card
  intro t ht
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
  exact hs t ht

theorem mult_dl (F : T → Finset B) (z : B) (s : T) (hz : z ∈ F s) :
    (Finset.univ.filter (fun t => z ∈ dl F z s t)).card + 1 ≤
      (Finset.univ.filter (fun t => z ∈ F t)).card := by
  have hsub : Finset.univ.filter (fun t => z ∈ dl F z s t) ⊆
      (Finset.univ.filter (fun t => z ∈ F t)).erase s := by
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_dl] at ht
    refine Finset.mem_erase.mpr ⟨fun e => ht.2 e, ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ht.1
  have := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem (by simp [hz])] at this
  have : 0 < (Finset.univ.filter (fun t => z ∈ F t)).card := Finset.card_pos.mpr ⟨s, by simp [hz]⟩
  omega

omit [DecidableEq T] in
theorem three_of (A : T → Finset B) (x : B) (h3 : (Finset.univ.filter (fun t => x ∈ A t)).card = 3) :
    ∃ s1 s2 s3, s1 ≠ s2 ∧ s1 ≠ s3 ∧ s2 ≠ s3 ∧ x ∈ A s1 ∧ x ∈ A s2 ∧ x ∈ A s3 := by
  classical
  obtain ⟨s1, s2, s3, h12, h13, h23, he⟩ := Finset.card_eq_three.mp h3
  have m : ∀ t, t ∈ ({s1, s2, s3} : Finset T) → x ∈ A t := by
    intro t ht
    rw [← he] at ht
    simpa using ht
  exact ⟨s1, s2, s3, h12, h13, h23, m s1 (by simp), m s2 (by simp), m s3 (by simp)⟩

/-- A subfamily with LC and element multiplicities at most two (one at `v`) gives P1 at `v`. -/
theorem finish (A D : T → Finset B) (hs : ∀ t, D t ⊆ A t)
    (hD : ∀ X : Finset T, X.Nonempty → X.card + 1 ≤ (X.biUnion D).card)
    (hdeg : ∀ b, (Finset.univ.filter (fun t => b ∈ D t)).card ≤ 2) (v : B)
    (hv : (Finset.univ.filter (fun t => v ∈ D t)).card ≤ 1) :
    ∃ e : T → B × B, (∀ t, (e t).1 ∈ A t ∧ (e t).2 ∈ A t ∧ (e t).1 ≠ (e t).2) ∧
      (∀ lcX : Finset _, lcX.Nonempty → lcX.card + 1 ≤
        (lcX.biUnion ((fun prt => ({(e prt).1, (e prt).2} : Finset B)))).card) ∧
      (∀ x, (Finset.univ.filter (fun t => x ∈ ({(e t).1, (e t).2} : Finset B))).card ≤ 2) ∧
      (Finset.univ.filter (fun t => v ∈ ({(e t).1, (e t).2} : Finset B))).card ≤ 1 := by
  obtain ⟨e, he, hL⟩ := lovasz_pairs _ D le_rfl hD
  have hdm : ∀ b, (Finset.univ.filter (fun t => b ∈ ({(e t).1, (e t).2} : Finset B))).card ≤
      (Finset.univ.filter (fun t => b ∈ D t)).card := by
    intro b
    apply Finset.card_le_card
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton] at ht ⊢
    rcases ht with rfl | rfl
    · exact (he t).1
    · exact (he t).2.1
  exact ⟨e, fun t => ⟨hs t (he t).1, hs t (he t).2.1, (he t).2.2⟩, hL,
    fun b => (hdm b).trans (hdeg b), (hdm v).trans hv⟩


omit [DecidableEq T] in
theorem two_sets (A : T → Finset B) (v : B) (t0 : T) (hm : (Finset.univ.filter (fun t => v ∈ A t)).card ≤ 2) (ht0 : v ∈ A t0) :
    ∃ sv, ∀ t, v ∈ A t → t = t0 ∨ t = sv := by
  classical
  by_cases hex : ∃ t', v ∈ A t' ∧ t' ≠ t0
  · obtain ⟨t', ht', hne⟩ := hex
    refine ⟨t', fun t ht => ?_⟩
    by_contra hc
    push Not at hc
    have hs : ({t0, t', t} : Finset T) ⊆ Finset.univ.filter (fun t => v ∈ A t) := by
      intro u hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl | rfl <;> simp [*]
    have h3 : ({t0, t', t} : Finset T).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_pair (Ne.symm hc.2)]
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm hne, Ne.symm hc.1⟩
    have := Finset.card_le_card hs
    omega
  · push Not at hex
    exact ⟨t0, fun t ht => Or.inl (hex t ht)⟩

/-- GL2 from a prepared family `C` (`v` reduced to one set). -/
theorem gl2_D (A C : T → Finset B) (h : (∀ hpS : Finset B, (Finset.univ.filter (fun hpt => (A hpt \ hpS).card ≤ 1)).card ≤ hpS.card)) (x0 x1 v : B)
    (hdeg : ∀ b, b ≠ x0 → b ≠ x1 → (Finset.univ.filter (fun t => b ∈ A t)).card ≤ 2)
    (hx0 : (Finset.univ.filter (fun t => x0 ∈ A t)).card ≤ 3) (hx1 : (Finset.univ.filter (fun t => x1 ∈ A t)).card ≤ 3)
    (hsub : ∀ t, C t ⊆ A t) (hlost : ∀ t, A t ⊆ insert v (C t))
    (hC : ∀ X : Finset T, X.Nonempty → X.card + 1 ≤ (X.biUnion C).card)
    (hvC : (Finset.univ.filter (fun t => v ∈ C t)).card ≤ 1)
    (hsv : x0 ≠ v → x1 ≠ v → x0 ≠ x1 → (Finset.univ.filter (fun t => x0 ∈ A t)).card = 3 →
      ∃ sv, ∀ t, v ∈ A t → v ∉ C t → t = sv) :
    ∃ e : T → B × B, (∀ t, (e t).1 ∈ A t ∧ (e t).2 ∈ A t ∧ (e t).1 ≠ (e t).2) ∧
      (∀ lcX : Finset _, lcX.Nonempty → lcX.card + 1 ≤
        (lcX.biUnion ((fun prt => ({(e prt).1, (e prt).2} : Finset B)))).card) ∧
      (∀ x, (Finset.univ.filter (fun t => x ∈ ({(e t).1, (e t).2} : Finset B))).card ≤ 2) ∧
      (Finset.univ.filter (fun t => v ∈ ({(e t).1, (e t).2} : Finset B))).card ≤ 1 := by
  classical
  have mC : ∀ b, b ≠ v → (Finset.univ.filter (fun t => b ∈ C t)).card = (Finset.univ.filter (fun t => b ∈ A t)).card := by
    intro b hb
    congr 1
    apply Finset.filter_congr
    intro t _
    constructor
    · exact fun hbt => hsub t hbt
    · intro hbt
      rcases Finset.mem_insert.mp (hlost t hbt) with e | e
      · exact absurd e hb
      · exact e
  have fin : ∀ D : T → Finset B, (∀ t, D t ⊆ C t) →
      (∀ X : Finset T, X.Nonempty → X.card + 1 ≤ (X.biUnion D).card) →
      (∀ b, (Finset.univ.filter (fun t => b ∈ D t)).card ≤ 2) → ∃ e : T → B × B, (∀ t, (e t).1 ∈ A t ∧ (e t).2 ∈ A t ∧ (e t).1 ≠ (e t).2) ∧
      (∀ lcX : Finset _, lcX.Nonempty → lcX.card + 1 ≤
        (lcX.biUnion ((fun prt => ({(e prt).1, (e prt).2} : Finset B)))).card) ∧
      (∀ x, (Finset.univ.filter (fun t => x ∈ ({(e t).1, (e t).2} : Finset B))).card ≤ 2) ∧
      (Finset.univ.filter (fun t => v ∈ ({(e t).1, (e t).2} : Finset B))).card ≤ 1 := by
    intro D hDC hD hDd
    exact finish A D (fun t => (hDC t).trans (hsub t)) hD hDd v
      ((mult_sub D C hDC v).trans hvC)
  have gen : ∀ D : T → Finset B, (∀ t, D t ⊆ C t) → ∀ b, b ≠ x0 → b ≠ x1 → (Finset.univ.filter (fun t => b ∈ D t)).card ≤ 2 := by
    intro D hDC b h0 h1
    by_cases hbv : b = v
    · subst hbv; have := (mult_sub D C hDC b).trans hvC; omega
    · exact (mult_sub D C hDC b).trans ((mC b hbv).le.trans (hdeg b h0 h1))
  have small : ∀ D : T → Finset B, (∀ t, D t ⊆ C t) → ∀ b, ¬ (b ≠ v ∧ (Finset.univ.filter (fun t => b ∈ A t)).card = 3) →
      (Finset.univ.filter (fun t => b ∈ A t)).card ≤ 3 → (Finset.univ.filter (fun t => b ∈ D t)).card ≤ 2 := by
    intro D hDC b hn h3
    by_cases hbv : b = v
    · subst hbv; have := (mult_sub D C hDC b).trans hvC; omega
    · have := (mult_sub D C hDC b).trans (mC b hbv).le
      have : (Finset.univ.filter (fun t => b ∈ A t)).card ≠ 3 := fun e => hn ⟨hbv, e⟩
      omega
  by_cases p0 : x0 ≠ v ∧ (Finset.univ.filter (fun t => x0 ∈ A t)).card = 3 <;>
    by_cases p1 : x1 ≠ v ∧ x1 ≠ x0 ∧ (Finset.univ.filter (fun t => x1 ∈ A t)).card = 3
  · -- both exceptional elements have multiplicity three
    obtain ⟨s1, s2, s3, a12, a13, a23, m1, m2, m3⟩ := three_of C x0 ((mC x0 p0.1).trans p0.2)
    obtain ⟨r1, r2, r3, b12, b13, b23, n1, n2, n3⟩ := three_of C x1 ((mC x1 p1.1).trans p1.2.2)
    obtain ⟨sv, hvs⟩ := hsv p0.1 p1.1 (Ne.symm p1.2.1) p0.2
    obtain ⟨s, r, hs, hr, hL⟩ := gl2_joint A C h hC hsub v hlost sv hvs x0 x1 (Ne.symm p1.2.1) p0.1 p1.1
      s1 s2 s3 r1 r2 r3 a12 a13 a23 b12 b13 b23 m1 m2 m3 n1 n2 n3
    have hxs : x0 ∈ C s := by rcases hs with rfl | rfl | rfl <;> assumption
    have hyr : x1 ∈ C r := by rcases hr with rfl | rfl | rfl <;> assumption
    have hDC : ∀ t, dl (dl C x0 s) x1 r t ⊆ C t := fun t => (dl_sub _ _ _ t).trans (dl_sub _ _ _ t)
    apply fin _ hDC hL
    intro b
    by_cases hb0 : b = x0
    · subst hb0
      have e1 := mult_sub (dl (dl C b s) x1 r) (dl C b s) (dl_sub _ _ _) b
      have e2 := mult_dl C b s hxs
      have e3 := mC b p0.1
      omega
    by_cases hb1 : b = x1
    · subst hb1
      have hyr' : b ∈ dl C x0 s r := (mem_dl C x0 s r b).mpr ⟨hyr, fun e => p1.2.1 e.1⟩
      have e1 := mult_dl (dl C x0 s) b r hyr'
      have e2 := mult_sub (dl C x0 s) C (dl_sub _ _ _) b
      have e3 := mC b p1.1
      omega
    exact gen _ hDC b hb0 hb1
  · obtain ⟨s1, s2, s3, a12, a13, a23, m1, m2, m3⟩ := three_of C x0 ((mC x0 p0.1).trans p0.2)
    obtain ⟨s, hs, hL⟩ := rf2 A C h hC hsub v hlost x0 p0.1 s1 s2 s3 a12 a13 a23 m1 m2 m3
    have hxs : x0 ∈ C s := by rcases hs with rfl | rfl | rfl <;> assumption
    have hDC : ∀ t, dl C x0 s t ⊆ C t := dl_sub _ _ _
    apply fin _ hDC hL
    intro b
    by_cases hb0 : b = x0
    · subst hb0
      have e2 := mult_dl C b s hxs
      have e3 := mC b p0.1
      omega
    by_cases hb1 : b = x1
    · subst hb1
      exact small _ hDC b (fun hh => p1 ⟨hh.1, hb0, hh.2⟩) hx1
    exact gen _ hDC b hb0 hb1
  · obtain ⟨r1, r2, r3, b12, b13, b23, n1, n2, n3⟩ := three_of C x1 ((mC x1 p1.1).trans p1.2.2)
    obtain ⟨r, hr, hL⟩ := rf2 A C h hC hsub v hlost x1 p1.1 r1 r2 r3 b12 b13 b23 n1 n2 n3
    have hyr : x1 ∈ C r := by rcases hr with rfl | rfl | rfl <;> assumption
    have hDC : ∀ t, dl C x1 r t ⊆ C t := dl_sub _ _ _
    apply fin _ hDC hL
    intro b
    by_cases hb1 : b = x1
    · subst hb1
      have e2 := mult_dl C b r hyr
      have e3 := mC b p1.1
      omega
    by_cases hb0 : b = x0
    · subst hb0
      exact small _ hDC b p0 hx0
    exact gen _ hDC b hb0 hb1
  · apply fin C (fun _ => subset_rfl) hC
    intro b
    by_cases hb0 : b = x0
    · subst hb0; exact small C (fun _ => subset_rfl) b p0 hx0
    by_cases hb1 : b = x1
    · subst hb1; exact small C (fun _ => subset_rfl) b (fun hh => p1 ⟨hh.1, hb0, hh.2⟩) hx1
    exact gen C (fun _ => subset_rfl) b hb0 hb1

/-- Theorem GL2: HP, every element in at most two sets except two elements in at most three sets
each ⟹ P1. -/
theorem theorem_GL2 (A : T → Finset B) (h : (∀ hpS : Finset B, (Finset.univ.filter (fun hpt => (A hpt \ hpS).card ≤ 1)).card ≤ hpS.card)) (x0 x1 : B)
    (hdeg : ∀ b, b ≠ x0 → b ≠ x1 → (Finset.univ.filter (fun t => b ∈ A t)).card ≤ 2)
    (hx0 : (Finset.univ.filter (fun t => x0 ∈ A t)).card ≤ 3) (hx1 : (Finset.univ.filter (fun t => x1 ∈ A t)).card ≤ 3) (v : B) :
    ∃ e : T → B × B, (∀ t, (e t).1 ∈ A t ∧ (e t).2 ∈ A t ∧ (e t).1 ≠ (e t).2) ∧
      (∀ lcX : Finset _, lcX.Nonempty → lcX.card + 1 ≤
        (lcX.biUnion ((fun prt => ({(e prt).1, (e prt).2} : Finset B)))).card) ∧
      (∀ x, (Finset.univ.filter (fun t => x ∈ ({(e t).1, (e t).2} : Finset B))).card ≤ 2) ∧
      (Finset.univ.filter (fun t => v ∈ ({(e t).1, (e t).2} : Finset B))).card ≤ 1 := by
  classical
  by_cases hv : ∃ t, v ∈ A t
  · obtain ⟨t0, ht0, hL⟩ := theorem_RF1 A h v hv
    apply gl2_D A (fun kpt => if kpt = t0 then A kpt else (A kpt).erase v) h x0 x1 v hdeg hx0 hx1
    · intro t
      by_cases ht : t = t0
      · simp [ht]
      · simp only [ht, if_false]; exact Finset.erase_subset _ _
    · intro t
      by_cases ht : t = t0
      · simp only [ht, if_true]; exact Finset.subset_insert _ _
      · simp only [ht, if_false]; exact Finset.insert_erase_subset _ _
    · exact hL
    · have hs : Finset.univ.filter (fun t => v ∈ (fun kpt => if kpt = t0 then A kpt else (A kpt).erase v) t) ⊆ {t0} := by
        intro t ht
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
        by_contra hne
        rw [Finset.mem_singleton] at hne
        simp [hne] at ht
      have := Finset.card_le_card hs
      rwa [Finset.card_singleton] at this
    · intro h0 h1 _ _
      obtain ⟨sv, hsv⟩ := two_sets A v t0 (hdeg v (Ne.symm h0) (Ne.symm h1)) ht0
      refine ⟨sv, fun t hvt hvn => ?_⟩
      rcases hsv t hvt with e | e
      · subst e; simp [hvt] at hvn
      · exact e
  · push Not at hv
    apply gl2_D A A h x0 x1 v hdeg hx0 hx1 (fun _ => subset_rfl) (fun _ => Finset.subset_insert _ _)
      (lc_of_hp A h)
    · have : Finset.univ.filter (fun t => v ∈ A t) = ∅ := by
        apply Finset.filter_false_of_mem; intro t _; exact hv t
      rw [this]; simp
    · intro _ _ _ h3
      obtain ⟨s1, -, -, -, -, -, -, -, -⟩ := three_of A x0 h3
      exact ⟨s1, fun t hvt => absurd hvt (hv t)⟩


end fam

section bl

variable {B : Type} [DecidableEq B]

/-- The block condition at `b` (as in `R1.H1.R2`). -/
def BLat {T : Type} (A : T → Finset B) (b : B) : Prop :=
  ∀ (blt1 blt2 blt3 : T), blt1 ≠ blt2 → blt1 ≠ blt3 → blt2 ≠ blt3 → b ∈ A blt1 → b ∈ A blt2 →
    b ∈ A blt3 → ∃ blp : T → Prop, (∀ bls bls2, blp bls → ¬ blp bls2 → A bls ∩ A bls2 ⊆ {b}) ∧
      ¬ ((blp blt1 ↔ blp blt2) ∧ (blp blt1 ↔ blp blt3))

theorem blat_mono {T T' : Type} (A : T → Finset B) (f : T' → T) (hf : Function.Injective f)
    (A' : T' → Finset B) (hA' : ∀ t, A' t ⊆ A (f t)) (b : B) (hb : BLat A b) : BLat A' b := by
  intro t1 t2 t3 h12 h13 h23 hb1 hb2 hb3
  obtain ⟨p, hsep, hns⟩ := hb (f t1) (f t2) (f t3) (fun e => h12 (hf e)) (fun e => h13 (hf e))
    (fun e => h23 (hf e)) (hA' _ hb1) (hA' _ hb2) (hA' _ hb3)
  refine ⟨fun s => p (f s), fun s s' hs hs' => ?_, hns⟩
  exact (Finset.inter_subset_inter (hA' s) (hA' s')).trans (hsep _ _ hs hs')

theorem mult_mono {T T' : Type} [Fintype T] [Fintype T'] (A : T → Finset B) (f : T' → T)
    (hf : Function.Injective f) (A' : T' → Finset B) (hA' : ∀ t, A' t ⊆ A (f t)) (b : B) :
    (Finset.univ.filter (fun t => b ∈ A' t)).card ≤ (Finset.univ.filter (fun t => b ∈ A t)).card := by
  classical
  have hsub : (Finset.univ.filter (fun t => b ∈ A' t)).map ⟨f, hf⟩ ⊆
      Finset.univ.filter (fun t => b ∈ A t) := by
    intro t ht
    obtain ⟨t', ht', rfl⟩ := Finset.mem_map.mp ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht' ⊢
    exact hA' t' ht'
  have := Finset.card_le_card hsub
  rwa [Finset.card_map] at this

/-- Theorem BL2: HP, the block condition at every element except `x0`, `x1`, and these two in at
most three sets each ⟹ P1. -/
theorem theorem_BL2 (x0 x1 : B) : ∀ (n : ℕ) (T : Type) [Fintype T] [DecidableEq T] (A : T → Finset B),
    Fintype.card T = n →
    (∀ hpS : Finset B, (Finset.univ.filter (fun hpt => (A hpt \ hpS).card ≤ 1)).card ≤ hpS.card) →
    (∀ b : B, b ≠ x0 → b ≠ x1 → BLat A b) →
    (Finset.univ.filter (fun t => x0 ∈ A t)).card ≤ 3 →
    (Finset.univ.filter (fun t => x1 ∈ A t)).card ≤ 3 →
    (∀ p1w, (∃ p1e : _ → _ × _, (∀ p1t, (p1e p1t).1 ∈ A p1t ∧ (p1e p1t).2 ∈ A p1t ∧
      (p1e p1t).1 ≠ (p1e p1t).2) ∧ (∀ lcX : Finset _, lcX.Nonempty → lcX.card + 1 ≤
      (lcX.biUnion ((fun prt => ({(p1e prt).1, (p1e prt).2} : Finset B)))).card) ∧
      (∀ p1x, (Finset.univ.filter (fun p1t => p1x ∈ ({(p1e p1t).1, (p1e p1t).2} : Finset B))).card
        ≤ 2) ∧
      (Finset.univ.filter (fun p1t => p1w ∈ ({(p1e p1t).1, (p1e p1t).2} : Finset B))).card ≤ 1)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
  intro T _ _ A hn hHP hbl hx0 hx1
  classical
  by_cases hsplit : ∃ b, b ≠ x0 ∧ b ≠ x1 ∧ 2 < (Finset.univ.filter (fun t => b ∈ A t)).card
  · obtain ⟨b, hb0, hb1, hb⟩ := hsplit
    obtain ⟨t1, ht1, t2, ht2, t3, ht3, h12, h13, h23⟩ := Finset.two_lt_card.mp hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht1 ht2 ht3
    obtain ⟨p, hsep, hns⟩ := hbl b hb0 hb1 t1 t2 t3 h12 h13 h23 ht1 ht2 ht3
    have hboth : (∃ s, p s) ∧ (∃ s, ¬ p s) := by
      by_cases hp1 : p t1
      · by_cases hp2 : p t2
        · by_cases hp3 : p t3
          · exact absurd ⟨iff_of_true hp1 hp2, iff_of_true hp1 hp3⟩ hns
          · exact ⟨⟨t1, hp1⟩, ⟨t3, hp3⟩⟩
        · exact ⟨⟨t1, hp1⟩, ⟨t2, hp2⟩⟩
      · by_cases hp2 : p t2
        · exact ⟨⟨t2, hp2⟩, ⟨t1, hp1⟩⟩
        · by_cases hp3 : p t3
          · exact ⟨⟨t3, hp3⟩, ⟨t1, hp1⟩⟩
          · exact absurd ⟨iff_of_false hp1 hp2, iff_of_false hp1 hp3⟩ hns
    obtain ⟨⟨s1, hs1⟩, ⟨s2, hs2⟩⟩ := hboth
    have c1 : Fintype.card {t // p t} < n := hn ▸ Fintype.card_subtype_lt hs2
    have c2 : Fintype.card {t // ¬ p t} < n := hn ▸ Fintype.card_subtype_lt (not_not.mpr hs1)
    have v1 := Subtype.val_injective (p := p)
    have v2 := Subtype.val_injective (p := fun t => ¬ p t)
    have inh : ∀ (T' : Type) [Fintype T'] (f : T' → T), Function.Injective f →
        ∀ A' : T' → Finset B, (∀ t, A' t ⊆ A (f t)) →
        (∀ b : B, b ≠ x0 → b ≠ x1 → BLat A' b) ∧
        (Finset.univ.filter (fun t => x0 ∈ A' t)).card ≤ 3 ∧
        (Finset.univ.filter (fun t => x1 ∈ A' t)).card ≤ 3 := by
      intro T' _ f hf A' hA'
      exact ⟨fun b h0 h1 => blat_mono A f hf A' hA' b (hbl b h0 h1),
        (mult_mono A f hf A' hA' x0).trans hx0, (mult_mono A f hf A' hA' x1).trans hx1⟩
    have i1m := inh {t // p t} Subtype.val v1 (fun t => (A t.1).erase b)
      (fun t => Finset.erase_subset _ _)
    have i1p := inh {t // p t} Subtype.val v1 (fun t => A t.1) (fun t => subset_rfl)
    have i2m := inh {t // ¬ p t} Subtype.val v2 (fun t => (A t.1).erase b)
      (fun t => Finset.erase_subset _ _)
    have i2p := inh {t // ¬ p t} Subtype.val v2 (fun t => A t.1) (fun t => subset_rfl)
    exact theorem_CE A hHP b p hsep
      (fun hm => ih _ c1 {t // p t} _ rfl hm i1m.1 i1m.2.1 i1m.2.2)
      (ih _ c1 {t // p t} _ rfl (hp_sub A hHP Subtype.val v1) i1p.1 i1p.2.1 i1p.2.2)
      (fun hm => ih _ c2 {t // ¬ p t} _ rfl hm i2m.1 i2m.2.1 i2m.2.2)
      (ih _ c2 {t // ¬ p t} _ rfl (hp_sub A hHP Subtype.val v2) i2p.1 i2p.2.1 i2p.2.2)
  · push Not at hsplit
    intro v
    exact theorem_GL2 A hHP x0 x1 hsplit hx0 hx1 v

/-- Theorem BL2 in the graph form of the R3 statement. -/
theorem BL2_R3form {T : Type} [Fintype T] [DecidableEq T] (A : T → Finset B) (x0 x1 : B)
    (h : ∀ hpS : Finset B, (Finset.univ.filter (fun hpt => (A hpt \ hpS).card ≤ 1)).card ≤ hpS.card)
    (hbl : ∀ b : B, b ≠ x0 → b ≠ x1 → BLat A b)
    (hx0 : (Finset.univ.filter (fun t => x0 ∈ A t)).card ≤ 3)
    (hx1 : (Finset.univ.filter (fun t => x1 ∈ A t)).card ≤ 3) (v : B) :
    ∃ e : T → B × B,
      (∀ t : T, (e t).1 ∈ A t ∧ (e t).2 ∈ A t ∧ (e t).1 ≠ (e t).2) ∧
      Function.Injective (fun t : T => s((e t).1, (e t).2)) ∧
      (SimpleGraph.fromRel (fun x y : B => ∃ t : T, e t = (x, y))).IsAcyclic ∧
      (∀ x a b c : B,
        (SimpleGraph.fromRel (fun x y : B => ∃ t : T, e t = (x, y))).Adj x a →
        (SimpleGraph.fromRel (fun x y : B => ∃ t : T, e t = (x, y))).Adj x b →
        (SimpleGraph.fromRel (fun x y : B => ∃ t : T, e t = (x, y))).Adj x c →
        a = b ∨ a = c ∨ b = c) ∧
      (∀ a b : B,
        (SimpleGraph.fromRel (fun x y : B => ∃ t : T, e t = (x, y))).Adj v a →
        (SimpleGraph.fromRel (fun x y : B => ∃ t : T, e t = (x, y))).Adj v b → a = b) := by
  obtain ⟨e, he, hL, hd2, hd1⟩ := theorem_BL2 x0 x1 _ T A rfl h hbl hx0 hx1 v
  obtain ⟨b1, b2, b3, b4⟩ := bridge e (fun t => (he t).2.2) hL hd2 v hd1
  exact ⟨e, he, b1, b2, b3, b4⟩

end bl


open SimpleGraph

section

private lemma isAcyclic_of_all_adj_eq {W : Type*} (H : SimpleGraph W) (r : W)
    (hstar : ∀ a b : W, H.Adj a b → a = r ∨ b = r) : H.IsAcyclic := by
  intro u c hc
  have hlen := hc.three_le_length
  cases c with
  | nil => simp at hlen
  | @cons _ x _ h1 c1 =>
    cases c1 with
    | nil => simp at hlen
    | @cons _ y _ h2 c2 =>
      cases c2 with
      | nil => simp at hlen
      | @cons _ z _ h3 c3 =>
        have hnd : (x :: y :: c3.support).Nodup := hc.support_nodup
        rw [List.nodup_cons] at hnd
        have hx_not : x ∉ y :: c3.support := hnd.1
        have hy_nd : (y :: c3.support).Nodup := hnd.2
        rw [List.nodup_cons] at hy_nd
        have hy_not : y ∉ c3.support := hy_nd.1
        have hz_mem : z ∈ c3.support := c3.start_mem_support
        have hu_mem : u ∈ c3.support := c3.end_mem_support
        rcases hstar u x h1 with rfl | rfl
        · rcases hstar x y h2 with hxr | rfl
          · exact H.ne_of_adj h1 hxr.symm
          · exact hy_not hu_mem
        · rcases hstar y z h3 with hyx | rfl
          · exact H.ne_of_adj h2 hyx.symm
          · exact hx_not (List.mem_cons_of_mem _ hz_mem)

private lemma indep_add_one_le_forest {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) (hconn : H.Connected) (hn : 1 < Fintype.card W)
    (I : Finset W) (hind : ∀ x ∈ I, ∀ y ∈ I, ¬ H.Adj x y) :
    I.card + 1 ≤ H.largestInducedForestSize := by
  obtain ⟨w, hw⟩ : ∃ w : W, w ∉ I := by
    by_contra hall
    push Not at hall
    obtain ⟨x, y, hxy⟩ := Fintype.one_lt_card_iff.mp hn
    obtain ⟨p⟩ := hconn.preconnected x y
    cases p with
    | nil => exact hxy rfl
    | @cons _ z _ hxz _ => exact hind x (hall x) z (hall z) hxz
  let T : Finset W := insert w I
  have hTcard : T.card = I.card + 1 := Finset.card_insert_of_notMem hw
  have hTacyc : (H.induce (T : Set W)).IsAcyclic := by
    apply isAcyclic_of_all_adj_eq (H.induce (T : Set W)) ⟨w, Finset.mem_insert_self w I⟩
    intro a b hadj
    have ha : a.val = w ∨ a.val ∈ I := Finset.mem_insert.mp a.prop
    have hb : b.val = w ∨ b.val ∈ I := Finset.mem_insert.mp b.prop
    rcases ha with haw | haI
    · exact Or.inl (Subtype.ext haw)
    · rcases hb with hbw | hbI
      · exact Or.inr (Subtype.ext hbw)
      · exact (hind a.val haI b.val hbI hadj).elim
  unfold SimpleGraph.largestInducedForestSize
  apply le_csSup
  · exact ⟨Fintype.card W, fun n ⟨t, _, ht⟩ => ht ▸ t.card_le_univ⟩
  · exact ⟨T, hTacyc, hTcard⟩

private lemma ncvr_exists_acyclic_card_eq {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) :
    ∃ F : Finset α, (G.induce (F : Set α)).IsAcyclic ∧
      F.card = G.largestInducedForestSize := by
  have hne : { n | ∃ s : Finset α, (G.induce (s : Set α)).IsAcyclic ∧ s.card = n }.Nonempty := by
    refine ⟨0, ∅, ?_, rfl⟩
    intro u
    exact False.elim (Finset.notMem_empty u.1 u.2)
  have hbdd : BddAbove { n | ∃ s : Finset α, (G.induce (s : Set α)).IsAcyclic ∧ s.card = n } :=
    ⟨Fintype.card α, fun _ ⟨t, _, ht⟩ => ht ▸ t.card_le_univ⟩
  exact Nat.sSup_mem hne hbdd

private lemma ncvr_card_le_largestInducedForestSize {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) (F : Finset α) (hF : (G.induce (F : Set α)).IsAcyclic) :
    F.card ≤ G.largestInducedForestSize := by
  unfold SimpleGraph.largestInducedForestSize
  apply le_csSup
  · exact ⟨Fintype.card α, fun _ ⟨t, _, ht⟩ => ht ▸ t.card_le_univ⟩
  · exact ⟨F, hF, rfl⟩

private lemma r2_isPathCover_mono {V : Type*} [Fintype V] [DecidableEq V]
    {G K : SimpleGraph V} (hle : K ≤ G) {P : Finset (Finset V)} (hP : K.IsPathCover P) :
    G.IsPathCover P := by
  rcases hP with ⟨hdisj, hcov, hpaths⟩
  refine ⟨hdisj, hcov, ?_⟩
  intro s hs
  rcases hpaths s hs with ⟨u, w, p, hp, rfl⟩
  refine ⟨u, w, p.mapLe hle, hp.mapLe hle, ?_⟩
  rw [Walk.support_mapLe_eq_support]

end

section

private lemma p1_reach_map {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} (ψ : V → W)
    (hψ : ∀ u w, G.Adj u w → ψ u = ψ w ∨ H.Adj (ψ u) (ψ w)) {u w : V}
    (h : G.Reachable u w) : H.Reachable (ψ u) (ψ w) := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact Reachable.refl _
  | cons hadj _ ih =>
    rcases hψ _ _ hadj with heq | hadj'
    · rw [heq]; exact ih
    · exact hadj'.reachable.trans ih

private lemma p1_path_interior {V : Type*} {G : SimpleGraph V} {u v : V} (p : G.Walk u v)
    (hp : p.IsPath) (x : V) (hx : x ∈ p.support) :
    x = u ∨ x = v ∨ ∃ a b, a ≠ b ∧ G.Adj x a ∧ G.Adj x b := by
  induction p with
  | nil =>
    left
    simpa using hx
  | @cons u w v h q ih =>
    rw [Walk.cons_isPath_iff] at hp
    rw [Walk.support_cons, List.mem_cons] at hx
    rcases hx with hxu | hx
    · exact Or.inl hxu
    · rcases ih hp.1 hx with hxw | hxv | h3
      · subst hxw
        cases q with
        | nil => exact Or.inr (Or.inl rfl)
        | @cons _ w' _ h' q' =>
          refine Or.inr (Or.inr ⟨u, w', ?_, h.symm, h'⟩)
          intro huw
          apply hp.2
          rw [Walk.support_cons, List.mem_cons]
          right
          rw [huw]
          exact q'.start_mem_support
      · exact Or.inr (Or.inl hxv)
      · exact Or.inr (Or.inr h3)

private lemma p1_reachable_of_mem_support {V : Type*} [DecidableEq V] {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) {x y : V} (hx : x ∈ p.support) (hy : y ∈ p.support) : G.Reachable x y :=
  (Walk.reachable (p.takeUntil x hx)).symm.trans (Walk.reachable (p.takeUntil y hy))

/-- A path whose vertex set contains a vertex `x` without two distinct neighbours can be
re-oriented to end at `x`. -/
private lemma p1_path_to_end {V : Type*} [DecidableEq V] {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (hp : p.IsPath) (x : V) (hx : x ∈ p.support)
    (hdeg : ∀ a b, G.Adj x a → G.Adj x b → a = b) :
    ∃ (z : V) (q : G.Walk z x), q.IsPath ∧ q.support.toFinset = p.support.toFinset := by
  rcases p1_path_interior p hp x hx with rfl | rfl | ⟨a, b, hab, ha, hb⟩
  · refine ⟨v, p.reverse, hp.reverse, ?_⟩
    rw [Walk.support_reverse, List.toFinset_reverse]
  · exact ⟨u, p, hp, rfl⟩
  · exact (hab (hdeg a b ha hb)).elim

/-- Path cover from a linear forest given by a finite edge set: every edge is a bridge and no
vertex lies on three edges. -/
private lemma p1_linear_forest_cover {V : Type*} [Fintype V] [DecidableEq V]
    (E : Finset (Sym2 V)) (hdiag : ∀ x y, s(x, y) ∈ E → x ≠ y)
    (hdeg : ∀ x a b c, s(x, a) ∈ E → s(x, b) ∈ E → s(x, c) ∈ E → a = b ∨ a = c ∨ b = c)
    (hbr : ∀ x y, s(x, y) ∈ E →
      ¬ (fromEdgeSet ((E.erase s(x, y) : Finset (Sym2 V)) : Set (Sym2 V))).Reachable x y) :
    ∃ P : Finset (Finset V),
      (fromEdgeSet (E : Set (Sym2 V))).IsPathCover P ∧ P.card + E.card = Fintype.card V := by
  suffices hmain : ∀ E' : Finset (Sym2 V), E' ⊆ E → ∃ P : Finset (Finset V),
      (fromEdgeSet (E' : Set (Sym2 V))).IsPathCover P ∧ P.card + E'.card = Fintype.card V from
    hmain E (Finset.Subset.refl E)
  intro E'
  induction E' using Finset.induction_on with
  | empty =>
    intro _
    refine ⟨Finset.univ.image (fun x : V => ({x} : Finset V)), ⟨?_, ?_, ?_⟩, ?_⟩
    · intro s1 hs1 s2 hs2 hne_s
      rcases Finset.mem_image.mp hs1 with ⟨x1, _, rfl⟩
      rcases Finset.mem_image.mp hs2 with ⟨x2, _, rfl⟩
      rw [Finset.disjoint_singleton]
      intro hx
      exact hne_s (by rw [hx])
    · intro x _
      rw [Finset.mem_biUnion]
      exact ⟨{x}, Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩, Finset.mem_singleton_self x⟩
    · intro s hs
      rcases Finset.mem_image.mp hs with ⟨x, _, rfl⟩
      exact ⟨x, x, Walk.nil, Walk.IsPath.nil, by simp⟩
    · rw [Finset.card_image_of_injective _ Finset.singleton_injective, Finset.card_empty,
        Finset.card_univ, Nat.add_zero]
  | @insert e E0 he ih =>
    intro hsub
    have hE0 : E0 ⊆ E := fun z hz => hsub (Finset.mem_insert_of_mem hz)
    have heE : e ∈ E := hsub (Finset.mem_insert_self e E0)
    obtain ⟨P0, hP0, hcard0⟩ := ih hE0
    obtain ⟨hdisj, hcov, hpaths⟩ := hP0
    induction e using Sym2.ind with
    | _ x y =>
    have hxy : x ≠ y := hdiag x y heE
    have hle : fromEdgeSet (E0 : Set (Sym2 V)) ≤
        fromEdgeSet ((insert s(x, y) E0 : Finset (Sym2 V)) : Set (Sym2 V)) := by
      apply fromEdgeSet_mono
      intro z hz
      exact Finset.mem_coe.mpr (Finset.mem_insert_of_mem (Finset.mem_coe.mp hz))
    have hadj : (fromEdgeSet ((insert s(x, y) E0 : Finset (Sym2 V)) : Set (Sym2 V))).Adj x y := by
      rw [fromEdgeSet_adj]
      exact ⟨Finset.mem_coe.mpr (Finset.mem_insert_self _ _), hxy⟩
    have hnr : ¬ (fromEdgeSet (E0 : Set (Sym2 V))).Reachable x y := by
      intro hr
      apply hbr x y heE
      refine hr.mono (fromEdgeSet_mono ?_)
      intro z hz
      rw [Finset.mem_coe, Finset.mem_erase]
      refine ⟨?_, hE0 (Finset.mem_coe.mp hz)⟩
      rintro rfl
      exact he (Finset.mem_coe.mp hz)
    have hdx : ∀ a b, (fromEdgeSet (E0 : Set (Sym2 V))).Adj x a →
        (fromEdgeSet (E0 : Set (Sym2 V))).Adj x b → a = b := by
      intro a b ha hb
      rw [fromEdgeSet_adj] at ha hb
      have ha' : s(x, a) ∈ E0 := Finset.mem_coe.mp ha.1
      have hb' : s(x, b) ∈ E0 := Finset.mem_coe.mp hb.1
      rcases hdeg x a b y (hE0 ha') (hE0 hb') heE with h | h | h
      · exact h
      · exact (he (h ▸ ha')).elim
      · exact (he (h ▸ hb')).elim
    have hdy : ∀ a b, (fromEdgeSet (E0 : Set (Sym2 V))).Adj y a →
        (fromEdgeSet (E0 : Set (Sym2 V))).Adj y b → a = b := by
      intro a b ha hb
      rw [fromEdgeSet_adj] at ha hb
      have ha' : s(y, a) ∈ E0 := Finset.mem_coe.mp ha.1
      have hb' : s(y, b) ∈ E0 := Finset.mem_coe.mp hb.1
      have heE' : s(y, x) ∈ E := Sym2.eq_swap ▸ heE
      have he' : s(y, x) ∉ E0 := Sym2.eq_swap ▸ he
      rcases hdeg y a b x (hE0 ha') (hE0 hb') heE' with h | h | h
      · exact h
      · exact (he' (h ▸ ha')).elim
      · exact (he' (h ▸ hb')).elim
    obtain ⟨s1, hs1P, hxs1⟩ : ∃ s ∈ P0, x ∈ s := by
      have := hcov (Finset.mem_univ x)
      rw [Finset.mem_biUnion] at this
      exact this
    obtain ⟨s2, hs2P, hys2⟩ : ∃ s ∈ P0, y ∈ s := by
      have := hcov (Finset.mem_univ y)
      rw [Finset.mem_biUnion] at this
      exact this
    obtain ⟨u1, v1, p1, hp1, hs1eq⟩ := hpaths s1 hs1P
    obtain ⟨u2, v2, p2, hp2, hs2eq⟩ := hpaths s2 hs2P
    have hx1 : x ∈ p1.support := by
      rw [hs1eq] at hxs1
      exact List.mem_toFinset.mp hxs1
    have hy2 : y ∈ p2.support := by
      rw [hs2eq] at hys2
      exact List.mem_toFinset.mp hys2
    have hs12 : s1 ≠ s2 := by
      intro h
      apply hnr
      have hy1 : y ∈ p1.support := by
        rw [← h, hs1eq] at hys2
        exact List.mem_toFinset.mp hys2
      exact p1_reachable_of_mem_support p1 hx1 hy1
    have hd12 : Disjoint s1 s2 := hdisj s1 hs1P s2 hs2P hs12
    obtain ⟨z1, q1, hq1, hq1s⟩ := p1_path_to_end p1 hp1 x hx1 hdx
    obtain ⟨z2, q2, hq2, hq2s⟩ := p1_path_to_end p2 hp2 y hy2 hdy
    rw [← hs1eq] at hq1s
    rw [← hs2eq] at hq2s
    let w := (q1.mapLe hle).append (Walk.cons hadj (q2.mapLe hle).reverse)
    have hwsupp : w.support = q1.support ++ q2.support.reverse := by
      simp only [w, Walk.support_append, Walk.support_cons, List.tail_cons, Walk.support_reverse,
        Walk.support_mapLe_eq_support]
    have hwpath : w.IsPath := by
      rw [Walk.isPath_def, hwsupp, List.nodup_append]
      refine ⟨hq1.support_nodup, List.nodup_reverse.mpr hq2.support_nodup, ?_⟩
      intro a ha b hb hab
      subst hab
      have h1 : a ∈ s1 := by
        rw [← hq1s]
        exact List.mem_toFinset.mpr ha
      have h2 : a ∈ s2 := by
        rw [← hq2s]
        exact List.mem_toFinset.mpr (List.mem_reverse.mp hb)
      exact Finset.disjoint_left.mp hd12 h1 h2
    have hwfin : s1 ∪ s2 = w.support.toFinset := by
      rw [hwsupp, List.toFinset_append, List.toFinset_reverse, hq1s, hq2s]
    have hs2P' : s2 ∈ P0.erase s1 := Finset.mem_erase.mpr ⟨fun h => hs12 h.symm, hs2P⟩
    have hnew : s1 ∪ s2 ∉ (P0.erase s1).erase s2 := by
      intro h
      have h3 := Finset.mem_erase.mp h
      have h4 := Finset.mem_erase.mp h3.2
      have hd := hdisj (s1 ∪ s2) h4.2 s1 hs1P h4.1
      exact Finset.disjoint_left.mp hd (Finset.mem_union_left _ hxs1) hxs1
    refine ⟨insert (s1 ∪ s2) ((P0.erase s1).erase s2), ⟨?_, ?_, ?_⟩, ?_⟩
    · have hkey : ∀ t ∈ (P0.erase s1).erase s2, Disjoint (s1 ∪ s2) t := by
        intro t ht
        have h3 := Finset.mem_erase.mp ht
        have h4 := Finset.mem_erase.mp h3.2
        rw [Finset.disjoint_union_left]
        exact ⟨hdisj s1 hs1P t h4.2 (Ne.symm h4.1), hdisj s2 hs2P t h4.2 (Ne.symm h3.1)⟩
      intro t1 ht1 t2 ht2 hne
      rcases Finset.mem_insert.mp ht1 with rfl | ht1'
      · rcases Finset.mem_insert.mp ht2 with rfl | ht2'
        · exact (hne rfl).elim
        · exact hkey t2 ht2'
      · rcases Finset.mem_insert.mp ht2 with rfl | ht2'
        · exact (hkey t1 ht1').symm
        · exact hdisj t1 (Finset.mem_erase.mp (Finset.mem_erase.mp ht1').2).2 t2
            (Finset.mem_erase.mp (Finset.mem_erase.mp ht2').2).2 hne
    · intro a _
      have := hcov (Finset.mem_univ a)
      rw [Finset.mem_biUnion] at this ⊢
      obtain ⟨t, htP, hat⟩ := this
      by_cases ht1 : t = s1
      · exact ⟨s1 ∪ s2, Finset.mem_insert_self _ _, Finset.mem_union_left _ (ht1 ▸ hat)⟩
      · by_cases ht2 : t = s2
        · exact ⟨s1 ∪ s2, Finset.mem_insert_self _ _, Finset.mem_union_right _ (ht2 ▸ hat)⟩
        · exact ⟨t, Finset.mem_insert_of_mem
            (Finset.mem_erase.mpr ⟨ht2, Finset.mem_erase.mpr ⟨ht1, htP⟩⟩), hat⟩
    · intro t ht
      rcases Finset.mem_insert.mp ht with rfl | ht'
      · exact ⟨z1, z2, w, hwpath, hwfin⟩
      · obtain ⟨a, b, p, hp, hpe⟩ := hpaths t (Finset.mem_erase.mp (Finset.mem_erase.mp ht').2).2
        refine ⟨a, b, p.mapLe hle, hp.mapLe hle, ?_⟩
        rw [Walk.support_mapLe_eq_support]
        exact hpe
    · rw [Finset.card_insert_of_notMem hnew, Finset.card_erase_of_mem hs2P',
        Finset.card_erase_of_mem hs1P, Finset.card_insert_of_notMem he]
      have h1 : 0 < P0.card := Finset.card_pos.mpr ⟨s1, hs1P⟩
      have h2 : 0 < (P0.erase s1).card := Finset.card_pos.mpr ⟨s2, hs2P'⟩
      rw [Finset.card_erase_of_mem hs1P] at h2
      omega

/-- Exchange: adding to a subforest an independent set of vertices each having at most one
neighbour in it keeps the induced graph acyclic. -/
private lemma p1_exchange_acyclic {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (U R D : Finset V) (hU : (G.induce (U : Set V)).IsAcyclic) (hRU : R ⊆ U)
    (hDU : ∀ d ∈ D, d ∉ U)
    (hDind : ∀ d ∈ D, ∀ d' ∈ D, ¬ G.Adj d d')
    (hD1 : ∀ d ∈ D, ∀ a ∈ R, ∀ b ∈ R, G.Adj d a → G.Adj d b → a = b) :
    (G.induce ((R ∪ D : Finset V) : Set V)).IsAcyclic := by
  rw [isAcyclic_iff_forall_adj_isBridge]
  have hleaf : ∀ u w : ((R ∪ D : Finset V) : Set V), u.1 ∈ D →
      (G.induce ((R ∪ D : Finset V) : Set V)).Adj u w →
      ¬ ((G.induce ((R ∪ D : Finset V) : Set V)).deleteEdges {s(u, w)}).Reachable u w := by
    intro u w hu hadj hreach
    have hGw : G.Adj u.1 w.1 := hadj
    have hwR : w.1 ∈ R := by
      rcases Finset.mem_union.mp (Finset.mem_coe.mp w.2) with h | h
      · exact h
      · exact (hDind u.1 hu w.1 h hGw).elim
    obtain ⟨p⟩ := hreach
    cases p with
    | nil => exact hGw.ne rfl
    | @cons _ z _ h _ =>
      rw [deleteEdges_adj] at h
      have hGz : G.Adj u.1 z.1 := h.1
      have hzR : z.1 ∈ R := by
        rcases Finset.mem_union.mp (Finset.mem_coe.mp z.2) with h' | h'
        · exact h'
        · exact (hDind u.1 hu z.1 h' hGz).elim
      have hzw : z.1 = w.1 := hD1 u.1 hu z.1 hzR w.1 hwR hGz hGw
      apply h.2
      rw [Set.mem_singleton_iff, Subtype.ext hzw]
  intro u w hadj
  rw [isBridge_iff]
  by_cases hu : u.1 ∈ D
  · exact hleaf u w hu hadj
  by_cases hw : w.1 ∈ D
  · intro hreach
    apply hleaf w u hw hadj.symm
    rw [Sym2.eq_swap]
    exact hreach.symm
  have huR : u.1 ∈ R := (Finset.mem_union.mp (Finset.mem_coe.mp u.2)).resolve_right hu
  have hwR : w.1 ∈ R := (Finset.mem_union.mp (Finset.mem_coe.mp w.2)).resolve_right hw
  have huU : u.1 ∈ U := hRU huR
  have hwU : w.1 ∈ U := hRU hwR
  intro hreach
  classical
  let ψ : ((R ∪ D : Finset V) : Set V) → ((U : Set V)) := fun z =>
    if hz : z.1 ∈ U then ⟨z.1, hz⟩ else
      if hex : ∃ a, a ∈ R ∧ G.Adj z.1 a then ⟨hex.choose, hRU hex.choose_spec.1⟩
      else ⟨u.1, huU⟩
  have hψU : ∀ (z : ((R ∪ D : Finset V) : Set V)) (hz : z.1 ∈ U), ψ z = ⟨z.1, hz⟩ :=
    fun z hz => dif_pos hz
  have hbridge := (isAcyclic_iff_forall_adj_isBridge.mp hU)
    (show (G.induce (U : Set V)).Adj ⟨u.1, huU⟩ ⟨w.1, hwU⟩ from hadj)
  rw [isBridge_iff] at hbridge
  apply hbridge
  have key : ∀ y y' : ((R ∪ D : Finset V) : Set V), G.Adj y.1 y'.1 → y.1 ∉ U → y'.1 ∈ U →
      ψ y = ψ y' := by
    intro y y' hyy hy hy'
    have hyD : y.1 ∈ D := (Finset.mem_union.mp (Finset.mem_coe.mp y.2)).resolve_left
      (fun h => hy (hRU h))
    have hy'R : y'.1 ∈ R := (Finset.mem_union.mp (Finset.mem_coe.mp y'.2)).resolve_right
      (fun h => hDU _ h hy')
    have hex : ∃ a, a ∈ R ∧ G.Adj y.1 a := ⟨y'.1, hy'R, hyy⟩
    rw [hψU y' hy']
    have h1 : ψ y = ⟨hex.choose, hRU hex.choose_spec.1⟩ := by
      dsimp only [ψ]
      rw [dif_neg hy, dif_pos hex]
    rw [h1]
    exact Subtype.ext (hD1 y.1 hyD _ hex.choose_spec.1 _ hy'R hex.choose_spec.2 hyy)
  have hmap := p1_reach_map
    (H := (G.induce (U : Set V)).deleteEdges {s(⟨u.1, huU⟩, ⟨w.1, hwU⟩)}) ψ ?_ hreach
  · rwa [hψU u huU, hψU w hwU] at hmap
  intro z z' hzz
  rw [deleteEdges_adj] at hzz
  obtain ⟨hG, hne⟩ := hzz
  have hG' : G.Adj z.1 z'.1 := hG
  by_cases hz : z.1 ∈ U
  · by_cases hz' : z'.1 ∈ U
    · right
      rw [hψU z hz, hψU z' hz', deleteEdges_adj]
      refine ⟨hG', ?_⟩
      intro hmem
      apply hne
      rw [Set.mem_singleton_iff, Sym2.eq_iff] at hmem ⊢
      rcases hmem with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨Subtype.ext (Subtype.mk.inj h1), Subtype.ext (Subtype.mk.inj h2)⟩
      · exact Or.inr ⟨Subtype.ext (Subtype.mk.inj h1), Subtype.ext (Subtype.mk.inj h2)⟩
    · left
      exact (key z' z hG'.symm hz' hz).symm
  · by_cases hz' : z'.1 ∈ U
    · left
      exact key z z' hG' hz hz'
    · exfalso
      have hzD : z.1 ∈ D := (Finset.mem_union.mp (Finset.mem_coe.mp z.2)).resolve_left
        (fun h => hz (hRU h))
      have hz'D : z'.1 ∈ D := (Finset.mem_union.mp (Finset.mem_coe.mp z'.2)).resolve_left
        (fun h => hz' (hRU h))
      exact hDind _ hzD _ hz'D hG'

/-- The all-but-one Hall condition HP for the neighbourhoods, inside a maximum induced forest
`U`, of the outside vertices of one colour. -/
private lemma p1_hp {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {κ : Type*} [DecidableEq κ] (c : V → κ)
    (hc : ∀ u w, G.Adj u w → c u ≠ c w)
    (U : Finset V) (hU : (G.induce (U : Set V)).IsAcyclic)
    (hmax : ∀ W : Finset V, (G.induce (W : Set V)).IsAcyclic → W.card ≤ U.card) (i : κ)
    (S : Finset V) :
    (Finset.univ.filter (fun t : {t : V // t ∉ U ∧ c t = i} =>
      ((U.filter (fun x => G.Adj t.1 x)) \ S).card ≤ 1)).card ≤ S.card := by
  obtain ⟨D, hD⟩ : ∃ D : Finset V, D = (Finset.univ.filter
      (fun t : {t : V // t ∉ U ∧ c t = i} =>
        ((U.filter (fun x => G.Adj t.1 x)) \ S).card ≤ 1)).image Subtype.val := ⟨_, rfl⟩
  have hDcard : D.card = (Finset.univ.filter (fun t : {t : V // t ∉ U ∧ c t = i} =>
      ((U.filter (fun x => G.Adj t.1 x)) \ S).card ≤ 1)).card := by
    rw [hD]
    exact Finset.card_image_of_injective _ Subtype.val_injective
  have hmem : ∀ d ∈ D, d ∉ U ∧ c d = i ∧ ((U.filter (fun x => G.Adj d x)) \ S).card ≤ 1 := by
    intro d hd
    rw [hD, Finset.mem_image] at hd
    obtain ⟨t, ht, rfl⟩ := hd
    exact ⟨t.2.1, t.2.2, (Finset.mem_filter.mp ht).2⟩
  have hac := p1_exchange_acyclic G U (U \ S) D hU Finset.sdiff_subset
    (fun d hd => (hmem d hd).1)
    (fun d hd d' hd' hadj => hc d d' hadj ((hmem d hd).2.1.trans (hmem d' hd').2.1.symm))
    (fun d hd a ha b hb hda hdb => Finset.card_le_one.mp (hmem d hd).2.2 a
      (Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp ha).1, hda⟩,
        (Finset.mem_sdiff.mp ha).2⟩) b
      (Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hb).1, hdb⟩,
        (Finset.mem_sdiff.mp hb).2⟩))
  have h1 := hmax _ hac
  have hdisj : Disjoint (U \ S) D :=
    Finset.disjoint_left.mpr (fun x hx hxD => (hmem x hxD).1 (Finset.mem_sdiff.mp hx).1)
  rw [Finset.card_union_of_disjoint hdisj] at h1
  have h2 : U.card ≤ (U \ S).card + S.card := by
    rw [Finset.card_sdiff_add_card]
    exact Finset.card_le_card Finset.subset_union_left
  rw [← hDcard]
  omega

/-- One colour side: from Theorem BL, a set of edges between the outside vertices of colour `i` and
the maximum induced forest `U` forming a linear forest with degree two at every such outside
vertex and degree at most one at the prescribed forest vertex `v`. -/
private lemma p1_side {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (c : V → Fin 2) (hc : ∀ u w, G.Adj u w → c u ≠ c w)
    (U : Finset V) (hU : (G.induce (U : Set V)).IsAcyclic)
    (hmax : ∀ W : Finset V, (G.induce (W : Set V)).IsAcyclic → W.card ≤ U.card)
    (i : Fin 2) (x0 x0' : V)
    (hBLG : ∀ x ∈ U, x ≠ x0 → x ≠ x0' → c x ≠ i → ∀ t1 t2 t3 : V, t1 ∉ U → t2 ∉ U → t3 ∉ U → t1 ≠ t2 → t1 ≠ t3 → t2 ≠ t3 →
      G.Adj x t1 → G.Adj x t2 → G.Adj x t3 → ∃ p : V → Prop,
        (∀ s s', s ∉ U → s' ∉ U → p s → ¬ p s' → ∀ z ∈ U, G.Adj s z → G.Adj s' z → z = x) ∧
        ¬ ((p t1 ↔ p t2) ∧ (p t1 ↔ p t3)))
    (hx0 : x0 ∈ U → ∀ t1 t2 t3 t4 : V, t1 ∉ U → t2 ∉ U → t3 ∉ U → t4 ∉ U →
      G.Adj x0 t1 → G.Adj x0 t2 → G.Adj x0 t3 → G.Adj x0 t4 →
      t1 = t2 ∨ t1 = t3 ∨ t1 = t4 ∨ t2 = t3 ∨ t2 = t4 ∨ t3 = t4)
    (hx0' : x0' ∈ U → ∀ t1 t2 t3 t4 : V, t1 ∉ U → t2 ∉ U → t3 ∉ U → t4 ∉ U →
      G.Adj x0' t1 → G.Adj x0' t2 → G.Adj x0' t3 → G.Adj x0' t4 →
      t1 = t2 ∨ t1 = t3 ∨ t1 = t4 ∨ t2 = t3 ∨ t2 = t4 ∨ t3 = t4)
    (v : V) (hvU : v ∈ U) :
    ∃ E : Finset (Sym2 V),
      (∀ p q, s(p, q) ∈ E →
        G.Adj p q ∧ ((p ∉ U ∧ c p = i ∧ q ∈ U) ∨ (q ∉ U ∧ c q = i ∧ p ∈ U))) ∧
      E.card = 2 * (Finset.univ.filter (fun z : V => z ∉ U ∧ c z = i)).card ∧
      (∀ x p q r, s(x, p) ∈ E → s(x, q) ∈ E → s(x, r) ∈ E → p = q ∨ p = r ∨ q = r) ∧
      (∀ p q, s(v, p) ∈ E → s(v, q) ∈ E → p = q) ∧
      (∀ x y, s(x, y) ∈ E →
        ¬ (fromEdgeSet ((E.erase s(x, y) : Finset (Sym2 V)) : Set (Sym2 V))).Reachable x y) := by
  classical
  have hdeg0 : (Finset.univ.filter (fun t : {t : V // t ∉ U ∧ c t = i} =>
      x0 ∈ U.filter (fun x => G.Adj t.1 x))).card ≤ 3 := by
    by_contra hbig
    push Not at hbig
    obtain ⟨s0, hs0⟩ : (Finset.univ.filter (fun t : {t : V // t ∉ U ∧ c t = i} =>
        x0 ∈ U.filter (fun x => G.Adj t.1 x))).Nonempty := Finset.card_pos.mp (by omega)
    have hlt : 2 < ((Finset.univ.filter (fun t : {t : V // t ∉ U ∧ c t = i} =>
        x0 ∈ U.filter (fun x => G.Adj t.1 x))).erase s0).card := by
      rw [Finset.card_erase_of_mem hs0]; omega
    obtain ⟨s1, hs1, s2, hs2, s3, hs3, h12, h13, h23⟩ := Finset.two_lt_card.mp hlt
    have adj : ∀ s ∈ Finset.univ.filter (fun t : {t : V // t ∉ U ∧ c t = i} =>
        x0 ∈ U.filter (fun x => G.Adj t.1 x)), G.Adj x0 s.1 := by
      intro s hs
      exact ((Finset.mem_filter.mp (Finset.mem_filter.mp hs).2).2).symm
    have e1 := Finset.ne_of_mem_erase hs1
    have e2 := Finset.ne_of_mem_erase hs2
    have e3 := Finset.ne_of_mem_erase hs3
    have f1 := Finset.mem_of_mem_erase hs1
    have f2 := Finset.mem_of_mem_erase hs2
    have f3 := Finset.mem_of_mem_erase hs3
    rcases hx0 (Finset.mem_filter.mp (Finset.mem_filter.mp hs0).2).1 s0.1 s1.1 s2.1 s3.1 s0.2.1 s1.2.1 s2.2.1 s3.2.1 (adj s0 hs0) (adj s1 f1)
      (adj s2 f2) (adj s3 f3) with h | h | h | h | h | h
    · exact e1 (Subtype.ext h).symm
    · exact e2 (Subtype.ext h).symm
    · exact e3 (Subtype.ext h).symm
    · exact h12 (Subtype.ext h)
    · exact h13 (Subtype.ext h)
    · exact h23 (Subtype.ext h)
  have hdeg0' : (Finset.univ.filter (fun t : {t : V // t ∉ U ∧ c t = i} =>
      x0' ∈ U.filter (fun x => G.Adj t.1 x))).card ≤ 3 := by
    by_contra hbig
    push Not at hbig
    obtain ⟨s0, hs0⟩ : (Finset.univ.filter (fun t : {t : V // t ∉ U ∧ c t = i} =>
        x0' ∈ U.filter (fun x => G.Adj t.1 x))).Nonempty := Finset.card_pos.mp (by omega)
    have hlt : 2 < ((Finset.univ.filter (fun t : {t : V // t ∉ U ∧ c t = i} =>
        x0' ∈ U.filter (fun x => G.Adj t.1 x))).erase s0).card := by
      rw [Finset.card_erase_of_mem hs0]; omega
    obtain ⟨s1, hs1, s2, hs2, s3, hs3, h12, h13, h23⟩ := Finset.two_lt_card.mp hlt
    have adj : ∀ s ∈ Finset.univ.filter (fun t : {t : V // t ∉ U ∧ c t = i} =>
        x0' ∈ U.filter (fun x => G.Adj t.1 x)), G.Adj x0' s.1 := by
      intro s hs
      exact ((Finset.mem_filter.mp (Finset.mem_filter.mp hs).2).2).symm
    have e1 := Finset.ne_of_mem_erase hs1
    have e2 := Finset.ne_of_mem_erase hs2
    have e3 := Finset.ne_of_mem_erase hs3
    have f1 := Finset.mem_of_mem_erase hs1
    have f2 := Finset.mem_of_mem_erase hs2
    have f3 := Finset.mem_of_mem_erase hs3
    rcases hx0' (Finset.mem_filter.mp (Finset.mem_filter.mp hs0).2).1 s0.1 s1.1 s2.1 s3.1 s0.2.1 s1.2.1 s2.2.1 s3.2.1 (adj s0 hs0) (adj s1 f1)
      (adj s2 f2) (adj s3 f3) with h | h | h | h | h | h
    · exact e1 (Subtype.ext h).symm
    · exact e2 (Subtype.ext h).symm
    · exact e3 (Subtype.ext h).symm
    · exact h12 (Subtype.ext h)
    · exact h13 (Subtype.ext h)
    · exact h23 (Subtype.ext h)
  obtain ⟨e, he1, hinj, hacyc, hdeg, hv⟩ := BL2_R3form
    (fun t : {t : V // t ∉ U ∧ c t = i} => U.filter (fun x => G.Adj t.1 x)) x0 x0'
    (p1_hp G c hc U hU hmax i) (by
      intro b hbx0 hbx0' t1 t2 t3 h12 h13 h23 hb1 hb2 hb3
      have m1 : b ∈ U ∧ G.Adj t1.1 b := Finset.mem_filter.mp hb1
      have m2 : b ∈ U ∧ G.Adj t2.1 b := Finset.mem_filter.mp hb2
      have m3 : b ∈ U ∧ G.Adj t3.1 b := Finset.mem_filter.mp hb3
      have hcb : c b ≠ i := fun e => hc t1.1 b m1.2 (t1.2.2.trans e.symm)
      obtain ⟨p, hsep, hns⟩ := hBLG b m1.1 hbx0 hbx0' hcb t1.1 t2.1 t3.1 t1.2.1 t2.2.1 t3.2.1
        (fun h => h12 (Subtype.ext h)) (fun h => h13 (Subtype.ext h)) (fun h => h23 (Subtype.ext h))
        m1.2.symm m2.2.symm m3.2.symm
      refine ⟨fun s => p s.1, fun s s' hs hs' => ?_, hns⟩
      intro z hz
      have z1 : z ∈ U ∧ G.Adj s.1 z := Finset.mem_filter.mp (Finset.mem_inter.mp hz).1
      have z2 : z ∈ U ∧ G.Adj s'.1 z := Finset.mem_filter.mp (Finset.mem_inter.mp hz).2
      exact Finset.mem_singleton.mpr (hsep s.1 s'.1 s.2.1 s'.2.1 hs hs' z z1.1 z1.2 z2.2)) hdeg0 hdeg0' v
  obtain ⟨Pg, hPg⟩ : ∃ Pg : SimpleGraph V, Pg = SimpleGraph.fromRel
      (fun x y : V => ∃ t : {t : V // t ∉ U ∧ c t = i}, e t = (x, y)) := ⟨_, rfl⟩
  rw [← hPg] at hacyc hdeg hv
  let X : {t : V // t ∉ U ∧ c t = i} → Bool → V := fun t k => cond k (e t).1 (e t).2
  have hXU : ∀ t k, X t k ∈ U := by
    intro t k
    cases k
    · exact (Finset.mem_filter.mp (he1 t).2.1).1
    · exact (Finset.mem_filter.mp (he1 t).1).1
  have hXadj : ∀ t k, G.Adj t.1 (X t k) := by
    intro t k
    cases k
    · exact (Finset.mem_filter.mp (he1 t).2.1).2
    · exact (Finset.mem_filter.mp (he1 t).1).2
  have hXne : ∀ t k, X t k ≠ X t (!k) := by
    intro t k
    cases k
    · exact (he1 t).2.2.symm
    · exact (he1 t).2.2
  have hXP : ∀ t k, Pg.Adj (X t k) (X t (!k)) := by
    intro t k
    rw [hPg, SimpleGraph.fromRel_adj]
    refine ⟨hXne t k, ?_⟩
    cases k
    · exact Or.inr ⟨t, rfl⟩
    · exact Or.inl ⟨t, rfl⟩
  have hXs : ∀ t k, s(X t k, X t (!k)) = s((e t).1, (e t).2) := by
    intro t k
    cases k
    · exact Sym2.eq_swap
    · rfl
  have hfin : ∀ t k t' k', X t k = X t' k' → X t (!k) = X t' (!k') → t = t' := by
    intro t k t' k' h1 h2
    apply hinj
    show s((e t).1, (e t).2) = s((e t').1, (e t').2)
    rw [← hXs t k, ← hXs t' k', h1, h2]
  obtain ⟨E, hEdef⟩ : ∃ E : Finset (Sym2 V), E = (Finset.univ :
      Finset ({t : V // t ∉ U ∧ c t = i} × Bool)).image
        (fun tk => s(tk.1.1, X tk.1 tk.2)) := ⟨_, rfl⟩
  have hE : ∀ p q, s(p, q) ∈ E → ∃ t k, (p = t.1 ∧ q = X t k) ∨ (q = t.1 ∧ p = X t k) := by
    intro p q h
    rw [hEdef] at h
    obtain ⟨⟨t, k⟩, _, htk⟩ := Finset.mem_image.mp h
    rw [Sym2.eq_iff] at htk
    rcases htk with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨t, k, Or.inl ⟨h1.symm, h2.symm⟩⟩
    · exact ⟨t, k, Or.inr ⟨h1.symm, h2.symm⟩⟩
  have hEU : ∀ x p, x ∈ U → s(x, p) ∈ E → ∃ t k, p = t.1 ∧ x = X t k := by
    intro x p hx h
    obtain ⟨t, k, h' | h'⟩ := hE x p h
    · exact (t.2.1 (h'.1 ▸ hx)).elim
    · exact ⟨t, k, h'⟩
  have hEN : ∀ x p, x ∉ U → s(x, p) ∈ E → ∃ t k, x = t.1 ∧ p = X t k := by
    intro x p hx h
    obtain ⟨t, k, h' | h'⟩ := hE x p h
    · exact ⟨t, k, h'⟩
    · exact (hx (h'.2 ▸ hXU t k)).elim
  have hbool : ∀ k k' : Bool, k ≠ k' → k' = !k := by decide
  refine ⟨E, ?_, ?_, ?_, ?_, ?_⟩
  · intro p q h
    obtain ⟨t, k, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := hE p q h
    · exact ⟨hXadj t k, Or.inl ⟨t.2.1, t.2.2, hXU t k⟩⟩
    · exact ⟨(hXadj t k).symm, Or.inr ⟨t.2.1, t.2.2, hXU t k⟩⟩
  · rw [hEdef, Finset.card_image_of_injective, Finset.card_univ, Fintype.card_prod,
      Fintype.card_bool, Fintype.card_subtype, Nat.mul_comm]
    rintro ⟨t, k⟩ ⟨t', k'⟩ h
    simp only at h
    rw [Sym2.eq_iff] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have htt : t = t' := Subtype.ext h1
      subst htt
      have hkk : k = k' := by
        by_contra hne
        have hk' : k' = !k := hbool k k' hne
        rw [hk'] at h2
        exact hXne t k h2
      rw [hkk]
    · exact (t.2.1 (h1 ▸ hXU t' k')).elim
  · intro x p q r hp hq hr
    by_cases hx : x ∈ U
    · obtain ⟨tp, kp, hp1, hp2⟩ := hEU x p hx hp
      obtain ⟨tq, kq, hq1, hq2⟩ := hEU x q hx hq
      obtain ⟨tr, kr, hr1, hr2⟩ := hEU x r hx hr
      have hap : Pg.Adj x (X tp (!kp)) := by
        rw [hp2]
        exact hXP tp kp
      have haq : Pg.Adj x (X tq (!kq)) := by
        rw [hq2]
        exact hXP tq kq
      have har : Pg.Adj x (X tr (!kr)) := by
        rw [hr2]
        exact hXP tr kr
      rcases hdeg x _ _ _ hap haq har with h | h | h
      · left
        rw [hp1, hq1, hfin tp kp tq kq (hp2.symm.trans hq2) h]
      · right
        left
        rw [hp1, hr1, hfin tp kp tr kr (hp2.symm.trans hr2) h]
      · right
        right
        rw [hq1, hr1, hfin tq kq tr kr (hq2.symm.trans hr2) h]
    · obtain ⟨tp, kp, hp1, hp2⟩ := hEN x p hx hp
      obtain ⟨tq, kq, hq1, hq2⟩ := hEN x q hx hq
      obtain ⟨tr, kr, hr1, hr2⟩ := hEN x r hx hr
      have e1 : tq = tp := Subtype.ext (hq1.symm.trans hp1)
      have e2 : tr = tp := Subtype.ext (hr1.symm.trans hp1)
      rw [e1] at hq2
      rw [e2] at hr2
      rw [hp2, hq2, hr2]
      cases kp <;> cases kq <;> cases kr <;> simp
  · intro p q hp hq
    obtain ⟨tp, kp, hp1, hp2⟩ := hEU v p hvU hp
    obtain ⟨tq, kq, hq1, hq2⟩ := hEU v q hvU hq
    have hap : Pg.Adj v (X tp (!kp)) := by
      rw [hp2]
      exact hXP tp kp
    have haq : Pg.Adj v (X tq (!kq)) := by
      rw [hq2]
      exact hXP tq kq
    rw [hp1, hq1, hfin tp kp tq kq (hp2.symm.trans hq2) (hv _ _ hap haq)]
  · have hbr0 : ∀ (t0 : {t : V // t ∉ U ∧ c t = i}) (k0 : Bool),
        ¬ (fromEdgeSet ((E.erase s(t0.1, X t0 k0) : Finset (Sym2 V)) :
          Set (Sym2 V))).Reachable t0.1 (X t0 k0) := by
      intro t0 k0 hreach
      have hbP := (isAcyclic_iff_forall_adj_isBridge.mp hacyc) (hXP t0 k0)
      rw [isBridge_iff] at hbP
      apply hbP
      let ψ : V → V := fun z =>
        if h : z ∉ U ∧ c z = i then (if z = t0.1 then X t0 (!k0) else X ⟨z, h⟩ true) else z
      have hψT : ∀ t : {t : V // t ∉ U ∧ c t = i},
          ψ t.1 = if t.1 = t0.1 then X t0 (!k0) else X t true := fun t => dif_pos t.2
      have hψU : ∀ z, z ∈ U → ψ z = z := fun z hz => dif_neg (fun h => h.1 hz)
      have hkey : ∀ t k, (t, k) ≠ (t0, k0) →
          (ψ t.1 = ψ (X t k) ∨
            (Pg.deleteEdges {s(X t0 k0, X t0 (!k0))}).Adj (ψ t.1) (ψ (X t k))) := by
        intro t k hne
        rw [hψT t, hψU _ (hXU t k)]
        by_cases ht : t = t0
        · subst ht
          rw [if_pos rfl]
          left
          have hk : k = !k0 := hbool k0 k (fun h => hne (by rw [h]))
          rw [hk]
        · rw [if_neg (fun h => ht (Subtype.ext h))]
          cases k
          · right
            rw [deleteEdges_adj]
            refine ⟨hXP t true, ?_⟩
            intro hmem
            rw [Set.mem_singleton_iff] at hmem
            apply ht
            apply hinj
            show s((e t).1, (e t).2) = s((e t0).1, (e t0).2)
            rw [← hXs t0 k0]
            exact hmem
          · left
            rfl
      have hmap := p1_reach_map (H := Pg.deleteEdges {s(X t0 k0, X t0 (!k0))}) ψ ?_ hreach
      · rw [hψT t0, if_pos rfl, hψU _ (hXU t0 k0)] at hmap
        exact hmap.symm
      intro p q hpq
      rw [fromEdgeSet_adj] at hpq
      obtain ⟨hmem, _⟩ := hpq
      rw [Finset.mem_coe, Finset.mem_erase] at hmem
      obtain ⟨hne2, hin⟩ := hmem
      obtain ⟨t, k, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := hE p q hin
      · apply hkey t k
        intro h
        apply hne2
        rw [(Prod.mk.inj h).1, (Prod.mk.inj h).2]
      · have h3 := hkey t k (by
          intro h
          apply hne2
          rw [(Prod.mk.inj h).1, (Prod.mk.inj h).2, Sym2.eq_swap])
        rcases h3 with h3 | h3
        · exact Or.inl h3.symm
        · exact Or.inr h3.symm
    intro x y hxy
    obtain ⟨t, k, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := hE x y hxy
    · exact hbr0 t k
    · intro h
      rw [Sym2.eq_swap] at h
      exact hbr0 t k h.symm

/-- The two one-sided linear forests and one edge of the maximum induced forest `U` form a linear
forest with `2 (n - f) + 1` edges, hence a path cover with `2 f - n - 1` paths, as soon as the
outside neighbourhoods of `U` are in the block class. -/
private lemma k2_bipartite_core {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hconn : G.Connected) (hn : 1 < Fintype.card V) (c : V → Fin 2)
    (hc : ∀ u w, G.Adj u w → c u ≠ c w) (U : Finset V) (hU : (G.induce (U : Set V)).IsAcyclic)
    (hUcard : U.card = G.largestInducedForestSize)
    (hside : ∀ i : Fin 2, ∃ x0 x0' : V, (∀ x ∈ U, x ≠ x0 → x ≠ x0' → c x ≠ i → ∀ t1 t2 t3 : V, t1 ∉ U → t2 ∉ U → t3 ∉ U → t1 ≠ t2 → t1 ≠ t3 → t2 ≠ t3 →
        G.Adj x t1 → G.Adj x t2 → G.Adj x t3 → ∃ p : V → Prop,
          (∀ s s', s ∉ U → s' ∉ U → p s → ¬ p s' → ∀ z ∈ U, G.Adj s z → G.Adj s' z → z = x) ∧
          ¬ ((p t1 ↔ p t2) ∧ (p t1 ↔ p t3))) ∧
      (x0 ∈ U → ∀ t1 t2 t3 t4 : V, t1 ∉ U → t2 ∉ U → t3 ∉ U → t4 ∉ U →
        G.Adj x0 t1 → G.Adj x0 t2 → G.Adj x0 t3 → G.Adj x0 t4 →
        t1 = t2 ∨ t1 = t3 ∨ t1 = t4 ∨ t2 = t3 ∨ t2 = t4 ∨ t3 = t4) ∧ (x0' ∈ U → ∀ t1 t2 t3 t4 : V, t1 ∉ U → t2 ∉ U → t3 ∉ U → t4 ∉ U →
        G.Adj x0' t1 → G.Adj x0' t2 → G.Adj x0' t3 → G.Adj x0' t4 →
        t1 = t2 ∨ t1 = t3 ∨ t1 = t4 ∨ t2 = t3 ∨ t2 = t4 ∨ t3 = t4)) :
    G.pathCoverNumber + Fintype.card V + 1 ≤ 2 * G.largestInducedForestSize := by
  classical
  have hmax : ∀ W : Finset V, (G.induce (W : Set V)).IsAcyclic → W.card ≤ U.card := by
    intro W hW
    rw [hUcard]
    exact ncvr_card_le_largestInducedForestSize G W hW
  obtain ⟨a, haU, b, hbU, hab⟩ : ∃ a ∈ U, ∃ b ∈ U, G.Adj a b := by
    by_contra hno
    push Not at hno
    have := indep_add_one_le_forest G hconn hn U hno
    omega
  have hcab : c a ≠ c b := hc a b hab
  have hfin2 : ∀ x y z : Fin 2, y ≠ z → x = y ∨ x = z := by decide
  have hpig : ∀ z, c z = c a ∨ c z = c b := fun z => hfin2 (c z) (c a) (c b) hcab
  have hfin2' : ∀ x y z : Fin 2, x ≠ z → y ≠ z → x = y := by decide
  obtain ⟨y0, y0', hy0, hy0d, hy0d'⟩ := hside (c b)
  obtain ⟨y1, y1', hy1, hy1d, hy1d'⟩ := hside (c a)
  obtain ⟨E0, h0form, h0card, h0deg, h0v, h0br⟩ := p1_side G c hc U hU hmax (c b) y0 y0' hy0 hy0d hy0d' a haU
  obtain ⟨E1, h1form, h1card, h1deg, h1v, h1br⟩ := p1_side G c hc U hU hmax (c a) y1 y1' hy1 hy1d hy1d' b hbU
  obtain ⟨s0, hs0⟩ : ∃ s0 : V → Prop, s0 = fun z => (z ∈ U ↔ c z = c a) := ⟨_, rfl⟩
  have hs0a : s0 a := by
    rw [hs0]
    exact ⟨fun _ => rfl, fun _ => haU⟩
  have hs0b : ¬ s0 b := by
    rw [hs0]
    intro h
    exact hcab (h.mp hbU).symm
  have h0side : ∀ p q, s(p, q) ∈ E0 → s0 p ∧ s0 q := by
    have key : ∀ p q, G.Adj p q → p ∉ U → c p = c b → q ∈ U → s0 p ∧ s0 q := by
      intro p q hadj hp hcp hq
      rw [hs0]
      refine ⟨⟨fun h => (hp h).elim, fun h => (hcab (h.symm.trans hcp)).elim⟩,
        ⟨fun _ => ?_, fun _ => hq⟩⟩
      rcases hpig q with h | h
      · exact h
      · exact (hc p q hadj (hcp.trans h.symm)).elim
    intro p q h
    obtain ⟨hadj, ⟨hp, hcp, hq⟩ | ⟨hq, hcq, hp⟩⟩ := h0form p q h
    · exact key p q hadj hp hcp hq
    · exact (key q p hadj.symm hq hcq hp).symm
  have h1side : ∀ p q, s(p, q) ∈ E1 → ¬ s0 p ∧ ¬ s0 q := by
    have key : ∀ p q, G.Adj p q → p ∉ U → c p = c a → q ∈ U → ¬ s0 p ∧ ¬ s0 q := by
      intro p q hadj hp hcp hq
      rw [hs0]
      refine ⟨fun h => hp (h.mpr hcp), fun h => ?_⟩
      exact hc p q hadj (hcp.trans (h.mp hq).symm)
    intro p q h
    obtain ⟨hadj, ⟨hp, hcp, hq⟩ | ⟨hq, hcq, hp⟩⟩ := h1form p q h
    · exact key p q hadj hp hcp hq
    · exact (key q p hadj.symm hq hcq hp).symm
  obtain ⟨E, hEdef⟩ : ∃ E : Finset (Sym2 V), E = insert s(a, b) (E0 ∪ E1) := ⟨_, rfl⟩
  have hEcases : ∀ p q, s(p, q) ∈ E → s(p, q) = s(a, b) ∨ s(p, q) ∈ E0 ∨ s(p, q) ∈ E1 := by
    intro p q h
    rw [hEdef, Finset.mem_insert, Finset.mem_union] at h
    exact h
  have hab_cases : ∀ p q, s(p, q) = s(a, b) → (p = a ∧ q = b) ∨ (p = b ∧ q = a) := by
    intro p q h
    exact Sym2.eq_iff.mp h
  have hEadj : ∀ p q, s(p, q) ∈ E → G.Adj p q := by
    intro p q h
    rcases hEcases p q h with h | h | h
    · rcases hab_cases p q h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hab
      · exact hab.symm
    · exact (h0form p q h).1
    · exact (h1form p q h).1
  have hnab : s(a, b) ∉ E0 ∪ E1 := by
    intro h
    rcases Finset.mem_union.mp h with h | h
    · exact hs0b (h0side a b h).2
    · exact (h1side a b h).1 hs0a
  have hdisj01 : Disjoint E0 E1 := by
    rw [Finset.disjoint_left]
    intro z
    induction z using Sym2.ind with
    | _ p q =>
      intro h0 h1
      exact (h1side p q h1).1 (h0side p q h0).1
  have hEcard : E.card = 1 + E0.card + E1.card := by
    rw [hEdef, Finset.card_insert_of_notMem hnab, Finset.card_union_of_disjoint hdisj01]
    omega
  have hcount : (Finset.univ.filter (fun z : V => z ∉ U ∧ c z = c b)).card +
      (Finset.univ.filter (fun z : V => z ∉ U ∧ c z = c a)).card = Fintype.card V - U.card := by
    rw [← Finset.card_compl, ← Finset.card_union_of_disjoint]
    · congr 1
      ext z
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_compl]
      constructor
      · rintro (h | h)
        · exact h.1
        · exact h.1
      · intro h
        rcases hpig z with h' | h'
        · exact Or.inr ⟨h, h'⟩
        · exact Or.inl ⟨h, h'⟩
    · rw [Finset.disjoint_left]
      intro z h1 h2
      exact hcab ((Finset.mem_filter.mp h2).2.2.symm.trans (Finset.mem_filter.mp h1).2.2)
  have hdegE : ∀ x p q r, s(x, p) ∈ E → s(x, q) ∈ E → s(x, r) ∈ E → p = q ∨ p = r ∨ q = r := by
    have hgen : ∀ (E' : Finset (Sym2 V)) (x : V),
        (∀ p q r, s(x, p) ∈ E' → s(x, q) ∈ E' → s(x, r) ∈ E' → p = q ∨ p = r ∨ q = r) →
        (∀ p, s(x, p) = s(a, b) → ∀ q r, s(x, q) ∈ E' → s(x, r) ∈ E' → q = r) →
        ∀ p q r, (s(x, p) = s(a, b) ∨ s(x, p) ∈ E') → (s(x, q) = s(a, b) ∨ s(x, q) ∈ E') →
          (s(x, r) = s(a, b) ∨ s(x, r) ∈ E') → p = q ∨ p = r ∨ q = r := by
      intro E' x hd hv' p q r hp hq hr
      rcases hp with hp | hp <;> rcases hq with hq | hq <;> rcases hr with hr | hr
      · exact Or.inl (Sym2.congr_right.mp (hp.trans hq.symm))
      · exact Or.inl (Sym2.congr_right.mp (hp.trans hq.symm))
      · exact Or.inr (Or.inl (Sym2.congr_right.mp (hp.trans hr.symm)))
      · exact Or.inr (Or.inr (hv' p hp q r hq hr))
      · exact Or.inr (Or.inr (Sym2.congr_right.mp (hq.trans hr.symm)))
      · exact Or.inr (Or.inl (hv' q hq p r hp hr))
      · exact Or.inl (hv' r hr p q hp hq)
      · exact hd p q r hp hq hr
    intro x p q r hp hq hr
    by_cases hx : s0 x
    · have hconv : ∀ p, s(x, p) ∈ E → s(x, p) = s(a, b) ∨ s(x, p) ∈ E0 := by
        intro p h
        rcases hEcases x p h with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · exact ((h1side x p h).1 hx).elim
      refine hgen E0 x (h0deg x) ?_ p q r (hconv p hp) (hconv q hq) (hconv r hr)
      intro p' hp' q' r' hq' hr'
      have hxa : x = a := by
        rcases hab_cases x p' hp' with ⟨h, _⟩ | ⟨h, _⟩
        · exact h
        · exact (hs0b (h ▸ hx)).elim
      rw [hxa] at hq' hr'
      exact h0v q' r' hq' hr'
    · have hconv : ∀ p, s(x, p) ∈ E → s(x, p) = s(a, b) ∨ s(x, p) ∈ E1 := by
        intro p h
        rcases hEcases x p h with h | h | h
        · exact Or.inl h
        · exact (hx (h0side x p h).1).elim
        · exact Or.inr h
      refine hgen E1 x (h1deg x) ?_ p q r (hconv p hp) (hconv q hq) (hconv r hr)
      intro p' hp' q' r' hq' hr'
      have hxb : x = b := by
        rcases hab_cases x p' hp' with ⟨h, _⟩ | ⟨h, _⟩
        · exact (hx (h ▸ hs0a)).elim
        · exact h
      rw [hxb] at hq' hr'
      exact h1v q' r' hq' hr'
  have hbrE : ∀ x y, s(x, y) ∈ E →
      ¬ (fromEdgeSet ((E.erase s(x, y) : Finset (Sym2 V)) : Set (Sym2 V))).Reachable x y := by
    intro x y hxy hreach
    have hedge : ∀ p q, (fromEdgeSet ((E.erase s(x, y) : Finset (Sym2 V)) :
        Set (Sym2 V))).Adj p q →
        s(p, q) ≠ s(x, y) ∧ p ≠ q ∧ (s(p, q) = s(a, b) ∨ s(p, q) ∈ E0 ∨ s(p, q) ∈ E1) := by
      intro p q hpq
      rw [fromEdgeSet_adj, Finset.mem_coe, Finset.mem_erase] at hpq
      exact ⟨hpq.1.1, hpq.2, hEcases p q hpq.1.2⟩
    rcases hEcases x y hxy with h | h | h
    · have hmap := p1_reach_map (H := (⊥ : SimpleGraph Prop)) s0 ?_ hreach
      · rw [reachable_bot] at hmap
        rcases hab_cases x y h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hs0b (hmap ▸ hs0a)
        · exact hs0b (hmap.symm ▸ hs0a)
      intro p q hpq
      left
      obtain ⟨hne, _, h' | h' | h'⟩ := hedge p q hpq
      · exact (hne (h'.trans h.symm)).elim
      · exact propext ⟨fun _ => (h0side p q h').2, fun _ => (h0side p q h').1⟩
      · exact propext ⟨fun hp => ((h1side p q h').1 hp).elim, fun hq => ((h1side p q h').2 hq).elim⟩
    · apply h0br x y h
      have hmap := p1_reach_map
        (H := fromEdgeSet ((E0.erase s(x, y) : Finset (Sym2 V)) : Set (Sym2 V)))
        (fun z => if s0 z then z else a) ?_ hreach
      · simp only [if_pos (h0side x y h).1, if_pos (h0side x y h).2] at hmap
        exact hmap
      intro p q hpq
      obtain ⟨hne, hpq', h' | h' | h'⟩ := hedge p q hpq
      · left
        rcases hab_cases p q h' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · simp only [if_pos hs0a, if_neg hs0b]
        · simp only [if_pos hs0a, if_neg hs0b]
      · right
        simp only [if_pos (h0side p q h').1, if_pos (h0side p q h').2]
        rw [fromEdgeSet_adj, Finset.mem_coe, Finset.mem_erase]
        exact ⟨⟨hne, h'⟩, hpq'⟩
      · left
        simp only [if_neg (h1side p q h').1, if_neg (h1side p q h').2]
    · apply h1br x y h
      have hmap := p1_reach_map
        (H := fromEdgeSet ((E1.erase s(x, y) : Finset (Sym2 V)) : Set (Sym2 V)))
        (fun z => if s0 z then b else z) ?_ hreach
      · simp only [if_neg (h1side x y h).1, if_neg (h1side x y h).2] at hmap
        exact hmap
      intro p q hpq
      obtain ⟨hne, hpq', h' | h' | h'⟩ := hedge p q hpq
      · left
        rcases hab_cases p q h' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · simp only [if_pos hs0a, if_neg hs0b]
        · simp only [if_pos hs0a, if_neg hs0b]
      · left
        simp only [if_pos (h0side p q h').1, if_pos (h0side p q h').2]
      · right
        simp only [if_neg (h1side p q h').1, if_neg (h1side p q h').2]
        rw [fromEdgeSet_adj, Finset.mem_coe, Finset.mem_erase]
        exact ⟨⟨hne, h'⟩, hpq'⟩
  obtain ⟨P, hP, hPcard⟩ := p1_linear_forest_cover E
    (fun x y h => (hEadj x y h).ne) hdegE hbrE
  have hle : fromEdgeSet (E : Set (Sym2 V)) ≤ G := by
    intro p q h
    rw [fromEdgeSet_adj] at h
    exact hEadj p q (Finset.mem_coe.mp h.1)
  have hpc : G.pathCoverNumber ≤ P.card := by
    unfold SimpleGraph.pathCoverNumber
    exact Nat.sInf_le ⟨P, rfl, r2_isPathCover_mono hle hP⟩
  have hUle : U.card ≤ Fintype.card V := Finset.card_le_univ U
  omega


private lemma out3_iff {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (U : Finset V)
    (x : V) : Set.ncard {t | t ∉ U ∧ G.Adj x t} ≤ 3 ↔
      ∀ t1 t2 t3 t4 : V, t1 ∉ U → t2 ∉ U → t3 ∉ U → t4 ∉ U →
        G.Adj x t1 → G.Adj x t2 → G.Adj x t3 → G.Adj x t4 →
        t1 = t2 ∨ t1 = t3 ∨ t1 = t4 ∨ t2 = t3 ∨ t2 = t4 ∨ t3 = t4 := by
  classical
  have hS : {t | t ∉ U ∧ G.Adj x t} = ↑(Finset.univ.filter (fun t => t ∉ U ∧ G.Adj x t)) := by
    ext t
    simp
  rw [hS, Set.ncard_coe_finset]
  constructor
  · intro h t1 t2 t3 t4 n1 n2 n3 n4 a1 a2 a3 a4
    by_contra hc
    push Not at hc
    obtain ⟨h12, h13, h14, h23, h24, h34⟩ := hc
    have hsub : ({t1, t2, t3, t4} : Finset V) ⊆ Finset.univ.filter (fun t => t ∉ U ∧ G.Adj x t) := by
      intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl <;> simp [*]
    have h4 : ({t1, t2, t3, t4} : Finset V).card = 4 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair h34]
      · simp [h23, h24]
      · simp [h12, h13, h14]
    have := Finset.card_le_card hsub
    omega
  · intro h
    by_contra hbig
    push Not at hbig
    obtain ⟨s0, hs0⟩ : (Finset.univ.filter (fun t => t ∉ U ∧ G.Adj x t)).Nonempty :=
      Finset.card_pos.mp (by omega)
    have hlt : 2 < ((Finset.univ.filter (fun t => t ∉ U ∧ G.Adj x t)).erase s0).card := by
      rw [Finset.card_erase_of_mem hs0]; omega
    obtain ⟨s1, hs1, s2, hs2, s3, hs3, h12, h13, h23⟩ := Finset.two_lt_card.mp hlt
    have m : ∀ s ∈ Finset.univ.filter (fun t => t ∉ U ∧ G.Adj x t), s ∉ U ∧ G.Adj x s :=
      fun s hs => (Finset.mem_filter.mp hs).2
    have f0 := m s0 hs0
    have f1 := m s1 (Finset.mem_of_mem_erase hs1)
    have f2 := m s2 (Finset.mem_of_mem_erase hs2)
    have f3 := m s3 (Finset.mem_of_mem_erase hs3)
    rcases h s0 s1 s2 s3 f0.1 f1.1 f2.1 f3.1 f0.2 f1.2 f2.2 f3.2 with e | e | e | e | e | e
    · exact Finset.ne_of_mem_erase hs1 e.symm
    · exact Finset.ne_of_mem_erase hs2 e.symm
    · exact Finset.ne_of_mem_erase hs3 e.symm
    · exact h12 e
    · exact h13 e
    · exact h23 e


private lemma two_cover {T : Type} [DecidableEq T] (s : Finset T) (hs : s.card ≤ 2) (d : T) :
    ∃ a b, ∀ y ∈ s, y = a ∨ y = b := by
  by_cases h0 : s = ∅
  · exact ⟨d, d, fun y hy => by simp [h0] at hy⟩
  obtain ⟨a, ha⟩ := Finset.nonempty_of_ne_empty h0
  by_cases h1 : ∃ b ∈ s, b ≠ a
  · obtain ⟨b, hb, hba⟩ := h1
    refine ⟨a, b, fun y hy => ?_⟩
    by_contra hc
    push Not at hc
    have hsub : ({a, b, y} : Finset T) ⊆ s := by
      intro u hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl | rfl <;> assumption
    have h3 : ({a, b, y} : Finset T).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_pair (Ne.symm hc.2)]
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm hba, Ne.symm hc.1⟩
    have := Finset.card_le_card hsub
    omega
  · push Not at h1
    exact ⟨a, a, fun y hy => Or.inl (h1 y hy)⟩

theorem main_H1 : OMA.R_WrittenOnTheWallII_GraphConjecture40_conjecture40_R1_H1_R2_H1_R1.H1 := by
  intro V _ _ G hn hconn h2c hbip hscat _ hS
  classical
  obtain ⟨U, hU, hUc, hD3, hcnt⟩ := hS
  obtain ⟨col⟩ := hbip
  have hc : ∀ u w, G.Adj u w → (fun z => col z) u ≠ (fun z => col z) w := fun u w h => col.valid h
  apply k2_bipartite_core G hconn (by omega) (fun z => col z) hc U hU hUc
  intro i
  obtain ⟨j, hj⟩ : ∃ j : Fin 2, ∀ z : Fin 2, z ≠ i → z = j := by
    revert i; decide
  have hcj := hcnt (fun z => col z) hc j
  have hfs : {y | y ∈ U ∧ (fun z => col z) y = j ∧ ∃ a b d : V, a ∉ U ∧ b ∉ U ∧ d ∉ U ∧ a ≠ b ∧ a ≠ d ∧ b ≠ d ∧
          G.Adj y a ∧ G.Adj y b ∧ G.Adj y d ∧ ∀ p : V → Prop,
            (∀ s r, s ∉ U → r ∉ U → p s → ¬ p r → ∀ z ∈ U, G.Adj s z → G.Adj r z → z = y) →
            (p a ↔ p b) ∧ (p a ↔ p d)} =
      ↑(Finset.univ.filter (fun y => y ∈ U ∧ (fun z => col z) y = j ∧ ∃ a b d : V, a ∉ U ∧ b ∉ U ∧ d ∉ U ∧ a ≠ b ∧ a ≠ d ∧ b ≠ d ∧
          G.Adj y a ∧ G.Adj y b ∧ G.Adj y d ∧ ∀ p : V → Prop,
            (∀ s r, s ∉ U → r ∉ U → p s → ¬ p r → ∀ z ∈ U, G.Adj s z → G.Adj r z → z = y) →
            (p a ↔ p b) ∧ (p a ↔ p d))) := by
    ext y; simp
  rw [hfs, Set.ncard_coe_finset] at hcj
  obtain ⟨x0, x0', hcov⟩ := two_cover _ hcj hconn.nonempty.some
  refine ⟨x0, x0', ?_, fun h => (out3_iff G U x0).mp (hD3 x0 h),
    fun h => (out3_iff G U x0').mp (hD3 x0' h)⟩
  intro x hx h0 h1 hxi t1 t2 t3 n1 n2 n3 d12 d13 d23 a1 a2 a3
  by_contra hno
  push Not at hno
  have hmem : x ∈ Finset.univ.filter (fun y => y ∈ U ∧ (fun z => col z) y = j ∧ ∃ a b d : V, a ∉ U ∧ b ∉ U ∧ d ∉ U ∧ a ≠ b ∧ a ≠ d ∧ b ≠ d ∧
          G.Adj y a ∧ G.Adj y b ∧ G.Adj y d ∧ ∀ p : V → Prop,
            (∀ s r, s ∉ U → r ∉ U → p s → ¬ p r → ∀ z ∈ U, G.Adj s z → G.Adj r z → z = y) →
            (p a ↔ p b) ∧ (p a ↔ p d)) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hx, hj _ hxi, t1, t2, t3, n1, n2, n3, d12, d13, d23, a1, a2, a3, hno⟩
  rcases hcov x hmem with e | e
  · exact h0 e
  · exact h1 e

end

end OMA.W40B0

theorem OMA.solution : OMA.R_WrittenOnTheWallII_GraphConjecture40_conjecture40_R1_H1_R2_H1_R1.H1 :=
  OMA.W40B0.main_H1
