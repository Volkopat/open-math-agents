import FormalConjectures.ErdosProblems.«338»

/-! Restricted order after finite removal, following Shi-Qiang Chen, Quan-Hui Yang and Lilu Zhao. -/

section

/-
The progression used in Lemma 4 of On a Problem of Erdős and Graham Related
to Restricted Order, by Shi-Qiang Chen, Quan-Hui Yang and Lilu Zhao.
For the campaign interface use Erdos338Campaign.kneser_tail_levels.
The proof uses their nested levels with amplified multiplicities.
The last two lemmas justify the new numerical constants.
-/


section

/- Finite Kneser and dense intervals for the Erdős 338 campaign.
Copyright (c) 2023 Mantas Bakšys, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mantas Bakšys, Yaël Dillies

Finite stabilizers and Kneser's addition theorem are adapted from MiscYD,
revision f2f1d413b681dfd7a0f0e8481aee3ab7e0bae7ba. The interval argument
is adapted from Daniel Veljjanoski, Erdős 338, revision a699263, Apache 2.0.
Here density is required only on a cofinal sequence of initial intervals. -/

open Function MulAction
open scoped Pointwise

namespace Finset
variable {ι α : Type*}

section Group
variable [Group α] [DecidableEq α] {s t : Finset α} {a : α}

instance (s : Finset α) : DecidablePred (· ∈ stabilizer α (s : Set α)) :=
  fun a ↦ decidable_of_iff (a ∈ stabilizer α s) (by simp)

def mulStab (s : Finset α) : Finset α := {a ∈ s / s | a • s = s}

@[simp]
lemma mem_mulStab (hs : s.Nonempty) : a ∈ s.mulStab ↔ a • s = s := by
  rw [mulStab, mem_filter, mem_div, and_iff_right_of_imp]
  obtain ⟨b, hb⟩ := hs
  exact fun h ↦ ⟨_, by rw [← h]; exact smul_mem_smul_finset hb, _, hb, mul_div_cancel_right _ _⟩

lemma mulStab_subset_div : s.mulStab ⊆ s / s := filter_subset _ _

lemma mulStab_subset_div_right (ha : a ∈ s) : s.mulStab ⊆ s / {a} := by
  refine fun b hb ↦ mem_div.2 ⟨_, ?_, _, mem_singleton_self _, mul_div_cancel_right _ _⟩
  rw [mem_mulStab ⟨a, ha⟩] at hb
  rw [← hb]
  exact smul_mem_smul_finset ha

@[simp]
lemma coe_mulStab (hs : s.Nonempty) : (s.mulStab : Set α) = stabilizer α (s : Set α) := by
  ext; simp [mem_mulStab hs]

lemma mem_mulStab_iff_subset_smul_finset (hs : s.Nonempty) : a ∈ s.mulStab ↔ s ⊆ a • s := by
  rw [← mem_coe, coe_mulStab hs, SetLike.mem_coe, stabilizer_coe_finset,
    mem_stabilizer_finset_iff_subset_smul_finset]

lemma mem_mulStab_iff_smul_finset_subset (hs : s.Nonempty) : a ∈ s.mulStab ↔ a • s ⊆ s := by
  rw [← mem_coe, coe_mulStab hs, SetLike.mem_coe, stabilizer_coe_finset,
    mem_stabilizer_finset_iff_smul_finset_subset]

lemma mem_mulStab' (hs : s.Nonempty) : a ∈ s.mulStab ↔ ∀ ⦃b⦄, b ∈ s → a • b ∈ s := by
  rw [← mem_coe, coe_mulStab hs, SetLike.mem_coe, stabilizer_coe_finset, mem_stabilizer_finset']

@[simp]
lemma mulStab_empty : mulStab (∅ : Finset α) = ∅ := by simp [mulStab]

@[simp]
lemma mulStab_singleton (a : α) : mulStab ({a} : Finset α) = 1 := by
  simp [mulStab, singleton_one, filter_true_of_mem]

lemma Nonempty.of_mulStab : s.mulStab.Nonempty → s.Nonempty := by
  simp_rw [nonempty_iff_ne_empty, not_imp_not]; rintro rfl; exact mulStab_empty

@[simp]
lemma one_mem_mulStab : (1 : α) ∈ s.mulStab ↔ s.Nonempty :=
  ⟨fun h ↦ Nonempty.of_mulStab ⟨_, h⟩, fun h ↦ (mem_mulStab h).2 <| one_smul _ _⟩

 protected alias ⟨_, Nonempty.one_mem_mulStab⟩ := one_mem_mulStab

lemma Nonempty.mulStab (h : s.Nonempty) : s.mulStab.Nonempty := ⟨_, h.one_mem_mulStab⟩

@[simp]
lemma mulStab_nonempty : s.mulStab.Nonempty ↔ s.Nonempty := ⟨Nonempty.of_mulStab, Nonempty.mulStab⟩

@[simp]
lemma card_mulStab_eq_one : #s.mulStab = 1 ↔ s.mulStab = 1 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h, card_one]⟩
  obtain ⟨a, ha⟩ := card_eq_one.1 h
  rw [ha]
  rw [eq_singleton_iff_nonempty_unique_mem, mulStab_nonempty, ← one_mem_mulStab] at ha
  rw [← ha.2 _ ha.1, singleton_one]

lemma Nonempty.mulStab_nontrivial (h : s.Nonempty) : s.mulStab.Nontrivial ↔ s.mulStab ≠ 1 :=
  nontrivial_iff_ne_singleton h.one_mem_mulStab

lemma subset_mulStab_mul_left (ht : t.Nonempty) : s.mulStab ⊆ (s * t).mulStab := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  simp_rw [subset_iff, mem_mulStab hs, mem_mulStab (hs.mul ht)]
  rintro a h
  rw [← smul_mul_assoc, h]

@[simp]
lemma mulStab_mul (s : Finset α) : s.mulStab * s = s := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · exact mul_empty _
  · simp only [← coe_inj, hs, coe_mul, coe_mulStab, stabilizer_mul_self]

lemma mul_subset_right_iff (ht : t.Nonempty) : s * t ⊆ t ↔ s ⊆ t.mulStab := by
  simp_rw [← smul_eq_mul, ← biUnion_smul_finset, biUnion_subset,
    ← mem_mulStab_iff_smul_finset_subset ht, subset_iff]

lemma mul_subset_right : s ⊆ t.mulStab → s * t ⊆ t := by
  obtain rfl | ht := t.eq_empty_or_nonempty
  · simp
  · exact (mul_subset_right_iff ht).2

lemma smul_mulStab (ha : a ∈ s.mulStab) : a • s.mulStab = s.mulStab := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  rw [← mem_coe, coe_mulStab hs, SetLike.mem_coe] at ha
  rw [← coe_inj, coe_smul_finset, coe_mulStab hs, smul_coe_set ha]

@[simp]
lemma mulStab_mul_mulStab (s : Finset α) : s.mulStab * s.mulStab = s.mulStab := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  · simp_rw [← smul_eq_mul, ← biUnion_smul_finset, biUnion_congr rfl fun _ ↦ smul_mulStab,
      ← sup_eq_biUnion, sup_const hs.mulStab]

lemma inter_mulStab_subset_mulStab_union : s.mulStab ∩ t.mulStab ⊆ (s ∪ t).mulStab := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  obtain rfl | ht := t.eq_empty_or_nonempty
  · simp
  intro x hx
  rw [mem_mulStab (hs.mono subset_union_left), smul_finset_union,
    (mem_mulStab hs).mp (mem_of_mem_inter_left hx),
    (mem_mulStab ht).mp (mem_of_mem_inter_right hx)]

end Group

variable [CommGroup α] [DecidableEq α] {s t : Finset α} {a : α}

lemma mulStab_subset_div_left (ha : a ∈ s) : s.mulStab ⊆ {a} / s := by
  refine fun b hb ↦ mem_div.2 ⟨_, mem_singleton_self _, _, ?_, div_div_cancel _ _⟩
  rw [mem_mulStab ⟨a, ha⟩] at hb
  rwa [← hb, ← inv_smul_mem_iff, smul_eq_mul, inv_mul_eq_div] at ha

lemma subset_mulStab_mul_right (hs : s.Nonempty) : t.mulStab ⊆ (s * t).mulStab := by
  rw [mul_comm]; exact subset_mulStab_mul_left hs

@[simp]
lemma mul_mulStab (s : Finset α) : s * s.mulStab = s := by rw [mul_comm]; exact mulStab_mul _

@[simp]
lemma mul_mulStab_mul_mul_mul_mulStab_mul :
    s * (s * t).mulStab * (t * (s * t).mulStab) = s * t := by
  rw [mul_mul_mul_comm, mulStab_mul_mulStab, mul_mulStab]

lemma smul_finset_mulStab_subset (ha : a ∈ s) : a • s.mulStab ⊆ s :=
  (smul_finset_subset_smul ha).trans s.mul_mulStab.subset

lemma mul_subset_left_iff (hs : s.Nonempty) : s * t ⊆ s ↔ t ⊆ s.mulStab := by
  rw [mul_comm, mul_subset_right_iff hs]

lemma mul_subset_left : t ⊆ s.mulStab → s * t ⊆ s := by rw [mul_comm]; exact mul_subset_right

@[simp]
lemma mulStab_idem (s : Finset α) : s.mulStab.mulStab = s.mulStab := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  rw [← coe_inj, coe_mulStab hs, coe_mulStab hs.mulStab, coe_mulStab hs]
  simp

@[simp]
lemma mulStab_smul (a : α) (s : Finset α) : (a • s).mulStab = s.mulStab := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  · rw [← coe_inj, coe_mulStab hs, coe_mulStab hs.smul_finset, stabilizer_coe_finset,
    stabilizer_coe_finset, stabilizer_smul_eq_right]

lemma mulStab_image_coe_quotient (hs : s.Nonempty) :
    (s.image (↑) : Finset (α ⧸ stabilizer α (s : Set α))).mulStab = 1 := by
  simp_rw [← coe_inj, coe_mulStab (hs.image _), coe_image, coe_one]
  rw [stabilizer_image_coe_quotient, Subgroup.coe_bot, Set.singleton_one]

lemma preimage_image_quotientMk_stabilizer_eq_mul_mulStab (ht : t.Nonempty) (s : Finset α) :
    QuotientGroup.mk ⁻¹' ((Set.image ((↑) : α → α ⧸ (stabilizer α (t : Set α))) s)) = s * t.mulStab := by
  rw [QuotientGroup.preimage_image_mk_eq_mul, coe_mulStab ht, stabilizer_coe_finset]

omit [DecidableEq α] in

lemma preimage_image_quotientMk_mulStabilizer (s : Finset α) :
    QuotientGroup.mk ⁻¹' ((Set.image ((↑) : α → α ⧸ (stabilizer α (s : Set α))) s)) = s := by
  classical
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  · rw [preimage_image_quotientMk_stabilizer_eq_mul_mulStab hs s, ← coe_mul, mul_mulStab]

lemma pairwiseDisjoint_smul_finset_mulStab (s : Finset α) :
    (Set.range fun a : α ↦ a • s.mulStab).PairwiseDisjoint id := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  simp only [onFun, id_eq]
  simp_rw [← disjoint_coe, ← coe_injective.ne_iff, coe_smul_finset, coe_mulStab hs]
  exact fun h ↦ isBlock_subgroup h

lemma disjoint_smul_finset_mulStab_mul_mulStab :
    ¬a • s.mulStab ⊆ t * s.mulStab → Disjoint (a • s.mulStab) (t * s.mulStab) := by
  simp_rw [@not_imp_comm (_ ≤ _), ← smul_eq_mul, ← biUnion_smul_finset, disjoint_biUnion_right,
    Classical.not_forall]
  rintro ⟨b, hb, h⟩
  rw [s.pairwiseDisjoint_smul_finset_mulStab.eq (Set.mem_range_self _) (Set.mem_range_self _) h]
  exact subset_biUnion_of_mem (· • mulStab s) hb

lemma card_mulStab_dvd_card_mul_mulStab (s t : Finset α) : #t.mulStab ∣ #(s * t.mulStab) :=
  card_dvd_card_smul_right <|
    t.pairwiseDisjoint_smul_finset_mulStab.subset <| Set.image_subset_range _ _

lemma card_mulStab_dvd_card (s : Finset α) : #s.mulStab ∣ #s := by
  simpa only [mul_mulStab] using s.card_mulStab_dvd_card_mul_mulStab s

lemma card_mulStab_le_card : #s.mulStab ≤ #s := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · rfl
  · exact Nat.le_of_dvd hs.card_pos s.card_mulStab_dvd_card

private abbrev fintypeStabilizerOfMulStab (hs : s.Nonempty) : Fintype (stabilizer α s) where
  elems := s.mulStab.attach.map
    ⟨Subtype.map id fun _ ↦ (mem_mulStab hs).1, Subtype.map_injective _ injective_id⟩
  complete a := mem_map.2
    ⟨⟨_, (mem_mulStab hs).2 a.2⟩, mem_attach _ ⟨_, (mem_mulStab hs).2 a.2⟩, Subtype.ext rfl⟩

lemma card_mulStab_dvd_card_mulStab (hs : s.Nonempty) (h : s.mulStab ⊆ t.mulStab) :
    #s.mulStab ∣ #t.mulStab := by
  obtain rfl | ht := t.eq_empty_or_nonempty
  · simp
  rw [← coe_subset, coe_mulStab hs, coe_mulStab ht, SetLike.coe_subset_coe] at h
  let : Fintype (stabilizer α s) := fintypeStabilizerOfMulStab hs
  let : Fintype (stabilizer α t) := fintypeStabilizerOfMulStab ht
  convert Subgroup.card_dvd_of_le h using 1
  · simp only [stabilizer_coe_finset, Nat.card_eq_fintype_card]
    change _ = #(s.mulStab.attach.map
    ⟨Subtype.map id fun _ ↦ (mem_mulStab hs).1, Subtype.map_injective _ injective_id⟩)
    simp
  · simp only [stabilizer_coe_finset, Nat.card_eq_fintype_card]
    change _ = #(t.mulStab.attach.map
      ⟨Subtype.map id fun _ ↦ (mem_mulStab ht).1, Subtype.map_injective _ injective_id⟩)
    simp

lemma card_mulStab_mul_card_image_coe' (s t : Finset α)
    [DecidableEq (α ⧸ stabilizer α (t : Set α))] :
    #t.mulStab * #((Finset.image ((↑) : α → α ⧸ (stabilizer α (t : Set α))) s)) = #(s * t.mulStab) := by
  obtain rfl | ht := t.eq_empty_or_nonempty
  · simp
  have := QuotientGroup.preimageMkEquivSubgroupProdSet _ ((Set.image ((↑) : α → α ⧸ (stabilizer α (t : Set α))) s))
  have that : ↥(stabilizer α (t : Set α)) = ↥t.mulStab := by
    rw [← SetLike.coe_sort_coe, ← coe_mulStab ht, Finset.coe_sort_coe]
  have temp := this.trans ((Equiv.cast that).prodCongr (Equiv.refl _))
  rw [preimage_image_quotientMk_stabilizer_eq_mul_mulStab ht] at temp
  simpa only [coe_sort_coe, ← coe_mul, Fintype.card_prod, Fintype.card_coe, Fintype.card_ofFinset,
    toFinset_coe, mem_image, Set.mem_image, mem_coe, forall_const, eq_comm]
    using Fintype.card_congr temp

lemma card_mul_card_eq_mulStab_card_mul_coe (s t : Finset α) :
    #(s * t) = #(s * t).mulStab * #((Finset.image ((↑) : α → α ⧸ (stabilizer α (↑(s * t) : Set α))) (s * t))) := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  obtain rfl | ht := t.eq_empty_or_nonempty
  · simp
  have := QuotientGroup.preimageMkEquivSubgroupProdSet _ <|
    (Set.image ((↑) : α → α ⧸ (stabilizer α (↑(s * t) : Set α))) (↑(s * t) : Set α))
  have that : ↥(stabilizer α (↑(s * t) : Set α)) = ↥(s * t).mulStab := by
    rw [← SetLike.coe_sort_coe, ← coe_mulStab (hs.mul ht), Finset.coe_sort_coe]
  have temp := this.trans <| (Equiv.cast that).prodCongr (Equiv.refl _)
  rw [preimage_image_quotientMk_mulStabilizer] at temp
  simpa [-coe_mul] using Fintype.card_congr temp

lemma card_mulStab_mul_card_image_coe (s t : Finset α) :
    #(s * t).mulStab *
      #(((Finset.image ((↑) : α → α ⧸ (stabilizer α (↑(s * t) : Set α))) s)) * ((Finset.image ((↑) : α → α ⧸ (stabilizer α (↑(s * t) : Set α))) t))) =
        #(s * t) := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  obtain rfl | ht := t.eq_empty_or_nonempty
  · simp
  let this := QuotientGroup.preimageMkEquivSubgroupProdSet (stabilizer α (↑(s * t) : Set α))
    (((Set.image ((↑) : α → α ⧸ (stabilizer α (↑(s * t) : Set α))) s)) * ((Set.image ((↑) : α → α ⧸ (stabilizer α (↑(s * t) : Set α))) t)))
  have image_coe_mul :
    ((Set.image ((↑) : α → α ⧸ (stabilizer α (↑(s * t) : Set α))) (↑(s * t) : Set α))) =
      ((Set.image ((↑) : α → α ⧸ (stabilizer α (↑(s * t) : Set α))) s)) * ((Set.image ((↑) : α → α ⧸ (stabilizer α (↑(s * t) : Set α))) t)) := by
    simpa [coe_mul] using Set.image_mul (QuotientGroup.mk' (stabilizer α (↑(s * t) : Set α)))
  rw [← image_coe_mul, preimage_image_quotientMk_mulStabilizer, image_coe_mul] at this
  have that :
    (stabilizer α (↑(s * t) : Set α) ×
      ↥(((Set.image ((↑) : α → α ⧸ (stabilizer α (↑(s * t) : Set α))) s)) * ((Set.image ((↑) : α → α ⧸ (stabilizer α (↑(s * t) : Set α))) t)))) =
      ((s * t).mulStab ×
        ↥(((Set.image ((↑) : α → α ⧸ (stabilizer α (↑(s * t) : Set α))) s)) * ((Set.image ((↑) : α → α ⧸ (stabilizer α (↑(s * t) : Set α))) t)))) := by
    rw [← SetLike.coe_sort_coe, ← coe_mulStab (hs.mul ht), Finset.coe_sort_coe]
  let temp := this.trans (Equiv.cast that)
  replace temp := Fintype.card_congr temp
  simp only [Fintype.card_prod, Fintype.card_coe] at temp
  have h1 : Fintype.card ((s * t : Finset α) : Set α) = Fintype.card (s * t) := by congr
  have h2 : ((Set.image ((↑) : α → α ⧸ (stabilizer α (↑(s * t) : Set α))) s)) * ((Set.image ((↑) : α → α ⧸ (stabilizer α (↑(s * t) : Set α))) t)) =
    ↑(((Finset.image ((↑) : α → α ⧸ (stabilizer α (↑(s * t) : Set α))) s)) * ((Finset.image ((↑) : α → α ⧸ (stabilizer α (↑(s * t) : Set α))) t))) := by simp
  have h3 :
    Fintype.card (((Set.image ((↑) : α → α ⧸ (stabilizer α (↑(s * t) : Set α))) s)) * ((Set.image ((↑) : α → α ⧸ (stabilizer α (↑(s * t) : Set α))) t))) =
      Fintype.card (((Finset.image ((↑) : α → α ⧸ (stabilizer α (↑(s * t) : Set α))) s)) *
        ((Finset.image ((↑) : α → α ⧸ (stabilizer α (↑(s * t) : Set α))) t))) := by
    simp_rw [h2]
    congr
  simp only [h1, h3, Fintype.card_coe] at temp
  rw [temp]

lemma subgroup_mul_card_eq_mul_of_mul_stab_subset (s : Subgroup α) [DecidablePred (· ∈ s)]
    (t : Finset α) (hst : (s : Set α) ⊆ t.mulStab) : Nat.card s * #((Finset.image ((↑) : α → α ⧸ (s)) t)) = #t := by
  suffices h : (t : Set α) * s = t by
    simpa [h, eq_comm] using s.card_mul_eq_card_subgroup_mul_card_quotient  t
  apply Set.Subset.antisymm (Set.Subset.trans (Set.mul_subset_mul_left hst) _)
  · intro x
    rw [Set.mem_mul]
    aesop
  · rw [← coe_mul, mul_mulStab]

lemma mulStab_quotient_commute_subgroup (s : Subgroup α) [DecidablePred (· ∈ s)] (t : Finset α)
    (hst : (s : Set α) ⊆ t.mulStab) : ((Finset.image ((↑) : α → α ⧸ (s)) t.mulStab)) = ((Finset.image ((↑) : α → α ⧸ (s)) t)).mulStab := by
  obtain rfl | ht := t.eq_empty_or_nonempty
  · simp
  have hti : (image (QuotientGroup.mk (s := s)) t).Nonempty := by aesop
  ext x;
  simp only [mem_image, mem_mulStab hti]
  constructor
  · rintro ⟨a, hax⟩
    rw [← hax.2]
    ext z
    simp only [mem_smul_finset, mem_image, smul_eq_mul, exists_exists_and_eq_and]
    constructor
    · rintro ⟨b, hbt, hbaz⟩
      use (b * a)
      rw [← mul_mulStab t]
      refine ⟨mul_mem_mul hbt hax.1, ?_⟩
      rw [← hbaz, QuotientGroup.mk_mul, mul_comm]
    · rintro ⟨b, hbt, hbz⟩
      rw [← hbz, ← mul_mulStab t, mul_comm]
      use a⁻¹ * b
      refine ⟨mul_mem_mul ?_ hbt, by simp⟩
      rw [← mem_coe, coe_mulStab ht]
      aesop
  · intro hx
    have : s ≤ stabilizer α t := by aesop
    obtain ⟨y, hyx⟩ := Quotient.exists_rep x
    refine ⟨y, (mem_mulStab_iff_subset_smul_finset ht).mpr ?_, by simpa⟩
    intros z hzt
    replace hx : image QuotientGroup.mk (y • t) = image (QuotientGroup.mk (s := s)) t := by
      rw [← hx, ← hyx]
      exact image_smul_comm QuotientGroup.mk y t (congrFun rfl)
    have hyz : QuotientGroup.mk z ∈ image (QuotientGroup.mk (s := s)) (y • t) := by aesop
    simp only [mem_image] at hyz
    obtain ⟨a, ha, hayz⟩ := hyz
    obtain ⟨b, hbt, haby⟩ := mem_smul_finset.mp ha
    subst a
    rw [QuotientGroup.eq, smul_eq_mul] at hayz
    replace : ∃ c ∈ mulStab t, (y • b)⁻¹ * z = c := by aesop
    obtain ⟨c, hct, hcbyz⟩ := this
    rw [inv_mul_eq_iff_eq_mul] at hcbyz
    rw [hcbyz, smul_mul_assoc, mul_comm, ← smul_eq_mul]
    exact smul_mem_smul_finset ((mem_mulStab' ht).mp hct hbt)

end Finset

open Function MulAction
open scoped Pointwise

variable {α : Type*} [CommGroup α] [DecidableEq α] {s s' t t' C : Finset α} {a b : α}

namespace Finset

lemma mulStab_mul_ssubset_mulStab (hs₁ : (s ∩ a • C.mulStab).Nonempty)
    (ht₁ : (t ∩ b • C.mulStab).Nonempty) (hab : ¬(a * b) • C.mulStab ⊆ s * t) :
    (s ∩ a • C.mulStab * (t ∩ b • C.mulStab)).mulStab ⊂ C.mulStab := by
  have hCne : C.Nonempty := by
    contrapose! hab
    simp only [hab, mulStab_empty, smul_finset_empty, empty_subset]
  obtain ⟨x, hx⟩ := hs₁
  obtain ⟨y, hy⟩ := ht₁
  obtain ⟨c, hc, hac⟩ := mem_smul_finset.mp (mem_of_mem_inter_right hx)
  obtain ⟨d, hd, had⟩ := mem_smul_finset.mp (mem_of_mem_inter_right hy)
  have hsubset : (s ∩ a • C.mulStab * (t ∩ b • C.mulStab)).mulStab ⊆ C.mulStab := by
    have hxymem : x * y ∈ s ∩ a • C.mulStab * (t ∩ b • C.mulStab) := mul_mem_mul hx hy
    apply subset_trans (mulStab_subset_div_right hxymem)
    have : s ∩ a • C.mulStab * (t ∩ b • C.mulStab) ⊆ (x * y) • C.mulStab := by
      apply subset_trans (mul_subset_mul inter_subset_right inter_subset_right)
      rw [smul_mul_smul_comm]
      rw [← hac, ← had, smul_mul_smul_comm, smul_assoc]
      apply smul_finset_subset_smul_finset
      rw [← smul_smul]
      rw [mul_subset_iff]
      intro x hx y hy
      rw [smul_mulStab hd, smul_mulStab hc, mem_mulStab hCne, ← smul_smul,
        (mem_mulStab hCne).mp hy, (mem_mulStab hCne).mp hx]
    apply subset_trans (div_subset_div_right this) _
    simp [singleton_mul, div_eq_inv_mul, smul_smul, mul_assoc]
  have : (a * b) • C.mulStab = (a * c * (b * d)) • C.mulStab := by
    rw [smul_eq_iff_eq_inv_smul, ← smul_assoc, smul_eq_mul, mul_assoc, mul_comm c _, ← mul_assoc, ←
      mul_assoc, ← mul_assoc, mul_assoc _ a b, inv_mul_cancel (a * b), one_mul, ← smul_eq_mul,
      smul_assoc, smul_mulStab hc, smul_mulStab hd]
  have hsub : s ∩ a • C.mulStab * (t ∩ b • C.mulStab) ⊆ (a * b) • C.mulStab := by
    apply subset_trans (mul_subset_mul inter_subset_right inter_subset_right)
    simp only [smul_mul_smul_comm, mulStab_mul_mulStab, subset_refl]
  have hxy : x * y ∈ s ∩ a • C.mulStab * (t ∩ b • C.mulStab) := mul_mem_mul hx hy
  rw [this] at hsub
  rw [this] at hab
  obtain ⟨z, hz, hzst⟩ := not_subset.1 hab
  obtain ⟨w, hw, hwz⟩ := mem_smul_finset.mp hz
  refine (Finset.ssubset_iff_of_subset hsubset).mpr ⟨w, hw, ?_⟩
  rw [mem_mulStab' ⟨x * y, hxy⟩]
  push Not
  refine ⟨a * c * (b * d), by simp_all, ?_⟩
  rw [smul_eq_mul, mul_comm w, ← smul_eq_mul (b := w), hwz]
  exact notMem_mono (mul_subset_mul inter_subset_left inter_subset_left) hzst

lemma mulStab_union (hs₁ : (s ∩ a • C.mulStab).Nonempty) (ht₁ : (t ∩ b • C.mulStab).Nonempty)
    (hab : ¬(a * b) • C.mulStab ⊆ s * t)
    (hC : Disjoint C (s ∩ a • C.mulStab * (t ∩ b • C.mulStab))) :
    (C ∪ s ∩ a • C.mulStab * (t ∩ b • C.mulStab)).mulStab =
      (s ∩ a • C.mulStab * (t ∩ b • C.mulStab)).mulStab := by
  obtain rfl | hCne := C.eq_empty_or_nonempty
  · simp
  refine
    ((subset_inter (mulStab_mul_ssubset_mulStab hs₁ ht₁ hab).subset Subset.rfl).trans
          inter_mulStab_subset_mulStab_union).antisymm'
      fun x hx => ?_
  replace hx := (mem_mulStab <| (hs₁.mul ht₁).mono subset_union_right).mp hx
  rw [smul_finset_union] at hx
  suffices hxC : x ∈ C.mulStab by
    rw [(mem_mulStab hCne).mp hxC] at hx
    rw [mem_mulStab_iff_subset_smul_finset (hs₁.mul ht₁)]
    exact hC.symm.left_le_of_le_sup_left (le_sup_right.trans hx.ge)
  rw [mem_mulStab_iff_smul_finset_subset hCne]
  obtain h | h := disjoint_or_nonempty_inter (x • C) (s ∩ a • C.mulStab * (t ∩ b • C.mulStab))
  · exact h.left_le_of_le_sup_right (le_sup_left.trans_eq hx)
  have hUn :
    ((C.biUnion fun y => x • y • C.mulStab) ∩
        (s ∩ a • C.mulStab * (t ∩ b • C.mulStab))).Nonempty := by
    have : (x • C.biUnion fun y => y • C.mulStab) = C.biUnion fun y => x • y • C.mulStab :=
      biUnion_image
    simpa [← this]
  simp_rw [biUnion_inter, biUnion_nonempty, ← smul_assoc, smul_eq_mul] at hUn
  obtain ⟨y, hy, hyne⟩ := hUn
  have hxyCsubC : (x * y) • C.mulStab ⊆ x • C := by
    rw [← smul_eq_mul, smul_assoc, smul_finset_subset_smul_finset_iff]
    exact smul_finset_mulStab_subset hy
  have hxyC : Disjoint ((x * y) • C.mulStab) C := by
    convert disjoint_smul_finset_mulStab_mul_mulStab fun hxyC => _
    · exact C.mul_mulStab.symm
    rw [mul_mulStab] at hxyC
    exact hyne.not_disjoint (hC.mono_left hxyC)
  have hxysub : (x * y) • C.mulStab ⊆ s ∩ a • C.mulStab * (t ∩ b • C.mulStab) :=
    hxyC.left_le_of_le_sup_left (hxyCsubC.trans <| subset_union_left.trans hx.subset)
  suffices s ∩ a • C.mulStab * (t ∩ b • C.mulStab) ⊂ (a * b) • C.mulStab by
    have := (card_le_card hxysub).not_gt ((card_lt_card this).trans_eq ?_)
    cases this
    simp_rw [card_smul_finset]
  apply ssubset_of_subset_not_subset
  · refine (mul_subset_mul inter_subset_right inter_subset_right).trans ?_
    simp only [smul_mul_smul_comm, mulStab_mul_mulStab, subset_refl]
  · contrapose hab
    exact hab.trans (mul_subset_mul inter_subset_left inter_subset_left)

lemma mul_aux1
    (ih : #(s' * (s' * t').mulStab) + #(t' * (s' * t').mulStab) ≤ #(s' * t') + #(s' * t').mulStab)
    (hconv : #(s ∩ t) + #((s ∪ t) * C.mulStab) ≤ #C + #C.mulStab)
    (hnotconv :
      #(C ∪ s' * t') + #(C ∪ s' * t').mulStab < #(s ∩ t) + #((s ∪ t) * (C ∪ s' * t').mulStab))
    (hCun : (C ∪ s' * t').mulStab = (s' * t').mulStab) (hdisj : Disjoint C (s' * t')) :
    (#((s ∪ t) * C.mulStab) - #((s ∪ t) * (s' * t').mulStab) : ℤ) <
      #C.mulStab - #(s' * (s' * t').mulStab) - #(t' * (s' * t').mulStab) := by
  set H := C.mulStab
  set H' := (s' * t').mulStab
  set C' := C ∪ s' * t'
  zify at hconv hnotconv ih
  calc
    (#((s ∪ t) * H) - #((s ∪ t) * H') : ℤ) < #C + #H - #(s ∩ t) - (#C' + #H' - #(s ∩ t)) := by
      rw [← hCun]
      linarith [hconv, hnotconv]
    _ = #H - #(s' * t') - #H' := by
      rw [card_union_of_disjoint hdisj, Int.natCast_add]
      abel
    _ ≤ #H - #(s' * H') - #(t' * H') := by linarith [ih]

lemma disjoint_smul_mulStab (hst : s ⊆ t) (has : ¬a • s.mulStab ⊆ t) :
    Disjoint s (a • s.mulStab) := by
  suffices Disjoint (a • s.mulStab) (s * s.mulStab) by
    simpa [mul_comm, disjoint_comm, mulStab_mul]
  apply disjoint_smul_finset_mulStab_mul_mulStab
  rw [mul_comm, mulStab_mul]
  contrapose has
  exact subset_trans has hst

lemma disjoint_mul_sub_card_le {a : α} (b : α) {s t C : Finset α} (has : a ∈ s)
    (hsC : Disjoint t (a • C.mulStab))
    (hst : (s ∩ a • C.mulStab * (t ∩ b • C.mulStab)).mulStab ⊆ C.mulStab) :
    (#C.mulStab : ℤ) -
        #(s ∩ a • C.mulStab * (s ∩ a • C.mulStab * (t ∩ b • C.mulStab)).mulStab) ≤
      #((s ∪ t) * C.mulStab) -
        #((s ∪ t) * (s ∩ a • C.mulStab * (t ∩ b • C.mulStab)).mulStab) := by
  obtain rfl | hC := C.eq_empty_or_nonempty
  · simp
  calc
    (#C.mulStab : ℤ) -
          #(s ∩ a • C.mulStab * (s ∩ a • C.mulStab * (t ∩ b • C.mulStab)).mulStab) =
        #(a • C.mulStab \
            (s ∩ a • C.mulStab * (s ∩ a • C.mulStab * (t ∩ b • C.mulStab)).mulStab)) := by
      rw [card_sdiff_of_subset
          (subset_trans (mul_subset_mul_left hst)
            (subset_trans (mul_subset_mul_right inter_subset_right) _)),
        card_smul_finset, Int.ofNat_sub]
      · apply le_trans (card_le_card (mul_subset_mul_left hst))
        apply
          le_trans (card_le_card inter_mul_subset)
            (le_of_le_of_eq (card_le_card inter_subset_right) _)
        rw [smul_mul_assoc, mulStab_mul_mulStab, card_smul_finset]
      · simp only [smul_mul_assoc, mulStab_mul_mulStab, Subset.rfl]
    _ ≤ #((s ∪ t) * C.mulStab) -
          #((s ∪ t) * (s ∩ a • C.mulStab * (t ∩ b • C.mulStab)).mulStab) := by
      rw [← Int.ofNat_sub (card_le_card (mul_subset_mul_left hst)),
        ← card_sdiff_of_subset (mul_subset_mul_left hst)]
      norm_cast
      gcongr #?_
      refine fun x hx => mem_sdiff.mpr ⟨?_, ?_⟩
      · apply smul_finset_subset_smul (mem_union_left t has) (mem_sdiff.mp hx).1
      have hx' := (mem_sdiff.mp hx).2
      contrapose hx'
      obtain ⟨y, hyst, d, hd, hxyd⟩ := mem_mul.mp hx'
      obtain ⟨c, hc, hcx⟩ := mem_smul_finset.mp (mem_sdiff.mp hx).1
      rw [← hcx, ← eq_mul_inv_iff_mul_eq] at hxyd
      have hyC : y ∈ a • C.mulStab := by
        rw [hxyd, smul_mul_assoc, smul_mem_smul_finset_iff, ← mulStab_mul_mulStab]
        apply mul_mem_mul hc ((mem_mulStab hC).mpr (inv_smul_eq_iff.mpr _))
        exact Eq.symm ((mem_mulStab hC).mp (hst hd))
      replace hyst : y ∈ s := by
        apply or_iff_not_imp_right.mp (mem_union.mp hyst)
        contrapose hsC
        exact not_disjoint_iff.mpr ⟨y, hsC, hyC⟩
      rw [eq_mul_inv_iff_mul_eq, hcx] at hxyd
      rw [← hxyd]
      exact mul_mem_mul (mem_inter.mpr ⟨hyst, hyC⟩) hd

lemma inter_mul_sub_card_le {a : α} {s t C : Finset α} (has : a ∈ s)
    (hst : (s ∩ a • C.mulStab * (t ∩ a • C.mulStab)).mulStab ⊆ C.mulStab) :
    (#C.mulStab : ℤ) -
          #(s ∩ a • C.mulStab * (s ∩ a • C.mulStab * (t ∩ a • C.mulStab)).mulStab) -
        #(t ∩ a • C.mulStab * (s ∩ a • C.mulStab * (t ∩ a • C.mulStab)).mulStab) ≤
      #((s ∪ t) * C.mulStab) -
        #((s ∪ t) * (s ∩ a • C.mulStab * (t ∩ a • C.mulStab)).mulStab) := by
  obtain rfl | hC := C.eq_empty_or_nonempty
  · simp
  calc
    (#C.mulStab : ℤ) -
            #(s ∩ a • C.mulStab * (s ∩ a • C.mulStab * (t ∩ a • C.mulStab)).mulStab) -
          #(t ∩ a • C.mulStab * (s ∩ a • C.mulStab * (t ∩ a • C.mulStab)).mulStab) ≤
        #(a • C.mulStab \
            ((s ∩ a • C.mulStab ∪ t ∩ a • C.mulStab) *
              (s ∩ a • C.mulStab * (t ∩ a • C.mulStab)).mulStab)) := by
      rw [card_sdiff_of_subset, Int.ofNat_sub (card_le_card _), card_smul_finset]
      · grw [union_mul, le_sub_iff_add_le, card_union_le]
        norm_num
      all_goals
        apply subset_trans (mul_subset_mul_left hst)
        rw [← union_inter_distrib_right]
        refine subset_trans (mul_subset_mul_right inter_subset_right) ?_
        simp only [smul_mul_assoc, mulStab_mul_mulStab, Subset.rfl]
    _ ≤ #((s ∪ t) * C.mulStab) -
          #((s ∪ t) * (s ∩ a • C.mulStab * (t ∩ a • C.mulStab)).mulStab) := by
      rw [← Int.ofNat_sub (card_le_card (mul_subset_mul_left hst)),
        ← card_sdiff_of_subset (mul_subset_mul_left hst)]
      norm_cast
      apply card_le_card
      refine fun x hx => mem_sdiff.mpr ⟨?_, ?_⟩
      · apply smul_finset_subset_smul (mem_union_left t has) (mem_sdiff.mp hx).1
      have hx' := (mem_sdiff.mp hx).2
      contrapose hx'
      rw [← union_inter_distrib_right]
      obtain ⟨y, hyst, d, hd, hxyd⟩ := mem_mul.mp hx'
      obtain ⟨c, hc, hcx⟩ := mem_smul_finset.mp (mem_sdiff.mp hx).1
      rw [← hcx, ← eq_mul_inv_iff_mul_eq] at hxyd
      have hyC : y ∈ a • C.mulStab := by
        rw [hxyd, smul_mul_assoc, smul_mem_smul_finset_iff, ← mulStab_mul_mulStab]
        apply mul_mem_mul hc ((mem_mulStab hC).mpr (inv_smul_eq_iff.mpr _))
        exact Eq.symm ((mem_mulStab hC).mp (hst hd))
      rw [eq_mul_inv_iff_mul_eq, hcx] at hxyd
      rw [← hxyd]
      exact mul_mem_mul (mem_inter.mpr ⟨hyst, hyC⟩) hd

private lemma card_mul_add_card_lt (hC : C.Nonempty) (hs : s' ⊆ s) (ht : t' ⊆ t)
    (hCst : C ⊆ s * t) (hCst' : Disjoint C (s' * t')) :
    #(s' * t') + #s' < #(s * t) + #s :=
  add_lt_add_of_lt_of_le
      (by
        rw [← tsub_pos_iff_lt, ← card_sdiff_of_subset (mul_subset_mul hs ht), card_pos]
        exact hC.mono (subset_sdiff.2 ⟨hCst, hCst'⟩)) <|
    card_le_card hs

variable (s t)

theorem mul_kneser :
    #(s * (s * t).mulStab) + #(t * (s * t).mulStab)
      ≤ #(s * t) + #(s * t).mulStab := by
  -- We're doing induction on `#(s * t) + #s` generalizing the group. This is a bit tricky
  -- in Lean.
  set n : ℕ := #(s * t) + #s with hn
  clear_value n
  induction n using Nat.strong_induction_on generalizing α with | h n ih =>
  subst hn
  -- The cases `s = ∅` and `t = ∅` are easily taken care of.
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  obtain rfl | ht := t.eq_empty_or_nonempty
  · simp
  classical
  -- We distinguish whether `s * t` has trivial stabilizer.
  obtain hstab | hstab := ne_or_eq (s * t).mulStab 1
  · have image_coe_mul :
      ((s * t).image (↑) : Finset (α ⧸ stabilizer α (↑(s * t) : Set α))) =
        s.image (↑) * t.image (↑) :=
      image_mul (QuotientGroup.mk' _ : α →* α ⧸ stabilizer α (↑(s * t) : Set α))
    suffices hineq :
      #(s * t).mulStab *
          (#(s.image (↑) : Finset (α ⧸ stabilizer α (↑(s * t) : Set α))) +
              #(t.image (↑) : Finset (α ⧸ stabilizer α (↑(s * t) : Set α))) -  1) ≤
        #(s * t) by
    -- now to prove that `#(s * (s * t).mulStab) = #(s * t).mulStab * #(s.image (↑))` and
    -- the analogous statement for `s` and `t` interchanged
    -- this will conclude the proof of the first case immediately
      rw [mul_tsub, mul_one, mul_add, tsub_le_iff_left, card_mulStab_mul_card_image_coe',
        card_mulStab_mul_card_image_coe'] at hineq
      convert! hineq using 1
      exact add_comm _ _
    refine le_of_le_of_eq (mul_le_mul_right ?_ _) (card_mul_card_eq_mulStab_card_mul_coe s t).symm
    have := ih _ ?_ (s.image (↑) : Finset (α ⧸ stabilizer α (↑(s * t) : Set α))) (t.image (↑)) rfl
    · classical
      simpa only [← image_coe_mul, mulStab_image_coe_quotient (hs.mul ht), mul_one,
        tsub_le_iff_right, card_one] using this
    rw [← image_coe_mul, card_mul_card_eq_mulStab_card_mul_coe]
    exact
      add_lt_add_of_lt_of_le
        (lt_mul_left ((hs.mul ht).image _).card_pos <|
          Finset.one_lt_card.2 ((hs.mul ht).mulStab_nontrivial.2 hstab))
        card_image_le
  -- Simplify the induction hypothesis a bit. We will only need it over `α` from now on.
  simp only [hstab, mul_one, card_one] at ih ⊢
  replace ih := fun s' t' h => @ih _ h α _ _ s' t' rfl
  obtain ⟨a, rfl⟩ | ⟨a, ha, b, hb, hab⟩ := hs.exists_eq_singleton_or_nontrivial
  · rw [card_singleton, card_singleton_mul, add_comm]
  have : b / a ∉ t.mulStab := by
    refine fun h => hab (Eq.symm (eq_of_div_eq_one ?_))
    replace h := subset_mulStab_mul_right hs h
    rw [hstab, mem_one] at h
    exact h
  simp only [mem_mulStab' ht, smul_eq_mul, Classical.not_forall, exists_prop] at this
  obtain ⟨c, hc, hbac⟩ := this
  set t' := (a / c) • t with ht'
  clear_value t'
  rw [← inv_smul_eq_iff] at ht'
  subst ht'
  rename' t' => t
  rw [mem_inv_smul_finset_iff, smul_eq_mul, div_mul_cancel] at hc
  rw [div_mul_comm, mem_inv_smul_finset_iff, smul_eq_mul, ← mul_assoc, div_mul_div_cancel',
    div_self', one_mul] at hbac
  rw [smul_finset_nonempty] at ht
  simp only [mul_smul_comm, mulStab_smul, card_smul_finset] at *
  have hst : (s ∩ t).Nonempty := ⟨_, mem_inter.2 ⟨ha, hc⟩⟩
  have hsts : s ∩ t ⊂ s :=
    ⟨inter_subset_left, not_subset.2 ⟨_, hb, fun h => hbac <| inter_subset_right h⟩⟩
  clear! a b
  set convergent : Set (Finset α) :=
    {C | C ⊆ s * t ∧ #(s ∩ t) + #((s ∪ t) * C.mulStab) ≤ #C + #C.mulStab}
  have convergent_nonempty : convergent.Nonempty := by
    refine ⟨s ∩ t * (s ∪ t), inter_mul_union_subset, (add_le_add_left (card_le_card <|
      subset_mul_left _ <| one_mem_mulStab.2 <| hst.mul <| hs.mono subset_union_left) _).trans <|
        ih (s ∩ t) (s ∪ t) ?_⟩
    exact add_lt_add_of_le_of_lt (card_le_card inter_mul_union_subset) (card_lt_card hsts)
  let C := argminOn (fun C : Finset α => #C.mulStab) _ convergent_nonempty
  set H := C.mulStab with hH
  obtain ⟨hCst, hCcard⟩ : C ∈ convergent := argminOn_mem _ _ _
  have hCmin (D : Finset α) (hDH : D.mulStab ⊂ H) : D ∉ convergent := fun hD ↦
    (card_lt_card hDH).not_ge <| argminOn_le (fun D : Finset α => #D.mulStab) _ hD
  clear_value C
  clear convergent_nonempty
  obtain rfl | hC := C.eq_empty_or_nonempty
  · simp [hst.ne_empty] at hCcard
  -- If the stabilizer of `C` is trivial, then
  -- `#s + #t - 1 = #(s ∩ t) + #(s ∪ t) - 1 = ≤ #C ≤ #(s * t)`
  obtain hCstab | hCstab := eq_singleton_or_nontrivial (one_mem_mulStab.2 hC)
  · simp only [hCstab, card_singleton, card_mul_singleton, card_inter_add_card_union] at hCcard
    grw [hCcard, hCst]
  exfalso
  have : ¬s * t * H ⊆ s * t := by
    rw [mul_subset_left_iff (hs.mul ht), hstab, ← coe_subset, coe_one]
    exact hCstab.coe.not_subset_singleton
  simp_rw [mul_subset_iff_left, Classical.not_forall, mem_mul] at this
  obtain ⟨_, ⟨a, ha, b, hb, rfl⟩, hab⟩ := this
  set s₁ := s ∩ a • H with hs₁
  set s₂ := s ∩ b • H with hs₂
  set t₁ := t ∩ b • H with ht₁
  set t₂ := t ∩ a • H with ht₂
  have hs₁s : s₁ ⊆ s := inter_subset_left
  have hs₂s : s₂ ⊆ s := inter_subset_left
  have ht₁t : t₁ ⊆ t := inter_subset_left
  have ht₂t : t₂ ⊆ t := inter_subset_left
  have has₁ : a ∈ s₁ := mem_inter.mpr ⟨ha, mem_smul_finset.2 ⟨1, one_mem_mulStab.2 hC, mul_one _⟩⟩
  have hbt₁ : b ∈ t₁ := mem_inter.mpr ⟨hb, mem_smul_finset.2 ⟨1, one_mem_mulStab.2 hC, mul_one _⟩⟩
  have hs₁ne : s₁.Nonempty := ⟨_, has₁⟩
  have ht₁ne : t₁.Nonempty := ⟨_, hbt₁⟩
  set C₁ := C ∪ s₁ * t₁
  set C₂ := C ∪ s₂ * t₂
  set H₁ := (s₁ * t₁).mulStab with hH₁
  set H₂ := (s₂ * t₂).mulStab
  have hC₁st : C₁ ⊆ s * t := union_subset hCst (mul_subset_mul hs₁s ht₁t)
  have hC₂st : C₂ ⊆ s * t := union_subset hCst (mul_subset_mul hs₂s ht₂t)
  have hstabH₁ : s₁ * t₁ ⊆ (a * b) • H := by
    rw [hH, ← mulStab_mul_mulStab C, ← smul_mul_smul_comm]
    apply mul_subset_mul inter_subset_right inter_subset_right
  have hstabH₂ : s₂ * t₂ ⊆ (a * b) • H := by
    rw [hH, ← mulStab_mul_mulStab C, ← smul_mul_smul_comm, mul_comm s₂ t₂]
    apply mul_subset_mul inter_subset_right inter_subset_right
  have hCst₁ := disjoint_of_subset_right hstabH₁ (disjoint_smul_mulStab hCst hab)
  have hCst₂ := disjoint_of_subset_right hstabH₂ (disjoint_smul_mulStab hCst hab)
  have hst₁ : #(s₁ * t₁) + #s₁ < #(s * t) + #s :=
    card_mul_add_card_lt hC hs₁s ht₁t hCst hCst₁
  have hst₂ : #(s₂ * t₂) + #s₂ < #(s * t) + #s :=
    card_mul_add_card_lt hC hs₂s ht₂t hCst hCst₂
  have hC₁stab : C₁.mulStab = H₁ := mulStab_union hs₁ne ht₁ne hab hCst₁
  have hH₁H : H₁ ⊂ H := mulStab_mul_ssubset_mulStab hs₁ne ht₁ne hab
  have aux1₁ :=
    mul_aux1 (ih _ _ hst₁) hCcard
      (not_le.1 fun h => hCmin _ (hC₁stab.trans_ssubset hH₁H) ⟨hC₁st, h⟩) hC₁stab hCst₁
  obtain ht₂ | ht₂ne := t₂.eq_empty_or_nonempty
  · have aux₁_contr :=
      disjoint_mul_sub_card_le b (hs₁s has₁) (disjoint_iff_inter_eq_empty.2 ht₂) hH₁H.subset
    linarith [aux1₁, aux₁_contr, Int.natCast_nonneg #(t₁ * (s₁ * t₁).mulStab)]
  obtain hs₂ | hs₂ne := s₂.eq_empty_or_nonempty
  · have aux1₁_contr :
      (#C.mulStab : ℤ) - #(t₁ * (s₁ * t₁).mulStab) ≤
        #((s ∪ t) * C.mulStab) - #((s ∪ t) * (s₁ * t₁).mulStab) := by
      simpa [union_comm, mul_comm s₁ t₁] using
        disjoint_mul_sub_card_le a (ht₁t hbt₁) (disjoint_iff_inter_eq_empty.2 hs₂)
          (by rw [mul_comm]; exact hH₁H.subset)
    linarith [aux1₁, aux1₁_contr, Int.natCast_nonneg #(s₁ * (s₁ * t₁).mulStab)]
  have hC₂stab : C₂.mulStab = H₂ := mulStab_union hs₂ne ht₂ne (by rwa [mul_comm]) hCst₂
  have hH₂H : H₂ ⊂ H := mulStab_mul_ssubset_mulStab hs₂ne ht₂ne (by rwa [mul_comm])
  have aux1₂ :=
    mul_aux1 (ih _ _ hst₂) hCcard
      (not_le.1 fun h => hCmin _ (hC₂stab.trans_ssubset hH₂H) ⟨hC₂st, h⟩) hC₂stab hCst₂
  obtain habH | habH := eq_or_ne (a • H) (b • H)
  · rw [hH₁, hs₁, ht₁, ← habH, hH] at hH₁H
    refine aux1₁.not_ge ?_
    simp only [hs₁, ht₁, ← habH, inter_mul_sub_card_le (hs₁s has₁) hH₁H.subset, H]
  -- temporarily skipping deduction of inequality (2)
  set S := a • H \ (s₁ ∪ t₂) with hS
  set T := b • H \ (s₂ ∪ t₁) with hT
  have hST : Disjoint S T :=
    (C.pairwiseDisjoint_smul_finset_mulStab (Set.mem_range_self _) (Set.mem_range_self _)
          habH).mono
      sdiff_le sdiff_le
  have hSst : S ⊆ a • H \ (s ∪ t) := by
    simp only [hS, hs₁, ht₂, ← union_inter_distrib_right, sdiff_inter_self_right, Subset.rfl]
  have hTst : T ⊆ b • H \ (s ∪ t) := by
    simp only [hT, hs₂, ht₁, ← union_inter_distrib_right, sdiff_inter_self_right, Subset.rfl]
  have hSTst : Disjoint (S ∪ T) (s ∪ t) := (subset_sdiff.1 hSst).2.sup_left (subset_sdiff.1 hTst).2
  have hstconv : s * t ∉ convergent := by
    apply hCmin (s * t)
    rw [hstab]
    refine (hC.mulStab_nontrivial.mp hCstab).symm.ssubset_of_subset ?_
    simp only [one_subset, one_mem_mulStab, hC]
  simp only [Set.mem_ofPred_eq, Subset.rfl, true_and, not_le, hstab, mul_one, card_one,
    convergent] at hstconv
  zify at hstconv
  have hSTcard : (#S : ℤ) + #T + #(s ∪ t) ≤ #((s ∪ t) * H) := by
    norm_cast
    conv_lhs => rw [← card_union_of_disjoint hST, ← card_union_of_disjoint hSTst, ← mul_one (s ∪ t)]
    refine card_le_card
      (union_subset (union_subset ?_ ?_) <| mul_subset_mul_left <| one_subset.2 hC.one_mem_mulStab)
    · exact hSst.trans (sdiff_subset.trans <| smul_finset_subset_smul <| mem_union_left _ ha)
    · exact hTst.trans (sdiff_subset.trans <| smul_finset_subset_smul <| mem_union_right _ hb)
  have hH₁ne : H₁.Nonempty := (hs₁ne.mul ht₁ne).mulStab
  have hH₂ne : H₂.Nonempty := (hs₂ne.mul ht₂ne).mulStab
  -- Now we prove inequality (2)
  have aux2₁ : (#s₁ : ℤ) + #t₁ + #H₁ ≤ #H := by
    rw [← le_sub_iff_add_le']
    refine (Int.le_of_dvd ((sub_nonneg_of_le <| Nat.cast_le.2 <| card_le_card <|
      mul_subset_mul_left hH₁H.subset).trans_lt aux1₁) <| dvd_sub
        (dvd_sub (card_mulStab_dvd_card_mulStab (hs₁ne.mul ht₁ne) hH₁H.subset).natCast
          (card_mulStab_dvd_card_mul_mulStab _ _).natCast) <|
        (card_mulStab_dvd_card_mul_mulStab _ _).natCast).trans ?_
    rw [sub_sub]
    gcongr _ - (Nat.cast ?_ + Nat.cast ?_) <;> exact card_le_card_mul_right hH₁ne
  have aux2₂ : (#s₂ : ℤ) + #t₂ + #H₂ ≤ #H := by
    rw [← le_sub_iff_add_le']
    refine (Int.le_of_dvd ((sub_nonneg_of_le <| Nat.cast_le.2 <| card_le_card <|
      mul_subset_mul_left hH₂H.subset).trans_lt aux1₂) <| dvd_sub
        (dvd_sub (card_mulStab_dvd_card_mulStab (hs₂ne.mul ht₂ne) hH₂H.subset).natCast
          (card_mulStab_dvd_card_mul_mulStab _ _).natCast) <|
        (card_mulStab_dvd_card_mul_mulStab _ _).natCast).trans ?_
    rw [sub_sub]
    exact sub_le_sub_left (add_le_add (Nat.cast_le.2 <| card_le_card_mul_right hH₂ne) <|
      Nat.cast_le.2 <| card_le_card_mul_right hH₂ne) _
  -- Now we deduce inequality (3) using the above lemma in addition to the facts that `s * t` is not
  -- convergent and then induction hypothesis applied to `sᵢ` and `tᵢ`
  have aux3₁ : (#S : ℤ) + #T + #s₁ + #t₁ - #H₁ < #H :=
    calc
      (#S : ℤ) + #T + #s₁ + #t₁ - #H₁
        < #S + #T + #(s ∪ t) + #(s ∩ t) - #(s * t) + #(s₁ * t₁) := by
        have ih₁ :=
          (add_le_add (card_le_card_mul_right hH₁ne) <| card_le_card_mul_right hH₁ne).trans
            (ih _ _ hst₁)
        zify at ih₁
        linarith [hstconv, ih₁]
      _ ≤ #((s ∪ t) * H) + #(s ∩ t) - #C := by
        suffices (#C : ℤ) + #(s₁ * t₁) ≤ #(s * t) by linarith [this, hSTcard]
        · norm_cast
          simpa only [← card_union_of_disjoint hCst₁] using card_le_card hC₁st
      _ ≤ #H := by
        simpa only [sub_le_iff_le_add, ← Int.natCast_add, Int.ofNat_le, add_comm _ #C,
          add_comm _ #(s ∩ t)] using hCcard
  have aux3₂ : (#S : ℤ) + #T + #s₂ + #t₂ - #H₂ < #H :=
    calc
      (#S : ℤ) + #T + #s₂ + #t₂ - #H₂
       < #S + #T + #(s ∪ t) + #(s ∩ t) - #(s * t) + #(s₂ * t₂) := by
        have ih₂ :=
          (add_le_add (card_le_card_mul_right hH₂ne) <| card_le_card_mul_right hH₂ne).trans
            (ih _ _ hst₂)
        zify at hstconv ih₂
        linarith [ih₂]
      _ ≤ #((s ∪ t) * H) + #(s ∩ t) - #C := by
        suffices (#C : ℤ) + #(s₂ * t₂) ≤ #(s * t) by linarith [this, hSTcard]
        · norm_cast
          simpa only [← card_union_of_disjoint hCst₂] using card_le_card hC₂st
      _ ≤ #H := by
        simpa only [sub_le_iff_le_add, ← Int.natCast_add, Int.ofNat_le, add_comm _ #C,
          add_comm _ #(s ∩ t)] using hCcard
  have aux4₁ : #H ≤ #S + (#s₁ + #t₂) := by
    grw [← card_smul_finset a H, card_le_card_sdiff_add_card, card_union_le]
  have aux4₂ : #H ≤ #T + (#s₂ + #t₁) := by
    grw [← card_smul_finset b H, card_le_card_sdiff_add_card, card_union_le]
  linarith [aux2₁, aux2₂, aux3₁, aux3₂, aux4₁, aux4₂]

end Finset

namespace Finset
open scoped Pointwise
variable {G : Type*} [AddCommGroup G] [DecidableEq G] {s t : Finset G}

def addStab (s : Finset G) : Finset G := @mulStab (Multiplicative G) _ _ s

lemma add_kneser (s t : Finset G) :
    #(s + (s + t).addStab) + #(t + (s + t).addStab) ≤ #(s + t) + #(s + t).addStab :=
  @mul_kneser (Multiplicative G) _ _ s t

lemma add_addStab (s : Finset G) : s + s.addStab = s :=
  @mul_mulStab (Multiplicative G) _ _ s

lemma addStab_add_addStab (s : Finset G) : s.addStab + s.addStab = s.addStab :=
  @mulStab_mul_mulStab (Multiplicative G) _ _ s

lemma Nonempty.addStab (hs : s.Nonempty) : s.addStab.Nonempty :=
  @Nonempty.mulStab (Multiplicative G) _ _ s hs

lemma Nonempty.zero_mem_addStab (hs : s.Nonempty) : (0 : G) ∈ s.addStab :=
  @Nonempty.one_mem_mulStab (Multiplicative G) _ _ s hs

lemma addStab_idem (s : Finset G) : s.addStab.addStab = s.addStab :=
  @mulStab_idem (Multiplicative G) _ _ s

lemma subset_addStab_add_left (hs : s.Nonempty) : t.addStab ⊆ (t + s).addStab :=
  @subset_mulStab_mul_left (Multiplicative G) _ _ t s hs

lemma subset_addStab_add_right (hs : s.Nonempty) : t.addStab ⊆ (s + t).addStab :=
  @subset_mulStab_mul_right (Multiplicative G) _ _ s t hs

lemma coe_addStab (hs : s.Nonempty) : (s.addStab : Set G) = AddAction.stabilizer G (s : Set G) := by
  ext x
  exact (@mem_mulStab (Multiplicative G) _ _ s x hs).trans
    (show x +ᵥ s = s ↔ x ∈ AddAction.stabilizer G (s : Set G) from by
      rw [AddAction.stabilizer_coe_finset]
      rfl)

lemma card_addStab_dvd_card_add_addStab (s t : Finset G) : #t.addStab ∣ #(s + t.addStab) :=
  @card_mulStab_dvd_card_mul_mulStab (Multiplicative G) _ _ s t
end Finset
open Finset
open scoped Pointwise

namespace Erdos338Proof

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

lemma nsmul_add_stab (s H : Finset G) (hH : H + H = H) {h : ℕ} (hh : 1 ≤ h) :
    h • (s + H) = h • s + H := by
  induction h, hh using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [succ_nsmul, ih, succ_nsmul]
    calc n • s + H + (s + H) = n • s + s + (H + H) := by abel
      _ = n • s + s + H := by rw [hH]

lemma kneser_nsmul {h : ℕ} (hh : 1 ≤ h) :
    ∀ s : Finset G, s.Nonempty →
      h * #(s + (h • s).addStab) ≤ #(h • s) + (h - 1) * #(h • s).addStab := by
  induction h, hh using Nat.le_induction with
  | base =>
    intro s _
    simp [add_addStab]
  | succ n hn ih =>
    intro s hs
    set H := ((n + 1) • s).addStab with hHdef
    have hns : (n • s).Nonempty := hs.nsmul
    have hn1 : ((n + 1) • s).Nonempty := hs.nsmul
    have hHH : H + H = H := addStab_add_addStab _
    have hsH : (s + H).Nonempty := hs.add hn1.addStab
    -- the stabilizer of `n • (s + H) = n • s + H` is `H`
    have hnsH : n • (s + H) = n • s + H := nsmul_add_stab s H hHH hn
    have hstab : (n • (s + H)).addStab = H := by
      rw [hnsH]
      apply le_antisymm
      · calc (n • s + H).addStab ⊆ (n • s + H + s).addStab := subset_addStab_add_left hs
          _ = ((n + 1) • s + H).addStab := by rw [succ_nsmul]; congr 1; abel
          _ = H := by rw [add_addStab]
      · calc H = H.addStab := (addStab_idem _).symm
          _ ⊆ (n • s + H).addStab := subset_addStab_add_right hns
    have key := ih (s + H) hsH
    rw [hstab, hnsH, add_assoc, hHH] at key
    -- Kneser for `n • s` and `s`
    have hk := add_kneser (n • s) s
    rw [← succ_nsmul] at hk
    rw [← hHdef] at hk
    -- combine
    have hsub : (n - 1) * #H + #H = n * #H := by
      rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hn]
    have hexp : (n + 1) * #(s + H) = n * #(s + H) + #(s + H) := by ring
    simp only [Nat.add_sub_cancel]
    omega

lemma nsmul_eq_univ [Fintype G] {s : Finset G} (h0 : (0 : G) ∈ s)
    (hgen : AddSubgroup.closure (s : Set G) = ⊤) {h : ℕ} (hh : 1 ≤ h)
    (hcard : 2 * Fintype.card G ≤ h * #s) : h • s = univ := by
  by_contra hne
  have hs : s.Nonempty := ⟨0, h0⟩
  set T := h • s with hTdef
  have hT : T.Nonempty := hs.nsmul
  set H := T.addStab with hHdef
  have hH0 : (0 : G) ∈ H := hT.zero_mem_addStab
  have hHstab : (H : Set G) = AddAction.stabilizer G (T : Set G) := coe_addStab hT
  have mem_H : ∀ {k : G}, k ∈ H ↔ k ∈ AddAction.stabilizer G (T : Set G) := by
    intro k; rw [← Finset.mem_coe, hHstab, SetLike.mem_coe]
  -- `T` is a union of `H`-cosets that misses a coset, so `|T| + |H| ≤ |G|`
  obtain ⟨y, hy⟩ : ∃ y, y ∉ T := by
    by_contra hall
    exact hne (eq_univ_of_forall fun x ↦ by by_contra hx; exact hall ⟨x, hx⟩)
  have hdisj : Disjoint T (y +ᵥ H) := by
    rw [Finset.disjoint_left]
    intro z hzT hzH
    obtain ⟨k, hk, rfl⟩ := Finset.mem_vadd_finset.1 hzH
    have hnk : -k ∈ AddAction.stabilizer G (T : Set G) := neg_mem (mem_H.1 hk)
    have : -k +ᵥ (y +ᵥ k) ∈ (T : Set G) := by
      rw [← AddAction.mem_stabilizer_iff.1 hnk]
      exact Set.vadd_mem_vadd_set (Finset.mem_coe.2 hzT)
    apply hy
    have e : -k +ᵥ (y +ᵥ k) = y := by simp [vadd_eq_add]
    rw [e] at this
    exact Finset.mem_coe.1 this
  have hTH : #T + #H ≤ Fintype.card G := by
    rw [← card_vadd_finset y H, ← card_union_of_disjoint hdisj]
    exact card_le_univ _
  -- `s + H` is a union of at least two `H`-cosets
  have hsub : s ⊆ s + H := by
    intro x hx
    exact Finset.mem_add.2 ⟨x, hx, 0, hH0, add_zero x⟩
  have hHsub : H ⊆ s + H := by
    intro x hx
    exact Finset.mem_add.2 ⟨0, h0, x, hx, zero_add x⟩
  have hdvd : #H ∣ #(s + H) := card_addStab_dvd_card_add_addStab s T
  have hHpos : 0 < #H := card_pos.2 ⟨0, hH0⟩
  have hne2 : #(s + H) ≠ #H := by
    intro heq
    have hsH : s + H = H := (eq_of_subset_of_card_le hHsub heq.le).symm
    have hsH' : (s : Set G) ⊆ AddAction.stabilizer G (T : Set G) := by
      intro x hx
      exact mem_H.1 (hsH ▸ hsub (Finset.mem_coe.1 hx))
    have htop : AddAction.stabilizer G (T : Set G) = ⊤ :=
      eq_top_iff.2 (hgen ▸ (AddSubgroup.closure_le _).2 hsH')
    apply hne
    apply eq_univ_of_forall
    intro g
    obtain ⟨t, ht⟩ := hT
    have hg : g - t ∈ AddAction.stabilizer G (T : Set G) := htop ▸ AddSubgroup.mem_top _
    have : (g - t) +ᵥ t ∈ (T : Set G) := by
      rw [← AddAction.mem_stabilizer_iff.1 hg]
      exact Set.vadd_mem_vadd_set (Finset.mem_coe.2 ht)
    simpa [vadd_eq_add] using this
  have h2H : 2 * #H ≤ #(s + H) := by
    obtain ⟨c, hc⟩ := hdvd
    have hc2 : c ≠ 1 := by rintro rfl; exact hne2 (by rw [hc, mul_one])
    have hc0 : c ≠ 0 := by
      rintro rfl
      have hne' : (s + H).Nonempty := hs.add ⟨0, hH0⟩
      rw [mul_zero, card_eq_zero] at hc
      exact hne'.ne_empty hc
    rw [hc]
    have : 2 ≤ c := by omega
    nlinarith
  have hsle : #s ≤ #(s + H) := card_le_card hsub
  have hK := kneser_nsmul hh s hs
  rw [← hTdef, ← hHdef] at hK
  obtain ⟨k, rfl⟩ : ∃ k, h = k + 1 := ⟨h - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hK
  have h3 : k * (2 * #H) ≤ k * #(s + H) := Nat.mul_le_mul_left k h2H
  have h4 : (k + 1) * #s ≤ (k + 1) * #(s + H) := Nat.mul_le_mul_left _ hsle
  nlinarith

lemma exists_multiset_of_mem_nsmul_image {f : ℕ →+ G} {A : Finset ℕ} :
    ∀ {h : ℕ} {z : G}, z ∈ h • A.image f →
      ∃ M : Multiset ℕ, M.card = h ∧ (∀ a ∈ M, a ∈ A) ∧ f M.sum = z := by
  intro h
  induction h with
  | zero =>
    intro z hz
    rw [zero_nsmul, Finset.mem_zero] at hz
    exact ⟨0, by simp, by simp, by simp [hz]⟩
  | succ n ih =>
    intro z hz
    rw [succ_nsmul, Finset.mem_add] at hz
    obtain ⟨x, hx, w, hw, rfl⟩ := hz
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hw
    obtain ⟨M, hMc, hMA, hMs⟩ := ih hx
    refine ⟨a ::ₘ M, by simp [hMc], ?_, ?_⟩
    · intro b hb
      rcases Multiset.mem_cons.1 hb with rfl | hb
      · exact ha
      · exact hMA b hb
    · rw [Multiset.sum_cons, map_add, hMs, add_comm]

lemma exists_multiset_of_nsmul_eq_univ {A : Finset ℕ} {ℓ h m x : ℕ} [NeZero ℓ]
    (hA0 : 0 ∈ A) (hAℓ : ℓ ∈ A) (hle : ∀ a ∈ A, a ≤ ℓ)
    (huniv : h • A.image (Nat.castAddMonoidHom (ZMod ℓ)) = univ)
    (hx1 : h * ℓ ≤ x) (hx2 : x + h * ℓ ≤ m * ℓ) :
    ∃ M : Multiset ℕ, M.card = m ∧ (∀ a ∈ M, a ∈ A) ∧ M.sum = x := by
  have hℓ : 0 < ℓ := Nat.pos_of_ne_zero (NeZero.ne ℓ)
  obtain ⟨M₀, hc, hA, hs⟩ := exists_multiset_of_mem_nsmul_image
    (huniv ▸ Finset.mem_univ (x : ZMod ℓ))
  simp only [Nat.coe_castAddMonoidHom] at hs
  have hsum : M₀.sum ≤ h * ℓ := by
    rw [← hc]
    exact Multiset.sum_le_card_nsmul _ _ fun a ha ↦ hle a (hA a ha)
  have hmod : M₀.sum ≡ x [MOD ℓ] := (ZMod.natCast_eq_natCast_iff _ _ _).1 hs
  obtain ⟨j, hj⟩ : ℓ ∣ x - M₀.sum := (Nat.modEq_iff_dvd' (by omega)).1 hmod
  have hjm : h + j ≤ m := by
    have : j * ℓ ≤ x := by rw [mul_comm]; omega
    by_contra hcon
    have : m * ℓ < (h + j) * ℓ := Nat.mul_lt_mul_of_pos_right (by omega) hℓ
    nlinarith
  refine ⟨M₀ + Multiset.replicate j ℓ + Multiset.replicate (m - (h + j)) 0, ?_, ?_, ?_⟩
  · simp [hc]; omega
  · intro a ha
    simp only [Multiset.mem_add, Multiset.mem_replicate] at ha
    rcases ha with (ha | ⟨_, rfl⟩) | ⟨_, rfl⟩
    · exact hA a ha
    · exact hAℓ
    · exact hA0
  · simp only [Multiset.sum_add, Multiset.sum_replicate, smul_eq_mul, mul_zero, add_zero]
    rw [mul_comm j ℓ, ← hj]
    omega

end Erdos338Proof
open Finset
open scoped Pointwise

namespace Erdos338Proof

open Classical in

noncomputable def cnt (S : Set ℕ) (b : ℕ) : ℕ := #((range b).filter (· ∈ S))

lemma block_step {h : ℕ} (hh1 : 1 ≤ h) {E : Set ℕ}
    {F : Finset ℕ} (hFE : (F : Set ℕ) ⊆ E)
    (h1 : (1 : ℤ) ∈ Submodule.span ℤ ((Nat.cast : ℕ → ℤ) '' F))
    (hE0 : 0 ∈ E) {ℓ : ℕ} (hℓE : ℓ ∈ E) (hℓF : F.sup id ≤ ℓ)
    (hℓpos : 0 < ℓ) (hbound : 2 * ℓ ≤ h * (cnt E (ℓ + 1) - 1)) {m x : ℕ}
    (hx1 : h * ℓ ≤ x) (hx2 : x + h * ℓ ≤ m * ℓ) :
    ∃ M : Multiset ℕ, M.card = m ∧ (∀ a ∈ M, a ∈ E) ∧ M.sum = x := by
  classical
  have : NeZero ℓ := ⟨hℓpos.ne'⟩
  set A := (range (ℓ + 1)).filter (· ∈ E) with hA
  have hA0 : 0 ∈ A := by simp [hA, hE0]
  have hAℓ : ℓ ∈ A := by simp [hA, hℓE]
  have hle : ∀ a ∈ A, a ≤ ℓ := by
    intro a ha
    simp only [hA, mem_filter, mem_range] at ha
    omega
  set f := Nat.castAddMonoidHom (ZMod ℓ)
  set S := A.image f with hS
  -- `S` is large
  have hScard : #A ≤ #S + 1 := by
    have hinj : Set.InjOn f (A.erase ℓ : Set ℕ) := by
      intro a ha b hb hab
      simp only [coe_erase, Set.mem_sdiff, Finset.mem_coe, Set.mem_singleton_iff] at ha hb
      have ha' : a < ℓ := lt_of_le_of_ne (hle a ha.1) ha.2
      have hb' : b < ℓ := lt_of_le_of_ne (hle b hb.1) hb.2
      have := congrArg ZMod.val hab
      simp only [f, Nat.coe_castAddMonoidHom, ZMod.val_natCast] at this
      rwa [Nat.mod_eq_of_lt ha', Nat.mod_eq_of_lt hb'] at this
    have h1 : #(A.erase ℓ) ≤ #S := by
      rw [← card_image_of_injOn hinj]
      exact card_le_card (image_subset_image (erase_subset ℓ A))
    have h2 := card_erase_add_one hAℓ
    omega
  have hcard : 2 * Fintype.card (ZMod ℓ) ≤ h * #S := by
    rw [ZMod.card]
    change 2 * ℓ ≤ h * (#A - 1) at hbound
    exact hbound.trans (Nat.mul_le_mul_left h (by omega))
  -- `S` generates `ZMod ℓ`
  have hgen : AddSubgroup.closure (S : Set (ZMod ℓ)) = ⊤ := by
    set φ : ℤ →ₗ[ℤ] ZMod ℓ := (Int.castAddHom (ZMod ℓ)).toIntLinearMap
    have hmap : (1 : ZMod ℓ) ∈ Submodule.span ℤ (S : Set (ZMod ℓ)) := by
      have h2 : φ 1 ∈ Submodule.span ℤ (φ '' ((Nat.cast : ℕ → ℤ) '' F)) := by
        rw [← Submodule.map_span]
        exact Submodule.mem_map_of_mem h1
      have e1 : φ 1 = 1 := by simp [φ]
      rw [e1] at h2
      refine Submodule.span_mono ?_ h2
      rintro _ ⟨_, ⟨n, hn, rfl⟩, rfl⟩
      refine Finset.mem_coe.2 (Finset.mem_image.2 ⟨n, ?_, by simp [φ, f]⟩)
      simp only [hA, mem_filter, mem_range]
      refine ⟨?_, hFE hn⟩
      have : n ≤ F.sup id := Finset.le_sup (f := id) hn
      omega
    replace hmap : (1 : ZMod ℓ) ∈ (Submodule.span ℤ (S : Set (ZMod ℓ))).toAddSubgroup := hmap
    rw [Submodule.span_int_eq_addSubgroupClosure] at hmap
    rw [eq_top_iff]
    intro z _
    have : (z.val : ℕ) • (1 : ZMod ℓ) ∈ AddSubgroup.closure (S : Set (ZMod ℓ)) :=
      AddSubgroup.nsmul_mem _ hmap _
    simpa using this
  have h0S : (0 : ZMod ℓ) ∈ S := Finset.mem_image.2 ⟨0, hA0, by simp [f]⟩
  have huniv := nsmul_eq_univ h0S hgen hh1 hcard
  obtain ⟨M, hMc, hMA, hMs⟩ := exists_multiset_of_nsmul_eq_univ hA0 hAℓ hle huniv hx1 hx2
  refine ⟨M, hMc, fun a ha ↦ ?_, hMs⟩
  have := hMA a ha
  simp only [hA, mem_filter] at this
  exact this.2
end Erdos338Proof

namespace Erdos338Campaign
open Finset Erdos338Proof

private lemma blockCount_eq (M : Set ℕ) (n : ℕ) :
    (M ∩ Set.Iic n).ncard = cnt M (n + 1) := by
  classical
  let A := (range (n+1)).filter (· ∈ M)
  have he : M ∩ Set.Iic n = (A : Set ℕ) := by
    ext x
    simp [A, and_comm]
  rw [he, Set.ncard_coe_finset]
  rfl

/-- Cofinal mass in a normalized set produces arbitrarily long intervals inside
the sum of exactly half the available copies. -/
theorem denseBlocks_one (M : Set ℕ) (L : ℕ) (h0 : 0 ∈ M) (hL : 16 ≤ L)
    (hgen : ∃ F : Finset ℕ, (F : Set ℕ) ⊆ M ∧
      (1 : ℤ) ∈ Submodule.span ℤ ((Nat.cast : ℕ → ℤ) '' (F : Set ℕ)))
    (hd : ∀ B : ℕ, ∃ n ≥ B, 32 * n ≤ L * (M ∩ Set.Iic n).ncard) :
    ∀ k : ℕ, ∃ a : ℕ, ∀ j ≤ k, ∃ s : Multiset ℕ, s.card = L / 2 ∧
      (∀ x ∈ s, x ∈ M) ∧ s.sum = a + j := by
  classical
  obtain ⟨F,hF,hspan⟩ := hgen
  intro k
  let T := max k (F.sup id) + 2
  obtain ⟨n,hn,hdn⟩ := hd (L * T)
  let A := (range (n+1)).filter (· ∈ M)
  have hA0 : 0 ∈ A := by simp [A,h0]
  have hA : A.Nonempty := ⟨0,hA0⟩
  let ℓ := A.max' hA
  have hm := A.max'_mem hA
  change ℓ ∈ A at hm
  have hℓM := (mem_filter.mp hm).2
  have hℓn : ℓ ≤ n := by have := mem_range.mp (mem_filter.mp hm).1; omega
  have he : A = (range (ℓ + 1)).filter (· ∈ M) := by
    ext x
    constructor
    · intro hx
      have hle := A.le_max' x hx
      exact mem_filter.mpr ⟨mem_range.mpr (by change x ≤ ℓ at hle; omega), (mem_filter.mp hx).2⟩
    · intro hx
      obtain ⟨hr,hM⟩ := mem_filter.mp hx
      exact mem_filter.mpr ⟨mem_range.mpr (by have := mem_range.mp hr; omega),hM⟩
  have hn' : 32 * n ≤ L * #A := by simpa only [blockCount_eq,cnt,A] using hdn
  have hcardℓ : #A ≤ ℓ + 1 := by rw [he]; exact (card_filter_le _ _).trans (card_range _).le
  have hT : T ≤ #A := by
    exact Nat.le_of_mul_le_mul_left (show L*T ≤ L*#A by omega) (by omega)
  have hkl : k ≤ ℓ := by dsimp [T] at hT; omega
  have hFl : F.sup id ≤ ℓ := by dsimp [T] at hT; omega
  have hℓpos : 0 < ℓ := by dsimp [T] at hT; omega
  let h := L / 5
  have h8 : L ≤ 8*h := by dsimp [h]; omega
  have h2c : #A ≤ 2 * (#A-1) := by dsimp [T] at hT; omega
  have hecnt : #A = cnt M (ℓ + 1) := congrArg Finset.card he
  have hb : 2 * ℓ ≤ h * (cnt M (ℓ + 1) - 1) := by
    rw [← hecnt]
    have hin := Nat.mul_le_mul h8 h2c
    nlinarith
  refine ⟨h * ℓ, fun j hj ↦ ?_⟩
  apply block_step (h := h) (by dsimp [h];omega) hF hspan h0 hℓM hFl hℓpos hb
  · omega
  · have hcap : 2*h+1 ≤ L/2 := by dsimp [h];omega
    have := Nat.mul_le_mul_right ℓ hcap
    nlinarith

/-- The common positive difference divides every element of the original set.
Every progression begins at a multiple of that same difference. -/
theorem denseBlocks (M : Set ℕ) (L : ℕ) (h0 : 0 ∈ M) (hL : 16 ≤ L)
    (hdense : ∀ B : ℕ, ∃ n ≥ B, 32 * n ≤ L * (M ∩ Set.Iic n).ncard) :
    ∃ g : ℕ, 0 < g ∧ (∀ x ∈ M, g ∣ x) ∧ ∀ k : ℕ, ∃ a : ℕ, ∀ j ≤ k,
      ∃ s : Multiset ℕ, s.card = L / 2 ∧ (∀ x ∈ s, x ∈ M) ∧ s.sum = g * (a + j) := by
  classical
  set I := Submodule.span ℤ ((Nat.cast : ℕ → ℤ) '' M) with hI
  have hex : ∃ n : ℕ, 0 < n ∧ (n : ℤ) ∈ I := by
    suffices h : ∃ x ∈ M, 0 < x by
      obtain ⟨x,hx,hpos⟩ := h
      exact ⟨x,hpos,Submodule.subset_span ⟨x,hx,rfl⟩⟩
    by_contra hn
    push Not at hn
    obtain ⟨n,hnL,hcount⟩ := hdense (L+1)
    have hs : M ∩ Set.Iic n ⊆ ({0} : Set ℕ) := fun x hx ↦ by
      have := hn x hx.1
      simpa using this
    have hc := Set.ncard_le_ncard hs
    simp only [Set.ncard_singleton] at hc
    have := Nat.mul_le_mul_left L hc
    omega
  set d := Nat.find hex with hddef
  have hd : 0 < d ∧ (d : ℤ) ∈ I := Nat.find_spec hex
  -- `d` divides every element of `D`
  have hdvd : ∀ u ∈ M, d ∣ u := by
    intro u hu
    have hu' : (u : ℤ) ∈ I := Submodule.subset_span ⟨u, hu, rfl⟩
    have hmod : ((u % d : ℕ) : ℤ) ∈ I := by
      have e : ((u % d : ℕ) : ℤ) = (u : ℤ) - ((u / d : ℕ) : ℤ) * (d : ℤ) := by
        have := Nat.mod_add_div u d
        push_cast
        linarith [this]
      rw [e]
      exact I.sub_mem hu' (I.smul_mem _ hd.2)
    by_contra hnd
    have hpos : 0 < u % d := Nat.pos_of_ne_zero fun h ↦ hnd (Nat.dvd_of_mod_eq_zero h)
    exact Nat.find_min hex (Nat.mod_lt u hd.1) ⟨hpos, hmod⟩

  set E : Set ℕ := {y | d * y ∈ M} with hE
  have hE0 : 0 ∈ E := by simpa [hE] using h0
  -- a finite generating subset of `E`
  obtain ⟨T, hTD, hdT⟩ := Submodule.mem_span_finite_of_mem_span hd.2
  set F : Finset ℕ := T.image fun z ↦ z.toNat / d with hF
  have hFE : (F : Set ℕ) ⊆ E := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := mem_image.1 hy
    obtain ⟨u, hu, rfl⟩ := hTD hz
    show d * ((u : ℤ).toNat / d) ∈ M
    rw [Int.toNat_natCast, Nat.mul_div_cancel' (hdvd u hu)]
    exact hu
  have h1 : (1 : ℤ) ∈ Submodule.span ℤ ((Nat.cast : ℕ → ℤ) '' F) := by
    set f : ℤ →ₗ[ℤ] ℤ := LinearMap.mulLeft ℤ (d : ℤ) with hf
    have hT : (T : Set ℤ) ⊆ f '' ((Nat.cast : ℕ → ℤ) '' F) := by
      intro z hz
      obtain ⟨u, hu, rfl⟩ := hTD hz
      refine ⟨((u / d : ℕ) : ℤ), ⟨u / d, mem_image.2 ⟨u, hz, by simp⟩, rfl⟩, ?_⟩
      simp only [hf, LinearMap.mulLeft_apply]
      exact_mod_cast Nat.mul_div_cancel' (hdvd u hu)
    have hmem : (d : ℤ) ∈ Submodule.map f (Submodule.span ℤ ((Nat.cast : ℕ → ℤ) '' F)) := by
      rw [Submodule.map_span]
      exact Submodule.span_mono hT hdT
    obtain ⟨y, hy, hfy⟩ := Submodule.mem_map.1 hmem
    have hy1 : y = 1 := by
      simp only [hf, LinearMap.mulLeft_apply] at hfy
      have hd0 : (d : ℤ) ≠ 0 := by exact_mod_cast hd.1.ne'
      exact mul_left_cancel₀ hd0 (hfy.trans (mul_one _).symm)
    rwa [hy1] at hy

  have cnt_le (b : ℕ) : cnt M b ≤ cnt E b := by
    unfold cnt
    have hs : (range b).filter (· ∈ M) ⊆ ((range b).filter (· ∈ E)).image (d * ·) := by
      intro x hx
      obtain ⟨hr,hM⟩ := mem_filter.mp hx
      obtain ⟨y,hy⟩ := hdvd x hM
      refine mem_image.mpr ⟨y, mem_filter.mpr ⟨mem_range.mpr ?_, ?_⟩,hy.symm⟩
      · have := mem_range.mp hr
        have := Nat.le_mul_of_pos_left y hd.1
        omega
      · change d * y ∈ M
        rwa [← hy]
    exact (card_le_card hs).trans card_image_le
  have hdE : ∀ B : ℕ, ∃ n ≥ B, 32 * n ≤ L * (E ∩ Set.Iic n).ncard := by
    intro B
    obtain ⟨n,hn,hc⟩ := hdense B
    refine ⟨n, hn, hc.trans (Nat.mul_le_mul_left L ?_)⟩
    simpa only [blockCount_eq] using cnt_le (n+1)
  refine ⟨d,hd.1,hdvd,fun k ↦ ?_⟩
  obtain ⟨a,ha⟩ := denseBlocks_one E L hE0 hL ⟨F,hFE,h1⟩ hdE k
  refine ⟨a,fun j hj ↦ ?_⟩
  obtain ⟨s,hcard,hmem,hsum⟩ := ha j hj
  refine ⟨s.map (d * ·), by simpa using hcard, ?_, ?_⟩
  · intro x hx
    obtain ⟨y,hy,rfl⟩ := Multiset.mem_map.mp hx
    exact hmem y hy
  · rw [Multiset.sum_map_mul_left, Multiset.map_id', hsum]
end Erdos338Campaign

end


section

/- Freeman Dyson's finite addition theorem at full rank and density one.
The proof specializes the minimal-shift transform as presented by Melvyn Nathanson. -/

open Finset
namespace Erdos338Campaign
namespace Dyson

private def pref (A : Finset ℕ) (n : ℕ) := (A.filter (· ≤ n)).card

private lemma pref_mono (A : Finset ℕ) {k m : ℕ} (h : k ≤ m) : pref A k ≤ pref A m := by
  apply card_le_card
  exact fun _ hx ↦ mem_filter.mpr ⟨(mem_filter.mp hx).1, le_trans (mem_filter.mp hx).2 h⟩

private lemma pref_sets {A B : Finset ℕ} (h : A ⊆ B) (n : ℕ) : pref A n ≤ pref B n := by
  apply card_le_card
  intro x hx
  simpa only [mem_filter] using And.intro (h (mem_filter.mp hx).1) (mem_filter.mp hx).2

private def transfer (B : Finset ℕ) (A : Finset ℕ) (a : ℕ) := B.filter (fun c ↦ a+c ∉ A)

private def gain (B : Finset ℕ) (A : Finset ℕ) (a : ℕ) :=
  A ∪ (transfer B A a).image (fun c ↦ a+c)

/-- All removed entries up to k still contribute to the new two prefix counts at m. -/
private theorem compare {B A : Finset ℕ} {a k m : ℕ} (hk : k ≤ m)
    (h : ∀ c ∈ transfer B A a, c ≤ k → a+c ≤ m) :
    pref B k + pref A m ≤ pref (B \ transfer B A a) m + pref (gain B A a) m := by
  classical
  let T := transfer B A a
  let E := (B \ T).filter (· ≤ k)
  let D := T.filter (· ≤ k)
  have ed : Disjoint E D := by
    refine disjoint_left.mpr fun x hx hy ↦ ?_
    exact (mem_sdiff.mp (mem_filter.mp hx).1).2 (mem_filter.mp hy).1
  have eud : B.filter (· ≤ k) = E ∪ D := by
    ext c
    simp only [E, D, mem_filter, mem_union, mem_sdiff]
    have ht : c ∈ T → c ∈ B := fun hc ↦ (mem_filter.mp hc).1
    tauto
  have ecard : E.card ≤ pref (B \ T) m := pref_mono _ hk
  let G := D.image (fun c ↦ a+c)
  have gd : G.card = D.card := card_image_of_injective _ (fun x y hxy ↦ Nat.add_left_cancel hxy)
  have dis : Disjoint (A.filter (· ≤ m)) G := by
    refine disjoint_left.mpr fun x hx hy ↦ ?_
    obtain ⟨c,hc,rfl⟩ := mem_image.mp hy
    exact (mem_filter.mp (mem_filter.mp hc).1).2 (mem_filter.mp hx).1
  have sub : A.filter (· ≤ m) ∪ G ⊆ (gain B A a).filter (· ≤ m) := by
    intro x hx
    rcases mem_union.mp hx with hx | hx
    · exact mem_filter.mpr ⟨mem_union_left _ (mem_filter.mp hx).1,(mem_filter.mp hx).2⟩
    · obtain ⟨c,hc,rfl⟩ := mem_image.mp hx
      obtain ⟨ht,hk'⟩ := mem_filter.mp hc
      exact mem_filter.mpr ⟨mem_union_right _ (mem_image_of_mem _ ht),h c ht hk'⟩
  have cg := card_le_card sub
  rw [card_union_of_disjoint dis, gd] at cg
  change pref A m + D.card ≤ pref (gain B A a) m at cg
  have cb : pref B k = E.card + D.card := by
    unfold pref
    rw [eud,card_union_of_disjoint ed]
  change pref B k + pref A m ≤ pref (B \ T) m + pref (gain B A a) m
  omega

/-- When a short translation by c preserves all entries, two disjoint prefix
blocks and their common translation give this lower bound. -/
private theorem split {A : Finset ℕ} {c m : ℕ} (hc : 0 < c) (hcm : c ≤ m)
    (zero : 0 ∉ A) (h : ∀ x, (x = 0 ∨ x ∈ A) → x ≤ m-c → x+c ∈ A) :
    pref A (c-1) + pref A (m-c) + 1 ≤ pref A m := by
  classical
  let U := A.filter (· ≤ c-1)
  let V := (insert 0 (A.filter (· ≤ m-c))).image (fun x ↦ x+c)
  have dis : Disjoint U V := by
    refine disjoint_left.mpr fun x hx hy ↦ ?_
    obtain ⟨y,_,rfl⟩ := mem_image.mp hy
    have := (mem_filter.mp hx).2
    omega
  have sub : U ∪ V ⊆ A.filter (· ≤ m) := by
    intro x hx
    rcases mem_union.mp hx with hx | hx
    · exact mem_filter.mpr ⟨(mem_filter.mp hx).1, by have := (mem_filter.mp hx).2; omega⟩
    · obtain ⟨y,hy,rfl⟩ := mem_image.mp hx
      rcases mem_insert.mp hy with rfl | hy
      · exact mem_filter.mpr ⟨h 0 (Or.inl rfl) (by omega),by omega⟩
      · obtain ⟨hA,hy'⟩ := mem_filter.mp hy
        exact mem_filter.mpr ⟨h y (Or.inr hA) hy',by omega⟩
  have hv : V.card = pref A (m-c)+1 := by
    unfold V
    rw [card_image_of_injective _ (fun x y hxy ↦ Nat.add_right_cancel hxy),card_insert_of_notMem]
    · rfl
    · simpa using zero
  have hu := card_le_card sub
  rw [card_union_of_disjoint dis,hv] at hu
  change pref A (c-1) + (pref A (m-c)+1) ≤ pref A m at hu
  omega

private def total {ι : Type*} (s : Finset ι) (A : ι → Finset ℕ) (n : ℕ) :=
  ∑ i ∈ s, pref (A i) n

private theorem sum_split {ι : Type*} {s : Finset ι} {A : ι → Finset ℕ} {a c m : ℕ}
    (hs : s.Nonempty) (hc : 0 < c) (hm : c ≤ m) (hsmall : m-c < a)
    (hzero : ∀ i ∈ s, 0 ∉ A i)
    (hmin : ∀ x < a, ∀ i ∈ s, (x = 0 ∨ x ∈ A i) → x+c ∈ A i) :
    total s A (c-1) + total s A (m-c) + 1 ≤ total s A m := by
  have hsum := sum_le_sum (s := s) fun i hi ↦
    split hc hm (hzero i hi) (fun x hx hxm ↦ hmin x (lt_of_le_of_lt hxm hsmall) i hi hx)
  simp only [sum_add_distrib, sum_const, smul_eq_mul, mul_one] at hsum
  unfold total
  have := card_pos.mpr hs
  omega

private theorem transform_counts {ι : Type*} [DecidableEq ι] {s : Finset ι}
    {A : ι → Finset ℕ} {B : Finset ℕ} {g a : ℕ} {j : ι} (hj : j ∈ s)
    (hz : ∀ i ∈ s, 0 ∉ A i) (hB : 0 ∉ B)
    (hmin : ∀ x < a, ∀ i ∈ s, (x = 0 ∨ x ∈ A i) → ∀ c ∈ B, x+c ∈ A i)
    (hc : ∀ m ≤ g, m ≤ total s A m + pref B m) :
    ∀ m ≤ g, m ≤ total s (Function.update A j (gain B (A j) a)) m +
      pref (B \ transfer B (A j) a) m := by
  classical
  let A' := Function.update A j (gain B (A j) a)
  let T := transfer B (A j) a
  let B' := B \ T
  have replace (m : ℕ) : total s A m + pref (gain B (A j) a) m =
      total s A' m + pref (A j) m := by
    unfold total
    have heq : ∑ i ∈ s.erase j, pref (A i) m = ∑ i ∈ s.erase j, pref (A' i) m := by
      apply sum_congr rfl
      intro i hi
      simp [A', Function.update_of_ne (ne_of_mem_erase hi)]
    rw [← sum_erase_add _ _ hj, ← sum_erase_add _ (fun i ↦ pref (A' i) m) hj, heq]
    simp [A', add_right_comm]
  have near (z : ℕ) (hs : z < a) (hg : z ≤ g) : z ≤ total s A z := by
    induction z using Nat.strong_induction_on with
    | h z ih =>
      by_cases he : ∃ c ∈ B, c ≤ z
      · obtain ⟨c,hcB,hcz⟩ := he
        have hpos : 0 < c := Nat.pos_of_ne_zero (fun h ↦ hB (h ▸ hcB))
        have hp := sum_split (a := a) ⟨j,hj⟩ hpos hcz (by omega) hz
          (fun x hx i hi hxi ↦ hmin x hx i hi hxi c hcB)
        have h1 := ih (c-1) (by omega) (by omega) (by omega)
        have h2 := ih (z-c) (by omega) (by omega) (by omega)
        omega
      · have hb0 : pref B z = 0 := by
          apply card_eq_zero.mpr
          exact eq_empty_iff_forall_notMem.mpr (fun c h ↦ he ⟨c, (mem_filter.mp h).1, (mem_filter.mp h).2⟩)
        have hh := hc z hg
        omega
  intro m hmg
  change m ≤ total s A' m + pref B' m
  have swap := replace m
  by_cases he : ∃ c ∈ B, c ≤ m ∧ m < a+c
  · let b := Nat.find he
    obtain ⟨hb, hbm, hmb⟩ : b ∈ B ∧ b ≤ m ∧ m < a+b := Nat.find_spec he
    have hbpos : 0 < b := Nat.pos_of_ne_zero (fun h ↦ hB (h ▸ hb))
    have hm' := compare (B := B) (A := A j) (a := a) (k := b-1) (m := m)
      (by omega) (fun c hct hck ↦ by
        have hcb : c < b := by omega
        have hBD : c ∈ B := (mem_filter.mp hct).1
        by_contra! hbad
        exact (Nat.find_min he hcb) ⟨hBD, by omega, hbad⟩)
    change pref B (b-1) + pref (A j) m ≤ pref B' m + pref (gain B (A j) a) m at hm'
    have split' := sum_split (a := a) ⟨j,hj⟩ hbpos hbm (by omega) hz
      (fun x hx i hi hxi ↦ hmin x hx i hi hxi b hb)
    have h1 := hc (b-1) (by omega)
    have h2 := near (m-b) (by omega) (by omega)
    omega
  · have cmp := compare (B := B) (A := A j) (a := a) (k := m) (m := m) le_rfl
      (fun c hc' hcm ↦ le_of_not_gt (fun h ↦ he ⟨c,(mem_filter.mp hc').1,hcm,h⟩))
    change pref B m + pref (A j) m ≤ pref B' m + pref (gain B (A j) a) m at cmp
    have h := hc m hmg
    omega

private def represents {ι : Type*} (s : Finset ι) (A : ι → Finset ℕ) (n : ℕ) :=
  ∃ f : ι → ℕ, (∀ i ∈ s, f i = 0 ∨ f i ∈ A i) ∧ ∑ i ∈ s, f i = n

private def withLast {ι : Type*} (s : Finset ι) (A : ι → Finset ℕ) (B : Finset ℕ) (n : ℕ) :=
  ∃ b v, (b = 0 ∨ b ∈ B) ∧ represents s A v ∧ v+b = n

/-- A representation after the transform yields one before it. Exchange the two
chosen entries when the j-th entry was gained from the last column. -/
private theorem restore {ι : Type*} [DecidableEq ι] {s : Finset ι}
    {A : ι → Finset ℕ} {B : Finset ℕ} {g a : ℕ} {j : ι} (hj : j ∈ s)
    (ha : a = 0 ∨ a ∈ A j)
    (hr : withLast s (Function.update A j (gain B (A j) a)) (B \ transfer B (A j) a) g) :
    withLast s A B g := by
  obtain ⟨b,v,hb,⟨f,hf,hsum⟩,hvb⟩ := hr
  have other {i} (hi : i ∈ s) (hij : i ≠ j) : f i = 0 ∨ f i ∈ A i := by
    simpa [Function.update_of_ne hij] using hf i hi
  by_cases hold : f j = 0 ∨ f j ∈ A j
  · refine ⟨b,v,hb.imp_right (fun h ↦ (mem_sdiff.mp h).1),⟨f,?_,hsum⟩,hvb⟩
    intro i hi
    by_cases hij : i = j
    · simpa [hij] using hold
    · exact other hi hij
  have hnew := hf j hj
  simp only [Function.update_self] at hnew
  obtain ⟨c,hc,he⟩ : ∃ c ∈ transfer B (A j) a, a+c=f j := by
    rcases hnew with h | h
    · exact False.elim (hold (Or.inl h))
    · rcases mem_union.mp h with h | h
      · exact False.elim (hold (Or.inr h))
      · exact mem_image.mp h
  have hab : a+b=0 ∨ a+b ∈ A j := by
    rcases hb with rfl | h
    · simpa using ha
    · obtain ⟨hbB,hbT⟩ := mem_sdiff.mp h
      exact Or.inr (by
        by_contra hbad
        exact hbT (mem_filter.mpr ⟨hbB,hbad⟩))
  let f' := Function.update f j (a+b)
  have hsum' : (∑ i ∈ s, f' i) + c = g := by
    have hrest : ∑ i ∈ s.erase j, f' i = ∑ i ∈ s.erase j, f i := by
      apply sum_congr rfl
      intro i hi
      exact Function.update_of_ne (ne_of_mem_erase hi) _ _
    rw [← sum_erase_add _ _ hj, hrest]
    rw [← sum_erase_add _ _ hj] at hsum
    simp only [f',Function.update_self]
    omega
  refine ⟨c,_,Or.inr (mem_filter.mp hc).1,⟨f',?_,rfl⟩,hsum'⟩
  intro i hi
  by_cases hij : i=j
  · simpa [f',hij] using hab
  · simpa [f',Function.update_of_ne hij] using other hi hij

/-- Inner descent: decrease the number of positive choices in the last column,
allowing the other columns to change. -/
private theorem eliminate {ι : Type*} [DecidableEq ι] {s : Finset ι} (hs : s.Nonempty)
    (g : ℕ)
    (done' : ∀ A : ι → Finset ℕ, (∀ i ∈ s, 0 ∉ A i) →
      (∀ m ≤ g, m ≤ total s A m) → represents s A g)
    (A : ι → Finset ℕ) (B : Finset ℕ) (hz : ∀ i ∈ s, 0 ∉ A i) (hB : 0 ∉ B)
    (hc : ∀ m ≤ g, m ≤ total s A m + pref B m) : withLast s A B g := by
  classical
  generalize hsize : B.card = k
  induction k using Nat.strong_induction_on generalizing A B with
  | h k ih =>
    by_cases hBE : B = ∅
    · subst B
      exact ⟨0,g,Or.inl rfl,done' A hz (by simpa [pref] using hc),by omega⟩
    obtain ⟨c,hcB⟩ := nonempty_iff_ne_empty.mpr hBE
    have hcpos : 0<c := Nat.pos_of_ne_zero (fun h ↦ hB (h ▸ hcB))
    let bad (x : ℕ) := ∃ j ∈ s, (x=0 ∨ x ∈ A j) ∧ ∃ d ∈ B, x+d ∉ A j
    have existsBad : ∃ x, bad x := by
      obtain ⟨j,hj⟩ := hs
      let D := insert 0 (A j)
      have hD : D.Nonempty := ⟨0,mem_insert_self ..⟩
      let x := D.max' hD
      exact ⟨x,j,hj,mem_insert.mp (D.max'_mem hD),c,hcB,fun hxc ↦ by
        have hm := D.le_max' (x+c) (mem_insert_of_mem hxc)
        change x+c ≤ x at hm
        omega⟩
    let a := Nat.find existsBad
    obtain ⟨j,hj,ha,d,hdB,hda⟩ := (Nat.find_spec existsBad : bad a)
    let T := transfer B (A j) a
    let A' := Function.update A j (gain B (A j) a)
    have hmin : ∀ x < a, ∀ i ∈ s, (x=0 ∨ x ∈ A i) → ∀ d ∈ B, x+d ∈ A i := by
      intro x hx i hi hxi d hd
      by_contra hdx
      exact (Nat.find_min existsBad hx) ⟨i,hi,hxi,d,hd,hdx⟩
    have hdec : (B \ T).card < k := by
      rw [← hsize]
      apply card_lt_card
      refine Finset.ssubset_iff_subset_ne.mpr ⟨sdiff_subset,?_⟩
      intro e
      have ht : d ∈ T := mem_filter.mpr ⟨hdB,hda⟩
      have hin : d ∈ B \ T := e.symm ▸ hdB
      exact (mem_sdiff.mp hin).2 ht
    have hz' : ∀ i ∈ s, 0 ∉ A' i := by
      intro i hi
      by_cases hij : i=j
      · subst i
        simp only [A',Function.update_self,gain,mem_union,not_or,mem_image]
        refine ⟨hz j hj,?_⟩
        rintro ⟨x,hx,e⟩
        have hxB : x ∈ B := (mem_filter.mp hx).1
        exact hB ((show x=0 by omega) ▸ hxB)
      · simpa [A',Function.update_of_ne hij] using hz i hi
    have hb' : 0 ∉ B \ T := fun h ↦ hB (mem_sdiff.mp h).1
    have hc' := transform_counts hj hz hB hmin hc
    exact restore hj ha (ih _ hdec A' (B \ T) hz' hb' hc' rfl)

private theorem singleton_choice (A : Finset ℕ) (g : ℕ) (hz : 0 ∉ A) (hg : g ≤ pref A g) :
    g=0 ∨ g ∈ A := by
  by_cases h : g=0
  · exact Or.inl h
  right
  have sub : A.filter (· ≤ g) ⊆ Icc 1 g := by
    intro x hx
    obtain ⟨hx,hxg⟩ := mem_filter.mp hx
    have hp : 0 < x := Nat.pos_of_ne_zero (fun e ↦ hz (e ▸ hx))
    exact mem_Icc.mpr ⟨hp,hxg⟩
  have eq := eq_of_subset_of_card_le sub (by simpa [pref] using hg)
  have hgmem : g ∈ A.filter (· ≤ g) := eq.symm ▸ mem_Icc.mpr ⟨Nat.pos_of_ne_zero h,le_rfl⟩
  exact (mem_filter.mp hgmem).1

private theorem core {ι : Type*} [DecidableEq ι] (g : ℕ) (s : Finset ι)
    (A : ι → Finset ℕ) (hz : ∀ i ∈ s, 0 ∉ A i)
    (hc : ∀ m ≤ g, m ≤ total s A m) : represents s A g := by
  classical
  induction s using Finset.strongInductionOn generalizing A
  rename_i s ih
  
  by_cases hse : s=∅
  · subst s
    have hg := hc g le_rfl
    simp [total] at hg
    exact ⟨fun _ ↦ 0,by simp,by simp [hg]⟩
  obtain ⟨j,hj⟩ := nonempty_iff_ne_empty.mpr hse
  let R := s.erase j
  have hrsub : R ⊂ s := erase_ssubset hj
  have hsplit (m : ℕ) : total R A m + pref (A j) m = total s A m :=
    sum_erase_add _ _ hj
  by_cases he : R.Nonempty
  · have hlast : withLast R A (A j) g :=
      eliminate he g (fun A' hz' hc' ↦ ih R hrsub A' hz' hc') A (A j)
        (fun i hi ↦ hz i (mem_of_mem_erase hi)) (hz j hj)
        (fun m hm ↦ (hsplit m).symm ▸ hc m hm)
    obtain ⟨b,v,hb,⟨f,hf,hsum⟩,eq⟩ := hlast
    let f' := Function.update f j b
    refine ⟨f',?_,?_⟩
    · intro i hi
      by_cases hij : i=j
      · simpa [f',hij] using hb
      · simpa [f',Function.update_of_ne hij] using hf i (mem_erase.mpr ⟨hij,hi⟩)
    · have hrest : ∑ i ∈ R, f' i = ∑ i ∈ R, f i := by
        exact sum_congr rfl fun i hi ↦ Function.update_of_ne (ne_of_mem_erase hi) _ _
      rw [← sum_erase_add _ _ hj]
      change (∑ i ∈ R, f' i) + f' j = g
      rw [hrest,hsum]
      simpa only [f',Function.update_self] using eq
  · have hre : R = ∅ := not_nonempty_iff_eq_empty.mp he
    have hsg : s = {j} := by rw [← insert_erase hj]; change insert j R = {j}; rw [hre]; rfl
    have hg := hc g le_rfl
    rw [hsg] at hg ⊢
    have hh : g=0 ∨ g∈A j := singleton_choice _ _ (hz j hj) (by simpa [total] using hg)
    exact ⟨fun _ ↦ g, by simpa using hh, by simp⟩

end Dyson

/-- If the joint number of positive entries is at least m in every prefix
through n, then n is representable using exactly one entry from each set. -/
theorem dyson_cover {ι : Type*} [Fintype ι] (X : ι → Set ℕ) (h0 : ∀ i, 0 ∈ X i)
    (n : ℕ) (hc : ∀ m ≤ n, m ≤ ∑ i, (X i ∩ Set.Icc 1 m).ncard) :
    ∃ x : ι → ℕ, (∀ i, x i ∈ X i) ∧ ∑ i, x i = n := by
  classical
  let A := fun i ↦ (Icc 1 n).filter (· ∈ X i)
  have hz (i : ι) : 0 ∉ A i := by simp [A]
  have eq (i : ι) (m : ℕ) (hm : m ≤ n) : Dyson.pref (A i) m = (X i ∩ Set.Icc 1 m).ncard := by
    let B := (A i).filter (· ≤ m)
    have e : (↑B : Set ℕ) = X i ∩ Set.Icc 1 m := by
      ext x
      simp only [B,A,mem_coe,mem_filter,mem_Icc,Set.mem_inter_iff,Set.mem_Icc]
      constructor
      · rintro ⟨⟨⟨hx,_⟩,hX⟩,hxm⟩
        exact ⟨hX,hx,hxm⟩
      · rintro ⟨hX,hx,hxm⟩
        exact ⟨⟨⟨hx,hxm.trans hm⟩,hX⟩,hxm⟩
    rw [← e,Set.ncard_coe_finset]
    rfl
  have hd : ∀ m ≤ n, m ≤ Dyson.total univ A m := by
    intro m hm
    simpa only [Dyson.total,eq _ m hm] using hc m hm
  obtain ⟨f,hf,hsum⟩ := Dyson.core n univ A (fun i _ ↦ hz i) hd
  refine ⟨f,fun i ↦ ?_,hsum⟩
  rcases hf i (mem_univ i) with he | hi
  · rw [he]; exact h0 i
  · exact (mem_filter.mp hi).2

end Erdos338Campaign

end


section

/- The nested summands in Shi-Qiang Chen, Quan-Hui Yang and Lilu Zhao's proof
   of Lemma 4. The bounded-gap argument uses Freeman Dyson's addition theorem.
   Martin Kneser's density theorem motivates the progression conclusion. -/

open scoped BigOperators

namespace Erdos338Campaign

private def DysonCoverStatement : Prop :=
  ∀ {ι : Type} [Fintype ι] (X : ι → Set ℕ), (∀ i, 0 ∈ X i) →
    ∀ n : ℕ, (∀ m ≤ n, m ≤ ∑ i, (X i ∩ Set.Icc 1 m).ncard) →
    ∃ x : ι → ℕ, (∀ i, x i ∈ X i) ∧ ∑ i, x i = n

private def DenseBlockStatement : Prop :=
  ∀ (M : Set ℕ) (L : ℕ), 0 ∈ M → 16 ≤ L →
    (∀ B : ℕ, ∃ n ≥ B, 32 * n ≤ L * (M ∩ Set.Iic n).ncard) →
    ∃ g : ℕ, 0 < g ∧ (∀ x ∈ M, g ∣ x) ∧ ∀ k : ℕ, ∃ a : ℕ, ∀ j ≤ k,
      ∃ s : Multiset ℕ, s.card = L / 2 ∧ (∀ x ∈ s, x ∈ M) ∧ s.sum = g * (a+j)

private lemma zero_prefix_le (S : Set ℕ) (n : ℕ) :
    (S ∩ Set.Iic n).ncard ≤ (S ∩ Set.Icc 1 n).ncard + 1 := by
  have h : S ∩ Set.Iic n ⊆ insert 0 (S ∩ Set.Icc 1 n) := by
    rintro x ⟨hx, hn⟩
    by_cases he : x = 0
    · exact Or.inl he
    · exact Or.inr ⟨hx, Nat.one_le_iff_ne_zero.mpr he, hn⟩
  have hf : (S ∩ Set.Icc 1 n).Finite := (Set.finite_Icc 1 n).subset Set.inter_subset_right
  exact (Set.ncard_le_ncard h (hf.insert _)).trans (Set.ncard_insert_le _ _)

/-- If the large prefix counts add to at least twice the endpoint, the mixed
sum has bounded gaps. An extra finite initial interval makes Dyson applicable
at small endpoints. Removing its terms moves the representation only a bounded distance. -/
private lemma bounded_gaps_of_joint_counts (dyson : DysonCoverStatement)
    {ι : Type} [Fintype ι] [Nonempty ι] (X : ι → Set ℕ) (hz : ∀ i, 0 ∈ X i)
    (hc : ∃ N : ℕ, ∀ n ≥ N, 2*n ≤ ∑ i, (X i ∩ Set.Iic n).ncard) :
    ∃ B : ℕ, ∀ n : ℕ, ∃ x : ι → ℕ,
      (∀ i, x i ∈ X i) ∧ ∑ i, x i ≤ n ∧ n ≤ (∑ i, x i) + B := by
  classical
  obtain ⟨N, hN⟩ := hc
  let K := max N (Fintype.card ι)
  let Y (i : ι) := X i ∪ Set.Iic K
  refine ⟨Fintype.card ι * K, fun n => ?_⟩
  have hY (m : ℕ) : m ≤ ∑ i, (Y i ∩ Set.Icc 1 m).ncard := by
    by_cases hm : m ≤ K
    · let i : ι := Classical.arbitrary ι
      have hsub : Set.Icc 1 m ⊆ Y i ∩ Set.Icc 1 m := by
        intro y hy
        exact ⟨Or.inr (hy.2.trans hm), hy⟩
      have h := Set.ncard_le_ncard hsub ((Set.finite_Icc 1 m).subset Set.inter_subset_right)
      rw [Set.ncard_Icc_nat] at h
      exact (show m ≤ (Y i ∩ Set.Icc 1 m).ncard by omega).trans
        (Finset.single_le_sum (fun j _ => Nat.zero_le ((Y j ∩ Set.Icc 1 m).ncard))
          (Finset.mem_univ i))
    · have h₁ := hN m ((le_max_left N _).trans (le_of_not_ge hm))
      have h₂ : ∑ i, (X i ∩ Set.Iic m).ncard ≤
          (∑ i, (Y i ∩ Set.Icc 1 m).ncard) + Fintype.card ι := by
        calc
          _ ≤ ∑ i, ((Y i ∩ Set.Icc 1 m).ncard + 1) := by
            apply Finset.sum_le_sum
            intro i _
            apply (zero_prefix_le (X i) m).trans
            apply Nat.add_le_add_right
            exact Set.ncard_le_ncard (Set.inter_subset_inter_left _ Set.subset_union_left)
              ((Set.finite_Icc 1 m).subset Set.inter_subset_right)
          _ = _ := by simp [Finset.sum_add_distrib]
      have := (le_max_right N (Fintype.card ι)).trans (le_of_not_ge hm)
      omega
  obtain ⟨y, hy, hy_sum⟩ := dyson Y (fun i => Or.inl (hz i)) n (fun m _ => hY m)
  let x (i : ι) := if y i ∈ X i then y i else 0
  refine ⟨x, fun i => by dsimp [x]; split <;> first | assumption | exact hz i, ?_, ?_⟩
  · rw [← hy_sum]
    exact Finset.sum_le_sum fun i _ => by dsimp [x]; split <;> omega
  · rw [← hy_sum]
    calc
      _ ≤ ∑ i, (x i + K) := by
        apply Finset.sum_le_sum
        intro i _
        rcases hy i with h | h
        · simp [x, h]
        · exact (show y i ≤ K from h).trans (Nat.le_add_left _ _)
      _ = _ := by simp [Finset.sum_add_distrib]

open Filter

private lemma last_recurring {h : ℕ} (P : Fin h → ℕ → Prop)
    (hP : ∀ᶠ n in atTop, ∃ i, P i n) :
    ∃ r, (∃ᶠ n in atTop, P r n) ∧ ∀ᶠ n in atTop, ∃ i ≤ r, P i n := by
  classical
  let active := Finset.univ.filter fun i => ∃ᶠ n in atTop, P i n
  obtain ⟨i, hi⟩ := frequently_exists.mp hP.frequently
  have ha : active.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  let r := active.max' ha
  have hr : r ∈ active := Finset.max'_mem _ _
  refine ⟨r, (Finset.mem_filter.mp hr).2, ?_⟩
  have he : ∀ᶠ n in atTop, ∀ j, r < j → ¬ P j n := by
    apply eventually_all.mpr
    intro j
    by_cases h : r < j
    · have hn : ¬ ∃ᶠ n in atTop, P j n := by
        intro hj
        exact h.not_ge (Finset.le_max' active j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩))
      exact (not_frequently.mp hn).mono fun _ hm _ => hm
    · exact Eventually.of_forall fun _ h' => (h h').elim
  filter_upwards [hP, he] with n hn hall
  obtain ⟨j, hj⟩ := hn
  exact ⟨j, le_of_not_gt fun hh => hall j hh hj, hj⟩

private lemma sum_and_block {g B a n s : ℕ} (hg : 0 < g)
    (hs : s ≤ n - g*a) (hgap : n - g*a ≤ s + B) (hn : g*a ≤ n)
    (hsd : g ∣ s) (hnd : g ∣ n) :
    ∃ j ≤ B, s + g*(a+j) = n := by
  have he : g*a + s ≤ n := by omega
  have hd : g ∣ (n - (g*a + s)) := Nat.dvd_sub hnd (dvd_add (dvd_mul_right g a) hsd)
  obtain ⟨j, hj⟩ := hd
  have hj' : j ≤ g*j := Nat.le_mul_of_pos_left _ hg
  exact ⟨j, by omega, by rw [Nat.mul_add]; omega⟩

/-- Chen, Yang and Zhao's nested levels with a uniform constant of 32.
The largest level dense at arbitrarily large endpoints contributes a block
on its own lattice. Dyson's theorem makes the other chosen slots syndetic
on that lattice. No individual lower-density assumption is imposed. -/
private theorem nested_tail_from_finite_lemmas
    (dyson : DysonCoverStatement) (blocks : DenseBlockStatement)
    {h : ℕ} (C : Fin h → Set ℕ) (L : Fin h → ℕ)
    (hzero : ∀ i, 0 ∈ C i) (hmono : Monotone C)
    (hdense : ∃ N₀ : ℕ, ∀ n ≥ N₀, ∃ i, 32*n ≤ L i * (C i ∩ Set.Iic n).ncard) :
    ∃ g N : ℕ, 0 < g ∧ ∀ n ≥ N, g ∣ n →
      ∃ ms : Fin h → Multiset ℕ, (∀ i, (ms i).card ≤ L i) ∧
        (∀ i, ∀ x ∈ ms i, x ∈ C i) ∧ ∑ i, (ms i).sum = n := by
  classical
  obtain ⟨r, hr, he⟩ := last_recurring
    (fun i n => 32*n ≤ L i * (C i ∩ Set.Iic n).ncard) (eventually_atTop.mpr hdense)
  have hLr : 16 ≤ L r := by
    obtain ⟨m, hm, hd⟩ := frequently_atTop.mp hr 32
    have hc : (C r ∩ Set.Iic m).ncard ≤ m+1 := by
      simpa using Set.ncard_le_ncard (Set.inter_subset_right (s := C r) (t := Set.Iic m))
    by_contra hh
    have hmul := Nat.mul_le_mul (show L r ≤ 15 by omega) hc
    omega
  obtain ⟨g, hg, hgC, hblock⟩ := blocks (C r) (L r) (hzero r) hLr
    (frequently_atTop.mp hr)
  let W (i : Fin h) := if i ≤ r then L i - L i / 2 else 0
  let Slots := (i : Fin h) × Fin (W i)
  have hpos : 0 < W r := by simp [W]; omega
  let : Nonempty Slots := ⟨⟨r, ⟨0, hpos⟩⟩⟩
  let X (u : Slots) := C u.1
  have hcounts : ∃ N : ℕ, ∀ n ≥ N, 2*n ≤ ∑ u : Slots, (X u ∩ Set.Iic n).ncard := by
    apply eventually_atTop.mp
    filter_upwards [he] with n hn
    obtain ⟨i, hir, hi⟩ := hn
    have hli : L i ≤ 2 * W i := by simp [W, hir]; omega
    have hi' := Nat.mul_le_mul_right (C i ∩ Set.Iic n).ncard hli
    rw [Nat.mul_assoc] at hi'
    have hsum : ∑ u : Slots, (X u ∩ Set.Iic n).ncard =
        ∑ j, W j * (C j ∩ Set.Iic n).ncard := by
      rw [Fintype.sum_sigma]
      simp [X]
    rw [hsum]
    exact (show 2*n ≤ W i * (C i ∩ Set.Iic n).ncard by omega).trans
      (Finset.single_le_sum (fun j _ => Nat.zero_le (W j * (C j ∩ Set.Iic n).ncard))
        (Finset.mem_univ i))
  obtain ⟨B, hB⟩ := bounded_gaps_of_joint_counts dyson X (fun u => hzero u.1) hcounts
  obtain ⟨a, ha⟩ := hblock B
  refine ⟨g, g*a, hg, ?_⟩
  intro n hn hnd
  obtain ⟨x, hx, hle, hgap⟩ := hB (n - g*a)
  have hdiv : g ∣ ∑ u, x u := by
    apply Finset.dvd_sum
    intro u _
    have hu : u.1 ≤ r := by
      by_contra hh
      have hh' := u.2.isLt
      simp [W, hh] at hh'
    exact hgC _ (hmono hu (hx u))
  obtain ⟨j, hj, hjn⟩ := sum_and_block hg hle hgap hn hdiv hnd
  obtain ⟨block, hcard, hmem, hval⟩ := ha j hj
  let base (i : Fin h) : Multiset ℕ :=
    (Finset.univ : Finset (Fin (W i))).val.map fun k => x ⟨i,k⟩
  let extra (i : Fin h) : Multiset ℕ := if i = r then block else 0
  refine ⟨fun i => base i + extra i, ?_, ?_, ?_⟩
  · intro i
    by_cases hir : i = r
    · subst i
      simp [base, extra, W, hcard, Nat.sub_add_cancel (Nat.div_le_self _ _)]
    · simp [base, extra, hir, W]
      split <;> omega
  · intro i y hy
    rcases Multiset.mem_add.mp hy with hy | hy
    · obtain ⟨k, _, rfl⟩ := Multiset.mem_map.mp hy
      exact hx ⟨i, k⟩
    · by_cases hir : i = r
      · subst i
        exact hmem _ (by simpa [extra] using hy)
      · simp [extra, hir] at hy
  · have hb : (∑ i, (base i).sum) = ∑ u, x u := by
      rw [Fintype.sum_sigma]
      rfl
    have hxtra : (∑ i, (extra i).sum) = block.sum := by
      simp [extra, apply_ite Multiset.sum]
    simpa only [Multiset.sum_add, Finset.sum_add_distrib, hb, hxtra, hval] using! hjn

private lemma index_padded_multiset {C : Set ℕ} (hzero : 0 ∈ C)
    {s : Multiset ℕ} {L : ℕ} (hs : s.card ≤ L) (hmem : ∀ v ∈ s, v ∈ C) :
    ∃ x : Fin L → ℕ, (∀ i, x i ∈ C) ∧ ∑ i, x i = s.sum := by
  let m := s + Multiset.replicate (L-s.card) 0
  have hcard : m.toList.length = L := by
    simp [m, Multiset.length_toList, Nat.add_sub_of_le hs]
  let f : Fin m.toList.length → ℕ := m.toList.get
  have hsum : ∑ i, f i = s.sum := by
    rw [← List.sum_ofFn]
    change (List.ofFn m.toList.get).sum = s.sum
    rw [List.ofFn_get, Multiset.sum_toList]
    simp [m]
  have hmembers (i : Fin m.toList.length) : f i ∈ C := by
    have hy : f i ∈ m := (Multiset.mem_toList.mp (List.get_mem _ _))
    rcases Multiset.mem_add.mp hy with hy | hy
    · exact hmem _ hy
    · exact (Multiset.eq_of_mem_replicate hy) ▸ hzero
  rw [← hcard]
  exact ⟨f, hmembers, hsum⟩

/-- Version of Martin Kneser's progression conclusion for the nested families
in the restricted-order argument. The active level may change with n, and
the modulus works simultaneously for every sufficiently large target.
Every slot is filled, including slots padded with zero. -/
theorem kneser_tail_levels (h : ℕ) (C : Fin h → Set ℕ) (L : Fin h → ℕ)
    (h0 : ∀ i, 0 ∈ C i) (hnest : ∀ i j : Fin h, i ≤ j → C i ⊆ C j)
    (hact : ∃ N₀ : ℕ, ∀ n ≥ N₀, ∃ i, 32*n ≤ L i * (C i ∩ Set.Iic n).ncard) :
    ∃ g a N : ℕ, 0 < g ∧ ∀ n ≥ N, n ≡ a [MOD g] →
      ∃ x : ((i : Fin h) × Fin (L i)) → ℕ, (∀ p, x p ∈ C p.1) ∧ ∑ p, x p = n := by
  classical
  obtain ⟨g, N, hg, htail⟩ := nested_tail_from_finite_lemmas
    (@dyson_cover) denseBlocks C L h0 (fun ⦃i j⦄ hij => hnest i j hij) hact
  refine ⟨g, 0, N, hg, ?_⟩
  intro n hn hmod
  obtain ⟨s, hs, hm, hsum⟩ := htail n hn (Nat.modEq_zero_iff_dvd.mp hmod)
  choose x hx hval using fun i => index_padded_multiset (h0 i) (hs i) (hm i)
  refine ⟨fun p => x p.1 p.2, fun p => hx p.1 p.2, ?_⟩
  rw [Fintype.sum_sigma]
  simpa only [hval] using! hsum

end Erdos338Campaign

end


section

/-
Integer constants for the nested levels in the proof of Lemma 4 of
Shi-Qiang Chen, Quan-Hui Yang and Lilu Zhao. One can take α = 1/q.
The multiplicity is 128 q², and the preceding reciprocal density is
64 r Q q². The latter is chosen after Q, as in the paper.
-/

namespace Erdos338Campaign

/-- Lemma 3's pair count forces the stronger local density needed for the block
argument. Here M counts positive restricted sums up to N, e counts the preceding
level including zero, and c counts popular sums up to 2N. -/
theorem scaled_level_count (N M e c r Q q : ℕ) (hrQ : 1 ≤ Q)
    (hM : N ≤ q * M) (hMN : M ≤ N)
    (he : (64 * r * Q * q^2) * e ≤ 2 * N)
    (hpairs : M^2 ≤ r*M*e + N*c + 8*r*(Q-1)*e*N) :
    96*N ≤ (128*q^2)*c := by
  by_cases hN : N = 0
  · simp [hN]
  have hMn : M^2 ≤ N*c + (8*r*Q*e)*N := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : Q ≠ 0)
    simp only [Nat.succ_sub_one] at hpairs
    have hh : r*M*e ≤ r*N*e := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hMN)
    simp only [Nat.succ_eq_add_one] at *
    nlinarith [hh, Nat.zero_le (r * N * e)]
  have he' : 4*q^2*(8*r*Q*e) ≤ N := by
    have eq : (64*r*Q*q^2)*e = 2*(4*q^2*(8*r*Q*e)) := by ring
    omega
  have hc : 4 * N^2 ≤ 4 * (q^2*c)*N + N^2 := by
    calc
      4 * N^2 ≤ 4 * (q*M)^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hM 2)
      _ = 4*q^2*M^2 := by ring
      _ ≤ (4*q^2) * (N*c + (8*r*Q*e)*N) := Nat.mul_le_mul_left _ hMn
      _ = 4 * (q^2*c)*N + (4*q^2*(8*r*Q*e))*N := by ring
      _ ≤ 4 * (q^2*c)*N + N^2 := by
        simpa only [← Nat.pow_two] using Nat.add_le_add_left (Nat.mul_le_mul_right N he') (4 * (q^2*c)*N)
  have hh : (3*N)*N ≤ (4*(q^2*c))*N := by nlinarith [hc]
  have hcancel : 3*N ≤ 4*(q^2*c) := Nat.le_of_mul_le_mul_right hh (by omega)
  nlinarith

/-- The one active level at every sufficiently large even endpoint supplies
one active level at every sufficiently large endpoint. The inequality 96m ≥
32(2m+1) for m ≥ 1 absorbs the missing odd endpoint. -/
theorem active_levels_of_even_counts {ι : Type*} (C : ι → Set ℕ) (L : ι → ℕ)
    (h : ∃ N₀ : ℕ, ∀ m ≥ N₀, ∃ i, 96*m ≤ L i * (C i ∩ Set.Iic (2*m)).ncard) :
    ∃ N₁ : ℕ, ∀ n ≥ N₁, ∃ i, 32*n ≤ L i * (C i ∩ Set.Iic n).ncard := by
  obtain ⟨N₀, h⟩ := h
  refine ⟨2*(N₀+1), ?_⟩
  intro n hn
  obtain ⟨i, hi⟩ := h (n/2) (by omega)
  refine ⟨i, ?_⟩
  have hsub : C i ∩ Set.Iic (2*(n/2)) ⊆ C i ∩ Set.Iic n :=
    Set.inter_subset_inter_right _ (Set.Iic_subset_Iic.mpr (by omega))
  have hcard := Set.ncard_le_ncard hsub ((Set.finite_Iic n).subset Set.inter_subset_right)
  have := Nat.mul_le_mul_left (L i) hcard
  omega

end Erdos338Campaign

end

end

section

/- Shared definitions from the Erdős 338 campaign interface. -/

open Finset Erdos338

namespace Erdos338Campaign

/-- Sums of at most `k` distinct elements of `A` (CYZ's `R_k(A)`); the empty sum gives `0`. -/
def R (A : Set ℕ) (k : ℕ) : Set ℕ :=
  {n | ∃ S : Finset ℕ, ↑S ⊆ A ∧ S.card ≤ k ∧ ∑ x ∈ S, x = n}

/-- Sums of at most `k` elements of `A`, repetition allowed (CYZ's `S_k(A)`). -/
def Srep (A : Set ℕ) (k : ℕ) : Set ℕ :=
  {n | ∃ M : Multiset ℕ, (∀ x ∈ M, x ∈ A) ∧ Multiset.card M ≤ k ∧ M.sum = n}

/-- `n` has `Q` pairwise disjoint representations as a sum of between 1 and `k` distinct elements
of `A` (CYZ's `ρ_k(n; A) ≥ Q`). -/
def HasDisjointReps (A : Set ℕ) (k Q n : ℕ) : Prop :=
  ∃ G : Fin Q → Finset ℕ,
    (∀ i, ↑(G i) ⊆ A ∧ (G i).Nonempty ∧ (G i).card ≤ k ∧ ∑ x ∈ G i, x = n) ∧
    ∀ i j, i ≠ j → Disjoint (G i) (G j)

/-- Sumset of a finite family of sets of naturals. -/
def famSum {ι : Type*} [Fintype ι] (X : ι → Set ℕ) : Set ℕ :=
  {n | ∃ x : ι → ℕ, (∀ i, x i ∈ X i) ∧ ∑ i, x i = n}

end Erdos338Campaign

end

section

/-
Lemma 2 of the Erdős 338 campaign. This is an elementary replacement for
Hegyvári–Hennecart–Plagne 2003 Theorem 4 as used by Chen–Yang–Zhao
(arXiv:2611.33191). The proof route is from the Lane A campaign blueprint,
§3.1, by Claude Opus 5.5. The Lean proof was written by GPT-6.2-Astra.
-/

open Finset Erdos338

namespace Erdos338Campaign





/-- Fix a smallest distinct representation for each representable sum. -/
private theorem smallestRep (X : Finset ℕ) (w : ℕ) :
    ∃ F : Finset ℕ, ∀ T : Finset ℕ, T ⊆ X → (∑ x ∈ T, x) = w →
      F ⊆ X ∧ (∑ x ∈ F, x) = w ∧ F.card ≤ T.card := by
  classical
  let reps := X.powerset.filter fun T => (∑ x ∈ T, x) = w
  have mem_reps (T : Finset ℕ) : T ∈ reps ↔ T ⊆ X ∧ (∑ x ∈ T, x) = w := by
    simp [reps]
  by_cases hex : reps.Nonempty
  · obtain ⟨F, hF, hmin⟩ := reps.exists_min_image Finset.card hex
    exact ⟨F, fun T hT hs =>
      ⟨((mem_reps F).1 hF).1, ((mem_reps F).1 hF).2, hmin T ((mem_reps T).2 ⟨hT, hs⟩)⟩⟩
  · exact ⟨∅, fun T hT hs => (hex ⟨T, (mem_reps T).2 ⟨hT, hs⟩⟩).elim⟩

/-- Minimize the number of residual summands. Transferring any summand outside
the chosen distinct representation would give a shorter residual multiset. -/
private theorem supportedRemainder {X : Finset ℕ} {h n : ℕ} (hn : n ∈ Srep (↑X) h)
    (F : ℕ → Finset ℕ)
    (hF : ∀ w (T : Finset ℕ), T ⊆ X → (∑ x ∈ T, x) = w →
      F w ⊆ X ∧ (∑ x ∈ F w, x) = w ∧ (F w).card ≤ T.card) :
    ∃ w ∈ R (↑X) h, ∃ M : Multiset ℕ,
      M.toFinset ⊆ F w ∧ M.card ≤ h ∧ w + M.sum = n := by
  classical
  let P (k : ℕ) := ∃ (T : Finset ℕ) (M : Multiset ℕ),
    T ⊆ X ∧ (∀ x ∈ M, x ∈ X) ∧ T.card + M.card ≤ h ∧
    (∑ x ∈ T, x) + M.sum = n ∧ M.card = k
  obtain ⟨M₀, hX₀, hcard₀, hsum₀⟩ := hn
  have hex : ∃ k, P k :=
    ⟨M₀.card, ∅, M₀, empty_subset _, hX₀, by simpa using hcard₀, by simpa using hsum₀, rfl⟩
  obtain ⟨T, M, hTX, hMX, hbudget, hsum, hleast⟩ := Nat.find_spec hex
  let w := ∑ x ∈ T, x
  change w + M.sum = n at hsum
  obtain ⟨hFX, hFw, hcardF⟩ := hF w T hTX rfl
  refine ⟨w, ⟨T, hTX, by omega, rfl⟩, M, ?_, by omega, hsum⟩
  intro y hy
  have hyM := Multiset.mem_toFinset.mp hy
  by_contra hyF
  have herase := Multiset.cons_erase hyM
  have hc := congrArg Multiset.card herase
  have hs := congrArg Multiset.sum herase
  rw [Multiset.card_cons] at hc
  rw [Multiset.sum_cons] at hs
  have hshort : P (M.erase y).card := by
    refine ⟨insert y (F w), M.erase y, ?_, ?_, ?_, ?_, rfl⟩
    · exact insert_subset (hMX y hyM) hFX
    · exact fun x hx => hMX x (Multiset.erase_subset y M hx)
    · rw [card_insert_of_notMem hyF]
      omega
    · rw [sum_insert hyF, hFw]
      omega
  have hminimal := Nat.find_min' hex hshort
  omega

private theorem finiteR (X : Finset ℕ) (h : ℕ) : (R (↑X) h).Finite := by
  refine (X.powerset.image fun T => ∑ x ∈ T, x).finite_toSet.subset ?_
  rintro n ⟨T, hT, _, rfl⟩
  exact mem_image_of_mem _ (mem_powerset.mpr hT)

theorem ncard_Srep_le (X : Finset ℕ) (h : ℕ) :
    (Srep (↑X) h).ncard ≤ (h + 1) ^ h * (R (↑X) h).ncard := by
  classical
  choose F hF using smallestRep X
  let Y := (finiteR X h).toFinset
  let values (w : ℕ) := (univ : Finset (F w → Fin (h + 1))).image
    fun f => w + ∑ x : F w, (f x : ℕ) • (x : ℕ)
  have hcover : Srep (↑X) h ⊆ ↑(Y.biUnion values) := by
    intro n hn
    obtain ⟨w, hw, M, hsupp, hcard, hsum⟩ := supportedRemainder hn F hF
    refine mem_biUnion.mpr ⟨w, (finiteR X h).mem_toFinset.mpr hw, ?_⟩
    let f (x : F w) : Fin (h + 1) :=
      ⟨M.count (x : ℕ), Nat.lt_succ_of_le ((Multiset.count_le_card _ _).trans hcard)⟩
    refine mem_image.mpr ⟨f, mem_univ _, ?_⟩
    change w + (∑ x : F w, M.count (x : ℕ) • (x : ℕ)) = n
    rwa [sum_coe_sort (F w) (fun x => M.count x • x), ← sum_multiset_count_of_subset M (F w) hsupp]
  have hbound (w : ℕ) (hw : w ∈ Y) : (values w).card ≤ (h + 1) ^ h := by
    obtain ⟨T, hTX, hcard, hsum⟩ := (finiteR X h).mem_toFinset.mp hw
    have hcardF := (hF w T hTX hsum).2.2.trans hcard
    calc
      (values w).card ≤ (univ : Finset (F w → Fin (h + 1))).card := card_image_le
      _ = (h + 1) ^ (F w).card := by simp
      _ ≤ (h + 1) ^ h := Nat.pow_le_pow_right (by omega) hcardF
  calc
    (Srep (↑X) h).ncard ≤ (↑(Y.biUnion values) : Set ℕ).ncard :=
      Set.ncard_le_ncard hcover (Y.biUnion values).finite_toSet
    _ = (Y.biUnion values).card := Set.ncard_coe_finset _
    _ ≤ Y.card * (h + 1) ^ h := card_biUnion_le_card_mul Y values _ hbound
    _ = (h + 1) ^ h * (R (↑X) h).ncard := by
      rw [mul_comm, Set.ncard_eq_toFinset_card _ (finiteR X h)]

/-- Restrict summands to `[0,L]`. Only the empty sum's value needs an extra
place when we count the distinct sums in the positive interval `[1,N]`. -/
private theorem countTruncation {A : Set ℕ} {h m₀ : ℕ}
    (htail : ∀ n ≥ m₀, n ∈ Srep A h) (L N : ℕ) (hLN : h * L ≤ N) :
    L + 1 - m₀ ≤ (h + 1) ^ h * ((R A h ∩ Set.Icc 1 N).ncard + 1) := by
  classical
  let X := (Finset.Iic L).filter fun x => x ∈ A
  have mem_X (x : ℕ) : x ∈ X ↔ x ≤ L ∧ x ∈ A := by simp [X]
  have hinterval : Set.Icc m₀ L ⊆ Srep (↑X) h := by
    intro n hn
    obtain ⟨M, hMA, hcard, hsum⟩ := htail n hn.1
    refine ⟨M, fun x hx => (mem_X x).2 ⟨?_, hMA x hx⟩, hcard, hsum⟩
    exact (Multiset.le_sum_of_mem hx).trans (hsum ▸ hn.2)
  have hfinite : (Srep (↑X) h).Finite := by
    refine (Set.finite_Iic (h * L)).subset ?_
    rintro n ⟨M, hM, hcard, rfl⟩
    exact (M.sum_le_card_nsmul L (fun x hx => ((mem_X x).1 (hM x hx)).1)).trans
      (Nat.mul_le_mul_right L hcard)
  have hrestrict : R (↑X) h ⊆ insert 0 (R A h ∩ Set.Icc 1 N) := by
    rintro n ⟨T, hT, hcard, hsum⟩
    by_cases hn : n = 0
    · exact Or.inl hn
    refine Or.inr ⟨⟨T, fun x hx => ((mem_X x).1 (hT hx)).2, hcard, hsum⟩, by omega, ?_⟩
    rw [← hsum]
    exact (T.sum_le_card_nsmul id L (fun x hx => ((mem_X x).1 (hT hx)).1)).trans
      ((Nat.mul_le_mul_right L hcard).trans hLN)
  have htarget := (Set.finite_Icc 1 N).inter_of_right (R A h)
  calc
    L + 1 - m₀ = (Set.Icc m₀ L).ncard := (Set.ncard_Icc_nat _ _).symm
    _ ≤ (Srep (↑X) h).ncard := Set.ncard_le_ncard hinterval hfinite
    _ ≤ (h + 1) ^ h * (R (↑X) h).ncard := ncard_Srep_le X h
    _ ≤ _ := Nat.mul_le_mul_left _ ((Set.ncard_le_ncard hrestrict (htarget.insert 0)).trans
      (Set.ncard_insert_le _ _))

theorem lemma2 (A : Set ℕ) (h : ℕ) (hA : HasOrder A h) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, N ≤ 4 * h * (h + 1) ^ h * (R A h ∩ Set.Icc 1 N).ncard := by
  obtain ⟨m₀, htail⟩ := Filter.eventually_atTop.mp hA
  have hh : 0 < h := by
    by_contra! hz
    obtain ⟨M, _, hcard, hsum⟩ := htail (m₀ + 1) (by omega)
    have hzero : M = 0 := Multiset.card_eq_zero.mp (by omega)
    simp [hzero] at hsum
  let C := (h + 1) ^ h
  refine ⟨2 * (m₀ + C + 1) * h, ?_⟩
  intro N hN
  let L := N / h
  have hlarge : 2 * (m₀ + C + 1) ≤ L := (Nat.le_div_iff_mul_le hh).2 hN
  have hcount := countTruncation htail L N (Nat.mul_div_le N h)
  let r := (R A h ∩ Set.Icc 1 N).ncard
  change L + 1 - m₀ ≤ C * (r + 1) at hcount
  rw [Nat.mul_succ] at hcount
  have hround : L + 1 ≤ 4 * (C * r) := by omega
  calc
    N ≤ h * (L + 1) := (Nat.lt_mul_div_succ N hh).le
    _ ≤ h * (4 * (C * r)) := Nat.mul_le_mul_left _ hround
    _ = 4 * h * (h + 1) ^ h * (R A h ∩ Set.Icc 1 N).ncard := by
      dsimp only [C, r]
      ac_rfl

end Erdos338Campaign

end

section

/- Integer choices and nesting for Lemma 4 of Shi-Qiang Chen, Quan-Hui Yang
and Lilu Zhao. A uniform upper bound for the number of previously used
elements makes the disjoint-representation threshold explicit. -/

open Finset

namespace Erdos338Campaign

private def copies (q : ℕ) := 128*q^2
private def threshold (h b q : ℕ) := b + h*(2*h*copies q) + 1

private def reciprocal (h b c : ℕ) : ℕ → ℕ
  | 0 => c
  | k+1 =>
    let q := reciprocal h b c k
    q + 64*h*threshold h b q*q^2

private lemma reciprocal_mono (h b c : ℕ) : Monotone (reciprocal h b c) := by
  apply monotone_nat_of_le_succ
  intro k
  exact Nat.le_add_right _ _

private lemma copies_mono : Monotone copies := by
  intro m n h
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h _)

private lemma threshold_mono (h b : ℕ) : Monotone (threshold h b) := by
  intro m n hmn
  unfold threshold
  gcongr
  exact copies_mono hmn

/-- The source recurses from the largest level downwards. These choices give
the counting inequality and leave enough representations to avoid the full
erased set and all previously used elements. -/
theorem choose_level_plan (h b c : ℕ) :
    ∃ q Q L : Fin h → ℕ,
      (∀ i, 1 ≤ Q i) ∧
      (∀ i, 128*(q i)^2 ≤ L i) ∧
      (∀ j i : Fin h, j.val+1 = i.val → 64*(i.val+1)*Q i*(q i)^2 ≤ q j) ∧
      (∀ i : Fin h, i.val+1 = h → c ≤ q i) ∧
      Antitone Q ∧
      (∀ i, b + (∑ j ∈ Finset.univ.filter (fun j : Fin h => i ≤ j),
        2*(j.val+1)*L j) < Q i) := by
  let q (i : Fin h) := reciprocal h b c (h-1-i.val)
  let Q (i : Fin h) := threshold h b (q i)
  let L (i : Fin h) := copies (q i)
  have hq : Antitone q := by
    intro i j hij
    exact reciprocal_mono h b c (Nat.sub_le_sub_left hij _)
  have hL : Antitone L := fun _ _ hj => copies_mono (hq hj)
  refine ⟨q,Q,L,fun i => by dsimp [Q,threshold]; omega,fun _ => le_rfl,?_,?_,?_,?_⟩
  · intro j i hji
    have he : h-1-j.val = (h-1-i.val)+1 := by omega
    have hr : i.val+1 ≤ h := i.isLt
    have hle : 64*(i.val+1)*Q i*(q i)^2 ≤ 64*h*Q i*(q i)^2 := by gcongr
    apply hle.trans
    change _ ≤ reciprocal h b c (h-1-j.val)
    rw [he, reciprocal]
    exact Nat.le_add_left _ _
  · intro i hi
    have he : h-1-i.val = 0 := by omega
    simp [q,he,reciprocal]
  · exact fun _ _ hij => threshold_mono h b (hq hij)
  · intro i
    let s := Finset.univ.filter (fun j : Fin h => i ≤ j)
    have hcard : s.card ≤ h := by simpa using Finset.card_le_univ s
    have hs : (∑ j ∈ s, 2*(j.val+1)*L j) ≤ h*(2*h*L i) := by
      calc
        _ ≤ ∑ _j ∈ s, 2*h*L i := by
          apply Finset.sum_le_sum
          intro j hj
          have hij : i ≤ j := (Finset.mem_filter.mp hj).2
          have hr : j.val+1 ≤ h := j.isLt
          exact Nat.mul_le_mul (Nat.mul_le_mul_left _ hr) (hL hij)
        _ = s.card * (2*h*L i) := by simp
        _ ≤ _ := Nat.mul_le_mul_right _ hcard
    change b + (∑ j ∈ s, 2*(j.val+1)*L j) < b + h*(2*h*L i) + 1
    omega

/-- More summands and fewer required pairwise-disjoint representations
preserve membership in a popular level. -/
theorem disjoint_reps_mono_bounds {A : Set ℕ} {k k' Q Q' n : ℕ}
    (hk : k ≤ k') (hQ : Q' ≤ Q) (hx : HasDisjointReps A k Q n) :
    HasDisjointReps A k' Q' n := by
  obtain ⟨G,hG,hd⟩ := hx
  let f (i : Fin Q') : Fin Q := Fin.castLE hQ i
  have hinj : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    exact congrArg (fun t : Fin Q => t.val) hij
  refine ⟨fun i => G (f i), fun i => ?_, fun i j hij => hd _ _ (hinj.ne hij)⟩
  obtain ⟨hs,hn,hc,he⟩ := hG (f i)
  exact ⟨hs,hn,hc.trans hk,he⟩

end Erdos338Campaign

end

section

/-
Density selection in the proof of Lemma 4 of Shi-Qiang Chen, Quan-Hui Yang
and Lilu Zhao. The integer parameters use the strengthened multiplicities
from the nested-level progression theorem.
-/

namespace Erdos338Campaign

/-- A popular sum at level r, with zero admitted for unused slots. -/
def activeLevel (A : Set ℕ) (r Q : ℕ) : Set ℕ :=
  {n | n = 0 ∨ HasDisjointReps A (2*r) Q n}

private lemma initial_count_le_one (A : Set ℕ) (N : ℕ) :
    (R A 0 ∩ Set.Icc 0 N).ncard ≤ 1 := by
  have hs : R A 0 ∩ Set.Icc 0 N ⊆ ({0} : Set ℕ) := by
    rintro x ⟨⟨S, _, hcard, hsum⟩, _⟩
    have hempty : S = ∅ := Finset.card_eq_zero.mp (by omega)
    subst S
    simpa using hsum.symm
  simpa using Set.ncard_le_ncard hs

private lemma include_zero_in_count (X : Set ℕ) (N : ℕ) :
    (X ∩ Set.Icc 0 N).ncard ≤ (X ∩ Set.Icc 1 N).ncard + 1 := by
  have hs : X ∩ Set.Icc 0 N ⊆ insert 0 (X ∩ Set.Icc 1 N) := by
    intro n hn
    by_cases hz : n = 0
    · exact Or.inl hz
    · exact Or.inr ⟨hn.1, Nat.one_le_iff_ne_zero.mpr hz, hn.2.2⟩
  have hfin := (Set.finite_Icc 1 N).subset (Set.inter_subset_right (s := X))
  exact (Set.ncard_le_ncard hs (hfin.insert 0)).trans (Set.ncard_insert_le _ _)

/-- Positive lower density at the top level and the pair count of Lemma 3
supply the active-level hypothesis at every sufficiently large endpoint. -/
theorem active_levels_from_pairs (A : Set ℕ) (h : ℕ) (hh : 1 ≤ h)
    (c N₀ : ℕ) (hbase : ∀ N ≥ N₀, N ≤ c * (R A h ∩ Set.Icc 1 N).ncard)
    (q Q L : Fin h → ℕ)
    (hQ : ∀ i, 1 ≤ Q i)
    (hL : ∀ i, 128*(q i)^2 ≤ L i)
    (hprev : ∀ j i : Fin h, j.val + 1 = i.val →
      64*(i.val+1)*Q i*(q i)^2 ≤ q j)
    (htop : ∀ i : Fin h, i.val+1 = h → c ≤ q i)
    (hpairs : ∀ r Q N : ℕ, 1 ≤ r → 1 ≤ Q →
      (R A r ∩ Set.Icc 1 N).ncard ^ 2 ≤
        r * (R A r ∩ Set.Icc 1 N).ncard * (R A (r-1) ∩ Set.Icc 0 N).ncard
        + N * ({n | 1 ≤ n ∧ HasDisjointReps A (2*r) Q n} ∩ Set.Icc 1 (2*N)).ncard
        + 8*r*(Q-1)*(R A (r-1) ∩ Set.Icc 0 N).ncard*N) :
    ∃ N₁ : ℕ, ∀ n ≥ N₁, ∃ i : Fin h, 32*n ≤
      L i * (activeLevel A (i.val+1) (Q i) ∩ Set.Iic n).ncard := by
  classical
  apply active_levels_of_even_counts
  let budget (i : Fin h) := 64*(i.val+1)*Q i*(q i)^2
  refine ⟨max N₀ (∑ i, budget i), ?_⟩
  intro N hN
  have hbudget (i : Fin h) : budget i ≤ N := by
    exact (Finset.single_le_sum (fun (j : Fin h) _ => Nat.zero_le (budget j))
        (Finset.mem_univ i)).trans ((le_max_right _ _).trans hN)
  let cnt (i : Fin h) := (R A (i.val+1) ∩ Set.Icc 1 N).ncard
  let good := Finset.univ.filter (fun i : Fin h => N ≤ q i * cnt i)
  let last : Fin h := ⟨h-1, by omega⟩
  have hlast : last.val+1 = h := by dsimp [last]; omega
  have hactive : good.Nonempty := by
    refine ⟨last, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    have ht := hbase N ((le_max_left _ _).trans hN)
    exact ht.trans (by simpa only [cnt, hlast] using
      (Nat.mul_le_mul_right (cnt last) (htop last hlast)))
  let i := good.min' hactive
  have hig : i ∈ good := good.min'_mem hactive
  have hi : N ≤ q i * cnt i := (Finset.mem_filter.mp hig).2
  let e := (R A i.val ∩ Set.Icc 0 N).ncard
  have he : budget i * e ≤ 2*N := by
    by_cases hz : i.val = 0
    · have he1 : e ≤ 1 := by simpa [e, hz] using initial_count_le_one A N
      calc budget i * e ≤ budget i * 1 := Nat.mul_le_mul_left _ he1
           _ ≤ 2*N := by simpa using (hbudget i).trans (by omega : N ≤ 2*N)
    · let j : Fin h := ⟨i.val-1, by have := i.isLt; omega⟩
      have hj : j.val+1 = i.val := by dsimp [j]; omega
      have hji : j < i := by change i.val-1 < i.val; omega
      have hsmall : q j * cnt j < N := by
        by_contra! hc
        have hjg : j ∈ good := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩
        exact (not_le_of_gt hji) (good.min'_le _ hjg)
      have hle : e ≤ cnt j + 1 := by
        simpa only [e, cnt, hj] using include_zero_in_count (R A i.val) N
      calc
        budget i * e ≤ budget i * (cnt j + 1) := Nat.mul_le_mul_left _ hle
        _ = budget i * cnt j + budget i := by rw [Nat.mul_add, Nat.mul_one]
        _ ≤ q j * cnt j + N := Nat.add_le_add
          (Nat.mul_le_mul_right _ (hprev j i hj)) (hbudget i)
        _ ≤ 2*N := by omega
  have hMN : cnt i ≤ N := by
    simpa [cnt] using Set.ncard_le_ncard
      (Set.inter_subset_right (s := R A (i.val+1)) (t := Set.Icc 1 N))
  let D := {n | 1 ≤ n ∧ HasDisjointReps A (2*(i.val+1)) (Q i) n}
  have hp := hpairs (i.val+1) (Q i) N (by omega) (hQ i)
  have count := scaled_level_count N (cnt i) e (D ∩ Set.Icc 1 (2*N)).ncard
    (i.val+1) (Q i) (q i) (hQ i) hi hMN he (by simpa [cnt, e, D] using hp)
  have hsub : D ∩ Set.Icc 1 (2*N) ⊆ activeLevel A (i.val+1) (Q i) ∩ Set.Iic (2*N) :=
    fun _ hn => ⟨Or.inr hn.1.2, hn.2.2⟩
  exact ⟨i, count.trans (Nat.mul_le_mul (hL i) (Set.ncard_le_ncard hsub
    ((Set.finite_Iic _).subset Set.inter_subset_right)))⟩

end Erdos338Campaign

end

section

/- Greedy disjoint choices for Lemma 4 of Shi-Qiang Chen, Quan-Hui Yang and
Lilu Zhao. Representations are selected from the highest levels first. -/

open Finset

namespace Erdos338Campaign

private lemma greedy_avoid {A : Set ℕ} {k Q n : ℕ} (W : Finset ℕ)
    (hn : n = 0 ∨ HasDisjointReps A k Q n) (hw : W.card < Q) :
    ∃ T : Finset ℕ, ↑T ⊆ A ∧ T.card ≤ k ∧ (∑ a ∈ T, a) = n ∧ Disjoint T W := by
  classical
  obtain rfl | ⟨G, hG, hd⟩ := hn
  · exact ⟨∅, by simp, by simp, by simp, by simp⟩
  have happ : ∃ i, Disjoint (G i) W := by
    by_contra! h
    have hits (i) := Finset.not_disjoint_iff.mp (h i)
    choose f hf hW using hits
    let g : Fin Q → W := fun i => ⟨f i, hW i⟩
    have inj : Function.Injective g := by
      intro i j e
      by_contra hij
      have he : f i = f j := congrArg Subtype.val e
      exact (hd i j hij).forall_ne_finset (hf i) (hf j) he
    have hc : Q ≤ W.card := by simpa using Fintype.card_le_of_injective g inj
    exact hc.not_gt hw
  obtain ⟨i, hi⟩ := happ
  exact ⟨G i, (hG i).1, (hG i).2.2.1, (hG i).2.2.2, hi⟩

/-- The sum of all slots can avoid the prescribed finite set. Each level only
needs enough disjoint representations to avoid slots at its own or higher levels. -/
theorem greedy_levels {A : Set ℕ} {h b : ℕ} (L Q : Fin h → ℕ)
    (hQ : ∀ i, b + (∑ j ∈ Finset.univ.filter (fun j : Fin h => i ≤ j),
      2 * (j.val + 1) * L j) < Q i)
    (F : Finset ℕ) (hF : F.card ≤ b) {n : ℕ}
    (hn : n ∈ famSum (fun p : (Σ i : Fin h, Fin (L i)) =>
      {x | x = 0 ∨ HasDisjointReps A (2 * (p.1.val + 1)) (Q p.1) x})) :
    n ∈ R (A \ ↑F) (∑ i, 2 * (i.val + 1) * L i) := by
  classical
  obtain ⟨x, hx, rfl⟩ := hn
  let w (p : Σ i : Fin h, Fin (L i)) := 2 * (p.1.val + 1)
  have select (s : Finset (Σ i : Fin h, Fin (L i))) :
      ∑ p ∈ s, x p ∈ R (A \ ↑F) (∑ p ∈ s, w p) := by
    induction s using Finset.strongInductionOn with
    | _ s ih =>
      by_cases hs : s.Nonempty
      · obtain ⟨p, hp, hm⟩ := s.exists_min_image (fun p => p.1) hs
        obtain ⟨S, hS, hsCard, hsSum⟩ := ih (s.erase p) (Finset.erase_ssubset hp)
        let J := Finset.univ.filter (fun j : Fin h => p.1 ≤ j)
        have sub : s.erase p ⊆ J.sigma (fun j => (Finset.univ : Finset (Fin (L j)))) := by
          intro q hq
          exact mem_sigma.mpr ⟨mem_filter.mpr ⟨mem_univ _, hm q (mem_of_mem_erase hq)⟩, mem_univ _⟩
        have hsum : (∑ q ∈ s.erase p, w q) ≤ ∑ j ∈ J, 2 * (j.val + 1) * L j := by
          calc
            _ ≤ ∑ q ∈ J.sigma (fun j => (Finset.univ : Finset (Fin (L j)))), w q :=
              sum_le_sum_of_subset_of_nonneg sub (fun _ _ _ => Nat.zero_le _)
            _ = _ := by simp [sum_sigma, w, Nat.mul_comm]
        have hsmall : (F ∪ S).card < Q p.1 :=
          (card_union_le F S).trans_lt ((Nat.add_le_add hF (hsCard.trans hsum)).trans_lt (hQ p.1))
        obtain ⟨T, hT, htCard, htSum, htDisj⟩ := greedy_avoid (F ∪ S) (hx p) hsmall
        have htF := Finset.disjoint_of_subset_right (Finset.subset_union_left (s₂ := S)) htDisj
        have htS := Finset.disjoint_of_subset_right (Finset.subset_union_right (s₁ := F)) htDisj
        refine ⟨T ∪ S, ?_, ?_, ?_⟩
        · intro a ha
          rcases mem_union.mp ha with ha | ha
          · exact ⟨hT ha, fun hf => (Finset.disjoint_left.mp htF) ha hf⟩
          · exact hS ha
        · rw [← Finset.add_sum_erase s w hp]
          exact (card_union_le T S).trans (Nat.add_le_add htCard hsCard)
        · rw [Finset.sum_union htS, htSum, hsSum, Finset.add_sum_erase s x hp]
      · obtain rfl := Finset.not_nonempty_iff_eq_empty.mp hs
        exact ⟨∅, by simp, by simp, by simp⟩
  simpa [Fintype.sum_sigma, w, Nat.mul_comm] using select Finset.univ

end Erdos338Campaign

end

section

/- The robust progression of Shi-Qiang Chen, Quan-Hui Yang and Lilu Zhao,
Lemma 4, using the nested-level tail theorem and their Lemma 3 pair count. -/

open Finset

namespace Erdos338Campaign

theorem lemma4_of_pairs
    (hLemma3 : ∀ (A : Set ℕ) (r Q N : ℕ), 1 ≤ r → 1 ≤ Q →
      (R A r ∩ Set.Icc 1 N).ncard ^ 2 ≤
        r * (R A r ∩ Set.Icc 1 N).ncard * (R A (r - 1) ∩ Set.Icc 0 N).ncard
        + N * ({n | 1 ≤ n ∧ HasDisjointReps A (2 * r) Q n} ∩ Set.Icc 1 (2 * N)).ncard
        + 8*r*(Q-1)*(R A (r-1) ∩ Set.Icc 0 N).ncard*N)
    (A : Set ℕ) (h : ℕ) (hh : 1 ≤ h)
    (hdens : ∃ c N₀ : ℕ, 0 < c ∧ ∀ N ≥ N₀, N ≤ c * (R A h ∩ Set.Icc 1 N).ncard) (b : ℕ) :
    ∃ K g a N₀ : ℕ, 0 < g ∧ ∀ F : Finset ℕ, F.card ≤ b →
      ∀ n ≥ N₀, n ≡ a [MOD g] → n ∈ R (A \ ↑F) K := by
  obtain ⟨c, Nbase, _, hd⟩ := hdens
  obtain ⟨q,Q,L,hQ,hL,hprev,htop,hanti,hbudget⟩ := choose_level_plan h b c
  let C (i : Fin h) := activeLevel A (i.val+1) (Q i)
  have hnest (i j : Fin h) (hij : i ≤ j) : C i ⊆ C j := by
    intro n hn
    rcases hn with hz | hr
    · exact Or.inl hz
    · exact Or.inr (disjoint_reps_mono_bounds
        (Nat.mul_le_mul_left 2 (Nat.add_le_add_right hij 1)) (hanti hij) hr)
  have hact := active_levels_from_pairs A h hh c Nbase hd q Q L hQ hL hprev htop (hLemma3 A)
  obtain ⟨g,a,N,hg,htail⟩ :=
    kneser_tail_levels h C L (fun _ => Or.inl rfl) hnest hact
  refine ⟨∑ i, 2*(i.val+1)*L i, g, a, N, hg, ?_⟩
  intro F hF n hn hmod
  exact greedy_levels L Q hbudget F hF (htail n hn hmod)

end Erdos338Campaign

end

section

/-
S.-Q. Chen, Q.-H. Yang and L. Zhao, On a Problem of Erdős and Graham Related to
Restricted Order, Theorem 2, sufficiency, and Theorem 1.
-/

open Finset Erdos338

namespace Erdos338Campaign

/-- Correct a robustly representable residue class by one restricted sum
chosen in advance for each residue. -/
private theorem restrictedOrder_of_robust_class (A : Set ℕ) (H K g a N₀ : ℕ)
    (hg : 0 < g)
    (hres : ∀ v, ∃ S : Finset ℕ, ↑S ⊆ A ∧ S.card ≤ H ∧ ∑ x ∈ S, x ≡ v [MOD g])
    (hrobust : ∀ F : Finset ℕ, F.card ≤ H →
      ∀ n ≥ N₀, n ≡ a [MOD g] → n ∈ R (A \ ↑F) K) :
    HasRestrictedOrder A (K + H) := by
  classical
  choose E hEA hEH hEmod using fun v : Fin g => hres v.val
  let e (v : Fin g) := ∑ x ∈ E v, x
  apply Filter.eventually_atTop.2
  refine ⟨N₀ + a + ∑ i, e i, ?_⟩
  intro n hn
  let v : Fin g := ⟨(n - a) % g, Nat.mod_lt _ hg⟩
  have hev : e v ≤ ∑ i, e i :=
    Finset.single_le_sum (fun i _ => Nat.zero_le (e i)) (Finset.mem_univ v)
  have hcorr : e v ≡ n - a [MOD g] := (hEmod v).trans (by simp [v, Nat.ModEq])
  have hrem : n - e v ≡ a [MOD g] := by
    apply hcorr.add_right_cancel
    rw [Nat.sub_add_cancel (by omega : e v ≤ n), Nat.add_sub_of_le (by omega : a ≤ n)]
  obtain ⟨U, hUA, hUK, hUsum⟩ := hrobust (E v) (hEH v) (n - e v) (by omega) hrem
  have hdisj : Disjoint U (E v) := Finset.disjoint_left.mpr fun _ hx => (hUA hx).2
  refine ⟨U ∪ E v, ?_, ?_, ?_⟩
  · intro x hx
    exact (Finset.mem_union.mp hx).elim (fun hu => (hUA hu).1) (fun he => hEA v he)
  · rw [Finset.card_union_of_disjoint hdisj]
    exact Nat.add_le_add hUK (hEH v)
  · rw [Finset.sum_union hdisj, hUsum]
    exact Nat.sub_add_cancel (by omega : e v ≤ n)

/-- Theorem 2, sufficiency, from the three preceding results. -/
theorem theorem2_of_pieces
    (hLemma2 : ∀ (A : Set ℕ) (h : ℕ), HasOrder A h →
      ∃ N₀ : ℕ, ∀ N ≥ N₀, N ≤ 4 * h * (h + 1) ^ h * (R A h ∩ Set.Icc 1 N).ncard)
    (hLemma4 : ∀ (A : Set ℕ) (h : ℕ), 1 ≤ h →
      (∃ c N₀ : ℕ, 0 < c ∧ ∀ N ≥ N₀, N ≤ c * (R A h ∩ Set.Icc 1 N).ncard) →
      ∀ b : ℕ, ∃ K g a N₀ : ℕ, 0 < g ∧ ∀ F : Finset ℕ, F.card ≤ b →
        ∀ n ≥ N₀, n ≡ a [MOD g] → n ∈ R (A \ ↑F) K)
    (hTheorem3 : ∀ (A : Set ℕ), (∃ h, HasOrder A h) →
      (∀ q, 0 < q → ∀ v, ∃ S : Finset ℕ, ↑S ⊆ A ∧ ∑ x ∈ S, x ≡ v [MOD q]) →
      ∃ H : ℕ, ∀ q, 0 < q → ∀ v, ∃ S : Finset ℕ, ↑S ⊆ A ∧ S.card ≤ H ∧
        ∑ x ∈ S, x ≡ v [MOD q])
    (A : Set ℕ) (hord : ∃ h, HasOrder A h)
    (hloc : ∀ q, 0 < q → ∀ v, ∃ S : Finset ℕ, ↑S ⊆ A ∧ ∑ x ∈ S, x ≡ v [MOD q]) :
    ∃ t, HasRestrictedOrder A t := by
  obtain ⟨H, hH⟩ := hTheorem3 A hord hloc
  obtain ⟨h, hh⟩ := hord
  obtain ⟨N₁, hdensity⟩ := hLemma2 A h hh
  have hpos : 0 < h := by
    by_contra! hz
    have := hdensity (N₁ + 1) (by omega)
    simp [show h = 0 by omega] at this
  obtain ⟨K, g, a, N₀, hg, hrobust⟩ := hLemma4 A h hpos
    ⟨4 * h * (h + 1) ^ h, N₁, by positivity, hdensity⟩ H
  exact ⟨K + H, restrictedOrder_of_robust_class A H K g a N₀ hg (hH g hg) hrobust⟩

/-- Theorem 1 follows by local completeness after arbitrary finite removals. -/
theorem theorem1_of_pieces
    (hTheorem2 : ∀ (A : Set ℕ), (∃ h, HasOrder A h) →
      (∀ q, 0 < q → ∀ v, ∃ S : Finset ℕ, ↑S ⊆ A ∧ ∑ x ∈ S, x ≡ v [MOD q]) →
      ∃ t, HasRestrictedOrder A t)
    (hLocal : ∀ (A : Set ℕ), (∀ F : Set ℕ, F.Finite → ∃ h, HasOrder (A \ F) h) →
      ∀ q, 0 < q → ∀ v, ∃ S : Finset ℕ, ↑S ⊆ A ∧ ∑ x ∈ S, x ≡ v [MOD q])
    (A : Set ℕ) (hA : ∀ F : Set ℕ, F.Finite → ∃ h, HasOrder (A \ F) h) :
    ∃ t, HasRestrictedOrder A t :=
  hTheorem2 A (by simpa using hA ∅ Set.finite_empty) (hLocal A hA)

theorem board_basis_of_theorem1
    (hTheorem1 : ∀ (A : Set ℕ), (∀ F : Set ℕ, F.Finite → ∃ h, HasOrder (A \ F) h) →
      ∃ t, HasRestrictedOrder A t) :
    type_of% @Erdos338.erdos_338.variants.basis_after_finite_removal := hTheorem1

theorem board_same_order_of_theorem1
    (hTheorem1 : ∀ (A : Set ℕ), (∀ F : Set ℕ, F.Finite → ∃ h, HasOrder (A \ F) h) →
      ∃ t, HasRestrictedOrder A t) :
    type_of% @Erdos338.erdos_338.variants.same_order_after_finite_removal := by
  rintro A ⟨h, hrem⟩
  apply hTheorem1
  intro F hF
  by_contra! hnone
  have htop : basisOrder (A \ F) = ⊤ := by simp [basisOrder, hnone]
  exact ENat.top_ne_natCast h (htop.symm.trans (hrem F hF))

end Erdos338Campaign

end

section

/-
Piece: lemma3 of the Erdős 338 campaign.
Source: S.-Q. Chen, Q.-H. Yang, L. Zhao, arXiv:2611.33191v1 (CYZ),
Lemma 3 (pp. 4-5) in the combined form used in the proof of Lemma 4 (p. 7),
following BLUEPRINT §3.3.
Adapted external code: none (written freshly from CYZ pp. 4-5, 7;
Daniel Veljjanoski's Pairs.lean was inspected for reference only).
Written in Lean by Gemini 4 Neon (XHigh).
-/

open Finset Erdos338

namespace Erdos338Campaign





namespace L3

/-- Express `S ∩ Set.Icc a b` as a `Finset` with the same cardinality. -/
private lemma exists_finset_inter_Icc (S : Set ℕ) (a b : ℕ) :
    ∃ T : Finset ℕ, (∀ x, x ∈ T ↔ a ≤ x ∧ x ≤ b ∧ x ∈ S) ∧ (S ∩ Set.Icc a b).ncard = T.card := by
  classical
  let T : Finset ℕ := (Finset.Icc a b).filter (· ∈ S)
  refine ⟨T, ?_, ?_⟩
  · intro x
    simp only [T, Finset.mem_filter, Finset.mem_Icc, and_assoc]
  · have hEq : S ∩ Set.Icc a b = (T : Set ℕ) := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Icc, Finset.mem_coe, T, Finset.mem_filter,
        Finset.mem_Icc, and_comm, and_assoc]
    rw [hEq, Set.ncard_coe_finset]

/-- Choose a nonempty representation in `A` of size at most `r` for every element of `X`. -/
private lemma exists_rep_fn (A : Set ℕ) (r : ℕ) (X : Finset ℕ)
    (hX : ∀ x ∈ X, 1 ≤ x ∧ x ∈ R A r) :
    ∃ F : ℕ → Finset ℕ, ∀ x ∈ X,
      ↑(F x) ⊆ A ∧ (F x).Nonempty ∧ (F x).card ≤ r ∧ ∑ u ∈ F x, u = x := by
  classical
  have hex : ∀ x : {y // y ∈ X}, ∃ S : Finset ℕ,
      ↑S ⊆ A ∧ S.Nonempty ∧ S.card ≤ r ∧ ∑ u ∈ S, u = x.1 := by
    intro ⟨x, hx⟩
    obtain ⟨hx1, S, hSA, hScard, hSsum⟩ := hX x hx
    have hSne : S.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hEmpty
      rw [hEmpty, Finset.sum_empty] at hSsum
      rw [← hSsum] at hx1
      exact Nat.not_succ_le_zero 0 hx1
    exact ⟨S, hSA, hSne, hScard, hSsum⟩
  choose f hf using hex
  refine ⟨fun x => if hx : x ∈ X then f ⟨x, hx⟩ else ∅, ?_⟩
  intro x hx
  simp only [dif_pos hx]
  exact hf ⟨x, hx⟩

/-- CYZ equation (1): each element `a` lies in at most `|E|` chosen representations `F y`. -/
private lemma card_filter_mem_rep_le (A : Set ℕ) (r N : ℕ) (X E : Finset ℕ)
    (hXle : ∀ x ∈ X, x ≤ N)
    (hE : ∀ y, y ≤ N → y ∈ R A (r - 1) → y ∈ E)
    (F : ℕ → Finset ℕ)
    (hF : ∀ x ∈ X, ↑(F x) ⊆ A ∧ (F x).Nonempty ∧ (F x).card ≤ r ∧ ∑ u ∈ F x, u = x)
    (a : ℕ) :
    (X.filter (fun y => a ∈ F y)).card ≤ E.card := by
  refine Finset.card_le_card_of_injOn (fun y => y - a) ?_ ?_
  · intro y hy
    rw [Finset.mem_coe, Finset.mem_filter] at hy
    obtain ⟨hyX, hay⟩ := hy
    obtain ⟨hsub, _, hcard, hsum⟩ := hF y hyX
    refine Finset.mem_coe.mpr (hE (y - a) ?_ ?_)
    · exact Nat.sub_le_of_le_add ((hXle y hyX).trans (Nat.le_add_right N a))
    · refine ⟨(F y).erase a, ?_, ?_, ?_⟩
      · exact Set.Subset.trans (Finset.coe_subset.mpr (Finset.erase_subset a (F y))) hsub
      · rw [Finset.card_erase_of_mem hay]
        exact Nat.sub_le_sub_right hcard 1
      · have hadd : (∑ u ∈ (F y).erase a, u) + a = y := by
          rw [Finset.sum_erase_add _ _ hay, hsum]
        exact Nat.eq_sub_of_add_eq hadd
  · intro y₁ hy₁ y₂ hy₂ heq
    rw [Finset.mem_coe, Finset.mem_filter] at hy₁ hy₂
    have hle₁ : a ≤ y₁ := by
      rw [← (hF y₁ hy₁.1).2.2.2]
      exact Finset.single_le_sum (f := fun u => u) (fun _ _ => Nat.zero_le _) hy₁.2
    have hle₂ : a ≤ y₂ := by
      rw [← (hF y₂ hy₂.1).2.2.2]
      exact Finset.single_le_sum (f := fun u => u) (fun _ _ => Nat.zero_le _) hy₂.2
    have heq' : y₁ - a = y₂ - a := heq
    calc
      y₁ = y₁ - a + a := (Nat.sub_add_cancel hle₁).symm
      _ = y₂ - a + a := by rw [heq']
      _ = y₂ := Nat.sub_add_cancel hle₂

/-- The number of pairs `(x, y) ∈ X × X` with `F x` and `F y` not disjoint is at most `r * |X| * |E|`. -/
private lemma card_nonDisjoint_pairs_le (A : Set ℕ) (r N : ℕ) (X E : Finset ℕ)
    (hXle : ∀ x ∈ X, x ≤ N)
    (hE : ∀ y, y ≤ N → y ∈ R A (r - 1) → y ∈ E)
    (F : ℕ → Finset ℕ)
    (hF : ∀ x ∈ X, ↑(F x) ⊆ A ∧ (F x).Nonempty ∧ (F x).card ≤ r ∧ ∑ u ∈ F x, u = x)
    (B : Finset (ℕ × ℕ))
    (hB : ∀ p ∈ B, p.1 ∈ X ∧ p.2 ∈ X ∧ ¬ Disjoint (F p.1) (F p.2)) :
    B.card ≤ r * X.card * E.card := by
  let cover := X.biUnion fun x =>
    (F x).biUnion fun a => (X.filter (fun y => a ∈ F y)).image (fun y => (x, y))
  have hsub : B ⊆ cover := by
    intro p hp
    obtain ⟨hx, hy, hnd⟩ := hB p hp
    obtain ⟨a, hax, hay⟩ := Finset.not_disjoint_iff.mp hnd
    refine Finset.mem_biUnion.mpr ⟨p.1, hx, Finset.mem_biUnion.mpr ⟨a, hax, ?_⟩⟩
    exact Finset.mem_image.mpr ⟨p.2, Finset.mem_filter.mpr ⟨hy, hay⟩, Prod.mk.eta⟩
  calc
    B.card ≤ cover.card := Finset.card_le_card hsub
    _ ≤ ∑ x ∈ X, ((F x).biUnion fun a =>
        (X.filter (fun y => a ∈ F y)).image (fun y => (x, y))).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ x ∈ X, ∑ a ∈ F x, ((X.filter (fun y => a ∈ F y)).image (fun y => (x, y))).card :=
      Finset.sum_le_sum fun x _ => Finset.card_biUnion_le
    _ ≤ ∑ x ∈ X, ∑ a ∈ F x, E.card := by
      refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun a _ => ?_
      exact Finset.card_image_le.trans (card_filter_mem_rep_le A r N X E hXle hE F hF a)
    _ = ∑ x ∈ X, (F x).card * E.card := by
      simp only [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ x ∈ X, r * E.card :=
      Finset.sum_le_sum fun x hx => Nat.mul_le_mul_right E.card (hF x hx).2.2.1
    _ = X.card * (r * E.card) := by
      simp only [Finset.sum_const, smul_eq_mul]
    _ = r * X.card * E.card := by ac_rfl

/-- Lower bound on the disjoint-representation pair set `P`: `|X|^2 ≤ |P| + r * |X| * |E|`. -/
private lemma card_sq_le_card_pairs_add (A : Set ℕ) (r N : ℕ) (X E : Finset ℕ)
    (hXle : ∀ x ∈ X, x ≤ N)
    (hE : ∀ y, y ≤ N → y ∈ R A (r - 1) → y ∈ E)
    (F : ℕ → Finset ℕ)
    (hF : ∀ x ∈ X, ↑(F x) ⊆ A ∧ (F x).Nonempty ∧ (F x).card ≤ r ∧ ∑ u ∈ F x, u = x)
    (P : Finset (ℕ × ℕ))
    (hP : ∀ p, p ∈ P ↔ p.1 ∈ X ∧ p.2 ∈ X ∧ Disjoint (F p.1) (F p.2)) :
    X.card ^ 2 ≤ P.card + r * X.card * E.card := by
  classical
  let B := (X ×ˢ X).filter (fun p => ¬ Disjoint (F p.1) (F p.2))
  have hdisj : Disjoint P B := by
    rw [Finset.disjoint_left]
    intro p hpP hpB
    exact (Finset.mem_filter.mp hpB).2 ((hP p).mp hpP).2.2
  have hunion : P ∪ B = X ×ˢ X := by
    ext p
    rw [Finset.mem_union, hP, Finset.mem_filter, Finset.mem_product]
    constructor
    · rintro (⟨h1, h2, _⟩ | ⟨⟨h1, h2⟩, _⟩) <;> exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      by_cases hd : Disjoint (F p.1) (F p.2)
      · exact Or.inl ⟨h1, h2, hd⟩
      · exact Or.inr ⟨⟨h1, h2⟩, hd⟩
  have hsplit : P.card + B.card = X.card ^ 2 := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_product, sq]
  have hB : ∀ p ∈ B, p.1 ∈ X ∧ p.2 ∈ X ∧ ¬ Disjoint (F p.1) (F p.2) := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_product] at hp
    exact ⟨hp.1.1, hp.1.2, hp.2⟩
  calc
    X.card ^ 2 = P.card + B.card := hsplit.symm
    _ ≤ P.card + r * X.card * E.card :=
      Nat.add_le_add_left (card_nonDisjoint_pairs_le A r N X E hXle hE F hF B hB) P.card

/-- Each fiber `p_n = |{(x, y) ∈ P : x + y = n}|` satisfies `p_n ≤ |X| ≤ N`. -/
private lemma card_fiber_le_N (N : ℕ) (X : Finset ℕ)
    (hX_Icc : ∀ x ∈ X, 1 ≤ x ∧ x ≤ N)
    (P : Finset (ℕ × ℕ))
    (hP1 : ∀ p ∈ P, p.1 ∈ X)
    (n : ℕ) :
    (P.filter (fun p => p.1 + p.2 = n)).card ≤ N := by
  have hleX : (P.filter (fun p => p.1 + p.2 = n)).card ≤ X.card := by
    refine Finset.card_le_card_of_injOn Prod.fst ?_ ?_
    · intro p hp
      rw [Finset.mem_coe, Finset.mem_filter] at hp
      exact Finset.mem_coe.mpr (hP1 p hp.1)
    · intro p hp q hq hpq
      rw [Finset.mem_coe, Finset.mem_filter] at hp hq
      have h2 : p.2 = q.2 := Nat.add_left_cancel (hp.2.trans (hq.2.symm.trans (by rw [hpq])))
      exact Prod.ext hpq h2
  have hXsub : X ⊆ Finset.Icc 1 N := fun x hx => Finset.mem_Icc.mpr (hX_Icc x hx)
  have hXleN : X.card ≤ N := by
    calc
      X.card ≤ (Finset.Icc 1 N).card := Finset.card_le_card hXsub
      _ = N := by rw [Nat.card_Icc]; exact Nat.add_sub_cancel N 1
  exact hleX.trans hXleN

/-- A pairwise disjoint family of `Q` pairs in `P_n` witnesses `HasDisjointReps A (2 * r) Q n`. -/
private lemma hasDisjointReps_of_pairwiseDisj (A : Set ℕ) (r Q n : ℕ) (X : Finset ℕ)
    (F : ℕ → Finset ℕ)
    (hF : ∀ x ∈ X, ↑(F x) ⊆ A ∧ (F x).Nonempty ∧ (F x).card ≤ r ∧ ∑ u ∈ F x, u = x)
    (P : Finset (ℕ × ℕ))
    (hP : ∀ p ∈ P, p.1 ∈ X ∧ p.2 ∈ X ∧ Disjoint (F p.1) (F p.2))
    (M : Finset (ℕ × ℕ))
    (hM_sub : M ⊆ P.filter (fun p => p.1 + p.2 = n))
    (hM_pw : ∀ p ∈ M, ∀ q ∈ M, p ≠ q → Disjoint (F p.1 ∪ F p.2) (F q.1 ∪ F q.2))
    (hQle : Q ≤ M.card) :
    HasDisjointReps A (2 * r) Q n := by
  let e : Fin M.card ≃ M := M.equivFin.symm
  let idx : Fin Q → Fin M.card := fun i => ⟨i.1, Nat.lt_of_lt_of_le i.2 hQle⟩
  refine ⟨fun i => F (e (idx i)).1.1 ∪ F (e (idx i)).1.2, ?_, ?_⟩
  · intro i
    have hpPn := Finset.mem_filter.mp (hM_sub (e (idx i)).2)
    obtain ⟨hp1, hp2, hpdisj⟩ := hP _ hpPn.1
    obtain ⟨hA1, hne1, hcard1, hsum1⟩ := hF _ hp1
    obtain ⟨hA2, _, hcard2, hsum2⟩ := hF _ hp2
    refine ⟨?_, hne1.mono Finset.subset_union_left, ?_, ?_⟩
    · rw [Finset.coe_union]
      exact Set.union_subset hA1 hA2
    · calc
        (F (e (idx i)).1.1 ∪ F (e (idx i)).1.2).card
          ≤ (F (e (idx i)).1.1).card + (F (e (idx i)).1.2).card := Finset.card_union_le _ _
        _ ≤ r + r := Nat.add_le_add hcard1 hcard2
        _ = 2 * r := (two_mul r).symm
    · rw [Finset.sum_union hpdisj, hsum1, hsum2, hpPn.2]
  · intro i j hij
    have hidx : idx i ≠ idx j := fun h => hij (Fin.ext (congrArg (Fin.val : Fin M.card → ℕ) h))
    have hne : (e (idx i)).1 ≠ (e (idx j)).1 := fun h => hidx (e.injective (Subtype.ext h))
    exact hM_pw _ (e (idx i)).2 _ (e (idx j)).2 hne

/-- Fiber bound via projection onto the first coordinate containing `a`. -/
private lemma card_fiber_filter_fst_le (A : Set ℕ) (r N : ℕ) (X E : Finset ℕ)
    (hXle : ∀ x ∈ X, x ≤ N)
    (hE : ∀ y, y ≤ N → y ∈ R A (r - 1) → y ∈ E)
    (F : ℕ → Finset ℕ)
    (hF : ∀ x ∈ X, ↑(F x) ⊆ A ∧ (F x).Nonempty ∧ (F x).card ≤ r ∧ ∑ u ∈ F x, u = x)
    (P : Finset (ℕ × ℕ))
    (hP1 : ∀ p ∈ P, p.1 ∈ X)
    (n a : ℕ) :
    ((P.filter (fun p => p.1 + p.2 = n)).filter (fun q => a ∈ F q.1)).card ≤ E.card := by
  have h1 : ((P.filter (fun p => p.1 + p.2 = n)).filter (fun q => a ∈ F q.1)).card ≤
      (X.filter (fun x => a ∈ F x)).card := by
    refine Finset.card_le_card_of_injOn Prod.fst ?_ ?_
    · intro q hq
      rw [Finset.mem_coe, Finset.mem_filter] at hq ⊢
      exact ⟨hP1 q (Finset.mem_filter.mp hq.1).1, hq.2⟩
    · intro p hp q hq hpq
      rw [Finset.mem_coe, Finset.mem_filter] at hp hq
      have hps := (Finset.mem_filter.mp hp.1).2
      have hqs := (Finset.mem_filter.mp hq.1).2
      have h2 : p.2 = q.2 := Nat.add_left_cancel (hps.trans (hqs.symm.trans (by rw [hpq])))
      exact Prod.ext hpq h2
  exact h1.trans (card_filter_mem_rep_le A r N X E hXle hE F hF a)

/-- Fiber bound via projection onto the second coordinate containing `a`. -/
private lemma card_fiber_filter_snd_le (A : Set ℕ) (r N : ℕ) (X E : Finset ℕ)
    (hXle : ∀ x ∈ X, x ≤ N)
    (hE : ∀ y, y ≤ N → y ∈ R A (r - 1) → y ∈ E)
    (F : ℕ → Finset ℕ)
    (hF : ∀ x ∈ X, ↑(F x) ⊆ A ∧ (F x).Nonempty ∧ (F x).card ≤ r ∧ ∑ u ∈ F x, u = x)
    (P : Finset (ℕ × ℕ))
    (hP2 : ∀ p ∈ P, p.2 ∈ X)
    (n a : ℕ) :
    ((P.filter (fun p => p.1 + p.2 = n)).filter (fun q => a ∈ F q.2)).card ≤ E.card := by
  have h1 : ((P.filter (fun p => p.1 + p.2 = n)).filter (fun q => a ∈ F q.2)).card ≤
      (X.filter (fun y => a ∈ F y)).card := by
    refine Finset.card_le_card_of_injOn Prod.snd ?_ ?_
    · intro q hq
      rw [Finset.mem_coe, Finset.mem_filter] at hq ⊢
      exact ⟨hP2 q (Finset.mem_filter.mp hq.1).1, hq.2⟩
    · intro p hp q hq hpq
      rw [Finset.mem_coe, Finset.mem_filter] at hp hq
      have hps := (Finset.mem_filter.mp hp.1).2
      have hqs := (Finset.mem_filter.mp hq.1).2
      have h1' : p.1 = q.1 := Nat.add_right_cancel (hps.trans (hqs.symm.trans (by rw [hpq])))
      exact Prod.ext h1' hpq
  exact h1.trans (card_filter_mem_rep_le A r N X E hXle hE F hF a)

/-- If `n` does not have `Q` pairwise disjoint representations of size at most `2 * r`,
then `p_n ≤ 4 * r * (Q - 1) * |E|`. -/
private lemma card_fiber_le_of_not_hasDisjointReps (A : Set ℕ) (r Q N n : ℕ) (X E : Finset ℕ)
    (hXle : ∀ x ∈ X, x ≤ N)
    (hE : ∀ y, y ≤ N → y ∈ R A (r - 1) → y ∈ E)
    (F : ℕ → Finset ℕ)
    (hF : ∀ x ∈ X, ↑(F x) ⊆ A ∧ (F x).Nonempty ∧ (F x).card ≤ r ∧ ∑ u ∈ F x, u = x)
    (P : Finset (ℕ × ℕ))
    (hP : ∀ p ∈ P, p.1 ∈ X ∧ p.2 ∈ X ∧ Disjoint (F p.1) (F p.2))
    (hn : ¬ HasDisjointReps A (2 * r) Q n) :
    (P.filter (fun p => p.1 + p.2 = n)).card ≤ 4 * r * (Q - 1) * E.card := by
  classical
  let Pn := P.filter (fun p => p.1 + p.2 = n)
  let IsPW (M : Finset (ℕ × ℕ)) : Prop :=
    ∀ p ∈ M, ∀ q ∈ M, p ≠ q → Disjoint (F p.1 ∪ F p.2) (F q.1 ∪ F q.2)
  let Fam := Pn.powerset.filter IsPW
  have hFam_ne : Fam.Nonempty := by
    refine ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.empty_subset _), ?_⟩⟩
    intro p hp
    exact False.elim (Finset.notMem_empty p hp)
  obtain ⟨M, hM_mem, hM_max⟩ := Fam.exists_max_image Finset.card hFam_ne
  have hM_sub : M ⊆ Pn := Finset.mem_powerset.mp (Finset.mem_filter.mp hM_mem).1
  have hM_pw : IsPW M := (Finset.mem_filter.mp hM_mem).2
  have hM_lt : M.card < Q := by
    by_contra hge
    have hQle : Q ≤ M.card := Nat.le_of_not_lt hge
    exact hn (hasDisjointReps_of_pairwiseDisj A r Q n X F hF P hP M hM_sub hM_pw hQle)
  have hM_le : M.card ≤ Q - 1 := Nat.le_sub_one_of_lt hM_lt
  let V : Finset ℕ := M.biUnion fun p => F p.1 ∪ F p.2
  have hV_card : V.card ≤ 2 * r * (Q - 1) := by
    calc
      V.card ≤ ∑ p ∈ M, (F p.1 ∪ F p.2).card := Finset.card_biUnion_le
      _ ≤ ∑ p ∈ M, (2 * r) := by
        refine Finset.sum_le_sum fun p hp => ?_
        obtain ⟨hp1, hp2, _⟩ := hP p (Finset.mem_filter.mp (hM_sub hp)).1
        calc
          (F p.1 ∪ F p.2).card ≤ (F p.1).card + (F p.2).card := Finset.card_union_le _ _
          _ ≤ r + r := Nat.add_le_add (hF p.1 hp1).2.2.1 (hF p.2 hp2).2.2.1
          _ = 2 * r := (two_mul r).symm
      _ = M.card * (2 * r) := by simp only [Finset.sum_const, smul_eq_mul]
      _ ≤ (Q - 1) * (2 * r) := Nat.mul_le_mul_right (2 * r) hM_le
      _ = 2 * r * (Q - 1) := by ac_rfl
  have hhit : ∀ q ∈ Pn, ∃ a ∈ V, a ∈ F q.1 ∨ a ∈ F q.2 := by
    intro q hq
    by_contra hnone
    have hdisjV : Disjoint (F q.1 ∪ F q.2) V := by
      rw [Finset.disjoint_left]
      intro a ha haV
      rw [Finset.mem_union] at ha
      exact hnone ⟨a, haV, ha⟩
    have hq1 : q.1 ∈ X := (hP q (Finset.mem_filter.mp hq).1).1
    have hqNotM : q ∉ M := by
      intro hqM
      obtain ⟨u, hu⟩ := (hF q.1 hq1).2.1
      have huU : u ∈ F q.1 ∪ F q.2 := Finset.mem_union_left _ hu
      have huV : u ∈ V := Finset.mem_biUnion.mpr ⟨q, hqM, huU⟩
      exact Finset.disjoint_left.mp hdisjV huU huV
    have hins : insert q M ∈ Fam := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.insert_subset hq hM_sub), ?_⟩
      intro p₁ hp₁ p₂ hp₂ hne
      rcases Finset.mem_insert.mp hp₁ with rfl | hp₁M
      · rcases Finset.mem_insert.mp hp₂ with rfl | hp₂M
        · exact False.elim (hne rfl)
        · exact hdisjV.mono_right (Finset.subset_biUnion_of_mem (fun p => F p.1 ∪ F p.2) hp₂M)
      · rcases Finset.mem_insert.mp hp₂ with rfl | hp₂M
        · exact (hdisjV.mono_right (Finset.subset_biUnion_of_mem (fun p => F p.1 ∪ F p.2) hp₁M)).symm
        · exact hM_pw p₁ hp₁M p₂ hp₂M hne
    have hmax := hM_max (insert q M) hins
    rw [Finset.card_insert_of_notMem hqNotM] at hmax
    exact Nat.not_succ_le_self M.card hmax
  let L₁ (a : ℕ) := Pn.filter (fun q => a ∈ F q.1)
  let L₂ (a : ℕ) := Pn.filter (fun q => a ∈ F q.2)
  have hcover : Pn ⊆ V.biUnion fun a => L₁ a ∪ L₂ a := by
    intro q hq
    obtain ⟨a, haV, haq⟩ := hhit q hq
    refine Finset.mem_biUnion.mpr ⟨a, haV, ?_⟩
    rcases haq with ha1 | ha2
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hq, ha1⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hq, ha2⟩)
  have h4 : (4 : ℕ) = 2 * 2 := rfl
  calc
    Pn.card ≤ (V.biUnion fun a => L₁ a ∪ L₂ a).card := Finset.card_le_card hcover
    _ ≤ ∑ a ∈ V, (L₁ a ∪ L₂ a).card := Finset.card_biUnion_le
    _ ≤ ∑ a ∈ V, ((L₁ a).card + (L₂ a).card) :=
      Finset.sum_le_sum fun a _ => Finset.card_union_le _ _
    _ ≤ ∑ a ∈ V, (E.card + E.card) :=
      Finset.sum_le_sum fun a _ =>
        Nat.add_le_add (card_fiber_filter_fst_le A r N X E hXle hE F hF P (fun p hp => (hP p hp).1) n a)
          (card_fiber_filter_snd_le A r N X E hXle hE F hF P (fun p hp => (hP p hp).2.1) n a)
    _ = V.card * (2 * E.card) := by
      simp only [← two_mul, Finset.sum_const, smul_eq_mul]
    _ ≤ (2 * r * (Q - 1)) * (2 * E.card) := Nat.mul_le_mul_right (2 * E.card) hV_card
    _ = 4 * r * (Q - 1) * E.card := by rw [h4]; ac_rfl

/-- Upper bound on `|P|` obtained by summing the fiber bounds over `n ∈ [1, 2N]`. -/
private lemma card_pairs_le_sum (A : Set ℕ) (r Q N : ℕ) (X E D : Finset ℕ)
    (hX_Icc : ∀ x ∈ X, 1 ≤ x ∧ x ≤ N)
    (hE : ∀ y, y ≤ N → y ∈ R A (r - 1) → y ∈ E)
    (hD : ∀ n, n ∈ D ↔ 1 ≤ n ∧ n ≤ 2 * N ∧ 1 ≤ n ∧ HasDisjointReps A (2 * r) Q n)
    (F : ℕ → Finset ℕ)
    (hF : ∀ x ∈ X, ↑(F x) ⊆ A ∧ (F x).Nonempty ∧ (F x).card ≤ r ∧ ∑ u ∈ F x, u = x)
    (P : Finset (ℕ × ℕ))
    (hP : ∀ p ∈ P, p.1 ∈ X ∧ p.2 ∈ X ∧ Disjoint (F p.1) (F p.2)) :
    P.card ≤ N * D.card + 8 * r * (Q - 1) * E.card * N := by
  have hmaps : ∀ p ∈ P, p.1 + p.2 ∈ Finset.Icc 1 (2 * N) := by
    intro p hp
    obtain ⟨hp1, hp2, _⟩ := hP p hp
    have h1 := hX_Icc p.1 hp1
    have h2 := hX_Icc p.2 hp2
    rw [Finset.mem_Icc]
    exact ⟨Nat.le_add_right_of_le h1.1, by rw [two_mul]; exact Nat.add_le_add h1.2 h2.2⟩
  have hfib : P.card =
      ∑ n ∈ Finset.Icc 1 (2 * N), (P.filter (fun p => p.1 + p.2 = n)).card :=
    Finset.card_eq_sum_card_fiberwise (f := fun p : ℕ × ℕ => p.1 + p.2)
      (s := P) (t := Finset.Icc 1 (2 * N))
      (fun p hp => Finset.mem_coe.mpr (hmaps p (Finset.mem_coe.mp hp)))
  have hterm : ∀ n ∈ Finset.Icc 1 (2 * N),
      (P.filter (fun p => p.1 + p.2 = n)).card ≤
        (if n ∈ D then N else 0) + 4 * r * (Q - 1) * E.card := by
    intro n hn
    by_cases hnD : n ∈ D
    · rw [if_pos hnD]
      exact (card_fiber_le_N N X hX_Icc P (fun p hp => (hP p hp).1) n).trans (Nat.le_add_right _ _)
    · rw [if_neg hnD, zero_add]
      have hnIcc := Finset.mem_Icc.mp hn
      have hnot : ¬ HasDisjointReps A (2 * r) Q n :=
        fun hrep => hnD ((hD n).mpr ⟨hnIcc.1, hnIcc.2, hnIcc.1, hrep⟩)
      exact card_fiber_le_of_not_hasDisjointReps A r Q N n X E
        (fun x hx => (hX_Icc x hx).2) hE F hF P hP hnot
  have hD_filter : (Finset.Icc 1 (2 * N)).filter (· ∈ D) = D := by
    ext n
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨fun h => h.2, fun h => ⟨⟨((hD n).mp h).1, ((hD n).mp h).2.1⟩, h⟩⟩
  have hD_sum : (∑ n ∈ Finset.Icc 1 (2 * N), if n ∈ D then N else 0) = N * D.card := by
    rw [← Finset.sum_filter, hD_filter, Finset.sum_const, smul_eq_mul, mul_comm]
  have hIcc_card : (Finset.Icc 1 (2 * N)).card = 2 * N := by
    rw [Nat.card_Icc]
    exact Nat.add_sub_cancel (2 * N) 1
  have h8 : (8 : ℕ) = 2 * 4 := rfl
  calc
    P.card = ∑ n ∈ Finset.Icc 1 (2 * N), (P.filter (fun p => p.1 + p.2 = n)).card := hfib
    _ ≤ ∑ n ∈ Finset.Icc 1 (2 * N),
        ((if n ∈ D then N else 0) + 4 * r * (Q - 1) * E.card) :=
      Finset.sum_le_sum hterm
    _ = (∑ n ∈ Finset.Icc 1 (2 * N), if n ∈ D then N else 0)
        + ∑ n ∈ Finset.Icc 1 (2 * N), (4 * r * (Q - 1) * E.card) :=
      Finset.sum_add_distrib
    _ = N * D.card + (2 * N) * (4 * r * (Q - 1) * E.card) := by
      rw [hD_sum, Finset.sum_const, smul_eq_mul, hIcc_card]
    _ = N * D.card + 8 * r * (Q - 1) * E.card * N := by rw [h8]; ac_rfl

end L3

theorem lemma3 (A : Set ℕ) (r Q N : ℕ) (hr : 1 ≤ r) (hQ : 1 ≤ Q) :
    (R A r ∩ Set.Icc 1 N).ncard ^ 2 ≤
      r * (R A r ∩ Set.Icc 1 N).ncard * (R A (r - 1) ∩ Set.Icc 0 N).ncard
      + N * ({n | 1 ≤ n ∧ HasDisjointReps A (2 * r) Q n} ∩ Set.Icc 1 (2 * N)).ncard
      + 8 * r * (Q - 1) * (R A (r - 1) ∩ Set.Icc 0 N).ncard * N := by
  classical
  have _ := hr
  have _ := hQ
  obtain ⟨X, hX, hXcard⟩ := L3.exists_finset_inter_Icc (R A r) 1 N
  obtain ⟨E, hE, hEcard⟩ := L3.exists_finset_inter_Icc (R A (r - 1)) 0 N
  obtain ⟨D, hD, hDcard⟩ :=
    L3.exists_finset_inter_Icc {n | 1 ≤ n ∧ HasDisjointReps A (2 * r) Q n} 1 (2 * N)
  rw [hXcard, hEcard, hDcard]
  have hX_Icc : ∀ x ∈ X, 1 ≤ x ∧ x ≤ N := fun x hx => ⟨((hX x).mp hx).1, ((hX x).mp hx).2.1⟩
  have hXle : ∀ x ∈ X, x ≤ N := fun x hx => ((hX x).mp hx).2.1
  have hE_of : ∀ y, y ≤ N → y ∈ R A (r - 1) → y ∈ E :=
    fun y hyN hyR => (hE y).mpr ⟨Nat.zero_le y, hyN, hyR⟩
  obtain ⟨F, hF⟩ := L3.exists_rep_fn A r X (fun x hx => ⟨((hX x).mp hx).1, ((hX x).mp hx).2.2⟩)
  let P := (X ×ˢ X).filter (fun p => Disjoint (F p.1) (F p.2))
  have hP : ∀ p, p ∈ P ↔ p.1 ∈ X ∧ p.2 ∈ X ∧ Disjoint (F p.1) (F p.2) := by
    intro p
    rw [Finset.mem_filter, Finset.mem_product, and_assoc]
  have hlow := L3.card_sq_le_card_pairs_add A r N X E hXle hE_of F hF P hP
  have hhigh := L3.card_pairs_le_sum A r Q N X E D hX_Icc hE_of hD F hF P (fun p hp => (hP p).mp hp)
  calc
    X.card ^ 2 ≤ P.card + r * X.card * E.card := hlow
    _ ≤ (N * D.card + 8 * r * (Q - 1) * E.card * N) + r * X.card * E.card :=
      Nat.add_le_add_right hhigh _
    _ = r * X.card * E.card + N * D.card + 8 * r * (Q - 1) * E.card * N := by ac_rfl

end Erdos338Campaign

end

section

/-
Erdős 338 campaign, piece `local_complete`: local completeness from finite removal.

If `A \ F` is a basis of finite order for every finite set `F`, then for every modulus `q ≥ 1`
every residue class modulo `q` contains a sum of distinct elements of `A`. This is the local
completeness step in the proof of Theorem 1 of S.-Q. Chen, Q.-H. Yang and L. Zhao, *On a problem
of Erdős and Graham related to restricted order*, arXiv:2611.33191v1 (CYZ), §5, pp. 16–17.

Route. The Lean proof follows Daniel Veljjanoski's argument, not the gcd and Bézout argument of
CYZ §5. Fix `q ≥ 1` and let `F` be the set of the elements of `A` whose residue class modulo `q`
contains only finitely many elements of `A`. There are at most `q` such classes, so `F` is finite
(`LC.finite_sparse`) and `A \ F` is still a basis. Write `v + q * N`, with `N` large, as a sum of
elements of `A \ F`, repetition allowed. Every summand lies in a class that contains infinitely
many elements of `A`, so the summands can be replaced one at a time by pairwise distinct elements
of `A` in the same classes (`LC.exists_distinct_sum`). The new sum is congruent to `v` modulo `q`.

Source and licence. `local_complete`, `LC.finite_sparse` and `LC.exists_distinct_sum` are adapted
from the declaration `Erdos338Proof.residue_of_robust` in the file `Erdos338/Residue.lean` of
Daniel Veljjanoski's Lean proof of the positive lower density case of Erdős Problem 338 (Palomar
registry entry PALOMAR-2026-11-03-000016, repository erdos338-palomar at commit a699263), which
is licensed under the Apache License, Version 2.0. Its notice follows, without the quotation
marks of the standard text, because the board file format does not allow that character.

    Licensed under the Apache License, Version 2.0 (the License); you may not use this file
    except in compliance with the License. You may obtain a copy of the License at

        http://www.apache.org/licenses/LICENSE-2.0

    Unless required by applicable law or agreed to in writing, software distributed under the
    License is distributed on an AS IS BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND,
    either express or implied. See the License for the specific language governing permissions
    and limitations under the License.

Changes made to the adapted declaration: the hypothesis is stated with `Erdos338.HasOrder` and the
conclusion with `↑S ⊆ A`, as in the campaign interface; the two steps of the proof are separate
lemmas in the namespace `Erdos338Campaign.LC`; the finiteness of `F` is proved with
`Set.Finite.of_finite_fibers`; the replacement lemma no longer needs its summands to lie in `A`;
and the arithmetic side goals are closed by explicit terms. `residue_uniform` from the same file
is not ported, because the campaign gets its uniform bound from `theorem3`.

The Lean in this file was written by Claude Fable 5.2 (Anthropic) on Nov 27, 2026.
-/

open Finset Erdos338

namespace Erdos338Campaign

namespace LC

/-- For `q ≥ 1`, only finitely many elements of `A` lie in a residue class modulo `q` that
contains finitely many elements of `A`: the map `a ↦ a % q` takes at most `q` values on this set
and each of its fibres is finite. -/
theorem finite_sparse (A : Set ℕ) {q : ℕ} (hq : 0 < q) :
    {a | a ∈ A ∧ {x | x ∈ A ∧ x ≡ a [MOD q]}.Finite}.Finite := by
  refine Set.Finite.of_finite_fibers (fun a => a % q) ((Set.finite_lt_nat q).subset ?_) ?_
  · rintro _ ⟨a, -, rfl⟩
    exact Nat.mod_lt a hq
  · rintro _ ⟨a, ha, rfl⟩
    exact ha.2.subset fun x hx => ⟨hx.1.1, hx.2⟩

/-- If every element of the multiset `M` lies in a residue class modulo `q` that contains
infinitely many elements of `A`, then `M.sum` is congruent modulo `q` to a sum of distinct
elements of `A`: replace the elements of `M` one at a time by new elements of `A` in the same
classes. -/
theorem exists_distinct_sum (A : Set ℕ) (q : ℕ) (M : Multiset ℕ)
    (hM : ∀ a ∈ M, {x | x ∈ A ∧ x ≡ a [MOD q]}.Infinite) :
    ∃ S : Finset ℕ, ↑S ⊆ A ∧ ∑ x ∈ S, x ≡ M.sum [MOD q] := by
  induction M using Multiset.induction_on with
  | empty =>
    refine ⟨∅, ?_, ?_⟩
    · rw [Finset.coe_empty]
      exact Set.empty_subset A
    · exact congrArg (fun n => n % q) (Finset.sum_empty.trans Multiset.sum_zero.symm)
  | cons a M ih =>
    obtain ⟨S, hSA, hS⟩ := ih fun x hx => hM x (Multiset.mem_cons_of_mem hx)
    obtain ⟨b, ⟨hbA, hba⟩, hbS⟩ := (hM a (Multiset.mem_cons_self a M)).exists_notMem_finset S
    refine ⟨insert b S, ?_, ?_⟩
    · rw [Finset.coe_insert]
      exact Set.insert_subset hbA hSA
    · rw [Finset.sum_insert hbS, Multiset.sum_cons]
      exact hba.add hS

end LC

/-- CYZ §5 (pp. 16–17), local completeness: if `A \ F` is a basis for every finite `F`, then for
every `q ≥ 1` every residue class modulo `q` contains a sum of distinct elements of `A`. Adapted
from Daniel Veljjanoski's `Erdos338Proof.residue_of_robust`. -/
theorem local_complete (A : Set ℕ) (hA : ∀ F : Set ℕ, F.Finite → ∃ h, HasOrder (A \ F) h) :
    ∀ q, 0 < q → ∀ v, ∃ S : Finset ℕ, ↑S ⊆ A ∧ ∑ x ∈ S, x ≡ v [MOD q] := by
  intro q hq v
  obtain ⟨h, hh⟩ := hA _ (LC.finite_sparse A hq)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hh
  obtain ⟨M, hM, -, hsum⟩ :=
    hN (v + q * N) ((Nat.le_mul_of_pos_left N hq).trans (Nat.le_add_left (q * N) v))
  obtain ⟨S, hSA, hS⟩ := LC.exists_distinct_sum A q M
    fun a ha hfin => (hM a ha).2 ⟨(hM a ha).1, hfin⟩
  refine ⟨S, hSA, hS.trans ?_⟩
  rw [hsum]
  exact Nat.add_mul_mod_self_left v q N

end Erdos338Campaign

end

section

/-
Theorem 3 of the Erdős 338 campaign. Chen, Yang and Zhao, arXiv:2611.33191v1,
Theorem 3, pp. 10–14. This proof uses finite refinements of congruence
classes and the least number of summands covering a class. The Lean code is
original to this piece, written by GPT-6.2 Astra at max reasoning effort.
-/

open Finset Erdos338

namespace Erdos338Campaign
namespace T3

structure ResidueClass where
  modulus : ℕ
  pos : 0 < modulus
  residue : ℕ

def Refines (c b : ResidueClass) : Prop :=
  b.modulus ∣ c.modulus ∧ c.residue ≡ b.residue [MOD b.modulus]

theorem Refines.refl (b : ResidueClass) : Refines b b :=
  ⟨dvd_refl _, Nat.ModEq.rfl⟩

theorem Refines.project {c b : ResidueClass} (h : Refines c b) {x : ℕ}
    (hx : x ≡ c.residue [MOD c.modulus]) : x ≡ b.residue [MOD b.modulus] :=
  (Nat.ModEq.of_dvd h.1 hx).trans h.2

theorem Refines.trans {c b d : ResidueClass} (h : Refines c b) (h' : Refines b d) :
    Refines c d := ⟨dvd_trans h'.1 h.1, h'.project h.2⟩

/-- Ordinary sums of at most k terms meet every finer congruence class. -/
def Covers (A : Set ℕ) (k : ℕ) (b : ResidueClass) : Prop :=
  ∀ c : ResidueClass, Refines c b →
    ∃ M : Multiset ℕ, (∀ x ∈ M, x ∈ A) ∧ M.card ≤ k ∧ M.sum ≡ c.residue [MOD c.modulus]

theorem exists_cover {A : Set ℕ} (hord : ∃ h, HasOrder A h) :
    ∃ k, ∃ b, Covers A k b := by
  obtain ⟨h, hh⟩ := hord
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hh
  refine ⟨h, ⟨1, Nat.zero_lt_one, 0⟩, fun c _ => ?_⟩
  have hle : N ≤ c.modulus * N + c.residue :=
    (Nat.le_mul_of_pos_left N c.pos).trans (Nat.le_add_right _ _)
  obtain ⟨M, hA, hc, hs⟩ := hN _ hle
  exact ⟨M, hA, hc, hs ▸ Nat.ModEq.modulus_mul_add⟩

theorem exists_complement {q : ℕ} (hq : 0 < q) (a v : ℕ) :
    ∃ w : ℕ, a + w ≡ v [MOD q] := by
  have hle : a ≤ q * a + v :=
    (Nat.le_mul_of_pos_left a hq).trans (Nat.le_add_right _ _)
  refine ⟨q * a + v - a, ?_⟩
  rw [Nat.add_sub_of_le hle]
  exact Nat.ModEq.modulus_mul_add

/-- Off a translate of the sums of size at most k, a representation of size
at most k + 1 cannot use the translating element. -/
theorem avoid_one {A : Set ℕ} {k : ℕ} (hmin : ∀ j < k, ¬ ∃ b, Covers A j b)
    (b : ResidueClass) (a : ℕ) :
    ∃ c, Refines c b ∧ ∀ M : Multiset ℕ, (∀ x ∈ M, x ∈ A) → M.card ≤ k →
      M.sum ≡ c.residue [MOD c.modulus] → a ∉ M := by
  classical
  cases k with
  | zero =>
    refine ⟨b, Refines.refl b, fun M _ hc _ => ?_⟩
    have hM := Multiset.card_eq_zero.mp (Nat.le_zero.mp hc)
    simp only [hM, Multiset.notMem_zero, not_false_eq_true]
  | succ k =>
    obtain ⟨s, hs⟩ := exists_complement b.pos a b.residue
    let bs : ResidueClass := ⟨b.modulus, b.pos, s⟩
    have hmiss : ¬ Covers A k bs := fun hc => hmin k (Nat.lt_succ_self k) ⟨bs, hc⟩
    unfold Covers at hmiss
    obtain ⟨d, hbad⟩ := Classical.not_forall.mp hmiss
    obtain ⟨hd, hnone⟩ := Classical.not_imp.mp hbad
    let c : ResidueClass := ⟨d.modulus, d.pos, a + d.residue⟩
    refine ⟨c, ⟨hd.1, (hd.2.add_left a).trans hs⟩, ?_⟩
    intro M hA hc hsum ha
    have hcard := congrArg Multiset.card (Multiset.cons_erase ha)
    have heq := congrArg Multiset.sum (Multiset.cons_erase ha)
    rw [Multiset.card_cons] at hcard
    rw [Multiset.sum_cons] at heq
    apply hnone
    refine ⟨M.erase a, fun x hx => hA x (Multiset.erase_subset a M hx), by omega, ?_⟩
    exact Nat.ModEq.add_left_cancel' a (heq ▸ hsum)

/-- Successive refinements exclude a finite list of possible summands.
Each earlier exclusion persists under all subsequent refinements. -/
theorem avoid_finite {A : Set ℕ} {k : ℕ} (hmin : ∀ j < k, ¬ ∃ b, Covers A j b)
    (F : Finset ℕ) (b : ResidueClass) :
    ∃ c, Refines c b ∧ ∀ M : Multiset ℕ, (∀ x ∈ M, x ∈ A) → M.card ≤ k →
      M.sum ≡ c.residue [MOD c.modulus] → ∀ a ∈ F, a ∉ M := by
  classical
  induction F using Finset.induction_on generalizing b with
  | empty =>
    exact ⟨b, Refines.refl b, fun _ _ _ _ a ha => (Finset.notMem_empty a ha).elim⟩
  | @insert a F _ ih =>
    obtain ⟨d, hdb, hF⟩ := ih b
    obtain ⟨c, hcd, ha⟩ := avoid_one hmin d a
    refine ⟨c, hcd.trans hdb, fun M hA hc hs x hx => ?_⟩
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact ha M hA hc hs
    · exact hF M hA hc (hcd.project hs) x hx

/-- A residue can be lifted outside every prescribed finite set. -/
def Fresh (A : Set ℕ) (q a : ℕ) : Prop :=
  ∀ F : Finset ℕ, ∃ y ∈ A, y ∉ F ∧ y ≡ a [MOD q]

/-- The residue classes with only finitely many lifts have finite union. -/
theorem fresh_outside_finite (A : Set ℕ) (q : ℕ) (hq : 0 < q) :
    ∃ E : Finset ℕ, ∀ a ∈ A, a ∉ E → Fresh A q a := by
  classical
  let fiber (r : Fin q) : Set ℕ := {x | x ∈ A ∧ x ≡ r.val [MOD q]}
  let rare (r : Fin q) : Finset ℕ :=
    if h : (fiber r).Finite then h.toFinset else ∅
  refine ⟨Finset.univ.biUnion rare, fun a ha hE F => ?_⟩
  let r : Fin q := ⟨a % q, Nat.mod_lt _ hq⟩
  have har : a ≡ r.val [MOD q] := (Nat.mod_modEq a q).symm
  have einf : (fiber r).Infinite := by
    intro hfin
    apply hE
    refine Finset.mem_biUnion.mpr ⟨r, Finset.mem_univ _, ?_⟩
    have haf : a ∈ fiber r := ⟨ha, har⟩
    simpa only [rare, dif_pos hfin, Set.Finite.mem_toFinset] using haf
  obtain ⟨y, hy, hyF⟩ := einf.exists_notMem_finset F
  exact ⟨y, hy.1, hyF, hy.2.trans har.symm⟩

/-- Replace every occurrence by a fresh element of its residue class. -/
theorem lift_distinct {A : Set ℕ} {q : ℕ} (F : Finset ℕ) (M : Multiset ℕ)
    (hfresh : ∀ x ∈ M, Fresh A q x) :
    ∃ S : Finset ℕ, ↑S ⊆ A ∧ Disjoint F S ∧ S.card = M.card ∧
      ∑ x ∈ S, x ≡ M.sum [MOD q] := by
  classical
  induction M using Multiset.induction_on with
  | empty => exact ⟨∅, by simp, by simp, by simp, Nat.ModEq.rfl⟩
  | @cons a M ih =>
    obtain ⟨S, hS, hd, hc, hs⟩ := ih fun x hx => hfresh x (Multiset.mem_cons_of_mem hx)
    obtain ⟨y, hy, hn, he⟩ := hfresh a (Multiset.mem_cons_self a M) (F ∪ S)
    have hyF : y ∉ F := fun h => hn (Finset.mem_union_left _ h)
    have hyS : y ∉ S := fun h => hn (Finset.mem_union_right _ h)
    refine ⟨insert y S, ?_, Finset.disjoint_insert_right.mpr ⟨hyF, hd⟩, ?_, ?_⟩
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hy
      · exact hS hx
    · rw [Finset.card_insert_of_notMem hyS, Multiset.card_cons, hc]
    · rw [Finset.sum_insert hyS, Multiset.sum_cons]
      exact he.add hs

/-- One congruence class has restricted representations, with one common
budget, in every refinement and outside every finite forbidden set. -/
theorem restricted_class {A : Set ℕ} (hord : ∃ h, HasOrder A h) :
    ∃ k b, ∀ c, Refines c b → ∀ F : Finset ℕ,
      ∃ S : Finset ℕ, ↑S ⊆ A ∧ Disjoint F S ∧ S.card ≤ k ∧
        ∑ x ∈ S, x ≡ c.residue [MOD c.modulus] := by
  classical
  have hex := exists_cover hord
  let k := Nat.find hex
  obtain ⟨b, hb⟩ := Nat.find_spec hex
  have hmin (j : ℕ) (hj : j < k) : ¬ ∃ d, Covers A j d := Nat.find_min hex hj
  refine ⟨k, b, fun c hcb F => ?_⟩
  obtain ⟨E, hE⟩ := fresh_outside_finite A c.modulus c.pos
  obtain ⟨d, hdc, havoid⟩ := avoid_finite hmin E c
  obtain ⟨M, hA, hc, hs⟩ := hb d (hdc.trans hcb)
  have hfr (x : ℕ) (hx : x ∈ M) : Fresh A c.modulus x :=
    hE x (hA x hx) (fun hxE => havoid M hA hc hs x hxE hx)
  obtain ⟨S, hS, hd, hcard, hsum⟩ := lift_distinct F M hfr
  exact ⟨S, hS, hd, hcard.le.trans hc, hsum.trans (hdc.project hs)⟩

end T3

theorem theorem3 (A : Set ℕ) (hord : ∃ h, HasOrder A h)
    (hloc : ∀ q, 0 < q → ∀ v, ∃ S : Finset ℕ, ↑S ⊆ A ∧ ∑ x ∈ S, x ≡ v [MOD q]) :
    ∃ H : ℕ, ∀ q, 0 < q → ∀ v, ∃ S : Finset ℕ, ↑S ⊆ A ∧ S.card ≤ H ∧ ∑ x ∈ S, x ≡ v [MOD q] := by
  classical
  obtain ⟨k, b, hb⟩ := T3.restricted_class hord
  choose E hEA hEmod using fun r : Fin b.modulus => hloc b.modulus b.pos r.val
  let B := Finset.univ.sup fun r => (E r).card
  refine ⟨B + k, fun q hq v => ?_⟩
  obtain ⟨w, hw⟩ := T3.exists_complement b.pos b.residue v
  let r : Fin b.modulus := ⟨w % b.modulus, Nat.mod_lt _ b.pos⟩
  let e := ∑ x ∈ E r, x
  have he : e + b.residue ≡ v [MOD b.modulus] := by
    rw [Nat.add_comm]
    exact (((hEmod r).trans (Nat.mod_modEq w _)).add_left b.residue).trans hw
  let Q := q * b.modulus
  have hQ : 0 < Q := Nat.mul_pos hq b.pos
  have hgQ : b.modulus ∣ Q := dvd_mul_left _ _
  have hqQ : q ∣ Q := dvd_mul_right _ _
  obtain ⟨s, hs⟩ := T3.exists_complement hQ e v
  have hsb : s ≡ b.residue [MOD b.modulus] :=
    Nat.ModEq.add_left_cancel' e ((Nat.ModEq.of_dvd hgQ hs).trans he.symm)
  obtain ⟨S, hS, hd, hc, hsum⟩ := hb ⟨Q, hQ, s⟩ ⟨hgQ, hsb⟩ (E r)
  refine ⟨E r ∪ S, ?_, ?_, ?_⟩
  · rw [Finset.coe_union]
    exact Set.union_subset (hEA r) hS
  · rw [Finset.card_union_of_disjoint hd]
    exact Nat.add_le_add (Finset.le_sup (f := fun i => (E i).card) (Finset.mem_univ r)) hc
  · rw [Finset.sum_union hd]
    exact Nat.ModEq.of_dvd hqQ ((hsum.add_left e).trans hs)

end Erdos338Campaign

end

open Finset Erdos338

namespace Erdos338Campaign

theorem lemma4 (A : Set ℕ) (h : ℕ) (hh : 1 ≤ h)
    (hdens : ∃ c N₀ : ℕ, 0 < c ∧ ∀ N ≥ N₀, N ≤ c * (R A h ∩ Set.Icc 1 N).ncard) (b : ℕ) :
    ∃ K g a N₀ : ℕ, 0 < g ∧ ∀ F : Finset ℕ, F.card ≤ b →
      ∀ n ≥ N₀, n ≡ a [MOD g] → n ∈ R (A \ ↑F) K :=
  lemma4_of_pairs lemma3 A h hh hdens b

theorem theorem2 (A : Set ℕ) (hord : ∃ h, HasOrder A h)
    (hloc : ∀ q, 0 < q → ∀ v, ∃ S : Finset ℕ, ↑S ⊆ A ∧ ∑ x ∈ S, x ≡ v [MOD q]) :
    ∃ t, HasRestrictedOrder A t :=
  theorem2_of_pieces lemma2 lemma4 theorem3 A hord hloc

/-- CYZ Theorem 1. -/
theorem theorem1 (A : Set ℕ) (hA : ∀ F : Set ℕ, F.Finite → ∃ h, HasOrder (A \ F) h) :
    ∃ t, HasRestrictedOrder A t :=
  theorem2 A (by simpa using hA ∅ Set.finite_empty) (local_complete A hA)

theorem board_basis : type_of% @Erdos338.erdos_338.variants.basis_after_finite_removal :=
  board_basis_of_theorem1 theorem1

theorem board_same_order : type_of% @Erdos338.erdos_338.variants.same_order_after_finite_removal :=
  board_same_order_of_theorem1 theorem1

end Erdos338Campaign

theorem OMA.solution : type_of% @Erdos338.erdos_338.variants.same_order_after_finite_removal := Erdos338Campaign.board_same_order
