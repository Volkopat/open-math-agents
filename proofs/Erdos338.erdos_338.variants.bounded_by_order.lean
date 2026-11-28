import FormalConjectures.ErdosProblems.«338»

-- Problem: Erdős Problem 338, variant bounded_by_order: the restricted order of an asymptotic basis
-- of order at most h, when finite, is bounded by a function of h alone.
-- Credit: @marcusbuffett (solver of record on Left to Solve).
--
-- PORT OF A PUBLIC PROOF, not a new result. Source: github.com/shoebyron/erdos-338-ii,
-- commit 527406e093744fcb4ae8c921d689ab143857a7d9 (author Excession, exsn.org), MIT License:
--   Copyright (c) 2026 Excession
--   Permission is hereby granted, free of charge, to any person obtaining a copy of this software
--   and associated documentation files (the Software), to deal in the Software without restriction,
--   including without limitation the rights to use, copy, modify, merge, publish, distribute,
--   sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
--   furnished to do so, subject to the following conditions: The above copyright notice and this
--   permission notice shall be included in all copies or substantial portions of the Software.
--   THE SOFTWARE IS PROVIDED AS IS, WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
--   NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
--   NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
--   DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
--   OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
-- Its module SingleSetCovering is adapted from github.com/veljjanoski/erdos338-palomar (Daniel
-- Veljjanoski, commit a699263d0f7cdce0e5b3026bce86eab30973d0f8, files Covering, Structure and
-- Shift), distributed under the Apache License, Version 2.0.
-- Kneser's theorem (modules MiscYD.AddCombi.Kneser.MulStab and Kneser) is from
-- github.com/YaelDillies/misc-yd, commit cd12c538d66f15a358a6904e7c847cd67661096f:
--   Copyright (c) 2023 Mantas Bakšys, Yaël Dillies. All rights reserved.
--   Released under Apache 2.0 license. Authors: Mantas Bakšys, Yaël Dillies.
-- The Apache-2.0 parts are used under the Apache License, Version 2.0; you may obtain a copy at
-- https://www.apache.org/licenses/LICENSE-2.0 . Distributed on an AS IS BASIS, WITHOUT WARRANTIES OR
-- CONDITIONS OF ANY KIND.
-- Changes here: modules concatenated into one file (each in its own section), comments and #check /
-- #print lines removed, namespace Erdos338 renamed to OMA.E338, to_additive attributes removed: the
-- additive Kneser statements the proof uses (addStab, add_kneser and a few addStab lemmas) are
-- derived here from the multiplicative ones by transfer through Multiplicative (section after
-- module Kneser, new), compatibility lemmas for the pinned Lean 4.33.1 Mathlib at the top.

theorem ite_eq_left {α : Sort*} {c : Prop} [Decidable c] {a b : α} (h : c) : ite c a b = a := if_pos h
theorem ite_eq_right {α : Sort*} {c : Prop} [Decidable c] {a b : α} (h : ¬c) : ite c a b = b := if_neg h
theorem dite_eq_left {α : Sort*} {c : Prop} [Decidable c] {a : c → α} {b : ¬c → α} (h : c) :
    dite c a b = a h := dif_pos h
theorem List.Sublist.prod_le_prod {l₁ l₂ : List ℕ} (h : l₁.Sublist l₂) (h₁ : ∀ a ∈ l₂, 1 ≤ a) :
    l₁.prod ≤ l₂.prod := h.prod_le_prod' h₁
theorem Finset.prod_le_prod₀ {ι : Type*} {s : Finset ι} {f g : ι → ℝ} (h0 : ∀ i ∈ s, 0 ≤ f i)
    (h1 : ∀ i ∈ s, f i ≤ g i) : ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := Finset.prod_le_prod h0 h1
-- module MiscYD.AddCombi.Kneser.MulStab
section
section
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
protected theorem Nonempty.one_mem_mulStab (h : s.Nonempty) : (1 : α) ∈ s.mulStab :=
  one_mem_mulStab.2 h
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
    QuotientGroup.mk ⁻¹' ((Set.image ((↑) : α → α ⧸ stabilizer α (t : Set α)) s)) = s * t.mulStab := by
  rw [QuotientGroup.preimage_image_mk_eq_mul, coe_mulStab ht, stabilizer_coe_finset]
omit [DecidableEq α] in
lemma preimage_image_quotientMk_mulStabilizer (s : Finset α) :
    QuotientGroup.mk ⁻¹' ((Set.image ((↑) : α → α ⧸ stabilizer α (s : Set α)) s)) = s := by
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
private def fintypeStabilizerOfMulStab (hs : s.Nonempty) : Fintype (stabilizer α s) where
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
    #t.mulStab * #((Finset.image ((↑) : α → α ⧸ stabilizer α (t : Set α)) s)) = #(s * t.mulStab) := by
  obtain rfl | ht := t.eq_empty_or_nonempty
  · simp
  have := QuotientGroup.preimageMkEquivSubgroupProdSet _ ((Set.image ((↑) : α → α ⧸ stabilizer α (t : Set α)) s))
  have that : ↥(stabilizer α (t : Set α)) = ↥t.mulStab := by
    rw [← SetLike.coe_sort_coe, ← coe_mulStab ht, Finset.coe_sort_coe]
  have temp := this.trans ((Equiv.cast that).prodCongr (Equiv.refl _))
  rw [preimage_image_quotientMk_stabilizer_eq_mul_mulStab ht] at temp
  simpa only [coe_sort_coe, ← coe_mul, Fintype.card_prod, Fintype.card_coe, Fintype.card_ofFinset,
    toFinset_coe, mem_image, Set.mem_image, mem_coe, forall_const, eq_comm]
    using Fintype.card_congr temp
lemma card_mul_card_eq_mulStab_card_mul_coe (s t : Finset α) :
    #(s * t) = #(s * t).mulStab * #((Finset.image ((↑) : α → α ⧸ stabilizer α (↑(s * t) : Set α)) (s * t))) := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  obtain rfl | ht := t.eq_empty_or_nonempty
  · simp
  have := QuotientGroup.preimageMkEquivSubgroupProdSet _ <|
    (Set.image ((↑) : α → α ⧸ stabilizer α (↑(s * t) : Set α)) ↑(s * t))
  have that : ↥(stabilizer α (↑(s * t) : Set α)) = ↥(s * t).mulStab := by
    rw [← SetLike.coe_sort_coe, ← coe_mulStab (hs.mul ht), Finset.coe_sort_coe]
  have temp := this.trans <| (Equiv.cast that).prodCongr (Equiv.refl _)
  rw [preimage_image_quotientMk_mulStabilizer] at temp
  simpa [-coe_mul] using Fintype.card_congr temp
lemma card_mulStab_mul_card_image_coe (s t : Finset α) :
    #(s * t).mulStab *
      #(((Finset.image ((↑) : α → α ⧸ stabilizer α (↑(s * t) : Set α)) s)) * ((Finset.image ((↑) : α → α ⧸ stabilizer α (↑(s * t) : Set α)) t))) =
        #(s * t) := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  obtain rfl | ht := t.eq_empty_or_nonempty
  · simp
  let this := QuotientGroup.preimageMkEquivSubgroupProdSet (stabilizer α (↑(s * t) : Set α))
    (((Set.image ((↑) : α → α ⧸ stabilizer α (↑(s * t) : Set α)) s)) * ((Set.image ((↑) : α → α ⧸ stabilizer α (↑(s * t) : Set α)) t)))
  have image_coe_mul :
    ((Set.image ((↑) : α → α ⧸ stabilizer α (↑(s * t) : Set α)) (↑(s * t) : Set α))) =
      ((Set.image ((↑) : α → α ⧸ stabilizer α (↑(s * t) : Set α)) s)) * ((Set.image ((↑) : α → α ⧸ stabilizer α (↑(s * t) : Set α)) t)) := by
    simpa [coe_mul] using Set.image_mul (QuotientGroup.mk' (stabilizer α (↑(s * t) : Set α)))
  rw [← image_coe_mul, preimage_image_quotientMk_mulStabilizer, image_coe_mul] at this
  have that :
    (stabilizer α (↑(s * t) : Set α) ×
      ↥(((Set.image ((↑) : α → α ⧸ stabilizer α (↑(s * t) : Set α)) s)) * ((Set.image ((↑) : α → α ⧸ stabilizer α (↑(s * t) : Set α)) t)))) =
      ((s * t).mulStab ×
        ↥(((Set.image ((↑) : α → α ⧸ stabilizer α (↑(s * t) : Set α)) s)) * ((Set.image ((↑) : α → α ⧸ stabilizer α (↑(s * t) : Set α)) t)))) := by
    rw [← SetLike.coe_sort_coe, ← coe_mulStab (hs.mul ht), Finset.coe_sort_coe]
  let temp := this.trans (Equiv.cast that)
  replace temp := Fintype.card_congr temp
  simp only [Fintype.card_prod, Fintype.card_coe] at temp
  have h1 : Fintype.card ((s * t : Finset α) : Set α) = Fintype.card (s * t) := by congr
  have h2 : ((Set.image ((↑) : α → α ⧸ stabilizer α (↑(s * t) : Set α)) s)) * ((Set.image ((↑) : α → α ⧸ stabilizer α (↑(s * t) : Set α)) t)) =
    ↑(((Finset.image ((↑) : α → α ⧸ stabilizer α (↑(s * t) : Set α)) s)) * ((Finset.image ((↑) : α → α ⧸ stabilizer α (↑(s * t) : Set α)) t))) := by simp
  have h3 :
    Fintype.card (((Set.image ((↑) : α → α ⧸ stabilizer α (↑(s * t) : Set α)) s)) * ((Set.image ((↑) : α → α ⧸ stabilizer α (↑(s * t) : Set α)) t))) =
      Fintype.card (((Finset.image ((↑) : α → α ⧸ stabilizer α (↑(s * t) : Set α)) s)) *
        ((Finset.image ((↑) : α → α ⧸ stabilizer α (↑(s * t) : Set α)) t))) := by
    simp_rw [h2]
    congr
  simp only [h1, h3, Fintype.card_coe] at temp
  rw [temp]
lemma subgroup_mul_card_eq_mul_of_mul_stab_subset (s : Subgroup α) [DecidablePred (· ∈ s)]
    (t : Finset α) (hst : (s : Set α) ⊆ t.mulStab) : Nat.card s * #((Finset.image ((↑) : α → α ⧸ s) t)) = #t := by
  suffices h : (t : Set α) * s = t by
    simpa [h, eq_comm] using s.card_mul_eq_card_subgroup_mul_card_quotient  t
  apply Set.Subset.antisymm (Set.Subset.trans (Set.mul_subset_mul_left hst) _)
  · intro x
    rw [Set.mem_mul]
    aesop
  · rw [← coe_mul, mul_mulStab]
lemma mulStab_quotient_commute_subgroup (s : Subgroup α) [DecidablePred (· ∈ s)] (t : Finset α)
    (hst : (s : Set α) ⊆ t.mulStab) : ((Finset.image ((↑) : α → α ⧸ s) t.mulStab)) = ((Finset.image ((↑) : α → α ⧸ s) t)).mulStab := by
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
end
end

-- module MiscYD.AddCombi.Kneser.Kneser
section
section
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
  · contrapose! hab
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
  contrapose! has
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
      contrapose! hx'
      obtain ⟨y, hyst, d, hd, hxyd⟩ := mem_mul.mp hx'
      obtain ⟨c, hc, hcx⟩ := mem_smul_finset.mp (mem_sdiff.mp hx).1
      rw [← hcx, ← eq_mul_inv_iff_mul_eq] at hxyd
      have hyC : y ∈ a • C.mulStab := by
        rw [hxyd, smul_mul_assoc, smul_mem_smul_finset_iff, ← mulStab_mul_mulStab]
        apply mul_mem_mul hc ((mem_mulStab hC).mpr (inv_smul_eq_iff.mpr _))
        exact Eq.symm ((mem_mulStab hC).mp (hst hd))
      replace hyst : y ∈ s := by
        apply or_iff_not_imp_right.mp (mem_union.mp hyst)
        contrapose! hsC
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
      contrapose! hx'
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
  set n : ℕ := #(s * t) + #s with hn
  clear_value n
  induction n using Nat.strong_induction_on generalizing α with | h n ih =>
  subst hn
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  obtain rfl | ht := t.eq_empty_or_nonempty
  · simp
  classical
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
lemma mul_strict_kneser (h : #(s * (s * t).mulStab) + #(t * (s * t).mulStab) <
      #(s * t) + #(s * t).mulStab) :
    #(s * (s * t).mulStab) + #(t * (s * t).mulStab) ≤ #(s * t) :=
  Nat.le_of_lt_add_of_dvd h
      ((card_mulStab_dvd_card_mul_mulStab _ _).add <| card_mulStab_dvd_card_mul_mulStab _ _) <|
    card_mulStab_dvd_card _
end Finset
end
end


section
open Function MulAction AddAction
open scoped Pointwise
namespace Finset
variable {α : Type*}

def addStab [AddGroup α] [DecidableEq α] (s : Finset α) : Finset α := {a ∈ s - s | a +ᵥ s = s}

section AddGroupLayer
variable [AddGroup α] [DecidableEq α] {s t : Finset α} {a : α}

def toM (s : Finset α) : Finset (Multiplicative α) := s.map Multiplicative.ofAdd.toEmbedding

theorem mem_toM {x : Multiplicative α} : x ∈ toM s ↔ Multiplicative.toAdd x ∈ s := by
  simp [toM, Finset.mem_map_equiv]

theorem ofAdd_mem_toM {y : α} : Multiplicative.ofAdd y ∈ toM s ↔ y ∈ s := by
  rw [mem_toM]; rfl

theorem card_toM : #(toM s) = #s := Finset.card_map _

theorem toM_injective : Function.Injective (toM : Finset α → Finset (Multiplicative α)) :=
  Finset.map_injective _

theorem toM_subset_iff : toM s ⊆ toM t ↔ s ⊆ t := Finset.map_subset_map

theorem toM_add : toM (s + t) = toM s * toM t := by
  ext x
  rw [mem_toM, Finset.mem_add, Finset.mem_mul]
  constructor
  · rintro ⟨a, ha, b, hb, hab⟩
    refine ⟨Multiplicative.ofAdd a, ofAdd_mem_toM.2 ha, Multiplicative.ofAdd b, ofAdd_mem_toM.2 hb, ?_⟩
    rw [← ofAdd_add, hab]; rfl
  · rintro ⟨a, ha, b, hb, hab⟩
    refine ⟨Multiplicative.toAdd a, mem_toM.1 ha, Multiplicative.toAdd b, mem_toM.1 hb, ?_⟩
    rw [← toAdd_mul, hab]

theorem toM_sub : toM (s - t) = toM s / toM t := by
  ext x
  rw [mem_toM, Finset.mem_sub, Finset.mem_div]
  constructor
  · rintro ⟨a, ha, b, hb, hab⟩
    refine ⟨Multiplicative.ofAdd a, ofAdd_mem_toM.2 ha, Multiplicative.ofAdd b, ofAdd_mem_toM.2 hb, ?_⟩
    rw [← ofAdd_sub, hab]; rfl
  · rintro ⟨a, ha, b, hb, hab⟩
    refine ⟨Multiplicative.toAdd a, mem_toM.1 ha, Multiplicative.toAdd b, mem_toM.1 hb, ?_⟩
    rw [← toAdd_div, hab]

theorem toM_vadd : toM (a +ᵥ s) = Multiplicative.ofAdd a • toM s := by
  ext x
  rw [mem_toM, Finset.mem_vadd_finset, Finset.mem_smul_finset]
  constructor
  · rintro ⟨b, hb, hab⟩
    refine ⟨Multiplicative.ofAdd b, ofAdd_mem_toM.2 hb, ?_⟩
    rw [smul_eq_mul, ← ofAdd_add, ← vadd_eq_add, hab]; rfl
  · rintro ⟨b, hb, hab⟩
    refine ⟨Multiplicative.toAdd b, mem_toM.1 hb, ?_⟩
    rw [smul_eq_mul] at hab
    rw [vadd_eq_add, ← hab, toAdd_mul]; rfl

theorem toM_addStab : toM s.addStab = (toM s).mulStab := by
  ext x
  rw [mem_toM, addStab, mulStab, Finset.mem_filter, Finset.mem_filter, ← toM_sub, mem_toM]
  apply and_congr_right
  intro _
  rw [← toM_injective.eq_iff, toM_vadd]
  rfl

theorem toM_nonempty : (toM s).Nonempty ↔ s.Nonempty := Finset.map_nonempty

theorem mem_addStab (hs : s.Nonempty) : a ∈ s.addStab ↔ a +ᵥ s = s := by
  rw [← ofAdd_mem_toM, toM_addStab, Finset.mem_mulStab (toM_nonempty.2 hs), ← toM_vadd,
    toM_injective.eq_iff]

theorem zero_mem_addStab : (0 : α) ∈ s.addStab ↔ s.Nonempty := by
  rw [← ofAdd_mem_toM, toM_addStab, ofAdd_zero, Finset.one_mem_mulStab, toM_nonempty]

protected theorem Nonempty.zero_mem_addStab (h : s.Nonempty) : (0 : α) ∈ s.addStab :=
  zero_mem_addStab.2 h

protected theorem Nonempty.addStab (h : s.Nonempty) : s.addStab.Nonempty := ⟨_, h.zero_mem_addStab⟩

theorem coe_addStab (hs : s.Nonempty) : (s.addStab : Set α) = AddAction.stabilizer α (s : Set α) := by
  ext a
  rw [Finset.mem_coe, mem_addStab hs, SetLike.mem_coe, AddAction.mem_stabilizer_iff, ← Finset.coe_vadd_finset,
    Finset.coe_inj]


end AddGroupLayer

section AddCommGroupLayer
variable [AddCommGroup α] [DecidableEq α] {s t : Finset α}

theorem addStab_idem (s : Finset α) : s.addStab.addStab = s.addStab := by
  apply toM_injective
  simp only [toM_addStab, Finset.mulStab_idem]

@[simp] theorem add_addStab (s : Finset α) : s + s.addStab = s := by
  apply toM_injective
  rw [toM_add, toM_addStab, Finset.mul_mulStab]

@[simp] theorem addStab_add_addStab (s : Finset α) : s.addStab + s.addStab = s.addStab := by
  apply toM_injective
  rw [toM_add, toM_addStab, Finset.mulStab_mul_mulStab]

theorem subset_addStab_add_left (ht : t.Nonempty) : s.addStab ⊆ (s + t).addStab := by
  rw [← toM_subset_iff, toM_addStab, toM_addStab, toM_add]
  exact Finset.subset_mulStab_mul_left (toM_nonempty.2 ht)

theorem subset_addStab_add_right (hs : s.Nonempty) : t.addStab ⊆ (s + t).addStab := by
  rw [← toM_subset_iff, toM_addStab, toM_addStab, toM_add]
  exact Finset.subset_mulStab_mul_right (toM_nonempty.2 hs)

theorem card_addStab_dvd_card_add_addStab (s t : Finset α) : #t.addStab ∣ #(s + t.addStab) := by
  rw [← card_toM, ← card_toM (s := s + t.addStab), toM_addStab, toM_add, toM_addStab]
  exact Finset.card_mulStab_dvd_card_mul_mulStab _ _

theorem add_kneser (s t : Finset α) :
    #(s + (s + t).addStab) + #(t + (s + t).addStab) ≤ #(s + t) + #(s + t).addStab := by
  rw [← card_toM (s := s + (s + t).addStab), ← card_toM (s := t + (s + t).addStab),
    ← card_toM (s := s + t), ← card_toM (s := (s + t).addStab), toM_add, toM_add, toM_addStab,
    toM_add]
  exact Finset.mul_kneser (toM s) (toM t)

end AddCommGroupLayer
end Finset
end

-- module SingleSetCovering
section
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
    have hk := add_kneser (n • s) s
    rw [← succ_nsmul] at hk
    rw [← hHdef] at hk
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
lemma cnt_le_of_subset {S : Set ℕ} {b c : ℕ} (h : ∀ x ∈ S, x < b → x < c) : cnt S b ≤ c := by
  classical
  unfold cnt
  calc #((range b).filter (· ∈ S)) ≤ #(range c) := by
        apply card_le_card
        intro x hx
        simp only [mem_filter, mem_range] at hx
        exact mem_range.2 (h x hx.2 hx.1)
    _ = c := card_range c
lemma dense_step_window {γ : ℝ} (hγ : 0 < γ) {h : ℕ} (hh : (4 / γ : ℝ) < h) {E : Set ℕ}
    {F : Finset ℕ} (hFE : (F : Set ℕ) ⊆ E)
    (h1 : (1 : ℤ) ∈ Submodule.span ℤ ((Nat.cast : ℕ → ℤ) '' F)) (hE0 : 0 ∈ E) {ℓ : ℕ} (hℓE : ℓ ∈ E) (hN : γ * ℓ ≤ cnt E ℓ) (hℓF : F.sup id ≤ ℓ) (hℓγ : (2 / γ : ℝ) ≤ ℓ) {m x : ℕ}
    (hx1 : h * ℓ ≤ x) (hx2 : x + h * ℓ ≤ m * ℓ) :
    ∃ M : Multiset ℕ, M.card = m ∧ (∀ a ∈ M, a ∈ E) ∧ M.sum = x := by
  classical
  have hℓpos : 0 < ℓ := by
    have : (0 : ℝ) < 2 / γ := by positivity
    exact_mod_cast this.trans_le hℓγ
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
  have hAcnt : γ * ℓ ≤ #A := by
    have h1 := hN
    have h2 : cnt E ℓ ≤ #A := by
      unfold cnt
      apply card_le_card
      intro a ha
      simp only [mem_filter, mem_range] at ha
      rw [hA]
      exact mem_filter.2 ⟨mem_range.2 (by omega), ha.2⟩
    exact h1.trans (by exact_mod_cast h2)
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
    have hS' : (γ * ℓ - 1 : ℝ) ≤ #S := by
      have : (#A : ℝ) ≤ #S + 1 := by exact_mod_cast hScard
      linarith
    have hpos : (0 : ℝ) ≤ γ * ℓ - 1 := by
      have : γ * (2 / γ) ≤ γ * ℓ := mul_le_mul_of_nonneg_left hℓγ hγ.le
      rw [mul_div_cancel₀ _ hγ.ne'] at this
      linarith
    have key : (4 / γ) * (γ * ℓ - 1) ≤ (h : ℝ) * #S :=
      mul_le_mul hh.le hS' hpos (by positivity)
    have e : (4 / γ) * (γ * ℓ - 1) = 4 * ℓ - 4 / γ := by field_simp
    have h4 : (4 / γ : ℝ) ≤ 2 * ℓ := by
      have : (4 / γ : ℝ) = 2 * (2 / γ) := by ring
      linarith
    have : (2 * ℓ : ℝ) ≤ h * #S := by linarith
    exact_mod_cast this
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
  have hh1 : 1 ≤ h := by
    have : (0 : ℝ) < h := lt_of_le_of_lt (by positivity) hh
    exact_mod_cast this
  have huniv := nsmul_eq_univ h0S hgen hh1 hcard
  obtain ⟨M, hMc, hMA, hMs⟩ := exists_multiset_of_nsmul_eq_univ hA0 hAℓ hle huniv hx1 hx2
  refine ⟨M, hMc, fun a ha ↦ ?_, hMs⟩
  have := hMA a ha
  simp only [hA, mem_filter] at this
  exact this.2
lemma exists_mem_Ioc {γ : ℝ} (hγ : 0 < γ) {C : ℕ} (hC : (2 / γ : ℝ) ≤ C) {E : Set ℕ} {N : ℕ}
    (hN : ∀ b ≥ N, γ * b ≤ cnt E b) {y : ℕ} (hyN : N ≤ y) (hy2 : 2 ≤ y) :
    ∃ ℓ ∈ E, y < ℓ ∧ ℓ ≤ C * y := by
  by_contra hcon
  push Not at hcon
  have hC1 : 1 ≤ C := by
    have : (0 : ℝ) < C := lt_of_lt_of_le (by positivity) hC
    exact_mod_cast this
  have hle : cnt E (C * y + 1) ≤ y + 1 := by
    apply cnt_le_of_subset
    intro x hx hxb
    by_contra hxy
    exact absurd (hcon x hx (by omega)) (by omega)
  have hb : N ≤ C * y + 1 := by nlinarith
  have h1 := hN _ hb
  have h2 : (cnt E (C * y + 1) : ℝ) ≤ y + 1 := by exact_mod_cast hle
  have h3 : (2 : ℝ) ≤ γ * C := by
    have := mul_le_mul_of_nonneg_left hC hγ.le
    rwa [mul_div_cancel₀ _ hγ.ne'] at this
  have hy : (2 : ℝ) ≤ y := by exact_mod_cast hy2
  push_cast at h1
  nlinarith
theorem cover {γ : ℝ} (hγ : 0 < γ) : ∃ K : ℕ, (2 / γ : ℝ) < K ∧ ∀ E : Set ℕ, 0 ∈ E →
    (∃ F : Finset ℕ, (F : Set ℕ) ⊆ E ∧ (1 : ℤ) ∈ Submodule.span ℤ ((Nat.cast : ℕ → ℤ) '' F)) →
    (∃ N, ∀ b ≥ N, γ * b ≤ cnt E b) →
    ∃ N', ∀ x ≥ N', ∃ M : Multiset ℕ, M.card = K ∧ (∀ a ∈ M, a ∈ E) ∧ M.sum = x := by
  set h : ℕ := ⌈4 / γ⌉₊ + 1 with hhdef
  set C : ℕ := ⌈2 / γ⌉₊ + 1 with hCdef
  have hh : (4 / γ : ℝ) < h := by
    rw [hhdef]; push_cast; linarith [Nat.le_ceil (4 / γ)]
  have hC : (2 / γ : ℝ) ≤ C := by
    rw [hCdef]; push_cast; linarith [Nat.le_ceil (2 / γ)]
  have hh1 : 1 ≤ h := by omega
  have hC1 : 1 ≤ C := by omega
  refine ⟨h * (C + 1), ?_, ?_⟩
  · have : (h : ℝ) ≤ h * (C + 1) := by
      have : (1 : ℝ) ≤ C + 1 := by linarith [(Nat.cast_nonneg C : (0 : ℝ) ≤ C)]
      nlinarith [(Nat.cast_nonneg h : (0 : ℝ) ≤ h)]
    have h42 : (2 / γ : ℝ) < 4 / γ := by
      apply div_lt_div_of_pos_right (by norm_num) hγ
    push_cast
    linarith
  rintro E hE0 ⟨F, hFE, h1⟩ ⟨N, hN⟩
  set L : ℕ := N + F.sup id + ⌈2 / γ⌉₊ + 2 with hL
  refine ⟨h * C * (L + 1), fun x hx ↦ ?_⟩
  have hhC : 0 < h * C := Nat.mul_pos (by omega) (by omega)
  set y := x / (h * C) with hy
  have hyL : L + 1 ≤ y := by
    rw [hy]
    exact (Nat.le_div_iff_mul_le hhC).2 (by rw [mul_comm]; exact hx)
  obtain ⟨ℓ, hℓE, hyℓ, hℓy⟩ := exists_mem_Ioc hγ hC hN (y := y) (by omega) (by omega)
  have hℓγ : (2 / γ : ℝ) ≤ ℓ := by
    have : ⌈2 / γ⌉₊ ≤ ℓ := by omega
    exact (Nat.le_ceil _).trans (by exact_mod_cast this)
  apply dense_step_window hγ hh hFE h1 hE0 hℓE (hN ℓ (by omega)) (by omega) hℓγ
  ·
    calc h * ℓ ≤ h * (C * y) := Nat.mul_le_mul_left h hℓy
      _ = y * (h * C) := by ring
      _ ≤ x := Nat.div_mul_le_self x (h * C)
  ·
    have hx' : x < (y + 1) * (h * C) := by rw [hy, mul_comm]; exact Nat.lt_mul_div_succ x hhC
    have : (y + 1) * (h * C) ≤ ℓ * (h * C) := Nat.mul_le_mul_right _ hyℓ
    nlinarith
end Erdos338Proof
open Finset
namespace Erdos338Proof
theorem usl {γ : ℝ} (hγ : 0 < γ) : ∃ K : ℕ, ∀ M : Set ℕ, (∃ N, ∀ b ≥ N, γ * b ≤ cnt M b) →
    ∃ d b₀ N', 1 ≤ d ∧ d ≤ K ∧ ∀ x ≥ N', ∃ Ms : Multiset ℕ, Multiset.card Ms = K ∧
      (∀ a ∈ Ms, a ∈ M) ∧ Ms.sum = K * b₀ + d * x := by
  classical
  obtain ⟨K, hK, hcov⟩ := cover (half_pos hγ)
  have hγK : 4 < K * γ := by
    have e : (2 / (γ / 2) : ℝ) = 4 / γ := by field_simp; norm_num
    rw [e, div_lt_iff₀ hγ] at hK
    exact hK
  refine ⟨K, fun M ⟨N, hN⟩ ↦ ?_⟩
  have hlarge : ∀ y, ∃ x ∈ M, y ≤ x := by
    intro y
    by_contra hcon
    push Not at hcon
    set b := N + ⌈((y : ℝ) + 1) / γ⌉₊ with hb
    have h1 := hN b (by omega)
    have h2 : cnt M b ≤ y := cnt_le_of_subset fun x hx _ ↦ hcon x hx
    have h3 : ((y : ℝ) + 1) / γ ≤ b :=
      (Nat.le_ceil _).trans (by exact_mod_cast (by omega : ⌈((y : ℝ) + 1) / γ⌉₊ ≤ b))
    have h4 : (y : ℝ) + 1 ≤ γ * b := by rwa [div_le_iff₀ hγ, mul_comm] at h3
    have h5 : (cnt M b : ℝ) ≤ y := by exact_mod_cast h2
    linarith
  obtain ⟨b₀, hb₀, -⟩ := hlarge 0
  set D : Set ℕ := {u | b₀ + u ∈ M} with hD
  set I := Submodule.span ℤ ((Nat.cast : ℕ → ℤ) '' D) with hI
  have hex : ∃ n : ℕ, 0 < n ∧ (n : ℤ) ∈ I := by
    obtain ⟨x, hx, hxb⟩ := hlarge (b₀ + 1)
    refine ⟨x - b₀, by omega, Submodule.subset_span ⟨x - b₀, ?_, rfl⟩⟩
    show b₀ + (x - b₀) ∈ M
    rwa [show b₀ + (x - b₀) = x by omega]
  set d := Nat.find hex with hddef
  have hd : 0 < d ∧ (d : ℤ) ∈ I := Nat.find_spec hex
  have hdvd : ∀ u ∈ D, d ∣ u := by
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
  have hdecomp : ∀ x ∈ M, b₀ ≤ x → ∃ q, x = b₀ + d * q ∧ q ∈ {y | b₀ + d * y ∈ M} := by
    intro x hx hxb
    have hu : x - b₀ ∈ D := by
      show b₀ + (x - b₀) ∈ M
      rwa [show b₀ + (x - b₀) = x by omega]
    obtain ⟨q, hq⟩ := hdvd _ hu
    refine ⟨q, by omega, ?_⟩
    show b₀ + d * q ∈ M
    rwa [← hq, show b₀ + (x - b₀) = x by omega]
  set E : Set ℕ := {y | b₀ + d * y ∈ M} with hE
  have hE0 : 0 ∈ E := by simpa [hE] using hb₀
  obtain ⟨T, hTD, hdT⟩ := Submodule.mem_span_finite_of_mem_span hd.2
  set F : Finset ℕ := T.image fun z ↦ z.toNat / d with hF
  have hFE : (F : Set ℕ) ⊆ E := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := mem_image.1 hy
    obtain ⟨u, hu, rfl⟩ := hTD hz
    show b₀ + d * ((u : ℤ).toNat / d) ∈ M
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
  have hcntM : ∀ b, cnt M b ≤ b₀ + cnt E b := by
    intro b
    unfold cnt
    have hsub : (range b).filter (· ∈ M) ⊆
        range b₀ ∪ ((range b).filter (· ∈ E)).image fun y ↦ b₀ + d * y := by
      intro x hx
      rw [mem_filter, mem_range] at hx
      rw [mem_union, mem_range, mem_image]
      by_cases hxb : x < b₀
      · exact Or.inl hxb
      · obtain ⟨q, rfl, hq⟩ := hdecomp x hx.2 (by omega)
        have : q ≤ d * q := Nat.le_mul_of_pos_left q hd.1
        exact Or.inr ⟨q, mem_filter.2 ⟨mem_range.2 (by omega), hq⟩, rfl⟩
    calc _ ≤ _ := card_le_card hsub
      _ ≤ _ := card_union_le _ _
      _ ≤ _ := by rw [card_range]; exact Nat.add_le_add_left card_image_le _
  have hcntM2 : ∀ b, cnt M b ≤ b₀ + (b / d + 1) := by
    intro b
    unfold cnt
    have hsub : (range b).filter (· ∈ M) ⊆
        range b₀ ∪ (range (b / d + 1)).image fun y ↦ b₀ + d * y := by
      intro x hx
      rw [mem_filter, mem_range] at hx
      rw [mem_union, mem_range, mem_image]
      by_cases hxb : x < b₀
      · exact Or.inl hxb
      · obtain ⟨q, rfl, -⟩ := hdecomp x hx.2 (by omega)
        refine Or.inr ⟨q, mem_range.2 (Nat.lt_succ_of_le ?_), rfl⟩
        rw [Nat.le_div_iff_mul_le hd.1, mul_comm]
        omega
    calc _ ≤ _ := card_le_card hsub
      _ ≤ _ := card_union_le _ _
      _ ≤ _ := Nat.add_le_add (card_range _).le (card_image_le.trans (card_range _).le)
  have hdK : d ≤ K := by
    by_contra hdK
    push Not at hdK
    set b := N + ⌈(2 * (b₀ : ℝ) + 2) / γ⌉₊ with hb
    have h1 := hN b (by omega)
    have h2 := hcntM2 b
    set q := b / d with hq
    have h3 : q * d ≤ b := Nat.div_mul_le_self b d
    have h4 : q * K ≤ b := (Nat.mul_le_mul_left q hdK.le).trans h3
    have h5 : ((2 * (b₀ : ℝ) + 2) / γ) ≤ b :=
      (Nat.le_ceil _).trans (by exact_mod_cast (by omega : ⌈(2 * (b₀ : ℝ) + 2) / γ⌉₊ ≤ b))
    have h6 : 2 * (b₀ : ℝ) + 2 ≤ γ * b := by rw [div_le_iff₀ hγ] at h5; linarith
    have h2' : (cnt M b : ℝ) ≤ b₀ + (q + 1) := by exact_mod_cast h2
    have h4' : (q : ℝ) * K ≤ b := by exact_mod_cast h4
    have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    have h7 : 4 * (q : ℝ) ≤ γ * b := by
      have := mul_le_mul_of_nonneg_left h4' hγ.le
      nlinarith
    linarith
  have hdens : ∃ N₁, ∀ b ≥ N₁, γ / 2 * b ≤ cnt E b := by
    refine ⟨N + ⌈2 * (b₀ : ℝ) / γ⌉₊, fun b hb ↦ ?_⟩
    have h1 := hN b (by omega)
    have h2 : (cnt M b : ℝ) ≤ b₀ + cnt E b := by exact_mod_cast hcntM b
    have h3 : 2 * (b₀ : ℝ) / γ ≤ b :=
      (Nat.le_ceil _).trans (by exact_mod_cast (by omega : ⌈2 * (b₀ : ℝ) / γ⌉₊ ≤ b))
    have h4 : 2 * (b₀ : ℝ) ≤ γ * b := by rw [div_le_iff₀ hγ] at h3; linarith
    linarith
  obtain ⟨N', hN'⟩ := hcov E hE0 ⟨F, hFE, h1⟩ hdens
  refine ⟨d, b₀, N', hd.1, hdK, fun x hx ↦ ?_⟩
  obtain ⟨Me, hMe1, hMe2, hMe3⟩ := hN' x hx
  refine ⟨Me.map fun y ↦ b₀ + d * y, by simp [hMe1], ?_, ?_⟩
  · intro a ha
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 ha
    exact hMe2 y hy
  · rw [Multiset.sum_map_add, Multiset.map_const', Multiset.sum_replicate, Multiset.sum_map_mul_left,
      Multiset.map_id', hMe3, hMe1, smul_eq_mul]
end Erdos338Proof
end

-- module InfiniteLevels
section
namespace OMA.E338.Bridge
open Filter
open scoped BigOperators Classical
noncomputable def windowCount (B : Set ℕ) (N : ℕ) : ℕ :=
  ((Finset.Icc 0 N).filter (· ∈ B)).card
noncomputable def infiniteRanks (C : ℕ → Set ℕ) (h : ℕ) : Finset ℕ :=
  (Finset.range h).filter (fun t => (C t).Infinite)
noncomputable def weightedCount (C : ℕ → Set ℕ) (L : ℕ → ℕ) (I : Finset ℕ) (N : ℕ) : ℕ :=
  ∑ t ∈ I, L t * windowCount (C t) N
theorem windowCount_mono (B : Set ℕ) : Monotone (windowCount B) := by
  intro i j hij
  apply Finset.card_le_card
  intro x hx
  obtain ⟨hxI, hB⟩ := Finset.mem_filter.mp hx
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le _, (Finset.mem_Icc.mp hxI).2.trans hij⟩, hB⟩
theorem weightedCount_mono (C : ℕ → Set ℕ) (L : ℕ → ℕ) (I : Finset ℕ) :
    Monotone (weightedCount C L I) := by
  intro i j hij
  exact Finset.sum_le_sum (fun t _ => Nat.mul_le_mul_left _ (windowCount_mono (C t) hij))
private theorem windowCount_le_ncard {B : Set ℕ} (hf : B.Finite) (N : ℕ) :
    windowCount B N ≤ B.ncard := by
  unfold windowCount
  rw [← Set.ncard_coe_finset]
  exact Set.ncard_le_ncard (fun x hx => (Finset.mem_filter.mp hx).2) hf
theorem eventually_infinite_rank_of_mass (C : ℕ → Set ℕ) (L : ℕ → ℕ) (h : ℕ)
    (mass : ∀ᶠ N : ℕ in atTop, ∃ t < h, 6 * N ≤ L t * windowCount (C t) (2 * N)) :
    ∀ᶠ N : ℕ in atTop, ∃ t ∈ infiniteRanks C h, 6 * N ≤ L t * windowCount (C t) (2 * N) := by
  let B := ∑ t ∈ Finset.range h, L t * (C t).ncard
  filter_upwards [mass, eventually_ge_atTop (B + 1)] with N hm hN
  obtain ⟨t, ht, hmass⟩ := hm
  refine ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ht, ?_⟩, hmass⟩
  intro hfinite
  have hcard := Nat.mul_le_mul_left (L t) (windowCount_le_ncard hfinite (2 * N))
  have hbound : L t * (C t).ncard ≤ B :=
    Finset.single_le_sum (f := fun j => L j * (C j).ncard)
      (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr ht)
  omega
theorem eventually_even_weightedCount (C : ℕ → Set ℕ) (L : ℕ → ℕ) (h : ℕ)
    (mass : ∀ᶠ N : ℕ in atTop, ∃ t < h, 6 * N ≤ L t * windowCount (C t) (2 * N)) :
    ∀ᶠ N : ℕ in atTop, 6 * N ≤ weightedCount C L (infiniteRanks C h) (2 * N) := by
  filter_upwards [eventually_infinite_rank_of_mass C L h mass] with N hn
  obtain ⟨t, ht, hm⟩ := hn
  exact hm.trans (Finset.single_le_sum (f := fun j => L j * windowCount (C j) (2 * N))
    (fun _ _ => Nat.zero_le _) ht)
theorem eventually_weightedCount_add_three (C : ℕ → Set ℕ) (L : ℕ → ℕ) (h : ℕ)
    (mass : ∀ᶠ N : ℕ in atTop, ∃ t < h, 6 * N ≤ L t * windowCount (C t) (2 * N)) :
    ∀ᶠ N : ℕ in atTop, 3 * N ≤ weightedCount C L (infiniteRanks C h) N + 3 := by
  obtain ⟨K, hK⟩ := eventually_atTop.mp (eventually_even_weightedCount C L h mass)
  filter_upwards [eventually_ge_atTop (2 * K)] with N hN
  have heven := hK (N / 2) (by omega)
  have hm := weightedCount_mono C L (infiniteRanks C h)
    (show 2 * (N / 2) ≤ N by omega)
  omega
private theorem weightedCount_le (C : ℕ → Set ℕ) (L : ℕ → ℕ) (I : Finset ℕ) (N : ℕ) :
    weightedCount C L I N ≤ (∑ t ∈ I, L t) * (N + 1) := by
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro t _
  apply Nat.mul_le_mul_left
  simpa [windowCount] using Finset.card_filter_le (Finset.Icc 0 N) (fun x => x ∈ C t)
theorem three_le_infinite_liminf (C : ℕ → Set ℕ) (L : ℕ → ℕ) (h : ℕ)
    (mass : ∀ᶠ N : ℕ in atTop, ∃ t < h, 6 * N ≤ L t * windowCount (C t) (2 * N)) :
    (3 : ℝ) ≤ liminf (fun N : ℕ => (weightedCount C L (infiniteRanks C h) N : ℝ) / N) atTop := by
  let I := infiniteRanks C h
  let W := ∑ t ∈ I, L t
  have hupper : ∀ N : ℕ, (weightedCount C L I N : ℝ) / N ≤ 2 * (W : ℝ) := by
    intro N
    by_cases hz : N = 0
    · simp [hz]
    · have hp : 0 < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hz
      apply (div_le_iff₀ hp).2
      have hcard := weightedCount_le C L I N
      have hu : W * (N + 1) ≤ (2 * W) * N := by
        calc
          _ ≤ W * (2 * N) := Nat.mul_le_mul_left _ (by omega)
          _ = _ := by ac_rfl
      exact_mod_cast hcard.trans hu
  have hlower : IsBoundedUnder (· ≥ ·) atTop (fun N : ℕ => (weightedCount C L I N : ℝ) / N) := by
    refine ⟨0, ?_⟩
    change ∀ᶠ N : ℕ in atTop, 0 ≤ (weightedCount C L I N : ℝ) / N
    exact Eventually.of_forall fun _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  apply (le_liminf_iff (isCoboundedUnder_ge_of_le (x := 2 * (W : ℝ)) _ hupper) hlower).mpr
  intro y hy
  obtain ⟨K, hK⟩ := exists_nat_gt (3 / (3 - y))
  filter_upwards [eventually_weightedCount_add_three C L h mass, eventually_ge_atTop K,
    eventually_ge_atTop 1] with N hm hN hpos
  have hp : 0 < (N : ℝ) := by exact_mod_cast hpos
  apply (lt_div_iff₀ hp).2
  have hK' := hK.trans_le (show (K : ℝ) ≤ N by exact_mod_cast hN)
  have hg := (div_lt_iff₀ (sub_pos.mpr hy)).mp hK'
  have hc : 3 * (N : ℝ) ≤ (weightedCount C L I N : ℝ) + 3 := by exact_mod_cast hm
  nlinarith
theorem infiniteRanks_nonempty (C : ℕ → Set ℕ) (L : ℕ → ℕ) (h : ℕ)
    (mass : ∀ᶠ N : ℕ in atTop, ∃ t < h, 6 * N ≤ L t * windowCount (C t) (2 * N)) :
    (infiniteRanks C h).Nonempty := by
  obtain ⟨_, t, ht, _⟩ := (eventually_infinite_rank_of_mass C L h mass).exists
  exact ⟨t, ht⟩
theorem two_le_infinite_multiplicity (C : ℕ → Set ℕ) (L : ℕ → ℕ) (h : ℕ)
    (mass : ∀ᶠ N : ℕ in atTop, ∃ t < h, 6 * N ≤ L t * windowCount (C t) (2 * N))
    (hL : ∀ t < h, 2 ≤ L t) : 2 ≤ ∑ t ∈ infiniteRanks C h, L t := by
  obtain ⟨t, ht⟩ := infiniteRanks_nonempty C L h mass
  exact (hL t (Finset.mem_range.mp (Finset.mem_filter.mp ht).1)).trans
    (Finset.single_le_sum (f := L) (fun _ _ => Nat.zero_le _) ht)
end OMA.E338.Bridge
end

-- module ProductiveWindow
section
namespace OMA.E338.Bridge
open Filter Finset
open scoped BigOperators Pointwise Classical
private theorem normalize_set {C : Set ℕ} (hp : ∃ n ∈ C, 0 < n) :
    ∃ d : ℕ, 0 < d ∧ (∀ x ∈ C, d ∣ x) ∧ ∃ F : Finset ℕ,
      ((F : Set ℕ) ⊆ {y | d*y ∈ C}) ∧ (1 : ℤ) ∈ Submodule.span ℤ ((Nat.cast : ℕ → ℤ) '' F) := by
  classical
  let I := Submodule.span ℤ ((Nat.cast : ℕ → ℤ) '' C)
  have hex : ∃ n : ℕ, 0 < n ∧ (n : ℤ) ∈ I := by
    obtain ⟨n, hn, hpos⟩ := hp
    exact ⟨n, hpos, Submodule.subset_span ⟨n, hn, rfl⟩⟩
  let d := Nat.find hex
  have hd : 0 < d ∧ (d : ℤ) ∈ I := Nat.find_spec hex
  have hdvd : ∀ x ∈ C, d ∣ x := by
    intro x hx
    have hx' : (x : ℤ) ∈ I := Submodule.subset_span ⟨x, hx, rfl⟩
    have hmod : ((x % d : ℕ) : ℤ) ∈ I := by
      have e : ((x % d : ℕ) : ℤ) = (x : ℤ) - ((x / d : ℕ) : ℤ) * (d : ℤ) := by
        have := Nat.mod_add_div x d
        push_cast
        linarith [this]
      rw [e]
      exact I.sub_mem hx' (I.smul_mem _ hd.2)
    by_contra hnd
    have hpos : 0 < x % d := Nat.pos_of_ne_zero fun h => hnd (Nat.dvd_of_mod_eq_zero h)
    exact Nat.find_min hex (Nat.mod_lt x hd.1) ⟨hpos, hmod⟩
  obtain ⟨T, hTC, hdT⟩ := Submodule.mem_span_finite_of_mem_span hd.2
  let F := T.image fun z => z.toNat / d
  refine ⟨d, hd.1, hdvd, F, ?_, ?_⟩
  · intro y hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨u, hu, rfl⟩ := hTC hz
    change d * ((u : ℤ).toNat / d) ∈ C
    rwa [Int.toNat_natCast, Nat.mul_div_cancel' (hdvd u hu)]
  · let f : ℤ →ₗ[ℤ] ℤ := LinearMap.mulLeft ℤ (d : ℤ)
    have hT : (T : Set ℤ) ⊆ f '' ((Nat.cast : ℕ → ℤ) '' F) := by
      intro z hz
      obtain ⟨u, hu, rfl⟩ := hTC hz
      refine ⟨((u / d : ℕ) : ℤ), ⟨u / d, Finset.mem_image.mpr ⟨u, hz, by simp⟩, rfl⟩, ?_⟩
      simp only [f, LinearMap.mulLeft_apply]
      exact_mod_cast Nat.mul_div_cancel' (hdvd u hu)
    have hmem : (d : ℤ) ∈ Submodule.map f (Submodule.span ℤ ((Nat.cast : ℕ → ℤ) '' F)) := by
      rw [Submodule.map_span]
      exact Submodule.span_mono hT hdT
    obtain ⟨y, hy, hfy⟩ := Submodule.mem_map.mp hmem
    have hy1 : y = 1 := by
      simp only [f, LinearMap.mulLeft_apply] at hfy
      have hd0 : (d : ℤ) ≠ 0 := (by exact_mod_cast hd.1.ne')
      exact mul_left_cancel₀ hd0 (hfy.trans (mul_one _).symm)
    rwa [hy1] at hy
private theorem scaled_multiset_mem {d : ℕ} {C : Set ℕ} (M : Multiset ℕ)
    (hM : ∀ x ∈ M, d*x ∈ C) : d*M.sum ∈ M.card • C := by
  induction M using Multiset.induction_on with
  | empty => simp
  | cons a M ih =>
    rw [Multiset.sum_cons, Nat.mul_add, Multiset.card_cons, succ_nsmul]
    rw [Nat.add_comm]
    exact Set.add_mem_add (ih (fun x hx => hM x (Multiset.mem_cons_of_mem hx)))
      (hM a (Multiset.mem_cons_self a M))
theorem localCoverAtProductiveWindows (C : Set ℕ) (h0 : 0 ∈ C) (L : ℕ) (hL : 0 < L) :
    ∃ d : ℕ, 0 < d ∧ ∀ᶠ X : ℕ in atTop, 6*X ≤ L*windowCount C (2*X) →
      ∃ ℓ ∈ C, 0 < ℓ ∧ ℓ ≤ 2*X ∧ X ≤ L*ℓ ∧ d ≤ L ∧
        ∀ u k : ℕ, d ∣ u → (4*(L+1))*ℓ ≤ u → u + (4*(L+1))*ℓ ≤ k*ℓ → u ∈ k • C := by
  classical
  by_cases hp : ∃ x ∈ C, 0 < x
  case neg =>
    refine ⟨1, Nat.one_pos, ?_⟩
    filter_upwards [eventually_gt_atTop L] with X hX
    intro hm
    have hsub : (Finset.Icc 0 (2*X)).filter (· ∈ C) ⊆ {0} := by
      intro x hx
      have h := (Finset.mem_filter.mp hx).2
      exact Finset.mem_singleton.mpr (by by_contra hn; exact hp ⟨x, h, Nat.pos_of_ne_zero hn⟩)
    have hw : windowCount C (2*X) ≤ 1 := (Finset.card_le_card hsub).trans (by simp)
    have := Nat.mul_le_mul_left L hw
    omega
  obtain ⟨d, hd, hdvd, F, hFE, hF⟩ := normalize_set hp
  let E : Set ℕ := {y | d*y ∈ C}
  have he0 : 0 ∈ E := by simpa [E] using h0
  let c := 4*(L+1)
  let T := F.sup id + 2*L + 1
  refine ⟨d, hd, ?_⟩
  filter_upwards [eventually_gt_atTop (L*(d*T) + L)] with X hX
  intro hm
  let V := (Finset.Icc 0 (2*X)).filter (· ∈ C)
  have hV : 6*X ≤ L*V.card := hm
  have hne : V.Nonempty := ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_rfl, Nat.zero_le _⟩, h0⟩⟩
  let ℓ := V.max' hne
  have hℓV : ℓ ∈ V := Finset.max'_mem _ _
  have hℓC : ℓ ∈ C := (Finset.mem_filter.mp hℓV).2
  have hℓX := (Finset.mem_Icc.mp (Finset.mem_filter.mp hℓV).1).2
  have hlarg : X ≤ L*ℓ := by
    have hsub : V ⊆ Finset.range (ℓ+1) := fun x hx => Finset.mem_range.mpr (by
      exact Nat.lt_succ_of_le (Finset.le_max' V x hx))
    have hvle : V.card ≤ ℓ+1 := (Finset.card_le_card hsub).trans (by simp)
    have hh := Nat.mul_le_mul_left L hvle
    rw [Nat.mul_add, Nat.mul_one] at hh
    omega
  have hℓpos : 0 < ℓ := by by_contra! hn; simp [Nat.eq_zero_of_le_zero hn] at hlarg; omega
  let z := ℓ/d
  have hdz : d*z = ℓ := Nat.mul_div_cancel' (hdvd ℓ hℓC)
  have hzT : T ≤ z := by
    by_contra! hz
    have hlt := Nat.mul_lt_mul_of_pos_left hz hd
    have hb := Nat.mul_le_mul_left L hlt.le
    rw [hdz] at hb
    omega
  have hzE : z ∈ E := by simpa [E, hdz] using hℓC
  have hdivinj : Set.InjOn (fun x : ℕ => x/d) (V : Set ℕ) := by
    intro x hx y hy he
    have h1 := Nat.mul_div_cancel' (hdvd x (Finset.mem_filter.mp hx).2)
    have h2 := Nat.mul_div_cancel' (hdvd y (Finset.mem_filter.mp hy).2)
    change x/d = y/d at he
    rw [he] at h1
    exact h1.symm.trans h2
  have hncard : V.card ≤ Erdos338Proof.cnt E z + 1 := by
    let P := (Finset.range z).filter (· ∈ E)
    have hsub : V.image (fun x => x/d) ⊆ insert z P := by
      intro t ht
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ht
      have xle : x/d ≤ z := Nat.div_le_div_right (Finset.le_max' V x hx)
      rcases Nat.eq_or_lt_of_le xle with heq | hlt
      · rw [heq]; exact Finset.mem_insert_self _ _
      · apply Finset.mem_insert_of_mem
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_range.mpr hlt, ?_⟩
        change d*(x/d) ∈ C
        rw [Nat.mul_div_cancel' (hdvd x (Finset.mem_filter.mp hx).2)]
        exact (Finset.mem_filter.mp hx).2
    rw [← Finset.card_image_of_injOn hdivinj]
    exact (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
  have hVsmall : V.card ≤ z+1 := by
    apply hncard.trans
    have hc : Erdos338Proof.cnt E z ≤ z := by
      simpa [Erdos338Proof.cnt] using Finset.card_filter_le (Finset.range z) (· ∈ E)
    omega
  have hdL : d ≤ L := by
    by_contra! hgt
    have hzL := Nat.mul_le_mul_right z hgt.le
    have hvc := Nat.mul_le_mul_left L hVsmall
    rw [Nat.mul_add, Nat.mul_one] at hvc
    omega
  have hzle : z ≤ 2*X := (Nat.div_le_self _ _).trans hℓX
  have hcnt : z ≤ L * Erdos338Proof.cnt E z := by
    have hu := Nat.mul_le_mul_left L hncard
    rw [Nat.mul_add, Nat.mul_one] at hu
    omega
  have hg : 0 < 1/(L : ℝ) := by positivity
  have hcg : 4/(1/(L : ℝ)) < (c : ℝ) := by simp [c, Nat.cast_add, Nat.cast_mul]
  have hzBig : 2/(1/(L : ℝ)) ≤ (z : ℝ) := by
    suffices 2 * L ≤ z by simpa using (show (2 : ℝ)*L ≤ z by exact_mod_cast this)
    dsimp [T] at hzT
    omega
  have hratio : (1/(L : ℝ))*z ≤ (Erdos338Proof.cnt E z : ℝ) := by
    rw [one_div, inv_mul_eq_div, div_le_iff₀ (by exact_mod_cast hL), mul_comm]
    exact_mod_cast hcnt
  refine ⟨ℓ, hℓC, hℓpos, hℓX, hlarg, hdL, ?_⟩
  intro u k hdu hl hu
  obtain ⟨v, rfl⟩ := hdu
  change c*ℓ ≤ d*v at hl
  change d*v+c*ℓ ≤ k*ℓ at hu
  have hdc : d*(c*z) = c*ℓ := (Nat.mul_left_comm d c z).trans (congrArg (c*·) hdz)
  have hdk : d*(k*z) = k*ℓ := (Nat.mul_left_comm d k z).trans (congrArg (k*·) hdz)
  have hl' : c*z ≤ v := Nat.le_of_mul_le_mul_left (by rwa [hdc]) hd
  have hu' : v+c*z ≤ k*z := Nat.le_of_mul_le_mul_left (by rwa [Nat.mul_add, hdc, hdk]) hd
  obtain ⟨M, hcard, hM, hsum⟩ := Erdos338Proof.dense_step_window hg hcg hFE hF he0 hzE
    hratio (by dsimp [T] at hzT; omega) hzBig hl' hu'
  have hres := scaled_multiset_mem (d := d) (C := C) M hM
  rwa [hsum, hcard] at hres
end OMA.E338.Bridge
end

-- module TwoScale
section
open Filter
open scoped Pointwise BigOperators
namespace OMA.E338.Bridge
def twoScaleCap (L : ℕ) : ℕ := 2*(4*(L+1)) + 4*L^2 + 2*(4*(L+1))*L
private theorem mul_mem_copies {C : Set ℕ} {q : ℕ} (hzero : 0 ∈ C) (hq : q ∈ C)
    (K k : ℕ) (hk : k ≤ K) : k*q ∈ K • C := by
  induction K generalizing k with
  | zero =>
    have : k = 0 := by omega
    simp [this]
  | succ K ih =>
    rw [succ_nsmul]
    cases k with
    | zero =>
      have h := ih 0 (by omega)
      simpa using (Set.add_mem_add h hzero)
    | succ k =>
      simpa [Nat.succ_mul] using (Set.add_mem_add (ih k (by omega)) hq)
private theorem glueAdjacent {A B : Set ℕ} {I J d p q X n : ℕ}
    (hzero : 0 ∈ B) (hq : q ∈ B) (hX : 0 < X)
    (hp : 0 < p) (hposq : 0 < q) (hpX : p ≤ 2*X) (hqX : q ≤ 2*(X+1))
    (hXI : X ≤ I*p) (hXJ : X+1 ≤ J*q) (hd : 0 < d) (hdI : d ≤ I)
    (hdn : d ∣ n) (hsmall : 2*(4*(I+1))*X ≤ n) (hlarge : n < 2*(4*(J+1))*(X+1))
    (hlocal : ∀ u k : ℕ, d ∣ u → 4*(I+1)*p ≤ u →
      u+4*(I+1)*p ≤ k*p → u ∈ k • A) :
    ∃ u ∈ twoScaleCap I • A, ∃ v ∈ twoScaleCap J • B, u+v=n := by
  let lo := 4*(I+1)*p
  let z := n-lo
  let stride := d*q
  let k := (z/stride)*d
  let v := k*q
  let u := lo+z%stride
  have hlo : lo ≤ n := calc
    lo ≤ 4*(I+1)*(2*X) := Nat.mul_le_mul_left _ hpX
    _ = 2*(4*(I+1))*X := by ring
    _ ≤ n := hsmall
  have hv : v = stride*(z/stride) := by dsimp [v,k,stride]; ring
  have hsum : u+v=n := by
    change (lo+z%stride)+v=n
    rw [hv, Nat.add_assoc, Nat.mod_add_div]
    dsimp [z]
    omega
  have hdv : d ∣ v := ⟨(z/stride)*q, by dsimp [v,k]; ring⟩
  have hdu : d ∣ u := by
    have heq : u = n-v := by omega
    rw [heq]
    exact Nat.dvd_sub hdn hdv
  have hstride : stride ≤ 4*I^2*p := calc
    d*q ≤ I*(4*X) := Nat.mul_le_mul hdI (by omega)
    _ ≤ I*(4*(I*p)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hXI)
    _ = 4*I^2*p := by ring
  have hmod : z%stride < stride := Nat.mod_lt _ (Nat.mul_pos hd hposq)
  have hu : u+lo ≤ twoScaleCap I*p := calc
    u+lo ≤ (2*(4*(I+1)) + 4*I^2)*p := by
      dsimp [u, lo]
      rw [Nat.add_mul]
      have he : 2*(4*(I+1))*p = 4*(I+1)*p + 4*(I+1)*p := by ring
      omega
    _ ≤ twoScaleCap I*p := Nat.mul_le_mul_right _ (by unfold twoScaleCap; omega)
  have hk : k ≤ twoScaleCap J := by
    have hs : k*q ≤ (2*(4*(J+1))*J)*q := calc
      k*q ≤ n := by change v ≤ n; omega
      _ ≤ 2*(4*(J+1))*(X+1) := by omega
      _ ≤ 2*(4*(J+1))*(J*q) := Nat.mul_le_mul_left _ hXJ
      _ = (2*(4*(J+1))*J)*q := by ring
    have hh : k ≤ 2*(4*(J+1))*J := Nat.le_of_mul_le_mul_right hs hposq
    unfold twoScaleCap
    omega
  exact ⟨u, hlocal u _ hdu (Nat.le_add_right _ _) hu, v,
    mul_mem_copies hzero hq _ k hk, hsum⟩
theorem twoScaleCover (h : ℕ) (C : ℕ → Set ℕ) (L d : ℕ → ℕ)
    (hd : ∀ i<h, 0<d i) (h0 : ∀ i<h, 0∈C i)
    (windows : ∀ᶠ X : ℕ in atTop, ∃ i<h, ∃ p∈C i,
      0<p ∧ p≤2*X ∧ X≤L i*p ∧ d i≤L i ∧
      ∀ u k : ℕ, d i∣u → 4*(L i+1)*p≤u →
        u+4*(L i+1)*p≤k*p → u∈k • C i) :
    ∃ g : ℕ, 0<g ∧ ∀ᶠ n : ℕ in atTop, g∣n → ∃ i<h, ∃ j<h,
      ∃ u∈twoScaleCap (L i) • C i, ∃ v∈twoScaleCap (L j) • C j, u+v=n := by
  classical
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.1 windows
  let B := X₀+1
  have hwin (t : ℕ) := hX₀ (B+t) (by dsimp [B]; omega)
  choose idx hi p hp hpPos hpX hXp hdL hcover using hwin
  let g := ∏ i ∈ Finset.range h, d i
  have hg : 0<g := Finset.prod_pos (fun i hi => hd i (Finset.mem_range.mp hi))
  refine ⟨g, hg, eventually_atTop.2 ⟨2*(4*(L (idx 0)+1))*B, ?_⟩⟩
  intro n hn hgn
  let fine := fun t : ℕ => 2*(4*(L (idx t)+1))*(B+t) ≤ n
  have hf : fine 0 := by simpa [fine] using hn
  have hc : ¬fine (n+1) := by
    have hp : 1 ≤ 2*(4*(L (idx (n+1))+1)) := by omega
    have hx := Nat.mul_le_mul_right (B+(n+1)) hp
    simp only [one_mul] at hx
    dsimp [fine]
    omega
  have hstep : ∃ t : ℕ, fine t ∧ ¬fine (t+1) := by
    by_contra hnone
    have every (t : ℕ) : fine t := by
      induction t with
      | zero => exact hf
      | succ t ih =>
        by_contra hh
        exact hnone ⟨t, ih, hh⟩
    exact hc (every _)
  obtain ⟨t,hf,hc⟩ := hstep
  have hdiv : d (idx t) ∣ g := Finset.dvd_prod_of_mem d (Finset.mem_range.mpr (hi t))
  refine ⟨idx t, hi t, idx (t+1), hi (t+1), ?_⟩
  apply glueAdjacent (X := B+t) (d := d (idx t))
    (p := p t) (q := p (t+1)) (h0 _ (hi _)) (hp _)
  · dsimp [B]; omega
  · exact hpPos _
  · exact hpPos _
  · exact hpX _
  · simpa [Nat.add_assoc] using hpX (t+1)
  · exact hXp _
  · simpa [Nat.add_assoc] using hXp (t+1)
  · exact hd _ (hi _)
  · exact hdL _
  · exact hdiv.trans hgn
  · exact hf
  · simpa [fine,Nat.add_assoc] using Nat.lt_of_not_ge hc
  · exact hcover _
end OMA.E338.Bridge
end

-- module CommonWindows
section
namespace OMA.E338.Bridge
open Filter
open scoped Pointwise Classical
theorem synchronizeProductiveWindows
    (h : ℕ) (C : ℕ → Set ℕ) (L : ℕ → ℕ)
    (cover : ∀ i < h, ∃ d : ℕ, 0 < d ∧ ∀ᶠ X : ℕ in atTop,
      6*X ≤ L i * windowCount (C i) (2*X) →
      ∃ ℓ ∈ C i, 0 < ℓ ∧ ℓ ≤ 2*X ∧ X ≤ L i * ℓ ∧ d ≤ L i ∧
        ∀ u k : ℕ, d ∣ u → (4*(L i+1))*ℓ ≤ u →
          u + (4*(L i+1))*ℓ ≤ k*ℓ → u ∈ k • C i)
    (mass : ∀ᶠ X : ℕ in atTop, ∃ i < h, 6*X ≤ L i * windowCount (C i) (2*X)) :
    ∃ d : ℕ → ℕ, (∀ i < h, 0 < d i) ∧ ∀ᶠ X : ℕ in atTop,
      ∃ i < h, ∃ ℓ ∈ C i, 0 < ℓ ∧ ℓ ≤ 2*X ∧ X ≤ L i * ℓ ∧ d i ≤ L i ∧
        ∀ u k : ℕ, d i ∣ u → (4*(L i+1))*ℓ ≤ u →
          u + (4*(L i+1))*ℓ ≤ k*ℓ → u ∈ k • C i := by
  classical
  let d := fun i => if hi : i < h then (cover i hi).choose else 1
  have pos (i : ℕ) (hi : i < h) : 0 < d i := by
    simpa [d, hi] using (cover i hi).choose_spec.1
  have per (i : ℕ) (hi : i ∈ Finset.range h) :
      ∀ᶠ X : ℕ in atTop, 6*X ≤ L i * windowCount (C i) (2*X) →
        ∃ ℓ ∈ C i, 0 < ℓ ∧ ℓ ≤ 2*X ∧ X ≤ L i * ℓ ∧ d i ≤ L i ∧
          ∀ u k : ℕ, d i ∣ u → (4*(L i+1))*ℓ ≤ u →
            u + (4*(L i+1))*ℓ ≤ k*ℓ → u ∈ k • C i := by
    have ht := Finset.mem_range.mp hi
    simpa [d, ht] using (cover i ht).choose_spec.2
  refine ⟨d, pos, ?_⟩
  filter_upwards [mass, ((Finset.range h).eventually_all).2 per] with X good all
  obtain ⟨i, hi, hm⟩ := good
  exact ⟨i, hi, all i (Finset.mem_range.mpr hi) hm⟩
end OMA.E338.Bridge
end

-- module FiniteModular
section
namespace OMA.E338.FiniteModular
open scoped BigOperators
def Short {ι G : Type*} [AddCommMonoid G] (a : ι → G) (h : ℕ) (x : G) : Prop :=
  ∃ s : Finset ι, s.card ≤ h ∧ s.sum a = x
noncomputable def shortResidues {ι G : Type*} [AddCommMonoid G] [Fintype G]
    (a : ι → G) (h : ℕ) : Finset G := by
  classical
  exact Finset.univ.filter (Short a h)
@[simp] theorem mem_shortResidues {ι G : Type*} [AddCommMonoid G] [Fintype G]
    (a : ι → G) (h : ℕ) (x : G) : x ∈ shortResidues a h ↔ Short a h x := by
  classical
  simp [shortResidues]
def UniformModularBound : Prop :=
  ∀ h m : ℕ, 0 < m → ∃ b : ℕ,
    ∀ (q : ℕ) [NeZero q] (n : ℕ) (a : Fin n → ZMod q),
      (∀ x, ∃ s : Finset (Fin n), s.sum a = x) →
      q ≤ m * (shortResidues a h).card → ∀ x, Short a b x
theorem column_card {ι G : Type*} [DecidableEq ι] [AddCommGroup G] [Fintype G]
    (R : Finset G) (w : G → Finset ι) (a : ι → G) (j : ℕ)
    (hsum : ∀ r ∈ R, (w r).sum a = r)
    (hsize : ∀ r ∈ R, (w r).card ≤ j + 1) (i : ι) :
    (R.filter (fun r => i ∈ w r)).card ≤ (shortResidues a j).card := by
  classical
  apply Finset.card_le_card_of_injOn (fun r : G => r - a i)
  · intro r hr
    obtain ⟨hrR, hi⟩ := Finset.mem_filter.mp hr
    apply (mem_shortResidues a j _).mpr
    refine ⟨(w r).erase i, ?_, ?_⟩
    · have hc := hsize r hrR
      rw [Finset.card_erase_of_mem hi]
      omega
    · exact eq_sub_iff_add_eq.mpr (((w r).sum_erase_add a hi).trans (hsum r hrR))
  · intro x _ y _ hxy
    simpa only [sub_add_cancel] using congrArg (fun z : G => z + a i) hxy
theorem hit_card {ι G : Type*} [DecidableEq ι] [DecidableEq G]
    (R : Finset G) (w : G → Finset ι) (W : Finset ι) (e : ℕ)
    (hcol : ∀ i ∈ W, (R.filter (fun r => i ∈ w r)).card ≤ e) :
    (W.biUnion (fun i => R.filter (fun r => i ∈ w r))).card ≤ W.card * e := by
  calc
    _ ≤ ∑ i ∈ W, (R.filter (fun r => i ∈ w r)).card := Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ W, e := Finset.sum_le_sum hcol
    _ = W.card * e := by simp [nsmul_eq_mul]
noncomputable def goodLeft {ι G : Type*} [AddCommGroup G]
    (R : Finset G) (w : G → Finset ι) (z : G) : Finset G := by
  classical
  exact R.filter (fun x => z - x ∈ R ∧ Disjoint (w x) (w (z - x)))
theorem avoid_for_popular {ι G : Type*} [DecidableEq ι] [DecidableEq G] [AddCommGroup G]
    (R : Finset G) (w : G → Finset ι) (a : ι → G) (W : Finset ι) (z : G) (j e : ℕ)
    (hsum : ∀ r ∈ R, (w r).sum a = r)
    (hsize : ∀ r ∈ R, (w r).card ≤ j)
    (hcol : ∀ i ∈ W, (R.filter (fun r => i ∈ w r)).card ≤ e)
    (hpop : 2 * (W.card * e) < (goodLeft R w z).card) :
    ∃ s : Finset ι, Disjoint W s ∧ s.card ≤ 2 * j ∧ s.sum a = z := by
  classical
  let H := W.biUnion (fun i => R.filter (fun r => i ∈ w r))
  let H' := H.image (fun y => z - y)
  have hH : H.card ≤ W.card * e := hit_card R w W e hcol
  have hH' : H'.card ≤ H.card := Finset.card_image_le
  have htotal := Finset.card_union_le H H'
  have hlt : (H ∪ H').card < (goodLeft R w z).card := by omega
  obtain ⟨x, hx, hout⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have hp : x ∈ R ∧ z - x ∈ R ∧ Disjoint (w x) (w (z - x)) := by
    simpa [goodLeft] using hx
  obtain ⟨hxR, hyR, hdis⟩ := hp
  have havoid (t : G) (ht : t ∈ R) (hnot : t ∉ H) : Disjoint W (w t) := by
    apply Finset.disjoint_left.mpr
    intro i hi hw
    exact hnot (Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_filter.mpr ⟨ht, hw⟩⟩)
  have hleft := havoid x hxR (fun h => hout (Finset.mem_union_left _ h))
  have hright : Disjoint W (w (z - x)) := by
    apply havoid (z - x) hyR
    intro h
    apply hout
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨z - x, h, by abel⟩
  refine ⟨w x ∪ w (z - x), ?_, ?_, ?_⟩
  · apply Finset.disjoint_left.mpr
    intro i hi hj
    rcases Finset.mem_union.mp hj with hl | hr
    · exact Finset.disjoint_left.mp hleft hi hl
    · exact Finset.disjoint_left.mp hright hi hr
  · have hc := Finset.card_union_le (w x) (w (z - x))
    have hl := hsize x hxR
    have hr := hsize (z - x) hyR
    omega
  · rw [Finset.sum_union hdis, hsum x hxR, hsum (z - x) hyR]
    abel
theorem liftGreedy {ι G : Type*} [DecidableEq ι] [AddCommMonoid G]
    (a : ι → G) (k cap : ℕ) (xs : List G) :
    ∀ W : Finset ι,
      (∀ x ∈ xs, ∀ F : Finset ι, F.card ≤ cap →
        ∃ S : Finset ι, Disjoint F S ∧ S.card ≤ k ∧ S.sum a = x) →
      W.card + k * xs.length ≤ cap →
      ∃ S : Finset ι, Disjoint W S ∧ S.card ≤ k * xs.length ∧
        S.sum a = xs.sum := by
  induction xs with
  | nil =>
    intro W _ _
    exact ⟨∅, by simp, by simp, by simp⟩
  | cons x xs ih =>
    intro W avail room
    simp only [List.length_cons, Nat.mul_succ] at room
    obtain ⟨S, hWS, hSc, hSs⟩ := avail x (by simp) W (by omega)
    have hc := Finset.card_union_le W S
    obtain ⟨T, hUT, hTc, hTs⟩ := ih (W ∪ S)
      (fun y hy => avail y (List.mem_cons_of_mem _ hy)) (by omega)
    have hST : Disjoint S T := Finset.disjoint_left.mpr (by
      intro i hi hj
      exact (Finset.disjoint_left.mp hUT) (Finset.mem_union_right W hi) hj)
    refine ⟨S ∪ T, ?_, ?_, ?_⟩
    · apply Finset.disjoint_left.mpr
      intro i hi hj
      rcases Finset.mem_union.mp hj with hs | ht
      · exact (Finset.disjoint_left.mp hWS) hi hs
      · exact (Finset.disjoint_left.mp hUT) (Finset.mem_union_left S hi) ht
    · have hcard := Finset.card_union_le S T
      simp only [List.length_cons, Nat.mul_succ]
      omega
    · rw [Finset.sum_union hST, hSs, hTs, List.sum_cons]
theorem popularity_card {α : Type*} (s : Finset α)
    (p : α → ℕ) (m q : ℕ) (hq : 0 < q) (hcard : s.card = q)
    (hcap : ∀ z ∈ s, p z ≤ q)
    (hmass : 15*q^2 ≤ 16*m^2*(∑ z ∈ s, p z)) :
    11*q ≤ 16*m^2*(s.filter (fun z => q ≤ 4*m^2*p z)).card := by
  have hpoint (z : α) (hz : z ∈ s) :
      16*m^2*p z ≤ 4*q + (if q ≤ 4*m^2*p z then 16*m^2*q else 0) := by
    by_cases h : q ≤ 4*m^2*p z
    · rw [if_pos h]
      have hb := Nat.mul_le_mul_left (16*m^2) (hcap z hz)
      omega
    · rw [if_neg h, add_zero]
      calc
        16*m^2*p z = 4*(4*m^2*p z) := by ring
        _ ≤ 4*q := Nat.mul_le_mul_left 4 (le_of_lt (lt_of_not_ge h))
  have hupper : 16*m^2*(∑ z ∈ s, p z) ≤ q*(4*q) +
      (s.filter (fun z => q ≤ 4*m^2*p z)).card*(16*m^2*q) := by
    calc
      _ = ∑ z ∈ s, 16*m^2*p z := by rw [Finset.mul_sum]
      _ ≤ ∑ z ∈ s, (4*q + (if q ≤ 4*m^2*p z then 16*m^2*q else 0)) :=
        Finset.sum_le_sum hpoint
      _ = _ := by
        rw [Finset.sum_add_distrib,
          ← Finset.sum_filter (s := s) (fun z => q ≤ 4*m^2*p z) (fun _ => 16*m^2*q)]
        simp [nsmul_eq_mul, hcard]
  apply Nat.le_of_mul_le_mul_left (c := q) ?_ hq
  nlinarith only [hmass.trans hupper]
theorem short_sum {ι G : Type*} [Fintype G] [AddCommMonoid G]
    (f : ι → G) (p : Finset ι) :
    ∃ t ⊆ p, t.sum f = p.sum f ∧ t.card < Fintype.card G := by
  classical
  let R (s : Finset ι) : Finset G :=
    Finset.univ.filter (fun x => ∃ u ⊆ s, u.sum f = x)
  have memR {s : Finset ι} {x : G} :
      x ∈ R s ↔ ∃ u ⊆ s, u.sum f = x := by
    simp only [R, Finset.mem_filter, Finset.mem_univ, true_and]
  have aux (s : Finset ι) : ∀ x ∈ R s,
      ∃ t ⊆ s, t.sum f = x ∧ t.card < (R s).card := by
    induction s using Finset.induction_on with
    | empty =>
      intro x hx
      obtain ⟨u, hu, he⟩ := memR.mp hx
      have hu0 : u = ∅ := by simpa using hu
      subst u
      exact ⟨∅, by simp, he, by simpa using Finset.card_pos.mpr ⟨x, hx⟩⟩
    | @insert a s ha ih =>
      intro x hx
      have inc : R s ⊆ R (insert a s) := by
        intro y hy
        obtain ⟨u, hu, he⟩ := memR.mp hy
        exact memR.mpr ⟨u, hu.trans (Finset.subset_insert a s), he⟩
      by_cases old : x ∈ R s
      · obtain ⟨t, ht, he, hc⟩ := ih x old
        exact ⟨t, ht.trans (Finset.subset_insert a s), he,
          lt_of_lt_of_le hc (Finset.card_le_card inc)⟩
      · have grow : (R s).card < (R (insert a s)).card :=
          Finset.card_lt_card ((Finset.ssubset_iff_of_subset inc).mpr ⟨x, hx, old⟩)
        obtain ⟨u, hu, he⟩ := memR.mp hx
        have hau : a ∈ u := by
          by_contra hn
          exact old (memR.mpr ⟨u, (Finset.subset_insert_iff_of_notMem hn).mp hu, he⟩)
        have hus : u.erase a ⊆ s := Finset.subset_insert_iff.mp hu
        obtain ⟨t, ht, et, ct⟩ := ih ((u.erase a).sum f) (memR.mpr ⟨_, hus, rfl⟩)
        have hat : a ∉ t := fun h => ha (ht h)
        refine ⟨insert a t, Finset.insert_subset_insert a ht, ?_, ?_⟩
        · rw [Finset.sum_insert hat, et, Finset.add_sum_erase u f hau, he]
        · rw [Finset.card_insert_of_notMem hat]
          omega
  obtain ⟨t, ht, he, hc⟩ := aux p (p.sum f) (memR.mpr ⟨p, by rfl, rfl⟩)
  exact ⟨t, ht, he, lt_of_lt_of_le hc (Finset.card_le_univ _)⟩
def budget (j m : ℕ) : ℕ := (2*j + 1) * (4*m^2)
def nextDenom (j m : ℕ) : ℕ := 16 * budget j m * m^2
def lengthBound : ℕ → ℕ → ℕ
  | 0, m => m
  | j+1, m => max (lengthBound j (nextDenom (j+1) m)) (budget (j+1) m)
def SparseStep : Prop :=
  ∀ (j m q : ℕ) [NeZero q] (n : ℕ) (a : Fin n → ZMod q), 0 < m →
    (∀ x, ∃ s : Finset (Fin n), s.sum a = x) →
    q ≤ m * (shortResidues a (j+1)).card →
    nextDenom (j+1) m * (shortResidues a j).card < q →
    ∀ x, Short a (budget (j+1) m) x
theorem short_mono {ι G : Type*} [AddCommMonoid G] {a : ι → G} {x : G}
    {s t : ℕ} (hst : s ≤ t) (hs : Short a s x) : Short a t x := by
  obtain ⟨U, hU, hx⟩ := hs
  exact ⟨U, hU.trans hst, hx⟩
theorem uniform_of_sparse (step : SparseStep) : UniformModularBound := by
  classical
  have main (h : ℕ) : ∀ m : ℕ, 0 < m →
      ∀ (q : ℕ) [NeZero q] (n : ℕ) (a : Fin n → ZMod q),
        (∀ x, ∃ s : Finset (Fin n), s.sum a = x) →
        q ≤ m * (shortResidues a h).card → ∀ x, Short a (lengthBound h m) x := by
    induction h with
    | zero =>
      intro m hm q inst n a cover dense x
      have hzero : shortResidues a 0 = {0} := by
        ext y
        simp only [mem_shortResidues, Finset.mem_singleton]
        constructor
        · rintro ⟨s, hs, he⟩
          have hs0 : s = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hs)
          simpa [hs0] using he.symm
        · rintro rfl
          exact ⟨∅, by simp, by simp⟩
      have hqm : q ≤ m := by simpa [hzero] using dense
      obtain ⟨s, hs⟩ := cover x
      obtain ⟨t, _, he, hc⟩ := short_sum a s
      have hlt : t.card < q := by simpa only [ZMod.card] using hc
      exact ⟨t, hlt.le.trans hqm, he.trans hs⟩
    | succ j ih =>
      intro m hm q inst n a cover dense x
      by_cases hsm : q ≤ nextDenom (j+1) m * (shortResidues a j).card
      · have hpos : 0 < nextDenom (j+1) m := by
          unfold nextDenom budget
          positivity
        exact short_mono (le_max_left _ _) (ih _ hpos q n a cover hsm x)
      · exact short_mono (le_max_right _ _)
          (step j m q n a hm cover dense (lt_of_not_ge hsm) x)
  intro h m hm
  exact ⟨lengthBound h m, main h m hm⟩
def DenseSplit : Prop :=
  ∀ (q : ℕ) [NeZero q] (n : ℕ) (a : Fin n → ZMod q) (D : Finset (ZMod q)) (L : ℕ),
    0 ∈ D → 2*q ≤ L*D.card → (∀ x, ∃ s : Finset (Fin n), s.sum a = x) →
    ∀ x, ∃ (E : Finset (Fin n)) (xs : List (ZMod q)),
      E.card ≤ L ∧ xs.length ≤ L ∧ (∀ d ∈ xs, d ∈ D) ∧ E.sum a + xs.sum = x
theorem goodLeft_mass {ι G : Type*} [DecidableEq ι] [AddCommGroup G] [Fintype G]
    (R : Finset G) (w : G → Finset ι) (j e : ℕ)
    (hsize : ∀ x ∈ R, (w x).card ≤ j)
    (hcol : ∀ i, (R.filter (fun y => i ∈ w y)).card ≤ e) :
    R.card ^ 2 ≤ (∑ z : G, (goodLeft R w z).card) + R.card * (j * e) := by
  classical
  let Q (x : G) := Finset.univ.filter (fun z => x ∈ goodLeft R w z)
  have row (x : G) (hx : x ∈ R) : R.card ≤ (Q x).card + j * e := by
    let H := (w x).biUnion (fun i => R.filter (fun y => i ∈ w y))
    have hH : H.card ≤ j * e :=
      (hit_card R w (w x) e (fun i _ => hcol i)).trans
        (Nat.mul_le_mul_right e (hsize x hx))
    have hrest : (R \ H).card ≤ (Q x).card := by
      apply Finset.card_le_card_of_injOn (fun y : G => x + y)
      · intro y hy
        obtain ⟨hyR, hyH⟩ := Finset.mem_sdiff.mp hy
        have hd : Disjoint (w x) (w y) := Finset.disjoint_left.mpr (by
          intro i hi hiy
          exact hyH (Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_filter.mpr ⟨hyR, hiy⟩⟩))
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        have he : x + y - x = y := by abel
        simpa only [goodLeft, Finset.mem_filter, he] using
          (show x ∈ R ∧ y ∈ R ∧ Disjoint (w x) (w y) from ⟨hx, hyR, hd⟩)
      · intro a _ b _ hab
        exact add_left_cancel hab
    have hsub : R ⊆ (R \ H) ∪ H := by
      intro y hy
      by_cases hyH : y ∈ H
      · exact Finset.mem_union_right _ hyH
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hy, hyH⟩)
    exact (Finset.card_le_card hsub).trans
      ((Finset.card_union_le _ _).trans (Nat.add_le_add hrest hH))
  have count (s : Finset G) (p : G → Prop) [DecidablePred p] :
      (s.filter p).card = ∑ x ∈ s, if p x then (1 : ℕ) else 0 := by
    rw [← Finset.sum_filter]
    simp
  have fibre (z : G) : R.filter (fun x => x ∈ goodLeft R w z) = goodLeft R w z := by
    ext x
    constructor
    · intro hx
      exact (Finset.mem_filter.mp hx).2
    · intro hx
      have hp : x ∈ R ∧ z - x ∈ R ∧ Disjoint (w x) (w (z - x)) := by
        simpa only [goodLeft, Finset.mem_filter] using hx
      exact Finset.mem_filter.mpr ⟨hp.1, hx⟩
  have doubleCount : (∑ x ∈ R, (Q x).card) = ∑ z : G, (goodLeft R w z).card := by
    calc
      _ = ∑ x ∈ R, ∑ z : G, if x ∈ goodLeft R w z then (1 : ℕ) else 0 :=
        Finset.sum_congr rfl (fun x _ => count Finset.univ _)
      _ = ∑ z : G, ∑ x ∈ R, if x ∈ goodLeft R w z then (1 : ℕ) else 0 :=
        Finset.sum_comm
      _ = _ := Finset.sum_congr rfl (fun z _ =>
        (count R (fun x => x ∈ goodLeft R w z)).symm.trans (congrArg Finset.card (fibre z)))
  calc
    R.card ^ 2 = ∑ _x ∈ R, R.card := by simp [pow_two, nsmul_eq_mul]
    _ ≤ ∑ x ∈ R, ((Q x).card + j * e) := Finset.sum_le_sum row
    _ = _ := by rw [Finset.sum_add_distrib, doubleCount]; simp [nsmul_eq_mul]
private theorem mass_estimate (q m M j e S P : ℕ)
    (hdense : q ≤ m*M) (hM : M ≤ q) (hj : j ≤ S)
    (hsparse : 16*S*m^2*e < q) (hcount : M^2 ≤ P + M*(j*e)) :
    15*q^2 ≤ 16*m^2*P := by
  have hs : q*q ≤ (m*M)*(m*M) := Nat.mul_le_mul hdense hdense
  have hje : 16*j*m^2*e ≤ q := by
    calc
      _ ≤ 16*S*m^2*e := by gcongr
      _ ≤ q := hsparse.le
  have hloss := Nat.mul_le_mul hM hje
  have hcount' := Nat.mul_le_mul_left (16*m^2) hcount
  nlinarith only [hs, hloss, hcount']
theorem sparse_of_denseSplit (split : DenseSplit) : SparseStep := by
  classical
  intro j m q inst n a hm cover dense sparse x
  let J := j+1
  let R := shortResidues a J
  let e := (shortResidues a j).card
  let L := 4*m^2
  let S := budget J m
  have hS : S = (2*J+1)*L := rfl
  have hL : 0 < L := by dsimp [L]; positivity
  have hJS : J ≤ S := by
    rw [hS]
    calc
      J ≤ 2*J+1 := by omega
      _ = (2*J+1)*1 := by simp
      _ ≤ (2*J+1)*L := Nat.mul_le_mul_left _ hL
  have hsp : 16*S*m^2*e < q := sparse
  have hR (u : ZMod q) (hu : u ∈ R) : Short a J u :=
    (mem_shortResidues a J u).mp hu
  let w (u : ZMod q) : Finset (Fin n) :=
    if hu : u ∈ R then (hR u hu).choose else ∅
  have hw (u : ZMod q) (hu : u ∈ R) :
      (w u).card ≤ J ∧ (w u).sum a = u := by
    simpa only [w, dif_pos hu] using (hR u hu).choose_spec
  have size := fun u hu => (hw u hu).1
  have sums := fun u hu => (hw u hu).2
  have col (i : Fin n) : (R.filter (fun u => i ∈ w u)).card ≤ e :=
    column_card R w a j sums size i
  let p (d : ZMod q) := (goodLeft R w d).card
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hM : R.card ≤ q := by simpa only [ZMod.card] using Finset.card_le_univ R
  have mass : 15*q^2 ≤ 16*m^2*(∑ d, p d) :=
    mass_estimate q m R.card J e S _ dense hM hJS hsp
      (goodLeft_mass R w J e size col)
  let P := Finset.univ.filter (fun d : ZMod q => q ≤ 4*m^2*p d)
  let D := insert 0 P
  have hP : 11*q ≤ 16*m^2*P.card :=
    popularity_card Finset.univ p m q hq (by simp [ZMod.card])
      (fun d _ => by simpa only [ZMod.card] using Finset.card_le_univ (goodLeft R w d)) mass
  have hPD : P.card ≤ D.card := Finset.card_le_card (Finset.subset_insert _ _)
  have hD : 2*q ≤ L*D.card := by
    dsimp [L]
    nlinarith only [hP, Nat.mul_le_mul_left (16*m^2) hPD, Nat.zero_le q]
  obtain ⟨E, xs, hE, hxs, hmem, hx⟩ :=
    split q n a D L (Finset.mem_insert_self _ _) hD cover x
  have avail (d : ZMod q) (hd : d ∈ xs) (W : Finset (Fin n)) (hW : W.card ≤ S) :
      ∃ T : Finset (Fin n), Disjoint W T ∧ T.card ≤ 2*J ∧ T.sum a = d := by
    rcases Finset.mem_insert.mp (hmem d hd) with hz | hpop
    · subst d
      exact ⟨∅, by simp, by simp, by simp⟩
    · have hpd : q ≤ 4*m^2*p d := (Finset.mem_filter.mp hpop).2
      apply avoid_for_popular R w a W d J e sums size (fun i _ => col i)
      change 2 * (W.card * e) < p d
      by_contra! hbad
      have hc : q ≤ 16*S*m^2*e := calc
        q ≤ 4*m^2*p d := hpd
        _ ≤ 4*m^2*(2*(W.card*e)) := Nat.mul_le_mul_left _ hbad
        _ = 8*W.card*m^2*e := by ring
        _ ≤ 16*S*m^2*e := by gcongr <;> norm_num
      exact (Nat.not_le_of_gt hsp) hc
  have hroom : E.card + (2*J)*xs.length ≤ S := calc
    _ ≤ L + (2*J)*L := Nat.add_le_add hE (Nat.mul_le_mul_left _ hxs)
    _ = S := by rw [hS]; ring
  obtain ⟨T, hdis, hT, hsum⟩ := liftGreedy a (2*J) S xs E avail hroom
  refine ⟨E ∪ T, ?_, ?_⟩
  · exact (Finset.card_union_le E T).trans
      ((Nat.add_le_add_left hT E.card).trans hroom)
  · rw [Finset.sum_union hdis, hsum, hx]
open scoped Pointwise
noncomputable def sumLayer {G : Type*} [Fintype G] [AddCommGroup G] [DecidableEq G]
    (D : Finset G) : ℕ → Finset G
  | 0 => {0}
  | k+1 => sumLayer D k + D
theorem zero_mem_sumLayer {G : Type*} [Fintype G] [AddCommGroup G] [DecidableEq G]
    (D : Finset G) (hD : 0 ∈ D) (k : ℕ) : 0 ∈ sumLayer D k := by
  induction k with
  | zero => simp [sumLayer]
  | succ k ih =>
    change 0 ∈ sumLayer D k + D
    exact Finset.mem_add.mpr ⟨0, ih, 0, hD, zero_add _⟩
theorem word_of_mem_sumLayer {G : Type*} [Fintype G] [AddCommGroup G] [DecidableEq G]
    (D : Finset G) (k : ℕ) {z : G} (hz : z ∈ sumLayer D k) :
    ∃ xs : List G, xs.length = k ∧ (∀ d ∈ xs, d ∈ D) ∧ xs.sum = z := by
  induction k generalizing z with
  | zero =>
    have hzero : z = 0 := Finset.mem_singleton.mp hz
    exact ⟨[], rfl, by simp, by simp [hzero]⟩
  | succ k ih =>
    change z ∈ sumLayer D k + D at hz
    obtain ⟨y, hy, d, hd, heq⟩ := Finset.mem_add.mp hz
    obtain ⟨ys, hlen, hmem, hsum⟩ := ih hy
    refine ⟨d :: ys, by simp [hlen], ?_, ?_⟩
    · intro b hb
      rcases List.mem_cons.mp hb with rfl | hb'
      · exact hd
      · exact hmem b hb'
    · rw [List.sum_cons, hsum, add_comm, heq]
def IteratedKneser : Prop :=
  ∀ (q : ℕ) [NeZero q] (D : Finset (ZMod q)) (L : ℕ), 0 ∈ D → 0 < L →
    ∃ H : AddSubgroup (ZMod q),
      (∀ h ∈ H, ∀ y ∈ sumLayer D L, y + h ∈ sumLayer D L) ∧
      L * D.card ≤ (sumLayer D L).card + (L-1) * Nat.card H
theorem denseSplit_of_iteratedKneser (kneser : IteratedKneser) : DenseSplit := by
  classical
  intro q inst n a D L hD dense cover x
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hL : 0 < L := by
    by_contra hn
    have hzero : L = 0 := by omega
    rw [hzero, zero_mul] at dense
    omega
  obtain ⟨H, period, bound⟩ := kneser q D L hD hL
  have hsize : (sumLayer D L).card ≤ q := by
    simpa only [ZMod.card] using Finset.card_le_univ (sumLayer D L)
  have hmul : q ≤ L * Nat.card H := by
    have hle := Nat.mul_le_mul_right (Nat.card H) (Nat.sub_le L 1)
    omega
  have hprod : Nat.card (ZMod q ⧸ H) * Nat.card H = q := by
    simpa only [Nat.card_zmod] using H.card_eq_card_quotient_mul_card_addSubgroup.symm
  have hindex : Fintype.card (ZMod q ⧸ H) ≤ L := by
    rw [← Nat.card_eq_fintype_card]
    by_contra! hlt
    have hp := Nat.mul_lt_mul_of_pos_right hlt (Nat.card_pos (α := H))
    omega
  let π : ZMod q →+ (ZMod q ⧸ H) := QuotientAddGroup.mk' H
  obtain ⟨s, hs⟩ := cover x
  obtain ⟨E, _, hEs, hEcard⟩ := short_sum (fun i => π (a i)) s
  have hcoset : π x = π (E.sum a) := by
    calc
      π x = π (s.sum a) := congrArg π hs.symm
      _ = π (E.sum a) := by simpa only [map_sum] using hEs.symm
  have herr : x - E.sum a ∈ H := QuotientAddGroup.eq_iff_sub_mem.mp hcoset
  have hword : x - E.sum a ∈ sumLayer D L := by
    simpa only [zero_add] using
      period (x - E.sum a) herr 0 (zero_mem_sumLayer D hD L)
  obtain ⟨xs, hlen, hmem, hsum⟩ := word_of_mem_sumLayer D L hword
  exact ⟨E, xs, hEcard.le.trans hindex, hlen.le, hmem, by rw [hsum]; abel⟩
open scoped Pointwise
def BinaryKneser : Prop :=
  ∀ (q : ℕ) [NeZero q] (s t : Finset (ZMod q)),
    (s + (s + t).addStab).card + (t + (s + t).addStab).card ≤
      (s + t).card + (s + t).addStab.card
private theorem binaryKneser_card (kneser : BinaryKneser)
    (q : ℕ) [NeZero q] (s t : Finset (ZMod q)) (hne : (s + t).Nonempty) :
    s.card + t.card ≤ (s + t).card + Nat.card (AddAction.stabilizer (ZMod q) (s + t)) := by
  let P := (s + t).addStab
  let H := AddAction.stabilizer (ZMod q) (s + t)
  have hz : (0 : ZMod q) ∈ P := by
    apply (Finset.mem_addStab hne).mpr
    simp
  have pad (B : Finset (ZMod q)) : B.card ≤ (B + P).card := by
    apply Finset.card_le_card
    intro b hb
    simpa only [add_zero] using Finset.add_mem_add hb hz
  have hP : P.card ≤ Nat.card H := by
    rw [← Nat.card_eq_finsetCard P]
    let f (p : P) : H :=
      ⟨p.val, AddAction.mem_stabilizer_iff.mpr ((Finset.mem_addStab hne).mp p.property)⟩
    apply Nat.card_le_card_of_injective f
    intro x y hxy
    exact Subtype.ext (congrArg (fun g : H => g.val) hxy)
  calc
    s.card + t.card ≤ (s + P).card + (t + P).card := Nat.add_le_add (pad s) (pad t)
    _ ≤ (s + t).card + P.card := kneser q s t
    _ ≤ (s + t).card + Nat.card H := Nat.add_le_add_left hP _
private theorem sumset_stabilizer_mono {G : Type*} [AddCommGroup G] [DecidableEq G]
    (A D : Finset G) : AddAction.stabilizer G A ≤ AddAction.stabilizer G (A + D) := by
  intro h hh
  have hfix := AddAction.mem_stabilizer_iff.mp hh
  apply AddAction.mem_stabilizer_iff.mpr
  calc
    h +ᵥ (A + D) = ({h} : Finset G) + (A + D) := (Finset.singleton_add h).symm
    _ = (({h} : Finset G) + A) + D := (add_assoc _ _ _).symm
    _ = A + D := by rw [Finset.singleton_add, hfix]
theorem iteratedKneser_of_binaryKneser (kneser : BinaryKneser) : IteratedKneser := by
  intro q _ D L hD hL
  let St (A : Finset (ZMod q)) := AddAction.stabilizer (ZMod q) A
  have bound (k : ℕ) : (k+1) * D.card ≤ (sumLayer D (k+1)).card +
      k * Nat.card (St (sumLayer D (k+1))) := by
    induction k with
    | zero =>
      have oneLayer : sumLayer D 1 = D := by
        change ({0} : Finset (ZMod q)) + D = D
        rw [Finset.singleton_add, zero_vadd]
      simp [oneLayer]
    | succ k ih =>
      let A := sumLayer D (k+1)
      have hA : 0 ∈ A := zero_mem_sumLayer D hD (k+1)
      have hstep := binaryKneser_card kneser q A D ⟨0+0, Finset.add_mem_add hA hD⟩
      have hmono := sumset_stabilizer_mono A D
      have hc : Nat.card (St A) ≤ Nat.card (St (A+D)) := by
        let f (h : St A) : St (A+D) := ⟨h.val, hmono h.property⟩
        apply Nat.card_le_card_of_injective f
        intro x y hxy
        exact Subtype.ext (congrArg (fun g : St (A+D) => g.val) hxy)
      have hmul := Nat.mul_le_mul_left k hc
      change (k+1) * D.card ≤ A.card + k * Nat.card (St A) at ih
      change A.card + D.card ≤ (A+D).card + Nat.card (St (A+D)) at hstep
      change (k+1+1) * D.card ≤ (A+D).card + (k+1) * Nat.card (St (A+D))
      rw [Nat.succ_mul (k+1) D.card, Nat.succ_mul k (Nat.card (St (A+D)))]
      omega
  refine ⟨St (sumLayer D L), ?_, ?_⟩
  · intro h hh y hy
    have hm : h+y ∈ h +ᵥ sumLayer D L := Finset.vadd_mem_vadd_finset hy
    rw [AddAction.mem_stabilizer_iff.mp hh] at hm
    simpa only [add_comm h y] using hm
  · cases L with
    | zero => omega
    | succ k => simpa using bound k
theorem uniformModularBound : UniformModularBound := by
  apply uniform_of_sparse
  apply sparse_of_denseSplit
  apply denseSplit_of_iteratedKneser
  apply iteratedKneser_of_binaryKneser
  intro q inst s t
  exact Finset.add_kneser s t
end OMA.E338.FiniteModular
end

-- module BoundedByOrderFixed
section
open scoped BigOperators
namespace OMA.E338.Bridge
open Filter
def HasOrder (A : Set ℕ) (h : ℕ) : Prop :=
  ∀ᶠ n in atTop, ∃ s : Multiset ℕ, (∀ x ∈ s, x ∈ A) ∧ s.card ≤ h ∧ s.sum = n
def Rep (A : Set ℕ) (h n : ℕ) : Prop :=
  ∃ s : Finset ℕ, (∀ x ∈ s, x ∈ A) ∧ s.card ≤ h ∧ s.sum id = n
def HasRestrictedOrder (A : Set ℕ) (t : ℕ) : Prop :=
  ∀ᶠ n in atTop, Rep A t n
def restrictedSums (A : Set ℕ) (h : ℕ) : Set ℕ := {n | Rep A h n}
open scoped Classical in
def DensityBound (B : Set ℕ) (m : ℕ) : Prop :=
  ∃ N₀ : ℕ, ∀ N ≥ N₀, N ≤ m * ((Finset.range N).filter (fun n => n ∈ B)).card
def UniformDensityInput : Prop :=
  ∀ h : ℕ, 0 < h → ∃ m : ℕ, 0 < m ∧
    ∀ A : Set ℕ, HasOrder A h → DensityBound (restrictedSums A h) m
def UniformProgressionInput : Prop :=
  ∀ h m b : ℕ, 0 < h → 0 < m → ∃ K : ℕ,
    ∀ A : Set ℕ, DensityBound (restrictedSums A h) m →
      ∃ g : ℕ, 0 < g ∧ ∃ a : ZMod g, ∃ N₀ : ℕ,
        ∀ F : Finset ℕ, (∀ x ∈ F, x ∈ A) → F.card ≤ b →
          ∀ n : ℕ, N₀ ≤ n → (n : ZMod g) = a → Rep (A \ (F : Set ℕ)) K n
open scoped Classical in
theorem block_density_reduction (B : Set ℕ) (m : ℕ)
    (h : ∃ N₀ : ℕ, ∀ N ≥ N₀,
      N ≤ m * ((Finset.range N).filter (fun n => n ∈ B)).card)
    (q : ℕ) [NeZero q] :
    q ≤ m * (Finset.univ.filter (fun v : ZMod q => ∃ n ∈ B, (n : ZMod q) = v)).card := by
  classical
  obtain ⟨N₀, hN₀⟩ := h
  let k := N₀ + 1
  let R := Finset.univ.filter (fun v : ZMod q => ∃ n ∈ B, (n : ZMod q) = v)
  let S := (Finset.range (k * q)).filter (fun n => n ∈ B)
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hk : 0 < k := Nat.succ_pos _
  have hlarge : N₀ ≤ k * q :=
    (Nat.le_succ N₀).trans (Nat.le_mul_of_pos_right k hq)
  have hcount : S.card ≤ ((Finset.range k).product R).card := by
    apply Finset.card_le_card_of_injOn (fun n : ℕ => (n / q, (n : ZMod q)))
    · intro n hn
      change n ∈ (Finset.range (k * q)).filter (fun j => j ∈ B) at hn
      obtain ⟨hnRange, hnB⟩ := Finset.mem_filter.mp hn
      apply Finset.mem_product.mpr
      constructor
      · exact Finset.mem_range.mpr ((Nat.div_lt_iff_lt_mul hq).mpr (Finset.mem_range.mp hnRange))
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, n, hnB, rfl⟩
    · intro a _ b _ hab
      have hd : a / q = b / q := congrArg Prod.fst hab
      have hz : (a : ZMod q) = (b : ZMod q) := congrArg Prod.snd hab
      have hr : a % q = b % q := by simpa only [ZMod.val_natCast] using congrArg ZMod.val hz
      calc
        a = a % q + q * (a / q) := (Nat.mod_add_div a q).symm
        _ = b % q + q * (b / q) := by rw [hd, hr]
        _ = b := Nat.mod_add_div b q
  have hupper : S.card ≤ k * R.card := by
    calc
      S.card ≤ ((Finset.range k).product R).card := hcount
      _ = (Finset.range k).card * R.card := Finset.card_product (Finset.range k) R
      _ = k * R.card := by rw [Finset.card_range]
  have hboth : k * q ≤ k * (m * R.card) := calc
    k * q ≤ m * S.card := hN₀ _ hlarge
    _ ≤ m * (k * R.card) := Nat.mul_le_mul_left _ hupper
    _ = k * (m * R.card) := by ac_rfl
  exact Nat.le_of_mul_le_mul_left hboth hk
def ModRep (A : Set ℕ) (q : ℕ) (s : Finset ℕ) (v : ZMod q) : Prop :=
  (∀ x ∈ s, x ∈ A) ∧ ((s.sum id : ℕ) : ZMod q) = v
noncomputable def shortMod (A : Set ℕ) (h q : ℕ) [NeZero q] : Finset (ZMod q) := by
  classical
  exact Finset.univ.filter (fun v => ∃ s : Finset ℕ, s.card ≤ h ∧ ModRep A q s v)
@[simp] theorem mem_shortMod (A : Set ℕ) (h q : ℕ) [NeZero q] (v : ZMod q) :
    v ∈ shortMod A h q ↔ ∃ s : Finset ℕ, s.card ≤ h ∧ ModRep A q s v := by
  classical
  simp [shortMod]
theorem uniformModularForSet (h m : ℕ) (hm : 0 < m) :
    ∃ b : ℕ, ∀ (A : Set ℕ) (q : ℕ) [NeZero q],
      (∀ v : ZMod q, ∃ s : Finset ℕ, ModRep A q s v) →
      q ≤ m * (shortMod A h q).card →
      ∀ v : ZMod q, ∃ s : Finset ℕ, s.card ≤ b ∧ ModRep A q s v := by
  classical
  obtain ⟨b, hb⟩ := FiniteModular.uniformModularBound h m hm
  refine ⟨b, ?_⟩
  intro A q inst cover dense
  have selectWitness (v : ZMod q) :
      ∃ s : Finset ℕ, ModRep A q s v ∧ (v ∈ shortMod A h q → s.card ≤ h) := by
    by_cases hv : v ∈ shortMod A h q
    · obtain ⟨s, hs, hrep⟩ := (mem_shortMod A h q v).mp hv
      exact ⟨s, hrep, fun _ => hs⟩
    · obtain ⟨s, hrep⟩ := cover v
      exact ⟨s, hrep, fun hmem => (hv hmem).elim⟩
  let w (v : ZMod q) := (selectWitness v).choose
  have wrep (v : ZMod q) : ModRep A q (w v) v :=
    (selectWitness v).choose_spec.1
  have wshort (v : ZMod q) : v ∈ shortMod A h q → (w v).card ≤ h :=
    (selectWitness v).choose_spec.2
  let U : Finset ℕ := Finset.univ.biUnion w
  have wsub (v : ZMod q) : w v ⊆ U :=
    fun _ hx => Finset.mem_biUnion.mpr ⟨v, Finset.mem_univ _, hx⟩
  have Usub (x : ℕ) (hx : x ∈ U) : x ∈ A := by
    obtain ⟨v, _, hv⟩ := Finset.mem_biUnion.mp hx
    exact (wrep v).1 x hv
  let n := Fintype.card ↥U
  let e : ↥U ≃ Fin n := Fintype.equivFin ↥U
  let value : Fin n ↪ ℕ :=
    ⟨fun i => (e.symm i).val,
     fun _ _ hi => e.symm.injective (Subtype.ext hi)⟩
  let a (i : Fin n) : ZMod q := (value i : ℕ)
  have encode (s : Finset ℕ) (hs : s ⊆ U) :
      ∃ t : Finset (Fin n), t.card = s.card ∧ t.sum a = ((s.sum id : ℕ) : ZMod q) := by
    let f : ↥s ↪ Fin n :=
      ⟨fun x => e ⟨x.val, hs x.property⟩,
       fun _ _ he => Subtype.ext (congrArg (fun x : ↥U => x.val) (e.injective he))⟩
    refine ⟨s.attach.map f, by simp, ?_⟩
    rw [Finset.sum_map, Nat.cast_sum]
    change (∑ x ∈ s.attach, (((e.symm (e ⟨x.val, hs x.property⟩)).val : ℕ) : ZMod q)) =
      ∑ x ∈ s, (x : ZMod q)
    simpa only [Equiv.symm_apply_apply] using
      Finset.sum_attach s (fun x : ℕ => (x : ZMod q))
  have windex (v : ZMod q) :
      ∃ t : Finset (Fin n), t.card = (w v).card ∧ t.sum a = v := by
    obtain ⟨t, ht, hsum⟩ := encode (w v) (wsub v)
    exact ⟨t, ht, hsum.trans (wrep v).2⟩
  have indexedCover (v : ZMod q) : ∃ t : Finset (Fin n), t.sum a = v := by
    obtain ⟨t, _, hsum⟩ := windex v
    exact ⟨t, hsum⟩
  have shortSub : shortMod A h q ⊆ FiniteModular.shortResidues a h := by
    intro v hv
    obtain ⟨t, ht, hsum⟩ := windex v
    exact (FiniteModular.mem_shortResidues a h v).mpr
      ⟨t, ht.le.trans (wshort v hv), hsum⟩
  have indexedDense : q ≤ m * (FiniteModular.shortResidues a h).card :=
    dense.trans (Nat.mul_le_mul_left m (Finset.card_le_card shortSub))
  intro v
  obtain ⟨t, ht, hsum⟩ := hb q n a indexedCover indexedDense v
  refine ⟨t.map value, by simpa only [Finset.card_map] using ht, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hx
    exact Usub _ (e.symm i).property
  · rw [Nat.cast_sum, Finset.sum_map]
    exact hsum
theorem modCover_of_eventually {A : Set ℕ} {t : ℕ}
    (h : ∀ᶠ n in atTop, Rep A t n) (q : ℕ) [NeZero q] (v : ZMod q) :
    ∃ E : Finset ℕ, (∀ x ∈ E, x ∈ A) ∧ E.card ≤ t ∧
      ((E.sum id : ℕ) : ZMod q) = v := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp h
  have hq : 1 ≤ q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hmul : T ≤ T * q := by
    calc
      T = T * 1 := (Nat.mul_one T).symm
      _ ≤ T * q := Nat.mul_le_mul_left T hq
  have hlarge : T ≤ v.val + T * q := by omega
  obtain ⟨E, hEA, hcard, hsum⟩ := hT (v.val + T * q) hlarge
  refine ⟨E, hEA, hcard, ?_⟩
  rw [hsum]
  simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, mul_zero, add_zero,
    ZMod.natCast_zmod_val]
theorem eventually_rep_of_progression {A : Set ℕ} {g : ℕ} [NeZero g]
    (a : ZMod g) (N0 K b : ℕ)
    (cover : ∀ v : ZMod g, ∃ E : Finset ℕ, (∀ x ∈ E, x ∈ A) ∧
      E.card ≤ b ∧ ((E.sum id : ℕ) : ZMod g) = v)
    (progression : ∀ F : Finset ℕ, (∀ x ∈ F, x ∈ A) → F.card ≤ b →
      ∀ n : ℕ, N0 ≤ n → (n : ZMod g) = a → Rep (A \ (F : Set ℕ)) K n) :
    ∀ᶠ n in atTop, Rep A (b + K) n := by
  classical
  let E (v : ZMod g) : Finset ℕ := (cover v).choose
  have hE (v : ZMod g) : (∀ x ∈ E v, x ∈ A) ∧ (E v).card ≤ b ∧
      (((E v).sum id : ℕ) : ZMod g) = v := (cover v).choose_spec
  let M := (Finset.univ : Finset (ZMod g)).sup (fun v => (E v).sum id)
  refine eventually_atTop.mpr ⟨N0 + M, ?_⟩
  intro n hn
  let v : ZMod g := (n : ZMod g) - a
  have hbound : (E v).sum id ≤ M :=
    Finset.le_sup (f := fun r => (E r).sum id) (Finset.mem_univ v)
  have hcost : (E v).sum id ≤ n := by omega
  have hlarge : N0 ≤ n - (E v).sum id := by omega
  have hres : ((n - (E v).sum id : ℕ) : ZMod g) = a := by
    rw [Nat.cast_sub hcost, (hE v).2.2]
    dsimp only [v]
    abel
  obtain ⟨S, hSA, hScard, hSsum⟩ :=
    progression (E v) (hE v).1 (hE v).2.1 _ hlarge hres
  have hd : Disjoint (E v) S := by
    refine Finset.disjoint_left.mpr ?_
    intro x hxE hxS
    exact (hSA x hxS).2 hxE
  refine ⟨E v ∪ S, ?_, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_union.mp hx with he | hs
    · exact (hE v).1 x he
    · exact (hSA x hs).1
  · rw [Finset.card_union_of_disjoint hd]
    exact Nat.add_le_add (hE v).2.1 hScard
  · rw [Finset.sum_union hd, hSsum]
    exact Nat.add_sub_of_le hcost
theorem shortMod_card_bound {A : Set ℕ} {h m : ℕ}
    (hd : DensityBound (restrictedSums A h) m) (q : ℕ) [NeZero q] :
    q ≤ m * (shortMod A h q).card := by
  classical
  have hblocks := block_density_reduction (restrictedSums A h) m hd q
  apply hblocks.trans
  apply Nat.mul_le_mul_left
  apply Finset.card_le_card
  intro v hv
  obtain ⟨n, hn, hnmod⟩ := (Finset.mem_filter.mp hv).2
  obtain ⟨s, hsA, hcard, hsum⟩ := hn
  exact (mem_shortMod A h q v).mpr ⟨s, hcard, hsA, by rw [hsum, hnmod]⟩
private theorem no_order_zero (A : Set ℕ) : ¬ HasOrder A 0 := by
  intro h
  obtain ⟨T, hT⟩ := eventually_atTop.mp h
  obtain ⟨s, _, hs, hsum⟩ := hT (T + 1) (Nat.le_succ _)
  have hz : s = 0 := Multiset.card_eq_zero.mp (Nat.le_zero.mp hs)
  subst s
  simpa using hsum
def BoundedByOrder : Prop :=
  ∃ f : ℕ → ℕ, ∀ (A : Set ℕ) (h : ℕ), HasOrder A h →
    (∃ t, HasRestrictedOrder A t) → HasRestrictedOrder A (f h)
theorem boundedByOrder_of_analyticInputs
    (density : UniformDensityInput) (progressions : UniformProgressionInput) :
    BoundedByOrder := by
  classical
  have perOrder (h : ℕ) : ∃ k : ℕ, ∀ A : Set ℕ, HasOrder A h →
      (∃ t, HasRestrictedOrder A t) → HasRestrictedOrder A k := by
    by_cases hzero : h = 0
    · subst h
      exact ⟨0, fun A hA _ => (no_order_zero A hA).elim⟩
    have hh : 0 < h := Nat.pos_of_ne_zero hzero
    obtain ⟨m, hm, hden⟩ := density h hh
    obtain ⟨b, hmod⟩ := uniformModularForSet h m hm
    obtain ⟨K, hprog⟩ := progressions h m b hh hm
    refine ⟨b + K, ?_⟩
    intro A hA hr
    obtain ⟨t, ht⟩ := hr
    have hd := hden A hA
    obtain ⟨g, hg, a, N₀, hp⟩ := hprog A hd
    letI : NeZero g := ⟨Nat.ne_of_gt hg⟩
    have cover (v : ZMod g) : ∃ s : Finset ℕ, ModRep A g s v := by
      obtain ⟨s, hsA, _, hsum⟩ := modCover_of_eventually ht g v
      exact ⟨s, hsA, hsum⟩
    have shortCover := hmod A g cover (shortMod_card_bound hd g)
    refine eventually_rep_of_progression a N₀ K b ?_ hp
    intro v
    obtain ⟨s, hs, hsA, hsum⟩ := shortCover v
    exact ⟨s, hsA, hs, hsum⟩
  exact ⟨fun h => (perOrder h).choose, fun A h => (perOrder h).choose_spec A⟩
example (density : UniformDensityInput) (progressions : UniformProgressionInput) :
    ∃ f : ℕ → ℕ, ∀ (A : Set ℕ) (h : ℕ),
      (∀ᶠ n in atTop, ∃ s : Multiset ℕ,
        (∀ x ∈ s, x ∈ A) ∧ s.card ≤ h ∧ s.sum = n) →
      (∃ t : ℕ, ∀ᶠ n in atTop, ∃ s : Finset ℕ,
        (∀ x ∈ s, x ∈ A) ∧ s.card ≤ t ∧ (∑ x ∈ s, x) = n) →
      ∀ᶠ n in atTop, ∃ s : Finset ℕ,
        (∀ x ∈ s, x ∈ A) ∧ s.card ≤ f h ∧ (∑ x ∈ s, x) = n :=
  boundedByOrder_of_analyticInputs density progressions
end OMA.E338.Bridge
end

-- module UniformProgression
section
namespace OMA.E338.Bridge
structure ProgressionStage where
  denominator : ℕ
  cost : ℕ
def ProgressionStage.length (s : ProgressionStage) : ℕ :=
  8 * s.denominator ^ 2
def ProgressionStage.multiplicity (s : ProgressionStage) (r b : ℕ) : ℕ :=
  b + s.cost + 2 * r * (s.length - 1) + 1
def progressionStage (h m b : ℕ) : ℕ → ProgressionStage
  | 0 => ⟨2 * m, 0⟩
  | t + 1 =>
    let s := progressionStage h m b t
    let r := h - t
    ⟨s.denominator ^ 2 * (64 * r * s.multiplicity r b),
      s.cost + 2 * r * s.length⟩
noncomputable def progressionAlpha (h m b t : ℕ) : ℝ :=
  1 / ((progressionStage h m b t).denominator : ℝ)
def progressionL (h m b t : ℕ) : ℕ := (progressionStage h m b t).length
def progressionQ (h m b t : ℕ) : ℕ := (progressionStage h m b t).multiplicity (h - t) b
def progressionK (h m b : ℕ) : ℕ := (progressionStage h m b h).cost
theorem progressionCost_eq_sum (h m b t : ℕ) :
    (progressionStage h m b t).cost = ∑ j ∈ Finset.range t, 2 * (h - j) * progressionL h m b j := by
  induction t with
  | zero => simp [progressionStage]
  | succ t ih => rw [Finset.sum_range_succ, ← ih]; rfl
theorem progressionK_eq_sum (h m b : ℕ) :
    progressionK h m b = ∑ t ∈ Finset.range h, 2 * (h - t) * progressionL h m b t :=
  progressionCost_eq_sum h m b h
theorem progressionK_pos (h m b : ℕ) (hh : 0 < h) (hm : 0 < m) :
    0 < progressionK h m b := by
  rw [progressionK_eq_sum]
  have bound := Finset.single_le_sum (f := fun j => 2 * (h - j) * progressionL h m b j)
    (fun j _ => Nat.zero_le _) (Finset.mem_range.mpr hh)
  have hL : 0 < progressionL h m b 0 := by
    change 0 < 8 * (2 * m) ^ 2
    positivity
  exact lt_of_lt_of_le (by simpa only [Nat.sub_zero] using
    (Nat.mul_pos (Nat.mul_pos (by decide : 0 < 2) hh) hL)) bound
theorem progressionQ_eq (h m b t : ℕ) :
    progressionQ h m b t = b + (∑ j ∈ Finset.range t, 2 * (h - j) * progressionL h m b j)
      + 2 * (h - t) * (progressionL h m b t - 1) + 1 := by
  rw [← progressionCost_eq_sum]
  rfl
theorem progressionDenominator_pos (h m b t : ℕ) (hm : 0 < m) (ht : t ≤ h) :
    0 < (progressionStage h m b t).denominator := by
  induction t with
  | zero => change 0 < 2 * m; positivity
  | succ t ih =>
    have hd := ih (by omega)
    have hr : 0 < h - t := by omega
    have hq : 0 < (progressionStage h m b t).multiplicity (h - t) b := Nat.zero_lt_succ _
    change 0 < (progressionStage h m b t).denominator ^ 2 *
      (64 * (h - t) * (progressionStage h m b t).multiplicity (h - t) b)
    positivity
theorem progressionAlpha_zero (h m b : ℕ) :
    progressionAlpha h m b 0 = 1 / (2 * (m : ℝ)) := by
  simp [progressionAlpha, progressionStage]
theorem progression_equation_two (h m b t : ℕ) (hm : 0 < m) (ht : t < h) :
    0 < progressionAlpha h m b t ∧
    progressionL h m b t = ⌈8 / progressionAlpha h m b t ^ 2⌉₊ ∧
    progressionQ h m b t =
      b + (∑ j ∈ Finset.range t, 2 * (h - j) * progressionL h m b j)
        + 2 * (h - t) * (progressionL h m b t - 1) + 1 ∧
    progressionAlpha h m b (t + 1) =
      progressionAlpha h m b t ^ 2 / (64 * ((h - t : ℕ) : ℝ) * progressionQ h m b t) := by
  have hd := progressionDenominator_pos h m b t hm ht.le
  refine ⟨by unfold progressionAlpha; positivity, ?_, progressionQ_eq h m b t, ?_⟩
  · have he : 8 / progressionAlpha h m b t ^ 2 = ((progressionL h m b t : ℕ) : ℝ) := by
      simp [progressionAlpha, progressionL, ProgressionStage.length]
    rw [he, Nat.ceil_natCast]
  · simp [progressionAlpha, progressionStage, progressionQ, div_eq_mul_inv,
      mul_inv_rev, mul_comm, mul_left_comm, mul_assoc]
end OMA.E338.Bridge
namespace OMA.E338.Bridge
open Filter
open scoped Classical
noncomputable def positiveLowerDensity (B : Set ℕ) : ℝ :=
  liminf (fun N : ℕ => (((Finset.Icc 1 N).filter (· ∈ B)).card : ℝ) / N) atTop
theorem half_inv_lt_positiveLowerDensity {B : Set ℕ} {m : ℕ}
    (hm : 0 < m) (hB : DensityBound B m) :
    1 / (2 * (m : ℝ)) < positiveLowerDensity B := by
  classical
  obtain ⟨N₀, hN₀⟩ := hB
  have hm' : 0 < (m : ℝ) := by exact_mod_cast hm
  have hgap : 1 / (2 * (m : ℝ)) < 2 / (3 * (m : ℝ)) := by
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    linarith
  apply hgap.trans_le
  unfold positiveLowerDensity
  refine le_liminf_of_le (f := (atTop : Filter ℕ)) ?_ ?_
  · apply isCoboundedUnder_ge_of_le (atTop : Filter ℕ) (x := (1 : ℝ))
    intro N
    by_cases hN : N = 0
    · simp [hN]
    · have hpos : 0 < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hN
      apply (div_le_iff₀ hpos).2
      rw [one_mul]
      have hcard : ((Finset.Icc 1 N).filter (· ∈ B)).card ≤ N := by
        simpa using (Finset.card_filter_le (Finset.Icc 1 N) (fun x => x ∈ B))
      exact_mod_cast hcard
  · filter_upwards [eventually_ge_atTop N₀, eventually_ge_atTop (3 * m)] with N hN hlarge
    let C := ((Finset.Icc 1 N).filter (· ∈ B)).card
    have hsub : (Finset.range N).filter (· ∈ B) ⊆
        insert 0 ((Finset.Icc 1 N).filter (· ∈ B)) := by
      intro x hx
      obtain ⟨hxN, hxB⟩ := Finset.mem_filter.mp hx
      have hxlt := Finset.mem_range.mp hxN
      by_cases hx : x = 0
      · simp [hx]
      · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr
          ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, hxB⟩)
    have hc : ((Finset.range N).filter (· ∈ B)).card ≤ C + 1 :=
      (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
    have hb := (hN₀ N hN).trans (Nat.mul_le_mul_left m hc)
    rw [Nat.mul_add, Nat.mul_one] at hb
    have hn : 2 * N ≤ (3 * m) * C := by
      rw [Nat.mul_assoc]
      omega
    have hpos : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
    apply (div_le_div_iff₀ (by positivity) hpos).2
    change 2 * (N : ℝ) ≤ (C : ℝ) * (3 * (m : ℝ))
    rw [mul_comm (C : ℝ)]
    exact_mod_cast hn
end OMA.E338.Bridge
namespace OMA.E338.Bridge
theorem progression_many_popular_sums
    (N r Q α L M e D : ℝ) (hN : 0 < N) (hr : 0 < r) (hQ : 0 < Q)
    (hα : 0 < α) (he : 0 ≤ e) (hM : α * N ≤ M) (hMN : M ≤ N)
    (hsmall : e ≤ 2 * (α ^ 2 / (64 * r * Q)) * N)
    (hcounts : M ^ 2 - r * M * e ≤ N * D + 8 * r * (Q - 1) * e * N)
    (hL : 8 / α ^ 2 ≤ L) :
    (3 / 4 : ℝ) * α ^ 2 * N ≤ D ∧ 6 * N ≤ L * D := by
  have hαN : 0 ≤ α * N := (mul_pos hα hN).le
  have hsq := mul_self_le_mul_self hαN hM
  have hden : 0 < 64 * r * Q := by positivity
  have hsmall' : e ≤ (2 * α ^ 2 * N) / (64 * r * Q) := by
    calc
      e ≤ _ := hsmall
      _ = _ := by ring
  have heN := mul_le_mul_of_nonneg_right ((le_div_iff₀ hden).mp hsmall') hN.le
  have hre : 0 ≤ r * e := mul_nonneg hr.le he
  have herr := mul_le_mul_of_nonneg_right hMN hre
  have hD : (3 / 4 : ℝ) * α ^ 2 * N ≤ D := by
    apply (mul_le_mul_iff_left₀ hN).mp
    nlinarith only [hsq, heN, herr, hcounts, mul_nonneg hre hN.le]
  have hα2 : 0 < α ^ 2 := by positivity
  have hscale := (div_le_iff₀ hα2).mp hL
  have hL0 : 0 ≤ L := (by positivity : (0 : ℝ) ≤ 8 / α ^ 2).trans hL
  refine ⟨hD, ?_⟩
  have hprod := mul_le_mul_of_nonneg_left hD hL0
  have hbound := mul_le_mul_of_nonneg_right hscale hN.le
  nlinarith only [hprod, hbound]
end OMA.E338.Bridge
open Filter
namespace OMA.E338.Bridge
theorem progression_of_eventual_periodicity
    {S : Set ℕ} (hinf : S.Infinite) {g : ℕ} {T : Set (ZMod g)}
    (hperiod : ∀ᶠ n : ℕ in atTop, n ∈ S ↔ (n : ZMod g) ∈ T) :
    ∃ a : ZMod g, ∃ N₀ : ℕ, 0 < N₀ ∧
      ∀ n ≥ N₀, (n : ZMod g) = a → n ∈ S := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 hperiod
  obtain ⟨u, hu, hNu⟩ := hinf.exists_gt N
  have hmem : (u : ZMod g) ∈ T := (hN u hNu.le).mp hu
  refine ⟨(u : ZMod g), N + 1, Nat.succ_pos _, ?_⟩
  intro n hn hcong
  exact (hN n (by omega)).mpr (hcong ▸ hmem)
theorem progression_of_finite_differences
    {S : Set ℕ} (hinf : S.Infinite) {g : ℕ} {T : Set (ZMod g)}
    (hextra : (S \ {n : ℕ | (n : ZMod g) ∈ T}).Finite)
    (hmissing : ({n : ℕ | (n : ZMod g) ∈ T} \ S).Finite) :
    ∃ a : ZMod g, ∃ N₀ : ℕ, 0 < N₀ ∧
      ∀ n ≥ N₀, (n : ZMod g) = a → n ∈ S := by
  apply progression_of_eventual_periodicity (T := T) hinf
  rw [← Nat.cofinite_eq_atTop]
  filter_upwards [hextra.eventually_cofinite_notMem, hmissing.eventually_cofinite_notMem]
    with n he hm
  change ¬ (n ∈ S ∧ (n : ZMod g) ∉ T) at he
  change ¬ ((n : ZMod g) ∈ T ∧ n ∉ S) at hm
  tauto
end OMA.E338.Bridge
namespace OMA.E338.Bridge
def richSums (A : Set ℕ) (w q : ℕ) : Set ℕ :=
  {d | d = 0 ∨ ∃ G : Fin q → Finset ℕ,
    (∀ i, (∀ x ∈ G i, x ∈ A) ∧ (G i).card ≤ w ∧ (G i).sum id = d) ∧
      Pairwise (fun i j => Disjoint (G i) (G j))}
private theorem chooseOutside {A : Set ℕ} {w q d : ℕ} (hd : d ∈ richSums A w q)
    (W : Finset ℕ) (hq : W.card < q) :
    ∃ G : Finset ℕ, (∀ x ∈ G, x ∈ A) ∧ G.card ≤ w ∧ G.sum id = d ∧ Disjoint G W := by
  classical
  rcases hd with rfl | ⟨G, hG, hpair⟩
  · exact ⟨∅, by simp, by simp, by simp, by simp⟩
  have hex : ∃ i, Disjoint (G i) W := by
    by_contra! hn
    have hh (i : Fin q) : ∃ x, x ∈ G i ∧ x ∈ W := Finset.not_disjoint_iff.mp (hn i)
    choose x hx hw using hh
    let f (i : Fin q) : ↥W := ⟨x i, hw i⟩
    have hinj : Function.Injective f := by
      intro i j he
      by_contra hne
      have e : x i = x j := congrArg Subtype.val he
      exact (Finset.disjoint_left.mp (hpair hne)) (hx i) (e ▸ hx j)
    have := Fintype.card_le_of_injective f hinj
    simp only [Fintype.card_fin, Fintype.card_coe] at this
    omega
  obtain ⟨i, hi⟩ := hex
  exact ⟨G i, (hG i).1, (hG i).2.1, (hG i).2.2, hi⟩
def addCopies (B C : Set ℕ) : ℕ → Set ℕ
  | 0 => B
  | k + 1 => {n | ∃ x ∈ addCopies B C k, ∃ d ∈ C, x + d = n}
private theorem rep_addCopies {A B : Set ℕ} {F : Finset ℕ} {p w q L : ℕ}
    (base : ∀ x ∈ B, Rep (A \ (F : Set ℕ)) p x)
    (room : F.card + p + w * (L - 1) < q) (k : ℕ) (hk : k ≤ L) :
    ∀ n ∈ addCopies B (richSums A w q) k, Rep (A \ (F : Set ℕ)) (p + w * k) n := by
  classical
  induction k with
  | zero => simpa [addCopies] using base
  | succ k ih =>
    rintro n ⟨x, hx, d, hd, rfl⟩
    obtain ⟨T, hT, ht, hsum⟩ := ih (by omega) x hx
    have hle : w * k ≤ w * (L - 1) := Nat.mul_le_mul_left w (by omega)
    have hroom : (F ∪ T).card < q := by
      have := Finset.card_union_le F T
      omega
    obtain ⟨G, hG, hg, hdsum, hdis⟩ := chooseOutside hd (F ∪ T) hroom
    have hGT : Disjoint G T := Finset.disjoint_left.mpr fun _ hx ht' =>
      Finset.disjoint_left.mp hdis hx (Finset.mem_union_right _ ht')
    refine ⟨T ∪ G, ?_, ?_, ?_⟩
    · intro a ha
      rcases Finset.mem_union.mp ha with hat | hag
      · exact hT a hat
      · exact ⟨hG a hag, fun haf => Finset.disjoint_left.mp hdis hag (Finset.mem_union_left _ haf)⟩
    · rw [Nat.mul_succ]
      have := Finset.card_union_le T G
      omega
    · rw [Finset.sum_union hGT.symm, hsum, hdsum]
def progressionSums (A : Set ℕ) (h m b : ℕ) : ℕ → Set ℕ
  | 0 => {0}
  | t + 1 => addCopies (progressionSums A h m b t)
      (richSums A (2 * (h - t)) (progressionQ h m b t)) (progressionL h m b t)
theorem rep_progressionSums {A : Set ℕ} {h m b : ℕ} (F : Finset ℕ) (hf : F.card ≤ b)
    (t : ℕ) : ∀ n ∈ progressionSums A h m b t,
      Rep (A \ (F : Set ℕ)) (progressionStage h m b t).cost n := by
  induction t with
  | zero =>
    intro n hn
    have he : n = 0 := hn
    exact ⟨∅, by simp, by simp, by simp [he]⟩
  | succ t ih =>
    apply rep_addCopies ih _ _ (le_refl _)
    change F.card + _ + _ < b + (progressionStage h m b t).cost +
      2 * (h - t) * (progressionL h m b t - 1) + 1
    omega
theorem uniformProgressionInput_of_sumset_progression
    (tail : ∀ h m b : ℕ, 0 < h → 0 < m →
      ∀ A : Set ℕ, DensityBound (restrictedSums A h) m →
        ∃ g : ℕ, 0 < g ∧ ∃ a : ZMod g, ∃ N₀ : ℕ,
          ∀ n : ℕ, N₀ ≤ n → (n : ZMod g) = a → n ∈ progressionSums A h m b h) :
    UniformProgressionInput := by
  intro h m b hh hm
  refine ⟨progressionK h m b, ?_⟩
  intro A hA
  obtain ⟨g, hg, a, N₀, hn⟩ := tail h m b hh hm A hA
  exact ⟨g, hg, a, N₀, fun F _ hF n hN ha =>
    rep_progressionSums F hF h n (hn n hN ha)⟩
private theorem subset_addCopies {B B' C : Set ℕ} (sub : B ⊆ B') (k : ℕ) :
    addCopies B C k ⊆ addCopies B' C k := by
  induction k with
  | zero => exact sub
  | succ k ih =>
    rintro n ⟨x, hx, d, hd, rfl⟩
    exact ⟨x, ih hx, d, hd, rfl⟩
private theorem subset_addCopies_of_zero {B C : Set ℕ} (hz : 0 ∈ C) (k : ℕ) :
    B ⊆ addCopies B C k := by
  induction k with
  | zero => exact Set.Subset.rfl
  | succ k ih =>
    intro x hx
    exact ⟨x, ih hx, 0, hz, Nat.add_zero x⟩
open scoped Classical in
noncomputable def infiniteLevelSums (A : Set ℕ) (h m b : ℕ) : ℕ → Set ℕ
  | 0 => {0}
  | t + 1 =>
    let C := richSums A (2 * (h - t)) (progressionQ h m b t)
    let B := infiniteLevelSums A h m b t
    if C.Infinite then addCopies B C (progressionL h m b t) else B
theorem infiniteLevelSums_subset (A : Set ℕ) (h m b t : ℕ) :
    infiniteLevelSums A h m b t ⊆ progressionSums A h m b t := by
  classical
  induction t with
  | zero => exact Set.Subset.rfl
  | succ t ih =>
    simp only [infiniteLevelSums, progressionSums]
    split
    · exact subset_addCopies ih _
    · exact ih.trans (subset_addCopies_of_zero (Or.inl rfl) _)
open scoped Classical in
theorem infinite_rank_of_counts {C : ℕ → Set ℕ} {L : ℕ → ℕ} {h : ℕ}
    (mass : ∀ᶠ N : ℕ in Filter.atTop,
      ∃ t < h, N ≤ L t * ((Finset.Icc 0 (2*N)).filter (· ∈ C t)).card) :
    ∃ t < h, (C t).Infinite := by
  classical
  by_contra! hfin
  let B := ∑ t ∈ Finset.range h, L t * (C t).ncard
  obtain ⟨N₀, hN⟩ := Filter.eventually_atTop.mp mass
  let N := max N₀ (B + 1)
  obtain ⟨t, ht, hcount⟩ := hN N (le_max_left _ _)
  let P := (Finset.Icc 0 (2*N)).filter (· ∈ C t)
  have hsub : (P : Set ℕ) ⊆ C t := fun x hx => (Finset.mem_filter.mp hx).2
  have hc : P.card ≤ (C t).ncard := by
    rw [← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard hsub (hfin t ht)
  have hbound : L t * (C t).ncard ≤ B :=
    Finset.single_le_sum (f := fun j => L j * (C j).ncard)
      (fun j _ => Nat.zero_le _) (Finset.mem_range.mpr ht)
  have hle : N ≤ B := hcount.trans ((Nat.mul_le_mul_left _ hc).trans hbound)
  have := le_max_right N₀ (B + 1)
  omega
private theorem infiniteLevelSums_mono (A : Set ℕ) (h m b t : ℕ) :
    infiniteLevelSums A h m b t ⊆ infiniteLevelSums A h m b (t+1) := by
  classical
  simp only [infiniteLevelSums]
  split
  · exact subset_addCopies_of_zero (Or.inl rfl) _
  · exact Set.Subset.rfl
private theorem zero_mem_infiniteLevelSums (A : Set ℕ) (h m b t : ℕ) :
    0 ∈ infiniteLevelSums A h m b t := by
  induction t with
  | zero => rfl
  | succ t ih => exact infiniteLevelSums_mono A h m b t ih
theorem infiniteLevelSums_infinite {A : Set ℕ} {h m b u : ℕ}
    (hm : 0 < m) (hu : u < h)
    (hi : (richSums A (2 * (h-u)) (progressionQ h m b u)).Infinite) :
    (infiniteLevelSums A h m b h).Infinite := by
  classical
  have hpos : 0 < progressionL h m b u := by
    have := progressionDenominator_pos h m b u hm hu.le
    unfold progressionL ProgressionStage.length
    positivity
  have hone : (infiniteLevelSums A h m b (u+1)).Infinite := by
    simp only [infiniteLevelSums, hi, ↓reduceIte]
    apply hi.mono
    intro d hd
    cases he : progressionL h m b u with
    | zero => omega
    | succ k =>
      exact ⟨0, subset_addCopies_of_zero (Or.inl rfl) k
        (zero_mem_infiniteLevelSums A h m b u), d, hd, Nat.zero_add d⟩
  have hgrow : Monotone (infiniteLevelSums A h m b) :=
    monotone_nat_of_le_succ (infiniteLevelSums_mono A h m b)
  exact hone.mono (hgrow hu)
theorem progressionK_works_of_periodicity (h m b : ℕ) (hm : 0 < m)
    (period : ∀ A : Set ℕ,
      progressionAlpha h m b 0 < positiveLowerDensity (restrictedSums A h) →
      (infiniteLevelSums A h m b h).Infinite ∧
        ∃ g : ℕ, 0 < g ∧ ∃ T : Set (ZMod g),
          ∀ᶠ n : ℕ in Filter.atTop, n ∈ infiniteLevelSums A h m b h ↔ (n : ZMod g) ∈ T) :
    ∀ A : Set ℕ, DensityBound (restrictedSums A h) m →
      ∃ g : ℕ, 0 < g ∧ ∃ a : ZMod g, ∃ N₀ : ℕ, 0 < N₀ ∧
        ∀ F : Finset ℕ, F.card ≤ b → ∀ n : ℕ, N₀ ≤ n → (n : ZMod g) = a →
          Rep (A \ (F : Set ℕ)) (progressionK h m b) n := by
  intro A hd
  have hα := half_inv_lt_positiveLowerDensity hm hd
  rw [← progressionAlpha_zero h m b] at hα
  obtain ⟨hinf, g, hg, T, hperiod⟩ := period A hα
  obtain ⟨a, N₀, hN₀, hn⟩ := progression_of_eventual_periodicity hinf hperiod
  refine ⟨g, hg, a, N₀, hN₀, ?_⟩
  intro F hF n hN hcong
  exact rep_progressionSums F hF h n (infiniteLevelSums_subset A h m b h (hn n hN hcong))
theorem uniformProgressionInput_of_periodicity
    (period : ∀ h m b : ℕ, 0 < h → 0 < m → ∀ A : Set ℕ,
      progressionAlpha h m b 0 < positiveLowerDensity (restrictedSums A h) →
      (infiniteLevelSums A h m b h).Infinite ∧
        ∃ g : ℕ, 0 < g ∧ ∃ T : Set (ZMod g),
          ∀ᶠ n : ℕ in Filter.atTop, n ∈ infiniteLevelSums A h m b h ↔ (n : ZMod g) ∈ T) :
    UniformProgressionInput := by
  intro h m b hh hm
  refine ⟨progressionK h m b, ?_⟩
  intro A hA
  obtain ⟨g, hg, a, N₀, _, hn⟩ :=
    progressionK_works_of_periodicity h m b hm (period h m b hh hm) A hA
  exact ⟨g, hg, a, N₀, fun F _ hF => hn F hF⟩
end OMA.E338.Bridge
end

-- module LemmaThree
section
namespace OMA.E338.Bridge.LemmaThree
open scoped BigOperators Classical
def goodPairs (X : Finset ℕ) (w : ℕ → Finset ℕ) : Finset (ℕ × ℕ) :=
  (X ×ˢ X).filter (fun z => Disjoint (w z.1) (w z.2))
def pairFiber (X : Finset ℕ) (w : ℕ → Finset ℕ) (n : ℕ) : Finset (ℕ × ℕ) :=
  (goodPairs X w).filter (fun z => z.1 + z.2 = n)
def pairCount (X : Finset ℕ) (w : ℕ → Finset ℕ) (n : ℕ) : ℕ :=
  (pairFiber X w n).card
noncomputable def window (A : Set ℕ) (r lo N : ℕ) : Finset ℕ :=
  (Finset.Icc lo N).filter (· ∈ restrictedSums A r)
noncomputable def chosenWitness (A : Set ℕ) (r : ℕ) (x : ℕ) : Finset ℕ :=
  if hx : Rep A r x then hx.choose else ∅
theorem chosenWitness_spec {A : Set ℕ} {r lo N x : ℕ} (hx : x ∈ window A r lo N) :
    (∀ a ∈ chosenWitness A r x, a ∈ A) ∧
    (chosenWitness A r x).card ≤ r ∧ (chosenWitness A r x).sum id = x := by
  have hre : Rep A r x := (Finset.mem_filter.mp hx).2
  simpa only [chosenWitness, dite_eq_left hre] using hre.choose_spec
theorem column_bound (A : Set ℕ) (r N : ℕ) (w : ℕ → Finset ℕ)
    (hw : ∀ x ∈ window A r 1 N,
      (∀ a ∈ w x, a ∈ A) ∧ (w x).card ≤ r ∧ (w x).sum id = x) (a : ℕ) :
    ((window A r 1 N).filter (fun x => a ∈ w x)).card ≤ (window A (r - 1) 0 N).card := by
  classical
  have removed (x : ℕ) (hx : x ∈ window A r 1 N) (ha : a ∈ w x) :
      ((w x).erase a).sum id + a = x :=
    ((w x).sum_erase_add id ha).trans (hw x hx).2.2
  apply Finset.card_le_card_of_injOn (fun x : ℕ => x - a)
  · intro x hx
    obtain ⟨hxX, ha⟩ := Finset.mem_filter.mp hx
    have hxN := (Finset.mem_Icc.mp (Finset.mem_filter.mp hxX).1).2
    have he := removed x hxX ha
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le _, (Nat.sub_le _ _).trans hxN⟩, (w x).erase a, ?_, ?_, ?_⟩
    · intro z hz
      exact (hw x hxX).1 z (Finset.mem_of_mem_erase hz)
    · rw [Finset.card_erase_of_mem ha]
      exact Nat.sub_le_sub_right (hw x hxX).2.1 1
    · change ((w x).erase a).sum id = x - a
      omega
  · intro x hx y hy he
    obtain ⟨hxX, hax⟩ := Finset.mem_filter.mp hx
    obtain ⟨hyX, hay⟩ := Finset.mem_filter.mp hy
    have := removed x hxX hax
    have := removed y hyX hay
    change x - a = y - a at he
    omega
theorem witness_hit_bound (A : Set ℕ) (r N : ℕ) (w : ℕ → Finset ℕ)
    (hw : ∀ x ∈ window A r 1 N,
      (∀ a ∈ w x, a ∈ A) ∧ (w x).card ≤ r ∧ (w x).sum id = x) (W : Finset ℕ) :
    ((window A r 1 N).filter (fun y => ¬ Disjoint (w y) W)).card ≤
      W.card * (window A (r - 1) 0 N).card := by
  classical
  refine (Finset.card_le_card ?_).trans (OMA.E338.FiniteModular.hit_card
    (window A r 1 N) w W _ (fun a _ => column_bound A r N w hw a))
  intro x hx
  obtain ⟨hxX, hhit⟩ := Finset.mem_filter.mp hx
  obtain ⟨a, hax, haW⟩ := Finset.not_disjoint_iff.mp hhit
  exact Finset.mem_biUnion.mpr ⟨a, haW, Finset.mem_filter.mpr ⟨hxX, hax⟩⟩
theorem mass_and_fiber (X : Finset ℕ) (w : ℕ → Finset ℕ) (r e N : ℕ)
    (hsize : ∀ x ∈ X, (w x).card ≤ r) (hN : ∀ x ∈ X, x ≤ N)
    (hhit : ∀ W : Finset ℕ,
      (X.filter (fun y => ¬ Disjoint (w y) W)).card ≤ W.card * e) :
    X.card ^ 2 ≤ (∑ n ∈ Finset.range (2 * N + 1), pairCount X w n) + r * X.card * e ∧
      ∀ n, pairCount X w n ≤ X.card := by
  classical
  let row (x : ℕ) := X.filter (fun y => Disjoint (w y) (w x))
  have rows (x : ℕ) (hx : x ∈ X) : X.card ≤ (row x).card + r * e := by
    have hpart := Finset.card_filter_add_card_filter_not (s := X)
      (fun y => Disjoint (w y) (w x))
    have hbad := (hhit (w x)).trans (Nat.mul_le_mul_right e (hsize x hx))
    change X.card ≤ (X.filter (fun y => Disjoint (w y) (w x))).card + r * e
    omega
  have hmem (z : ℕ × ℕ) : z ∈ goodPairs X w ↔ z.1 ∈ X ∧ z.2 ∈ row z.1 := by
    simp only [goodPairs, row, Finset.mem_filter, Finset.mem_product, and_assoc]
    rw [disjoint_comm (a := w z.1)]
  have byRow : (goodPairs X w).card = ∑ x ∈ X, (row x).card := by
    simpa using (Finset.sum_finset_product (goodPairs X w) X row hmem
      (f := fun _ => (1 : ℕ)))
  have bySum : (goodPairs X w).card = ∑ n ∈ Finset.range (2 * N + 1), pairCount X w n := by
    apply Finset.card_eq_sum_card_fiberwise (f := fun z : ℕ × ℕ => z.1 + z.2)
    intro z hz
    have hz' := (hmem z).mp hz
    have hx := hN z.1 hz'.1
    have hy := hN z.2 (Finset.mem_filter.mp hz'.2).1
    apply Finset.mem_range.mpr
    change z.1 + z.2 < 2 * N + 1
    omega
  constructor
  · calc
      X.card ^ 2 = ∑ _x ∈ X, X.card := by simp [pow_two]
      _ ≤ ∑ x ∈ X, ((row x).card + r * e) := Finset.sum_le_sum rows
      _ = _ := by rw [Finset.sum_add_distrib, ← byRow, bySum]; simp [mul_comm, mul_left_comm]
  · intro n
    apply Finset.card_le_card_of_injOn (s := pairFiber X w n) (t := X) Prod.fst
    · intro z hz
      exact ((hmem z).mp (Finset.mem_filter.mp hz).1).1
    · intro a ha b hb he
      have ha' : a.1 + a.2 = n := (Finset.mem_filter.mp ha).2
      have hb' : b.1 + b.2 = n := (Finset.mem_filter.mp hb).2
      exact Prod.ext he (by change a.1 = b.1 at he; omega)
theorem fiber_hit_bound (X : Finset ℕ) (w : ℕ → Finset ℕ) (e n : ℕ)
    (hhit : ∀ W : Finset ℕ, (X.filter (fun y => ¬ Disjoint (w y) W)).card ≤ W.card * e)
    (W : Finset ℕ) :
    ((pairFiber X w n).filter (fun z => ¬ Disjoint (w z.1 ∪ w z.2) W)).card ≤
      2 * W.card * e := by
  classical
  let P := pairFiber X w n
  let H := X.filter (fun y => ¬ Disjoint (w y) W)
  have facts (z : ℕ × ℕ) (hz : z ∈ P) : z.1 ∈ X ∧ z.2 ∈ X ∧ z.1 + z.2 = n := by
    have h := Finset.mem_filter.mp hz
    have hm := Finset.mem_product.mp (Finset.mem_filter.mp h.1).1
    exact ⟨hm.1, hm.2, h.2⟩
  have project (f : ℕ × ℕ → ℕ) (inj : Set.InjOn f (P : Set (ℕ × ℕ)))
      (hX : ∀ z ∈ P, f z ∈ X) :
      (P.filter (fun z => ¬ Disjoint (w (f z)) W)).card ≤ H.card := by
    apply Finset.card_le_card_of_injOn f
    · intro z hz
      obtain ⟨hzP, hw⟩ := Finset.mem_filter.mp hz
      exact Finset.mem_filter.mpr ⟨hX z hzP, hw⟩
    · intro z hz z' hz' he
      exact inj (Finset.mem_filter.mp hz).1 (Finset.mem_filter.mp hz').1 he
  let L := P.filter (fun z => ¬ Disjoint (w z.1) W)
  let R := P.filter (fun z => ¬ Disjoint (w z.2) W)
  have hl : L.card ≤ H.card := by
    apply project Prod.fst _ (fun z hz => (facts z hz).1)
    intro z hz y hy he
    have h₁ := (facts z hz).2.2
    have h₂ := (facts y hy).2.2
    exact Prod.ext he (by omega)
  have hr : R.card ≤ H.card := by
    apply project Prod.snd _ (fun z hz => (facts z hz).2.1)
    intro z hz y hy he
    have h₁ := (facts z hz).2.2
    have h₂ := (facts y hy).2.2
    exact Prod.ext (by omega) he
  have hsub : P.filter (fun z => ¬ Disjoint (w z.1 ∪ w z.2) W) ⊆ L ∪ R := by
    intro z hz
    obtain ⟨hp, hw⟩ := Finset.mem_filter.mp hz
    by_cases hd : Disjoint (w z.1) W
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr
        ⟨hp, fun he => hw (Finset.disjoint_union_left.mpr ⟨hd, he⟩)⟩)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hp, hd⟩)
  calc
    _ ≤ (L ∪ R).card := Finset.card_le_card hsub
    _ ≤ L.card + R.card := Finset.card_union_le _ _
    _ ≤ W.card * e + W.card * e := Nat.add_le_add (hl.trans (hhit W)) (hr.trans (hhit W))
    _ = 2 * W.card * e := by ring
theorem pack_pairs (P : Finset (ℕ × ℕ)) (U : ℕ × ℕ → Finset ℕ) (r e Q : ℕ)
    (hsize : ∀ z ∈ P, (U z).card ≤ 2 * r)
    (hhit : ∀ W : Finset ℕ, (P.filter (fun z => ¬ Disjoint (U z) W)).card ≤ 2 * W.card * e)
    (hcount : 4 * r * (Q - 1) * e < P.card) :
    ∃ f : Fin Q → ℕ × ℕ, (∀ i, f i ∈ P) ∧ Pairwise (fun i j => Disjoint (U (f i)) (U (f j))) := by
  classical
  suffices aux : ∀ k ≤ Q, ∃ f : Fin k → ℕ × ℕ, (∀ i, f i ∈ P) ∧
      Pairwise (fun i j => Disjoint (U (f i)) (U (f j))) from aux Q le_rfl
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨Fin.elim0, fun i => i.elim0, by intro i; exact i.elim0⟩
  | succ k ih =>
    intro hk
    obtain ⟨f, hf, hdis⟩ := ih (by omega)
    let W := Finset.univ.biUnion (fun i => U (f i))
    have hW : W.card ≤ k * (2 * r) := by
      simpa only [Finset.card_univ, Fintype.card_fin] using
        Finset.card_biUnion_le_card_mul Finset.univ (fun i => U (f i)) (2 * r)
          (fun i _ => hsize _ (hf i))
    have hroom : 2 * W.card * e ≤ 4 * r * (Q - 1) * e := calc
      2 * W.card * e ≤ 2 * (k * (2 * r)) * e := by gcongr
      _ = 4 * r * k * e := by ring
      _ ≤ 4 * r * (Q - 1) * e := by gcongr; omega
    obtain ⟨z, hz, hout⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (lt_of_le_of_lt ((hhit W).trans hroom) hcount)
    have hzW : Disjoint (U z) W := by
      by_contra hn
      exact hout (Finset.mem_filter.mpr ⟨hz, hn⟩)
    have hzdis (i : Fin k) : Disjoint (U z) (U (f i)) :=
      hzW.mono_right (fun x hx => Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hx⟩)
    refine ⟨Fin.cons z f, ?_, ?_⟩
    · exact Fin.forall_fin_succ.mpr ⟨by simpa using hz, by simpa using hf⟩
    · rw [pairwise_fin_succ_iff]
      simpa only [Fin.cons_succ, Fin.cons_zero] using
        (show (∀ i, Disjoint (U (f i)) (U z)) ∧ (∀ i, Disjoint (U z) (U (f i))) ∧
          Pairwise (fun i j => Disjoint (U (f i)) (U (f j))) from
          ⟨fun i => (hzdis i).symm, hzdis, hdis⟩)
theorem mem_richSums_iff_nonempty {A : Set ℕ} {s q n : ℕ} (hn : 0 < n) :
    n ∈ richSums A s q ↔ ∃ G : Fin q → Finset ℕ,
      (∀ i, (G i).Nonempty ∧ (∀ a ∈ G i, a ∈ A) ∧ (G i).card ≤ s ∧ (G i).sum id = n) ∧
      Pairwise (fun i j => Disjoint (G i) (G j)) := by
  constructor
  · rintro (he | ⟨G, hw, hp⟩)
    · omega
    · refine ⟨G, fun i => ⟨?_, hw i⟩, hp⟩
      apply Finset.nonempty_iff_ne_empty.mpr
      intro he
      have hsum := (hw i).2.2
      rw [he, Finset.sum_empty] at hsum
      omega
  · rintro ⟨G, hG, hp⟩
    exact Or.inr ⟨G, fun i => (hG i).2, hp⟩
def Estimates (A : Set ℕ) (r N : ℕ) (w : ℕ → Finset ℕ) : Prop :=
  let X := window A r 1 N
  let M := X.card
  let e := (window A (r - 1) 0 N).card
  let p := pairCount X w
  M ^ 2 ≤ (∑ n ∈ Finset.range (2 * N + 1), p n) + r * M * e ∧
    (∀ n, p n ≤ M) ∧
    ∀ Q n, 4 * r * (Q - 1) * e < p n → 0 < n ∧ n ∈ richSums A (2 * r) Q
theorem lemma_three (A : Set ℕ) (r N : ℕ) (w : ℕ → Finset ℕ)
    (hw : ∀ x ∈ window A r 1 N,
      (∀ a ∈ w x, a ∈ A) ∧ (w x).card ≤ r ∧ (w x).sum id = x) :
    Estimates A r N w := by
  classical
  let X := window A r 1 N
  let e := (window A (r - 1) 0 N).card
  have hxI {x : ℕ} (hx : x ∈ X) : 1 ≤ x ∧ x ≤ N :=
    Finset.mem_Icc.mp (Finset.mem_filter.mp hx).1
  have hhit := witness_hit_bound A r N w hw
  obtain ⟨hmass, hcap⟩ := mass_and_fiber X w r e N
    (fun x hx => (hw x hx).2.1) (fun _ hx => (hxI hx).2) hhit
  refine ⟨hmass, hcap, ?_⟩
  intro Q n hpop
  let P := pairFiber X w n
  let U (z : ℕ × ℕ) := w z.1 ∪ w z.2
  have facts {z : ℕ × ℕ} (hz : z ∈ P) :
      z.1 ∈ X ∧ z.2 ∈ X ∧ Disjoint (w z.1) (w z.2) ∧ z.1 + z.2 = n := by
    obtain ⟨hgood, hsum⟩ := Finset.mem_filter.mp hz
    obtain ⟨hprod, hd⟩ := Finset.mem_filter.mp hgood
    exact ⟨(Finset.mem_product.mp hprod).1, (Finset.mem_product.mp hprod).2, hd, hsum⟩
  have sizes : ∀ z ∈ P, (U z).card ≤ 2 * r := by
    intro z hz
    obtain ⟨hx, hy, _, _⟩ := facts hz
    have hcards := Nat.add_le_add (hw _ hx).2.1 (hw _ hy).2.1
    exact (Finset.card_union_le _ _).trans (by simpa only [two_mul] using hcards)
  have hP : 4 * r * (Q - 1) * e < P.card := hpop
  obtain ⟨z, hz⟩ := Finset.card_pos.mp (Nat.zero_lt_of_lt hP)
  obtain ⟨hx, _, _, hzn⟩ := facts hz
  have xpos := (hxI hx).1
  have hn : 0 < n := by omega
  obtain ⟨f, hf, hdis⟩ := pack_pairs P U r e Q sizes (fiber_hit_bound X w e n hhit) hP
  refine ⟨hn, Or.inr ⟨fun i => U (f i), ?_, hdis⟩⟩
  intro i
  obtain ⟨hx, hy, hd, hsum⟩ := facts (hf i)
  refine ⟨?_, sizes _ (hf i), ?_⟩
  · intro a ha
    rcases Finset.mem_union.mp ha with h | h
    · exact (hw _ hx).1 a h
    · exact (hw _ hy).1 a h
  · change (w (f i).1 ∪ w (f i).2).sum id = n
    rw [Finset.sum_union hd, (hw _ hx).2.2, (hw _ hy).2.2, hsum]
theorem lemma_three_chosen (A : Set ℕ) (r N : ℕ) :
    Estimates A r N (chosenWitness A r) :=
  lemma_three A r N (chosenWitness A r) (fun _ hx => chosenWitness_spec hx)
theorem popular_disjoint_representations (A : Set ℕ) (r N Q n : ℕ) (w : ℕ → Finset ℕ)
    (hw : ∀ x ∈ window A r 1 N,
      (∀ a ∈ w x, a ∈ A) ∧ (w x).card ≤ r ∧ (w x).sum id = x)
    (hpop : 4 * r * (Q - 1) * (window A (r - 1) 0 N).card < pairCount (window A r 1 N) w n) :
    ∃ G : Fin Q → Finset ℕ,
      (∀ i, (G i).Nonempty ∧ (∀ a ∈ G i, a ∈ A) ∧ (G i).card ≤ 2 * r ∧ (G i).sum id = n) ∧
      Pairwise (fun i j => Disjoint (G i) (G j)) := by
  obtain ⟨hn, hrich⟩ := (lemma_three A r N w hw).2.2 Q n hpop
  exact (mem_richSums_iff_nonempty hn).mp hrich
end OMA.E338.Bridge.LemmaThree
end

-- module WeightedCount
section
namespace OMA.E338.Bridge
open Filter LemmaThree
open scoped BigOperators Classical
theorem pair_count_bound (A : Set ℕ) (r Q N : ℕ) :
    let M := (window A r 1 N).card
    let e := (window A (r-1) 0 N).card
    let D := ((Finset.Icc 0 (2*N)).filter (· ∈ richSums A (2*r) Q)).card
    M^2 ≤ N*D + 8*r*(Q-1)*e*N + r*M*e := by
  classical
  let X := window A r 1 N
  let M := X.card
  let e := (window A (r-1) 0 N).card
  let p := pairCount X (chosenWitness A r)
  let C := richSums A (2*r) Q
  let S := Finset.range (2*N+1)
  let D := (S.filter (· ∈ C)).card
  let T := 4*r*(Q-1)*e
  have hMd : M ≤ N := by
    simpa [M, X, window] using
      Finset.card_filter_le (Finset.Icc 1 N) (· ∈ restrictedSums A r)
  obtain ⟨mass, pointwise, rich⟩ := lemma_three_chosen A r N
  have hzero : 0 ∈ C := Or.inl rfl
  have hcomp : (S.filter (· ∉ C)).card ≤ 2*N := by
    have hs : S.filter (· ∉ C) ⊆ Finset.Icc 1 (2*N) := by
      intro n hn
      obtain ⟨hnS, hnC⟩ := Finset.mem_filter.mp hn
      have hn' := Finset.mem_range.mp hnS
      have : n ≠ 0 := fun he => hnC (he ▸ hzero)
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    simpa using Finset.card_le_card hs
  have richpart : (∑ n ∈ S.filter (· ∈ C), p n) ≤ D * N := by
    calc
      _ ≤ ∑ _n ∈ S.filter (· ∈ C), N :=
        Finset.sum_le_sum fun n _ => (pointwise n).trans hMd
      _ = _ := by simp [D]
  have poorpart : (∑ n ∈ S.filter (· ∉ C), p n) ≤ 2*N*T := by
    calc
      _ ≤ ∑ _n ∈ S.filter (· ∉ C), T := by
        apply Finset.sum_le_sum
        intro n hn
        by_contra! hp
        exact (Finset.mem_filter.mp hn).2 ((rich Q n hp).2)
      _ = (S.filter (· ∉ C)).card*T := by simp
      _ ≤ _ := Nat.mul_le_mul_right _ hcomp
  have hpSum : (∑ n ∈ S, p n) ≤ N*D + 8*r*(Q-1)*e*N := by
    rw [← Finset.sum_filter_add_sum_filter_not S (· ∈ C) p]
    calc
      _ ≤ D*N + 2*N*T := Nat.add_le_add richpart poorpart
      _ = _ := by unfold T; ring
  have hfinal : M^2 ≤ N*D + 8*r*(Q-1)*e*N + r*M*e :=
    mass.trans (Nat.add_le_add_right hpSum _)
  simpa only [D, S, Nat.range_succ_eq_Icc_zero] using hfinal
private theorem count_zero_window_le (A : Set ℕ) (r N : ℕ) :
    (window A r 0 N).card ≤ (window A r 1 N).card + 1 := by
  classical
  have hs : window A r 0 N ⊆ insert 0 (window A r 1 N) := by
    intro n hn
    obtain ⟨hI, hx⟩ := Finset.mem_filter.mp hn
    by_cases hz : n = 0
    · simp [hz]
    · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨by omega, (Finset.mem_Icc.mp hI).2⟩, hx⟩)
  exact (Finset.card_le_card hs).trans (Finset.card_insert_le _ _)
private theorem zero_rank_card (A : Set ℕ) (N : ℕ) :
    (window A 0 1 N).card = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro n hn
  obtain ⟨hI, hw⟩ := Finset.mem_filter.mp hn
  obtain ⟨w, _, hs, he⟩ := hw
  have : w = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hs)
  simp [this] at he
  have := (Finset.mem_Icc.mp hI).1
  omega
private theorem exists_rank_transition (P : ℕ → Prop) (h : ℕ) (first : P 0) (last : ¬ P h) :
    ∃ t < h, P t ∧ ¬ P (t+1) := by
  classical
  induction h with
  | zero => exact (last first).elim
  | succ h ih =>
    by_cases hP : P h
    · exact ⟨h, Nat.lt_succ_self h, hP, last⟩
    · obtain ⟨t, ht, hgood, hnext⟩ := ih hP
      exact ⟨t, ht.trans (Nat.lt_succ_self h), hgood, hnext⟩
theorem eventually_rank_transition (A : Set ℕ) (h m b : ℕ) (hm : 0 < m)
    (hd : progressionAlpha h m b 0 < positiveLowerDensity (restrictedSums A h)) :
    ∀ᶠ N : ℕ in atTop, ∃ t < h,
      progressionAlpha h m b t * N ≤ ((window A (h-t) 1 N).card : ℝ) ∧
      ((window A (h-t-1) 0 N).card : ℝ) ≤ 2 * progressionAlpha h m b (t+1) * N := by
  classical
  let den (t : ℕ) := (progressionStage h m b t).denominator
  let K := ∑ t ∈ Finset.range (h+1), den t
  have hevent : ∀ᶠ N : ℕ in atTop,
      progressionAlpha h m b 0 < ((window A h 1 N).card : ℝ) / N := by
    exact eventually_lt_of_lt_liminf hd (isBoundedUnder_of ⟨0, fun n => by positivity⟩)
  filter_upwards [hevent, eventually_ge_atTop K, eventually_gt_atTop 0] with N hfirst hN hpos
  have hlarge (t : ℕ) (ht : t ≤ h) : 1 ≤ progressionAlpha h m b t * (N : ℝ) := by
    have hden : den t ≤ N :=
      (Finset.single_le_sum (f := den) (fun i _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega : t < h+1))).trans hN
    have hdpos : 0 < (den t : ℝ) := by exact_mod_cast progressionDenominator_pos h m b t hm ht
    have hden' : (den t : ℝ) ≤ N := by exact_mod_cast hden
    change 1 ≤ 1 / (den t : ℝ) * N
    rwa [one_div, inv_mul_eq_div, le_div_iff₀ hdpos, one_mul]
  let P (t : ℕ) := progressionAlpha h m b t * N ≤ ((window A (h-t) 1 N).card : ℝ)
  have first : P 0 := by
    have hNpos : 0 < (N : ℝ) := by exact_mod_cast hpos
    simpa [P] using ((lt_div_iff₀ hNpos).mp hfirst).le
  have last : ¬ P h := by
    intro ph
    have hzero : (window A (h-h) 1 N).card = 0 := by simp [zero_rank_card]
    change progressionAlpha h m b h * (N : ℝ) ≤ _ at ph
    rw [hzero, Nat.cast_zero] at ph
    linarith [hlarge h le_rfl]
  obtain ⟨t, ht, htgood, htbad⟩ := exists_rank_transition P h first last
  refine ⟨t, ht, htgood, ?_⟩
  have hprev : h-(t+1) = h-t-1 := by omega
  change ¬ progressionAlpha h m b (t+1) * N ≤ ((window A (h-(t+1)) 1 N).card : ℝ) at htbad
  rw [hprev, not_le] at htbad
  have hc : ((window A (h-t-1) 0 N).card : ℝ) ≤ ((window A (h-t-1) 1 N).card : ℝ) + 1 := by
    exact_mod_cast count_zero_window_le A (h-t-1) N
  linarith [hlarge (t+1) (by omega)]
theorem weighted_rank_at (A : Set ℕ) (h m b t N : ℕ) (hm : 0 < m) (ht : t < h) (hN : 0 < N)
    (hM : progressionAlpha h m b t * N ≤ ((window A (h-t) 1 N).card : ℝ))
    (he : ((window A (h-t-1) 0 N).card : ℝ) ≤ 2 * progressionAlpha h m b (t+1) * N) :
    6 * N ≤ progressionL h m b t *
      ((Finset.Icc 0 (2*N)).filter (· ∈ richSums A (2*(h-t)) (progressionQ h m b t))).card := by
  classical
  let r := h-t
  let Q := progressionQ h m b t
  let L := progressionL h m b t
  let α := progressionAlpha h m b t
  let M := (window A r 1 N).card
  let e := (window A (r-1) 0 N).card
  let D := ((Finset.Icc 0 (2*N)).filter (· ∈ richSums A (2*r) Q)).card
  have hQ : 0 < Q := Nat.zero_lt_succ _
  have hr : 0 < r := Nat.sub_pos_of_lt ht
  have hcap : M ≤ N := by
    simpa [M, window] using Finset.card_filter_le (Finset.Icc 1 N) (· ∈ restrictedSums A r)
  have hb : M^2 ≤ N*D + 8*r*(Q-1)*e*N + r*M*e := pair_count_bound A r Q N
  have hb' : (M : ℝ)^2 ≤ (N : ℝ)*D + 8*(r : ℝ)*((Q-1 : ℕ) : ℝ)*e*N + (r : ℝ)*M*e := by
    exact_mod_cast hb
  rw [Nat.cast_sub (by omega : 1 ≤ Q), Nat.cast_one] at hb'
  obtain ⟨hα, hL, _, hnext⟩ := progression_equation_two h m b t hm ht
  rw [hnext] at he
  have hceil : 8 / α^2 ≤ (L : ℝ) := by
    change 8 / progressionAlpha h m b t ^ 2 ≤ (progressionL h m b t : ℝ)
    rw [hL]; exact Nat.le_ceil _
  have hcount : (M : ℝ)^2 - (r : ℝ)*M*e ≤ (N : ℝ)*D + 8*(r : ℝ)*((Q : ℝ)-1)*e*N := by
    linarith only [hb']
  have result := (progression_many_popular_sums N r Q α L M e D
    (by exact_mod_cast hN) (by exact_mod_cast hr) (by exact_mod_cast hQ) hα (by positivity)
    hM (by exact_mod_cast hcap) he hcount hceil).2
  exact_mod_cast result
theorem eventually_weighted_rank (A : Set ℕ) (h m b : ℕ) (_hh : 0 < h) (hm : 0 < m)
    (hd : progressionAlpha h m b 0 < positiveLowerDensity (restrictedSums A h)) :
    ∀ᶠ N : ℕ in atTop, ∃ t < h, 6*N ≤ progressionL h m b t *
      ((Finset.Icc 0 (2*N)).filter (· ∈ richSums A (2*(h-t)) (progressionQ h m b t))).card := by
  filter_upwards [eventually_rank_transition A h m b hm hd, eventually_gt_atTop 0] with N hgood hN
  obtain ⟨t, ht, hM, he⟩ := hgood
  exact ⟨t, ht, weighted_rank_at A h m b t N hm ht hN hM he⟩
end OMA.E338.Bridge
end

-- module PaddedProgression
section
namespace OMA.E338.Bridge
open Filter LemmaThree
open scoped BigOperators Classical
def paddedMultiplicity (allow : ℕ → ℕ) (s : ProgressionStage) (r b : ℕ) : ℕ :=
  b + s.cost + 2 * r * (allow s.length - 1) + 1
def paddedStage (allow : ℕ → ℕ) (h m b : ℕ) : ℕ → ProgressionStage
  | 0 => ⟨2*m, 0⟩
  | t+1 =>
    let s := paddedStage allow h m b t
    let r := h-t
    ⟨s.denominator ^ 2 * (64*r*paddedMultiplicity allow s r b),
     s.cost + 2*r*allow s.length⟩
noncomputable def paddedAlpha (allow : ℕ → ℕ) (h m b t : ℕ) : ℝ :=
  1 / ((paddedStage allow h m b t).denominator : ℝ)
def paddedL (allow : ℕ → ℕ) (h m b t : ℕ) : ℕ := (paddedStage allow h m b t).length
def paddedB (allow : ℕ → ℕ) (h m b t : ℕ) : ℕ := allow (paddedL allow h m b t)
def paddedQ (allow : ℕ → ℕ) (h m b t : ℕ) : ℕ :=
  paddedMultiplicity allow (paddedStage allow h m b t) (h-t) b
def paddedK (allow : ℕ → ℕ) (h m b : ℕ) : ℕ := (paddedStage allow h m b h).cost
theorem paddedDenominator_pos (allow : ℕ → ℕ) (h m b t : ℕ) (hm : 0 < m) (ht : t ≤ h) :
    0 < (paddedStage allow h m b t).denominator := by
  induction t with
  | zero => change 0 < 2*m; positivity
  | succ t ih =>
    have hd := ih (by omega)
    have hr : 0 < h-t := by omega
    have hq : 0 < paddedMultiplicity allow (paddedStage allow h m b t) (h-t) b := Nat.zero_lt_succ _
    change 0 < (paddedStage allow h m b t).denominator ^ 2 *
      (64 * (h-t) * paddedMultiplicity allow (paddedStage allow h m b t) (h-t) b)
    positivity
theorem paddedL_pos (allow : ℕ → ℕ) (h m b t : ℕ) (hm : 0 < m) (ht : t ≤ h) :
    0 < paddedL allow h m b t := by
  have := paddedDenominator_pos allow h m b t hm ht
  unfold paddedL ProgressionStage.length
  positivity
theorem padded_equation (allow : ℕ → ℕ) (h m b t : ℕ) (hm : 0 < m) (ht : t < h) :
    0 < paddedAlpha allow h m b t ∧
    paddedL allow h m b t = ⌈8 / paddedAlpha allow h m b t ^ 2⌉₊ ∧
    paddedAlpha allow h m b (t+1) =
      paddedAlpha allow h m b t ^ 2 / (64 * ((h-t : ℕ) : ℝ) * paddedQ allow h m b t) := by
  have hd := paddedDenominator_pos allow h m b t hm ht.le
  refine ⟨by unfold paddedAlpha; positivity, ?_, ?_⟩
  · have he : 8 / paddedAlpha allow h m b t ^ 2 = ((paddedL allow h m b t : ℕ) : ℝ) := by
      simp [paddedAlpha, paddedL, ProgressionStage.length]
    rw [he, Nat.ceil_natCast]
  · simp [paddedAlpha, paddedStage, paddedQ, div_eq_mul_inv, mul_inv_rev,
      mul_comm, mul_left_comm, mul_assoc]
private theorem padded_zero_window_le (A : Set ℕ) (r N : ℕ) :
    (window A r 0 N).card ≤ (window A r 1 N).card + 1 := by
  classical
  have hs : window A r 0 N ⊆ insert 0 (window A r 1 N) := by
    intro n hn
    obtain ⟨hI, hx⟩ := Finset.mem_filter.mp hn
    by_cases hz : n = 0
    · simp [hz]
    · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨by omega, (Finset.mem_Icc.mp hI).2⟩, hx⟩)
  exact (Finset.card_le_card hs).trans (Finset.card_insert_le _ _)
private theorem padded_zero_rank_card (A : Set ℕ) (N : ℕ) :
    (window A 0 1 N).card = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro n hn
  obtain ⟨hI, hw⟩ := Finset.mem_filter.mp hn
  obtain ⟨w, _, hs, he⟩ := hw
  have : w = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hs)
  simp [this] at he
  have := (Finset.mem_Icc.mp hI).1
  omega
private theorem padded_exists_rank_transition (P : ℕ → Prop) (h : ℕ) (first : P 0) (last : ¬ P h) :
    ∃ t < h, P t ∧ ¬ P (t+1) := by
  classical
  induction h with
  | zero => exact (last first).elim
  | succ h ih =>
    by_cases hP : P h
    · exact ⟨h, Nat.lt_succ_self h, hP, last⟩
    · obtain ⟨t, ht, hgood, hnext⟩ := ih hP
      exact ⟨t, ht.trans (Nat.lt_succ_self h), hgood, hnext⟩
theorem eventually_padded_transition (allow : ℕ → ℕ) (A : Set ℕ) (h m b : ℕ) (hm : 0 < m)
    (hd : progressionAlpha h m b 0 < positiveLowerDensity (restrictedSums A h)) :
    ∀ᶠ N : ℕ in atTop, ∃ t < h,
      paddedAlpha allow h m b t * N ≤ ((window A (h-t) 1 N).card : ℝ) ∧
      ((window A (h-t-1) 0 N).card : ℝ) ≤ 2 * paddedAlpha allow h m b (t+1) * N := by
  classical
  let den (t : ℕ) := (paddedStage allow h m b t).denominator
  let K := ∑ t ∈ Finset.range (h+1), den t
  have hevent : ∀ᶠ N : ℕ in atTop,
      progressionAlpha h m b 0 < ((window A h 1 N).card : ℝ) / N := by
    exact eventually_lt_of_lt_liminf hd (isBoundedUnder_of ⟨0, fun n => by positivity⟩)
  filter_upwards [hevent, eventually_ge_atTop K, eventually_gt_atTop 0] with N hfirst hN hpos
  have hlarge (t : ℕ) (ht : t ≤ h) : 1 ≤ paddedAlpha allow h m b t * (N : ℝ) := by
    have hden : den t ≤ N :=
      (Finset.single_le_sum (f := den) (fun i _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega : t < h+1))).trans hN
    have hdpos : 0 < (den t : ℝ) := by exact_mod_cast paddedDenominator_pos allow h m b t hm ht
    have hden' : (den t : ℝ) ≤ N := by exact_mod_cast hden
    change 1 ≤ 1 / (den t : ℝ) * N
    rwa [one_div, inv_mul_eq_div, le_div_iff₀ hdpos, one_mul]
  let P (t : ℕ) := paddedAlpha allow h m b t * N ≤ ((window A (h-t) 1 N).card : ℝ)
  have first : P 0 := by
    have hNpos : 0 < (N : ℝ) := by exact_mod_cast hpos
    simpa [P, paddedAlpha, paddedStage, progressionAlpha, progressionStage] using ((lt_div_iff₀ hNpos).mp hfirst).le
  have last : ¬ P h := by
    intro ph
    have hzero : (window A (h-h) 1 N).card = 0 := by simp [padded_zero_rank_card]
    change paddedAlpha allow h m b h * (N : ℝ) ≤ _ at ph
    rw [hzero, Nat.cast_zero] at ph
    linarith [hlarge h le_rfl]
  obtain ⟨t, ht, htgood, htbad⟩ := padded_exists_rank_transition P h first last
  refine ⟨t, ht, htgood, ?_⟩
  have hprev : h-(t+1) = h-t-1 := by omega
  change ¬ paddedAlpha allow h m b (t+1) * N ≤ ((window A (h-(t+1)) 1 N).card : ℝ) at htbad
  rw [hprev, not_le] at htbad
  have hc : ((window A (h-t-1) 0 N).card : ℝ) ≤ ((window A (h-t-1) 1 N).card : ℝ) + 1 := by
    exact_mod_cast padded_zero_window_le A (h-t-1) N
  linarith [hlarge (t+1) (by omega)]
theorem padded_rank_at (allow : ℕ → ℕ) (A : Set ℕ) (h m b t N : ℕ) (hm : 0 < m) (ht : t < h) (hN : 0 < N)
    (hM : paddedAlpha allow h m b t * N ≤ ((window A (h-t) 1 N).card : ℝ))
    (he : ((window A (h-t-1) 0 N).card : ℝ) ≤ 2 * paddedAlpha allow h m b (t+1) * N) :
    6 * N ≤ paddedL allow h m b t *
      ((Finset.Icc 0 (2*N)).filter (· ∈ richSums A (2*(h-t)) (paddedQ allow h m b t))).card := by
  classical
  let r := h-t
  let Q := paddedQ allow h m b t
  let L := paddedL allow h m b t
  let α := paddedAlpha allow h m b t
  let M := (window A r 1 N).card
  let e := (window A (r-1) 0 N).card
  let D := ((Finset.Icc 0 (2*N)).filter (· ∈ richSums A (2*r) Q)).card
  have hQ : 0 < Q := Nat.zero_lt_succ _
  have hr : 0 < r := Nat.sub_pos_of_lt ht
  have hcap : M ≤ N := by
    simpa [M, window] using Finset.card_filter_le (Finset.Icc 1 N) (· ∈ restrictedSums A r)
  have hb : M^2 ≤ N*D + 8*r*(Q-1)*e*N + r*M*e := pair_count_bound A r Q N
  have hb' : (M : ℝ)^2 ≤ (N : ℝ)*D + 8*(r : ℝ)*((Q-1 : ℕ) : ℝ)*e*N + (r : ℝ)*M*e := by
    exact_mod_cast hb
  rw [Nat.cast_sub (by omega : 1 ≤ Q), Nat.cast_one] at hb'
  obtain ⟨hα, hL, hnext⟩ := padded_equation allow h m b t hm ht
  rw [hnext] at he
  have hceil : 8 / α^2 ≤ (L : ℝ) := by
    change 8 / paddedAlpha allow h m b t ^ 2 ≤ (paddedL allow h m b t : ℝ)
    rw [hL]; exact Nat.le_ceil _
  have hcount : (M : ℝ)^2 - (r : ℝ)*M*e ≤ (N : ℝ)*D + 8*(r : ℝ)*((Q : ℝ)-1)*e*N := by
    linarith only [hb']
  have result := (progression_many_popular_sums N r Q α L M e D
    (by exact_mod_cast hN) (by exact_mod_cast hr) (by exact_mod_cast hQ) hα (by positivity)
    hM (by exact_mod_cast hcap) he hcount hceil).2
  exact_mod_cast result
theorem eventually_padded_rank (allow : ℕ → ℕ) (A : Set ℕ) (h m b : ℕ) (_hh : 0 < h) (hm : 0 < m)
    (hd : progressionAlpha h m b 0 < positiveLowerDensity (restrictedSums A h)) :
    ∀ᶠ N : ℕ in atTop, ∃ t < h, 6*N ≤ paddedL allow h m b t *
      ((Finset.Icc 0 (2*N)).filter (· ∈ richSums A (2*(h-t)) (paddedQ allow h m b t))).card := by
  filter_upwards [eventually_padded_transition allow A h m b hm hd, eventually_gt_atTop 0] with N hgood hN
  obtain ⟨t, ht, hM, he⟩ := hgood
  exact ⟨t, ht, padded_rank_at allow A h m b t N hm ht hN hM he⟩
private theorem padded_chooseOutside {A : Set ℕ} {w q d : ℕ} (hd : d ∈ richSums A w q)
    (W : Finset ℕ) (hq : W.card < q) :
    ∃ G : Finset ℕ, (∀ x ∈ G, x ∈ A) ∧ G.card ≤ w ∧ G.sum id = d ∧ Disjoint G W := by
  classical
  rcases hd with rfl | ⟨G, hG, hpair⟩
  · exact ⟨∅, by simp, by simp, by simp, by simp⟩
  have hex : ∃ i, Disjoint (G i) W := by
    by_contra! hn
    have hh (i : Fin q) : ∃ x, x ∈ G i ∧ x ∈ W := Finset.not_disjoint_iff.mp (hn i)
    choose x hx hw using hh
    let f (i : Fin q) : ↥W := ⟨x i, hw i⟩
    have hinj : Function.Injective f := by
      intro i j he
      by_contra hne
      have e : x i = x j := congrArg Subtype.val he
      exact (Finset.disjoint_left.mp (hpair hne)) (hx i) (e ▸ hx j)
    have := Fintype.card_le_of_injective f hinj
    simp only [Fintype.card_fin, Fintype.card_coe] at this
    omega
  obtain ⟨i, hi⟩ := hex
  exact ⟨G i, (hG i).1, (hG i).2.1, (hG i).2.2, hi⟩
private theorem padded_rep_addCopies {A B : Set ℕ} {F : Finset ℕ} {p w q L : ℕ}
    (base : ∀ x ∈ B, Rep (A \ (F : Set ℕ)) p x)
    (room : F.card + p + w * (L - 1) < q) (k : ℕ) (hk : k ≤ L) :
    ∀ n ∈ addCopies B (richSums A w q) k, Rep (A \ (F : Set ℕ)) (p + w * k) n := by
  classical
  induction k with
  | zero => simpa [addCopies] using base
  | succ k ih =>
    rintro n ⟨x, hx, d, hd, rfl⟩
    obtain ⟨T, hT, ht, hsum⟩ := ih (by omega) x hx
    have hle : w * k ≤ w * (L - 1) := Nat.mul_le_mul_left w (by omega)
    have hroom : (F ∪ T).card < q := by
      have := Finset.card_union_le F T
      omega
    obtain ⟨G, hG, hg, hdsum, hdis⟩ := padded_chooseOutside hd (F ∪ T) hroom
    have hGT : Disjoint G T := Finset.disjoint_left.mpr fun _ hx ht' =>
      Finset.disjoint_left.mp hdis hx (Finset.mem_union_right _ ht')
    refine ⟨T ∪ G, ?_, ?_, ?_⟩
    · intro a ha
      rcases Finset.mem_union.mp ha with hat | hag
      · exact hT a hat
      · exact ⟨hG a hag, fun haf => Finset.disjoint_left.mp hdis hag (Finset.mem_union_left _ haf)⟩
    · rw [Nat.mul_succ]
      have := Finset.card_union_le T G
      omega
    · rw [Finset.sum_union hGT.symm, hsum, hdsum]
def paddedSums (allow : ℕ → ℕ) (A : Set ℕ) (h m b : ℕ) : ℕ → Set ℕ
  | 0 => {0}
  | t + 1 => addCopies (paddedSums allow A h m b t)
      (richSums A (2 * (h - t)) (paddedQ allow h m b t)) (paddedB allow h m b t)
theorem rep_paddedSums (allow : ℕ → ℕ) {A : Set ℕ} {h m b : ℕ} (F : Finset ℕ) (hf : F.card ≤ b)
    (t : ℕ) : ∀ n ∈ paddedSums allow A h m b t,
      Rep (A \ (F : Set ℕ)) (paddedStage allow h m b t).cost n := by
  induction t with
  | zero =>
    intro n hn
    have he : n = 0 := hn
    exact ⟨∅, by simp, by simp, by simp [he]⟩
  | succ t ih =>
    apply padded_rep_addCopies ih _ _ (le_refl _)
    change F.card + _ + _ < b + (paddedStage allow h m b t).cost +
      2 * (h - t) * (paddedB allow h m b t - 1) + 1
    omega
end OMA.E338.Bridge
end

-- module KneserFamily
section
namespace OMA.E338.Bridge
open Filter
open scoped Pointwise Classical
def AsymptoticKneser : Prop :=
  ∀ X : List (Set ℕ), 2 ≤ X.length → (∀ C ∈ X, C.Infinite) →
    positiveLowerDensity X.sum <
      liminf (fun N : ℕ =>
        (((X.map (fun C => windowCount C N)).sum : ℕ) : ℝ) / N) atTop →
    ∃ g : ℕ, 0 < g ∧ ∃ T : Set (ZMod g),
      ∀ᶠ n : ℕ in atTop, n ∈ X.sum ↔ (n : ZMod g) ∈ T
noncomputable def infiniteSummands (C : ℕ → Set ℕ) (L : ℕ → ℕ) : ℕ → List (Set ℕ)
  | 0 => []
  | t+1 => if (C t).Infinite then infiniteSummands C L t ++ List.replicate (L t) (C t)
           else infiniteSummands C L t
theorem infiniteSummands_infinite (C : ℕ → Set ℕ) (L : ℕ → ℕ) (t : ℕ) :
    ∀ S ∈ infiniteSummands C L t, S.Infinite := by
  induction t with
  | zero => simp [infiniteSummands]
  | succ t ih =>
    by_cases ht : (C t).Infinite
    · intro S hS
      rw [infiniteSummands, ite_eq_left ht, List.mem_append] at hS
      rcases hS with h | h
      · exact ih S h
      · obtain ⟨_, he⟩ := List.mem_replicate.mp h
        simpa only [he] using ht
    · simpa only [infiniteSummands, ht, ↓reduceIte] using ih
theorem infiniteSummands_total (C : ℕ → Set ℕ) (L : ℕ → ℕ) (t : ℕ) (f : Set ℕ → ℕ) :
    ((infiniteSummands C L t).map f).sum =
      ∑ j ∈ (Finset.range t).filter (fun j => (C j).Infinite), L j * f (C j) := by
  induction t with
  | zero => simp [infiniteSummands]
  | succ t ih =>
    rw [Finset.sum_filter, Finset.sum_range_succ, ← Finset.sum_filter]
    by_cases ht : (C t).Infinite <;>
      simp [infiniteSummands, ht, ih, List.sum_replicate]
theorem infiniteSummands_length (C : ℕ → Set ℕ) (L : ℕ → ℕ) (t : ℕ) :
    (infiniteSummands C L t).length =
      ∑ j ∈ (Finset.range t).filter (fun j => (C j).Infinite), L j := by
  simpa using infiniteSummands_total C L t (fun _ => 1)
theorem addCopies_eq_pointwise (B C : Set ℕ) (k : ℕ) :
    addCopies B C k = B + k • C := by
  induction k with
  | zero => simp [addCopies]
  | succ k ih =>
    rw [succ_nsmul, ← add_assoc, ← ih]
    rfl
theorem infiniteSummands_sum (A : Set ℕ) (h m b t : ℕ) :
    (infiniteSummands (fun j => richSums A (2 * (h - j)) (progressionQ h m b j))
      (progressionL h m b) t).sum = infiniteLevelSums A h m b t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    by_cases hi : (richSums A (2 * (h - t)) (progressionQ h m b t)).Infinite
    · simp [infiniteSummands, infiniteLevelSums, hi, ih, List.sum_replicate,
        addCopies_eq_pointwise]
    · simp [infiniteSummands, infiniteLevelSums, hi, ih]
theorem positiveLowerDensity_le_one (B : Set ℕ) : positiveLowerDensity B ≤ 1 := by
  unfold positiveLowerDensity
  apply liminf_le_of_frequently_le
  · apply Eventually.frequently
    filter_upwards [eventually_gt_atTop 0] with N hN
    apply (div_le_iff₀ (by exact_mod_cast hN : 0 < (N : ℝ))).mpr
    rw [one_mul]
    exact_mod_cast (show ((Finset.Icc 1 N).filter (· ∈ B)).card ≤ N by
      simpa using (Finset.card_filter_le (Finset.Icc 1 N) (fun x => x ∈ B)))
  · refine ⟨(0 : ℝ), ?_⟩
    change ∀ᶠ N : ℕ in atTop, 0 ≤ (((Finset.Icc 1 N).filter (· ∈ B)).card : ℝ) / N
    exact Eventually.of_forall fun N => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
end OMA.E338.Bridge
end

-- module PaddedEmbedding
section
namespace OMA.E338.Bridge
open scoped Pointwise BigOperators
private theorem zero_mem_prefix (D : ℕ → Set ℕ) (hD : ∀ k, 0 ∈ D k) (t : ℕ) :
    0 ∈ ∑ k ∈ Finset.range t, D k := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Finset.sum_range_succ]
    simpa using Set.add_mem_add ih (hD t)
private theorem mem_prefix_of_mem_level (D : ℕ → Set ℕ) (hD : ∀ k, 0 ∈ D k)
    (i t : ℕ) (hi : i < t) {u : ℕ} (hu : u ∈ D i) :
    u ∈ ∑ k ∈ Finset.range t, D k := by
  induction t with
  | zero => omega
  | succ t ih =>
    rw [Finset.sum_range_succ]
    by_cases he : i = t
    · subst i
      simpa using Set.add_mem_add (zero_mem_prefix D hD t) hu
    · simpa using Set.add_mem_add (ih (by omega)) (hD t)
theorem paddedSums_eq_double (cap : ℕ → ℕ) (A : Set ℕ) (h m b t : ℕ) :
    let allow := fun l => 2 * cap l
    let D := fun i => cap (paddedL allow h m b i) •
      richSums A (2 * (h-i)) (paddedQ allow h m b i)
    paddedSums allow A h m b t = (∑ i ∈ Finset.range t, D i) + ∑ i ∈ Finset.range t, D i := by
  dsimp only
  induction t with
  | zero => simp [paddedSums]; rfl
  | succ t ih =>
    rw [paddedSums, addCopies_eq_pointwise, ih, Finset.sum_range_succ]
    simp only [paddedB, two_mul, add_nsmul]
    ac_rfl
theorem two_mem_paddedSums (cap : ℕ → ℕ) (A : Set ℕ) (h m b i j u v : ℕ)
    (hi : i < h) (hj : j < h)
    (hu : u ∈ cap (paddedL (fun l => 2*cap l) h m b i) •
      richSums A (2*(h-i)) (paddedQ (fun l => 2*cap l) h m b i))
    (hv : v ∈ cap (paddedL (fun l => 2*cap l) h m b j) •
      richSums A (2*(h-j)) (paddedQ (fun l => 2*cap l) h m b j)) :
    u+v ∈ paddedSums (fun l => 2*cap l) A h m b h := by
  let allow := fun l => 2*cap l
  let D := fun i => cap (paddedL allow h m b i) • richSums A (2*(h-i)) (paddedQ allow h m b i)
  have hz (k : ℕ) : 0 ∈ D k := Set.zero_mem_nsmul (Or.inl rfl : 0 ∈ richSums A _ _)
  rw [paddedSums_eq_double]
  exact Set.add_mem_add (mem_prefix_of_mem_level D hz i h hi hu)
    (mem_prefix_of_mem_level D hz j h hj hv)
end OMA.E338.Bridge
end

-- module DensityPartners
section
namespace OMA.E338.Bridge
open scoped BigOperators
theorem exceptionalPartnerCount (B T G : Finset ℕ) (F : ℕ → Finset ℕ) (h : ℕ)
    (hcard : ∀ b ∈ B, (F b).card ≤ h) (hT : h < T.card)
    (allows : ∀ b ∈ B, ∀ a ∈ T, a ∉ F b → b + a ∈ G) :
    (B.biUnion (fun b => (F b).image (fun a => b + a))).card ≤ h * T.card * G.card := by
  classical
  let row (a : ℕ) := B.filter (fun b => a ∉ F b)
  have hcover : B ⊆ T.biUnion row := by
    intro b hb
    obtain ⟨a, ha, hab⟩ := Finset.exists_mem_notMem_of_card_lt_card ((hcard b hb).trans_lt hT)
    exact Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_filter.mpr ⟨hb, hab⟩⟩
  have hr (a : ℕ) (ha : a ∈ T) : (row a).card ≤ G.card := by
    apply Finset.card_le_card_of_injOn (fun b : ℕ => b + a)
    · intro b hb
      obtain ⟨hbB, hf⟩ := Finset.mem_filter.mp hb
      exact allows b hbB a ha hf
    · intro b _ b' _ he
      exact Nat.add_right_cancel he
  have hB : B.card ≤ T.card * G.card :=
    (Finset.card_le_card hcover).trans (Finset.card_biUnion_le_card_mul T row G.card hr)
  calc
    _ ≤ B.card * h := Finset.card_biUnion_le_card_mul B _ h (fun b hb =>
      Finset.card_image_le.trans (hcard b hb))
    _ ≤ (T.card * G.card) * h := Nat.mul_le_mul_right _ hB
    _ = _ := by ac_rfl
end OMA.E338.Bridge
end

-- module CollisionDensity
section
namespace OMA.E338.Bridge
open Filter
open scoped Classical BigOperators
def CollisionRep (A : Set ℕ) (h d n : ℕ) : Prop :=
  ∃ s : Multiset ℕ, (∀ a ∈ s, a ∈ A) ∧ s.card ≤ h ∧
    s.card ≤ s.toFinset.card + d ∧ s.sum = n
noncomputable def collisionWindow (A : Set ℕ) (h d N : ℕ) : Finset ℕ :=
  (Finset.range N).filter (CollisionRep A h d)
private theorem duplicate_cons {s : Multiset ℕ} (hn : ¬s.Nodup) :
    ∃ a t, s = a ::ₘ t ∧ a ∈ t := by
  rw [Multiset.nodup_iff_count_le_one] at hn
  push Not at hn
  obtain ⟨a, ha⟩ := hn
  obtain ⟨t, rfl⟩ := Multiset.exists_cons_of_mem (Multiset.count_pos.mp (Nat.zero_lt_of_lt ha))
  refine ⟨a, t, rfl, Multiset.count_pos.mp ?_⟩
  simpa using ha
private def PartialRep (A : Set ℕ) (h d b : ℕ) (t : Multiset ℕ) : Prop :=
  (∀ a ∈ t, a ∈ A) ∧ t.card < h ∧ t.card ≤ t.toFinset.card + d ∧ t.sum = b
private theorem append_fresh {A : Set ℕ} {h d b a : ℕ} {t : Multiset ℕ}
    (ht : PartialRep A h d b t) (ha : a ∈ A) (hf : a ∉ t.toFinset) :
    CollisionRep A h d (b + a) := by
  obtain ⟨hA, hlen, hcol, hsum⟩ := ht
  refine ⟨a ::ₘ t, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rcases Multiset.mem_cons.mp hx with rfl | h
    · exact ha
    · exact hA _ h
  · simp only [Multiset.card_cons]; omega
  · rw [Multiset.card_cons, Multiset.toFinset_cons, Finset.card_insert_of_notMem hf]
    omega
  · simp [hsum, Nat.add_comm]
private theorem split_collision {A : Set ℕ} {h d n : ℕ}
    (hs : CollisionRep A h (d+1) n) :
    CollisionRep A h d n ∨ ∃ b a t, PartialRep A h d b t ∧ a ∈ A ∧ b + a = n := by
  obtain ⟨s, hA, hlen, hcol, hsum⟩ := hs
  by_cases hn : s.Nodup
  · exact Or.inl ⟨s, hA, hlen, by rw [Multiset.toFinset_card_of_nodup hn]; omega, hsum⟩
  · obtain ⟨a, t, rfl, hat⟩ := duplicate_cons hn
    have haT : a ∈ t.toFinset := Multiset.mem_toFinset.mpr hat
    simp only [Multiset.card_cons, Multiset.toFinset_cons, Finset.insert_eq_of_mem haT] at hlen hcol
    refine Or.inr ⟨t.sum, a, t, ⟨fun x hx => hA x (Multiset.mem_cons_of_mem hx), by omega, by omega, rfl⟩,
      hA a (Multiset.mem_cons_self a t), ?_⟩
    simpa [Nat.add_comm] using hsum
theorem collisionWindow_step (A : Set ℕ) (h d N U : ℕ) (T : Finset ℕ)
    (hT : h < T.card) (hTA : ∀ a ∈ T, a ∈ A) (hU : ∀ a ∈ T, a ≤ U) :
    (collisionWindow A h (d+1) N).card ≤
      (1 + h*T.card) * (collisionWindow A h d (N+U)).card := by
  classical
  let G := collisionWindow A h d (N + U)
  let B := (Finset.range N).filter (fun b => ∃ t, PartialRep A h d b t)
  let t (b : ℕ) : Multiset ℕ :=
    if ex : ∃ s, PartialRep A h d b s then ex.choose else 0
  have chosen {b : ℕ} (hb : b ∈ B) : PartialRep A h d b (t b) := by
    have ex := (Finset.mem_filter.mp hb).2
    simpa only [t, dite_eq_left ex] using ex.choose_spec
  let F (b : ℕ) := (t b).toFinset
  have hsize (b : ℕ) (hb : b ∈ B) : (F b).card ≤ h :=
    (t b).toFinset_card_le.trans (chosen hb).2.1.le
  have allowed {b a : ℕ} (hb : b ∈ B) (ha : a ∈ A) (hf : a ∉ F b) (hn : b + a < N + U) :
      b + a ∈ G :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hn, append_fresh (chosen hb) ha hf⟩
  have bound := exceptionalPartnerCount B T G F h hsize hT (by
    intro b hb a hat hf
    have hbN := Finset.mem_range.mp (Finset.mem_filter.mp hb).1
    have haU := hU a hat
    apply allowed hb (hTA a hat) hf
    omega)
  have sub : collisionWindow A h (d+1) N ⊆ G ∪ B.biUnion (fun b => (F b).image (fun a => b+a)) := by
    intro n hn
    obtain ⟨hnN, hrep⟩ := Finset.mem_filter.mp hn
    have hnlt := Finset.mem_range.mp hnN
    rcases split_collision hrep with hgood | ⟨b, a, s, hs, haA, rfl⟩
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hgood⟩)
    · have hb : b ∈ B := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), s, hs⟩
      by_cases hf : a ∈ F b
      · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨b, hb, Finset.mem_image.mpr ⟨a, hf, rfl⟩⟩)
      · exact Finset.mem_union_left _ (allowed hb haA hf (by omega))
  calc
    _ ≤ (G ∪ B.biUnion (fun b => (F b).image (fun a => b+a))).card := Finset.card_le_card sub
    _ ≤ G.card + _ := Finset.card_union_le _ _
    _ ≤ G.card + h*T.card*G.card := Nat.add_le_add_left bound _
    _ = (1 + h*T.card) * G.card := by ring
theorem collisionWindow_iterate (A : Set ℕ) (h d N U : ℕ) (T : Finset ℕ)
    (hT : h < T.card) (hTA : ∀ a ∈ T, a ∈ A) (hU : ∀ a ∈ T, a ≤ U) :
    (collisionWindow A h d N).card ≤
      (1 + h * T.card)^d * (collisionWindow A h 0 (N + d*U)).card := by
  induction d generalizing N with
  | zero => simp
  | succ d ih =>
    calc
      _ ≤ _ := collisionWindow_step A h d N U T hT hTA hU
      _ ≤ (1+h*T.card) * ((1+h*T.card)^d * (collisionWindow A h 0 (N+U+d*U)).card) :=
        Nat.mul_le_mul_left _ (ih (N+U))
      _ = _ := by
        rw [show N+U+d*U = N+(d+1)*U by ring, pow_succ]
        ring
private theorem hasOrder_infinite {A : Set ℕ} {h : ℕ} (hA : HasOrder A h) : A.Infinite := by
  intro hfin
  obtain ⟨V, hV⟩ := hfin.bddAbove
  obtain ⟨n, ⟨s, hs, hc, he⟩, hn⟩ := (hA.and (eventually_gt_atTop (h * V))).exists
  have total (t : Multiset ℕ) (ht : ∀ x ∈ t, x ≤ V) : t.sum ≤ t.card * V := by
    induction t using Multiset.induction_on with
    | empty => simp
    | cons x t ih =>
      have hrest := ih (fun y hy => ht y (Multiset.mem_cons_of_mem hy))
      have hx := ht x (Multiset.mem_cons_self x t)
      simp only [Multiset.sum_cons, Multiset.card_cons, Nat.succ_mul]
      omega
  have hsum := total s (fun x hx => hV (hs x hx))
  exact (not_le_of_gt hn) (he ▸ (hsum.trans (Nat.mul_le_mul_right V hc)))
private theorem collision_zero_subset {A : Set ℕ} {h n : ℕ} (hs : CollisionRep A h 0 n) :
    Rep A h n := by
  obtain ⟨s, hA, hc, hd, he⟩ := hs
  have hnodup : s.Nodup := Multiset.toFinset_card_eq_card_iff_nodup.mp
    (le_antisymm s.toFinset_card_le (by simpa using hd))
  refine ⟨⟨s, hnodup⟩, hA, hc, ?_⟩
  change (s.map id).sum = n
  simpa using he
def collisionDenominator (h : ℕ) : ℕ := 2 * (1 + h * (h+1))^h
theorem collision_density_bound (A : Set ℕ) (h : ℕ) (ha : HasOrder A h) :
    DensityBound (restrictedSums A h) (collisionDenominator h) := by
  classical
  obtain ⟨S, hsA, hfin, hsCard⟩ := (hasOrder_infinite ha).exists_subset_ncard_eq (h+1)
  let T := hfin.toFinset
  have htCard : T.card = h+1 := by simpa only [T, ← Set.ncard_eq_toFinset_card S hfin] using hsCard
  have htA (a : ℕ) (haT : a ∈ T) : a ∈ A := hsA (hfin.mem_toFinset.mp haT)
  let U := T.sup id
  have htU (a : ℕ) (haT : a ∈ T) : a ≤ U := Finset.le_sup (f := id) haT
  obtain ⟨L, hL⟩ := eventually_atTop.mp ha
  refine ⟨2*(h*U+L), ?_⟩
  intro M hM
  let N := M - h*U
  have hNM : N + h*U = M := by dsimp [N]; omega
  have ordinary : Finset.Ico L N ⊆ collisionWindow A h h N := by
    intro n hn
    obtain ⟨hl, hr⟩ := Finset.mem_Ico.mp hn
    obtain ⟨s, hs, hlen, hsum⟩ := hL n hl
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hr, s, hs, hlen, by omega, hsum⟩
  have distinct : collisionWindow A h 0 M ⊆ (Finset.range M).filter (· ∈ restrictedSums A h) := by
    intro n hn
    have hx := Finset.mem_filter.mp hn
    exact Finset.mem_filter.mpr ⟨hx.1, collision_zero_subset hx.2⟩
  have hcount := collisionWindow_iterate A h h N U T (by omega) htA htU
  rw [htCard, hNM] at hcount
  have hprefix := Finset.card_le_card ordinary
  rw [Nat.card_Ico] at hprefix
  calc
    M ≤ 2*(N-L) := by omega
    _ ≤ 2*(collisionWindow A h h N).card := Nat.mul_le_mul_left 2 hprefix
    _ ≤ 2*((1+h*(h+1))^h * (collisionWindow A h 0 M).card) := Nat.mul_le_mul_left 2 hcount
    _ = collisionDenominator h * (collisionWindow A h 0 M).card := by
      rw [collisionDenominator, Nat.mul_assoc]
    _ ≤ _ := Nat.mul_le_mul_left _ (Finset.card_le_card distinct)
theorem uniformDensityInput : UniformDensityInput := by
  intro h _
  exact ⟨collisionDenominator h, by unfold collisionDenominator; positivity, fun A => collision_density_bound A h⟩
end OMA.E338.Bridge
end

-- module Erdos338Unconditional
section
namespace OMA.E338.Bridge
open Filter
open scoped Pointwise Classical
theorem uniformProgressionInput : UniformProgressionInput := by
  intro h m b hh hm
  let allow := fun l => 2 * twoScaleCap l
  refine ⟨paddedK allow h m b, ?_⟩
  intro A hden
  let C := fun t => richSums A (2*(h-t)) (paddedQ allow h m b t)
  let L := paddedL allow h m b
  have h0 (i : ℕ) : 0 ∈ C i := Or.inl rfl
  have hdens : progressionAlpha h m b 0 < positiveLowerDensity (restrictedSums A h) := by
    rw [progressionAlpha_zero]
    exact half_inv_lt_positiveLowerDensity hm hden
  have mass : ∀ᶠ X : ℕ in atTop, ∃ i < h, 6*X ≤ L i * windowCount (C i) (2*X) :=
    eventually_padded_rank allow A h m b hh hm hdens
  obtain ⟨d, hd, windows⟩ := synchronizeProductiveWindows h C L
    (fun i hi => localCoverAtProductiveWindows (C i) (h0 i) (L i)
      (paddedL_pos allow h m b i hm hi.le)) mass
  obtain ⟨g, hg, hn⟩ := twoScaleCover h C L d hd (fun i _ => h0 i) windows
  obtain ⟨N₀, hN⟩ := eventually_atTop.mp hn
  refine ⟨g, hg, 0, N₀, ?_⟩
  intro F _ hF n hn hnmod
  obtain ⟨i, hi, j, hj, u, hu, v, hv, huv⟩ :=
    hN n hn ((ZMod.natCast_eq_zero_iff n g).mp hnmod)
  apply rep_paddedSums allow F hF h n
  rw [← huv]
  exact two_mem_paddedSums twoScaleCap A h m b i j u v hi hj hu hv
theorem boundedByOrder : BoundedByOrder :=
  boundedByOrder_of_analyticInputs uniformDensityInput uniformProgressionInput
end OMA.E338.Bridge
end

theorem OMA.solution : type_of% @Erdos338.erdos_338.variants.bounded_by_order :=
  OMA.E338.Bridge.boundedByOrder
