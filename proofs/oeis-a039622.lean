import OMAStatements.S_oeis_a039622
import Mathlib

/-!
The following hook-length argument is adapted to the pinned Mathlib version
from Noah Walker's KostkaNumbers (Apache License 2.0). It implements the
Greene–Nijenhuis–Wilf probabilistic proof.
Source: https://github.com/NoahW314/KostkaNumbers/tree/135e49269833f4a760717b30777046d9629240df
-/

/- License of the adapted KostkaNumbers modules (verbatim).

                                 Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "[]"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright [yyyy] [name of copyright owner]

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

-/


/- Source module: KostkaNumbers.Util.Remove -/
section
/-
Copyright (c) 2026 Noah Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Walker
-/



/-!
Define a remove operation on multisets that removes all copies of a single element from a multiset.
-/

section

namespace Multiset

section Remove

variable {α : Type*} [DecidableEq α] (S : Multiset α) (a : α)

def remove := S - (replicate (count a S) a)

@[simp] lemma remove_bot : remove (⊥ : Multiset α) a = ⊥ := by
  simp [remove]

@[simp] lemma remove_zero : remove 0 a = 0 := by
  simp [remove]

@[simp]
lemma notMem_of_remove : a ∉ S.remove a := by
  simp [remove, ← count_eq_zero]

lemma remove_of_notMem (ha : a ∉ S) : S.remove a = S := by
  rw [← count_pos, Nat.pos_iff_ne_zero] at ha
  push Not at ha
  rw [remove, ha, replicate_zero, Multiset.sub_zero]

lemma mem_remove_of_ne {a b : α} (h : a ≠ b) : b ∈ S.remove a ↔ b ∈ S := by
  simp [remove, mem_sub, count_replicate, h, count_pos]

variable {S : Multiset α} {a b : α}

lemma mem_remove_of_mem (b : α) (h : a ∈ S) : a ∈ S.remove b ↔ b ≠ a := by
  grind [mem_remove_of_ne, notMem_of_remove]

lemma mem_of_mem_remove (h : b ∈ S.remove a) : b ∈ S := by
  rw [← count_pos]
  rw [remove, mem_sub] at h
  exact lt_of_le_of_lt (Nat.zero_le _) h

lemma insert_remove_toFinset (ha : a ∈ S) : insert a (S.remove a).toFinset = S.toFinset := by
  grind [mem_of_mem_remove, mem_remove_of_ne, notMem_of_remove]

lemma remove_toFinset (S : Multiset α) (a : α) : (S.remove a).toFinset = S.toFinset.erase a := by
  by_cases ha : a ∈ S
  · grind [insert_remove_toFinset, notMem_of_remove]
  · grind [remove_of_notMem]

lemma remove_toFinset_card (S : Multiset α) (a : α) (ha : a ∈ S) :
    (S.remove a).toFinset.card = S.toFinset.card - 1 := by grind [remove_toFinset]

lemma remove_zero_sum (μ : Multiset ℕ) : μ.sum = (μ.remove 0).sum := by
  by_cases! h0 : 0 ∉ μ
  · rw [remove_of_notMem μ 0 h0]
  simp only [Finset.sum_multiset_count, smul_eq_mul, remove, count_sub, count_replicate]
  rw [← insert_remove_toFinset h0, Finset.sum_insert_zero]
  · exact Finset.sum_congr rfl (by grind)
  · rw [mul_zero]

lemma cons_remove {μ : Multiset α} (a : α) : (a ::ₘ μ).remove a = μ.remove a := by
  simp [remove]

lemma sub_card_le_card {s t : Multiset α} : (s - t).card ≤ s.card := by
  exact card_le_card <| Multiset.sub_le_self s t

lemma remove_card_le_card {μ : Multiset α} {a : α} : (μ.remove a).card ≤ μ.card := by
  simp [remove, sub_card_le_card]

lemma remove_replicate {n : ℕ} {a b : α} (h : a = b) : (Multiset.replicate n a).remove b = ∅ := by
  simp [remove, h]

lemma remove_add {s t : Multiset α} (a : α) : (s + t).remove a = s.remove a + t.remove a := by
  rw [remove, count_add, replicate_add, tsub_add_eq_tsub_tsub, add_comm, add_tsub_assoc_of_le,
    add_comm, add_tsub_assoc_of_le, remove, remove]
  · rw [← Multiset.filter_eq]
    exact filter_le _ t
  · rw [← Multiset.filter_eq]
    exact filter_le _ s

lemma sub_remove {s : Multiset α} {a : α} : s - (s.remove a) = replicate (count a s) a := by
  rw [remove, tsub_tsub_cancel_of_le]
  rw [← Multiset.filter_eq]
  exact filter_le _ s

end Remove

end Multiset

end
end


/- Source module: KostkaNumbers.Util.Counts -/
section
/-
Copyright (c) 2026 Noah Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Walker
-/



section

/-!
The `counts` operation on a multiset tallies the number of each element that appear. For example,
{1, 1, 1, 2, 3, 4, 4}.counts = {3, 1, 1, 2}.
-/

namespace Multiset

section Counts

variable {α : Type*} [DecidableEq α] (M : Multiset α)

def counts : Multiset ℕ := Multiset.map (fun x : α => Multiset.count x M) M.dedup

@[simp] lemma zero_notMem_counts : 0 ∉ M.counts := by simp [counts]

@[simp] lemma counts_pos (n : ℕ) (hn : n ∈ M.counts) : n > 0 := by
  grind [zero_notMem_counts]

lemma bot_counts_iff : M.counts = ⊥ ↔ M = ⊥ := by
  simp [counts, dedup_eq_zero]

lemma sum_counts_eq_card : M.counts.sum = M.card := by
  simp only [counts, Finset.sum_multiset_map_count, toFinset_dedup, count_dedup, smul_eq_mul,
    ite_mul, one_mul, zero_mul,
    ← Multiset.sum_count_eq_card (s := M.toFinset) (m := M) (by simp)]
  exact Finset.sum_congr rfl (by grind)

lemma counts_card : M.counts.card = M.toFinset.card := by
  simp only [counts, card_map]
  rfl

lemma counts_replicate {n : ℕ} (a : α) (hn : n ≠ 0) : (replicate n a).counts = {n} := by
  simp_rw [counts, count_replicate, map_eq_singleton]
  use a
  simp [← nsmul_singleton, dedup_nsmul hn]

-- upstream
lemma replicate_dedup {x : α} {k : ℕ} (h : k ≠ 0) : (replicate k x).dedup = {x} := by
  simp [← coe_replicate, List.replicate_dedup h]

lemma replicate_add_counts_of_notMem {a : α} {M : Multiset α} {n : ℕ} (h : a ∉ M) (hn : n ≠ 0) :
    ((replicate n a) + M).counts = {n} + M.counts := by
  simp only [counts, count_add, count_replicate]
  ext m
  rw [count_add, count_map, count_map, Disjoint.dedup_add, replicate_dedup hn, filter_add,
    card_add]
  · by_cases hmn : m = n
    · simp only [hmn, nodup_singleton, mem_singleton, count_eq_one_of_mem]
      · congr 2
        · rw [card_eq_one]
          use a
          simp [h]
        · exact filter_congr (by grind [mem_dedup])
    · rw [← count_pos, Nat.pos_iff_ne_zero] at h
      push Not at h
      simp only [filter_singleton, ↓reduceIte, h, add_zero, hmn, empty_eq_zero, card_zero,
        mem_singleton, not_false_eq_true, count_eq_zero_of_notMem]
      congr 2
      refine filter_congr ?_
      intro x hx
      have hax : a ≠ x := by
        rw [mem_dedup, ← count_pos, Nat.pos_iff_ne_zero] at hx
        grind
      simp [hax]
  · refine disjoint_left.mpr ?_
    simp_all [mem_replicate]


end Counts

end Multiset

end
end


/- Source module: KostkaNumbers.Util.Util -/
section
/-
Copyright (c) 2026 Noah Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Walker
-/



/-!
This file contains some basic results about Lists and Multisets that I need that are not in Mathlib.
I intend to upstream most of these results to Mathlib.
-/

section

namespace List

variable {α : Type*} {x : α} {R : α → α → Prop} {r : α → α → Bool}

lemma sortedGE_replicate {α : Type*} [Preorder α] {a : α} (n : ℕ) :
    (replicate n a).SortedGE := pairwise_replicate_of_refl.sortedGE

lemma perm_iff_eq_of_sortedGE {α : Type*} [PartialOrder α] {l₁ l₂ : List α} (h₁ : l₁.SortedGE)
    (h₂ : l₂.SortedGE) : l₁.Perm l₂ ↔ l₁ = l₂ :=
  ⟨List.Perm.eq_of_sortedGE h₁ h₂, List.Perm.of_eq⟩

lemma pairwise_append_singleton {L : List α} (hL : Pairwise R L) (h : ∀ y ∈ L, R y x) :
    Pairwise R (L ++ [x]) := by
  simpa [pairwise_append, hL]

-- include dual version
lemma max_eq_bot_iff {α : Type*} [Max α] [PartialOrder α] [OrderBot α] [Std.LawfulOrderSup α]
    {l : List α} (hl : l ≠ []) :
    l.max hl = ⊥ ↔ ∀ x ∈ l, x = ⊥ := by
  simp_rw [eq_bot_iff, List.max_le_iff]

-- include dual version
lemma min_eq_bot_of_bot_mem {α : Type*} [LinearOrder α] [OrderBot α]
    {l : List α} (hl : l ≠ []) (h : ⊥ ∈ l) :
    l.min hl = ⊥ := by
  rw [eq_bot_iff]
  exact min_le_of_mem h

lemma mem_tail_of_mem_ne_head {α : Type*} {l : List α} {a : α} (hl : l ≠ []) (ha : a ∈ l)
    (hah : a ≠ l.head hl) :
    a ∈ l.tail := by
  rw [← List.cons_head_tail hl] at ha
  grind


end List


namespace Multiset

variable {α : Type*}

lemma prod_eq_one_iff_eq_one [CommMonoid α] [PartialOrder α] [IsOrderedMonoid α]
    [CanonicallyOrderedMul α] {μ : Multiset α} (h0 : 1 ∉ μ) :
    μ.prod = 1 ↔ μ = 0 := by
  refine ⟨?_, fun h ↦ h ▸ prod_zero⟩
  rw [prod_eq_one_iff, eq_zero_iff_forall_notMem]
  grind

lemma sum_eq_zero_iff_eq_zero [AddCommMonoid α] [PartialOrder α] [IsOrderedAddMonoid α]
    [CanonicallyOrderedAdd α] {μ : Multiset α} (h0 : 0 ∉ μ) :
    μ.sum = 0 ↔ μ = 0 := by
  refine ⟨?_, fun h ↦ h ▸ sum_zero⟩
  rw [sum_eq_zero_iff, eq_zero_iff_forall_notMem]
  grind

lemma card_le_sum (μ : Multiset ℕ) (hp : ∀ x ∈ μ, x > 0) : μ.card ≤ μ.sum := by
  grind [card_nsmul_le_sum hp]

lemma sum_erase' [DecidableEq α] [AddCommMonoid α] [PartialOrder α] [Sub α] [OrderedSub α]
    [AddLeftReflectLE α] {μ : Multiset α} {a : α} (h : a ∈ μ) : (μ.erase a).sum = μ.sum - a := by
  rw [← sum_erase h]
  simp only [add_tsub_cancel_left]


lemma dedup_eq_range {M : Multiset ℕ} {m : ℕ} (h : ∀ n < m, n ∈ M) (h' : ∀ n ≥ m, n ∉ M) :
    M.dedup = range m := by
  ext n
  rw [count_eq_of_nodup (nodup_dedup M), count_eq_of_nodup (nodup_range m)]
  grind [mem_dedup, mem_range]


lemma erase_eq_zero_iff [DecidableEq α] (s : Multiset α) (a : α) :
    s.erase a = 0 ↔ s = 0 ∨ s = {a} := by
  rw [← coe_toList s, coe_erase, coe_eq_zero, List.erase_eq_nil_iff, coe_eq_zero, coe_eq_singleton]

-- expand to match List.erase_replicate suite of lemmas
lemma erase_replicate [DecidableEq α] {n : ℕ} {a : α} :
    (replicate n a).erase a = replicate (n - 1) a := by
  rw [← Multiset.coe_replicate, Multiset.coe_erase, List.erase_replicate_self,
    Multiset.coe_replicate]

@[simp]
lemma replicate_toList {α : Type*} (a : α) (n : ℕ) :
    (replicate n a).toList = List.replicate n a := by
  simp [List.eq_replicate_iff, mem_replicate]

@[simp]
lemma replicate_eq_zero_iff {α : Type*} (n : ℕ) (a : α) :
    replicate n a = 0 ↔ n = 0 := by
  simp [replicate]

variable {r : α → α → Prop} [DecidableRel r] [IsTrans α r] [Std.Antisymm r] [Std.Total r]

lemma count_sort [DecidableEq α] {M : Multiset α} {x : α} :
    List.count x (M.sort r) = count x M := by
  simp [← coe_count]

lemma sort_perm_toList (s : Multiset α) : (s.sort r).Perm s.toList := by
  nth_rw 1 [← coe_toList s]
  rw [coe_sort]
  exact List.mergeSort_perm _ _

-- model after corresponding Finset lemmas
lemma sort_getElem_zero_eq_max {α : Type*} [LinearOrder α] {μ : Multiset α}
    (hμ : μ.toList ≠ []) :
    (μ.sort (· ≥ ·))[0]'(by simp [card_pos, ← toList_eq_nil, hμ]) =
    μ.toList.max hμ := by
  symm
  rw [List.max_eq_iff]
  simp_rw [mem_toList, ← mem_sort (· ≥ ·)]
  constructor
  · exact List.getElem_mem _
  · intro a ha
    obtain ⟨i, _, hia⟩ := List.getElem_of_mem ha
    rw [← hia]
    exact List.Pairwise.rel_get_of_le (pairwise_sort _ (· ≥ ·)) (by simp)

lemma sort_getElem_zero_eq_min {α : Type*} [LinearOrder α] {μ : Multiset α}
    (hμ : μ.toList ≠ []) :
    (μ.sort (· ≤ ·))[0]'(by simp [card_pos, ← toList_eq_nil, hμ]) =
    μ.toList.min hμ := by
  symm
  rw [List.min_eq_iff]
  simp_rw [mem_toList, ← mem_sort (· ≤ ·)]
  constructor
  · exact List.getElem_mem _
  · intro a ha
    obtain ⟨i, _, hia⟩ := List.getElem_of_mem ha
    rw [← hia]
    exact List.Pairwise.rel_get_of_le (pairwise_sort _ (· ≤ ·)) (by simp)

-- don't upstream
lemma sort_eq_replicate_iff {μ : Multiset α} {n : ℕ} {x : α} :
    (μ.sort r) = List.replicate n x ↔ μ = replicate n x := by
  simp [List.eq_replicate_iff, eq_replicate, length_sort, mem_sort]

@[simp]
lemma sort_sum (r : α → α → Prop) [DecidableRel r] [IsTrans α r]
    [Std.Antisymm r] [Std.Total r] [AddCommMonoid α] (s : Multiset α) :
    (s.sort r).sum = s.sum := by
  rw [← sum_toList s, (sort_perm_toList s).sum_eq]

lemma sort_cons' {x : α} {R : α → α → Prop} {M : Multiset α} [DecidableRel R] [Std.Total R]
    [IsTrans α R] [Std.Antisymm R] (h : ∀ y ∈ M, R y x) :
    (x ::ₘ M).sort R = M.sort R ++ [x] := by
  refine List.Perm.eq_of_pairwise' (Multiset.pairwise_sort _ R) ?_ ?_
  · simpa [List.pairwise_append]
  · rw [← singleton_add, add_comm, ← coe_eq_coe, sort_eq, ← coe_add, coe_singleton, sort_eq]

end Multiset

end
end


/- Source module: KostkaNumbers.Util.FromCounts -/
section
/-
Copyright (c) 2026 Noah Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Walker
-/







section

/-!
The `fromCounts` operation takes a Multiset and interprets it as the tally of some set (in a minimal
way) such that there are more smaller numbers.  For example,
{4, 4, 2, 1, 1}.fromCounts = {0,0,0,0,1,1,1,1,2,2,3,4}.  This is the "inverse" of the `counts`
operation (see `fromCounts_counts`).  This is a natural operation in the context of SSYT, where a
partition μ={4,4,2,1,1} indicates that the tableau has 4 0's, 4 1's, 2 2's, 1 3, and 1 4.  That is,
the content of the tableau should be `μ.fromCounts` (see the definition of `kostkaNumber`).
-/

namespace Multiset

section Counts

variable {μ : Multiset ℕ}

noncomputable
def fromCounts (μ : Multiset ℕ) : Multiset ℕ := ∑ n : {n : ℕ | n < (μ.sort (· ≥ ·)).length},
  replicate ((μ.sort (· ≥ ·))[n.1]'(n.2)) n.1

lemma count_fromCounts {n : ℕ} (h : n < μ.card) :
    count n μ.fromCounts = (μ.sort (· ≥ ·))[n]'(by simp[h]) := by
  simp only [fromCounts, ge_iff_le, count_sum', count_replicate]
  rw [Finset.sum_eq_single_of_mem (⟨n, by simp[h]⟩ :
    {n : ℕ | n < (μ.sort (· ≥ ·)).length}) (Finset.mem_univ _)]
  · simp
  · grind

lemma mem_fromCounts (h0 : 0 ∉ μ) (n : ℕ) (hn : n < μ.card) :
    n ∈ μ.fromCounts := by
  rw [← count_pos, count_fromCounts hn]
  refine Nat.pos_of_ne_zero ?_
  contrapose! h0
  rw [← h0]
  have hn' : n < (μ.sort (· ≥ ·)).length := by simp [hn]
  have hm := List.getElem_mem hn'
  rwa [Multiset.mem_sort] at hm

lemma notMem_fromCounts (μ : Multiset ℕ) (n : ℕ) (hn : n ≥ μ.card) :
    n ∉ μ.fromCounts := by
  rw [← count_pos, fromCounts, count_sum']
  simp [count_replicate]
  lia

lemma mem_fromCounts_iff {n : ℕ} (h0 : 0 ∉ μ) :
    n ∈ μ.fromCounts ↔ n < μ.card := by
  constructor
  · contrapose!
    exact notMem_fromCounts μ n
  · exact mem_fromCounts h0 n

lemma map_count_fromCounts (μ : Multiset ℕ) :
    List.map (fun n ↦ count n μ.fromCounts) (List.range μ.card) = μ.sort (· ≥ ·) :=
  List.ext_getElem (by simp) (by grind [count_fromCounts])

lemma fromCounts_dedup (h0 : 0 ∉ μ) : μ.fromCounts.dedup = range μ.card :=
  dedup_eq_range (mem_fromCounts h0) (notMem_fromCounts μ)

lemma fromCounts_counts (h0 : 0 ∉ μ) : μ.fromCounts.counts = μ := by
  rw [counts, fromCounts_dedup h0, ← coe_range, map_coe, map_count_fromCounts]
  nth_rw 2 [← coe_toList μ]
  rw [coe_eq_coe]
  exact Multiset.sort_perm_toList _

lemma fromCounts_sorted (μ : Multiset ℕ) : List.Pairwise (· ≥ ·) <|
    List.map (fun n => Multiset.count n μ.fromCounts) (List.range μ.card) := by
  rw [map_count_fromCounts]
  exact Multiset.pairwise_sort _ _

@[simp]
lemma fromCounts_card : μ.fromCounts.card = μ.sum := by
  simp only [fromCounts, ge_iff_le, card_sum, card_replicate]
  let e : {n : ℕ | n < (μ.sort (· ≥ ·)).length} → Fin (μ.sort (· ≥ ·)).length :=
    fun n ↦ ⟨n, n.2⟩
  rw [Fintype.sum_bijective e ?_ _ (fun n ↦ (μ.sort (· ≥ ·))[n.1]) ?_]
  · rw [Fin.sum_univ_getElem, ← sum_coe]
    congr
    nth_rw 2 [← coe_toList μ]
    rw [coe_eq_coe]
    exact Multiset.sort_perm_toList _
  · constructor
    · intro n m
      grind
    · intro n
      use ⟨n.1, n.2⟩
  · simp [e]

@[simp] lemma fromCounts_zero : fromCounts 0 = 0 := by
  rw [← Multiset.bot_eq_zero, ← bot_counts_iff]
  refine fromCounts_counts ?_
  rw [bot_eq_zero]
  exact notMem_zero 0

@[simp] lemma fromCounts_bot : fromCounts ⊥ = ⊥ := by simp


lemma ne_zero_of_fromCounts_ne_zero (hμ : μ.fromCounts ≠ 0) : μ ≠ 0 := by
  contrapose! hμ
  rw [hμ, fromCounts_zero]

lemma zero_mem_fromCounts_of_nonempty (hμ : μ.fromCounts ≠ 0) : 0 ∈ μ.fromCounts := by
  have hex : ∃ n, n ∈ μ.fromCounts := by
    contrapose! hμ
    exact eq_zero_of_forall_notMem hμ
  obtain ⟨n, hn⟩ := hex
  rw [← count_pos, count_fromCounts] at hn
  · rw [← count_pos, count_fromCounts]
    · refine lt_of_lt_of_le hn ?_
      refine List.Pairwise.rel_get_of_le (Multiset.pairwise_sort _ (· ≥ ·)) ?_
      simp
    · rw [Nat.pos_iff_ne_zero, ne_eq, card_eq_zero]
      exact ne_zero_of_fromCounts_ne_zero hμ
  · rw [count_pos] at hn
    contrapose! hn
    exact notMem_fromCounts μ n hn

lemma fromCounts_eq_zero_iff (μ : Multiset ℕ) (h0 : 0 ∉ μ) :
    μ.fromCounts = 0 ↔ μ = 0 := by
  rw [← Multiset.bot_eq_zero, ← Multiset.bot_counts_iff, Multiset.fromCounts_counts h0]

lemma fromCounts_eq_nil_iff (h0 : 0 ∉ μ) :
    μ.fromCounts.toList = [] ↔ μ.toList = [] := by
  rw [Multiset.toList_eq_nil, Multiset.toList_eq_nil, Multiset.fromCounts_eq_zero_iff μ h0]

lemma fromCounts_remove_card (h0 : 0 ∉ μ) :
    (μ.fromCounts.remove 0).toFinset.card = μ.card - 1 := by
  by_cases hμ : μ = 0
  · simp [hμ]
  · rw [remove_toFinset_card]
    · nth_rw 2 [← fromCounts_counts h0]
      rw [counts_card]
    · refine zero_mem_fromCounts_of_nonempty ?_
      rwa [ne_eq, fromCounts_eq_zero_iff μ h0]

lemma cons_fromCounts_of_min (n : ℕ) (h : ∀ m ∈ μ, m ≥ n) :
    (n ::ₘ μ).fromCounts = μ.fromCounts + Multiset.replicate n (μ.card) := by
  simp only [fromCounts, ge_iff_le, Multiset.sort_cons' h]
  let n' : {m | m < ((n ::ₘ μ).sort (· ≥ ·)).length} :=
    ⟨((n ::ₘ μ).sort (· ≥ ·)).length - 1, by simp⟩
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ n')]
  conv => lhs; rhs; simp [n']
  rw [add_left_inj]
  let e : (a : {m | m < ((n ::ₘ μ).sort (· ≥ ·)).length}) →
    (a ∈ (Finset.univ.erase n')) → {m | m < (μ.sort (· ≥ ·)).length} :=
    fun a ha ↦ ⟨a.1, by
      have ha' := a.2
      simp [n', ← Subtype.coe_inj] at ha ha'
      simp [Nat.lt_of_le_of_ne ha' ha]
      ⟩
  refine Finset.sum_bij e ?_ ?_ ?_ ?_
  · simp [e]
  · simp [e]
  · simp only [Finset.mem_univ, Finset.mem_erase, ne_eq, and_true, Subtype.exists, ge_iff_le,
      length_sort, card_cons, Order.lt_add_one_iff, forall_const, Subtype.forall, Subtype.mk.injEq,
      exists_prop, exists_and_right, exists_eq_right, e]
    intro a ha
    use (by grind)
    simp [n']
    grind
  · simp only [Finset.mem_erase, ne_eq, Finset.mem_univ, and_true, Subtype.forall, ge_iff_le,
      length_sort, card_cons, Order.lt_add_one_iff, e]
    intro a ha ha'
    rw [List.getElem_append_left]

lemma erase_fromCounts_of_min (μ : Multiset ℕ) (hμ : μ.toList ≠ []) :
    (μ.erase (μ.toList.min hμ)).fromCounts = μ.fromCounts.remove (μ.card - 1) := by
  have hm : μ.toList.min hμ ∈ μ.toList := List.min_mem hμ
  rw [mem_toList] at hm
  nth_rw 3 [← cons_erase hm]
  rw [cons_fromCounts_of_min (μ.toList.min hμ), remove_add, remove_of_notMem, remove_replicate,
    empty_eq_zero, add_zero]
  · exact Multiset.card_erase_of_mem hm
  · exact notMem_fromCounts _ _ <| by simp [Multiset.card_erase_of_mem hm]
  · intro m hm
    exact List.min_le_of_mem <| by simp [mem_of_mem_erase hm]

lemma fromCounts_singleton {n : ℕ} (hn : n ≠ 0) :
    ({n} : Multiset ℕ).fromCounts = Multiset.replicate n 0 := by
  have hn0 : 0 ∉ ({n} : Multiset ℕ) := by
    rw [mem_singleton]
    exact hn.symm
  simp only [fromCounts, ge_iff_le, sort_singleton, List.getElem_singleton]
  rw [Finset.sum_eq_single_of_mem ⟨0, by simp⟩ (Finset.mem_univ _) (by simp; grind)]

end Counts

end Multiset

end
end


/- Source module: KostkaNumbers.Util.SemistandardYoungTableau -/
section
/-
Copyright (c) 2026 Noah Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Walker
-/



/-!
This file contains some basic results about SemistandardYoungTableau that I need that are not in
Mathlib. I'll upstream these to Mathlib at some point.
-/

section

open YoungDiagram

namespace SemistandardYoungTableau

variable {γ : YoungDiagram}

lemma entry_eq_zero_of_bot (T : SemistandardYoungTableau γ) {i j : ℕ} (h : γ = ⊥) : T i j = 0 :=
  T.zeros <| h ▸ notMem_bot _

lemma col_le_entry {i j : ℕ} (h : (i, j) ∈ γ) (T : SemistandardYoungTableau γ) : i ≤ T i j := by
  induction i with
  | zero => exact Nat.zero_le _
  | succ i ih =>
    exact lt_of_le_of_lt (ih <| γ.up_left_mem (lt_add_one i).le (by rfl) h)
      <| T.col_strict (lt_add_one i) h

end SemistandardYoungTableau

end
end


/- Source module: KostkaNumbers.Util.Diagrams -/
section
/-
Copyright (c) 2026 Noah Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Walker
-/




/-!
This file contains some basic results about YoungDiagrams that I need that are not in Mathlib.
I intend to upstream most of these results to Mathlib.
-/

section

namespace YoungDiagram

variable {γ : YoungDiagram}

@[simp] lemma bot_card : (⊥ : YoungDiagram).card = 0 := by simp

@[simp] lemma bot_rowLens : (⊥ : YoungDiagram).rowLens = [] := by
  simp [rowLens, colLen]

lemma eq_bot_iff_forall_notMem : γ = ⊥ ↔ ∀ i j : ℕ, (i, j) ∉ γ := by
  simp [YoungDiagram.ext_iff, Finset.eq_empty_iff_forall_notMem]

lemma eq_bot_iff_card_eq_zero : γ = ⊥ ↔ γ.card = 0 := by
  simp [YoungDiagram.ext_iff]

lemma eq_bot_iff_zero_zero_notMem : γ = ⊥ ↔ (0, 0) ∉ γ := by
  rw [eq_bot_iff_forall_notMem]
  refine ⟨fun h ↦ h 0 0, fun h i j ↦ ?_⟩
  contrapose! h
  exact γ.up_left_mem i.zero_le j.zero_le h

lemma eq_iff_rowLens_eq {γ γ' : YoungDiagram} : γ = γ' ↔ γ.rowLens = γ'.rowLens := by
  simp_rw [← equivListRowLens_apply_coe, Subtype.coe_inj, equivListRowLens.apply_eq_iff_eq]

lemma eq_iff_rowLens_eq' {γ γ' : YoungDiagram} :
    γ = γ' ↔ Multiset.ofList γ.rowLens = Multiset.ofList γ'.rowLens := by
  rw [eq_iff_rowLens_eq, Multiset.coe_eq_coe,
    List.perm_iff_eq_of_sortedGE γ.rowLens_sorted γ'.rowLens_sorted]

lemma colLen_mono {γ γ' : YoungDiagram} (h : γ' ≤ γ) (j : ℕ) : γ'.colLen j ≤ γ.colLen j := by
  by_contra!
  rw [← mem_iff_lt_colLen] at this
  apply h at this
  simp [mem_iff_lt_colLen] at this

lemma rowLen_mono {γ γ' : YoungDiagram} (h : γ' ≤ γ) (i : ℕ) : γ'.rowLen i ≤ γ.rowLen i := by
  by_contra!
  rw [← mem_iff_lt_rowLen] at this
  apply h at this
  simp [mem_iff_lt_rowLen] at this

@[simp]
lemma rowLen_bot : (⊥ : YoungDiagram).rowLen = 0 := by
  ext i
  rw [Pi.zero_apply, ← le_zero_iff, ← Std.not_lt, ← mem_iff_lt_rowLen]
  exact notMem_bot _

@[simp]
lemma colLen_bot : (⊥ : YoungDiagram).colLen = 0 := by
  ext i
  rw [Pi.zero_apply, ← le_zero_iff, ← Std.not_lt, ← mem_iff_lt_colLen]
  exact notMem_bot _

lemma card_sdiff {γ' : YoungDiagram} (h : γ' ≤ γ) :
    (γ.cells \ γ'.cells).card = γ.card - γ'.card := by
  rw [YoungDiagram.card, Finset.card_sdiff_of_subset h]

lemma row_transpose (γ : YoungDiagram) (i : ℕ) : γ.transpose.row i =
    Finset.image Prod.swap (γ.col i) := by
  ext x
  simp [row, col]
  grind

lemma col_transpose (γ : YoungDiagram) (i : ℕ) : γ.transpose.col i =
    Finset.image Prod.swap (γ.row i) := by
  nth_rw 2 [← transpose_transpose γ]
  rw [row_transpose γ.transpose, Finset.image_image, Prod.swap_swap_eq, Finset.image_id]

lemma col_eq_image_swap_transpose {γ : YoungDiagram} (i : ℕ) : γ.col i =
    Finset.image Prod.swap (γ.transpose.row i) := by
  rw [row_transpose, Finset.image_image, Prod.swap_swap_eq, Finset.image_id]

lemma row_eq_image_swap_transpose {γ : YoungDiagram} (i : ℕ) : γ.row i =
    Finset.image Prod.swap (γ.transpose.col i) := by
  rw [col_transpose, Finset.image_image, Prod.swap_swap_eq, Finset.image_id]

end YoungDiagram

end
end


/- Source module: KostkaNumbers.Defs -/
section
/-
Copyright (c) 2026 Noah Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Walker
-/







/-
This file defines horizontal and hook diagrams (of shape (n) and (n-1,1)).  It also defines the
content of a SSYT and uses this to define Kostka numbers.  The intention is that this file contains
the main definitions that one needs to check to verify that the statement of `kostka_inequality` in
the Sum file is accurate.
-/

section

open SemistandardYoungTableau YoungDiagram

-- Various special young diagrams

namespace YoungDiagram

/-- The Young Diagram for (n). -/
def horizontalDiagram (n : ℕ) := ofRowLens [n] <| (List.pairwise_singleton _ n).sortedGE

@[simp]
lemma mem_horizontalDiagram (n : ℕ) (x : ℕ × ℕ) : x ∈ horizontalDiagram n ↔
    x.1 = 0 ∧ x.2 < n := by
  simp [horizontalDiagram, ofRowLens, YoungDiagram.cellsOfRowLens]
  grind

@[simp]
lemma horizontalDiagram_zero : horizontalDiagram 0 = ⊥ := by
  ext x
  simp [horizontalDiagram, mem_ofRowLens]

lemma horizontalDiagram_succ (n : ℕ) :
    (horizontalDiagram (n + 1)).cells.val = (0 , n) ::ₘ (horizontalDiagram n).cells.val := by
  simp [horizontalDiagram, ofRowLens, YoungDiagram.cellsOfRowLens]

@[simp]
lemma horizontalDiagram_card {n : ℕ} : (horizontalDiagram n).card = n := by
  simp [horizontalDiagram, ofRowLens, YoungDiagram.cellsOfRowLens, YoungDiagram.card]

@[simp]
lemma horizontalDiagram_rowLens {n : ℕ} (hn : n ≠ 0) : (horizontalDiagram n).rowLens = [n] := by
  rw [horizontalDiagram, rowLens_ofRowLens_eq_self]
  simp [Nat.pos_iff_ne_zero, hn]

/-- The Young Diagram for (n - 1, 1) when n ≥ 2 and junk values for n = 0, 1. -/
def hookDiagram (n : ℕ) := if h0 : n = 0 then (⊥ : YoungDiagram)
  else if h1 : n = 1 then horizontalDiagram 1
  else ofRowLens [n - 1, 1] (List.Pairwise.sortedGE (by grind))

@[simp] lemma hookDiagram_zero : hookDiagram 0 = ⊥ := by simp [hookDiagram]

@[simp] lemma hookDiagram_one : hookDiagram 1 = horizontalDiagram 1 := by simp [hookDiagram]

@[simp]
lemma hookDiagram_rowLens {n : ℕ} (hn : n ≥ 2) : (hookDiagram n).rowLens = [n - 1, 1] := by
  grind [hookDiagram, rowLens_ofRowLens_eq_self]

@[simp]
lemma mem_hookDiagram (n : ℕ) {x : ℕ × ℕ} (hn : n ≥ 2) : x ∈ hookDiagram n ↔
    (x.1 = 1 ∧ x.2 = 0) ∨ (x.1 = 0 ∧ x.2 < n - 1) := by
  simp [hookDiagram, Nat.ne_zero_of_lt hn, Nat.ne_of_lt' hn, ofRowLens, YoungDiagram.cellsOfRowLens]
  grind

end YoungDiagram

namespace SemistandardYoungTableau

section Content

variable {γ : YoungDiagram} {T : SemistandardYoungTableau γ}

def content (T : SemistandardYoungTableau γ) :=
  Multiset.map (fun (i, j) => T i j) (γ.cells).val

@[simp] lemma content_card_eq_card : T.content.card = γ.card := by simp [content]

@[simp] lemma content_eq_bot_iff : T.content = ⊥ ↔ γ = ⊥ := by
  simp [content, eq_bot_iff_card_eq_zero]

lemma mem_content_of_mem {i j : ℕ} (h : (i, j) ∈ γ) : T i j ∈ T.content := by
  simp only [content, Multiset.mem_map, Finset.mem_val, YoungDiagram.mem_cells, Prod.exists]
  use i, j

lemma mem_content_of_nonzero {i j : ℕ} (h : T i j ≠ 0) : T i j ∈ T.content := by
  refine mem_content_of_mem ?_
  contrapose! h
  exact T.zeros h

lemma entry_le_max {γ : YoungDiagram} {T : SemistandardYoungTableau γ} {i j : ℕ}
    (hTc : T.content.toList ≠ []) :
    T i j ≤ T.content.toList.max hTc := by
  by_cases hij : T i j = 0
  · exact hij ▸ Nat.zero_le _
  · exact List.le_max_of_mem (by simp [mem_content_of_nonzero hij])

end Content

end SemistandardYoungTableau

namespace Kostka

variable {γ : YoungDiagram} {μ : Multiset ℕ} {T : SemistandardYoungTableau γ}

def SemistandardYoungTableauWithContent (γ : YoungDiagram) (μ : Multiset ℕ) :=
  {T : SemistandardYoungTableau γ | T.content = μ.fromCounts}

lemma finite_SSYTWithContent (γ : YoungDiagram) (μ : Multiset ℕ) :
    Finite (SemistandardYoungTableauWithContent γ μ) := by
  let f : {T : SemistandardYoungTableau γ | T.content = μ.fromCounts} →
    (γ.cells → {n // n ∈ μ.fromCounts}) := fun ⟨T, hT⟩ ↦ (fun ⟨x, hx⟩ ↦ ⟨T x.1 x.2,
      hT ▸ mem_content_of_mem hx⟩)
  refine Finite.of_injective f ?_
  intro ⟨T, hT⟩ ⟨T', hT'⟩ hf
  simp only [Subtype.mk.injEq]
  ext i j
  by_cases hij : (i, j) ∈ γ
  · have hf : (f ⟨T, hT⟩) ⟨(i, j), hij⟩ = (f ⟨T', hT'⟩) ⟨(i, j), hij⟩ := congrFun hf ⟨(i, j), hij⟩
    simpa [Set.coe_ofPred, Set.mem_ofPred_eq, Subtype.mk.injEq, f] using hf
  · rw [T.zeros hij, T'.zeros hij]

noncomputable
instance : Fintype (SemistandardYoungTableauWithContent γ μ) := by
  have := finite_SSYTWithContent
  exact Fintype.ofFinite _

noncomputable def kostkaNumber (γ : YoungDiagram) (μ : Multiset ℕ) :=
  Nat.card {T : SemistandardYoungTableau γ | T.content = μ.fromCounts}

lemma kostka_eq_card_SSYTWithContent : kostkaNumber γ μ =
    Nat.card (SemistandardYoungTableauWithContent γ μ) := by
  simp [kostkaNumber, SemistandardYoungTableauWithContent]

theorem kostka_eq_zero {γ : YoungDiagram} {μ : Multiset ℕ}
    (h : ∀ T : SemistandardYoungTableau γ, T.content ≠ μ.fromCounts) : kostkaNumber γ μ = 0 := by
  rw [kostkaNumber, Nat.card_eq_zero]
  left
  exact Subtype.isEmpty_of_false h

theorem kostka_eq_zero_iff_forall_not {γ : YoungDiagram} {μ : Multiset ℕ} :
    kostkaNumber γ μ = 0 ↔ ∀ T : SemistandardYoungTableau γ, T.content ≠ μ.fromCounts := by
  constructor
  · intro h
    contrapose! h
    simp only [kostkaNumber, Set.coe_ofPred, nonempty_subtype, h, ne_eq, Nat.card_eq_zero,
      not_isEmpty_of_nonempty, false_or, not_infinite_iff_finite]
    exact finite_SSYTWithContent γ μ
  · exact kostka_eq_zero

theorem kostka_ne_card (γ : YoungDiagram) (μ : Multiset ℕ) (h : γ.card ≠ μ.sum) :
    kostkaNumber γ μ = 0 := by
  refine kostka_eq_zero ?_
  intro T
  contrapose! h
  rw [← Multiset.fromCounts_card, ← h]
  exact content_card_eq_card.symm

end Kostka

end
end


/- Source module: KostkaNumbers.HookLength.HookLength -/
section
/-
Copyright (c) 2026 Noah Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Walker
-/




/-!
This files has three definitions and proves lemmas about them and their interactions:
  * the hook length of a cell in a Young diagram
  * the corners of a Young diagram
  * the hook of a cell in a Young diagram
-/

section

open YoungDiagram SemistandardYoungTableau

namespace YoungDiagram

def hookLength (γ : YoungDiagram) (x : ℕ × ℕ) : ℕ :=
  (γ.rowLen x.1 - (x.2 + 1)) + (γ.colLen x.2 - (x.1 + 1)) + 1

lemma hookLength_def (γ : YoungDiagram) (x : ℕ × ℕ) :
    γ.hookLength x = (γ.rowLen x.1 - (x.2 + 1)) + (γ.colLen x.2 - (x.1 + 1)) + 1 := by rfl

lemma hookLength_eq_one_of_notMem (γ : YoungDiagram) {x : ℕ × ℕ} (hx : x ∉ γ) :
    γ.hookLength x = 1 := by
  simp [hookLength]
  grind [mem_iff_lt_colLen, mem_iff_lt_rowLen]

def corners (γ : YoungDiagram) : Finset (ℕ × ℕ) :=
    {x ∈ γ.cells | x.2 + 1 = γ.rowLen x.1 ∧ x.1 + 1 = γ.colLen x.2}

lemma corners_le {γ : YoungDiagram} : γ.corners ≤ γ.cells := by
  simp [corners]

@[simp]
lemma corners_bot : (⊥ : YoungDiagram).corners = ∅ := by simp [corners]

lemma ne_bot_of_mem_corners {γ : YoungDiagram} {x : ℕ × ℕ} (hx : x ∈ γ.corners) : γ ≠ ⊥ := by
  apply corners_le at hx
  rw [ne_eq, eq_bot_iff_forall_notMem]
  push Not
  use x.1, x.2
  exact hx

lemma not_le_of_mem_corners {γ : YoungDiagram} {x y : ℕ × ℕ} (hx : x ∈ γ.corners)
    (hy : y ∈ γ.corners) (hxy : x ≠ y) :
    ¬ x ≤ y := by
  rw [corners, Finset.mem_filter, mem_cells] at hx hy
  rw [Prod.le_def, not_and]
  intro h
  apply γ.rowLen_anti at h
  grind

def hook (γ : YoungDiagram) (x : ℕ × ℕ) : Finset (ℕ × ℕ) :=
    {y ∈ γ.cells | ((y.1 = x.1 ∧ y.2 ≥ x.2) ∨ (y.1 ≥ x.1 ∧ y.2 = x.2))}

@[simp]
lemma hook_of_notMem (γ : YoungDiagram) {x : ℕ × ℕ} (hx : x ∉ γ) :
    γ.hook x = ∅ := by
  simp only [hook, ge_iff_le, Finset.filter_eq_empty_iff, mem_cells, Prod.forall]
  grind [γ.up_left_mem]

lemma self_mem_hook (γ : YoungDiagram) (x : ℕ × ℕ) (h : x ∈ γ) :
    x ∈ γ.hook x := by simp [hook, h]

lemma mem_of_mem_hook (γ : YoungDiagram) {x y : ℕ × ℕ} (h : x ∈ γ.hook y) : x ∈ γ := by
  simp_all [hook]

lemma hook_card_eq_hookLength (γ : YoungDiagram) (x : ℕ × ℕ) (h : x ∈ γ) :
    (γ.hook x).card = γ.hookLength x := by
  let f : ℕ × ℕ → ℕ :=
    fun y ↦ if (y.1 = x.1 ∧ y.2 ≥ x.2) then y.2 - x.2 else γ.rowLen x.1 - (x.2 + 1) + y.1 - x.1
  conv => rhs; rw [← Finset.card_range (γ.hookLength x)]
  refine Set.BijOn.finsetCard_eq f ?_
  constructor
  · intro x hx
    rw [Finset.mem_coe] at hx
    simp only [hookLength_def, Finset.coe_range, ge_iff_le, Set.mem_Iio, f]
    grind [γ.mem_iff_lt_colLen, γ.mem_iff_lt_rowLen, hook, mem_cells]
  constructor
  · grind [γ.mem_iff_lt_rowLen, hook, mem_cells, Set.InjOn]
  · intro a
    simp only [hookLength_def, Finset.coe_range, Set.mem_Iio, ge_iff_le, hook, Finset.coe_filter,
      mem_cells, Set.mem_image, Set.mem_ofPred_eq, Prod.exists, f]
    intro ha
    by_cases hah : a ≤ γ.rowLen x.1 - (x.2 + 1)
    · use x.1, (a + x.2)
      simp only [le_add_iff_nonneg_left, zero_le, and_self, le_refl, Nat.add_eq_right, true_and,
        true_or, and_true, ↓reduceIte, add_tsub_cancel_right]
      rw [γ.mem_iff_lt_rowLen] at h ⊢
      lia
    · use (a - (γ.rowLen x.1 - (x.2 + 1)) + x.1), x.2
      grind [γ.mem_iff_lt_colLen]

lemma corner_iff_hookLength_eq_one (γ : YoungDiagram) (x : ℕ × ℕ) (hx : x ∈ γ) :
    (x.2 + 1 = γ.rowLen x.1 ∧ x.1 + 1 = γ.colLen x.2) ↔ γ.hookLength x = 1 := by
  grind [γ.mem_iff_lt_rowLen, γ.mem_iff_lt_colLen, hookLength_def]

lemma mem_corners_iff_hookLength_eq_one (γ : YoungDiagram) {x : ℕ × ℕ} (hx : x ∈ γ) :
    x ∈ γ.corners ↔ γ.hookLength x = 1 := by
  simp [← corner_iff_hookLength_eq_one _ _ hx, corners, hx]

lemma mem_corners_iff_hook_eq_self (γ : YoungDiagram) {x : ℕ × ℕ} :
    x ∈ γ.corners ↔ γ.hook x = {x} := by
  by_cases! hx : x ∈ γ
  · rw [mem_corners_iff_hookLength_eq_one γ hx, ← hook_card_eq_hookLength _ _ hx,
      Finset.card_eq_one]
    grind [self_mem_hook]
  · simp [hx, corners]

lemma hookLength_ne_zero (γ : YoungDiagram) (x : ℕ × ℕ) : γ.hookLength x ≠ 0 := by
  by_cases! h : x ∈ γ
  · rw [← Nat.pos_iff_ne_zero, ← hook_card_eq_hookLength _ _ h]
    refine Finset.card_pos.mpr ?_
    use x
    exact γ.self_mem_hook x h
  · rw [hookLength_eq_one_of_notMem _ h]
    exact zero_ne_one.symm

lemma exists_hook_of_hookLength_ne_one (γ : YoungDiagram) (x : ℕ × ℕ) (hij : x ∈ γ)
    (h : γ.hookLength x ≠ 1) : ∃ y ∈ γ.hook x, y ≠ x := by
  refine Finset.exists_mem_ne ?_ x
  rw [hook_card_eq_hookLength _ _ hij]
  have hhl := γ.hookLength_ne_zero x
  lia

lemma le_of_mem_hook (γ : YoungDiagram) {x y : ℕ × ℕ} (h : x ∈ γ.hook y) : y ≤ x := by
  grind [Prod.le_def, hook]

lemma mem_of_mem_hook_right (γ : YoungDiagram) {x y : ℕ × ℕ} (h : y ∈ γ.hook x) : x ∈ γ := by
  have hxy : x ≤ y := le_of_mem_hook γ h
  rw [Prod.le_def] at hxy
  exact γ.up_left_mem hxy.1 hxy.2 (γ.mem_of_mem_hook h)

end YoungDiagram

end
end


/- Source module: KostkaNumbers.HookLength.HookPath.Basic -/
section
/-
Copyright (c) 2026 Noah Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Walker
-/





section

open MeasureTheory
open scoped ENNReal NNReal

/-
The definition and basic properties of a hook path, which is a list of cells in a young diagram such
that each cell is in the hook of the previous one.  This can be thought of as the output of a trial
in the experiment defined in the GNW paper.
-/

namespace YoungDiagram

variable (γ : YoungDiagram)

structure hookPath where
  path : List (ℕ × ℕ)
  ne_nil : path ≠ []
  isPath : ∀ i, ∀ hi : i < path.length - 1, path[i + 1] ∈ γ.hook path[i]
  nodup : path.Nodup
  mem_cells : ∀ i, ∀ hi : i < path.length, path[i] ∈ γ.cells

lemma hookPath.eq_of_path_eq {p q : γ.hookPath} (h : p.path = q.path) : p = q := by
  cases p
  cases q
  cases h
  rfl

abbrev cornerHookPath := {p : γ.hookPath // p.path.getLast p.ne_nil ∈ γ.corners}

instance : MeasurableSpace γ.hookPath := ⊤

variable {γ : YoungDiagram}

@[simp]
lemma hookPath_ne_nil (p : γ.hookPath) : p.path ≠ [] := p.ne_nil

@[simp]
lemma hookPath_length_ne_zero (p : γ.hookPath) : p.path.length ≠ 0 := by simp

lemma mem_cells_of_mem_hookPath {p : γ.hookPath} {x : ℕ × ℕ} (hx : x ∈ p.path) : x ∈ γ.cells := by
  obtain ⟨i, hi⟩ := List.get_of_mem hx
  rw [← hi, List.get_eq_getElem]
  exact p.mem_cells _ _

lemma getLast_mem (p : γ.hookPath) : p.path.getLast p.ne_nil ∈ γ :=
  mem_cells_of_mem_hookPath <| List.getLast_mem p.ne_nil

lemma hookPath_length_le_card (p : γ.hookPath) : p.path.length ≤ γ.card := by
  rw [← List.length_attachWith (p := fun x ↦ x ∈ γ.cells)
    (H := (fun _ hx ↦ mem_cells_of_mem_hookPath hx)), YoungDiagram.card, ← Nat.card_eq_finsetCard]
  exact (List.Nodup.pmap (by simp) p.nodup).length_le_natCard

lemma zero_zero_mem_of_hookPath (p : γ.hookPath) : (0, 0) ∈ γ.cells := by
  have h0 : 0 < p.path.length := by
    rw [List.length_pos_iff]
    exact p.ne_nil
  exact γ.up_left_mem zero_le zero_le <| p.mem_cells 0 h0

lemma ne_bot_of_hookPath (p : γ.hookPath) : γ ≠ ⊥ := by
  rw [ne_eq, eq_bot_iff_zero_zero_notMem]
  push Not
  exact zero_zero_mem_of_hookPath p

lemma path_lt_succ {p : γ.hookPath} (i : ℕ) (hi : i + 1 < p.path.length) :
    p.path[i] < p.path[i + 1] := by
  refine lt_of_le_of_ne ?_ ?_
  · exact le_of_mem_hook γ <| p.isPath _ (by lia)
  · rw [ne_eq, List.Nodup.getElem_inj_iff p.nodup]
    exact Nat.ne_add_one i

lemma path_strict_mono {p : γ.hookPath} {i j : ℕ} (hj : j < p.path.length) (hij : i < j) :
    p.path[i] < p.path[j] := by
  by_cases! hi : i + 1 = j
  · subst hi
    exact path_lt_succ i hj
  · refine lt_trans (path_lt_succ i (by lia)) ?_
    exact path_strict_mono hj (by lia)

lemma path_mono {p : γ.hookPath} {i j : ℕ} (hj : j < p.path.length) (hij : i ≤ j) :
    p.path[i] ≤ p.path[j] := by
  by_cases! hij' : i = j
  · rw! [hij']
    rfl
  · exact (path_strict_mono hj (by lia)).le

lemma path_sortedLE {p : γ.hookPath} : p.path.SortedLE := by
  rw [List.sortedLE_iff_getElem_le_getElem_of_le]
  intro i j hi
  exact path_mono

lemma head_le {p : γ.hookPath} {x : ℕ × ℕ} (hx : x ∈ p.path) :
    p.path.head p.ne_nil ≤ x := by
  obtain ⟨i, hi⟩ := List.get_of_mem hx
  rw [← hi, List.head_eq_getElem, List.get_eq_getElem]
  exact path_mono _ (Nat.zero_le _)

lemma notMem_path_of_mem_hook {p : γ.hookPath} {x : ℕ × ℕ}
    (hx : x ∈ γ.hook (p.path.getLast p.ne_nil)) (hx' : x ≠ p.path.getLast p.ne_nil) :
    x ∉ p.path := by
  contrapose! hx'
  obtain ⟨i, hi⟩ := List.get_of_mem hx'
  subst hi
  simp only [List.getLast_eq_getElem, List.get_eq_getElem] at hx ⊢
  suffices i.1 = p.path.length - 1 by simp [this]
  refine le_antisymm (by lia) ?_
  apply le_of_mem_hook at hx
  contrapose! hx
  exact Std.not_le_of_gt <| path_strict_mono (by lia) hx

lemma head_le_of_mem_path {p : γ.hookPath} {x : ℕ × ℕ} (hx : x ∈ p.path) :
    p.path.head p.ne_nil ≤ x := by
  obtain ⟨i, hi⟩ := List.get_of_mem hx
  rw [← hi, List.head_eq_getElem, List.get_eq_getElem]
  exact path_mono _ (Nat.zero_le _)

lemma le_getLast_of_mem_path {p : γ.hookPath} {x : ℕ × ℕ} (hx : x ∈ p.path) :
    x ≤ p.path.getLast p.ne_nil := by
  obtain ⟨i, hi⟩ := List.get_of_mem hx
  rw [List.getLast_eq_getElem, ← hi, List.get_eq_getElem]
  exact path_mono _ (by lia)

def toCellList : γ.hookPath → { l : List γ.cells // l.Nodup } := fun p ↦
  ⟨List.attachWith p.path (fun x ↦ x ∈ γ.cells) (fun _ hx ↦ mem_cells_of_mem_hookPath hx),
  List.Nodup.pmap (by simp) p.nodup⟩

lemma toCellList_injective : Function.Injective γ.toCellList := by
  intro p q hpq
  apply hookPath.eq_of_path_eq
  have heq := congrArg (fun v : {l : List γ.cells // l.Nodup} ↦ List.unattach v.val) hpq
  simpa only [toCellList, List.unattach_attachWith] using heq

noncomputable
instance : Fintype γ.hookPath := Fintype.ofInjective γ.toCellList toCellList_injective

lemma path_length_eq_one_card : ({p : γ.hookPath | p.path.length = 1} : Finset _).card =
    γ.card := by
  unfold YoungDiagram.card
  refine Finset.card_bij (fun p hp ↦ p.path.head p.ne_nil) ?_ ?_ ?_
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_cells]
    intro p hp
    rw [List.head_eq_getElem]
    exact p.mem_cells 0 (by lia)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.head_eq_getElem]
    intro p hp q hq hpq
    apply hookPath.eq_of_path_eq
    exact List.ext_getElem (by lia) (by grind)
  · simp only [mem_cells, Finset.mem_filter, Finset.mem_univ, true_and, exists_prop, Prod.forall]
    intro a b hab
    use ⟨[(a, b)], by simp, by simp, by simp, by simp [hab]⟩
    simp


lemma hookLength_path_getElem_ne_zero {p : γ.hookPath} (i : ℕ) (hi : i < p.path.length - 1)
    (hpc : p.path.getLast p.ne_nil ∈ γ.corners) :
    (γ.hookLength (p.path[i]'(by lia)) - 1 : ℝ≥0) ≠ 0 := by
  rw [ne_eq, ← Nat.cast_one, ← Nat.cast_tsub, Nat.cast_eq_zero]
  suffices γ.hookLength (p.path[i]) ≠ 1 by grind [hookLength_ne_zero]
  rw [ne_eq, ← mem_corners_iff_hookLength_eq_one]
  · by_contra! hh
    have hph : p.path[i] ≠ p.path.getLast p.ne_nil := by
      rw [List.getLast_eq_getElem p.ne_nil, ne_eq, List.getElem_inj p.nodup]
      lia
    have h := not_le_of_mem_corners hh hpc hph
    refine h ?_
    rw [List.getLast_eq_getElem p.ne_nil]
    exact path_mono _ (by lia)
  · rw [← mem_cells]
    exact mem_cells_of_mem_hookPath <| List.getElem_mem _

lemma hookLength_head_sub_one_ne_zero {p : γ.hookPath} (hp : p.path.length > 1)
    (hpc : p.path.getLast p.ne_nil ∈ γ.corners) :
    (γ.hookLength (p.path.head p.ne_nil) - 1 : ℝ≥0) ≠ 0 := by
  rw [List.head_eq_getElem]
  exact hookLength_path_getElem_ne_zero 0 (by lia) hpc

end YoungDiagram

end
end


/- Source module: KostkaNumbers.HookLength.HookPath.Projections -/
section
/-
Copyright (c) 2026 Noah Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Walker
-/




/-!
Define the horizontal and vertical projections of a hook path as the set of
x-coordinates and y-coordinates, respectively, that the hook path reaches.
-/

section

namespace YoungDiagram

variable {γ : YoungDiagram}

abbrev hookPath.horizontal (p : γ.hookPath) :=
  {x.1 | x ∈ p.path} \ {(p.path.getLast p.ne_nil).1}
abbrev hookPath.vertical (p : γ.hookPath) :=
  {x.2 | x ∈ p.path} \ {(p.path.getLast p.ne_nil).2}

instance (p : γ.hookPath) : Fintype (p.horizontal) := by
  suffices Fintype {x.1 | x ∈ p.path} by infer_instance
  let f : {x // x ∈ p.path} → {x.1 | x ∈ p.path} := fun ⟨x, hx⟩ ↦ ⟨x.1, by
    rw [Set.mem_ofPred]
    use x⟩
  refine Fintype.ofSurjective f ?_
  intro ⟨x, hx⟩
  simp [f]
  grind

instance (p : γ.hookPath) : Fintype (p.vertical) := by
  suffices Fintype {x.2 | x ∈ p.path} by infer_instance
  let f : {x // x ∈ p.path} → {x.2 | x ∈ p.path} := fun ⟨x, hx⟩ ↦ ⟨x.2, by
    rw [Set.mem_ofPred]
    use x⟩
  refine Fintype.ofSurjective f ?_
  intro ⟨x, hx⟩
  simp [f]
  grind

lemma head_fst_eq_horz_min {p : γ.hookPath} {s : Finset ℕ} (hs : p.horizontal = s)
    (hs0 : s.Nonempty) :
    (p.path.head p.ne_nil).1 = s.min' hs0 := by
  symm
  rw [Finset.min'_eq_iff]
  constructor
  · simp only [← Finset.mem_coe, ← hs, Set.mem_sdiff, Prod.exists, exists_and_right,
      exists_eq_right, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · use (p.path.head p.ne_nil).2
      exact List.head_mem _
    · obtain ⟨i, hi⟩ := hs0
      simp only [← Finset.mem_coe, ← hs, Set.mem_sdiff, Prod.exists, exists_and_right,
        exists_eq_right, Set.mem_ofPred_eq, Set.mem_singleton_iff] at hi
      obtain ⟨⟨j, hij⟩, hi⟩ := hi
      have hh := head_le_of_mem_path hij
      have hl := le_getLast_of_mem_path hij
      rw [Prod.le_def] at hh hl
      lia
  · intro i hi
    simp only [← Finset.mem_coe, ← hs, Set.mem_sdiff, Prod.exists, exists_and_right,
      exists_eq_right, Set.mem_ofPred_eq, Set.mem_singleton_iff] at hi
    obtain ⟨⟨j, hij⟩, hi⟩ := hi
    have hh := head_le_of_mem_path hij
    rw [Prod.le_def] at hh
    exact hh.1

lemma head_snd_eq_vert_min {p : γ.hookPath} {t : Finset ℕ} (ht : p.vertical = t)
    (ht0 : t.Nonempty) :
    (p.path.head p.ne_nil).2 = t.min' ht0 := by
  symm
  rw [Finset.min'_eq_iff]
  constructor
  · simp only [← Finset.mem_coe, ← ht, Set.mem_sdiff, Prod.exists, exists_eq_right,
      Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · use (p.path.head p.ne_nil).1
      exact List.head_mem _
    · obtain ⟨j, hj⟩ := ht0
      simp only [← Finset.mem_coe, ← ht, Set.mem_sdiff, Prod.exists, exists_eq_right,
        Set.mem_ofPred_eq, Set.mem_singleton_iff] at hj
      obtain ⟨⟨i, hij⟩, hj⟩ := hj
      have hh := head_le_of_mem_path hij
      have hl := le_getLast_of_mem_path hij
      rw [Prod.le_def] at hh hl
      lia
  · intro j hj
    simp only [← Finset.mem_coe, ← ht, Set.mem_sdiff, Prod.exists, exists_eq_right,
      Set.mem_ofPred_eq, Set.mem_singleton_iff] at hj
    obtain ⟨⟨i, hij⟩, hj⟩ := hj
    have hh := head_le_of_mem_path hij
    rw [Prod.le_def] at hh
    exact hh.2

lemma head_eq_horz_vert_min {p : γ.hookPath} {s t : Finset ℕ} (hs : p.horizontal = s)
    (ht : p.vertical = t) (hs0 : s.Nonempty) (ht0 : t.Nonempty) :
    p.path.head p.ne_nil = (s.min' hs0, t.min' ht0) := by
  simp [Prod.ext_iff, head_fst_eq_horz_min hs hs0, head_snd_eq_vert_min ht ht0]

-- upstream (PR'd)
lemma Finset.card_le_card_of_surjective {α β : Type*} {s : Finset α} {t : Finset β} {f : ↥s → ↥t}
    (hf : Function.Surjective f) :
    t.card ≤ s.card := by
  rcases t.eq_empty_or_nonempty with rfl | ⟨b₀, hb₀⟩
  · simp
  · classical
    apply Finset.card_le_card_of_surjOn ((fun a => if ha : a ∈ s then f ⟨a, ha⟩ else b₀) : α → β)
    intro b hb
    obtain ⟨⟨a, ha⟩, hab⟩ := hf ⟨b, hb⟩
    rw [Set.mem_image]
    use a
    simp [ha, hab]

lemma length_gt_one_of_horz_nonempty {p : γ.hookPath} {s : Finset ℕ} (hs : p.horizontal = s)
    (hs0 : s.Nonempty) : p.path.length > 1 := by
  obtain ⟨i, hi⟩ := hs0
  simp only [← SetLike.mem_coe, ← hs, Set.mem_sdiff, Prod.exists, exists_and_right, exists_eq_right,
    Set.mem_ofPred_eq, Set.mem_singleton_iff] at hi
  obtain ⟨⟨j, hj⟩, hi⟩ := hi
  simp_rw [← List.toFinset_card_of_nodup p.nodup, gt_iff_lt, Finset.one_lt_card_iff,
    List.mem_toFinset]
  use (i, j), (p.path.getLast p.ne_nil)
  simp [hj, Prod.eq_iff_fst_eq_snd_eq, hi]

lemma length_gt_one_of_vert_nonempty {p : γ.hookPath} {t : Finset ℕ} (ht : p.vertical = t)
    (ht0 : t.Nonempty) : p.path.length > 1 := by
  obtain ⟨j, hj⟩ := ht0
  simp only [← SetLike.mem_coe, ← ht, Set.mem_sdiff, Prod.exists, exists_eq_right, Set.mem_ofPred_eq,
    Set.mem_singleton_iff] at hj
  obtain ⟨⟨i, hi⟩, hj⟩ := hj
  simp_rw [← List.toFinset_card_of_nodup p.nodup, gt_iff_lt, Finset.one_lt_card_iff,
    List.mem_toFinset]
  use (i, j), (p.path.getLast p.ne_nil)
  simp [hj, Prod.eq_iff_fst_eq_snd_eq, hi]

lemma eq_min'_iff_ne_min' {p : γ.hookPath} (hp : p.path.length > 1) {s t : Finset ℕ}
    (hs : p.horizontal = s) (ht : p.vertical = t) (hs0 : s.Nonempty) (ht0 : t.Nonempty) :
    p.path[1].1 = s.min' hs0 ↔ p.path[1].2 ≠ t.min' ht0 := by
  suffices ¬ (p.path[1].1 = s.min' hs0 ∧ p.path[1].2 = t.min' ht0) ∧
    ¬ (p.path[1].1 ≠ s.min' hs0 ∧ p.path[1].2 ≠ t.min' ht0) by grind
  constructor
  · by_contra! ⟨hps, hpt⟩
    have h : p.path[0] = p.path[1] := by
      rw [← List.head_eq_getElem p.ne_nil, head_eq_horz_vert_min hs ht hs0 ht0]
      grind
    rw [p.nodup.getElem_inj_iff] at h
    contradiction
  · by_contra! ⟨hps, hpt⟩
    have hp' : p.path[1] ∈ γ.hook (p.path.head p.ne_nil) := by
      rw [List.head_eq_getElem]
      exact p.isPath 0 (by lia)
    simp [head_eq_horz_vert_min hs ht hs0 ht0, hook, hps, hpt] at hp'

end YoungDiagram

end
end


/- Source module: KostkaNumbers.HookLength.HookPath.Special -/
section
/-
Copyright (c) 2026 Noah Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Walker
-/




/-!
Define two special hook paths: one goes straight down from a given cell hitting a chosen set of
cells along the way and the other goes straight left from a given cell hitting a chose set of cells
along the way.
-/

section

open YoungDiagram

variable {γ : YoungDiagram}

private lemma aux_sort_getElem_lt {n : ℕ} {t : Finset ℕ}
    (htx : t ∈ (Finset.range n).powerset) (i : ℕ) (hi : i < (t.sort (· ≤ ·)).length) :
    (t.sort (· ≤ ·))[i] ≤ n := by
  refine le_of_lt ?_
  rw [Finset.mem_powerset] at htx
  rw [← Finset.mem_range]
  apply htx
  rw [← Finset.mem_sort (· ≤ ·)]
  exact List.getElem_mem _

private lemma aux_ite_sort_mem1 {x : ℕ × ℕ} (hx : x ∈ γ.corners) {t : Finset ℕ}
    (htx : t ∈ (Finset.range x.2).powerset) (i : ℕ) :
    (if h : i < t.card then (x.1, (t.sort (· ≤ ·))[i]'(by simpa)) else x) ∈ γ := by
  apply corners_le at hx
  split_ifs with hi'
  · exact γ.up_left_mem (by rfl) (aux_sort_getElem_lt htx i _) hx
  · exact hx

private lemma aux_ite_sort_mem2 {x : ℕ × ℕ} (hx : x ∈ γ.corners) {s : Finset ℕ}
    (hsx : s ∈ (Finset.range x.1).powerset) (i : ℕ) :
    (if h : i < s.card then ((s.sort (· ≤ ·))[i]'(by simpa), x.2) else x) ∈ γ := by
  apply corners_le at hx
  split_ifs with hi'
  · exact γ.up_left_mem (aux_sort_getElem_lt hsx i _) (by rfl) hx
  · exact hx

def downHookPath {x : ℕ × ℕ} (hx : x ∈ γ.corners) {t : Finset ℕ}
  (htx : t ∈ (Finset.range x.2).powerset) :
  γ.cornerHookPath :=
  ⟨⟨List.map (fun n ↦ (x.1, n)) (t.sort (· ≤ ·)) ++ [x],
  by simp,
  by
    simp only [List.length_append, List.length_map, Finset.length_sort, List.length_cons,
      List.length_nil, zero_add, add_tsub_cancel_right, hook, List.getElem_append, List.getElem_map,
      List.getElem_singleton, ge_iff_le, Finset.mem_filter, mem_cells]
    intro i hi
    constructor
    · exact aux_ite_sort_mem1 hx htx (i + 1)
    · split_ifs with hi'
      · simp only [true_and, Std.le_refl]
        left
        exact (Finset.pairwise_sort t (· ≤ ·)).sortedLE.getElem_le_getElem_of_le
          (Nat.lt_add_one i).le
      · simp only [true_and, Std.le_refl]
        left
        exact aux_sort_getElem_lt htx i _,
  by
    simp only [List.nodup_append, List.nodup_cons, List.not_mem_nil, not_false_eq_true,
      List.nodup_nil, and_self, List.mem_map, Finset.mem_sort, List.mem_cons, or_false, ne_eq,
      forall_eq, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, true_and]
    constructor
    · exact (Finset.sort_nodup _ _).map (by grind [Function.Injective])
    · grind
  ,
  by
    simp only [List.length_append, List.length_map, Finset.length_sort, List.length_cons,
      List.length_nil, zero_add, Order.lt_add_one_iff, List.getElem_append, List.getElem_map,
      List.getElem_singleton, mem_cells]
    intro i hi
    exact aux_ite_sort_mem1 hx htx i
  ⟩,
  by simp [hx]⟩


def leftHookPath {x : ℕ × ℕ} (hx : x ∈ γ.corners) {s : Finset ℕ}
  (hsx : s ∈ (Finset.range x.1).powerset) :
  γ.cornerHookPath :=
  ⟨⟨List.map (fun n ↦ (n, x.2)) (s.sort (· ≤ ·)) ++ [x],
  by simp,
  by
    simp only [List.length_append, List.length_map, Finset.length_sort, List.length_cons,
      List.length_nil, zero_add, add_tsub_cancel_right, hook, List.getElem_append, List.getElem_map,
      List.getElem_singleton, ge_iff_le, Finset.mem_filter, mem_cells]
    intro i hi
    constructor
    · exact aux_ite_sort_mem2 hx hsx (i + 1)
    · split_ifs with hi'
      · simp only [Std.le_refl, and_true]
        right
        exact (Finset.pairwise_sort s (· ≤ ·)).sortedLE.getElem_le_getElem_of_le
          (Nat.lt_add_one i).le
      · simp only [Std.le_refl, and_true]
        right
        exact aux_sort_getElem_lt hsx i _,
  by
    simp only [List.nodup_append, List.nodup_cons, List.not_mem_nil, not_false_eq_true,
      List.nodup_nil, and_self, List.mem_map, Finset.mem_sort, List.mem_cons, or_false, ne_eq,
      forall_eq, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, true_and]
    constructor
    · exact (Finset.sort_nodup _ _).map (by grind [Function.Injective])
    · grind
  ,
  by
    simp only [List.length_append, List.length_map, Finset.length_sort, List.length_cons,
      List.length_nil, zero_add, Order.lt_add_one_iff, List.getElem_append, List.getElem_map,
      List.getElem_singleton, mem_cells]
    intro i hi
    exact aux_ite_sort_mem2 hx hsx i
  ⟩,
  by simp [hx]⟩

lemma downHookPath_getLast {x : ℕ × ℕ} (hx : x ∈ γ.corners) {t : Finset ℕ}
    (htx : t ∈ (Finset.range x.2).powerset) :
    (downHookPath hx htx).1.path.getLast (downHookPath hx htx).1.ne_nil = x := by
  simp [downHookPath]

lemma leftHookPath_getLast {x : ℕ × ℕ} (hx : x ∈ γ.corners) {s : Finset ℕ}
    (hsx : s ∈ (Finset.range x.1).powerset) :
    (leftHookPath hx hsx).1.path.getLast (leftHookPath hx hsx).1.ne_nil = x := by
  simp [leftHookPath]

end
end


/- Source module: KostkaNumbers.HookLength.HookPath.Operations -/
section
/-
Copyright (c) 2026 Noah Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Walker
-/




/-!
Convert the list operations dropLast, append, tail, and cons to operations on hookPath.
-/

section

namespace YoungDiagram

variable {γ : YoungDiagram}

section DropLast

def hookPath.dropLast (p : γ.hookPath) : γ.hookPath := if hp : p.path.length = 1 then p else
  ⟨p.path.dropLast,
  by
    have hp0 : p.path.length ≠ 0 := hookPath_length_ne_zero p
    rw [ne_eq, ← List.length_eq_zero_iff, List.length_dropLast]
    lia,
  by
    intro i hi
    have hp0 : p.path.length ≠ 0 := hookPath_length_ne_zero p
    rw [List.getElem_dropLast, List.getElem_dropLast]
    rw [List.length_dropLast] at hi
    exact p.isPath i (by lia),
  List.Nodup.sublist (List.dropLast_sublist _) p.nodup,
  by
    intro i hi
    have hp0 : p.path.length ≠ 0 := hookPath_length_ne_zero p
    rw [List.getElem_dropLast]
    rw [List.length_dropLast] at hi
    exact p.mem_cells i (by lia)⟩

@[simp]
lemma dropLast_of_length_eq_one (p : γ.hookPath) (hp : p.path.length = 1) : p.dropLast = p := by
  simp [hookPath.dropLast, hp]

lemma path_dropLast (p : γ.hookPath) (hp : p.path.length > 1) :
    p.dropLast.path = p.path.dropLast := by
  simp [hookPath.dropLast, hp.ne.symm]

lemma length_dropLast (p : γ.hookPath) (hp : p.path.length > 1) :
    p.dropLast.path.length = p.path.length - 1 := by
  simp [hp, path_dropLast]

lemma length_dropLast_le (p : γ.hookPath) : p.dropLast.path.length ≤ p.path.length := by
  by_cases! hp : p.path.length = 1
  · simp [hp]
  · have hp1 : p.path.length > 1 := by grind [hookPath_length_ne_zero]
    simp [hp1, path_dropLast]

lemma getLast_ne_getLast_dropLast (p : γ.hookPath) (hp : p.path.length > 1) :
    p.path.getLast p.ne_nil ≠ p.dropLast.path.getLast p.dropLast.ne_nil := by
  simp [path_dropLast, hp, List.getLast_eq_getElem, List.Nodup.getElem_inj_iff p.nodup]
  lia

lemma getLast_mem_hook_getLast_dropLast (p : γ.hookPath) :
    p.path.getLast p.ne_nil ∈ γ.hook (p.dropLast.path.getLast p.dropLast.ne_nil) := by
  by_cases! hp : p.path.length = 1
  · simp [hp, self_mem_hook _ _ (getLast_mem p)]
  · have hp : p.path.length > 1 := by grind [hookPath_length_ne_zero]
    simp only [gt_iff_lt, hp, path_dropLast, List.getLast_eq_getElem, List.length_dropLast,
      List.getElem_dropLast]
    conv => rhs; rw! [show p.path.length - 1 = p.path.length - 1 - 1 + 1 by lia]
    exact p.isPath _ (by lia)

lemma getLast_dropLast_notMem_corners (p : γ.hookPath) (hp : p.path.length > 1) :
    p.dropLast.path.getLast p.dropLast.ne_nil ∉ γ.corners := by
  rw [mem_corners_iff_hook_eq_self]
  simp only [Finset.ext_iff, Finset.mem_singleton, not_forall]
  use p.path.getLast p.ne_nil
  simp [getLast_ne_getLast_dropLast p hp, getLast_mem_hook_getLast_dropLast p]

lemma getLast_dropLast_le_getLast (p : γ.hookPath) :
    (p.dropLast.path.getLast p.dropLast.ne_nil) ≤ (p.path.getLast p.ne_nil) := by
  by_cases! hp : p.path.length = 1
  · rw [dropLast_of_length_eq_one _ hp]
  have hp : p.path.length > 1 := by
    have hp0 : p.path.length ≠ 0 := by simp [ne_eq, List.length_eq_zero_iff]
    lia
  simp only [path_dropLast _ hp, List.getLast_eq_getElem, List.length_dropLast,
    List.getElem_dropLast, ge_iff_le]
  exact path_mono _ (by lia)

lemma getElem_dropLast_eq_getElem (p : γ.hookPath) (a : ℕ) (ha : a < p.dropLast.path.length) :
    p.dropLast.path[a] = p.path[a]'(by grind [length_dropLast_le]) := by
  by_cases! hp : p.path.length = 1
  · simp [hp]
  · have hp : p.path.length > 1 := by grind [hookPath_length_ne_zero]
    simp [path_dropLast, hp]

lemma eq_of_length_dropLast_getLast_eq {p q : γ.hookPath} (hl : p.path.length = q.path.length)
    (ht : p.dropLast = q.dropLast) (hg : p.path.getLast p.ne_nil = q.path.getLast q.ne_nil) :
    p = q := by
  by_cases! hp : p.path.length = 1
  · simpa [hp, hp ▸ hl] using ht
  · have hp1 : p.path.length > 1 := by grind [hookPath_length_ne_zero]
    have hq1 : q.path.length > 1 := by lia
    apply hookPath.eq_of_path_eq
    rw [← List.dropLast_concat_getLast p.ne_nil, ← List.dropLast_concat_getLast q.ne_nil,
      ← path_dropLast p hp1, ← path_dropLast q hq1, ht, hg]

end DropLast



section Extend

def hookPath.extend (p : γ.hookPath) (x : ℕ × ℕ) (hx : x ∈ γ.hook (p.path.getLast p.ne_nil))
    (hx' : x ≠ p.path.getLast p.ne_nil) : γ.hookPath :=
  ⟨p.path ++ [x],
  by simp,
  by
    simp only [List.length_append, List.length_cons, List.length_nil, zero_add,
      add_tsub_cancel_right, List.getElem_append, List.getElem_singleton]
    intro i hi
    split_ifs with h
    · exact p.isPath i (by lia)
    · rw [List.getLast_eq_getElem] at hx
      grind,
  by
    simp only [List.nodup_append, p.nodup, List.nodup_cons, List.not_mem_nil, not_false_eq_true,
      List.nodup_nil, and_self, List.mem_cons, or_false, ne_eq, forall_eq, true_and]
    intro y hy
    contrapose! hy
    subst hy
    exact notMem_path_of_mem_hook hx hx',
  by
    simp only [List.length_append, List.length_cons, List.length_nil, zero_add,
      Order.lt_add_one_iff, List.getElem_append, List.getElem_singleton, YoungDiagram.mem_cells]
    intro i hi
    split_ifs with h
    · exact p.mem_cells _ _
    · exact mem_of_mem_hook γ hx⟩

lemma extend_length {p : γ.hookPath} {x : ℕ × ℕ} (hx : x ∈ γ.hook (p.path.getLast p.ne_nil))
    (hx' : x ≠ p.path.getLast p.ne_nil) :
    (p.extend x hx hx').path.length = p.path.length + 1 := by
  simp [hookPath.extend]

lemma extend_length_gt_one {p : γ.hookPath} {x : ℕ × ℕ} (hx : x ∈ γ.hook (p.path.getLast p.ne_nil))
    (hx' : x ≠ p.path.getLast p.ne_nil) :
    (p.extend x hx hx').path.length > 1 := by
  grind [extend_length hx hx', hookPath_length_ne_zero]

lemma dropLast_extend (p : γ.hookPath) (x : ℕ × ℕ) (hx : x ∈ γ.hook (p.path.getLast p.ne_nil))
    (hx' : x ≠ p.path.getLast p.ne_nil) :
    (p.extend x hx hx').dropLast = p := by
  apply hookPath.eq_of_path_eq
  rw [path_dropLast _ (extend_length_gt_one hx hx')]
  simp [hookPath.extend]

lemma getLast_extend (p : γ.hookPath) (x : ℕ × ℕ) (hx : x ∈ γ.hook (p.path.getLast p.ne_nil))
    (hx' : x ≠ p.path.getLast p.ne_nil) :
    (p.extend x hx hx').path.getLast (p.extend x hx hx').ne_nil = x := by
  simp [hookPath.extend]

end Extend



section Tail



def hookPath.tail (p : γ.hookPath) : γ.hookPath := if hp : p.path.length = 1 then p else
  ⟨p.path.tail,
  by
    have hp0 : p.path.length ≠ 0 := hookPath_length_ne_zero p
    rw [ne_eq, ← List.length_eq_zero_iff, List.length_tail]
    lia,
  by
    intro i hi
    have hp0 : p.path.length ≠ 0 := hookPath_length_ne_zero p
    rw [List.getElem_tail, List.getElem_tail]
    rw [List.length_tail] at hi
    exact p.isPath (i + 1) (by lia),
  List.Nodup.sublist (List.tail_sublist _) p.nodup,
  by
    intro i hi
    have hp0 : p.path.length ≠ 0 := hookPath_length_ne_zero p
    rw [List.getElem_tail]
    rw [List.length_tail] at hi
    exact p.mem_cells (i + 1) (by lia)⟩

@[simp]
lemma tail_of_length_eq_one (p : γ.hookPath) (hp : p.path.length = 1) : p.tail = p := by
  simp [hookPath.tail, hp]

lemma path_tail (p : γ.hookPath) (hp : p.path.length > 1) :
    p.tail.path = p.path.tail := by
  simp [hookPath.tail, hp.ne.symm]

lemma length_tail (p : γ.hookPath) (hp : p.path.length > 1) :
    p.tail.path.length = p.path.length - 1 := by
  simp [hp, path_tail]

lemma length_tail_le (p : γ.hookPath) : p.tail.path.length ≤ p.path.length := by
  by_cases! hp : p.path.length = 1
  · simp [hp]
  · have hp1 : p.path.length > 1 := by grind [hookPath_length_ne_zero]
    simp [hp1, path_tail]

end Tail



section Cons

def hookPath.cons (p : γ.hookPath) {x : ℕ × ℕ} (hx : p.path.head p.ne_nil ∈ γ.hook x)
  (hx' : x ≠ p.path.head p.ne_nil) : γ.hookPath :=
  ⟨x :: p.path,
  by simp,
  by
    simp only [List.length_cons, add_tsub_cancel_right, List.getElem_cons, Nat.succ_ne_zero,
      reduceDIte]
    intro i hi
    split_ifs with hi'
    · subst hi'
      rwa [← List.head_eq_getElem]
    · conv => rhs; rw! [show i = i - 1 + 1 by lia]
      exact p.isPath (i - 1) (by lia),
  by
    rw [List.nodup_cons]
    constructor
    · contrapose! hx'
      refine le_antisymm ?_ ?_
      · exact γ.le_of_mem_hook hx
      · exact head_le_of_mem_path hx'
    · exact p.nodup,
  by
    intro i hi
    simp only [List.getElem_cons, YoungDiagram.mem_cells]
    split_ifs
    · exact mem_of_mem_hook_right γ hx
    · exact p.mem_cells _ _
  ⟩

lemma path_cons (p : γ.hookPath) {x : ℕ × ℕ} (hx : p.path.head p.ne_nil ∈ γ.hook x)
    (hx' : x ≠ p.path.head p.ne_nil) :
    (p.cons hx hx').path = x :: p.path := by
  simp [hookPath.cons]

lemma length_cons (p : γ.hookPath) {x : ℕ × ℕ} (hx : p.path.head p.ne_nil ∈ γ.hook x)
    (hx' : x ≠ p.path.head p.ne_nil) :
    (p.cons hx hx').path.length = p.path.length + 1 := by
  simp [path_cons]

lemma length_cons_gt_one (p : γ.hookPath) {x : ℕ × ℕ} (hx : p.path.head p.ne_nil ∈ γ.hook x)
    (hx' : x ≠ p.path.head p.ne_nil) :
    (p.cons hx hx').path.length > 1 := by
  grind [length_cons, hookPath_length_ne_zero]

lemma tail_cons (p : γ.hookPath) {x : ℕ × ℕ} (hx : p.path.head p.ne_nil ∈ γ.hook x)
    (hx' : x ≠ p.path.head p.ne_nil) :
    (p.cons hx hx').tail = p := by
  apply hookPath.eq_of_path_eq
  rw [path_tail _ (length_cons_gt_one p hx hx'), path_cons, List.tail_cons]

lemma getLast_cons (p : γ.hookPath) {x : ℕ × ℕ} (hx : p.path.head p.ne_nil ∈ γ.hook x)
    (hx' : x ≠ p.path.head p.ne_nil) :
    (p.cons hx hx').path.getLast (p.cons hx hx').ne_nil = p.path.getLast p.ne_nil := by
  simp [path_cons]

end Cons

end YoungDiagram

end
end


/- Source module: KostkaNumbers.HookLength.HookPath.ProjOps -/
section
/-
Copyright (c) 2026 Noah Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Walker
-/







/-!
Lemmas about how the horizontal and vertical projections interact with the other
constructions defined.
-/

section

open YoungDiagram

variable {γ : YoungDiagram}

section Tail

lemma horizontal_tail_le {p : γ.hookPath} : p.tail.horizontal ≤ p.horizontal := by
  by_cases! hp : p.path.length = 1
  · rw [tail_of_length_eq_one _ hp]
  have hp : p.path.length > 1 := by
    have hp0 : p.path.length ≠ 0 := by simp [ne_eq, List.length_eq_zero_iff]
    lia
  intro i
  simp [path_tail _ hp]
  grind [List.mem_of_mem_tail]

lemma vertical_tail_le {p : γ.hookPath} : p.tail.vertical ≤ p.vertical := by
  by_cases! hp : p.path.length = 1
  · rw [tail_of_length_eq_one _ hp]
  have hp : p.path.length > 1 := by
    have hp0 : p.path.length ≠ 0 := by simp [ne_eq, List.length_eq_zero_iff]
    lia
  intro j
  simp [path_tail _ hp]
  grind [List.mem_of_mem_tail]

lemma horizontal_tail_of_eq_min' {p : γ.hookPath} (hp : p.path.length > 1) {s : Finset ℕ}
    (hs : p.horizontal = s) (hs0 : s.Nonempty) (h : p.path[1].1 = s.min' hs0) :
    p.tail.horizontal = s := by
  rw [← hs]
  refine le_antisymm horizontal_tail_le ?_
  intro i
  simp only [Set.mem_sdiff, Prod.exists, exists_and_right, exists_eq_right, Set.mem_ofPred_eq,
    Set.mem_singleton_iff, path_tail _ hp, List.getLast_tail, and_imp, forall_exists_index]
  intro j hij hil
  constructor
  · by_cases! hit : (i, j) = p.path.head p.ne_nil
    · use p.path[1].2
      simp only [Prod.ext_iff, head_fst_eq_horz_min hs hs0] at hit
      rw [hit.1, ← h, ← List.getElem_tail (by grind)]
      exact List.getElem_mem _
    · use j
      exact List.mem_tail_of_mem_ne_head _ hij hit
  · exact hil

lemma horizontal_tail_of_ne_min' {p : γ.hookPath} (hp : p.path.length > 1) {s : Finset ℕ}
    (hs : p.horizontal = s) (hs0 : s.Nonempty) (h : p.path[1].1 ≠ s.min' hs0) :
    p.tail.horizontal = s \ {s.min' hs0} := by
  ext i
  constructor
  · intro hi
    suffices i ≠ s.min' hs0 by
      simp only [Finset.coe_sdiff, Finset.coe_singleton, Set.mem_sdiff, SetLike.mem_coe,
        Set.mem_singleton_iff, this, not_false_eq_true, and_true]
      rw [← Finset.mem_coe, ← hs]
      exact horizontal_tail_le hi
    refine ne_of_gt ?_
    have hpp : p.path[1] = p.tail.path.head p.tail.ne_nil := by
      rw! [path_tail _ hp, List.head_eq_getElem, List.getElem_tail]
      rfl
    have hps : s.min' hs0 < p.path[1].1 := by
      refine lt_of_le_of_ne ?_ h.symm
      refine Finset.min'_le _ _ ?_
      simp only [← Finset.mem_coe, ← hs, Set.mem_sdiff, Prod.exists, exists_and_right,
        exists_eq_right, Set.mem_ofPred_eq, Set.mem_singleton_iff]
      constructor
      · use p.path[1].2
        exact List.getElem_mem _
      · simp only [Set.mem_sdiff, Prod.exists, exists_and_right, exists_eq_right, Set.mem_ofPred_eq,
          Set.mem_singleton_iff] at hi
        obtain ⟨⟨j, hij⟩, hi⟩ := hi
        refine ne_of_lt ?_
        refine lt_of_le_of_lt (b := i) ?_ ?_
        · rw [hpp]
          apply head_le_of_mem_path at hij
          rw [Prod.le_def] at hij
          exact hij.1
        · apply le_getLast_of_mem_path at hij
          simp [Prod.le_def, path_tail _ hp] at hij hi
          lia
    refine lt_of_lt_of_le hps ?_
    let s' : Finset ℕ := p.tail.horizontal.toFinset
    have hsi' : i ∈ s' := by
      unfold s'
      rwa [Set.mem_toFinset]
    rw [hpp, head_fst_eq_horz_min (s := s') (by simp [s']) (by use i)]
    refine Finset.min'_le _ _ hsi'
  · simp only [Finset.coe_sdiff, ← hs, Finset.coe_singleton, Set.mem_sdiff, Prod.exists,
      exists_and_right, exists_eq_right, Set.mem_ofPred_eq, Set.mem_singleton_iff, path_tail _ hp,
      List.getLast_tail, and_imp, forall_exists_index]
    intro j hij hil his
    constructor
    · use j
      refine List.mem_tail_of_mem_ne_head (by grind) hij ?_
      simp [Prod.ext_iff, head_fst_eq_horz_min hs hs0, his]
    · exact hil

lemma vertical_tail_of_eq_min' {p : γ.hookPath} (hp : p.path.length > 1) {t : Finset ℕ}
    (ht : p.vertical = t) (ht0 : t.Nonempty) (h : p.path[1].2 = t.min' ht0) :
    p.tail.vertical = t := by
  rw [← ht]
  refine le_antisymm vertical_tail_le ?_
  intro j
  simp only [Set.mem_sdiff, Prod.exists, exists_eq_right, Set.mem_ofPred_eq, Set.mem_singleton_iff,
    path_tail _ hp, List.getLast_tail, and_imp, forall_exists_index]
  intro i hij hjl
  constructor
  · by_cases! hjt : (i, j) = p.path.head p.ne_nil
    · use p.path[1].1
      simp only [Prod.ext_iff, head_snd_eq_vert_min ht ht0] at hjt
      rw [hjt.2, ← h, ← List.getElem_tail (by grind)]
      exact List.getElem_mem _
    · use i
      exact List.mem_tail_of_mem_ne_head _ hij hjt
  · exact hjl

lemma vertical_tail_of_ne_min' {p : γ.hookPath} (hp : p.path.length > 1) {t : Finset ℕ}
    (ht : p.vertical = t) (ht0 : t.Nonempty) (h : p.path[1].2 ≠ t.min' ht0) :
    p.tail.vertical = t \ {t.min' ht0} := by
  ext j
  constructor
  · intro hj
    suffices j ≠ t.min' ht0 by
      simp only [Finset.coe_sdiff, Finset.coe_singleton, Set.mem_sdiff, SetLike.mem_coe,
        Set.mem_singleton_iff, this, not_false_eq_true, and_true]
      rw [← Finset.mem_coe, ← ht]
      exact vertical_tail_le hj
    refine ne_of_gt ?_
    have hpp : p.path[1] = p.tail.path.head p.tail.ne_nil := by
      rw! [path_tail _ hp, List.head_eq_getElem, List.getElem_tail]
      rfl
    have hpt : t.min' ht0 < p.path[1].2 := by
      refine lt_of_le_of_ne ?_ h.symm
      refine Finset.min'_le _ _ ?_
      simp only [← Finset.mem_coe, ← ht, Set.mem_sdiff, Prod.exists, exists_eq_right,
        Set.mem_ofPred_eq, Set.mem_singleton_iff]
      constructor
      · use p.path[1].1
        exact List.getElem_mem _
      · simp only [Set.mem_sdiff, Prod.exists, exists_eq_right, Set.mem_ofPred_eq,
          Set.mem_singleton_iff] at hj
        obtain ⟨⟨i, hij⟩, hj⟩ := hj
        refine ne_of_lt ?_
        refine lt_of_le_of_lt (b := j) ?_ ?_
        · rw [hpp]
          apply head_le_of_mem_path at hij
          rw [Prod.le_def] at hij
          exact hij.2
        · apply le_getLast_of_mem_path at hij
          simp [Prod.le_def, path_tail _ hp] at hij hj
          lia
    refine lt_of_lt_of_le hpt ?_
    let t' : Finset ℕ := p.tail.vertical.toFinset
    have htj' : j ∈ t' := by
      unfold t'
      rwa [Set.mem_toFinset]
    rw [hpp, head_snd_eq_vert_min (t := t') (by simp [t']) (by use j)]
    refine Finset.min'_le _ _ htj'
  · simp only [Finset.coe_sdiff, ← ht, Finset.coe_singleton, Set.mem_sdiff, Prod.exists,
      exists_eq_right, Set.mem_ofPred_eq, Set.mem_singleton_iff, path_tail _ hp, List.getLast_tail,
      and_imp, forall_exists_index]
    intro i hij hjl hjt
    constructor
    · use i
      refine List.mem_tail_of_mem_ne_head (by grind) hij ?_
      simp [Prod.ext_iff, head_snd_eq_vert_min ht ht0, hjt]
    · exact hjl

end Tail



section Cons

lemma cons_horizontal_of_mem_horizontal (p : γ.hookPath) {x : ℕ × ℕ}
    (hx : p.path.head p.ne_nil ∈ γ.hook x) (hx' : x ≠ p.path.head p.ne_nil)
    (hxh : x.1 ∈ p.horizontal) :
    (p.cons hx hx').horizontal = p.horizontal := by
  ext i
  simp [path_cons] at hxh ⊢
  grind

lemma cons_horizontal_of_mem_vertical (p : γ.hookPath) {x : ℕ × ℕ}
    (hx : p.path.head p.ne_nil ∈ γ.hook x) (hx' : x ≠ p.path.head p.ne_nil)
    (hxh : x.2 ∈ p.vertical) :
    (p.cons hx hx').horizontal = p.horizontal ∪ {x.1} := by
  ext i
  simp [hook] at hx
  simp only [Set.mem_sdiff, Prod.exists, exists_eq_right, Set.mem_ofPred_eq, Set.mem_singleton_iff,
    path_cons, List.mem_cons, exists_eq_or_imp, exists_and_right, ne_eq, hookPath_ne_nil,
    not_false_eq_true, List.getLast_cons, Set.union_singleton, Set.mem_insert_iff] at hxh ⊢
  constructor
  · grind
  · intro h
    rcases h with h | h
    · subst h
      obtain ⟨⟨i, hix⟩, hxl⟩ := hxh
      have hh := head_le_of_mem_path hix
      have hl := le_getLast_of_mem_path hix
      rw [Prod.le_def] at hh hl
      grind
    · grind

lemma cons_vertical_of_mem_vertical (p : γ.hookPath) {x : ℕ × ℕ}
    (hx : p.path.head p.ne_nil ∈ γ.hook x) (hx' : x ≠ p.path.head p.ne_nil)
    (hxh : x.2 ∈ p.vertical) :
    (p.cons hx hx').vertical = p.vertical := by
  ext i
  simp [path_cons] at hxh ⊢
  grind

lemma cons_vertical_of_mem_horizontal (p : γ.hookPath) {x : ℕ × ℕ}
    (hx : p.path.head p.ne_nil ∈ γ.hook x) (hx' : x ≠ p.path.head p.ne_nil)
    (hxh : x.1 ∈ p.horizontal) :
    (p.cons hx hx').vertical = p.vertical ∪ {x.2} := by
  ext i
  simp [hook] at hx
  simp only [Set.mem_sdiff, Prod.exists, exists_eq_right, Set.mem_ofPred_eq, Set.mem_singleton_iff,
    path_cons, List.mem_cons, exists_eq_or_imp, exists_and_right, ne_eq, hookPath_ne_nil,
    not_false_eq_true, List.getLast_cons, Set.union_singleton, Set.mem_insert_iff] at hxh ⊢
  constructor
  · grind
  · intro h
    rcases h with h | h
    · subst h
      obtain ⟨⟨j, hjx⟩, hxl⟩ := hxh
      have hh := head_le_of_mem_path hjx
      have hl := le_getLast_of_mem_path hjx
      rw [Prod.le_def] at hh hl
      grind
    · grind

end Cons


section DownLeft


lemma downHookPath_horizontal {x : ℕ × ℕ} (hx : x ∈ γ.corners) {t : Finset ℕ}
    (htx : t ∈ (Finset.range x.2).powerset) :
    (downHookPath hx htx).1.horizontal = ∅ := by
  simp [downHookPath, hookPath.horizontal]
  grind

lemma downHookPath_vertical {x : ℕ × ℕ} (hx : x ∈ γ.corners) {t : Finset ℕ}
    (htx : t ∈ (Finset.range x.2).powerset) :
    (downHookPath hx htx).1.vertical = t := by
  simp [downHookPath, hookPath.vertical]
  grind

lemma leftHookPath_horizontal {x : ℕ × ℕ} (hx : x ∈ γ.corners) {s : Finset ℕ}
    (hsx : s ∈ (Finset.range x.1).powerset) :
    (leftHookPath hx hsx).1.horizontal = s := by
  simp [leftHookPath, hookPath.horizontal]
  grind

lemma leftHookPath_vertical {x : ℕ × ℕ} (hx : x ∈ γ.corners) {s : Finset ℕ}
    (hsx : s ∈ (Finset.range x.1).powerset) :
    (leftHookPath hx hsx).1.vertical = ∅ := by
  simp [leftHookPath, hookPath.vertical]
  grind


lemma setOf_horizontal_empty_eq_down {x : ℕ × ℕ} (hx : x ∈ γ.corners) {t : Finset ℕ}
    (htx : t ∈ (Finset.range x.2).powerset) :
    {p : γ.cornerHookPath | p.1.horizontal = ∅ ∧ p.1.vertical = t ∧
    p.1.path.getLast p.1.ne_nil = x} = {downHookPath hx htx} := by
  ext p
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · intro ⟨hph, hpv, hpl⟩
    apply Subtype.ext
    apply hookPath.eq_of_path_eq
    simp only [downHookPath]
    rw [← List.dropLast_append_getLast p.1.ne_nil, hpl]
    congr
    refine List.Perm.eq_of_sortedLE ?_ ?_ ?_
    · by_cases! hp : p.1.path.length = 1
      · suffices p.1.path.dropLast = [] by grind
        rw [List.eq_nil_iff_length_eq_zero, List.length_dropLast, hp]
      have hp : p.1.path.length > 1 := by
        have hp0 : p.1.path.length ≠ 0 := by simp [ne_eq, List.length_eq_zero_iff]
        lia
      rw [← path_dropLast _ hp]
      exact path_sortedLE
    · rw [StrictMono.sortedLE_listMap]
      · exact (Finset.pairwise_sort _ _).sortedLE
      · intro j k
        simp
    · rw [← Multiset.coe_eq_coe, ← Multiset.map_coe]
      ext y
      rw [Multiset.count_eq_of_nodup, Multiset.count_eq_of_nodup]
      · split_ifs with hy hy' hy'
        any_goals rfl
        · simp at hy'
          simp only [Multiset.mem_coe] at hy
          have hyx : y ≠ x := by
            have hp := p.1.nodup
            rw [← List.dropLast_append_getLast p.1.ne_nil, List.nodup_append] at hp
            grind
          have hyx1 : y.1 = x.1 := by
            have hyh : y.1 ∉ p.1.horizontal := by grind
            simp only [Set.mem_sdiff, Prod.exists, exists_and_right, exists_eq_right,
              Set.mem_ofPred_eq, Set.mem_singleton_iff, not_and, Decidable.not_not,
              forall_exists_index] at hyh
            specialize hyh y.2 (List.mem_of_mem_dropLast hy)
            rwa [← hpl]
          have hyv : y.2 ∈ p.1.vertical := by grind [List.mem_of_mem_dropLast]
          grind
        · simp only [Finset.sort_eq, Multiset.mem_map, Finset.mem_val] at hy'
          obtain ⟨j, hjt, hj⟩ := hy'
          simp only [← Finset.mem_coe, ← hpv, Prod.exists, exists_eq_right, Set.mem_sdiff,
            Set.mem_ofPred_eq, Set.mem_singleton_iff] at hjt
          subst hj
          obtain ⟨⟨i, hi⟩, hij⟩ := hjt
          by_cases! hix : i = x.1
          · subst hix
            rw [Multiset.mem_coe] at hy
            apply List.mem_dropLast_of_mem_of_ne_getLast at hi
            exact hy (hi (by grind))
          suffices i ∈ p.1.horizontal by grind
          simp only [Set.mem_sdiff, Prod.exists, exists_and_right, exists_eq_right,
            Set.mem_ofPred_eq, Set.mem_singleton_iff]
          constructor
          · use j
          · rwa [hpl]
      · refine Multiset.Nodup.map ?_ (by simp [Finset.nodup])
        intro i
        simp
      · rw [Multiset.coe_nodup]
        exact List.Sublist.nodup (List.dropLast_sublist _) p.1.nodup
  · intro hp
    subst hp
    constructor
    · exact downHookPath_horizontal hx htx
    constructor
    · exact downHookPath_vertical hx htx
    · exact downHookPath_getLast hx htx

lemma setOf_vertical_empty_eq_left {x : ℕ × ℕ} (hx : x ∈ γ.corners) {s : Finset ℕ}
    (hsx : s ∈ (Finset.range x.1).powerset) :
    {p : γ.cornerHookPath | p.1.horizontal = s ∧ p.1.vertical = ∅ ∧
    p.1.path.getLast p.1.ne_nil = x} = {leftHookPath hx hsx} := by
  ext p
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · intro ⟨hph, hpv, hpl⟩
    apply Subtype.ext
    apply hookPath.eq_of_path_eq
    simp only [leftHookPath]
    rw [← List.dropLast_append_getLast p.1.ne_nil, hpl]
    congr
    refine List.Perm.eq_of_sortedLE ?_ ?_ ?_
    · by_cases! hp : p.1.path.length = 1
      · suffices p.1.path.dropLast = [] by grind
        rw [List.eq_nil_iff_length_eq_zero, List.length_dropLast, hp]
      have hp : p.1.path.length > 1 := by
        have hp0 : p.1.path.length ≠ 0 := by simp [ne_eq, List.length_eq_zero_iff]
        lia
      rw [← path_dropLast _ hp]
      exact path_sortedLE
    · rw [StrictMono.sortedLE_listMap]
      · exact (Finset.pairwise_sort _ _).sortedLE
      · intro j k
        simp
    · rw [← Multiset.coe_eq_coe, ← Multiset.map_coe]
      ext y
      rw [Multiset.count_eq_of_nodup, Multiset.count_eq_of_nodup]
      · split_ifs with hy hy' hy'
        any_goals rfl
        · simp at hy'
          simp only [Multiset.mem_coe] at hy
          have hyx : y ≠ x := by
            have hp := p.1.nodup
            rw [← List.dropLast_append_getLast p.1.ne_nil, List.nodup_append] at hp
            grind
          have hyx2 : y.2 = x.2 := by
            have hyv : y.2 ∉ p.1.vertical := by grind
            simp only [Set.mem_sdiff, Prod.exists, exists_eq_right, Set.mem_ofPred_eq,
              Set.mem_singleton_iff, not_and, Decidable.not_not, forall_exists_index] at hyv
            specialize hyv y.1 (List.mem_of_mem_dropLast hy)
            rwa [← hpl]
          have hyh : y.1 ∈ p.1.horizontal := by grind [List.mem_of_mem_dropLast]
          grind
        · simp only [Finset.sort_eq, Multiset.mem_map, Finset.mem_val] at hy'
          obtain ⟨i, his, hi⟩ := hy'
          simp only [← Finset.mem_coe, ← hph, Set.mem_sdiff, Prod.exists, exists_and_right,
            exists_eq_right, Set.mem_ofPred_eq, Set.mem_singleton_iff] at his
          subst hi
          obtain ⟨⟨j, hj⟩, hij⟩ := his
          by_cases! hjx : j = x.2
          · subst hjx
            rw [Multiset.mem_coe] at hy
            apply List.mem_dropLast_of_mem_of_ne_getLast at hj
            exact hy (hj (by grind))
          suffices j ∈ p.1.vertical by grind
          simp only [Set.mem_sdiff, Prod.exists, exists_eq_right, Set.mem_ofPred_eq,
            Set.mem_singleton_iff]
          constructor
          · use i
          · rwa [hpl]
      · refine Multiset.Nodup.map ?_ (by simp [Finset.nodup])
        intro i
        simp
      · rw [Multiset.coe_nodup]
        exact List.Sublist.nodup (List.dropLast_sublist _) p.1.nodup
  · intro hp
    subst hp
    constructor
    · exact leftHookPath_horizontal hx hsx
    constructor
    · exact leftHookPath_vertical hx hsx
    · exact leftHookPath_getLast hx hsx

end DownLeft

end
end


/- Source module: KostkaNumbers.HookLength.PMF -/
section
/-
Copyright (c) 2026 Noah Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Walker
-/






/-!
Define the probability mass function for the trial described in GNW.  The experiment is to uniformly
randomly choose a cell in the Young diagram, then uniformly randomly choose a different cell in its
hook and so on until a corner is reached.  Mathlib doesn't have this way of describing a probability
so we give an equivalent definition in terms of hook paths.  A hook path is a list of cells in the
Young diagram such that each is in the hook of the previous.  We assign each hook path a probability
and use these in the proof.
-/

section

open MeasureTheory
open scoped ENNReal NNReal

namespace YoungDiagram

variable (γ : YoungDiagram)

noncomputable
abbrev pmf_fun : γ.hookPath → ℝ≥0 := fun p ↦
  1 / γ.card * ∏ i ∈ (Finset.univ : Finset (Fin (p.path.length))).erase ⟨p.path.length - 1, by
    grind [hookPath_length_ne_zero]⟩, (1 / (γ.hookLength (p.path.get i) - 1) : ℝ≥0)

lemma disjoint_length_eq_length_lt_and_cornerHookPath (n : ℕ) : Disjoint
    ({p : γ.hookPath | p.path.length = n + 1} : Finset _)
    ({p : γ.hookPath | p.path.length < n + 1 ∧ p.path.getLast p.ne_nil ∈ γ.corners} :
    Finset _) := by
  intro s hs hs' p hp
  have hp' := hs' hp
  apply hs at hp
  simp at hp hp'
  lia

lemma disjoint_length_eq_length_eq_and_cornerHookPath (n : ℕ) : Disjoint
    ({p : γ.hookPath | p.path.length = n + 1 + 1} : Finset _)
    ({p : γ.hookPath | p.path.length = n + 1 ∧ p.path.getLast p.ne_nil ∈ γ.corners} :
    Finset _) := by
  intro s hs hs' p hp
  have hp' := hs' hp
  apply hs at hp
  simp at hp hp'
  lia

lemma card_hook_ne_eq_hookLength_sub_one {x : ℕ × ℕ} (hx : x ∈ γ) :
    {y ∈ γ.hook x | y ≠ x}.card = γ.hookLength x - 1 := by
  have h : {y ∈ γ.hook x | y ≠ x} = (γ.hook x).erase x := by grind
  rw [h, Finset.card_erase_of_mem (self_mem_hook γ x hx), hook_card_eq_hookLength γ x hx]

lemma pmf_fun_eq_div_mul_dropLast {p : γ.hookPath} (hp : p.path.length > 1) :
    γ.pmf_fun p =
    1 / (γ.hookLength (p.dropLast.path.getLast p.dropLast.ne_nil) - 1) * γ.pmf_fun p.dropLast := by
  unfold pmf_fun
  have hγ : 1 / (γ.card : ℝ≥0) ≠ 0 := by
    simp only [one_div, ne_eq, inv_eq_zero, Nat.cast_eq_zero, ← eq_bot_iff_card_eq_zero,
      ne_bot_of_hookPath p, not_false_eq_true]
  simp only [mul_left_comm, mul_eq_mul_left_iff, hγ, or_false]
  have hps : ∏ i, 1 / (γ.hookLength (p.dropLast.path.get i) - 1 : ℝ≥0) =
      1 / (γ.hookLength (p.dropLast.path.getLast p.dropLast.ne_nil) - 1 : ℝ≥0) *
      ∏ i ∈ (Finset.univ : Finset (Fin (p.dropLast.path.length))).erase
      ⟨p.dropLast.path.length - 1, by grind [hookPath_length_ne_zero]⟩,
      1 / (γ.hookLength (p.dropLast.path.get i) - 1 : ℝ≥0) := by
    simp_rw [List.get_eq_getElem]
    have ha : ⟨p.dropLast.path.length - 1, by grind [length_dropLast]⟩ ∈
        (Finset.univ : Finset (Fin p.dropLast.path.length)) := Finset.mem_univ _
    rw [List.getLast_eq_getElem, ← Finset.mul_prod_erase _ _ ha]
  simp_rw [← hps, List.get_eq_getElem]
  have hp : p.path.length = p.dropLast.path.length + 1 := by
    simp [length_dropLast, hp, tsub_add_cancel_of_le hp.le]
  symm
  rw! [hp]
  refine Finset.prod_nbij (Fin.castSucc (n := p.dropLast.path.length)) ?_ ?_ ?_ ?_
  · grind
  · exact Set.injOn_of_injective (Fin.castSucc_injective _)
  · intro a
    simp
    grind
  · simp [getElem_dropLast_eq_getElem]

lemma sum_hookPath_eq_sum_sum_one_hookPath (n : ℕ) :
    ∑ p : γ.hookPath with p.path.length = n + 1 + 1, 1 / γ.card *
    ∏ i ∈ (Finset.univ : Finset (Fin (p.path.length))).erase ⟨p.path.length - 1, by
    grind [hookPath_length_ne_zero]⟩, 1 / ((γ.hookLength (p.path.get i) : ℝ≥0) - 1) =
    ∑ p : γ.hookPath with p.path.length = n + 1 ∧ p.path.getLast p.ne_nil ∉ γ.corners,
    ∑ x ∈ γ.hook (p.path.getLast p.ne_nil) with x ≠ p.path.getLast p.ne_nil,
    1 / γ.card * (1 / (γ.hookLength (p.path.getLast p.ne_nil) - 1)) *
    ∏ i ∈ (Finset.univ : Finset (Fin (p.path.length))).erase ⟨p.path.length - 1, by
    grind [hookPath_length_ne_zero]⟩, 1 / ((γ.hookLength (p.path.get i) : ℝ≥0) - 1) := by
  let R : Set (γ.hookPath × (ℕ × ℕ)) := { (p, x) | p.path.length = n + 1 ∧
    p.path.getLast p.ne_nil ∉ γ.corners ∧ x ∈ γ.hook (p.path.getLast p.ne_nil) ∧
    x ≠ p.path.getLast p.ne_nil}
  have hR : Fintype R := by
    let e : R → γ.hookPath × (Finset.univ : Finset γ.hookPath).biUnion
      (fun p ↦ γ.hook (p.path.getLast p.ne_nil)) := fun ⟨(p, x), h⟩ ↦
      (p, ⟨x, by
        simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
        use p
        exact h.2.2.1⟩)
    refine Fintype.ofInjective e ?_
    intro ⟨(p, x), hpx⟩ ⟨(q, y), hqy⟩ hpq
    simpa [e] using hpq
  rw [← Finset.sum_finset_product' R.toFinset _ _ (by grind)]
  let e : (p : γ.hookPath) →
    (hp : p ∈ Finset.filter (fun q ↦ q.path.length = n + 1 + 1) (Finset.univ : Finset _)) →
    γ.hookPath × (ℕ × ℕ) := fun p hp ↦ (p.dropLast, p.path.getLast p.ne_nil)
  refine Finset.sum_bij e ?_ ?_ ?_ ?_
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, ne_eq, Set.mem_toFinset,
      Set.mem_ofPred_eq, R, e]
    intro p hp
    simp [hp, length_dropLast, getLast_dropLast_notMem_corners, getLast_mem_hook_getLast_dropLast,
      getLast_ne_getLast_dropLast]
  · grind [eq_of_length_dropLast_getLast_eq]
  · simp only [ne_eq, Set.mem_toFinset, Set.mem_ofPred_eq, Finset.mem_filter, Finset.mem_univ,
      true_and, exists_prop, and_imp, Prod.forall, Prod.mk.injEq, R, e]
    intro p i j hp hpc hij hijl
    use p.extend (i, j) hij hijl
    simp [hp, extend_length, dropLast_extend, getLast_extend]
  · unfold e
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    nth_rw 3 [mul_comm]
    rw [mul_assoc, ← pmf_fun, ← pmf_fun]
    exact pmf_fun_eq_div_mul_dropLast γ (by lia)

lemma sum_partial_hookPath_pmf_eq_one {n : ℕ} (hγ : γ ≠ ⊥) :
    ∑ p : γ.hookPath with p.path.length = n + 1 ∨
    (p.path.length < n + 1 ∧ p.path.getLast p.ne_nil ∈ γ.corners), γ.pmf_fun p = 1 := by
  induction n with
  | zero =>
    simp only [zero_add, Order.lt_one_iff, List.length_eq_zero_iff, hookPath_ne_nil, false_and,
      or_false]
    have h : (1 : ℝ≥0) = ∑ p : γ.hookPath with p.path.length = 1, (1 / γ.card : ℝ≥0) := by
      rw [ne_eq, γ.eq_bot_iff_card_eq_zero] at hγ
      simp [path_length_eq_one_card, hγ]
    conv_rhs => rw [h]
    refine Finset.sum_congr rfl ?_
    intro p hp
    simp at hp
    suffices (Finset.univ : Finset (Fin (p.path.length))).erase ⟨p.path.length - 1,
        by grind [hookPath_length_ne_zero]⟩ = ∅ by
      simp [pmf_fun, this]
    grind
  | succ n ih =>
    classical
    have hd := disjoint_length_eq_length_lt_and_cornerHookPath γ n
    conv_rhs => rw [← ih, Finset.filter_or, Finset.sum_union hd]
    symm
    have h : ({p : γ.hookPath | p.path.length < n + 1 ∧ p.path.getLast p.ne_nil ∈ γ.corners} :
        Finset _) ⊆ ({p : γ.hookPath | p.path.length = n + 1 + 1 ∨
        p.path.length < n + 1 + 1 ∧ p.path.getLast p.ne_nil ∈ γ.corners} : Finset _) := by grind
    rw [← eq_tsub_iff_add_eq_of_le]
    · classical
      rw [← Finset.sum_sdiff h, add_tsub_cancel_right]
      have h' : ({p : γ.hookPath | p.path.length = n + 1 + 1 ∨ (p.path.length < n + 1 + 1 ∧
          p.path.getLast p.ne_nil ∈ γ.corners)} : Finset _) \ ({p : γ.hookPath |
          p.path.length < n + 1 ∧ p.path.getLast p.ne_nil ∈ γ.corners} : Finset _) =
          ({p : γ.hookPath | p.path.length = n + 1 + 1} : Finset _) ∪ ({p : γ.hookPath |
          p.path.length = n + 1 ∧ p.path.getLast p.ne_nil ∈ γ.corners} : Finset _) := by grind
      have hd' := disjoint_length_eq_length_eq_and_cornerHookPath γ n
      rw [h', Finset.sum_union hd', ← Finset.sum_filter_not_add_sum_filter
        {p : γ.hookPath | p.path.length = n + 1}
        (fun x : γ.hookPath ↦ x.path.getLast x.ne_nil ∈ γ.corners) _,
        Finset.filter_filter, Finset.filter_filter, add_left_inj]
      unfold pmf_fun
      rw [sum_hookPath_eq_sum_sum_one_hookPath γ n]
      simp_rw [← Finset.mul_sum]
      rw [Finset.mul_sum]
      refine Finset.sum_congr (by rfl) ?_
      intro p hp
      let b : ℝ≥0 := ∏ i ∈ (Finset.univ.erase ⟨p.path.length - 1, by grind⟩),
        1 / (γ.hookLength (p.path.get i) - 1)
      rw [Finset.sum_const b, nsmul_eq_mul]
      unfold b
      rw [mul_assoc, mul_eq_mul_left_iff]
      conv_rhs => simp only [one_div, NNReal.coe_inv, NNReal.coe_natCast, inv_eq_zero,
          Nat.cast_eq_zero, ← eq_bot_iff_card_eq_zero, hγ]
      rw [or_false, card_hook_ne_eq_hookLength_sub_one γ (γ.getLast_mem p), ← mul_assoc]
      norm_cast
      rw [one_div_mul_cancel, one_mul]
      simp [mem_corners_iff_hookLength_eq_one _ (γ.getLast_mem p)] at hp
      have hhl := γ.hookLength_ne_zero (p.path.getLast p.ne_nil)
      rw [Nat.cast_ne_zero]
      lia
    · exact Finset.sum_mono_set_of_nonneg (by simp) h

lemma cornerHookPath_eq_setOf_card_hookPath :
    ({p : γ.hookPath | p.path.getLast p.ne_nil ∈ γ.corners} : Finset _) =
    ({p : γ.hookPath | p.path.length = γ.card + 1 ∨
    (p.path.length < γ.card + 1 ∧ p.path.getLast p.ne_nil ∈ γ.corners)} : Finset _) := by
  grind [hookPath_length_le_card]



noncomputable abbrev pmf_fun' : γ.cornerHookPath → ℝ≥0∞ := fun ⟨p, _⟩ ↦ γ.pmf_fun p

noncomputable
def pmf (hγ : γ ≠ ⊥) : PMF γ.cornerHookPath  where
  val := γ.pmf_fun'
  property := by
    suffices 1 = ∑ p : γ.cornerHookPath, γ.pmf_fun' p by
      rw [this]
      exact hasSum_fintype γ.pmf_fun'
    unfold pmf_fun'
    simp only
    have h : ∑ p : γ.cornerHookPath, (γ.pmf_fun p : ℝ≥0∞) =
        ∑ p : γ.hookPath with p.path.getLast p.ne_nil ∈ γ.corners, (γ.pmf_fun p : ℝ≥0∞) := by
      refine Finset.sum_bij (fun p hp ↦ p) ?_ ?_ ?_ ?_ <;> simp
    rw [h, cornerHookPath_eq_setOf_card_hookPath γ, ← ENNReal.ofNNReal_finsetSum,
      sum_partial_hookPath_pmf_eq_one γ (n := γ.card) hγ]
    rfl

end YoungDiagram

end
end


/- Source module: KostkaNumbers.Diagrams.FinsuppEquiv -/
section
/-
Copyright (c) 2026 Noah Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Walker
-/




section

/-!
This shows that YoungDiagrams are equivalent to finitely supported antitone functions from ℕ to ℕ.
-/

open YoungDiagram

namespace YoungDiagram

def rowLen' (γ : YoungDiagram) : ℕ →₀ ℕ := ⟨Finset.range (γ.colLen 0),
  γ.rowLen, by simp [← Nat.pos_iff_ne_zero, ← mem_iff_lt_colLen, mem_iff_lt_rowLen]⟩

lemma rowLen'_anti (γ : YoungDiagram) : Antitone γ.rowLen' := by
  rw [Finsupp.coe_mk]
  exact γ.rowLen_anti

lemma rowLen'_eq_rowLen {γ : YoungDiagram} {i : ℕ} : γ.rowLen' i = γ.rowLen i := by
  simp [rowLen']

def ofRowLen' (f : ℕ →₀ ℕ) (hf : Antitone f) : YoungDiagram :=
  ⟨Finset.biUnion f.support (fun i ↦ {i} ×ˢ Finset.range (f i)),
  by
  simp only [IsLowerSet, Finset.singleton_product, Finset.coe_biUnion, Finset.mem_coe,
    Finsupp.mem_support_iff, ne_eq, Finset.coe_map, Function.Embedding.coeFn_mk, Finset.coe_range,
    Set.mem_iUnion, Set.mem_image, Set.mem_Iio, exists_prop, forall_exists_index, and_imp,
    Prod.forall, Prod.mk.injEq, exists_eq_right_right, Prod.mk_le_mk]
  intro a b c d hca hdb x hfx y hyfx hxa hyb
  rw [hxa] at hfx
  rw [hxa, hyb] at hyfx
  constructor
  · contrapose! hfx
    rw [← nonpos_iff_eq_zero, ← hfx]
    exact hf hca
  · specialize hf hca
    lia
  ⟩

@[simp] lemma mem_ofRowLen' (f : ℕ →₀ ℕ) (hf : Antitone f) (x : ℕ × ℕ) :
    x ∈ ofRowLen' f hf ↔ x.2 < f x.1 := by
  simp only [ofRowLen', Finset.singleton_product, mem_mk, Finset.mem_biUnion,
    Finsupp.mem_support_iff, Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk]
  constructor
  · intro h
    obtain ⟨a, _, ⟨b, hb, hx⟩⟩ := h
    simp [← hx, hb]
  · intro hx
    use x.1
    constructor
    · rw [← Nat.pos_iff_ne_zero]
      exact lt_of_le_of_lt (Nat.zero_le x.2) hx
    · use x.2

@[simp] lemma ofRowLen'_rowLen'_eq_self (γ : YoungDiagram) :
    ofRowLen' γ.rowLen' γ.rowLen'_anti = γ := by
  ext x
  simp [rowLen', ← mem_iff_lt_rowLen]

@[simp] lemma rowLen'_ofRowLen'_eq_self (f : ℕ →₀ ℕ) (hf : Antitone f) :
    (ofRowLen' f hf).rowLen' = f := by
  ext n
  simp only [rowLen', ofRowLen', Finsupp.coe_mk, rowLen_eq_card, row]
  suffices Finset.filter (fun c ↦ c.1 = n)
      (f.support.biUnion (fun i ↦ {i} ×ˢ Finset.range (f i))) =
      {n} ×ˢ Finset.range (f n) by
    rw [this]
    simp
  aesop

def equivRowLen' : YoungDiagram ≃ {f : ℕ →₀ ℕ // Antitone f} where
  toFun γ := ⟨γ.rowLen', γ.rowLen'_anti⟩
  invFun f := ofRowLen' f.1 f.2
  left_inv := ofRowLen'_rowLen'_eq_self
  right_inv := by
    intro ⟨f, hf⟩
    simp


@[simp] lemma rowLen'_eq_zero {γ : YoungDiagram} {i : ℕ} (hi : ¬ i < γ.colLen 0) :
    γ.rowLen' i = 0 := by
  rw [← mem_iff_lt_colLen, mem_iff_lt_rowLen, Nat.pos_iff_ne_zero] at hi
  push Not at hi
  exact hi

lemma rowLen'_eq_zero_of_ge_length {γ : YoungDiagram} (i : ℕ) (hi : i ≥ γ.rowLens.length) :
    γ.rowLen' i = 0 := by
  rw [length_rowLens] at hi
  exact rowLen'_eq_zero (by lia)

@[simp]
lemma rowLen'_bot : (⊥ : YoungDiagram).rowLen' = 0 := by
  ext
  simp [rowLen']

lemma rowLen'_eq_iff {γ γ' : YoungDiagram} : γ.rowLen' = γ'.rowLen' ↔ γ = γ' := by
  constructor
  · intro h
    rw! [← γ.ofRowLen'_rowLen'_eq_self, h, γ'.ofRowLen'_rowLen'_eq_self]
    rfl
  · intro h
    rw [h]

end YoungDiagram

end
end


/- Source module: KostkaNumbers.HookLength.F -/
section
/-
Copyright (c) 2026 Noah Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Walker
-/





/-!
Define the function `F` from the GNW paper as well as the useful collection, `SubSingle`.
-/

section

open MeasureTheory YoungDiagram
open scoped ENNReal NNReal

abbrev SubSingle (γ : YoungDiagram) := {a : ℕ //
  (∀ i, γ.rowLen' i - (Finsupp.single a 1) i ≥ γ.rowLen' (i + 1)) ∧
  (∀ i, (Finsupp.single a 1) i ≤ γ.rowLen' i)}

variable {γ : YoungDiagram}

noncomputable
instance : Fintype (SubSingle γ) := by
  let f : SubSingle γ → {g : ℕ →₀ ℕ // g ≤ γ.rowLen'} := fun ⟨a, ha⟩ ↦ ⟨Finsupp.single a 1, ha.2⟩
  have : Fintype {g : ℕ →₀ ℕ // g ≤ γ.rowLen'} := by
    have : Finite {g : ℕ →₀ ℕ // g ≤ γ.rowLen'} := instFiniteSubtypeLeOfLocallyFiniteOrderBot
    exact Fintype.ofFinite _
  refine Fintype.ofInjective f ?_
  intro ⟨a, ha⟩ ⟨b, hb⟩
  simp [f, Finsupp.single_left_inj]

lemma subSingle_sub_cond {x : ℕ × ℕ} (hx : x ∈ γ.corners) :
    ∀ i : ℕ, γ.rowLen' i - (Finsupp.single x.1 1) i ≥ γ.rowLen' (i + 1) := by
  simp only [corners, Finset.mem_filter, mem_cells] at hx
  obtain ⟨hx, hxr, hxc⟩ := hx
  intro i
  rw [Finsupp.single_apply]
  split_ifs with hi
  · rw [γ.rowLen'_eq_rowLen, ← hi, ← hxr, add_tsub_cancel_right, rowLen'_eq_rowLen, hxc,
      ge_iff_le, ← Std.not_lt, ← γ.mem_iff_lt_rowLen, γ.mem_iff_lt_colLen]
    exact Nat.lt_irrefl _
  · simp [γ.rowLen'_anti i.le_succ]

lemma subSingle_le_rowLen' {x : ℕ × ℕ} (hx : x ∈ γ.corners) :
    ∀ i : ℕ, (Finsupp.single x.1 1) i ≤ γ.rowLen' i := by
  simp only [corners, Finset.mem_filter, mem_cells] at hx
  obtain ⟨hx, hxr, hxc⟩ := hx
  intro i
  rw [Finsupp.single_apply]
  split_ifs with hi
  · refine Nat.le_of_pred_lt ?_
    rw [rowLen'_eq_rowLen, ← hi, ← γ.mem_iff_lt_rowLen]
    exact γ.up_left_mem (by rfl) zero_le hx
  · exact zero_le

noncomputable
abbrev F : YoungDiagram → ℝ≥0∞ := fun γ ↦ (γ.card).factorial / ∏ x ∈ γ.cells, γ.hookLength x

lemma coe_F :
    (F γ : ℝ≥0∞) = (γ.card).factorial / ∏ x ∈ γ.cells, γ.hookLength x := rfl

lemma F_ne_zero : F γ ≠ 0 := by
  simp [F, Nat.factorial_ne_zero, ENNReal.prod_ne_top]

lemma F_ne_top : F γ ≠ ⊤ := by
  simp [F, ENNReal.div_eq_top, Nat.factorial_ne_zero, Finset.prod_eq_zero_iff, hookLength_ne_zero]

end
end


/- Source module: KostkaNumbers.HookLength.Prob -/
section
/-
Copyright (c) 2026 Noah Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Walker
-/







/-!
This file formalizes part of the GNW proof involving p(A, B ∣ a, b).
-/

section

open MeasureTheory YoungDiagram
open scoped ENNReal NNReal


variable {γ : YoungDiagram}

lemma pmf_downHookPath {x : ℕ × ℕ} (hx : x ∈ γ.corners) {t : Finset ℕ}
    (htx : t ∈ (Finset.range x.2).powerset) :
    γ.pmf (ne_bot_of_mem_corners hx) (downHookPath hx htx) =
    1 / γ.card * ∏ j ∈ t, 1 / (γ.hookLength (x.1, j) - 1 : ℝ≥0∞) := by
  unfold pmf pmf_fun' pmf_fun
  simp only [DFunLike.coe, one_div, List.get_eq_getElem, Finset.prod_inv_distrib, ENNReal.coe_mul]
  congr
  · rw [ENNReal.coe_inv, ENNReal.coe_natCast]
    simp only [ne_eq, Nat.cast_eq_zero, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem,
      mem_cells, Prod.forall, not_forall, Decidable.not_not]
    use x.1, x.2
    exact corners_le hx
  · rw [ENNReal.coe_inv, ENNReal.ofNNReal_finsetProd, ENNReal.prod_inv_distrib]
    · refine Finset.prod_bij (fun i hi ↦ (downHookPath hx htx).1.path[i].2) ?_ ?_ ?_ ?_
      · unfold downHookPath
        simp only [List.length_append, List.length_map, Finset.length_sort, List.length_cons,
          List.length_nil, zero_add, add_tsub_cancel_right, Finset.mem_erase, ne_eq,
          Finset.mem_univ, and_true, Fin.getElem_fin, List.getElem_append, List.getElem_map,
          List.getElem_singleton]
        intro ⟨i, hi⟩ hi'
        simp at hi hi'
        have hi'' : i < t.card := by lia
        simp only [hi'', ↓reduceDIte]
        rw [← Finset.mem_sort (· ≤ ·)]
        exact List.getElem_mem _
      · unfold downHookPath
        simp only [List.length_append, List.length_map, Finset.length_sort, List.length_cons,
          List.length_nil, zero_add, add_tsub_cancel_right, Finset.mem_erase, ne_eq,
          Finset.mem_univ, and_true, Fin.getElem_fin, List.getElem_append, List.getElem_map,
          List.getElem_singleton]
        intro ⟨i, hi⟩ hi' ⟨j, hj⟩ hj'
        simp at hi hi' hj hj'
        have hi'' : i < t.card := by lia
        have hj'' : j < t.card := by lia
        simp [hi'', hj'', List.Nodup.getElem_inj_iff]
      · unfold downHookPath
        simp only [Fin.getElem_fin, List.getElem_append, List.length_map, Finset.length_sort,
          List.getElem_map, List.getElem_singleton, List.length_append, List.length_cons,
          List.length_nil, zero_add, add_tsub_cancel_right, Finset.mem_erase, ne_eq,
          Finset.mem_univ, and_true, exists_prop]
        intro j hj
        rw [← Finset.mem_sort (· ≤ ·)] at hj
        obtain ⟨n, hn, hnj⟩ := List.getElem_of_mem hj
        use ⟨n, by grind⟩
        simp at hn
        simp [hn.ne, hnj, hn]
      · unfold downHookPath
        simp
        grind
    · simp only [Finset.coe_erase, Finset.coe_univ, ENNReal.coe_sub, ENNReal.coe_natCast,
        ENNReal.coe_one, ne_eq, ENNReal.sub_eq_top_iff, ENNReal.natCast_ne_top, ENNReal.one_ne_top,
        not_false_eq_true, and_true, or_true]
      exact Pairwise.set_pairwise (fun ⦃i j⦄ a ↦ trivial) _
    · simp only [ne_eq, Finset.prod_eq_zero_iff, Finset.mem_erase, Finset.mem_univ, and_true,
        not_exists, not_and]
      intro ⟨i, hi⟩ hi'
      simp only [Fin.mk.injEq] at hi' ⊢
      exact hookLength_path_getElem_ne_zero i (by lia) (downHookPath hx htx).2

lemma pmf_leftHookPath {x : ℕ × ℕ} (hx : x ∈ γ.corners) {s : Finset ℕ}
    (hsx : s ∈ (Finset.range x.1).powerset) :
    γ.pmf (ne_bot_of_mem_corners hx) (leftHookPath hx hsx) =
    1 / γ.card * ∏ i ∈ s, 1 / (γ.hookLength (i, x.2) - 1 : ℝ≥0∞) := by
  unfold pmf pmf_fun' pmf_fun
  simp only [DFunLike.coe, one_div, List.get_eq_getElem, Finset.prod_inv_distrib, ENNReal.coe_mul]
  congr
  · rw [ENNReal.coe_inv, ENNReal.coe_natCast]
    simp only [ne_eq, Nat.cast_eq_zero, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem,
      mem_cells, Prod.forall, not_forall, Decidable.not_not]
    use x.1, x.2
    exact corners_le hx
  · rw [ENNReal.coe_inv, ENNReal.ofNNReal_finsetProd, ENNReal.prod_inv_distrib]
    · refine Finset.prod_bij (fun i hi ↦ (leftHookPath hx hsx).1.path[i].1) ?_ ?_ ?_ ?_
      · unfold leftHookPath
        simp only [List.length_append, List.length_map, Finset.length_sort, List.length_cons,
          List.length_nil, zero_add, add_tsub_cancel_right, Finset.mem_erase, ne_eq,
          Finset.mem_univ, and_true, Fin.getElem_fin, List.getElem_append, List.getElem_map,
          List.getElem_singleton]
        intro ⟨i, hi⟩ hi'
        simp at hi hi'
        have hi'' : i < s.card := by lia
        simp only [hi'', ↓reduceDIte]
        rw [← Finset.mem_sort (· ≤ ·)]
        exact List.getElem_mem _
      · unfold leftHookPath
        simp only [List.length_append, List.length_map, Finset.length_sort, List.length_cons,
          List.length_nil, zero_add, add_tsub_cancel_right, Finset.mem_erase, ne_eq,
          Finset.mem_univ, and_true, Fin.getElem_fin, List.getElem_append, List.getElem_map,
          List.getElem_singleton]
        intro ⟨i, hi⟩ hi' ⟨j, hj⟩ hj'
        simp at hi hi' hj hj'
        have hi'' : i < s.card := by lia
        have hj'' : j < s.card := by lia
        simp [hi'', hj'', List.Nodup.getElem_inj_iff]
      · unfold leftHookPath
        simp only [Fin.getElem_fin, List.getElem_append, List.length_map, Finset.length_sort,
          List.getElem_map, List.getElem_singleton, List.length_append, List.length_cons,
          List.length_nil, zero_add, add_tsub_cancel_right, Finset.mem_erase, ne_eq,
          Finset.mem_univ, and_true, exists_prop]
        intro j hj
        rw [← Finset.mem_sort (· ≤ ·)] at hj
        obtain ⟨n, hn, hnj⟩ := List.getElem_of_mem hj
        use ⟨n, by grind⟩
        simp at hn
        simp [hn.ne, hnj, hn]
      · unfold leftHookPath
        simp
        grind
    · simp only [Finset.coe_erase, Finset.coe_univ, ENNReal.coe_sub, ENNReal.coe_natCast,
        ENNReal.coe_one, ne_eq, ENNReal.sub_eq_top_iff, ENNReal.natCast_ne_top, ENNReal.one_ne_top,
        not_false_eq_true, and_true, or_true]
      exact Pairwise.set_pairwise (fun ⦃i j⦄ a ↦ trivial) _
    · simp only [ne_eq, Finset.prod_eq_zero_iff, Finset.mem_erase, Finset.mem_univ, and_true,
        not_exists, not_and]
      intro ⟨i, hi⟩ hi'
      simp only [Fin.mk.injEq] at hi' ⊢
      exact hookLength_path_getElem_ne_zero i (by lia) (leftHookPath hx hsx).2


lemma pmf_fun_eq_div_mul_tail (p : γ.hookPath) (hp : p.path.length > 1)
    (hpc : p.path.getLast p.ne_nil ∈ γ.corners) :
    γ.pmf_fun p = 1 / (γ.hookLength (p.path.head p.ne_nil) - 1) * γ.pmf_fun p.tail := by
  have hγ : 1 / (γ.card : ℝ≥0) ≠ 0 := by
    simp only [one_div, ne_eq, inv_eq_zero, Nat.cast_eq_zero, ← eq_bot_iff_card_eq_zero,
      ne_bot_of_hookPath p, not_false_eq_true]
  simp only [pmf_fun, mul_left_comm, mul_eq_mul_left_iff, hγ, or_false]
  have hps :
      1 / (γ.hookLength (p.path.head p.ne_nil) - 1 : ℝ≥0) *
      ∏ i ∈ ((Finset.univ : Finset (Fin p.path.length)).erase
      ⟨p.path.length - 1, by grind [hookPath_length_ne_zero]⟩).erase ⟨0, by lia⟩,
      1 / (γ.hookLength (p.path.get i) - 1 : ℝ≥0) =
      ∏ i ∈ (Finset.univ : Finset (Fin p.path.length)).erase
      ⟨p.path.length - 1, by grind [hookPath_length_ne_zero]⟩,
      1 / (γ.hookLength (p.path.get i) - 1 : ℝ≥0) := by
    simp_rw [List.get_eq_getElem]
    have ha : ⟨0, by lia⟩ ∈ (Finset.univ : Finset (Fin p.path.length)).erase
        ⟨p.path.length - 1, by grind [hookPath_length_ne_zero]⟩ := by
      grind
    rw [List.head_eq_getElem, ← Finset.mul_prod_erase _ _ ha]
  have hγh : 1 / (γ.hookLength (p.path.head p.ne_nil) - 1 : ℝ≥0) ≠ 0 := by
    rw [one_div, ne_eq, inv_eq_zero, ← ne_eq]
    exact hookLength_head_sub_one_ne_zero hp hpc
  simp only [← hps, mul_eq_mul_left_iff, hγh, or_false]
  simp_rw [List.get_eq_getElem]
  have hp' : p.path.length = p.tail.path.length + 1 := by
    simp [length_tail, hp, tsub_add_cancel_of_le hp.le]
  symm
  rw! [hp', add_tsub_cancel_right]
  refine Finset.prod_nbij (Fin.succ (n := p.tail.path.length)) ?_ ?_ ?_ ?_
  · simp
    grind
  · exact Set.injOn_of_injective <| Fin.succ_injective _
  · intro ⟨a, ha⟩
    simp only [Fin.zero_eta, Finset.coe_erase, Finset.coe_univ, Set.mem_sdiff, Set.mem_univ,
      Set.mem_singleton_iff, Fin.mk.injEq, true_and, Fin.mk_eq_zero, Set.mem_image, and_imp]
    intro ha' ha0
    use ⟨a - 1, by lia⟩
    grind
  · simp [path_tail _ hp]


noncomputable
abbrev pab {x : ℕ × ℕ} (hx : x ∈ γ.corners) (s t : Finset ℕ) :=
  (γ.pmf (ne_bot_of_mem_corners hx)).toMeasure
  {p : γ.cornerHookPath | p.1.horizontal = s ∧ p.1.vertical = t ∧ p.1.path.getLast p.1.ne_nil = x}

lemma pab_eq {x : ℕ × ℕ} (hx : x ∈ γ.corners) (s t : Finset ℕ) :
    pab hx s t =
    ∑ p : γ.hookPath with p.horizontal = SetLike.coe s ∧ p.vertical  = SetLike.coe t ∧
    p.path.getLast p.ne_nil = x, γ.pmf_fun p := by
  unfold pab
  rw [← Set.coe_toFinset {p : γ.cornerHookPath | p.1.horizontal = s ∧ p.1.vertical = t ∧
      p.1.path.getLast p.1.ne_nil = x}, PMF.toMeasure_apply_finset, Set.toFinset_ofPred]
  simp only [pmf, pmf_fun', DFunLike.coe]
  rw [ENNReal.ofNNReal_finsetSum]
  refine Finset.sum_nbij (fun p : γ.cornerHookPath ↦ p.1) ?_ ?_ ?_ ?_
  · simp
  · simp
  · intro p
    simp
    grind
  · simp

lemma pab_empty_left_eq {x : ℕ × ℕ} (hx : x ∈ γ.corners) (t : Finset ℕ)
    (htx : t ∈ (Finset.range x.2).powerset) :
    pab hx ∅ t = 1 / γ.card * ∏ j ∈ t, 1 / (γ.hookLength (x.1, j) - 1 : ℝ≥0∞) := by
  simp only [PMF.toMeasure_apply_fintype, Finset.coe_empty, setOf_horizontal_empty_eq_down hx htx,
    Finsupp.set_indicator_singleton, Finsupp.univ_sum_single_apply]
  rw [pmf_downHookPath hx htx]

lemma pab_empty_right_eq {x : ℕ × ℕ} (hx : x ∈ γ.corners) (s : Finset ℕ)
    (hsx : s ∈ (Finset.range x.1).powerset) :
    pab hx s ∅ = 1 / γ.card * ∏ i ∈ s, 1 / (γ.hookLength (i, x.2) - 1 : ℝ≥0∞) := by
  simp only [PMF.toMeasure_apply_fintype, Finset.coe_empty, setOf_vertical_empty_eq_left hx hsx,
    Finsupp.set_indicator_singleton, Finsupp.univ_sum_single_apply]
  rw [pmf_leftHookPath hx hsx]

lemma pab_recursion {x : ℕ × ℕ} (hx : x ∈ γ.corners) {s t : Finset ℕ}
    (hs : s ∈ (Finset.range x.1).powerset) (ht : t ∈ (Finset.range x.2).powerset)
    (hs0 : s.Nonempty) (ht0 : t.Nonempty) :
    pab hx s t =
    1 / (γ.hookLength (s.min' hs0, t.min' ht0) - 1) *
    (pab hx (s.erase (s.min' hs0)) t + pab hx s (t.erase (t.min' ht0))) := by
  simp_rw [pab_eq, ENNReal.ofNNReal_finsetSum]
  classical rw [← Finset.sum_union, Finset.filter_union_right, Finset.mul_sum]
  · refine Finset.sum_nbij (fun p ↦ p.tail) ?_ ?_ ?_ ?_
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.coe_erase, and_imp]
      intro p hps hpt hpx
      have hp1 : p.path.length > 1 := length_gt_one_of_horz_nonempty hps hs0
      by_cases! hh : p.path[1].1 = s.min' hs0
      · right
        simp [path_tail p hp1, hpx, horizontal_tail_of_eq_min' hp1 hps hs0 hh,
          vertical_tail_of_ne_min' hp1 hpt ht0 ((eq_min'_iff_ne_min' hp1 hps hpt hs0 ht0).mp hh)]
      · left
        have hv : p.path[1].2 = t.min' ht0 := by
          rwa [ne_eq, eq_min'_iff_ne_min' hp1 hps hpt hs0 ht0, not_not] at hh
        simp [path_tail p hp1, hpx, horizontal_tail_of_ne_min' hp1 hps hs0 hh,
          vertical_tail_of_eq_min' hp1 hpt ht0 hv]
    · intro p
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq, and_imp]
      intro hps hpt hpx q hqs hqt hqx hpq
      have hp1 : p.path.length > 1 := length_gt_one_of_horz_nonempty hps hs0
      have hq1 : q.path.length > 1 := length_gt_one_of_horz_nonempty hqs hs0
      apply hookPath.eq_of_path_eq
      apply_fun hookPath.path at hpq
      rw [path_tail p hp1, path_tail q hq1] at hpq
      rw [← List.cons_head_tail p.ne_nil, ← List.cons_head_tail q.ne_nil, hpq,
        head_eq_horz_vert_min hps hpt hs0 ht0, head_eq_horz_vert_min hqs hqt hs0 ht0]
    · intro p hp
      simp only [Finset.coe_erase, Finset.coe_filter, Finset.mem_univ, true_and,
        Set.mem_ofPred_eq] at hp
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_image, Set.mem_ofPred_eq]
      have hst : p.path.head p.ne_nil ∈ γ.hook (s.min' hs0, t.min' ht0) := by
        simp only [hook, ge_iff_le, Finset.mem_filter, mem_cells]
        constructor
        · rw [← mem_cells]
          exact mem_cells_of_mem_hookPath (List.head_mem p.ne_nil)
        rcases hp with hp | hp
        · right
          rw [← Finset.coe_singleton, ← Finset.coe_sdiff] at hp
          simp only [head_snd_eq_vert_min hp.2.1 ht0, and_true]
          by_cases! hs0' : (s \ {s.min' hs0}).Nonempty
          · rw [head_fst_eq_horz_min hp.1 hs0']
            simp only [Finset.le_min'_iff, Finset.mem_sdiff, Finset.mem_singleton, and_imp]
            intro y hy _
            exact Finset.min'_le _ _ hy
          · simp only [Finset.sdiff_eq_empty_iff_subset, Finset.subset_singleton_iff,
              Finset.nonempty_iff_ne_empty.mp hs0, false_or] at hs0'
            suffices (p.path.head p.ne_nil).1 = x.1 by grind
            rw [Prod.ext_iff] at hp
            rw [← hp.2.2.1]
            apply And.left at hp
            conv at hp => rhs; rhs; lhs; rw [hs0']
            simp only [hookPath.horizontal, Prod.exists, exists_and_right, exists_eq_right,
              sdiff_self, Finset.bot_eq_empty, Finset.coe_empty, Set.sdiff_eq_empty,
              Set.subset_singleton_iff, Set.mem_ofPred_eq, forall_exists_index] at hp
            exact hp (p.path.head p.ne_nil).1 (p.path.head p.ne_nil).2 (List.head_mem _)
        · left
          rw [← Finset.coe_singleton, ← Finset.coe_sdiff] at hp
          simp only [head_fst_eq_horz_min hp.1 hs0, true_and]
          by_cases! ht0' : (t \ {t.min' ht0}).Nonempty
          · rw [head_snd_eq_vert_min hp.2.1 ht0']
            simp only [Finset.le_min'_iff, Finset.mem_sdiff, Finset.mem_singleton, and_imp]
            intro y hy _
            exact Finset.min'_le _ _ hy
          · simp only [Finset.sdiff_eq_empty_iff_subset, Finset.subset_singleton_iff,
              Finset.nonempty_iff_ne_empty.mp ht0, false_or] at ht0'
            suffices (p.path.head p.ne_nil).2 = x.2 by grind
            rw [Prod.ext_iff] at hp
            rw [← hp.2.2.2]
            apply And.right at hp; apply And.left at hp
            conv at hp => rhs; rhs; lhs; rw [ht0']
            simp only [Prod.exists, exists_eq_right, sdiff_self, Finset.bot_eq_empty,
              Finset.coe_empty, Set.sdiff_eq_empty, Set.subset_singleton_iff, Set.mem_ofPred_eq,
              forall_exists_index] at hp
            exact hp (p.path.head p.ne_nil).2 (p.path.head p.ne_nil).1 (List.head_mem _)
      have hst' : (s.min' hs0, t.min' ht0) ≠ p.path.head p.ne_nil := by
        rw [ne_eq, Prod.ext_iff, not_and_or]
        rcases hp with hp | hp
        · left
          by_cases! hh : (p.path.head p.ne_nil).1 ∈ p.horizontal
          · grind
          · simp only [Set.mem_sdiff, Prod.exists, exists_and_right, exists_eq_right,
              Set.mem_ofPred_eq, Set.mem_singleton_iff, not_and, Decidable.not_not,
              forall_exists_index] at hh
            specialize hh (p.path.head p.ne_nil).2 (List.head_mem _)
            rw [hh, hp.2.2]
            refine ne_of_lt ?_
            obtain ⟨a, ha⟩ := hs0
            exact lt_of_le_of_lt (Finset.min'_le _ _ ha) (by grind)
        · right
          by_cases! hv : (p.path.head p.ne_nil).2 ∈ p.vertical
          · grind
          · simp only [Set.mem_sdiff, Prod.exists, exists_eq_right,
              Set.mem_ofPred_eq, Set.mem_singleton_iff, not_and, Decidable.not_not,
              forall_exists_index] at hv
            specialize hv (p.path.head p.ne_nil).1 (List.head_mem _)
            rw [hv, hp.2.2]
            refine ne_of_lt ?_
            obtain ⟨a, ha⟩ := ht0
            exact lt_of_le_of_lt (Finset.min'_le _ _ ha) (by grind)
      use p.cons hst hst'
      constructor
      constructor
      · rcases hp with hp | hp
        · rw [cons_horizontal_of_mem_vertical, hp.1, Set.sdiff_union_of_subset]
          · simp [Finset.min'_mem]
          · simp [hp.2.1, Finset.min'_mem]
        · rw [cons_horizontal_of_mem_horizontal, hp.1]
          simp [hp.1, Finset.min'_mem]
      constructor
      · rcases hp with hp | hp
        · rw [cons_vertical_of_mem_vertical, hp.2.1]
          simp [hp.2.1, Finset.min'_mem]
        · rw [cons_vertical_of_mem_horizontal, hp.2.1, Set.sdiff_union_of_subset]
          · simp [Finset.min'_mem]
          · simp [hp.1, Finset.min'_mem]
      · rw [getLast_cons]
        grind
      · exact tail_cons p hst hst'
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      have hp1 : p.path.length > 1 := length_gt_one_of_horz_nonempty hp.1 hs0
      have hpc : p.path.getLast p.ne_nil ∈ γ.corners := hp.2.2 ▸ hx
      rw [pmf_fun_eq_div_mul_tail p hp1 hpc, ENNReal.coe_mul, ENNReal.coe_div]
      · rw [head_eq_horz_vert_min hp.1 hp.2.1 hs0 ht0]
        rfl
      · exact hookLength_head_sub_one_ne_zero hp1 hpc
  · intro S hS hS' p hp
    have hp' := hS' hp
    apply hS at hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp hp'
    apply And.left at hp
    rw [hp'.1] at hp
    have hs : s ≠ s.erase (s.min' hs0) := (Finset.erase_ne_self.mpr (Finset.min'_mem s hs0)).symm
    rw [Finset.coe_inj] at hp
    contradiction

end
end


/- Source module: KostkaNumbers.Diagrams.Diagrams -/
section
/-
Copyright (c) 2026 Noah Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Walker
-/




/-!
Some additional lemmas about Young Diagrams that are used.  These are either more complicated to
prove or more specific, so I don't plan to upstream them to Mathlib. The main result of this file is
`card_ofRowLens`, which shows `(ofRowLens L hL).card = L.sum`
-/

section

namespace YoungDiagram

variable {γ : YoungDiagram}

lemma cells_eq_biUnion_row : γ.cells = Finset.biUnion
    (Finset.univ : Finset (Fin (γ.rowLens.length))) (fun x ↦ γ.row x) := by
  ext x
  simp only [mem_cells, Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · intro h
    use ⟨x.1, by
      rw [length_rowLens, ← mem_iff_lt_colLen]
      exact γ.up_left_mem (by rfl) (Nat.zero_le x.2) h⟩
    simp [mem_row_iff, h]
  · grind [mem_row_iff]

lemma disjoint_row {i j : ℕ} (h : i ≠ j) : Disjoint (γ.row i) (γ.row j) := by
  grind [Disjoint, mem_row_iff]

lemma card_eq_sum_rowLens_get : γ.card = ∑ i : Fin (γ.rowLens.length), γ.rowLens.get i := by
  simp only [List.get_eq_getElem, get_rowLens, rowLen_eq_card]
  rw [← Finset.card_biUnion, YoungDiagram.card, cells_eq_biUnion_row]
  simp only [Set.PairwiseDisjoint, Finset.coe_univ]
  intro a _ b _ hab
  simp only [Function.onFun]
  exact disjoint_row <| Fin.val_ne_of_ne hab

lemma card_eq_sum_rowLen : γ.card = ∑ i : Fin (γ.rowLens.length + 1), γ.rowLen i := by
  let r : Fin (γ.rowLens.length + 1) := ⟨γ.rowLens.length, Nat.lt_add_one γ.rowLens.length⟩
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ r)]
  have hrl : ¬ γ.rowLen r.1 ≠ 0 := by
    simp [← Nat.pos_iff_ne_zero, ← mem_iff_lt_rowLen, mem_iff_lt_colLen, r]
  push Not at hrl
  rw [hrl, card_eq_sum_rowLens_get, add_zero]
  let e : (i : Fin γ.rowLens.length) → (i ∈ Finset.univ) → Fin (γ.rowLens.length + 1) :=
    fun i _ ↦ ⟨i.1, lt_trans i.2 (Nat.lt_add_one γ.rowLens.length)⟩
  refine Finset.sum_bij e ?_ ?_ ?_ ?_
  · grind
  · grind
  · simp only [Finset.mem_erase, ne_eq, Finset.mem_univ, and_true, exists_const, e, r]
    intro i hi
    rw [Fin.eq_mk_iff_val_eq] at hi
    use ⟨i, by lia⟩
  · simp only [Finset.mem_univ, List.get_eq_getElem, get_rowLens, imp_self, implies_true, e]

lemma card_eq_sum_rowLens : γ.card = γ.rowLens.sum := by
  simp only [card_eq_sum_rowLens_get, List.get_eq_getElem, Fin.sum_univ_getElem]

@[simp]
lemma card_ofRowLens {L : List ℕ} {hL : L.SortedGE} (hp : ∀ x ∈ L, 0 < x) :
    (ofRowLens L hL).card = L.sum := by
  rw [card_eq_sum_rowLens_get, rowLens_ofRowLens_eq_self hp]
  simp only [List.get_eq_getElem, Fin.sum_univ_getElem]

@[simp]
lemma rowLen_eq_zero {γ : YoungDiagram} {i : ℕ} (hi : ¬ i < γ.colLen 0) :
    γ.rowLen i = 0 := by
  rw [← mem_iff_lt_colLen, mem_iff_lt_rowLen, Nat.pos_iff_ne_zero] at hi
  exact Function.notMem_support.mp hi

@[simp]
lemma rowLen_ofRowLens' {w : List ℕ} {hw : w.SortedGE} {i : ℕ} (hi : i < w.length) :
    (ofRowLens w hw).rowLen i = w[i] := by
  simp [rowLen, Nat.find_eq_iff, mem_ofRowLens, hi]

@[simp]
lemma colLen_ofRowLens_two {a b : ℕ} {hab : [a, b].SortedGE} {i : ℕ} :
    (ofRowLens [a, b] hab).colLen i = if i < a then if i < b then 2 else 1 else 0 := by
  split_ifs
  all_goals simp [colLen, Nat.find_eq_iff, mem_ofRowLens]; grind

@[simp]
lemma colLen_ofRowLens_three {a b c : ℕ} {habc : [a, b, c].SortedGE} {i : ℕ} :
    (ofRowLens [a, b, c] habc).colLen i =
    if i < a then if i < b then if i < c then 3 else 2 else 1 else 0 := by
  split_ifs
  all_goals simp [colLen, Nat.find_eq_iff, mem_ofRowLens]; grind

end YoungDiagram

end
end


/- Source module: KostkaNumbers.Diagrams.Sub -/
section
/-
Copyright (c) 2026 Noah Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Walker
-/







/-!
Defines an operation on Young diagrams that creates a new diagram by removing a specified number of
boxes from each row.  We also introduce a type `SubRowLensType` that is useful in several places for
describing the functions we want to subtract by.
-/

section

open YoungDiagram SemistandardYoungTableau

namespace YoungDiagram

open Classical in
noncomputable
def sub (γ : YoungDiagram) (f : ℕ →₀ ℕ) : YoungDiagram :=
  if h : ∀ i, γ.rowLen' i - f i ≥ γ.rowLen' (i + 1) - (f (i + 1))
  then ofRowLen' (γ.rowLen' - f) (antitone_nat_of_succ_le h) else ⊥

variable {γ : YoungDiagram} {f : ℕ →₀ ℕ}

@[simp] lemma mem_sub (x : ℕ × ℕ)
    (h : ∀ i, γ.rowLen' i - f i ≥ γ.rowLen' (i + 1) - (f (i + 1))) :
    x ∈ γ.sub f ↔ x.2 < γ.rowLen' x.1 - f x.1 := by
  simp [sub, h]

@[simp] lemma sub_rowLen' (h : ∀ i, γ.rowLen' i - f i ≥ γ.rowLen' (i + 1) - (f (i + 1))) :
    (γ.sub f).rowLen' = γ.rowLen' - f := by
  simp [sub, h]

@[simp]
lemma sub_bot {f : ℕ →₀ ℕ} : (⊥ : YoungDiagram).sub f = ⊥ := by
  ext
  simp [sub, ofRowLen']

@[simp]
lemma sub_zero (γ : YoungDiagram) : γ.sub (0 : ℕ →₀ ℕ) = γ := by
  rw [← rowLen'_eq_iff, sub_rowLen', tsub_zero]
  intro i
  simp [γ.rowLen'_anti (Nat.le_add_right i 1)]

lemma sub_le (h : ∀ i, γ.rowLen' i - f i ≥ γ.rowLen' (i + 1) - (f (i + 1))) :
    γ.sub f ≤ γ := by
  intro x hx
  rw [mem_sub _ h] at hx
  rw [mem_iff_lt_rowLen]
  exact lt_of_lt_of_le hx <| Nat.sub_le (γ.rowLen x.1) (f x.1)

theorem sub_cond (h : ∀ i, γ.rowLen' i - f i ≥ γ.rowLen' (i + 1)) :
    ∀ i, γ.rowLen' i - f i ≥ γ.rowLen' (i + 1) - (f (i + 1)) := by
  grind

lemma exists_mem_sdiff_of_ne {g : ℕ →₀ ℕ}
    (hf : ∀ i, γ.rowLen' i - f i ≥ γ.rowLen' (i + 1))
    (hg : ∀ i, γ.rowLen' i - g i ≥ γ.rowLen' (i + 1))
    (hf' : ∀ i, f i ≤ γ.rowLen' i) (hg' : ∀ i, g i ≤ γ.rowLen' i)
    (hfg : f ≠ g) :
    ∃ x ∈ γ, (x ∈ (γ.sub f).cells \ (γ.sub g).cells) ∨
    (x ∈ (γ.sub g).cells \ (γ.sub f).cells) := by
  rw [Finsupp.ne_iff] at hfg
  obtain ⟨i, hfg⟩ := hfg
  wlog hfg' : f i > g i generalizing f g
  · specialize this hg hf hg' hf' hfg.symm ?_
    · push Not at hfg'
      exact Nat.lt_of_le_of_ne hfg' hfg
    · obtain ⟨x, this⟩ := this
      rw [Or.comm] at this
      use x
  · use (i, γ.rowLen' i - (g i + 1))
    constructor
    · rw [mem_iff_lt_rowLen, ← rowLen'_eq_rowLen]
      grind
    · right
      simp only [Finset.mem_sdiff, mem_cells, mem_sub _ (sub_cond hf),
        mem_sub _ (sub_cond hg), not_lt, tsub_le_iff_right]
      grind

lemma card_sub (h : ∀ i, γ.rowLen' i - f i ≥ γ.rowLen' (i + 1) - (f (i + 1)))
    (h' : ∀ i, f i ≤ γ.rowLen' i) :
    (γ.sub f).card = γ.card - ∑ x ∈ f.support, f x := by
  simp only [card_eq_sum_rowLens_get, List.get_eq_getElem, get_rowLens, ← rowLen'_eq_rowLen,
    sub_rowLen' h, Finsupp.coe_tsub, Pi.sub_apply]
  have hf : ∑ x ∈ f.support, f x = ∑ x : Fin (γ.rowLens.length), f x.1 := by
    rw [Fin.sum_univ_eq_sum_range]
    refine Finset.sum_subset_zero_on_sdiff ?_ ?_ ?_
    · intro x
      simp only [Finsupp.mem_support_iff, ne_eq, length_rowLens, Finset.mem_range]
      contrapose
      intro hx
      suffices γ.rowLen' x = 0 by grind
      rw [rowLen'_eq_rowLen]
      exact rowLen_eq_zero hx
    · simp
    · simp
  rw [hf, ← Finset.sum_tsub_distrib _ (by simp [h'])]
  have hrs : ∑ x : Fin (γ.sub f).rowLens.length, (γ.rowLen' x.1 - f x.1) =
      ∑ x ∈ Finset.range (γ.sub f).rowLens.length, (γ.rowLen' x - f x) := by
    rw [← Fin.sum_univ_eq_sum_range]
  have hrs' : ∑ x : Fin γ.rowLens.length, (γ.rowLen' x.1 - f x.1) =
      ∑ x ∈ Finset.range γ.rowLens.length, (γ.rowLen' x - f x) := by
    rw [← Fin.sum_univ_eq_sum_range]
  rw [hrs, hrs']
  refine Finset.sum_subset_zero_on_sdiff ?_ ?_ ?_
  · simp [colLen_mono (γ.sub_le h) 0]
  · simp only [length_rowLens, Finset.mem_sdiff, Finset.mem_range, not_lt, and_imp]
    intro x hx hxs
    rw [← Pi.sub_apply, ← Finsupp.coe_tsub, ← sub_rowLen' h, rowLen'_eq_rowLen]
    have : ¬ x < (γ.sub f).colLen 0 := by lia
    rw [← mem_iff_lt_colLen, mem_iff_lt_rowLen] at this
    push Not at this
    rwa [Nat.le_zero] at this
  · simp

end YoungDiagram

namespace SemistandardYoungTableau

lemma entry_lt_ite_max {γ : YoungDiagram} {f : ℕ →₀ ℕ} (T : SemistandardYoungTableau (γ.sub f))
    (i j : ℕ) (hij : (i, j) ∈ γ.sub f) :
     T i j < (if hTc : T.content.toList = [] then 0 else ((T.content.toList.max hTc) + 1)) := by
  split_ifs with hTc
  · apply_fun List.length at hTc
    simp only [Multiset.length_toList, content_card_eq_card, List.length_nil,
      Finset.card_eq_zero] at hTc
    rw [← mem_cells, hTc] at hij
    contradiction
  · suffices T i j ≤ T.content.toList.max hTc by exact Order.lt_add_one_iff.mpr this
    refine List.le_max_of_mem ?_
    simp [mem_content_of_mem hij]

end SemistandardYoungTableau

section SubRowLensType

def SubRowLensType (γ : YoungDiagram) := {f : ℕ →₀ ℕ //
  (∀ i, γ.rowLen' i - f i ≥ γ.rowLen' (i + 1)) ∧ (∀ i, f i ≤ γ.rowLen' i)}

lemma finite_subRowLensType (γ : YoungDiagram) : Finite (SubRowLensType γ) := by
  suffices Finite {f : ℕ →₀ ℕ | (∀ i, γ.rowLen' i - f i ≥ γ.rowLen' (i + 1)) ∧
    (∀ i, f i ≤ γ.rowLen' i)} by exact this
  have : Finite {f : ℕ →₀ ℕ | f ≤ γ.rowLen'} := instFiniteSubtypeLeOfLocallyFiniteOrderBot
  refine Finite.Set.subset {f : ℕ →₀ ℕ | f ≤ γ.rowLen'} ?_
  intro f hf
  rw [Set.mem_ofPred] at hf ⊢
  intro i
  exact hf.2 i

noncomputable
instance subRowLensFintype (γ : YoungDiagram) : Fintype (SubRowLensType γ) := by
  have := finite_subRowLensType γ
  exact Fintype.ofFinite (SubRowLensType γ)

lemma zero_subRowLensType {γ : YoungDiagram} :
    (∀ i, γ.rowLen' i - (0 : ℕ →₀ ℕ) i ≥ γ.rowLen' (i + 1)) ∧
    (∀ i, (0 : ℕ →₀ ℕ) i ≤ γ.rowLen' i) := by
  constructor
  · simp only [Finsupp.coe_zero, Pi.zero_apply, tsub_zero, ge_iff_le]
    intro i
    exact γ.rowLen'_anti (Nat.le_add_right i 1)
  · simp

end SubRowLensType

end
end


/- Source module: KostkaNumbers.HookLength.Calc -/
section
/-
Copyright (c) 2026 Noah Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Walker
-/






/-!
This files completes most of the GNW proof.  The only thing not done here is the connection to
Kostka numbers.
-/

open MeasureTheory YoungDiagram
open scoped ENNReal NNReal

variable {γ : YoungDiagram}

lemma col_sub_corner {w : ℕ × ℕ} (hw : w ∈ γ.corners) {j : ℕ} :
    (γ.sub (Finsupp.single w.1 1)).col j =
    if j = w.2 then (γ.col j).erase (w.1, j) else γ.col j := by
  have hw' := hw
  simp [corners] at hw'
  split_ifs with hwj
  · subst hwj
    ext y
    simp [col, mem_sub _ (sub_cond (subSingle_sub_cond hw)), rowLen'_eq_rowLen]
    by_cases hwy : w.1 = y.1
    · simp [hwy]
      grind
    · simp [hwy, ← mem_iff_lt_rowLen]
      grind
  · ext y
    simp only [col, Finset.mem_filter, mem_cells, mem_sub _ (sub_cond (subSingle_sub_cond hw)),
      and_congr_left_iff]
    intro hyj
    by_cases! hyw : y.1 = w.1
    · simp only [hyw, rowLen'_eq_rowLen, Finsupp.single_eq_same]
      rw [mem_iff_lt_rowLen]
      lia
    · simp [hyw, rowLen'_eq_rowLen, ← mem_iff_lt_rowLen]


lemma hookLength_sub_of_antiHook {x w : ℕ × ℕ} (hw : w ∈ γ.corners)
    (hx : x ∈ (γ.sub (Finsupp.single w.1 1)).cells)
    (h : x.1 = w.1 ∨ x.2 = w.2) :
    (γ.sub (Finsupp.single w.1 1)).hookLength x = γ.hookLength x - 1 := by
  simp only [hookLength_def, ← rowLen'_eq_rowLen, ge_iff_le, sub_cond (subSingle_sub_cond hw),
    implies_true, sub_rowLen', Finsupp.coe_tsub, Pi.sub_apply, add_tsub_cancel_right]
  have hw' := hw
  simp only [corners, Finset.mem_filter, mem_cells] at hw'
  rcases h with h | h
  · have hr2 : x.2 + 1 ≤ w.2 := by
      simp [mem_cells, mem_sub x (sub_cond (subSingle_sub_cond hw)), h, rowLen'_eq_rowLen] at hx
      lia
    have hxw : x.2 ≠ w.2 := by lia
    simp [h, colLen_eq_card, col_sub_corner hw, hxw, rowLen'_eq_rowLen]
    lia
  · have hxw : x.1 < w.1 := by
      rw [mem_cells, mem_sub x (sub_cond (subSingle_sub_cond hw)), h, rowLen'_eq_rowLen] at hx
      have hwx : w.1 ≠ x.1 := by
        contrapose! hx
        simp [hx, hw'.2.1]
      suffices x.1 < w.1 + 1 by lia
      simp [hwx, ← h] at hx
      rwa [hw'.2.2, ← h, ← mem_iff_lt_colLen, mem_iff_lt_rowLen]
    have hc : (γ.sub (Finsupp.single w.1 1)).colLen x.2 = γ.colLen x.2 - 1 := by
      have hwc : w ∈ γ.col w.2 := by simp [mem_col_iff, hw'.1]
      simp [colLen_eq_card, col_sub_corner hw, h, Finset.card_erase_of_mem hwc]
    rw [hc]
    simp [h, hxw.ne]
    lia

lemma hookLength_sub_of_not_antiHook {x w : ℕ × ℕ} (hw : w ∈ γ.corners)
    (h : ¬(x.1 = w.1 ∨ x.2 = w.2)) :
    (γ.sub (Finsupp.single w.1 1)).hookLength x = γ.hookLength x := by
  simp at h
  simp [hookLength_def, ← rowLen'_eq_rowLen, sub_rowLen' (sub_cond (subSingle_sub_cond hw)),
    colLen_eq_card, col_sub_corner hw, h.1, h.2]

lemma hookLength_sub_ite {x w : ℕ × ℕ} (hw : w ∈ γ.corners)
    (hx : x ∈ (γ.sub (Finsupp.single w.1 1)).cells) :
    ((γ.sub (Finsupp.single w.1 1)).hookLength x : ℝ≥0∞) =
    (if x.1 = w.1 ∨ x.2 = w.2 then γ.hookLength x - 1 else γ.hookLength x : ℝ≥0∞) := by
  split_ifs with h
  · exact_mod_cast hookLength_sub_of_antiHook hw hx h
  · exact_mod_cast hookLength_sub_of_not_antiHook hw h

lemma prod_sub_hookLength {x : ℕ × ℕ} (hx : x ∈ γ.corners) :
    ∏ i ∈ (γ.sub (Finsupp.single x.1 1)).cells,
    ((γ.sub (Finsupp.single x.1 1)).hookLength i : ℝ≥0∞) =
    ∏ i ∈ (γ.sub (Finsupp.single x.1 1)).cells,
    ((if i.1 = x.1 ∨ i.2 = x.2 then γ.hookLength i - 1 else γ.hookLength i) : ℝ≥0∞) :=
  Finset.prod_congr (by rfl) (by grind [hookLength_sub_ite])

lemma prod_hookLength_eq_sub {x : ℕ × ℕ} (hx : x ∈ γ.corners) :
    ∏ i ∈ γ.cells with i.1 = x.1 ∨ i.2 = x.2, (γ.hookLength i : ℝ≥0∞) =
    ∏ i ∈ (γ.sub (Finsupp.single x.1 1)).cells with i.1 = x.1 ∨ i.2 = x.2,
    (γ.hookLength i : ℝ≥0∞) := by
  have hx' : x ∈ γ := by
    simp only [corners, Finset.mem_filter, mem_cells] at hx
    exact hx.1
  have h : (γ.hookLength x : ℝ≥0∞) = 1 := by
    rw [γ.mem_corners_iff_hookLength_eq_one hx'] at hx
    exact_mod_cast hx
  rw [← Finset.prod_erase _ (f := fun w ↦ (γ.hookLength w : ℝ≥0∞)) h]
  congr
  ext z
  simp [mem_sub _ (sub_cond (subSingle_sub_cond hx)), rowLen'_eq_rowLen]
  by_cases hxz : x.1 = z.1
  · simp [hxz]
    simp [corners] at hx
    grind [mem_iff_lt_rowLen]
  · push Not at hxz
    simp [hxz.symm, ← mem_iff_lt_rowLen, Prod.ext_iff]

lemma prod_hookLength_not_eq_sub {x : ℕ × ℕ} (hx : x ∈ γ.corners) :
    ∏ i ∈ γ.cells with ¬(i.1 = x.1 ∨ i.2 = x.2), (γ.hookLength i : ℝ≥0∞) =
    ∏ i ∈ (γ.sub (Finsupp.single x.1 1)).cells with ¬(i.1 = x.1 ∨ i.2 = x.2),
    (γ.hookLength i : ℝ≥0∞) := by
  congr 1
  ext z
  simp [mem_sub _ (sub_cond (subSingle_sub_cond hx)), rowLen'_eq_rowLen]
  grind [mem_iff_lt_rowLen]


lemma ENNReal.mul_inv_sub_one {a : ℝ≥0∞} (ha : a ≥ 1) (hat : a ≠ ⊤) :
    a * (a - 1)⁻¹ = 1 + (a - 1)⁻¹ := by
  suffices (a * (a - 1)⁻¹).HolderConjugate a by exact ENNReal.HolderConjugate.conj_eq
  rw [ENNReal.holderConjugate_iff, ENNReal.mul_inv, inv_inv]
  · nth_rw 2 [← mul_one a⁻¹]
    rw [← left_distrib, tsub_add_cancel_of_le ha, ENNReal.inv_mul_cancel (by positivity) hat]
  · left
    positivity
  · left
    exact hat

lemma prod_range_hookLength {x : ℕ × ℕ} (hx : x ∈ γ.corners) :
    ∏ i ∈ Finset.range x.1,
    (1 + 1 / (γ.hookLength (i, x.2) - 1 : ℝ≥0∞)) =
    ∏ i ∈ (γ.sub (Finsupp.single x.1 1)).cells with i.2 = x.2,
    (γ.hookLength i * (γ.hookLength i - 1 : ℝ≥0∞)⁻¹)  := by
  have hx' := hx
  simp [corners] at hx'
  symm
  let e : ℕ × ℕ → ℕ := fun i ↦ i.1
  refine Finset.prod_nbij e ?_ ?_ ?_ ?_
  · simp only [Finset.mem_filter, mem_cells, mem_sub _ (sub_cond (subSingle_sub_cond hx)),
      rowLen'_eq_rowLen, Finset.mem_range, and_imp, Prod.forall, e]
    intro a
    by_cases! hax : a = x.1
    · intro b
      simp [hax]
      lia
    · simp only [ne_eq, hax, not_false_eq_true, Finsupp.single_eq_of_ne, tsub_zero]
      intro b hb
      rw [← mem_iff_lt_rowLen, mem_iff_lt_colLen] at hb
      lia
  · intro y
    simp [e]
    grind
  · intro b
    simp only [Finset.coe_range, Set.mem_Iio, Finset.coe_filter, mem_cells,
      mem_sub _ (sub_cond (subSingle_sub_cond hx)), rowLen'_eq_rowLen, Set.mem_image,
      Set.mem_ofPred_eq, Prod.exists, exists_and_right, ↓existsAndEq, and_true, exists_eq_right, e]
    intro hb
    simp [hb.ne, ← mem_iff_lt_rowLen, mem_iff_lt_colLen]
    lia
  · simp only [Finset.mem_filter, mem_cells, one_div, and_imp, Prod.forall, e]
    intro i j _ hj
    subst hj
    rw [ENNReal.mul_inv_sub_one]
    · grind [hookLength_ne_zero, Nat.one_le_cast]
    · simp

lemma prod_range_hookLength' {x : ℕ × ℕ} (hx : x ∈ γ.corners) :
    ∏ i ∈ Finset.range x.2,
    (1 + 1 / (γ.hookLength (x.1, i) - 1 : ℝ≥0∞)) =
    ∏ i ∈ (γ.sub (Finsupp.single x.1 1)).cells with i.1 = x.1,
    (γ.hookLength i * (γ.hookLength i - 1 : ℝ≥0∞)⁻¹)  := by
  have hx' := hx
  simp [corners] at hx'
  symm
  let e : ℕ × ℕ → ℕ := fun i ↦ i.2
  refine Finset.prod_nbij e ?_ ?_ ?_ ?_
  · simp only [Finset.mem_filter, mem_cells, mem_sub _ (sub_cond (subSingle_sub_cond hx)),
      rowLen'_eq_rowLen, Finset.mem_range, and_imp, Prod.forall, e]
    intro a
    by_cases! hax : a = x.1
    · intro b
      simp [hax]
      lia
    · simp only [ne_eq, hax, not_false_eq_true, Finsupp.single_eq_of_ne, tsub_zero]
      intro b hb
      rw [← mem_iff_lt_rowLen, mem_iff_lt_colLen] at hb
      lia
  · intro y
    simp [e]
    grind
  · intro b
    simp [e, mem_sub _ (sub_cond (subSingle_sub_cond hx)), rowLen'_eq_rowLen]
    lia
  · simp only [Finset.mem_filter, mem_cells, one_div, and_imp, Prod.forall, e]
    intro i j _ hj
    subst hj
    rw [ENNReal.mul_inv_sub_one]
    · grind [hookLength_ne_zero, Nat.one_le_cast]
    · simp

lemma F_div_eq_prod_mul_prod {x : ℕ × ℕ} (hx : x ∈ γ.corners) :
    F (γ.sub (Finsupp.single x.1 1)) / F γ = 1 / γ.card *
    ((∏ i ∈ Finset.range x.1, (1 + 1 / (γ.hookLength (i, x.2) - 1 : ℝ≥0∞))) *
    (∏ j ∈ Finset.range x.2, (1 + 1 / (γ.hookLength (x.1, j) - 1 : ℝ≥0∞)))) := by
  have hγ : γ.card ≠ 0 := by
    rw [ne_eq, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    push Not
    use x
    exact Finset.mem_of_mem_filter x hx
  have hxp0 : ∏ i ∈ (γ.sub (Finsupp.single x.1 1)).cells with ¬ (i.1 = x.1 ∨ i.2 = x.2),
      (γ.hookLength i : ℝ≥0∞) ≠ 0 := by
    simp [Finset.prod_eq_zero_iff, γ.hookLength_ne_zero]
  have hxpt : ∏ i ∈ (γ.sub (Finsupp.single x.1 1)).cells with ¬ (i.1 = x.1 ∨ i.2 = x.2),
      (γ.hookLength i : ℝ≥0∞) ≠ ⊤ := by
    exact ENNReal.prod_ne_top (by simp)
  have hd : Disjoint ({y ∈ (γ.sub fun₀ | x.1 => 1).cells | y.1 = x.1})
      ({y ∈ (γ.sub fun₀ | x.1 => 1).cells | y.2 = x.2}) := by
    rw [Finset.disjoint_filter]
    simp [mem_sub _ (sub_cond (subSingle_sub_cond hx)), rowLen'_eq_rowLen]
    simp [corners] at hx
    grind
  unfold F
  rw [card_sub (sub_cond (subSingle_sub_cond hx)) (subSingle_le_rowLen' hx)]
  conv_lhs => simp [ENNReal.div_eq_inv_mul]
  rw [ENNReal.div_eq_inv_mul, ENNReal.mul_inv (by simp) (by simp [Nat.factorial_ne_zero]),
    inv_inv, mul_assoc]
  nth_rw 2 [← mul_assoc]
  rw [mul_right_comm, ← Nat.mul_factorial_pred hγ, Nat.cast_mul,
    ENNReal.mul_inv (by simp) (by simp)]
  nth_rw 2 [mul_assoc]
  rw [ENNReal.inv_mul_cancel (by simp [Nat.factorial_ne_zero]) (by simp), mul_one, mul_left_comm,
    ENNReal.mul_right_inj (by simp) (by simp [hγ]),
    ← Finset.prod_filter_mul_prod_filter_not _ (fun i ↦ i.1 = x.1 ∨ i.2 = x.2),
    prod_sub_hookLength hx, Finset.prod_ite,
    ENNReal.mul_inv (by right; exact hxpt) (by right; exact hxp0), prod_hookLength_eq_sub hx,
    prod_hookLength_not_eq_sub hx, mul_left_comm, mul_assoc, ENNReal.mul_inv_cancel hxp0 hxpt,
    mul_one, ENNReal.prod_inv_distrib (Set.pairwise_of_forall _ _ (by simp)), Finset.filter_or,
    Finset.prod_union hd, Finset.prod_union hd, mul_left_comm, mul_assoc, ← mul_assoc,
    ← Finset.prod_mul_distrib]
  nth_rw 2 [mul_comm]
  rw [← Finset.prod_mul_distrib]
  nth_rw 2 [mul_comm]
  rw [prod_range_hookLength hx, prod_range_hookLength' hx]


lemma hookLength_add_of_mem_corners {γ : YoungDiagram} (x y : ℕ × ℕ) (hy : y ∈ γ.corners)
    (h : x ≤ y) :
    (γ.hookLength (x.1, y.2) - 1 : ℝ≥0∞) + (γ.hookLength (y.1, x.2) - 1) = γ.hookLength x - 1 := by
  simp only [hookLength, Nat.cast_add, ENNReal.natCast_sub, Nat.cast_one,
    ENNReal.addLECancellable_iff_ne, ne_eq, ENNReal.one_ne_top, not_false_eq_true,
    AddLECancellable.add_tsub_cancel_right]
  simp only [corners, Finset.mem_filter, mem_cells] at hy
  obtain ⟨hy, hyr, hyc⟩ := hy
  rw [← hyr, ← hyc]
  rw [Prod.le_def] at h
  push_cast
  calc γ.rowLen x.1 - (y.2 + 1 : ℝ≥0∞) + ((y.1 + 1) - (x.1 + 1)) +
    (y.2 + 1 - (x.2 + 1) + (γ.colLen x.2 - (y.1 + 1)))
    _ = γ.rowLen x.1 - (y.2 + 1 : ℝ≥0∞) + (y.2 + 1 - (x.2 + 1)) +
    ((γ.colLen x.2 - (y.1 + 1)) + ((y.1 + 1) - (x.1 + 1))) := by ring
    _ = γ.rowLen x.1 - (x.2 + 1) + ((γ.colLen x.2 - (y.1 + 1)) + ((y.1 + 1) - (x.1 + 1))) := by
      rw [tsub_add_tsub_cancel]
      · rw_mod_cast [hyr]
        exact γ.rowLen_anti _ _ h.1
      · simp [h.2]
    _ = γ.rowLen x.1 - (x.2 + 1) + (γ.colLen x.2 - (x.1 + 1)) := by
      rw [tsub_add_tsub_cancel]
      · rw_mod_cast [hyc]
        exact γ.colLen_anti _ _ h.2
      · simp [h.1]

lemma ENNReal.div_add_mul_add_div {a b : ℝ≥0∞} :
    (1 / (a + b)) * (1 / a + 1 / b) = (1 / a) * (1 / b) := by
  by_cases! hb0 : b = 0
  · simp [hb0]
  by_cases! hbt : b = ⊤
  · simp [hbt]
  by_cases! ha0 : a = 0
  · simp [ha0, hbt]
  by_cases! hat : a = ⊤
  · simp [hat]
  have ha : 1 / a = b / (a * b) := by rw [← ENNReal.mul_div_mul_right 1 a hb0 hbt, one_mul]
  have hb : 1 / b = a / (a * b) := by rw [← ENNReal.mul_div_mul_left 1 b ha0 hat, mul_one]
  conv_lhs => rw [ha, hb, ← ENNReal.add_div, add_comm, mul_div]
  rw [ENNReal.div_mul_cancel (by simp [hb0]) (by simp [hat, hbt]),
    ← ENNReal.mul_div_mul_comm (by grind) (by grind), one_mul]

lemma measure_horz_vert_eq {x : ℕ × ℕ} (hx : x ∈ γ.corners) {s t : Finset ℕ}
    (hs : s ∈ (Finset.range x.1).powerset) (ht : t ∈ (Finset.range x.2).powerset) :
    1 / γ.card *
    ((∏ i ∈ s, 1 / (γ.hookLength (i, x.2) - 1 : ℝ≥0∞)) *
    (∏ j ∈ t, 1 / (γ.hookLength (x.1, j) - 1 : ℝ≥0∞))) =
    pab hx s t := by
  by_cases! hs0 : s = ∅
  · simp [hs0, pab_empty_left_eq hx t ht]
  by_cases! ht0 : t = ∅
  · simp [ht0, pab_empty_right_eq hx s hs]
  rw [pab_recursion hx hs ht hs0 ht0]
  rw [← measure_horz_vert_eq hx (by grind) ht, ← measure_horz_vert_eq hx hs (by grind), ← mul_add]
  conv_rhs => rw [mul_left_comm]
  congr 1
  rw [← Finset.prod_erase_mul s _ (Finset.min'_mem s hs0),
    ← Finset.prod_erase_mul t _ (Finset.min'_mem t ht0), mul_right_comm, ← mul_assoc]
  nth_rw 4 [mul_right_comm]
  rw [← left_distrib, mul_left_comm, mul_assoc]
  congr 1
  have hxst : (s.min' hs0, t.min' ht0) ≤ x := by
    rw [Finset.mem_powerset] at hs ht
    have hs' := hs (Finset.min'_mem _ hs0)
    have ht' := ht (Finset.min'_mem _ ht0)
    rw [Prod.le_def]
    grind
  rw [← hookLength_add_of_mem_corners (s.min' hs0, t.min' ht0) x hx hxst, add_comm,
    ENNReal.div_add_mul_add_div]
  termination_by (s.card + t.card)
  decreasing_by
  · rw [← ne_eq, ← Finset.nonempty_iff_ne_empty] at hs0
    simp [Finset.card_erase_lt_of_mem (Finset.min'_mem _ hs0)]
  · rw [← ne_eq, ← Finset.nonempty_iff_ne_empty] at ht0
    simp [Finset.card_erase_lt_of_mem (Finset.min'_mem _ ht0)]

lemma sum_prod_eq_horz_vert {x : ℕ × ℕ} (hx : x ∈ γ.corners) :
    1 / γ.card *
    ∑ S ∈ (Finset.range x.1).powerset ×ˢ (Finset.range x.2).powerset,
    ((∏ i ∈ S.1, 1 / (γ.hookLength (i, x.2) - 1 : ℝ≥0∞)) *
    (∏ j ∈ S.2, 1 / (γ.hookLength (x.1, j) - 1 : ℝ≥0∞))) =
    ∑ S ∈ (Finset.range x.1).powerset ×ˢ (Finset.range x.2).powerset,
    (γ.pmf (ne_bot_of_mem_corners hx)).toMeasure
    {p : γ.cornerHookPath | p.1.horizontal = S.1 ∧ p.1.vertical = S.2
      ∧ p.1.path.getLast p.1.ne_nil = x} := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr (by rfl) ?_
  intro S hS
  simp only [Finset.mem_product] at hS
  exact measure_horz_vert_eq hx hS.1 hS.2

theorem F_prob {x : ℕ × ℕ} (hx : x ∈ γ.corners) :
    (γ.pmf (ne_bot_of_mem_corners hx)).toMeasure
    {p : γ.cornerHookPath | p.1.path.getLast p.1.ne_nil = x} =
    F (γ.sub (Finsupp.single x.1 1)) / F γ := by
  rw [F_div_eq_prod_mul_prod hx, Finset.prod_one_add, Finset.prod_one_add, Finset.sum_mul_sum,
    ← Finset.sum_product', sum_prod_eq_horz_vert hx, ← MeasureTheory.measure_biUnion_finset]
  · congr 1
    ext p
    simp only [Set.mem_ofPred_eq, Finset.mem_product, Finset.mem_powerset, Set.mem_iUnion,
      exists_and_left, exists_prop, Prod.exists]
    constructor
    · intro hpx
      subst hpx
      use p.1.horizontal.toFinset
      constructor
      · exact (Set.coe_toFinset _).symm
      use p.1.vertical.toFinset
      constructor
      · exact (Set.coe_toFinset _).symm
      constructor
      constructor
      · intro i
        simp only [Set.mem_toFinset, Set.mem_sdiff, Prod.exists, exists_and_right, exists_eq_right,
          Set.mem_ofPred_eq, Set.mem_singleton_iff, Finset.mem_range, and_imp, forall_exists_index]
        intro j hij
        have h := le_getLast_of_mem_path hij
        rw [Prod.le_def] at h
        lia
      · intro i
        simp only [Set.mem_toFinset, Set.mem_sdiff, Prod.exists, exists_eq_right,
          Set.mem_ofPred_eq, Set.mem_singleton_iff, Finset.mem_range, and_imp, forall_exists_index]
        intro j hij
        have h := le_getLast_of_mem_path hij
        rw [Prod.le_def] at h
        lia
      · rfl
    · intro ⟨_, _, _, _, _, hpx⟩
      exact hpx
  · unfold Set.PairwiseDisjoint Set.Pairwise
    simp only [Finset.coe_product, Finset.coe_powerset, Finset.coe_range, Set.mem_prod,
      Set.mem_preimage, Set.mem_powerset_iff, ne_eq, and_imp, Prod.forall, Prod.mk.injEq, not_and]
    intro s t hs ht s' t' hs' ht' h S hS hS' p hp
    have hp' := hS' hp
    have hp := hS hp
    grind
  · intro _ _
    exact DiscreteMeasurableSpace.forall_measurableSet _


-- upstream(ed)
lemma ENNReal.sum_div {α : Type*} {s : Finset α} (f : α → ℝ≥0∞) (a : ℝ≥0∞) :
    (∑ i ∈ s, f i) / a = ∑ i ∈ s, f i / a := by
  simp [div_eq_mul_inv, Finset.sum_mul]


lemma sum_subSingle_eq_sum_corners : ∑ a : SubSingle γ,
    (F (γ.sub (Finsupp.single a.1 1)) / F γ : ℝ≥0∞) =
    ∑ x ∈ γ.corners, (F (γ.sub (Finsupp.single x.1 1)) / F γ) := by
  let e : SubSingle γ → ℕ × ℕ := fun ⟨a, ha⟩ ↦ (a, (γ.rowLen a) - 1)
  refine Finset.sum_nbij e ?_ ?_ ?_ ?_
  · simp only [Finset.mem_univ, corners, Finset.mem_filter, mem_cells, forall_const,
    Subtype.forall, ge_iff_le, and_imp, e]
    intro a ha ha'
    specialize ha' a
    rw [Finsupp.single_eq_same, rowLen'_eq_rowLen] at ha'
    constructor
    · rw [mem_iff_lt_rowLen]
      lia
    constructor
    · lia
    · refine le_antisymm ?_ ?_
      · suffices a < γ.colLen (γ.rowLen a - 1) by lia
        rw [← mem_iff_lt_colLen, mem_iff_lt_rowLen]
        lia
      · rw [← Std.not_lt, ← mem_iff_lt_colLen, mem_iff_lt_rowLen, Std.not_lt]
        specialize ha a
        simpa [rowLen'_eq_rowLen] using ha
  · intro ⟨a, ha⟩ _ ⟨b, hb⟩ _
    grind
  · intro x hx
    simp only [Finset.coe_univ, Set.image_univ, Set.mem_range, e]
    use ⟨x.1, ⟨subSingle_sub_cond hx, subSingle_le_rowLen' hx⟩⟩
    simp [corners] at hx
    simp [← hx.2.1]
  · simp [e]

lemma sum_corners_div_eq_sum_corners_measure (hγ : γ ≠ ⊥) : ∑ x ∈ γ.corners,
    (F (γ.sub (Finsupp.single x.1 1)) / F γ) =
    ∑ x ∈ γ.corners, (γ.pmf hγ).toMeasure
    {p : γ.cornerHookPath | p.1.path.getLast p.1.ne_nil = x} := by
  refine Finset.sum_congr (by rfl) ?_
  intro x hx
  rw [F_prob hx]

lemma union_corners_eq_univ : ⋃ x ∈ γ.corners,
    {p : γ.cornerHookPath | p.1.path.getLast p.1.ne_nil = x} = Set.univ := by
  ext x
  simp [x.2]

theorem F_recursion {γ : YoungDiagram} (hγ : γ.card ≠ 0) :
    (F γ : ℝ≥0∞) = ∑ a : SubSingle γ, F (γ.sub (Finsupp.single a.1 1)) := by
  have hγ' : γ ≠ ⊥ := by rwa [ne_eq, eq_bot_iff_card_eq_zero]
  symm
  rw [← ENNReal.div_eq_one_iff F_ne_zero, ENNReal.sum_div, sum_subSingle_eq_sum_corners,
    sum_corners_div_eq_sum_corners_measure hγ', ← measure_biUnion_finset, union_corners_eq_univ,
    measure_univ]
  · intro x hx y hy hxy s hsx hsy z hz
    have hzx := hsx hz
    have hzy := hsy hz
    simp at hzx hzy
    lia
  · intro _ _
    exact DiscreteMeasurableSpace.forall_measurableSet _
  · simp [F, ENNReal.div_eq_top, Nat.factorial_ne_zero, Finset.prod_eq_zero_iff, hookLength_ne_zero]

end


/- Source module: KostkaNumbers.Diagrams.RestrictExtend -/
section
/-
Copyright (c) 2026 Noah Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Walker
-/





/-!
Define operations on SSYT to restrict them to smaller shape or extend them by a new value to a
larger shape. These are inverse operations as proved in `extend_restrict` and `restrict_extend`.
These operations are useful for expressing the recursion in the Recursion file.
-/

section

open YoungDiagram SemistandardYoungTableau

variable {γ γ' : YoungDiagram}

namespace YoungDiagram

-- To extend a SSYT with a single value, each column must have at most one new box added
abbrev valid_extend (γ γ' : YoungDiagram) := ∀ i1 i2 j : ℕ, i1 < i2 → (i2, j) ∈ γ' → (i1, j) ∈ γ

lemma sub_valid {f : ℕ →₀ ℕ} (h : ∀ i, γ.rowLen' i - f i ≥ γ.rowLen' (i + 1)) :
    valid_extend (γ.sub f) γ := by
  intro i1 i2 j hi hij2
  rw [mem_iff_lt_rowLen] at hij2
  simp only [mem_sub _ (sub_cond h)]
  refine lt_of_lt_of_le ?_ (h i1)
  rw [rowLen'_eq_rowLen]
  refine lt_of_lt_of_le hij2 ?_
  exact γ.rowLen_anti (i1 + 1) i2 hi

end YoungDiagram

namespace SemistandardYoungTableau

/-- Restrict a SSYT to a smaller shape. -/
def restrict (T : SemistandardYoungTableau γ) (h : γ' ≤ γ) :
  SemistandardYoungTableau γ' := ⟨
    fun i j ↦ if (i, j) ∈ γ' then T i j else 0,
    by
      intro i j1 j2 hj hij2
      have hij1 : (i, j1) ∈ γ' := γ'.up_left_mem (by rfl) (le_of_lt hj) hij2
      simp only [hij2, ↓reduceIte, hij1, T.row_weak hj (h hij2)]
    ,
      by
      intro i1 i2 j hi hij2
      have hij1 : (i1, j) ∈ γ' := γ'.up_left_mem (le_of_lt hi) (by rfl) hij2
      simp only [hij1, ↓reduceIte, hij2]
      exact T.col_strict hi (h hij2)
    ,
      by grind
  ⟩

/-- Extend a SSYT to a larger shape, filling each new box with the same value. -/
def extend (T : SemistandardYoungTableau γ')
  (hγ : valid_extend γ' γ) (a : ℕ) (ha : ∀ i j : ℕ, (i, j) ∈ γ' → T i j < a) :
  SemistandardYoungTableau γ := ⟨
    fun i j ↦ if (i, j) ∈ γ then if (i, j) ∈ γ' then T i j else a else 0, by
      intro i j1 j2 hj hij2
      have hij1 : (i, j1) ∈ γ := γ.up_left_mem (by rfl) (le_of_lt hj) hij2
      by_cases hij2' : (i, j2) ∈ γ'
      · have hij1' : (i, j1) ∈ γ' := γ'.up_left_mem (by rfl) (le_of_lt hj) hij2'
        simp [hij1, hij2, hij1', hij2', T.row_weak hj hij2']
      · grind
    ,
      by
      intro i1 i2 j hi hij2
      have hij1 : (i1, j) ∈ γ := γ.up_left_mem (le_of_lt hi) (by rfl) hij2
      by_cases hij2' : (i2, j) ∈ γ'
      · have hij1' : (i1, j) ∈ γ' := γ'.up_left_mem (le_of_lt hi) (by rfl) hij2'
        simp [hij1', hij2', hij1, hij2, T.col_strict hi hij2']
      · have hij1' : (i1, j) ∈ γ' := hγ i1 i2 j hi hij2
        simp [hij1, hij2, hij1', hij2', ha i1 j hij1']
    ,
      by grind
  ⟩

@[simp]
lemma restrict_entry {γ γ' : YoungDiagram} (T : SemistandardYoungTableau γ) (h : γ' ≤ γ) (i j : ℕ)
    (hij : (i, j) ∈ γ') : (T.restrict h) i j = T i j := by
  simp only [restrict, DFunLike.coe, hij, reduceIte]

theorem extend_restrict {γ γ' : YoungDiagram} (T : SemistandardYoungTableau γ') (h : γ' ≤ γ)
    (hγ : valid_extend γ' γ) (a : ℕ) (ha : ∀ i j : ℕ, (i, j) ∈ γ' → T i j < a) :
    (T.extend hγ a ha).restrict h = T := by
  ext i j
  simp only [extend, restrict, DFunLike.coe]
  by_cases hij' : (i, j) ∈ γ'
  · have hij : (i, j) ∈ γ := h hij'
    simp [hij', hij]
  · simp only [hij', ↓reduceIte]
    exact (T.zeros hij').symm

theorem restrict_extend {γ γ' : YoungDiagram} (T : SemistandardYoungTableau γ)
    {a : ℕ} (h : γ' ≤ γ) (hγ : valid_extend γ' γ)
    (hγ' : ∀ i j : ℕ, (i, j) ∈ γ → (i, j) ∉ γ' → T i j = a)
    (ha : ∀ i j : ℕ, (i, j) ∈ γ' → (T.restrict h) i j < a) :
    (T.restrict h).extend hγ a ha = T := by
  ext i j
  simp only [restrict, extend, DFunLike.coe]
  by_cases hij' : (i, j) ∈ γ'
  · have hij : (i, j) ∈ γ := h hij'
    simp [hij, hij']
  · by_cases hij : (i, j) ∈ γ
    · simp only [hij, ↓reduceIte, hij']
      exact (hγ' i j hij hij').symm
    · simp only [hij, ↓reduceIte]
      exact (T.zeros hij).symm

lemma extend_content {γ γ' : YoungDiagram} (T : SemistandardYoungTableau γ') (h : γ' ≤ γ)
    (hγ : valid_extend γ' γ) (a : ℕ) (ha : ∀ i j : ℕ, (i, j) ∈ γ' → T i j < a) :
    (T.extend hγ a ha).content = T.content + Multiset.replicate (γ.card - γ'.card) a := by
  simp only [content, extend, DFunLike.coe, Prod.mk.eta]
  ext b
  by_cases hb : b = a
  · simp only [hb, Multiset.count_map, Multiset.count_add, Multiset.count_replicate_self]
    rw [← card_sdiff h, Finset.card_def, ← Multiset.card_add]
    congr
    ext x
    simp [Multiset.count_filter, Multiset.count_eq_of_nodup γ'.cells.nodup,
      Multiset.count_eq_of_nodup γ.cells.nodup]
    grind
  · push Not at hb
    simp only [Multiset.count_map, Multiset.count_add, Multiset.count_replicate, hb.symm,
      ↓reduceIte, add_zero]
    congr 1
    ext x
    simp [Multiset.count_filter, Multiset.count_eq_of_nodup γ'.cells.nodup,
      Multiset.count_eq_of_nodup γ.cells.nodup]
    by_cases hx' : x ∈ γ'
    · simp [h hx', hx']
    · grind

lemma mem_content_sdiff_of_mem_sdiff {γ γ' : YoungDiagram} (T : SemistandardYoungTableau γ)
    (hγ : γ' ≤ γ) {i j : ℕ} (h : (i, j) ∈ γ.cells \ γ'.cells) :
    T i j ∈ T.content - (T.restrict hγ).content := by
  simp at h
  have hmap : Multiset.map (fun x ↦ (T.restrict hγ) x.1 x.2) γ'.cells.val =
      Multiset.map (fun x ↦ T x.1 x.2) γ'.cells.val := by
    refine Multiset.map_congr rfl ?_
    intro x hx
    simp only [Finset.mem_val, mem_cells] at hx
    simp [restrict, hx, ← to_fun_eq_coe]
  simp only [content, hmap, Multiset.mem_sub, Multiset.count_map, gt_iff_lt]
  refine Multiset.card_lt_card ?_
  rw [Multiset.lt_iff_cons_le]
  use (i, j)
  rw [Multiset.le_iff_subset]
  · intro x
    simp only [Multiset.mem_cons, Multiset.mem_filter, Finset.mem_val, mem_cells]
    intro hx
    rcases hx with hx | hx
    · simp [hx, h.1]
    · constructor
      · exact hγ hx.1
      · exact hx.2
  · refine Multiset.nodup_cons.mpr ?_
    constructor
    · simp [h.2]
    · exact Multiset.Nodup.filter _ γ'.cells.nodup

end SemistandardYoungTableau

end
end


/- Source module: KostkaNumbers.Kostka.Recursion -/
section
/-
Copyright (c) 2026 Noah Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Walker
-/






/-!
Prove a recursion for the Kostka numbers.  This is the standard recursion which involves removing
all cells in the tableau that contain the max value.  We have two versions, `kostka_recursion` and
`kostka_recursion'`.
-/

open YoungDiagram Kostka SemistandardYoungTableau

lemma exists_max_cell_start {γ : YoungDiagram} (T : SemistandardYoungTableau γ) (i : ℕ)
    (hT : T.content.toList ≠ []) :
    ∃ j : ℕ, ∀ j' ≥ j, (i, j') ∈ γ → T i j' = T.content.toList.max hT := by
  use γ.rowLen i
  grind [mem_iff_lt_rowLen]

open Classical in
lemma find_max_cell_start_le {γ : YoungDiagram} (T : SemistandardYoungTableau γ)
    {i j : ℕ} (hT : T.content.toList ≠ []) (h : T i j = T.content.toList.max hT) :
    Nat.find (exists_max_cell_start T i hT) ≤ j := by
  refine Nat.find_min' (exists_max_cell_start T i hT) ?_
  intro j' hj hij'
  refine antisymm (entry_le_max hT) ?_
  rw [← h]
  exact T.row_weak_of_le hj hij'

open Classical in
lemma find_max_cell_start_eq_zero {γ : YoungDiagram}
    (T : SemistandardYoungTableau γ) (hTc : T.content.toList ≠ []) {i : ℕ}
    (h : ∀ x ∈ T.content, x = 0) :
    Nat.find (exists_max_cell_start T i hTc) = 0 := by
  rw [← Nat.le_zero]
  refine find_max_cell_start_le T hTc ?_
  have hT : T.content.toList.max hTc = 0 := by
    simp_rw [← Nat.bot_eq_zero, List.max_eq_bot_iff, Multiset.mem_toList] at h ⊢
    exact h
  rw [hT]
  by_cases hi : (i, 0) ∈ γ
  · exact h (T i 0) (mem_content_of_mem hi)
  · exact T.zeros hi

open Classical in
lemma entry_find_eq_max {γ : YoungDiagram} {T : SemistandardYoungTableau γ}
    (i : ℕ) (hT : T.content.toList ≠ []) (h : (i, Nat.find (exists_max_cell_start T i hT)) ∈ γ) :
    T i (Nat.find (exists_max_cell_start T i hT)) = T.content.toList.max hT := by
  let hm := Nat.find_spec (exists_max_cell_start T i hT)
  exact hm (Nat.find (exists_max_cell_start T i hT)) (by rfl) h

open Classical in
noncomputable
def max_cell_len {γ : YoungDiagram} (T : SemistandardYoungTableau γ)
  (hTc : T.content.toList ≠ []) : ℕ →₀ ℕ :=
  ⟨ if T.content.toList.max hTc ≠ 0 then
    {i ∈ Finset.range <| γ.colLen 0 | ∃ j, T i j = T.content.toList.max hTc}
    else Finset.range <| γ.colLen 0,
  fun i ↦ γ.rowLen' i - Nat.find (exists_max_cell_start T i hTc),
    by
    split_ifs with hTc0
    · intro i
      constructor
      · intro hi
        simp only [Finset.mem_filter, Finset.mem_range, ← mem_iff_lt_colLen] at hi
        obtain ⟨hi, ⟨j, hj⟩⟩ := hi
        refine ne_of_gt ?_
        simp only [tsub_pos_iff_lt, rowLen'_eq_rowLen]
        rw [← hj] at hTc0
        refine lt_of_le_of_lt (find_max_cell_start_le T hTc hj) ?_
        rw [← mem_iff_lt_rowLen]
        contrapose! hTc0
        exact T.zeros hTc0
      · simp only [Finset.mem_filter, Finset.mem_range]
        intro hi
        constructor
        · rw [← mem_iff_lt_colLen, mem_iff_lt_rowLen, Nat.pos_iff_ne_zero]
          rw [rowLen'_eq_rowLen] at hi
          contrapose! hi
          rw [hi, zero_tsub]
        · contrapose! hi
          suffices ¬ Nat.find (exists_max_cell_start T i hTc) < γ.rowLen i by
            push Not at this
            rw [rowLen'_eq_rowLen]
            exact Nat.sub_eq_zero_of_le this
          rw [← mem_iff_lt_rowLen]
          contrapose! hi
          use (Nat.find (exists_max_cell_start T i hTc))
          exact entry_find_eq_max i hTc hi
    · push Not at hTc0
      simp_rw [← Nat.bot_eq_zero, List.max_eq_bot_iff, Multiset.mem_toList, Nat.bot_eq_zero] at hTc0
      simp [← mem_iff_lt_colLen, rowLen'_eq_rowLen, ← Nat.pos_iff_ne_zero,
        find_max_cell_start_eq_zero T hTc hTc0, ← mem_iff_lt_rowLen]
    ⟩

lemma max_cell_len_sub {γ : YoungDiagram} (T : SemistandardYoungTableau γ)
    (hTc : T.content.toList ≠ []) (i : ℕ) : γ.rowLen' i - (max_cell_len T hTc i) ≥
    γ.rowLen' (i + 1) := by
  simp only [max_cell_len, ne_eq, ite_not, ge_iff_le, Finsupp.coe_mk]
  rw [Nat.sub_sub_eq_min, Nat.le_min]
  constructor
  · exact γ.rowLen'_anti (Nat.le_add_right i 1)
  · refine Nat.le_of_not_gt ?_
    rw [rowLen'_eq_rowLen, gt_iff_lt, ← mem_iff_lt_rowLen]
    by_contra! h
    let hc := T.col_strict (Nat.lt_add_one i) h
    rw [entry_find_eq_max i hTc (γ.up_left_mem (le_of_lt (Nat.lt_add_one i)) (by rfl) h)] at hc
    contrapose! hc
    exact entry_le_max hTc

lemma max_cell_len_le_rowLen' {γ : YoungDiagram} (T : SemistandardYoungTableau γ)
    (hTc : T.content.toList ≠ []) (i : ℕ) : (max_cell_len T hTc i) ≤ γ.rowLen' i := by
  simp [max_cell_len]

open Classical in
lemma find_max_cell_start_le_rowLen' {γ : YoungDiagram} (T : SemistandardYoungTableau γ)
    (i : ℕ) (hTc : T.content.toList ≠ []) : Nat.find (exists_max_cell_start T i hTc) ≤
    γ.rowLen' i := by
  refine Nat.find_min' _ ?_
  intro j hij hij'
  rw [mem_iff_lt_rowLen, ← rowLen'_eq_rowLen] at hij'
  lia

lemma entry_eq_max {γ : YoungDiagram} (T : SemistandardYoungTableau γ)
    (hTc : T.content.toList ≠ []) (i j : ℕ) (hij : (i, j) ∈ γ)
    (hij' : (i, j) ∉ γ.sub (max_cell_len T hTc)) :
    T i j = T.content.toList.max hTc := by
  rw [mem_sub _ (sub_cond (max_cell_len_sub T hTc))] at hij'
  simp only [max_cell_len, ne_eq, ite_not, ge_iff_le, Finsupp.coe_mk, not_lt,
    tsub_le_iff_right] at hij'
  classical
  suffices j ≥ Nat.find (exists_max_cell_start T i hTc) by
    exact Nat.find_spec (exists_max_cell_start T i hTc) j this hij
  let hc := find_max_cell_start_le_rowLen' T i
  grind

lemma entry_eq_max_iff {γ : YoungDiagram} (T : SemistandardYoungTableau γ)
    (hTc : T.content.toList ≠ []) (he : ∃ x ∈ T.content, x ≠ ⊥)
    (i j : ℕ) : T i j = T.content.toList.max hTc ↔
    (i, j) ∈ γ.cells \ (γ.sub (max_cell_len T hTc)).cells := by
  constructor
  · intro hij
    rw [Finset.mem_sdiff, mem_cells, mem_cells, mem_sub _ (sub_cond (max_cell_len_sub T hTc))]
    simp only [max_cell_len, ne_eq, ite_not, ge_iff_le, Finsupp.coe_mk, not_lt, tsub_le_iff_right]
    constructor
    · contrapose! hij
      symm
      simp_rw [T.zeros hij, ← bot_eq_zero, ne_eq, List.max_eq_bot_iff, Multiset.mem_toList]
      push Not
      exact he
    · apply find_max_cell_start_le T at hij
      let hc := find_max_cell_start_le_rowLen' T i
      lia
  · intro hij
    simp only [Finset.mem_sdiff, mem_cells] at hij
    exact entry_eq_max T hTc i j hij.1 hij.2

lemma exists_nonzero_of_mem_sub {γ : YoungDiagram} (T : SemistandardYoungTableau γ)
    (hTc : T.content.toList ≠ []) (i j : ℕ) (hij' : (i, j) ∈ γ.sub (max_cell_len T hTc)) :
    ∃ x ∈ T.content, x ≠ 0 := by
  contrapose! hij'
  simp [max_cell_len, find_max_cell_start_eq_zero T hTc hij']

lemma entry_lt_max {γ : YoungDiagram} (T : SemistandardYoungTableau γ)
    (hTc : T.content.toList ≠ []) (i j : ℕ) (hij' : (i, j) ∈ γ.sub (max_cell_len T hTc)) :
    T i j < T.content.toList.max hTc := by
  have hemp := exists_nonzero_of_mem_sub T hTc i j hij'
  contrapose! hij'
  have he : T i j = T.content.toList.max hTc := antisymm' hij' <| entry_le_max hTc
  rw [entry_eq_max_iff T hTc hemp, Finset.mem_sdiff, mem_cells] at he
  exact he.2

lemma entry_restrict_lt_max {γ : YoungDiagram} (T : SemistandardYoungTableau γ)
    (hTc : T.content.toList ≠ []) (i j : ℕ) (hij' : (i, j) ∈ γ.sub (max_cell_len T hTc)) :
    (T.restrict (γ.sub_le (sub_cond (max_cell_len_sub T hTc))))
    i j < T.content.toList.max hTc := by
  rw [restrict_entry _ _ _ _ hij']
  exact entry_lt_max T hTc i j hij'


lemma max_notMem_restrict_max_cells {γ : YoungDiagram} (T : SemistandardYoungTableau γ)
    (hTc : T.content.toList ≠ []) : (T.content.toList.max hTc) ∉
    (T.restrict (γ.sub_le (sub_cond (max_cell_len_sub T hTc)))).content := by
  simp only [content, Multiset.mem_map, Finset.mem_val, mem_cells,
    Prod.exists, not_exists, not_and]
  intro i j hij
  exact ne_of_lt <| entry_restrict_lt_max T hTc i j hij

lemma restrict_max_cells_content {γ : YoungDiagram} (T : SemistandardYoungTableau γ)
    (hTc : T.content.toList ≠ []) :
    (T.restrict (γ.sub_le (sub_cond (max_cell_len_sub T hTc)))).content =
    T.content.remove (T.content.toList.max hTc) := by
  nth_rw 7 [← restrict_extend T (γ.sub_le (sub_cond (max_cell_len_sub T hTc)))
      (γ.sub_valid (max_cell_len_sub T hTc)) (entry_eq_max T hTc)]
  · rw [extend_content]
    · rw [Multiset.remove_add, Multiset.remove_replicate, Multiset.empty_eq_zero, add_zero,
        Multiset.remove_of_notMem]
      · exact max_notMem_restrict_max_cells T hTc
      · rfl
    · exact sub_le (sub_cond (max_cell_len_sub T hTc))
  · exact entry_restrict_lt_max T hTc

lemma max_fromCounts_add_one_eq_card {μ : Multiset ℕ} (hμ : μ.fromCounts.toList ≠ []) (h0 : 0 ∉ μ) :
    μ.fromCounts.toList.max hμ + 1 = μ.card := by
  have hle : μ.fromCounts.toList.max hμ + 1 ≤ μ.card := by
    suffices μ.fromCounts.toList.max hμ < μ.card by exact this
    rw [← Multiset.mem_fromCounts_iff h0, ← Multiset.mem_toList]
    exact List.max_mem hμ
  refine antisymm hle ?_
  suffices μ.card - 1 ≤ μ.fromCounts.toList.max hμ by lia
  refine List.le_max_of_mem ?_
  rw [Multiset.mem_toList]
  refine Multiset.mem_fromCounts h0 (μ.card - 1) ?_
  simp only [tsub_lt_self_iff, zero_lt_one, and_true]
  rwa [Nat.pos_iff_ne_zero, ne_eq, Multiset.card_eq_zero, ← Multiset.fromCounts_eq_zero_iff _ h0,
      ← Multiset.toList_eq_nil]

lemma max_fromCounts_eq_card_sub_one {μ : Multiset ℕ} (hμ : μ.fromCounts.toList ≠ []) (h0 : 0 ∉ μ) :
    μ.fromCounts.toList.max hμ = μ.card - 1 := by
  rw [← max_fromCounts_add_one_eq_card hμ h0, add_tsub_cancel_right]

open Classical in
def unionEquiv (γ : YoungDiagram) (μ : Multiset ℕ) (hμ : μ.toList ≠ []) (h0 : 0 ∉ μ) :
    SemistandardYoungTableauWithContent γ μ ≃
    Finset.biUnion (Finset.univ : Finset (SubRowLensType γ)) (fun ⟨_, hf⟩ ↦
    {T : SemistandardYoungTableauWithContent γ μ |
    (T.1.restrict (γ.sub_le (sub_cond hf.1))).content =
    (μ.erase (μ.toList.min hμ)).fromCounts}) where
  toFun T := ⟨T, by
    have hTc : T.1.content.toList ≠ [] := by
      rwa [T.2, ne_eq, Multiset.fromCounts_eq_nil_iff h0]
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
    use ⟨max_cell_len T.1 hTc, by
      constructor
      · exact max_cell_len_sub T.1 hTc
      · exact max_cell_len_le_rowLen' T.1 hTc
      ⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [restrict_max_cells_content T.1 hTc]
    nth_rw 1 [T.2, Multiset.erase_fromCounts_of_min μ hμ]
    rw [← max_fromCounts_eq_card_sub_one ?_ h0]
    · congr
      exact T.2
    · rwa [T.2] at hTc
    ⟩
  invFun T := ⟨T.1, by simp⟩
  left_inv := by simp [Function.LeftInverse]
  right_inv := by simp [Function.RightInverse, Function.LeftInverse]








lemma entry_eq_ite_max {γ : YoungDiagram} {μ : Multiset ℕ} (hμ : μ.toList ≠ []) (h0 : 0 ∉ μ)
    {f : ℕ →₀ ℕ} (hf : ∀ i, γ.rowLen' i - f i ≥ γ.rowLen' (i + 1))
    (T : SemistandardYoungTableau γ) (hT : T.content = μ.fromCounts)
    (hT' : (T.restrict <| γ.sub_le (sub_cond hf)).content =
    (μ.erase (μ.toList.min hμ)).fromCounts) (i j : ℕ) (hij : (i, j) ∈ γ)
    (hij' : (i, j) ∉ γ.sub f) :
    T i j = (if hTc : (T.restrict (γ.sub_le (sub_cond hf))).content.toList = []
    then 0 else (T.restrict (γ.sub_le (sub_cond hf))).content.toList.max hTc + 1) := by
  split_ifs with hc0
  · have hμ0 : μ ≠ 0 := by rwa [ne_eq, ← Multiset.toList_eq_nil]
    rw [hT', Multiset.fromCounts_eq_nil_iff, Multiset.toList_eq_nil,
      Multiset.erase_eq_zero_iff] at hc0
    · simp only [hμ0, false_or] at hc0
      rw [hc0, Multiset.fromCounts_singleton] at hT
      · have hTc : T i j ∈ T.content := T.mem_content_of_mem hij
        rw [hT, Multiset.mem_replicate] at hTc
        exact hTc.2
      · contrapose! h0
        rw [← h0, ← Multiset.mem_toList]
        exact List.min_mem hμ
    · contrapose! h0
      exact Multiset.mem_of_mem_erase h0
  · simp only [hT']
    have h0' : 0 ∉ μ.erase (μ.toList.min hμ) := by
      contrapose! h0
      exact Multiset.mem_of_mem_erase h0
    rw [max_fromCounts_add_one_eq_card ?_ h0',
      Multiset.card_erase_of_mem, Nat.pred_eq_sub_one]
    · have hijs : (i, j) ∈ γ.cells \ (γ.sub f).cells := by
        simp [hij, hij']
      let hijc := mem_content_sdiff_of_mem_sdiff T (γ.sub_le (sub_cond hf)) hijs
      rw [hT, hT', Multiset.erase_fromCounts_of_min μ hμ, Multiset.sub_remove,
        Multiset.mem_replicate] at hijc
      exact hijc.2
    · rw [← Multiset.mem_toList]
      exact List.min_mem hμ
    · rw [ne_eq, ← hT']
      exact hc0



noncomputable
def recEquiv (γ : YoungDiagram) (μ : Multiset ℕ) (hμ : μ.toList ≠ []) (h0 : 0 ∉ μ)
    (h : γ.card = μ.sum) (f : ℕ →₀ ℕ) (hf : ∀ i, γ.rowLen' i - f i ≥ γ.rowLen' (i + 1)) :
    {T : SemistandardYoungTableauWithContent γ μ |
    (T.1.restrict (γ.sub_le (sub_cond hf))).content =
    (μ.erase (μ.toList.min hμ)).fromCounts} ≃
    SemistandardYoungTableauWithContent (γ.sub f) (μ.erase (μ.toList.min hμ)) where
  toFun := fun ⟨T, hT⟩ ↦ ⟨T.1.restrict (γ.sub_le (sub_cond hf)), by
    simp at hT
    simp [SemistandardYoungTableauWithContent, hT]⟩
  invFun := fun ⟨T, hT⟩ ↦ ⟨⟨T.extend (γ.sub_valid hf)
    (if hTc : T.content.toList = [] then 0 else ((T.content.toList.max hTc) + 1))
    (entry_lt_ite_max T), by
    rw [SemistandardYoungTableauWithContent, Set.mem_ofPred] at hT ⊢
    rw [extend_content T (γ.sub_le (sub_cond hf)), hT]
    apply_fun Multiset.card at hT
    simp only [content_card_eq_card, Multiset.fromCounts_card] at hT
    rw [hT, h, ← Multiset.sum_erase, Nat.add_sub_cancel]
    · suffices (if hμ' : (μ.erase (μ.toList.min hμ)).fromCounts.toList = [] then 0 else
          (μ.erase (μ.toList.min hμ)).fromCounts.toList.max hμ' + 1) =
          (μ.erase (μ.toList.min hμ)).card by
        rw [this, ← Multiset.cons_fromCounts_of_min]
        · congr
          refine Multiset.cons_erase ?_
          rw [← Multiset.mem_toList]
          exact List.min_mem hμ
        · intro m hm
          refine List.min_le_of_mem ?_
          rw [Multiset.mem_toList]
          exact Multiset.mem_of_mem_erase hm
      have h0' : 0 ∉ (μ.erase (μ.toList.min hμ)) := by
        contrapose! h0
        exact Multiset.mem_of_mem_erase h0
      by_cases! hTc : (μ.erase (μ.toList.min hμ)).fromCounts.toList = []
      · simp only [hTc, ↓reduceDIte]
        rw [Multiset.fromCounts_eq_nil_iff h0', Multiset.toList_eq_nil] at hTc
        rw [hTc, Multiset.card_zero]
      · simp only [hTc, ↓reduceDIte]
        exact max_fromCounts_add_one_eq_card hTc h0'
    · rw [← Multiset.mem_toList]
      exact List.min_mem hμ
    ⟩, by
    rw [SemistandardYoungTableauWithContent, Set.mem_ofPred] at hT
    rw [Set.mem_ofPred, T.extend_restrict, hT]
    ⟩
  left_inv := by
    simp only [Function.LeftInverse, Set.coe_ofPred, Set.mem_ofPred_eq, Subtype.forall]
    intro T hT hT'
    congr
    exact T.restrict_extend (γ.sub_le (sub_cond hf)) _ (entry_eq_ite_max hμ h0 hf T hT hT') _
  right_inv := by
    simp only [Function.RightInverse, Function.LeftInverse, Subtype.forall, Subtype.mk.injEq]
    intro T _
    exact T.extend_restrict (γ.sub_le (sub_cond hf)) (γ.sub_valid hf)
      _ (entry_lt_ite_max T)



theorem kostka_recursion {γ : YoungDiagram} {μ : Multiset ℕ} (hμ : μ.toList ≠ []) (h0 : 0 ∉ μ)
    (h : γ.card = μ.sum) : kostkaNumber γ μ =
    ∑ f : SubRowLensType γ, kostkaNumber (γ.sub f.1) (μ.erase (μ.toList.min hμ)) := by
  classical
  rw [kostka_eq_card_SSYTWithContent, Nat.card_congr (unionEquiv γ μ hμ h0),
    Nat.card_eq_finsetCard, Finset.card_biUnion]
  · congr
    ext f
    rw [kostka_eq_card_SSYTWithContent, ← Nat.card_congr (recEquiv γ μ hμ h0 h f.1 f.2.1)]
    refine (Nat.subtype_card _ ?_).symm
    split
    simp
  · intro ⟨f, hf⟩ _ ⟨g, hg⟩ _ hfg s hfs hgs ⟨T, hT⟩ hTs
    contrapose! hfg
    suffices f = g by exact Subtype.ext this
    specialize hfs hTs
    specialize hgs hTs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hfs hgs
    rw [SemistandardYoungTableauWithContent, Set.mem_ofPred] at hT
    by_contra! hfg
    apply exists_mem_sdiff_of_ne hf.1 hg.1 hf.2 hg.2 at hfg
    obtain ⟨x, hxγ, hx⟩ := hfg
    wlog hx' : (x ∈ (γ.sub f).cells \ (γ.sub g).cells) generalizing f g
    · exact this g hg (by assumption) f hf (by assumption) hgs hfs (by rwa [Or.comm]) (by
        simpa [hx'] using hx)
    simp only [Finset.mem_sdiff, mem_cells] at hx'
    let Tf := T.restrict (γ.sub_le (sub_cond hf.1))
    let Tg := T.restrict (γ.sub_le (sub_cond hg.1))
    have hxm : Tf x.1 x.2 ∈ Tf.content := mem_content_of_mem hx'.1
    rw [hfs, Multiset.erase_fromCounts_of_min μ hμ, restrict_entry _ _ _ _ hx'.1,
      Multiset.mem_remove_of_mem] at hxm
    · have hxc : T x.1 x.2 ∈ T.content - Tg.content :=
        mem_content_sdiff_of_mem_sdiff T (γ.sub_le (sub_cond hg.1)) (by simp [hxγ, hx'.2])
      rw [hT, hgs, Multiset.erase_fromCounts_of_min μ hμ, Multiset.sub_remove,
        Multiset.mem_replicate] at hxc
      rw [← hxc.2] at hxm
      contradiction
    · rw [← hT]
      exact mem_content_of_mem hxγ




-- This is used in the proof of the hook length formula
lemma sum_support_subRowLensType_le_card {γ : YoungDiagram} (f : SubRowLensType γ) :
    ∑ x ∈ f.1.support, f.1 x ≤ γ.card := by
  rw [card_eq_sum_rowLen, Fin.sum_univ_eq_sum_range]
  simp only [← rowLen'_eq_rowLen]
  have hfs : f.1.support ⊆ Finset.range (γ.rowLens.length + 1) := by
    intro x
    simp only [Finsupp.mem_support_iff, ne_eq, length_rowLens, Finset.mem_range,
      Order.lt_add_one_iff]
    contrapose!
    intro hx
    suffices γ.rowLen x = 0 by
      rw [← Nat.le_zero, ← this, ← rowLen'_eq_rowLen]
      exact f.2.2 x
    exact γ.rowLen_eq_zero (by lia)
  refine le_trans (Finset.sum_le_sum_of_subset hfs) <| Finset.sum_le_sum ?_
  intro i hi
  exact f.2.2 i

-- This is used in the final SumInequality file
lemma sum_subRowLensSumType {γ : YoungDiagram} {μ : Multiset ℕ} (hμ : μ.toList ≠ [])
    (h0 : 0 ∉ μ) (k : ℕ) (h : γ.card - k = μ.sum) :
    ∑ f : SubRowLensType γ, kostkaNumber (γ.sub f.1) μ =
    ∑ f : SubRowLensType γ with (∑ x ∈ f.1.support, f.1 x = k), kostkaNumber (γ.sub f.1) μ := by
  classical
  refine (Finset.sum_subset_zero_on_sdiff ?_ ?_ ?_).symm
  · intro f _
    exact Finset.mem_univ f
  · intro f hf
    simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_filter, true_and] at hf
    refine kostka_ne_card _ _ ?_
    rw [card_sub (sub_cond f.2.1) f.2.2]
    have hcf := sum_support_subRowLensType_le_card f
    have hμ0 : μ.sum ≠ 0 := by
      rwa [ne_eq, Multiset.sum_eq_zero_iff_eq_zero h0, ← Multiset.toList_eq_nil]
    lia
  · intro _ _
    rfl

lemma sum_subRowLensType_with_sum_eq {γ : YoungDiagram} {μ : Multiset ℕ} {hμ : μ.toList ≠ []}
    (h : γ.card = μ.sum) :
    ∑ f : SubRowLensType γ, kostkaNumber (γ.sub f.1)
    (μ.erase (μ.toList.min hμ)) = ∑ f : SubRowLensType γ with (∑ x ∈ f.1.support,
    f.1 x = μ.toList.min hμ), kostkaNumber (γ.sub f.1)
    (μ.erase (μ.toList.min hμ)) := by
  classical
  refine (Finset.sum_subset_zero_on_sdiff ?_ ?_ ?_).symm
  · intro f _
    exact Finset.mem_univ f
  · intro f hf
    simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_filter, true_and] at hf
    refine kostka_ne_card _ _ ?_
    rw [card_sub (sub_cond f.2.1) f.2.2]
    have hcf := sum_support_subRowLensType_le_card f
    have hme : μ.toList.min hμ + (μ.erase (μ.toList.min hμ)).sum = μ.sum :=
      Multiset.sum_erase <| by rw [← Multiset.mem_toList]; exact List.min_mem hμ
    have hmm : μ.toList.min hμ ≤ μ.sum :=
      Multiset.le_sum_of_mem <| (by rw [← Multiset.mem_toList]; exact List.min_mem hμ)
    lia
  · intro _ _
    rfl

theorem kostka_recursion' {γ : YoungDiagram} {μ : Multiset ℕ} (hμ : μ.toList ≠ []) (h0 : 0 ∉ μ)
    (h : γ.card = μ.sum) :
    kostkaNumber γ μ = ∑ f : SubRowLensType γ with ∑ x ∈ f.1.support, f.1 x = μ.toList.min hμ,
    kostkaNumber (γ.sub f.1) (μ.erase (μ.toList.min hμ)) := by
  rw [kostka_recursion hμ h0 h, sum_subRowLensType_with_sum_eq h]

end


/- Source module: KostkaNumbers.Basic -/
section
/-
Copyright (c) 2026 Noah Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Walker
-/







/-!
This file contains various basic results about the definitions from the Defs file.  We place proofs
here if they are longer or require more imports, so that the Defs file stays lean.
-/

section

open SemistandardYoungTableau YoungDiagram

namespace YoungDiagram

@[simp]
lemma hookDiagram_card (n : ℕ) : (hookDiagram n).card = n := by
  by_cases! hn : n ≥ 2
  · rw! [← ofRowLens_to_rowLens_eq_self (μ := hookDiagram n), hookDiagram_rowLens hn,
      card_ofRowLens]
    all_goals grind
  · interval_cases n <;> simp

@[simp]
lemma hookDiagram_cells {n : ℕ} (h : n > 0) :
    (hookDiagram (n + 1)).cells = (horizontalDiagram n).cells ∪ {(1, 0)} := by
  ext x
  simp [mem_hookDiagram (n + 1) (by lia), Prod.ext_iff]

end YoungDiagram

namespace SemistandardYoungTableau

variable {γ : YoungDiagram} {T : SemistandardYoungTableau γ}

lemma entry_lt_card {μ : Multiset ℕ} (h : T.content = μ.fromCounts) {i j : ℕ}
    (hij : (i, j) ∈ γ) : T i j < μ.card := by
  have := h ▸ mem_content_of_mem hij
  contrapose! this
  exact Multiset.notMem_fromCounts μ (T i j) this

-- lemma entry_eq_zero_of_content_eq_replicate (n : ℕ) (h : T.content = Multiset.replicate n 0)
--     (i j : ℕ) : T i j = 0 := by
--   by_cases hb : γ = ⊥
--   · exact entry_eq_zero_of_bot T hb
--   suffices T i j ∈ T.content by exact Multiset.eq_of_mem_replicate (h ▸ this)
--   by_cases htij : T i j = 0
--   · rw [htij, h, Multiset.mem_replicate]
--     simp only [ne_eq, and_true]
--     contrapose! hb
--     rwa [hb, Multiset.replicate_zero, ← Multiset.bot_eq_zero, content_eq_bot_iff] at h
--   · exact mem_content_of_nonzero htij

theorem top_left_eq_zero_of_content_eq_fromCounts {μ : Multiset ℕ}
    (h : T.content = μ.fromCounts) : T 0 0 = 0 := by
  by_cases! hγ : γ = ⊥
  · exact entry_eq_zero_of_bot T hγ
  have h0 : 0 ∈ μ.fromCounts := by
    refine Multiset.zero_mem_fromCounts_of_nonempty ?_
    rwa [← h, ne_eq, ← bot_eq_zero, content_eq_bot_iff]
  simp only [← h, content, Multiset.mem_map, Finset.mem_val, mem_cells, Prod.exists] at h0
  obtain ⟨i, j, hij, hT⟩ := h0
  refine antisymm ?_ (Nat.zero_le (T 0 0))
  nth_rw 3 [← hT]
  refine le_trans (T.col_weak (Nat.zero_le i) <| γ.up_left_mem (by rfl) (Nat.zero_le j) hij) ?_
  exact T.row_weak_of_le (Nat.zero_le j) hij

end SemistandardYoungTableau

namespace Kostka

section SSYTBot

@[simp] lemma content_SSYTBot (T : SemistandardYoungTableau ⊥) : T.content = ⊥ := by
  simp [content]

@[simp] lemma entry_SSYTBot (T : SemistandardYoungTableau ⊥) (i j : ℕ) : T i j = 0 :=
  T.zeros (notMem_bot (i, j))

instance : Subsingleton (SemistandardYoungTableau ⊥) where
  allEq T T' := by simp [SemistandardYoungTableau.ext_iff]

lemma card_SSYTBot : Nat.card (SemistandardYoungTableau ⊥) = 1 :=
  Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩

lemma kostka_bot_bot : kostkaNumber ⊥ ⊥ = 1 := by
  simp [kostka_eq_card_SSYTWithContent, SemistandardYoungTableauWithContent]

end SSYTBot

end Kostka

end
end


/- Source module: KostkaNumbers.HookLength.HookLengthFormula -/
section
/-
Copyright (c) 2026 Noah Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Walker
-/










/-!
This file formalizes the probabilistic proof of the hook length formula given by
  Greene, Nijenhus, and Wilf (1979).
-/

open MeasureTheory YoungDiagram Kostka
open scoped ENNReal NNReal


open Classical in
lemma subSingle_sum_eq_subRowLensType_sum {γ : YoungDiagram} : ∑ a : SubSingle γ,
    kostkaNumber (γ.sub (Finsupp.single a.1 1)) (Multiset.replicate (γ.card - 1) 1) =
    ∑ f ∈ {g : SubRowLensType γ | ∃ a : ℕ, g.1 = Finsupp.single a 1},
    kostkaNumber (γ.sub f.1) (Multiset.replicate (γ.card - 1) 1) := by
  let e : SubSingle γ → SubRowLensType γ := fun ⟨a, ha⟩ ↦ ⟨Finsupp.single a 1, ha⟩
  refine Finset.sum_nbij e ?_ ?_ ?_ ?_
  · grind
  · intro ⟨a, ha⟩ _ ⟨b, hb⟩ _
    unfold SubRowLensType
    simp [e, Finsupp.single_left_inj]
  · intro ⟨f, hf⟩
    unfold SubRowLensType
    simp [e]
    grind
  · simp [e]

lemma sum_support_gt_one {f : ℕ →₀ ℕ}
    (h : f.support.card ≥ 2 ∨ ∃ a, f a > 1) :
    ∑ x ∈ f.support, f x > 1 := by
  rcases h with h | h
  · have hf : f.support.card • 1 > 1 := by lia
    exact lt_of_lt_of_le hf <| Finset.card_nsmul_le_sum _ _ 1 (by grind)
  · obtain ⟨a, ha⟩ := h
    exact lt_of_lt_of_le ha (Finset.single_le_sum (by lia) (by grind))

theorem kostka_recursion_single {γ : YoungDiagram} (hγ : γ.card ≠ 0) :
    kostkaNumber γ (Multiset.replicate γ.card 1) = ∑ a : SubSingle γ,
    kostkaNumber (γ.sub (Finsupp.single a.1 1)) (Multiset.replicate (γ.card - 1) 1) := by
  have hμ : (Multiset.replicate γ.card 1).toList ≠ [] := by
    rw [ne_eq, Multiset.toList_eq_nil, Eq.comm, Multiset.eq_replicate]
    simp [hγ.symm]
  rw [kostka_recursion hμ (by simp [Multiset.mem_replicate]) (by simp),
    subSingle_sum_eq_subRowLensType_sum]
  symm
  classical refine Finset.sum_subset_zero_on_sdiff (Finset.subset_univ _) ?_ ?_
  · simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_filter, true_and, not_exists]
    intro f ha
    refine kostka_ne_card _ _ ?_
    simp only [card_sub (sub_cond f.2.1) f.2.2, Multiset.replicate_toList, List.min_replicate,
      Multiset.erase_replicate, Multiset.sum_replicate, smul_eq_mul, mul_one, ne_eq]
    by_cases! hf0 : ∑ x ∈ f.1.support, f.1 x = 0
    · lia
    have hf := sum_support_subRowLensType_le_card (f := f)
    suffices ∑ x ∈ f.1.support, f.1 x > 1 by lia
    refine sum_support_gt_one ?_
    contrapose! ha
    obtain ⟨hfs, hf1⟩ := ha
    interval_cases h : f.1.support.card
    · rw [Finset.card_eq_zero, Finsupp.support_eq_empty] at h
      simp [h] at hf0
    · rw [Finset.card_eq_one] at h
      obtain ⟨a, h⟩ := h
      have ha : f.1 a = 1 := by
        have ha : a ∈ f.1.support := by grind
        grind
      apply subset_of_eq at h
      rw [Finsupp.support_subset_singleton, ha] at h
      use a
  · simp [Multiset.erase_replicate]

theorem ennreal_hookLength_formula (γ : YoungDiagram) :
    (kostkaNumber γ (Multiset.replicate γ.card 1) : ℝ≥0∞) =
    Nat.factorial γ.card / ∏ x ∈ γ.cells, γ.hookLength x := by
  by_cases! hγ : γ = ⊥
  · simp only [hγ, bot_card, Multiset.replicate_zero, Nat.factorial_zero, Nat.cast_one, cells_bot,
      Finset.prod_empty, ENNReal.div_self one_ne_zero ENNReal.one_ne_top]
    rw [← bot_eq_zero, kostka_bot_bot, Nat.cast_one]
  rw [ne_eq, eq_bot_iff_card_eq_zero] at hγ
  rw [kostka_recursion_single hγ, Nat.cast_sum, ← coe_F, F_recursion hγ]
  refine Finset.sum_congr (by rfl) ?_
  intro x _
  have hx : γ.card - 1 = (γ.sub (fun₀ | x.1 => 1)).card := by
    simp [card_sub (sub_cond x.2.1) x.2.2]
  rw [hx]
  exact ennreal_hookLength_formula (γ.sub (fun₀ | x.1 => 1))
  termination_by γ.card
  decreasing_by
    suffices γ.card ≠ 0 by lia
    obtain ⟨a, ha⟩ := x
    apply And.right at ha
    specialize ha a
    simp [rowLen'_eq_rowLen] at ha
    rw [ne_eq, ← eq_bot_iff_card_eq_zero, eq_bot_iff_zero_zero_notMem,
      γ.mem_iff_lt_rowLen]
    have h0 : γ.rowLen 0 ≥ γ.rowLen a := γ.rowLen_anti _ _ zero_le
    lia

theorem hookLength_formula (γ : YoungDiagram) {n : ℕ} (h : γ.card = n) :
    (∏ x ∈ γ.cells, γ.hookLength x) *
    kostkaNumber γ (Multiset.replicate n 1) = Nat.factorial n := by
  apply_fun Nat.cast (R := ℝ≥0∞) using CharZero.cast_injective
  subst h
  rw [Nat.cast_mul, ennreal_hookLength_formula γ, ENNReal.mul_div_cancel]
  · simp [Finset.prod_eq_zero_iff, hookLength_ne_zero]
  · simp [ENNReal.prod_ne_top]

theorem hookLength_formula' (γ : YoungDiagram) {n : ℕ} (h : γ.card = n) :
    kostkaNumber γ (Multiset.replicate n 1) =
    Nat.factorial n / (∏ x ∈ γ.cells, γ.hookLength x) := by
  simp [← hookLength_formula γ h, hookLength]

end


namespace OMA.S_oeis_a039622

open Finset

/-- Hook product, with rows and columns counted from the lower right corner. -/
def squareHookProduct (n : ℕ) : ℕ :=
  ∏ i ∈ range n, ∏ j ∈ range n, (i+j+1)

private theorem rising_product (i n : ℕ) :
    (∏ j ∈ range n, (i+j+1))*i.factorial = (i+n).factorial := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [prod_range_succ, ← Nat.add_assoc, Nat.factorial_succ, ← ih]
    ring

theorem square_hook_evaluation (n : ℕ) :
    squareHookProduct n * (∏ i ∈ range n, i.factorial) =
    ∏ i ∈ range n, (n+i).factorial := by
  rw [squareHookProduct,← prod_mul_distrib]
  apply prod_congr rfl
  intro i hi
  simpa [Nat.add_comm n i] using rising_product i n

theorem square_count_of_hooks (n : ℕ)
    (h : squareHookProduct n * tableaux n = (n^2).factorial) :
    tableaux n * (∏ j ∈ range n, (n+j).factorial) =
      (n^2).factorial * (∏ j ∈ range n, j.factorial) := by
  rw [← square_hook_evaluation, ← h]
  ring

private theorem square_rowLen {n i : ℕ} (hi : i<n) : (squareDiagram n).rowLen i=n := by
  apply eq_of_forall_lt_iff
  intro j
  rw [← YoungDiagram.mem_iff_lt_rowLen]
  change (i,j) ∈ range n ×ˢ range n ↔ _
  simp [hi]

private theorem square_colLen {n j : ℕ} (hj : j<n) : (squareDiagram n).colLen j=n := by
  apply eq_of_forall_lt_iff
  intro i
  rw [← YoungDiagram.mem_iff_lt_colLen]
  change (i,j) ∈ range n ×ˢ range n ↔ _
  simp [hj]

theorem reflected_square_hooks (n : ℕ) :
    (∏ x ∈ (squareDiagram n).cells,
      (((squareDiagram n).rowLen x.1 - (x.2+1)) +
        ((squareDiagram n).colLen x.2 - (x.1+1)) + 1)) = squareHookProduct n := by
  change (∏ x ∈ range n ×ˢ range n, _)=_
  rw [prod_product]
  calc
    _ = ∏ i ∈ range n, ∏ j ∈ range n, ((n-1-i)+(n-1-j)+1) := by
      apply prod_congr rfl
      intro i hi
      apply prod_congr rfl
      intro j hj
      rw [square_rowLen (mem_range.mp hi),square_colLen (mem_range.mp hj)]
      omega
    _ = ∏ i ∈ range n, ∏ j ∈ range n, ((n-1-i)+j+1) := by
      apply prod_congr rfl
      intro i hi
      exact prod_range_reflect (fun j : ℕ => (n-1-i)+j+1) n
    _ = squareHookProduct n := prod_range_reflect (fun i => ∏ j ∈ range n, (i+j+1)) n

end OMA.S_oeis_a039622

namespace OMA.S_oeis_a039622

private theorem ones_content (m : ℕ) :
    (Multiset.replicate m 1).fromCounts = Multiset.range m := by
  induction m with
  | zero => simp [Multiset.fromCounts,Multiset.range]
  | succ m ih =>
    rw [Multiset.replicate_succ,Multiset.cons_fromCounts_of_min,ih,Multiset.card_replicate,
      Multiset.replicate_one,Multiset.range_succ,add_comm,Multiset.singleton_add]
    intro x hx
    have := Multiset.eq_of_mem_replicate hx
    omega

private theorem square_kostka (n : ℕ) :
    Kostka.kostkaNumber (squareDiagram n) (Multiset.replicate (n^2) 1) = tableaux n := by
  simp only [Kostka.kostkaNumber,ones_content,SemistandardYoungTableau.content,tableaux]
  rfl

theorem square_count (n : ℕ) :
    tableaux n * (∏ j ∈ Finset.range n, (n+j).factorial) =
      (n^2).factorial * (∏ j ∈ Finset.range n, j.factorial) := by
  apply square_count_of_hooks
  have hc : (squareDiagram n).card = n^2 := by
    simp [YoungDiagram.card,squareDiagram,pow_two]
  have h := hookLength_formula (squareDiagram n) hc
  rw [square_kostka] at h
  rw [← reflected_square_hooks]
  exact h

end OMA.S_oeis_a039622

theorem OMA.solution : type_of% @OMA.S_oeis_a039622.main := OMA.S_oeis_a039622.square_count

open OMA.S_oeis_a039622 Finset in
/-- Normalization used in the conjectured moment after the arithmetic Euler product is removed. -/
theorem OMA.tableau_moment_factor (n : ℕ) :
    (tableaux n : ℝ) / (n^2).factorial =
      ∏ j ∈ range n, ((j.factorial : ℝ) / (n+j).factorial) := by
  rw [prod_div_distrib]
  have ht : (tableaux n : ℝ) * (∏ j ∈ range n, ((n+j).factorial : ℝ)) =
      ((n^2).factorial : ℝ) * (∏ j ∈ range n, (j.factorial : ℝ)) := by
    exact_mod_cast square_count n
  apply (div_eq_div_iff (by positivity) (by positivity)).mpr
  simpa only [mul_comm ((n^2).factorial : ℝ)] using ht
