import OMAReductions.R_Erdos6_erdos_6_variants_decreasing_R1_H1_R1_H2_R2
import Mathlib
-- Adapted from the merged Elliott–Halberstam Siegel–Walfisz leaf by retargeting its identical proposition.
/- Adapted and modified from Whidden (7a1748306e026825ed6a5555516cc2f28989b2ac), PrimeNumberTheoremAnd, Robin1984 and openai/math (3344da59991ed94f9ba711217b29c1d760badfa6, BombieriVinogradov character blocks). Modified for the frozen H1 checker. Sources: kimihiro64/bombieri-vinogradov, kimihiro64/PrimeNumberTheoremAnd@0f15a38c619298b5cd786d39a84dd4bb8997324c, kimihiro64/Robin1984@bfa72aec0c25c8ee29cefe4449d778ff30412bee; openai/math. All four distribute the following Apache-2.0 license.
Authors: James Sundstrom
Authors: Matteo Cipollina
Authors: Michael Stoll
Authors: Robby Sneiderman
Authors: Stefan Kebekus, Matteo Cipollina
Copyright (c) 2024 James Sundstrom. All rights reserved.
Copyright (c) 2024 Michael Stoll. All rights reserved.
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Copyright (c) 2026. All rights reserved.
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

section

section

open Complex Set Topology

open scoped Interval

variable {z w : ℂ} {c : ℝ}

namespace Rectangle

lemma symm : Rectangle z w = Rectangle w z := by
  simp [Rectangle, uIcc_comm]

lemma symm_re : Rectangle (w.re + z.im * I) (z.re + w.im * I) = Rectangle z w := by
  simp [Rectangle, uIcc_comm]

end Rectangle

def RectangleBorder (z w : ℂ) : Set ℂ :=
  [[z.re, w.re]] ×ℂ {z.im} ∪ {z.re} ×ℂ [[z.im, w.im]] ∪
    [[z.re, w.re]] ×ℂ {w.im} ∪ {w.re} ×ℂ [[z.im, w.im]]

def Square (p : ℂ) (c : ℝ) : Set ℂ := Rectangle (-c - c * I + p) (c + c * I + p)

lemma Square_apply (p : ℂ) (cpos : c > 0) :
    Square p c = Icc (-c + p.re) (c + p.re) ×ℂ Icc (-c + p.im) (c + p.im) := by
  rw [Square, Rectangle, uIcc_of_le (by simp; linarith), uIcc_of_le (by simp; linarith)]
  simp

@[simp]
theorem preimage_equivRealProdCLM_reProdIm (s t : Set ℝ) :
    equivRealProdCLM.symm ⁻¹' (s ×ℂ t) = s ×ˢ t :=
  rfl

@[simp]
theorem ContinuousLinearEquiv.coe_toLinearEquiv_symm {R : Type*} {S : Type*} [Semiring R]
    [Semiring S] {σ : R →+* S} {σ' : S →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    (M : Type*) [TopologicalSpace M]
    [AddCommMonoid M] {M₂ : Type*} [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R M]
    [Module S M₂] (e : M ≃SL[σ] M₂) :
    ⇑e.toLinearEquiv.symm = e.symm :=
  rfl

lemma segment_reProdIm_segment_eq_convexHull (z w : ℂ) :
    [[z.re, w.re]] ×ℂ [[z.im, w.im]] =
      convexHull ℝ {z, z.re + w.im * I, w.re + z.im * I, w} := by
  simp_rw [← segment_eq_uIcc, ← convexHull_pair, ← convexHull_reProdIm, reProdIm]
  exact congrArg _ <| Set.ext <| by simpa [Complex.ext_iff] using by tauto

lemma rectangle_in_convex {U : Set ℂ} (U_convex : Convex ℝ U) {z w : ℂ} (hz : z ∈ U)
    (hw : w ∈ U) (hzw : (z.re + w.im * I) ∈ U) (hwz : (w.re + z.im * I) ∈ U) :
    Rectangle z w ⊆ U := by
  rw [Rectangle, segment_reProdIm_segment_eq_convexHull]
  exact convexHull_min (by simp_all [insert_subset_iff]) U_convex

lemma mem_Rect {z w : ℂ} (zRe_lt_wRe : z.re ≤ w.re) (zIm_lt_wIm : z.im ≤ w.im) (p : ℂ) :
    p ∈ Rectangle z w ↔
      z.re ≤ p.re ∧ p.re ≤ w.re ∧ z.im ≤ p.im ∧ p.im ≤ w.im := by
  rw [Rectangle, uIcc_of_le zRe_lt_wRe, uIcc_of_le zIm_lt_wIm]
  exact and_assoc

lemma square_neg (p : ℂ) (c : ℝ) : Square p (-c) = Square p c := by
  simpa [Square] using! Rectangle.symm

theorem Set.left_not_mem_uIoo {a b : ℝ} : a ∉ Set.uIoo a b :=
  fun ⟨h1, h2⟩ ↦ (left_lt_sup.mp h2) (le_of_not_ge (inf_lt_left.mp h1))

theorem Set.right_not_mem_uIoo {a b : ℝ} : b ∉ Set.uIoo a b :=
  fun ⟨h1, h2⟩ ↦ (right_lt_sup.mp h2) (le_of_not_ge (inf_lt_right.mp h1))

theorem Set.ne_left_of_mem_uIoo {a b c : ℝ} (hc : c ∈ Set.uIoo a b) : c ≠ a :=
  fun h ↦ Set.left_not_mem_uIoo (h ▸ hc)

theorem Set.ne_right_of_mem_uIoo {a b c : ℝ} (hc : c ∈ Set.uIoo a b) : c ≠ b :=
  fun h ↦ Set.right_not_mem_uIoo (h ▸ hc)

lemma left_mem_rect (z w : ℂ) : z ∈ Rectangle z w := ⟨left_mem_uIcc, left_mem_uIcc⟩

lemma right_mem_rect (z w : ℂ) : w ∈ Rectangle z w := ⟨right_mem_uIcc, right_mem_uIcc⟩

lemma rect_subset_iff {z w z' w' : ℂ} :
    Rectangle z' w' ⊆ Rectangle z w ↔ z' ∈ Rectangle z w ∧ w' ∈ Rectangle z w := by
  use fun h ↦ ⟨h (left_mem_rect z' w'), h (right_mem_rect z' w')⟩
  intro ⟨⟨⟨hz're_ge, hz're_le⟩, ⟨hz'im_ge, hz'im_le⟩⟩,
    ⟨⟨hw're_ge, hw're_le⟩, ⟨hw'im_ge, hw'im_le⟩⟩⟩ x
    ⟨⟨hxre_ge, hxre_le⟩, ⟨hxim_ge, hxim_le⟩⟩
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · exact (le_inf hz're_ge hw're_ge).trans hxre_ge
  · exact (le_sup_iff.mp hxre_le).casesOn (fun h ↦ h.trans hz're_le)
      (fun h ↦ h.trans hw're_le)
  · exact (le_inf hz'im_ge hw'im_ge).trans hxim_ge
  · exact (le_sup_iff.mp hxim_le).casesOn (fun h ↦ h.trans hz'im_le)
      (fun h ↦ h.trans hw'im_le)

lemma RectSubRect {x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃ : ℝ} (x₀_le_x₁ : x₀ ≤ x₁)
    (x₁_le_x₂ : x₁ ≤ x₂) (x₂_le_x₃ : x₂ ≤ x₃) (y₀_le_y₁ : y₀ ≤ y₁)
    (y₁_le_y₂ : y₁ ≤ y₂) (y₂_le_y₃ : y₂ ≤ y₃) :
    Rectangle (x₁ + y₁ * I) (x₂ + y₂ * I) ⊆
      Rectangle (x₀ + y₀ * I) (x₃ + y₃ * I) := by
  rw [rect_subset_iff, mem_Rect, mem_Rect]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  all_goals simpa using by linarith

lemma RectSubRect' {z₀ z₁ z₂ z₃ : ℂ} (x₀_le_x₁ : z₀.re ≤ z₁.re)
    (x₁_le_x₂ : z₁.re ≤ z₂.re) (x₂_le_x₃ : z₂.re ≤ z₃.re)
    (y₀_le_y₁ : z₀.im ≤ z₁.im) (y₁_le_y₂ : z₁.im ≤ z₂.im)
    (y₂_le_y₃ : z₂.im ≤ z₃.im) :
    Rectangle z₁ z₂ ⊆ Rectangle z₀ z₃ := by
  rw [← re_add_im z₀, ← re_add_im z₁, ← re_add_im z₂, ← re_add_im z₃]
  exact RectSubRect x₀_le_x₁ x₁_le_x₂ x₂_le_x₃ y₀_le_y₁ y₁_le_y₂ y₂_le_y₃

lemma rectangleBorder_subset_rectangle (z w : ℂ) : RectangleBorder z w ⊆ Rectangle z w := by
  intro x hx
  obtain ⟨⟨h | h⟩ | h⟩ | h := hx
  · exact ⟨h.1, h.2 ▸ left_mem_uIcc⟩
  · exact ⟨h.1 ▸ left_mem_uIcc, h.2⟩
  · exact ⟨h.1, h.2 ▸ right_mem_uIcc⟩
  · exact ⟨h.1 ▸ right_mem_uIcc, h.2⟩

lemma rectangle_disjoint_singleton {z w p : ℂ}
    (h : (p.re < z.re ∧ p.re < w.re) ∨ (p.im < z.im ∧ p.im < w.im) ∨
      (z.re < p.re ∧ w.re < p.re) ∨ (z.im < p.im ∧ w.im < p.im)) :
    Disjoint (Rectangle z w) {p} := by
  refine disjoint_singleton_right.mpr (not_and_or.mpr ?_)
  obtain h | h | h | h := h
  · exact Or.inl (notMem_uIcc_of_lt h.1 h.2)
  · exact Or.inr (notMem_uIcc_of_lt h.1 h.2)
  · exact Or.inl (notMem_uIcc_of_gt h.1 h.2)
  · exact Or.inr (notMem_uIcc_of_gt h.1 h.2)

lemma rectangleBorder_disjoint_singleton {z w p : ℂ}
    (h : p.re ≠ z.re ∧ p.re ≠ w.re ∧ p.im ≠ z.im ∧ p.im ≠ w.im) :
    Disjoint (RectangleBorder z w) {p} := by
  refine disjoint_singleton_right.mpr ?_
  simp_rw [RectangleBorder, Set.mem_union, not_or]
  exact ⟨⟨⟨fun hc ↦ h.2.2.1 hc.2, fun hc ↦ h.1 hc.1⟩, fun hc ↦ h.2.2.2 hc.2⟩,
    fun hc ↦ h.2.1 hc.1⟩

lemma rectangle_subset_punctured_rect {z₀ z₁ z₂ z₃ p : ℂ}
    (hz : z₀.re ≤ z₁.re ∧ z₁.re ≤ z₂.re ∧ z₂.re ≤ z₃.re ∧
      z₀.im ≤ z₁.im ∧ z₁.im ≤ z₂.im ∧ z₂.im ≤ z₃.im)
    (hp : (p.re < z₁.re ∧ p.re < z₂.re) ∨ (p.im < z₁.im ∧ p.im < z₂.im) ∨
      (z₁.re < p.re ∧ z₂.re < p.re) ∨ (z₁.im < p.im ∧ z₂.im < p.im)) :
    Rectangle z₁ z₂ ⊆ Rectangle z₀ z₃ \ {p} :=
  Set.subset_sdiff.mpr ⟨by apply RectSubRect' <;> tauto, rectangle_disjoint_singleton hp⟩

lemma rectangleBorder_subset_punctured_rect {z₀ z₁ z₂ z₃ p : ℂ}
    (hz : z₀.re ≤ z₁.re ∧ z₁.re ≤ z₂.re ∧ z₂.re ≤ z₃.re ∧
      z₀.im ≤ z₁.im ∧ z₁.im ≤ z₂.im ∧ z₂.im ≤ z₃.im)
    (hp : p.re ≠ z₁.re ∧ p.re ≠ z₂.re ∧ p.im ≠ z₁.im ∧ p.im ≠ z₂.im) :
    RectangleBorder z₁ z₂ ⊆ Rectangle z₀ z₃ \ {p} :=
  Set.subset_sdiff.mpr ⟨
    (rectangleBorder_subset_rectangle _ _).trans (by apply RectSubRect' <;> tauto),
    rectangleBorder_disjoint_singleton hp⟩

lemma rectangle_mem_nhds_iff {z w p : ℂ} :
    Rectangle z w ∈ 𝓝 p ↔ p ∈ (Set.uIoo z.re w.re) ×ℂ (Set.uIoo z.im w.im) := by
  simp_rw [← mem_interior_iff_mem_nhds, Rectangle, Complex.interior_reProdIm, uIoo, uIcc,
    interior_Icc]

lemma mapsTo_rectangle_left_re (z w : ℂ) :
    MapsTo (fun (y : ℝ) => ↑z.re + ↑y * I) [[z.im, w.im]] (Rectangle z w) :=
  fun _ hx ↦ ⟨by simp, by simp [hx]⟩

lemma mapsTo_rectangle_right_re (z w : ℂ) :
    MapsTo (fun (y : ℝ) => ↑w.re + ↑y * I) [[z.im, w.im]] (Rectangle z w) :=
  fun _ hx ↦ ⟨by simp, by simp [hx]⟩

lemma mapsTo_rectangle_left_im (z w : ℂ) :
    MapsTo (fun (x : ℝ) => ↑x + z.im * I) [[z.re, w.re]] (Rectangle z w) :=
  fun _ hx ↦ ⟨by simp [hx], by simp⟩

lemma mapsTo_rectangle_right_im (z w : ℂ) :
    MapsTo (fun (x : ℝ) => ↑x + w.im * I) [[z.re, w.re]] (Rectangle z w) :=
  fun _ hx ↦ ⟨by simp [hx], by simp⟩

lemma mapsTo_rectangleBorder_left_re (z w : ℂ) :
    MapsTo (fun (y : ℝ) => ↑z.re + ↑y * I) [[z.im, w.im]] (RectangleBorder z w) :=
  (Set.mapsTo_image _ _).mono subset_rfl fun _ ↦
    by simp_all [verticalSegment_eq, RectangleBorder]

lemma mapsTo_rectangleBorder_right_re (z w : ℂ) :
    MapsTo (fun (y : ℝ) => ↑w.re + ↑y * I) [[z.im, w.im]] (RectangleBorder z w) :=
  (Set.mapsTo_image _ _).mono subset_rfl fun _ ↦
    by simp_all [verticalSegment_eq, RectangleBorder]

lemma mapsTo_rectangleBorder_left_im (z w : ℂ) :
    MapsTo (fun (x : ℝ) => ↑x + z.im * I) [[z.re, w.re]] (RectangleBorder z w) :=
  (Set.mapsTo_image _ _).mono subset_rfl fun _ ↦
    by simp_all [horizontalSegment_eq, RectangleBorder]

lemma mapsTo_rectangleBorder_right_im (z w : ℂ) :
    MapsTo (fun (x : ℝ) => ↑x + w.im * I) [[z.re, w.re]] (RectangleBorder z w) :=
  (Set.mapsTo_image _ _).mono subset_rfl fun _ ↦
    by simp_all [horizontalSegment_eq, RectangleBorder]

lemma mapsTo_rectangle_left_re_NoP (z w : ℂ) {p : ℂ}
    (pNotOnBorder : p ∉ RectangleBorder z w) :
    MapsTo (fun (y : ℝ) => ↑z.re + ↑y * I) [[z.im, w.im]] (Rectangle z w \ {p}) := by
  refine (mapsTo_rectangleBorder_left_re z w).mono_right (Set.subset_sdiff.mpr ?_)
  exact ⟨rectangleBorder_subset_rectangle z w, disjoint_singleton_right.mpr pNotOnBorder⟩

lemma mapsTo_rectangle_right_re_NoP (z w : ℂ) {p : ℂ}
    (pNotOnBorder : p ∉ RectangleBorder z w) :
    MapsTo (fun (y : ℝ) => ↑w.re + ↑y * I) [[z.im, w.im]] (Rectangle z w \ {p}) := by
  refine (mapsTo_rectangleBorder_right_re z w).mono_right (Set.subset_sdiff.mpr ?_)
  exact ⟨rectangleBorder_subset_rectangle z w, disjoint_singleton_right.mpr pNotOnBorder⟩

lemma mapsTo_rectangle_left_im_NoP (z w : ℂ) {p : ℂ}
    (pNotOnBorder : p ∉ RectangleBorder z w) :
    MapsTo (fun (x : ℝ) => ↑x + z.im * I) [[z.re, w.re]] (Rectangle z w \ {p}) := by
  refine (mapsTo_rectangleBorder_left_im z w).mono_right (Set.subset_sdiff.mpr ?_)
  exact ⟨rectangleBorder_subset_rectangle z w, disjoint_singleton_right.mpr pNotOnBorder⟩

lemma mapsTo_rectangle_right_im_NoP (z w : ℂ) {p : ℂ}
    (pNotOnBorder : p ∉ RectangleBorder z w) :
    MapsTo (fun (x : ℝ) => ↑x + w.im * I) [[z.re, w.re]] (Rectangle z w \ {p}) := by
  refine (mapsTo_rectangleBorder_right_im z w).mono_right (Set.subset_sdiff.mpr ?_)
  exact ⟨rectangleBorder_subset_rectangle z w, disjoint_singleton_right.mpr pNotOnBorder⟩

theorem not_mem_rectangleBorder_of_rectangle_mem_nhds {z w p : ℂ}
    (hp : Rectangle z w ∈ 𝓝 p) :
    p ∉ RectangleBorder z w := by
  refine Set.disjoint_right.mp (rectangleBorder_disjoint_singleton ?_) rfl
  have h1 := rectangle_mem_nhds_iff.mp hp
  exact ⟨Set.ne_left_of_mem_uIoo h1.1, Set.ne_right_of_mem_uIoo h1.1,
    Set.ne_left_of_mem_uIoo h1.2, Set.ne_right_of_mem_uIoo h1.2⟩

theorem Complex.nhds_hasBasis_square (p : ℂ) : (𝓝 p).HasBasis (0 < ·) (Square p ·) := by
  suffices
      (𝓝 p.re ×ˢ 𝓝 p.im).HasBasis (0 < ·)
        (equivRealProdCLM.symm.toHomeomorph ⁻¹' Square p ·)
    by simpa only [← nhds_prod_eq, Homeomorph.map_nhds_eq, Homeomorph.image_preimage]
      using! this.map equivRealProdCLM.symm.toHomeomorph
  apply ((nhds_basis_Icc_pos p.re).prod_same_index_mono (nhds_basis_Icc_pos p.im) ?_ ?_).congr
  · intro; rfl
  · intros
    rw [← uIcc_of_lt (by linarith), ← uIcc_of_lt (by linarith)]
    simpa [Square, Rectangle] using by ring_nf
  all_goals exact (antitone_const_tsub.Icc (monotone_id.const_add _)).monotoneOn _

lemma square_mem_nhds (p : ℂ) {c : ℝ} (hc : c ≠ 0) :
    Square p c ∈ 𝓝 p := by
  wlog hc_pos : 0 < c generalizing c with h
  · rw [← square_neg]
    exact h (neg_ne_zero.mpr hc) <| neg_pos.mpr <| hc.lt_of_le <| not_lt.mp hc_pos
  exact (nhds_hasBasis_square p).mem_of_mem hc_pos

lemma square_subset_square {p : ℂ} {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc : c₁ ≤ c₂) :
    Square p c₁ ⊆ Square p c₂ := by
  apply RectSubRect' <;> simpa using by linarith

lemma SmallSquareInRectangle {z w p : ℂ} (pInRectInterior : Rectangle z w ∈ nhds p) :
    ∀ᶠ (c : ℝ) in 𝓝[>]0, Square p c ⊆ Rectangle z w := by
  obtain ⟨ε, hε0, hε⟩ := ((Complex.nhds_hasBasis_square p).1 _).mp pInRectInterior
  filter_upwards [Ioo_mem_nhdsGT (hε0)] with _ ⟨hε'0, hε'⟩
  exact subset_trans (square_subset_square hε'0 hε'.le) hε

end

section

open Complex BigOperators Nat Classical Real Topology Filter
open Set MeasureTheory intervalIntegral Asymptotics

open scoped Interval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f g : ℂ → E} {z w p c A : ℂ}
  {x x₁ x₂ y y₁ y₂ σ : ℝ}

noncomputable def HIntegral (f : ℂ → E) (x₁ x₂ y : ℝ) : E :=
    ∫ x in x₁..x₂, f (x + y * I)

noncomputable def VIntegral (f : ℂ → E) (x y₁ y₂ : ℝ) : E :=
    I • ∫ y in y₁..y₂, f (x + y * I)

noncomputable def HIntegral' (f : ℂ → E) (x₁ x₂ y : ℝ) : E :=
    (1 / (2 * π * I)) • HIntegral f x₁ x₂ y

noncomputable def VIntegral' (f : ℂ → E) (x y₁ y₂ : ℝ) : E :=
    (1 / (2 * π * I)) • VIntegral f x y₁ y₂

lemma HIntegral_symm :
    HIntegral f x₁ x₂ y = -HIntegral f x₂ x₁ y := integral_symm _ _

lemma VIntegral_symm :
    VIntegral f x y₁ y₂ = -VIntegral f x y₂ y₁ := by
  simp_rw [VIntegral, integral_symm y₁ y₂, smul_neg, neg_neg]

noncomputable def RectangleIntegral (f : ℂ → E) (z w : ℂ) : E :=
    HIntegral f z.re w.re z.im - HIntegral f z.re w.re w.im +
    VIntegral f w.re z.im w.im - VIntegral f z.re z.im w.im

noncomputable abbrev RectangleIntegral' (f : ℂ → E) (z w : ℂ) : E :=
    (1 / (2 * π * I)) • RectangleIntegral f z w

noncomputable def UpperUIntegral (f : ℂ → E) (σ σ' T : ℝ) : E :=
    HIntegral f σ σ' T +
    I • (∫ y : ℝ in Ici T, f (σ' + y * I)) -
    I • (∫ y : ℝ in Ici T, f (σ + y * I))

noncomputable def LowerUIntegral (f : ℂ → E) (σ σ' T : ℝ) : E :=
    HIntegral f σ σ' (-T) -
    I • (∫ y : ℝ in Iic (-T), f (σ' + y * I)) +
    I • (∫ y : ℝ in Iic (-T), f (σ + y * I))

noncomputable def VerticalIntegral (f : ℂ → E) (σ : ℝ) : E :=
    I • ∫ t : ℝ, f (σ + t * I)

noncomputable abbrev VerticalIntegral' (f : ℂ → E) (σ : ℝ) : E :=
    (1 / (2 * π * I)) • VerticalIntegral f σ

lemma verticalIntegral_split_three (a b : ℝ)
    (hf : Integrable (fun t : ℝ ↦ f (σ + t * I))) :
    VerticalIntegral f σ =
      I • (∫ t in Iic a, f (σ + t * I)) + VIntegral f σ a b +
      I • ∫ t in Ici b, f (σ + t * I) := by
  simp_rw [VerticalIntegral, VIntegral, ← smul_add]
  congr
  rw [← integral_Iic_sub_Iic hf.restrict hf.restrict, add_sub_cancel,
    integral_Iic_eq_integral_Iio, integral_Iio_add_Ici hf.restrict hf.restrict]

lemma DiffVertRect_eq_UpperLowerUs {σ σ' T : ℝ}
    (f_int_σ : Integrable (fun (t : ℝ) ↦ f (σ + t * I)))
    (f_int_σ' : Integrable (fun (t : ℝ) ↦ f (σ' + t * I))) :
    VerticalIntegral f σ' - VerticalIntegral f σ -
      RectangleIntegral f (σ - I * T) (σ' + I * T) =
    UpperUIntegral f σ σ' T - LowerUIntegral f σ σ' T := by
  rw [verticalIntegral_split_three (-T) T f_int_σ, verticalIntegral_split_three (-T) T f_int_σ']
  simp only [RectangleIntegral, UpperUIntegral, LowerUIntegral]
  simp only [sub_re, mul_re, I_re, add_re, ofReal_re, I_im, ofReal_im, sub_im, mul_im, add_im]
  ring_nf
  abel

abbrev HolomorphicOn (f : ℂ → E) (s : Set ℂ) : Prop :=
    DifferentiableOn ℂ f s

theorem existsDifferentiableOn_of_bddAbove [CompleteSpace E]
    {s : Set ℂ} {c : ℂ} (hc : s ∈ nhds c)
    (hd : HolomorphicOn f (s \ {c}))
    (hb : BddAbove (norm ∘ f '' (s \ {c}))) :
    ∃ (g : ℂ → E),
      HolomorphicOn g s ∧ Set.EqOn f g (s \ {c}) :=
  ⟨Function.update f c (limUnder (𝓝[{c}ᶜ] c) f),
    differentiableOn_update_limUnder_of_bddAbove hc hd hb,
    fun z hz ↦ if h : z = c then (hz.2 h).elim
      else by simp [h]⟩

theorem HolomorphicOn.vanishesOnRectangle [CompleteSpace E]
    {U : Set ℂ} (f_holo : HolomorphicOn f U)
    (hU : Rectangle z w ⊆ U) :
    RectangleIntegral f z w = 0 :=
  integral_boundary_rect_eq_zero_of_differentiableOn f z w
    (f_holo.mono hU)

theorem RectangleIntegral_congr (h : Set.EqOn f g (RectangleBorder z w)) :
    RectangleIntegral f z w = RectangleIntegral g z w := by
  unfold RectangleIntegral VIntegral
  congrm ?_ - ?_ + I • ?_ - I • ?_
  all_goals refine integral_congr fun _ _ ↦ h ?_
  · exact Or.inl <| Or.inl <| Or.inl ⟨by simpa, by simp⟩
  · exact Or.inl <| Or.inr ⟨by simpa, by simp⟩
  · exact Or.inr ⟨by simp, by simpa⟩
  · exact Or.inl <| Or.inl <| Or.inr ⟨by simp, by simpa⟩

theorem RectangleIntegral'_congr (h : Set.EqOn f g (RectangleBorder z w)) :
    RectangleIntegral' f z w = RectangleIntegral' g z w := by
  rw [RectangleIntegral', RectangleIntegral_congr h]

theorem rectangleIntegral_symm (f : ℂ → E) (z w : ℂ) :
    RectangleIntegral f z w = RectangleIntegral f w z := by
  simp_rw [RectangleIntegral, HIntegral, VIntegral, intervalIntegral.integral_symm w.re,
    intervalIntegral.integral_symm w.im, sub_neg_eq_add, smul_neg, sub_neg_eq_add,
    ← sub_eq_add_neg, neg_add_eq_sub, sub_add_eq_add_sub]

theorem rectangleIntegral_symm_re (f : ℂ → E) (z w : ℂ) :
    RectangleIntegral f (w.re + z.im * I) (z.re + w.im * I) = -RectangleIntegral f z w := by
  simp only [RectangleIntegral, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
    mul_one, sub_self, add_zero, add_im, mul_im, zero_add, neg_sub, ← sub_eq_zero, sub_zero]
  rw [HIntegral_symm (y := z.im), HIntegral_symm (y := w.im)]
  abel

def RectangleBorderIntegrable (f : ℂ → E) (z w : ℂ) : Prop :=
    IntervalIntegrable (fun x => f (x + z.im * I)) volume z.re w.re ∧
    IntervalIntegrable (fun x => f (x + w.im * I)) volume z.re w.re ∧
    IntervalIntegrable (fun y => f (w.re + y * I)) volume z.im w.im ∧
    IntervalIntegrable (fun y => f (z.re + y * I)) volume z.im w.im

theorem RectangleBorderIntegrable.add {f g : ℂ → E}
    (hf : RectangleBorderIntegrable f z w) (hg : RectangleBorderIntegrable g z w) :
    RectangleIntegral (f + g) z w = RectangleIntegral f z w + RectangleIntegral g z w := by
  dsimp [RectangleIntegral, HIntegral, VIntegral]
  have h₁ := intervalIntegral.integral_add hf.1 hg.1
  have h₂ := intervalIntegral.integral_add hf.2.1 hg.2.1
  have h₃ := intervalIntegral.integral_add hf.2.2.1 hg.2.2.1
  have h₄ := intervalIntegral.integral_add hf.2.2.2 hg.2.2.2
  rw [h₁, h₂, h₃, h₄]
  module

theorem ContinuousOn.rectangleBorder_integrable {F : Type*} [NormedAddCommGroup F] {f : ℂ → F} (hf : ContinuousOn f (RectangleBorder z w)) :
    RectangleBorderIntegrable f z w :=
  ⟨(hf.comp (by fun_prop) (mapsTo_rectangleBorder_left_im z w)).intervalIntegrable,
    (hf.comp (by fun_prop) (mapsTo_rectangleBorder_right_im z w)).intervalIntegrable,
    (hf.comp (by fun_prop) (mapsTo_rectangleBorder_right_re z w)).intervalIntegrable,
    (hf.comp (by fun_prop) (mapsTo_rectangleBorder_left_re z w)).intervalIntegrable⟩

theorem ContinuousOn.rectangleBorderIntegrable {F : Type*} [NormedAddCommGroup F] {f : ℂ → F} (hf : ContinuousOn f (Rectangle z w)) :
    RectangleBorderIntegrable f z w :=
  ContinuousOn.rectangleBorder_integrable (hf.mono (rectangleBorder_subset_rectangle z w))

theorem ContinuousOn.rectangleBorderNoPIntegrable {F : Type*} [NormedAddCommGroup F] {f : ℂ → F}
    (hf : ContinuousOn f (Rectangle z w \ {p})) (pNotOnBorder : p ∉ RectangleBorder z w) :
    RectangleBorderIntegrable f z w := by
  refine ContinuousOn.rectangleBorder_integrable (hf.mono (Set.subset_sdiff.mpr ?_))
  exact ⟨rectangleBorder_subset_rectangle z w, disjoint_singleton_right.mpr pNotOnBorder⟩

theorem HolomorphicOn.rectangleBorderIntegrable'
    (hf : HolomorphicOn f (Rectangle z w \ {p})) (hp : Rectangle z w ∈ nhds p) :
    RectangleBorderIntegrable f z w :=
  hf.continuousOn.rectangleBorderNoPIntegrable (not_mem_rectangleBorder_of_rectangle_mem_nhds hp)

theorem HolomorphicOn.rectangleBorderIntegrable (hf : HolomorphicOn f (Rectangle z w)) :
    RectangleBorderIntegrable f z w := hf.continuousOn.rectangleBorderIntegrable

lemma RectangleIntegralHSplit {a x₀ x₁ y₀ y₁ : ℝ}
    (f_int_x₀_a_bot : IntervalIntegrable (fun x => f (↑x + ↑y₀ * I)) volume x₀ a)
    (f_int_a_x₁_bot : IntervalIntegrable (fun x => f (↑x + ↑y₀ * I)) volume a x₁)
    (f_int_x₀_a_top : IntervalIntegrable (fun x => f (↑x + ↑y₁ * I)) volume x₀ a)
    (f_int_a_x₁_top : IntervalIntegrable (fun x => f (↑x + ↑y₁ * I)) volume a x₁) :
    RectangleIntegral f (x₀ + y₀ * I) (x₁ + y₁ * I) =
      RectangleIntegral f (x₀ + y₀ * I) (a + y₁ * I) +
      RectangleIntegral f (a + y₀ * I) (x₁ + y₁ * I) := by
  dsimp [RectangleIntegral, HIntegral, VIntegral]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_one, mul_zero, add_zero, zero_add, sub_self]
  have h₁ := integral_add_adjacent_intervals f_int_x₀_a_bot f_int_a_x₁_bot
  have h₂ := integral_add_adjacent_intervals f_int_x₀_a_top f_int_a_x₁_top
  have h₁' :
      (∫ (x : ℝ) in x₀..a, f (↑x + ↑y₀ * I)) +
          ∫ (x : ℝ) in a..x₁, f (↑y₀ * I + ↑x) =
        ∫ (x : ℝ) in x₀..x₁, f (↑x + ↑y₀ * I) := by
    simpa [add_comm] using h₁
  have h₂' :
      (∫ (x : ℝ) in x₀..a, f (↑x + ↑y₁ * I)) +
          ∫ (x : ℝ) in a..x₁, f (↑y₁ * I + ↑x) =
        ∫ (x : ℝ) in x₀..x₁, f (↑x + ↑y₁ * I) := by
    simpa [add_comm] using h₂
  rw [← h₁', ← h₂']
  have hcomm₁ :
      ∫ (x : ℝ) in a..x₁, f (↑y₀ * I + ↑x) =
        ∫ (x : ℝ) in a..x₁, f (↑x + ↑y₀ * I) := by
    apply intervalIntegral.integral_congr
    intro x _
    exact congrArg f (by ring)
  have hcomm₂ :
      ∫ (x : ℝ) in a..x₁, f (↑y₁ * I + ↑x) =
        ∫ (x : ℝ) in a..x₁, f (↑x + ↑y₁ * I) := by
    apply intervalIntegral.integral_congr
    intro x _
    exact congrArg f (by ring)
  rw [hcomm₁, hcomm₂]
  abel

lemma RectangleIntegralHSplit' {a x₀ x₁ y₀ y₁ : ℝ}
    (ha : a ∈ [[x₀, x₁]])
    (hf : RectangleBorderIntegrable f (↑x₀ + ↑y₀ * I) (↑x₁ + ↑y₁ * I)) :
    RectangleIntegral f (x₀ + y₀ * I) (x₁ + y₁ * I) =
      RectangleIntegral f (x₀ + y₀ * I) (a + y₁ * I) +
      RectangleIntegral f (a + y₀ * I) (x₁ + y₁ * I) :=
  RectangleIntegralHSplit
    (IntervalIntegrable.mono (by simpa using hf.1) (uIcc_subset_uIcc left_mem_uIcc ha) le_rfl)
    (IntervalIntegrable.mono (by simpa using hf.1) (uIcc_subset_uIcc ha right_mem_uIcc) le_rfl)
    (IntervalIntegrable.mono (by simpa using hf.2.1) (uIcc_subset_uIcc left_mem_uIcc ha) le_rfl)
    (IntervalIntegrable.mono (by simpa using hf.2.1) (uIcc_subset_uIcc ha right_mem_uIcc) le_rfl)

lemma RectangleIntegralVSplit {b x₀ x₁ y₀ y₁ : ℝ}
    (f_int_y₀_b_left : IntervalIntegrable (fun y => f (x₀ + y * I)) volume y₀ b)
    (f_int_b_y₁_left : IntervalIntegrable (fun y => f (x₀ + y * I)) volume b y₁)
    (f_int_y₀_b_right : IntervalIntegrable (fun y => f (x₁ + y * I)) volume y₀ b)
    (f_int_b_y₁_right : IntervalIntegrable (fun y => f (x₁ + y * I)) volume b y₁) :
    RectangleIntegral f (x₀ + y₀ * I) (x₁ + y₁ * I) =
      RectangleIntegral f (x₀ + y₀ * I) (x₁ + b * I) +
      RectangleIntegral f (x₀ + b * I) (x₁ + y₁ * I) := by
  dsimp [RectangleIntegral, HIntegral, VIntegral]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_one, mul_zero, add_zero, zero_add, sub_self]
  have h₁ := integral_add_adjacent_intervals f_int_y₀_b_left f_int_b_y₁_left
  have h₂ := integral_add_adjacent_intervals f_int_y₀_b_right f_int_b_y₁_right
  rw [← h₁, ← h₂]
  module

lemma RectangleIntegralVSplit' {b x₀ x₁ y₀ y₁ : ℝ}
    (hb : b ∈ [[y₀, y₁]])
    (hf : RectangleBorderIntegrable f (↑x₀ + ↑y₀ * I) (↑x₁ + ↑y₁ * I)) :
    RectangleIntegral f (x₀ + y₀ * I) (x₁ + y₁ * I) =
      RectangleIntegral f (x₀ + y₀ * I) (x₁ + b * I) +
      RectangleIntegral f (x₀ + b * I) (x₁ + y₁ * I) :=
  RectangleIntegralVSplit
    (IntervalIntegrable.mono (by simpa using hf.2.2.2) (uIcc_subset_uIcc left_mem_uIcc hb) le_rfl)
    (IntervalIntegrable.mono (by simpa using hf.2.2.2) (uIcc_subset_uIcc hb right_mem_uIcc) le_rfl)
    (IntervalIntegrable.mono (by simpa using hf.2.2.1) (uIcc_subset_uIcc left_mem_uIcc hb) le_rfl)
    (IntervalIntegrable.mono (by simpa using hf.2.2.1) (uIcc_subset_uIcc hb right_mem_uIcc) le_rfl)

lemma RectanglePullToNhdOfPole' [CompleteSpace E] {z₀ z₁ z₂ z₃ p : ℂ}
    (h_orientation : z₀.re ≤ z₃.re ∧ z₀.im ≤ z₃.im ∧
      z₁.re ≤ z₂.re ∧ z₁.im ≤ z₂.im)
    (hp : Rectangle z₁ z₂ ∈ 𝓝 p) (hz : Rectangle z₁ z₂ ⊆ Rectangle z₀ z₃)
    (fHolo : HolomorphicOn f (Rectangle z₀ z₃ \ {p})) :
    RectangleIntegral f z₀ z₃ = RectangleIntegral f z₁ z₂ := by
  obtain ⟨hz₀_re, hz₀_im, hz₁_re, hz₁_im⟩ := h_orientation
  have := rect_subset_iff.mp hz
  rw [Rectangle, uIcc_of_le hz₀_re, uIcc_of_le hz₀_im] at this
  obtain ⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨_, _⟩, ⟨_, _⟩⟩ := this
  obtain ⟨⟨_, _⟩, ⟨_, _⟩⟩ :=
    (uIoo_of_le hz₁_re) ▸ (uIoo_of_le hz₁_im) ▸ rectangle_mem_nhds_iff.mp hp
  obtain ⟨_, _, _, _⟩ := show
      p.re < z₂.re ∧ p.re < z₃.re ∧ p.im < z₂.im ∧ p.im < z₃.im from
    ⟨by linarith, by linarith, by linarith, by linarith⟩
  obtain ⟨_, _, _, _⟩ := show
      z₀.re < p.re ∧ z₁.re < p.re ∧ z₀.im < p.im ∧ z₁.im < p.im from
    ⟨by linarith, by linarith, by linarith, by linarith⟩
  have fCont := fHolo.continuousOn
  have hbot : RectangleBorderIntegrable f (↑z₀.re + ↑z₀.im * I)
      (↑z₃.re + ↑z₃.im * I) := ?_
  have htop : RectangleBorderIntegrable f (↑z₀.re + ↑z₁.im * I)
      (↑z₃.re + ↑z₃.im * I) := ?_
  have hleft : RectangleBorderIntegrable f (↑z₀.re + ↑z₁.im * I)
      (↑z₃.re + ↑z₂.im * I) := ?_
  have hright : RectangleBorderIntegrable f (↑z₁.re + ↑z₁.im * I)
      (↑z₃.re + ↑z₂.im * I) := ?_
  all_goals try {
    refine ContinuousOn.rectangleBorder_integrable
      (fCont.mono (rectangleBorder_subset_punctured_rect ?_ ?_))
    · simp_all
    · simpa using ⟨by linarith, by linarith, by linarith, by linarith⟩
  }
  have hbot' : z₁.im ∈ [[z₀.im, z₃.im]] := ?_
  have htop' : z₂.im ∈ [[z₁.im, z₃.im]] := ?_
  have hleft' : z₁.re ∈ [[z₀.re, z₃.re]] := ?_
  have hright' : z₂.re ∈ [[z₁.re, z₃.re]] := ?_
  all_goals try {
    rw [Set.uIcc_of_le]
    constructor
    all_goals assumption
  }
  have hbot'' : Rectangle (↑z₀.re + ↑z₀.im * I) (↑z₃.re + ↑z₁.im * I) ⊆
    Rectangle z₀ z₃ \ {p} := ?_
  have htop'' : Rectangle (↑z₀.re + ↑z₂.im * I) (↑z₃.re + ↑z₃.im * I) ⊆
    Rectangle z₀ z₃ \ {p} := ?_
  have hleft'' : Rectangle (↑z₀.re + ↑z₁.im * I) (↑z₁.re + ↑z₂.im * I) ⊆
    Rectangle z₀ z₃ \ {p} := ?_
  have hright'' : Rectangle (↑z₂.re + ↑z₁.im * I) (↑z₃.re + ↑z₂.im * I) ⊆
    Rectangle z₀ z₃ \ {p} := ?_
  all_goals try { apply rectangle_subset_punctured_rect <;> simp_all }
  have h₁ := RectangleIntegralVSplit' hbot' hbot
  have h₂ := fHolo.vanishesOnRectangle hbot''
  have h₃ := RectangleIntegralVSplit' htop' htop
  have h₄ := fHolo.vanishesOnRectangle htop''
  have h₅ := RectangleIntegralHSplit' hleft' hleft
  have h₆ := fHolo.vanishesOnRectangle hleft''
  have h₇ := RectangleIntegralHSplit' hright' hright
  have h₈ := fHolo.vanishesOnRectangle hright''
  simp only [re_add_im] at *
  simp only [h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, zero_add, add_zero]

lemma RectanglePullToNhdOfPole [CompleteSpace E] {z w p : ℂ}
    (zRe_lt_wRe : z.re ≤ w.re) (zIm_lt_wIm : z.im ≤ w.im)
    (hp : Rectangle z w ∈ 𝓝 p) (fHolo : HolomorphicOn f (Rectangle z w \ {p})) :
    ∀ᶠ (c : ℝ) in 𝓝[>]0,
      RectangleIntegral f z w = RectangleIntegral f (-c - I * c + p) (c + I * c + p) := by
  filter_upwards [Ioo_mem_nhdsGT zero_lt_one, SmallSquareInRectangle hp]
  intro c ⟨cpos, _⟩ hc
  simp_rw [mul_comm I]
  exact RectanglePullToNhdOfPole' (by simp_all [cpos.le])
    (square_mem_nhds p (ne_of_gt cpos)) hc fHolo

lemma RectanglePullToNhdOfPole'' [CompleteSpace E] {z w p : ℂ}
    (zRe_le_wRe : z.re ≤ w.re) (zIm_le_wIm : z.im ≤ w.im)
    (pInRectInterior : Rectangle z w ∈ 𝓝 p) (fHolo : HolomorphicOn f (Rectangle z w \ {p})) :
    ∀ᶠ (c : ℝ) in 𝓝[>]0,
      RectangleIntegral' f z w = RectangleIntegral' f (-c - I * c + p) (c + I * c + p) := by
  filter_upwards [RectanglePullToNhdOfPole zRe_le_wRe zIm_le_wIm pInRectInterior fHolo] with c h
  simp_rw [RectangleIntegral', h]

theorem ResidueTheoremAtOrigin_aux1c (a b : ℝ) :
    let f : ℝ → ℂ := fun y => (y + I)⁻¹
    IntervalIntegrable f volume a b :=
  (ContinuousOn.inv₀ (by fun_prop)
    (by simp [Complex.ext_iff])).intervalIntegrable

theorem ResidueTheoremAtOrigin_aux1c' (a b : ℝ) :
    let f : ℝ → ℂ := fun y => (y - I)⁻¹
    IntervalIntegrable f volume a b :=
  (ContinuousOn.inv₀ (by fun_prop)
    (by simp [Complex.ext_iff])).intervalIntegrable

theorem ResidueTheoremAtOrigin_aux2c (a b : ℝ) :
    let f : ℝ → ℂ := fun y => (1 + y * I)⁻¹
    IntervalIntegrable f volume a b :=
  (ContinuousOn.inv₀ (by fun_prop)
    (by simp [Complex.ext_iff])).intervalIntegrable

theorem ResidueTheoremAtOrigin_aux2c' (a b : ℝ) :
    let f : ℝ → ℂ := fun y => (-1 + y * I)⁻¹
    IntervalIntegrable f volume a b :=
  (ContinuousOn.inv₀ (by fun_prop)
    (by simp [Complex.ext_iff])).intervalIntegrable

theorem RectangleIntegral.const_smul (f : ℂ → E) (z w c : ℂ) :
    RectangleIntegral (fun s => c • f s) z w = c • RectangleIntegral f z w := by
  simp [RectangleIntegral, HIntegral, VIntegral, smul_add, smul_sub, smul_smul, mul_comm]

theorem RectangleIntegral.const_mul' (f : ℂ → E) (z w c : ℂ) :
    RectangleIntegral' (fun s => c • f s) z w = c • RectangleIntegral' f z w := by
  simp [RectangleIntegral', RectangleIntegral.const_smul, smul_smul]
  ring_nf

theorem RectangleIntegral.translate (f : ℂ → E) (z w p : ℂ) :
    RectangleIntegral (fun s => f (s - p)) z w = RectangleIntegral f (z - p) (w - p) := by
  simp_rw [RectangleIntegral, HIntegral, VIntegral, sub_re, sub_im,
    ← intervalIntegral.integral_comp_sub_right]
  congr <;> ext <;> congr 1 <;> simp [Complex.ext_iff]

theorem RectangleIntegral.translate' (f : ℂ → E) (z w p : ℂ) :
    RectangleIntegral' (fun s => f (s - p)) z w = RectangleIntegral' f (z - p) (w - p) := by
  simp_rw [RectangleIntegral', RectangleIntegral.translate]

lemma Complex.inv_re_add_im : (x + y * I)⁻¹ = (x - I * y) / (x ^ 2 + y ^ 2) := by
  rw [Complex.inv_def, div_eq_mul_inv]
  congr <;> simp [conj_ofReal, normSq] <;> ring

lemma sq_add_sq_ne_zero (hy : y ≠ 0) : x ^ 2 + y ^ 2 ≠ 0 := by
  linarith [sq_nonneg x, sq_pos_iff.mpr hy]

lemma continuous_self_div_sq_add_sq (hy : y ≠ 0) :
    Continuous fun x => x / (x ^ 2 + y ^ 2) :=
  continuous_id.div (continuous_id.pow 2 |>.add continuous_const) (fun _ => sq_add_sq_ne_zero hy)

lemma integral_self_div_sq_add_sq (hy : y ≠ 0) :
    ∫ x in x₁..x₂, x / (x ^ 2 + y ^ 2) =
    Real.log (x₂ ^ 2 + y ^ 2) / 2 - Real.log (x₁ ^ 2 + y ^ 2) / 2 := by
  let f (x : ℝ) : ℝ := Real.log (x ^ 2 + y ^ 2) / 2
  have e1 {x} := HasDerivAt.add_const (y ^ 2) (by simpa using hasDerivAt_pow 2 x)
  have e2 {x} : HasDerivAt f (x / (x ^ 2 + y ^ 2)) x := by
    convert! (e1.log (sq_add_sq_ne_zero hy)).div_const 2 using 1
    field_simp
  have e3 : deriv f = fun x => x / (x ^ 2 + y ^ 2) := funext (fun _ => e2.deriv)
  have e4 : Continuous (deriv f) := by simpa only [e3] using continuous_self_div_sq_add_sq hy
  simp_rw [← e2.deriv]
  exact integral_deriv_eq_sub (fun _ _ => e2.differentiableAt) (e4.intervalIntegrable _ _)

lemma integral_const_div_sq_add_sq (hy : y ≠ 0) :
    ∫ x in x₁..x₂, y / (x ^ 2 + y ^ 2) = Real.arctan (x₂ / y) - Real.arctan (x₁ / y) := by
  nth_rewrite 1 [← div_mul_cancel₀ x₁ hy, ← div_mul_cancel₀ x₂ hy]
  simp_rw [← mul_integral_comp_mul_right, ← intervalIntegral.integral_const_mul,
    ← integral_one_div_one_add_sq]
  exact integral_congr fun x _ => by
    field_simp
    ring

lemma integral_const_div_self_add_im (hy : y ≠ 0) :
    ∫ x : ℝ in x₁..x₂, A / (x + y * I) =
    A * (Real.log (x₂ ^ 2 + y ^ 2) / 2 - Real.log (x₁ ^ 2 + y ^ 2) / 2) -
    A * I * (Real.arctan (x₂ / y) - Real.arctan (x₁ / y)) := by
  have e1 {x : ℝ} : A / (x + y * I) = A * x / (x ^ 2 + y ^ 2) - A * I * y / (x ^ 2 + y ^ 2) := by
    ring_nf
    simp_rw [inv_re_add_im]
    ring
  have e2 : IntervalIntegrable (fun x ↦ A * x / (x ^ 2 + y ^ 2)) volume x₁ x₂ := by
    apply Continuous.intervalIntegrable
    simp_rw [mul_div_assoc]
    norm_cast
    exact continuous_const.mul (continuous_ofReal.comp (continuous_self_div_sq_add_sq hy))
  have e3 : IntervalIntegrable (fun x ↦ A * I * y / (x ^ 2 + y ^ 2)) volume x₁ x₂ := by
    apply Continuous.intervalIntegrable
    refine continuous_const.div (by fun_prop) (fun x => ?_)
    norm_cast
    exact sq_add_sq_ne_zero hy
  simp_rw [integral_congr (fun _ _ => e1), integral_sub e2 e3, mul_div_assoc]
  norm_cast
  simp_rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal,
    integral_self_div_sq_add_sq hy, integral_const_div_sq_add_sq hy]

lemma integral_const_div_re_add_self (hx : x ≠ 0) :
    ∫ y : ℝ in y₁..y₂, A / (x + y * I) =
    A / I * (Real.log (y₂ ^ 2 + (-x) ^ 2) / 2 - Real.log (y₁ ^ 2 + (-x) ^ 2) / 2) -
    A / I * I * (Real.arctan (y₂ / -x) - Real.arctan (y₁ / -x)) := by
  have l1 {y : ℝ} : A / (x + y * I) = A / I / (y + ↑(-x) * I) := by
    have e1 : x + y * I ≠ 0 := by
      contrapose! hx
      simpa using congr_arg re hx
    have e2 : y + I * ↑(-x) ≠ 0 := by
      contrapose! hx
      simpa using congr_arg im hx
    field_simp [*]
    push_cast
    ring_nf
    simp
  have l2 : -x ≠ 0 := by rwa [neg_ne_zero]
  simp_rw [l1, integral_const_div_self_add_im l2]

lemma ResidueTheoremAtOrigin' {z w c : ℂ}
    (h1 : z.re < 0) (h2 : z.im < 0) (h3 : 0 < w.re) (h4 : 0 < w.im) :
    RectangleIntegral (fun s => c / s) z w = 2 * I * π * c := by
  simp only [RectangleIntegral, HIntegral, VIntegral, smul_eq_mul]
  rw [integral_const_div_re_add_self h1.ne, integral_const_div_re_add_self h3.ne.symm]
  rw [integral_const_div_self_add_im h2.ne, integral_const_div_self_add_im h4.ne.symm]
  have l1 : z.im * w.re⁻¹ = (w.re * z.im⁻¹)⁻¹ := by group
  have l3 := arctan_inv_of_neg <| mul_neg_of_pos_of_neg h3 <| inv_lt_zero.mpr h2
  have l4 : w.im * z.re⁻¹ = (z.re * w.im⁻¹)⁻¹ := by group
  have l6 := arctan_inv_of_neg <| mul_neg_of_neg_of_pos h1 <| inv_pos.mpr h4
  have r1 : z.im * z.re⁻¹ = (z.re * z.im⁻¹)⁻¹ := by group
  have r3 := arctan_inv_of_pos <| mul_pos_of_neg_of_neg h1 <| inv_lt_zero.mpr h2
  have r4 : w.im * w.re⁻¹ = (w.re * w.im⁻¹)⁻¹ := by group
  have r6 := arctan_inv_of_pos <| mul_pos h3 <| inv_pos.mpr h4
  ring_nf
  simp only [one_div, inv_I, mul_neg, neg_mul, I_sq, neg_neg, arctan_neg, ofReal_neg,
    sub_neg_eq_add]
  rw [l1, l3, l4, l6, r1, r3, r4, r6]
  ring_nf
  simp only [I_sq, ofReal_sub, ofReal_mul, ofReal_ofNat, ofReal_div, ofReal_neg, ofReal_one]
  ring_nf

theorem ResidueTheoremInRectangle
    (zRe_le_wRe : z.re ≤ w.re) (zIm_le_wIm : z.im ≤ w.im)
    (pInRectInterior : Rectangle z w ∈ 𝓝 p) :
    RectangleIntegral' (fun s => c / (s - p)) z w = c := by
  simp only [rectangle_mem_nhds_iff, uIoo_of_le zRe_le_wRe, uIoo_of_le zIm_le_wIm,
    mem_reProdIm, mem_Ioo] at pInRectInterior
  rw [RectangleIntegral.translate', RectangleIntegral']
  have : 1 / (2 * ↑π * I) * (2 * I * ↑π * c) = c := by
    field_simp
  rwa [ResidueTheoremAtOrigin']
  all_goals simp [*]

lemma ResidueTheoremAtOrigin :
    RectangleIntegral' (fun s ↦ 1 / s) (-1 - I) (1 + I) = 1 := by
  rw [RectangleIntegral', ResidueTheoremAtOrigin']
  all_goals simp [field]

lemma ResidueTheoremOnRectangleWithSimplePole {f g : ℂ → ℂ} {z w p A : ℂ}
    (zRe_le_wRe : z.re ≤ w.re) (zIm_le_wIm : z.im ≤ w.im)
    (pInRectInterior : Rectangle z w ∈ 𝓝 p) (gHolo : HolomorphicOn g (Rectangle z w))
    (principalPart : Set.EqOn (f - fun s ↦ A / (s - p)) g (Rectangle z w \ {p})) :
    RectangleIntegral' f z w = A := by
  have principalPart' : Set.EqOn f (g + (fun s ↦ A / (s - p))) (Rectangle z w \ {p}) :=
    fun s hs => by rw [Pi.add_apply, ← principalPart hs, Pi.sub_apply, sub_add_cancel]
  have : Set.EqOn f (g + (fun s ↦ A / (s - p))) (RectangleBorder z w) :=
    principalPart'.mono <| Set.subset_sdiff.mpr
      ⟨rectangleBorder_subset_rectangle z w,
        disjoint_singleton_right.mpr
          (not_mem_rectangleBorder_of_rectangle_mem_nhds pInRectInterior)⟩
  rw [RectangleIntegral'_congr this]
  have t1 : RectangleBorderIntegrable g z w :=
    gHolo.rectangleBorderIntegrable
  have t2 : HolomorphicOn (fun s ↦ A / (s - p)) (Rectangle z w \ {p}) := by
    apply DifferentiableOn.mono (t := {p}ᶜ)
    · apply DifferentiableOn.div
      · exact differentiableOn_const _
      · exact DifferentiableOn.sub differentiableOn_id (differentiableOn_const _)
      · exact fun x hx => by
          rw [sub_ne_zero]
          exact hx
    · rintro s ⟨_, hs⟩
      exact hs
  have t3 : RectangleBorderIntegrable (fun s ↦ A / (s - p)) z w :=
    HolomorphicOn.rectangleBorderIntegrable' t2 pInRectInterior
  rw [RectangleIntegral', RectangleBorderIntegrable.add t1 t3, smul_add]
  rw [gHolo.vanishesOnRectangle (by rfl), smul_zero, zero_add]
  exact ResidueTheoremInRectangle zRe_le_wRe zIm_le_wIm pInRectInterior

lemma IsBigO_to_BddAbove {f : ℂ → ℂ} {p : ℂ}
    (f_near_p : f =O[𝓝[≠] p] (1 : ℂ → ℂ)) :
    ∃ U ∈ 𝓝 p, BddAbove (norm ∘ f '' (U \ {p})) := by
  simp only [isBigO_iff, Pi.one_apply, one_mem, CStarRing.norm_of_mem_unitary, mul_one] at f_near_p
  obtain ⟨c, hc⟩ := f_near_p
  dsimp [Filter.Eventually, nhdsWithin] at hc
  rw [mem_inf_principal'] at hc
  obtain ⟨U, hU, ⟨U_is_open, p_in_U⟩⟩ := mem_nhds_iff.mp hc
  use U
  constructor
  · exact IsOpen.mem_nhds U_is_open p_in_U
  · refine bddAbove_def.mpr ?_
    use c
    intro y hy
    simp only [Function.comp_apply, mem_image, Set.mem_sdiff, mem_singleton_iff] at hy
    obtain ⟨x, ⟨x_in_U, x_not_p⟩, fxy⟩ := hy
    rw [← fxy]
    simpa [x_not_p] using hU x_in_U

theorem BddAbove_on_rectangle_of_bdd_near {z w p : ℂ} {f : ℂ → ℂ}
    (f_cont : ContinuousOn f (Rectangle z w \ {p}))
    (f_near_p : f =O[𝓝[≠] p] (1 : ℂ → ℂ)) :
    BddAbove (norm ∘ f '' (Rectangle z w \ {p})) := by
  obtain ⟨V, V_in_nhds, V_prop⟩ := IsBigO_to_BddAbove f_near_p
  rw [mem_nhds_iff] at V_in_nhds
  obtain ⟨W, W_subset, W_open, p_in_W⟩ := V_in_nhds
  set U := Rectangle z w
  have : U \ {p} = (U \ W) ∪ ((U ∩ W) \ {p}) := by
    ext x
    simp only [Set.mem_sdiff, mem_singleton_iff, mem_union, mem_inter_iff]
    constructor
    · intro ⟨xu, x_not_p⟩
      tauto
    · intro h
      rcases h with ⟨h1, h2⟩ | ⟨⟨h1, h2⟩, h3⟩
      · refine ⟨h1, ?_⟩
        intro h
        rw [← h] at p_in_W
        exact h2 p_in_W
      · tauto
  rw [this, image_union]
  apply BddAbove.union
  · apply IsCompact.bddAbove_image
    · apply IsCompact.diff _ W_open
      exact IsCompact.reProdIm isCompact_uIcc isCompact_uIcc
    · apply f_cont.norm.mono
      apply Set.sdiff_subset_sdiff_right
      simpa
  · exact V_prop.mono
      (image_mono <| Set.sdiff_subset_sdiff_left <| subset_trans inter_subset_right W_subset)

theorem ResidueTheoremOnRectangleWithSimplePole' {f : ℂ → ℂ} {z w p A : ℂ}
    (zRe_le_wRe : z.re ≤ w.re) (zIm_le_wIm : z.im ≤ w.im)
    (pInRectInterior : Rectangle z w ∈ 𝓝 p) (fHolo : HolomorphicOn f (Rectangle z w \ {p}))
    (near_p : (f - (fun s ↦ A / (s - p))) =O[𝓝[≠] p] (1 : ℂ → ℂ)) :
    RectangleIntegral' f z w = A := by
  set g := f - (fun s ↦ A / (s - p))
  have gHolo : HolomorphicOn g (Rectangle z w \ {p}) := by
    apply DifferentiableOn.sub fHolo
    intro s hs
    have : s - p ≠ 0 := sub_ne_zero.mpr hs.2
    exact  DifferentiableWithinAt.div (by fun_prop) (by fun_prop) this
  have := BddAbove_on_rectangle_of_bdd_near gHolo.continuousOn near_p
  obtain ⟨h, ⟨hHolo, hEq⟩⟩ := existsDifferentiableOn_of_bddAbove pInRectInterior gHolo this
  exact ResidueTheoremOnRectangleWithSimplePole zRe_le_wRe zIm_le_wIm pInRectInterior hHolo hEq

def HasSimplePolesOn (f : ℂ → ℂ) (s : Set ℂ) : Prop :=
  ∀ z ∈ s, (-1 : ℤ) ≤ meromorphicOrderAt f z

lemma HasSimplePolesOn.mono {f : ℂ → ℂ} {s t : Set ℂ}
    (h : HasSimplePolesOn f t) (hst : s ⊆ t) : HasSimplePolesOn f s := by
  intro z hz
  exact h z (hst hz)

noncomputable def residue (f : ℂ → ℂ) (z₀ : ℂ) : ℂ :=
  Filter.limUnder (nhdsWithin z₀ {z₀}ᶜ) (fun z ↦ (z - z₀) * f z)

noncomputable def sumResiduesIn (f : ℂ → ℂ) (S : Set ℂ) : ℂ :=
  ∑' z : S, residue f z

lemma residue_eq_of_tendsto {f : ℂ → ℂ} {p c : ℂ}
    (h : Filter.Tendsto (fun z ↦ (z - p) * f z) (nhdsWithin p {p}ᶜ) (nhds c)) :
    residue f p = c := by
  unfold residue
  exact h.limUnder_eq

lemma residue_analyticAt_eq_zero {f : ℂ → ℂ} {p : ℂ} (hf : AnalyticAt ℂ f p) :
    residue f p = 0 := by
  apply residue_eq_of_tendsto
  have hsub : Filter.Tendsto (fun z : ℂ ↦ z - p) (nhdsWithin p {p}ᶜ) (nhds 0) :=
    tendsto_sub_nhds_zero_iff.mpr (tendsto_id.mono_left nhdsWithin_le_nhds)
  have hf' : Filter.Tendsto f (nhdsWithin p {p}ᶜ) (nhds (f p)) :=
    hf.continuousAt.continuousWithinAt.tendsto
  simpa using hsub.mul hf'

lemma simplePole_sub_residue_isBigO_one {f : ℂ → ℂ} {p : ℂ}
    (hf : MeromorphicAt f p) (hord : meromorphicOrderAt f p = (-1 : ℤ)) :
    (f - (fun z ↦ residue f p / (z - p))) =O[nhdsWithin p {p}ᶜ] (1 : ℂ → ℂ) := by
  obtain ⟨g, hg_analytic, hg_ne, hg_eq⟩ := (meromorphicOrderAt_eq_int_iff hf).1 hord
  have hres : residue f p = g p :=
    residue_eq_of_tendsto (hg_analytic.continuousAt.continuousWithinAt.tendsto.congr'
      (show (fun z ↦ (z - p) * f z) =ᶠ[nhdsWithin p {p}ᶜ] g from by
        filter_upwards [hg_eq, self_mem_nhdsWithin] with z hz hz_ne
        simp [hz, sub_ne_zero.mpr hz_ne]).symm)
  have hdslope : (fun z ↦ (z - p)⁻¹ * (g z - g p)) =O[nhdsWithin p {p}ᶜ] (1 : ℂ → ℂ) := by
    have hcont : ContinuousAt (dslope g p) p :=
      continuousAt_dslope_same.2 hg_analytic.differentiableAt
    have hbig : dslope g p =O[nhds p] (1 : ℂ → ℂ) :=
      hcont.norm.isBoundedUnder_le.isBigO_one ℂ
    have hbig_ne : dslope g p =O[nhdsWithin p {p}ᶜ] (1 : ℂ → ℂ) :=
      IsBigO.mono hbig inf_le_left
    simpa [slope] using! hbig_ne.congr' (dslope_eventuallyEq_slope_nhdsNE (f := g) (a := p)) .rfl
  refine hdslope.congr' ?_ .rfl
  filter_upwards [hg_eq, self_mem_nhdsWithin] with z hz hz_ne
  simp [hz, hres, div_eq_mul_inv, sub_eq_add_neg]; ring

private lemma intervalIntegral_congr_ae_of_codiscreteWithin_along_path_bv188
    {f g : ℂ → ℂ} {R : Set ℂ}
    (heq : {s : ℂ | f s = g s} ∈ Filter.codiscreteWithin R)
    {a b : ℝ} {p : ℝ → ℂ}
    (hp_an : AnalyticOnNhd ℝ p (Set.uIcc a b))
    (hp_nonconst : ∀ x ∈ Set.uIcc a b, ¬Filter.EventuallyConst p (nhds x))
    (hp_maps : Set.MapsTo p (Set.uIcc a b) R) :
    ∫ x in a..b, f (p x) = ∫ x in a..b, g (p x) := by
  refine intervalIntegral.integral_congr_ae_restrict (μ := volume) ?_
  apply ae_restrict_le_codiscreteWithin measurableSet_uIoc
  change {x : ℝ | f (p x) = g (p x)} ∈ Filter.codiscreteWithin (Set.uIoc a b)
  simpa [Set.preimage] using Filter.codiscreteWithin_mono Set.uIoc_subset_uIcc
    (hp_an.preimage_mem_codiscreteWithin hp_nonconst
      (Filter.codiscreteWithin_mono
        (by intro s hs; rcases hs with ⟨x, hx, rfl⟩; exact hp_maps hx) heq))

private lemma meromorphicOrderAt_eq_neg_one_of_simplePole_bv188
    {f : ℂ → ℂ} {U : Set ℂ} {p : ℂ}
    (hpU : p ∈ U)
    (hf_simple : HasSimplePolesOn f U)
    (hpneg : meromorphicOrderAt f p < 0) :
    meromorphicOrderAt f p = (-1 : ℤ) := by
  lift meromorphicOrderAt f p to ℤ using hpneg.ne_top with n hn
  have hsimple : (-1 : ℤ) ≤ n := WithTop.coe_le_coe.mp (hn ▸ hf_simple p hpU)
  have hneg : n < 0 := by exact_mod_cast hpneg
  have hn1 : n = -1 := by omega
  simp [hn1]

private lemma residue_toMeromorphicNFOn_eq_residue_bv188
    {f : ℂ → ℂ} {U : Set ℂ} {p : ℂ}
    (hpU : p ∈ U)
    (hf_mero : MeromorphicOn f U)
    (hf_simple : HasSimplePolesOn f U)
    (hpneg : meromorphicOrderAt f p < 0) :
    residue (toMeromorphicNFOn f U) p = residue f p := by
  have hmero : MeromorphicAt f p := hf_mero p hpU
  have h_exists : ∃ c, Filter.Tendsto (fun z : ℂ ↦ (z - p) * f z) (nhdsWithin p ({p}ᶜ)) (nhds c) := by
    have hmul_mero : MeromorphicAt (fun z : ℂ ↦ (z - p) * f z) p :=
      (by fun_prop : MeromorphicAt (fun z : ℂ ↦ z - p) p).mul hmero
    have hmul_nonneg : 0 ≤ meromorphicOrderAt (fun z : ℂ ↦ (z - p) * f z) p := by
      change 0 ≤ meromorphicOrderAt ((fun z ↦ z - p) * f) p
      rw [meromorphicOrderAt_mul (by fun_prop : MeromorphicAt (fun z : ℂ ↦ z - p) p) hmero,
        meromorphicOrderAt_id_sub_const,
        meromorphicOrderAt_eq_neg_one_of_simplePole_bv188 hpU hf_simple hpneg]
      norm_num
    exact tendsto_nhds_of_meromorphicOrderAt_nonneg hmul_mero hmul_nonneg
  have h_tendsto : Filter.Tendsto (fun z : ℂ ↦ (z - p) * f z) (nhdsWithin p ({p}ᶜ)) (nhds (residue f p)) := by
    simpa [residue] using tendsto_nhds_limUnder h_exists
  have h_eq :
      (fun z ↦ (z - p) * toMeromorphicNFOn f U z) =ᶠ[nhdsWithin p ({p}ᶜ)]
        (fun z ↦ (z - p) * f z) := by
    filter_upwards [hf_mero.toMeromorphicNFOn_eq_self_on_nhdsNE hpU] with z hz
    simp [hz]
  exact residue_eq_of_tendsto
    (h_tendsto.congr' h_eq.symm)

private lemma horizontalPath_not_eventuallyConst_bv188 (h : ℝ) (x : ℝ) :
    ¬Filter.EventuallyConst (fun r : ℝ ↦ (r : ℂ) + (h : ℂ) * Complex.I) (nhds x) := by
  intro hc
  obtain ⟨c, hc⟩ := Filter.eventuallyConst_iff_exists_eventuallyEq.1 hc
  have hpath : HasDerivAt (fun r : ℝ ↦ (r : ℂ) + (h : ℂ) * Complex.I) 1 x := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).add_const ((h : ℂ) * Complex.I)
  have hconst : HasDerivAt (fun r : ℝ ↦ (r : ℂ) + (h : ℂ) * Complex.I) 0 x :=
    (hasDerivAt_const x c).congr_of_eventuallyEq hc
  exact one_ne_zero (hpath.unique hconst)

lemma verticalPath_not_eventuallyConst (r : ℝ) (x : ℝ) :
    ¬Filter.EventuallyConst (fun y : ℝ ↦ (r : ℂ) + (y : ℂ) * Complex.I) (nhds x) := by
  intro hc
  obtain ⟨c, hc⟩ := Filter.eventuallyConst_iff_exists_eventuallyEq.1 hc
  have hpath : HasDerivAt (fun y : ℝ ↦ (r : ℂ) + (y : ℂ) * Complex.I) Complex.I x := by
    simpa using ((Complex.ofRealCLM.hasDerivAt (x := x)).mul_const Complex.I).const_add (r : ℂ)
  have hconst : HasDerivAt (fun y : ℝ ↦ (r : ℂ) + (y : ℂ) * Complex.I) 0 x :=
    (hasDerivAt_const x c).congr_of_eventuallyEq hc
  exact Complex.I_ne_zero (hpath.unique hconst)

private lemma HIntegral_congr_codiscreteWithin_bv188 {f g : ℂ → ℂ} {R : Set ℂ} {a b c : ℝ}
    (h_eq : {s : ℂ | f s = g s} ∈ Filter.codiscreteWithin R)
    (hmaps : ∀ x ∈ Set.uIcc a b, (↑x + ↑c * Complex.I) ∈ R) :
    HIntegral f a b c = HIntegral g a b c := by
  unfold HIntegral
  exact intervalIntegral_congr_ae_of_codiscreteWithin_along_path_bv188 h_eq
    (by intro x _; exact (Complex.ofRealCLM.analyticAt x).add analyticAt_const)
    (fun x _ ↦ horizontalPath_not_eventuallyConst_bv188 c x) hmaps

private lemma VIntegral_congr_codiscreteWithin_bv188 {f g : ℂ → ℂ} {R : Set ℂ} {c a b : ℝ}
    (h_eq : {s : ℂ | f s = g s} ∈ Filter.codiscreteWithin R)
    (hmaps : ∀ y ∈ Set.uIcc a b, (↑c + ↑y * Complex.I) ∈ R) :
    VIntegral f c a b = VIntegral g c a b := by
  unfold VIntegral; simp only [smul_eq_mul]; congr 1
  exact intervalIntegral_congr_ae_of_codiscreteWithin_along_path_bv188 h_eq
    (by intro y _; exact analyticAt_const.add ((Complex.ofRealCLM.analyticAt y).mul analyticAt_const))
    (fun x _ ↦ verticalPath_not_eventuallyConst c x) hmaps

private lemma rectangleIntegral_bv188'_toMeromorphicNFOn_eq {f : ℂ → ℂ} {z w : ℂ}
    (f_mero : MeromorphicOn f (Rectangle z w)) :
    RectangleIntegral' f z w = RectangleIntegral' (toMeromorphicNFOn f (Rectangle z w)) z w := by
  classical
  let R : Set ℂ := Rectangle z w
  let fNF : ℂ → ℂ := toMeromorphicNFOn f R
  have h_eq : {s : ℂ | f s = fNF s} ∈ Filter.codiscreteWithin R := by
    simpa [Filter.EventuallyEq, Filter.Eventually, fNF] using
      (toMeromorphicNFOn_eqOn_codiscrete (f := f) (U := R) f_mero)
  have hbot := HIntegral_congr_codiscreteWithin_bv188 h_eq (by simpa [R] using! mapsTo_rectangle_left_im z w)
  have htop := HIntegral_congr_codiscreteWithin_bv188 h_eq (by simpa [R] using! mapsTo_rectangle_right_im z w)
  have hright := VIntegral_congr_codiscreteWithin_bv188 h_eq (by simpa [R] using! mapsTo_rectangle_right_re z w)
  have hleft := VIntegral_congr_codiscreteWithin_bv188 h_eq (by simpa [R] using! mapsTo_rectangle_left_re z w)
  unfold RectangleIntegral'; congr 1; unfold RectangleIntegral
  rw [hbot, htop, hright, hleft]

private lemma principalPart_meromorphicOn_bv188 {R : Set ℂ} {polesFin : Finset ℂ} {c : ℂ → ℂ} :
    MeromorphicOn (fun s ↦ ∑ p ∈ polesFin, c p / (s - p)) R := by
  intro x _
  refine MeromorphicAt.fun_sum (G := fun p s ↦ c p / (s - p)) ?_
  intro p _
  exact (analyticAt_const.meromorphicAt.div
    ((analyticAt_id.sub analyticAt_const).meromorphicAt))

private lemma sub_principalPart_analyticAt_of_not_mem_poles_bv188
    {f : ℂ → ℂ} {polesFin : Finset ℂ} {x : ℂ}
    (h_nf : MeromorphicNFAt f x)
    (hxnp : x ∉ polesFin)
    (hxneg : 0 ≤ meromorphicOrderAt f x) :
    AnalyticAt ℂ (f - fun s ↦ ∑ p ∈ polesFin, residue f p / (s - p)) x := by
  have h_f_analytic : AnalyticAt ℂ f x :=
    h_nf.meromorphicOrderAt_nonneg_iff_analyticAt.1 hxneg
  have h_principal_analytic : AnalyticAt ℂ (fun s ↦ ∑ p ∈ polesFin, residue f p / (s - p)) x := by
    refine Finset.analyticAt_fun_sum polesFin ?_
    intro p hp
    have hxp : x ≠ p := by
      intro heq
      subst heq
      exact hxnp hp
    have : AnalyticAt ℂ (fun z : ℂ ↦ residue f p / (z - p)) x := by
      fun_prop (disch := exact sub_ne_zero.mpr hxp)
    simpa using this
  exact h_f_analytic.sub h_principal_analytic

private lemma meromorphicOrderAt_sub_principalPart_nonneg_bv188
    {f : ℂ → ℂ} {polesFin : Finset ℂ} {p : ℂ}
    (hpFin : p ∈ polesFin)
    (h_mero : MeromorphicAt f p)
    (h_ord : meromorphicOrderAt f p = -1) :
    0 ≤ meromorphicOrderAt (f - fun s ↦ ∑ q ∈ polesFin, residue f q / (s - q)) p := by
  have hcore : (f - fun z ↦ residue f p / (z - p)) =O[nhdsWithin p ({p}ᶜ)] (1 : ℂ → ℂ) := by
    exact simplePole_sub_residue_isBigO_one h_mero h_ord
  let rest : ℂ → ℂ := fun z ↦ ∑ q ∈ polesFin.erase p, residue f q / (z - q)
  have hrest_cont : ContinuousAt rest p := by
    dsimp [rest]
    refine tendsto_finsetSum _ (fun q hq ↦ ?_)
    have hpq : p - q ≠ 0 := sub_ne_zero.mpr (Finset.mem_erase.mp hq).1.symm
    have h_cont : ContinuousAt (fun z : ℂ ↦ residue f q / (z - q)) p := by
      fun_prop (disch := exact hpq)
    exact h_cont
  have hrest : rest =O[nhdsWithin p ({p}ᶜ)] (1 : ℂ → ℂ) := by
    have hbig : rest =O[nhds p] (1 : ℂ → ℂ) :=
      hrest_cont.norm.isBoundedUnder_le.isBigO_one ℂ
    exact IsBigO.mono hbig inf_le_left
  have hraw_big : (f - fun s ↦ ∑ q ∈ polesFin, residue f q / (s - q)) =O[nhdsWithin p ({p}ᶜ)] (1 : ℂ → ℂ) := by
    have htmp : (fun z : ℂ ↦ (f z - residue f p / (z - p)) - rest z) =O[nhdsWithin p ({p}ᶜ)] (1 : ℂ → ℂ) :=
      hcore.sub hrest
    have hdecomp : (f - fun s ↦ ∑ q ∈ polesFin, residue f q / (s - q)) =
        (fun z : ℂ ↦ (f z - residue f p / (z - p)) - rest z) := by
      funext z
      dsimp [rest]
      rw [← Finset.add_sum_erase (s := polesFin) (f := fun q ↦ residue f q / (z - q)) hpFin]
      simp [sub_eq_add_neg, add_assoc, add_comm]
    simpa [hdecomp, rest] using htmp
  by_contra hneg
  have hnorm : Filter.Tendsto (fun z : ℂ ↦ ‖(f - fun s ↦ ∑ q ∈ polesFin, residue f q / (s - q)) z‖) (nhdsWithin p ({p}ᶜ)) Filter.atTop := by
    rw [tendsto_norm_atTop_iff_cobounded]
    exact tendsto_cobounded_of_meromorphicOrderAt_neg (not_le.mp hneg)
  exact (Filter.not_isBoundedUnder_of_tendsto_atTop hnorm) hraw_big.isBoundedUnder_le

private lemma holoPart_holomorphicOn_bv188 {f : ℂ → ℂ} {z w : ℂ}
    (f_mero : MeromorphicOn f (Rectangle z w))
    (f_simple_poles : HasSimplePolesOn f (Rectangle z w))
    (f_poles_finite : (Rectangle z w ∩ {z | meromorphicOrderAt f z < 0}).Finite) :
    HolomorphicOn (toMeromorphicNFOn (toMeromorphicNFOn f (Rectangle z w) -
      fun s ↦ ∑ p ∈ f_poles_finite.toFinset, residue (toMeromorphicNFOn f (Rectangle z w)) p / (s - p)) (Rectangle z w)) (Rectangle z w) := by
  classical
  let R := Rectangle z w
  let poles := R ∩ {u | meromorphicOrderAt f u < 0}
  let polesFin := f_poles_finite.toFinset
  let fNF := toMeromorphicNFOn f R
  let principalPart := fun s ↦ ∑ p ∈ polesFin, residue fNF p / (s - p)
  let holoPart := toMeromorphicNFOn (fNF - principalPart) R
  have h_fNF_mero : MeromorphicOn fNF R := by
    simpa [fNF] using
      (meromorphicNFOn_toMeromorphicNFOn (f := f) (U := R)).meromorphicOn
  have h_principalPart_mero : MeromorphicOn principalPart R := principalPart_meromorphicOn_bv188
  have h_raw_mero : MeromorphicOn (fNF - principalPart) R := h_fNF_mero.sub h_principalPart_mero
  intro x hx
  have h_raw_nonneg : 0 ≤ meromorphicOrderAt (fNF - principalPart) x := by
    by_cases hxp : x ∈ poles
    · have hpFin : x ∈ polesFin := by simpa [polesFin, poles] using hxp
      have hord : meromorphicOrderAt f x = (-1 : ℤ) :=
        meromorphicOrderAt_eq_neg_one_of_simplePole_bv188 hxp.1 f_simple_poles hxp.2
      have hordNF : meromorphicOrderAt fNF x = (-1 : ℤ) := by
        rw [show meromorphicOrderAt fNF x = meromorphicOrderAt f x by
          simpa [fNF] using
            (meromorphicOrderAt_toMeromorphicNFOn (f := f) (U := R) f_mero hxp.1)]
        exact hord
      exact meromorphicOrderAt_sub_principalPart_nonneg_bv188 hpFin (h_fNF_mero x hxp.1) hordNF
    · have hxnp : x ∉ polesFin := by
        intro h
        exact hxp (by simpa [polesFin, poles] using h)
      have h_fNF_nonneg : 0 ≤ meromorphicOrderAt fNF x := by
        rw [show meromorphicOrderAt fNF x = meromorphicOrderAt f x by
          simpa [fNF] using
            (meromorphicOrderAt_toMeromorphicNFOn (f := f) (U := R) f_mero hx)]
        exact le_of_not_gt fun hxneg => hxp ⟨hx, hxneg⟩
      have h_fNF_nf : MeromorphicNFAt fNF x := by
        simpa [fNF] using
          (meromorphicNFOn_toMeromorphicNFOn (f := f) (U := R) hx)
      exact (sub_principalPart_analyticAt_of_not_mem_poles_bv188 h_fNF_nf hxnp h_fNF_nonneg).meromorphicOrderAt_nonneg
  have h_nf : MeromorphicNFAt holoPart x := by
    simpa [holoPart] using
      (meromorphicNFOn_toMeromorphicNFOn (f := fNF - principalPart) (U := R) hx)
  have h_ord :
      meromorphicOrderAt holoPart x = meromorphicOrderAt (fNF - principalPart) x := by
    simpa [holoPart] using
      (meromorphicOrderAt_toMeromorphicNFOn (f := fNF - principalPart) (U := R) h_raw_mero hx)
  exact (h_nf.meromorphicOrderAt_nonneg_iff_analyticAt.1 (h_ord.symm ▸ h_raw_nonneg)).differentiableAt.differentiableWithinAt

private lemma principalPart_borderIntegrable_bv188 {f : ℂ → ℂ} {z w : ℂ}
    (f_no_poles_boundary : Disjoint (RectangleBorder z w) {z | meromorphicOrderAt f z < 0})
    (f_poles_finite : (Rectangle z w ∩ {z | meromorphicOrderAt f z < 0}).Finite) :
    RectangleBorderIntegrable (fun s ↦ ∑ p ∈ f_poles_finite.toFinset, residue (toMeromorphicNFOn f (Rectangle z w)) p / (s - p)) z w := by
  classical
  let R := Rectangle z w
  let poles := R ∩ {u | meromorphicOrderAt f u < 0}
  let polesFin := f_poles_finite.toFinset
  let fNF := toMeromorphicNFOn f R
  let principalPart := fun s ↦ ∑ p ∈ polesFin, residue fNF p / (s - p)
  refine ContinuousOn.rectangleBorder_integrable ?_
  refine continuousOn_finsetSum _ ?_
  intro p hp s hs
  have hsp : s ≠ p := fun hsp => Set.disjoint_right.mp f_no_poles_boundary
    ((by simpa [polesFin, poles] using hp : p ∈ poles).2) (hsp ▸ hs)
  have : ContinuousAt (fun z : ℂ ↦ residue fNF p / (z - p)) s := by
    fun_prop (disch := exact sub_ne_zero.mpr hsp)
  exact this.continuousWithinAt

private lemma rectangle_mem_nhds_of_interior_bv188 {z w p : ℂ}
    (zRe_le_wRe : z.re ≤ w.re) (zIm_le_wIm : z.im ≤ w.im)
    (hpR : p ∈ Rectangle z w) (hpnot : p ∉ RectangleBorder z w) :
    Rectangle z w ∈ nhds p := by
  rw [mem_Rect zRe_le_wRe zIm_le_wIm] at hpR
  have hp_re_left : z.re < p.re :=
    lt_of_le_of_ne hpR.1 fun hEq => hpnot
      (by simp [RectangleBorder, hEq, hpR.2.2.1, hpR.2.2.2, zIm_le_wIm, mem_reProdIm])
  have hp_re_right : p.re < w.re :=
    lt_of_le_of_ne hpR.2.1 fun hEq => hpnot
      (by simp [RectangleBorder, hEq, hpR.2.2.1, hpR.2.2.2, zIm_le_wIm, mem_reProdIm])
  have hp_im_left : z.im < p.im :=
    lt_of_le_of_ne hpR.2.2.1 fun hEq => hpnot
      (by simp [RectangleBorder, hEq, hpR.1, hpR.2.1, zRe_le_wRe, mem_reProdIm])
  have hp_im_right : p.im < w.im :=
    lt_of_le_of_ne hpR.2.2.2 fun hEq => hpnot
      (by simp [RectangleBorder, hEq, hpR.1, hpR.2.1, zRe_le_wRe, mem_reProdIm])
  rw [rectangle_mem_nhds_iff, mem_reProdIm, Set.uIoo_of_le zRe_le_wRe, Set.uIoo_of_le zIm_le_wIm]
  exact ⟨⟨hp_re_left, hp_re_right⟩, ⟨hp_im_left, hp_im_right⟩⟩

private lemma sum_div_rectangleBorderIntegrable_bv188 {z w : ℂ} {S : Finset ℂ}
    (hS_disjoint : Disjoint (RectangleBorder z w) S) (c : ℂ → ℂ) :
    RectangleBorderIntegrable (fun s ↦ ∑ p ∈ S, c p / (s - p)) z w := by
  refine ContinuousOn.rectangleBorder_integrable ?_
  refine continuousOn_finsetSum _ ?_
  intro p hp s hs
  have hsp : s ≠ p := fun hsp => Set.disjoint_right.mp hS_disjoint hp (hsp ▸ hs)
  have : ContinuousAt (fun z : ℂ ↦ c p / (z - p)) s := by
    fun_prop (disch := exact sub_ne_zero.mpr hsp)
  exact this.continuousWithinAt

private lemma rectangleIntegral_bv188'_sum_div_sub {z w : ℂ} (zRe_le_wRe : z.re ≤ w.re) (zIm_le_wIm : z.im ≤ w.im)
    {S : Finset ℂ} (hS_subset : (S : Set ℂ) ⊆ Rectangle z w)
    (hS_disjoint : Disjoint (RectangleBorder z w) S)
    (c : ℂ → ℂ) :
    RectangleIntegral' (fun s ↦ ∑ p ∈ S, c p / (s - p)) z w = ∑ p ∈ S, c p := by
  classical
  have h_partial_border : ∀ (S' : Finset ℂ), S' ⊆ S → RectangleBorderIntegrable (fun s ↦ ∑ p ∈ S', c p / (s - p)) z w := by
    intro S' hS'
    exact sum_div_rectangleBorderIntegrable_bv188 (Disjoint.mono_right hS' hS_disjoint) c
  have h_term_integral : ∀ {p : ℂ}, p ∈ S → RectangleIntegral' (fun s ↦ c p / (s - p)) z w = c p :=
    fun {p} hp => ResidueTheoremInRectangle zRe_le_wRe zIm_le_wIm
      (rectangle_mem_nhds_of_interior_bv188 zRe_le_wRe zIm_le_wIm
        (hS_subset hp) (Set.disjoint_right.mp hS_disjoint hp))
  have h_partial_integral :
      ∀ (S' : Finset ℂ), S' ⊆ S →
        RectangleIntegral' (fun s ↦ ∑ p ∈ S', c p / (s - p)) z w =
          ∑ p ∈ S', c p := by
    intro S' hS'
    revert hS'
    refine Finset.induction_on S' ?_ ?_
    · intro _
      simp [RectangleIntegral', RectangleIntegral, HIntegral, VIntegral]
    · intro a S' ha ih hS'
      obtain ⟨haFin, hSsub⟩ := Finset.insert_subset_iff.mp hS'
      have hterm_border :
          RectangleBorderIntegrable (fun s ↦ c a / (s - a)) z w :=
        by simpa using h_partial_border ({a} : Finset ℂ) (Finset.singleton_subset_iff.mpr haFin)
      have hfun :
          (fun s ↦ ∑ p ∈ insert a S', c p / (s - p)) =
            (fun s ↦ c a / (s - a)) +
              (fun s ↦ ∑ p ∈ S', c p / (s - p)) := by
        funext s; simp [Finset.sum_insert, ha]
      have h_add_primed :
          RectangleIntegral' ((fun s ↦ c a / (s - a)) + (fun s ↦ ∑ p ∈ S', c p / (s - p))) z w =
            RectangleIntegral' (fun s ↦ c a / (s - a)) z w +
              RectangleIntegral' (fun s ↦ ∑ p ∈ S', c p / (s - p)) z w := by
        unfold RectangleIntegral'
        rw [RectangleBorderIntegrable.add hterm_border (h_partial_border S' hSsub), smul_add]
      rw [hfun, h_add_primed, h_term_integral haFin, ih hSsub, Finset.sum_insert ha]
  exact h_partial_integral S (by intro p hp; exact hp)

private lemma toMeromorphicNFOn_add_integral_bv188 {f : ℂ → ℂ} {z w : ℂ}
    (f_mero : MeromorphicOn f (Rectangle z w))
    (f_no_poles_boundary : Disjoint (RectangleBorder z w) {z | meromorphicOrderAt f z < 0})
    (f_poles_finite : (Rectangle z w ∩ {z | meromorphicOrderAt f z < 0}).Finite)
    (f_simple_poles : HasSimplePolesOn f (Rectangle z w)) :
    RectangleIntegral' (toMeromorphicNFOn f (Rectangle z w)) z w =
      RectangleIntegral' (toMeromorphicNFOn (toMeromorphicNFOn f (Rectangle z w) -
        fun s ↦ ∑ p ∈ f_poles_finite.toFinset, residue (toMeromorphicNFOn f (Rectangle z w)) p / (s - p)) (Rectangle z w)) z w +
      RectangleIntegral' (fun s ↦ ∑ p ∈ f_poles_finite.toFinset, residue (toMeromorphicNFOn f (Rectangle z w)) p / (s - p)) z w := by
  let R : Set ℂ := Rectangle z w
  let poles : Set ℂ := R ∩ {u | meromorphicOrderAt f u < 0}
  let polesFin : Finset ℂ := f_poles_finite.toFinset
  let fNF : ℂ → ℂ := toMeromorphicNFOn f R
  let principalPart : ℂ → ℂ := fun s ↦ ∑ p ∈ polesFin, residue fNF p / (s - p)
  let holoPart : ℂ → ℂ := toMeromorphicNFOn (fNF - principalPart) R
  have h_holoPart_border : RectangleBorderIntegrable holoPart z w :=
    (holoPart_holomorphicOn_bv188 f_mero f_simple_poles f_poles_finite).rectangleBorderIntegrable
  have h_fNF_eq :
      Set.EqOn fNF (holoPart + principalPart) (RectangleBorder z w) := by
    intro s hs
    have hsR : s ∈ R := rectangleBorder_subset_rectangle z w hs
    have hsnp : s ∉ poles := fun hsp => Set.disjoint_right.mp f_no_poles_boundary hsp.2 hs
    have hraw_analytic : AnalyticAt ℂ (fNF - principalPart) s := by
      have h_fNF_nonneg : 0 ≤ meromorphicOrderAt fNF s := by
        rw [show meromorphicOrderAt fNF s = meromorphicOrderAt f s by
          simpa [fNF] using
            (meromorphicOrderAt_toMeromorphicNFOn (f := f) (U := R) f_mero hsR)]
        exact le_of_not_gt fun hsneg => hsnp ⟨hsR, hsneg⟩
      exact sub_principalPart_analyticAt_of_not_mem_poles_bv188
        (by simpa [fNF] using meromorphicNFOn_toMeromorphicNFOn (f := f) (U := R) hsR)
        (fun h => hsnp (by simpa [polesFin, poles] using h))
        h_fNF_nonneg
    have hs_eq : holoPart s = (fNF - principalPart) s := by
      rw [show holoPart = toMeromorphicNFOn (fNF - principalPart) R by rfl]
      have h_fNF_mero : MeromorphicOn fNF R := by
        simpa [fNF] using (meromorphicNFOn_toMeromorphicNFOn (f := f) (U := R)).meromorphicOn
      have hf_sub_mero : MeromorphicOn (fNF - principalPart) R :=
        h_fNF_mero.sub principalPart_meromorphicOn_bv188
      rw [toMeromorphicNFOn_eq_toMeromorphicNFAt (f := fNF - principalPart) (U := R) hf_sub_mero hsR]
      exact congr_fun (toMeromorphicNFAt_eq_self.2 hraw_analytic.meromorphicNFAt) s
    calc
      fNF s = (fNF - principalPart) s + principalPart s := by simp
      _ = holoPart s + principalPart s := by rw [← hs_eq]
  rw [RectangleIntegral'_congr h_fNF_eq, RectangleIntegral',
    RectangleBorderIntegrable.add h_holoPart_border
      (principalPart_borderIntegrable_bv188 f_no_poles_boundary f_poles_finite), smul_add]

lemma RectangleIntegral'_eq_sumResiduesIn {f : ℂ → ℂ} {z w : ℂ}
    (zRe_le_wRe : z.re ≤ w.re) (zIm_le_wIm : z.im ≤ w.im)
    (f_mero : MeromorphicOn f (Rectangle z w))
    (f_no_poles_boundary : Disjoint (RectangleBorder z w) {z | meromorphicOrderAt f z < 0})
    (f_poles_finite : (Rectangle z w ∩ {z | meromorphicOrderAt f z < 0}).Finite)
    (f_simple_poles : HasSimplePolesOn f (Rectangle z w)) :
    RectangleIntegral' f z w = sumResiduesIn f (Rectangle z w ∩ {z | meromorphicOrderAt f z < 0}) := by
  let R : Set ℂ := Rectangle z w
  let poles : Set ℂ := R ∩ {u | meromorphicOrderAt f u < 0}
  let polesFin : Finset ℂ := f_poles_finite.toFinset
  let fNF : ℂ → ℂ := toMeromorphicNFOn f R
  let principalPart : ℂ → ℂ := fun s ↦ ∑ p ∈ polesFin, residue fNF p / (s - p)
  let holoPart : ℂ → ℂ := toMeromorphicNFOn (fNF - principalPart) R
  have h_residue_congr : sumResiduesIn f poles = sumResiduesIn fNF poles := by
    rw [sumResiduesIn, sumResiduesIn]
    apply tsum_congr
    intro p
    exact (residue_toMeromorphicNFOn_eq_residue_bv188 p.2.1 f_mero f_simple_poles p.2.2).symm
  have h_principalPart_integral : RectangleIntegral' principalPart z w = sumResiduesIn fNF poles := by
    have h_sum : RectangleIntegral' principalPart z w = ∑ p ∈ polesFin, residue fNF p := by
      apply rectangleIntegral_bv188'_sum_div_sub zRe_le_wRe zIm_le_wIm
      · intro p hp
        dsimp [polesFin, poles, R] at hp
        simp only [Finset.mem_coe, Set.Finite.mem_toFinset] at hp
        exact hp.1
      · exact Disjoint.mono_right (by rw [f_poles_finite.coe_toFinset]; exact Set.inter_subset_right) f_no_poles_boundary
    rw [h_sum]
    have h_eq_poles : poles = ↑polesFin := by
      dsimp [poles, polesFin, R]
      exact f_poles_finite.coe_toFinset.symm
    rw [sumResiduesIn, h_eq_poles,
      tsum_fintype (f := fun p : (polesFin : Set ℂ) => residue fNF p),
      ← Finset.sum_coe_sort polesFin]; rfl
  calc
    RectangleIntegral' f z w = RectangleIntegral' fNF z w := rectangleIntegral_bv188'_toMeromorphicNFOn_eq f_mero
    _ = RectangleIntegral' holoPart z w + RectangleIntegral' principalPart z w :=
      toMeromorphicNFOn_add_integral_bv188 f_mero f_no_poles_boundary f_poles_finite f_simple_poles
    _ = 0 + sumResiduesIn fNF poles := by
      rw [h_principalPart_integral]
      rw [RectangleIntegral',
        (holoPart_holomorphicOn_bv188 f_mero f_simple_poles f_poles_finite).vanishesOnRectangle subset_rfl]
      simp
    _ = sumResiduesIn fNF poles := by simp
    _ = sumResiduesIn f poles := h_residue_congr.symm

lemma residue_eq_zero_of_not_pole_of_meromorphicAt {F : ℂ → ℂ} {s : ℂ}
    (hs_mero : MeromorphicAt F s) (hs_not_pole : 0 ≤ meromorphicOrderAt F s) :
    residue F s = 0 := by
  apply residue_eq_of_tendsto
  obtain ⟨c, hc⟩ := tendsto_nhds_of_meromorphicOrderAt_nonneg hs_mero hs_not_pole
  have hsub : Filter.Tendsto (fun z : ℂ ↦ z - s) (nhdsWithin s {s}ᶜ) (nhds 0) :=
    tendsto_sub_nhds_zero_iff.mpr (tendsto_id.mono_left nhdsWithin_le_nhds)
  simpa using hsub.mul hc

lemma sumResiduesIn_inter_eq_of_set_eq {F : ℂ → ℂ} {Rn S2 P : Set ℂ}
    (h_set_eq : Rn ∩ P = S2 ∩ P)
    (h_residue_zero : ∀ s ∈ S2, s ∉ P → residue F s = 0) :
    sumResiduesIn F (Rn ∩ P) = sumResiduesIn F S2 := by
  rw [sumResiduesIn, sumResiduesIn, tsum_subtype, tsum_subtype]
  apply tsum_congr
  intro s
  by_cases hs_S2 : s ∈ S2
  · by_cases hs_pole : s ∈ P
    · have hs_rect_pole : s ∈ Rn ∩ P := h_set_eq.symm ▸ ⟨hs_S2, hs_pole⟩
      simp [hs_S2, hs_rect_pole]
    · have hs_not_rect_pole : s ∉ Rn ∩ P := fun hs => hs_pole hs.2
      have hres0 : residue F s = 0 := h_residue_zero s hs_S2 hs_pole
      simp [hs_S2, hs_not_rect_pole, hres0]
  · have hs_not_rect_pole : s ∉ Rn ∩ P := fun hs => hs_S2 (h_set_eq ▸ hs).1
    simp [hs_S2, hs_not_rect_pole]

end

section

open Filter Set Complex Real

open scoped Topology in
private theorem riemannZetaLogDerivResidueBigO :
    (-(deriv riemannZeta) / riemannZeta - fun z ↦ (z - 1)⁻¹) =O[nhdsWithin 1 {1}ᶜ] (1 : ℂ → ℂ) := by
  have H := log_deriv_riemannZeta_add_inv_sub_bounded.neg_left
  apply H.congr_left
  intro z
  change -(deriv riemannZeta z / riemannZeta z + (z-1)⁻¹) = -deriv riemannZeta z / riemannZeta z - (z-1)⁻¹
  ring

lemma ShiftZeroBound :
    ∃ (C : ℝ), C ≥ 1 ∧
      ∀ (δ : ℝ), δ ∈ Ioo 0 1 →
        -((deriv riemannZeta) (1 + δ) / riemannZeta (1 + δ)).re ≤ 1 / δ + C := by
  have zetaAnalyticOnNhd : AnalyticOnNhd ℂ riemannZeta {(1 : ℂ)}ᶜ := DifferentiableOn.analyticOnNhd
    (fun _ hs => (differentiableAt_riemannZeta hs).differentiableWithinAt) isOpen_compl_singleton
  have oneAddContinuous : Continuous (fun x : ℝ => (1 + (x : ℂ))) :=
    Continuous.add continuous_const continuous_ofReal
  have ShiftZeroBoundNear :
      ∃ (C r : ℝ), r ∈ Ioo 0 1 ∧
        ∀ (δ : ℝ), δ ∈ Ioo 0 r →
          -((deriv riemannZeta) (1 + δ) / riemannZeta (1 + δ)).re ≤ 1 / δ + C := by
    obtain ⟨C, hC⟩ := riemannZetaLogDerivResidueBigO.bound
    rcases Metric.mem_nhdsWithin_iff.mp hC with ⟨ε, εpos, hε⟩
    refine ⟨C, min ε (1 / 2), ⟨?_, fun δ δrange => ?_⟩⟩
    · constructor
      · positivity
      · exact lt_of_le_of_lt (min_le_right ε (1 / 2)) (by norm_num)
    · have δin : ((1 : ℂ) + δ) ∈ Metric.ball 1 ε ∩ {1}ᶜ := by
        simp only [mem_inter_iff, Metric.mem_ball, dist_self_add_left, norm_real, norm_eq_abs,
          mem_compl_iff, mem_singleton_iff, add_eq_left, ofReal_eq_zero, abs_lt]
        exact ⟨⟨by linarith [δrange.1], by linarith [δrange.2, min_le_left ε (1 / 2)]⟩,
          by linarith [δrange.1]⟩
      have reBound := (Complex.re_le_norm _).trans (hε δin)
      simp only [Pi.sub_apply, Pi.div_apply, Pi.neg_apply, add_sub_cancel_left, sub_re, inv_re,
        ofReal_re, normSq_ofReal, div_self_mul_self', Pi.one_apply, norm_one, mul_one,
        tsub_le_iff_right] at reBound
      simp only [one_div, ← Complex.neg_re, ← neg_div, add_comm _ C, reBound]
  obtain ⟨C₀, r, rIn, boundNear⟩ := ShiftZeroBoundNear
  have ShiftZeroBoundCompact :
      ∃ (C : ℝ), ∀ (δ : ℝ), δ ∈ Icc r 1 →
        -((deriv riemannZeta) (1 + δ) / riemannZeta (1 + δ)).re ≤ 1 / δ + C := by
    simp only [← sub_le_iff_le_add', ← Complex.neg_re]
    refine ⟨_, fun δ hδ => le_csSup (IsCompact.bddAbove (isCompact_Icc.image_of_continuousOn ?_))
      (Set.mem_image_of_mem _ hδ)⟩
    refine ContinuousOn.add (Complex.continuous_re.comp_continuousOn
      (ContinuousOn.neg (ContinuousOn.div (ContinuousOn.comp zetaAnalyticOnNhd.deriv.continuousOn
        (by apply fun x hx => oneAddContinuous.continuousOn) ?_)
      (ContinuousOn.comp zetaAnalyticOnNhd.continuousOn
        (by apply fun x hx => oneAddContinuous.continuousOn) ?_)
      (fun x hx => riemannZeta_ne_zero_of_one_lt_re ?_)))) (ContinuousOn.neg
        (ContinuousOn.div continuousOn_const continuousOn_id ?_))
    · simp only [MapsTo, mem_Icc, mem_compl_iff, mem_singleton_iff, add_eq_left,
        ofReal_eq_zero, and_imp]
      exact fun x hx _ => by linarith [rIn.1, hx]
    · simp only [MapsTo, mem_Icc, mem_compl_iff, mem_singleton_iff, add_eq_left,
        ofReal_eq_zero, and_imp]
      exact fun x hx _ => by linarith [rIn.1, hx]
    · simp only [add_re, one_re, ofReal_re, lt_add_iff_pos_right]
      linarith [rIn.1, hx.1]
    · simp only [ne_eq]
      exact fun x hx => by linarith [rIn.1, hx.1]
  obtain ⟨C₁, boundCompact⟩ := ShiftZeroBoundCompact
  refine ⟨1 + max |C₀| |C₁|, ?_, fun δ δrange => ?_⟩
  · simp only [ge_iff_le, le_add_iff_nonneg_right, le_sup_iff, abs_nonneg, or_self]
  · by_cases δ_lt_r : δ < r
    · have δIn : δ ∈ Ioo 0 r := by simp only [mem_Ioo, δrange.1, δ_lt_r, and_self]
      apply le_trans (boundNear δ δIn)
      simp only [one_div, add_le_add_iff_left]
      linarith [le_abs_self C₀, le_max_left |C₀| |C₁|]
    · have δIn : δ ∈ Icc r 1 := by
        simp only [mem_Icc, δrange.2.le, ← not_lt, δ_lt_r, not_false_eq_true, and_self]
      apply le_trans (boundCompact δ δIn)
      simp only [one_div, add_le_add_iff_left]
      linarith [le_abs_self C₁, le_max_right |C₀| |C₁|]

end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

def explicitFormulaIntegrand {N : Nat} [NeZero N]
    (chi : DirichletCharacter Complex N) (x : Nat) (s : Complex) : Complex :=
  logDeriv chi.LFunction s * (-((x : Complex) ^ s / s))

end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

def perronStepWeight (y : Real) : Real :=
  if y < 1 then 0 else if y = 1 then 1 / 2 else 1

def perronKernelIntegrand (y : Real) (s : Complex) : Complex :=
  (y : Complex) ^ s / s

def truncatedPerronKernel (y c T : Real) : Complex :=
  VIntegral' (perronKernelIntegrand y) c (-T) T

@[simp] theorem perronStepWeight_one : perronStepWeight 1 = 1 / 2 := by
  simp [perronStepWeight]

end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

theorem perronKernelIntegrand_eq_exp {y : Real} (hy : 0 < y) (s : Complex) :
    perronKernelIntegrand y s =
      Complex.exp ((Real.log y : Complex) * s) / s := by
  rw [perronKernelIntegrand,
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hy.ne')]
  rw [Complex.ofReal_log hy.le]

theorem holomorphicOn_perronKernelIntegrand {y : Real} (hy : 0 < y) :
    HolomorphicOn (perronKernelIntegrand y) {s : Complex | 0 < s.re} := by
  intro s hs
  have hsne : Ne s 0 := by
    intro hzero
    subst s
    simp at hs
  have hEq :
      perronKernelIntegrand y =
        fun z : Complex => Complex.exp ((Real.log y : Complex) * z) / z := by
    funext z
    exact perronKernelIntegrand_eq_exp hy z
  rw [hEq]
  fun_prop

theorem norm_perronKernelIntegrand {y : Real} (hy : 0 < y) (s : Complex) :
    norm (perronKernelIntegrand y s) = y ^ s.re / norm s := by
  rw [perronKernelIntegrand, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hy]

end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

def twistedMangoldtSequence {N : Nat}
    (chi : DirichletCharacter Complex N) (n : Nat) : Complex :=
  chi n * (ArithmeticFunction.vonMangoldt n : Complex)

def explicitFormulaDirichletTerm {N : Nat}
    (chi : DirichletCharacter Complex N) (x n : Nat) (s : Complex) : Complex :=
  LSeries.term (twistedMangoldtSequence chi) s n *
    ((x : Complex) ^ s / s)

def explicitFormulaVerticalIntegral {N : Nat} [NeZero N]
    (chi : DirichletCharacter Complex N) (x : Nat) (c T : Real) : Complex :=
  VIntegral' (explicitFormulaIntegrand chi x) c (-T) T

end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

def scalarPerronSeriesTerm {N : Nat}
    (chi : DirichletCharacter Complex N) (x : Nat) (c T : Real) (n : Nat) : Complex :=
  if n = 0 then 0 else
    twistedMangoldtSequence chi n *
      truncatedPerronKernel ((x : Real) / (n : Real)) c T

end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

theorem explicitFormulaDirichletTerm_eq_coeff_mul_perronKernel
    {N : Nat} (chi : DirichletCharacter Complex N) (x n : Nat)
    (s : Complex) (hn : Ne n 0) :
    explicitFormulaDirichletTerm chi x n s =
      twistedMangoldtSequence chi n *
        perronKernelIntegrand ((x : Real) / (n : Real)) s := by
  rw [explicitFormulaDirichletTerm, LSeries.term_def, if_neg hn,
    perronKernelIntegrand]
  rw [Complex.ofReal_div]
  rw [Complex.div_cpow_ofReal_nonneg (Nat.cast_nonneg x)
    (Nat.cast_nonneg n)]
  simp only [Complex.ofReal_natCast]
  ring

theorem VIntegral_explicitFormulaDirichletTerm_eq_scalarPerronSeriesTerm
    {N : Nat} (chi : DirichletCharacter Complex N) (x n : Nat)
    (c T : Real) :
    VIntegral' (explicitFormulaDirichletTerm chi x n) c (-T) T =
      scalarPerronSeriesTerm chi x c T n := by
  by_cases hn : n = 0
  case pos =>
    subst n
    simp [scalarPerronSeriesTerm, explicitFormulaDirichletTerm,
      LSeries.term_def, VIntegral', VIntegral]
  case neg =>
    have hFunctions : (fun t : Real =>
        explicitFormulaDirichletTerm chi x n (c + t * Complex.I)) =
        fun t : Real => twistedMangoldtSequence chi n *
          perronKernelIntegrand ((x : Real) / (n : Real))
            (c + t * Complex.I) := by
      funext t
      exact explicitFormulaDirichletTerm_eq_coeff_mul_perronKernel chi x n
        (c + t * Complex.I) hn
    rw [scalarPerronSeriesTerm, if_neg hn]
    simp only [VIntegral', VIntegral, truncatedPerronKernel]
    rw [hFunctions, intervalIntegral.integral_const_mul]
    simp only [smul_eq_mul]
    ring

end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

theorem neg_logDeriv_LFunction_eq_LSeries
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) {s : Complex}
    (hs : 1 < s.re) :
    -logDeriv chi.LFunction s = LSeries (twistedMangoldtSequence chi) s := by
  have hSeries := DirichletCharacter.LSeries_twist_vonMangoldt_eq chi hs
  rw [logDeriv_apply,
    DirichletCharacter.deriv_LFunction_eq_deriv_LSeries chi hs,
    DirichletCharacter.LFunction_eq_LSeries chi hs]
  have hSequence : twistedMangoldtSequence chi =
      (fun n : Nat => chi n) *
        (fun n : Nat => (ArithmeticFunction.vonMangoldt n : Complex)) := by
    funext n
    rfl
  rw [hSequence, <- neg_div]
  exact hSeries.symm

theorem explicitFormulaIntegrand_eq_tsum
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    {x : Nat} (s : Complex) (hs : 1 < s.re) :
    explicitFormulaIntegrand chi x s =
      tsum (fun n : Nat => explicitFormulaDirichletTerm chi x n s) := by
  rw [explicitFormulaIntegrand]
  rw [show logDeriv chi.LFunction s * (-((x : Complex) ^ s / s)) =
      (-logDeriv chi.LFunction s) * ((x : Complex) ^ s / s) by ring]
  rw [neg_logDeriv_LFunction_eq_LSeries chi hs]
  rw [LSeries]
  simp only [explicitFormulaDirichletTerm]
  rw [<- tsum_mul_right]

end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

def perronSeriesFunction {N : Nat}
    (chi : DirichletCharacter Complex N) (x n : Nat) (c : Real) (t : Real) : Complex :=
  explicitFormulaDirichletTerm chi x n (c + t * Complex.I)

theorem perronSeriesFunction_continuous
    {N : Nat} (chi : DirichletCharacter Complex N) {x : Nat} (hx : 0 < x)
    (n : Nat) {c : Real} (hc : 1 < c) :
    Continuous (perronSeriesFunction chi x n c) := by
  by_cases hn : n = 0
  case pos =>
    subst n
    change Continuous (fun t : Real =>
      explicitFormulaDirichletTerm chi x 0 (c + t * Complex.I))
    simpa [explicitFormulaDirichletTerm, LSeries.term_def] using
      (continuous_const : Continuous (fun _ : Real => (0 : Complex)))
  case neg =>
    have hnC : Ne (n : Complex) 0 := by exact_mod_cast hn
    have hxC : Ne (x : Complex) 0 := by exact_mod_cast (Nat.ne_of_gt hx)
    have hsNe : forall t : Real, Ne ((c : Complex) + t * Complex.I) 0 := by
      intro t h
      have hre := congrArg Complex.re h
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im,
        mul_one, sub_self, add_zero, Complex.zero_re] at hre
      linarith
    have hpath : Continuous (fun t : Real =>
        (c : Complex) + t * Complex.I) := by
      fun_prop
    have hnPow : Continuous (fun t : Real =>
        (n : Complex) ^ ((c : Complex) + t * Complex.I)) :=
      hpath.const_cpow (Or.inl hnC)
    have hxPow : Continuous (fun t : Real =>
        (x : Complex) ^ ((c : Complex) + t * Complex.I)) :=
      hpath.const_cpow (Or.inl hxC)
    change Continuous (fun t : Real =>
      explicitFormulaDirichletTerm chi x n (c + t * Complex.I))
    simp only [explicitFormulaDirichletTerm, LSeries.term_def, hn, if_false]
    exact (continuous_const.div hnPow (fun _ =>
        Complex.cpow_ne_zero_iff.mpr (Or.inl hnC))).mul
      (hxPow.div hpath hsNe)

def perronSeriesContinuousMap
    {N : Nat} (chi : DirichletCharacter Complex N) {x : Nat} (hx : 0 < x)
    (n : Nat) {c : Real} (hc : 1 < c) : C(Real, Complex) :=
  ContinuousMap.mk (perronSeriesFunction chi x n c)
    (perronSeriesFunction_continuous chi hx n hc)

end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

open Set

namespace BombieriVinogradov.SiegelWalfisz

theorem norm_perronSeriesFunction_le
    {N : Nat} (chi : DirichletCharacter Complex N) {x : Nat} (hx : 0 < x)
    (n : Nat) {c : Real} (hc : 1 < c) (t : Real) :
    norm (perronSeriesFunction chi x n c t) <=
      ((x : Real) ^ c / c) *
        norm (LSeries.term (twistedMangoldtSequence chi) (c : Complex) n) := by
  by_cases hn : n = 0
  case pos =>
    subst n
    simp [perronSeriesFunction, explicitFormulaDirichletTerm,
      LSeries.term_def]
  case neg =>
    have hcPos : 0 < c := lt_trans zero_lt_one hc
    have hcNe : Ne c 0 := ne_of_gt hcPos
    have hReNe : Ne (((c : Complex) + t * Complex.I).re) 0 := by
      simpa using hcNe
    have hNormLower : c <= norm ((c : Complex) + t * Complex.I) := by
      calc
        c = abs (((c : Complex) + t * Complex.I).re) := by
          simp [abs_of_pos hcPos]
        _ <= norm ((c : Complex) + t * Complex.I) :=
          Complex.abs_re_le_norm _
    simp only [perronSeriesFunction, explicitFormulaDirichletTerm,
      LSeries.term_def, hn, if_false, norm_mul, norm_div]
    rw [Complex.norm_natCast_cpow_of_re_ne_zero n hReNe,
      Complex.norm_natCast_cpow_of_re_ne_zero x hReNe,
      Complex.norm_natCast_cpow_of_re_ne_zero n (by simpa using hcNe)]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im,
      mul_one, sub_self, add_zero]
    have hNormPos : 0 < norm ((c : Complex) + t * Complex.I) :=
      lt_of_lt_of_le hcPos hNormLower
    have hxPowNonneg : 0 <= (x : Real) ^ c :=
      Real.rpow_nonneg (Nat.cast_nonneg x) c
    have hCoeffNonneg :
        0 <= norm (twistedMangoldtSequence chi n) / (n : Real) ^ c :=
      div_nonneg (norm_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg n) c)
    calc
      norm (twistedMangoldtSequence chi n) / (n : Real) ^ c *
          ((x : Real) ^ c / norm ((c : Complex) + t * Complex.I)) <=
          norm (twistedMangoldtSequence chi n) / (n : Real) ^ c *
            ((x : Real) ^ c / c) := by
        gcongr
      _ = (x : Real) ^ c / c *
          (norm (twistedMangoldtSequence chi n) / (n : Real) ^ c) := by
        ring

theorem norm_restrict_perronSeriesContinuousMap_le
    {N : Nat} (chi : DirichletCharacter Complex N) {x : Nat} (hx : 0 < x)
    (n : Nat) {c T : Real} (hc : 1 < c) :
    norm ((perronSeriesContinuousMap chi hx n hc).restrict
      (TopologicalSpace.Compacts.mk (uIcc (-T) T) isCompact_uIcc)) <=
      ((x : Real) ^ c / c) *
        norm (LSeries.term (twistedMangoldtSequence chi) (c : Complex) n) := by
  have hcPos : 0 < c := lt_trans zero_lt_one hc
  have hMajorantNonneg : 0 <=
      ((x : Real) ^ c / c) *
        norm (LSeries.term (twistedMangoldtSequence chi) (c : Complex) n) :=
    mul_nonneg
      (div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg x) c) (le_of_lt hcPos))
      (norm_nonneg _)
  apply (ContinuousMap.norm_le _ hMajorantNonneg).mpr
  intro t
  simpa [perronSeriesContinuousMap] using
    norm_perronSeriesFunction_le chi hx n hc t.1

theorem summable_norm_restrict_perronSeriesContinuousMap
    {N : Nat} (chi : DirichletCharacter Complex N) {x : Nat} (hx : 0 < x)
    {c T : Real} (hc : 1 < c) :
    Summable (fun n : Nat =>
      norm ((perronSeriesContinuousMap chi hx n hc).restrict
        (TopologicalSpace.Compacts.mk (uIcc (-T) T) isCompact_uIcc))) := by
  have hSequence : twistedMangoldtSequence chi =
      (fun n : Nat => chi n) *
        (fun n : Nat => (ArithmeticFunction.vonMangoldt n : Complex)) := by
    funext n
    rfl
  have hLSeries : LSeriesSummable (twistedMangoldtSequence chi) (c : Complex) := by
    rw [hSequence]
    exact DirichletCharacter.LSeriesSummable_twist_vonMangoldt chi (by simpa using hc)
  have hMajorant : Summable (fun n : Nat =>
      ((x : Real) ^ c / c) *
        norm (LSeries.term (twistedMangoldtSequence chi) (c : Complex) n)) :=
    hLSeries.norm.mul_left ((x : Real) ^ c / c)
  apply Summable.of_nonneg_of_le
    (fun _ => norm_nonneg _)
    (fun n => norm_restrict_perronSeriesContinuousMap_le chi hx n hc)
    hMajorant

end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

theorem tsum_intervalIntegral_perronSeriesFunction
    {N : Nat} (chi : DirichletCharacter Complex N) {x : Nat} (hx : 0 < x)
    {c T : Real} (hc : 1 < c) :
    tsum (fun n : Nat => intervalIntegral
      (perronSeriesFunction chi x n c) (-T) T MeasureTheory.volume) =
      intervalIntegral (fun t : Real =>
        tsum (fun n : Nat => perronSeriesFunction chi x n c t))
        (-T) T MeasureTheory.volume := by
  exact intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm
    (summable_norm_restrict_perronSeriesContinuousMap chi hx hc)

end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

theorem explicitFormulaVerticalIntegral_eq_tsum_VIntegral
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    {x : Nat} (hx : 0 < x) {c T : Real} (hc : 1 < c) :
    explicitFormulaVerticalIntegral chi x c T =
      tsum (fun n : Nat =>
        VIntegral' (explicitFormulaDirichletTerm chi x n) c (-T) T) := by
  have hFunctions : (fun t : Real =>
      explicitFormulaIntegrand chi x (c + t * Complex.I)) =
      fun t : Real => tsum (fun n : Nat =>
        perronSeriesFunction chi x n c t) := by
    funext t
    apply explicitFormulaIntegrand_eq_tsum
    simpa using hc
  have hInterchange := tsum_intervalIntegral_perronSeriesFunction
    (T := T) chi hx hc
  simp only [explicitFormulaVerticalIntegral, VIntegral', VIntegral]
  rw [hFunctions]
  rw [<- hInterchange]
  rw [<- tsum_const_smul'' Complex.I]
  rw [<- tsum_const_smul'' (1 / (2 * Real.pi * Complex.I))]
  rfl

end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

theorem explicitFormulaVerticalIntegral_eq_tsum_scalarPerronSeriesTerm
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    {x : Nat} (hx : 0 < x) {c T : Real} (hc : 1 < c) :
    explicitFormulaVerticalIntegral chi x c T =
      tsum (scalarPerronSeriesTerm chi x c T) := by
  calc
    explicitFormulaVerticalIntegral chi x c T =
        tsum (fun n : Nat =>
          VIntegral' (explicitFormulaDirichletTerm chi x n) c (-T) T) :=
      explicitFormulaVerticalIntegral_eq_tsum_VIntegral chi hx hc
    _ = tsum (scalarPerronSeriesTerm chi x c T) := by
      apply tsum_congr
      intro n
      exact VIntegral_explicitFormulaDirichletTerm_eq_scalarPerronSeriesTerm
        chi x n c T

end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

open Finset
open scoped BigOperators

namespace BombieriVinogradov.SiegelWalfisz

def scalarPerronStepTerm {N : Nat}
    (chi : DirichletCharacter Complex N) (x n : Nat) : Complex :=
  if n = 0 then 0 else
    twistedMangoldtSequence chi n *
      (perronStepWeight ((x : Real) / (n : Real)) : Complex)

def characterChebyshevHalfSum {N : Nat}
    (x : Nat) (chi : DirichletCharacter Complex N) : Complex :=
  (Finset.sum (Finset.Ico 1 x) (twistedMangoldtSequence chi)) +
    (1 / 2 : Complex) * twistedMangoldtSequence chi x

end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

def scalarPerronErrorTerm {N : Nat}
    (chi : DirichletCharacter Complex N) (x : Nat) (c T : Real) (n : Nat) : Complex :=
  scalarPerronSeriesTerm chi x c T n - scalarPerronStepTerm chi x n

def scalarPerronErrorMajorantTerm {N : Nat}
    (chi : DirichletCharacter Complex N) (x : Nat) (c T : Real) (n : Nat) : Real :=
  if n = 0 then 0 else
    norm (twistedMangoldtSequence chi n) *
      if (x : Real) / (n : Real) = 1 then c / (Real.pi * T)
      else ((x : Real) / (n : Real)) ^ c *
        min 1 (1 / (Real.pi * T *
          abs (Real.log ((x : Real) / (n : Real)))))

end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

def sourcePerronErrorMajorantTerm (x : Nat) (c T : Real) (n : Nat) : Real :=
  if n = 0 then 0 else
    ArithmeticFunction.vonMangoldt n *
      if (x : Real) / (n : Real) = 1 then c / (Real.pi * T)
      else ((x : Real) / (n : Real)) ^ c *
        min 1 (1 / (Real.pi * T *
          abs (Real.log ((x : Real) / (n : Real)))))

end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

theorem norm_twistedMangoldtSequence_le_vonMangoldt
    {N : Nat} (chi : DirichletCharacter Complex N) (n : Nat) :
    norm (twistedMangoldtSequence chi n) <= ArithmeticFunction.vonMangoldt n := by
  unfold twistedMangoldtSequence
  rw [norm_mul, Complex.norm_real,
    Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  exact mul_le_of_le_one_left ArithmeticFunction.vonMangoldt_nonneg
    (chi.norm_le_one n)

theorem scalarPerronErrorMajorantTerm_le_source
    {N : Nat} (chi : DirichletCharacter Complex N) {x : Nat} (hx : 0 < x)
    {c T : Real} (hc : 0 < c) (hT : 0 < T) (n : Nat) :
    scalarPerronErrorMajorantTerm chi x c T n <=
      sourcePerronErrorMajorantTerm x c T n := by
  by_cases hn : n = 0
  case pos =>
    simp [scalarPerronErrorMajorantTerm, sourcePerronErrorMajorantTerm, hn]
  case neg =>
    have hnPos : 0 < n := Nat.pos_of_ne_zero hn
    have hRatioPos : 0 < (x : Real) / (n : Real) :=
      div_pos (by exact_mod_cast hx) (by exact_mod_cast hnPos)
    by_cases hRatio : (x : Real) / (n : Real) = 1
    case pos =>
      simp only [scalarPerronErrorMajorantTerm,
        sourcePerronErrorMajorantTerm, hn, hRatio, if_false, if_true]
      apply mul_le_mul_of_nonneg_right
        (norm_twistedMangoldtSequence_le_vonMangoldt chi n)
      positivity
    case neg =>
      simp only [scalarPerronErrorMajorantTerm,
        sourcePerronErrorMajorantTerm, hn, hRatio, if_false]
      apply mul_le_mul_of_nonneg_right
        (norm_twistedMangoldtSequence_le_vonMangoldt chi n)
      have hReciprocal : 0 <= 1 / (Real.pi * T *
          abs (Real.log ((x : Real) / (n : Real)))) := by
        positivity
      exact mul_nonneg (Real.rpow_nonneg hRatioPos.le c)
        (le_min zero_le_one hReciprocal)

end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

def optimizedPerronLine (x : Nat) : Real :=
  1 + 1 / Real.log (x : Real)

end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

theorem one_le_log_natCast {x : Nat} (hx : 2 < x) :
    (1 : Real) <= Real.log (x : Real) := by
  have hLogThree := Real.le_log_one_add_of_nonneg
    (x := (2 : Real)) (by norm_num)
  norm_num at hLogThree
  have hxThree : (3 : Real) <= (x : Real) := by exact_mod_cast hx
  exact hLogThree.trans (Real.log_le_log (by norm_num) hxThree)

theorem optimizedPerronLine_gt_one {x : Nat} (hx : 2 < x) :
    1 < optimizedPerronLine x := by
  have hLogPos : 0 < Real.log (x : Real) :=
    lt_of_lt_of_le zero_lt_one (one_le_log_natCast hx)
  have hInvPos : 0 < 1 / Real.log (x : Real) := by positivity
  unfold optimizedPerronLine
  linarith

theorem optimizedPerronLine_le_two {x : Nat} (hx : 2 < x) :
    optimizedPerronLine x <= 2 := by
  have hLog := one_le_log_natCast hx
  have hInv : 1 / Real.log (x : Real) <= 1 := by
    have h := one_div_le_one_div_of_le zero_lt_one hLog
    norm_num at h
    simpa only [one_div] using h
  unfold optimizedPerronLine
  linarith

end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

theorem rpow_optimizedPerronLine_eq {x : Nat} (hx : 2 < x) :
    (x : Real) ^ optimizedPerronLine x =
      (x : Real) * Real.exp 1 := by
  have hxPos : 0 < x := lt_trans zero_lt_two hx
  have hxReal : 0 < (x : Real) := by exact_mod_cast hxPos
  have hxNeOne : Ne (x : Real) 1 := by
    have hxThree : (3 : Real) <= (x : Real) := by exact_mod_cast hx
    linarith
  unfold optimizedPerronLine
  rw [Real.rpow_add hxReal, Real.rpow_one, one_div]
  rw [Real.rpow_inv_log hxReal hxNeOne]

end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

def vonMangoldtLSeriesNormSum (c : Real) : Real :=
  tsum (fun n : Nat =>
    norm (LSeries.term
      (fun m : Nat => (ArithmeticFunction.vonMangoldt m : Complex))
      (c : Complex) n))

theorem LSeriesTerm_vonMangoldt_eq_ofReal
    {c : Real} (n : Nat) :
    LSeries.term
        (fun m : Nat => (ArithmeticFunction.vonMangoldt m : Complex))
        (c : Complex) n =
      ((ArithmeticFunction.vonMangoldt n / (n : Real) ^ c : Real) : Complex) := by
  by_cases hn : n = 0
  case pos =>
    subst n
    simp [LSeries.term_def]
  case neg =>
    rw [LSeries.term_def, if_neg hn]
    rw [Complex.ofReal_div]
    rw [Complex.ofReal_cpow (Nat.cast_nonneg n) c]
    norm_cast

theorem re_LSeriesTerm_vonMangoldt_eq_norm
    {c : Real} (n : Nat) :
    (LSeries.term
      (fun m : Nat => (ArithmeticFunction.vonMangoldt m : Complex))
      (c : Complex) n).re =
    norm (LSeries.term
      (fun m : Nat => (ArithmeticFunction.vonMangoldt m : Complex))
      (c : Complex) n) := by
  rw [LSeriesTerm_vonMangoldt_eq_ofReal]
  rw [Complex.ofReal_re, Complex.norm_real]
  apply Eq.symm
  rw [Real.norm_of_nonneg]
  exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg
    (Real.rpow_nonneg (Nat.cast_nonneg n) c)

theorem norm_LSeriesTerm_vonMangoldt_eq
    {c : Real} (n : Nat) :
    norm (LSeries.term
      (fun m : Nat => (ArithmeticFunction.vonMangoldt m : Complex))
      (c : Complex) n) =
      ArithmeticFunction.vonMangoldt n / (n : Real) ^ c := by
  rw [LSeriesTerm_vonMangoldt_eq_ofReal, Complex.norm_real,
    Real.norm_of_nonneg]
  exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg
    (Real.rpow_nonneg (Nat.cast_nonneg n) c)

theorem vonMangoldtLSeriesNormSum_eq_neg_logDeriv_re
    {c : Real} (hc : 1 < c) :
    vonMangoldtLSeriesNormSum c =
      (-deriv riemannZeta (c : Complex) / riemannZeta (c : Complex)).re := by
  have hSummable := ArithmeticFunction.LSeriesSummable_vonMangoldt
    (s := (c : Complex)) (by simpa using hc)
  have hSeries := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div
    (s := (c : Complex)) (by simpa using hc)
  rw [LSeries] at hSeries
  have hReal := congrArg Complex.re hSeries
  rw [Complex.re_tsum hSummable] at hReal
  have hTerms : (fun n : Nat =>
      (LSeries.term
        (fun m : Nat => (ArithmeticFunction.vonMangoldt m : Complex))
        (c : Complex) n).re) = fun n : Nat =>
      norm (LSeries.term
        (fun m : Nat => (ArithmeticFunction.vonMangoldt m : Complex))
        (c : Complex) n) := by
    funext n
    exact re_LSeriesTerm_vonMangoldt_eq_norm n
  rw [hTerms] at hReal
  exact hReal

end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

theorem scalarPerronErrorMajorantTerm_le_summable
    {N : Nat} (chi : DirichletCharacter Complex N) {x : Nat} (hx : 0 < x)
    {c T : Real} (hc : 0 < c) (n : Nat) :
    scalarPerronErrorMajorantTerm chi x c T n <=
      (x : Real) ^ c *
          norm (LSeries.term (twistedMangoldtSequence chi) (c : Complex) n) +
        if n = x then
          norm (twistedMangoldtSequence chi n) * (c / (Real.pi * T))
        else 0 := by
  by_cases hn : n = 0
  case pos =>
    subst n
    simp [scalarPerronErrorMajorantTerm, LSeries.term_def,
      (Nat.ne_of_gt hx).symm]
  case neg =>
    have hnRealNe : Ne (n : Real) 0 := by exact_mod_cast hn
    by_cases hRatio : (x : Real) / (n : Real) = 1
    case pos =>
      have hxnReal : (x : Real) = (n : Real) :=
        (div_eq_one_iff_eq hnRealNe).mp hRatio
      have hxn : x = n := by exact_mod_cast hxnReal
      rw [scalarPerronErrorMajorantTerm, if_neg hn, if_pos hRatio,
        if_pos hxn.symm]
      exact le_add_of_nonneg_left (mul_nonneg
        (Real.rpow_nonneg (Nat.cast_nonneg x) c) (norm_nonneg _))
    case neg =>
      have hnx : Ne n x := by
        intro h
        subst n
        apply hRatio
        exact div_self (by exact_mod_cast (Nat.ne_of_gt hx))
      rw [scalarPerronErrorMajorantTerm, if_neg hn, if_neg hRatio,
        if_neg hnx]
      calc
        norm (twistedMangoldtSequence chi n) *
            (((x : Real) / (n : Real)) ^ c *
              min 1 (1 / (Real.pi * T *
                abs (Real.log ((x : Real) / (n : Real)))))) <=
            norm (twistedMangoldtSequence chi n) *
              (((x : Real) / (n : Real)) ^ c * 1) := by
          gcongr
          exact min_le_left _ _
        _ = (x : Real) ^ c *
            norm (LSeries.term (twistedMangoldtSequence chi)
              (c : Complex) n) := by
          rw [LSeries.term_def, if_neg hn, norm_div,
            Complex.norm_natCast_cpow_of_re_ne_zero n (by simpa using ne_of_gt hc),
            Real.div_rpow (Nat.cast_nonneg x) (Nat.cast_nonneg n) c]
          simp only [Complex.ofReal_re, mul_one]
          ring
        _ = (x : Real) ^ c *
              norm (LSeries.term (twistedMangoldtSequence chi)
                (c : Complex) n) + 0 := by
          ring

theorem scalarPerronErrorMajorantTerm_nonneg
    {N : Nat} (chi : DirichletCharacter Complex N) {x : Nat} (hx : 0 < x)
    {c T : Real} (hc : 0 < c) (hT : 0 < T) (n : Nat) :
    0 <= scalarPerronErrorMajorantTerm chi x c T n := by
  by_cases hn : n = 0
  case pos =>
    simp [scalarPerronErrorMajorantTerm, hn]
  case neg =>
    have hnPos : 0 < n := Nat.pos_of_ne_zero hn
    have hRatioPos : 0 < (x : Real) / (n : Real) :=
      div_pos (by exact_mod_cast hx) (by exact_mod_cast hnPos)
    by_cases hRatio : (x : Real) / (n : Real) = 1
    case pos =>
      rw [scalarPerronErrorMajorantTerm, if_neg hn, if_pos hRatio]
      positivity
    case neg =>
      rw [scalarPerronErrorMajorantTerm, if_neg hn, if_neg hRatio]
      have hReciprocal : 0 <= 1 / (Real.pi * T *
          abs (Real.log ((x : Real) / (n : Real)))) := by
        positivity
      exact mul_nonneg (norm_nonneg _)
        (mul_nonneg (Real.rpow_nonneg hRatioPos.le c)
          (le_min zero_le_one hReciprocal))

theorem summable_scalarPerronErrorMajorantTerm
    {N : Nat} (chi : DirichletCharacter Complex N) {x : Nat} (hx : 0 < x)
    {c T : Real} (hc : 1 < c) (hT : 0 < T) :
    Summable (scalarPerronErrorMajorantTerm chi x c T) := by
  have hSequence : twistedMangoldtSequence chi =
      (fun n : Nat => chi n) *
        (fun n : Nat => (ArithmeticFunction.vonMangoldt n : Complex)) := by
    funext n
    rfl
  have hLSeries : LSeriesSummable (twistedMangoldtSequence chi) (c : Complex) := by
    rw [hSequence]
    exact DirichletCharacter.LSeriesSummable_twist_vonMangoldt chi (by simpa using hc)
  have hBase : Summable (fun n : Nat =>
      (x : Real) ^ c *
        norm (LSeries.term (twistedMangoldtSequence chi) (c : Complex) n)) :=
    hLSeries.norm.mul_left ((x : Real) ^ c)
  have hEndpoint : Summable (fun n : Nat =>
      if n = x then
        norm (twistedMangoldtSequence chi n) * (c / (Real.pi * T))
      else 0) := by
    have hFunction : (fun n : Nat =>
        if n = x then
          norm (twistedMangoldtSequence chi n) * (c / (Real.pi * T))
        else 0) = fun n : Nat =>
          if n = x then
            norm (twistedMangoldtSequence chi x) * (c / (Real.pi * T))
          else 0 := by
      funext n
      by_cases hnx : n = x
      case pos =>
        subst n
        rfl
      case neg =>
        simp [hnx]
    rw [hFunction]
    exact (hasSum_ite_eq x
      (norm (twistedMangoldtSequence chi x) * (c / (Real.pi * T)))).summable
  apply Summable.of_nonneg_of_le
    (fun n => scalarPerronErrorMajorantTerm_nonneg chi hx
      (lt_trans zero_lt_one hc) hT n)
    (fun n => scalarPerronErrorMajorantTerm_le_summable chi hx
      (lt_trans zero_lt_one hc) n)
    (hBase.add hEndpoint)

end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

theorem norm_twistedMangoldtSequence_one_eq (n : Nat) :
    norm (twistedMangoldtSequence (1 : DirichletCharacter Complex 1) n) =
      ArithmeticFunction.vonMangoldt n := by
  unfold twistedMangoldtSequence
  rw [norm_mul, Complex.norm_real,
    Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  have hOneFunction :
      ((fun m : Nat => (1 : DirichletCharacter Complex 1) m) : Nat -> Complex) = 1 :=
    DirichletCharacter.modOne_eq_one
  have hOneValue : (1 : DirichletCharacter Complex 1) n = 1 := by
    simpa using congrFun hOneFunction n
  rw [hOneValue, norm_one, one_mul]

theorem summable_sourcePerronErrorMajorantTerm
    {x : Nat} (hx : 0 < x) {c T : Real} (hc : 1 < c) (hT : 0 < T) :
    Summable (sourcePerronErrorMajorantTerm x c T) := by
  have hFunction : sourcePerronErrorMajorantTerm x c T =
      scalarPerronErrorMajorantTerm
        (1 : DirichletCharacter Complex 1) x c T := by
    funext n
    unfold sourcePerronErrorMajorantTerm
    unfold scalarPerronErrorMajorantTerm
    rw [norm_twistedMangoldtSequence_one_eq]
  rw [hFunction]
  exact summable_scalarPerronErrorMajorantTerm
    (1 : DirichletCharacter Complex 1) hx hc hT

end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

theorem perronStepWeight_natRatio_eq_one_of_lt
    {x n : Nat} (hn : 0 < n) (hnx : n < x) :
    perronStepWeight ((x : Real) / (n : Real)) = 1 := by
  have hnReal : 0 < (n : Real) := by exact_mod_cast hn
  have hnxReal : (n : Real) < (x : Real) := by exact_mod_cast hnx
  have hRatio : 1 < (x : Real) / (n : Real) := by
    rw [one_lt_div hnReal]
    exact hnxReal
  simp [perronStepWeight, not_lt_of_ge hRatio.le, ne_of_gt hRatio]

theorem perronStepWeight_natRatio_eq_half
    {x : Nat} (hx : 0 < x) :
    perronStepWeight ((x : Real) / (x : Real)) = 1 / 2 := by
  have hxNe : Ne (x : Real) 0 := by exact_mod_cast (Nat.ne_of_gt hx)
  simp [hxNe, perronStepWeight]

theorem perronStepWeight_natRatio_eq_zero_of_lt
    {x n : Nat} (hn : 0 < n) (hxn : x < n) :
    perronStepWeight ((x : Real) / (n : Real)) = 0 := by
  have hnReal : 0 < (n : Real) := by exact_mod_cast hn
  have hxnReal : (x : Real) < (n : Real) := by exact_mod_cast hxn
  have hRatio : (x : Real) / (n : Real) < 1 := by
    rw [div_lt_one hnReal]
    exact hxnReal
  simp [perronStepWeight, hRatio]

theorem scalarPerronStepTerm_eq_coeff_of_lt
    {N x n : Nat} (chi : DirichletCharacter Complex N)
    (hn : 0 < n) (hnx : n < x) :
    scalarPerronStepTerm chi x n = twistedMangoldtSequence chi n := by
  simp [scalarPerronStepTerm, Nat.ne_of_gt hn,
    perronStepWeight_natRatio_eq_one_of_lt hn hnx]

theorem scalarPerronStepTerm_eq_half
    {N x : Nat} (chi : DirichletCharacter Complex N) (hx : 0 < x) :
    scalarPerronStepTerm chi x x =
      (1 / 2 : Complex) * twistedMangoldtSequence chi x := by
  rw [scalarPerronStepTerm, if_neg (Nat.ne_of_gt hx),
    perronStepWeight_natRatio_eq_half hx]
  simpa using mul_comm (twistedMangoldtSequence chi x) (1 / 2 : Complex)

theorem scalarPerronStepTerm_eq_zero_of_lt
    {N x n : Nat} (chi : DirichletCharacter Complex N)
    (hn : 0 < n) (hxn : x < n) :
    scalarPerronStepTerm chi x n = 0 := by
  simp [scalarPerronStepTerm, Nat.ne_of_gt hn,
    perronStepWeight_natRatio_eq_zero_of_lt hn hxn]

end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

open Finset
open scoped BigOperators

namespace BombieriVinogradov.SiegelWalfisz

theorem summable_scalarPerronStepTerm
    {N x : Nat} (chi : DirichletCharacter Complex N) :
    Summable (scalarPerronStepTerm chi x) := by
  apply summable_of_ne_finset_zero (s := Finset.Icc 1 x)
  intro n hnMem
  by_cases hnZero : n = 0
  case pos =>
    simp [scalarPerronStepTerm, hnZero]
  case neg =>
    have hnPos : 0 < n := Nat.pos_of_ne_zero hnZero
    have hOne : 1 <= n := hnPos
    have hNotLe : Not (n <= x) := by
      intro hnx
      exact hnMem (by simp [hOne, hnx])
    exact scalarPerronStepTerm_eq_zero_of_lt chi hnPos
      (Nat.lt_of_not_ge hNotLe)

theorem tsum_scalarPerronStepTerm_eq_characterChebyshevHalfSum
    {N x : Nat} (chi : DirichletCharacter Complex N) (hx : 0 < x) :
    tsum (scalarPerronStepTerm chi x) = characterChebyshevHalfSum x chi := by
  have hTail : forall n : Nat, Not (Membership.mem (Finset.Icc 1 x) n) ->
      scalarPerronStepTerm chi x n = 0 := by
    intro n hnMem
    by_cases hnZero : n = 0
    case pos =>
      simp [scalarPerronStepTerm, hnZero]
    case neg =>
      have hnPos : 0 < n := Nat.pos_of_ne_zero hnZero
      have hOne : 1 <= n := hnPos
      have hNotLe : Not (n <= x) := by
        intro hnx
        exact hnMem (by simp [hOne, hnx])
      exact scalarPerronStepTerm_eq_zero_of_lt chi hnPos
        (Nat.lt_of_not_ge hNotLe)
  rw [tsum_eq_sum hTail]
  have hInterior :
      Finset.sum (Finset.Ico 1 x) (scalarPerronStepTerm chi x) =
        Finset.sum (Finset.Ico 1 x) (twistedMangoldtSequence chi) := by
    apply Finset.sum_congr rfl
    intro n hnMem
    have hnBounds := Finset.mem_Ico.mp hnMem
    exact scalarPerronStepTerm_eq_coeff_of_lt chi
      (lt_of_lt_of_le zero_lt_one hnBounds.1) hnBounds.2
  have hxMem : Membership.mem (Finset.Icc 1 x) x :=
    Finset.mem_Icc.mpr (And.intro hx (le_refl x))
  have hDecomp := Finset.sum_erase_add (Finset.Icc 1 x)
    (scalarPerronStepTerm chi x) hxMem
  rw [Finset.Icc_erase_right] at hDecomp
  rw [<- hDecomp]
  rw [scalarPerronStepTerm_eq_half chi hx]
  unfold characterChebyshevHalfSum
  rw [hInterior]

end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

open MeasureTheory Set

namespace BombieriVinogradov.SiegelWalfisz

theorem integrableOn_rpow_Iic
    {y : Real} (hy1 : 1 < y) (c : Real) :
    IntegrableOn (fun x : Real => y ^ x) (Iic c) := by
  have hy : 0 < y := lt_trans Real.zero_lt_one hy1
  simpa [Real.rpow_def_of_pos hy] using
    integrableOn_exp_mul_Iic (Real.log_pos hy1) c

theorem integral_rpow_Iic
    {y : Real} (hy1 : 1 < y) (c : Real) :
    integral (volume.restrict (Iic c)) (fun x : Real => y ^ x) =
      y ^ c / abs (Real.log y) := by
  have hy : 0 < y := lt_trans Real.zero_lt_one hy1
  rw [show (fun x : Real => y ^ x) =
      fun x : Real => Real.exp (Real.log y * x) by
    funext x
    exact Real.rpow_def_of_pos hy x]
  rw [integral_exp_mul_Iic (Real.log_pos hy1)]
  rw [(Real.rpow_def_of_pos hy c).symm]
  rw [abs_of_pos (Real.log_pos hy1)]

end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

open Filter MeasureTheory Set Topology

namespace BombieriVinogradov.SiegelWalfisz

theorem norm_perron_left_horizontal_le
    {y t x : Real} (hy : 0 < y) (ht : 0 < abs t) :
    norm (perronKernelIntegrand y
      ((x : Complex) + (t : Complex) * Complex.I)) <= y ^ x / abs t := by
  rw [norm_perronKernelIntegrand hy]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]
  have hLower : abs t <=
      norm ((x : Complex) + (t : Complex) * Complex.I) := by
    simpa using Complex.abs_im_le_norm
      ((x : Complex) + (t : Complex) * Complex.I)
  exact div_le_div_of_nonneg_left (Real.rpow_nonneg hy.le x) ht hLower

theorem integrableOn_perron_horizontal_Iic
    {y c t : Real} (hy1 : 1 < y) (ht : 0 < abs t) :
    IntegrableOn
      (fun x : Real => perronKernelIntegrand y
        ((x : Complex) + (t : Complex) * Complex.I))
      (Iic c) := by
  have hy : 0 < y := lt_trans Real.zero_lt_one hy1
  have hDom : IntegrableOn (fun x : Real => y ^ x / abs t) (Iic c) :=
    (integrableOn_rpow_Iic hy1 c).div_const (abs t)
  apply hDom.mono'
  next =>
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Iic
    intro x _
    have hEq :
        (fun u : Real => perronKernelIntegrand y
          ((u : Complex) + (t : Complex) * Complex.I)) =
          fun u : Real =>
            Complex.exp
                ((Real.log y : Complex) *
                  ((u : Complex) + (t : Complex) * Complex.I)) /
              ((u : Complex) + (t : Complex) * Complex.I) := by
      funext u
      exact perronKernelIntegrand_eq_exp hy _
    rw [hEq]
    fun_prop (disch :=
      intro hzero
      have hImag := congrArg Complex.im hzero
      simp at hImag
      exact (ne_of_gt ht) (abs_eq_zero.mpr hImag))
  next =>
    filter_upwards [ae_restrict_mem measurableSet_Iic] with x _
    exact norm_perron_left_horizontal_le hy ht

theorem norm_integral_perron_horizontal_Iic_le
    {y c t : Real} (hy1 : 1 < y) (ht : 0 < abs t) :
    norm
        (integral (volume.restrict (Iic c))
          (fun x : Real => perronKernelIntegrand y
            ((x : Complex) + (t : Complex) * Complex.I))) <=
      y ^ c / (abs t * abs (Real.log y)) := by
  have hy : 0 < y := lt_trans Real.zero_lt_one hy1
  have hDom : IntegrableOn (fun x : Real => y ^ x / abs t) (Iic c) :=
    (integrableOn_rpow_Iic hy1 c).div_const (abs t)
  have hNorm :
      norm
          (integral (volume.restrict (Iic c))
            (fun x : Real => perronKernelIntegrand y
              ((x : Complex) + (t : Complex) * Complex.I))) <=
        integral (volume.restrict (Iic c)) (fun x : Real => y ^ x / abs t) := by
    apply MeasureTheory.norm_integral_le_of_norm_le hDom
    filter_upwards [ae_restrict_mem measurableSet_Iic] with x _
    exact norm_perron_left_horizontal_le hy ht
  calc
    norm
        (integral (volume.restrict (Iic c))
          (fun x : Real => perronKernelIntegrand y
            ((x : Complex) + (t : Complex) * Complex.I))) <=
        integral (volume.restrict (Iic c)) (fun x : Real => y ^ x / abs t) := hNorm
    _ = (1 / abs t) *
        integral (volume.restrict (Iic c)) (fun x : Real => y ^ x) := by
      rw [show (fun x : Real => y ^ x / abs t) =
          fun x : Real => (1 / abs t) * y ^ x by
        funext x
        ring]
      rw [integral_const_mul]
    _ = y ^ c / (abs t * abs (Real.log y)) := by
      rw [integral_rpow_Iic hy1]
      ring

def leftHorizontalIntegral (y c t : Real) : Complex :=
  integral (volume.restrict (Iic c))
    (fun x : Real => perronKernelIntegrand y
      ((x : Complex) + (t : Complex) * Complex.I))

theorem tendsto_hIntegral'_left_atTop
    {y c t : Real} (hy1 : 1 < y) (ht : 0 < abs t) :
    Tendsto
      (fun R : Real => HIntegral' (perronKernelIntegrand y) (-R) c t)
      atTop
      (nhds
        ((1 / (2 * Real.pi * Complex.I) : Complex) *
          leftHorizontalIntegral y c t)) := by
  have hLimit := intervalIntegral_tendsto_integral_Iic
    (f := fun x : Real => perronKernelIntegrand y
      ((x : Complex) + (t : Complex) * Complex.I)) c
    (integrableOn_perron_horizontal_Iic hy1 ht)
    tendsto_neg_atTop_atBot
  simpa [HIntegral', HIntegral, leftHorizontalIntegral, smul_eq_mul] using
    hLimit.const_smul (1 / (2 * Real.pi * Complex.I) : Complex)

end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

open Filter MeasureTheory Set

namespace BombieriVinogradov.SiegelWalfisz

theorem norm_integral_perron_horizontal_Iic_lt
    {y c t : Real} (hy1 : 1 < y) (hc : 0 < c) (ht : 0 < abs t) :
    norm
        (integral (volume.restrict (Iic c))
          (fun x : Real => perronKernelIntegrand y
            ((x : Complex) + (t : Complex) * Complex.I))) <
      y ^ c / (abs t * abs (Real.log y)) := by
  have hy : 0 < y := lt_trans Real.zero_lt_one hy1
  let mu := volume.restrict (Iic c)
  let f : Real -> Real := fun x =>
    norm (perronKernelIntegrand y
      ((x : Complex) + (t : Complex) * Complex.I))
  let g : Real -> Real := fun x => y ^ x / abs t
  have hf : Integrable f mu := by
    dsimp [f, mu]
    exact (integrableOn_perron_horizontal_Iic hy1 ht).norm
  have hg : Integrable g mu := by
    dsimp [g, mu]
    exact (integrableOn_rpow_Iic hy1 c).div_const (abs t)
  have hfg : Filter.Eventually (fun x => f x <= g x) (ae mu) :=
    Eventually.of_forall fun x => by
      exact norm_perron_left_horizontal_le hy ht
  have hdInt : Integrable (g - f) mu := hg.sub hf
  have hdNonneg : Filter.Eventually (fun x => 0 <= (g - f) x) (ae mu) :=
    hfg.mono fun x hx => by
      simpa only [Pi.sub_apply, sub_nonneg] using hx
  have hSmallSubset : Set.Ioc (-2 : Real) (-1) <= Set.Iic c := by
    intro x hx
    change x <= c
    linarith [hx.2]
  have hSmallSupport :
      Set.Ioc (-2 : Real) (-1) <= Function.support (g - f) := by
    intro x hx
    change Ne ((g - f) x) 0
    apply ne_of_gt
    rw [Pi.sub_apply, sub_pos]
    dsimp [f, g]
    rw [norm_perronKernelIntegrand hy]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one,
      sub_self, add_zero]
    have hx0 : Ne x 0 := by linarith [hx.2]
    have hDenom : abs t <
        norm ((x : Complex) + (t : Complex) * Complex.I) := by
      have hStrict := (Complex.abs_im_lt_norm).2 (by
        simpa using hx0 :
          Ne (((x : Complex) + (t : Complex) * Complex.I).re) 0)
      simpa using hStrict
    exact div_lt_div_of_pos_left (Real.rpow_pos_of_pos hy x) ht hDenom
  have hSmallMeasure : 0 < mu (Set.Ioc (-2 : Real) (-1)) := by
    dsimp [mu]
    rw [Measure.restrict_apply measurableSet_Ioc]
    rw [Set.inter_eq_left.mpr hSmallSubset]
    norm_num [Real.volume_Ioc]
  have hSupportMeasure : 0 < mu (Function.support (g - f)) :=
    hSmallMeasure.trans_le (measure_mono hSmallSupport)
  have hdPos : 0 < integral mu (g - f) :=
    (integral_pos_iff_support_of_nonneg_ae hdNonneg hdInt).2 hSupportMeasure
  change 0 < integral mu (fun x => g x - f x) at hdPos
  rw [integral_sub hg hf] at hdPos
  have hStrictIntegral : integral mu f < integral mu g := by linarith
  calc
    norm
        (integral (volume.restrict (Iic c))
          (fun x : Real => perronKernelIntegrand y
            ((x : Complex) + (t : Complex) * Complex.I))) <=
        integral mu f := by
      dsimp [mu, f]
      exact norm_integral_le_integral_norm _
    _ < integral mu g := hStrictIntegral
    _ = (1 / abs t) *
        integral (volume.restrict (Iic c)) (fun x : Real => y ^ x) := by
      dsimp [mu, g]
      rw [show (fun x : Real => y ^ x / abs t) =
          fun x : Real => (1 / abs t) * y ^ x by
        funext x
        ring]
      rw [integral_const_mul]
    _ = y ^ c / (abs t * abs (Real.log y)) := by
      rw [integral_rpow_Iic hy1]
      ring

end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

def perronKernelRemainder (y : Real) (s : Complex) : Complex :=
  dslope (fun z : Complex =>
    Complex.exp ((Real.log y : Complex) * z)) 0 s

theorem differentiableAt_perronKernelRemainder
    (y : Real) (s : Complex) :
    DifferentiableAt Complex (perronKernelRemainder y) s := by
  let h : Complex -> Complex := fun z =>
    Complex.exp ((Real.log y : Complex) * z)
  by_cases hs : s = 0
  next =>
    subst s
    have hh : AnalyticAt Complex h 0 := by
      dsimp [h]
      fun_prop
    choose p hp using hh
    exact hp.has_fpower_series_dslope_fslope.differentiableAt
  next =>
    change DifferentiableAt Complex (dslope h 0) s
    exact (differentiableAt_dslope_of_ne hs).2 (by
      dsimp [h]
      fun_prop)

theorem perronKernelIntegrand_sub_pole_eq_remainder
    {y : Real} (hy : 0 < y) :
    Set.EqOn
      (perronKernelIntegrand y - fun s : Complex => 1 / (s - 0))
      (perronKernelRemainder y) (Set.compl ({0} : Set Complex)) := by
  intro s hs
  have hs0 : Ne s 0 := by
    intro h
    apply hs
    simp [h]
  rw [Pi.sub_apply, perronKernelIntegrand_eq_exp hy]
  rw [perronKernelRemainder, dslope_of_ne _ hs0]
  simp only [slope, sub_zero, Complex.exp_zero, mul_zero, one_div]
  simp only [vsub_eq_sub, smul_eq_mul]
  ring

theorem rectangleIntegral'_perron_eq_one
    {y : Real} (hy : 0 < y) {z w : Complex}
    (hRe : z.re <= w.re) (hIm : z.im <= w.im)
    (hZero : Membership.mem (nhds (0 : Complex)) (Complex.Rectangle z w)) :
    RectangleIntegral' (perronKernelIntegrand y) z w = 1 := by
  apply ResidueTheoremOnRectangleWithSimplePole hRe hIm hZero
    (g := perronKernelRemainder y)
  next =>
    intro s _
    exact (differentiableAt_perronKernelRemainder y s).differentiableWithinAt
  next =>
    exact (perronKernelIntegrand_sub_pole_eq_remainder hy).mono
      (Set.sdiff_subset_compl _ _)

end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

theorem truncatedPerronKernel_sub_one_eq_left_rectangle_terms
    {y c T R : Real} (hy : 0 < y) (hc : 0 < c) (hT : 0 < T)
    (hR : 0 < R) :
    truncatedPerronKernel y c T - 1 =
      -HIntegral' (perronKernelIntegrand y) (-R) c (-T) +
        HIntegral' (perronKernelIntegrand y) (-R) c T +
          VIntegral' (perronKernelIntegrand y) (-R) (-T) T := by
  let z : Complex := ((-R : Real) : Complex) -
    Complex.I * (T : Complex)
  let w : Complex := (c : Complex) + Complex.I * (T : Complex)
  have hIm : z.im <= w.im := by
    dsimp [z, w]
    simp
    linarith
  have hRe : z.re <= w.re := by
    dsimp [z, w]
    simp
    linarith
  have hZero : Membership.mem (nhds (0 : Complex)) (Complex.Rectangle z w) := by
    rw [rectangle_mem_nhds_iff]
    simp only [Complex.mem_reProdIm, z, w, Complex.sub_re, Complex.ofReal_re,
      Complex.mul_re, Complex.I_re, zero_mul, Complex.I_im,
      Complex.ofReal_im, mul_zero, sub_self, sub_zero, Complex.add_re,
      add_zero, Complex.sub_im, Complex.mul_im, one_mul, zero_add,
      zero_sub, Complex.add_im, Complex.zero_re, Complex.zero_im]
    rw [Set.uIoo_of_lt (by linarith), Set.uIoo_of_lt (by linarith)]
    exact And.intro (And.intro (by linarith) hc)
      (And.intro (by linarith) hT)
  have hResidue := rectangleIntegral'_perron_eq_one hy hRe hIm hZero
  simp only [z, w, RectangleIntegral', RectangleIntegral, smul_eq_mul,
    Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    zero_mul, Complex.I_im, Complex.ofReal_im, mul_zero, sub_self,
    sub_zero, Complex.add_re, add_zero, Complex.sub_im, Complex.mul_im,
    one_mul, zero_add, zero_sub, Complex.add_im] at hResidue
  simp only [truncatedPerronKernel, HIntegral', VIntegral', smul_eq_mul]
  linear_combination hResidue

end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

open Filter Topology

namespace BombieriVinogradov.SiegelWalfisz

private lemma norm_perron_left_vertical_integrand_le_bv420
    {y R t : Real} (hy : 0 < y) (hR : 0 < R) :
    norm (perronKernelIntegrand y
      (((-R : Real) : Complex) + (t : Complex) * Complex.I)) <=
      y ^ (-R) / R := by
  rw [norm_perronKernelIntegrand hy]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]
  have hLower : R <=
      norm (((-R : Real) : Complex) + (t : Complex) * Complex.I) := by
    have hAbs := Complex.abs_re_le_norm
      (((-R : Real) : Complex) + (t : Complex) * Complex.I)
    simpa [abs_of_pos hR] using hAbs
  exact div_le_div_of_nonneg_left (Real.rpow_nonneg hy.le (-R)) hR hLower

theorem norm_vIntegral'_perron_left_le
    {y R T : Real} (hy : 0 < y) (hR : 0 < R) (hT : 0 <= T) :
    norm (VIntegral' (perronKernelIntegrand y) (-R) (-T) T) <=
      (T / Real.pi) * (y ^ (-R) / R) := by
  rw [VIntegral', norm_smul]
  have hRaw :
      norm (VIntegral (perronKernelIntegrand y) (-R) (-T) T) <=
        2 * T * (y ^ (-R) / R) := by
    rw [VIntegral, norm_smul]
    simp only [Complex.norm_I, one_mul]
    have hIntegral := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := -T) (b := T)
      (f := fun t : Real => perronKernelIntegrand y
        (((-R : Real) : Complex) + (t : Complex) * Complex.I))
      (C := y ^ (-R) / R)
      (fun t _ => norm_perron_left_vertical_integrand_le_bv420 hy hR)
    calc
      norm
          (intervalIntegral
            (fun t : Real => perronKernelIntegrand y
              (((-R : Real) : Complex) + (t : Complex) * Complex.I))
            (-T) T MeasureTheory.volume) <=
          (y ^ (-R) / R) * abs (T - -T) := hIntegral
      _ = 2 * T * (y ^ (-R) / R) := by
        rw [abs_of_nonneg (by linarith)]
        ring
  calc
    norm (1 / (2 * (Real.pi : Complex) * Complex.I)) *
        norm (VIntegral (perronKernelIntegrand y) (-R) (-T) T) <=
        norm (1 / (2 * (Real.pi : Complex) * Complex.I)) *
          (2 * T * (y ^ (-R) / R)) := by
      gcongr
    _ = (T / Real.pi) * (y ^ (-R) / R) := by
      rw [norm_div, norm_one, norm_mul, norm_mul]
      simp [Complex.norm_I, abs_of_pos Real.pi_pos]
      field_simp [ne_of_gt Real.pi_pos]

theorem tendsto_vIntegral'_perron_left_atTop
    {y T : Real} (hy1 : 1 < y) (hT : 0 <= T) :
    Tendsto (fun R : Real =>
      VIntegral' (perronKernelIntegrand y) (-R) (-T) T) atTop (nhds 0) := by
  have hy : 0 < y := lt_trans Real.zero_lt_one hy1
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hY : Tendsto (fun R : Real => y ^ (-R)) atTop (nhds 0) :=
    (tendsto_rpow_atBot_of_base_gt_one y hy1).comp tendsto_neg_atTop_atBot
  have hInv : Tendsto (fun R : Real => Inv.inv R) atTop (nhds 0) :=
    tendsto_inv_atTop_zero
  have hMajorant :
      Tendsto (fun R : Real => (T / Real.pi) * (y ^ (-R) / R))
        atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using (hY.mul hInv).const_mul (T / Real.pi)
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ hMajorant
  filter_upwards [eventually_gt_atTop (0 : Real)] with R hR
  exact norm_vIntegral'_perron_left_le hy hR hT

end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

open Filter Topology

namespace BombieriVinogradov.SiegelWalfisz

theorem truncatedPerronKernel_sub_one_eq_leftHorizontalIntegrals
    {y c T : Real} (hy1 : 1 < y) (hc : 0 < c) (hT : 0 < T) :
    truncatedPerronKernel y c T - 1 =
      -(1 / (2 * Real.pi * Complex.I) : Complex) *
          leftHorizontalIntegral y c (-T) +
        (1 / (2 * Real.pi * Complex.I) : Complex) *
          leftHorizontalIntegral y c T := by
  have hy : 0 < y := lt_trans Real.zero_lt_one hy1
  have hMinusAbs : 0 < abs (-T) :=
    abs_pos.mpr (neg_ne_zero.mpr hT.ne')
  have hPlusAbs : 0 < abs T := abs_pos.mpr hT.ne'
  have hBottom := tendsto_hIntegral'_left_atTop
    (c := c) hy1 hMinusAbs
  have hTop := tendsto_hIntegral'_left_atTop
    (c := c) hy1 hPlusAbs
  have hLeft := tendsto_vIntegral'_perron_left_atTop hy1 hT.le
  have hCombined := (hBottom.neg.add hTop).add hLeft
  have hFinite : Filter.Eventually
      (fun R : Real => truncatedPerronKernel y c T - 1 =
        -HIntegral' (perronKernelIntegrand y) (-R) c (-T) +
          HIntegral' (perronKernelIntegrand y) (-R) c T +
            VIntegral' (perronKernelIntegrand y) (-R) (-T) T) atTop := by
    filter_upwards [eventually_gt_atTop (0 : Real)] with R hR
    exact truncatedPerronKernel_sub_one_eq_left_rectangle_terms hy hc hT hR
  have hConst : Tendsto
      (fun _ : Real => truncatedPerronKernel y c T - 1) atTop
      (nhds
        (-(1 / (2 * Real.pi * Complex.I) : Complex) *
            leftHorizontalIntegral y c (-T) +
          (1 / (2 * Real.pi * Complex.I) : Complex) *
            leftHorizontalIntegral y c T)) := by
    have hCombined' : Tendsto
        (fun R : Real =>
          -HIntegral' (perronKernelIntegrand y) (-R) c (-T) +
            HIntegral' (perronKernelIntegrand y) (-R) c T +
              VIntegral' (perronKernelIntegrand y) (-R) (-T) T)
        atTop
        (nhds
          (-(1 / (2 * Real.pi * Complex.I) : Complex) *
              leftHorizontalIntegral y c (-T) +
            (1 / (2 * Real.pi * Complex.I) : Complex) *
              leftHorizontalIntegral y c T)) := by
      simpa using hCombined
    apply hCombined'.congr'
    filter_upwards [hFinite] with R hR
    exact hR.symm
  exact tendsto_nhds_unique tendsto_const_nhds hConst

end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

theorem norm_truncatedPerronKernel_sub_one_lt_log_bound
    {y c T : Real} (hy1 : 1 < y) (hc : 0 < c) (hT : 0 < T) :
    norm (truncatedPerronKernel y c T - 1) <
      y ^ c / (Real.pi * T * abs (Real.log y)) := by
  let a : Complex := 1 / (2 * Real.pi * Complex.I)
  let B : Real := y ^ c / (T * abs (Real.log y))
  have hMinusAbs : 0 < abs (-T) :=
    abs_pos.mpr (neg_ne_zero.mpr hT.ne')
  have hPlusAbs : 0 < abs T := abs_pos.mpr hT.ne'
  have hMinus : norm (leftHorizontalIntegral y c (-T)) < B := by
    simpa [B, leftHorizontalIntegral, abs_of_pos hT] using
      (norm_integral_perron_horizontal_Iic_lt hy1 hc hMinusAbs)
  have hPlus : norm (leftHorizontalIntegral y c T) < B := by
    simpa [B, leftHorizontalIntegral, abs_of_pos hT] using
      (norm_integral_perron_horizontal_Iic_lt hy1 hc hPlusAbs)
  have hCoeff : norm a = 1 / (2 * Real.pi) := by
    dsimp [a]
    rw [norm_div, norm_one, norm_mul, norm_mul]
    simp [Complex.norm_I, abs_of_pos Real.pi_pos]
  have hCoeffPos : 0 < norm a := by
    rw [hCoeff]
    positivity
  rw [truncatedPerronKernel_sub_one_eq_leftHorizontalIntegrals hy1 hc hT]
  change norm
      (-a * leftHorizontalIntegral y c (-T) +
        a * leftHorizontalIntegral y c T) < _
  calc
    norm
        (-a * leftHorizontalIntegral y c (-T) +
          a * leftHorizontalIntegral y c T) <=
        norm (-a * leftHorizontalIntegral y c (-T)) +
          norm (a * leftHorizontalIntegral y c T) := norm_add_le _ _
    _ = norm a * norm (leftHorizontalIntegral y c (-T)) +
          norm a * norm (leftHorizontalIntegral y c T) := by
      rw [norm_mul, norm_mul, norm_neg]
    _ < norm a * B + norm a * B := by
      exact add_lt_add (mul_lt_mul_of_pos_left hMinus hCoeffPos)
        (mul_lt_mul_of_pos_left hPlus hCoeffPos)
    _ = y ^ c / (Real.pi * T * abs (Real.log y)) := by
      rw [hCoeff]
      dsimp [B]
      field_simp [ne_of_gt Real.pi_pos]
      ring

end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

theorem circleIntegral_perronKernelIntegrand_eq
    {y R : Real} (hy : 0 < y) (hR : 0 < R) :
    circleIntegral (perronKernelIntegrand y) 0 R =
      2 * Real.pi * Complex.I := by
  let h : Complex -> Complex := fun z =>
    Complex.exp ((Real.log y : Complex) * z)
  have hd : DifferentiableOn Complex h (Metric.closedBall 0 R) := by
    intro z _
    dsimp [h]
    fun_prop
  have hw : Metric.ball (0 : Complex) R 0 := Metric.mem_ball_self hR
  have hC := hd.circleIntegral_sub_inv_smul hw
  have hEq : perronKernelIntegrand y =
      fun z : Complex => Inv.inv (z - 0) * h z := by
    funext z
    rw [perronKernelIntegrand_eq_exp hy]
    dsimp [h]
    simp [div_eq_mul_inv, mul_comm]
  rw [hEq]
  simpa [smul_eq_mul, h] using hC

end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

def perronRightArcRadius (c T : Real) : Real := Real.sqrt (c ^ 2 + T ^ 2)

def perronRightArcAngle (c T : Real) : Real := Real.arctan (T / c)

def perronRightArc (c T theta : Real) : Complex :=
  circleMap 0 (perronRightArcRadius c T) theta

private lemma sqrt_one_add_div_sq_bv424
    {c T : Real} (hc : 0 < c) :
    Real.sqrt (1 + (T / c) ^ 2) = perronRightArcRadius c T / c := by
  rw [show 1 + (T / c) ^ 2 = (c ^ 2 + T ^ 2) / c ^ 2 by
    field_simp]
  rw [Real.sqrt_div (by positivity)]
  rw [Real.sqrt_sq_eq_abs, abs_of_pos hc]
  rfl

theorem perronRightArc_angle
    {c T : Real} (hc : 0 < c) :
    perronRightArc c T (perronRightArcAngle c T) =
      (c : Complex) + (T : Complex) * Complex.I := by
  have hRoot := sqrt_one_add_div_sq_bv424 (T := T) hc
  apply Complex.ext
  next =>
    simp only [perronRightArc, circleMap_zero_re, perronRightArcAngle,
      Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]
    rw [Real.cos_arctan, hRoot]
    field_simp [ne_of_gt (show 0 < perronRightArcRadius c T by
      dsimp [perronRightArcRadius]
      positivity)]
  next =>
    simp only [perronRightArc, circleMap_zero_im, perronRightArcAngle,
      Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im,
      mul_one, Complex.ofReal_re, Complex.I_re, mul_zero, add_zero]
    rw [Real.sin_arctan, hRoot]
    field_simp [ne_of_gt (show 0 < perronRightArcRadius c T by
      dsimp [perronRightArcRadius]
      positivity)]
    ring

theorem perronRightArc_neg_angle
    {c T : Real} (hc : 0 < c) :
    perronRightArc c T (-perronRightArcAngle c T) =
      (c : Complex) - (T : Complex) * Complex.I := by
  have hPlus := perronRightArc_angle (T := T) hc
  apply Complex.ext
  next =>
    simp only [perronRightArc, circleMap_zero_re, Complex.sub_re,
      Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_self]
    rw [Real.cos_neg]
    simpa [perronRightArc, circleMap_zero_re] using congrArg Complex.re hPlus
  next =>
    simp only [perronRightArc, circleMap_zero_im, Complex.sub_im,
      Complex.ofReal_im, Complex.mul_im, Complex.I_im, mul_one,
      Complex.ofReal_re, Complex.I_re, mul_zero, zero_sub]
    rw [Real.sin_neg]
    have hIm : perronRightArcRadius c T *
        Real.sin (perronRightArcAngle c T) = T := by
      simpa [perronRightArc, circleMap_zero_im] using congrArg Complex.im hPlus
    nlinarith

theorem perronRightArc_re_ge
    {c T theta : Real} (hc : 0 < c) (hT : 0 < T)
    (htheta : Set.uIcc (-perronRightArcAngle c T)
      (perronRightArcAngle c T) theta) :
    c <= (perronRightArc c T theta).re := by
  have hAnglePos : 0 < perronRightArcAngle c T := by
    rw [perronRightArcAngle]
    exact Real.arctan_pos.mpr (div_pos hT hc)
  have hThetaBounds :
      And (-perronRightArcAngle c T <= theta)
        (theta <= perronRightArcAngle c T) := by
    rw [Set.uIcc_of_le (by linarith :
      -perronRightArcAngle c T <= perronRightArcAngle c T)] at htheta
    change And (-perronRightArcAngle c T <= theta)
      (theta <= perronRightArcAngle c T) at htheta
    exact htheta
  have hAbs : abs theta <= perronRightArcAngle c T :=
    abs_le.mpr hThetaBounds
  have hAnglePi : perronRightArcAngle c T <= Real.pi :=
    (Real.arctan_lt_pi_div_two _).le.trans (by linarith [Real.pi_pos])
  have hCos :
      Real.cos (perronRightArcAngle c T) <= Real.cos theta := by
    have hCosAbs := Real.cos_le_cos_of_nonneg_of_le_pi
      (abs_nonneg theta) hAnglePi hAbs
    simpa using hCosAbs
  have hRadius : 0 <= perronRightArcRadius c T := by
    dsimp [perronRightArcRadius]
    positivity
  have hEndpointRe :
      perronRightArcRadius c T * Real.cos (perronRightArcAngle c T) = c := by
    simpa [perronRightArc, circleMap_zero_re] using
      congrArg Complex.re (perronRightArc_angle (T := T) hc)
  have hMul := mul_le_mul_of_nonneg_left hCos hRadius
  simpa [perronRightArc, circleMap_zero_re, hEndpointRe] using hMul

end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

def perronLeftArc (c T theta : Real) : Complex :=
  circleMap 0 (perronRightArcRadius c T) theta

theorem perronLeftArc_re_le
    {c T theta : Real} (hc : 0 < c) (hT : 0 < T)
    (htheta : Set.uIcc (perronRightArcAngle c T)
      (2 * Real.pi - perronRightArcAngle c T) theta) :
    (perronLeftArc c T theta).re <= c := by
  have hAnglePos : 0 < perronRightArcAngle c T := by
    rw [perronRightArcAngle]
    exact Real.arctan_pos.mpr (div_pos hT hc)
  have hAngleLt : perronRightArcAngle c T < Real.pi / 2 :=
    Real.arctan_lt_pi_div_two _
  have hOrdered : perronRightArcAngle c T <=
      2 * Real.pi - perronRightArcAngle c T := by
    linarith [Real.pi_pos]
  have hBounds :
      And (perronRightArcAngle c T <= theta)
        (theta <= 2 * Real.pi - perronRightArcAngle c T) := by
    rw [Set.uIcc_of_le hOrdered] at htheta
    exact htheta
  have hCos : Real.cos theta <= Real.cos (perronRightArcAngle c T) := by
    rcases le_total theta Real.pi with hThetaPi | hPiTheta
    next =>
      exact Real.cos_le_cos_of_nonneg_of_le_pi hAnglePos.le hThetaPi hBounds.1
    next =>
      have hPhiNonneg : 0 <= 2 * Real.pi - theta := by
        linarith [hBounds.2, hAnglePos]
      have hPhiPi : 2 * Real.pi - theta <= Real.pi := by linarith
      have hAnglePhi : perronRightArcAngle c T <=
          2 * Real.pi - theta := by linarith
      have hCosPhi := Real.cos_le_cos_of_nonneg_of_le_pi
        hAnglePos.le hPhiPi hAnglePhi
      simpa [Real.cos_two_pi_sub] using hCosPhi
  have hRadius : 0 <= perronRightArcRadius c T := by
    dsimp [perronRightArcRadius]
    positivity
  have hEndpointRe :
      perronRightArcRadius c T * Real.cos (perronRightArcAngle c T) = c := by
    simpa [perronRightArc, circleMap_zero_re] using
      congrArg Complex.re (perronRightArc_angle (T := T) hc)
  have hMul := mul_le_mul_of_nonneg_left hCos hRadius
  simpa [perronLeftArc, circleMap_zero_re, hEndpointRe] using hMul

theorem perronLeftArc_length_lt_two_pi
    {c T : Real} (hc : 0 < c) (hT : 0 < T) :
    (2 * Real.pi - perronRightArcAngle c T) -
        perronRightArcAngle c T < 2 * Real.pi := by
  have hAnglePos : 0 < perronRightArcAngle c T := by
    rw [perronRightArcAngle]
    exact Real.arctan_pos.mpr (div_pos hT hc)
  linarith

end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

def perronRightArcIntegral (y c T : Real) : Complex :=
  intervalIntegral
    (fun theta : Real =>
      (perronRightArc c T theta * Complex.I) *
        perronKernelIntegrand y (perronRightArc c T theta))
    (-perronRightArcAngle c T) (perronRightArcAngle c T)
    MeasureTheory.volume

private lemma continuous_perron_vertical_derivative_bv426
    {y c : Real} (hy : 0 < y) (hc : 0 < c) :
    Continuous
      (fun t : Real =>
        Complex.I * perronKernelIntegrand y
          ((c : Complex) + (t : Complex) * Complex.I)) := by
  have hEq :
      (fun t : Real =>
        Complex.I * perronKernelIntegrand y
          ((c : Complex) + (t : Complex) * Complex.I)) =
        fun t : Real => Complex.I *
          (Complex.exp
              ((Real.log y : Complex) *
                ((c : Complex) + (t : Complex) * Complex.I)) /
            ((c : Complex) + (t : Complex) * Complex.I)) := by
    funext t
    rw [perronKernelIntegrand_eq_exp hy]
  rw [hEq]
  fun_prop (disch :=
    intro t hzero
    have hReal := congrArg Complex.re hzero
    simp at hReal
    exact hc.ne' hReal)

private lemma continuous_perron_arc_derivative_bv426
    {y c T : Real} (hy : 0 < y) (hc : 0 < c) :
    Continuous
      (fun theta : Real =>
        (perronRightArc c T theta * Complex.I) *
          perronKernelIntegrand y (perronRightArc c T theta)) := by
  have hRadius : Ne (perronRightArcRadius c T) 0 := by
    apply ne_of_gt
    dsimp [perronRightArcRadius]
    positivity
  have hEq :
      (fun theta : Real =>
        (perronRightArc c T theta * Complex.I) *
          perronKernelIntegrand y (perronRightArc c T theta)) =
        fun theta : Real =>
          (perronRightArc c T theta * Complex.I) *
            (Complex.exp
                ((Real.log y : Complex) * perronRightArc c T theta) /
              perronRightArc c T theta) := by
    funext theta
    rw [perronKernelIntegrand_eq_exp hy]
  rw [hEq]
  simp only [perronRightArc]
  fun_prop (disch :=
    intro theta hzero
    have hCircleNe : Ne (circleMap 0 (perronRightArcRadius c T) theta) 0 :=
      circleMap_ne_center hRadius
    exact hCircleNe (by simpa [perronRightArc] using hzero))

theorem vIntegral_eq_perronRightArcIntegral
    {y c T : Real} (hy : 0 < y) (hc : 0 < c) (hT : 0 < T) :
    VIntegral (perronKernelIntegrand y) c (-T) T =
      perronRightArcIntegral y c T := by
  let S : Set Complex := {z : Complex | 0 < z.re}
  have hConvex : Convex Real S := by
    simpa [S] using convex_halfSpace_re_gt (0 : Real)
  have hOpen : IsOpen S := by
    dsimp [S]
    exact isOpen_lt continuous_const Complex.continuous_re
  choose F hF using hConvex.exists_forall_hasDerivWithinAt
    (holomorphicOn_perronKernelIntegrand hy)
  let vertical : Real -> Complex :=
    fun t => (c : Complex) + (t : Complex) * Complex.I
  have hVerticalMem (t : Real) : S (vertical t) := by
    change 0 < (vertical t).re
    simp [vertical, hc]
  have hVerticalDeriv (t : Real) :
      HasDerivAt (Function.comp F vertical)
        (Complex.I * perronKernelIntegrand y (vertical t)) t := by
    have hFAt := (hF (vertical t) (hVerticalMem t)).hasDerivAt
      (hOpen.mem_nhds (hVerticalMem t))
    have hPath : HasDerivAt vertical Complex.I t := by
      simpa [vertical] using
        (((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const Complex.I).const_add
          (c : Complex))
    simpa [smul_eq_mul, mul_comm] using hFAt.scomp t hPath
  have hVerticalFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := -T) (b := T)
    (f := Function.comp F vertical)
    (f' := fun t : Real =>
      Complex.I * perronKernelIntegrand y (vertical t))
    (fun t _ => hVerticalDeriv t)
    (by
      simpa [vertical] using
        (continuous_perron_vertical_derivative_bv426 hy hc).intervalIntegrable (-T) T)
  have hArcMem (theta : Real)
      (htheta : Set.uIcc (-perronRightArcAngle c T)
        (perronRightArcAngle c T) theta) :
      S (perronRightArc c T theta) := by
    change 0 < (perronRightArc c T theta).re
    exact hc.trans_le (perronRightArc_re_ge hc hT htheta)
  have hArcDeriv (theta : Real)
      (htheta : Set.uIcc (-perronRightArcAngle c T)
        (perronRightArcAngle c T) theta) :
      HasDerivAt (Function.comp F (perronRightArc c T))
        ((perronRightArc c T theta * Complex.I) *
          perronKernelIntegrand y (perronRightArc c T theta)) theta := by
    have hFAt := (hF (perronRightArc c T theta) (hArcMem theta htheta)).hasDerivAt
      (hOpen.mem_nhds (hArcMem theta htheta))
    have hPath : HasDerivAt (perronRightArc c T)
        (perronRightArc c T theta * Complex.I) theta := by
      change HasDerivAt (circleMap 0 (perronRightArcRadius c T))
        (circleMap 0 (perronRightArcRadius c T) theta * Complex.I) theta
      exact hasDerivAt_circleMap 0 (perronRightArcRadius c T) theta
    simpa [smul_eq_mul] using hFAt.scomp theta hPath
  have hArcFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := -perronRightArcAngle c T) (b := perronRightArcAngle c T)
    (f := Function.comp F (perronRightArc c T))
    (f' := fun theta : Real =>
      (perronRightArc c T theta * Complex.I) *
        perronKernelIntegrand y (perronRightArc c T theta))
    hArcDeriv
    (by
      exact (continuous_perron_arc_derivative_bv426 (T := T) hy hc).intervalIntegrable
        (-perronRightArcAngle c T) (perronRightArcAngle c T))
  rw [VIntegral, smul_eq_mul]
  have hVerticalValue :
      Complex.I * intervalIntegral
        (fun t : Real => perronKernelIntegrand y
          ((c : Complex) + (t : Complex) * Complex.I))
        (-T) T MeasureTheory.volume =
        Function.comp F vertical T - Function.comp F vertical (-T) := by
    rw [<- intervalIntegral.integral_const_mul]
    simpa [vertical] using hVerticalFTC
  rw [hVerticalValue]
  rw [perronRightArcIntegral, hArcFTC]
  simp only [Function.comp_apply, vertical]
  rw [perronRightArc_angle hc, perronRightArc_neg_angle hc]
  have hLower :
      (c : Complex) + ((-T : Real) : Complex) * Complex.I =
        (c : Complex) - (T : Complex) * Complex.I := by
    push_cast
    ring
  rw [hLower]

end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

def perronLeftArcIntegral (y c T : Real) : Complex :=
  intervalIntegral
    (fun theta : Real =>
      (perronLeftArc c T theta * Complex.I) *
        perronKernelIntegrand y (perronLeftArc c T theta))
    (perronRightArcAngle c T)
    (2 * Real.pi - perronRightArcAngle c T)
    MeasureTheory.volume

private lemma continuous_perron_circle_integrand_bv427
    {y c T : Real} (hy : 0 < y) (hc : 0 < c) :
    Continuous
      (fun theta : Real =>
        (perronLeftArc c T theta * Complex.I) *
          perronKernelIntegrand y (perronLeftArc c T theta)) := by
  have hRadius : Ne (perronRightArcRadius c T) 0 := by
    apply ne_of_gt
    dsimp [perronRightArcRadius]
    positivity
  have hEq :
      (fun theta : Real =>
        (perronLeftArc c T theta * Complex.I) *
          perronKernelIntegrand y (perronLeftArc c T theta)) =
        fun theta : Real =>
          (perronLeftArc c T theta * Complex.I) *
            (Complex.exp
                ((Real.log y : Complex) * perronLeftArc c T theta) /
              perronLeftArc c T theta) := by
    funext theta
    rw [perronKernelIntegrand_eq_exp hy]
  rw [hEq]
  simp only [perronLeftArc]
  fun_prop (disch :=
    intro theta hzero
    have hCircleNe : Ne (circleMap 0 (perronRightArcRadius c T) theta) 0 :=
      circleMap_ne_center hRadius
    exact hCircleNe hzero)

theorem perronArcIntegrals_add_eq_circleIntegral
    {y c T : Real} (hy : 0 < y) (hc : 0 < c) :
    perronRightArcIntegral y c T + perronLeftArcIntegral y c T =
      circleIntegral (perronKernelIntegrand y) 0 (perronRightArcRadius c T) := by
  let a := perronRightArcAngle c T
  let b := 2 * Real.pi - a
  let q : Real -> Complex := fun theta =>
    (perronLeftArc c T theta * Complex.I) *
      perronKernelIntegrand y (perronLeftArc c T theta)
  have hCont : Continuous q := by
    simpa [q] using continuous_perron_circle_integrand_bv427 (T := T) hy hc
  have hPeriodic : Function.Periodic q (2 * Real.pi) := by
    intro theta
    dsimp [q, perronLeftArc]
    have hCircle := periodic_circleMap 0 (perronRightArcRadius c T) theta
    rw [hCircle]
  have hShiftBase := intervalIntegral.integral_comp_add_right
    (f := q) (a := -a) (b := 0) (2 * Real.pi)
  have hShift :
      intervalIntegral q (-a) 0 MeasureTheory.volume =
        intervalIntegral q b (2 * Real.pi) MeasureTheory.volume := by
    calc
      intervalIntegral q (-a) 0 MeasureTheory.volume =
          intervalIntegral (fun theta => q (theta + 2 * Real.pi))
            (-a) 0 MeasureTheory.volume := by
        apply intervalIntegral.integral_congr
        intro theta _
        exact (hPeriodic theta).symm
      _ = intervalIntegral q (-a + 2 * Real.pi)
          (0 + 2 * Real.pi) MeasureTheory.volume := hShiftBase
      _ = intervalIntegral q b (2 * Real.pi) MeasureTheory.volume := by
        dsimp [b]
        congr 1 <;> ring
  have hIntNegZero : IntervalIntegrable q MeasureTheory.volume (-a) 0 :=
    hCont.intervalIntegrable (-a) 0
  have hIntZeroA : IntervalIntegrable q MeasureTheory.volume 0 a :=
    hCont.intervalIntegrable 0 a
  have hIntAB : IntervalIntegrable q MeasureTheory.volume a b :=
    hCont.intervalIntegrable a b
  have hIntZeroB : IntervalIntegrable q MeasureTheory.volume 0 b :=
    hCont.intervalIntegrable 0 b
  have hIntBFull : IntervalIntegrable q MeasureTheory.volume b (2 * Real.pi) :=
    hCont.intervalIntegrable b (2 * Real.pi)
  have hRightSplit := intervalIntegral.integral_add_adjacent_intervals
    hIntNegZero hIntZeroA
  have hMiddleSplit := intervalIntegral.integral_add_adjacent_intervals
    hIntZeroA hIntAB
  have hFullSplit := intervalIntegral.integral_add_adjacent_intervals
    hIntZeroB hIntBFull
  rw [perronRightArcIntegral, perronLeftArcIntegral, circleIntegral]
  simp only [deriv_circleMap, smul_eq_mul, perronRightArc, perronLeftArc]
  change intervalIntegral q (-a) a MeasureTheory.volume +
      intervalIntegral q a b MeasureTheory.volume =
    intervalIntegral q 0 (2 * Real.pi) MeasureTheory.volume
  calc
    intervalIntegral q (-a) a MeasureTheory.volume +
        intervalIntegral q a b MeasureTheory.volume =
        (intervalIntegral q (-a) 0 MeasureTheory.volume +
          intervalIntegral q 0 a MeasureTheory.volume) +
            intervalIntegral q a b MeasureTheory.volume := by
      rw [hRightSplit]
    _ = (intervalIntegral q b (2 * Real.pi) MeasureTheory.volume +
          intervalIntegral q 0 a MeasureTheory.volume) +
            intervalIntegral q a b MeasureTheory.volume := by
      rw [hShift]
    _ = (intervalIntegral q 0 a MeasureTheory.volume +
          intervalIntegral q a b MeasureTheory.volume) +
            intervalIntegral q b (2 * Real.pi) MeasureTheory.volume := by
      abel
    _ = intervalIntegral q 0 b MeasureTheory.volume +
          intervalIntegral q b (2 * Real.pi) MeasureTheory.volume := by
      rw [hMiddleSplit]
    _ = intervalIntegral q 0 (2 * Real.pi) MeasureTheory.volume := hFullSplit

theorem truncatedPerronKernel_sub_one_eq_neg_leftArc
    {y c T : Real} (hy1 : 1 < y) (hc : 0 < c) (hT : 0 < T) :
    truncatedPerronKernel y c T - 1 =
      -(1 / (2 * Real.pi * Complex.I) : Complex) *
        perronLeftArcIntegral y c T := by
  have hy : 0 < y := lt_trans Real.zero_lt_one hy1
  have hRadius : 0 < perronRightArcRadius c T := by
    dsimp [perronRightArcRadius]
    positivity
  have hRaw :
      VIntegral (perronKernelIntegrand y) c (-T) T +
          perronLeftArcIntegral y c T =
        2 * Real.pi * Complex.I := by
    calc
      VIntegral (perronKernelIntegrand y) c (-T) T +
          perronLeftArcIntegral y c T =
          perronRightArcIntegral y c T +
            perronLeftArcIntegral y c T := by
        rw [vIntegral_eq_perronRightArcIntegral hy hc hT]
      _ = circleIntegral (perronKernelIntegrand y) 0
          (perronRightArcRadius c T) :=
        perronArcIntegrals_add_eq_circleIntegral hy hc
      _ = 2 * Real.pi * Complex.I :=
        circleIntegral_perronKernelIntegrand_eq hy hRadius
  let a : Complex := 1 / (2 * Real.pi * Complex.I)
  have hNormalize : a * (2 * Real.pi * Complex.I) = 1 := by
    dsimp [a]
    field_simp [ne_of_gt Real.pi_pos, Complex.I_ne_zero]
  rw [truncatedPerronKernel, VIntegral', smul_eq_mul]
  change a * VIntegral (perronKernelIntegrand y) c (-T) T - 1 =
    -a * perronLeftArcIntegral y c T
  rw [<- hNormalize]
  linear_combination a * hRaw

end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

theorem norm_perronRightArc_integrand
    {y c T theta : Real} (hy : 0 < y) (hc : 0 < c) :
    norm ((perronRightArc c T theta * Complex.I) *
      perronKernelIntegrand y (perronRightArc c T theta)) =
      y ^ (perronRightArc c T theta).re := by
  have hRadius : 0 < perronRightArcRadius c T := by
    dsimp [perronRightArcRadius]
    positivity
  have hNorm : norm (perronRightArc c T theta) = perronRightArcRadius c T := by
    rw [perronRightArc, norm_circleMap_zero, abs_of_pos hRadius]
  rw [norm_mul, norm_mul, Complex.norm_I,
    norm_perronKernelIntegrand hy, hNorm]
  field_simp

theorem norm_perronRightArc_integrand_le
    {y c T theta : Real} (hy : 0 < y) (hy1 : y < 1)
    (hc : 0 < c) (hT : 0 < T)
    (htheta : Set.uIcc (-perronRightArcAngle c T)
      (perronRightArcAngle c T) theta) :
    norm ((perronRightArc c T theta * Complex.I) *
      perronKernelIntegrand y (perronRightArc c T theta)) <= y ^ c := by
  rw [norm_perronRightArc_integrand hy hc]
  exact Real.rpow_le_rpow_of_exponent_ge hy hy1.le
    (perronRightArc_re_ge hc hT htheta)

theorem norm_perronRightArcIntegral_le
    {y c T : Real} (hy : 0 < y) (hy1 : y < 1)
    (hc : 0 < c) (hT : 0 < T) :
    norm (perronRightArcIntegral y c T) <=
      y ^ c * abs (perronRightArcAngle c T -
        (-perronRightArcAngle c T)) := by
  rw [perronRightArcIntegral]
  exact intervalIntegral.norm_integral_le_of_norm_le_const
    (fun theta htheta =>
      norm_perronRightArc_integrand_le hy hy1 hc hT
        (Set.uIoc_subset_uIcc htheta))

theorem norm_perronRightArcIntegral_lt_pi_mul
    {y c T : Real} (hy : 0 < y) (hy1 : y < 1)
    (hc : 0 < c) (hT : 0 < T) :
    norm (perronRightArcIntegral y c T) < Real.pi * y ^ c := by
  have hAnglePos : 0 < perronRightArcAngle c T := by
    rw [perronRightArcAngle]
    exact Real.arctan_pos.mpr (div_pos hT hc)
  have hAngleLt : perronRightArcAngle c T < Real.pi / 2 := by
    exact Real.arctan_lt_pi_div_two (T / c)
  have hLength :
      abs (perronRightArcAngle c T -
        (-perronRightArcAngle c T)) < Real.pi := by
    rw [abs_of_pos (by linarith)]
    linarith
  calc
    norm (perronRightArcIntegral y c T) <=
        y ^ c * abs (perronRightArcAngle c T -
          (-perronRightArcAngle c T)) :=
      norm_perronRightArcIntegral_le hy hy1 hc hT
    _ < y ^ c * Real.pi :=
      mul_lt_mul_of_pos_left hLength (Real.rpow_pos_of_pos hy c)
    _ = Real.pi * y ^ c := by ring

end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

theorem norm_perronLeftArc_integrand_le
    {y c T theta : Real} (hy1 : 1 < y) (hc : 0 < c) (hT : 0 < T)
    (htheta : Set.uIcc (perronRightArcAngle c T)
      (2 * Real.pi - perronRightArcAngle c T) theta) :
    norm ((perronLeftArc c T theta * Complex.I) *
      perronKernelIntegrand y (perronLeftArc c T theta)) <= y ^ c := by
  have hy : 0 < y := lt_trans Real.zero_lt_one hy1
  rw [show norm ((perronLeftArc c T theta * Complex.I) *
      perronKernelIntegrand y (perronLeftArc c T theta)) =
      y ^ (perronLeftArc c T theta).re by
    simpa [perronLeftArc, perronRightArc] using
      (norm_perronRightArc_integrand (T := T) (theta := theta) hy hc)]
  exact Real.rpow_le_rpow_of_exponent_le hy1.le
    (perronLeftArc_re_le hc hT htheta)

theorem norm_perronLeftArcIntegral_le
    {y c T : Real} (hy1 : 1 < y) (hc : 0 < c) (hT : 0 < T) :
    norm (perronLeftArcIntegral y c T) <=
      y ^ c * abs ((2 * Real.pi - perronRightArcAngle c T) -
        perronRightArcAngle c T) := by
  rw [perronLeftArcIntegral]
  exact intervalIntegral.norm_integral_le_of_norm_le_const
    (fun theta htheta =>
      norm_perronLeftArc_integrand_le hy1 hc hT
        (Set.uIoc_subset_uIcc htheta))

theorem norm_perronLeftArcIntegral_lt_two_pi_mul
    {y c T : Real} (hy1 : 1 < y) (hc : 0 < c) (hT : 0 < T) :
    norm (perronLeftArcIntegral y c T) < 2 * Real.pi * y ^ c := by
  have hy : 0 < y := lt_trans Real.zero_lt_one hy1
  have hAnglePos : 0 < perronRightArcAngle c T := by
    rw [perronRightArcAngle]
    exact Real.arctan_pos.mpr (div_pos hT hc)
  have hAngleLt : perronRightArcAngle c T < Real.pi / 2 :=
    Real.arctan_lt_pi_div_two _
  have hLengthPos : 0 <
      (2 * Real.pi - perronRightArcAngle c T) -
        perronRightArcAngle c T := by
    linarith [Real.pi_pos]
  have hLength := perronLeftArc_length_lt_two_pi hc hT
  calc
    norm (perronLeftArcIntegral y c T) <=
        y ^ c * abs ((2 * Real.pi - perronRightArcAngle c T) -
          perronRightArcAngle c T) :=
      norm_perronLeftArcIntegral_le hy1 hc hT
    _ = y ^ c * ((2 * Real.pi - perronRightArcAngle c T) -
          perronRightArcAngle c T) := by
      rw [abs_of_pos hLengthPos]
    _ < y ^ c * (2 * Real.pi) :=
      mul_lt_mul_of_pos_left hLength (Real.rpow_pos_of_pos hy c)
    _ = 2 * Real.pi * y ^ c := by ring

end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

theorem norm_truncatedPerronKernel_sub_one_lt_unit_bound
    {y c T : Real} (hy1 : 1 < y) (hc : 0 < c) (hT : 0 < T) :
    norm (truncatedPerronKernel y c T - 1) < y ^ c := by
  let a : Complex := 1 / (2 * Real.pi * Complex.I)
  have hCoeff : norm a = 1 / (2 * Real.pi) := by
    dsimp [a]
    rw [norm_div, norm_one, norm_mul, norm_mul]
    simp [Complex.norm_I, abs_of_pos Real.pi_pos]
  have hCoeffPos : 0 < norm a := by
    rw [hCoeff]
    positivity
  rw [truncatedPerronKernel_sub_one_eq_neg_leftArc hy1 hc hT]
  change norm (-a * perronLeftArcIntegral y c T) < _
  rw [norm_mul, norm_neg]
  calc
    norm a * norm (perronLeftArcIntegral y c T) <
        norm a * (2 * Real.pi * y ^ c) :=
      mul_lt_mul_of_pos_left
        (norm_perronLeftArcIntegral_lt_two_pi_mul hy1 hc hT) hCoeffPos
    _ = y ^ c := by
      rw [hCoeff]
      field_simp [ne_of_gt Real.pi_pos]

end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

theorem norm_truncatedPerronKernel_sub_one_lt_min_bound
    {y c T : Real} (hy1 : 1 < y) (hc : 0 < c) (hT : 0 < T) :
    norm (truncatedPerronKernel y c T - 1) <
      y ^ c * min 1 (1 / (Real.pi * T * abs (Real.log y))) := by
  have hy : 0 < y := lt_trans Real.zero_lt_one hy1
  have hPowerNonneg : 0 <= y ^ c := (Real.rpow_pos_of_pos hy c).le
  rw [mul_min_of_nonneg 1 (1 / (Real.pi * T * abs (Real.log y)))
    hPowerNonneg]
  apply lt_min
  next =>
    simpa using norm_truncatedPerronKernel_sub_one_lt_unit_bound hy1 hc hT
  next =>
    simpa [div_eq_mul_inv] using
      norm_truncatedPerronKernel_sub_one_lt_log_bound hy1 hc hT

theorem norm_truncatedPerronKernel_sub_stepWeight_lt_of_one_lt
    {y c T : Real} (hy1 : 1 < y) (hc : 0 < c) (hT : 0 < T) :
    norm (truncatedPerronKernel y c T -
      (perronStepWeight y : Complex)) <
      y ^ c * min 1 (1 / (Real.pi * T * abs (Real.log y))) := by
  have hWeight : perronStepWeight y = 1 := by
    simp [perronStepWeight, not_lt_of_ge hy1.le, ne_of_gt hy1]
  rw [hWeight, Complex.ofReal_one]
  exact norm_truncatedPerronKernel_sub_one_lt_min_bound hy1 hc hT

end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

open MeasureTheory Set

namespace BombieriVinogradov.SiegelWalfisz

theorem integrableOn_rpow_Ioi
    {y : Real} (hy : 0 < y) (hy1 : y < 1) (c : Real) :
    IntegrableOn (fun x : Real => y ^ x) (Ioi c) := by
  simpa [Real.rpow_def_of_pos hy] using
    integrableOn_exp_mul_Ioi (Real.log_neg hy hy1) c

theorem integral_rpow_Ioi
    {y : Real} (hy : 0 < y) (hy1 : y < 1) (c : Real) :
    integral (volume.restrict (Ioi c)) (fun x : Real => y ^ x) =
      y ^ c / abs (Real.log y) := by
  rw [show (fun x : Real => y ^ x) =
      fun x : Real => Real.exp (Real.log y * x) by
    funext x
    exact Real.rpow_def_of_pos hy x]
  rw [integral_exp_mul_Ioi (Real.log_neg hy hy1)]
  rw [(Real.rpow_def_of_pos hy c).symm]
  rw [abs_of_neg (Real.log_neg hy hy1)]
  ring

end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

open Filter MeasureTheory Set Topology

namespace BombieriVinogradov.SiegelWalfisz

private lemma sqrt_sq_add_sq_le_norm_add_mul_I_bv433
    {c t x : Real} (hc : 0 < c) (hcx : c <= x) :
    Real.sqrt (c ^ 2 + t ^ 2) <=
      norm ((x : Complex) + (t : Complex) * Complex.I) := by
  rw [Complex.norm_def, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero,
    Complex.add_im, Complex.mul_im, zero_add]
  apply Real.sqrt_le_sqrt
  nlinarith

theorem norm_perron_horizontal_le
    {y c t x : Real} (hy : 0 < y) (hc : 0 < c) (hcx : c <= x) :
    norm (perronKernelIntegrand y
      ((x : Complex) + (t : Complex) * Complex.I)) <=
      y ^ x / Real.sqrt (c ^ 2 + t ^ 2) := by
  rw [norm_perronKernelIntegrand hy]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]
  have hLower : Real.sqrt (c ^ 2 + t ^ 2) <=
      norm ((x : Complex) + (t : Complex) * Complex.I) :=
    sqrt_sq_add_sq_le_norm_add_mul_I_bv433 hc hcx
  have hD : 0 < Real.sqrt (c ^ 2 + t ^ 2) := by positivity
  exact div_le_div_of_nonneg_left (Real.rpow_nonneg hy.le x) hD hLower

theorem integrableOn_perron_horizontal_Ioi
    {y c t : Real} (hy : 0 < y) (hy1 : y < 1) (hc : 0 < c) :
    IntegrableOn
      (fun x : Real => perronKernelIntegrand y
        ((x : Complex) + (t : Complex) * Complex.I))
      (Ioi c) := by
  let D : Real := Real.sqrt (c ^ 2 + t ^ 2)
  have hD : 0 < D := by
    dsimp [D]
    positivity
  have hDom : IntegrableOn (fun x : Real => y ^ x / D) (Ioi c) :=
    (integrableOn_rpow_Ioi hy hy1 c).div_const D
  apply hDom.mono'
  next =>
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    intro x hx
    have hEq :
        (fun u : Real => perronKernelIntegrand y
          ((u : Complex) + (t : Complex) * Complex.I)) =
          fun u : Real =>
            Complex.exp
                ((Real.log y : Complex) *
                  ((u : Complex) + (t : Complex) * Complex.I)) /
              ((u : Complex) + (t : Complex) * Complex.I) := by
      funext u
      exact perronKernelIntegrand_eq_exp hy _
    rw [hEq]
    have hNumerator :
        ContinuousAt
          (fun u : Real =>
            Complex.exp
              ((Real.log y : Complex) *
                ((u : Complex) + (t : Complex) * Complex.I))) x := by
      fun_prop
    have hDenominator :
        ContinuousAt
          (fun u : Real => (u : Complex) + (t : Complex) * Complex.I) x := by
      fun_prop
    have hNe : Ne ((x : Complex) + (t : Complex) * Complex.I) 0 := by
      intro hzero
      have hReal := congrArg Complex.re hzero
      simp at hReal
      change c < x at hx
      linarith
    exact (hNumerator.div hDenominator hNe).continuousWithinAt
  next =>
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact norm_perron_horizontal_le hy hc hx.le

theorem norm_integral_perron_horizontal_Ioi_le
    {y c t : Real} (hy : 0 < y) (hy1 : y < 1) (hc : 0 < c) :
    norm
        (integral (volume.restrict (Ioi c))
          (fun x : Real => perronKernelIntegrand y
            ((x : Complex) + (t : Complex) * Complex.I))) <=
      y ^ c /
        (Real.sqrt (c ^ 2 + t ^ 2) * abs (Real.log y)) := by
  let D : Real := Real.sqrt (c ^ 2 + t ^ 2)
  have hDom : IntegrableOn (fun x : Real => y ^ x / D) (Ioi c) :=
    (integrableOn_rpow_Ioi hy hy1 c).div_const D
  have hNorm :
      norm
          (integral (volume.restrict (Ioi c))
            (fun x : Real => perronKernelIntegrand y
              ((x : Complex) + (t : Complex) * Complex.I))) <=
        integral (volume.restrict (Ioi c)) (fun x : Real => y ^ x / D) := by
    apply MeasureTheory.norm_integral_le_of_norm_le hDom
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact norm_perron_horizontal_le hy hc hx.le
  calc
    norm
        (integral (volume.restrict (Ioi c))
          (fun x : Real => perronKernelIntegrand y
            ((x : Complex) + (t : Complex) * Complex.I))) <=
        integral (volume.restrict (Ioi c)) (fun x : Real => y ^ x / D) := hNorm
    _ = (1 / D) * integral (volume.restrict (Ioi c)) (fun x : Real => y ^ x) := by
      rw [show (fun x : Real => y ^ x / D) = fun x : Real => (1 / D) * y ^ x by
        funext x
        ring]
      rw [integral_const_mul]
    _ = y ^ c / (Real.sqrt (c ^ 2 + t ^ 2) * abs (Real.log y)) := by
      rw [integral_rpow_Ioi hy hy1]
      dsimp [D]
      ring

def rightHorizontalIntegral (y c t : Real) : Complex :=
  integral (volume.restrict (Ioi c))
    (fun x : Real => perronKernelIntegrand y
      ((x : Complex) + (t : Complex) * Complex.I))

theorem tendsto_hIntegral'_right_atTop
    {y c t : Real} (hy : 0 < y) (hy1 : y < 1) (hc : 0 < c) :
    Tendsto
      (fun R : Real => HIntegral' (perronKernelIntegrand y) c R t)
      atTop
      (nhds
        ((1 / (2 * Real.pi * Complex.I) : Complex) *
          rightHorizontalIntegral y c t)) := by
  have hLimit := intervalIntegral_tendsto_integral_Ioi
    (f := fun x : Real => perronKernelIntegrand y
      ((x : Complex) + (t : Complex) * Complex.I)) c
    (integrableOn_perron_horizontal_Ioi (t := t) hy hy1 hc) tendsto_id
  simpa [HIntegral', HIntegral, rightHorizontalIntegral, smul_eq_mul] using
    hLimit.const_smul (1 / (2 * Real.pi * Complex.I) : Complex)

end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

theorem vIntegral_eq_right_rectangle_terms
    {y c T R : Real} (hy : 0 < y) (hc : 0 < c) (hT : 0 < T)
    (hcR : c <= R) :
    VIntegral (perronKernelIntegrand y) c (-T) T =
      HIntegral (perronKernelIntegrand y) c R (-T) -
        HIntegral (perronKernelIntegrand y) c R T +
          VIntegral (perronKernelIntegrand y) R (-T) T := by
  let z : Complex := (c : Complex) - Complex.I * (T : Complex)
  let w : Complex := (R : Complex) + Complex.I * (T : Complex)
  have hIm : z.im <= w.im := by
    dsimp [z, w]
    simp
    linarith
  have hRe : z.re <= w.re := by
    simpa [z, w] using hcR
  have hSubset : Complex.Rectangle z w <= {s : Complex | 0 < s.re} := by
    intro s hs
    have hCoords := (mem_Rect hRe hIm s).mp hs
    have hLower : c <= s.re := by
      simpa [z, w] using hCoords.1
    exact hc.trans_le hLower
  have hZero : RectangleIntegral (perronKernelIntegrand y) z w = 0 :=
    (holomorphicOn_perronKernelIntegrand hy).vanishesOnRectangle hSubset
  have hExpanded :
      HIntegral (perronKernelIntegrand y) c R (-T) -
          HIntegral (perronKernelIntegrand y) c R T +
          VIntegral (perronKernelIntegrand y) R (-T) T -
          VIntegral (perronKernelIntegrand y) c (-T) T = 0 := by
    simpa [z, w, RectangleIntegral] using hZero
  linear_combination -hExpanded

theorem truncatedPerronKernel_eq_right_rectangle_terms
    {y c T R : Real} (hy : 0 < y) (hc : 0 < c) (hT : 0 < T)
    (hcR : c <= R) :
    truncatedPerronKernel y c T =
      HIntegral' (perronKernelIntegrand y) c R (-T) -
        HIntegral' (perronKernelIntegrand y) c R T +
          VIntegral' (perronKernelIntegrand y) R (-T) T := by
  simp only [truncatedPerronKernel, HIntegral', VIntegral']
  rw [vIntegral_eq_right_rectangle_terms hy hc hT hcR]
  module

end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

open Filter Topology

namespace BombieriVinogradov.SiegelWalfisz

private lemma norm_perron_vertical_integrand_le_bv435
    {y R t : Real} (hy : 0 < y) (hR : 0 < R) :
    norm (perronKernelIntegrand y
      ((R : Complex) + (t : Complex) * Complex.I)) <= y ^ R / R := by
  rw [norm_perronKernelIntegrand hy]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]
  have hLower : R <= norm ((R : Complex) + (t : Complex) * Complex.I) := by
    simpa using Complex.re_le_norm ((R : Complex) + (t : Complex) * Complex.I)
  exact div_le_div_of_nonneg_left (Real.rpow_nonneg hy.le R) hR hLower

theorem norm_vIntegral_perron_right_le
    {y R T : Real} (hy : 0 < y) (hR : 0 < R) (hT : 0 <= T) :
    norm (VIntegral (perronKernelIntegrand y) R (-T) T) <=
      2 * T * (y ^ R / R) := by
  rw [VIntegral, norm_smul]
  simp only [Complex.norm_I, one_mul]
  have hIntegral := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := -T) (b := T)
    (f := fun t : Real => perronKernelIntegrand y
      ((R : Complex) + (t : Complex) * Complex.I))
    (C := y ^ R / R)
    (fun t _ => norm_perron_vertical_integrand_le_bv435 hy hR)
  calc
    norm
        (intervalIntegral
          (fun t : Real => perronKernelIntegrand y
            ((R : Complex) + (t : Complex) * Complex.I))
          (-T) T MeasureTheory.volume) <=
        (y ^ R / R) * abs (T - -T) := hIntegral
    _ = 2 * T * (y ^ R / R) := by
      rw [abs_of_nonneg (by linarith)]
      ring

theorem norm_vIntegral'_perron_right_le
    {y R T : Real} (hy : 0 < y) (hR : 0 < R) (hT : 0 <= T) :
    norm (VIntegral' (perronKernelIntegrand y) R (-T) T) <=
      (T / Real.pi) * (y ^ R / R) := by
  rw [VIntegral', norm_smul]
  calc
    norm (1 / (2 * (Real.pi : Complex) * Complex.I)) *
        norm (VIntegral (perronKernelIntegrand y) R (-T) T) <=
        norm (1 / (2 * (Real.pi : Complex) * Complex.I)) *
          (2 * T * (y ^ R / R)) := by
      gcongr
      exact norm_vIntegral_perron_right_le hy hR hT
    _ = (T / Real.pi) * (y ^ R / R) := by
      rw [norm_div, norm_one, norm_mul, norm_mul]
      simp [Complex.norm_I, abs_of_pos Real.pi_pos]
      field_simp [ne_of_gt Real.pi_pos]

theorem tendsto_vIntegral'_perron_right_atTop
    {y T : Real} (hy : 0 < y) (hy1 : y < 1) (hT : 0 <= T) :
    Tendsto (fun R : Real =>
      VIntegral' (perronKernelIntegrand y) R (-T) T) atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hY : Tendsto (fun R : Real => y ^ R) atTop (nhds 0) :=
    tendsto_rpow_atTop_of_base_lt_one y (by linarith) hy1
  have hInv : Tendsto (fun R : Real => Inv.inv R) atTop (nhds 0) :=
    tendsto_inv_atTop_zero
  have hMajorant :
      Tendsto (fun R : Real => (T / Real.pi) * (y ^ R / R)) atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using (hY.mul hInv).const_mul (T / Real.pi)
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ hMajorant
  filter_upwards [eventually_gt_atTop (0 : Real)] with R hR
  exact norm_vIntegral'_perron_right_le hy hR hT

end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

open Filter Topology

namespace BombieriVinogradov.SiegelWalfisz

theorem truncatedPerronKernel_eq_rightHorizontalIntegrals
    {y c T : Real} (hy : 0 < y) (hy1 : y < 1) (hc : 0 < c)
    (hT : 0 < T) :
    truncatedPerronKernel y c T =
      (1 / (2 * Real.pi * Complex.I) : Complex) *
          rightHorizontalIntegral y c (-T) -
        (1 / (2 * Real.pi * Complex.I) : Complex) *
          rightHorizontalIntegral y c T := by
  have hBottom := tendsto_hIntegral'_right_atTop
    (t := -T) hy hy1 hc
  have hTop := tendsto_hIntegral'_right_atTop
    (t := T) hy hy1 hc
  have hRight := tendsto_vIntegral'_perron_right_atTop hy hy1 hT.le
  have hCombined := (hBottom.sub hTop).add hRight
  have hFinite : Filter.Eventually
      (fun R : Real => truncatedPerronKernel y c T =
        HIntegral' (perronKernelIntegrand y) c R (-T) -
          HIntegral' (perronKernelIntegrand y) c R T +
            VIntegral' (perronKernelIntegrand y) R (-T) T) atTop := by
    filter_upwards [eventually_ge_atTop c] with R hR
    exact truncatedPerronKernel_eq_right_rectangle_terms hy hc hT hR
  have hConst : Tendsto (fun _ : Real => truncatedPerronKernel y c T) atTop
      (nhds
        ((1 / (2 * Real.pi * Complex.I) : Complex) *
            rightHorizontalIntegral y c (-T) -
          (1 / (2 * Real.pi * Complex.I) : Complex) *
            rightHorizontalIntegral y c T)) := by
    have hCombined' : Tendsto
        (fun R : Real =>
          HIntegral' (perronKernelIntegrand y) c R (-T) -
            HIntegral' (perronKernelIntegrand y) c R T +
              VIntegral' (perronKernelIntegrand y) R (-T) T)
        atTop
        (nhds
          ((1 / (2 * Real.pi * Complex.I) : Complex) *
              rightHorizontalIntegral y c (-T) -
            (1 / (2 * Real.pi * Complex.I) : Complex) *
              rightHorizontalIntegral y c T)) := by
      simpa using hCombined
    apply hCombined'.congr'
    filter_upwards [hFinite] with R hR
    exact hR.symm
  exact tendsto_nhds_unique tendsto_const_nhds hConst

end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

theorem norm_truncatedPerronKernel_le_sqrt_log_bound
    {y c T : Real} (hy : 0 < y) (hy1 : y < 1) (hc : 0 < c)
    (hT : 0 < T) :
    norm (truncatedPerronKernel y c T) <=
      y ^ c /
        (Real.pi * Real.sqrt (c ^ 2 + T ^ 2) * abs (Real.log y)) := by
  let a : Complex := 1 / (2 * Real.pi * Complex.I)
  let B : Real :=
    y ^ c / (Real.sqrt (c ^ 2 + T ^ 2) * abs (Real.log y))
  have hMinus : norm (rightHorizontalIntegral y c (-T)) <= B := by
    simpa [B, rightHorizontalIntegral] using
      (norm_integral_perron_horizontal_Ioi_le
        (t := -T) hy hy1 hc)
  have hPlus : norm (rightHorizontalIntegral y c T) <= B := by
    simpa [B, rightHorizontalIntegral] using
      (norm_integral_perron_horizontal_Ioi_le
        (t := T) hy hy1 hc)
  have hCoeff : norm a = 1 / (2 * Real.pi) := by
    dsimp [a]
    rw [norm_div, norm_one, norm_mul, norm_mul]
    simp [Complex.norm_I, abs_of_pos Real.pi_pos]
  rw [truncatedPerronKernel_eq_rightHorizontalIntegrals hy hy1 hc hT]
  change norm
      (a * rightHorizontalIntegral y c (-T) -
        a * rightHorizontalIntegral y c T) <= _
  calc
    norm
        (a * rightHorizontalIntegral y c (-T) -
          a * rightHorizontalIntegral y c T) <=
        norm (a * rightHorizontalIntegral y c (-T)) +
          norm (a * rightHorizontalIntegral y c T) := norm_sub_le _ _
    _ = norm a * norm (rightHorizontalIntegral y c (-T)) +
          norm a * norm (rightHorizontalIntegral y c T) := by
      rw [norm_mul, norm_mul]
    _ <= norm a * B + norm a * B := by
      gcongr
    _ = y ^ c /
          (Real.pi * Real.sqrt (c ^ 2 + T ^ 2) * abs (Real.log y)) := by
      rw [hCoeff]
      dsimp [B]
      field_simp [ne_of_gt Real.pi_pos]
      ring

theorem norm_truncatedPerronKernel_lt_log_bound
    {y c T : Real} (hy : 0 < y) (hy1 : y < 1) (hc : 0 < c)
    (hT : 0 < T) :
    norm (truncatedPerronKernel y c T) <
      y ^ c / (Real.pi * T * abs (Real.log y)) := by
  have hD : T < Real.sqrt (c ^ 2 + T ^ 2) := by
    have hSq : 0 <= c ^ 2 + T ^ 2 := by positivity
    have hSqrtSq := Real.sq_sqrt hSq
    have hSqrtNonneg := Real.sqrt_nonneg (c ^ 2 + T ^ 2)
    nlinarith [sq_pos_of_pos hc]
  have hLogAbs : 0 < abs (Real.log y) :=
    abs_pos.mpr (ne_of_lt (Real.log_neg hy hy1))
  have hNumerator : 0 < y ^ c := Real.rpow_pos_of_pos hy c
  have hSmallDenom : 0 < Real.pi * T * abs (Real.log y) := by positivity
  have hDenomLt :
      Real.pi * T * abs (Real.log y) <
        Real.pi * Real.sqrt (c ^ 2 + T ^ 2) * abs (Real.log y) := by
    nlinarith [Real.pi_pos]
  exact (norm_truncatedPerronKernel_le_sqrt_log_bound hy hy1 hc hT).trans_lt
    (div_lt_div_of_pos_left hNumerator hSmallDenom hDenomLt)

end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

theorem norm_truncatedPerronKernel_lt_unit_bound
    {y c T : Real} (hy : 0 < y) (hy1 : y < 1)
    (hc : 0 < c) (hT : 0 < T) :
    norm (truncatedPerronKernel y c T) < y ^ c := by
  let a : Complex := 1 / (2 * Real.pi * Complex.I)
  have hCoeff : norm a = 1 / (2 * Real.pi) := by
    dsimp [a]
    rw [norm_div, norm_one, norm_mul, norm_mul]
    simp [Complex.norm_I, abs_of_pos Real.pi_pos]
  have hCoeffPos : 0 < norm a := by
    rw [hCoeff]
    positivity
  have hPowerPos : 0 < y ^ c := Real.rpow_pos_of_pos hy c
  rw [truncatedPerronKernel, VIntegral']
  change norm (a * VIntegral (perronKernelIntegrand y) c (-T) T) < _
  rw [vIntegral_eq_perronRightArcIntegral hy hc hT, norm_mul]
  calc
    norm a * norm (perronRightArcIntegral y c T) <
        norm a * (Real.pi * y ^ c) :=
      mul_lt_mul_of_pos_left
        (norm_perronRightArcIntegral_lt_pi_mul hy hy1 hc hT) hCoeffPos
    _ = y ^ c / 2 := by
      rw [hCoeff]
      field_simp [ne_of_gt Real.pi_pos]
    _ < y ^ c := by linarith

end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

theorem norm_truncatedPerronKernel_lt_min_bound
    {y c T : Real} (hy : 0 < y) (hy1 : y < 1)
    (hc : 0 < c) (hT : 0 < T) :
    norm (truncatedPerronKernel y c T) <
      y ^ c * min 1 (1 / (Real.pi * T * abs (Real.log y))) := by
  have hPowerNonneg : 0 <= y ^ c := (Real.rpow_pos_of_pos hy c).le
  rw [mul_min_of_nonneg 1 (1 / (Real.pi * T * abs (Real.log y)))
    hPowerNonneg]
  apply lt_min
  next =>
    simpa using norm_truncatedPerronKernel_lt_unit_bound hy hy1 hc hT
  next =>
    simpa [div_eq_mul_inv] using
      norm_truncatedPerronKernel_lt_log_bound hy hy1 hc hT

theorem norm_truncatedPerronKernel_sub_stepWeight_lt_of_lt_one
    {y c T : Real} (hy : 0 < y) (hy1 : y < 1)
    (hc : 0 < c) (hT : 0 < T) :
    norm (truncatedPerronKernel y c T -
      (perronStepWeight y : Complex)) <
      y ^ c * min 1 (1 / (Real.pi * T * abs (Real.log y))) := by
  have hWeight : perronStepWeight y = 0 := by
    simp [perronStepWeight, hy1]
  rw [hWeight, Complex.ofReal_zero, sub_zero]
  exact norm_truncatedPerronKernel_lt_min_bound hy hy1 hc hT

end BombieriVinogradov.SiegelWalfisz

end
end

section

namespace Real

theorem arctan_lt_self_of_pos {x : Real} (hx : 0 < x) : arctan x < x := by
  have hArctanPos : 0 < arctan x := arctan_pos.mpr hx
  have hTangent := lt_tan hArctanPos (arctan_lt_pi_div_two x)
  simpa using hTangent

end Real

end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

private lemma inv_ofReal_add_ofReal_mul_I_bv441 (c t : Real) :
    Inv.inv ((c : Complex) + (t : Complex) * Complex.I) =
      ((c / (c ^ 2 + t ^ 2) : Real) : Complex) -
        ((t / (c ^ 2 + t ^ 2) : Real) : Complex) * Complex.I := by
  rw [Complex.inv_def]
  simp [Complex.normSq_apply, div_eq_mul_inv]
  ring

private lemma odd_fraction_integral_eq_zero_bv441 (c T : Real) :
    intervalIntegral (fun t : Real => t / (c ^ 2 + t ^ 2)) (-T) T
        MeasureTheory.volume = 0 := by
  let f : Real -> Real := fun t => t / (c ^ 2 + t ^ 2)
  have hOdd (t : Real) : f (-t) = -f t := by
    dsimp [f]
    ring
  have hComp := intervalIntegral.integral_comp_neg (f := f) (a := -T) (b := T)
  have hSame :
      intervalIntegral (fun t : Real => f (-t)) (-T) T MeasureTheory.volume =
        intervalIntegral f (-T) T MeasureTheory.volume := by
    simpa only [neg_neg] using hComp
  have hNeg :
      intervalIntegral (fun t : Real => f (-t)) (-T) T MeasureTheory.volume =
        -intervalIntegral f (-T) T MeasureTheory.volume := by
    calc
      intervalIntegral (fun t : Real => f (-t)) (-T) T MeasureTheory.volume =
          intervalIntegral (fun t : Real => -f t) (-T) T MeasureTheory.volume := by
        apply intervalIntegral.integral_congr
        intro t _
        exact hOdd t
      _ = -intervalIntegral f (-T) T MeasureTheory.volume :=
        intervalIntegral.integral_neg
  have hZero : intervalIntegral f (-T) T MeasureTheory.volume = 0 := by
    linarith
  simpa [f] using hZero

private lemma reciprocal_vertical_integral_eq_arctan_bv441
    {c T : Real} (hc : 0 < c) :
    intervalIntegral
        (fun t : Real => Inv.inv ((c : Complex) + (t : Complex) * Complex.I))
        (-T) T MeasureTheory.volume =
      ((2 * Real.arctan (T / c) : Real) : Complex) := by
  have hden (t : Real) : Ne (c ^ 2 + t ^ 2) 0 := by
    nlinarith [sq_nonneg t]
  have hRealContinuous : Continuous (fun t : Real => c / (c ^ 2 + t ^ 2)) := by
    fun_prop (disch := exact hden _)
  have hImagContinuous : Continuous (fun t : Real => t / (c ^ 2 + t ^ 2)) := by
    fun_prop (disch := exact hden _)
  have hRealComplexContinuous :
      Continuous (fun t : Real => ((c / (c ^ 2 + t ^ 2) : Real) : Complex)) := by
    fun_prop
  have hImagComplexContinuous :
      Continuous
        (fun t : Real =>
          ((t / (c ^ 2 + t ^ 2) : Real) : Complex) * Complex.I) := by
    fun_prop
  have hRealIntegral :
      intervalIntegral (fun t : Real => c / (c ^ 2 + t ^ 2)) (-T) T
          MeasureTheory.volume =
        2 * Real.arctan (T / c) := by
    calc
      intervalIntegral (fun t : Real => c / (c ^ 2 + t ^ 2)) (-T) T
          MeasureTheory.volume =
          Real.arctan (T / c) - Real.arctan (-T / c) := integral_div_sq_add_sq
      _ = 2 * Real.arctan (T / c) := by
        rw [neg_div, Real.arctan_neg]
        ring
  calc
    intervalIntegral
        (fun t : Real => Inv.inv ((c : Complex) + (t : Complex) * Complex.I))
        (-T) T MeasureTheory.volume =
        intervalIntegral
          (fun t : Real =>
            ((c / (c ^ 2 + t ^ 2) : Real) : Complex) -
              ((t / (c ^ 2 + t ^ 2) : Real) : Complex) * Complex.I)
          (-T) T MeasureTheory.volume := by
      apply intervalIntegral.integral_congr
      intro t _
      exact inv_ofReal_add_ofReal_mul_I_bv441 c t
    _ = intervalIntegral
          (fun t : Real => ((c / (c ^ 2 + t ^ 2) : Real) : Complex))
          (-T) T MeasureTheory.volume -
        intervalIntegral
          (fun t : Real =>
            ((t / (c ^ 2 + t ^ 2) : Real) : Complex) * Complex.I)
          (-T) T MeasureTheory.volume := by
      exact intervalIntegral.integral_sub
        (hRealComplexContinuous.intervalIntegrable _ _)
        (hImagComplexContinuous.intervalIntegrable _ _)
    _ = ((2 * Real.arctan (T / c) : Real) : Complex) := by
      rw [intervalIntegral.integral_mul_const]
      rw [intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal]
      rw [hRealIntegral, odd_fraction_integral_eq_zero_bv441]
      simp

theorem truncatedPerronKernel_one_eq_arctan
    {c T : Real} (hc : 0 < c) :
    truncatedPerronKernel 1 c T =
      (Real.arctan (T / c) / Real.pi : Complex) := by
  rw [truncatedPerronKernel]
  simp [perronKernelIntegrand, VIntegral', VIntegral]
  rw [reciprocal_vertical_integral_eq_arctan_bv441 hc]
  push_cast
  field_simp
  ring_nf
  simp [Complex.I_sq]

end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

theorem norm_truncatedPerronKernel_one_sub_perronStepWeight_lt
    {c T : Real} (hc : 0 < c) (hT : 0 < T) :
    norm
        (truncatedPerronKernel 1 c T -
          (perronStepWeight 1 : Complex)) <
      c / (Real.pi * T) := by
  have hRatio : 0 < T / c := div_pos hT hc
  have hInverse : Inv.inv (T / c) = c / T := by
    field_simp
  have hComplement :
      Real.pi / 2 - Real.arctan (T / c) = Real.arctan (c / T) := by
    rw [hInverse.symm]
    exact (Real.arctan_inv_of_pos hRatio).symm
  have hArctanUpper : Real.arctan (T / c) < Real.pi / 2 :=
    Real.arctan_lt_pi_div_two _
  have hSmall : Real.arctan (c / T) < c / T :=
    Real.arctan_lt_self_of_pos (div_pos hc hT)
  have hDifferenceNeg :
      Real.arctan (T / c) / Real.pi - 1 / 2 < 0 := by
    have hScaledUpper :
        Real.arctan (T / c) / Real.pi < (Real.pi / 2) / Real.pi :=
      div_lt_div_of_pos_right hArctanUpper Real.pi_pos
    have hHalf : (Real.pi / 2) / Real.pi = 1 / 2 := by
      field_simp [ne_of_gt Real.pi_pos]
    rw [hHalf] at hScaledUpper
    exact sub_neg.mpr hScaledUpper
  rw [truncatedPerronKernel_one_eq_arctan hc, perronStepWeight_one]
  rw [(Complex.ofReal_div _ _).symm, (Complex.ofReal_sub _ _).symm,
    Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_neg hDifferenceNeg]
  rw [show
      Real.arctan (T / c) / Real.pi - 1 / 2 =
        -(Real.arctan (c / T) / Real.pi) by
      rw [hComplement.symm]
      field_simp [ne_of_gt Real.pi_pos]
      ring]
  rw [neg_neg]
  have hPi : 0 < Real.pi := Real.pi_pos
  have hScaled : Real.arctan (c / T) / Real.pi < (c / T) / Real.pi :=
    div_lt_div_of_pos_right hSmall hPi
  calc
    Real.arctan (c / T) / Real.pi < (c / T) / Real.pi := hScaled
    _ = c / (Real.pi * T) := by field_simp

end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

theorem norm_truncatedPerronKernel_sub_stepWeight_lt
    {y c T : Real} (hy : 0 < y) (hc : 0 < c) (hT : 0 < T) :
    norm (truncatedPerronKernel y c T -
      (perronStepWeight y : Complex)) <
      if y = 1 then c / (Real.pi * T)
      else y ^ c * min 1 (1 / (Real.pi * T * abs (Real.log y))) := by
  rcases lt_trichotomy y 1 with hy1 | hyeq | hy1
  next =>
    rw [if_neg (ne_of_lt hy1)]
    exact norm_truncatedPerronKernel_sub_stepWeight_lt_of_lt_one
      hy hy1 hc hT
  next =>
    subst y
    rw [if_pos rfl]
    exact norm_truncatedPerronKernel_one_sub_perronStepWeight_lt hc hT
  next =>
    rw [if_neg (ne_of_gt hy1)]
    exact norm_truncatedPerronKernel_sub_stepWeight_lt_of_one_lt hy1 hc hT

end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

theorem norm_scalarPerronErrorTerm_le_majorant
    {N : Nat} (chi : DirichletCharacter Complex N) {x : Nat} (hx : 0 < x)
    {c T : Real} (hc : 0 < c) (hT : 0 < T) (n : Nat) :
    norm (scalarPerronErrorTerm chi x c T n) <=
      scalarPerronErrorMajorantTerm chi x c T n := by
  by_cases hn : n = 0
  case pos =>
    subst n
    simp [scalarPerronErrorTerm, scalarPerronErrorMajorantTerm,
      scalarPerronSeriesTerm, scalarPerronStepTerm]
  case neg =>
    have hnPos : 0 < n := Nat.pos_of_ne_zero hn
    have hRatioPos : 0 < (x : Real) / (n : Real) :=
      div_pos (by exact_mod_cast hx) (by exact_mod_cast hnPos)
    have hPerron := norm_truncatedPerronKernel_sub_stepWeight_lt
      hRatioPos hc hT
    rw [scalarPerronErrorTerm, scalarPerronSeriesTerm,
      scalarPerronStepTerm, if_neg hn, if_neg hn,
      scalarPerronErrorMajorantTerm, if_neg hn]
    have hFactor :
        twistedMangoldtSequence chi n *
            truncatedPerronKernel ((x : Real) / (n : Real)) c T -
          twistedMangoldtSequence chi n *
            (perronStepWeight ((x : Real) / (n : Real)) : Complex) =
        twistedMangoldtSequence chi n *
          (truncatedPerronKernel ((x : Real) / (n : Real)) c T -
            (perronStepWeight ((x : Real) / (n : Real)) : Complex)) := by
      ring
    rw [hFactor, norm_mul]
    exact mul_le_mul_of_nonneg_left hPerron.le (norm_nonneg _)

end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

theorem summable_norm_scalarPerronErrorTerm
    {N : Nat} (chi : DirichletCharacter Complex N) {x : Nat} (hx : 0 < x)
    {c T : Real} (hc : 1 < c) (hT : 0 < T) :
    Summable (fun n : Nat => norm (scalarPerronErrorTerm chi x c T n)) := by
  apply Summable.of_nonneg_of_le
    (fun _ => norm_nonneg _)
    (fun n => norm_scalarPerronErrorTerm_le_majorant chi hx
      (lt_trans zero_lt_one hc) hT n)
    (summable_scalarPerronErrorMajorantTerm chi hx hc hT)

theorem summable_scalarPerronErrorTerm
    {N : Nat} (chi : DirichletCharacter Complex N) {x : Nat} (hx : 0 < x)
    {c T : Real} (hc : 1 < c) (hT : 0 < T) :
    Summable (scalarPerronErrorTerm chi x c T) :=
  summable_norm_iff.mp (summable_norm_scalarPerronErrorTerm chi hx hc hT)

theorem summable_scalarPerronSeriesTerm
    {N : Nat} (chi : DirichletCharacter Complex N) {x : Nat} (hx : 0 < x)
    {c T : Real} (hc : 1 < c) (hT : 0 < T) :
    Summable (scalarPerronSeriesTerm chi x c T) := by
  have hFunction : scalarPerronSeriesTerm chi x c T = fun n : Nat =>
      scalarPerronErrorTerm chi x c T n + scalarPerronStepTerm chi x n := by
    funext n
    unfold scalarPerronErrorTerm
    ring
  rw [hFunction]
  exact (summable_scalarPerronErrorTerm chi hx hc hT).add
    (summable_scalarPerronStepTerm chi)

end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

theorem norm_explicitFormulaVerticalIntegral_sub_halfSum_le
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    {x : Nat} (hx : 0 < x) {c T : Real} (hc : 1 < c) (hT : 0 < T) :
    norm (explicitFormulaVerticalIntegral chi x c T -
      characterChebyshevHalfSum x chi) <=
      tsum (scalarPerronErrorMajorantTerm chi x c T) := by
  have hErrorNorm := summable_norm_scalarPerronErrorTerm chi hx hc hT
  have hMajorant := summable_scalarPerronErrorMajorantTerm chi hx hc hT
  have hSeries := summable_scalarPerronSeriesTerm chi hx hc hT
  have hStep := summable_scalarPerronStepTerm (x := x) chi
  rw [explicitFormulaVerticalIntegral_eq_tsum_scalarPerronSeriesTerm chi hx hc]
  rw [<- tsum_scalarPerronStepTerm_eq_characterChebyshevHalfSum chi hx]
  rw [<- hSeries.tsum_sub hStep]
  change norm (tsum (scalarPerronErrorTerm chi x c T)) <= _
  exact (norm_tsum_le_tsum_norm hErrorNorm).trans
    (hErrorNorm.tsum_le_tsum
      (fun n => norm_scalarPerronErrorTerm_le_majorant chi hx
        (lt_trans zero_lt_one hc) hT n)
      hMajorant)

end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

theorem norm_explicitFormulaVerticalIntegral_sub_halfSum_le_source
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    {x : Nat} (hx : 0 < x) {c T : Real} (hc : 1 < c) (hT : 0 < T) :
    norm (explicitFormulaVerticalIntegral chi x c T -
      characterChebyshevHalfSum x chi) <=
      tsum (sourcePerronErrorMajorantTerm x c T) := by
  exact (norm_explicitFormulaVerticalIntegral_sub_halfSum_le chi hx hc hT).trans
    ((summable_scalarPerronErrorMajorantTerm chi hx hc hT).tsum_le_tsum
      (fun n => scalarPerronErrorMajorantTerm_le_source chi hx
        (lt_trans zero_lt_one hc) hT n)
      (summable_sourcePerronErrorMajorantTerm hx hc hT))

end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

open Set

namespace BombieriVinogradov.SiegelWalfisz

theorem exists_vonMangoldtLSeriesNormSum_le_div :
    Exists fun C : Real => And (0 < C) (forall c : Real,
      1 < c -> c < 2 ->
        vonMangoldtLSeriesNormSum c <= C / (c - 1)) := by
  have hExist := ShiftZeroBound
  let C0 : Real := hExist.choose
  have hSpec := hExist.choose_spec
  have hC0 : 1 <= C0 := hSpec.1
  have hBound : forall delta : Real, Membership.mem (Ioo 0 1) delta ->
      -(deriv riemannZeta (1 + (delta : Complex)) /
        riemannZeta (1 + (delta : Complex))).re <= 1 / delta + C0 :=
    hSpec.2
  refine Exists.intro (1 + C0) (And.intro (by linarith) ?_)
  intro c hcLower hcUpper
  have hDelta : Membership.mem (Ioo 0 1) (c - 1) := by
    exact And.intro (sub_pos.mpr hcLower) (by linarith)
  have hRaw := hBound (c - 1) hDelta
  have hPoint : (1 : Complex) + ((c - 1 : Real) : Complex) = (c : Complex) := by
    push_cast
    ring
  have hSeriesBound : vonMangoldtLSeriesNormSum c <=
      1 / (c - 1) + C0 := by
    rw [vonMangoldtLSeriesNormSum_eq_neg_logDeriv_re hcLower]
    rw [hPoint] at hRaw
    rw [neg_div, Complex.neg_re]
    exact hRaw
  have hC0Nonneg : 0 <= C0 := le_trans zero_le_one hC0
  have hDenom : Ne (c - 1) 0 := ne_of_gt hDelta.1
  have hMulDiv : C0 / (c - 1) * (c - 1) = C0 := by
    field_simp [hDenom]
  have hC0Div : C0 <= C0 / (c - 1) := by
    nlinarith [hDelta.1, hDelta.2, hC0Nonneg, hMulDiv]
  calc
    vonMangoldtLSeriesNormSum c <= 1 / (c - 1) + C0 := hSeriesBound
    _ <= 1 / (c - 1) + C0 / (c - 1) := add_le_add_right hC0Div _
    _ = (1 + C0) / (c - 1) := by ring

end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

theorem norm_LSeriesTerm_vonMangoldt_antitone
    {c d : Real} (hcd : c <= d) (n : Nat) :
    norm (LSeries.term
      (fun m : Nat => (ArithmeticFunction.vonMangoldt m : Complex))
      (d : Complex) n) <=
    norm (LSeries.term
      (fun m : Nat => (ArithmeticFunction.vonMangoldt m : Complex))
      (c : Complex) n) := by
  rw [norm_LSeriesTerm_vonMangoldt_eq,
    norm_LSeriesTerm_vonMangoldt_eq]
  by_cases hn : n = 0
  case pos =>
    subst n
    simp
  case neg =>
    have hnPos : 0 < n := Nat.pos_of_ne_zero hn
    have hnRealPos : 0 < (n : Real) := by exact_mod_cast hnPos
    have hnOne : (1 : Real) <= (n : Real) := by exact_mod_cast hnPos
    have hPow := Real.rpow_le_rpow_of_exponent_le hnOne hcd
    have hReciprocal : 1 / (n : Real) ^ d <= 1 / (n : Real) ^ c :=
      one_div_le_one_div_of_le (Real.rpow_pos_of_pos hnRealPos c) hPow
    calc
      ArithmeticFunction.vonMangoldt n / (n : Real) ^ d =
          ArithmeticFunction.vonMangoldt n * (1 / (n : Real) ^ d) := by ring
      _ <= ArithmeticFunction.vonMangoldt n * (1 / (n : Real) ^ c) :=
        mul_le_mul_of_nonneg_left hReciprocal
          ArithmeticFunction.vonMangoldt_nonneg
      _ = ArithmeticFunction.vonMangoldt n / (n : Real) ^ c := by ring

theorem vonMangoldtLSeriesNormSum_antitone
    {c d : Real} (hc : 1 < c) (hcd : c <= d) :
    vonMangoldtLSeriesNormSum d <= vonMangoldtLSeriesNormSum c := by
  have hd : 1 < d := lt_of_lt_of_le hc hcd
  have hSummableD := ArithmeticFunction.LSeriesSummable_vonMangoldt
    (s := (d : Complex)) (by simpa using hd)
  have hSummableC := ArithmeticFunction.LSeriesSummable_vonMangoldt
    (s := (c : Complex)) (by simpa using hc)
  unfold vonMangoldtLSeriesNormSum
  exact hSummableD.norm.tsum_le_tsum
    (norm_LSeriesTerm_vonMangoldt_antitone hcd) hSummableC.norm

end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

theorem exists_vonMangoldtLSeriesNormSum_le_div_le_three :
    Exists fun C : Real => And (0 < C) (forall c : Real,
      1 < c -> c <= 3 ->
        vonMangoldtLSeriesNormSum c <= C / (c - 1)) := by
  have hExist := exists_vonMangoldtLSeriesNormSum_le_div
  let C0 : Real := hExist.choose
  have hSpec := hExist.choose_spec
  have hC0 : 0 < C0 := hSpec.1
  have hNarrow := hSpec.2
  refine Exists.intro (4 * C0) (And.intro (by positivity) ?_)
  intro c hc1 hc3
  have hDenomPos : 0 < c - 1 := sub_pos.mpr hc1
  by_cases hc2 : c < 2
  case pos =>
    have hRaw := hNarrow c hc1 hc2
    calc
      vonMangoldtLSeriesNormSum c <= C0 / (c - 1) := hRaw
      _ <= (4 * C0) / (c - 1) := by
        have hUnitNonneg : 0 <= 1 / (c - 1) := by positivity
        calc
          C0 / (c - 1) = C0 * (1 / (c - 1)) := by ring
          _ <= (4 * C0) * (1 / (c - 1)) :=
            mul_le_mul_of_nonneg_right (by nlinarith [hC0]) hUnitNonneg
          _ = (4 * C0) / (c - 1) := by ring
  case neg =>
    have hcTwo : (2 : Real) <= c := le_of_not_gt hc2
    have hMono := vonMangoldtLSeriesNormSum_antitone
      (c := (3 / 2 : Real)) (d := c) (by norm_num) (by linarith)
    have hAt := hNarrow (3 / 2 : Real) (by norm_num) (by norm_num)
    have hFixed : vonMangoldtLSeriesNormSum c <= 2 * C0 := by
      calc
        vonMangoldtLSeriesNormSum c <=
            vonMangoldtLSeriesNormSum (3 / 2 : Real) := hMono
        _ <= C0 / ((3 / 2 : Real) - 1) := hAt
        _ = 2 * C0 := by ring
    have hDenomUpper : c - 1 <= 2 := by linarith
    have hReciprocal : (1 / 2 : Real) <= 1 / (c - 1) :=
      one_div_le_one_div_of_le hDenomPos hDenomUpper
    calc
      vonMangoldtLSeriesNormSum c <= 2 * C0 := hFixed
      _ = (4 * C0) * (1 / 2 : Real) := by ring
      _ <= (4 * C0) * (1 / (c - 1)) :=
        mul_le_mul_of_nonneg_left hReciprocal (by positivity)
      _ = (4 * C0) / (c - 1) := by ring

end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

def endpointPerronBound (x : Nat) (c T : Real) (n : Nat) : Real :=
  if n = x then
    ArithmeticFunction.vonMangoldt x * (c / (Real.pi * T))
  else 0

theorem sourcePerronErrorMajorantTerm_self
    {x : Nat} (hx : 0 < x) (c T : Real) :
    sourcePerronErrorMajorantTerm x c T x =
      ArithmeticFunction.vonMangoldt x * (c / (Real.pi * T)) := by
  have hxNe : Ne (x : Real) 0 := by exact_mod_cast Nat.ne_of_gt hx
  rw [sourcePerronErrorMajorantTerm, if_neg (Nat.ne_of_gt hx),
    if_pos (div_self hxNe)]

theorem endpointPerronBound_nonneg
    (x : Nat) {c T : Real} (hc : 0 <= c) (hT : 0 < T) (n : Nat) :
    0 <= endpointPerronBound x c T n := by
  unfold endpointPerronBound
  split
  case isTrue =>
    exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
      (div_nonneg hc (mul_nonneg Real.pi_pos.le hT.le))
  case isFalse =>
    exact le_refl 0

theorem summable_endpointPerronBound (x : Nat) (c T : Real) :
    Summable (endpointPerronBound x c T) := by
  exact (hasSum_ite_eq x
    (ArithmeticFunction.vonMangoldt x * (c / (Real.pi * T)))).summable

theorem tsum_endpointPerronBound_eq (x : Nat) (c T : Real) :
    tsum (endpointPerronBound x c T) =
      ArithmeticFunction.vonMangoldt x * (c / (Real.pi * T)) := by
  exact (hasSum_ite_eq x
    (ArithmeticFunction.vonMangoldt x * (c / (Real.pi * T)))).tsum_eq

end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

theorem half_le_log_two : (1 / 2 : Real) <= Real.log 2 := by
  have h := Real.le_log_one_add_of_nonneg (x := (1 : Real)) (by norm_num)
  norm_num at h
  exact le_trans (by norm_num : (1 / 2 : Real) <= 2 / 3) h

theorem half_le_abs_log_ratio_of_far
    {x n : Nat} (hx : 0 < x) (hn : 0 < n)
    (hfar : n <= x / 2 \/ 2 * x <= n) :
    (1 / 2 : Real) <= abs (Real.log ((x : Real) / (n : Real))) := by
  have hxReal : 0 < (x : Real) := by exact_mod_cast hx
  have hnReal : 0 < (n : Real) := by exact_mod_cast hn
  have hRatioPos : 0 < (x : Real) / (n : Real) := div_pos hxReal hnReal
  have hDivMul : ((x : Real) / (n : Real)) * (n : Real) = (x : Real) := by
    field_simp [ne_of_gt hnReal]
  rcases hfar with hLower | hUpper
  case inl =>
    have hTwice : 2 * n <= x := by omega
    have hTwiceReal : (2 : Real) * (n : Real) <= (x : Real) := by
      exact_mod_cast hTwice
    have hRatio : (2 : Real) <= (x : Real) / (n : Real) := by
      nlinarith [hnReal, hDivMul, hTwiceReal]
    have hLog := Real.log_le_log (by norm_num : (0 : Real) < 2) hRatio
    have hLogNonneg : 0 <= Real.log ((x : Real) / (n : Real)) :=
      (Real.log_nonneg (by norm_num : (1 : Real) <= 2)).trans hLog
    rw [abs_of_nonneg hLogNonneg]
    exact half_le_log_two.trans hLog
  case inr =>
    have hTwiceReal : (2 : Real) * (x : Real) <= (n : Real) := by
      exact_mod_cast hUpper
    have hRatio : (x : Real) / (n : Real) <= (1 / 2 : Real) := by
      nlinarith [hnReal, hRatioPos, hDivMul, hTwiceReal]
    have hLog := Real.log_le_log hRatioPos hRatio
    have hHalfLog : Real.log (1 / 2 : Real) = -Real.log 2 := by
      rw [one_div, Real.log_inv]
    have hLogNonpos : Real.log ((x : Real) / (n : Real)) <= 0 := by
      rw [hHalfLog] at hLog
      nlinarith [half_le_log_two]
    rw [abs_of_nonpos hLogNonpos]
    rw [hHalfLog] at hLog
    nlinarith [half_le_log_two]

end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

open Finset
open scoped BigOperators

namespace BombieriVinogradov.SiegelWalfisz

theorem lower_distance_sum_eq_harmonic (x : Nat) :
    (Finset.sum (range x) (fun n : Nat =>
      1 / (((x - n : Nat) : Real)))) = (harmonic x : Real) := by
  calc
    Finset.sum (range x) (fun n : Nat =>
        1 / (((x - n : Nat) : Real))) =
      Finset.sum (range x) (fun n : Nat =>
        1 / ((((x - 1 - n) + 1 : Nat) : Real))) := by
      apply sum_congr rfl
      intro n hn
      have hnx : n < x := mem_range.mp hn
      congr 3
      omega
    _ = Finset.sum (range x) (fun k : Nat =>
        1 / (((k + 1 : Nat) : Real))) :=
      sum_range_reflect (fun k : Nat => 1 / (((k + 1 : Nat) : Real))) x
    _ = (harmonic x : Real) := by
      rw [harmonic, Rat.cast_sum]
      simp only [Rat.cast_inv, Rat.cast_natCast, one_div]

theorem upper_distance_sum_eq_harmonic (x : Nat) :
    (Finset.sum (Ico (x + 1) (2 * x + 1)) (fun n : Nat =>
      1 / (((n - x : Nat) : Real)))) = (harmonic x : Real) := by
  rw [sum_Ico_eq_sum_range]
  have hLength : 2 * x + 1 - (x + 1) = x := by omega
  rw [hLength]
  calc
    Finset.sum (range x) (fun k : Nat =>
        1 / (((x + 1 + k - x : Nat) : Real))) =
      Finset.sum (range x) (fun k : Nat =>
        1 / (((k + 1 : Nat) : Real))) := by
      apply sum_congr rfl
      intro k hk
      congr 3
      omega
    _ = (harmonic x : Real) := by
      rw [harmonic, Rat.cast_sum]
      simp only [Rat.cast_inv, Rat.cast_natCast, one_div]

end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

theorem one_le_log_two_mul {x : Nat} (hx : 2 < x) :
    (1 : Real) <= Real.log (2 * (x : Real)) := by
  have hLogThree := Real.le_log_one_add_of_nonneg
    (x := (2 : Real)) (by norm_num)
  norm_num at hLogThree
  have hThree : (3 : Real) <= 2 * (x : Real) := by
    have hxThree : 3 <= x := hx
    exact_mod_cast (show 3 <= 2 * x by omega)
  exact hLogThree.trans (Real.log_le_log (by norm_num) hThree)

theorem harmonic_le_three_log_two_mul
    {x : Nat} (hx : 0 < x) :
    (harmonic x : Real) <= 3 * Real.log (2 * (x : Real)) := by
  have hxReal : 0 < (x : Real) := by exact_mod_cast hx
  have hLogMono : Real.log (x : Real) <= Real.log (2 * (x : Real)) := by
    apply Real.log_le_log hxReal
    nlinarith [hxReal]
  have hTwoLe : (2 : Real) <= 2 * (x : Real) := by exact_mod_cast
    (show 2 <= 2 * x by omega)
  have hHalf : (1 / 2 : Real) <= Real.log (2 * (x : Real)) :=
    half_le_log_two.trans (Real.log_le_log (by norm_num) hTwoLe)
  have hHarmonic : (harmonic x : Real) <= 1 + Real.log (x : Real) :=
    harmonic_le_one_add_log x
  linarith

end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

theorem endpointPerronBoundValue_le_logSquared
    {x : Nat} (hx : 2 < x) {c T : Real}
    (hc0 : 0 <= c) (hc3 : c <= 3) (hT : 0 < T) :
    ArithmeticFunction.vonMangoldt x * (c / (Real.pi * T)) <=
      3 * (x : Real) * Real.log (2 * (x : Real)) ^ 2 / T := by
  have hxPos : 0 < x := lt_trans zero_lt_two hx
  have hxReal : 0 < (x : Real) := by exact_mod_cast hxPos
  have hxOne : (1 : Real) <= (x : Real) := by exact_mod_cast hxPos
  have hLogOne := one_le_log_two_mul hx
  have hLogNonneg : 0 <= Real.log (2 * (x : Real)) := le_trans zero_le_one hLogOne
  have hLambdaLog : ArithmeticFunction.vonMangoldt x <=
      Real.log (2 * (x : Real)) := by
    exact ArithmeticFunction.vonMangoldt_le_log.trans
      (Real.log_le_log hxReal (by nlinarith [hxReal]))
  have hPiOne : (1 : Real) <= Real.pi := by
    linarith [Real.pi_gt_three]
  have hDenom : T <= Real.pi * T := by
    nlinarith [hT, hPiOne]
  have hReciprocal : 1 / (Real.pi * T) <= 1 / T :=
    one_div_le_one_div_of_le hT hDenom
  have hFactor : c / (Real.pi * T) <= 3 / T := by
    calc
      c / (Real.pi * T) = c * (1 / (Real.pi * T)) := by ring
      _ <= c * (1 / T) := mul_le_mul_of_nonneg_left hReciprocal hc0
      _ <= 3 * (1 / T) := by
        exact mul_le_mul_of_nonneg_right hc3 (by positivity)
      _ = 3 / T := by ring
  have hFirst : ArithmeticFunction.vonMangoldt x * (c / (Real.pi * T)) <=
      Real.log (2 * (x : Real)) * (3 / T) := by
    exact mul_le_mul hLambdaLog hFactor (by positivity) hLogNonneg
  have hXL : (1 : Real) <= (x : Real) * Real.log (2 * (x : Real)) := by
    calc
      (1 : Real) = 1 * 1 := by ring
      _ <= (x : Real) * Real.log (2 * (x : Real)) :=
        mul_le_mul hxOne hLogOne zero_le_one hxReal.le
  calc
    ArithmeticFunction.vonMangoldt x * (c / (Real.pi * T)) <=
        Real.log (2 * (x : Real)) * (3 / T) := hFirst
    _ = (Real.log (2 * (x : Real)) * (3 / T)) * 1 := by ring
    _ <= (Real.log (2 * (x : Real)) * (3 / T)) *
        ((x : Real) * Real.log (2 * (x : Real))) :=
      mul_le_mul_of_nonneg_left hXL (mul_nonneg hLogNonneg (by positivity))
    _ = 3 * (x : Real) * Real.log (2 * (x : Real)) ^ 2 / T := by ring

end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

open Finset

namespace BombieriVinogradov.SiegelWalfisz

def lowerNearPerronBound (x : Nat) (T : Real) (n : Nat) : Real :=
  if n < x then
    8 * (x : Real) * Real.log (2 * (x : Real)) /
      (T * ((x - n : Nat) : Real))
  else 0

def upperNearPerronBound (x : Nat) (T : Real) (n : Nat) : Real :=
  if And (x < n) (n <= 2 * x) then
    8 * (x : Real) * Real.log (2 * (x : Real)) /
      (T * ((n - x : Nat) : Real))
  else 0

theorem lowerNearPerronBound_nonneg
    {x : Nat} (hx : 0 < x) {T : Real} (hT : 0 < T) (n : Nat) :
    0 <= lowerNearPerronBound x T n := by
  unfold lowerNearPerronBound
  split
  case isTrue hnx =>
    have hDist : 0 < ((x - n : Nat) : Real) := by
      exact_mod_cast Nat.sub_pos_of_lt hnx
    have hxOne : (1 : Real) <= (x : Real) := by exact_mod_cast hx
    have hLog : 0 <= Real.log (2 * (x : Real)) := by
      apply Real.log_nonneg
      nlinarith [hxOne]
    positivity
  case isFalse =>
    exact le_refl 0

theorem upperNearPerronBound_nonneg
    {x : Nat} (hx : 0 < x) {T : Real} (hT : 0 < T) (n : Nat) :
    0 <= upperNearPerronBound x T n := by
  unfold upperNearPerronBound
  split
  case isTrue hnear =>
    have hDist : 0 < ((n - x : Nat) : Real) := by
      exact_mod_cast Nat.sub_pos_of_lt hnear.1
    have hxOne : (1 : Real) <= (x : Real) := by exact_mod_cast hx
    have hLog : 0 <= Real.log (2 * (x : Real)) := by
      apply Real.log_nonneg
      nlinarith [hxOne]
    positivity
  case isFalse =>
    exact le_refl 0

theorem summable_lowerNearPerronBound (x : Nat) (T : Real) :
    Summable (lowerNearPerronBound x T) := by
  apply summable_of_ne_finset_zero (s := range x)
  intro n hnMem
  have hnx : Not (n < x) := by
    simpa only [mem_range] using hnMem
  simp [lowerNearPerronBound, hnx]

theorem summable_upperNearPerronBound (x : Nat) (T : Real) :
    Summable (upperNearPerronBound x T) := by
  apply summable_of_ne_finset_zero (s := Ico (x + 1) (2 * x + 1))
  intro n hnMem
  by_cases hnear : And (x < n) (n <= 2 * x)
  case pos =>
    exfalso
    apply hnMem
    exact mem_Ico.mpr (And.intro
      (Nat.add_one_le_iff.mpr hnear.1) (Nat.lt_succ_iff.mpr hnear.2))
  case neg =>
    simp [upperNearPerronBound, hnear]

end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

open Finset
open scoped BigOperators

namespace BombieriVinogradov.SiegelWalfisz

theorem tsum_lowerNearPerronBound_eq (x : Nat) (T : Real) :
    tsum (lowerNearPerronBound x T) =
      (8 * (x : Real) * Real.log (2 * (x : Real)) / T) *
        (harmonic x : Real) := by
  have hTail : forall n : Nat, Not (Membership.mem (range x) n) ->
      lowerNearPerronBound x T n = 0 := by
    intro n hnMem
    have hnx : Not (n < x) := by
      simpa only [mem_range] using hnMem
    simp [lowerNearPerronBound, hnx]
  rw [tsum_eq_sum hTail]
  calc
    Finset.sum (range x) (lowerNearPerronBound x T) =
        Finset.sum (range x) (fun n : Nat =>
          (8 * (x : Real) * Real.log (2 * (x : Real)) / T) *
            (1 / (((x - n : Nat) : Real)))) := by
      apply sum_congr rfl
      intro n hnMem
      have hnx : n < x := mem_range.mp hnMem
      rw [lowerNearPerronBound, if_pos hnx]
      ring
    _ = (8 * (x : Real) * Real.log (2 * (x : Real)) / T) *
        Finset.sum (range x) (fun n : Nat =>
          1 / (((x - n : Nat) : Real))) := by
      rw [Finset.mul_sum]
    _ = (8 * (x : Real) * Real.log (2 * (x : Real)) / T) *
        (harmonic x : Real) := by
      rw [lower_distance_sum_eq_harmonic]

theorem tsum_upperNearPerronBound_eq (x : Nat) (T : Real) :
    tsum (upperNearPerronBound x T) =
      (8 * (x : Real) * Real.log (2 * (x : Real)) / T) *
        (harmonic x : Real) := by
  have hTail : forall n : Nat,
      Not (Membership.mem (Ico (x + 1) (2 * x + 1)) n) ->
        upperNearPerronBound x T n = 0 := by
    intro n hnMem
    by_cases hnear : And (x < n) (n <= 2 * x)
    case pos =>
      exfalso
      apply hnMem
      exact mem_Ico.mpr (And.intro
        (Nat.add_one_le_iff.mpr hnear.1) (Nat.lt_succ_iff.mpr hnear.2))
    case neg =>
      simp [upperNearPerronBound, hnear]
  rw [tsum_eq_sum hTail]
  calc
    Finset.sum (Ico (x + 1) (2 * x + 1))
        (upperNearPerronBound x T) =
      Finset.sum (Ico (x + 1) (2 * x + 1)) (fun n : Nat =>
        (8 * (x : Real) * Real.log (2 * (x : Real)) / T) *
          (1 / (((n - x : Nat) : Real)))) := by
      apply sum_congr rfl
      intro n hnMem
      have hBounds := mem_Ico.mp hnMem
      have hnear : And (x < n) (n <= 2 * x) := by omega
      rw [upperNearPerronBound, if_pos hnear]
      ring
    _ = (8 * (x : Real) * Real.log (2 * (x : Real)) / T) *
        Finset.sum (Ico (x + 1) (2 * x + 1)) (fun n : Nat =>
          1 / (((n - x : Nat) : Real))) := by
      rw [Finset.mul_sum]
    _ = (8 * (x : Real) * Real.log (2 * (x : Real)) / T) *
        (harmonic x : Real) := by
      rw [upper_distance_sum_eq_harmonic]

end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

theorem sourcePerronErrorMajorantTerm_le_farBase
    {x n : Nat} (hx : 0 < x) (hn : 0 < n)
    {c T : Real} (hT : 0 < T)
    (hfar : n <= x / 2 \/ 2 * x <= n) :
    sourcePerronErrorMajorantTerm x c T n <=
      ((x : Real) ^ c / T) *
        norm (LSeries.term
          (fun m : Nat => (ArithmeticFunction.vonMangoldt m : Complex))
          (c : Complex) n) := by
  have hLog := half_le_abs_log_ratio_of_far hx hn hfar
  have hLogNonneg : 0 <= abs (Real.log ((x : Real) / (n : Real))) := abs_nonneg _
  have hPiTwo : (2 : Real) <= Real.pi := by
    linarith [Real.pi_gt_three]
  have hPiLog : 1 <= Real.pi *
      abs (Real.log ((x : Real) / (n : Real))) := by
    calc
      (1 : Real) = 2 * (1 / 2) := by norm_num
      _ <= Real.pi * abs (Real.log ((x : Real) / (n : Real))) := by
        exact mul_le_mul hPiTwo hLog (by norm_num) Real.pi_pos.le
  have hDenom : T <= Real.pi * T *
      abs (Real.log ((x : Real) / (n : Real))) := by
    calc
      T = T * 1 := by ring
      _ <= T * (Real.pi *
          abs (Real.log ((x : Real) / (n : Real)))) :=
        mul_le_mul_of_nonneg_left hPiLog hT.le
      _ = Real.pi * T *
          abs (Real.log ((x : Real) / (n : Real))) := by ring
  have hReciprocal :
      1 / (Real.pi * T * abs (Real.log ((x : Real) / (n : Real)))) <=
        1 / T :=
    one_div_le_one_div_of_le hT hDenom
  have hRatioNe : Ne ((x : Real) / (n : Real)) 1 := by
    intro hRatio
    rw [hRatio, Real.log_one, abs_zero] at hLog
    norm_num at hLog
  rw [sourcePerronErrorMajorantTerm, if_neg (Nat.ne_of_gt hn), if_neg hRatioNe]
  calc
    ArithmeticFunction.vonMangoldt n *
        (((x : Real) / (n : Real)) ^ c *
          min 1 (1 / (Real.pi * T *
            abs (Real.log ((x : Real) / (n : Real)))))) <=
      ArithmeticFunction.vonMangoldt n *
        (((x : Real) / (n : Real)) ^ c *
          (1 / (Real.pi * T *
            abs (Real.log ((x : Real) / (n : Real)))))) := by
      gcongr
      exact min_le_right _ _
    _ <= ArithmeticFunction.vonMangoldt n *
        (((x : Real) / (n : Real)) ^ c * (1 / T)) := by
      gcongr
    _ = ((x : Real) ^ c / T) *
        norm (LSeries.term
          (fun m : Nat => (ArithmeticFunction.vonMangoldt m : Complex))
          (c : Complex) n) := by
      rw [norm_LSeriesTerm_vonMangoldt_eq,
        Real.div_rpow (Nat.cast_nonneg x) (Nat.cast_nonneg n) c]
      ring

end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

theorem sourcePerronErrorMajorantTerm_nonneg
    {x : Nat} (hx : 0 < x) {c T : Real} (hc : 0 <= c) (hT : 0 < T)
    (n : Nat) :
    0 <= sourcePerronErrorMajorantTerm x c T n := by
  by_cases hn : n = 0
  case pos =>
    simp [sourcePerronErrorMajorantTerm, hn]
  case neg =>
    have hnPos : 0 < n := Nat.pos_of_ne_zero hn
    have hRatioPos : 0 < (x : Real) / (n : Real) :=
      div_pos (by exact_mod_cast hx) (by exact_mod_cast hnPos)
    by_cases hRatio : (x : Real) / (n : Real) = 1
    case pos =>
      rw [sourcePerronErrorMajorantTerm, if_neg hn, if_pos hRatio]
      exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
        (div_nonneg hc (mul_nonneg Real.pi_pos.le hT.le))
    case neg =>
      rw [sourcePerronErrorMajorantTerm, if_neg hn, if_neg hRatio]
      have hReciprocal : 0 <= 1 / (Real.pi * T *
          abs (Real.log ((x : Real) / (n : Real)))) := by
        positivity
      exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
        (mul_nonneg (Real.rpow_nonneg hRatioPos.le c)
          (le_min zero_le_one hReciprocal))

end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

def farSourcePerronErrorTerm
    (x : Nat) (c T : Real) (n : Nat) : Real :=
  if n <= x / 2 \/ 2 * x <= n then
    sourcePerronErrorMajorantTerm x c T n
  else 0

theorem farSourcePerronErrorTerm_nonneg
    {x : Nat} (hx : 0 < x) {c T : Real} (hc : 0 <= c) (hT : 0 < T)
    (n : Nat) :
    0 <= farSourcePerronErrorTerm x c T n := by
  unfold farSourcePerronErrorTerm
  split
  case isTrue =>
    exact sourcePerronErrorMajorantTerm_nonneg hx hc hT n
  case isFalse =>
    exact le_refl 0

theorem farSourcePerronErrorTerm_le_base
    {x : Nat} (hx : 0 < x) {c T : Real} (hT : 0 < T) (n : Nat) :
    farSourcePerronErrorTerm x c T n <=
      ((x : Real) ^ c / T) *
        norm (LSeries.term
          (fun m : Nat => (ArithmeticFunction.vonMangoldt m : Complex))
          (c : Complex) n) := by
  by_cases hn : n = 0
  case pos =>
    subst n
    simp [farSourcePerronErrorTerm, sourcePerronErrorMajorantTerm,
      LSeries.term_def]
  case neg =>
    by_cases hfar : n <= x / 2 \/ 2 * x <= n
    case pos =>
      rw [farSourcePerronErrorTerm, if_pos hfar]
      exact sourcePerronErrorMajorantTerm_le_farBase hx
        (Nat.pos_of_ne_zero hn) hT hfar
    case neg =>
      rw [farSourcePerronErrorTerm, if_neg hfar]
      positivity

theorem summable_farSourcePerronErrorTerm
    {x : Nat} (hx : 0 < x) {c T : Real} (hc : 1 < c) (hT : 0 < T) :
    Summable (farSourcePerronErrorTerm x c T) := by
  have hLSeries := ArithmeticFunction.LSeriesSummable_vonMangoldt
    (s := (c : Complex)) (by simpa using hc)
  have hBase : Summable (fun n : Nat =>
      ((x : Real) ^ c / T) *
        norm (LSeries.term
          (fun m : Nat => (ArithmeticFunction.vonMangoldt m : Complex))
          (c : Complex) n)) :=
    hLSeries.norm.mul_left ((x : Real) ^ c / T)
  exact Summable.of_nonneg_of_le
    (fun n => farSourcePerronErrorTerm_nonneg hx
      (le_trans zero_lt_one.le hc.le) hT n)
    (farSourcePerronErrorTerm_le_base hx hT)
    hBase

theorem tsum_farSourcePerronErrorTerm_le
    {x : Nat} (hx : 0 < x) {c T : Real} (hc : 1 < c) (hT : 0 < T) :
    tsum (farSourcePerronErrorTerm x c T) <=
      ((x : Real) ^ c / T) * vonMangoldtLSeriesNormSum c := by
  have hLSeries := ArithmeticFunction.LSeriesSummable_vonMangoldt
    (s := (c : Complex)) (by simpa using hc)
  have hBase : Summable (fun n : Nat =>
      ((x : Real) ^ c / T) *
        norm (LSeries.term
          (fun m : Nat => (ArithmeticFunction.vonMangoldt m : Complex))
          (c : Complex) n)) :=
    hLSeries.norm.mul_left ((x : Real) ^ c / T)
  calc
    tsum (farSourcePerronErrorTerm x c T) <=
        tsum (fun n : Nat =>
          ((x : Real) ^ c / T) *
            norm (LSeries.term
              (fun m : Nat => (ArithmeticFunction.vonMangoldt m : Complex))
              (c : Complex) n)) :=
      (summable_farSourcePerronErrorTerm hx hc hT).tsum_le_tsum
        (farSourcePerronErrorTerm_le_base hx hT) hBase
    _ = ((x : Real) ^ c / T) * vonMangoldtLSeriesNormSum c := by
      rw [tsum_mul_left]
      rfl

end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

theorem cast_sub_div_le_abs_log_ratio_of_lt
    {x n : Nat} (hn : 0 < n) (hnx : n < x) :
    ((x - n : Nat) : Real) / (x : Real) <=
      abs (Real.log ((x : Real) / (n : Real))) := by
  have hx : 0 < x := lt_trans hn hnx
  have hxReal : 0 < (x : Real) := by exact_mod_cast hx
  have hnReal : 0 < (n : Real) := by exact_mod_cast hn
  have hnxReal : (n : Real) < (x : Real) := by exact_mod_cast hnx
  have hRatioPos : 0 < (x : Real) / (n : Real) := div_pos hxReal hnReal
  have hDivMul : ((x : Real) / (n : Real)) * (n : Real) = (x : Real) := by
    field_simp [ne_of_gt hnReal]
  have hRatioOne : (1 : Real) <= (x : Real) / (n : Real) := by
    nlinarith [hnReal, hDivMul, hnxReal]
  have hLogNonneg : 0 <= Real.log ((x : Real) / (n : Real)) :=
    Real.log_nonneg hRatioOne
  have hInverse : (x : Real) / (n : Real) =
      ((n : Real) / (x : Real)) ^ (-1 : Int) := by
    rw [zpow_neg_one]
    field_simp [ne_of_gt hxReal, ne_of_gt hnReal]
  have hLogInverse : Real.log ((x : Real) / (n : Real)) =
      -Real.log ((n : Real) / (x : Real)) := by
    rw [hInverse, zpow_neg_one, Real.log_inv]
  have hBasic := Real.log_le_sub_one_of_pos (div_pos hnReal hxReal)
  have hCastSub : ((x - n : Nat) : Real) = (x : Real) - (n : Real) := by
    rw [Nat.cast_sub hnx.le]
  have hFraction : ((x : Real) - (n : Real)) / (x : Real) =
      1 - (n : Real) / (x : Real) := by
    field_simp [ne_of_gt hxReal]
  rw [abs_of_nonneg hLogNonneg, hLogInverse, hCastSub, hFraction]
  linarith

theorem cast_sub_div_le_abs_log_ratio_of_gt
    {x n : Nat} (hx : 0 < x) (hxn : x < n) :
    ((n - x : Nat) : Real) / (n : Real) <=
      abs (Real.log ((x : Real) / (n : Real))) := by
  have hxReal : 0 < (x : Real) := by exact_mod_cast hx
  have hn : 0 < n := lt_trans hx hxn
  have hnReal : 0 < (n : Real) := by exact_mod_cast hn
  have hxnReal : (x : Real) < (n : Real) := by exact_mod_cast hxn
  have hRatioPos : 0 < (x : Real) / (n : Real) := div_pos hxReal hnReal
  have hDivMul : ((x : Real) / (n : Real)) * (n : Real) = (x : Real) := by
    field_simp [ne_of_gt hnReal]
  have hRatioOne : (x : Real) / (n : Real) <= 1 := by
    nlinarith [hnReal, hDivMul, hxnReal]
  have hLogNonpos : Real.log ((x : Real) / (n : Real)) <= 0 :=
    Real.log_nonpos hRatioPos.le hRatioOne
  have hBasic := Real.log_le_sub_one_of_pos hRatioPos
  have hCastSub : ((n - x : Nat) : Real) = (n : Real) - (x : Real) := by
    rw [Nat.cast_sub hxn.le]
  have hFraction : ((n : Real) - (x : Real)) / (n : Real) =
      1 - (x : Real) / (n : Real) := by
    field_simp [ne_of_gt hnReal]
  rw [abs_of_nonpos hLogNonpos, hCastSub, hFraction]
  linarith

end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

theorem sourcePerronErrorMajorantTerm_le_lowerNear
    {x n : Nat} (hn : 0 < n) (hnHalf : x / 2 < n) (hnx : n < x)
    {c T : Real} (hc0 : 0 <= c) (hc3 : c <= 3) (hT : 0 < T) :
    sourcePerronErrorMajorantTerm x c T n <=
      8 * (x : Real) * Real.log (2 * (x : Real)) /
        (T * ((x - n : Nat) : Real)) := by
  have hx : 0 < x := lt_trans hn hnx
  have hxReal : 0 < (x : Real) := by exact_mod_cast hx
  have hnReal : 0 < (n : Real) := by exact_mod_cast hn
  have hnxReal : (n : Real) < (x : Real) := by exact_mod_cast hnx
  have hRatioPos : 0 < (x : Real) / (n : Real) := div_pos hxReal hnReal
  have hDivMul : ((x : Real) / (n : Real)) * (n : Real) = (x : Real) := by
    field_simp [ne_of_gt hnReal]
  have hTwice : x <= 2 * n := by omega
  have hTwiceReal : (x : Real) <= 2 * (n : Real) := by exact_mod_cast hTwice
  have hRatioTwo : (x : Real) / (n : Real) <= 2 := by
    nlinarith [hnReal, hDivMul, hTwiceReal]
  have hPow : ((x : Real) / (n : Real)) ^ c <= 8 := by
    calc
      ((x : Real) / (n : Real)) ^ c <= (2 : Real) ^ c :=
        Real.rpow_le_rpow hRatioPos.le hRatioTwo hc0
      _ <= (2 : Real) ^ (3 : Real) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hc3
      _ = 8 := by norm_num
  have hnTwoX : n <= 2 * x := by omega
  have hnTwoXReal : (n : Real) <= 2 * (x : Real) := by exact_mod_cast hnTwoX
  have hLambdaLog : ArithmeticFunction.vonMangoldt n <=
      Real.log (2 * (x : Real)) := by
    exact ArithmeticFunction.vonMangoldt_le_log.trans
      (Real.log_le_log hnReal hnTwoXReal)
  have hLogTwoXNonneg : 0 <= Real.log (2 * (x : Real)) := by
    apply Real.log_nonneg
    have hxOne : (1 : Real) <= (x : Real) := by exact_mod_cast hx
    nlinarith [hxOne]
  have hDistance := cast_sub_div_le_abs_log_ratio_of_lt hn hnx
  have hAbsNonneg : 0 <= abs (Real.log ((x : Real) / (n : Real))) := abs_nonneg _
  have hPiOne : (1 : Real) <= Real.pi := by
    linarith [Real.pi_gt_three]
  have hPiLog : ((x - n : Nat) : Real) / (x : Real) <=
      Real.pi * abs (Real.log ((x : Real) / (n : Real))) := by
    calc
      ((x - n : Nat) : Real) / (x : Real) <=
          abs (Real.log ((x : Real) / (n : Real))) := hDistance
      _ = 1 * abs (Real.log ((x : Real) / (n : Real))) := by ring
      _ <= Real.pi * abs (Real.log ((x : Real) / (n : Real))) :=
        mul_le_mul_of_nonneg_right hPiOne hAbsNonneg
  have hDenom : T * (((x - n : Nat) : Real) / (x : Real)) <=
      Real.pi * T * abs (Real.log ((x : Real) / (n : Real))) := by
    calc
      T * (((x - n : Nat) : Real) / (x : Real)) <=
          T * (Real.pi * abs (Real.log ((x : Real) / (n : Real)))) :=
        mul_le_mul_of_nonneg_left hPiLog hT.le
      _ = Real.pi * T * abs (Real.log ((x : Real) / (n : Real))) := by ring
  have hDistPos : 0 < ((x - n : Nat) : Real) := by
    exact_mod_cast Nat.sub_pos_of_lt hnx
  have hBaseDenomPos : 0 <
      T * (((x - n : Nat) : Real) / (x : Real)) := by
    positivity
  have hReciprocal :
      1 / (Real.pi * T * abs (Real.log ((x : Real) / (n : Real)))) <=
        (x : Real) / (T * ((x - n : Nat) : Real)) := by
    calc
      1 / (Real.pi * T * abs (Real.log ((x : Real) / (n : Real)))) <=
          1 / (T * (((x - n : Nat) : Real) / (x : Real))) :=
        one_div_le_one_div_of_le hBaseDenomPos hDenom
      _ = (x : Real) / (T * ((x - n : Nat) : Real)) := by
        field_simp [ne_of_gt hxReal, ne_of_gt hT, ne_of_gt hDistPos]
  have hRatioNe : Ne ((x : Real) / (n : Real)) 1 := by
    intro hRatio
    have heq := (div_eq_one_iff_eq (ne_of_gt hnReal)).mp hRatio
    nlinarith
  rw [sourcePerronErrorMajorantTerm, if_neg (Nat.ne_of_gt hn), if_neg hRatioNe]
  calc
    ArithmeticFunction.vonMangoldt n *
        (((x : Real) / (n : Real)) ^ c *
          min 1 (1 / (Real.pi * T *
            abs (Real.log ((x : Real) / (n : Real)))))) <=
      ArithmeticFunction.vonMangoldt n *
        (((x : Real) / (n : Real)) ^ c *
          (1 / (Real.pi * T *
            abs (Real.log ((x : Real) / (n : Real)))))) := by
      gcongr
      exact min_le_right (1 : Real) _
    _ <= Real.log (2 * (x : Real)) *
        (8 * ((x : Real) / (T * ((x - n : Nat) : Real)))) := by
      exact mul_le_mul hLambdaLog
        (mul_le_mul hPow hReciprocal (by positivity) (by norm_num))
        (mul_nonneg (Real.rpow_nonneg hRatioPos.le c) (by positivity))
        hLogTwoXNonneg
    _ = 8 * (x : Real) * Real.log (2 * (x : Real)) /
        (T * ((x - n : Nat) : Real)) := by ring

end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

theorem sourcePerronErrorMajorantTerm_le_upperNear
    {x n : Nat} (hx : 0 < x) (hxn : x < n) (hnTwice : n <= 2 * x)
    {c T : Real} (hc0 : 0 <= c) (hT : 0 < T) :
    sourcePerronErrorMajorantTerm x c T n <=
      8 * (x : Real) * Real.log (2 * (x : Real)) /
        (T * ((n - x : Nat) : Real)) := by
  have hxReal : 0 < (x : Real) := by exact_mod_cast hx
  have hn : 0 < n := lt_trans hx hxn
  have hnReal : 0 < (n : Real) := by exact_mod_cast hn
  have hxnReal : (x : Real) < (n : Real) := by exact_mod_cast hxn
  have hnTwiceReal : (n : Real) <= 2 * (x : Real) := by exact_mod_cast hnTwice
  have hRatioPos : 0 < (x : Real) / (n : Real) := div_pos hxReal hnReal
  have hDivMul : ((x : Real) / (n : Real)) * (n : Real) = (x : Real) := by
    field_simp [ne_of_gt hnReal]
  have hRatioOne : (x : Real) / (n : Real) <= 1 := by
    nlinarith [hnReal, hDivMul, hxnReal]
  have hPow : ((x : Real) / (n : Real)) ^ c <= 1 := by
    simpa using Real.rpow_le_rpow hRatioPos.le hRatioOne hc0
  have hLambdaLog : ArithmeticFunction.vonMangoldt n <=
      Real.log (2 * (x : Real)) := by
    exact ArithmeticFunction.vonMangoldt_le_log.trans
      (Real.log_le_log hnReal hnTwiceReal)
  have hLogTwoXNonneg : 0 <= Real.log (2 * (x : Real)) := by
    apply Real.log_nonneg
    have hxOne : (1 : Real) <= (x : Real) := by exact_mod_cast hx
    nlinarith [hxOne]
  have hDistance := cast_sub_div_le_abs_log_ratio_of_gt hx hxn
  have hAbsNonneg : 0 <= abs (Real.log ((x : Real) / (n : Real))) := abs_nonneg _
  have hPiOne : (1 : Real) <= Real.pi := by
    linarith [Real.pi_gt_three]
  have hPiLog : ((n - x : Nat) : Real) / (n : Real) <=
      Real.pi * abs (Real.log ((x : Real) / (n : Real))) := by
    calc
      ((n - x : Nat) : Real) / (n : Real) <=
          abs (Real.log ((x : Real) / (n : Real))) := hDistance
      _ = 1 * abs (Real.log ((x : Real) / (n : Real))) := by ring
      _ <= Real.pi * abs (Real.log ((x : Real) / (n : Real))) :=
        mul_le_mul_of_nonneg_right hPiOne hAbsNonneg
  have hDenom : T * (((n - x : Nat) : Real) / (n : Real)) <=
      Real.pi * T * abs (Real.log ((x : Real) / (n : Real))) := by
    calc
      T * (((n - x : Nat) : Real) / (n : Real)) <=
          T * (Real.pi * abs (Real.log ((x : Real) / (n : Real)))) :=
        mul_le_mul_of_nonneg_left hPiLog hT.le
      _ = Real.pi * T * abs (Real.log ((x : Real) / (n : Real))) := by ring
  have hDistPos : 0 < ((n - x : Nat) : Real) := by
    exact_mod_cast Nat.sub_pos_of_lt hxn
  have hBaseDenomPos : 0 <
      T * (((n - x : Nat) : Real) / (n : Real)) := by
    positivity
  have hReciprocal :
      1 / (Real.pi * T * abs (Real.log ((x : Real) / (n : Real)))) <=
        (n : Real) / (T * ((n - x : Nat) : Real)) := by
    calc
      1 / (Real.pi * T * abs (Real.log ((x : Real) / (n : Real)))) <=
          1 / (T * (((n - x : Nat) : Real) / (n : Real))) :=
        one_div_le_one_div_of_le hBaseDenomPos hDenom
      _ = (n : Real) / (T * ((n - x : Nat) : Real)) := by
        field_simp [ne_of_gt hnReal, ne_of_gt hT, ne_of_gt hDistPos]
  have hScaled : (n : Real) / (T * ((n - x : Nat) : Real)) <=
      8 * ((x : Real) / (T * ((n - x : Nat) : Real))) := by
    have hnEight : (n : Real) <= 8 * (x : Real) := by
      nlinarith [hnTwiceReal]
    have hUnitNonneg : 0 <= 1 / (T * ((n - x : Nat) : Real)) := by
      positivity
    calc
      (n : Real) / (T * ((n - x : Nat) : Real)) =
          (n : Real) * (1 / (T * ((n - x : Nat) : Real))) := by ring
      _ <= (8 * (x : Real)) *
          (1 / (T * ((n - x : Nat) : Real))) :=
        mul_le_mul_of_nonneg_right hnEight hUnitNonneg
      _ = 8 * ((x : Real) / (T * ((n - x : Nat) : Real))) := by ring
  have hRatioNe : Ne ((x : Real) / (n : Real)) 1 := by
    intro hRatio
    have heq := (div_eq_one_iff_eq (ne_of_gt hnReal)).mp hRatio
    nlinarith
  rw [sourcePerronErrorMajorantTerm, if_neg (Nat.ne_of_gt hn), if_neg hRatioNe]
  calc
    ArithmeticFunction.vonMangoldt n *
        (((x : Real) / (n : Real)) ^ c *
          min 1 (1 / (Real.pi * T *
            abs (Real.log ((x : Real) / (n : Real)))))) <=
      ArithmeticFunction.vonMangoldt n *
        (((x : Real) / (n : Real)) ^ c *
          (1 / (Real.pi * T *
            abs (Real.log ((x : Real) / (n : Real)))))) := by
      gcongr
      exact min_le_right (1 : Real) _
    _ <= Real.log (2 * (x : Real)) *
        (1 * ((n : Real) / (T * ((n - x : Nat) : Real)))) := by
      exact mul_le_mul hLambdaLog
        (mul_le_mul hPow hReciprocal (by positivity) (by norm_num))
        (mul_nonneg (Real.rpow_nonneg hRatioPos.le c) (by positivity))
        hLogTwoXNonneg
    _ <= Real.log (2 * (x : Real)) *
        (8 * ((x : Real) / (T * ((n - x : Nat) : Real)))) := by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_left hScaled hLogTwoXNonneg
    _ = 8 * (x : Real) * Real.log (2 * (x : Real)) /
        (T * ((n - x : Nat) : Real)) := by ring

end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

theorem sourcePerronErrorMajorantTerm_le_decomposition
    {x : Nat} (hx : 0 < x) {c T : Real}
    (hc0 : 0 <= c) (hc3 : c <= 3) (hT : 0 < T) (n : Nat) :
    sourcePerronErrorMajorantTerm x c T n <=
      farSourcePerronErrorTerm x c T n +
        lowerNearPerronBound x T n +
        endpointPerronBound x c T n +
        upperNearPerronBound x T n := by
  by_cases hfar : n <= x / 2 \/ 2 * x <= n
  case pos =>
    rw [farSourcePerronErrorTerm, if_pos hfar]
    have hLower := lowerNearPerronBound_nonneg hx hT n
    have hEndpoint := endpointPerronBound_nonneg x hc0 hT n
    have hUpper := upperNearPerronBound_nonneg hx hT n
    linarith
  case neg =>
    rw [farSourcePerronErrorTerm, if_neg hfar]
    by_cases hnZero : n = 0
    case pos =>
      subst n
      have hxNe : Ne 0 x := Ne.symm (Nat.ne_of_gt hx)
      have hLower := lowerNearPerronBound_nonneg hx hT 0
      simpa [sourcePerronErrorMajorantTerm, endpointPerronBound,
        upperNearPerronBound, hxNe] using hLower
    case neg =>
      have hn : 0 < n := Nat.pos_of_ne_zero hnZero
      rcases lt_trichotomy n x with hnx | hnx | hxn
      case inl =>
        have hnHalf : x / 2 < n := by
          by_contra hnot
          exact hfar (Or.inl (Nat.le_of_not_gt hnot))
        have hBound := sourcePerronErrorMajorantTerm_le_lowerNear
          hn hnHalf hnx hc0 hc3 hT
        have hne : Ne n x := Nat.ne_of_lt hnx
        have hnotUpper : Not (And (x < n) (n <= 2 * x)) := by
          intro h
          exact (Nat.not_lt_of_ge hnx.le) h.1
        rw [lowerNearPerronBound, if_pos hnx,
          endpointPerronBound, if_neg hne,
          upperNearPerronBound, if_neg hnotUpper]
        simpa only [zero_add, add_zero] using hBound
      case inr.inl =>
        subst n
        have hnotLower : Not (x < x) := Nat.lt_irrefl x
        have hnotUpper : Not (And (x < x) (x <= 2 * x)) := by
          intro h
          exact hnotLower h.1
        rw [lowerNearPerronBound, if_neg hnotLower,
          endpointPerronBound, if_pos rfl,
          upperNearPerronBound, if_neg hnotUpper]
        simpa only [zero_add, add_zero] using
          le_of_eq (sourcePerronErrorMajorantTerm_self hx c T)
      case inr.inr =>
        have hnTwice : n <= 2 * x := by
          by_contra hnot
          exact hfar (Or.inr (Nat.le_of_not_ge hnot))
        have hBound := sourcePerronErrorMajorantTerm_le_upperNear
          hx hxn hnTwice hc0 hT
        have hnotLower : Not (n < x) := Nat.not_lt_of_ge hxn.le
        have hne : Ne n x := Ne.symm (Nat.ne_of_lt hxn)
        have hnear : And (x < n) (n <= 2 * x) := And.intro hxn hnTwice
        rw [lowerNearPerronBound, if_neg hnotLower,
          endpointPerronBound, if_neg hne,
          upperNearPerronBound, if_pos hnear]
        simpa only [zero_add, add_zero] using hBound

end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

theorem tsum_sourcePerronErrorMajorantTerm_le_ranges
    {x : Nat} (hx : 0 < x) {c T : Real}
    (hc1 : 1 < c) (hc3 : c <= 3) (hT : 0 < T) :
    tsum (sourcePerronErrorMajorantTerm x c T) <=
      ((x : Real) ^ c / T) * vonMangoldtLSeriesNormSum c +
        2 * ((8 * (x : Real) * Real.log (2 * (x : Real)) / T) *
          (harmonic x : Real)) +
        ArithmeticFunction.vonMangoldt x * (c / (Real.pi * T)) := by
  have hSource := summable_sourcePerronErrorMajorantTerm hx hc1 hT
  have hFar := summable_farSourcePerronErrorTerm hx hc1 hT
  have hLower := summable_lowerNearPerronBound x T
  have hEndpoint := summable_endpointPerronBound x c T
  have hUpper := summable_upperNearPerronBound x T
  have hAll := ((hFar.add hLower).add hEndpoint).add hUpper
  have hDecomposition :
      tsum (sourcePerronErrorMajorantTerm x c T) <=
        tsum (farSourcePerronErrorTerm x c T) +
          tsum (lowerNearPerronBound x T) +
          tsum (endpointPerronBound x c T) +
          tsum (upperNearPerronBound x T) := by
    calc
      tsum (sourcePerronErrorMajorantTerm x c T) <=
          tsum (fun n : Nat =>
            farSourcePerronErrorTerm x c T n +
              lowerNearPerronBound x T n +
              endpointPerronBound x c T n +
              upperNearPerronBound x T n) :=
        hSource.tsum_le_tsum
          (sourcePerronErrorMajorantTerm_le_decomposition hx
            (le_trans zero_lt_one.le hc1.le) hc3 hT) hAll
      _ = tsum (fun n : Nat =>
            farSourcePerronErrorTerm x c T n +
              lowerNearPerronBound x T n +
              endpointPerronBound x c T n) +
            tsum (upperNearPerronBound x T) :=
        ((hFar.add hLower).add hEndpoint).tsum_add hUpper
      _ = (tsum (fun n : Nat =>
            farSourcePerronErrorTerm x c T n +
              lowerNearPerronBound x T n) +
            tsum (endpointPerronBound x c T)) +
            tsum (upperNearPerronBound x T) := by
        rw [(hFar.add hLower).tsum_add hEndpoint]
      _ = ((tsum (farSourcePerronErrorTerm x c T) +
            tsum (lowerNearPerronBound x T)) +
            tsum (endpointPerronBound x c T)) +
            tsum (upperNearPerronBound x T) := by
        rw [hFar.tsum_add hLower]
  rw [tsum_lowerNearPerronBound_eq,
    tsum_endpointPerronBound_eq, tsum_upperNearPerronBound_eq] at hDecomposition
  calc
    tsum (sourcePerronErrorMajorantTerm x c T) <=
        tsum (farSourcePerronErrorTerm x c T) +
          (8 * (x : Real) * Real.log (2 * (x : Real)) / T) *
            (harmonic x : Real) +
          ArithmeticFunction.vonMangoldt x * (c / (Real.pi * T)) +
          (8 * (x : Real) * Real.log (2 * (x : Real)) / T) *
            (harmonic x : Real) := hDecomposition
    _ <= ((x : Real) ^ c / T) * vonMangoldtLSeriesNormSum c +
          (8 * (x : Real) * Real.log (2 * (x : Real)) / T) *
            (harmonic x : Real) +
          ArithmeticFunction.vonMangoldt x * (c / (Real.pi * T)) +
          (8 * (x : Real) * Real.log (2 * (x : Real)) / T) *
            (harmonic x : Real) := by
      gcongr
      exact tsum_farSourcePerronErrorTerm_le hx hc1 hT
    _ = ((x : Real) ^ c / T) * vonMangoldtLSeriesNormSum c +
        2 * ((8 * (x : Real) * Real.log (2 * (x : Real)) / T) *
          (harmonic x : Real)) +
        ArithmeticFunction.vonMangoldt x * (c / (Real.pi * T)) := by ring

end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

theorem exists_tsum_sourcePerronErrorMajorantTerm_le_scale :
    Exists fun C : Real => And (0 < C) (forall x : Nat, 2 < x ->
      forall c T : Real, 1 < c -> c <= 3 -> 0 < T ->
        tsum (sourcePerronErrorMajorantTerm x c T) <=
          C * (((x : Real) ^ c / (T * (c - 1))) +
            ((x : Real) * Real.log (2 * (x : Real)) ^ 2 / T))) := by
  have hExist := exists_vonMangoldtLSeriesNormSum_le_div_le_three
  let C0 : Real := hExist.choose
  have hSpec := hExist.choose_spec
  have hC0 : 0 < C0 := hSpec.1
  have hSeries := hSpec.2
  refine Exists.intro (C0 + 51) (And.intro (by linarith) ?_)
  intro x hx c T hc1 hc3 hT
  have hxPos : 0 < x := lt_trans zero_lt_two hx
  have hLogOne := one_le_log_two_mul hx
  have hLogNonneg : 0 <= Real.log (2 * (x : Real)) :=
    le_trans zero_le_one hLogOne
  have hRange := tsum_sourcePerronErrorMajorantTerm_le_ranges
    hxPos hc1 hc3 hT
  have hSeriesAt := hSeries c hc1 hc3
  have hcDenom : Ne (c - 1) 0 := ne_of_gt (sub_pos.mpr hc1)
  have hFar : ((x : Real) ^ c / T) * vonMangoldtLSeriesNormSum c <=
      C0 * ((x : Real) ^ c / (T * (c - 1))) := by
    calc
      ((x : Real) ^ c / T) * vonMangoldtLSeriesNormSum c <=
          ((x : Real) ^ c / T) * (C0 / (c - 1)) :=
        mul_le_mul_of_nonneg_left hSeriesAt (by positivity)
      _ = C0 * ((x : Real) ^ c / (T * (c - 1))) := by
        field_simp [ne_of_gt hT, hcDenom]
  have hHarmonic := harmonic_le_three_log_two_mul hxPos
  have hNear :
      2 * ((8 * (x : Real) * Real.log (2 * (x : Real)) / T) *
        (harmonic x : Real)) <=
      48 * ((x : Real) * Real.log (2 * (x : Real)) ^ 2 / T) := by
    calc
      2 * ((8 * (x : Real) * Real.log (2 * (x : Real)) / T) *
          (harmonic x : Real)) <=
        2 * ((8 * (x : Real) * Real.log (2 * (x : Real)) / T) *
          (3 * Real.log (2 * (x : Real)))) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hHarmonic (by positivity)) (by norm_num)
      _ = 48 * ((x : Real) * Real.log (2 * (x : Real)) ^ 2 / T) := by
        ring
  have hEndpoint := endpointPerronBoundValue_le_logSquared hx
    (le_trans zero_lt_one.le hc1.le) hc3 hT
  have hCombined : tsum (sourcePerronErrorMajorantTerm x c T) <=
      C0 * ((x : Real) ^ c / (T * (c - 1))) +
        51 * ((x : Real) * Real.log (2 * (x : Real)) ^ 2 / T) := by
    calc
      tsum (sourcePerronErrorMajorantTerm x c T) <=
          ((x : Real) ^ c / T) * vonMangoldtLSeriesNormSum c +
            2 * ((8 * (x : Real) * Real.log (2 * (x : Real)) / T) *
              (harmonic x : Real)) +
            ArithmeticFunction.vonMangoldt x * (c / (Real.pi * T)) := hRange
      _ <= C0 * ((x : Real) ^ c / (T * (c - 1))) +
            48 * ((x : Real) * Real.log (2 * (x : Real)) ^ 2 / T) +
            3 * (x : Real) * Real.log (2 * (x : Real)) ^ 2 / T := by
        gcongr
      _ = C0 * ((x : Real) ^ c / (T * (c - 1))) +
          51 * ((x : Real) * Real.log (2 * (x : Real)) ^ 2 / T) := by ring
  have hFirstNonneg : 0 <= (x : Real) ^ c / (T * (c - 1)) := by
    positivity
  have hSecondNonneg :
      0 <= (x : Real) * Real.log (2 * (x : Real)) ^ 2 / T := by
    positivity
  calc
    tsum (sourcePerronErrorMajorantTerm x c T) <=
        C0 * ((x : Real) ^ c / (T * (c - 1))) +
          51 * ((x : Real) * Real.log (2 * (x : Real)) ^ 2 / T) := hCombined
    _ <= (C0 + 51) * (((x : Real) ^ c / (T * (c - 1))) +
        ((x : Real) * Real.log (2 * (x : Real)) ^ 2 / T)) := by
      nlinarith [mul_nonneg hC0.le hSecondNonneg,
        mul_nonneg (by norm_num : (0 : Real) <= 51) hFirstNonneg]

end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

theorem exists_norm_explicitFormulaVerticalIntegral_sub_halfSum_le_scale :
    Exists fun C : Real => And (0 < C) (forall N : Nat, forall [NeZero N],
      forall chi : DirichletCharacter Complex N, forall x : Nat, 2 < x ->
      forall c T : Real, 1 < c -> c <= 3 -> 0 < T ->
        norm (explicitFormulaVerticalIntegral chi x c T -
          characterChebyshevHalfSum x chi) <=
          C * (((x : Real) ^ c / (T * (c - 1))) +
            ((x : Real) * Real.log (2 * (x : Real)) ^ 2 / T))) := by
  have hExist := exists_tsum_sourcePerronErrorMajorantTerm_le_scale
  let C : Real := hExist.choose
  have hSpec := hExist.choose_spec
  refine Exists.intro C (And.intro hSpec.1 ?_)
  intro N hNe chi x hx c T hc1 hc3 hT
  exact (norm_explicitFormulaVerticalIntegral_sub_halfSum_le_source chi
    (lt_trans zero_lt_two hx) hc1 hT).trans
      (hSpec.2 x hx c T hc1 hc3 hT)

end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

theorem optimizedPerronScale_le
    {x : Nat} (hx : 2 < x) {T : Real} (hT : 0 < T) :
    ((x : Real) ^ optimizedPerronLine x /
        (T * (optimizedPerronLine x - 1))) +
      ((x : Real) * Real.log (2 * (x : Real)) ^ 2 / T) <=
    4 * ((x : Real) * Real.log (2 * (x : Real)) ^ 2 / T) := by
  have hxPos : 0 < x := lt_trans zero_lt_two hx
  have hxReal : 0 < (x : Real) := by exact_mod_cast hxPos
  have hLogOne := one_le_log_natCast hx
  have hLogPos : 0 < Real.log (x : Real) := lt_of_lt_of_le zero_lt_one hLogOne
  have hLogTwoOne := one_le_log_two_mul hx
  have hLogTwoNonneg : 0 <= Real.log (2 * (x : Real)) :=
    le_trans zero_le_one hLogTwoOne
  have hLogMono : Real.log (x : Real) <=
      Real.log (2 * (x : Real)) := by
    apply Real.log_le_log hxReal
    nlinarith [hxReal]
  have hLogSquare : Real.log (x : Real) <=
      Real.log (2 * (x : Real)) ^ 2 := by
    calc
      Real.log (x : Real) <= Real.log (2 * (x : Real)) := hLogMono
      _ = Real.log (2 * (x : Real)) * 1 := by ring
      _ <= Real.log (2 * (x : Real)) *
          Real.log (2 * (x : Real)) :=
        mul_le_mul_of_nonneg_left hLogTwoOne hLogTwoNonneg
      _ = Real.log (2 * (x : Real)) ^ 2 := by ring
  have hPower := rpow_optimizedPerronLine_eq hx
  have hLineSub : optimizedPerronLine x - 1 =
      1 / Real.log (x : Real) := by
    unfold optimizedPerronLine
    ring
  have hFirstEq :
      (x : Real) ^ optimizedPerronLine x /
          (T * (optimizedPerronLine x - 1)) =
        (x : Real) * Real.exp 1 * Real.log (x : Real) / T := by
    rw [hPower, hLineSub]
    field_simp [ne_of_gt hLogPos, ne_of_gt hT]
  have hExp : Real.exp 1 <= 3 := Real.exp_one_lt_three.le
  have hFirst :
      (x : Real) ^ optimizedPerronLine x /
          (T * (optimizedPerronLine x - 1)) <=
        3 * ((x : Real) * Real.log (2 * (x : Real)) ^ 2 / T) := by
    rw [hFirstEq]
    have hXTNonneg : 0 <= (x : Real) / T := by positivity
    calc
      (x : Real) * Real.exp 1 * Real.log (x : Real) / T =
          ((x : Real) / T) * (Real.exp 1 * Real.log (x : Real)) := by ring
      _ <= ((x : Real) / T) *
          (3 * Real.log (2 * (x : Real)) ^ 2) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul hExp hLogSquare hLogPos.le (by norm_num)) hXTNonneg
      _ = 3 * ((x : Real) * Real.log (2 * (x : Real)) ^ 2 / T) := by ring
  linarith

end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

theorem exists_norm_explicitFormulaVerticalIntegral_sub_halfSum_le_optimized :
    Exists fun C : Real => And (0 < C) (forall N : Nat, forall [NeZero N],
      forall chi : DirichletCharacter Complex N, forall x : Nat, 2 < x ->
      forall T : Real, 0 < T ->
        norm (explicitFormulaVerticalIntegral chi x (optimizedPerronLine x) T -
          characterChebyshevHalfSum x chi) <=
          C * ((x : Real) * Real.log (2 * (x : Real)) ^ 2 / T)) := by
  have hExist := exists_norm_explicitFormulaVerticalIntegral_sub_halfSum_le_scale
  let C0 : Real := hExist.choose
  have hSpec := hExist.choose_spec
  have hC0 : 0 < C0 := hSpec.1
  refine Exists.intro (4 * C0) (And.intro (by positivity) ?_)
  intro N hNe chi x hx T hT
  have hLineLower := optimizedPerronLine_gt_one hx
  have hLineUpper : optimizedPerronLine x <= 3 :=
    (optimizedPerronLine_le_two hx).trans (by norm_num)
  have hGeneral := hSpec.2 N chi x hx (optimizedPerronLine x) T
    hLineLower hLineUpper hT
  have hScale := optimizedPerronScale_le hx hT
  calc
    norm (explicitFormulaVerticalIntegral chi x (optimizedPerronLine x) T -
        characterChebyshevHalfSum x chi) <=
      C0 * (((x : Real) ^ optimizedPerronLine x /
          (T * (optimizedPerronLine x - 1))) +
        ((x : Real) * Real.log (2 * (x : Real)) ^ 2 / T)) := hGeneral
    _ <= C0 *
        (4 * ((x : Real) * Real.log (2 * (x : Real)) ^ 2 / T)) :=
      mul_le_mul_of_nonneg_left hScale hC0.le
    _ = (4 * C0) *
        ((x : Real) * Real.log (2 * (x : Real)) ^ 2 / T) := by ring

end BombieriVinogradov.SiegelWalfisz

end
end

section

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def quadraticCharacterFour : DirichletCharacter ℂ 4 :=
  ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)

theorem quadraticCharacterFour_sq : quadraticCharacterFour ^ 2 = 1 :=
  (ZMod.isQuadratic_χ₄.comp (Int.castRingHom ℂ)).sq_eq_one

theorem quadraticCharacterFour_ne_one : quadraticCharacterFour ≠ 1 := by
  rw [quadraticCharacterFour, MulChar.ringHomComp_ne_one_iff Int.cast_injective]
  intro hone
  have hvalue := congrArg (fun chi : MulChar (ZMod 4) ℤ ↦ chi (3 : ℕ)) hone
  have hthree : ZMod.χ₄ (3 : ℕ) = -1 :=
    ZMod.χ₄_nat_three_mod_four (by norm_num)
  rw [hthree] at hvalue
  have hunit : IsUnit (3 : ZMod 4) := by decide
  have honeValue : (1 : MulChar (ZMod 4) ℤ) ((3 : ℕ) : ZMod 4) = 1 :=
    MulChar.one_apply hunit
  rw [honeValue] at hvalue
  norm_num at hvalue

theorem three_le_level_of_ne_one {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchi : chi ≠ 1) : 3 ≤ N := by
  by_contra hN
  have hNle : N ≤ 2 := by omega
  interval_cases N
  · exact (NeZero.ne 0) rfl
  · exact hchi (Subsingleton.elim _ _)
  · apply hchi
    ext x
    have hx : x = 1 := Subsingleton.elim _ _
    subst x
    simp

theorem primitive_ne_one_of_three_le {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchi : DirichletCharacter.IsPrimitive chi)
    (hN : 3 ≤ N) : chi ≠ 1 := by
  intro hone
  subst chi
  rw [DirichletCharacter.IsPrimitive,
    DirichletCharacter.conductor_one] at hchi
  omega

theorem primitiveCharacter_ne_one {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchi : chi ≠ 1) :
    chi.primitiveCharacter ≠ 1 := by
  intro hprimitive
  apply hchi
  rw [← chi.changeLevel_primitiveCharacter, hprimitive]
  simp

theorem primitiveCharacter_sq_eq_one {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchi : chi ^ 2 = 1) :
    chi.primitiveCharacter ^ 2 = 1 := by
  apply DirichletCharacter.changeLevel_injective chi.conductor_dvd_level
  rw [map_pow, chi.changeLevel_primitiveCharacter, hchi, map_one]

theorem three_le_conductor_of_ne_one {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchi : chi ≠ 1) :
    3 ≤ chi.conductor := by
  let _ : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  exact three_le_level_of_ne_one chi.primitiveCharacter
    (primitiveCharacter_ne_one chi hchi)

theorem quadraticCharacterFour_isPrimitive :
    DirichletCharacter.IsPrimitive quadraticCharacterFour := by
  rw [DirichletCharacter.IsPrimitive]
  have hlower := three_le_conductor_of_ne_one quadraticCharacterFour
    quadraticCharacterFour_ne_one
  have hdvd := quadraticCharacterFour.conductor_dvd_level
  have hupper : quadraticCharacterFour.conductor ≤ 4 :=
    Nat.le_of_dvd (by norm_num) hdvd
  interval_cases quadraticCharacterFour.conductor
  · norm_num at hdvd
  · rfl

theorem crossLevelMul_sq_eq_one {N M : ℕ}
    [NeZero N] [NeZero M] [NeZero (N.lcm M)]
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M)
    (hchiSquare : chi ^ 2 = 1) (hpsiSquare : psi ^ 2 = 1) :
    DirichletCharacter.mul chi psi ^ 2 = 1 := by
  change (DirichletCharacter.changeLevel (Nat.dvd_lcm_left N M) chi *
      DirichletCharacter.changeLevel (Nat.dvd_lcm_right N M) psi) ^ 2 = 1
  rw [mul_pow, ← map_pow, hchiSquare, map_one, ← map_pow, hpsiSquare, map_one, one_mul]

theorem crossLevelMul_ne_one_of_primitive_of_ne {N M : ℕ}
    [NeZero N] [NeZero M] [NeZero (N.lcm M)]
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M)
    (hchi : DirichletCharacter.IsPrimitive chi)
    (hpsi : DirichletCharacter.IsPrimitive psi) (hNM : N ≠ M) :
    DirichletCharacter.mul chi psi ≠ 1 := by
  intro hmul
  change DirichletCharacter.changeLevel (Nat.dvd_lcm_left N M) chi *
      DirichletCharacter.changeLevel (Nat.dvd_lcm_right N M) psi = 1 at hmul
  have hinv : DirichletCharacter.changeLevel (Nat.dvd_lcm_left N M) chi =
      (DirichletCharacter.changeLevel (Nat.dvd_lcm_right N M) psi)⁻¹ :=
    eq_inv_of_mul_eq_one_left hmul
  have hconductor := congrArg DirichletCharacter.conductor hinv
  rw [DirichletCharacter.conductor_changeLevel,
    DirichletCharacter.conductor_inv,
    DirichletCharacter.conductor_changeLevel,
    hchi, hpsi] at hconductor
  exact hNM hconductor

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem quadraticValue_cases {N : ℕ} (χ : DirichletCharacter ℂ N)
    (hχ : χ ^ 2 = 1) (n : ℕ) :
    χ n = 0 ∨ χ n = 1 ∨ χ n = -1 :=
  MulChar.isQuadratic_iff_sq_eq_one.mpr hχ n

end BombieriVinogradov.SiegelWalfisz

end

section

open scoped ComplexOrder

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def characterLevelCorrection {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (s : ℝ) : ℂ :=
  ∏ p ∈ N.primeFactors,
    (1 - chi.primitiveCharacter p * (p : ℂ) ^ (-(s : ℂ)))

theorem characterLevelCorrection_pos {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchiSquare : chi ^ 2 = 1)
    {s : ℝ} (hs : 0 < s) : 0 < characterLevelCorrection chi s := by
  rw [characterLevelCorrection]
  apply Finset.prod_pos
  intro p hp
  have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpgt : (1 : ℝ) < p := by exact_mod_cast hpPrime.one_lt
  have hpnonneg : (0 : ℝ) ≤ p := by positivity
  have hrpowPos : 0 < (p : ℝ) ^ (-s) := Real.rpow_pos_of_pos (by positivity) _
  have hrpowLt : (p : ℝ) ^ (-s) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hpgt (neg_neg_of_pos hs)
  rcases quadraticValue_cases chi.primitiveCharacter
      (primitiveCharacter_sq_eq_one chi hchiSquare) p with hzero | hone | hneg
  · simp [hzero]
  · rw [hone, one_mul, show (-(s : ℂ)) = ((-s : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_natCast p, ← Complex.ofReal_cpow hpnonneg (-s),
      ← Complex.ofReal_one, ← Complex.ofReal_sub]
    exact Complex.zero_lt_real.mpr (sub_pos.mpr hrpowLt)
  · rw [hneg, show (-(s : ℂ)) = ((-s : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_natCast p, ← Complex.ofReal_cpow hpnonneg (-s)]
    convert Complex.zero_lt_real.mpr (show 0 < 1 + (p : ℝ) ^ (-s) by positivity) using 1
    norm_num [Complex.ofReal_add]

theorem LFunction_eq_primitive_mul_correction {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) [NeZero chi.conductor]
    (hchi : chi ≠ 1) {s : ℝ} :
    chi.LFunction s =
      chi.primitiveCharacter.LFunction s * characterLevelCorrection chi s := by
  have hprimitive := primitiveCharacter_ne_one chi hchi
  have hchange := DirichletCharacter.LFunction_changeLevel chi.conductor_dvd_level
    chi.primitiveCharacter (s := (s : ℂ)) (.inl hprimitive)
  rw [chi.changeLevel_primitiveCharacter] at hchange
  exact hchange

end BombieriVinogradov.SiegelWalfisz

end

section

open Filter LSeries Set

namespace BombieriVinogradov.SiegelWalfisz

private theorem quadraticLFunction_im_eq_zero_of_one_lt_bv616 {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchi : chi ^ 2 = 1)
    {x : ℝ} (hx : 1 < x) : (chi.LFunction x).im = 0 := by
  rw [DirichletCharacter.LFunction_eq_LSeries chi (by simpa using hx)]
  rw [LSeries, Complex.im_tsum (chi.LSeriesSummable_of_one_lt_re (by simpa using hx))]
  convert tsum_zero with n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [LSeries.term_of_ne_zero hn]
    rcases quadraticValue_cases chi hchi n with hzero | hone | hneg
    · simp [hzero]
    · rw [hone, ← Complex.ofReal_natCast, ← Complex.ofReal_cpow (Nat.cast_nonneg n)]
      simp
    · rw [hneg, ← Complex.ofReal_natCast, ← Complex.ofReal_cpow (Nat.cast_nonneg n)]
      simp

private theorem quadraticLFunction_im_eq_zero_at_one_bv616 {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchi : chi ^ 2 = 1) (hchi_ne : chi ≠ 1) :
    (chi.LFunction 1).im = 0 := by
  let f : ℝ → ℝ := fun x ↦ (chi.LFunction x).im
  have hLcont : ContinuousAt chi.LFunction (1 : ℂ) :=
    (chi.differentiableAt_LFunction 1 (.inr hchi_ne)).continuousAt
  have hLreal : ContinuousAt (fun x : ℝ ↦ chi.LFunction x) 1 :=
    hLcont.comp_of_eq Complex.continuous_ofReal.continuousAt (by simp)
  have hfcont : ContinuousAt f 1 :=
    Complex.continuous_im.continuousAt.comp' hLreal
  have hlimit : Tendsto f (nhdsWithin 1 (Ioi 1)) (nhds (f 1)) :=
    hfcont.mono_left inf_le_left
  have hzero : Tendsto f (nhdsWithin 1 (Ioi 1)) (nhds 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (quadraticLFunction_im_eq_zero_of_one_lt_bv616 chi hchi hx).symm
  exact tendsto_nhds_unique hlimit hzero

theorem quadraticLFunction_one_re_pos {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchi : chi ^ 2 = 1) (hchi_ne : chi ≠ 1) :
    0 < (chi.LFunction 1).re := by
  have habs : LSeries.abscissaOfAbsConv (chi ·) < ⊤ := by
    rw [DirichletCharacter.absicssaOfAbsConv_eq_one (NeZero.ne N) chi]
    exact EReal.coe_lt_top 1
  have hseries : Tendsto (fun x : ℝ ↦ LSeries (chi ·) x) atTop (nhds 1) := by
    simpa using LSeries.tendsto_atTop habs
  have hL : Tendsto (fun x : ℝ ↦ chi.LFunction x) atTop (nhds 1) := by
    apply hseries.congr'
    filter_upwards [eventually_gt_atTop 1] with x hx
    exact (DirichletCharacter.LFunction_eq_LSeries chi (by simpa using hx)).symm
  have hre : Tendsto (fun x : ℝ ↦ (chi.LFunction x).re) atTop (nhds 1) := by
    convert Complex.continuous_re.continuousAt.tendsto.comp hL using 1 <;>
      simp [Function.comp_def]
  have heventuallyPos : ∀ᶠ x : ℝ in atTop, 0 < (chi.LFunction x).re :=
    hre (Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  obtain ⟨X, hXpos, hXone⟩ :=
    (heventuallyPos.and (eventually_gt_atTop (a := (1 : ℝ)))).exists
  by_contra hnot
  have himOne := quadraticLFunction_im_eq_zero_at_one_bv616 chi hchi hchi_ne
  have hreOne_ne : (chi.LFunction 1).re ≠ 0 := by
    intro hreOne
    apply chi.LFunction_apply_one_ne_zero hchi_ne
    apply Complex.ext
    · simpa using hreOne
    · simpa using himOne
  have hreOne_neg : (chi.LFunction 1).re < 0 :=
    lt_of_le_of_ne (le_of_not_gt hnot) hreOne_ne
  let f : ℝ → ℝ := fun x ↦ (chi.LFunction x).re
  have hfcont : Continuous f := by
    apply continuous_iff_continuousAt.mpr
    intro x
    have hLcont : ContinuousAt chi.LFunction (x : ℂ) :=
      (chi.differentiable_LFunction hchi_ne).continuous.continuousAt
    have hLreal : ContinuousAt (fun y : ℝ ↦ chi.LFunction y) x :=
      hLcont.comp_of_eq Complex.continuous_ofReal.continuousAt rfl
    exact Complex.continuous_re.continuousAt.comp' hLreal
  have hzeroMem : 0 ∈ Icc (f 1) (f X) := ⟨hreOne_neg.le, hXpos.le⟩
  obtain ⟨y, hy, hfy⟩ := intermediate_value_Icc hXone.le hfcont.continuousOn hzeroMem
  have himY : (chi.LFunction y).im = 0 := by
    rcases hy.1.eq_or_lt with rfl | hylt
    · exact himOne
    · exact quadraticLFunction_im_eq_zero_of_one_lt_bv616 chi hchi hylt
  have hLy : chi.LFunction y = 0 := by
    apply Complex.ext
    · simpa [f] using hfy
    · simpa using himY
  exact chi.LFunction_ne_zero_of_one_le_re (.inl hchi_ne) (by simpa using hy.1) hLy

theorem norm_quadraticLFunction_one_eq_re {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchi : chi ^ 2 = 1) (hchi_ne : chi ≠ 1) :
    ‖chi.LFunction 1‖ = (chi.LFunction 1).re := by
  have him := quadraticLFunction_im_eq_zero_at_one_bv616 chi hchi hchi_ne
  have hre := quadraticLFunction_one_re_pos chi hchi hchi_ne
  rw [Complex.norm_def, Complex.normSq_apply, him]
  norm_num [← pow_two, Real.sqrt_sq_eq_abs, abs_of_pos hre]

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

abbrev BoundedDirichletCharacter (N : ℕ) :=
  Σ M : Fin (N + 1), DirichletCharacter ℂ M.val

noncomputable def finiteLevelValue (epsilon : ℝ) {N : ℕ}
    (entry : BoundedDirichletCharacter N) : ℝ := by
  classical
  exact if hlevel : 0 < entry.1.val then
      let _ : NeZero entry.1.val := ⟨hlevel.ne'⟩
      if hquadratic : entry.2 ^ 2 = 1 ∧ Ne entry.2 1 then
        (entry.2.LFunction 1).re * (entry.1.val : ℝ) ^ epsilon
      else
        1
    else
      1

theorem finiteLevelValue_pos (epsilon : ℝ) {N : ℕ}
    (entry : BoundedDirichletCharacter N) :
    0 < finiteLevelValue epsilon entry := by
  classical
  rw [finiteLevelValue]
  split
  · next hlevel =>
      let _ : NeZero entry.1.val := ⟨hlevel.ne'⟩
      split
      · next hquadratic =>
          have hlevelReal : (0 : ℝ) < (entry.1.val : ℕ) := by
            exact_mod_cast hlevel
          exact mul_pos
            (quadraticLFunction_one_re_pos entry.2 hquadratic.1 hquadratic.2)
            (Real.rpow_pos_of_pos hlevelReal epsilon)
      · norm_num
  · norm_num

noncomputable def finiteLevelValues (epsilon : ℝ) (N : ℕ) : Finset ℝ := by
  classical
  exact (Finset.univ : Finset (BoundedDirichletCharacter N)).image
    (finiteLevelValue epsilon)

theorem finiteLevelValues_nonempty (epsilon : ℝ) (N : ℕ) :
    (finiteLevelValues epsilon N).Nonempty := by
  classical
  unfold finiteLevelValues
  exact Finset.image_nonempty.mpr Finset.univ_nonempty

noncomputable def finiteLevelConstant (epsilon : ℝ) (N : ℕ) : ℝ :=
  (finiteLevelValues epsilon N).min' (finiteLevelValues_nonempty epsilon N)

theorem finiteLevelConstant_pos (epsilon : ℝ) (N : ℕ) :
    0 < finiteLevelConstant epsilon N := by
  classical
  have hmem := Finset.min'_mem (finiteLevelValues epsilon N)
    (finiteLevelValues_nonempty epsilon N)
  unfold finiteLevelValues at hmem
  obtain ⟨entry, _, hentry⟩ := Finset.mem_image.mp hmem
  unfold finiteLevelConstant
  unfold finiteLevelValues
  rw [← hentry]
  exact finiteLevelValue_pos epsilon entry

theorem finiteLevelConstant_le_value {epsilon : ℝ} {N M : ℕ}
    [NeZero M] (hMN : M ≤ N) (hM : 3 ≤ M)
    (psi : DirichletCharacter ℂ M) (hpsiSquare : psi ^ 2 = 1)
    (hpsi : Ne psi 1) :
    finiteLevelConstant epsilon N * (M : ℝ) ^ (-epsilon) ≤
      (psi.LFunction 1).re := by
  classical
  let level : Fin (N + 1) := ⟨M, Nat.lt_succ_of_le hMN⟩
  let entry : BoundedDirichletCharacter N := ⟨level, psi⟩
  have hlevel : 0 < level.val := by
    dsimp [level]
    omega
  have hentryValue : finiteLevelValue epsilon entry =
      (psi.LFunction 1).re * (M : ℝ) ^ epsilon := by
    rw [finiteLevelValue]
    simp [entry, level, hlevel, hpsiSquare, hpsi]
  have hentryMem : finiteLevelValue epsilon entry ∈ finiteLevelValues epsilon N := by
    rw [finiteLevelValues]
    exact Finset.mem_image.mpr ⟨entry, Finset.mem_univ _, rfl⟩
  have hminimum : finiteLevelConstant epsilon N ≤ finiteLevelValue epsilon entry := by
    exact Finset.min'_le _ _ hentryMem
  rw [hentryValue] at hminimum
  have hMnonneg : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hMpos : (0 : ℝ) < M := by exact_mod_cast NeZero.pos M
  have hscaled := mul_le_mul_of_nonneg_right hminimum
    (Real.rpow_nonneg hMnonneg (-epsilon))
  calc
    finiteLevelConstant epsilon N * (M : ℝ) ^ (-epsilon) ≤
        ((psi.LFunction 1).re * (M : ℝ) ^ epsilon) *
          (M : ℝ) ^ (-epsilon) := hscaled
    _ = (psi.LFunction 1).re := by
      rw [mul_assoc, ← Real.rpow_add hMpos]
      norm_num

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def siegelLowerEndpoint (epsilon : ℝ) (D : ℕ) : ℝ :=
  max (7 / 8) (1 - epsilon / (2 * ((D : ℝ) + 1)))

theorem seven_eighths_le_siegelLowerEndpoint (epsilon : ℝ) (D : ℕ) :
    7 / 8 ≤ siegelLowerEndpoint epsilon D :=
  le_max_left _ _

theorem siegelLowerEndpoint_lt_one {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (D : ℕ) : siegelLowerEndpoint epsilon D < 1 := by
  apply max_lt
  · norm_num
  · have hdenominator : 0 < 2 * ((D : ℝ) + 1) := by positivity
    have : 0 < epsilon / (2 * ((D : ℝ) + 1)) := div_pos hepsilon hdenominator
    linarith

theorem siegel_exponent_control {epsilon s : ℝ} (hepsilon : 0 < epsilon)
    (D : ℕ) (hs : siegelLowerEndpoint epsilon D ≤ s) :
    (D : ℝ) * (1 - s) + epsilon / 2 ≤ epsilon := by
  have hDnonneg : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  have hDplus : 0 < (D : ℝ) + 1 := by positivity
  have hrange : 1 - epsilon / (2 * ((D : ℝ) + 1)) ≤ s :=
    (le_max_right (7 / 8) (1 - epsilon / (2 * ((D : ℝ) + 1)))).trans hs
  have hgap : 1 - s ≤ epsilon / (2 * ((D : ℝ) + 1)) := by linarith
  have hscaled : (D : ℝ) * (1 - s) ≤
      (D : ℝ) * (epsilon / (2 * ((D : ℝ) + 1))) :=
    mul_le_mul_of_nonneg_left hgap hDnonneg
  have hratio : (D : ℝ) / ((D : ℝ) + 1) ≤ 1 :=
    (div_le_one hDplus).2 (by linarith)
  have habsorb : (D : ℝ) * (epsilon / (2 * ((D : ℝ) + 1))) ≤ epsilon / 2 := by
    calc
      (D : ℝ) * (epsilon / (2 * ((D : ℝ) + 1))) =
          (epsilon / 2) * ((D : ℝ) / ((D : ℝ) + 1)) := by
        field_simp
      _ ≤ epsilon / 2 :=
        mul_le_of_le_one_right (div_nonneg hepsilon.le zero_le_two) hratio
  linarith

end BombieriVinogradov.SiegelWalfisz

end

section

open Metric Set

namespace BombieriVinogradov.SiegelWalfisz

def siegelCauchyCircle : Set ℂ := sphere 2 (3 / 2 : ℝ)

theorem siegelCauchyCircle_re_lower {s : ℂ} (hs : s ∈ siegelCauchyCircle) :
    (1 / 2 : ℝ) ≤ s.re := by
  have hnorm : ‖s - 2‖ = (3 / 2 : ℝ) := by
    simpa [siegelCauchyCircle, mem_sphere, Complex.dist_eq] using hs
  have hre : |s.re - 2| ≤ (3 / 2 : ℝ) := by
    calc
      |s.re - 2| = |(s - 2).re| := by norm_num
      _ ≤ ‖s - 2‖ := Complex.abs_re_le_norm _
      _ = (3 / 2 : ℝ) := hnorm
  linarith [neg_abs_le (s.re - 2)]

theorem siegelCauchyCircle_norm_sub_one_lower {s : ℂ}
    (hs : s ∈ siegelCauchyCircle) : (1 / 2 : ℝ) ≤ ‖s - 1‖ := by
  have hdist : dist s (2 : ℂ) = (3 / 2 : ℝ) := by
    simpa only [siegelCauchyCircle, mem_sphere] using hs
  have htriangle : dist s (2 : ℂ) ≤ dist s (1 : ℂ) + dist (1 : ℂ) (2 : ℂ) :=
    dist_triangle _ _ _
  rw [hdist] at htriangle
  simp only [Complex.dist_eq] at htriangle
  norm_num at htriangle
  have hone : ‖(1 : ℂ)‖ = 1 := by
    simpa only [Nat.cast_one] using Complex.norm_natCast 1
  try rw [hone] at htriangle
  linarith

theorem siegelCauchyCircle_ne_one {s : ℂ} (hs : s ∈ siegelCauchyCircle) : s ≠ 1 := by
  intro h
  subst s
  have hbound := siegelCauchyCircle_norm_sub_one_lower hs
  norm_num at hbound

theorem siegelCauchyCircle_norm_upper {s : ℂ} (hs : s ∈ siegelCauchyCircle) :
    ‖s‖ ≤ (7 / 2 : ℝ) := by
  have hdist : dist s (2 : ℂ) = (3 / 2 : ℝ) := by
    simpa only [siegelCauchyCircle, mem_sphere] using hs
  have htriangle : dist s (0 : ℂ) ≤ dist s (2 : ℂ) + dist (2 : ℂ) (0 : ℂ) :=
    dist_triangle _ _ _
  rw [hdist] at htriangle
  simp only [Complex.dist_eq] at htriangle
  norm_num at htriangle
  linarith

end BombieriVinogradov.SiegelWalfisz

end

section

open Metric Set

namespace BombieriVinogradov.SiegelWalfisz

def siegelAnalyticDomain : Set ℂ := ball 2 (7 / 4 : ℝ)

theorem siegelCauchyCircle_subset_analyticDomain :
    siegelCauchyCircle ⊆ siegelAnalyticDomain := by
  intro s hs
  rw [siegelCauchyCircle, mem_sphere] at hs
  rw [siegelAnalyticDomain, mem_ball]
  linarith

theorem siegelAnalyticDomain_re_lower {s : ℂ} (hs : s ∈ siegelAnalyticDomain) :
    (1 / 4 : ℝ) < s.re := by
  have hnorm : ‖s - 2‖ < (7 / 4 : ℝ) := by
    simpa [siegelAnalyticDomain, mem_ball, Complex.dist_eq] using hs
  have hre : |s.re - 2| < (7 / 4 : ℝ) :=
    (Complex.abs_re_le_norm (s - 2)).trans_lt (by simpa using hnorm)
  linarith [neg_abs_le (s.re - 2)]

theorem siegelAnalyticDomain_norm_upper {s : ℂ} (hs : s ∈ siegelAnalyticDomain) :
    ‖s‖ < (15 / 4 : ℝ) := by
  have hdist : dist s (2 : ℂ) < (7 / 4 : ℝ) := by
    simpa only [siegelAnalyticDomain, mem_ball] using hs
  have htriangle : dist s (0 : ℂ) ≤ dist s (2 : ℂ) + dist (2 : ℂ) (0 : ℂ) :=
    dist_triangle _ _ _
  rw [Complex.dist_eq] at hdist
  simp only [Complex.dist_eq] at htriangle
  norm_num at htriangle
  linarith

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def characterLBlock {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (k : ℕ) (s : ℂ) : ℂ :=
  ∑ j : ZMod N, χ j * ((k * N + j.val : ℕ) : ℂ) ^ (-s)

theorem characterLBlock_recenter {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (k : ℕ) (s : ℂ) :
    characterLBlock χ k s =
      ∑ j : ZMod N, χ j *
        (((k * N + j.val : ℕ) : ℂ) ^ (-s) - (((k + 1) * N : ℕ) : ℂ) ^ (-s)) := by
  rw [characterLBlock]
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  rw [χ.sum_eq_zero_of_ne_one hχ, zero_mul, sub_zero]

theorem characterLBlock_differentiableOn {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (k : ℕ) :
    DifferentiableOn ℂ (characterLBlock χ k) siegelAnalyticDomain := by
  have hN : N ≠ 1 := by
    intro h
    subst N
    exact hχ (Subsingleton.elim _ _)
  rw [show characterLBlock χ k = fun s ↦
      ∑ j : ZMod N, χ j *
        (((k * N + j.val : ℕ) : ℂ) ^ (-s) - (((k + 1) * N : ℕ) : ℂ) ^ (-s)) by
    funext s
    exact characterLBlock_recenter χ hχ k s]
  intro s hs
  apply DifferentiableAt.differentiableWithinAt
  apply DifferentiableAt.fun_sum
  intro j hj
  by_cases hj0 : j = 0
  · subst j
    rw [χ.map_zero' hN]
    simp
  · have hx : ((k * N + j.val : ℕ) : ℂ) ≠ 0 := by
      exact Nat.cast_ne_zero.mpr (by
        have hjv : j.val ≠ 0 := (ZMod.val_ne_zero j).mpr hj0
        omega)
    have hy : ((((k + 1) * N : ℕ) : ℂ)) ≠ 0 := by
      exact Nat.cast_ne_zero.mpr (Nat.mul_ne_zero (by omega) (NeZero.ne N))
    exact (((differentiableAt_id.neg).const_cpow (Or.inl hx)).sub
      ((differentiableAt_id.neg).const_cpow (Or.inl hy))).const_mul (χ j)

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

private theorem sum_zmod_val_inv_le_harmonic_bv622 (N : ℕ) [NeZero N] :
    ∑ j : ZMod N, ((j.val : ℝ)⁻¹) ≤ 2 * (harmonic N : ℝ) := by
  calc
    ∑ j : ZMod N, ((j.val : ℝ)⁻¹) = ∑ i : Fin N, ((i.val : ℝ)⁻¹) := by
      symm
      apply Fintype.sum_equiv (ZMod.finEquiv N).toEquiv
      intro i
      change ((i.val : ℝ)⁻¹) = ((((ZMod.finEquiv N) i).val : ℝ)⁻¹)
      congr 2
      obtain _ | n := N
      · exact (NeZero.ne 0 rfl).elim
      · rfl
    _ ≤ ∑ i : Fin N, 2 * ((((i.val + 1 : ℕ) : ℝ))⁻¹) := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases hi0 : i.val = 0
      · simp [hi0]
      · have hipos : (0 : ℝ) < i.val := by exact_mod_cast Nat.pos_of_ne_zero hi0
        have hisucc : (0 : ℝ) < i.val + 1 := by positivity
        rw [← one_div, ← div_eq_mul_inv]
        norm_num only [Nat.cast_add, Nat.cast_one]
        rw [div_le_div_iff₀ hipos hisucc]
        norm_num
        have hiNat : i.val + 1 ≤ 2 * i.val := by omega
        exact_mod_cast hiNat
    _ = 2 * (harmonic N : ℝ) := by
      rw [← Finset.mul_sum]
      congr 1
      rw [Finset.sum_fin_eq_sum_range, harmonic, Rat.cast_sum]
      apply Finset.sum_congr rfl
      intro x hx
      simp [Finset.mem_range.mp hx]

theorem norm_characterLBlock_zero_one_le {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchi : chi ≠ 1) :
    ‖characterLBlock chi 0 1‖ ≤ 2 * (1 + Real.log N) := by
  have hN : N ≠ 1 := by
    intro h
    subst N
    exact hchi (Subsingleton.elim _ _)
  rw [characterLBlock]
  calc
    ‖∑ j : ZMod N, chi j * (((0 * N + j.val : ℕ) : ℂ) ^ (-(1 : ℂ)))‖ ≤
        ∑ j : ZMod N, ‖chi j * (((0 * N + j.val : ℕ) : ℂ) ^ (-(1 : ℂ)))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ j : ZMod N, ((j.val : ℝ)⁻¹) := by
      apply Finset.sum_le_sum
      intro j hj
      by_cases hj0 : j = 0
      · subst j
        rw [chi.map_zero' hN]
        simp
      · have hjv : j.val ≠ 0 := (ZMod.val_ne_zero j).mpr hj0
        rw [norm_mul]
        calc
          ‖chi j‖ * ‖((0 * N + j.val : ℕ) : ℂ) ^ (-(1 : ℂ))‖ ≤
              1 * ‖((j.val : ℕ) : ℂ) ^ (-(1 : ℂ))‖ := by
            norm_num only [Nat.zero_mul, Nat.zero_add]
            exact mul_le_mul_of_nonneg_right (chi.norm_le_one j) (norm_nonneg _)
          _ = ((j.val : ℝ)⁻¹) := by
            rw [one_mul, show (-(1 : ℂ)) = ((-1 : ℝ) : ℂ) by norm_num,
              ← Complex.ofReal_natCast j.val,
              ← Complex.ofReal_cpow (Nat.cast_nonneg j.val) (-1), Complex.norm_real,
              Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg j.val) _),
              Real.rpow_neg_one]
    _ ≤ 2 * (harmonic N : ℝ) := sum_zmod_val_inv_le_harmonic_bv622 N
    _ ≤ 2 * (1 + Real.log N) := by
      gcongr
      exact harmonic_le_one_add_log N

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem norm_cpow_neg_one_sub_le {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    ‖(x : ℂ) ^ ((-1 : ℝ) : ℂ) - (y : ℂ) ^ ((-1 : ℝ) : ℂ)‖ ≤
      (y - x) / x ^ 2 := by
  have hy : 0 < y := hx.trans_le hxy
  rw [← Complex.ofReal_cpow hx.le (-1), ← Complex.ofReal_cpow hy.le (-1),
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    Real.rpow_neg_one, Real.rpow_neg_one]
  have hinv : y⁻¹ ≤ x⁻¹ := (inv_le_inv₀ hy hx).mpr hxy
  rw [abs_of_nonneg (sub_nonneg.mpr hinv)]
  have hid : x⁻¹ - y⁻¹ = (y - x) / (x * y) := by
    field_simp
  rw [hid, pow_two]
  exact div_le_div_of_nonneg_left (sub_nonneg.mpr hxy) (mul_pos hx hx)
    (mul_le_mul_of_nonneg_left hxy hx.le)

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem norm_characterLBlock_one_le {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchi : chi ≠ 1) {k : ℕ} (hk : 1 ≤ k) :
    ‖characterLBlock chi k 1‖ ≤ ((k : ℝ) ^ 2)⁻¹ := by
  have hN : N ≠ 1 := by
    intro h
    subst N
    exact hchi (Subsingleton.elim _ _)
  rw [characterLBlock_recenter chi hchi]
  calc
    ‖∑ j : ZMod N, chi j *
        (((k * N + j.val : ℕ) : ℂ) ^ (-(1 : ℂ)) -
          (((k + 1) * N : ℕ) : ℂ) ^ (-(1 : ℂ)))‖ ≤
        ∑ j : ZMod N, ‖chi j *
          (((k * N + j.val : ℕ) : ℂ) ^ (-(1 : ℂ)) -
            (((k + 1) * N : ℕ) : ℂ) ^ (-(1 : ℂ)))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _j : ZMod N, (((k : ℝ) ^ 2) * (N : ℝ))⁻¹ := by
      apply Finset.sum_le_sum
      intro j hj
      by_cases hj0 : j = 0
      · subst j
        rw [chi.map_zero' hN]
        simp
        positivity
      · have hjv : j.val ≠ 0 := (ZMod.val_ne_zero j).mpr hj0
        have hxNat : 0 < k * N + j.val := by omega
        have hxyNat : k * N + j.val ≤ (k + 1) * N := by
          have hjlt := j.val_lt
          rw [Nat.add_mul, one_mul]
          omega
        have hlenNat : (k + 1) * N - (k * N + j.val) ≤ N := by
          have hjlt := j.val_lt
          rw [Nat.add_mul, one_mul]
          omega
        have hkN : k * N ≤ k * N + j.val := Nat.le_add_right _ _
        have hx : (0 : ℝ) < (k * N + j.val : ℕ) := by exact_mod_cast hxNat
        have hxy : ((k * N + j.val : ℕ) : ℝ) ≤ ((k + 1) * N : ℕ) := by
          exact_mod_cast hxyNat
        have hlen : (((k + 1) * N : ℕ) : ℝ) - (k * N + j.val : ℕ) ≤ N := by
          rw [← Nat.cast_sub hxyNat]
          exact_mod_cast hlenNat
        have hkNreal : ((k * N : ℕ) : ℝ) ≤ (k * N + j.val : ℕ) := by
          exact_mod_cast hkN
        have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
        have hNpos : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
        have hvar := norm_cpow_neg_one_sub_le hx hxy
        rw [norm_mul]
        calc
          ‖chi j‖ * ‖((k * N + j.val : ℕ) : ℂ) ^ (-(1 : ℂ)) -
              (((k + 1) * N : ℕ) : ℂ) ^ (-(1 : ℂ))‖ ≤
              1 * (((((k + 1) * N : ℕ) : ℝ) - (k * N + j.val : ℕ)) /
                ((k * N + j.val : ℕ) : ℝ) ^ 2) := by
            have hvar' :
                ‖((k * N + j.val : ℕ) : ℂ) ^ (-(1 : ℂ)) -
                  (((k + 1) * N : ℕ) : ℂ) ^ (-(1 : ℂ))‖ ≤
                    ((((k + 1) * N : ℕ) : ℝ) - (k * N + j.val : ℕ)) /
                      ((k * N + j.val : ℕ) : ℝ) ^ 2 := by
              rw [show (-(1 : ℂ)) = ((-1 : ℝ) : ℂ) by norm_num]
              simpa only [Complex.ofReal_natCast] using hvar
            exact mul_le_mul (chi.norm_le_one j) hvar'
              (by positivity) (by positivity)
          _ ≤ (N : ℝ) / ((k * N + j.val : ℕ) : ℝ) ^ 2 := by
            simpa using div_le_div_of_nonneg_right hlen (sq_nonneg _)
          _ ≤ (N : ℝ) / ((k * N : ℕ) : ℝ) ^ 2 := by
            have hkNposNat : 0 < k * N := Nat.mul_pos (lt_of_lt_of_le Nat.zero_lt_one hk) (NeZero.pos N)
            have hdenpos : 0 < (((k * N : ℕ) : ℝ) ^ 2) := by
              exact pow_pos (by exact_mod_cast hkNposNat) 2
            have hsq : (((k * N : ℕ) : ℝ) ^ 2) ≤
                (((k * N + j.val : ℕ) : ℝ) ^ 2) := by
              nlinarith [show (0 : ℝ) ≤ (k * N : ℕ) by positivity]
            exact div_le_div_of_nonneg_left hNpos.le hdenpos hsq
          _ = (((k : ℝ) ^ 2) * (N : ℝ))⁻¹ := by
            norm_num [Nat.cast_mul]
            field_simp
    _ = ((k : ℝ) ^ 2)⁻¹ := by
      simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
      have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hk))
      have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
      field_simp

end BombieriVinogradov.SiegelWalfisz

end

section

open Set

namespace BombieriVinogradov.SiegelWalfisz

theorem norm_cpow_neg_sub_le {s : ℂ} {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y)
    (hre : (1 / 4 : ℝ) ≤ s.re) (hs : ‖s‖ ≤ (15 / 4 : ℝ)) :
    ‖(x : ℂ) ^ (-s) - (y : ℂ) ^ (-s)‖ ≤
      (15 / 4 : ℝ) * (y - x) * x ^ (-5 / 4 : ℝ) := by
  have hs0 : -s ≠ 0 := by
    intro h
    have : s = 0 := neg_eq_zero.mp h
    subst s
    norm_num at hre
  have hderiv (t : ℝ) (ht : t ∈ Icc x y) :
      HasDerivWithinAt (fun u : ℝ ↦ (u : ℂ) ^ (-s))
        ((-s) * (t : ℂ) ^ (-s - 1)) (Icc x y) t := by
    exact (hasDerivAt_ofReal_cpow_const (ne_of_gt (lt_of_lt_of_le zero_lt_one (hx.trans ht.1)))
      hs0).hasDerivWithinAt
  have hbound (t : ℝ) (ht : t ∈ Icc x y) :
      ‖(-s) * (t : ℂ) ^ (-s - 1)‖ ≤ (15 / 4 : ℝ) * x ^ (-5 / 4 : ℝ) := by
    have htpos : 0 < t := lt_of_lt_of_le zero_lt_one (hx.trans ht.1)
    have hpow_exp : t ^ (-s.re - 1) ≤ t ^ (-5 / 4 : ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le
      · exact hx.trans ht.1
      · linarith
    have hpow_base : t ^ (-5 / 4 : ℝ) ≤ x ^ (-5 / 4 : ℝ) := by
      exact Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le zero_lt_one hx) ht.1 (by norm_num)
    rw [norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos htpos]
    exact mul_le_mul hs (hpow_exp.trans hpow_base) (Real.rpow_nonneg htpos.le _) (by norm_num)
  have hmv := (convex_Icc x y : Convex ℝ (Icc x y)).norm_image_sub_le_of_norm_hasDerivWithin_le
    hderiv hbound (left_mem_Icc.mpr hxy) (right_mem_Icc.mpr hxy)
  rw [norm_sub_rev, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hxy)] at hmv
  calc
    ‖(x : ℂ) ^ (-s) - (y : ℂ) ^ (-s)‖
        ≤ ((15 / 4 : ℝ) * x ^ (-5 / 4 : ℝ)) * (y - x) := hmv
    _ = (15 / 4 : ℝ) * (y - x) * x ^ (-5 / 4 : ℝ) := by ring

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def characterLBlockMajorant (N k : ℕ) : ℝ :=
  (15 / 4 : ℝ) * (N : ℝ) ^ 2 * ((k + 1 : ℕ) : ℝ) ^ (-5 / 4 : ℝ)

theorem norm_characterLBlock_le {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (k : ℕ) {s : ℂ}
    (hs : s ∈ siegelAnalyticDomain) :
    ‖characterLBlock χ k s‖ ≤ characterLBlockMajorant N k := by
  have hN : N ≠ 1 := by
    intro h
    subst N
    exact hχ (Subsingleton.elim _ _)
  rw [characterLBlock_recenter χ hχ]
  calc
    ‖∑ j : ZMod N, χ j *
        (((k * N + j.val : ℕ) : ℂ) ^ (-s) - (((k + 1) * N : ℕ) : ℂ) ^ (-s))‖
        ≤ ∑ j : ZMod N, ‖χ j *
          (((k * N + j.val : ℕ) : ℂ) ^ (-s) - (((k + 1) * N : ℕ) : ℂ) ^ (-s))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _j : ZMod N,
        (15 / 4 : ℝ) * (N : ℝ) * ((k + 1 : ℕ) : ℝ) ^ (-5 / 4 : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      by_cases hj0 : j = 0
      · subst j
        rw [χ.map_zero' hN]
        simp only [zero_mul, norm_zero]
        positivity
      · have hjv : j.val ≠ 0 := (ZMod.val_ne_zero j).mpr hj0
        have hxoneNat : 1 ≤ k * N + j.val := by omega
        have hxyNat : k * N + j.val ≤ (k + 1) * N := by
          have hjlt := j.val_lt
          rw [Nat.add_mul, one_mul]
          omega
        have hlenNat : (k + 1) * N - (k * N + j.val) ≤ N := by
          have hjlt := j.val_lt
          rw [Nat.add_mul, one_mul]
          omega
        have hxkNat : k + 1 ≤ k * N + j.val := by
          have hNp := NeZero.pos N
          have hk : k ≤ k * N := by
            simpa using Nat.mul_le_mul_left k hNp
          omega
        have hxone : (1 : ℝ) ≤ (k * N + j.val : ℕ) := by exact_mod_cast hxoneNat
        have hxy : ((k * N + j.val : ℕ) : ℝ) ≤ ((k + 1) * N : ℕ) := by
          exact_mod_cast hxyNat
        have hlen : (((k + 1) * N : ℕ) : ℝ) - (k * N + j.val : ℕ) ≤ N := by
          rw [← Nat.cast_sub hxyNat]
          exact_mod_cast hlenNat
        have hxk : (((k + 1 : ℕ) : ℝ)) ≤ (k * N + j.val : ℕ) := by
          exact_mod_cast hxkNat
        have hpow : ((k * N + j.val : ℕ) : ℝ) ^ (-5 / 4 : ℝ) ≤
            ((k + 1 : ℕ) : ℝ) ^ (-5 / 4 : ℝ) := by
          exact Real.rpow_le_rpow_of_nonpos (by positivity) hxk (by norm_num)
        have hvar := norm_cpow_neg_sub_le hxone hxy
          (le_of_lt (siegelAnalyticDomain_re_lower hs))
          (le_of_lt (siegelAnalyticDomain_norm_upper hs))
        rw [norm_mul]
        calc
          ‖χ j‖ * ‖((k * N + j.val : ℕ) : ℂ) ^ (-s) -
              (((k + 1) * N : ℕ) : ℂ) ^ (-s)‖
              ≤ ‖χ j‖ * ((15 / 4 : ℝ) *
                ((((k + 1) * N : ℕ) : ℝ) - (k * N + j.val : ℕ)) *
                  ((k * N + j.val : ℕ) : ℝ) ^ (-5 / 4 : ℝ)) :=
            mul_le_mul_of_nonneg_left hvar (norm_nonneg _)
          _ ≤ 1 * ((15 / 4 : ℝ) *
                ((((k + 1) * N : ℕ) : ℝ) - (k * N + j.val : ℕ)) *
                  ((k * N + j.val : ℕ) : ℝ) ^ (-5 / 4 : ℝ)) := by
            gcongr
            exact χ.norm_le_one j
          _ = (15 / 4 : ℝ) *
                ((((k + 1) * N : ℕ) : ℝ) - (k * N + j.val : ℕ)) *
                  ((k * N + j.val : ℕ) : ℝ) ^ (-5 / 4 : ℝ) := by ring
          _ ≤ (15 / 4 : ℝ) * (N : ℝ) *
                ((k * N + j.val : ℕ) : ℝ) ^ (-5 / 4 : ℝ) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hlen (by norm_num)) (Real.rpow_nonneg (by positivity) _)
          _ ≤ (15 / 4 : ℝ) * (N : ℝ) * ((k + 1 : ℕ) : ℝ) ^ (-5 / 4 : ℝ) := by
            exact mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = characterLBlockMajorant N k := by
      simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
      rw [characterLBlockMajorant]
      ring

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def characterLBlockSeries {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  ∑' k : ℕ, characterLBlock χ k s

theorem characterLBlockMajorant_summable (N : ℕ) :
    Summable (characterLBlockMajorant N) := by
  have hp : Summable (fun n : ℕ ↦ (n : ℝ) ^ (-5 / 4 : ℝ)) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have hshift := (summable_nat_add_iff 1).mpr hp
  change Summable (fun k : ℕ ↦
    (15 / 4 : ℝ) * (N : ℝ) ^ 2 * ((k + 1 : ℕ) : ℝ) ^ (-5 / 4 : ℝ))
  exact hshift.mul_left ((15 / 4 : ℝ) * (N : ℝ) ^ 2)

theorem characterLBlockSeries_differentiableOn {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) :
    DifferentiableOn ℂ (characterLBlockSeries χ) siegelAnalyticDomain := by
  change DifferentiableOn ℂ (fun s ↦ ∑' k : ℕ, characterLBlock χ k s)
    siegelAnalyticDomain
  exact Complex.differentiableOn_tsum_of_summable_norm
    (characterLBlockMajorant_summable N)
    (fun k ↦ characterLBlock_differentiableOn χ hχ k)
    (by exact Metric.isOpen_ball)
    (fun k s hs ↦ norm_characterLBlock_le χ hχ k hs)

theorem norm_characterLBlockSeries_le {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {s : ℂ}
    (hs : s ∈ siegelAnalyticDomain) :
    ‖characterLBlockSeries χ s‖ ≤ ∑' k : ℕ, characterLBlockMajorant N k := by
  rw [characterLBlockSeries]
  exact tsum_of_norm_bounded (characterLBlockMajorant_summable N).hasSum
    (fun k ↦ norm_characterLBlock_le χ hχ k hs)

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def characterLTailConstant : ℝ :=
  ∑' k : ℕ, ((((k + 1 : ℕ) : ℝ) ^ 2)⁻¹)

theorem characterLTail_summable :
    Summable (fun k : ℕ ↦ ((((k + 1 : ℕ) : ℝ) ^ 2)⁻¹)) := by
  have hp : Summable (fun k : ℕ ↦ (((k : ℝ) ^ 2)⁻¹)) :=
    Real.summable_nat_pow_inv.mpr (by norm_num)
  exact (summable_nat_add_iff 1).mpr hp

theorem characterLTailConstant_nonneg : 0 ≤ characterLTailConstant := by
  rw [characterLTailConstant]
  exact tsum_nonneg fun k ↦ by positivity

theorem characterLBlock_one_norm_summable {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchi : chi ≠ 1) :
    Summable (fun k : ℕ ↦ ‖characterLBlock chi k 1‖) := by
  have hs : (1 : ℂ) ∈ siegelAnalyticDomain := by
    rw [siegelAnalyticDomain, Metric.mem_ball]
    norm_num [Complex.dist_eq]
  exact (characterLBlockMajorant_summable N).of_nonneg_of_le
    (fun k ↦ norm_nonneg _) fun k ↦ norm_characterLBlock_le chi hchi k hs

set_option maxHeartbeats 4000000 in
theorem characterLBlock_tail_norm_le {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchi : chi ≠ 1) :
    ∑' k : ℕ, ‖characterLBlock chi (k + 1) 1‖ ≤ characterLTailConstant := by
  have hnorm := characterLBlock_one_norm_summable chi hchi
  have htailNorm : Summable (fun k : ℕ ↦ ‖characterLBlock chi (k + 1) 1‖) :=
    (summable_nat_add_iff 1).mpr hnorm
  rw [characterLTailConstant]
  exact htailNorm.tsum_le_tsum
    (fun k ↦ norm_characterLBlock_one_le chi hchi (Nat.le_add_left 1 k))
    characterLTail_summable

theorem norm_characterLBlockSeries_one_le {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchi : chi ≠ 1) :
    ‖characterLBlockSeries chi 1‖ ≤
      2 * (1 + Real.log N) + characterLTailConstant := by
  have hnorm := characterLBlock_one_norm_summable chi hchi
  rw [characterLBlockSeries]
  calc
    ‖∑' k : ℕ, characterLBlock chi k 1‖ ≤
        ∑' k : ℕ, ‖characterLBlock chi k 1‖ :=
      norm_tsum_le_tsum_norm hnorm
    _ = ‖characterLBlock chi 0 1‖ +
        ∑' k : ℕ, ‖characterLBlock chi (k + 1) 1‖ := hnorm.tsum_eq_zero_add
    _ ≤ 2 * (1 + Real.log N) + characterLTailConstant :=
      add_le_add (norm_characterLBlock_zero_one_le chi hchi)
        (characterLBlock_tail_norm_le chi hchi)

end BombieriVinogradov.SiegelWalfisz

end

section

open Complex Filter LSeries Metric Set Topology

namespace BombieriVinogradov.SiegelWalfisz

theorem LFunction_eq_characterLBlockSeries_of_one_lt_re {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {s : ℂ} (hs : 1 < s.re) :
    χ.LFunction s = characterLBlockSeries χ s := by
  have hN : N ≠ 1 := by
    intro h
    subst N
    exact hχ (Subsingleton.elim _ _)
  have hzero : (fun n : ℕ ↦ χ n) 0 = 0 := by
    simpa using χ.map_zero' hN
  have hsum : Summable (fun n : ℕ ↦ χ n * (n : ℂ) ^ (-s)) := by
    rw [← funext (LSeries.term_def₀ hzero s)]
    exact DirichletCharacter.LSeriesSummable_of_one_lt_re χ hs
  have hterm (j : ZMod N) (k : ℕ) :
      χ ((j.val + N * k : ℕ) : ZMod N) * ((j.val + N * k : ℕ) : ℂ) ^ (-s) =
        χ j * ((k * N + j.val : ℕ) : ℂ) ^ (-s) := by
    have hcast : ((j.val + N * k : ℕ) : ZMod N) = j := by
      simp [Nat.cast_add, Nat.cast_mul]
    rw [hcast]
    congr 2
    simp only [Nat.add_comm, Nat.mul_comm]
  have hsub (j : ZMod N) :
      Summable (fun k : ℕ ↦ χ j * ((k * N + j.val : ℕ) : ℂ) ^ (-s)) := by
    have hinj : Function.Injective (fun k : ℕ ↦ j.val + N * k) := by
      intro a b hab
      exact Nat.mul_left_cancel (NeZero.pos N) (Nat.add_left_cancel hab)
    have h := hsum.comp_injective hinj
    exact h.congr (hterm j)
  have hswap := Summable.tsum_finsetSum (s := Finset.univ)
    (fun j _hj ↦ hsub j)
  calc
    χ.LFunction s = LSeries (χ ·) s := DirichletCharacter.LFunction_eq_LSeries χ hs
    _ = ∑' n : ℕ, χ n * (n : ℂ) ^ (-s) := by
      rw [LSeries_def₀ hzero]
      congr 1
      funext n
      rw [Complex.cpow_neg, div_eq_mul_inv]
    _ = ∑ j : ZMod N, ∑' k : ℕ,
        χ ((j.val + N * k : ℕ) : ZMod N) * ((j.val + N * k : ℕ) : ℂ) ^ (-s) :=
      Nat.sumByResidueClasses hsum N
    _ = ∑ j : ZMod N, ∑' k : ℕ,
        χ j * ((k * N + j.val : ℕ) : ℂ) ^ (-s) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact tsum_congr (hterm j)
    _ = ∑' k : ℕ, ∑ j : ZMod N,
        χ j * ((k * N + j.val : ℕ) : ℂ) ^ (-s) := by
      simpa only [Finset.mem_univ, ↓reduceIte] using hswap.symm
    _ = characterLBlockSeries χ s := rfl

theorem LFunction_eq_characterLBlockSeries {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {s : ℂ}
    (hs : s ∈ siegelAnalyticDomain) : χ.LFunction s = characterLBlockSeries χ s := by
  have hL : AnalyticOnNhd ℂ (χ.LFunction) siegelAnalyticDomain :=
    (DirichletCharacter.differentiable_LFunction hχ).differentiableOn.analyticOnNhd
      Metric.isOpen_ball
  have hB : AnalyticOnNhd ℂ (characterLBlockSeries χ) siegelAnalyticDomain :=
    (characterLBlockSeries_differentiableOn χ hχ).analyticOnNhd Metric.isOpen_ball
  have h2 : (2 : ℂ) ∈ siegelAnalyticDomain := by
    rw [siegelAnalyticDomain, mem_ball]
    norm_num
  have heq : χ.LFunction =ᶠ[𝓝 (2 : ℂ)] characterLBlockSeries χ := by
    have hV : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
      (continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds (by norm_num)
    filter_upwards [hV] with z hz
    exact LFunction_eq_characterLBlockSeries_of_one_lt_re χ hχ hz
  exact hL.eqOn_of_preconnected_of_eventuallyEq hB
    (convex_ball (2 : ℂ) (7 / 4 : ℝ)).isPreconnected h2 heq hs

end BombieriVinogradov.SiegelWalfisz

end

section

open Metric Set

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def characterLLogBoundConstant : ℝ :=
  2 + characterLTailConstant

theorem characterLLogBoundConstant_pos : 0 < characterLLogBoundConstant := by
  rw [characterLLogBoundConstant]
  linarith [characterLTailConstant_nonneg]

theorem norm_LFunction_one_le_log {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchi : chi ≠ 1) :
    ‖chi.LFunction 1‖ ≤ characterLLogBoundConstant * (1 + Real.log N) := by
  have hs : (1 : ℂ) ∈ siegelAnalyticDomain := by
    rw [siegelAnalyticDomain, mem_ball]
    norm_num [Complex.dist_eq]
  have hlog : 1 ≤ 1 + Real.log N := by
    have hN : (1 : ℝ) ≤ N := by exact_mod_cast NeZero.pos N
    linarith [Real.log_nonneg hN]
  rw [LFunction_eq_characterLBlockSeries chi hchi hs]
  calc
    ‖characterLBlockSeries chi 1‖ ≤
        2 * (1 + Real.log N) + characterLTailConstant :=
      norm_characterLBlockSeries_one_le chi hchi
    _ ≤ characterLLogBoundConstant * (1 + Real.log N) := by
      rw [characterLLogBoundConstant]
      nlinarith [characterLTailConstant_nonneg]

end BombieriVinogradov.SiegelWalfisz

end

section

open Metric Set

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def characterLAbsoluteMajorant (k : ℕ) : ℝ :=
  (15 / 4 : ℝ) * ((k + 1 : ℕ) : ℝ) ^ (-5 / 4 : ℝ)

noncomputable def characterLBoundConstant : ℝ :=
  1 + ∑' k : ℕ, characterLAbsoluteMajorant k

theorem characterLBoundConstant_pos : 0 < characterLBoundConstant := by
  have hnon : 0 ≤ ∑' k : ℕ, characterLAbsoluteMajorant k := by
    apply tsum_nonneg
    intro k
    rw [characterLAbsoluteMajorant]
    positivity
  rw [characterLBoundConstant]
  linarith

theorem norm_LFunction_le_square_on_analyticDomain {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {s : ℂ}
    (hs : s ∈ siegelAnalyticDomain) :
    ‖χ.LFunction s‖ ≤ characterLBoundConstant * (N : ℝ) ^ 2 := by
  rw [LFunction_eq_characterLBlockSeries χ hχ hs]
  apply (norm_characterLBlockSeries_le χ hχ hs).trans
  calc
    ∑' k : ℕ, characterLBlockMajorant N k =
        (N : ℝ) ^ 2 * ∑' k : ℕ, characterLAbsoluteMajorant k := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro k
      rw [characterLAbsoluteMajorant, characterLBlockMajorant]
      ring
    _ ≤ characterLBoundConstant * (N : ℝ) ^ 2 := by
      rw [mul_comm characterLBoundConstant]
      apply mul_le_mul_of_nonneg_left
      · rw [characterLBoundConstant]
        linarith
      · positivity

theorem exists_characterLFunction_circle_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N),
      χ ≠ 1 → ∀ {s : ℂ}, s ∈ siegelCauchyCircle →
        ‖χ.LFunction s‖ ≤ C * (N : ℝ) ^ 2 := by
  exact ⟨characterLBoundConstant, characterLBoundConstant_pos, fun χ hχ s hs ↦
    norm_LFunction_le_square_on_analyticDomain χ hχ
      (siegelCauchyCircle_subset_analyticDomain hs)⟩

theorem norm_LFunction_one_le_square {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) :
    ‖χ.LFunction 1‖ ≤ characterLBoundConstant * (N : ℝ) ^ 2 := by
  apply norm_LFunction_le_square_on_analyticDomain χ hχ
  rw [siegelAnalyticDomain, mem_ball]
  norm_num [Complex.dist_eq]

end BombieriVinogradov.SiegelWalfisz

end

section

open ArithmeticFunction

namespace BombieriVinogradov.SiegelWalfisz

theorem arithmeticFunction_mul_apply_primePower (f g : ArithmeticFunction ℂ)
    {p r : ℕ} (hp : p.Prime) :
    (f * g) (p ^ r) = ∑ i ∈ Finset.range (r + 1), f (p ^ i) * g (p ^ (r - i)) := by
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun x y ↦ f x * g y),
    Nat.sum_divisors_prime_pow hp]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Nat.pow_div (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hp.pos]

noncomputable def characterPairArithmetic {N M : ℕ} (χ : DirichletCharacter ℂ N)
    (ψ : DirichletCharacter ℂ M) : ArithmeticFunction ℂ :=
  toArithmeticFunction fun n ↦ χ n * ψ n

theorem toArithmeticFunction_apply_of_ne_zero (f : ℕ → ℂ) {n : ℕ} (hn : n ≠ 0) :
    toArithmeticFunction f n = f n := by
  simp [toArithmeticFunction, hn]

theorem characterPairArithmetic_isMultiplicative {N M : ℕ}
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M) :
    (characterPairArithmetic χ ψ).IsMultiplicative := by
  refine ArithmeticFunction.IsMultiplicative.iff_ne_zero.mpr ⟨?_, fun {m n} hm hn _ ↦ ?_⟩
  · simp [characterPairArithmetic, toArithmeticFunction]
  · simp [characterPairArithmetic, toArithmeticFunction, hm, hn, map_mul]
    ring

theorem arithmeticZeta_primePower {p i : ℕ} (hp : p.Prime) :
    (ArithmeticFunction.zeta : ArithmeticFunction ℂ) (p ^ i) = 1 := by
  simp [hp.ne_zero]

theorem characterArithmetic_primePower {N : ℕ} (χ : DirichletCharacter ℂ N)
    {p i : ℕ} (hp : p.Prime) :
    toArithmeticFunction (χ ·) (p ^ i) = (χ p) ^ i := by
  rw [← χ.apply_eq_toArithmeticFunction_apply (pow_ne_zero i hp.ne_zero), Nat.cast_pow,
    map_pow]

theorem characterPairArithmetic_primePower {N M : ℕ}
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    {p i : ℕ} (hp : p.Prime) :
    characterPairArithmetic χ ψ (p ^ i) = (χ p * ψ p) ^ i := by
  have hpPow : p ^ i ≠ 0 := pow_ne_zero i hp.ne_zero
  rw [characterPairArithmetic, toArithmeticFunction_apply_of_ne_zero _ hpPow]
  simp only [Nat.cast_pow, map_pow, mul_pow]

noncomputable def siegelProductCoefficients {N M : ℕ} (χ : DirichletCharacter ℂ N)
    (ψ : DirichletCharacter ℂ M) : ArithmeticFunction ℂ :=
  ArithmeticFunction.zeta * toArithmeticFunction (χ ·) * toArithmeticFunction (ψ ·) *
    characterPairArithmetic χ ψ

theorem siegelProductCoefficients_isMultiplicative {N M : ℕ}
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M) :
    (siegelProductCoefficients χ ψ).IsMultiplicative := by
  exact (((isMultiplicative_zeta.natCast.mul χ.isMultiplicative_toArithmeticFunction).mul
    ψ.isMultiplicative_toArithmeticFunction).mul (characterPairArithmetic_isMultiplicative χ ψ))

theorem siegelProductCoefficients_grouped {N M : ℕ}
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M) :
    siegelProductCoefficients χ ψ =
      ((ArithmeticFunction.zeta : ArithmeticFunction ℂ) * toArithmeticFunction (χ ·)) *
        (toArithmeticFunction (ψ ·) * characterPairArithmetic χ ψ) := by
  rw [siegelProductCoefficients, mul_assoc]

theorem siegelProductCoefficients_grouped_swap {N M : ℕ}
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M) :
    siegelProductCoefficients χ ψ =
      ((ArithmeticFunction.zeta : ArithmeticFunction ℂ) * toArithmeticFunction (ψ ·)) *
        (toArithmeticFunction (χ ·) * characterPairArithmetic χ ψ) := by
  rw [siegelProductCoefficients]
  ring

theorem siegelProductCoefficients_outer_expand {N M : ℕ}
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M) (n : ℕ) :
    siegelProductCoefficients χ ψ n =
      ∑ d ∈ n.divisorsAntidiagonal,
        (ArithmeticFunction.zeta * toArithmeticFunction (χ ·) *
          toArithmeticFunction (ψ ·)) d.1 * characterPairArithmetic χ ψ d.2 := by
  rw [siegelProductCoefficients, ArithmeticFunction.mul_apply]

end BombieriVinogradov.SiegelWalfisz

end

section

open ArithmeticFunction
open scoped ComplexOrder

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def localPairCoefficient (a b : ℂ) (r : ℕ) : ℂ :=
  ∑ i ∈ Finset.range (r + 1), a ^ i * b ^ (r - i)

theorem arithmeticFunction_mul_apply_primePower_eq_localPair
    (f g : ArithmeticFunction ℂ) (a b : ℂ) {p r : ℕ} (hp : p.Prime)
    (hf : ∀ i : ℕ, f (p ^ i) = a ^ i) (hg : ∀ i : ℕ, g (p ^ i) = b ^ i) :
    (f * g) (p ^ r) = localPairCoefficient a b r := by
  rw [arithmeticFunction_mul_apply_primePower f g hp, localPairCoefficient]
  apply Finset.sum_congr rfl
  intro i _
  rw [hf, hg]

theorem localPairCoefficient_comm (a b : ℂ) (r : ℕ) :
    localPairCoefficient a b r = localPairCoefficient b a r := by
  simpa [localPairCoefficient] using (Commute.all a b).geom_sum₂_comm (r + 1)

theorem localPairCoefficient_one_left_eq_geom (b : ℂ) (r : ℕ) :
    localPairCoefficient 1 b r = ∑ i ∈ Finset.range (r + 1), b ^ i := by
  calc
    localPairCoefficient 1 b r = localPairCoefficient b 1 r :=
      localPairCoefficient_comm 1 b r
    _ = ∑ i ∈ Finset.range (r + 1), b ^ i := by
      simp [localPairCoefficient]

theorem localPairCoefficient_one_left_nonneg (b : ℂ)
    (hb : b = 0 ∨ b = 1 ∨ b = -1) (r : ℕ) :
    0 ≤ localPairCoefficient 1 b r := by
  rw [localPairCoefficient_one_left_eq_geom]
  rcases hb with rfl | rfl | rfl
  · simp [zero_geom_sum]
  · simp only [one_geom_sum]
    exact_mod_cast Nat.zero_le (r + 1)
  · rw [neg_one_geom_sum]
    split_ifs <;> simp

theorem localPairCoefficient_one_right_nonneg (a : ℂ)
    (ha : a = 0 ∨ a = 1 ∨ a = -1) (r : ℕ) :
    0 ≤ localPairCoefficient a 1 r := by
  rw [localPairCoefficient_comm]
  exact localPairCoefficient_one_left_nonneg a ha r

theorem localPairCoefficient_zero_zero_nonneg (r : ℕ) :
    0 ≤ localPairCoefficient 0 0 r := by
  cases r with
  | zero => simp [localPairCoefficient]
  | succ r =>
      rw [localPairCoefficient]
      apply Finset.sum_nonneg
      intro i hi
      rcases eq_or_ne i 0 with rfl | hi0
      · simp
      · simp [zero_pow hi0]

theorem zeta_mul_character_primePower {N : ℕ} (χ : DirichletCharacter ℂ N)
    {p r : ℕ} (hp : p.Prime) :
    ((ArithmeticFunction.zeta : ArithmeticFunction ℂ) * toArithmeticFunction (χ ·))
        (p ^ r) = localPairCoefficient 1 (χ p) r :=
  arithmeticFunction_mul_apply_primePower_eq_localPair _ _ _ _ hp
    (fun _ ↦ by simpa using arithmeticZeta_primePower hp)
    (fun _ ↦ characterArithmetic_primePower χ hp)

theorem character_mul_pair_primePower {N M : ℕ}
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    {p r : ℕ} (hp : p.Prime) :
    (toArithmeticFunction (χ ·) * characterPairArithmetic χ ψ) (p ^ r) =
      localPairCoefficient (χ p) (χ p * ψ p) r :=
  arithmeticFunction_mul_apply_primePower_eq_localPair _ _ _ _ hp
    (fun _ ↦ characterArithmetic_primePower χ hp)
    (fun _ ↦ characterPairArithmetic_primePower χ ψ hp)

theorem character_right_mul_pair_primePower {N M : ℕ}
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    {p r : ℕ} (hp : p.Prime) :
    (toArithmeticFunction (ψ ·) * characterPairArithmetic χ ψ) (p ^ r) =
      localPairCoefficient (ψ p) (χ p * ψ p) r :=
  arithmeticFunction_mul_apply_primePower_eq_localPair _ _ _ _ hp
    (fun _ ↦ characterArithmetic_primePower ψ hp)
    (fun _ ↦ characterPairArithmetic_primePower χ ψ hp)

end BombieriVinogradov.SiegelWalfisz

end

section

open ArithmeticFunction
open scoped ComplexOrder

namespace BombieriVinogradov.SiegelWalfisz

theorem siegelProductCoefficients_primePower_nonneg {N M : ℕ}
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    (hχ : χ ^ 2 = 1) (hψ : ψ ^ 2 = 1) {p r : ℕ} (hp : p.Prime) :
    0 ≤ siegelProductCoefficients χ ψ (p ^ r) := by
  rcases quadraticValue_cases χ hχ p with hχp | hχp | hχp
  · rw [siegelProductCoefficients_grouped_swap,
      arithmeticFunction_mul_apply_primePower _ _ hp]
    apply Finset.sum_nonneg
    intro i hi
    apply mul_nonneg
    · rw [zeta_mul_character_primePower ψ hp]
      exact localPairCoefficient_one_left_nonneg _ (quadraticValue_cases ψ hψ p) i
    · rw [character_mul_pair_primePower χ ψ hp, hχp, zero_mul]
      exact localPairCoefficient_zero_zero_nonneg (r - i)
  · rw [siegelProductCoefficients_grouped_swap,
      arithmeticFunction_mul_apply_primePower _ _ hp]
    apply Finset.sum_nonneg
    intro i hi
    apply mul_nonneg
    · rw [zeta_mul_character_primePower ψ hp]
      exact localPairCoefficient_one_left_nonneg _ (quadraticValue_cases ψ hψ p) i
    · rw [character_mul_pair_primePower χ ψ hp, hχp, one_mul]
      exact localPairCoefficient_one_left_nonneg _ (quadraticValue_cases ψ hψ p) (r - i)
  · rw [siegelProductCoefficients_grouped,
      arithmeticFunction_mul_apply_primePower _ _ hp]
    apply Finset.sum_nonneg
    intro i hi
    apply mul_nonneg
    · rw [zeta_mul_character_primePower χ hp, hχp]
      exact localPairCoefficient_one_left_nonneg (-1) (Or.inr (Or.inr rfl)) i
    · rw [character_right_mul_pair_primePower χ ψ hp, hχp]
      rcases quadraticValue_cases ψ hψ p with hψp | hψp | hψp
      · rw [hψp]
        norm_num
        exact localPairCoefficient_zero_zero_nonneg (r - i)
      · rw [hψp]
        norm_num
        exact localPairCoefficient_one_left_nonneg (-1) (Or.inr (Or.inr rfl)) (r - i)
      · rw [hψp]
        norm_num
        exact localPairCoefficient_one_right_nonneg (-1) (Or.inr (Or.inr rfl)) (r - i)

end BombieriVinogradov.SiegelWalfisz

end

section

open scoped ComplexOrder

namespace BombieriVinogradov.SiegelWalfisz

theorem siegelProductCoefficients_nonneg {N M : ℕ}
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    (hχ : χ ^ 2 = 1) (hψ : ψ ^ 2 = 1) (n : ℕ) :
    0 ≤ siegelProductCoefficients χ ψ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [ArithmeticFunction.map_zero, le_refl]
  · simpa only [(siegelProductCoefficients_isMultiplicative χ ψ).multiplicative_factorization
      _ hn] using!
      Finset.prod_nonneg fun p hp ↦
        siegelProductCoefficients_primePower_nonneg χ ψ hχ hψ
          (Nat.prime_of_mem_primeFactors hp)

theorem siegelProductCoefficients_one {N M : ℕ}
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M) :
    siegelProductCoefficients χ ψ 1 = 1 :=
  (siegelProductCoefficients_isMultiplicative χ ψ).map_one

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem crossLevelMul_apply_nat {N M : ℕ} (χ : DirichletCharacter ℂ N)
    (ψ : DirichletCharacter ℂ M) (n : ℕ) :
    DirichletCharacter.mul χ ψ n = χ n * ψ n := by
  rw [DirichletCharacter.mul, MulChar.mul_apply]
  by_cases hN : n.Coprime N
  · by_cases hM : n.Coprime M
    · have hLcm : n.Coprime (N.lcm M) :=
        Nat.Coprime.of_dvd_right (Nat.lcm_dvd_mul N M) (hN.mul_right hM)
      have hLcmInt : IsCoprime (n : ℤ) (N.lcm M) :=
        Nat.isCoprime_iff_coprime.mpr hLcm
      have hχEval :
          DirichletCharacter.changeLevel (Nat.dvd_lcm_left N M) χ n = χ n := by
        simpa using DirichletCharacter.changeLevel_eq_cast_of_dvd' χ _ hLcmInt
      have hψEval :
          DirichletCharacter.changeLevel (Nat.dvd_lcm_right N M) ψ n = ψ n := by
        simpa using DirichletCharacter.changeLevel_eq_cast_of_dvd' ψ _ hLcmInt
      rw [hχEval, hψEval]
    · have hLcm : ¬n.Coprime (N.lcm M) := fun h ↦
        hM (Nat.Coprime.of_dvd_right (Nat.dvd_lcm_right N M) h)
      have hLcmInt : ¬IsCoprime (n : ℤ) (N.lcm M) := fun h ↦
        hLcm (Nat.isCoprime_iff_coprime.mp h)
      have hMInt : ¬IsCoprime (n : ℤ) M := fun h ↦
        hM (Nat.isCoprime_iff_coprime.mp h)
      have hLiftZero :
          DirichletCharacter.changeLevel (Nat.dvd_lcm_right N M) ψ n = 0 := by
        simpa using (DirichletCharacter.apply_eq_zero_iff _ _).mpr hLcmInt
      have hZero : ψ n = 0 := by
        simpa using (DirichletCharacter.apply_eq_zero_iff _ _).mpr hMInt
      rw [hLiftZero, hZero, mul_zero, mul_zero]
  · have hLcm : ¬n.Coprime (N.lcm M) := fun h ↦
      hN (Nat.Coprime.of_dvd_right (Nat.dvd_lcm_left N M) h)
    have hLcmInt : ¬IsCoprime (n : ℤ) (N.lcm M) := fun h ↦
      hLcm (Nat.isCoprime_iff_coprime.mp h)
    have hNInt : ¬IsCoprime (n : ℤ) N := fun h ↦
      hN (Nat.isCoprime_iff_coprime.mp h)
    have hLiftZero :
        DirichletCharacter.changeLevel (Nat.dvd_lcm_left N M) χ n = 0 := by
      simpa using (DirichletCharacter.apply_eq_zero_iff _ _).mpr hLcmInt
    have hZero : χ n = 0 := by
      simpa using (DirichletCharacter.apply_eq_zero_iff _ _).mpr hNInt
    rw [hLiftZero, hZero, zero_mul, zero_mul]

end BombieriVinogradov.SiegelWalfisz

end

section

open ArithmeticFunction
open LSeries

namespace BombieriVinogradov.SiegelWalfisz

theorem characterPairArithmetic_eq_crossLevel {N M : ℕ}
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M) :
    characterPairArithmetic χ ψ =
      toArithmeticFunction (DirichletCharacter.mul χ ψ ·) := by
  rw [characterPairArithmetic]
  apply toArithmeticFunction_congr
  intro n _
  exact (crossLevelMul_apply_nat χ ψ n).symm

theorem characterArithmetic_LSeriesSummable {N : ℕ}
    (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (toArithmeticFunction (χ ·)) s := by
  exact (LSeriesSummable_congr s fun hn ↦
    (χ.apply_eq_toArithmeticFunction_apply hn).symm).mpr
      (DirichletCharacter.LSeriesSummable_of_one_lt_re χ hs)

theorem characterPairArithmetic_LSeriesSummable {N M : ℕ}
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (characterPairArithmetic χ ψ) s := by
  rw [characterPairArithmetic_eq_crossLevel]
  exact characterArithmetic_LSeriesSummable (DirichletCharacter.mul χ ψ) hs

theorem siegelProductCoefficients_LSeriesSummable {N M : ℕ}
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (siegelProductCoefficients χ ψ) s := by
  rw [siegelProductCoefficients]
  exact ArithmeticFunction.LSeriesSummable_mul
    (ArithmeticFunction.LSeriesSummable_mul
      (ArithmeticFunction.LSeriesSummable_mul
        (ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hs)
        (characterArithmetic_LSeriesSummable χ hs))
      (characterArithmetic_LSeriesSummable ψ hs))
    (characterPairArithmetic_LSeriesSummable χ ψ hs)

end BombieriVinogradov.SiegelWalfisz

end

section

open ArithmeticFunction
open LSeries

namespace BombieriVinogradov.SiegelWalfisz

theorem characterArithmetic_LSeries_eq_LFunction {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    LSeries (toArithmeticFunction (χ ·)) s = χ.LFunction s := by
  rw [LSeries_congr (fun hn ↦ (χ.apply_eq_toArithmeticFunction_apply hn).symm) s]
  exact (DirichletCharacter.LFunction_eq_LSeries χ hs).symm

theorem characterPairArithmetic_LSeries_eq_LFunction {N M : ℕ} [NeZero N] [NeZero M]
    [NeZero (N.lcm M)]
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (characterPairArithmetic χ ψ) s =
      (DirichletCharacter.mul χ ψ).LFunction s := by
  rw [characterPairArithmetic_eq_crossLevel]
  exact characterArithmetic_LSeries_eq_LFunction (DirichletCharacter.mul χ ψ) hs

theorem siegelProduct_LSeries_eq {N M : ℕ} [NeZero N] [NeZero M]
    [NeZero (N.lcm M)]
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (siegelProductCoefficients χ ψ) s =
      riemannZeta s * χ.LFunction s * ψ.LFunction s *
        (DirichletCharacter.mul χ ψ).LFunction s := by
  have hzeta : LSeriesSummable (ArithmeticFunction.zeta : ArithmeticFunction ℂ) s :=
    ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hs
  have hχ := characterArithmetic_LSeriesSummable χ hs
  have hψ := characterArithmetic_LSeriesSummable ψ hs
  have hpair := characterPairArithmetic_LSeriesSummable χ ψ hs
  rw [siegelProductCoefficients,
    ArithmeticFunction.LSeries_mul'
      (ArithmeticFunction.LSeriesSummable_mul
        (ArithmeticFunction.LSeriesSummable_mul hzeta hχ) hψ) hpair,
    ArithmeticFunction.LSeries_mul'
      (ArithmeticFunction.LSeriesSummable_mul hzeta hχ) hψ,
    ArithmeticFunction.LSeries_mul' hzeta hχ,
    characterArithmetic_LSeries_eq_LFunction χ hs,
    characterArithmetic_LSeries_eq_LFunction ψ hs,
    characterPairArithmetic_LSeries_eq_LFunction χ ψ hs]
  simp_rw [← ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs,
    ← ArithmeticFunction.natCoe_apply]

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def siegelLProduct {N M : ℕ} [NeZero N] [NeZero M] [NeZero (N.lcm M)]
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M) (s : ℂ) : ℂ :=
  χ.LFunction s * ψ.LFunction s * (DirichletCharacter.mul χ ψ).LFunction s

noncomputable def siegelProductResidue {N M : ℕ} [NeZero N] [NeZero M]
    [NeZero (N.lcm M)] (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M) : ℂ :=
  χ.LFunction 1 * ψ.LFunction 1 * (DirichletCharacter.mul χ ψ).LFunction 1

theorem siegelLProduct_differentiable {N M : ℕ} [NeZero N] [NeZero M]
    [NeZero (N.lcm M)] (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    (hχ : χ ≠ 1) (hψ : ψ ≠ 1) (hmul : DirichletCharacter.mul χ ψ ≠ 1) :
    Differentiable ℂ (siegelLProduct χ ψ) := by
  exact ((DirichletCharacter.differentiable_LFunction hχ).mul
    (DirichletCharacter.differentiable_LFunction hψ)).mul
      (DirichletCharacter.differentiable_LFunction hmul)

theorem siegelLProduct_one {N M : ℕ} [NeZero N] [NeZero M] [NeZero (N.lcm M)]
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M) :
    siegelLProduct χ ψ 1 = siegelProductResidue χ ψ :=
  rfl

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def siegelResidueBoundConstant : ℝ := characterLBoundConstant ^ 3

theorem siegelResidueBoundConstant_pos : 0 < siegelResidueBoundConstant := by
  rw [siegelResidueBoundConstant]
  exact pow_pos characterLBoundConstant_pos 3

theorem norm_siegelProductResidue_le {N M : ℕ} [NeZero N] [NeZero M]
    [NeZero (N.lcm M)] (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    (hχ : χ ≠ 1) (hψ : ψ ≠ 1) (hmul : DirichletCharacter.mul χ ψ ≠ 1) :
    ‖siegelProductResidue χ ψ‖ ≤
      siegelResidueBoundConstant * ((N : ℝ) * (M : ℝ)) ^ 4 := by
  have hχb := norm_LFunction_one_le_square χ hχ
  have hψb := norm_LFunction_one_le_square ψ hψ
  have hmulb := norm_LFunction_one_le_square (DirichletCharacter.mul χ ψ) hmul
  have hC : 0 ≤ characterLBoundConstant := characterLBoundConstant_pos.le
  have hNMpos : 0 < N * M := Nat.mul_pos (NeZero.pos N) (NeZero.pos M)
  have hlcmNat : N.lcm M ≤ N * M := Nat.le_of_dvd hNMpos (Nat.lcm_dvd_mul N M)
  have hlcm : ((N.lcm M : ℕ) : ℝ) ≤ (N : ℝ) * (M : ℝ) := by
    exact_mod_cast hlcmNat
  have hlcmSq : ((N.lcm M : ℕ) : ℝ) ^ 2 ≤ ((N : ℝ) * (M : ℝ)) ^ 2 := by
    gcongr
  rw [siegelProductResidue, norm_mul, norm_mul]
  calc
    ‖χ.LFunction 1‖ * ‖ψ.LFunction 1‖ * ‖(DirichletCharacter.mul χ ψ).LFunction 1‖
        ≤ (characterLBoundConstant * (N : ℝ) ^ 2) *
            (characterLBoundConstant * (M : ℝ) ^ 2) *
              (characterLBoundConstant * ((N.lcm M : ℕ) : ℝ) ^ 2) := by
      have hχψ : ‖χ.LFunction 1‖ * ‖ψ.LFunction 1‖ ≤
          (characterLBoundConstant * (N : ℝ) ^ 2) *
            (characterLBoundConstant * (M : ℝ) ^ 2) := by
        exact mul_le_mul hχb hψb (norm_nonneg _) (mul_nonneg hC (sq_nonneg _))
      exact mul_le_mul hχψ hmulb (norm_nonneg _) (mul_nonneg
        (mul_nonneg hC (sq_nonneg _)) (mul_nonneg hC (sq_nonneg _)))
    _ = characterLBoundConstant ^ 3 * ((N : ℝ) * (M : ℝ)) ^ 2 *
          ((N.lcm M : ℕ) : ℝ) ^ 2 := by ring
    _ ≤ characterLBoundConstant ^ 3 * ((N : ℝ) * (M : ℝ)) ^ 2 *
          ((N : ℝ) * (M : ℝ)) ^ 2 := by
      exact mul_le_mul_of_nonneg_left hlcmSq
        (mul_nonneg (pow_nonneg hC _) (sq_nonneg _))
    _ = siegelResidueBoundConstant * ((N : ℝ) * (M : ℝ)) ^ 4 := by
      rw [siegelResidueBoundConstant]
      ring

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem norm_siegelLProduct_le {N M : ℕ} [NeZero N] [NeZero M]
    [NeZero (N.lcm M)] (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    (hχ : χ ≠ 1) (hψ : ψ ≠ 1) (hmul : DirichletCharacter.mul χ ψ ≠ 1)
    {s : ℂ} (hs : s ∈ siegelCauchyCircle) :
    ‖siegelLProduct χ ψ s‖ ≤
      siegelResidueBoundConstant * ((N : ℝ) * (M : ℝ)) ^ 4 := by
  have hsDomain := siegelCauchyCircle_subset_analyticDomain hs
  have hχb := norm_LFunction_le_square_on_analyticDomain χ hχ hsDomain
  have hψb := norm_LFunction_le_square_on_analyticDomain ψ hψ hsDomain
  have hmulb := norm_LFunction_le_square_on_analyticDomain
    (DirichletCharacter.mul χ ψ) hmul hsDomain
  have hC : 0 ≤ characterLBoundConstant := characterLBoundConstant_pos.le
  have hNMpos : 0 < N * M := Nat.mul_pos (NeZero.pos N) (NeZero.pos M)
  have hlcmNat : N.lcm M ≤ N * M := Nat.le_of_dvd hNMpos (Nat.lcm_dvd_mul N M)
  have hlcm : ((N.lcm M : ℕ) : ℝ) ≤ (N : ℝ) * (M : ℝ) := by
    exact_mod_cast hlcmNat
  have hlcmSq : ((N.lcm M : ℕ) : ℝ) ^ 2 ≤ ((N : ℝ) * (M : ℝ)) ^ 2 := by
    gcongr
  rw [siegelLProduct, norm_mul, norm_mul]
  calc
    ‖χ.LFunction s‖ * ‖ψ.LFunction s‖ * ‖(DirichletCharacter.mul χ ψ).LFunction s‖
        ≤ (characterLBoundConstant * (N : ℝ) ^ 2) *
            (characterLBoundConstant * (M : ℝ) ^ 2) *
              (characterLBoundConstant * ((N.lcm M : ℕ) : ℝ) ^ 2) := by
      have hχψ : ‖χ.LFunction s‖ * ‖ψ.LFunction s‖ ≤
          (characterLBoundConstant * (N : ℝ) ^ 2) *
            (characterLBoundConstant * (M : ℝ) ^ 2) := by
        exact mul_le_mul hχb hψb (norm_nonneg _) (mul_nonneg hC (sq_nonneg _))
      exact mul_le_mul hχψ hmulb (norm_nonneg _) (mul_nonneg
        (mul_nonneg hC (sq_nonneg _)) (mul_nonneg hC (sq_nonneg _)))
    _ = characterLBoundConstant ^ 3 * ((N : ℝ) * (M : ℝ)) ^ 2 *
          ((N.lcm M : ℕ) : ℝ) ^ 2 := by ring
    _ ≤ characterLBoundConstant ^ 3 * ((N : ℝ) * (M : ℝ)) ^ 2 *
          ((N : ℝ) * (M : ℝ)) ^ 2 := by
      exact mul_le_mul_of_nonneg_left hlcmSq
        (mul_nonneg (pow_nonneg hC _) (sq_nonneg _))
    _ = siegelResidueBoundConstant * ((N : ℝ) * (M : ℝ)) ^ 4 := by
      rw [siegelResidueBoundConstant]
      ring

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem zetaRegularized_differentiable : Differentiable ℂ riemannZeta₀ :=
  differentiable_riemannZeta₀

theorem riemannZeta_eq_pole_add_regularized {s : ℂ} (hs : s ≠ 1) :
    riemannZeta s = (s - 1)⁻¹ + riemannZeta₀ s :=
  riemannZeta_eq_inv_sub_add hs

end BombieriVinogradov.SiegelWalfisz

end

section

open Metric Set

namespace BombieriVinogradov.SiegelWalfisz

theorem exists_zetaRegularized_circle_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ s ∈ siegelCauchyCircle, ‖riemannZeta₀ s‖ ≤ C := by
  obtain ⟨M, hM⟩ := (isCompact_sphere (2 : ℂ) (3 / 2 : ℝ)).bddAbove_image
    zetaRegularized_differentiable.continuous.norm.continuousOn
  refine ⟨max 1 M, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro s hs
  exact (hM (mem_image_of_mem _ hs)).trans (le_max_right _ _)

theorem exists_riemannZeta_circle_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ s ∈ siegelCauchyCircle, ‖riemannZeta s‖ ≤ C := by
  obtain ⟨C, hC, hregular⟩ := exists_zetaRegularized_circle_bound
  refine ⟨2 + C, by linarith, ?_⟩
  intro s hs
  have hdist := siegelCauchyCircle_norm_sub_one_lower hs
  have hnormpos : 0 < ‖s - 1‖ := lt_of_lt_of_le (by norm_num) hdist
  have hinv : ‖(s - 1)⁻¹‖ ≤ 2 := by
    rw [norm_inv]
    have : 1 * ‖s - 1‖⁻¹ ≤ 2 := by
      rw [mul_inv_le_iff₀ hnormpos]
      linarith
    simpa using this
  rw [riemannZeta_eq_pole_add_regularized (siegelCauchyCircle_ne_one hs)]
  exact (norm_add_le _ _).trans ((add_le_add hinv (hregular s hs)).trans_eq (by ring))

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def entireDividedDifference (f : ℂ → ℂ) (c : ℂ) : ℂ → ℂ :=
  Function.update (fun z ↦ (f z - f c) / (z - c)) c (deriv f c)

theorem entireDividedDifference_apply_of_ne (f : ℂ → ℂ) {c z : ℂ} (hz : z ≠ c) :
    entireDividedDifference f c z = (f z - f c) / (z - c) := by
  rw [entireDividedDifference, Function.update_of_ne hz]

theorem entireDividedDifference_differentiableAt_of_ne (f : ℂ → ℂ) {c z : ℂ}
    (hf : Differentiable ℂ f) (hz : z ≠ c) :
    DifferentiableAt ℂ (entireDividedDifference f c) z := by
  apply DifferentiableAt.congr_of_eventuallyEq
  · have hconst : DifferentiableAt ℂ (fun _ : ℂ ↦ f c) z := by fun_prop
    have hden : DifferentiableAt ℂ (fun w : ℂ ↦ w - c) z := by fun_prop
    exact ((hf z).sub hconst).div hden (sub_ne_zero.mpr hz)
  · filter_upwards [eventually_ne_nhds hz] with w hw
    exact entireDividedDifference_apply_of_ne f hw

theorem entireDividedDifference_differentiable (f : ℂ → ℂ) (c : ℂ)
    (hf : Differentiable ℂ f) :
    Differentiable ℂ (entireDividedDifference f c) := by
  intro z
  rcases eq_or_ne z c with rfl | hz
  · refine (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ ?_).differentiableAt
    · filter_upwards [self_mem_nhdsWithin] with w hw
      exact entireDividedDifference_differentiableAt_of_ne f hf (by simpa using hw)
    · simpa [entireDividedDifference] using (hf z).hasDerivAt.continuousAt_div
  · exact entireDividedDifference_differentiableAt_of_ne f hf hz

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def siegelPoleSubtracted {N M : ℕ} [NeZero N] [NeZero M]
    [NeZero (N.lcm M)] (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M) :
    ℂ → ℂ := fun s ↦
  riemannZeta₀ s * siegelLProduct χ ψ s +
    entireDividedDifference (siegelLProduct χ ψ) 1 s

theorem siegelProduct_sub_pole_entire {N M : ℕ} [NeZero N] [NeZero M]
    [NeZero (N.lcm M)] (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    (hχ : χ ≠ 1) (hψ : ψ ≠ 1) (hmul : DirichletCharacter.mul χ ψ ≠ 1) :
    Differentiable ℂ (siegelPoleSubtracted χ ψ) := by
  exact zetaRegularized_differentiable.mul (siegelLProduct_differentiable χ ψ hχ hψ hmul) |>.add
    (entireDividedDifference_differentiable _ _
      (siegelLProduct_differentiable χ ψ hχ hψ hmul))

theorem siegelPoleSubtracted_apply_of_ne {N M : ℕ} [NeZero N] [NeZero M]
    [NeZero (N.lcm M)] (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    {s : ℂ} (hs : s ≠ 1) :
    siegelPoleSubtracted χ ψ s =
      riemannZeta s * siegelLProduct χ ψ s - siegelProductResidue χ ψ / (s - 1) := by
  rw [siegelPoleSubtracted, entireDividedDifference_apply_of_ne _ hs,
    siegelLProduct_one, riemannZeta_eq_pole_add_regularized hs]
  field_simp [sub_ne_zero.mpr hs]
  ring

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem siegelPoleSubtracted_circle_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ K : ℕ,
      ∀ {N M : ℕ} [NeZero N] [NeZero M] [NeZero (N.lcm M)]
        (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M),
        χ ≠ 1 → ψ ≠ 1 → DirichletCharacter.mul χ ψ ≠ 1 →
          ∀ {s : ℂ}, s ∈ siegelCauchyCircle →
            ‖siegelPoleSubtracted χ ψ s‖ ≤ C * ((N : ℝ) * (M : ℝ)) ^ K := by
  obtain ⟨CriemannZeta, hCriemannZeta, hzeta⟩ := exists_riemannZeta_circle_bound
  refine ⟨(CriemannZeta + 2) * siegelResidueBoundConstant,
    mul_pos (by linarith) siegelResidueBoundConstant_pos, 4, ?_⟩
  intro N M instN instM instLcm χ ψ hχ hψ hmul s hs
  have hL := norm_siegelLProduct_le χ ψ hχ hψ hmul hs
  have hres := norm_siegelProductResidue_le χ ψ hχ hψ hmul
  have hdist := siegelCauchyCircle_norm_sub_one_lower hs
  have hnormpos : 0 < ‖s - 1‖ := lt_of_lt_of_le (by norm_num) hdist
  have hinv : ‖s - 1‖⁻¹ ≤ 2 := by
    have : 1 * ‖s - 1‖⁻¹ ≤ 2 := by
      rw [mul_inv_le_iff₀ hnormpos]
      linarith
    simpa using this
  rw [siegelPoleSubtracted_apply_of_ne χ ψ (siegelCauchyCircle_ne_one hs)]
  calc
    ‖riemannZeta s * siegelLProduct χ ψ s - siegelProductResidue χ ψ / (s - 1)‖
        ≤ ‖riemannZeta s * siegelLProduct χ ψ s‖ +
          ‖siegelProductResidue χ ψ / (s - 1)‖ := norm_sub_le _ _
    _ = ‖riemannZeta s‖ * ‖siegelLProduct χ ψ s‖ +
          ‖siegelProductResidue χ ψ‖ * ‖s - 1‖⁻¹ := by
      rw [norm_mul, norm_div, div_eq_mul_inv]
    _ ≤ CriemannZeta * (siegelResidueBoundConstant * ((N : ℝ) * (M : ℝ)) ^ 4) +
          (siegelResidueBoundConstant * ((N : ℝ) * (M : ℝ)) ^ 4) * 2 := by
      apply add_le_add
      · exact mul_le_mul (hzeta s hs) hL (norm_nonneg _) hCriemannZeta.le
      · exact mul_le_mul hres hinv (inv_nonneg.mpr (norm_nonneg _))
          (mul_nonneg siegelResidueBoundConstant_pos.le (pow_nonneg (by positivity) _))
    _ = ((CriemannZeta + 2) * siegelResidueBoundConstant) * ((N : ℝ) * (M : ℝ)) ^ 4 := by
      ring

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.ComplexAnalysis

noncomputable def taylorCoefficient (f : ℂ → ℂ) (c : ℂ) (n : ℕ) : ℂ :=
  iteratedDeriv n f c / (n.factorial : ℂ)

theorem norm_taylorCoefficient_le {f : ℂ → ℂ} {c : ℂ} {R C : ℝ}
    (n : ℕ) (hR : 0 < R) (hf : Differentiable ℂ f)
    (hC : ∀ z ∈ Metric.sphere c R, ‖f z‖ ≤ C) :
    ‖taylorCoefficient f c n‖ ≤ C / R ^ n := by
  have hderiv := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    n hR hf.diffContOnCl hC
  have hfac : 0 < (n.factorial : ℝ) := by positivity
  rw [taylorCoefficient, norm_div]
  simp only [norm_natCast]
  calc
    ‖iteratedDeriv n f c‖ / n.factorial ≤
        (n.factorial * C / R ^ n) / n.factorial :=
      (div_le_div_iff_of_pos_right hfac).2 hderiv
    _ = C / R ^ n := by
      field_simp [Nat.factorial_ne_zero]

end BombieriVinogradov.ComplexAnalysis

end

section

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def siegelRegularCoefficient {N M : ℕ} [NeZero N] [NeZero M]
    [NeZero (N.lcm M)] (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    (m : ℕ) : ℂ :=
  (-1 : ℂ) ^ m * BombieriVinogradov.ComplexAnalysis.taylorCoefficient
    (siegelPoleSubtracted χ ψ) 2 m

theorem norm_siegelRegularCoefficient {N M : ℕ} [NeZero N] [NeZero M]
    [NeZero (N.lcm M)] (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    (m : ℕ) :
    ‖siegelRegularCoefficient χ ψ m‖ =
      ‖BombieriVinogradov.ComplexAnalysis.taylorCoefficient
        (siegelPoleSubtracted χ ψ) 2 m‖ := by
  rw [siegelRegularCoefficient, norm_mul, norm_pow, norm_neg]
  have hone : ‖(1 : ℂ)‖ = 1 := by
    simpa only [Nat.cast_one] using Complex.norm_natCast 1
  rw [hone, one_pow, one_mul]

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem norm_siegelRegularCoefficient_le_of_circle_bound
    {N M : ℕ} [NeZero N] [NeZero M] [NeZero (N.lcm M)]
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    (hχ : χ ≠ 1) (hψ : ψ ≠ 1) (hmul : DirichletCharacter.mul χ ψ ≠ 1)
    {C : ℝ} {K : ℕ}
    (hcircle : ∀ {s : ℂ}, s ∈ siegelCauchyCircle →
      ‖siegelPoleSubtracted χ ψ s‖ ≤ C * ((N : ℝ) * (M : ℝ)) ^ K)
    (m : ℕ) :
    ‖siegelRegularCoefficient χ ψ m‖ ≤
      C * ((N : ℝ) * (M : ℝ)) ^ K * (2 / 3 : ℝ) ^ m := by
  rw [norm_siegelRegularCoefficient]
  have hcauchy := BombieriVinogradov.ComplexAnalysis.norm_taylorCoefficient_le
    m (by norm_num : (0 : ℝ) < 3 / 2)
    (siegelProduct_sub_pole_entire χ ψ hχ hψ hmul)
    (fun z hz ↦ hcircle hz)
  calc
    ‖BombieriVinogradov.ComplexAnalysis.taylorCoefficient
        (siegelPoleSubtracted χ ψ) 2 m‖
        ≤ (C * ((N : ℝ) * (M : ℝ)) ^ K) / (3 / 2 : ℝ) ^ m := hcauchy
    _ = C * ((N : ℝ) * (M : ℝ)) ^ K * (2 / 3 : ℝ) ^ m := by
      rw [div_eq_mul_inv, ← inv_pow]
      norm_num

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem siegelProduct_coefficient_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ K : ℕ,
      ∀ {N M : ℕ} [NeZero N] [NeZero M] [NeZero (N.lcm M)]
        (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M),
        χ ≠ 1 → ψ ≠ 1 → DirichletCharacter.mul χ ψ ≠ 1 →
          ∀ m : ℕ, ‖siegelRegularCoefficient χ ψ m‖ ≤
            C * ((N : ℝ) * (M : ℝ)) ^ K * (2 / 3 : ℝ) ^ m := by
  obtain ⟨C, hC, K, hcircle⟩ := siegelPoleSubtracted_circle_bound
  refine ⟨C, hC, K, ?_⟩
  intro N M instN instM instLcm χ ψ hχ hψ hmul m
  exact norm_siegelRegularCoefficient_le_of_circle_bound χ ψ hχ hψ hmul
    (hcircle χ ψ hχ hψ hmul) m

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem hasSum_siegelRegularCoefficient {N M : ℕ}
    [NeZero N] [NeZero M] [NeZero (N.lcm M)]
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M)
    (hchi : chi ≠ 1) (hpsi : psi ≠ 1)
    (hmul : DirichletCharacter.mul chi psi ≠ 1) (s : ℂ) :
    HasSum (fun m : ℕ => siegelRegularCoefficient chi psi m * (2 - s) ^ m)
      (siegelPoleSubtracted chi psi s) := by
  have h := Complex.hasSum_taylorSeries_of_entire
    (siegelProduct_sub_pole_entire chi psi hchi hpsi hmul) 2 s
  refine HasSum.congr_fun h (fun m => ?_)
  unfold siegelRegularCoefficient BombieriVinogradov.ComplexAnalysis.taylorCoefficient
  simp only [smul_eq_mul]
  have hpow : (s - 2) ^ m = (-1 : ℂ) ^ m * (2 - s) ^ m := by
    rw [show s - 2 = -(2 - s) by ring, neg_pow]
  rw [hpow]
  field_simp [Nat.factorial_ne_zero]

end BombieriVinogradov.SiegelWalfisz

end

section

open scoped ComplexOrder

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def siegelSourceCoefficient {N M : ℕ}
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M) (m : ℕ) : ℂ :=
  (-1 : ℂ) ^ m * BombieriVinogradov.ComplexAnalysis.taylorCoefficient
    (LSeries (siegelProductCoefficients chi psi)) 2 m

theorem siegelSourceCoefficient_nonneg {N M : ℕ}
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M)
    (hchi : chi ^ 2 = 1) (hpsi : psi ^ 2 = 1) (m : ℕ) :
    0 ≤ siegelSourceCoefficient chi psi m := by
  have hsumm : LSeriesSummable (siegelProductCoefficients chi psi) (3 / 2 : ℂ) :=
    siegelProductCoefficients_LSeriesSummable chi psi (by norm_num)
  have habs : LSeries.abscissaOfAbsConv (siegelProductCoefficients chi psi) < (2 : ℝ) :=
    hsumm.abscissaOfAbsConv_le.trans_lt (by norm_num)
  have hderiv := LSeries.iteratedDeriv_alternating
    (siegelProductCoefficients_nonneg chi psi hchi hpsi) habs m
  have hfactorial : (0 : ℂ) ≤ m.factorial := by positivity
  simpa [siegelSourceCoefficient,
    BombieriVinogradov.ComplexAnalysis.taylorCoefficient, mul_div_assoc] using
      div_nonneg hderiv hfactorial

theorem one_le_siegelSourceCoefficient_zero {N M : ℕ}
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M)
    (hchi : chi ^ 2 = 1) (hpsi : psi ^ 2 = 1) :
    (1 : ℂ) ≤ siegelSourceCoefficient chi psi 0 := by
  rw [siegelSourceCoefficient,
    BombieriVinogradov.ComplexAnalysis.taylorCoefficient]
  simp only [pow_zero, one_mul, iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, div_one]
  rw [LSeries]
  have hsumm : Summable (LSeries.term (siegelProductCoefficients chi psi) 2) :=
    siegelProductCoefficients_LSeriesSummable chi psi (by norm_num)
  calc
    (1 : ℂ) = ∑ n ∈ {1}, LSeries.term (siegelProductCoefficients chi psi) 2 n := by
      simp [LSeries.term_def, siegelProductCoefficients_one]
    _ ≤ ∑' n, LSeries.term (siegelProductCoefficients chi psi) 2 n :=
      hsumm.sum_le_tsum {1} fun n _ =>
        LSeries.term_nonneg (siegelProductCoefficients_nonneg chi psi hchi hpsi n) 2

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem pole_source_coefficient (residue : ℂ) (m : ℕ) :
    (-1 : ℂ) ^ m * BombieriVinogradov.ComplexAnalysis.taylorCoefficient
      (fun s : ℂ => residue / (s - 1)) 2 m = residue := by
  rw [BombieriVinogradov.ComplexAnalysis.taylorCoefficient,
    show (fun s : ℂ => residue / (s - 1)) = fun s : ℂ => residue * (s - 1)⁻¹ by
      funext s
      rw [div_eq_mul_inv],
    iteratedDeriv_const_mul_field]
  simp only [iteratedDeriv_eq_iterate]
  have hinv : deriv^[m] (fun s : ℂ => (s - 1)⁻¹) 2 =
      (-1 : ℂ) ^ m * m.factorial := by
    have h := congrFun (iter_deriv_inv_linear_sub m (1 : ℂ) 1) 2
    norm_num at h
    simpa using h
  rw [hinv]
  field_simp [Nat.factorial_ne_zero]
  have hsign : (((-1 : ℂ) ^ m) ^ 2) = 1 := by
    rw [← pow_mul]
    simp
  rw [hsign, one_mul]

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem siegelSourceCoefficient_eq_regular_add_residue {N M : ℕ}
    [NeZero N] [NeZero M] [NeZero (N.lcm M)]
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M)
    (hchi : chi ≠ 1) (hpsi : psi ≠ 1)
    (hmul : DirichletCharacter.mul chi psi ≠ 1) (m : ℕ) :
    siegelSourceCoefficient chi psi m =
      siegelRegularCoefficient chi psi m + siegelProductResidue chi psi := by
  let halfPlane : Set ℂ := {s | 1 < s.re}
  have hopen : IsOpen halfPlane := isOpen_lt continuous_const Complex.continuous_re
  have htwo : (2 : ℂ) ∈ halfPlane := by norm_num [halfPlane]
  have heq : halfPlane.EqOn (LSeries (siegelProductCoefficients chi psi))
      (fun s => siegelPoleSubtracted chi psi s + siegelProductResidue chi psi / (s - 1)) := by
    intro s hs
    have hsone : s ≠ 1 := by
      intro h
      subst s
      norm_num [halfPlane] at hs
    rw [siegelProduct_LSeries_eq chi psi hs]
    change _ = siegelPoleSubtracted chi psi s + siegelProductResidue chi psi / (s - 1)
    rw [siegelPoleSubtracted_apply_of_ne chi psi hsone]
    rw [siegelLProduct]
    ring
  have hderiv := heq.iteratedDeriv_of_isOpen hopen m htwo
  have hregular : ContDiffAt ℂ m (siegelPoleSubtracted chi psi) 2 :=
    (siegelProduct_sub_pole_entire chi psi hchi hpsi hmul).contDiff.contDiffAt
  have hpole : ContDiffAt ℂ m
      (fun s : ℂ => siegelProductResidue chi psi / (s - 1)) 2 := by
    fun_prop (disch := norm_num)
  change iteratedDeriv m (LSeries (siegelProductCoefficients chi psi)) 2 =
    iteratedDeriv m
      (siegelPoleSubtracted chi psi +
        fun s : ℂ => siegelProductResidue chi psi / (s - 1)) 2 at hderiv
  rw [iteratedDeriv_add hregular hpole] at hderiv
  rw [siegelSourceCoefficient, siegelRegularCoefficient,
    BombieriVinogradov.ComplexAnalysis.taylorCoefficient,
    BombieriVinogradov.ComplexAnalysis.taylorCoefficient, hderiv]
  calc
    (-1 : ℂ) ^ m *
          ((iteratedDeriv m (siegelPoleSubtracted chi psi) 2 +
            iteratedDeriv m (fun s : ℂ => siegelProductResidue chi psi / (s - 1)) 2) /
            (m.factorial : ℂ)) =
        (-1 : ℂ) ^ m *
            (iteratedDeriv m (siegelPoleSubtracted chi psi) 2 / (m.factorial : ℂ)) +
          (-1 : ℂ) ^ m *
            (iteratedDeriv m (fun s : ℂ => siegelProductResidue chi psi / (s - 1)) 2 /
              (m.factorial : ℂ)) := by ring
    _ = (-1 : ℂ) ^ m *
          (iteratedDeriv m (siegelPoleSubtracted chi psi) 2 / (m.factorial : ℂ)) +
        siegelProductResidue chi psi := by
      have hpoleCoefficient := pole_source_coefficient (siegelProductResidue chi psi) m
      rw [BombieriVinogradov.ComplexAnalysis.taylorCoefficient] at hpoleCoefficient
      rw [hpoleCoefficient]

end BombieriVinogradov.SiegelWalfisz

end

section

open scoped ComplexOrder

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def siegelSourcePartialSum {N M : ℕ}
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M)
    (cutoff : ℕ) (t : ℝ) : ℂ :=
  ∑ m ∈ Finset.range cutoff, siegelSourceCoefficient chi psi m * (t : ℂ) ^ m

theorem one_le_siegelSourcePartialSum {N M : ℕ}
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M)
    (hchiSquare : chi ^ 2 = 1) (hpsiSquare : psi ^ 2 = 1)
    {cutoff : ℕ} (hcutoff : 0 < cutoff) {t : ℝ} (ht : 0 ≤ t) :
    (1 : ℂ) ≤ siegelSourcePartialSum chi psi cutoff t := by
  calc
    (1 : ℂ) ≤ siegelSourceCoefficient chi psi 0 :=
      one_le_siegelSourceCoefficient_zero chi psi hchiSquare hpsiSquare
    _ = siegelSourceCoefficient chi psi 0 * (t : ℂ) ^ 0 := by simp
    _ ≤ ∑ m ∈ Finset.range cutoff,
        siegelSourceCoefficient chi psi m * (t : ℂ) ^ m := by
      exact Finset.single_le_sum
        (fun m _ => mul_nonneg
          (siegelSourceCoefficient_nonneg chi psi hchiSquare hpsiSquare m)
          (pow_nonneg (by exact_mod_cast ht) m))
        (Finset.mem_range.mpr hcutoff)

theorem regularPartialSum_eq_source_sub_residue {N M : ℕ}
    [NeZero N] [NeZero M] [NeZero (N.lcm M)]
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M)
    (hchi : chi ≠ 1) (hpsi : psi ≠ 1)
    (hmul : DirichletCharacter.mul chi psi ≠ 1)
    (cutoff : ℕ) (t : ℝ) :
    (∑ m ∈ Finset.range cutoff,
        siegelRegularCoefficient chi psi m * (t : ℂ) ^ m) =
      siegelSourcePartialSum chi psi cutoff t -
        siegelProductResidue chi psi * ∑ m ∈ Finset.range cutoff, (t : ℂ) ^ m := by
  rw [siegelSourcePartialSum]
  simp_rw [siegelSourceCoefficient_eq_regular_add_residue chi psi hchi hpsi hmul]
  simp only [add_mul, Finset.sum_add_distrib, Finset.mul_sum]
  ring

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def regularCoefficientTail
    (a : ℕ → ℂ) (cutoff : ℕ) (t : ℝ) : ℂ :=
  ∑' k : ℕ, a (cutoff + k) * (t : ℂ) ^ (cutoff + k)

theorem norm_regularCoefficientTail_le
    (a : ℕ → ℂ) {A t : ℝ} (cutoff : ℕ)
    (hA : 0 ≤ A) (ht0 : 0 ≤ t) (ht : t ≤ 9 / 8)
    (ha : ∀ m, ‖a m‖ ≤ A * (2 / 3 : ℝ) ^ m) :
    ‖regularCoefficientTail a cutoff t‖ ≤
      4 * A * (3 / 4 : ℝ) ^ cutoff := by
  have hterm (k : ℕ) :
      ‖a (cutoff + k) * (t : ℂ) ^ (cutoff + k)‖ ≤
        A * (3 / 4 : ℝ) ^ (cutoff + k) := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
    calc
      ‖a (cutoff + k)‖ * t ^ (cutoff + k) ≤
          (A * (2 / 3 : ℝ) ^ (cutoff + k)) * t ^ (cutoff + k) :=
        mul_le_mul_of_nonneg_right (ha _) (pow_nonneg ht0 _)
      _ = A * ((2 / 3 : ℝ) * t) ^ (cutoff + k) := by
        rw [mul_assoc, mul_pow]
      _ ≤ A * (3 / 4 : ℝ) ^ (cutoff + k) := by
        gcongr
        nlinarith
  have hgeom : HasSum (fun k : ℕ => (3 / 4 : ℝ) ^ k) 4 := by
    have h := hasSum_geometric_of_norm_lt_one (ξ := (3 / 4 : ℝ)) (by norm_num)
    norm_num at h
    exact h
  have hmajor : HasSum (fun k : ℕ => A * (3 / 4 : ℝ) ^ (cutoff + k))
      (4 * A * (3 / 4 : ℝ) ^ cutoff) := by
    have h := hgeom.mul_left (A * (3 / 4 : ℝ) ^ cutoff)
    simpa only [pow_add, mul_assoc, mul_comm, mul_left_comm] using h
  exact tsum_of_norm_bounded hmajor hterm

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def siegelProductValue {N M : ℕ}
    [NeZero N] [NeZero M] [NeZero (N.lcm M)]
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M) (s : ℂ) : ℂ :=
  riemannZeta s * siegelLProduct chi psi s

theorem siegelProductValue_eq_regular_add_pole {N M : ℕ}
    [NeZero N] [NeZero M] [NeZero (N.lcm M)]
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M)
    {s : ℂ} (hs : s ≠ 1) :
    siegelProductValue chi psi s =
      siegelPoleSubtracted chi psi s + siegelProductResidue chi psi / (s - 1) := by
  rw [siegelPoleSubtracted_apply_of_ne chi psi hs]
  unfold siegelProductValue
  ring

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem siegelProductValue_decomposition {N M : ℕ}
    [NeZero N] [NeZero M] [NeZero (N.lcm M)]
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M)
    (hchi : chi ≠ 1) (hpsi : psi ≠ 1)
    (hmul : DirichletCharacter.mul chi psi ≠ 1)
    (cutoff : ℕ) {delta : ℝ} (hdelta : 0 < delta) :
    siegelProductValue chi psi (1 - delta) =
      siegelSourcePartialSum chi psi cutoff (1 + delta) +
        regularCoefficientTail (siegelRegularCoefficient chi psi) cutoff (1 + delta) -
          siegelProductResidue chi psi * ((1 + delta : ℝ) : ℂ) ^ cutoff / delta := by
  let s : ℂ := (1 - delta : ℝ)
  let t : ℝ := 1 + delta
  have hs : s ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    dsimp [s] at hre
    norm_num at hre
    linarith
  have hexpansion := hasSum_siegelRegularCoefficient chi psi hchi hpsi hmul s
  have hsplit : siegelPoleSubtracted chi psi s =
      (∑ m ∈ Finset.range cutoff, siegelRegularCoefficient chi psi m * (t : ℂ) ^ m) +
        regularCoefficientTail (siegelRegularCoefficient chi psi) cutoff t := by
    have hsum := hexpansion.summable.sum_add_tsum_nat_add cutoff
    rw [hexpansion.tsum_eq] at hsum
    have hst : (2 - s : ℂ) = t := by
      dsimp [s, t]
      push_cast
      ring
    rw [hst] at hsum
    simpa only [regularCoefficientTail, Nat.add_comm] using hsum.symm
  have hsdef : (1 : ℂ) - delta = s := by
    dsimp [s]
    push_cast
    rfl
  have htdef : 1 + delta = t := rfl
  rw [hsdef, htdef]
  rw [siegelProductValue_eq_regular_add_pole chi psi hs, hsplit]
  rw [regularPartialSum_eq_source_sub_residue chi psi hchi hpsi hmul]
  have ht : (t : ℂ) ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    dsimp [t] at hre
    norm_num at hre
    linarith
  rw [geom_sum_eq ht]
  dsimp [s, t]
  push_cast
  field_simp
  ring

end BombieriVinogradov.SiegelWalfisz

end

section

open scoped ComplexOrder

namespace BombieriVinogradov.SiegelWalfisz

theorem siegelProductValue_re_lower_bound {N M : ℕ}
    [NeZero N] [NeZero M] [NeZero (N.lcm M)]
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M)
    (hchiSquare : chi ^ 2 = 1) (hpsiSquare : psi ^ 2 = 1)
    (hchi : chi ≠ 1) (hpsi : psi ≠ 1)
    (hmul : DirichletCharacter.mul chi psi ≠ 1)
    {A delta : ℝ} (hA : 0 ≤ A) (hdelta : 0 < delta) (hdeltaUpper : delta ≤ 1 / 8)
    {cutoff : ℕ} (hcutoff : 0 < cutoff)
    (hcoeff : ∀ m, ‖siegelRegularCoefficient chi psi m‖ ≤ A * (2 / 3 : ℝ) ^ m) :
    1 - (siegelProductResidue chi psi).re * (1 + delta) ^ cutoff / delta -
        4 * A * (3 / 4 : ℝ) ^ cutoff ≤
      (siegelProductValue chi psi (1 - delta)).re := by
  let partialSum := siegelSourcePartialSum chi psi cutoff (1 + delta)
  let tail := regularCoefficientTail (siegelRegularCoefficient chi psi) cutoff (1 + delta)
  have hpartialComplex : (1 : ℂ) ≤ partialSum :=
    one_le_siegelSourcePartialSum chi psi hchiSquare hpsiSquare hcutoff (by linarith)
  have hpartial : 1 ≤ partialSum.re := (Complex.le_def.mp hpartialComplex).1
  have htailNorm : ‖tail‖ ≤ 4 * A * (3 / 4 : ℝ) ^ cutoff :=
    norm_regularCoefficientTail_le (siegelRegularCoefficient chi psi) cutoff hA
      (by linarith) (by linarith) hcoeff
  have htailRe : -(4 * A * (3 / 4 : ℝ) ^ cutoff) ≤ tail.re := by
    exact (neg_le_neg htailNorm).trans ((abs_le.mp (Complex.abs_re_le_norm tail)).1)
  have hdecomp := congrArg Complex.re
    (siegelProductValue_decomposition chi psi hchi hpsi hmul cutoff hdelta)
  have hpowcast : (((1 + delta : ℝ) : ℂ) ^ cutoff) =
      (((1 + delta) ^ cutoff : ℝ) : ℂ) := by
    norm_cast
  have hbasecast : (1 : ℂ) + delta = ((1 + delta : ℝ) : ℂ) := by
    push_cast
    rfl
  have hpowRe : ((1 + (delta : ℂ)) ^ cutoff).re = (1 + delta) ^ cutoff := by
    rw [hbasecast, hpowcast]
    rfl
  have hpowIm : ((1 + (delta : ℂ)) ^ cutoff).im = 0 := by
    rw [hbasecast, hpowcast]
    rfl
  have hpoleRe :
      (siegelProductResidue chi psi * (((1 + delta : ℝ) : ℂ) ^ cutoff) / delta).re =
        (siegelProductResidue chi psi).re * (1 + delta) ^ cutoff / delta := by
    simp
    rw [hpowRe, hpowIm]
    ring
  rw [Complex.sub_re, Complex.add_re, hpoleRe] at hdecomp
  change (siegelProductValue chi psi (1 - delta)).re =
      partialSum.re + tail.re -
        (siegelProductResidue chi psi).re * (1 + delta) ^ cutoff / delta at hdecomp
  linarith

end BombieriVinogradov.SiegelWalfisz

end

section

open scoped ComplexOrder

open Filter
open Topology

namespace BombieriVinogradov.SiegelWalfisz

theorem siegelProductResidue_nonneg {N M : ℕ}
    [NeZero N] [NeZero M] [NeZero (N.lcm M)]
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M)
    (hchiSquare : chi ^ 2 = 1) (hpsiSquare : psi ^ 2 = 1)
    (hchi : chi ≠ 1) (hpsi : psi ≠ 1)
    (hmul : DirichletCharacter.mul chi psi ≠ 1) :
    0 ≤ siegelProductResidue chi psi := by
  obtain ⟨C, _hC, K, hbound⟩ := siegelProduct_coefficient_bound
  let A : ℝ := C * ((N : ℝ) * (M : ℝ)) ^ K
  have hregular : Tendsto (fun m => siegelRegularCoefficient chi psi m)
      atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun m => norm_nonneg (siegelRegularCoefficient chi psi m))
      (fun m => hbound chi psi hchi hpsi hmul m) ?_
    have hpow := tendsto_pow_atTop_nhds_zero_of_norm_lt_one
      (show ‖(2 / 3 : ℝ)‖ < 1 by norm_num)
    have hconst : Tendsto (fun _ : ℕ => A) atTop (𝓝 A) := tendsto_const_nhds
    have hmulZero := hconst.mul hpow
    simpa [A] using hmulZero
  have hsource : Tendsto (fun m => siegelSourceCoefficient chi psi m)
      atTop (𝓝 (siegelProductResidue chi psi)) := by
    have hseq : (fun m => siegelSourceCoefficient chi psi m) =
        fun m => siegelRegularCoefficient chi psi m + siegelProductResidue chi psi := by
      funext m
      exact siegelSourceCoefficient_eq_regular_add_residue chi psi hchi hpsi hmul m
    rw [hseq]
    simpa using hregular.add_const (siegelProductResidue chi psi)
  exact ge_of_tendsto hsource <| Eventually.of_forall fun m =>
    siegelSourceCoefficient_nonneg chi psi hchiSquare hpsiSquare m

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def siegelTruncationIndex (B Q : ℝ) (K : ℕ) : ℕ :=
  ⌈4 * Real.log (B * Q ^ K)⌉₊ + 1

theorem truncationIndex_lower {B Q : ℝ} {K : ℕ}
    (hB : 1 ≤ B) (hQ : 1 ≤ Q) :
    4 * Real.log (B * Q ^ K) < siegelTruncationIndex B Q K := by
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hQpow : 1 ≤ Q ^ K := one_le_pow₀ hQ
  have hX : 1 ≤ B * Q ^ K :=
    hB.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hQpow hB0)
  have hlog : 0 ≤ 4 * Real.log (B * Q ^ K) :=
    mul_nonneg (by norm_num) (Real.log_nonneg hX)
  unfold siegelTruncationIndex
  rw [Nat.cast_add, Nat.cast_one]
  have hceil := Nat.le_ceil (4 * Real.log (B * Q ^ K))
  exact hceil.trans_lt (lt_add_one _)

theorem truncationIndex_upper {B Q : ℝ} {K : ℕ}
    (hB : 1 ≤ B) (hQ : 1 ≤ Q) :
    (siegelTruncationIndex B Q K : ℝ) <
      4 * Real.log (B * Q ^ K) + 2 := by
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hQpow : 1 ≤ Q ^ K := one_le_pow₀ hQ
  have hX : 1 ≤ B * Q ^ K :=
    hB.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hQpow hB0)
  have hlog : 0 ≤ 4 * Real.log (B * Q ^ K) :=
    mul_nonneg (by norm_num) (Real.log_nonneg hX)
  unfold siegelTruncationIndex
  rw [Nat.cast_add, Nat.cast_one]
  linarith [Nat.ceil_lt_add_one hlog]

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem truncationPoleGrowth {B Q delta : ℝ} {K : ℕ}
    (hB : 1 ≤ B) (hQ : 1 ≤ Q) (hdelta0 : 0 ≤ delta) (hdelta : delta ≤ 1 / 8) :
    (1 + delta) ^ siegelTruncationIndex B Q K ≤
      Real.exp 2 * B * Q ^ ((4 * K : ℝ) * delta) := by
  let cutoff := siegelTruncationIndex B Q K
  let X := B * Q ^ K
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hQ0 : 0 ≤ Q := zero_le_one.trans hQ
  have hQpos : 0 < Q := zero_lt_one.trans_le hQ
  have hXpos : 0 < X := mul_pos (zero_lt_one.trans_le hB) (pow_pos hQpos K)
  have hcutoff := truncationIndex_upper (K := K) hB hQ
  have hmul : (cutoff : ℝ) * delta ≤
      (4 * Real.log X + 2) * delta :=
    mul_le_mul_of_nonneg_right hcutoff.le hdelta0
  have hexponent : (cutoff : ℝ) * delta ≤ 4 * delta * Real.log X + 2 := by
    calc
      (cutoff : ℝ) * delta ≤ (4 * Real.log X + 2) * delta := hmul
      _ ≤ 4 * delta * Real.log X + 2 := by nlinarith
  have hbase : 1 + delta ≤ Real.exp delta := by
    simpa only [add_comm] using Real.add_one_le_exp delta
  have hbase0 : 0 ≤ 1 + delta := by linarith
  have hpow : (1 + delta) ^ cutoff ≤ (Real.exp delta) ^ cutoff := by
    exact pow_le_pow_left₀ hbase0 hbase cutoff
  calc
    (1 + delta) ^ cutoff ≤ (Real.exp delta) ^ cutoff := hpow
    _ = Real.exp ((cutoff : ℝ) * delta) := by
      rw [← Real.exp_nat_mul]
    _ ≤ Real.exp (4 * delta * Real.log X + 2) := Real.exp_le_exp.mpr hexponent
    _ = Real.exp 2 * X ^ (4 * delta) := by
      rw [Real.exp_add, Real.rpow_def_of_pos hXpos]
      have harg : 4 * delta * Real.log X = Real.log X * (4 * delta) := by ring
      rw [harg]
      ring
    _ ≤ Real.exp 2 * B * Q ^ ((4 * K : ℝ) * delta) := by
      have hBrpow : B ^ (4 * delta) ≤ B := by
        simpa only [Real.rpow_one] using
          Real.rpow_le_rpow_of_exponent_le hB (by nlinarith : 4 * delta ≤ 1)
      have hQrpow : (Q ^ K) ^ (4 * delta) = Q ^ ((4 * K : ℝ) * delta) := by
        calc
          (Q ^ K) ^ (4 * delta) = (Q ^ (4 * delta)) ^ K :=
            (Real.rpow_pow_comm hQ0 (4 * delta) K).symm
          _ = Q ^ ((4 * delta) * K) :=
            (Real.rpow_mul_natCast hQ0 (4 * delta) K).symm
          _ = Q ^ ((4 * K : ℝ) * delta) := by
            congr 1
            ring
      dsimp [X]
      rw [Real.mul_rpow hB0 (pow_nonneg hQ0 K), hQrpow]
      have hQnonneg : 0 ≤ Q ^ ((4 * K : ℝ) * delta) := Real.rpow_nonneg hQ0 _
      calc
        Real.exp 2 * (B ^ (4 * delta) * Q ^ ((4 * K : ℝ) * delta)) ≤
            Real.exp 2 * (B * Q ^ ((4 * K : ℝ) * delta)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hBrpow hQnonneg) (Real.exp_nonneg 2)
        _ = Real.exp 2 * B * Q ^ ((4 * K : ℝ) * delta) := by ring

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem truncationTail_lt_half {A B Q : ℝ} {K : ℕ}
    (hA : 0 ≤ A) (hB : 1 ≤ B) (hAB : 8 * A ≤ B) (hQ : 1 ≤ Q) :
    4 * A * Q ^ K * (3 / 4 : ℝ) ^ siegelTruncationIndex B Q K < 1 / 2 := by
  let cutoff := siegelTruncationIndex B Q K
  let X := B * Q ^ K
  have hBpos : 0 < B := zero_lt_one.trans_le hB
  have hQpos : 0 < Q := zero_lt_one.trans_le hQ
  have hQpowpos : 0 < Q ^ K := pow_pos hQpos K
  have hXpos : 0 < X := mul_pos hBpos hQpowpos
  have hbase : Real.log (3 / 4 : ℝ) ≤ -1 / 4 := by
    have h := Real.log_le_sub_one_of_pos (show 0 < (3 / 4 : ℝ) by norm_num)
    norm_num at h ⊢
    exact h
  have hcutoff : 4 * Real.log X < (cutoff : ℝ) := by
    exact truncationIndex_lower hB hQ
  have hcutoff0 : 0 ≤ (cutoff : ℝ) := by positivity
  have hexponent : Real.log (3 / 4 : ℝ) * (cutoff : ℝ) < -Real.log X := by
    calc
      Real.log (3 / 4 : ℝ) * (cutoff : ℝ) ≤
          (-1 / 4 : ℝ) * (cutoff : ℝ) :=
        mul_le_mul_of_nonneg_right hbase hcutoff0
      _ < -Real.log X := by nlinarith
  have hpow : (3 / 4 : ℝ) ^ cutoff < 1 / X := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num)]
    have h := Real.exp_lt_exp.mpr hexponent
    rw [Real.exp_neg, Real.exp_log hXpos] at h
    simpa only [inv_eq_one_div] using h
  rcases hA.eq_or_lt with rfl | hApos
  · norm_num
  · have hpref : 0 < 4 * A * Q ^ K := mul_pos (mul_pos (by norm_num) hApos) hQpowpos
    calc
      4 * A * Q ^ K * (3 / 4 : ℝ) ^ cutoff <
          4 * A * Q ^ K * (1 / X) := mul_lt_mul_of_pos_left hpow hpref
      _ = 4 * A / B := by
        dsimp [X]
        field_simp
      _ ≤ 1 / 2 := by
        rw [div_le_iff₀ hBpos]
        nlinarith

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem siegelTruncation_spec {A B Q delta : ℝ} {K : ℕ}
    (hA : 0 ≤ A) (hB : 1 ≤ B) (hAB : 8 * A ≤ B) (hQ : 1 ≤ Q)
    (hdelta0 : 0 ≤ delta) (hdelta : delta ≤ 1 / 8) :
    4 * A * Q ^ K * (3 / 4 : ℝ) ^ siegelTruncationIndex B Q K < 1 / 2 ∧
      (1 + delta) ^ siegelTruncationIndex B Q K ≤
        Real.exp 2 * B * Q ^ ((4 * K : ℝ) * delta) :=
  ⟨truncationTail_lt_half hA hB hAB hQ,
    truncationPoleGrowth hB hQ hdelta0 hdelta⟩

end BombieriVinogradov.SiegelWalfisz

end

section

open scoped ComplexOrder

namespace BombieriVinogradov.SiegelWalfisz

theorem siegelProduct_pos_of_coefficient_bound {N M : ℕ}
    [NeZero N] [NeZero M] [NeZero (N.lcm M)]
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M)
    (hchiSquare : chi ^ 2 = 1) (hpsiSquare : psi ^ 2 = 1)
    (hchi : chi ≠ 1) (hpsi : psi ≠ 1)
    (hmul : DirichletCharacter.mul chi psi ≠ 1)
    {C B Q delta : ℝ} {K : ℕ}
    (hC : 0 < C) (hB : 1 ≤ B) (hCB : 8 * C ≤ B) (hQ : 1 ≤ Q)
    (hdelta : 0 < delta) (hdeltaUpper : delta ≤ 1 / 8)
    (hcoeff : ∀ m, ‖siegelRegularCoefficient chi psi m‖ ≤
      C * Q ^ K * (2 / 3 : ℝ) ^ m)
    (hsmall : 2 * (Real.exp 2 * B) * (siegelProductResidue chi psi).re *
      Q ^ ((4 * K : ℝ) * delta) < delta) :
    0 < (siegelProductValue chi psi (1 - delta)).re := by
  let cutoff := siegelTruncationIndex B Q K
  have hcutoff : 0 < cutoff := by
    dsimp [cutoff, siegelTruncationIndex]
    omega
  have hresidue := siegelProductResidue_nonneg chi psi hchiSquare hpsiSquare hchi hpsi hmul
  have hresidueRe : 0 ≤ (siegelProductResidue chi psi).re :=
    (Complex.le_def.mp hresidue).1
  have htruncation := siegelTruncation_spec (K := K)
    hC.le hB hCB hQ hdelta.le hdeltaUpper
  have htail : 4 * (C * Q ^ K) * (3 / 4 : ℝ) ^ cutoff < 1 / 2 := by
    simpa only [mul_assoc] using htruncation.1
  have hpoleGrowth : (1 + delta) ^ cutoff ≤
      Real.exp 2 * B * Q ^ ((4 * K : ℝ) * delta) := htruncation.2
  have hpoleNumerator :
      (siegelProductResidue chi psi).re * (1 + delta) ^ cutoff ≤
        (siegelProductResidue chi psi).re *
          (Real.exp 2 * B * Q ^ ((4 * K : ℝ) * delta)) :=
    mul_le_mul_of_nonneg_left hpoleGrowth hresidueRe
  have hpole :
      (siegelProductResidue chi psi).re * (1 + delta) ^ cutoff / delta < 1 / 2 := by
    calc
      (siegelProductResidue chi psi).re * (1 + delta) ^ cutoff / delta ≤
          (siegelProductResidue chi psi).re *
            (Real.exp 2 * B * Q ^ ((4 * K : ℝ) * delta)) / delta :=
        div_le_div_of_nonneg_right hpoleNumerator hdelta.le
      _ < 1 / 2 := by
        rw [div_lt_iff₀ hdelta]
        ring_nf at hsmall ⊢
        linarith
  have hlower := siegelProductValue_re_lower_bound chi psi hchiSquare hpsiSquare
    hchi hpsi hmul (mul_nonneg hC.le (pow_nonneg (zero_le_one.trans hQ) K))
    hdelta hdeltaUpper hcutoff hcoeff
  linarith

end BombieriVinogradov.SiegelWalfisz

end

section

open scoped ComplexOrder

namespace BombieriVinogradov.SiegelWalfisz

theorem siegelProduct_pos :
    ∃ C : ℝ, 0 < C ∧ ∃ D : ℕ,
      ∀ {N M : ℕ} [NeZero N] [NeZero M] [NeZero (N.lcm M)]
        (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M),
        chi ^ 2 = 1 → psi ^ 2 = 1 → chi ≠ 1 → psi ≠ 1 →
          DirichletCharacter.mul chi psi ≠ 1 →
          ∀ s : ℝ, 7 / 8 ≤ s → s < 1 →
            C * ‖siegelProductResidue chi psi‖ <
              (1 - s) * ((N : ℝ) * (M : ℝ)) ^ (-(D : ℝ) * (1 - s)) →
              0 < (siegelProductValue chi psi s).re := by
  obtain ⟨C0, hC0, K, hcoeff⟩ := siegelProduct_coefficient_bound
  let B : ℝ := max 1 (8 * C0)
  have hB : 1 ≤ B := le_max_left _ _
  have hC0B : 8 * C0 ≤ B := le_max_right _ _
  have hBpos : 0 < B := zero_lt_one.trans_le hB
  refine ⟨2 * (Real.exp 2 * B), mul_pos (by norm_num) (mul_pos (Real.exp_pos 2) hBpos),
    4 * K, ?_⟩
  intro N M instN instM instLcm chi psi hchiSquare hpsiSquare hchi hpsi hmul s hsLower hsUpper hsmall
  let Q : ℝ := (N : ℝ) * (M : ℝ)
  let delta : ℝ := 1 - s
  have hdelta : 0 < delta := sub_pos.mpr hsUpper
  have hdeltaUpper : delta ≤ 1 / 8 := by
    dsimp [delta]
    linarith
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast NeZero.pos N
  have hM : (1 : ℝ) ≤ M := by exact_mod_cast NeZero.pos M
  have hQ : 1 ≤ Q := by
    dsimp [Q]
    nlinarith [mul_le_mul hN hM (by norm_num : (0 : ℝ) ≤ 1) (by linarith : (0 : ℝ) ≤ N)]
  have hQpos : 0 < Q := zero_lt_one.trans_le hQ
  have hQ0 : 0 ≤ Q := hQpos.le
  have hresidue := siegelProductResidue_nonneg chi psi hchiSquare hpsiSquare hchi hpsi hmul
  have hresidueParts := Complex.le_def.mp hresidue
  have hnormResidue : ‖siegelProductResidue chi psi‖ =
      (siegelProductResidue chi psi).re := by
    have habs := Complex.abs_re_eq_norm.mpr hresidueParts.2.symm
    rw [abs_of_nonneg hresidueParts.1] at habs
    exact habs.symm
  have hsourceSmall :
      2 * (Real.exp 2 * B) * (siegelProductResidue chi psi).re *
        Q ^ ((4 * K : ℝ) * delta) < delta := by
    have hsmall' : 2 * (Real.exp 2 * B) * (siegelProductResidue chi psi).re <
        delta * Q ^ (-((4 * K : ℝ) * delta)) := by
      simpa [Q, delta, hnormResidue] using hsmall
    have hpowPos : 0 < Q ^ ((4 * K : ℝ) * delta) := Real.rpow_pos_of_pos hQpos _
    calc
      2 * (Real.exp 2 * B) * (siegelProductResidue chi psi).re *
          Q ^ ((4 * K : ℝ) * delta) <
        (delta * Q ^ (-((4 * K : ℝ) * delta))) *
          Q ^ ((4 * K : ℝ) * delta) :=
        mul_lt_mul_of_pos_right hsmall' hpowPos
      _ = delta := by
        rw [Real.rpow_neg hQ0]
        field_simp
  have hpositive := siegelProduct_pos_of_coefficient_bound chi psi hchiSquare hpsiSquare
    hchi hpsi hmul hC0 hB hC0B hQ hdelta hdeltaUpper
    (fun m => by simpa [Q, mul_assoc] using hcoeff chi psi hchi hpsi hmul m) hsourceSmall
  simpa [delta] using hpositive

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

def IsSiegelPositivityPair (C : ℝ) (D : ℕ) : Prop :=
  0 < C ∧
    ∀ {N M : ℕ} [NeZero N] [NeZero M] [NeZero (N.lcm M)]
      (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M),
      chi ^ 2 = 1 → psi ^ 2 = 1 → chi ≠ 1 → psi ≠ 1 →
        DirichletCharacter.mul chi psi ≠ 1 →
        ∀ s : ℝ, 7 / 8 ≤ s → s < 1 →
          C * ‖siegelProductResidue chi psi‖ <
            (1 - s) * ((N : ℝ) * (M : ℝ)) ^ (-(D : ℝ) * (1 - s)) →
            0 < (siegelProductValue chi psi s).re

theorem exists_siegelPositivityPair :
    ∃ C : ℝ, ∃ D : ℕ, IsSiegelPositivityPair C D := by
  obtain ⟨C, hC, D, hpos⟩ := siegelProduct_pos
  exact ⟨C, D, hC, hpos⟩

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem siegelProductResidue_lower_of_nonpos {C : ℝ} {D : ℕ}
    (hpair : IsSiegelPositivityPair C D)
    {N M : ℕ} [NeZero N] [NeZero M] [NeZero (N.lcm M)]
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M)
    (hchiSquare : chi ^ 2 = 1) (hpsiSquare : psi ^ 2 = 1)
    (hchi : chi ≠ 1) (hpsi : psi ≠ 1)
    (hmul : DirichletCharacter.mul chi psi ≠ 1)
    {s : ℝ} (hsLower : 7 / 8 ≤ s) (hsUpper : s < 1)
    (hnonpos : (siegelProductValue chi psi s).re ≤ 0) :
    (1 - s) * ((N : ℝ) * (M : ℝ)) ^ (-(D : ℝ) * (1 - s)) ≤
      C * ‖siegelProductResidue chi psi‖ := by
  apply le_of_not_gt
  intro hsmall
  have hpositive := hpair.2 chi psi hchiSquare hpsiSquare hchi hpsi hmul
    s hsLower hsUpper hsmall
  linarith

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem norm_siegelProductResidue_le_log {N M : ℕ}
    [NeZero N] [NeZero M] [NeZero (N.lcm M)]
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M)
    (hchi : chi ≠ 1) (hmul : DirichletCharacter.mul chi psi ≠ 1) :
    ‖siegelProductResidue chi psi‖ ≤
      characterLLogBoundConstant ^ 2 * (1 + Real.log N) *
        (1 + Real.log (N.lcm M)) * ‖psi.LFunction 1‖ := by
  have hchiBound := norm_LFunction_one_le_log chi hchi
  have hmulBound := norm_LFunction_one_le_log (DirichletCharacter.mul chi psi) hmul
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast NeZero.pos N
  have hlogN : 0 ≤ 1 + Real.log N := by linarith [Real.log_nonneg hN]
  have hfirstUpper : 0 ≤
      (characterLLogBoundConstant * (1 + Real.log N)) * ‖psi.LFunction 1‖ :=
    mul_nonneg (mul_nonneg characterLLogBoundConstant_pos.le hlogN) (norm_nonneg _)
  rw [siegelProductResidue, norm_mul, norm_mul]
  calc
    ‖chi.LFunction 1‖ * ‖psi.LFunction 1‖ *
        ‖(DirichletCharacter.mul chi psi).LFunction 1‖ ≤
      (characterLLogBoundConstant * (1 + Real.log N)) *
        ‖psi.LFunction 1‖ *
          (characterLLogBoundConstant * (1 + Real.log (N.lcm M))) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_right hchiBound (norm_nonneg _)) hmulBound
        (norm_nonneg _) hfirstUpper
    _ = characterLLogBoundConstant ^ 2 * (1 + Real.log N) *
        (1 + Real.log (N.lcm M)) * ‖psi.LFunction 1‖ := by ring

theorem targetLValue_transfer {C : ℝ} {D : ℕ}
    (hpair : IsSiegelPositivityPair C D)
    {N M : ℕ} [NeZero N] [NeZero M] [NeZero (N.lcm M)]
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M)
    (hchiSquare : chi ^ 2 = 1) (hpsiSquare : psi ^ 2 = 1)
    (hchi : chi ≠ 1) (hpsi : psi ≠ 1)
    (hmul : DirichletCharacter.mul chi psi ≠ 1)
    {s : ℝ} (hsLower : 7 / 8 ≤ s) (hsUpper : s < 1)
    (hnonpos : (siegelProductValue chi psi s).re ≤ 0) :
    (1 - s) * ((N : ℝ) * (M : ℝ)) ^ (-(D : ℝ) * (1 - s)) ≤
      C * (characterLLogBoundConstant ^ 2 * (1 + Real.log N) *
        (1 + Real.log (N.lcm M)) * ‖psi.LFunction 1‖) := by
  exact (siegelProductResidue_lower_of_nonpos hpair chi psi hchiSquare hpsiSquare
    hchi hpsi hmul hsLower hsUpper hnonpos).trans
      (mul_le_mul_of_nonneg_left (norm_siegelProductResidue_le_log chi psi hchi hmul)
        hpair.1.le)

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def siegelLargeLevelDenominator
    (C : ℝ) (N : ℕ) (delta : ℝ) : ℝ :=
  C * characterLLogBoundConstant ^ 2 * (1 + Real.log N) * (1 + delta⁻¹)

theorem siegelLargeLevelDenominator_pos {C delta : ℝ} {N : ℕ}
    (hC : 0 < C) (hN : 0 < N) (hdelta : 0 < delta) :
    0 < siegelLargeLevelDenominator C N delta := by
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog : 0 < 1 + Real.log N := by
    linarith [Real.log_nonneg hNreal]
  have hinverse : 0 < 1 + delta⁻¹ := by
    have : 0 < delta⁻¹ := inv_pos.mpr hdelta
    linarith
  unfold siegelLargeLevelDenominator
  exact mul_pos (mul_pos (mul_pos hC (pow_pos characterLLogBoundConstant_pos 2)) hlog)
    hinverse

noncomputable def siegelLargeLevelConstant
    (C epsilon s : ℝ) (N : ℕ) : ℝ :=
  ((1 - s) / siegelLargeLevelDenominator C N (epsilon / 2)) *
    (N : ℝ) ^ (-epsilon)

theorem siegelLargeLevelConstant_pos {C epsilon s : ℝ} {N : ℕ}
    (hC : 0 < C) (hepsilon : 0 < epsilon) (hN : 0 < N) (hs : s < 1) :
    0 < siegelLargeLevelConstant C epsilon s N := by
  have hdenominator := siegelLargeLevelDenominator_pos hC hN
    (div_pos hepsilon zero_lt_two)
  unfold siegelLargeLevelConstant
  exact mul_pos (div_pos (sub_pos.mpr hs) hdenominator)
    (Real.rpow_pos_of_pos (by exact_mod_cast hN) (-epsilon))

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem one_add_log_le_rpow_mul {x delta : ℝ}
    (hx : 1 ≤ x) (hdelta : 0 < delta) :
    1 + Real.log x ≤ (1 + delta⁻¹) * x ^ delta := by
  have hpow : 1 ≤ x ^ delta := by
    simpa using Real.rpow_le_rpow zero_le_one hx hdelta.le
  have hlog := Real.log_le_rpow_div (zero_le_one.trans hx) hdelta
  calc
    1 + Real.log x ≤ x ^ delta + x ^ delta / delta := add_le_add hpow hlog
    _ = (1 + delta⁻¹) * x ^ delta := by
      rw [div_eq_mul_inv]
      ring

theorem one_add_log_lcm_le_rpow_mul {N M : ℕ}
    (hN : 0 < N) (hM : 0 < M) {delta : ℝ} (hdelta : 0 < delta) :
    1 + Real.log (N.lcm M) ≤
      (1 + delta⁻¹) * ((N : ℝ) * (M : ℝ)) ^ delta := by
  have hmul : 0 < N * M := Nat.mul_pos hN hM
  have hlcmNat : N.lcm M ≤ N * M :=
    Nat.le_of_dvd hmul (Nat.lcm_dvd_mul N M)
  have hlcm : (0 : ℝ) < N.lcm M := by
    exact_mod_cast Nat.pos_of_ne_zero (Nat.lcm_ne_zero hN.ne' hM.ne')
  have hlcmMul : (N.lcm M : ℝ) ≤ (N * M : ℕ) := by
    exact_mod_cast hlcmNat
  have hproduct : (1 : ℝ) ≤ (N * M : ℕ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hmul.ne'
  calc
    1 + Real.log (N.lcm M) ≤ 1 + Real.log (N * M : ℕ) := by
      simpa [add_comm] using add_le_add_left (Real.log_le_log hlcm hlcmMul) 1
    _ ≤ (1 + delta⁻¹) * (N * M : ℕ) ^ delta :=
      one_add_log_le_rpow_mul hproduct hdelta
    _ = (1 + delta⁻¹) * ((N : ℝ) * (M : ℝ)) ^ delta := by
      norm_num

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem weighted_rpow_transfer {prefactor bound base exponent delta epsilon value : ℝ}
    (hprefactor : 0 < prefactor) (hbound : 0 < bound) (hbase : 1 ≤ base)
    (hsum : exponent + delta ≤ epsilon)
    (hweighted : prefactor * base ^ (-exponent) ≤
      bound * base ^ delta * value) :
    (prefactor / bound) * base ^ (-epsilon) ≤ value := by
  have hbasePos : 0 < base := zero_lt_one.trans_le hbase
  have hpowerDelta : 0 < base ^ delta := Real.rpow_pos_of_pos hbasePos delta
  have hdenominator : 0 < bound * base ^ delta := mul_pos hbound hpowerDelta
  have hdivided :
      (prefactor * base ^ (-exponent)) / (bound * base ^ delta) ≤ value := by
    rw [div_le_iff₀ hdenominator]
    simpa [mul_assoc, mul_comm, mul_left_comm] using hweighted
  have hquotient :
      (prefactor * base ^ (-exponent)) / (bound * base ^ delta) =
        (prefactor / bound) * base ^ (-(exponent + delta)) := by
    rw [show -(exponent + delta) = -exponent + -delta by ring,
      Real.rpow_add hbasePos, Real.rpow_neg hbasePos.le]
    field_simp
    rw [← Real.rpow_add hbasePos]
    norm_num
  have hpower : base ^ (-epsilon) ≤ base ^ (-(exponent + delta)) :=
    Real.rpow_le_rpow_of_exponent_le hbase (by linarith)
  calc
    (prefactor / bound) * base ^ (-epsilon) ≤
        (prefactor / bound) * base ^ (-(exponent + delta)) :=
      mul_le_mul_of_nonneg_left hpower (div_nonneg hprefactor.le hbound.le)
    _ = (prefactor * base ^ (-exponent)) / (bound * base ^ delta) :=
      hquotient.symm
    _ ≤ value := hdivided

end BombieriVinogradov.SiegelWalfisz

end

section

open Filter Metric Set

namespace BombieriVinogradov.SiegelWalfisz

theorem riemannZeta_im_real (s : ℝ) : (riemannZeta s).im = 0 := by
  have hsym := riemannZeta_conj (s : ℂ)
  have him := congrArg Complex.im hsym
  simp at him
  linarith

theorem exists_riemannZeta_neg_left :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ s : ℝ, 1 - eta < s → s < 1 → (riemannZeta s).re < 0 := by
  have hofReal : Tendsto (fun s : ℝ ↦ (s : ℂ))
      (nhdsWithin 1 (Iio 1)) (nhdsWithin 1 ({1}ᶜ : Set ℂ)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · exact Complex.continuous_ofReal.continuousAt.tendsto.mono_left inf_le_left
    · filter_upwards [self_mem_nhdsWithin] with s hs
      have hsne : s ≠ 1 := ne_of_lt (Set.mem_Iio.mp hs)
      change (s : ℂ) ≠ 1
      exact_mod_cast hsne
  have hresidue : Tendsto
      (fun s : ℝ ↦ (((s : ℂ) - 1) * riemannZeta s).re)
      (nhdsWithin 1 (Iio 1)) (nhds 1) := by
    convert Complex.continuous_re.continuousAt.tendsto.comp
      (riemannZeta_residue_one.comp hofReal) using 1 <;>
        simp [Function.comp_def]
  have heventually : ∀ᶠ s : ℝ in nhdsWithin 1 (Iio 1),
      0 < (((s : ℂ) - 1) * riemannZeta s).re :=
    hresidue (Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  obtain ⟨eta, heta, hball⟩ := Metric.mem_nhdsWithin_iff.mp heventually
  refine ⟨eta, heta, ?_⟩
  intro s hsLower hsUpper
  have hdist : dist s 1 < eta := by
    rw [Real.dist_eq]
    rw [abs_of_nonpos (sub_nonpos.mpr hsUpper.le)]
    linarith
  have hproduct : 0 < (((s : ℂ) - 1) * riemannZeta s).re :=
    hball ⟨hdist, hsUpper⟩
  have him := riemannZeta_im_real s
  simp only [Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.one_re,
    Complex.sub_im, Complex.ofReal_im, Complex.one_im, zero_mul,
    sub_zero] at hproduct
  nlinarith

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem exists_siegelComparisonPoint {lower : ℝ}
    (hlower : 7 / 8 ≤ lower) (hupper : lower < 1) :
    ∃ s : ℝ, lower ≤ s ∧ 7 / 8 ≤ s ∧ s < 1 ∧ (riemannZeta s).re < 0 := by
  obtain ⟨eta, heta, hzeta⟩ := exists_riemannZeta_neg_left
  let s := max lower (1 - eta / 2)
  have hlowerS : lower ≤ s := le_max_left _ _
  have hsevenS : 7 / 8 ≤ s := hlower.trans hlowerS
  have hsUpper : s < 1 := by
    apply max_lt hupper
    linarith
  have hetaS : 1 - eta < s := by
    have : 1 - eta < 1 - eta / 2 := by linarith
    exact this.trans_le (le_max_right _ _)
  exact ⟨s, hlowerS, hsevenS, hsUpper, hzeta s hetaS hsUpper⟩

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem real_mem_siegelAnalyticDomain {s : ℝ} (hsLower : 7 / 8 ≤ s)
    (hsUpper : s ≤ 1) : (s : ℂ) ∈ siegelAnalyticDomain := by
  rw [siegelAnalyticDomain, Metric.mem_ball, Complex.dist_eq]
  have hnonpos : s - 2 ≤ 0 := by linarith
  rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonpos hnonpos]
  norm_num at hsLower ⊢
  linarith

private theorem characterLBlock_im_eq_zero_bv675 {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchiSquare : chi ^ 2 = 1)
    (k : ℕ) (s : ℝ) : (characterLBlock chi k s).im = 0 := by
  rw [characterLBlock, Complex.im_sum]
  apply Finset.sum_eq_zero
  intro j hj
  rcases MulChar.isQuadratic_iff_sq_eq_one.mpr hchiSquare j with hzero | hone | hneg
  · simp [hzero]
  · rw [hone, show (-(s : ℂ)) = ((-s : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_natCast (k * N + j.val),
      ← Complex.ofReal_cpow (Nat.cast_nonneg (k * N + j.val)) (-s)]
    simp
  · rw [hneg, show (-(s : ℂ)) = ((-s : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_natCast (k * N + j.val),
      ← Complex.ofReal_cpow (Nat.cast_nonneg (k * N + j.val)) (-s)]
    simp

theorem quadraticLFunction_im_eq_zero {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchiSquare : chi ^ 2 = 1) (hchi : chi ≠ 1)
    {s : ℝ} (hs : (s : ℂ) ∈ siegelAnalyticDomain) :
    (chi.LFunction s).im = 0 := by
  have hsum : Summable (fun k : ℕ ↦ characterLBlock chi k s) := by
    apply Summable.of_norm
    exact (characterLBlockMajorant_summable N).of_nonneg_of_le
      (fun k ↦ norm_nonneg _) fun k ↦ norm_characterLBlock_le chi hchi k hs
  rw [LFunction_eq_characterLBlockSeries chi hchi hs, characterLBlockSeries,
    Complex.im_tsum hsum]
  convert tsum_zero with k
  exact characterLBlock_im_eq_zero_bv675 chi hchiSquare k s

end BombieriVinogradov.SiegelWalfisz

end

section

open Set

namespace BombieriVinogradov.SiegelWalfisz

theorem quadraticLFunction_re_pos_of_no_zero {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchiSquare : chi ^ 2 = 1) (hchi : chi ≠ 1)
    {s : ℝ} (hsLower : 7 / 8 ≤ s) (hsUpper : s < 1)
    (hnozero : ∀ t : ℝ, s ≤ t → t ≤ 1 → chi.LFunction t ≠ 0) :
    0 < (chi.LFunction s).re := by
  let f : ℝ → ℝ := fun t ↦ (chi.LFunction t).re
  have hfcont : Continuous f := by
    exact Complex.continuous_re.comp
      ((chi.differentiable_LFunction hchi).continuous.comp Complex.continuous_ofReal)
  have hone : 0 < f 1 := quadraticLFunction_one_re_pos chi hchiSquare hchi
  by_contra hnot
  have himS := quadraticLFunction_im_eq_zero chi hchiSquare hchi
    (real_mem_siegelAnalyticDomain hsLower hsUpper.le)
  have hfs_ne : f s ≠ 0 := by
    intro hfs
    apply hnozero s le_rfl hsUpper.le
    apply Complex.ext
    · simpa [f] using hfs
    · simpa using himS
  have hfsNeg : f s < 0 := lt_of_le_of_ne (le_of_not_gt hnot) hfs_ne
  have hzeroMem : 0 ∈ Icc (f s) (f 1) := ⟨hfsNeg.le, hone.le⟩
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc hsUpper.le hfcont.continuousOn hzeroMem
  have himT := quadraticLFunction_im_eq_zero chi hchiSquare hchi
    (real_mem_siegelAnalyticDomain (hsLower.trans ht.1) ht.2)
  apply hnozero t ht.1 ht.2
  apply Complex.ext
  · simpa [f] using hft
  · simpa using himT

end BombieriVinogradov.SiegelWalfisz

end

section

open scoped ComplexOrder

namespace BombieriVinogradov.SiegelWalfisz

theorem quadraticLFunction_re_pos_of_primitive_no_zero {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) [NeZero chi.conductor]
    (hchiSquare : chi ^ 2 = 1) (hchi : chi ≠ 1)
    {s : ℝ} (hsLower : 7 / 8 ≤ s) (hsUpper : s < 1)
    (hnozero : ∀ t : ℝ, s ≤ t → t ≤ 1 →
      chi.primitiveCharacter.LFunction t ≠ 0) :
    0 < (chi.LFunction s).re := by
  have hprimitiveNe := primitiveCharacter_ne_one chi hchi
  have hprimitiveSquare := primitiveCharacter_sq_eq_one chi hchiSquare
  have hprimitivePos := quadraticLFunction_re_pos_of_no_zero chi.primitiveCharacter
    hprimitiveSquare hprimitiveNe hsLower hsUpper hnozero
  have hcorrection := characterLevelCorrection_pos chi hchiSquare
    (show 0 < s by linarith)
  have hcorrectionParts := Complex.lt_def.mp hcorrection
  have hprimitiveIm := quadraticLFunction_im_eq_zero chi.primitiveCharacter
    hprimitiveSquare hprimitiveNe
    (real_mem_siegelAnalyticDomain hsLower hsUpper.le)
  rw [LFunction_eq_primitive_mul_correction chi hchi, Complex.mul_re]
  rw [hprimitiveIm]
  norm_num
  exact mul_pos hprimitivePos (by simpa using hcorrectionParts.1)

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem siegelProductValue_re_eq_product {N M : ℕ}
    [NeZero N] [NeZero M] [NeZero (N.lcm M)]
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M)
    (hchiSquare : chi ^ 2 = 1) (hpsiSquare : psi ^ 2 = 1)
    (hchi : Ne chi 1) (hpsi : Ne psi 1)
    (hmul : Ne (DirichletCharacter.mul chi psi) 1)
    {s : ℝ} (hsLower : 7 / 8 ≤ s) (hsUpper : s < 1) :
    (siegelProductValue chi psi s).re =
      (riemannZeta s).re * (chi.LFunction s).re * (psi.LFunction s).re *
        ((DirichletCharacter.mul chi psi).LFunction s).re := by
  have hmulSquare := crossLevelMul_sq_eq_one chi psi hchiSquare hpsiSquare
  have hzetaIm := riemannZeta_im_real s
  have hchiIm := quadraticLFunction_im_eq_zero chi hchiSquare hchi
    (real_mem_siegelAnalyticDomain hsLower hsUpper.le)
  have hpsiIm := quadraticLFunction_im_eq_zero psi hpsiSquare hpsi
    (real_mem_siegelAnalyticDomain hsLower hsUpper.le)
  have hmulIm := quadraticLFunction_im_eq_zero (DirichletCharacter.mul chi psi)
    hmulSquare hmul (real_mem_siegelAnalyticDomain hsLower hsUpper.le)
  simp only [siegelProductValue, siegelLProduct, Complex.mul_re, Complex.mul_im,
    hzetaIm, hchiIm, hpsiIm, hmulIm, mul_zero, zero_mul, add_zero, sub_zero]
  ring

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

def PrimitiveQuadraticZeroFreeFrom (s : ℝ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (chi : DirichletCharacter ℂ N),
    DirichletCharacter.IsPrimitive chi -> chi ^ 2 = 1 -> Ne chi 1 ->
      ∀ t : ℝ, s ≤ t -> t ≤ 1 -> Ne (chi.LFunction t) 0

theorem PrimitiveQuadraticZeroFreeFrom.mono {lower s : ℝ}
    (hzeroFree : PrimitiveQuadraticZeroFreeFrom lower) (h : lower ≤ s) :
    PrimitiveQuadraticZeroFreeFrom s := by
  intro N _ chi hprimitive hsquare hne t hst ht
  exact hzeroFree N chi hprimitive hsquare hne t (h.trans hst) ht

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem siegelProductValue_nonpos_of_left_zero {N M : ℕ}
    [NeZero N] [NeZero M] [NeZero (N.lcm M)]
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M)
    {s : ℝ} (hzero : chi.LFunction s = 0) :
    (siegelProductValue chi psi s).re ≤ 0 := by
  simp [siegelProductValue, siegelLProduct, hzero]

theorem quadraticCharacterFour_product_nonpos_of_zeroFree {M : ℕ}
    [NeZero M] [NeZero ((4 : ℕ).lcm M)]
    (psi : DirichletCharacter ℂ M)
    (hpsiPrimitive : DirichletCharacter.IsPrimitive psi)
    (hpsiSquare : psi ^ 2 = 1) (hpsi : Ne psi 1)
    (hM : 4 < M) {s : ℝ} (hsLower : 7 / 8 ≤ s) (hsUpper : s < 1)
    (hzeta : (riemannZeta s).re < 0)
    (hzeroFree : PrimitiveQuadraticZeroFreeFrom s) :
    (siegelProductValue quadraticCharacterFour psi s).re ≤ 0 := by
  have hlevels : Ne 4 M := Ne.symm (Nat.ne_of_gt hM)
  have hmul := crossLevelMul_ne_one_of_primitive_of_ne quadraticCharacterFour psi
    quadraticCharacterFour_isPrimitive hpsiPrimitive hlevels
  have hmulSquare := crossLevelMul_sq_eq_one quadraticCharacterFour psi
    quadraticCharacterFour_sq hpsiSquare
  have hfourNoZero := hzeroFree 4 quadraticCharacterFour
    quadraticCharacterFour_isPrimitive quadraticCharacterFour_sq
      quadraticCharacterFour_ne_one
  have hfourPos := quadraticLFunction_re_pos_of_no_zero quadraticCharacterFour
    quadraticCharacterFour_sq quadraticCharacterFour_ne_one hsLower hsUpper hfourNoZero
  have hpsiNoZero := hzeroFree M psi hpsiPrimitive hpsiSquare hpsi
  have hpsiPos := quadraticLFunction_re_pos_of_no_zero psi hpsiSquare hpsi
    hsLower hsUpper hpsiNoZero
  let _ : NeZero (DirichletCharacter.mul quadraticCharacterFour psi).conductor :=
    ⟨(DirichletCharacter.mul quadraticCharacterFour psi).conductor_ne_zero⟩
  have hmulPrimitiveSquare := primitiveCharacter_sq_eq_one
    (DirichletCharacter.mul quadraticCharacterFour psi) hmulSquare
  have hmulPrimitiveNe := primitiveCharacter_ne_one
    (DirichletCharacter.mul quadraticCharacterFour psi) hmul
  have hmulPrimitiveNoZero := hzeroFree
    (DirichletCharacter.mul quadraticCharacterFour psi).conductor
    (DirichletCharacter.mul quadraticCharacterFour psi).primitiveCharacter
    (DirichletCharacter.mul quadraticCharacterFour psi).primitiveCharacter_isPrimitive
    hmulPrimitiveSquare hmulPrimitiveNe
  have hmulPos := quadraticLFunction_re_pos_of_primitive_no_zero
    (DirichletCharacter.mul quadraticCharacterFour psi) hmulSquare hmul
      hsLower hsUpper hmulPrimitiveNoZero
  rw [siegelProductValue_re_eq_product quadraticCharacterFour psi
    quadraticCharacterFour_sq hpsiSquare quadraticCharacterFour_ne_one hpsi hmul
      hsLower hsUpper]
  exact (mul_neg_of_neg_of_pos
    (mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hzeta hfourPos) hpsiPos)
      hmulPos).le

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

def IsSiegelSeed (lower : ℝ) (N : ℕ) (chi : DirichletCharacter ℂ N)
    (s : ℝ) : Prop :=
  0 < N ∧ DirichletCharacter.IsPrimitive chi ∧ chi ^ 2 = 1 ∧ Ne chi 1 ∧
    lower ≤ s ∧ 7 / 8 ≤ s ∧ s < 1 ∧
      ∀ (M : ℕ) [NeZero N] [NeZero M] [NeZero (N.lcm M)]
        (psi : DirichletCharacter ℂ M), N < M ->
          DirichletCharacter.IsPrimitive psi -> psi ^ 2 = 1 -> Ne psi 1 ->
            (siegelProductValue chi psi s).re ≤ 0

theorem exists_siegelSeed {lower : ℝ}
    (hlower : 7 / 8 ≤ lower) (hupper : lower < 1) :
    ∃ (N : ℕ) (chi : DirichletCharacter ℂ N) (s : ℝ),
      IsSiegelSeed lower N chi s := by
  by_cases hzeroFree : PrimitiveQuadraticZeroFreeFrom lower
  · obtain ⟨s, hlowerS, hsevenS, hsUpper, hzeta⟩ :=
      exists_siegelComparisonPoint hlower hupper
    have hzeroFreeS := hzeroFree.mono hlowerS
    refine ⟨4, quadraticCharacterFour, s, ?_⟩
    refine ⟨by norm_num, quadraticCharacterFour_isPrimitive,
      quadraticCharacterFour_sq, quadraticCharacterFour_ne_one,
      hlowerS, hsevenS, hsUpper, ?_⟩
    intro M _ _ _ psi hM hpsiPrimitive hpsiSquare hpsi
    exact quadraticCharacterFour_product_nonpos_of_zeroFree psi hpsiPrimitive
      hpsiSquare hpsi hM hsevenS hsUpper hzeta hzeroFreeS
  · rw [PrimitiveQuadraticZeroFreeFrom] at hzeroFree
    push Not at hzeroFree
    obtain ⟨N, hN, chi, hprimitive, hchiSquare, hchi, s,
      hlowerS, hsOne, hzero⟩ := hzeroFree
    let _ : NeZero N := hN
    have hsUpper : s < 1 := by
      apply lt_of_le_of_ne hsOne
      intro hs
      apply chi.LFunction_apply_one_ne_zero hchi
      simpa [hs] using hzero
    refine ⟨N, chi, s, ?_⟩
    refine ⟨NeZero.pos N, hprimitive, hchiSquare, hchi,
      hlowerS, hlower.trans hlowerS, hsUpper, ?_⟩
    intro M _ _ _ psi _ _ _ _
    exact siegelProductValue_nonpos_of_left_zero chi psi hzero

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem siegelLowerBound_largeLevel {C epsilon : ℝ} {D N : ℕ}
    {chi : DirichletCharacter ℂ N} {s : ℝ}
    (hpair : IsSiegelPositivityPair C D) (hepsilon : 0 < epsilon)
    (hseed : IsSiegelSeed (siegelLowerEndpoint epsilon D) N chi s) :
    ∀ (M : ℕ) [NeZero M] [NeZero (N.lcm M)]
      (psi : DirichletCharacter ℂ M), N < M ->
        DirichletCharacter.IsPrimitive psi -> psi ^ 2 = 1 -> Ne psi 1 ->
          siegelLargeLevelConstant C epsilon s N * (M : ℝ) ^ (-epsilon) ≤
            (psi.LFunction 1).re := by
  obtain ⟨hN, hchiPrimitive, hchiSquare, hchi, hlowerS,
    hsevenS, hsUpper, hseedNonpos⟩ := hseed
  let _ : NeZero N := ⟨hN.ne'⟩
  intro M _ _ psi hNM hpsiPrimitive hpsiSquare hpsi
  have hM : 0 < M := NeZero.pos M
  have hmul := crossLevelMul_ne_one_of_primitive_of_ne chi psi
    hchiPrimitive hpsiPrimitive (Ne.symm (Nat.ne_of_gt hNM))
  have hnonpos := hseedNonpos M psi hNM hpsiPrimitive hpsiSquare hpsi
  have hraw := targetLValue_transfer hpair chi psi hchiSquare hpsiSquare
    hchi hpsi hmul hsevenS hsUpper hnonpos
  have hnorm := norm_quadraticLFunction_one_eq_re psi hpsiSquare hpsi
  rw [hnorm] at hraw
  have hvaluePos := quadraticLFunction_one_re_pos psi hpsiSquare hpsi
  let delta : ℝ := epsilon / 2
  let base : ℝ := (N : ℝ) * (M : ℝ)
  let fixed : ℝ := C * characterLLogBoundConstant ^ 2 * (1 + Real.log N)
  have hdelta : 0 < delta := by
    dsimp [delta]
    positivity
  have hbase : 1 ≤ base := by
    dsimp [base]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hN.ne' hM.ne')
  have hfixed : 0 < fixed := by
    have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hlog : 0 < 1 + Real.log N := by
      linarith [Real.log_nonneg hNreal]
    dsimp [fixed]
    exact mul_pos (mul_pos hpair.1 (pow_pos characterLLogBoundConstant_pos 2)) hlog
  have hlogBound : 1 + Real.log (N.lcm M) ≤
      (1 + delta⁻¹) * base ^ delta := by
    simpa [delta, base] using one_add_log_lcm_le_rpow_mul hN hM hdelta
  have hscaled : fixed * (1 + Real.log (N.lcm M)) * (psi.LFunction 1).re ≤
      fixed * ((1 + delta⁻¹) * base ^ delta) * (psi.LFunction 1).re :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hlogBound hfixed.le) hvaluePos.le
  have hweighted :
      (1 - s) * base ^ (-((D : ℝ) * (1 - s))) ≤
        siegelLargeLevelDenominator C N delta * base ^ delta *
          (psi.LFunction 1).re := by
    calc
      (1 - s) * base ^ (-((D : ℝ) * (1 - s))) ≤
          fixed * (1 + Real.log (N.lcm M)) * (psi.LFunction 1).re := by
        simpa [base, fixed, mul_assoc] using hraw
      _ ≤ fixed * ((1 + delta⁻¹) * base ^ delta) *
          (psi.LFunction 1).re := hscaled
      _ = siegelLargeLevelDenominator C N delta * base ^ delta *
          (psi.LFunction 1).re := by
        dsimp [fixed]
        unfold siegelLargeLevelDenominator
        ring
  have hdirect := weighted_rpow_transfer (sub_pos.mpr hsUpper)
    (siegelLargeLevelDenominator_pos hpair.1 hN hdelta) hbase
      (siegel_exponent_control hepsilon D hlowerS) hweighted
  have hbasePower : base ^ (-epsilon) =
      (N : ℝ) ^ (-epsilon) * (M : ℝ) ^ (-epsilon) := by
    dsimp [base]
    exact Real.mul_rpow (by positivity) (by positivity)
  rw [hbasePower] at hdirect
  simpa [siegelLargeLevelConstant, delta, mul_assoc] using hdirect

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem siegelLowerBound :
    ∀ epsilon > (0 : ℝ), ∃ c > (0 : ℝ),
      ∀ (M : ℕ) [NeZero M] (psi : DirichletCharacter ℂ M), 3 ≤ M ->
        DirichletCharacter.IsPrimitive psi -> psi ^ 2 = 1 -> Ne psi 1 ->
          c * (M : ℝ) ^ (-epsilon) ≤ (psi.LFunction 1).re := by
  intro epsilon hepsilon
  obtain ⟨C, D, hpair⟩ := exists_siegelPositivityPair
  obtain ⟨N, chi, s, hseed⟩ := exists_siegelSeed
    (seven_eighths_le_siegelLowerEndpoint epsilon D)
    (siegelLowerEndpoint_lt_one hepsilon D)
  have hN : 0 < N := hseed.1
  have hsUpper : s < 1 := hseed.2.2.2.2.2.2.1
  let _ : NeZero N := ⟨hN.ne'⟩
  let c := min (finiteLevelConstant epsilon N)
    (siegelLargeLevelConstant C epsilon s N)
  have hcPositive : 0 < c := by
    apply lt_min
    · exact finiteLevelConstant_pos epsilon N
    · exact siegelLargeLevelConstant_pos hpair.1 hepsilon hN hsUpper
  refine ⟨c, hcPositive, ?_⟩
  intro M _ psi hM hpsiPrimitive hpsiSquare hpsi
  have hpowerNonneg : 0 ≤ (M : ℝ) ^ (-epsilon) :=
    Real.rpow_nonneg (Nat.cast_nonneg M) (-epsilon)
  by_cases hMN : M ≤ N
  · have hcoefficient : c ≤ finiteLevelConstant epsilon N := min_le_left _ _
    exact (mul_le_mul_of_nonneg_right hcoefficient hpowerNonneg).trans
      (finiteLevelConstant_le_value hMN hM psi hpsiSquare hpsi)
  · have hNM : N < M := Nat.lt_of_not_ge hMN
    let _ : NeZero (N.lcm M) :=
      ⟨Nat.lcm_ne_zero hN.ne' (NeZero.ne M)⟩
    have hcoefficient : c ≤ siegelLargeLevelConstant C epsilon s N :=
      min_le_right _ _
    exact (mul_le_mul_of_nonneg_right hcoefficient hpowerNonneg).trans
      (siegelLowerBound_largeLevel hpair hepsilon hseed M psi hNM
        hpsiPrimitive hpsiSquare hpsi)

end BombieriVinogradov.SiegelWalfisz

end

namespace BVShort
open Complex DirichletCharacter

theorem local_lower {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x M t : ℝ} (hx : 0 < x) (hM : 0 < M) (hs : 16*M^8*x < 1)
    (hp : ‖LFunctionTrivChar q (1+x)‖ ≤ M/x)
    (hd : ‖(χ^2).LFunction (1+x+2*I*t)‖ ≤ M) :
    2*M*x < ‖χ.LFunction (1+x+I*t)‖ := by
  by_contra! h
  have H := χ.norm_LFunction_product_ge_one hx t
  simp only [norm_mul,norm_pow] at H
  have H' : (1:ℝ) ≤ (M/x)^3*(2*M*x)^4*M := H.trans (by gcongr)
  have e : (M/x)^3*(2*M*x)^4*M = 16*M^8*x := by field_simp; ring
  linarith [e]

theorem local_disk {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hn : χ ≠ 1)
    {x M t : ℝ} (hx : 0 < x) (hM : 0 < M) (hs : 16*M^8*x < 1)
    (hp : ‖LFunctionTrivChar q (1+x)‖ ≤ M/x)
    (hd : ‖(χ^2).LFunction (1+x+2*I*t)‖ ≤ M)
    (D : ∀ z ∈ Metric.closedBall (1+x+I*t) (3*x/2), ‖deriv χ.LFunction z‖ ≤ M)
    {z : ℂ} (hz : z ∈ Metric.closedBall (1+x+I*t) (3*x/2)) :
    M*x/2 < ‖χ.LFunction z‖ ∧ ‖deriv χ.LFunction z / χ.LFunction z‖ ≤ 2/x := by
  let c : ℂ := 1+x+I*t
  have hc : c ∈ Metric.closedBall c (3*x/2) := Metric.mem_closedBall_self (by positivity)
  have H := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun z _ => (differentiable_LFunction hn z)) D (convex_closedBall c _) hz hc
  have hb : ‖c-z‖ ≤ 3*x/2 := by rw [←dist_eq_norm,dist_comm]; exact hz
  have hh := local_lower χ hx hM hs hp hd
  change 2*M*x < ‖χ.LFunction c‖ at hh
  have hl : M*x/2 < ‖χ.LFunction z‖ := by
    linarith [norm_sub_norm_le (χ.LFunction c) (χ.LFunction z), mul_le_mul_of_nonneg_left hb hM.le]
  refine ⟨hl, ?_⟩
  rw [norm_div, div_le_div_iff₀ (lt_trans (by positivity) hl) hx]
  nlinarith [mul_le_mul_of_nonneg_right (D z hz) hx.le]
end BVShort

namespace BVShort
open Complex DirichletCharacter Filter
open scoped Topology
lemma principal_le_zeta {q : ℕ} [NeZero q] {u : ℝ} (hu : 1 < u) :
    ‖LFunctionTrivChar q u‖ ≤ ‖riemannZeta u‖ := by
  have h : (u:ℂ) ≠ 1 := by exact_mod_cast hu.ne'
  rw [LFunctionTrivChar_eq_mul_riemannZeta h, norm_mul, norm_prod]
  apply mul_le_of_le_one_left (norm_nonneg _)
  apply Finset.prod_le_one (fun _ _ => norm_nonneg _)
  intro p hp
  have h1 : 1 ≤ (p:ℝ) := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_le
  have ha : 0 ≤ (p:ℝ)^(-u) := by positivity
  have hb := Real.rpow_le_one_of_one_le_of_nonpos h1 (show -u ≤ 0 by linarith)
  have e : (1:ℂ) - (p:ℂ)^(-(u:ℂ)) = ((1-(p:ℝ)^(-u):ℝ):ℂ) := by
    push_cast; rw [Complex.ofReal_cpow (by positivity)]; simp
  rw [e, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]; linarith
lemma principal_uniform : ∀ᶠ u : ℝ in 𝓝[>] 1, ∀ (q : ℕ) [NeZero q],
    ‖LFunctionTrivChar q u‖ ≤ 2 / (u-1) := by
  have ht : Tendsto (fun x : ℝ => (x:ℂ)) (𝓝[>] 1) (𝓝[≠] 1) :=
    continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin (by
      intro x hx; change (x:ℂ) ≠ 1; exact_mod_cast (show 1 < x from hx).ne')
  have hh := (riemannZeta_residue_one.comp ht).norm.eventually (gt_mem_nhds (show ‖(1:ℂ)‖ < 2 by norm_num))
  filter_upwards [hh, eventually_mem_nhdsWithin] with u hu hu1
  have hu' : 1 < u := hu1
  intro q _
  apply (principal_le_zeta hu').trans
  apply (le_div_iff₀ (sub_pos.mpr hu')).mpr
  change ‖((u:ℂ)-1)*riemannZeta u‖ < 2 at hu
  rw [norm_mul, ←ofReal_one, ←ofReal_sub, norm_real, Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hu')] at hu
  simpa [mul_comm] using hu.le
end BVShort

end

section

open Complex Filter LSeries Metric Set Topology
namespace BVHeight
noncomputable section
variable (t : ℝ)
lemma hre {s : ℂ} (hs : s ∈ (ball (2+I*t : ℂ) (7/4 : ℝ))) : 1/4 < s.re := by
  have h := Complex.abs_re_le_norm (s-(2+I*t))
  rw [mem_ball, dist_eq_norm] at hs
  norm_num [sub_re, add_re, mul_re] at h
  linarith [neg_abs_le (s.re-2)]
lemma hnorm {s : ℂ} (hs : s ∈ (ball (2+I*t : ℂ) (7/4 : ℝ))) : ‖s‖ ≤ (4+|t|) := by
  rw [mem_ball, dist_eq_norm] at hs
  have h := norm_sub_norm_le s (2+I*t)
  have h' := norm_add_le (2:ℂ) (I*t)
  simp [Real.norm_eq_abs] at h'
  linarith

noncomputable def characterLBlock {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (k : ℕ) (s : ℂ) : ℂ :=
  ∑ j : ZMod N, χ j * ((k * N + j.val : ℕ) : ℂ) ^ (-s)

theorem characterLBlock_recenter {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (k : ℕ) (s : ℂ) :
    characterLBlock χ k s =
      ∑ j : ZMod N, χ j *
        (((k * N + j.val : ℕ) : ℂ) ^ (-s) - (((k + 1) * N : ℕ) : ℂ) ^ (-s)) := by
  rw [characterLBlock]
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  rw [χ.sum_eq_zero_of_ne_one hχ, zero_mul, sub_zero]

theorem characterLBlock_differentiableOn {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (k : ℕ) :
    DifferentiableOn ℂ (characterLBlock χ k) (ball (2+I*t : ℂ) (7/4 : ℝ)) := by
  have hN : N ≠ 1 := by
    intro h
    subst N
    exact hχ (Subsingleton.elim _ _)
  rw [show characterLBlock χ k = fun s ↦
      ∑ j : ZMod N, χ j *
        (((k * N + j.val : ℕ) : ℂ) ^ (-s) - (((k + 1) * N : ℕ) : ℂ) ^ (-s)) by
    funext s
    exact characterLBlock_recenter χ hχ k s]
  intro s hs
  apply DifferentiableAt.differentiableWithinAt
  apply DifferentiableAt.fun_sum
  intro j hj
  by_cases hj0 : j = 0
  · subst j
    rw [χ.map_zero' hN]
    simp
  · have hx : ((k * N + j.val : ℕ) : ℂ) ≠ 0 := by
      exact Nat.cast_ne_zero.mpr (by
        have hjv : j.val ≠ 0 := (ZMod.val_ne_zero j).mpr hj0
        omega)
    have hy : ((((k + 1) * N : ℕ) : ℂ)) ≠ 0 := by
      exact Nat.cast_ne_zero.mpr (Nat.mul_ne_zero (by omega) (NeZero.ne N))
    exact (((differentiableAt_id.neg).const_cpow (Or.inl hx)).sub
      ((differentiableAt_id.neg).const_cpow (Or.inl hy))).const_mul (χ j)

theorem norm_cpow_neg_sub_le {s : ℂ} {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y)
    (hre : (1 / 4 : ℝ) ≤ s.re) (hs : ‖s‖ ≤ (4+|t|)) :
    ‖(x : ℂ) ^ (-s) - (y : ℂ) ^ (-s)‖ ≤
      (4+|t|) * (y - x) * x ^ (-5 / 4 : ℝ) := by
  have hs0 : -s ≠ 0 := by
    intro h
    have : s = 0 := neg_eq_zero.mp h
    subst s
    norm_num at hre
  have hderiv (t : ℝ) (ht : t ∈ Icc x y) :
      HasDerivWithinAt (fun u : ℝ ↦ (u : ℂ) ^ (-s))
        ((-s) * (t : ℂ) ^ (-s - 1)) (Icc x y) t := by
    exact (hasDerivAt_ofReal_cpow_const (ne_of_gt (lt_of_lt_of_le zero_lt_one (hx.trans ht.1)))
      hs0).hasDerivWithinAt
  have hbound (u : ℝ) (ht : u ∈ Icc x y) :
      ‖(-s) * (u : ℂ) ^ (-s - 1)‖ ≤ (4+|t|) * x ^ (-5 / 4 : ℝ) := by
    have htpos : 0 < u := lt_of_lt_of_le zero_lt_one (hx.trans ht.1)
    have hpow_exp : u ^ (-s.re - 1) ≤ u ^ (-5 / 4 : ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le
      · exact hx.trans ht.1
      · linarith
    have hpow_base : u ^ (-5 / 4 : ℝ) ≤ x ^ (-5 / 4 : ℝ) := by
      exact Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le zero_lt_one hx) ht.1 (by norm_num)
    rw [norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos htpos]
    exact mul_le_mul hs (hpow_exp.trans hpow_base) (Real.rpow_nonneg htpos.le _) (by positivity)
  have hmv := (convex_Icc x y : Convex ℝ (Icc x y)).norm_image_sub_le_of_norm_hasDerivWithin_le
    hderiv hbound (left_mem_Icc.mpr hxy) (right_mem_Icc.mpr hxy)
  rw [norm_sub_rev, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hxy)] at hmv
  calc
    ‖(x : ℂ) ^ (-s) - (y : ℂ) ^ (-s)‖
        ≤ ((4+|t|) * x ^ (-5 / 4 : ℝ)) * (y - x) := hmv
    _ = (4+|t|) * (y - x) * x ^ (-5 / 4 : ℝ) := by ring

noncomputable def characterLBlockMajorant (N k : ℕ) : ℝ :=
  (4+|t|) * (N : ℝ) ^ 2 * ((k + 1 : ℕ) : ℝ) ^ (-5 / 4 : ℝ)

theorem norm_characterLBlock_le {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (k : ℕ) {s : ℂ}
    (hs : s ∈ (ball (2+I*t : ℂ) (7/4 : ℝ))) :
    ‖characterLBlock χ k s‖ ≤ characterLBlockMajorant t N k := by
  have hN : N ≠ 1 := by
    intro h
    subst N
    exact hχ (Subsingleton.elim _ _)
  rw [characterLBlock_recenter χ hχ]
  calc
    ‖∑ j : ZMod N, χ j *
        (((k * N + j.val : ℕ) : ℂ) ^ (-s) - (((k + 1) * N : ℕ) : ℂ) ^ (-s))‖
        ≤ ∑ j : ZMod N, ‖χ j *
          (((k * N + j.val : ℕ) : ℂ) ^ (-s) - (((k + 1) * N : ℕ) : ℂ) ^ (-s))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _j : ZMod N,
        (4+|t|) * (N : ℝ) * ((k + 1 : ℕ) : ℝ) ^ (-5 / 4 : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      by_cases hj0 : j = 0
      · subst j
        rw [χ.map_zero' hN]
        simp only [zero_mul, norm_zero]
        positivity
      · have hjv : j.val ≠ 0 := (ZMod.val_ne_zero j).mpr hj0
        have hxoneNat : 1 ≤ k * N + j.val := by omega
        have hxyNat : k * N + j.val ≤ (k + 1) * N := by
          have hjlt := j.val_lt
          rw [Nat.add_mul, one_mul]
          omega
        have hlenNat : (k + 1) * N - (k * N + j.val) ≤ N := by
          have hjlt := j.val_lt
          rw [Nat.add_mul, one_mul]
          omega
        have hxkNat : k + 1 ≤ k * N + j.val := by
          have hNp := NeZero.pos N
          have hk : k ≤ k * N := by
            simpa using Nat.mul_le_mul_left k hNp
          omega
        have hxone : (1 : ℝ) ≤ (k * N + j.val : ℕ) := by exact_mod_cast hxoneNat
        have hxy : ((k * N + j.val : ℕ) : ℝ) ≤ ((k + 1) * N : ℕ) := by
          exact_mod_cast hxyNat
        have hlen : (((k + 1) * N : ℕ) : ℝ) - (k * N + j.val : ℕ) ≤ N := by
          rw [← Nat.cast_sub hxyNat]
          exact_mod_cast hlenNat
        have hxk : (((k + 1 : ℕ) : ℝ)) ≤ (k * N + j.val : ℕ) := by
          exact_mod_cast hxkNat
        have hpow : ((k * N + j.val : ℕ) : ℝ) ^ (-5 / 4 : ℝ) ≤
            ((k + 1 : ℕ) : ℝ) ^ (-5 / 4 : ℝ) := by
          exact Real.rpow_le_rpow_of_nonpos (by positivity) hxk (by norm_num)
        have hvar := norm_cpow_neg_sub_le t hxone hxy
          (le_of_lt (hre t hs))
          (hnorm t hs)
        rw [norm_mul]
        calc
          ‖χ j‖ * ‖((k * N + j.val : ℕ) : ℂ) ^ (-s) -
              (((k + 1) * N : ℕ) : ℂ) ^ (-s)‖
              ≤ ‖χ j‖ * ((4+|t|) *
                ((((k + 1) * N : ℕ) : ℝ) - (k * N + j.val : ℕ)) *
                  ((k * N + j.val : ℕ) : ℝ) ^ (-5 / 4 : ℝ)) :=
            mul_le_mul_of_nonneg_left hvar (norm_nonneg _)
          _ ≤ 1 * ((4+|t|) *
                ((((k + 1) * N : ℕ) : ℝ) - (k * N + j.val : ℕ)) *
                  ((k * N + j.val : ℕ) : ℝ) ^ (-5 / 4 : ℝ)) := by
            gcongr
            exact χ.norm_le_one j
          _ = (4+|t|) *
                ((((k + 1) * N : ℕ) : ℝ) - (k * N + j.val : ℕ)) *
                  ((k * N + j.val : ℕ) : ℝ) ^ (-5 / 4 : ℝ) := by ring
          _ ≤ (4+|t|) * (N : ℝ) *
                ((k * N + j.val : ℕ) : ℝ) ^ (-5 / 4 : ℝ) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hlen (by positivity)) (Real.rpow_nonneg (by positivity) _)
          _ ≤ (4+|t|) * (N : ℝ) * ((k + 1 : ℕ) : ℝ) ^ (-5 / 4 : ℝ) := by
            exact mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = characterLBlockMajorant t N k := by
      simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
      rw [characterLBlockMajorant]
      ring

noncomputable def characterLBlockSeries {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  ∑' k : ℕ, characterLBlock χ k s

theorem characterLBlockMajorant_summable (N : ℕ) :
    Summable (characterLBlockMajorant t N) := by
  have hp : Summable (fun n : ℕ ↦ (n : ℝ) ^ (-5 / 4 : ℝ)) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have hshift := (summable_nat_add_iff 1).mpr hp
  change Summable (fun k : ℕ ↦
    (4+|t|) * (N : ℝ) ^ 2 * ((k + 1 : ℕ) : ℝ) ^ (-5 / 4 : ℝ))
  exact hshift.mul_left ((4+|t|) * (N : ℝ) ^ 2)

theorem characterLBlockSeries_differentiableOn {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) :
    DifferentiableOn ℂ (characterLBlockSeries χ) (ball (2+I*t : ℂ) (7/4 : ℝ)) := by
  change DifferentiableOn ℂ (fun s ↦ ∑' k : ℕ, characterLBlock χ k s)
    (ball (2+I*t : ℂ) (7/4 : ℝ))
  exact Complex.differentiableOn_tsum_of_summable_norm
    (characterLBlockMajorant_summable t N)
    (fun k ↦ characterLBlock_differentiableOn t χ hχ k)
    (by exact Metric.isOpen_ball)
    (fun k s hs ↦ norm_characterLBlock_le t χ hχ k hs)

theorem LFunction_eq_characterLBlockSeries_of_one_lt_re {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hN : N ≠ 1) {s : ℂ} (hs : 1 < s.re) :
    χ.LFunction s = characterLBlockSeries χ s ∧ Summable (fun k => characterLBlock χ k s) := by
  have hzero : (fun n : ℕ ↦ χ n) 0 = 0 := by
    simpa using χ.map_zero' hN
  have hsum : Summable (fun n : ℕ ↦ χ n * (n : ℂ) ^ (-s)) := by
    rw [← funext (LSeries.term_def₀ hzero s)]
    exact DirichletCharacter.LSeriesSummable_of_one_lt_re χ hs
  have hterm (j : ZMod N) (k : ℕ) :
      χ ((j.val + N * k : ℕ) : ZMod N) * ((j.val + N * k : ℕ) : ℂ) ^ (-s) =
        χ j * ((k * N + j.val : ℕ) : ℂ) ^ (-s) := by
    have hcast : ((j.val + N * k : ℕ) : ZMod N) = j := by
      simp [Nat.cast_add, Nat.cast_mul]
    rw [hcast]
    congr 2
    simp only [Nat.add_comm, Nat.mul_comm]
  have hsub (j : ZMod N) :
      Summable (fun k : ℕ ↦ χ j * ((k * N + j.val : ℕ) : ℂ) ^ (-s)) := by
    have hinj : Function.Injective (fun k : ℕ ↦ j.val + N * k) := by
      intro a b hab
      exact Nat.mul_left_cancel (NeZero.pos N) (Nat.add_left_cancel hab)
    have h := hsum.comp_injective hinj
    exact h.congr (hterm j)
  have hswap := Summable.tsum_finsetSum (s := Finset.univ)
    (fun j _hj ↦ hsub j)
  refine ⟨?_, ?_⟩
  · exact calc
    χ.LFunction s = LSeries (χ ·) s := DirichletCharacter.LFunction_eq_LSeries χ hs
    _ = ∑' n : ℕ, χ n * (n : ℂ) ^ (-s) := by
      rw [LSeries_def₀ hzero]
      congr 1
      funext n
      rw [Complex.cpow_neg, div_eq_mul_inv]
    _ = ∑ j : ZMod N, ∑' k : ℕ,
        χ ((j.val + N * k : ℕ) : ZMod N) * ((j.val + N * k : ℕ) : ℂ) ^ (-s) :=
      Nat.sumByResidueClasses hsum N
    _ = ∑ j : ZMod N, ∑' k : ℕ,
        χ j * ((k * N + j.val : ℕ) : ℂ) ^ (-s) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact tsum_congr (hterm j)
    _ = ∑' k : ℕ, ∑ j : ZMod N,
        χ j * ((k * N + j.val : ℕ) : ℂ) ^ (-s) := by
      simpa only [Finset.mem_univ, ↓reduceIte] using hswap.symm
    _ = characterLBlockSeries χ s := rfl

  · classical
    have aux (S : Finset (ZMod N)) : Summable (fun k : ℕ => ∑ j ∈ S, χ j * ((k*N+j.val:ℕ):ℂ)^(-s)) := by
      induction S using Finset.induction_on with
      | empty => simp
      | insert j S hj ih => simpa [Finset.sum_insert hj] using (hsub j).add ih
    exact aux _

theorem LFunction_eq_characterLBlockSeries {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {s : ℂ}
    (hs : s ∈ (ball (2+I*t : ℂ) (7/4 : ℝ))) : χ.LFunction s = characterLBlockSeries χ s := by
  have hL : AnalyticOnNhd ℂ (χ.LFunction) (ball (2+I*t : ℂ) (7/4 : ℝ)) :=
    (DirichletCharacter.differentiable_LFunction hχ).differentiableOn.analyticOnNhd
      Metric.isOpen_ball
  have hB : AnalyticOnNhd ℂ (characterLBlockSeries χ) (ball (2+I*t : ℂ) (7/4 : ℝ)) :=
    (characterLBlockSeries_differentiableOn t χ hχ).analyticOnNhd Metric.isOpen_ball
  have h2 : (2+I*t : ℂ) ∈ (ball (2+I*t : ℂ) (7/4 : ℝ)) := by
    rw [mem_ball]
    norm_num
  have heq : χ.LFunction =ᶠ[𝓝 (2+I*t : ℂ)] characterLBlockSeries χ := by
    have hV : {z : ℂ | 1 < z.re} ∈ 𝓝 (2+I*t : ℂ) :=
      (continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds (by norm_num [mul_re])
    filter_upwards [hV] with z hz
    exact (LFunction_eq_characterLBlockSeries_of_one_lt_re χ (by rintro rfl; exact hχ (Subsingleton.elim _ _)) hz).1
  exact hL.eqOn_of_preconnected_of_eventuallyEq hB
    (convex_ball (2+I*t : ℂ) (7 / 4 : ℝ)).isPreconnected h2 heq hs

private theorem sum_zmod_val_inv_le_harmonic_bv622 (N : ℕ) [NeZero N] :
    ∑ j : ZMod N, ((j.val : ℝ)⁻¹) ≤ 2 * (harmonic N : ℝ) := by
  calc
    ∑ j : ZMod N, ((j.val : ℝ)⁻¹) = ∑ i : Fin N, ((i.val : ℝ)⁻¹) := by
      symm
      apply Fintype.sum_equiv (ZMod.finEquiv N).toEquiv
      intro i
      change ((i.val : ℝ)⁻¹) = ((((ZMod.finEquiv N) i).val : ℝ)⁻¹)
      congr 2
      obtain _ | n := N
      · exact (NeZero.ne 0 rfl).elim
      · rfl
    _ ≤ ∑ i : Fin N, 2 * ((((i.val + 1 : ℕ) : ℝ))⁻¹) := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases hi0 : i.val = 0
      · simp [hi0]
      · have hipos : (0 : ℝ) < i.val := by exact_mod_cast Nat.pos_of_ne_zero hi0
        have hisucc : (0 : ℝ) < i.val + 1 := by positivity
        rw [← one_div, ← div_eq_mul_inv]
        norm_num only [Nat.cast_add, Nat.cast_one]
        rw [div_le_div_iff₀ hipos hisucc]
        norm_num
        have hiNat : i.val + 1 ≤ 2 * i.val := by omega
        exact_mod_cast hiNat
    _ = 2 * (harmonic N : ℝ) := by
      rw [← Finset.mul_sum]
      congr 1
      rw [Finset.sum_fin_eq_sum_range, harmonic, Rat.cast_sum]
      apply Finset.sum_congr rfl
      intro x hx
      simp [Finset.mem_range.mp hx]

private lemma weight {s : ℂ} {x U : ℝ} (hx : 1 ≤ x) (hxU : x ≤ U)
    (h : (1-s.re)*Real.log U ≤ 1) : ‖(x:ℂ)^(-s)‖ ≤ Real.exp 1 / x := by
  have xp : 0 < x := by linarith
  rw [norm_cpow_eq_rpow_re_of_pos xp, neg_re, le_div_iff₀ xp]
  nth_rw 2 [← Real.rpow_one x]
  rw [← Real.rpow_add xp]
  rw [Real.rpow_def_of_pos xp, Real.exp_le_exp]
  by_cases hs : 0 ≤ 1-s.re
  · nlinarith [mul_le_mul_of_nonneg_left (Real.log_le_log xp hxU) hs]
  · nlinarith [mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hs) (Real.log_nonneg hx)]

private lemma first {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hn1 : N ≠ 1)
    {s : ℂ} {U : ℝ} (hN : (N:ℝ) ≤ U) (h : (1-s.re)*Real.log U ≤ 1) :
    ‖characterLBlock χ 0 s‖ ≤ Real.exp 1 * (2*(1+Real.log N)) := by
  simp only [characterLBlock, zero_mul, zero_add]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ j : ZMod N, Real.exp 1 * (j.val : ℝ)⁻¹ := by
      apply Finset.sum_le_sum; intro j _
      by_cases hj : j = 0
      · subst j; simp [χ.map_zero' hn1]
      have hv : 1 ≤ j.val := Nat.one_le_iff_ne_zero.mpr ((ZMod.val_ne_zero j).mpr hj)
      rw [norm_mul]
      apply (mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one j)).trans
      simpa only [ofReal_natCast, div_eq_mul_inv] using weight (s:=s) (x:=(j.val:ℝ)) (by exact_mod_cast hv)
        ((show (j.val:ℝ) ≤ N by exact_mod_cast j.val_lt.le).trans hN) h
    _ ≤ _ := by rw [← Finset.mul_sum]; gcongr; exact (sum_zmod_val_inv_le_harmonic_bv622 N).trans (by gcongr; exact harmonic_le_one_add_log N)

private lemma middle {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (k : ℕ) {s : ℂ} {U : ℝ} (hN : ((k+2:ℕ):ℝ)*N ≤ U) (h : (1-s.re)*Real.log U ≤ 1) :
    ‖characterLBlock χ (k+1) s‖ ≤ Real.exp 1 / (k+1) := by
  have hp : 0 < ((k+1)*N) := Nat.mul_pos (by omega) (NeZero.pos N)
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _j : ZMod N, Real.exp 1 / (((k+1)*N:ℕ):ℝ) := by
      apply Finset.sum_le_sum; intro j _
      let n := (k+1)*N+j.val
      have hn : 1 ≤ n := by dsimp [n]; omega
      have hnu : n ≤ (k+2)*N := by
        dsimp [n]
        have hj := j.val_lt
        nlinarith
      rw [norm_mul]; apply (mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one j)).trans
      change ‖(n:ℂ)^(-s)‖ ≤ _
      rw [← Complex.ofReal_natCast n]
      apply (weight (s:=s) (x:=(n:ℝ)) (by exact_mod_cast hn) ((show (n:ℝ) ≤ ((k+2:ℕ):ℝ)*N by exact_mod_cast hnu).trans hN) h).trans
      gcongr; first | exact_mod_cast hp | exact_mod_cast Nat.le_add_right ((k+1)*N) j.val
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, Nat.cast_mul, Nat.cast_add, Nat.cast_one]; field_simp [NeZero.ne N]

noncomputable def tailC : ℝ := ∑' i : ℕ, ((i+1:ℕ):ℝ)^(-9/8:ℝ)
private lemma tail_sum : Summable (fun i : ℕ => ((i+1:ℕ):ℝ)^(-9/8:ℝ)) :=
  (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr (by norm_num))

theorem split_bound {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hn : χ ≠ 1)
    {s : ℂ} (hs : s ∈ (ball (2+I*t : ℂ) (7/4 : ℝ))) (K : ℕ) {U : ℝ} (hU : ((K+2:ℕ):ℝ)*N ≤ U)
    (h : (1-s.re)*Real.log U ≤ 1) (hK : ((4+|t|)*(N:ℝ)^2)^8 ≤ K) :
    ‖χ.LFunction s‖ ≤ Real.exp 1 * (2*(1+Real.log N) + (1+Real.log K)) + tailC := by
  let f := fun i => ‖characterLBlock χ i s‖
  have hf : Summable f := (characterLBlockMajorant_summable t N).of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun i => norm_characterLBlock_le t χ hn i hs)
  rw [LFunction_eq_characterLBlockSeries t χ hn hs, characterLBlockSeries]
  apply (norm_tsum_le_tsum_norm hf).trans
  change ∑' i, f i ≤ _
  rw [← hf.sum_add_tsum_nat_add (K+1), Finset.sum_range_succ' f K]
  have hfirst := first χ (by rintro rfl; exact hn (Subsingleton.elim _ _)) (show (N:ℝ) ≤ U by apply le_trans _ hU; push_cast; nlinarith [Nat.cast_nonneg (α:=ℝ) K, Nat.cast_nonneg (α:=ℝ) N, mul_nonneg (Nat.cast_nonneg (α:=ℝ) K) (Nat.cast_nonneg (α:=ℝ) N)]) h
  have hmid : ∑ i ∈ Finset.range K, f (i+1) ≤ Real.exp 1 * (1+Real.log K) := by
    calc
      _ ≤ ∑ i ∈ Finset.range K, Real.exp 1 * (((i+1:ℕ):ℝ)⁻¹) := by
        apply Finset.sum_le_sum; intro i hi
        simpa only [div_eq_mul_inv, Nat.cast_add, Nat.cast_one] using middle χ i (s:=s) (U:=U) (by apply le_trans _ hU; gcongr; exact (Finset.mem_range.mp hi).le) h
      _ = Real.exp 1 * (harmonic K : ℝ) := by simp [harmonic, Finset.mul_sum]
      _ ≤ _ := by gcongr; exact harmonic_le_one_add_log K
  have htail : (∑' i : ℕ, f (i+(K+1))) ≤ tailC := by
    apply Summable.tsum_le_tsum _ ((summable_nat_add_iff _).mpr hf) tail_sum
    intro i
    let y : ℝ := ((i+(K+1)+1:ℕ):ℝ)
    have yp : 0 < y := by dsimp [y]; positivity
    have hy : (K:ℝ) ≤ y := by dsimp [y]; exact_mod_cast (by omega : K ≤ i+(K+1)+1)
    have hco : (4+|t|)*(N:ℝ)^2 ≤ y^(1/8:ℝ) := by
      have hh := Real.rpow_le_rpow (show 0 ≤ ((4+|t|)*(N:ℝ)^2)^8 by positivity) (hK.trans hy) (by norm_num : 0 ≤ (1/8:ℝ))
      rwa [← Real.rpow_natCast _ 8, ← Real.rpow_mul (by positivity), show (↑(8:ℕ):ℝ)*(1/8)=1 by norm_num, Real.rpow_one] at hh
    apply (norm_characterLBlock_le t χ hn _ hs).trans
    change (4+|t|)*(N:ℝ)^2*y^(-5/4:ℝ) ≤ _
    calc
      _ ≤ y^(1/8:ℝ)*y^(-5/4:ℝ) := by gcongr
      _ = y^(-9/8:ℝ) := by rw [← Real.rpow_add yp]; norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_nonpos (by positivity) (by dsimp [y]; exact_mod_cast (by omega : i+1 ≤ i+(K+1)+1)) (by norm_num)
  change f 0 ≤ _ at hfirst
  linarith

noncomputable def Q (N : ℕ) (t : ℝ) := 2+(N:ℝ)*(2+|t|)
noncomputable def C := 30*Real.exp 1 + |tailC|
lemma Q_ge {N : ℕ} [NeZero N] : 4+|t| ≤ Q N t := by
  have hn : (1:ℝ) ≤ N := by exact_mod_cast NeZero.pos N
  unfold Q; nlinarith [mul_le_mul_of_nonneg_right hn (show 0 ≤ 2+|t| by positivity)]
lemma logQ_ge {N : ℕ} [NeZero N] : 1 ≤ Real.log (Q N t) := by
  rw [← Real.exp_le_exp, Real.exp_log (by linarith [Q_ge (N:=N) t, abs_nonneg t])]
  linarith [Real.exp_one_lt_d9, Q_ge (N:=N) t, abs_nonneg t]

theorem disk_bound {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hn : χ ≠ 1)
    {s : ℂ} (hs : dist s (1+I*t) ≤ 1/(26*Real.log (Q N t))) :
    ‖χ.LFunction s‖ ≤ C*Real.log (Q N t) := by
  let A := Q N t
  have hA : 4 ≤ A := by linarith [Q_ge (N:=N) t, abs_nonneg t]
  have ha : 1 ≤ Real.log A := logQ_ge t
  have hN : (N:ℝ) ≤ A := by dsimp [A,Q]; nlinarith [mul_nonneg (Nat.cast_nonneg (α:=ℝ) N) (abs_nonneg t)]
  let K := ⌈A^24⌉₊
  have hk : A^24 ≤ (K:ℝ) := Nat.le_ceil _
  have hk' : (K:ℝ) < A^24 + 1 := Nat.ceil_lt_add_one (by positivity)
  have hk2 : (K:ℝ)+2 ≤ A^25 := by
    rw [pow_succ]; nlinarith [show (1:ℝ) ≤ A^24 by exact one_le_pow₀ (by linarith) ]
  have hk0 : (0:ℝ) < K := lt_of_lt_of_le (by positivity) hk
  have hlk := Real.log_le_log hk0 (show (K:ℝ) ≤ A^25 by linarith)
  rw [Real.log_pow] at hlk
  have hln := Real.log_le_log (show (0:ℝ) < N by exact_mod_cast NeZero.pos N) hN
  change dist s _ ≤ 1/(26*Real.log A) at hs
  have hw := (le_div_iff₀ (by positivity : 0 < 26*Real.log A)).mp hs
  have hd : dist s (1+I*t) ≤ 1/26 := by nlinarith [mul_le_mul_of_nonneg_left ha (dist_nonneg (x:=s) (y:=1+I*t))]
  have hD : s ∈ (ball (2+I*t : ℂ) (7/4 : ℝ)) := by
    have H := dist_triangle s (1+I*t) (2+I*t)
    rw [dist_add_right] at H; norm_num [dist_eq_norm] at H hd ⊢; linarith
  apply (split_bound t χ hn hD K (U:=A^26) (by
    push_cast; rw [pow_succ A 25]; gcongr) (by
    rw [Real.log_pow]; have hv := abs_re_le_norm (s-(1+I*t))
    norm_num [sub_re, add_re, mul_re] at hv
    rw [dist_eq_norm] at hw
    norm_num only [Nat.cast_ofNat]
    apply le_trans _ hw
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    linarith [neg_le_abs (s.re-1)]) (by
    apply le_trans _ hk
    calc
      _ ≤ (A*A^2)^8 := by gcongr; exact Q_ge t
      _ = _ := by ring)).trans
  change _ ≤ C*Real.log A
  norm_num only [Nat.cast_ofNat] at hlk
  unfold C; have he := Real.exp_pos 1
  nlinarith [mul_le_mul_of_nonneg_left hln he.le, mul_le_mul_of_nonneg_left hlk he.le,
    mul_le_mul_of_nonneg_left ha (abs_nonneg tailC), le_abs_self tailC,
    mul_le_mul_of_nonneg_left ha he.le]

theorem deriv_bound {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hn : χ ≠ 1)
    {s : ℂ} (hs : dist s (1+I*t) ≤ 1/(52*Real.log (Q N t))) :
    ‖deriv χ.LFunction s‖ ≤ 52*C*(Real.log (Q N t))^2 := by
  have h := logQ_ge (N:=N) t
  let R := 1/(52*Real.log (Q N t))
  have hr : 0 < R := by dsimp [R]; positivity
  have H := norm_deriv_le_of_forall_mem_sphere_norm_le (f:=χ.LFunction) (c:=s) hr
    (DirichletCharacter.differentiable_LFunction hn).diffContOnCl (C:=C*Real.log (Q N t)) (by
      intro z hz; apply disk_bound t χ hn
      apply (dist_triangle z s _).trans
      rw [mem_sphere_iff_norm] at hz
      rw [dist_eq_norm z s, hz]; change R+_ ≤ _
      have hh : R+R = 1/(26*Real.log (Q N t)) := by dsimp [R]; ring
      rw [← hh]; gcongr)
  apply H.trans_eq; dsimp [R]; rw [div_div_eq_mul_div, div_one]; ring

private noncomputable def mean {N : ℕ} (χ : DirichletCharacter ℂ N) [NeZero N] : ℂ :=
  (∑ j : ZMod N, χ j) / N
private lemma mean_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : ‖mean χ‖ ≤ 1 := by
  have hn : (0:ℝ) < N := by exact_mod_cast NeZero.pos N
  rw [mean, norm_div, Complex.norm_natCast, div_le_iff₀ hn, one_mul]
  apply (norm_sum_le _ _).trans
  simpa using Finset.sum_le_sum (s:=Finset.univ) (fun (j : ZMod N) _ => χ.norm_le_one j)
private noncomputable def prim (N k : ℕ) (s : ℂ) : ℂ :=
  (((k*N:ℕ):ℂ)^(-s+1))/(-s+1)
private lemma prim_le {N k : ℕ} (hk : 0 < k*N) {s : ℂ} (hs : 1 < s.re) :
    ‖prim N k s‖ ≤ 1/‖-s+1‖ := by
  rw [prim,norm_div]; gcongr
  rw [← ofReal_natCast, norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hk)]
  apply Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hk); simp; linarith

private lemma error_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {s : ℂ} (hs : s ∈ (ball (2+I*t : ℂ) (7/4 : ℝ))) (hr : 1 < s.re) {k : ℕ} (hk : 1 ≤ k) :
    ‖characterLBlock χ k s - mean χ * (prim N (k+1) s - prim N k s)‖ ≤
    2*(4+|t|)*(N:ℝ)^2*(k:ℝ)^(-5/4:ℝ) := by
  let a : ℝ := (k*N:ℕ)
  let b : ℝ := ((k+1)*N:ℕ)
  let F := fun x : ℝ => (x:ℂ)^(-s)
  have hka : (k:ℝ) ≤ a := by dsimp [a]; exact_mod_cast (Nat.le_mul_of_pos_right k (NeZero.pos N))
  have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hab : b-a=N := by dsimp [a,b]; push_cast; ring
  have hn : (0:ℝ) < N := by exact_mod_cast NeZero.pos N
  have hab' : a ≤ b := by linarith
  have var (x : ℝ) (hx : x ∈ Icc a b) : ‖F x - F b‖ ≤ (4+|t|)*N*(k:ℝ)^(-5/4:ℝ) := by
    apply (norm_cpow_neg_sub_le t (hk1.trans (hka.trans hx.1)) hx.2 (hre t hs).le (hnorm t hs)).trans
    apply mul_le_mul (mul_le_mul_of_nonneg_left (by linarith [hx.1]) (by positivity))
      (Real.rpow_le_rpow_of_nonpos (by positivity) (hka.trans hx.1) (by norm_num)) (Real.rpow_nonneg (by linarith [hx.1]) _) (by positivity)
  let S := ∑ j : ZMod N, χ j
  have H1 : ‖characterLBlock χ k s-S*F b‖ ≤ N*((4+|t|)*N*(k:ℝ)^(-5/4:ℝ)) := by
    unfold characterLBlock; dsimp only [S]; rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _j : ZMod N, (4+|t|)*N*(k:ℝ)^(-5/4:ℝ) := by
        apply Finset.sum_le_sum; intro j _; rw [← mul_sub,norm_mul]
        apply (mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one j)).trans
        simpa only [F,ofReal_natCast] using var ((k*N+j.val:ℕ):ℝ) (by
          change _ ≤ _ ∧ _ ≤ _; dsimp [a,b]; exact_mod_cast (show k*N ≤ k*N+j.val ∧ k*N+j.val ≤ (k+1)*N by have := j.val_lt; constructor <;> nlinarith))
      _ = _ := by simp
  have intF : IntervalIntegrable F MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable
    intro x hx; apply (hasDerivAt_ofReal_cpow_const (x:=x) _ _).continuousAt.continuousWithinAt
    · rw [uIcc_of_le hab'] at hx; linarith [hx.1]
    · intro H; have H' := congrArg Complex.re H; simp at H'; linarith
  have H2 := intervalIntegral.norm_integral_le_of_norm_le_const (a:=a) (b:=b) (f:=fun x => F b - F x) (C:=(4+|t|)*N*(k:ℝ)^(-5/4:ℝ)) (by
    intro x hx; rw [uIoc_of_le hab'] at hx; rw [norm_sub_rev]; exact var _ ⟨hx.1.le,hx.2⟩)
  rw [intervalIntegral.integral_sub intervalIntegrable_const intF, intervalIntegral.integral_const, hab,abs_of_pos hn] at H2
  have he : (∫ x in a..b, F x) = prim N (k+1) s - prim N k s := by
    dsimp only [F]; rw [integral_cpow (Or.inr ⟨by intro H; have hh := congrArg Complex.re H; simp at hh; linarith, by rw [uIcc_of_le hab']; intro hh; linarith [hh.1]⟩),sub_div]; simp [prim,a,b]
  rw [he, Complex.real_smul] at H2
  have he' : mean χ*(N:ℂ)=S := by dsimp [mean,S]; field_simp [NeZero.ne N]
  calc
    _ = ‖(characterLBlock χ k s-S*F b)+mean χ*((N:ℂ)*F b-(prim N (k+1) s-prim N k s))‖ := by congr 1; rw [← he']; ring
    _ ≤ _ := by apply (norm_add_le _ _).trans; rw [norm_mul]; have hm := mean_le χ; push_cast at H2; nlinarith [mul_le_of_le_one_left (norm_nonneg ((N:ℂ)*F b-(prim N (k+1) s-prim N k s))) hm]

private lemma sum_tail_bound {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {s : ℂ} (hs : s ∈ (ball (2+I*t : ℂ) (7/4 : ℝ))) (hr : 1 < s.re) (K m : ℕ) (hK : ((4+|t|)*(N:ℝ)^2)^8 ≤ K) :
    ‖∑ i ∈ Finset.range m, characterLBlock χ (K+1+i) s‖ ≤ 2*tailC+2/‖-s+1‖ := by
  let p := fun i => prim N (K+1+i) s
  let f := fun i => characterLBlock χ (K+1+i) s
  let e := fun i => f i-mean χ*(p (i+1)-p i)
  have err (i : ℕ) : ‖e i‖ ≤ 2*((i+1:ℕ):ℝ)^(-9/8:ℝ) := by
    let y : ℝ := ((K+1+i:ℕ):ℝ)
    have yp : 0 < y := by dsimp [y]; positivity
    have hy : (K:ℝ) ≤ y := by dsimp [y]; exact_mod_cast (by omega : K ≤ K+1+i)
    have hco : (4+|t|)*(N:ℝ)^2 ≤ y^(1/8:ℝ) := by
      have hh := Real.rpow_le_rpow (show 0 ≤ ((4+|t|)*(N:ℝ)^2)^8 by positivity) (hK.trans hy) (by norm_num : 0 ≤ (1/8:ℝ))
      rwa [← Real.rpow_natCast _ 8, ← Real.rpow_mul (by positivity), show (↑(8:ℕ):ℝ)*(1/8)=1 by norm_num, Real.rpow_one] at hh
    apply (error_le t χ hs hr (k:=K+1+i) (by omega)).trans
    change 2*(4+|t|)*(N:ℝ)^2*y^(-5/4:ℝ) ≤ _
    calc
      _ = 2*(((4+|t|)*(N:ℝ)^2)*y^(-5/4:ℝ)) := by ring
      _ ≤ 2*(y^(1/8:ℝ)*y^(-5/4:ℝ)) := by gcongr
      _ = 2*y^(-9/8:ℝ) := by rw [← Real.rpow_add yp]; norm_num
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (by positivity) (by dsimp [y]; exact_mod_cast (by omega : i+1 ≤ K+1+i)) (by norm_num)) (by norm_num)
  have he : ‖∑ i ∈ Finset.range m, e i‖ ≤ 2*tailC := by
    apply (norm_sum_le _ _).trans; apply (Finset.sum_le_sum (fun i _ => err i)).trans
    rw [← Finset.mul_sum]; gcongr; exact tail_sum.sum_le_tsum _ (by intros; positivity)
  have hp (i : ℕ) : ‖p i‖ ≤ 1/‖-s+1‖ := prim_le (Nat.mul_pos (by omega) (NeZero.pos N)) hr
  have H : ‖mean χ*(p m-p 0)‖ ≤ 2/‖-s+1‖ := by
    rw [norm_mul]; apply (mul_le_of_le_one_left (norm_nonneg _) (mean_le χ)).trans
    apply (norm_sub_le _ _).trans
    apply (add_le_add (hp m) (hp 0)).trans_eq; ring
  have eqn : ∑ i ∈ Finset.range m, e i = ∑ i ∈ Finset.range m, f i-mean χ*(p m-p 0) := by
    dsimp only [e]; rw [Finset.sum_sub_distrib,← Finset.mul_sum, Finset.sum_range_sub]
  change ‖∑ i ∈ Finset.range m, f i‖ ≤ _
  rw [← sub_add_cancel (∑ i ∈ Finset.range m, f i) (mean χ*(p m-p 0)), ← eqn]
  exact (norm_add_le _ _).trans (add_le_add he H)

theorem right_bound {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hn1 : N ≠ 1)
    {s : ℂ} (hs : s ∈ (ball (2+I*t : ℂ) (7/4 : ℝ))) (hr : 1 < s.re) :
    ‖χ.LFunction s‖ ≤ 2*C*Real.log (Q N t) + 2/‖-s+1‖ := by
  let A := Q N t
  have hA : 4 ≤ A := by linarith [Q_ge (N:=N) t, abs_nonneg t]
  have ha : 1 ≤ Real.log A := logQ_ge t
  have hN : (N:ℝ) ≤ A := by dsimp [A,Q]; nlinarith [mul_nonneg (Nat.cast_nonneg (α:=ℝ) N) (abs_nonneg t)]
  let K := ⌈A^24⌉₊
  have hk : A^24 ≤ (K:ℝ) := Nat.le_ceil _
  have hk' : (K:ℝ) < A^24 + 1 := Nat.ceil_lt_add_one (by positivity)
  have hk2 : (K:ℝ)+2 ≤ A^25 := by
    rw [pow_succ]; nlinarith [show (1:ℝ) ≤ A^24 by exact one_le_pow₀ (by linarith) ]
  have hk0 : (0:ℝ) < K := lt_of_lt_of_le (by positivity) hk
  have hlk := Real.log_le_log hk0 (show (K:ℝ) ≤ A^25 by linarith)
  rw [Real.log_pow] at hlk
  have hln := Real.log_le_log (show (0:ℝ) < N by exact_mod_cast NeZero.pos N) hN
  let U := A^26
  have hU : ((K+2:ℕ):ℝ)*N ≤ U := by dsimp [U]; push_cast; rw [pow_succ A 25]; gcongr
  have h : (1-s.re)*Real.log U ≤ 1 := by
    apply le_trans (mul_nonpos_of_nonpos_of_nonneg (by linarith) (Real.log_nonneg (one_le_pow₀ (by linarith)))) (by norm_num)
  let f := fun k => ‖characterLBlock χ k s‖
  have hfirst := first χ hn1 (show (N:ℝ) ≤ U by apply le_trans _ hU; push_cast; nlinarith [Nat.cast_nonneg (α:=ℝ) K, Nat.cast_nonneg (α:=ℝ) N, mul_nonneg (Nat.cast_nonneg (α:=ℝ) K) (Nat.cast_nonneg (α:=ℝ) N)]) h
  have hmid : ∑ i ∈ Finset.range K, f (i+1) ≤ Real.exp 1 * (1+Real.log K) := by
    calc
      _ ≤ ∑ i ∈ Finset.range K, Real.exp 1 * (((i+1:ℕ):ℝ)⁻¹) := by
        apply Finset.sum_le_sum; intro i hi
        simpa only [div_eq_mul_inv, Nat.cast_add, Nat.cast_one] using middle χ i (s:=s) (U:=U) (by apply le_trans _ hU; gcongr; exact (Finset.mem_range.mp hi).le) h
      _ = Real.exp 1 * (harmonic K : ℝ) := by simp [harmonic, Finset.mul_sum]
      _ ≤ _ := by gcongr; exact harmonic_le_one_add_log K
  have hK : ((4+|t|)*(N:ℝ)^2)^8 ≤ K := by
    apply le_trans _ hk
    calc
      _ ≤ (A*A^2)^8 := by gcongr; exact Q_ge t
      _ = _ := by ring
  obtain ⟨he,hf⟩ := LFunction_eq_characterLBlockSeries_of_one_lt_re χ hn1 hr
  rw [he,characterLBlockSeries,← hf.sum_add_tsum_nat_add (K+1)]
  apply (norm_add_le _ _).trans
  have hpre := norm_sum_le (Finset.range (K+1)) (fun i => characterLBlock χ i s)
  change _ ≤ ∑ i ∈ Finset.range (K+1), f i at hpre
  rw [Finset.sum_range_succ' f K] at hpre; change f 0 ≤ _ at hfirst
  have H := ((summable_nat_add_iff (K+1)).mpr hf).tendsto_sum_tsum_nat.norm
  have ht := le_of_tendsto H (Eventually.of_forall (fun m => by simpa only [Nat.add_comm _ (K+1)] using sum_tail_bound t χ hs hr K m hK))
  change _ ≤ 2*C*Real.log A + _
  have HC : Real.exp 1 * (2*(1+Real.log N)+(1+Real.log K)) + 2*tailC ≤ 2*C*Real.log A := by
    norm_num only [Nat.cast_ofNat] at hlk
    unfold C; have he := Real.exp_pos 1
    nlinarith [mul_le_mul_of_nonneg_left hln he.le, mul_le_mul_of_nonneg_left hlk he.le,
      mul_le_mul_of_nonneg_left ha (abs_nonneg tailC), le_abs_self tailC,
      mul_le_mul_of_nonneg_left ha he.le]
  linarith

theorem doubled_bound {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hn : χ ≠ 1)
    {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) (ht : t ≠ 0) :
    ‖(χ^2).LFunction (1+x+2*I*t)‖ ≤ 2*C*Real.log (Q N (2*t)) + 1/|t| := by
  let s : ℂ := 1+x+2*I*t
  have hN : N ≠ 1 := by rintro rfl; exact hn (Subsingleton.elim _ _)
  have hr : 1 < s.re := by dsimp [s]; norm_num [add_re,mul_re,mul_im]; linarith
  have hs : s ∈ ball (2+I*(2*t:ℝ):ℂ) (7/4:ℝ) := by
    rw [mem_ball,dist_eq_norm]; have eqn : s-(2+I*(2*t:ℝ)) = ((x-1:ℝ):ℂ) := by dsimp [s]; push_cast; ring
    rw [eqn,norm_real,Real.norm_eq_abs,abs_of_nonpos (by linarith)]; linarith
  apply (right_bound (2*t) (χ^2) hN hs hr).trans; apply add_le_add le_rfl
  have hb := abs_im_le_norm (-s+1)
  have hi : (-s+1).im = -(2*t) := by dsimp [s]; norm_num [add_im,mul_im,mul_re]
  rw [hi, abs_neg,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)] at hb
  have htp := abs_pos.mpr ht
  exact (div_le_div_iff₀ (by linarith : 0 < ‖-s+1‖) htp).mpr (by linarith)

theorem strip_bounds {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hn : χ ≠ 1)
    (s : ℂ) (hs : |s.re-1| ≤ 1/(52*Real.log (Q N s.im))) :
    ‖χ.LFunction s‖ ≤ C*Real.log (Q N s.im) ∧
    ‖deriv χ.LFunction s‖ ≤ 52*C*(Real.log (Q N s.im))^2 := by
  have e : dist s (1+I*s.im) = |s.re-1| := by
    rw [dist_eq_norm]; have hh : s-(1+I*s.im) = ((s.re-1:ℝ):ℂ) := by apply Complex.ext <;> simp [mul_re,mul_im]
    rw [hh,norm_real,Real.norm_eq_abs]
  rw [← e] at hs
  refine ⟨disk_bound s.im χ hn (hs.trans ?_),deriv_bound s.im χ hn hs⟩
  have := logQ_ge (N:=N) s.im
  apply one_div_le_one_div_of_le (by positivity); linarith

end
end BVHeight

end

section
namespace BVShort
open Complex Metric DirichletCharacter BVHeight
private lemma Cnonneg : 0 ≤ C := by unfold C; positivity

theorem uniform_box {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hn : χ ≠ 1)
    {x r T L D M : ℝ} (hx : 0 < x) (hx1 : x ≤ 1/4) (hr : 0 < r) (hr1 : r ≤ 1/2)
    (_hL : 0 < L) (hD : 0 < D) (hM : 2 ≤ M) (hDM : D ≤ M)
    (hlog : ∀ t : ℝ, |t| ≤ 2*|T|+2 → Real.log (Q q t) ≤ L)
    (hnarrow : 3*x ≤ 1/(52*L)) (hsmall : 16*M^8*x < 1)
    (hder : 52*C*L^2 ≤ D) (hdbl : 2*C*L+1/r ≤ M)
    (hp : ‖LFunctionTrivChar q (1+x)‖ ≤ M/x)
    (hreal : χ^2 = 1 → 2*D*(x+r) ≤ ‖χ.LFunction 1‖)
    {s : ℂ} (hs : |s.re-1| ≤ x/2) (ht : |s.im| ≤ T) :
    χ.LFunction s ≠ 0 ∧ ‖deriv χ.LFunction s / χ.LFunction s‖ ≤ 2/x := by
  have hT := (abs_nonneg _).trans ht
  have H {z : ℂ} (a : |z.re-1| ≤ 3*x) (b : |z.im| ≤ 2*|T|+2) :=
    strip_bounds χ hn z (a.trans (hnarrow.trans (one_div_le_one_div_of_le
      (by have := logQ_ge (N:=q) z.im; positivity) (mul_le_mul_of_nonneg_left (hlog _ b) (by norm_num)))))
  have der {z : ℂ} (a : |z.re-1| ≤ 3*x) (b : |z.im| ≤ 2*|T|+2) : ‖deriv χ.LFunction z‖ ≤ D := by
    apply (H a b).2.trans; apply le_trans _ hder; gcongr; exact mul_nonneg (by norm_num) Cnonneg; exact (logQ_ge (N:=q) z.im).trans' (by norm_num); exact hlog _ b
  have b0 : |s.im| ≤ 2*|T|+2 := by rw [abs_of_nonneg hT]; linarith
  have ds := der (by linarith : |s.re-1| ≤ 3*x) b0
  by_cases low : χ^2 = 1 ∧ |s.im| ≤ r
  · let K := {z : ℂ | |z.re-1| ≤ x ∧ |z.im| ≤ r}
    have cv : Convex ℝ K := by
      intro a ha b hb u v hu hv huv
      obtain ⟨ha,ha'⟩ := ha; obtain ⟨hb,hb'⟩ := hb
      change |(u • a + v • b).re-1| ≤ x ∧ |(u • a + v • b).im| ≤ r
      simp only [add_re,add_im,smul_re,smul_im,smul_eq_mul]
      rw [show u*a.re+v*b.re-1=u*(a.re-1)+v*(b.re-1) by linear_combination huv]
      constructor <;> apply (abs_add_le ..).trans <;> rw [abs_mul, abs_mul,abs_of_nonneg hu,abs_of_nonneg hv]
      · calc _ ≤ u*x+v*x := by gcongr
             _ = x := by linear_combination x*huv
      · calc _ ≤ u*r+v*r := by gcongr
             _ = r := by linear_combination r*huv
    have dK : ∀ z ∈ K, ‖deriv χ.LFunction z‖ ≤ D := fun z hz => der (hz.1.trans (by linarith)) (hz.2.trans (by linarith [abs_nonneg T]))
    have oneK : (1:ℂ) ∈ K := by change |(1:ℂ).re-1| ≤ x ∧ |(1:ℂ).im| ≤ r; simpa using And.intro hx.le hr.le
    have sk : s ∈ K := ⟨hs.trans (by linarith),low.2⟩
    have lip := Convex.norm_image_sub_le_of_norm_deriv_le (fun z _ => (differentiable_LFunction hn z)) dK cv sk oneK
    have d : ‖1-s‖ ≤ x+r := by
      apply (norm_le_abs_re_add_abs_im _).trans
      simp only [sub_re,one_re,sub_im,one_im,zero_sub,abs_neg,abs_sub_comm 1 s.re]; linarith [low.2]
    have lo : D*(x+r) ≤ ‖χ.LFunction s‖ := by linarith [norm_sub_norm_le (χ.LFunction 1) (χ.LFunction s),mul_le_mul_of_nonneg_left d hD.le,hreal low.1]
    have pos : 0 < ‖χ.LFunction s‖ := lt_of_lt_of_le (by positivity) lo
    refine ⟨norm_pos_iff.mp pos, ?_⟩
    rw [norm_div,div_le_div_iff₀ pos hx]; nlinarith [mul_le_mul_of_nonneg_right ds hx.le,mul_pos hD hr]
  · let c : ℂ := 1+x+I*s.im
    have cr : c.re = 1+x := by simp [c,mul_re]
    have ci : c.im = s.im := by simp [c,mul_im]
    have dd : ∀ z ∈ closedBall c (3*x/2), ‖deriv χ.LFunction z‖ ≤ M := by
      intro z hz; rw [mem_closedBall,dist_eq_norm] at hz
      have a := (abs_re_le_norm (z-c)).trans hz; have b := (abs_im_le_norm (z-c)).trans hz
      rw [sub_re,cr] at a; rw [sub_im,ci] at b
      apply (der _ _).trans hDM
      · rw [abs_le] at a ⊢; constructor <;> linarith [a.1,a.2]
      · have := abs_add_le (z.im-s.im) s.im; rw [sub_add_cancel] at this; linarith [le_abs_self T]
    have hz : s ∈ closedBall c (3*x/2) := by
      rw [mem_closedBall,dist_eq_norm]; apply (norm_le_abs_re_add_abs_im _).trans; rw [sub_re,sub_im,cr,ci,sub_self,abs_zero,add_zero,abs_le]; rw [abs_le] at hs; constructor <;> linarith [hs.1,hs.2]
    have dbl : ‖(χ^2).LFunction (1+x+2*I*s.im)‖ ≤ M := by
      by_cases sq : χ^2 = 1
      · have rr : r < |s.im| := lt_of_not_ge (fun h => low ⟨sq,h⟩)
        apply (doubled_bound s.im χ hn hx (by linarith) (abs_pos.mp (hr.trans rr))).trans
        apply le_trans _ hdbl; apply add_le_add
        · exact mul_le_mul_of_nonneg_left (hlog _ (by rw [abs_mul]; norm_num; linarith [le_abs_self T])) (by positivity [Cnonneg])
        · exact one_div_le_one_div_of_le hr rr.le
      · let z : ℂ := 1+x+2*I*s.im
        have zr : z.re = 1+x := by simp [z,mul_re,mul_im]
        have zi : z.im = 2*s.im := by simp [z,mul_re,mul_im]
        have B := hlog z.im (by rw [zi,abs_mul]; norm_num; linarith [le_abs_self T])
        have V := (strip_bounds (χ^2) sq z (by rw [zr,add_sub_cancel_left,abs_of_pos hx]; apply le_trans (by linarith : x ≤ 1/(52*L)); apply one_div_le_one_div_of_le (by have := logQ_ge (N:=q) z.im; positivity); gcongr)).1
        apply V.trans; nlinarith [mul_le_mul_of_nonneg_left B Cnonneg, mul_nonneg Cnonneg _hL.le,one_div_pos.mpr hr]
    obtain ⟨a,b⟩ := local_disk χ hn hx (by linarith) hsmall hp dbl dd hz
    exact ⟨norm_pos_iff.mp (lt_trans (by positivity) a), b⟩
end BVShort

end

section
open Filter Real Complex Metric DirichletCharacter BVHeight
open scoped Topology
namespace BVShort
private noncomputable def E (t a : ℝ) := Real.exp (a*t)
private lemma Ep (t a : ℝ) : 0 < E t a := exp_pos _
private lemma Ea (t a b : ℝ) : E t (a+b) = E t a * E t b := by simp [E, add_mul,Real.exp_add]
private lemma En (t a : ℝ) : E t (-a) = (E t a)⁻¹ := by simp [E,Real.exp_neg]
private lemma Epow (t a : ℝ) (n : ℕ) : E t a ^ n = E t (n*a) := by simp [E,mul_assoc,Real.exp_nat_mul]
private lemma Edom (a b K k : ℝ) (hab : a < b) (hk : 0 < k) :
    ∀ᶠ t : ℝ in atTop, K*E t a < k*E t b := by
  have hh := (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (sub_pos.mpr hab))).eventually (eventually_gt_atTop (K/k))
  filter_upwards [hh] with t ht
  change K/k < E t (b-a) at ht
  have h := mul_lt_mul_of_pos_right ((div_lt_iff₀ hk).mp ht) (Ep t a)
  rwa [mul_right_comm,←Ea,sub_add_cancel,mul_comm (E t b)] at h
private lemma ln_budget (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    ∀ᶠ t : ℝ in atTop, ∀ (q : ℕ), (q:ℝ) ≤ E t B → ∀ y : ℝ,
    |y| ≤ 2*|E t A|+2 → Real.log (Q q y) ≤ E t (1/256) := by
  have hh := (isLittleO_pow_exp_pos_mul_atTop 1 (by norm_num : (0:ℝ)<1/256)).def (show 0 < 1/(A+B+8) by positivity)
  filter_upwards [hh,eventually_ge_atTop (1:ℝ)] with t ht ht1
  have ha : 1 ≤ E t A := Real.one_le_exp (by positivity)
  have hb : 1 ≤ E t B := Real.one_le_exp (by positivity)
  intro q hq y hy
  rw [abs_of_pos (Ep ..)] at hy
  have H : Q q y ≤ 8 * (E t A*E t B) := by unfold Q; nlinarith [mul_le_mul_of_nonneg_right hq (by positivity : 0 ≤ 2+|y|),mul_le_mul_of_nonneg_right hy (Ep t B).le,mul_le_mul_of_nonneg_right ha (Ep t B).le]
  have H' := Real.log_le_log (by unfold Q; positivity) H
  rw [← Ea, Real.log_mul (by norm_num) (Ep ..).ne', E,Real.log_exp] at H'
  simp only [pow_one] at ht
  change ‖t‖ ≤ (1/(A+B+8))*‖E t (1/256)‖ at ht
  rw [Real.norm_eq_abs,abs_of_pos (by linarith),Real.norm_eq_abs,abs_of_pos (Ep ..),one_div_mul_eq_div] at ht
  have h := (le_div_iff₀ (by positivity)).mp ht
  linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<8)]
private lemma Ep0 (t : ℝ) : E t 0 = 1 := by simp [E]
open BombieriVinogradov.SiegelWalfisz in
private theorem scaled (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    ∀ᶠ t : ℝ in atTop, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → χ.IsPrimitive →
      (q:ℝ) ≤ E t B → ∀ s : ℂ, |s.re-1| ≤ E t (-1/2) → |s.im| ≤ E t A →
      χ.LFunction s ≠ 0 ∧ ‖deriv χ.LFunction s / χ.LFunction s‖ ≤ E t (1/2) := by
  have he : 0 < 1/(128*B) := by positivity
  obtain ⟨k,hk,hS⟩ := siegelLowerBound _ he
  have p : Tendsto (fun t => 1+E t (-1/3)) atTop (𝓝[>] 1) := by
    apply tendsto_nhdsWithin_iff.mpr; constructor
    · simpa [E] using (Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by norm_num : (-1/3:ℝ)<0))).const_add 1
    · exact Eventually.of_forall (fun t => show 1 < 1+E t (-1/3) by linarith [Ep t (-1/3)])
  filter_upwards [p.eventually principal_uniform,ln_budget A B hA hB,
    Edom (-1/3) 0 1 (1/4) (by norm_num) (by norm_num), Edom (-1/32) 0 1 (1/2) (by norm_num) (by norm_num),
    Edom 0 (1/28) 2 1 (by norm_num) (by norm_num), Edom (1/64) (1/28) 1 1 (by norm_num) (by norm_num),
    Edom (-1/3+1/256) 0 156 1 (by norm_num) (by norm_num),
    Edom (8*(1/28)-1/3) 0 16 1 (by norm_num) (by norm_num),
    Edom (2*(1/256)) (1/64) (52*C) 1 (by norm_num) (by norm_num),
    Edom (1/256) (1/28) (2*C) (1/2) (by norm_num) (by norm_num),
    Edom (1/32) (1/28) 1 (1/2) (by norm_num) (by norm_num),
    Edom (1/64-1/3) (-1/128) 2 (k/2) (by norm_num) (by positivity),
    Edom (1/64-1/32) (-1/128) 2 (k/2) (by norm_num) (by positivity),
    Edom (-1/2) (-1/3) 2 1 (by norm_num) (by norm_num), Edom (1/3) (1/2) 2 1 (by norm_num) (by norm_num)] with t hp hlog hx hr hM hDM hna hsm hd hdb1 hdb2 hs1 hs2 hw hfin
  simp only [Ep0,one_mul,mul_one] at *
  intro q _ χ hn hpr hq s hs ht
  have IX (a : ℝ) : 1 / E t (-a) = E t a := by rw [En,one_div,inv_inv]
  obtain ⟨a,b⟩ := uniform_box χ hn (x:=E t (-1/3)) (r:=E t (-1/32)) (T:=E t A) (L:=E t (1/256)) (D:=E t (1/64)) (M:=E t (1/28)) (Ep ..) hx.le (Ep ..) hr.le (Ep ..) (Ep ..) hM.le hDM.le (hlog _ hq) (by
    apply (le_div_iff₀ (mul_pos (by norm_num) (Ep ..))).mpr; rw [Ea] at hna; linarith) (by
    rw [Epow]; norm_num only [Nat.cast_ofNat]; rw [sub_eq_add_neg,Ea] at hsm; linarith) (by simpa only [Epow,Nat.cast_ofNat] using hd.le) (by
    rw [show (-1/32:ℝ) = -(1/32) by ring,IX]; linarith) (by
    have H := hp q; rw [add_sub_cancel_left] at H; push_cast at H; exact H.trans (div_le_div_of_nonneg_right hM.le (Ep ..).le)) (by
    intro sq; have h := hS q χ (three_le_level_of_ne_one χ hn) hpr sq hn
    have pow := Real.rpow_le_rpow_of_nonpos (show 0 < (q:ℝ) by exact_mod_cast NeZero.pos q) hq (neg_nonpos.mpr he.le)
    have e : (E t B)^(-(1/(128*B))) = E t (-1/128) := by unfold E; rw [← Real.exp_mul]; congr 1; field_simp
    rw [e] at pow
    have z := le_trans (mul_le_mul_of_nonneg_left pow hk.le) (h.trans (re_le_norm _))
    rw [sub_eq_add_neg,Ea] at hs1 hs2
    norm_num only [neg_div] at *; nlinarith) (by linarith) ht
  refine ⟨a,b.trans ?_⟩
  rw [div_eq_mul_one_div, show (-1/3:ℝ) = -(1/3) by ring, IX]; exact hfin.le

theorem log_strip (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    ∀ᶠ X : ℝ in atTop, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → χ.IsPrimitive →
      (q:ℝ) ≤ (Real.log X)^B → ∀ s : ℂ, |s.re-1| ≤ 1/Real.sqrt (Real.log X) → |s.im| ≤ (Real.log X)^A →
      χ.LFunction s ≠ 0 ∧ ‖deriv χ.LFunction s / χ.LFunction s‖ ≤ Real.sqrt (Real.log X) := by
  filter_upwards [(Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually (scaled A B hA hB),eventually_gt_atTop (1:ℝ)] with X hx hX
  have e (a : ℝ) : E (Real.log (Real.log X)) a = (Real.log X)^a := by rw [Real.rpow_def_of_pos (Real.log_pos hX),mul_comm]; rfl
  change ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), _ at hx
  simp only [Function.comp_apply, e] at hx
  rw [Real.sqrt_eq_rpow]; have en : (-1/2:ℝ) = -(1/2) := by ring
  simpa only [en,Real.rpow_neg (Real.log_pos hX).le,one_div] using hx
end BVShort

end

section

open Complex Set Filter DirichletCharacter
open BombieriVinogradov.SiegelWalfisz
namespace BVRect
lemma shift {n q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hn : 2 < n) (hχ : χ ≠ 1)
    {a b T M : ℝ} (ha : 0 < a) (hab : a ≤ b) (hT : 0 < T) (hM : 0 ≤ M)
    (H : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → |s.im| ≤ T → χ.LFunction s ≠ 0 ∧ ‖deriv χ.LFunction s / χ.LFunction s‖ ≤ M) :
    ‖explicitFormulaVerticalIntegral χ n b T‖ ≤
    2*T*(M*(n:ℝ)^a/a) + 2*(b-a)*(M*(n:ℝ)^b/T) := by
  let f := explicitFormulaIntegrand χ n
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hn0 : (n:ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have ht : -T ≤ T := by linarith
  have hd := differentiable_LFunction hχ
  have E : RectangleIntegral f (a + (-T:ℝ)*I) (b + T*I) = 0 := by
    apply HolomorphicOn.vanishesOnRectangle (U := Rectangle _ _) _ (Subset.rfl)
    intro s hs
    have hs' : s.re ∈ Icc a b ∧ s.im ∈ Icc (-T) T := by
      simp [Rectangle,uIcc_of_le,hab,ht] at hs
      exact hs
    have nz := (H s hs'.1.1 hs'.1.2 (abs_le.mpr hs'.2)).1
    have sz : s ≠ 0 := fun e => by simp [e] at hs'; linarith [hs'.1.1]
    apply ((hd.deriv.differentiableAt.div (hd s) nz).differentiableWithinAt.mul _)
    apply DifferentiableWithinAt.neg
    change DifferentiableWithinAt ℂ (perronKernelIntegrand (n:ℝ)) _ s
    exact (holomorphicOn_perronKernelIntegrand (show 0 < (n:ℝ) by positivity) s
      (ha.trans_le hs'.1.1)).mono (by intro z hz; simp [Rectangle,uIcc_of_le,hab,ht] at hz; exact ha.trans_le hz.1.1)
  simp [RectangleIntegral] at E
  have e : VIntegral f b (-T) T = VIntegral f a (-T) T + HIntegral f a b T - HIntegral f a b (-T) := by linear_combination E
  have normF (s : ℂ) (h1 : a ≤ s.re) (h2 : s.re ≤ b) (h3 : |s.im| ≤ T) :
      ‖f s‖ ≤ M*(n:ℝ)^s.re/‖s‖ := by
    simp only [f, explicitFormulaIntegrand,logDeriv_apply,norm_mul,norm_neg,norm_div,
      Complex.norm_natCast_cpow_of_re_ne_zero n (ne_of_gt (ha.trans_le h1)),mul_div_assoc]
    gcongr
    simpa only [norm_div] using (H s h1 h2 h3).2
  have hor (t : ℝ) (ht' : |t| = T) : ‖HIntegral f a b t‖ ≤ (M*(n:ℝ)^b/T)*(b-a) := by
    apply (intervalIntegral.norm_integral_le_of_norm_le_const _).trans_eq
    · rw [abs_of_nonneg (sub_nonneg.mpr hab)]
    · intro u hu
      rw [uIoc_of_le hab] at hu
      let z : ℂ := u+t*I
      have zr : z.re = u := by simp [z]
      have zi : z.im = t := by simp [z]
      have hz := normF z (zr ▸ hu.1.le) (zr ▸ hu.2) (by rw [zi,ht'])
      have hden : T ≤ ‖z‖ := by simpa [zi,ht'] using abs_im_le_norm z
      apply hz.trans
      rw [zr]; gcongr; exact hu.2
  have ver : ‖VIntegral f a (-T) T‖ ≤ (M*(n:ℝ)^a/a)*(T- -T) := by
    rw [VIntegral,norm_smul,norm_I,one_mul]
    apply (intervalIntegral.norm_integral_le_of_norm_le_const _).trans_eq
    · rw [abs_of_nonneg (sub_nonneg.mpr ht)]
    · intro t ht'
      rw [uIoc_of_le ht] at ht'
      let z : ℂ := a+t*I
      have zr : z.re = a := by simp [z]
      have hz := normF z zr.ge (zr.trans_le hab) (by simpa [z] using abs_le.mpr ⟨ht'.1.le,ht'.2⟩)
      exact hz.trans (by rw [zr]; gcongr; simpa [zr] using re_le_norm z)
  change ‖(1/(2*Real.pi*I):ℂ) • VIntegral f b (-T) T‖ ≤ _
  have hpi : ‖(1/(2*Real.pi*I):ℂ)‖ ≤ 1 := by
    simp [abs_of_pos Real.pi_pos]; apply mul_le_one₀ _ (by positivity) (by norm_num); exact inv_le_one_of_one_le₀ (by linarith [Real.pi_gt_three])
  rw [norm_smul,e]
  apply (mul_le_of_le_one_left (norm_nonneg _) hpi).trans
  calc
    _ ≤ (‖VIntegral f a (-T) T‖ + ‖HIntegral f a b T‖) + ‖HIntegral f a b (-T)‖ :=
      (norm_sub_le ..).trans (by gcongr; exact norm_add_le ..)
    _ ≤ _ := by linarith [ver,hor T (abs_of_pos hT),hor (-T) (by simp [abs_of_pos hT])]
end BVRect
open Filter Real Complex DirichletCharacter
open BombieriVinogradov.SiegelWalfisz
namespace BVRect
lemma power_absorb (k : ℝ) : ∀ᶠ x : ℝ in atTop, x^k ≤ Real.exp x := by
  filter_upwards [(tendsto_exp_div_rpow_atTop k).eventually_ge_atTop 1, eventually_gt_atTop (0:ℝ)] with x hx hx0
  exact (one_mul _).symm.le.trans ((le_div_iff₀ (Real.rpow_pos_of_pos hx0 k)).mp hx)
lemma scalar (A : ℝ) (_hA : 0 < A) : ∀ᶠ n : ℕ in atTop,
    let L := Real.log n
    let a := 1-1/Real.sqrt L
    let T := L^(A+5)
    0 < a ∧ a ≤ optimizedPerronLine n ∧ 0 < T ∧ 0 ≤ L ∧
    2*T*(L*(n:ℝ)^a/a) ≤ 4*n/L^A ∧
    2*(optimizedPerronLine n-a)*(L*(n:ℝ)^(optimizedPerronLine n)/T) ≤ 4*Real.exp 1*n/L^A ∧
    (n:ℝ)*Real.log (2*(n:ℝ))^2/T ≤ 4*n/L^A ∧ L ≤ n/L^A := by
  have lim := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have slim := Real.tendsto_sqrt_atTop.comp lim
  filter_upwards [slim.eventually_ge_atTop 2, lim.eventually_ge_atTop 4,
    slim.eventually (power_absorb (2*(2*A+6))),lim.eventually (power_absorb (A+1)), eventually_gt_atTop 2] with n hs hL hpow hend hn
  let L := Real.log (n:ℝ)
  let r := Real.sqrt L
  change 2 ≤ r at hs
  change 4 ≤ L at hL
  have hL0 : 0 < L := by linarith
  have hr : 0 < r := by linarith
  have hrr : r^2 = L := Real.sq_sqrt hL0.le
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
  have ha : 1/2 ≤ 1-1/r := by apply sub_le_sub_left (show 1/r ≤ 1/2 by gcongr) 1 |>.trans' (by norm_num)
  have ha0 : 0 < 1-1/r := by linarith
  have hb := optimizedPerronLine_le_two hn
  have he : (n:ℝ)^(1-1/r) = n/Real.exp r := by
    rw [Real.rpow_def_of_pos hn0]; change Real.exp (L*(1-1/r)) = _
    have : L*(1-1/r)=L-r := by field_simp; nlinarith [hrr]
    rw [this,Real.exp_sub,Real.exp_log hn0]
  have p : L^(2*A+6) ≤ Real.exp r := by
    rw [← hrr, ← Real.rpow_natCast, ← Real.rpow_mul hr.le]; exact hpow
  let D := L^A
  have dpos : 0 < D := Real.rpow_pos_of_pos hL0 _
  have te : L^(A+5) = D*L^5 := by simp [D,Real.rpow_add hL0]
  have pe : D^2*L^6 ≤ Real.exp r := by
    convert p using 1
    rw [Real.rpow_add hL0, mul_comm 2 A,Real.rpow_mul hL0.le];simp [D]
  have l1 : 1 ≤ L := by linarith
  have l5 : L ≤ L^5 := by simpa using pow_le_pow_right₀ l1 (show 1 ≤ 5 by decide)
  have l25 : L^2 ≤ L^5 := pow_le_pow_right₀ l1 (by decide)
  have hl2 : Real.log (2*(n:ℝ))^2 ≤ 4*L^2 := by
    rw [Real.log_mul (by norm_num) hn0.ne']; change (Real.log 2+L)^2 ≤ _
    have log2 : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
    nlinarith [log2, Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2), sq_nonneg (L-Real.log 2),mul_nonneg (show 0 ≤ L-Real.log 2 by linarith [log2]) (show 0 ≤ 3*L+Real.log 2 by positivity)]
  dsimp only
  change 0 < 1-1/r ∧ _
  refine ⟨ha0, (show 1-1/r ≤ 1 by linarith [one_div_pos.mpr hr]).trans (optimizedPerronLine_gt_one hn).le, Real.rpow_pos_of_pos hL0 _,hL0.le,?_,?_,?_,?_⟩
  · change 2*L^(A+5)*(L*(n:ℝ)^(1-1/r)/(1-1/r)) ≤ 4*n/D
    rw [te,he]; apply (le_div_iff₀ dpos).mpr
    rw [mul_div_assoc', ← mul_div_right_comm, div_le_iff₀ ha0]
    field_simp [ne_of_gt (Real.exp_pos r)]
    nlinarith only [mul_le_mul_of_nonneg_right pe hr.le,mul_nonneg (sub_nonneg.mpr hs) (Real.exp_pos r).le]
  · change 2*(_-(1-1/r))*(L*_ / L^(A+5)) ≤ _ / D
    rw [te,rpow_optimizedPerronLine_eq hn]; field_simp
    nlinarith only [mul_le_mul_of_nonneg_right hb hr.le,hs,mul_le_mul_of_nonneg_left (show 1 ≤ L^4 from one_le_pow₀ l1) hr.le]
  · change (n:ℝ)*_ / L^(A+5) ≤ _ / D
    rw [te]; field_simp
    rw [mul_comm (n:ℝ) 2]; linarith
  · apply (le_div_iff₀ dpos).mpr
    change L^(A+1) ≤ Real.exp L at hend
    simpa [Real.rpow_add hL0,Real.exp_log hn0,D,mul_comm,L] using hend
end BVRect
open Filter Complex DirichletCharacter
open BombieriVinogradov.SiegelWalfisz
namespace BVRect

def Strip : Prop := ∀ A B : ℝ, 0 < A → 0 < B → ∀ᶠ n : ℕ in atTop,
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → χ ≠ 1 →
  (q:ℝ) ≤ (Real.log n)^B → ∀ s : ℂ, 1-1/Real.sqrt (Real.log n) ≤ s.re →
  s.re ≤ 1+1/Real.log n → |s.im| ≤ (Real.log n)^(A+5) →
  χ.LFunction s ≠ 0 ∧ ‖deriv χ.LFunction s / χ.LFunction s‖ ≤ Real.log n
open Finset in
lemma endpoint {n q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hn : 1 ≤ n) :
  ‖∑ k ∈ Icc 1 n, (ArithmeticFunction.vonMangoldt k:ℂ)*χ k‖ ≤
  ‖characterChebyshevHalfSum n χ‖ + Real.log n := by
  classical
  let f := twistedMangoldtSequence χ
  have e : Finset.Icc 1 n = insert n (Finset.Ico 1 n) := by ext k; simp; omega
  have eq : ∑ k ∈ Icc 1 n, (ArithmeticFunction.vonMangoldt k:ℂ)*χ k = characterChebyshevHalfSum n χ + (1/2:ℂ)*f n := by
    rw [e,sum_insert (by simp),characterChebyshevHalfSum]; simp only [f,twistedMangoldtSequence]; simp_rw [mul_comm (ArithmeticFunction.vonMangoldt _:ℂ)]; ring_nf; rfl
  rw [eq]; apply (norm_add_le ..).trans; gcongr
  rw [norm_mul]; apply (mul_le_of_le_one_left (norm_nonneg _) (by norm_num)).trans
  exact (norm_twistedMangoldtSequence_le_vonMangoldt χ n).trans ArithmeticFunction.vonMangoldt_le_log
open Finset in
lemma natural_hs (h : Strip) : ∀ B A : ℝ, 0 < B → 0 < A → ∃ K > (0:ℝ), ∀ᶠ n : ℕ in atTop,
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → χ ≠ 1 → (q:ℝ) ≤ (Real.log n)^B →
  ‖∑ k ∈ Icc 1 n, (ArithmeticFunction.vonMangoldt k:ℂ)*χ k‖ ≤ K*n/(Real.log n)^A := by
  intro B A hB hA
  obtain ⟨C,hC,P⟩ := exists_norm_explicitFormulaVerticalIntegral_sub_halfSum_le_optimized
  refine ⟨5+4*Real.exp 1+4*C,by positivity,?_⟩
  filter_upwards [scalar A hA,h A B hA hB,eventually_gt_atTop 2] with n S H hn
  obtain ⟨ha,hab,hT,hM,hleft,hhor,herr,hend⟩ := S
  intro q _ χ hp hχ hq
  have sh := shift χ hn hχ ha hab hT hM (H q χ hp hχ hq)
  have per := P q χ n hn _ hT
  have tri := norm_sub_le (explicitFormulaVerticalIntegral χ n (optimizedPerronLine n) ((Real.log n)^(A+5)))
    (explicitFormulaVerticalIntegral χ n (optimizedPerronLine n) ((Real.log n)^(A+5)) - characterChebyshevHalfSum n χ)
  rw [sub_sub_cancel] at tri
  have ep := endpoint χ (show 1 ≤ n by omega)
  linarith only [ep,tri,per,sh,hleft,hhor,hend,mul_le_mul_of_nonneg_left herr hC.le,
    show (5+4*Real.exp 1+4*C)*(n:ℝ)/(Real.log n)^A = 4*n/(Real.log n)^A + 4*Real.exp 1*n/(Real.log n)^A + C*(4*n/(Real.log n)^A) + n/(Real.log n)^A by ring]
end BVRect

end

section
open Filter in
theorem BVShort.strip : BVRect.Strip := by
  intro A B hA hB
  filter_upwards [tendsto_natCast_atTop_atTop.eventually (BVShort.log_strip (A+5) B (by linarith) hB),
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_gt_atTop (1:ℝ))] with n H hn
  intro q _ χ hp hc hq s hl hr ht
  change 1 < Real.log (n:ℝ) at hn
  have p : 0 < Real.sqrt (Real.log n) := Real.sqrt_pos.mpr (by linarith)
  have b : Real.sqrt (Real.log n) ≤ Real.log n := by by_contra! hh; nlinarith [Real.sq_sqrt (show 0 ≤ Real.log (n:ℝ) by linarith),mul_lt_mul_of_pos_right hh (by linarith : 0 < Real.sqrt (Real.log n)),mul_le_mul_of_nonneg_right hn.le p.le]
  obtain ⟨nz,v⟩ := H q χ hc hp hq s (abs_le.mpr ⟨by linarith,by linarith [one_div_le_one_div_of_le p b]⟩) ht
  exact ⟨nz,v.trans b⟩
open Filter Finset in
theorem BVShort.natural : ∀ B A : ℝ, 0 < B → 0 < A → ∃ K > (0:ℝ), ∀ᶠ n : ℕ in atTop,
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → χ ≠ 1 → (q:ℝ) ≤ (Real.log n)^B →
  ‖∑ k ∈ Icc 1 n, (ArithmeticFunction.vonMangoldt k:ℂ)*χ k‖ ≤ K*n/(Real.log n)^A := BVRect.natural_hs BVShort.strip

end

-- Adapted from openai/math 3344da59991ed94f9ba711217b29c1d760badfa6: ResidueSqrtSplit.
namespace BV391
lemma modulus_admissible_above_sqrt {A X t : ℝ} (hA : 0 < A) (hX : 3 ≤ Real.sqrt X)
    (hlog : 2*(2:ℝ)^A ≤ Real.log X) (ht : Real.sqrt X ≤ t) {q : ℕ}
    (hq : (q:ℝ) ≤ (Real.log X)^A) :
    (q:ℝ) ≤ (Real.log t)^(A+1) := by
  have hs : 0 < Real.sqrt X := by linarith
  have hx0 : 0 ≤ X := (Real.sqrt_pos.mp hs).le
  have ht3 : 3 ≤ t := hX.trans ht
  have hl : 0 < Real.log t := Real.log_pos (by linarith)
  have hcompare : Real.log X ≤ 2*Real.log t := by
    have h : Real.log (Real.sqrt X) ≤ Real.log t := Real.log_le_log hs ht
    rw [Real.log_sqrt hx0] at h
    linarith
  have hpow : (2:ℝ)^A ≤ Real.log t := by linarith
  have hL : 0 ≤ Real.log X := le_trans (by positivity) hlog
  calc
    _ ≤ (Real.log X)^A := hq
    _ ≤ (2*Real.log t)^A := Real.rpow_le_rpow hL hcompare hA.le
    _ = (2:ℝ)^A*(Real.log t)^A := Real.mul_rpow (by norm_num) hl.le
    _ ≤ Real.log t*(Real.log t)^A := mul_le_mul_of_nonneg_right hpow (by positivity)
    _ = (Real.log t)^(A+1) := by rw [Real.rpow_add hl,Real.rpow_one]; ring


lemma character_vonMangoldt_norm_le {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (n : ℕ) :
    ‖chi n*(ArithmeticFunction.vonMangoldt n:ℂ)‖ ≤ Real.log (n:ℝ) := by
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (ArithmeticFunction.vonMangoldt_nonneg (n := n))]
  calc
    _ ≤ ArithmeticFunction.vonMangoldt n := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (chi.norm_le_one n)
        (ArithmeticFunction.vonMangoldt_nonneg (n := n))
    _ ≤ _ := ArithmeticFunction.vonMangoldt_le_log
open Finset in
lemma small_sum {d : ℕ} [NeZero d] (χ : DirichletCharacter ℂ d) {y : ℕ} {X : ℝ}
    (hX : 1 ≤ X) (hy : (y:ℝ) ≤ Real.sqrt X) (hyX : (y:ℝ) ≤ X) :
    ‖∑ n ∈ Icc 1 y, (ArithmeticFunction.vonMangoldt n:ℂ) * χ n‖ ≤ Real.sqrt X * Real.log X := by
  calc
    _ ≤ ∑ n ∈ Icc 1 y, ‖(ArithmeticFunction.vonMangoldt n:ℂ) * χ n‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Icc 1 y, Real.log X := by
      apply sum_le_sum; intro n hn
      rw [mul_comm]; apply (character_vonMangoldt_norm_le χ n).trans
      apply Real.log_le_log (by exact_mod_cast (show 0 < n from (mem_Icc.mp hn).1))
      exact (Nat.cast_le.mpr (mem_Icc.mp hn).2).trans hyX
    _ ≤ _ := by simpa [Nat.card_Icc] using mul_le_mul_of_nonneg_right hy (Real.log_nonneg hX)
lemma high_sum {K M X t E : ℝ} (hK : 0 ≤ K) (hM : 0 < M) (hX : 3 ≤ Real.sqrt X)
    (ht : Real.sqrt X ≤ t) (htX : t ≤ X) (hE : E ≤ K*t/(Real.log t)^M) :
    E ≤ K*(2:ℝ)^M*X/(Real.log X)^M := by
  have hs : 0 < Real.sqrt X := by linarith
  have hx0 : 0 < X := Real.sqrt_pos.mp hs
  have hx3 : 3 ≤ X := by nlinarith [Real.sq_sqrt hx0.le]
  have ht3 : 3 ≤ t := hX.trans ht
  have ht0 : 0 < t := by linarith
  have hl1 : 1 ≤ Real.log t :=
    ((Real.lt_log_iff_exp_lt ht0).mpr (Real.exp_one_lt_three.trans_le ht3)).le
  have hl : 0 < Real.log t := by linarith
  have hL : 0 < Real.log X := Real.log_pos (by linarith)
  have hcompare : Real.log X ≤ 2*Real.log t := by
    have h : Real.log (Real.sqrt X) ≤ Real.log t := Real.log_le_log hs ht
    rw [Real.log_sqrt hx0.le] at h
    linarith
  have hp : (Real.log X)^M ≤ (2:ℝ)^M*(Real.log t)^M := by
    rw [← Real.mul_rpow (by norm_num : (0:ℝ)≤2) hl.le]
    exact Real.rpow_le_rpow hL.le hcompare hM.le
  apply hE.trans
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  calc
    _ ≤ K*t*((2:ℝ)^M*(Real.log t)^M) := mul_le_mul_of_nonneg_left hp (by positivity)
    _ = (K*2^M*(Real.log t)^M)*t := by ring
    _ ≤ (K*2^M*(Real.log t)^M)*X := mul_le_mul_of_nonneg_left htX (by positivity)
    _ = _ := by ring
open Filter
open scoped Topology
theorem maximal {I : ℕ → Type*} {F : (d : ℕ) → I d → ℕ → ℝ} {A B K T : ℝ} (hA : 0 < A) (hB : 0 < B) (hK : 0 < K)
  (lo : ∀ x y d : ℕ, y ≤ x → (y:ℝ) ≤ Real.sqrt x → 1 ≤ d → ∀ i, F d i y ≤ Real.sqrt x * Real.log x)
  (hi : ∀ y d : ℕ, T ≤ y → 1 ≤ d → (d:ℝ) ≤ (Real.log y)^(B+1) → ∀ i, F d i y ≤ K*y/(Real.log y)^A) :
  ∃ C > (0:ℝ), ∀ᶠ x : ℕ in atTop, ∀ d : ℕ, 1 ≤ d → (d:ℝ) ≤ (Real.log x)^B → ∀ i, ∀ y ≤ x,
    F d i y ≤ C*x/(Real.log x)^A := by
  let C := max 1 (K*(2:ℝ)^A)
  refine ⟨C, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  have hh := Real.tendsto_sqrt_atTop.eventually (eventually_ge_atTop (max 3 T))
  have hl := Real.tendsto_log_atTop.eventually (eventually_ge_atTop (2*(2:ℝ)^B))
  filter_upwards [tendsto_natCast_atTop_atTop.eventually hh,tendsto_natCast_atTop_atTop.eventually hl,
    tendsto_natCast_atTop_atTop.eventually (E6BVAux.RealAnalysis.eventually_log_rpow_le_rpow (A+1) (by norm_num : (0:ℝ) < 1/2))] with x hx hlog hsmall
  intro d hd hdx i y hy
  rw [← Real.sqrt_eq_rpow] at hsmall
  have h3 := (le_max_left 3 T).trans hx
  have hL : 0 < Real.log x := lt_of_lt_of_le (by positivity : 0 < 2*(2:ℝ)^B) hlog
  have hxy : (y:ℝ) ≤ x := by exact_mod_cast hy
  by_cases h : (y:ℝ) ≤ Real.sqrt x
  · apply (lo x y d hy h hd i).trans
    calc
      _ ≤ ((x:ℝ)/(Real.log x)^(A+1))*Real.log x := by
        apply mul_le_mul_of_nonneg_right _ hL.le
        apply (le_div_iff₀ (Real.rpow_pos_of_pos hL _)).mpr
        exact (mul_le_mul_of_nonneg_left hsmall (Real.sqrt_nonneg _)).trans_eq (Real.mul_self_sqrt (by positivity))
      _ = (x:ℝ)/(Real.log x)^A := by rw [Real.rpow_add hL,Real.rpow_one]; field_simp
      _ ≤ _ := by gcongr; exact le_mul_of_one_le_left (by positivity) (le_max_left _ _)
  · have ht := le_of_not_ge h
    have hq := modulus_admissible_above_sqrt hB h3 hlog ht hdx
    exact (high_sum hK.le hA h3 ht hxy (hi y d (((le_max_right 3 T).trans hx).trans ht) hd hq i)).trans
      (by gcongr; exact le_max_right _ _)
open Finset in
lemma natural_adapter (hs : ∀ B A : ℝ, 0 < B → 0 < A → ∃ K > (0:ℝ), ∀ᶠ X : ℕ in atTop, ∀ (d : ℕ) [NeZero d] (χ : DirichletCharacter ℂ d), χ.IsPrimitive → χ ≠ 1 → (d:ℝ) ≤ (Real.log X)^B →
  ‖∑ n ∈ Icc 1 X, (ArithmeticFunction.vonMangoldt n:ℂ)*χ n‖ ≤ K*X/(Real.log X)^A) :
  ∀ A B : ℝ, 0 < A → 0 < B → ∃ C > (0:ℝ), ∀ᶠ x : ℕ in atTop, ∀ d : ℕ, 1 ≤ d → (d:ℝ) ≤ (Real.log x)^B → ∀ χ : DirichletCharacter ℂ d, χ.IsPrimitive → χ ≠ 1 → ∀ y ≤ x,
  ‖∑ n ∈ Icc 1 y, (ArithmeticFunction.vonMangoldt n:ℂ) * χ n‖ ≤ C*x/(Real.log x)^A := by
  intro A B hA hB
  obtain ⟨K,hK,h⟩ := hs (B+1) A (by linarith) hA
  obtain ⟨T,hT⟩ := eventually_atTop.mp h
  let F := fun (d : ℕ) (i : {χ : DirichletCharacter ℂ d // χ.IsPrimitive ∧ χ ≠ 1}) (y : ℕ) => ‖∑ n ∈ Icc 1 y, (ArithmeticFunction.vonMangoldt n:ℂ)*i.val n‖
  obtain ⟨C,hC,hmax⟩ := maximal (F:=F) (T:=(T:ℝ)) hA hB hK (by
    intro x y d hy hs hd i
    letI : NeZero d := ⟨by omega⟩
    by_cases hx : x=0
    · have : y=0 := by omega
      simp [F,hx,this]
    exact small_sum i.val (by exact_mod_cast (show 1 ≤ x by omega)) hs (by exact_mod_cast hy)) (by
    intro y d hy hd hq i
    letI : NeZero d := ⟨by omega⟩
    exact hT y (by exact_mod_cast hy) d i.val i.property.1 i.property.2 hq)
  refine ⟨C,hC,?_⟩
  filter_upwards [hmax] with x hx
  intro d hd hq χ hp hχ y hy
  exact hx d hd hq ⟨χ,hp,hχ⟩ y hy
end BV391


theorem OMA.solution : OMA.R_Erdos6_erdos_6_variants_decreasing_R1_H1_R1_H2_R2.H1 := by
  exact BV391.natural_adapter BVShort.natural
