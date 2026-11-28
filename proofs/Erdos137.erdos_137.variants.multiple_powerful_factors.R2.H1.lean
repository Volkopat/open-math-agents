import OMAReductions.R_Erdos137_erdos_137_variants_multiple_powerful_factors_R2
import Mathlib

/-!
# Bounded polynomial height in Erdős problem 137

The quantitative prime number theorem and its supporting lemmas below are adapted from
AlexKontorovich/PrimeNumberTheoremAnd, revision 55270df80721, under Apache License 2.0.
The individual components are identified by their original names. The adaptation uses
the pinned Mathlib environment, expands local notation, and omits unused results.

For an endpoint between the cube of the block length and a fixed power of it, count
primes in a logarithmically short band immediately above the block length. Apply
integer divided differences separately to the reciprocal and squared reciprocal to
bound the two sets of exceptions. The cubic range uses a binomial coefficient and
a count of square divisors.

Copyright (c) 2024 Michael Stoll. All rights reserved.
Authors: Michael Stoll

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

/- Adapted from PrimeNumberTheoremAnd/Auxiliary.lean. -/
section
namespace Complex

lemma hasDerivAt_ofReal (x : ℝ) : HasDerivAt ofReal 1 x :=
  HasDerivAt.ofReal_comp <| hasDerivAt_id x

lemma deriv_ofReal (x : ℝ) : deriv ofReal x = 1 :=
  (hasDerivAt_ofReal x).deriv

lemma differentiableAt_ofReal (x : ℝ) : DifferentiableAt ℝ ofReal x :=
  (hasDerivAt_ofReal x).differentiableAt

end Complex

lemma DifferentiableAt.comp_ofReal {e : ℂ → ℂ} {z : ℝ} (hf : DifferentiableAt ℂ e z) :
    DifferentiableAt ℝ (fun x : ℝ ↦ e x) z :=
  hf.hasDerivAt.comp_ofReal.differentiableAt

lemma deriv.comp_ofReal {e : ℂ → ℂ} {z : ℝ} (hf : DifferentiableAt ℂ e z) :
    deriv (fun x : ℝ ↦ e x) z = deriv e z :=
  hf.hasDerivAt.comp_ofReal.deriv

lemma Differentiable.comp_ofReal {e : ℂ → ℂ} (h : Differentiable ℂ e) :
    Differentiable ℝ (fun x : ℝ ↦ e x) :=
  fun _ ↦ h.differentiableAt.comp_ofReal

lemma DifferentiableAt.ofReal_comp {z : ℝ} {f : ℝ → ℝ} (hf : DifferentiableAt ℝ f z) :
    DifferentiableAt ℝ (fun (y : ℝ) ↦ (f y : ℂ)) z :=
  hf.hasDerivAt.ofReal_comp.differentiableAt

lemma Differentiable.ofReal_comp {f : ℝ → ℝ} (hf : Differentiable ℝ f) :
    Differentiable ℝ (fun (y : ℝ) ↦ (f y : ℂ)) :=
  fun _ ↦ hf.differentiableAt.ofReal_comp

open Complex ContinuousLinearMap in
lemma HasDerivAt.of_hasDerivAt_ofReal_comp {z : ℝ} {f : ℝ → ℝ} {u : ℂ}
    (hf : HasDerivAt (fun y ↦ (f y : ℂ)) u z) :
    ∃ u' : ℝ, u = u' ∧ HasDerivAt f u' z := by
  lift u to ℝ
  · have H := (imCLM.hasFDerivAt.comp z hf.hasFDerivAt).hasDerivAt.deriv
    simp only [Function.comp_def, imCLM_apply, ofReal_im, deriv_const] at H
    rwa [eq_comm, comp_apply, imCLM_apply, toSpanSingleton_apply_one] at H
  refine ⟨u, rfl, ?_⟩
  convert! (reCLM.hasFDerivAt.comp z hf.hasFDerivAt).hasDerivAt
  rw [comp_apply, toSpanSingleton_apply_one, reCLM_apply, ofReal_re]

lemma DifferentiableAt.ofReal_comp_iff {z : ℝ} {f : ℝ → ℝ} :
    DifferentiableAt ℝ (fun (y : ℝ) ↦ (f y : ℂ)) z ↔ DifferentiableAt ℝ f z := by
  refine ⟨fun H ↦ ?_, ofReal_comp⟩
  obtain ⟨u, _, hu₂⟩ := H.hasDerivAt.of_hasDerivAt_ofReal_comp
  exact HasDerivAt.differentiableAt hu₂

lemma Differentiable.ofReal_comp_iff {f : ℝ → ℝ} :
    Differentiable ℝ (fun (y : ℝ) ↦ (f y : ℂ)) ↔ Differentiable ℝ f :=
  forall_congr' fun _ ↦ DifferentiableAt.ofReal_comp_iff

lemma deriv.ofReal_comp {z : ℝ} {f : ℝ → ℝ} :
    deriv (fun (y : ℝ) ↦ (f y : ℂ)) z = deriv f z := by
  by_cases hf : DifferentiableAt ℝ f z
  · exact hf.hasDerivAt.ofReal_comp.deriv
  · have hf' := mt DifferentiableAt.ofReal_comp_iff.mp hf
    rw [deriv_zero_of_not_differentiableAt hf, deriv_zero_of_not_differentiableAt hf',
      Complex.ofReal_zero]
end

/- Adapted from PrimeNumberTheoremAnd/MellinCalculus.lean. -/
section
open scoped ContDiff

theorem MeasureTheory.setIntegral_integral_swap {α : Type*} {β : Type*} {E : Type*}
    [MeasurableSpace α] [MeasurableSpace β] {μ : MeasureTheory.Measure α}
    {ν : MeasureTheory.Measure β} [NormedAddCommGroup E]
    [MeasureTheory.SigmaFinite ν] [NormedSpace ℝ E] [MeasureTheory.SigmaFinite μ]
    (f : α → β → E) {s : Set α} {t : Set β}
    (hf : IntegrableOn (f.uncurry) (s ×ˢ t) (μ.prod ν)) :
    (∫ (x : α) in s, ∫ (y : β) in t, f x y ∂ν ∂μ)
      = ∫ (y : β) in t, ∫ (x : α) in s, f x y ∂μ ∂ν := by
  apply integral_integral_swap
  convert hf.integrable
  exact Measure.prod_restrict s t

open Complex Topology Filter Real MeasureTheory Set

variable {𝕂 : Type*} [RCLike 𝕂]

lemma MeasureTheory.integral_comp_mul_right_I0i_haar
    (f : ℝ → 𝕂) {a : ℝ} (ha : 0 < a) :
    ∫ (y : ℝ) in Ioi 0, f (y * a) / y = ∫ (y : ℝ) in Ioi 0, f y / y := by
  have := integral_comp_mul_right_Ioi (fun y ↦ f y / y) 0 ha
  simp only [RCLike.ofReal_mul, zero_mul, eq_inv_smul_iff₀ (ne_of_gt ha)] at this
  rw [← integral_smul] at this
  rw [← this, setIntegral_congr_fun (by simp)]
  intro _ _
  simp only [RCLike.real_smul_eq_coe_mul]
  rw [mul_comm (a : 𝕂), div_mul, mul_div_assoc, div_self ?_, mul_one]
  exact (RCLike.ofReal_ne_zero).mpr <| ne_of_gt ha

lemma MeasureTheory.integral_comp_mul_right_I0i_haar_real
    (f : ℝ → ℝ) {a : ℝ} (ha : 0 < a) :
    ∫ (y : ℝ) in Ioi 0, f (y * a) / y = ∫ (y : ℝ) in Ioi 0, f y / y :=
  MeasureTheory.integral_comp_mul_right_I0i_haar f ha

lemma MeasureTheory.integral_comp_mul_left_I0i_haar
    (f : ℝ → 𝕂) {a : ℝ} (ha : 0 < a) :
    ∫ (y : ℝ) in Ioi 0, f (a * y) / y = ∫ (y : ℝ) in Ioi 0, f y / y := by
  convert integral_comp_mul_right_I0i_haar f ha using 5; ring

lemma MeasureTheory.integral_comp_rpow_I0i_haar_real (f : ℝ → ℝ) {p : ℝ} (hp : p ≠ 0) :
    ∫ (y : ℝ) in Ioi 0, |p| * f (y ^ p) / y = ∫ (y : ℝ) in Ioi 0, f y / y := by
  rw [← integral_comp_rpow_Ioi (fun y ↦ f y / y) hp, setIntegral_congr_fun (by simp)]
  intro y hy
  have ypos : 0 < y := mem_Ioi.mp hy
  simp only [rpow_sub_one ypos.ne', smul_eq_mul]
  field_simp

lemma MeasureTheory.integral_comp_inv_I0i_haar (f : ℝ → 𝕂) :
    ∫ (y : ℝ) in Ioi 0, f (1 / y) / y = ∫ (y : ℝ) in Ioi 0, f y / y := by
  have := integral_comp_rpow_Ioi (fun y ↦ f y / y) (p := -1) (by simp)
  rw [← this, setIntegral_congr_fun (by simp)]
  intro y hy
  have : (y : 𝕂) ≠ 0 := (RCLike.ofReal_ne_zero).mpr <| LT.lt.ne' hy
  simp only [abs_neg, abs_one, rpow_neg_one, map_inv₀, div_inv_eq_mul,
    RCLike.real_smul_eq_coe_mul, RCLike.algebraMap_eq_ofReal]
  ring_nf
  simp [field]

lemma MeasureTheory.integral_comp_div_I0i_haar
    (f : ℝ → 𝕂) {a : ℝ} (ha : 0 < a) :
    ∫ (y : ℝ) in Ioi 0, f (a / y) / y = ∫ (y : ℝ) in Ioi 0, f y / y := by
  calc
    _ = ∫ (y : ℝ) in Ioi 0, f (a * y) / y := ?_
    _ = _ := integral_comp_mul_left_I0i_haar f ha
  convert (integral_comp_inv_I0i_haar fun y ↦ f (a * (1 / y))).symm using 4
  · rw [mul_one_div]
  · rw [one_div_one_div]

theorem Complex.ofReal_rpow {x : ℝ} (h : x > 0) (y : ℝ) :
    (((x : ℝ) ^ (y : ℝ)) : ℝ) = (x : ℂ) ^ (y : ℂ) := by
  rw [rpow_def_of_pos h, ofReal_exp, ofReal_mul, Complex.ofReal_log h.le,
    Complex.cpow_def_of_ne_zero]
  simp only [ne_eq, ofReal_eq_zero, ne_of_gt h, not_false_eq_true]

@[simp]
lemma Function.support_abs {α : Type*} (f : α → 𝕂) :
    (fun x ↦ ‖f x‖).support = f.support := by
  simp only [support, ne_eq]; simp_rw [norm_ne_zero_iff]

@[simp]
lemma Function.support_ofReal {f : ℝ → ℝ} :
    (fun x ↦ ((f x) : ℂ)).support = f.support := by
  apply Function.support_comp_eq (g := ofReal); simp

lemma Function.support_mul_subset_of_subset {s : Set ℝ} {f g : ℝ → 𝕂}
    (fSupp : f.support ⊆ s) : (f * g).support ⊆ s := by
  simp_rw [support_mul', inter_subset, subset_union_of_subset_right fSupp]

lemma Function.support_of_along_fiber_subset_subset {α β M : Type*} [Zero M]
    {f : α × β → M} {s : Set α} {t : Set β}
    (hx : ∀ (y : β), (fun x ↦ f (x, y)).support ⊆ s)
    (hy : ∀ (x : α), (fun y ↦ f (x, y)).support ⊆ t) :
    f.support ⊆ s ×ˢ t := by
  intro ⟨x, y⟩ hxy
  constructor
  · exact hx y (by simp only [Function.mem_support, ne_eq] at hxy ⊢; exact hxy)
  · exact hy x (by simp only [Function.mem_support, ne_eq] at hxy ⊢; exact hxy)

lemma Function.support_deriv_subset_Icc {a b : ℝ} {f : ℝ → 𝕂}
    (fSupp : f.support ⊆ Set.Icc a b) :
    (deriv f).support ⊆ Set.Icc a b := by
    have := support_deriv_subset (f := fun x ↦ f x)
    dsimp [tsupport] at this
    have := subset_trans this <| closure_mono fSupp
    rwa [closure_Icc] at this

lemma IntervalIntegral.integral_eq_integral_of_support_subset_Icc {a b : ℝ} {μ : Measure ℝ}
    [NullSingletonClass μ] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E} (h : f.support ⊆ Icc a b) :
    ∫ x in a..b, f x ∂μ = ∫ x, f x ∂μ := by
  rcases le_total a b with hab | hab
  · rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc,
    ← integral_indicator measurableSet_Icc, indicator_eq_self.2 h]
  · by_cases hab2 : b = a
    · rw [hab2] at h ⊢
      simp only [intervalIntegral.integral_same]
      simp only [Icc_self] at h
      have : ∫ (x : ℝ), f x ∂μ = ∫ (x : ℝ) in {a}, f x ∂μ := by
        rw [ ← integral_indicator (by simp), indicator_eq_self.2 h]
      rw [this, integral_singleton]; simp [Measure.real]
    · rw [Icc_eq_empty_iff.mpr <| by exact fun x ↦ hab2 <| le_antisymm hab x, subset_empty_iff,
          Function.support_eq_empty_iff] at h; simp [h]

lemma SetIntegral.integral_eq_integral_inter_of_support_subset {μ : Measure ℝ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s t : Set ℝ} {f : ℝ → E} (h : f.support ⊆ t) (ht : MeasurableSet t) :
    ∫ x in s, f x ∂μ = ∫ x in s ∩ t, f x ∂μ := by
  rw [← setIntegral_indicator ht, indicator_eq_self.2 h]

lemma SetIntegral.integral_eq_integral_inter_of_support_subset_Icc {a b} {μ : Measure ℝ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set ℝ} {f : ℝ → E} (h : f.support ⊆ Icc a b) (hs : Icc a b ⊆ s) :
    ∫ x in s, f x ∂μ = ∫ x in Icc a b, f x ∂μ := by
  rw [SetIntegral.integral_eq_integral_inter_of_support_subset h measurableSet_Icc,
      inter_eq_self_of_subset_right hs]

lemma intervalIntegral.norm_integral_le_of_norm_le_const' {a b C : ℝ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hab : a ≤ b) (h : ∀ x ∈ (Icc a b), ‖f x‖ ≤ C) :
    ‖∫ x in a..b, f x‖ ≤ C * |b - a| := by
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  exact fun x hx ↦ h x <| mem_Icc_of_Ioc <| uIoc_of_le hab ▸ hx

lemma Filter.TendstoAtZero_of_support_in_Icc {a b : ℝ} (f : ℝ → 𝕂) (ha : 0 < a)
    (fSupp : f.support ⊆ Set.Icc a b) :
    Tendsto f (𝓝[>]0) (𝓝 0) := by
  apply Tendsto.comp (tendsto_nhds_of_eventually_eq ?_) tendsto_id
  filter_upwards [Ioo_mem_nhdsGT ha] with c hc; replace hc := (mem_Ioo.mp hc).2
  have h : c ∉ Icc a b := fun h ↦ by linarith [mem_Icc.mp h]
  convert mt (Function.support_subset_iff.mp fSupp c) h; simp

lemma Filter.TendstoAtTop_of_support_in_Icc {a b : ℝ} (f : ℝ → 𝕂)
    (fSupp : f.support ⊆ Set.Icc a b) :
    Tendsto f atTop (𝓝 0) := by
  apply Tendsto.comp (tendsto_nhds_of_eventually_eq ?_) tendsto_id
  filter_upwards [Ioi_mem_atTop b] with c hc; rw [mem_Ioi] at hc
  have h : c ∉ Icc a b := fun h ↦ by linarith [mem_Icc.mp h]
  convert mt (Function.support_subset_iff.mp fSupp c) h; simp

lemma Filter.BigO_zero_atZero_of_support_in_Icc {a b : ℝ} (f : ℝ → 𝕂) (ha : 0 < a)
    (fSupp : f.support ⊆ Set.Icc a b) :
    f =O[𝓝[>] 0] fun _ ↦ (0 : ℝ) := by
  refine Eventually.isBigO ?_
  filter_upwards [Ioo_mem_nhdsGT (by linarith : (0 : ℝ) < a)] with c hc
  refine norm_le_zero_iff.mpr <| Function.support_subset_iff'.mp fSupp c ?_
  exact fun h ↦ by linarith [mem_Icc.mp h, (mem_Ioo.mp hc).2]

lemma Filter.BigO_zero_atTop_of_support_in_Icc {a b : ℝ} (f : ℝ → 𝕂)
    (fSupp : f.support ⊆ Set.Icc a b) :
    f =O[atTop] fun _ ↦ (0 : ℝ) := by
  refine Eventually.isBigO ?_
  filter_upwards [Ioi_mem_atTop b] with c hc; replace hc := mem_Ioi.mp hc
  refine norm_le_zero_iff.mpr <| Function.support_subset_iff'.mp fSupp c ?_
  exact fun h ↦ by linarith [mem_Icc.mp h]

lemma deriv.ofReal_comp' {f : ℝ → ℝ} :
    deriv (fun x : ℝ ↦ (f x : ℂ)) = (fun x ↦ ((deriv f) x : ℂ)) :=
  funext fun _ ↦ deriv.ofReal_comp

lemma deriv.comp_ofReal' {e : ℂ → ℂ} (hf : Differentiable ℂ e) :
    deriv (fun x : ℝ ↦ e x) = fun (x : ℝ) ↦ deriv e x :=
  funext fun _ ↦ deriv.comp_ofReal (hf.differentiableAt)

lemma PartialIntegration (f g : ℝ → ℂ)
    (fDiff : DifferentiableOn ℝ f (Ioi 0))
    (gDiff : DifferentiableOn ℝ g (Ioi 0))
    (fDerivgInt : IntegrableOn (f * deriv g) (Ioi 0))
    (gDerivfInt : IntegrableOn (deriv f * g) (Ioi 0))
    (lim_at_zero : Tendsto (f * g) (𝓝[>] 0) (𝓝 0))
    (lim_at_inf : Tendsto (f * g) atTop (𝓝 0)) :
    ∫ x in Ioi 0, f x * deriv g x = -∫ x in Ioi 0, deriv f x * g x := by
  simpa using integral_Ioi_mul_deriv_eq_deriv_mul
    (fun x hx ↦ fDiff.hasDerivAt (Ioi_mem_nhds hx))
    (fun x hx ↦ gDiff.hasDerivAt (Ioi_mem_nhds hx))
    fDerivgInt gDerivfInt lim_at_zero lim_at_inf

lemma PartialIntegration_of_support_in_Icc {a b : ℝ} (f g : ℝ → ℂ) (ha : 0 < a)
    (h : a ≤ b)
    (fSupp : f.support ⊆ Set.Icc a b)
    (fDiff : DifferentiableOn ℝ f (Ioi 0))
    (gDiff : DifferentiableOn ℝ g (Ioi 0))
    (fderivCont : ContinuousOn (deriv f) (Ioi 0))
    (gderivCont : ContinuousOn (deriv g) (Ioi 0)) :
    ∫ x in Ioi 0, f x * deriv g x = -∫ x in Ioi 0, deriv f x * g x := by
  have Icc_sub : Icc a b ⊆ Ioi 0 := (Icc_subset_Ioi_iff h).mpr ha
  have fderivSupp := Function.support_deriv_subset_Icc fSupp
  have fgSupp : (f * g).support ⊆ Icc a b := Function.support_mul_subset_of_subset fSupp
  have fDerivgInt : IntegrableOn (f * deriv g) (Ioi 0) := by
    apply (integrableOn_iff_integrable_of_support_subset <|
           Function.support_mul_subset_of_subset fSupp).mp
    exact fDiff.continuousOn.mono Icc_sub |>.mul (gderivCont.mono Icc_sub) |>.integrableOn_Icc
  have gDerivfInt : IntegrableOn (deriv f * g) (Ioi 0) := by
    apply (integrableOn_iff_integrable_of_support_subset <|
           Function.support_mul_subset_of_subset fderivSupp).mp
    exact fderivCont.mono Icc_sub |>.mul (gDiff.continuousOn.mono Icc_sub) |>.integrableOn_Icc
  have lim_at_zero : Tendsto (f * g) (𝓝[>]0) (𝓝 0) :=
    TendstoAtZero_of_support_in_Icc (f * g) ha fgSupp
  have lim_at_inf : Tendsto (f * g) atTop (𝓝 0) := TendstoAtTop_of_support_in_Icc (f * g) fgSupp
  apply PartialIntegration f g fDiff gDiff fDerivgInt gDerivfInt lim_at_zero lim_at_inf

noncomputable def MellinConvolution (f g : ℝ → 𝕂) (x : ℝ) : 𝕂 :=
  ∫ y in Ioi 0, f y * g (x / y) / y

lemma MellinConvolutionSymmetric (f g : ℝ → 𝕂) {x : ℝ} (xpos : 0 < x) :
    MellinConvolution f g x = MellinConvolution g f x := by
  unfold MellinConvolution
  calc
    _ = ∫ y in Ioi 0, f (y * x) * g (1 / y) / y := ?_
    _ = _ := ?_
  · rw [← integral_comp_mul_right_I0i_haar (fun y ↦ f y * g (x / y)) xpos]
    simp [div_mul_cancel_right₀ <| ne_of_gt xpos]
  · convert (integral_comp_inv_I0i_haar fun y ↦ f (y * x) * g (1 / y)).symm using 3
    rw [one_div_one_div, mul_comm, mul_comm_div, one_mul]

open Pointwise in
lemma support_MellinConvolution_subsets {f g : ℝ → 𝕂} {A B : Set ℝ} (hf : f.support ⊆ A)
    (hg : g.support ⊆ B) : (MellinConvolution f g).support ⊆ A * B := by
  rw [Function.support_subset_iff'] at hf hg ⊢
  intro x hx
  unfold MellinConvolution
  simp only [Set.mem_mul, not_exists, not_and] at hx
  apply MeasureTheory.integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem (by measurability)]
  intro y hy
  simp only [mem_Ioi] at hy
  simp only [Pi.zero_apply, div_eq_zero_iff, mul_eq_zero, map_eq_zero]
  left
  by_cases hyA : y ∈ A
  · right
    apply hg
    intro hxyB
    apply hx _ hyA _ hxyB
    field_simp
  · left
    apply hf _ hyA

open Pointwise in
lemma support_MellinConvolution (f g : ℝ → 𝕂) :
    (MellinConvolution f g).support ⊆ f.support * g.support :=
  support_MellinConvolution_subsets subset_rfl subset_rfl

lemma MellinConvolutionTransform (f g : ℝ → ℂ) (s : ℂ)
    (hf : IntegrableOn (fun x y ↦ f y * g (x / y) / (y : ℂ) * (x : ℂ) ^ (s - 1)).uncurry
      (Ioi 0 ×ˢ Ioi 0)) :
    mellin (MellinConvolution f g) s = mellin f s * mellin g s := by
  dsimp [mellin, MellinConvolution]
  set f₁ : ℝ × ℝ → ℂ :=
    fun ⟨x, y⟩ ↦ f y * g (x / y) / (y : ℂ) * (x : ℂ) ^ (s - 1)
  calc
    _ = ∫ (x : ℝ) in Ioi 0, ∫ (y : ℝ) in Ioi 0, f₁ (x, y) := ?_
    _ = ∫ (y : ℝ) in Ioi 0, ∫ (x : ℝ) in Ioi 0, f₁ (x, y) :=
        setIntegral_integral_swap _ hf
    _ = ∫ (y : ℝ) in Ioi 0, ∫ (x : ℝ) in Ioi 0,
        f y * g (x / y) / ↑y * ↑x ^ (s - 1) := rfl
    _ = ∫ (y : ℝ) in Ioi 0, ∫ (x : ℝ) in Ioi 0,
        f y * g (x * y / y) / ↑y * ↑(x * y) ^ (s - 1) * y := ?_
    _ = ∫ (y : ℝ) in Ioi 0, ∫ (x : ℝ) in Ioi 0,
        f y * ↑y ^ (s - 1) * (g x * ↑x ^ (s - 1)) := ?_
    _ = ∫ (y : ℝ) in Ioi 0,
        f y * ↑y ^ (s - 1) * ∫ (x : ℝ) in Ioi 0, g x * ↑x ^ (s - 1) := ?_
    _ = _ := integral_mul_const _ _
  <;> try (rw [setIntegral_congr_fun (by simp)]; intro y hy; simp only [ofReal_mul])
  · simp only [integral_mul_const, f₁, mul_comm]
  · simp only [integral_mul_const]
    have := integral_comp_mul_right_Ioi
      (fun x ↦ f y * g (x / y) / (y : ℂ) * (x : ℂ) ^ (s - 1)) 0 hy
    have y_ne_zeroℂ : (y : ℂ) ≠ 0 := slitPlane_ne_zero (Or.inl hy)
    field_simp at this ⊢
    simp only [ofReal_mul, one_div, mul_zero, real_smul, ofReal_inv, field] at this ⊢
    rw [← this]
    field_simp
    congr with x
    ring_nf
  · rw [setIntegral_congr_fun (by simp)]
    intro x hx
    have y_ne_zeroℝ : y ≠ 0 := ne_of_gt (mem_Ioi.mp hy)
    have y_ne_zeroℂ : (y : ℂ) ≠ 0 := by exact_mod_cast y_ne_zeroℝ
    field_simp
    rw [mul_cpow_ofReal_nonneg hy.le hx.le]
    ring
  · apply integral_const_mul
  · congr <;> ext <;> ring

lemma mem_within_strip (σ₁ σ₂ : ℝ) :
    {s : ℂ | σ₁ ≤ s.re ∧ s.re ≤ σ₂} ∈
      𝓟 {s | σ₁ ≤ s.re ∧ s.re ≤ σ₂} :=
  mem_principal_self _

lemma MellinOfPsi_aux {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (suppν : ν.support ⊆ Set.Icc (1 / 2) 2)
    {s : ℂ} (hs : s ≠ 0) :
    ∫ (x : ℝ) in Ioi 0, (ν x) * (x : ℂ) ^ (s - 1) =
    - (1 / s) * ∫ (x : ℝ) in Ioi 0, (deriv ν x) * (x : ℂ) ^ s := by
  let g (s : ℂ) := fun (x : ℝ)  ↦ x ^ s / s
  have gderiv {s : ℂ} (hs : s ≠ 0) {x: ℝ} (hx : x ∈ Ioi 0) :
      deriv (g s) x = x ^ (s - 1) := by
    have := HasDerivAt.cpow_const (c := s) (hasDerivAt_id (x : ℂ)) (Or.inl hx)
    simp_rw [mul_one, id_eq] at this
    rw [deriv_div_const, deriv.comp_ofReal (e := fun x ↦ x ^ s)]
    · rw [this.deriv, mul_div_right_comm, div_self hs, one_mul]
    · apply hasDerivAt_deriv_iff.mp
      simp only [this.deriv, this]
  calc
    _ =  ∫ (x : ℝ) in Ioi 0, ↑(ν x) * deriv (@g s) x := ?_
    _ = -∫ (x : ℝ) in Ioi 0, deriv (fun x ↦ ↑(ν x)) x * @g s x := ?_
    _ = -∫ (x : ℝ) in Ioi 0, deriv ν x * @g s x := ?_
    _ = -∫ (x : ℝ) in Ioi 0, deriv ν x * x ^ s / s := by simp only [mul_div, g]
    _ = _ := ?_
  · rw [setIntegral_congr_fun (by simp)]
    intro _ hx
    simp only [gderiv hs hx]
  · apply PartialIntegration_of_support_in_Icc (ν ·) (g s)
      (a := 1 / 2) (b := 2) (by norm_num) (by norm_num)
    · simpa only [Function.support_subset_iff, ne_eq, ofReal_eq_zero]
    · exact (Differentiable.ofReal_comp_iff.mpr
        (diffν.differentiable (by norm_num))).differentiableOn
    · refine DifferentiableOn.div_const ?_ s
      intro a ha
      refine DifferentiableAt.comp_ofReal (e := fun x ↦ x ^ s) ?_ |>.differentiableWithinAt
      apply differentiableAt_fun_id.cpow (differentiableAt_const s) <| by exact Or.inl ha
    · simp only [deriv.ofReal_comp']
      exact continuous_ofReal.comp (diffν.continuous_deriv (by norm_num)) |>.continuousOn
    · apply ContinuousOn.congr (f := fun (x : ℝ) ↦ (x : ℂ) ^ (s - 1)) ?_
        fun x hx ↦ gderiv hs hx
      exact Continuous.continuousOn (by continuity) |>.cpow continuousOn_const (by simp)
  · congr; funext; congr
    apply (hasDerivAt_deriv_iff.mpr ?_).ofReal_comp.deriv
    exact diffν.contDiffAt.differentiableAt (by norm_num)
  · simp only [neg_mul, neg_inj]
    conv => lhs; rhs; intro; rw [← mul_one_div, mul_comm]
    rw [integral_const_mul]

lemma MellinOfPsi {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (suppν : ν.support ⊆ Set.Icc (1 / 2) 2) :
    ∃ C > 0, ∀ (σ₁ : ℝ) (_ : 0 < σ₁) (s : ℂ) (_ : σ₁ ≤ s.re) (_ : s.re ≤ 2),
    ‖mellin (fun x ↦ (ν x : ℂ)) s‖ ≤ C * ‖s‖⁻¹ := by
  let f := fun (x : ℝ) ↦ ‖deriv ν x‖
  have cont : ContinuousOn f (Icc (1 / 2) 2) :=
    (Continuous.comp (by continuity) <| diffν.continuous_deriv (by norm_num)).continuousOn
  obtain ⟨a, _, max⟩ := isCompact_Icc.exists_isMaxOn (f := f) (by norm_num) cont
  let σ₂ : ℝ := 2
  let C : ℝ := f a * 2 ^ σ₂ * (3 / 2)
  have mainBnd : ∀ (σ₁ : ℝ), 0 < σ₁ → ∀ (s : ℂ), σ₁ ≤ s.re → s.re ≤ 2 →
      ‖mellin (fun x ↦ (ν x : ℂ)) s‖ ≤ C * ‖s‖⁻¹ := by
    intro σ₁ σ₁pos s hs₁ hs₂
    have s_ne_zero: s ≠ 0 := fun h ↦ by linarith [zero_re ▸ h ▸ hs₁]
    simp only [mellin, f, MellinOfPsi_aux diffν suppν s_ne_zero, norm_mul, smul_eq_mul, mul_comm]
    gcongr
    · simp
    calc
      _ ≤ ∫ (x : ℝ) in Ioi 0, ‖(deriv ν x * (x : ℂ) ^ s)‖ := ?_
      _ = ∫ (x : ℝ) in Icc (1 / 2) 2, ‖(deriv ν x * (x : ℂ) ^ s)‖ := ?_
      _ ≤ ‖∫ (x : ℝ) in Icc (1 / 2) 2, ‖(deriv ν x * (x : ℂ) ^ s)‖‖ :=
          le_abs_self _
      _ ≤ _ := ?_
    · simp_rw [norm_integral_le_integral_norm]
    · apply SetIntegral.integral_eq_integral_inter_of_support_subset_Icc
      · simp only [Function.support_abs, Function.support_mul, Function.support_ofReal]
        apply subset_trans (by apply inter_subset_left) <| Function.support_deriv_subset_Icc suppν
      · exact (Icc_subset_Ioi_iff (by norm_num)).mpr (by norm_num)
    · have := intervalIntegral.norm_integral_le_of_norm_le_const' (C := f a * 2 ^ σ₂)
        (f := fun x ↦ f x * ‖(x : ℂ) ^ s‖) (a := (1 / 2 : ℝ)) ( b := 2) (by norm_num) ?_
      · simp only [Real.norm_eq_abs, norm_real, norm_mul] at this ⊢
        rwa [(by norm_num: |(2 : ℝ) - 1 / 2| = 3 / 2),
            intervalIntegral.integral_of_le (by norm_num), ← integral_Icc_eq_integral_Ioc] at this
      · intro x hx;
        have f_bound := isMaxOn_iff.mp max x hx
        have pow_bound : ‖(x : ℂ) ^ s‖ ≤ 2 ^ σ₂ := by
          rw [norm_cpow_eq_rpow_re_of_pos (by linarith [mem_Icc.mp hx])]
          have xpos : 0 ≤ x := by linarith [(mem_Icc.mp hx).1]
          have h := rpow_le_rpow xpos (mem_Icc.mp hx).2 (by linarith : 0 ≤ s.re)
          exact le_trans h <| rpow_le_rpow_of_exponent_le (by norm_num) hs₂
        convert! mul_le_mul f_bound pow_bound (norm_nonneg _) ?_ using 1 <;> simp [f]
  have Cnonneg : 0 ≤ C := by
    have hh := mainBnd 1 (by norm_num) ((3 : ℂ) / 2) (by norm_num) (by norm_num)
    have hhh : 0 ≤ ‖mellin (fun x ↦ (ν x : ℂ)) ((3 : ℂ) / 2)‖ := by positivity
    have hhhh : 0 < ‖(3 : ℂ) / 2‖⁻¹ := by norm_num
    have := hhh.trans hh
    exact (mul_nonneg_iff_of_pos_right hhhh).mp this
  by_cases CeqZero : C = 0
  · refine ⟨1, by linarith, ?_⟩
    intro ε εpos s hs₁ hs₂
    have := mainBnd ε εpos s hs₁ hs₂
    rw [CeqZero, zero_mul] at this
    have : 0 ≤ 1 * ‖s‖⁻¹ := by positivity
    linarith
  · exact ⟨C, lt_of_le_of_ne Cnonneg fun a ↦ CeqZero (id (Eq.symm a)), mainBnd⟩

noncomputable def DeltaSpike (ν : ℝ → ℝ) (ε : ℝ) : ℝ → ℝ :=
  fun x ↦ ν (x ^ (1 / ε)) / ε

lemma DeltaSpikeMass {ν : ℝ → ℝ} (mass_one : ∫ x in Ioi 0, ν x / x = 1) {ε : ℝ}
    (εpos : 0 < ε) : ∫ x in Ioi 0, ((DeltaSpike ν ε) x) / x = 1 :=
  calc
    _ = ∫ (x : ℝ) in Ioi 0, (|1/ε| * x ^ (1 / ε - 1)) •
      ((fun z ↦ (ν z) / z) (x ^ (1 / ε))) := by
      apply setIntegral_congr_ae measurableSet_Ioi
      filter_upwards with x hx
      simp only [smul_eq_mul, abs_of_pos (one_div_pos.mpr εpos)]
      symm; calc
        _ = (ν (x ^ (1 / ε)) / x ^ (1 / ε)) * x ^ (1 / ε - 1) * (1 / ε) := by ring
        _ = _ := by rw [rpow_sub hx, rpow_one]
        _ = (ν (x ^ (1 / ε)) / x ^ (1 / ε) * x ^ (1 / ε) / x) * (1/ ε) := by ring
        _ = _ := by rw [div_mul_cancel₀ _ (ne_of_gt (rpow_pos_of_pos hx (1/ε)))]
        _ = (ν (x ^ (1 / ε)) / ε / x) := by ring
    _ = 1 := by
      rw [integral_comp_rpow_Ioi (fun z ↦ (ν z) / z), ← mass_one]
      simp only [ne_eq, div_eq_zero_iff, one_ne_zero, εpos.ne', or_self, not_false_eq_true]

lemma DeltaSpikeSupport_aux {ν : ℝ → ℝ} {ε : ℝ} (εpos : 0 < ε)
    (suppν : ν.support ⊆ Icc (1 / 2) 2) :
    (fun x ↦ if x < 0 then 0 else DeltaSpike ν ε x).support ⊆ Icc (2 ^ (-ε)) (2 ^ ε) := by
  unfold DeltaSpike
  simp only [one_div, Function.support_subset_iff, ne_eq, ite_eq_left_iff, not_lt, div_eq_zero_iff,
    not_forall, exists_prop, mem_Icc, and_imp]
  intro x hx h; push Not at h
  have := suppν <| Function.mem_support.mpr h.1
  simp only [one_div, mem_Icc] at this
  have hl := (le_rpow_inv_iff_of_pos (by norm_num) hx εpos).mp this.1
  rw [inv_rpow (by norm_num) ε, ← rpow_neg (by norm_num)] at hl
  refine ⟨hl, (rpow_inv_le_iff_of_pos ?_ (by norm_num) εpos).mp this.2⟩
  linarith [(by apply rpow_nonneg (by norm_num) : 0 ≤ (2 : ℝ) ^ (-ε))]

lemma DeltaSpikeSupport' {ν : ℝ → ℝ} {ε x : ℝ} (εpos : 0 < ε) (xnonneg : 0 ≤ x)
    (suppν : ν.support ⊆ Icc (1 / 2) 2) :
    DeltaSpike ν ε x ≠ 0 → x ∈ Icc (2 ^ (-ε)) (2 ^ ε) := by
  intro h
  have : (fun x ↦ if x < 0 then 0 else DeltaSpike ν ε x) x = DeltaSpike ν ε x := by
    simp [xnonneg]
  rw [← this] at h
  exact (Function.support_subset_iff.mp <| DeltaSpikeSupport_aux εpos suppν) _ h

lemma DeltaSpikeSupport {ν : ℝ → ℝ} {ε x : ℝ} (εpos : 0 < ε) (xnonneg : 0 ≤ x)
    (suppν : ν.support ⊆ Icc (1 / 2) 2) :
    x ∉ Icc (2 ^ (-ε)) (2 ^ ε) → DeltaSpike ν ε x = 0 := by
  contrapose!; exact DeltaSpikeSupport' εpos xnonneg suppν

lemma DeltaSpikeContinuous {ν : ℝ → ℝ} {ε : ℝ} (εpos : 0 < ε)
    (diffν : ContDiff ℝ 1 ν) : Continuous (fun x ↦ DeltaSpike ν ε x) := by
  apply diffν.continuous.comp (g := ν) _ |>.div_const
  exact continuous_id.rpow_const fun _ ↦ Or.inr <| div_nonneg (by norm_num) εpos.le

lemma DeltaSpikeOfRealContinuous {ν : ℝ → ℝ} {ε : ℝ} (εpos : 0 < ε)
    (diffν : ContDiff ℝ 1 ν) : Continuous (fun x ↦ (DeltaSpike ν ε x : ℂ)) :=
  continuous_ofReal.comp <| DeltaSpikeContinuous εpos diffν

theorem MellinOfDeltaSpike (ν : ℝ → ℝ) {ε : ℝ} (εpos : ε > 0) (s : ℂ) :
    mellin (fun x ↦ (DeltaSpike ν ε x : ℂ)) s = mellin (fun x ↦ (ν x : ℂ)) (ε * s) := by
  unfold DeltaSpike
  push_cast
  rw [mellin_div_const, mellin_comp_rpow (fun x ↦ (ν x : ℂ)), abs_of_nonneg (by positivity)]
  simp only [one_div, inv_inv, ofReal_inv, div_inv_eq_mul, real_smul]
  rw [mul_div_cancel_left₀ _ (ne_zero_of_re_pos εpos)]
  ring_nf

lemma MellinOfDeltaSpikeAt1 (ν : ℝ → ℝ) {ε : ℝ} (εpos : ε > 0) :
    mellin (fun x ↦ (DeltaSpike ν ε x : ℂ)) 1 = mellin (fun x ↦ (ν x : ℂ)) ε := by
  convert MellinOfDeltaSpike ν εpos 1; simp [mul_one]

lemma MellinOfDeltaSpikeAt1_asymp {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (suppν : ν.support ⊆ Set.Icc (1 / 2) 2)
    (mass_one : ∫ x in Set.Ioi 0, ν x / x = 1) :
    (fun (ε : ℝ) ↦ (mellin (fun x ↦ (ν x : ℂ)) ε) - 1) =O[𝓝[>]0] id := by
  have diff : DifferentiableWithinAt ℝ
      (fun (ε : ℝ) ↦ mellin (fun x ↦ (ν x : ℂ)) ε - 1) (Ioi 0) 0 := by
    apply DifferentiableAt.differentiableWithinAt
    simp only [(differentiableAt_const _).fun_sub_iff_left]
    refine DifferentiableAt.comp_ofReal ?_
    refine mellin_differentiableAt_of_isBigO_rpow (a := 1) (b := -1) ?_ ?_ (by simp) ?_ (by simp)
    · apply (Continuous.continuousOn ?_).locallyIntegrableOn (by simp)
      have := diffν.continuous; continuity
    · apply Asymptotics.IsBigO.trans_le (g' := fun _ ↦ (0 : ℝ)) ?_ (by simp)
      apply BigO_zero_atTop_of_support_in_Icc (a := 1 / 2) (b := 2)
      rwa [ν.support_ofReal]
    · apply Asymptotics.IsBigO.trans_le (g' := fun _ ↦ (0 : ℝ)) ?_ (by simp)
      apply BigO_zero_atZero_of_support_in_Icc (a := 1 / 2) (b := 2) (ha := (by norm_num))
      rwa [ν.support_ofReal]
  have := ofReal_zero ▸ diff.isBigO_sub
  simp only [sub_sub_sub_cancel_right, sub_zero] at this
  convert! this using 1
  simp only [mellin, zero_sub, cpow_neg_one, smul_eq_mul]
  funext ε
  congr 1
  symm
  calc (∫ (t : ℝ) in Ioi 0, (↑t)⁻¹ * ↑(ν t) : ℂ)
      = ∫ (t : ℝ) in Ioi 0, ((ν t / t : ℝ) : ℂ) :=
        integral_congr_ae (Filter.Eventually.of_forall fun t => by push_cast; ring)
    _ = ((∫ t in Ioi 0, ν t / t : ℝ) : ℂ) := integral_ofReal
    _ = 1 := by rw [mass_one, ofReal_one]

lemma MellinOf1 (s : ℂ) (h : s.re > 0) :
    mellin ((fun x ↦ if 0 < x ∧ x ≤ 1 then 1 else 0)) s = 1 / s := by
  convert (hasMellin_one_Ioc h).right <;> first | rfl | simp [Set.indicator, Set.mem_Ioc] | congr

noncomputable def Smooth1 (ν : ℝ → ℝ) (ε : ℝ) : ℝ → ℝ :=
  MellinConvolution (fun x ↦ if 0 < x ∧ x ≤ 1 then 1 else 0) (DeltaSpike ν ε)

lemma Smooth1_def_ite {ν : ℝ → ℝ} {ε x : ℝ} (xpos : 0 < x) :
    Smooth1 ν ε x = MellinConvolution (fun x ↦ if 0 < x ∧ x ≤ 1 then 1 else 0)
      (fun x ↦ if x < 0 then 0 else DeltaSpike ν ε x) x := by
  unfold Smooth1
  rw [MellinConvolutionSymmetric _ _ xpos]
  conv => lhs; rw [MellinConvolutionSymmetric _ _ xpos]
  unfold MellinConvolution
  apply MeasureTheory.integral_congr_ae
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi]
  simp +contextual only [mem_Ioi, true_and, ite_mul, one_mul, zero_mul, RCLike.ofReal_real_eq_id,
    id_eq, mul_ite, mul_zero]
  intro y ypos
  rw [eq_comm, if_neg (by push Not; positivity)]

lemma Smooth1Properties_estimate {ε : ℝ} (εpos : 0 < ε) :
    (1 - 2 ^ (-ε)) / ε < Real.log 2 := by
  apply (div_lt_iff₀' εpos).mpr
  have : 1 - 1 / (2 : ℝ) ^ ε = ((2 : ℝ) ^ ε - 1) / (2 : ℝ) ^ ε := by
    rw [sub_div, div_self (by positivity)]
  rw [← Real.log_rpow (by norm_num), rpow_neg (by norm_num), inv_eq_one_div (2 ^ ε), this]
  set c := (2 : ℝ) ^ ε
  have hc : 1 < c := by
    rw [← rpow_zero (2 : ℝ)]
    apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num) εpos
  apply (div_lt_iff₀' (by positivity)).mpr <| lt_sub_iff_add_lt'.mp ?_
  let f := (fun x ↦ x * Real.log x - x)
  rw [(by simp [f] : -1 = f 1), (by simp [f] : c * Real.log c - c = f c)]
  have mono: StrictMonoOn f <| Ici 1 := by
    refine strictMonoOn_of_deriv_pos (convex_Ici _) ?_ ?_
    · apply continuousOn_id.mul (continuousOn_id.log ?_) |>.sub continuousOn_id
      intro x hx; simp only [mem_Ici] at hx; simp only [id_eq, ne_eq]; linarith
    · intro x hx; simp only [nonempty_Iio, interior_Ici', mem_Ioi] at hx
      dsimp only [f]
      rw [deriv_fun_sub, deriv_fun_mul, Real.deriv_log, deriv_id'', one_mul, mul_inv_cancel₀]
      · simp [log_pos hx]
      · linarith
      · simp only [differentiableAt_fun_id]
      · simp only [differentiableAt_log_iff, ne_eq]; linarith
      · exact differentiableAt_fun_id.mul <| differentiableAt_fun_id.log (by linarith)
      · simp only [differentiableAt_fun_id]
  exact mono (by rw [mem_Ici]) (mem_Ici.mpr <| le_of_lt hc) hc

lemma Smooth1Properties_below_aux {x ε : ℝ} (hx : x ≤ 1 - Real.log 2 * ε) (εpos : 0 < ε) :
    x < 2 ^ (-ε) := by
  calc
    x ≤ 1 - Real.log 2 * ε := hx
    _ < 2 ^ (-ε) := ?_
  rw [sub_lt_iff_lt_add, add_comm, ← sub_lt_iff_lt_add]
  exact (div_lt_iff₀ εpos).mp <| Smooth1Properties_estimate εpos

lemma Smooth1Properties_below {ν : ℝ → ℝ} (suppν : ν.support ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi 0, ν x / x = 1) :
    ∃ (c : ℝ), 0 < c ∧ c = Real.log 2 ∧
      ∀ (ε x) (_ : 0 < ε), 0 < x → x ≤ 1 - c * ε → Smooth1 ν ε x = 1 := by
  set c := Real.log 2; use c
  refine ⟨log_pos (by norm_num), rfl, ?_⟩
  intro ε x εpos xpos hx
  have hx2 := Smooth1Properties_below_aux hx εpos
  rewrite [← DeltaSpikeMass mass_one εpos]
  unfold Smooth1 MellinConvolution
  calc
    _ = ∫ (y : ℝ) in Ioi 0,
        indicator (Ioc 0 1) (fun y ↦ DeltaSpike ν ε (x / y) / ↑y) y := ?_
    _ = ∫ (y : ℝ) in Ioi 0, DeltaSpike ν ε (x / y) / y := ?_
    _ = _ := integral_comp_div_I0i_haar (fun y ↦ DeltaSpike ν ε y) xpos
  · rw [setIntegral_congr_fun (by simp)]
    intro y hy
    by_cases h : y ≤ 1 <;> simp [indicator, mem_Ioi.mp hy, h]
  · rw [setIntegral_congr_fun (by simp)]
    intro y hy
    have : y ≠ 0 := by
      rintro rfl
      simp at hy
    simp only [indicator_apply_eq_self, mem_Ioc, not_and, not_le, div_eq_zero_iff, this, or_false]
    intro hy2; replace hy2 := hy2 <| mem_Ioi.mp hy
    apply DeltaSpikeSupport εpos ?_ suppν
    · simp only [mem_Icc, not_and, not_le]; intro
      linarith [(by apply (div_lt_iff₀ (by linarith)).mpr; nlinarith : x / y < 2 ^ (-ε))]
    · rw [le_div_iff₀ (by linarith), zero_mul]; exact xpos.le

lemma Smooth1Properties_above_aux {x ε : ℝ} (hx : 1 + (2 * Real.log 2) * ε ≤ x)
    (hε : ε ∈ Ioo 0 1) :
    2 ^ ε < x := by
  calc
    x ≥ 1 + (2 * Real.log 2) * ε := hx
    _ > 2 ^ ε := ?_
  refine lt_add_of_sub_left_lt <| (div_lt_iff₀ hε.1).mp ?_
  calc
    2 * Real.log 2 > 2 * (1 - 2 ^ (-ε)) / ε := ?_
    _ > 2 ^ ε * (1 - 2 ^ (-ε)) / ε := ?_
    _ = (2 ^ ε - 1) / ε := ?_
  · field_simp
    exact Smooth1Properties_estimate hε.1
  · have : (2 : ℝ) ^ ε < 2 := by
      have h := rpow_lt_rpow_of_exponent_lt (x := 2) (by norm_num) hε.2
      rwa [Real.rpow_one] at h
    have pos: 0 < (1 - 2 ^ (-ε)) / ε := by
      refine div_pos ?_ hε.1
      rw [sub_pos]
      have h := rpow_lt_rpow_of_exponent_lt (x := 2) (by norm_num) (neg_lt_zero.mpr hε.1)
      rwa [Real.rpow_zero] at h
    have := (mul_lt_mul_iff_left₀ pos).mpr this
    ring_nf at this ⊢
    exact this
  · have : (2 : ℝ) ^ ε * (2 : ℝ) ^ (-ε) = (2 : ℝ) ^ (ε - ε) := by
      rw [← rpow_add (by norm_num), add_neg_cancel, sub_self]
    conv => lhs; lhs; ring_nf; rhs; simp [this]

lemma Smooth1Properties_above_aux2 {x y ε : ℝ} (hε : ε ∈ Ioo 0 1) (hy : y ∈ Ioc 0 1)
  (hx2 : 2 ^ ε < x) :
    2 < (x / y) ^ (1 / ε) := by
  obtain ⟨εpos, ε1⟩ := hε
  obtain ⟨ypos, y1⟩ := hy
  calc
    _ > (2 ^ ε / y) ^ (1 / ε) := ?_
    _ = 2 / y ^ (1 / ε) := ?_
    _ ≥ 2 / y := ?_
    _ ≥ 2 := ?_
  · rw [gt_iff_lt, div_rpow, div_rpow, lt_div_iff₀, mul_comm_div, div_self, mul_one]
    <;> try positivity
    · exact rpow_lt_rpow (by positivity) hx2 (by positivity)
    · exact LT.lt.le <| lt_trans (by positivity) hx2
  · rw [div_rpow, ← rpow_mul, mul_div_cancel₀ 1 <| ne_of_gt εpos, rpow_one] <;> positivity
  · have : y ^ (1 / ε) ≤ y := by
      nth_rewrite 2 [← rpow_one y]
      exact rpow_le_rpow_of_exponent_ge ypos y1 (by linarith [one_lt_one_div εpos ε1])
    have pos : 0 < y ^ (1 / ε) := rpow_pos_of_pos ypos _
    rw [ge_iff_le, div_le_iff₀, div_mul_eq_mul_div, le_div_iff₀', mul_comm] <;> try linarith
  · rw [ge_iff_le, le_div_iff₀ <| ypos]; exact (mul_le_iff_le_one_right zero_lt_two).mpr y1

lemma Smooth1Properties_above {ν : ℝ → ℝ} (suppν : ν.support ⊆ Icc (1 / 2) 2) :
    ∃ (c : ℝ), 0 < c ∧ c = 2 * Real.log 2 ∧
      ∀ (ε x) (_ : ε ∈ Ioo 0 1), 1 + c * ε ≤ x → Smooth1 ν ε x = 0 := by
  set c := 2 * Real.log 2; use c
  constructor
  · simp only [c, zero_lt_two, mul_pos_iff_of_pos_left]; exact log_pos (by norm_num)
  constructor
  · rfl
  intro ε x hε hx
  have hx2 := Smooth1Properties_above_aux hx hε
  unfold Smooth1 MellinConvolution
  simp only [ite_mul, one_mul, zero_mul, RCLike.ofReal_real_eq_id, id_eq]
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro y hy
  have ypos := mem_Ioi.mp hy
  by_cases y1 : y ≤ 1
  swap
  · simp [ypos, y1]
  simp only [mem_Ioi.mp hy, y1, and_self, ↓reduceIte, div_eq_zero_iff]; left
  apply DeltaSpikeSupport hε.1 ?_ suppν
  on_goal 1 =>
    simp only [mem_Icc, not_and, not_le]
  on_goal 2 =>
    suffices h : 2 ^ ε < x / y by
      linarith [(by apply rpow_pos_of_pos (by norm_num) : 0 < (2 : ℝ) ^ ε)]
  all_goals
  try intro
  have : x / y = ((x / y) ^ (1 / ε)) ^ ε := by
    rw [← rpow_mul]
    simp only [one_div, inv_mul_cancel₀ (ne_of_gt hε.1), rpow_one]
    apply div_nonneg_iff.mpr; left;
    exact ⟨(le_trans (rpow_pos_of_pos (by norm_num) ε).le) hx2.le, ypos.le⟩
  rw [this]
  refine rpow_lt_rpow (by norm_num) ?_ hε.1
  exact Smooth1Properties_above_aux2 hε ⟨ypos, y1⟩ hx2

lemma DeltaSpikeNonNeg_of_NonNeg {ν : ℝ → ℝ} (νnonneg : ∀ x > 0, 0 ≤ ν x)
     {x ε : ℝ} (xpos : 0 < x) (εpos : 0 < ε) :
    0 ≤ DeltaSpike ν ε x := by
  dsimp [DeltaSpike]
  have : 0 < x ^ (1 / ε) := by positivity
  have : 0 ≤ ν (x ^ (1 / ε)) := νnonneg _ this
  positivity

lemma MellinConvNonNeg_of_NonNeg {f g : ℝ → ℝ} (f_nonneg : ∀ x > 0, 0 ≤ f x)
    (g_nonneg : ∀ x > 0, 0 ≤ g x) {x : ℝ} (xpos : 0 < x) :
    0 ≤ MellinConvolution f g x := by
  dsimp [MellinConvolution]
  apply MeasureTheory.setIntegral_nonneg
  · exact measurableSet_Ioi
  · intro y ypos; simp only [mem_Ioi] at ypos
    have : 0 ≤ f y := f_nonneg _ ypos
    have : 0 < x / y := by positivity
    have : 0 ≤ g (x / y) := g_nonneg _ this
    positivity

lemma Smooth1Nonneg {ν : ℝ → ℝ} (νnonneg : ∀ x > 0, 0 ≤ ν x) {ε x : ℝ}
    (xpos : 0 < x) (εpos : 0 < ε) : 0 ≤ Smooth1 ν ε x := by
  dsimp [Smooth1]
  apply MellinConvNonNeg_of_NonNeg ?_ ?_ xpos
  · intro y hy; by_cases h : y ≤ 1 <;> simp [h, hy]
  · intro y ypos; exact DeltaSpikeNonNeg_of_NonNeg νnonneg ypos εpos

lemma Smooth1LeOne_aux {x ε : ℝ} {ν : ℝ → ℝ} (xpos : 0 < x) (εpos : 0 < ε)
    (mass_one : ∫ x in Ioi 0, ν x / x = 1) :
    ∫ (y : ℝ) in Ioi 0, ν ((x / y) ^ (1 / ε)) / ε / y = 1 := by
    calc
      _ = ∫ (y : ℝ) in Ioi 0, (ν (y ^ (1 / ε)) / ε) / y := ?_
      _ = ∫ (y : ℝ) in Ioi 0, ν y / y := ?_
      _ = 1 := mass_one
    · have := integral_comp_div_I0i_haar (fun y ↦ ν ((x / y) ^ (1 / ε)) / ε) xpos
      convert! this.symm using 1
      congr; funext y; congr; field_simp [mul_comm]
    · have := integral_comp_rpow_I0i_haar_real (fun y ↦ ν y) (one_div_ne_zero εpos.ne')
      rw [← this, abs_of_pos <| one_div_pos.mpr εpos]
      field_simp

lemma Smooth1LeOne {ν : ℝ → ℝ} (νnonneg : ∀ x > 0, 0 ≤ ν x)
    (mass_one : ∫ x in Ioi 0, ν x / x = 1) {ε : ℝ} (εpos : 0 < ε) {x : ℝ} (xpos : 0 < x) :
    Smooth1 ν ε x ≤ 1 := by
  unfold Smooth1 MellinConvolution DeltaSpike
  have := Smooth1LeOne_aux xpos εpos mass_one
  calc
    _ = ∫ (y : ℝ) in Ioi 0,
        (fun y ↦ if y ∈ Ioc 0 1 then 1 else 0) y * (ν ((x / y) ^ (1 / ε)) / ε / y) := ?_
    _ ≤ ∫ (y : ℝ) in Ioi 0, (ν ((x / y) ^ (1 / ε)) / ε) / y := ?_
    _ = 1 := this
  · rw [setIntegral_congr_fun (by simp)]
    simp only [ite_mul, one_mul, zero_mul, RCLike.ofReal_real_eq_id, id_eq, mem_Ioc]
    intro y hy; aesop
  · refine setIntegral_mono_on ?_ (integrable_of_integral_eq_one this) (by simp) ?_
    · refine integrable_of_integral_eq_one this |>.bdd_mul ?_
        (ae_of_all _ <| by aesop)
      have : (fun x ↦ if 0 < x ∧ x ≤ 1 then 1 else 0) =
          indicator (Ioc 0 1) (1 : ℝ → ℝ) := by
        aesop
      simp only [mem_Ioc, this, measurableSet_Ioc, aestronglyMeasurable_indicator_iff]
      exact aestronglyMeasurable_one
    · simp only [ite_mul, one_mul, zero_mul]
      intro y hy
      by_cases h : y ≤ 1
      · aesop
      field_simp
      simp only [mem_Ioc, h, and_false, ↓reduceIte, one_div, mul_zero]
      simp only [mem_Ioi] at hy
      apply div_nonneg
      · apply νnonneg; exact rpow_pos_of_pos (div_pos xpos <| mem_Ioi.mp hy) _
      · positivity

lemma MellinOfSmooth1a {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (suppν : ν.support ⊆ Icc (1 / 2) 2)
    {ε : ℝ} (εpos : 0 < ε) {s : ℂ} (hs : 0 < s.re) :
    mellin (fun x ↦ (Smooth1 ν ε x : ℂ)) s =
      s⁻¹ * mellin (fun x ↦ (ν x : ℂ)) (ε * s) := by
  let f' : ℝ → ℂ := fun x ↦ DeltaSpike ν ε x
  let f : ℝ → ℂ := fun x ↦ DeltaSpike ν ε x / x
  let g : ℝ → ℂ := fun x ↦ if 0 < x ∧ x ≤ 1 then 1 else 0
  let F : ℝ × ℝ → ℂ := Function.uncurry fun x y ↦ f y * g (x / y) * (x : ℂ) ^ (s - 1)
  let S := {⟨x, y⟩ : ℝ × ℝ | 0 < x  ∧ x ≤ y ∧ 2 ^ (-ε) ≤ y ∧ y ≤ 2 ^ ε}
  let F' : ℝ × ℝ → ℂ := piecewise S (fun ⟨x, y⟩ ↦ f y * (x : ℂ) ^ (s - 1))
     (fun _ ↦ 0)
  let Tx := Ioc 0 ((2 : ℝ) ^ ε)
  let Ty := Icc ((2 : ℝ) ^ (-ε)) ((2 : ℝ) ^ ε)

  have Seq : S = (Tx ×ˢ Ty) ∩ {(x, y) : ℝ × ℝ | x ≤ y} := by
    ext ⟨x, y⟩; constructor
    · exact fun h ↦ ⟨⟨⟨h.1, le_trans h.2.1 h.2.2.2⟩, ⟨h.2.2.1, h.2.2.2⟩⟩, h.2.1⟩
    · exact fun h ↦  ⟨h.1.1.1, ⟨h.2, h.1.2.1, h.1.2.2⟩⟩
  have SsubI : S ⊆ Ioi 0 ×ˢ Ioi 0 :=
    fun z hz ↦ ⟨hz.1, lt_of_lt_of_le (by apply rpow_pos_of_pos; norm_num) hz.2.2.1⟩
  have SsubT: S ⊆ Tx ×ˢ Ty := by simp_rw [Seq, inter_subset_left]
  have Smeas : MeasurableSet S := by
    rw [Seq]; apply MeasurableSet.inter ?_ <| measurableSet_le measurable_fst measurable_snd
    simp [measurableSet_prod, Tx, Ty]

  have int_F: IntegrableOn F (Ioi 0 ×ˢ Ioi 0) := by
    apply IntegrableOn.congr_fun (f := F') ?_ ?_ (by simp [measurableSet_prod]); swap
    · simp only [F, F', f, g, mul_ite, mul_one, mul_zero]
      intro ⟨x, y⟩ hz
      by_cases hS : ⟨x, y⟩ ∈ S <;> simp only [hS, piecewise]
      <;> simp only [mem_prod, mem_Ioi, mem_setOf_eq, not_and, not_le, S] at hz hS
      · simp [div_pos hz.1 hz.2, (div_le_one hz.2).mpr hS.2.1]
      · by_cases hxy : x / y ≤ 1
        swap
        · simp [hxy]
        have hy : y ∉ Icc (2 ^ (-ε)) (2 ^ ε) := by
          simp only [mem_Icc, not_and, not_le]; exact hS hz.1 <| (div_le_one hz.2).mp hxy
        simp [DeltaSpikeSupport εpos hz.2.le suppν hy]
    · apply Integrable.piecewise Smeas ?_ integrableOn_zero
      simp only [IntegrableOn, Measure.restrict_restrict_of_subset SsubI]
      apply MeasureTheory.Integrable.mono_measure ?_
      · apply MeasureTheory.Measure.restrict_mono' SsubT.eventuallyLE le_rfl
      have : volume.restrict (Tx ×ˢ Ty) = (volume.restrict Tx).prod (volume.restrict Ty) := by
        rw [Measure.prod_restrict, MeasureTheory.Measure.volume_eq_prod]
      conv => rw [this]; lhs; intro; rw [mul_comm]
      apply MeasureTheory.Integrable.mul_prod (f := fun x ↦ (x : ℂ) ^ (s - 1))
        (μ := Measure.restrict volume Tx)
      · simp only [Tx]
        rw [← IntegrableOn, integrableOn_Ioc_iff_integrableOn_Ioo,
          intervalIntegral.integrableOn_Ioo_cpow_iff]
        · simp [hs]
        · apply rpow_pos_of_pos (by norm_num)
      · apply (ContinuousOn.div ?_ ?_ ?_).integrableOn_compact isCompact_Icc
        · exact (DeltaSpikeOfRealContinuous εpos diffν).continuousOn
        · exact continuous_ofReal.continuousOn
        · intro x hx; simp only [mem_Icc] at hx; simp only [ofReal_ne_zero]
          linarith [(by apply rpow_pos_of_pos (by norm_num) : (0 : ℝ) < 2 ^ (-ε))]

  have : mellin (MellinConvolution g f') s = mellin g s * mellin f' s := by
    rw [mul_comm, ← MellinConvolutionTransform f' g s
      (by convert int_F using 1; simp only [f', F, f]; field_simp)]
    dsimp [mellin]; rw [setIntegral_congr_fun (by simp)]
    intro x hx; simp_rw [MellinConvolutionSymmetric _ _ <| mem_Ioi.mp hx]

  convert! this using 1
  · congr; funext x; convert! integral_ofReal.symm
    simp only [MellinConvolution, RCLike.ofReal_div, ite_mul, one_mul, zero_mul, @apply_ite ℝ ℂ,
      algebraMap.coe_zero, g]; rfl
  · rw [MellinOf1 s hs, MellinOfDeltaSpike ν εpos s]
    simp

lemma MellinOfSmooth1b {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (suppν : ν.support ⊆ Set.Icc (1 / 2) 2) :
    ∃ (C : ℝ) (_ : 0 < C), ∀ (σ₁ : ℝ) (_ : 0 < σ₁)
    (s) (_ : σ₁ ≤ s.re) (_ : s.re ≤ 2) (ε : ℝ) (_ : 0 < ε) (_ : ε < 1),
    ‖mellin (fun x ↦ (Smooth1 ν ε x : ℂ)) s‖ ≤ C * (ε * ‖s‖ ^ 2)⁻¹ := by
  obtain ⟨C, Cpos, hC⟩ := MellinOfPsi diffν suppν
  refine ⟨C, Cpos, ?_⟩
  intro σ₁ σ₁pos s hs1 hs2 ε εpos ε_lt_one
  rw [MellinOfSmooth1a diffν suppν εpos <| lt_of_le_of_lt' hs1 σ₁pos]
  have hh1 : ε * σ₁ ≤ (ε * s).re := by
    simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
    nlinarith
  have hh2 : (ε * s).re ≤ 2 := by
    simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
    nlinarith
  calc
    ‖s⁻¹ * mellin (fun x ↦ (ν x : ℂ)) (ε * s)‖ =
        ‖s⁻¹‖ * ‖mellin (fun x ↦ (ν x : ℂ)) (ε * s)‖ := by simp
    _                        ≤ ‖s⁻¹‖ * (C * (ε * ‖s‖)⁻¹) := by
      gcongr
      convert! hC (ε * σ₁) (by positivity) (ε * s) hh1 hh2
      simp [abs_eq_self.mpr εpos.le]
    _                        = C * (ε * ‖s‖ ^ 2)⁻¹ := by
      simp only [norm_inv, mul_inv_rev]
      ring

lemma MellinOfSmooth1c {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (suppν : ν.support ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi 0, ν x / x = 1) :
    (fun ε ↦ mellin (fun x ↦ (Smooth1 ν ε x : ℂ)) 1 - 1) =O[𝓝[>]0] id := by
  have h := MellinOfDeltaSpikeAt1_asymp diffν suppν mass_one
  rw [Asymptotics.isBigO_iff] at h ⊢
  obtain ⟨c, hc⟩ := h
  use c
  filter_upwards [hc, Ioo_mem_nhdsGT (by linarith : (0 : ℝ) < 1)] with ε hε hε'
  rw [MellinOfSmooth1a diffν suppν hε'.1 (s := 1) (by norm_num)]
  simp only [inv_one, mul_one, one_mul, id_eq, Real.norm_eq_abs]
  exact hε

lemma Smooth1ContinuousAt {SmoothingF : ℝ → ℝ}
    (diffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (SmoothingFpos : ∀ x > 0, 0 ≤ SmoothingF x)
    (suppSmoothingF : SmoothingF.support ⊆ Icc (1 / 2) 2)
    {ε : ℝ} (εpos : 0 < ε) {y : ℝ} (ypos : 0 < y) :
    ContinuousAt (fun x ↦ Smooth1 SmoothingF ε x) y := by
  apply ContinuousAt.congr
    (f := (fun x ↦ MellinConvolution (DeltaSpike SmoothingF ε)
      (fun x ↦ if 0 < x ∧ x ≤ 1 then 1 else 0) x)) _
  · filter_upwards [lt_mem_nhds ypos] with x hx
    apply MellinConvolutionSymmetric _ _ hx
  apply continuousAt_of_dominated (bound := (fun x ↦ 2 ^ ε * DeltaSpike SmoothingF ε x))
  · filter_upwards [lt_mem_nhds ypos] with x hx
    apply Measurable.aestronglyMeasurable
    apply Measurable.mul
    · apply Measurable.mul
      · exact Continuous.measurable <| DeltaSpikeContinuous εpos diffSmoothingF
      · apply Measurable.ite _ (by fun_prop) (by fun_prop)
        apply MeasurableSet.congr (s := Ici x) (by measurability)
        ext a
        constructor
        · intro ha
          have apos : 0 < a := lt_of_lt_of_le hx ha
          constructor
          · exact div_pos hx apos
          · exact (div_le_one apos).mpr ha
        · intro ha
          have : 0 < a := (div_pos_iff_of_pos_left hx).mp ha.1
          exact (div_le_one this).mp ha.2
    · fun_prop
  · filter_upwards [lt_mem_nhds ypos] with x hx
    filter_upwards [ae_restrict_mem (by measurability)] with t ht
    simp only [mul_ite, mul_one, mul_zero, RCLike.ofReal_real_eq_id, id_eq, norm_div, norm_eq_abs]
    by_cases! h : DeltaSpike SmoothingF ε t = 0
    · simp [h]
    have := DeltaSpikeSupport' εpos ht.le suppSmoothingF h
    have dsnonneg : 0 ≤ DeltaSpike SmoothingF ε t := by
      apply DeltaSpikeNonNeg_of_NonNeg <;> assumption
    calc
      _ ≤ |DeltaSpike SmoothingF ε t| / |t| := by
        gcongr
        · split_ifs with h
          · apply le_refl
          · exact dsnonneg
      _ ≤ _ := by
        rw [_root_.abs_of_nonneg dsnonneg, mul_comm, div_eq_mul_one_div, _root_.abs_of_pos ht]
        gcongr
        apply (one_div_le ht (by bound)).mpr
        · convert this.1 using 1
          rw [div_eq_iff (by positivity), ← rpow_add (by norm_num), neg_add_cancel, rpow_zero]
  · apply Integrable.const_mul
    apply (integrable_indicator_iff (by measurability)).mp
    apply (integrableOn_iff_integrable_of_support_subset (s := Icc (2 ^ (-ε)) (2 ^ ε)) _).mp
    · apply ContinuousOn.integrableOn_compact isCompact_Icc
      apply ContinuousOn.congr  (f := DeltaSpike SmoothingF ε)
      · apply Continuous.continuousOn
        apply DeltaSpikeContinuous<;> assumption
      · intro x hx
        have : x ∈ Ioi 0 := by
          apply mem_Ioi.mpr
          apply lt_of_lt_of_le (by bound) hx.1
        rw [indicator, if_pos this]
    · unfold indicator
      simp_rw [mem_Ioi]
      apply Function.support_subset_iff.mpr
      simp only [ne_eq, ite_eq_right_iff, Classical.not_imp, mem_Icc, and_imp]
      intro x hx
      apply DeltaSpikeSupport' εpos hx.le suppSmoothingF
  · have : ∀ᵐ (a : ℝ) ∂volume.restrict (Ioi 0), a ≠ y := by
      apply ae_iff.mpr
      simp
    filter_upwards [ae_restrict_mem (by measurability), this] with x hx hx2
    simp only [mem_Ioi] at hx
    apply ContinuousAt.div_const
    apply ContinuousAt.mul (by fun_prop)
    have : (fun x_1 ↦ if 0 < x_1 / x ∧ x_1 / x ≤ 1 then 1 else 0) =
        (Ioc 0 x).indicator (fun _ ↦ (1 : ℝ)) := by
      ext t
      unfold indicator
      simp [div_pos_iff_of_pos_right, div_le_one₀, hx]
    rw [this]
    apply ContinuousOn.continuousAt_indicator (by fun_prop)
    simp [frontier_Ioc hx, ypos.ne', hx2.symm]

lemma Smooth1MellinConvergent {Ψ : ℝ → ℝ} {ε : ℝ} (diffΨ : ContDiff ℝ 1 Ψ)
    (suppΨ : Ψ.support ⊆ Icc (1 / 2) 2) (hε : ε ∈ Ioo 0 1)
    (Ψnonneg : ∀ x > 0, 0 ≤ Ψ x) (mass_one : ∫ x in Ioi 0, Ψ x / x = 1)
    {s : ℂ} (hs : 0 < s.re) : MellinConvergent (fun x ↦ (Smooth1 Ψ ε x : ℂ)) s := by
  apply mellinConvergent_of_isBigO_rpow_exp zero_lt_one _ _ _ hs
  · apply ContinuousOn.locallyIntegrableOn _ (by measurability)
    apply continuousOn_of_forall_continuousAt
    exact fun x hx ↦ Smooth1ContinuousAt diffΨ Ψnonneg suppΨ hε.1 hx |>.ofReal
  · rw [Asymptotics.isBigO_iff]
    use 1
    obtain ⟨c, cpos, ceq, hc⟩ := Smooth1Properties_above suppΨ
    filter_upwards [eventually_ge_atTop (1 + c * ε)] with x hx
    rw [hc _ _ hε hx]
    simp only [ofReal_zero, norm_zero, neg_mul, one_mul, norm_eq_abs, abs_exp]
    bound
  · rw [Asymptotics.isBigO_iff]
    use 1
    filter_upwards [eventually_mem_nhdsWithin] with x hx
    simp only [norm_real, norm_eq_abs, neg_zero, rpow_zero, one_mem, CStarRing.norm_of_mem_unitary,
      mul_one]
    rw [_root_.abs_of_nonneg <| Smooth1Nonneg Ψnonneg hx hε.1]
    exact Smooth1LeOne Ψnonneg mass_one hε.1 hx

lemma Smooth1MellinDifferentiable {Ψ : ℝ → ℝ} {ε : ℝ} (diffΨ : ContDiff ℝ 1 Ψ)
    (suppΨ : Ψ.support ⊆ Icc (1 / 2) 2) (hε : ε ∈ Ioo 0 1)
    (Ψnonneg : ∀ x > 0, 0 ≤ Ψ x) (mass_one : ∫ x in Ioi 0, Ψ x / x = 1)
    {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (mellin (fun x ↦ (Smooth1 Ψ ε x : ℂ))) s := by
  apply mellin_differentiableAt_of_isBigO_rpow_exp zero_lt_one _ _ _ hs
  · apply ContinuousOn.locallyIntegrableOn _ (by measurability)
    apply continuousOn_of_forall_continuousAt
    exact fun x hx ↦ Smooth1ContinuousAt diffΨ Ψnonneg suppΨ hε.1 hx |>.ofReal
  · rw [Asymptotics.isBigO_iff]
    use 1
    obtain ⟨c, cpos, ceq, hc⟩ := Smooth1Properties_above suppΨ
    filter_upwards [eventually_ge_atTop (1 + c * ε)] with x hx
    rw [hc _ _ hε hx]
    simp only [ofReal_zero, norm_zero, neg_mul, one_mul, norm_eq_abs, abs_exp]
    bound
  · rw [Asymptotics.isBigO_iff]
    use 1
    filter_upwards [eventually_mem_nhdsWithin] with x hx
    simp only [norm_real, norm_eq_abs, neg_zero, rpow_zero, one_mem, CStarRing.norm_of_mem_unitary,
      mul_one]
    rw [_root_.abs_of_nonneg <| Smooth1Nonneg Ψnonneg hx hε.1]
    exact Smooth1LeOne Ψnonneg mass_one hε.1 hx
end

/- Adapted from PrimeNumberTheoremAnd/Sobolev.lean. -/
section
open Real Complex MeasureTheory Filter Topology BoundedContinuousFunction SchwartzMap  BigOperators
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

structure CS (n : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  toFun : ℝ → E
  h1 : ContDiff ℝ n toFun
  h2 : HasCompactSupport toFun

structure trunc extends (CS 2 ℝ) where
  h3 : (Set.Icc (-1) (1)).indicator 1 ≤ toFun
  h4 : toFun ≤ Set.indicator (Set.Ioo (-2) (2)) 1

structure W1 (n : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  toFun : ℝ → E
  smooth : ContDiff ℝ n toFun
  integrable : ∀ ⦃k⦄, k ≤ n → Integrable (iteratedDeriv k toFun)

abbrev W21 := W1 2 ℂ

section lemmas

noncomputable def funscale {E : Type*} (g : ℝ → E) (R x : ℝ) : E := g (R⁻¹ • x)

lemma contDiff_ofReal : ContDiff ℝ ∞ ofReal := by
  have key x : HasDerivAt ofReal 1 x := hasDerivAt_id x |>.ofReal_comp
  have key' : deriv ofReal = fun _ => 1 := by ext x ; exact (key x).deriv
  refine contDiff_infty_iff_deriv.mpr ⟨fun x => (key x).differentiableAt, ?_⟩
  simpa [key'] using contDiff_const

omit [NormedSpace ℝ E] in
lemma tendsto_funscale {f : ℝ → E} (hf : ContinuousAt f 0) (x : ℝ) :
    Tendsto (fun R => funscale f R x) atTop (𝓝 (f 0)) :=
  hf.tendsto.comp (by simpa using tendsto_inv_atTop_zero.mul_const x)

end lemmas

namespace CS

variable {f : CS n E} {R x v : ℝ}

instance : CoeFun (CS n E) (fun _ => ℝ → E) where coe := CS.toFun

instance : Coe (CS n ℝ) (CS n ℂ) where coe f := ⟨fun x => f x,
  contDiff_ofReal.of_le (mod_cast le_top) |>.comp f.h1, f.h2.comp_left (g := ofReal) rfl⟩

def neg (f : CS n E) : CS n E where
  toFun := -f
  h1 := f.h1.neg
  h2 := by simpa [HasCompactSupport, tsupport] using f.h2

instance : Neg (CS n E) where neg := neg

@[simp] lemma neg_apply {x : ℝ} : (-f) x = - (f x) := rfl

def smul (R : ℝ) (f : CS n E) : CS n E := ⟨R • f, f.h1.const_smul R, f.h2.smul_left⟩

instance : HSMul ℝ (CS n E) (CS n E) where hSMul := smul

@[simp] lemma smul_apply : (R • f) x = R • f x := rfl

lemma continuous (f : CS n E) : Continuous f := f.h1.continuous

noncomputable def deriv (f : CS (n + 1) E) : CS n E where
  toFun := _root_.deriv f
  h1 := (contDiff_succ_iff_deriv.mp f.h1).2.2
  h2 := f.h2.deriv

lemma hasDerivAt (f : CS (n + 1) E) (x : ℝ) : HasDerivAt f (f.deriv x) x :=
  (f.h1.differentiable (by simp)).differentiableAt.hasDerivAt

lemma deriv_apply {f : CS (n + 1) E} {x : ℝ} : f.deriv x = _root_.deriv f x := rfl

private lemma equal_of_apply {g h : CS n E} (he : ∀ t : ℝ, g t = h t) : g=h := by
  cases g
  cases h
  congr 1
  exact funext he

lemma deriv_smul {f : CS (n + 1) E} : (R • f).deriv = R • f.deriv := by
  apply equal_of_apply
  intro x
  exact (f.hasDerivAt x |>.const_smul R).deriv

noncomputable def scale (g : CS n E) (R : ℝ) : CS n E := by
  by_cases h : R = 0
  · exact ⟨0, contDiff_const, by simp [HasCompactSupport, tsupport]⟩
  · refine ⟨fun x => funscale g R x, ?_, ?_⟩
    · exact g.h1.comp (contDiff_const_smul R⁻¹)
    · exact g.h2.comp_smul (inv_ne_zero h)

lemma deriv_scale {f : CS (n + 1) E} : (f.scale R).deriv = R⁻¹ • f.deriv.scale R := by
  apply equal_of_apply
  intro v
  by_cases hR : R = 0
  · simp [hR, scale, deriv]
  · simp only [scale, hR, ↓reduceDIte, smul_apply]
    exact ((f.hasDerivAt (R⁻¹ • v)).scomp v
      (by simpa using! (hasDerivAt_id v).const_smul R⁻¹)).deriv

lemma deriv_scale' {f : CS (n + 1) E} :
    (f.scale R).deriv v = R⁻¹ • f.deriv (R⁻¹ • v) := by
  rw [deriv_scale, smul_apply]
  by_cases hR : R = 0 <;> simp [hR, scale, funscale]

lemma hasDerivAt_scale (f : CS (n + 1) E) (R x : ℝ) :
    HasDerivAt (f.scale R) (R⁻¹ • _root_.deriv f (R⁻¹ • x)) x := by
  convert hasDerivAt (f.scale R) x ; rw [deriv_scale'] ; rfl

lemma tendsto_scale (f : CS n E) (x : ℝ) : Tendsto (fun R => f.scale R x) atTop (𝓝 (f 0)) := by
  apply (tendsto_funscale f.continuous.continuousAt x).congr'
  filter_upwards [eventually_ne_atTop 0] with R hR ; simp [scale, hR]

lemma bounded : ∃ C, ∀ v, ‖f v‖ ≤ C := by
  obtain ⟨x, hx⟩ :=
    (continuous_norm.comp f.continuous).exists_forall_ge_of_hasCompactSupport f.h2.norm
  exact ⟨_, hx⟩

end CS

namespace trunc

instance : CoeFun trunc (fun _ => ℝ → ℝ) where coe f := f.toFun

instance : Coe trunc (CS 2 ℝ) where coe := trunc.toCS

lemma nonneg (g : trunc) (x : ℝ) : 0 ≤ g x := (Set.indicator_nonneg (by simp) x).trans (g.h3 x)

lemma le_one (g : trunc) (x : ℝ) : g x ≤ 1 :=
  (g.h4 x).trans <| Set.indicator_le_self' (by simp) x

lemma zero (g : trunc) : g =ᶠ[𝓝 0] 1 := by
  have : Set.Icc (-1) 1 ∈ 𝓝 (0 : ℝ) := by apply Icc_mem_nhds <;> linarith
  exact eventually_of_mem this (fun x hx => le_antisymm (g.le_one x) (by simpa [hx] using g.h3 x))

@[simp] lemma zero_at {g : trunc} : g 0 = 1 := g.zero.eq_of_nhds

end trunc

namespace W1

instance : CoeFun (W1 n E) (fun _ => ℝ → E) where coe := W1.toFun

lemma continuous (f : W1 n E) : Continuous f := f.smooth.continuous

lemma differentiable (f : W1 (n + 1) E) : Differentiable ℝ f :=
  f.smooth.differentiable (by simp)

lemma iteratedDeriv_sub {f g : ℝ → E} (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) :
    iteratedDeriv n (f - g) = iteratedDeriv n f - iteratedDeriv n g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    have hf' : ContDiff ℝ n (deriv f) := hf.iterate_deriv' n 1
    have hg' : ContDiff ℝ n (deriv g) := hg.iterate_deriv' n 1
    have hfg : deriv (f - g) = deriv f - deriv g := by
      ext x ; apply deriv_sub
      · exact (hf.differentiable (by simp)).differentiableAt
      · exact (hg.differentiable (by simp)).differentiableAt
    simp_rw [iteratedDeriv_succ', ← ih hf' hg', hfg]

noncomputable def deriv (f : W1 (n + 1) E) : W1 n E where
  toFun := _root_.deriv f
  smooth := contDiff_succ_iff_deriv.mp f.smooth |>.2.2
  integrable k hk := by
    simpa [iteratedDeriv_succ'] using f.integrable (Nat.succ_le_succ hk)

lemma hasDerivAt (f : W1 (n + 1) E) (x : ℝ) : HasDerivAt f (f.deriv x) x :=
  f.differentiable.differentiableAt.hasDerivAt

def sub (f g : W1 n E) : W1 n E where
  toFun := f - g
  smooth := f.smooth.sub g.smooth
  integrable k hk := by
    have hf : ContDiff ℝ k f := f.smooth.of_le (by simp [hk])
    have hg : ContDiff ℝ k g := g.smooth.of_le (by simp [hk])
    simpa [iteratedDeriv_sub hf hg] using (f.integrable hk).sub (g.integrable hk)

instance : Sub (W1 n E) where sub := sub

lemma integrable_iteratedDeriv_Schwarz {f : 𝓢(ℝ, ℂ)} : Integrable (iteratedDeriv n f) := by
  induction n generalizing f with
  | zero => exact f.integrable
  | succ n ih => simpa [iteratedDeriv_succ'] using! ih (f := SchwartzMap.derivCLM ℝ ℂ f)

noncomputable def of_Schwartz (f : 𝓢(ℝ, ℂ)) : W1 n ℂ where
  toFun := f
  smooth := f.smooth n
  integrable _ _ := integrable_iteratedDeriv_Schwarz

end W1

namespace W21

variable {f : W21}

noncomputable def norm (f : ℝ → ℂ) : ℝ :=
    (∫ v, ‖f v‖) + (4 * π ^ 2)⁻¹ * (∫ v, ‖deriv (deriv f) v‖)

lemma norm_nonneg {f : ℝ → ℂ} : 0 ≤ norm f :=
  add_nonneg (integral_nonneg (fun t => by simp))
    (mul_nonneg (by positivity) (integral_nonneg (fun t => by simp)))

noncomputable instance : Norm W21 where norm := norm ∘ W1.toFun

noncomputable instance : Coe 𝓢(ℝ, ℂ) W21 where coe := W1.of_Schwartz

def ofCS2 (f : CS 2 ℂ) : W21 := by
  refine ⟨f, f.h1, fun k hk => ?_⟩ ; match k with
  | 0 => exact f.h1.continuous.integrable_of_hasCompactSupport f.h2
  | 1 => simpa using (f.h1.continuous_deriv one_le_two).integrable_of_hasCompactSupport f.h2.deriv
  | 2 => simpa [iteratedDeriv_succ] using
    (f.h1.iterate_deriv' 0 2).continuous.integrable_of_hasCompactSupport f.h2.deriv.deriv

instance : Coe (CS 2 ℂ) W21 where coe := ofCS2

instance : HMul (CS 2 ℂ) W21 (CS 2 ℂ) where
  hMul g f := ⟨g * f, g.h1.mul f.smooth, g.h2.mul_right⟩

instance : HMul (CS 2 ℝ) W21 (CS 2 ℂ) where hMul g f := (g : CS 2 ℂ) * f

lemma hf (f : W21) : Integrable f := f.integrable zero_le_two

lemma hf' (f : W21) : Integrable (deriv f) := by
  simpa [iteratedDeriv_succ] using f.integrable one_le_two

lemma hf'' (f : W21) : Integrable (deriv (deriv f))  := by
  simpa [iteratedDeriv_succ] using f.integrable le_rfl

end W21

theorem W21_approximation (f : W21) (g : trunc) :
    Tendsto (fun R => ‖f - (g.scale R * f : W21)‖) atTop (𝓝 0) := by

  let f' := f.deriv
  let f'' := f'.deriv
  let g' := (g : CS 2 ℝ).deriv
  let g'' := g'.deriv
  let h R v := 1 - g.scale R v
  let h' R := - (g.scale R).deriv
  let h'' R := - (g.scale R).deriv.deriv

  have ch {R} : Continuous (fun v => (h R v : ℂ)) :=
    continuous_ofReal.comp <| continuous_const.sub (CS.continuous _)
  have ch' {R} : Continuous (fun v => (h' R v : ℂ)) := continuous_ofReal.comp (CS.continuous _)
  have ch'' {R} : Continuous (fun v => (h'' R v : ℂ)) := continuous_ofReal.comp (CS.continuous _)
  have dh R v : HasDerivAt (h R) (h' R v) v := by
    convert! CS.hasDerivAt_scale (g : CS 2 ℝ) R v |>.const_sub 1 using 1
    simp [h', CS.deriv_scale', show g.deriv.toFun = deriv g.toFun from rfl]
  have dh' R v : HasDerivAt (h' R) (h'' R v) v := ((g.scale R).deriv.hasDerivAt v).neg
  have hh1 R v : |h R v| ≤ 1 := by
    by_cases hR : R = 0 <;>
      simp only [CS.scale, funscale, smul_eq_mul, hR, ↓reduceDIte, Pi.zero_apply, sub_zero,
        abs_one, le_refl, h]
    rw [abs_le] ; constructor <;>
    linarith [g.le_one (R⁻¹ * v), g.nonneg (R⁻¹ * v)]
  have vR v : Tendsto (fun R : ℝ => v * R⁻¹) atTop (𝓝 0) := by
    simpa using tendsto_inv_atTop_zero.const_mul v

  convert_to Tendsto (fun R => W21.norm (fun v => h R v * f v)) atTop (𝓝 0)
  · ext R ; change W21.norm _ = _ ; congr ; ext v ; simp [h, sub_mul] ; rfl
  rw [show (0 : ℝ) = 0 + ((4 * π ^ 2)⁻¹ : ℝ) * 0 by simp]
  refine Tendsto.add ?_ (Tendsto.const_mul _ ?_)

  · let F R v := ‖h R v * f v‖
    have eh v : ∀ᶠ R in atTop, h R v = 0 := by
      filter_upwards [(vR v).eventually g.zero, eventually_ne_atTop 0] with R hR hR'
      simp [h, hR, CS.scale, hR', funscale, mul_comm R⁻¹]
    have e1 : ∀ᶠ (n : ℝ) in atTop, AEStronglyMeasurable (F n) volume := by
      apply Eventually.of_forall ; intro R
      exact (ch.mul f.continuous).norm.aestronglyMeasurable
    have e2 : ∀ᶠ (n : ℝ) in atTop, ∀ᵐ (a : ℝ), ‖F n a‖ ≤ ‖f a‖ := by
      apply Eventually.of_forall ; intro R
      apply Eventually.of_forall ; intro v
      simpa [F] using mul_le_mul (hh1 R v) le_rfl (by simp) zero_le_one
    have e4 : ∀ᵐ (a : ℝ), Tendsto (fun n ↦ F n a) atTop (𝓝 0) := by
      apply Eventually.of_forall ; intro v
      apply tendsto_nhds_of_eventually_eq ; filter_upwards [eh v] with R hR ; simp [F, hR]
    simpa [F] using tendsto_integral_filter_of_dominated_convergence _ e1 e2 f.hf.norm e4

  · let F R v := ‖h'' R v * f v + 2 * h' R v * f' v + h R v * f'' v‖
    convert_to Tendsto (fun R ↦ ∫ (v : ℝ), F R v) atTop (𝓝 0)
    · have this R v :
        deriv (deriv (fun v => h R v * f v)) v =
          h'' R v * f v + 2 * h' R v * f' v + h R v * f'' v := by
        have df v : HasDerivAt f (f' v) v := f.hasDerivAt v
        have df' v : HasDerivAt f' (f'' v) v := f'.hasDerivAt v
        have l3 v : HasDerivAt (fun v => h R v * f v) (h' R v * f v + h R v * f' v) v :=
          (dh R v).ofReal_comp.mul (df v)
        have l5 : HasDerivAt (fun v => h' R v * f v) (h'' R v * f v + h' R v * f' v) v :=
          (dh' R v).ofReal_comp.mul (df v)
        have l7 : HasDerivAt (fun v => h R v * f' v) (h' R v * f' v + h R v * f'' v) v :=
          (dh R v).ofReal_comp.mul (df' v)
        have d1 : deriv (fun v => h R v * f v) = fun v => h' R v * f v + h R v * f' v :=
          funext (fun v => (l3 v).deriv)
        rw [d1] ; convert! (l5.add l7).deriv using 1 ; ring
      simp_rw [this, F]

    obtain ⟨c1, mg'⟩ := g'.bounded
    obtain ⟨c2, mg''⟩ := g''.bounded
    let bound v := c2 * ‖f v‖ + 2 * c1 * ‖f' v‖ + ‖f'' v‖
    have e1 : ∀ᶠ (n : ℝ) in atTop, AEStronglyMeasurable (F n) volume := by
      apply Eventually.of_forall ; intro R ; apply (Continuous.norm ?_).aestronglyMeasurable
      exact ((ch''.mul f.continuous).add ((continuous_const.mul ch').mul f.deriv.continuous)).add
        (ch.mul f.deriv.deriv.continuous)
    have e2 : ∀ᶠ R in atTop, ∀ᵐ (a : ℝ), ‖F R a‖ ≤ bound a := by
      have hc1 : ∀ᶠ R in atTop, ∀ v, |h' R v| ≤ c1 := by
        filter_upwards [eventually_ge_atTop 1] with R hR v
        have hR' : R ≠ 0 := by linarith
        have : 0 ≤ R := by linarith
        simp only [CS.deriv_scale, CS.neg_apply, CS.smul_apply, smul_eq_mul, abs_neg, abs_mul,
          abs_inv, abs_eq_self.mpr this, ge_iff_le, h']
        simp only [CS.scale, hR', ↓reduceDIte, funscale, smul_eq_mul]
        convert_to _ ≤ c1 * 1
        · simp
        · rw [mul_comm]
          apply mul_le_mul (mg' _)
            (inv_le_of_inv_le₀ (by linarith) (by simpa using hR)) (by positivity)
          exact (abs_nonneg _).trans (mg' 0)
      have hc2 : ∀ᶠ R in atTop, ∀ v, |h'' R v| ≤ c2 := by
        filter_upwards [eventually_ge_atTop 1] with R hR v
        have e1 : 0 ≤ R := by linarith
        have e2 : R⁻¹ ≤ 1 := inv_le_of_inv_le₀ (by linarith) (by simpa using hR)
        have e3 : R ≠ 0 := by linarith
        simp only [CS.deriv_scale, CS.deriv_smul, CS.neg_apply, CS.smul_apply, smul_eq_mul, abs_neg,
          abs_mul, abs_inv, abs_eq_self.mpr e1, ge_iff_le, h'']
        convert_to _ ≤ 1 * (1 * c2)
        · simp
        apply mul_le_mul e2 ?_ (by positivity) zero_le_one
        apply mul_le_mul e2 ?_ (by positivity) zero_le_one
        simp only [CS.scale, e3, ↓reduceDIte, funscale, smul_eq_mul] ; apply mg''
      filter_upwards [hc1, hc2] with R hc1 hc2
      apply Eventually.of_forall ; intro v ; specialize hc1 v ; specialize hc2 v
      simp only [F, bound, norm_norm]
      refine (norm_add_le _ _).trans ?_ ; apply add_le_add
      · refine (norm_add_le _ _).trans ?_ ; apply add_le_add <;> simp only [Complex.norm_mul,
        Complex.norm_ofNat, norm_real, norm_eq_abs] <;> gcongr
      · simpa using mul_le_mul (hh1 R v) le_rfl (by simp) zero_le_one
    have e3 : Integrable bound volume :=
      (((f.hf.norm).const_mul _).add ((f.hf'.norm).const_mul _)).add f.hf''.norm
    have e4 : ∀ᵐ (a : ℝ), Tendsto (fun n ↦ F n a) atTop (𝓝 0) := by
      apply Eventually.of_forall ; intro v
      have evg' : g' =ᶠ[𝓝 0] 0 := by convert! ← g.zero.deriv ; exact deriv_const' _
      have evg'' : g'' =ᶠ[𝓝 0] 0 := by convert! ← evg'.deriv ; exact deriv_const' _
      refine tendsto_norm_zero.comp <| (ZeroAtFilter.add ?_ ?_).add ?_
      · have eh'' v : ∀ᶠ R in atTop, h'' R v = 0 := by
          filter_upwards [(vR v).eventually evg'', eventually_ne_atTop 0] with R hR hR'
          simp only [CS.deriv_scale, CS.deriv_smul, CS.neg_apply, CS.smul_apply, smul_eq_mul,
            neg_eq_zero, mul_eq_zero, inv_eq_zero, hR', false_or, h'']
          simp only [CS.scale, hR', ↓reduceDIte, funscale, smul_eq_mul, mul_comm R⁻¹]
          exact hR
        apply tendsto_nhds_of_eventually_eq
        filter_upwards [eh'' v] with R hR ; simp [hR]
      · have eh' v : ∀ᶠ R in atTop, h' R v = 0 := by
          filter_upwards [(vR v).eventually evg'] with R hR
          simp [g'] at hR
          simp [h', CS.deriv_scale', mul_comm R⁻¹, hR]
        apply tendsto_nhds_of_eventually_eq
        filter_upwards [eh' v] with R hR ; simp [hR]
      · simpa [h] using! ((g.tendsto_scale v).const_sub 1).ofReal.mul tendsto_const_nhds
    simpa [F] using tendsto_integral_filter_of_dominated_convergence bound e1 e2 e3 e4
end

/- Adapted from PrimeNumberTheoremAnd/Fourier.lean. -/
section
open FourierTransform Real Complex MeasureTheory Filter Topology BoundedContinuousFunction
  SchwartzMap VectorFourier BigOperators

local instance {E : Type*} : Coe (E → ℝ) (E → ℂ) := ⟨fun f n => f n⟩

section lemmas

@[simp]
theorem nnnorm_eq_of_mem_circle (z : Circle) : ‖z.val‖₊ = 1 :=
  NNReal.coe_eq_one.mp (by simp [Circle.norm_coe])

@[simp]
theorem nnnorm_circle_smul (z : Circle) (s : ℂ) : ‖z • s‖₊ = ‖s‖₊ := by
  simp [show z • s = z.val * s from rfl]

noncomputable def e (u : ℝ) : ℝ →ᵇ ℂ where
  toFun v := 𝐞 (-v * u)
  map_bounded' :=
    ⟨2, fun x y => (dist_le_norm_add_norm _ _).trans (by simp [Circle.norm_coe, one_add_one_eq_two])⟩

@[simp] lemma e_apply (u : ℝ) (v : ℝ) : e u v = 𝐞 (-v * u) := rfl

theorem hasDerivAt_e {u x : ℝ} : HasDerivAt (e u) (-2 * π * u * I * e u x) x := by
  have l2 : HasDerivAt (fun v => -v * u) (-u) x := by
    simpa only [neg_mul_comm] using hasDerivAt_mul_const (-u)
  convert! (hasDerivAt_fourierChar (-x * u)).scomp x l2 using 1
  change _ = ((-u : ℝ) : ℂ) * _ 
  simp ; ring

lemma fourierIntegral_deriv_aux2 (e : ℝ →ᵇ ℂ) {f : ℝ → ℂ} (hf : Integrable f) :
    Integrable (⇑e * f) :=
  hf.bdd_mul e.continuous.aestronglyMeasurable (ae_of_all _ e.norm_coe_le_norm)

@[simp] lemma F_neg {f : ℝ → ℂ} {u : ℝ} : 𝓕 (fun x => -f x) u = - 𝓕 f u := by
  simp [fourier_eq, integral_neg]

@[simp] lemma F_add {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (x : ℝ) :
    𝓕 (fun x => f x + g x) x = 𝓕 f x + 𝓕 g x := by
  have : Continuous fun p : ℝ × ℝ ↦ ((innerₗ ℝ) p.1) p.2 := continuous_inner
  have := fourierIntegral_add continuous_fourierChar this hf hg
  exact congr_fun this x

@[simp] lemma F_sub {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (x : ℝ) :
    𝓕 (fun x => f x - g x) x = 𝓕 f x - 𝓕 g x := by
  simpa [sub_eq_add_neg, Pi.neg_def] using F_add hf hg.neg x

@[simp] lemma F_mul {f : ℝ → ℂ} {c : ℂ} {u : ℝ} :
    𝓕 (fun x => c * f x) u = c * 𝓕 f u := by
  exact congr_fun (VectorFourier.fourierIntegral_const_smul 𝐞 _ _ f c) u

end lemmas

theorem fourierIntegral_self_add_deriv_deriv (f : W21) (u : ℝ) :
    (1 + u ^ 2) * 𝓕 (f : ℝ → ℂ) u =
      𝓕 (fun u : ℝ => (f u - (1 / (4 * π ^ 2)) * deriv^[2] f u : ℂ)) u := by
  have l1 : Integrable (fun x => (((π : ℂ) ^ 2)⁻¹ * 4⁻¹) * deriv (deriv f) x) := by
    apply Integrable.const_mul ; simpa [iteratedDeriv_succ] using f.integrable le_rfl
  have l4 : Differentiable ℝ f := f.differentiable
  have l5 : Differentiable ℝ (deriv f) := f.deriv.differentiable
  simp [f.hf, l1, add_mul, Real.fourier_deriv f.hf' l5 f.hf'', Real.fourier_deriv f.hf l4 f.hf']
  field_simp [pi_ne_zero] ; ring_nf ; simp

@[simp] lemma deriv_ofReal : deriv ofReal = fun _ => 1 := by
  ext x ; exact ((hasDerivAt_id x).ofReal_comp).deriv

lemma tendsto_intervalIntegral_zero_of_uniform_norm_bound
    {f : ℝ → ℝ → ℂ} {lo hi : ℝ} {B : ℝ → ℝ}
    (hB : Filter.Tendsto (fun T : ℝ => B T * |hi - lo|) Filter.atTop (nhds 0))
    (hf : ∀ᶠ T in Filter.atTop, ∀ x ∈ Set.uIoc lo hi, ‖f T x‖ ≤ B T) :
    Filter.Tendsto (fun T : ℝ => ∫ x in lo..hi, f T x) Filter.atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun T => norm_nonneg _) ?_ hB
  filter_upwards [hf] with T hT
  exact intervalIntegral.norm_integral_le_of_norm_le_const (fun x hx => hT x hx)

lemma tendsto_const_mul_log_add_two_div_add_two_atTop (K : ℝ) :
    Filter.Tendsto (fun T : ℝ => K * (Real.log (T + 2) / (T + 2)))
      Filter.atTop (nhds 0) := by
  have h0 : Filter.Tendsto (fun x : ℝ => Real.log x / x) Filter.atTop (nhds 0) := by
    simpa using (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by norm_num : (1 : ℝ) ≠ 0))
  have hshift : Filter.Tendsto (fun T : ℝ => Real.log (T + 2) / (T + 2))
      Filter.atTop (nhds 0) := by
    have := h0.comp (tendsto_atTop_add_const_right Filter.atTop 2 tendsto_id)
    simpa [Function.comp_def] using this
  simpa using hshift.const_mul K

lemma norm_fourier_le_integral_deriv_div
    (g : ℝ → ℂ) (hg : Integrable g) (hdiff : Differentiable ℝ g)
    (hg' : Integrable (deriv g)) {w : ℝ} (hw : w ≠ 0) :
    ‖𝓕 g w‖ ≤ (∫ x, ‖deriv g x‖ ∂volume) / ((2 * Real.pi) * |w|) := by
  have hmul :
      𝓕 (deriv g) w = (2 * Real.pi * Complex.I * (w : ℂ)) * 𝓕 g w := by
    have h := congrFun (Real.fourier_deriv hg hdiff hg') w
    simpa [smul_eq_mul, mul_assoc] using h
  have h_fourier :
      ‖𝓕 (deriv g) w‖ ≤ ∫ x, ‖deriv g x‖ ∂volume := by
    exact VectorFourier.norm_fourierIntegral_le_integral_norm 𝐞 volume (innerₗ ℝ)
      (deriv g) w
  have hleft :
      ((2 * Real.pi) * |w|) * ‖𝓕 g w‖ =
        ‖(2 * Real.pi * Complex.I * (w : ℂ)) * 𝓕 g w‖ := by
    have htwopi : ‖(2 * ↑Real.pi : ℂ)‖ = 2 * Real.pi := by
      rw [norm_mul, Complex.norm_two, Complex.norm_of_nonneg Real.pi_pos.le]
    have hwc : ‖(w : ℂ)‖ = |w| := by rw [norm_real, Real.norm_eq_abs]
    rw [norm_mul, norm_mul, norm_mul, htwopi, norm_I, hwc]
    ring
  have hmain : ((2 * Real.pi) * |w|) * ‖𝓕 g w‖ ≤ ∫ x, ‖deriv g x‖ ∂volume := by
    rw [hleft, ← hmul]
    exact h_fourier
  have hpos : 0 < (2 * Real.pi) * |w| := by
    positivity
  exact (le_div_iff₀ hpos).mpr (by simpa [mul_comm, mul_left_comm, mul_assoc] using hmain)

lemma norm_oscillatory_integral_le_integral_deriv_div
    (g : ℝ → ℂ) (hg : Integrable g) (hdiff : Differentiable ℝ g)
    (hg' : Integrable (deriv g)) {T : ℝ} (hT : 0 < T) :
    ‖∫ y, g y * exp ((T : ℂ) * Complex.I * (y : ℂ)) ∂volume‖ ≤
      (∫ x, ‖deriv g x‖ ∂volume) / T := by
  have hw : -T / (2 * Real.pi) ≠ 0 := by
    exact div_ne_zero (neg_ne_zero.mpr hT.ne') (mul_ne_zero two_ne_zero Real.pi_ne_zero)
  have hfourier := norm_fourier_le_integral_deriv_div g hg hdiff hg' hw
  have heq :
      (∫ y, g y * exp ((T : ℂ) * Complex.I * (y : ℂ)) ∂volume) =
        𝓕 g (-T / (2 * Real.pi)) := by
    rw [Real.fourier_real_eq_integral_exp_smul]
    apply integral_congr_ae
    filter_upwards with y
    rw [smul_eq_mul]
    rw [mul_comm (g y)]
    congr 1
    congr 1
    push_cast
    field_simp [Real.pi_ne_zero]
  rw [heq]
  refine hfourier.trans_eq ?_
  congr 1
  have hden : (2 * Real.pi) * |-T / (2 * Real.pi)| = T := by
    have htwopi_pos : 0 < 2 * Real.pi := by positivity
    have hneg : -T / (2 * Real.pi) < 0 := div_neg_of_neg_of_pos (neg_neg_of_pos hT) htwopi_pos
    rw [abs_of_neg hneg]
    field_simp [Real.pi_ne_zero]
  rw [hden]

lemma norm_oscillatory_integral_le_integral_deriv_div_abs
    (g : ℝ → ℂ) (hg : Integrable g) (hdiff : Differentiable ℝ g)
    (hg' : Integrable (deriv g)) {T : ℝ} (hT : T ≠ 0) :
    ‖∫ y, g y * exp ((T : ℂ) * Complex.I * (y : ℂ)) ∂volume‖ ≤
      (∫ x, ‖deriv g x‖ ∂volume) / |T| := by
  have hw : -T / (2 * Real.pi) ≠ 0 := by
    exact div_ne_zero (neg_ne_zero.mpr hT) (mul_ne_zero two_ne_zero Real.pi_ne_zero)
  have hfourier := norm_fourier_le_integral_deriv_div g hg hdiff hg' hw
  have heq :
      (∫ y, g y * exp ((T : ℂ) * Complex.I * (y : ℂ)) ∂volume) =
        𝓕 g (-T / (2 * Real.pi)) := by
    rw [Real.fourier_real_eq_integral_exp_smul]
    apply integral_congr_ae
    filter_upwards with y
    rw [smul_eq_mul]
    rw [mul_comm (g y)]
    congr 1
    congr 1
    push_cast
    field_simp [Real.pi_ne_zero]
  rw [heq]
  refine hfourier.trans_eq ?_
  congr 1
  have hden : (2 * Real.pi) * |-T / (2 * Real.pi)| = |T| := by
    have htwopi_pos : 0 < 2 * Real.pi := by positivity
    rw [abs_div, abs_neg, abs_of_pos htwopi_pos]
    field_simp [Real.pi_ne_zero]
  rw [hden]
end

/- Adapted from PrimeNumberTheoremAnd/Mathlib/Analysis/SpecialFunctions/Log/Basic.lean. -/
section
open Filter Real

theorem Real.tendsto_pow_log_div_pow_atTop (a : ℝ) (b : ℝ) (ha : 0 < a) :
    Filter.Tendsto (fun x ↦ log x ^ b / x^a) Filter.atTop (nhds 0) := by
  apply Asymptotics.isLittleO_iff_tendsto' _|>.mp <| isLittleO_log_rpow_rpow_atTop _ ha
  filter_upwards [eventually_gt_atTop 0] with x hx
  intro h
  rw [rpow_eq_zero hx.le ha.ne.symm] at h
  exfalso
  linarith
end

/- Adapted from PrimeNumberTheoremAnd/Rectangle.lean. -/
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

/- Adapted from PrimeNumberTheoremAnd/ResidueCalcOnRectangles.lean. -/
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

omit [NormedSpace ℂ E] in
theorem ContinuousOn.rectangleBorder_integrable (hf : ContinuousOn f (RectangleBorder z w)) :
    RectangleBorderIntegrable f z w :=
  ⟨(hf.comp (by fun_prop) (mapsTo_rectangleBorder_left_im z w)).intervalIntegrable,
    (hf.comp (by fun_prop) (mapsTo_rectangleBorder_right_im z w)).intervalIntegrable,
    (hf.comp (by fun_prop) (mapsTo_rectangleBorder_right_re z w)).intervalIntegrable,
    (hf.comp (by fun_prop) (mapsTo_rectangleBorder_left_re z w)).intervalIntegrable⟩

omit [NormedSpace ℂ E] in
theorem ContinuousOn.rectangleBorderIntegrable (hf : ContinuousOn f (Rectangle z w)) :
    RectangleBorderIntegrable f z w :=
  ContinuousOn.rectangleBorder_integrable (hf.mono (rectangleBorder_subset_rectangle z w))

omit [NormedSpace ℂ E] in
theorem ContinuousOn.rectangleBorderNoPIntegrable
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
  linear_combination (norm := abel) h₁ + h₂ + h₃ + h₄ + h₅ + h₆ + h₇ + h₈

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
end

/- Adapted from PrimeNumberTheoremAnd/EulerMaclaurin.lean. -/
section
open Finset Interval MeasureTheory

variable {𝕜 : Type*} [RCLike 𝕜] {f : ℝ → 𝕜} {a b : ℝ}

noncomputable def B1 (x : ℝ) : ℝ := x - ⌊x⌋₊ - 1 / 2

lemma aestronglyMeasurable_B1 : AEStronglyMeasurable B1 := by
  unfold B1
  fun_prop

lemma abs_B1_le_half {x : ℝ} (hx : 0 ≤ x) : |B1 x| ≤ 1 / 2 := by
  unfold B1
  refine abs_le.mpr ⟨?_, ?_⟩
  · grind [Nat.floor_le hx]
  · grind [Nat.lt_succ_floor x]

lemma integral_deriv_mul_add_const (c : 𝕜) (hab : a ≤ b) (h_int : IntervalIntegrable (deriv f) volume a b)
    (hf_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t) :
    ∫ t in a..b, (t + c) * deriv f t = (b + c) * f b - (a + c) * f a - ∫ t in a..b, f t := by
  rw [← Set.uIcc_of_le hab] at hf_diff
  have : ∀ t ∈ [[a, b]], HasDerivAt (fun (t : ℝ) ↦ t + c) 1 t := by
    intro t ht
    simp only [hasDerivAt_add_const_iff]
    convert! ContinuousLinearMap.hasDerivAt (RCLike.ofRealCLM (K := 𝕜)) using 1
    simp
  replace hf_diff := fun t ht ↦ (hf_diff t ht).hasDerivAt
  rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul this hf_diff (by simp) h_int]
  simp

lemma intervalIntegrable_deriv_mul_B1 (ha : 0 ≤ a) (hab : a ≤ b) (h_cont : ContinuousOn (deriv f) [[a, b]]) :
    IntervalIntegrable (fun t ↦ deriv f t * B1 t) volume a b := by
  refine IntervalIntegrable.continuousOn_mul ?_ h_cont
  rw [intervalIntegrable_iff']
  apply MeasureTheory.Measure.integrableOn_of_bounded (by simp) (RCLike.continuous_ofReal.comp_aestronglyMeasurable aestronglyMeasurable_B1) (M := 1 / 2)
  filter_upwards [self_mem_ae_restrict (by measurability)] with x hx
  rw [Set.uIcc_of_le hab, Set.mem_Icc] at hx
  norm_cast
  exact abs_B1_le_half (by linarith)

lemma integral_deriv_mul_floor_add_one (ha : 0 ≤ a) (hab : a ≤ b)
    (hf_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t) (h_cont : ContinuousOn (deriv f) [[a, b]]) :
    ∫ t in a..b, deriv f t * (⌊t⌋₊ + 1) = (b + 1 / 2) * f b - (a + 1 / 2) * f a - (∫ t in a..b, f t) - ∫ t in a..b, deriv f t * B1 t := by
  calc
  _ = ∫ t in a..b, (deriv f t * (t + 1 / 2) -deriv f t * B1 t) := by
    congr
    ext
    simp only [B1]
    push_cast
    ring
  _ = (∫ t in a..b, deriv f t * (t + 1 / 2)) - ∫ t in a..b, deriv f t * B1 t := by
    exact intervalIntegral.integral_sub (ContinuousOn.intervalIntegrable (by fun_prop)) (intervalIntegrable_deriv_mul_B1 ha hab h_cont)
  _ = _ := by
    conv => lhs; arg 1; arg 1; ext; rw [mul_comm]
    rw [integral_deriv_mul_add_const _ hab h_cont.intervalIntegrable hf_diff]

theorem sum_eq_integral_add_integral_deriv (ha : 0 ≤ a) (hab : a ≤ b)
    (hf_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t)
    (h_cont : ContinuousOn (deriv f) [[a, b]]) :
    ∑ k ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, f k =
      f a * B1 a - f b * B1 b + (∫ t in a..b, f t) + ∫ t in a..b, deriv f t * B1 t  := by
  have := sum_mul_eq_sub_sub_integral_mul (fun _ ↦ 1) ha hab hf_diff (Set.uIcc_of_le hab ▸ h_cont).integrableOn_Icc
  simp only [mul_one, sum_const, Nat.card_Icc, tsub_zero, nsmul_eq_mul, Nat.cast_add,
    Nat.cast_one] at this
  rw [this, ← intervalIntegral.integral_of_le hab]
  rw [integral_deriv_mul_floor_add_one ha hab hf_diff h_cont]
  unfold B1
  push_cast
  ring
end

/- Adapted from PrimeNumberTheoremAnd/ZetaBounds.lean. -/
section
open Complex Topology Filter Interval Set Asymptotics

lemma div_cpow_eq_cpow_neg (a x s : ℂ) : a / x ^ s = a * x ^ (-s) := by
  rw [div_eq_mul_inv, cpow_neg]

lemma one_div_cpow_eq_cpow_neg (x s : ℂ) : 1 / x ^ s = x ^ (-s) := by
  convert div_cpow_eq_cpow_neg 1 x s using 1; simp

lemma div_rpow_eq_rpow_neg (a x s : ℝ) (hx : 0 ≤ x) : a / x ^ s = a * x ^ (-s) := by
  rw [div_eq_mul_inv, Real.rpow_neg hx]

lemma div_rpow_neg_eq_rpow_div {x y s : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x ^ (-s) / y ^ (-s) = (y / x) ^ s := by
  rw [div_eq_mul_inv, Real.rpow_neg hx, Real.rpow_neg hy, Real.div_rpow hy hx]; field_simp

lemma div_rpow_eq_rpow_div_neg {x y s : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x ^ s / y ^ s = (y / x) ^ (-s) := by
  convert div_rpow_neg_eq_rpow_div (s := -s) hx hy using 1; simp only [neg_neg]

theorem ResidueOfTendsTo {f : ℂ → ℂ} {p : ℂ} {U : Set ℂ}
    (hU : U ∈ 𝓝 p)
    (hf : HolomorphicOn f (U \ {p}))
    {A : ℂ}
    (h_limit : Tendsto (fun s ↦ (s - p) * f s) (𝓝[≠] p) (𝓝 A)) :
    ∃ V ∈ 𝓝 p,
    BddAbove (norm ∘ (f - fun s ↦ A * (s - p)⁻¹) '' (V \ {p})) := by
  
  have h_event : ∀ᶠ s in 𝓝[≠] p, ‖(s - p) * f s - A‖ < 1 := by
    simp_rw [← dist_eq_norm_sub]
    exact h_limit.eventually (Metric.ball_mem_nhds _ (by norm_num))
  have h_event_nhds :
      ∀ᶠ s in 𝓝 p, s ≠ p → ‖(s - p) * f s - A‖ < 1 := by
    exact (eventually_nhdsWithin_iff).1 h_event
  rcases (eventually_nhds_iff.1 h_event_nhds) with ⟨V₀, hV₀_mem, hV₀_prop⟩
  have h_bound :
      ∀ s, s ∈ V₀ \ {p} → ‖(s - p) * f s‖ ≤ ‖A‖ + 1 := by
    intro s hs
    rcases hs with ⟨hV₀, hsne⟩
    calc ‖(s - p) * f s‖ = ‖((s - p) * f s - A) + A‖ := by
          ring_nf
        _ ≤ ‖(s - p) * f s - A‖ + ‖A‖ := norm_add_le ((s - p) * f s - A) A
        _ ≤ 1 + ‖A‖ := add_le_add_left (le_of_lt (hV₀_mem s hV₀ hsne)) ‖A‖
        _ = ‖A‖ + 1 := add_comm 1 ‖A‖
  have h_bdd :
      BddAbove (norm ∘ (fun s ↦ (s - p) * f s) '' (V₀ \ {p})) := by
    refine ⟨‖A‖ + 1, ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    exact h_bound s hs
  
  set W : Set ℂ := V₀ ∩ U with hW_def
  have hW_mem : (W : Set ℂ) ∈ 𝓝 p := inter_mem (IsOpen.mem_nhds hV₀_prop.1 hV₀_prop.2) hU
  have h_subset_V₀ : (W \ {p}) ⊆ (V₀ \ {p}) := by
    intro z hz; exact ⟨hz.1.1, hz.2⟩
  have h_prod_holo : HolomorphicOn (fun z ↦ (z - p) * f z) (W \ {p}) := by
    have h_id : HolomorphicOn (fun z : ℂ ↦ z - p) (W \ {p}) :=
      Differentiable.differentiableOn (Differentiable.sub_const differentiable_fun_id p)
    have hfW : HolomorphicOn f (W \ {p}) := by
      apply hf.mono
      exact Set.sdiff_subset_sdiff_left inter_subset_right
    simpa using! h_id.mul hfW
  have h_bdd_W : BddAbove (norm ∘ (fun s ↦ (s - p) * f s) '' (W \ {p})) :=
    h_bdd.mono (image_mono h_subset_V₀)
  
  obtain ⟨g, hg_holo, hg_eq⟩ :=
    existsDifferentiableOn_of_bddAbove hW_mem h_prod_holo h_bdd_W
  have h_event_eq :
      (fun z ↦ g z) =ᶠ[𝓝[≠] p] fun z ↦ (z - p) * f z := by
    have hW_diff_mem : (W \ {p} : Set ℂ) ∈ 𝓝[≠] p :=
      sdiff_mem_nhdsWithin_compl hW_mem {p}
    exact (hg_eq.eventuallyEq_of_mem hW_diff_mem).symm
  have h_tendsto_gA : Tendsto g (𝓝[≠] p) (𝓝 A) :=
      h_limit.congr' (id (EventuallyEq.symm h_event_eq))
  have hpW : p ∈ W := by
    exact mem_of_mem_nhds hW_mem
  have h_cont_g : ContinuousAt g p := by
    apply (hg_holo.continuousOn.continuousWithinAt hpW).continuousAt hW_mem
  have h_tendsto_gp : Tendsto g (𝓝[≠] p) (𝓝 (g p)) :=
    h_cont_g.tendsto.mono_left inf_le_left
  have g_p_eq : g p = A :=
    tendsto_nhds_unique' (NormedField.nhdsNE_neBot p) h_tendsto_gp h_tendsto_gA
  let q : ℂ → ℂ := fun z ↦ (g z - A) / (z - p)
  have h_deriv : HasDerivAt g (deriv g p) p := by
    exact DifferentiableOn.hasDerivAt hg_holo hW_mem
  have h_q_limit : Tendsto q (𝓝[≠] p) (𝓝 (deriv g p)) := by
    rw [hasDerivAt_iff_tendsto_slope] at h_deriv
    unfold slope at h_deriv
    simp only [vsub_eq_sub, smul_eq_mul, inv_mul_eq_div, g_p_eq] at h_deriv
    exact h_deriv
  have h_event_q : ∀ᶠ z in 𝓝[≠] p, ‖q z - deriv g p‖ < 1 := by
    simp_rw [← dist_eq_norm_sub]
    exact h_q_limit.eventually (Metric.ball_mem_nhds _ (by norm_num))
  have h_event_q_nhds : ∀ᶠ z in 𝓝 p, z ≠ p → ‖q z - deriv g p‖ < 1 := by
    simpa using (eventually_nhdsWithin_iff).1 h_event_q
  rcases (eventually_nhds_iff.1 h_event_q_nhds) with
    ⟨V₁, hV₁_mem, hV₁_prop⟩
  have h_q_bound :
      ∀ z, z ∈ V₁ \ {p} → ‖q z‖ ≤ ‖deriv g p‖ + 1 := by
    intro z hz
    rcases hz with ⟨hV₁, hz_ne⟩
    calc ‖q z‖ = ‖(q z - deriv g p) + (deriv g p)‖ := by
          ring_nf
        _ ≤ ‖q z - deriv g p‖ + ‖deriv g p‖ := norm_add_le (q z - deriv g p) (deriv g p)
        _ ≤ 1 + ‖deriv g p‖  := add_le_add_left (le_of_lt (hV₁_mem z hV₁ hz_ne)) ‖deriv g p‖
        _ = ‖deriv g p‖ + 1 := add_comm 1 ‖deriv g p‖
  
  have h_eq_diff :
      EqOn (fun z ↦ f z - A * (z - p)⁻¹) q (W \ {p}) := by
    intro z hz
    simp only
    have hz_ne : (z - p) ≠ 0 := sub_ne_zero.mpr hz.2
    have hgz : g z = (z - p) * f z := by
      exact id (EqOn.symm hg_eq) hz
    simp only [hgz, q]
    field_simp
  apply IsBigO_to_BddAbove
  rw [isBigO_iff]
  use ‖deriv g p‖ + 1
  apply eventually_nhdsWithin_iff.mpr
  filter_upwards [IsOpen.mem_nhds hV₁_prop.1 hV₁_prop.2, hW_mem] with z hV₁ hW z_ne_p
  specialize h_eq_diff ⟨ hW, z_ne_p⟩
  simp only [Pi.sub_apply, Pi.one_apply, one_mem, CStarRing.norm_of_mem_unitary,
    mul_one] at h_eq_diff ⊢
  rw [h_eq_diff]
  exact h_q_bound _ ⟨hV₁, z_ne_p⟩

theorem analyticAt_riemannZeta {s : ℂ} (s_ne_one : s ≠ 1) :
  AnalyticAt ℂ riemannZeta s := by
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  filter_upwards [eventually_ne_nhds s_ne_one] with z hz using differentiableAt_riemannZeta hz

theorem differentiableAt_deriv_riemannZeta {s : ℂ} (s_ne_one : s ≠ 1) :
    DifferentiableAt ℂ (deriv riemannZeta) s := by
  exact (analyticAt_riemannZeta s_ne_one).deriv.differentiableAt

theorem riemannZetaResidue :
    ∃ U ∈ 𝓝 1, BddAbove (norm ∘ (riemannZeta - (fun s ↦ (s - 1)⁻¹)) '' (U \ {1})) := by
  have zeta_holc : HolomorphicOn riemannZeta (univ \ {1}) := by
    intro y hy
    exact DifferentiableAt.differentiableWithinAt <| differentiableAt_riemannZeta hy.2
  convert ResidueOfTendsTo univ_mem zeta_holc riemannZeta_residue_one using 6
  simp

theorem deriv_eqOn_of_eqOn_punctured (f g : ℂ → ℂ) (U : Set ℂ) (p : ℂ)
    (hU_open : IsOpen U)
    (h_eq : EqOn f g (U \ {p})) :
    EqOn (deriv f) (deriv g) (U \ {p}) := by
  intro x hx
  apply EventuallyEq.deriv_eq
  filter_upwards [IsOpen.mem_nhds (hU_open.sdiff isClosed_singleton) hx] with t ht using h_eq ht

theorem analytic_deriv_bounded_near_point
    (f : ℂ → ℂ) {U : Set ℂ} {p : ℂ} (hU : IsOpen U) (hp : p ∈ U) (hf : HolomorphicOn f U) :
    (deriv f) =O[𝓝[≠] p] (1 : ℂ → ℂ) := by
  have U_in_filter : U ∈ 𝓝 p := by
    exact IsOpen.mem_nhds hU hp
  have T := (analyticOn_iff_differentiableOn hU).mpr hf
  have T2 : ContDiffOn ℂ 1 f U :=
      DifferentiableOn.contDiffOn hf hU
  have T3 : ContinuousOn (fun x ↦ ((deriv f) x)) U := by
    apply T2.continuousOn_deriv_of_isOpen hU (by simp)
  have T4 := T3.continuousAt U_in_filter
  have T5 : (deriv f) =O[𝓝 p] (1 : ℂ → ℂ) :=
    T4.norm.isBoundedUnder_le.isBigO_one ℂ
  exact Asymptotics.IsBigO.mono T5 inf_le_left

theorem derivative_const_plus_product {g : ℂ → ℂ} (A p x : ℂ) (hg : DifferentiableAt ℂ g x) :
    deriv ((fun _ ↦ A) + g * fun s ↦ s - p) x = deriv g x * (x - p) + g x := by
  rw [deriv_add (by fun_prop) (by fun_prop), deriv_const, deriv_mul hg (by fun_prop)]
  simp

lemma deriv_inv_sub {x p : ℂ} (hp : x ≠ p) :
  deriv (fun z => (z - p)⁻¹) x =  -((x - p) ^ 2)⁻¹ := by
  rw [deriv_fun_inv'' (by fun_prop) (by grind)]
  simp
  field

theorem deriv_f_minus_A_inv_sub_clean (f : ℂ → ℂ) (A x p : ℂ)
    (hf : DifferentiableAt ℂ f x) (hp : x ≠ p) :
    deriv (f  - (fun z ↦ A * (z - p)⁻¹)) x = deriv f x + A * ((x - p) ^ 2)⁻¹ := by
  have h1 : DifferentiableAt ℂ (fun z => (z - p)⁻¹) x := by
    fun_prop (disch := grind)
  rw [deriv_sub hf (h1.const_mul A), deriv_const_mul A h1, deriv_inv_sub hp]
  ring

theorem nonZeroOfBddAbove {f : ℂ → ℂ} {p : ℂ} {U : Set ℂ}
    (U_in_nhds : U ∈ 𝓝 p) {A : ℂ} (A_ne_zero : A ≠ 0)
    (f_near_p : BddAbove (norm ∘ (f - fun s ↦ A * (s - p)⁻¹) '' (U \ {p}))) :
    ∃ V ∈ 𝓝 p, IsOpen V ∧ ∀ s ∈ V \ {p}, f s ≠ 0 := by

  have h_decomp : ∀ s, f s = (f s - A * (s - p)⁻¹) + A * (s - p)⁻¹ := by
    intro s
    ring
  
  obtain ⟨M, hM⟩ := f_near_p

  have A_norm_pos : 0 < ‖A‖ := norm_pos_iff.mpr A_ne_zero
  
  let δ := ‖A‖ / (‖M‖ + 1)
  have δ_pos : 0 < δ := by
    refine div_pos A_norm_pos (add_pos_of_nonneg_of_pos (norm_nonneg M) one_pos)
  
  obtain ⟨V, hV_open, hV_mem, hV_sub⟩ : ∃ V, IsOpen V ∧ p ∈ V ∧ V ⊆ U ∩ Metric.ball p δ := by
    
    obtain ⟨W, hW_sub, hW_open, hW_mem⟩ := mem_nhds_iff.mp U_in_nhds
    let V := W ∩ Metric.ball p δ
    have VNp : V ∈ 𝓝 p := (𝓝 p).inter_mem (IsOpen.mem_nhds hW_open hW_mem)
      (Metric.ball_mem_nhds p δ_pos)
    exact ⟨V, IsOpen.inter hW_open Metric.isOpen_ball, mem_of_mem_nhds VNp,
      inter_subset_inter_left _ hW_sub⟩
  use V, mem_nhds_iff.mpr ⟨V, subset_refl V, hV_open, hV_mem⟩, hV_open
  
  intro s hs
  have hs_in_U : s ∈ U := hV_sub hs.1 |>.1
  have hs_near_p : dist s p < δ := hV_sub hs.1 |>.2
  have hs_ne_p : s ≠ p := hs.2
  
  rw [h_decomp s]
  
  have bound_first : ‖f s - A * (s - p)⁻¹‖ ≤ M := by
    apply hM
    exact ⟨s, ⟨hs_in_U, hs_ne_p⟩, rfl⟩
  
  have large_second : ‖M‖ + 1 < ‖A * (s - p)⁻¹‖ := by
    rw [norm_mul, norm_inv, ← div_eq_mul_inv]
    rw [lt_div_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hs_ne_p))]
    rw [mul_comm, ← lt_div_iff₀ (add_pos_of_nonneg_of_pos (norm_nonneg M) one_pos)]
    rw [dist_eq_norm_sub] at hs_near_p
    exact hs_near_p
  
  by_contra h_zero
  
  rw [add_eq_zero_iff_eq_neg] at h_zero
  rw [h_zero, norm_neg] at bound_first
  
  have : ‖M‖ + 1 < ‖M‖ := (lt_of_lt_of_le (lt_of_lt_of_le large_second bound_first)
    (Real.le_norm_self M))
  norm_num at this

theorem logDerivResidue' {f : ℂ → ℂ} {p : ℂ} {U : Set ℂ}
    (U_is_open : IsOpen U)
    (non_zero : ∀ x ∈ U \ {p}, f x ≠ 0)
    (holc : HolomorphicOn f (U \ {p}))
    (U_in_nhds : U ∈ 𝓝 p) {A : ℂ} (A_ne_zero : A ≠ 0)
    (f_near_p : BddAbove (norm ∘ (f - fun s ↦ A * (s - p)⁻¹) '' (U \ {p}))) :
    (deriv f * f⁻¹ + (fun s ↦ (s - p)⁻¹)) =O[𝓝[≠] p] (1 : ℂ → ℂ) := by

  have simpleHolo : HolomorphicOn (fun s ↦ A / (s - p)) (U \ {p}) := by
    apply DifferentiableOn.mono (t := {p}ᶜ)
    · apply DifferentiableOn.div
      · exact differentiableOn_const _
      · exact DifferentiableOn.sub differentiableOn_id (differentiableOn_const _)
      · exact fun x hx => by rw [sub_ne_zero]; exact hx
    · rintro s ⟨_, hs⟩ ; exact hs

  have f_minus_pole_is_holomorphic : HolomorphicOn (f - (fun s ↦ A * (s - p)⁻¹)) (U \ {p}) := by
    exact (DifferentiableOn.sub_iff_right holc).mpr simpleHolo

  let ⟨g, ⟨g_is_holomorphic, g_is_f_minus_pole⟩⟩ := existsDifferentiableOn_of_bddAbove
    U_in_nhds f_minus_pole_is_holomorphic f_near_p

  let h := (fun _ ↦ A) + g * (fun (s : ℂ) ↦ (s - p))

  have linear_is_holomorphic : HolomorphicOn (fun (s : ℂ ) ↦ (s - p)) U := by
    exact DifferentiableOn.sub_const differentiableOn_id p

  have h_is_holomorphic : HolomorphicOn h U := by
    have T := DifferentiableOn.mul g_is_holomorphic linear_is_holomorphic
    exact DifferentiableOn.const_add A T

  have h_continuous : ContinuousOn h U :=
    by exact DifferentiableOn.continuousOn h_is_holomorphic

  have deriv_h_identity : ∀x ∈ (U \ {p}), (deriv h) x = f x + (deriv f x) * (x - p) := by
    intro x x_in_u_not_p
    have x_in_u : x ∈ U := by exact Set.mem_of_mem_sdiff x_in_u_not_p
    have x_not_p : x ≠ p := by
      exact ((Set.mem_sdiff x).mp x_in_u_not_p).2

    have weird : U ∈ 𝓝 x := by
      exact IsOpen.mem_nhds (U_is_open) (x_in_u)

    rw [derivative_const_plus_product, ← g_is_f_minus_pole x_in_u_not_p,
      ← deriv_eqOn_of_eqOn_punctured _ _ U p U_is_open g_is_f_minus_pole x_in_u_not_p,
      deriv_f_minus_A_inv_sub_clean]
    · simp only [Pi.sub_apply]
      have := sub_ne_zero_of_ne x_not_p
      field_simp
      ring
    · apply holc.differentiableAt
      exact Filter.inter_mem weird <| compl_singleton_mem_nhds x_not_p
    · exact x_not_p
    · exact g_is_holomorphic.differentiableAt weird
  have h_identity : ∀x ∈ (U \ {p}), h x = (f x) * (x - p)  := by
    intro x x_in_u_not_p
    have hyp_x_not_p : x ≠ p := by
      exact ((Set.mem_sdiff x).mp x_in_u_not_p).2
    simp only [h, Pi.add_apply, Pi.mul_apply]
    rw [← g_is_f_minus_pole x_in_u_not_p]
    simp only [Pi.sub_apply]
    field [sub_ne_zero.mpr hyp_x_not_p]
  have log_deriv_f_plus_pole_equal_log_deriv_h :
      EqOn (deriv f * f⁻¹ + fun s ↦ (s - p)⁻¹) ((deriv h) * h⁻¹) (U \ {p}) := by
    simp only [Set.mem_sdiff, mem_singleton_iff, ne_eq, and_imp, Function.comp_apply, Pi.sub_apply,
      DifferentiableOn.sub_iff_right, differentiableOn_const, DifferentiableOn.fun_sub_iff_left,
      holc] at *
    intro x hyp_x
    have x_not_p : x ≠ p := by
      exact ((Set.mem_sdiff x).mp hyp_x).2
    have x_in_u : x ∈ U := by exact Set.mem_of_mem_sdiff hyp_x
    simp only [Pi.add_apply, Pi.mul_apply, Pi.inv_apply]
    rw [deriv_h_identity _ x_in_u x_not_p, h_identity _ x_in_u x_not_p]

    field [sub_ne_zero.mpr x_not_p, non_zero x (x_in_u) x_not_p]
  have h_inv_bounded :
      h⁻¹ =O[𝓝[≠] p] (1 : ℂ → ℂ) := by
    have : ContinuousAt h⁻¹ p := by
      apply ContinuousOn.continuousAt h_continuous U_in_nhds |>.inv₀
      simp [h, A_ne_zero]
    exact Asymptotics.IsBigO.mono (this.norm.isBoundedUnder_le.isBigO_one ℂ) inf_le_left

  have h_deriv_bounded :
        (deriv h) =O[𝓝[≠] p] (1 : ℂ → ℂ) :=
          analytic_deriv_bounded_near_point h U_is_open
            (by exact mem_of_mem_nhds U_in_nhds) h_is_holomorphic

  have h_log_deriv_bounded :
    ((deriv h) * h⁻¹) =O[𝓝[≠] p] (1 : ℂ → ℂ)  := by
      have T := Asymptotics.IsBigO.mul h_deriv_bounded h_inv_bounded
      exact IsBigO.of_const_mul_right T

  have u_not_p_in_filter : U \ {p} ∈ 𝓝[≠] p := by
    exact sdiff_mem_nhdsWithin_compl U_in_nhds {p}
  have T := Set.EqOn.eventuallyEq_of_mem log_deriv_f_plus_pole_equal_log_deriv_h u_not_p_in_filter
  exact EventuallyEq.trans_isBigO T h_log_deriv_bounded

theorem logDerivResidue {f : ℂ → ℂ} {p : ℂ} {U : Set ℂ}
    (non_zero : ∀ x ∈ U \ {p}, f x ≠ 0)
    (holc : HolomorphicOn f (U \ {p}))
    (U_in_nhds : U ∈ 𝓝 p) {A : ℂ} (A_ne_zero : A ≠ 0)
    (f_near_p : BddAbove (norm ∘ (f - fun s ↦ A * (s - p)⁻¹) '' (U \ {p}))) :
    (deriv f * f⁻¹ + (fun s ↦ (s - p)⁻¹)) =O[𝓝[≠] p] (1 : ℂ → ℂ) :=
    by
      let ⟨U', ⟨a,b,c⟩⟩ := mem_nhds_iff.mp U_in_nhds
      have W : (U' \ {p}) ⊆ U' := by
        exact Set.sdiff_subset

      have T : (U' \ {p}) ⊆ (U \ {p}) := by
        exact Set.sdiff_subset_sdiff a (subset_refl _)

      refine logDerivResidue' b ?_ ?_ (IsOpen.mem_nhds b c) A_ne_zero ?_
      · intro x hyp_x
        exact non_zero x <| T hyp_x
      · exact DifferentiableOn.mono holc T
      · exact (f_near_p.mono (image_mono (Set.sdiff_subset_sdiff a (subset_refl _))))

lemma BddAbove_to_IsBigO {f : ℂ → ℂ} {p : ℂ}
    {U : Set ℂ} (hU : U ∈ 𝓝 p) (bdd : BddAbove (norm ∘ f '' (U \ {p}))) :
    f =O[𝓝[≠] p] (1 : ℂ → ℂ)  := by
  dsimp [BddAbove, upperBounds] at bdd
  rcases bdd with ⟨C, hC⟩

  have h : ∀ x ∈ U \ {p}, ‖f x‖ ≤ C := by
    intro x hx
    have fx_is_norm : ‖f x‖ ∈ norm ∘ f ''(U \ {p}) := by
      exact ⟨x, hx, rfl⟩
    exact hC fx_is_norm

  rw [Asymptotics.isBigO_iff]
  use C
  rw [eventually_nhdsWithin_iff]
  simp only [Set.mem_sdiff, mem_singleton_iff, and_imp, mem_compl_iff, Pi.one_apply, one_mem,
    CStarRing.norm_of_mem_unitary, mul_one] at h ⊢
  filter_upwards [hU] using h

theorem logDerivResidue'' {f : ℂ → ℂ} {p : ℂ} {U : Set ℂ}
    (non_zero : ∀ x ∈ U \ {p}, f x ≠ 0)
    (holc : HolomorphicOn f (U \ {p}))
    (U_in_nhds : U ∈ 𝓝 p) {A : ℂ} (A_ne_zero : A ≠ 0)
    (f_near_p : BddAbove (norm ∘ (f - fun s ↦ A * (s - p)⁻¹) '' (U \ {p}))) :
    ∃ V ∈ 𝓝 p, BddAbove (norm ∘ (deriv f * f⁻¹ + (fun s ↦ (s - p)⁻¹)) '' (V \ {p})) := by
  apply IsBigO_to_BddAbove
  exact logDerivResidue non_zero holc U_in_nhds A_ne_zero f_near_p

theorem ResidueMult {f g : ℂ → ℂ} {p : ℂ} {U : Set ℂ}
    (g_holc : HolomorphicOn g U) (U_in_nhds : U ∈ 𝓝 p) {A : ℂ}
    (f_near_p : (f - (fun s ↦ A * (s - p)⁻¹)) =O[𝓝[≠] p] (1 : ℂ → ℂ)) :
    (f * g - (fun s ↦ A * g p * (s - p)⁻¹)) =O[𝓝[≠] p] (1 : ℂ → ℂ) := by
  
  have : (f * g - fun s ↦ A * g p * (s - p)⁻¹)
      = (f - A • fun s ↦ (s - p)⁻¹) * g + fun s ↦ (A * (g s - g p) / (s - p)) := by
    ext; simp; ring
  
  rw[this]
  have p_in_U : p ∈ U := mem_of_mem_nhds U_in_nhds
  refine Asymptotics.IsBigO.add ?_ ?_
  · rw[← mul_one (1 : ℂ → ℂ)]
    refine Asymptotics.IsBigO.mul f_near_p ?_
    
    have g_cont : ContinuousAt g p := by
      
      exact (g_holc.continuousOn.continuousWithinAt p_in_U).continuousAt U_in_nhds
    
    have := g_cont.norm.isBoundedUnder_le.isBigO_one ℂ
    exact IsBigO.mono this inf_le_left
  · 

    suffices (fun s ↦ A * ((s - p)⁻¹ * (g s - g p))) =O[𝓝[≠] p] 1 by
      convert! this using 2
      rw[div_eq_mul_inv]
      ring
    apply Asymptotics.IsBigO.const_mul_left

    have g_diff : HasDerivAt g (deriv g p) p :=
        (DifferentiableOn.differentiableAt g_holc U_in_nhds).hasDerivAt

    rw [hasDerivAt_iff_isLittleO] at g_diff
    apply Asymptotics.IsLittleO.isBigO at g_diff
    have : (fun x' ↦ deriv g p * (x' - p)) =O[𝓝 p] fun x' ↦ x' - p := by
      apply Asymptotics.IsBigO.const_mul_left
      exact Asymptotics.isBigO_refl (fun x ↦ x - p) (𝓝 p)
    have h1 := g_diff.add this
    have h2 : (fun x ↦ g x - g p) =O[𝓝 p] fun x' ↦ x' - p := by
      convert! h1 using 2
      simp
      ring
    refine (Asymptotics.isBigO_mul_iff_isBigO_div ?_).mpr ?_
    · filter_upwards [self_mem_nhdsWithin] with x hx
      simp only [mem_compl_iff, mem_singleton_iff] at hx
      exact inv_ne_zero (sub_ne_zero.mpr hx)
    · simp only [div_inv_eq_mul]
      refine Asymptotics.IsBigO.mono ?_ inf_le_left
      simpa

theorem riemannZetaLogDerivResidue :
    ∃ U ∈ 𝓝 1, BddAbove (norm ∘ (-((deriv riemannZeta) / riemannZeta) - (fun s ↦ (s - 1)⁻¹)) '' (U \ {1})) := by
  obtain ⟨U,U_in_nhds, hU⟩ := riemannZetaResidue
  have hU' : BddAbove (norm ∘ (riemannZeta - fun s ↦ 1 * (s - 1)⁻¹) '' (U \ {1})) := by
    simp only [Function.comp_apply, Pi.sub_apply, one_mul] at hU ⊢
    exact hU
  obtain ⟨V,V_in_nhds, V_is_open, hV⟩ := nonZeroOfBddAbove U_in_nhds one_ne_zero hU'
  let W := V ∩ interior U
  have hW : ∀ s ∈ W \ {1}, riemannZeta s ≠ 0 := by
    intro s hs
    have s_in_V_diff : s ∈ V \ {1} := ⟨hs.1.1, hs.2⟩
    exact hV s s_in_V_diff
  have ζ_holc: HolomorphicOn riemannZeta (W \ {1}) := by
    intro y hy
    simp only [Set.mem_sdiff, mem_singleton_iff] at hy
    refine DifferentiableAt.differentiableWithinAt ?_
    apply differentiableAt_riemannZeta hy.2
  have W_in_nhds : W ∈ 𝓝 1 := by
    refine inter_mem V_in_nhds ?_
    exact interior_mem_nhds.mpr U_in_nhds
  have := logDerivResidue'' hW ζ_holc W_in_nhds one_ne_zero
  have HW : BddAbove (norm ∘ (riemannZeta - fun s ↦ (s - 1)⁻¹) '' (W \ {1})) := by
    obtain ⟨c, hc⟩ := bddAbove_def.mp hU
    apply bddAbove_def.mpr
    use c
    rintro y ⟨x, x_in_W, fxy⟩
    apply hc
    exact ⟨x, ⟨interior_subset x_in_W.1.2, x_in_W.2⟩, fxy⟩
  simp only [one_mul] at this
  have aux: ∀ a, ‖-(deriv riemannZeta a / riemannZeta a) - (a - 1)⁻¹‖ = ‖(deriv riemannZeta a / riemannZeta a) + (a - 1)⁻¹‖ := by
    intro a
    calc ‖-(deriv riemannZeta a / riemannZeta a) - (a - 1)⁻¹‖
         = ‖-((deriv riemannZeta a / riemannZeta a) + (a - 1)⁻¹)‖ := by ring_nf
       _ = ‖(deriv riemannZeta a / riemannZeta a) + (a - 1)⁻¹‖ := by rw [norm_neg]
  simp only [Function.comp_apply, Pi.sub_apply] at hU
  simp only [Function.comp_apply, Pi.sub_apply, Pi.neg_apply, Pi.div_apply, aux]
  apply this HW

theorem riemannZetaLogDerivResidueBigO :
    (-(deriv riemannZeta) / riemannZeta - fun z ↦ (z - 1)⁻¹) =O[nhdsWithin 1 {1}ᶜ] (1 : ℂ → ℂ) := by
  obtain ⟨U, hU, bdd⟩ := riemannZetaLogDerivResidue
  convert BddAbove_to_IsBigO hU bdd using 2
  rw [neg_div]

noncomputable def riemannZeta0 (N : ℕ) (s : ℂ) : ℂ :=
  (∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s) +
  (- N ^ (1 - s)) / (1 - s) + (- N ^ (-s)) / 2
      + s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)

lemma riemannZeta0_apply (N : ℕ) (s : ℂ) : riemannZeta0 N s =
    (∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s) +
    ((- N ^ (1 - s)) / (1 - s) + (- N ^ (-s)) / 2
      + s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1))) := by
  simp_rw [riemannZeta0, div_cpow_eq_cpow_neg]; ring

lemma Real.differentiableAt_cpow_const_of_ne (s : ℂ) {x : ℝ} (xpos : 0 < x) :
    DifferentiableAt ℝ (fun (x : ℝ) ↦ (x : ℂ) ^ s) x := by
  apply DifferentiableAt.comp_ofReal (e := fun z ↦ z ^ s)
  apply DifferentiableAt.cpow (by simp) (by simp) (by simp [xpos])

lemma Complex.one_div_cpow_eq {s : ℂ} {x : ℝ} (x_ne : x ≠ 0) :
    1 / (x : ℂ) ^ s = (x : ℂ) ^ (-s) := by
  refine (eq_one_div_of_mul_eq_one_left ?_).symm
  rw [← cpow_add _ _ <| mod_cast x_ne, neg_add_cancel, cpow_zero]

lemma sum_eq_int_deriv {φ : ℝ → ℂ} {a b : ℝ} (apos : 0 ≤ a) (a_lt_b : a < b)
    (φDiff : ∀ x ∈ [[a, b]], HasDerivAt φ (deriv φ x) x)
    (derivφCont : ContinuousOn (deriv φ) [[a, b]]) :
    ∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, φ n =
      (∫ x in a..b, φ x) + (⌊b⌋₊ + 1 / 2 - b) * φ b - (⌊a⌋₊ + 1 / 2 - a) * φ a
        - ∫ x in a..b, (⌊x⌋ + 1 / 2 - x) * deriv φ x := by
  rw [uIcc_of_le a_lt_b.le] at φDiff
  convert sum_eq_integral_add_integral_deriv apos a_lt_b.le (fun t ht ↦ (φDiff t ht).differentiableAt) derivφCont using 1
  unfold B1
  push_cast
  suffices ∫ (x : ℝ) in a..b, (↑⌊x⌋ + 1 / 2 - ↑x) * deriv φ x = -∫ (t : ℝ) in a..b, deriv φ t * (↑t - ↑⌊t⌋₊ - 1 / 2) by
    rw [this]
    ring_nf!
  rw [← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr fun x hx ↦ ?_
  rw [uIcc_of_le a_lt_b.le, mem_Icc] at hx
  rw [← Int.natCast_floor_eq_floor (by linarith)]
  norm_cast
  push_cast
  ring

lemma xpos_of_uIcc {a b : ℕ} (ha : a ∈ Ioo 0 b) {x : ℝ} (x_in : x ∈ [[(a : ℝ), b]]) :
    0 < x := by
  rw [uIcc_of_le (by exact_mod_cast ha.2.le), mem_Icc] at x_in
  linarith [(by exact_mod_cast ha.1 : (0 : ℝ) < a)]

lemma ZetaSum_aux1₁ {a b : ℕ} {s : ℂ} (s_ne_one : s ≠ 1) (ha : a ∈ Ioo 0 b) :
    (∫ (x : ℝ) in a..b, 1 / (x : ℂ) ^ s) =
    (b ^ (1 - s) - a ^ (1 - s)) / (1 - s) := by
  convert integral_cpow (a := a) (b := b) (r := -s) ?_ using 1
  · refine intervalIntegral.integral_congr fun x hx ↦ one_div_cpow_eq ?_
    exact (xpos_of_uIcc ha hx).ne'
  · norm_cast; ring_nf
  · right; refine ⟨(by grind), ?_⟩
    exact fun hx ↦ (lt_self_iff_false 0).mp <| xpos_of_uIcc ha hx

lemma ZetaSum_aux1φDiff {s : ℂ} {x : ℝ} (xpos : 0 < x) :
    HasDerivAt (fun (t : ℝ) ↦ 1 / (t : ℂ) ^ s) (deriv (fun (t : ℝ) ↦ 1 / (t : ℂ) ^ s) x) x := by
  exact hasDerivAt_deriv_iff.mpr <|
    DifferentiableAt.div (differentiableAt_const _)
      (Real.differentiableAt_cpow_const_of_ne s xpos) (by simp [cpow_eq_zero_iff, xpos.ne'])

lemma ZetaSum_aux1φderiv {s : ℂ} (s_ne_zero : s ≠ 0) {x : ℝ} (xpos : 0 < x) :
    deriv (fun (t : ℝ) ↦ 1 / (t : ℂ) ^ s) x = (fun (x : ℝ) ↦ -s * (x : ℂ) ^ (-(s + 1))) x := by
  let r := -s - 1
  have r_add1_ne_zero : r + 1 ≠ 0 := fun hr ↦ by simp [neg_ne_zero.mpr s_ne_zero, r] at hr
  have r_ne_neg1 : r ≠ -1 := fun hr ↦ (hr ▸ r_add1_ne_zero) <| by norm_num
  have hasDeriv := hasDerivAt_ofReal_cpow_const' xpos.ne' r_ne_neg1
  have := hasDeriv.deriv ▸ deriv_const_mul (-s) (hasDeriv).differentiableAt
  convert! this using 2
  · ext y
    by_cases y_zero : (y : ℂ) = 0
    · simp only [y_zero, ne_eq, s_ne_zero, not_false_eq_true, zero_cpow, div_zero,
      r_add1_ne_zero, zero_div, mul_zero]
    · have : (y : ℂ) ^ s ≠ 0 := fun hy ↦ y_zero ((cpow_eq_zero_iff _ _).mp hy).1
      simp only [one_div, sub_add_cancel, cpow_neg, neg_mul, r]
      field_simp
  · simp only [r]
    ring_nf

lemma ZetaSum_aux1derivφCont {s : ℂ} (s_ne_zero : s ≠ 0) {a b : ℕ} (ha : a ∈ Ioo 0 b) :
    ContinuousOn (deriv (fun (t : ℝ) ↦ 1 / (t : ℂ) ^ s)) [[a, b]] := by
  have : EqOn _ (fun (t : ℝ) ↦ -s * (t : ℂ) ^ (-(s + 1))) [[a, b]] :=
    fun x hx ↦ ZetaSum_aux1φderiv s_ne_zero <| xpos_of_uIcc ha hx
  refine continuous_ofReal.continuousOn.cpow_const ?_ |>.const_smul (c := -s) |>.congr this
  exact fun x hx ↦ ofReal_mem_slitPlane.mpr <| xpos_of_uIcc ha hx

lemma ZetaSum_aux1 {a b : ℕ} {s : ℂ} (s_ne_one : s ≠ 1) (s_ne_zero : s ≠ 0) (ha : a ∈ Ioo 0 b) :
    ∑ n ∈ Finset.Ioc a b, 1 / (n : ℂ) ^ s =
    (b ^ (1 - s) - a ^ (1 - s)) / (1 - s) + 1 / 2 * (1 / b ^ (s)) - 1 / 2 * (1 / a ^ s)
      + s * ∫ x in a..b, (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1)) := by
  let φ := fun (x : ℝ) ↦ 1 / (x : ℂ) ^ s
  let φ' := fun (x : ℝ) ↦ -s * (x : ℂ) ^ (-(s + 1))
  have xpos : ∀ x ∈ [[(a : ℝ), b]], 0 < x := fun x hx ↦ xpos_of_uIcc ha hx
  have φDiff : ∀ x ∈ [[(a : ℝ), b]], HasDerivAt φ (deriv φ x) x :=
    fun x hx ↦ ZetaSum_aux1φDiff (xpos x hx)
  have φderiv : ∀ x ∈ [[(a : ℝ), b]], deriv φ x = φ' x := by
    exact fun x hx ↦ ZetaSum_aux1φderiv s_ne_zero (xpos x hx)
  have derivφCont : ContinuousOn (deriv φ) [[a, b]] := ZetaSum_aux1derivφCont s_ne_zero ha
  convert sum_eq_int_deriv (by linarith) (by exact_mod_cast ha.2) φDiff derivφCont using 1
  · congr <;> simp only [Nat.floor_natCast]
  · rw [Nat.floor_natCast, Nat.floor_natCast, ← intervalIntegral.integral_const_mul]
    simp_rw [mul_div, ← mul_div, φ, ZetaSum_aux1₁ s_ne_one ha]
    conv => rhs; rw [sub_eq_add_neg]
    congr; any_goals norm_cast; simp only [one_div, add_sub_cancel_left]
    rw [← intervalIntegral.integral_neg, intervalIntegral.integral_congr]
    simp only [φ, one_div] at φderiv
    intro x hx; simp_rw [φderiv x hx, φ']; ring_nf

lemma ZetaSum_aux1_1' {a b x : ℝ} (apos : 0 < a) (hx : x ∈ Icc a b) : 0 < x :=
  lt_of_lt_of_le apos hx.1

lemma ZetaSum_aux1_1 {a b x : ℝ} (apos : 0 < a) (a_lt_b : a < b) (hx : x ∈ [[a, b]]) : 0 < x :=
  lt_of_lt_of_le apos (uIcc_of_le a_lt_b.le ▸ hx).1

lemma ZetaSum_aux1_2 {a b : ℝ} {c : ℝ} (apos : 0 < a) (a_lt_b : a < b)
    (h : c ≠ 0 ∧ 0 ∉ [[a, b]]) :
    ∫ (x : ℝ) in a..b, 1 / x ^ (c+1) = (a ^ (-c) - b ^ (-c)) / c := by
  rw [(by ring : (a ^ (-c) - b ^ (-c)) / c = (b ^ (-c) - a ^ (-c)) / (-c))]
  have := integral_rpow (a := a) (b := b) (r := -c-1) (Or.inr ⟨by simp [h.1], h.2⟩)
  simp only [sub_add_cancel] at this
  rw [← this]
  apply intervalIntegral.integral_congr
  intro x hx
  have : 0 ≤ x := (ZetaSum_aux1_1 apos a_lt_b hx).le
  simp [div_rpow_eq_rpow_neg _ _ _ this, sub_eq_add_neg, add_comm]

lemma ZetaSum_aux1_3 (x : ℝ) : ‖(⌊x⌋ + 1/2 - x)‖ ≤ 1/2 :=
  abs_le.mpr ⟨(by linarith [Int.lt_floor_add_one x]), (by linarith [Int.floor_le x])⟩

lemma ZetaSum_aux1_4' (x : ℝ) (hx : 0 < x) (s : ℂ) :
      ‖(⌊x⌋ + 1 / 2 - (x : ℝ)) / (x : ℂ) ^ (s + 1)‖ =
      ‖⌊x⌋ + 1 / 2 - x‖ / x ^ ((s + 1).re) := by
  simp_rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hx, ← norm_real]
  simp

lemma ZetaSum_aux1_4 {a b : ℝ} (apos : 0 < a) (a_lt_b : a < b) {s : ℂ} :
  ∫ (x : ℝ) in a..b, ‖(↑⌊x⌋ + (1 : ℝ) / 2 - ↑x) / (x : ℂ) ^ (s + 1)‖ =
    ∫ (x : ℝ) in a..b, |⌊x⌋ + 1 / 2 - x| / x ^ (s + 1).re := by
  apply intervalIntegral.integral_congr
  exact fun x hx ↦ ZetaSum_aux1_4' x (ZetaSum_aux1_1 apos a_lt_b hx) s

lemma ZetaSum_aux1_5a {a b : ℝ} (apos : 0 < a) {s : ℂ} (x : ℝ)
  (h : x ∈ Icc a b) : |↑⌊x⌋ + 1 / 2 - x| / x ^ (s.re + 1) ≤ 1 / x ^ (s.re + 1) := by
  apply div_le_div_of_nonneg_right _ _
  · exact le_trans (ZetaSum_aux1_3 x) (by norm_num)
  · apply Real.rpow_nonneg <| le_of_lt (ZetaSum_aux1_1' apos h)

lemma ZetaSum_aux1_5b {a b : ℝ} (apos : 0 < a) (a_lt_b : a < b) {s : ℂ} (σpos : 0 < s.re) :
  IntervalIntegrable (fun u ↦ 1 / u ^ (s.re + 1)) MeasureTheory.volume a b := by
  refine continuousOn_const.div ?_ ?_ |>.intervalIntegrable_of_Icc (le_of_lt a_lt_b)
  · exact continuousOn_id.rpow_const fun x hx ↦ Or.inl (ne_of_gt <| ZetaSum_aux1_1' apos hx)
  · exact fun x hx h ↦ by rw [Real.rpow_eq_zero] at h <;> linarith [ZetaSum_aux1_1' apos hx]

open MeasureTheory in
lemma measurable_floor_add_half_sub : Measurable fun (u : ℝ) ↦ ↑⌊u⌋ + 1 / 2 - u := by
  refine Measurable.add ?_ measurable_const |>.sub measurable_id
  exact Measurable.comp (by exact fun _ _ ↦ trivial) Int.measurable_floor

open MeasureTheory in
lemma ZetaSum_aux1_5c {a b : ℝ} {s : ℂ} :
    let g : ℝ → ℝ := fun u ↦ |↑⌊u⌋ + 1 / 2 - u| / u ^ (s.re + 1);
    AEStronglyMeasurable g
      (Measure.restrict volume (Ι a b)) := by
  intro
  refine (Measurable.div ?_ <| measurable_id.pow_const _).aestronglyMeasurable
  exact _root_.continuous_abs.measurable.comp measurable_floor_add_half_sub

lemma ZetaSum_aux1_5d {a b : ℝ} (apos : 0 < a) (a_lt_b : a < b) {s : ℂ} (σpos : 0 < s.re) :
  IntervalIntegrable (fun u ↦ |↑⌊u⌋ + 1 / 2 - u| / u ^ (s.re + 1)) MeasureTheory.volume a b := by
  set g : ℝ → ℝ := (fun u ↦ |↑⌊u⌋ + 1 / 2 - u| / u ^ (s.re + 1))
  apply ZetaSum_aux1_5b apos a_lt_b σpos |>.mono_fun ZetaSum_aux1_5c ?_
  filter_upwards with x
  simp only [Real.norm_eq_abs, one_div, norm_inv, abs_div, _root_.abs_abs]
  conv => rw [div_eq_mul_inv, ← one_div]; rhs; rw [← one_mul |x ^ (s.re + 1)|⁻¹]
  refine mul_le_mul ?_ (le_refl _) (by simp) <| by norm_num
  exact le_trans (ZetaSum_aux1_3 x) <| by norm_num

lemma ZetaSum_aux1_5 {a b : ℝ} (apos : 0 < a) (a_lt_b : a < b) {s : ℂ} (σpos : 0 < s.re) :
  ∫ (x : ℝ) in a..b, |⌊x⌋ + 1 / 2 - x| / x ^ (s.re + 1) ≤
    ∫ (x : ℝ) in a..b, 1 / x ^ (s.re + 1) := by
  apply intervalIntegral.integral_mono_on (le_of_lt a_lt_b) ?_ ?_
  · exact ZetaSum_aux1_5a apos
  · exact ZetaSum_aux1_5d apos a_lt_b σpos
  · exact ZetaSum_aux1_5b apos a_lt_b σpos

lemma ZetaBnd_aux1a {a b : ℝ} (apos : 0 < a) (a_lt_b : a < b) {s : ℂ} (σpos : 0 < s.re) :
    ∫ x in a..b, ‖(⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)‖ ≤
      (a ^ (-s.re) - b ^ (-s.re)) / s.re := by
  calc
    _ = ∫ x in a..b, |(⌊x⌋ + 1 / 2 - x)| / x ^ (s+1).re := ZetaSum_aux1_4 apos a_lt_b
    _ ≤ ∫ x in a..b, 1 / x ^ (s.re + 1) := ZetaSum_aux1_5 apos a_lt_b σpos
    _ = (a ^ (-s.re) - b ^ (-s.re)) / s.re := ?_
  refine ZetaSum_aux1_2 (c := s.re) apos a_lt_b ⟨ne_of_gt σpos, ?_⟩
  exact fun h ↦ (lt_self_iff_false 0).mp <| ZetaSum_aux1_1 apos a_lt_b h

lemma Finset.Ioc_eq_Ico (M N : ℕ) : Finset.Ioc N M = Finset.Ico (N + 1) (M + 1) := by
  ext a; simp only [Finset.mem_Ioc, Finset.mem_Ico]; constructor <;> intro ⟨h₁, h₂⟩ <;> omega

lemma Finset.Ioc_eq_Icc (M N : ℕ) : Finset.Ioc N M = Finset.Icc (N + 1) M := by
  ext a; simp only [Finset.mem_Ioc, Finset.mem_Icc]; constructor <;> intro ⟨h₁, h₂⟩ <;> omega

lemma Finset.Icc_eq_Ico (M N : ℕ) : Finset.Icc N M = Finset.Ico N (M + 1) := by
  ext a; simp only [Finset.mem_Icc, Finset.mem_Ico]; constructor <;> intro ⟨h₁, h₂⟩ <;> omega

lemma finsetSum_tendsto_tsum {N : ℕ} {f : ℕ → ℂ} (hf : Summable f) :
    Tendsto (fun (k : ℕ) ↦ ∑ n ∈ Finset.Ico N k, f n) atTop (𝓝 (∑' (n : ℕ), f (n + N))) := by
  have := Summable.hasSum_iff_tendsto_nat hf (m := ∑' (n : ℕ), f n) |>.mp hf.hasSum
  have const := tendsto_const_nhds (α := ℕ) (x := ∑ i ∈ Finset.range N, f i) (f := atTop)
  have := Filter.Tendsto.sub this const
  rw [← hf.sum_add_tsum_nat_add N, add_comm, add_sub_cancel_right] at this
  apply this.congr'
  filter_upwards [Filter.mem_atTop (N + 1)]
  intro M hM
  rw [Finset.sum_Ico_eq_sub]
  linarith

lemma Complex.cpow_tendsto {s : ℂ} (s_re_gt : 1 < s.re) :
    Tendsto (fun (x : ℕ) ↦ (x : ℂ) ^ (1 - s)) atTop (𝓝 0) := by
  have one_sub_s_re_ne : (1 - s).re ≠ 0 := by simp only [sub_re, one_re]; linarith
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp_rw [Complex.norm_natCast_cpow_of_re_ne_zero _ (one_sub_s_re_ne)]
  rw [(by simp only [sub_re, one_re, neg_sub] : (1 - s).re = - (s - 1).re)]
  apply (tendsto_rpow_neg_atTop _).comp tendsto_natCast_atTop_atTop; simp [s_re_gt]

lemma Complex.cpow_inv_tendsto {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun (x : ℕ) ↦ ((x : ℂ) ^ s)⁻¹) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp_rw [norm_inv, Complex.norm_natCast_cpow_of_re_ne_zero _ <| ne_of_gt hs]
  apply Filter.Tendsto.inv_tendsto_atTop
  exact (tendsto_rpow_atTop hs).comp tendsto_natCast_atTop_atTop

lemma ZetaSum_aux2a : ∃ C, ∀ (x : ℝ), ‖⌊x⌋ + 1 / 2 - x‖ ≤ C := by
  use 1 / 2; exact ZetaSum_aux1_3

lemma ZetaSum_aux3 {N : ℕ} {s : ℂ} (s_re_gt : 1 < s.re) :
    Tendsto (fun k ↦ ∑ n ∈ Finset.Ioc N k, 1 / (n : ℂ) ^ s) atTop
    (𝓝 (∑' (n : ℕ), 1 / (n + N + 1 : ℂ) ^ s)) := by
  let f := fun (n : ℕ) ↦ 1 / (n : ℂ) ^ s
  have hf := summable_one_div_nat_cpow.mpr s_re_gt
  simp_rw [Finset.Ioc_eq_Ico]
  convert finsetSum_tendsto_tsum (f := fun n ↦ f (n + 1)) (N := N) ?_ using 1
  · ext k
    rw [Finset.sum_Ico_add']
  · congr; ext n; simp only [one_div, Nat.cast_add, Nat.cast_one, f]
  · rwa [summable_nat_add_iff (k := 1)]

lemma integrableOn_of_Zeta0_fun {N : ℕ} (N_pos : 0 < N) {s : ℂ} (s_re_gt : 0 < s.re) :
    MeasureTheory.IntegrableOn (fun (x : ℝ) ↦ (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1))) (Ioi N)
    MeasureTheory.volume := by
  obtain ⟨c, hc⟩ := ZetaSum_aux2a
  apply MeasureTheory.Integrable.bdd_mul (c := c) ?_ ?_
  · apply MeasureTheory.ae_of_all
    convert hc; simp only [← Complex.norm_real]; simp
  · apply integrableOn_Ioi_cpow_iff (by positivity) |>.mpr (by simp [s_re_gt])
  · refine Measurable.add ?_ measurable_const |>.sub (by fun_prop) |>.aestronglyMeasurable
    exact Measurable.comp (by exact fun _ _ ↦ trivial) Int.measurable_floor

lemma ZetaSum_aux2 {N : ℕ} (N_pos : 0 < N) {s : ℂ} (s_re_gt : 1 < s.re) :
    ∑' (n : ℕ), 1 / (n + N + 1 : ℂ) ^ s =
    (- N ^ (1 - s)) / (1 - s) - N ^ (-s) / 2
      + s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1)) := by
  have s_ne_zero : s ≠ 0 := fun hs ↦ by linarith [zero_re ▸ hs ▸ s_re_gt]
  have s_ne_one : s ≠ 1 := fun hs ↦ (lt_self_iff_false _).mp <| one_re ▸ hs ▸ s_re_gt
  apply tendsto_nhds_unique (X := ℂ) (Y := ℕ) (l := atTop)
    (f := fun k ↦ ((k : ℂ) ^ (1 - s) - (N : ℂ) ^ (1 - s)) / (1 - s) +
      1 / 2 * (1 / ↑k ^ s) - 1 / 2 * (1 / ↑N ^ s)
      + s * ∫ (x : ℝ) in (N : ℝ)..k, (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1)))
    (b := (- N ^ (1 - s)) / (1 - s) - N ^ (-s) / 2
      + s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1)))
  · apply Filter.Tendsto.congr'
      (f₁ := fun (k : ℕ) ↦ ∑ n ∈ Finset.Ioc N k, 1 / (n : ℂ) ^ s) (l₁ := atTop)
    · apply Filter.eventually_atTop.mpr
      use N + 1
      intro k hk
      exact ZetaSum_aux1 (a := N) (b := k) s_ne_one s_ne_zero ⟨N_pos, hk⟩
    · exact ZetaSum_aux3 s_re_gt
  · apply (Tendsto.sub ?_ ?_).add (Tendsto.const_mul _ ?_)
    · rw [(by ring : -↑N ^ (1 - s) / (1 - s) = (0 - ↑N ^ (1 - s)) / (1 - s) + 0)]
      apply cpow_tendsto s_re_gt |>.sub_const _ |>.div_const _ |>.add
      simp_rw [mul_comm_div, one_mul, one_div, (by congr; ring : 𝓝 (0 : ℂ) = 𝓝 ((0 : ℂ) / 2))]
      apply Tendsto.div_const <| cpow_inv_tendsto (by positivity)
    · simp_rw [mul_comm_div, one_mul, one_div, cpow_neg]; exact tendsto_const_nhds
    · exact MeasureTheory.intervalIntegral_tendsto_integral_Ioi (a := N)
        (b := (fun (n : ℕ) ↦ (n : ℝ)))
        (integrableOn_of_Zeta0_fun N_pos <| by positivity) tendsto_natCast_atTop_atTop

open MeasureTheory in

lemma ZetaBnd_aux1b (N : ℕ) (Npos : 1 ≤ N) {σ t : ℝ} (σpos : 0 < σ) :
    ‖∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ ((σ + t * I) + 1)‖
    ≤ N ^ (-σ) / σ := by
  apply le_trans (by apply norm_integral_le_integral_norm)
  apply le_of_tendsto (x := atTop (α := ℝ)) (f := fun (t : ℝ) ↦ ∫ (x : ℝ) in N..t,
    ‖(⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (σ + t * I + 1)‖) ?_ ?_
  · apply intervalIntegral_tendsto_integral_Ioi (μ := volume) (l := atTop) (b := id)
      (f := fun (x : ℝ) ↦ ‖(⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (σ + t * I + 1)‖) N ?_ ?_ |>.congr' ?_
    · filter_upwards [Filter.mem_atTop ((N : ℝ))]
      intro u hu
      simp only [id_eq, intervalIntegral.integral_of_le hu, norm_div]
      apply setIntegral_congr_fun (by simp)
      intro x hx; beta_reduce
      iterate 2 (rw [norm_cpow_eq_rpow_re_of_pos (by linarith [hx.1])])
      simp
    · apply IntegrableOn.integrable ?_ |>.norm
      convert! integrableOn_of_Zeta0_fun (s := σ + t * I) Npos (by simp [σpos]) using 1
      simp_rw [div_eq_mul_inv, cpow_neg]
    · exact fun ⦃_⦄ a ↦ a
  · filter_upwards [mem_atTop (N + 1 : ℝ)] with t ht
    have : (N ^ (-σ) - t ^ (-σ)) / σ ≤ N ^ (-σ) / σ :=
      div_le_div_iff_of_pos_right σpos |>.mpr (by simp [Real.rpow_nonneg (by linarith)])
    apply le_trans ?_ this
    convert! ZetaBnd_aux1a (a := N) (b := t) (by positivity) (by linarith) ?_ <;> simp [σpos]

lemma ZetaBnd_aux1 (N : ℕ) (Npos : 1 ≤ N) {σ t : ℝ} (hσ : σ ∈ Ioc 0 2) (ht : 2 ≤ |t|) :
    ‖(σ + t * I) * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ ((σ + t * I) + 1)‖
    ≤ 2 * |t| * N ^ (-σ) / σ := by
  rw [norm_mul, mul_div_assoc]
  rw [Set.mem_Ioc] at hσ
  apply mul_le_mul ?_ (ZetaBnd_aux1b N Npos hσ.1) (norm_nonneg _) (by positivity)
  refine le_trans (by apply norm_add_le) ?_
  simp only [Complex.norm_of_nonneg hσ.1.le, Complex.norm_mul, norm_real, Real.norm_eq_abs, norm_I,
    mul_one]
  linarith [hσ.2]

lemma ZetaBnd_aux1p (N : ℕ) (Npos : 1 ≤ N) {σ : ℝ} (hσ : σ ∈ Ioc 0 2) :
    (fun (t : ℝ) ↦
      ‖(σ + t * I) * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ ((σ + t * I) + 1)‖)
    =O[Filter.principal {t | 2 ≤ |t|}] fun t ↦ |t| * N ^ (-σ) / σ := by
  rw [Asymptotics.IsBigO_def]
  use 2
  rw [Asymptotics.isBigOWith_principal]
  intro t ht
  simp only [mem_setOf_eq] at ht
  rw [norm_norm, norm_mul, mul_div_assoc, norm_mul]
  have : 2 * (‖|t|‖ * ‖↑N ^ (-σ) / σ‖) = (2 * |t|) * ((N : ℝ) ^ (-σ) / σ) := by
    simp only [Real.norm_eq_abs, _root_.abs_abs, norm_div]
    have : σ ≠ 0 := by linarith [hσ.1]
    field_simp
    rw [abs_of_pos hσ.1]
    have : 0 < (N : ℝ) ^ (-σ) := by
      refine Real.rpow_pos_of_pos ?_ _
      positivity
    rw [abs_of_pos this]
    ring
  rw [this]
  apply mul_le_mul ?_ (ZetaBnd_aux1b N Npos hσ.1) (norm_nonneg _) (by positivity)
  refine le_trans (by apply norm_add_le) ?_
  simp only [norm_real, norm_mul, norm_I, mul_one, Complex.norm_of_nonneg hσ.1.le, Real.norm_eq_abs]
  linarith [hσ.2]

lemma isOpen_aux : IsOpen {z : ℂ | z ≠ 1 ∧ 0 < z.re} := by
  refine IsOpen.inter isOpen_ne ?_
  exact isOpen_lt (g := fun (z : ℂ) ↦ z.re) (by continuity) (by continuity)

open MeasureTheory in
lemma integrable_log_over_pow {r : ℝ} (rneg : r < 0) {N : ℕ} (Npos : 0 < N) :
    IntegrableOn (fun (x : ℝ) ↦ ‖x ^ (r - 1)‖ * ‖Real.log x‖) <| Ioi N := by
  apply IntegrableOn.mono_set (hst := Set.Ioi_subset_Ici <| le_refl (N : ℝ))
  apply LocallyIntegrableOn.integrableOn_of_isBigO_atTop (g := fun x ↦ x ^ (r / 2 - 1))
  · apply ContinuousOn.abs ?_ |>.mul ?_ |>.locallyIntegrableOn (by simp)
    · apply ContinuousOn.rpow (by fun_prop) (by fun_prop)
      intro x hx; left; contrapose! Npos with h; exact_mod_cast h ▸ mem_Ici.mp hx
    · apply continuous_id.continuousOn.log ?_ |>.abs
      intro x hx; simp only [id_eq]; contrapose! Npos with h; exact_mod_cast h ▸ mem_Ici.mp hx
  · have := isLittleO_log_rpow_atTop (r := -r / 2) (by linarith) |>.isBigO
    rw [Asymptotics.isBigO_iff_eventually, Filter.eventually_atTop] at this
    obtain ⟨C, hC⟩ := this
    have hh := hC C (by simp)
    rw [Asymptotics.isBigO_atTop_iff_eventually_exists]
    have := Filter.eventually_atTop.mp hh
    obtain ⟨x₀, hx₀ ⟩ := this
    filter_upwards [hh, Filter.mem_atTop x₀, Filter.mem_atTop 1]
    intro x hx x_gt x_pos
    use C
    intro y hy
    simp only [norm_mul, Real.norm_eq_abs, _root_.abs_abs]
    simp only [Real.norm_eq_abs] at hx
    have y_pos : 0 < y := by linarith
    have : y ^ (r / 2 - 1) = y ^ (r - 1) * y ^ (-r / 2) := by
      rw [← Real.rpow_add y_pos]; ring_nf
    rw [this, abs_mul]
    have y_gt : y ≥ x₀ := by linarith
    have := hx₀ y y_gt
    simp only [Real.norm_eq_abs] at this
    rw [← mul_assoc, mul_comm C, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hbc := this) (a := |y ^ (r - 1)|) (ha := by simp)
  · have := integrableOn_Ioi_rpow_iff (s := r / 2 - 1) (t := N) (by simp [Npos]) |>.mpr
      (by linarith [rneg])
    exact integrableOn_Ioi_iff_integrableAtFilter_atTop_nhdsWithin.mp this |>.1

open MeasureTheory in
lemma integrableOn_of_Zeta0_fun_log {N : ℕ} (Npos : 0 < N) {s : ℂ} (s_re_gt : 0 < s.re) :
    IntegrableOn (fun (x : ℝ) ↦ (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1)) * (-Real.log x)) (Ioi N)
    volume := by
  simp_rw [mul_assoc]
  obtain ⟨c, hc⟩ := ZetaSum_aux2a
  apply Integrable.bdd_mul (c := c) ?_ ?_ ?_
  · simp only [neg_add_rev, mul_neg, add_comm, ← sub_eq_add_neg]
    apply integrable_norm_iff ?_ |>.mp ?_ |>.neg
    · apply ContinuousOn.mul ?_ ?_ |>.aestronglyMeasurable (by simp)
      · intro x hx
        apply ContinuousWithinAt.cpow ?_ continuous_const.continuousWithinAt ?_
        · exact RCLike.continuous_ofReal.continuousWithinAt
        · simp only [ofReal_mem_slitPlane]; linarith [mem_Ioi.mp hx]
      · apply RCLike.continuous_ofReal.continuousOn.comp ?_ (mapsTo_image _ _)
        refine continuous_id.continuousOn.log ?_
        intro x hx; simp only [id_eq]; linarith [mem_Ioi.mp hx]
    · simp only [norm_mul, norm_real]
      have := integrable_log_over_pow (r := -s.re) (by linarith) Npos
      apply IntegrableOn.congr_fun this ?_ (by simp)
      intro x hx
      simp only [mul_eq_mul_right_iff, norm_eq_zero, Real.log_eq_zero]
      left
      have xpos : 0 < x := by linarith [mem_Ioi.mp hx]
      simp [norm_cpow_eq_rpow_re_of_pos xpos, Real.abs_rpow_of_nonneg xpos.le,
        abs_eq_self.mpr xpos.le]
  · apply Measurable.add ?_ measurable_const |>.sub (by fun_prop) |>.aestronglyMeasurable
    exact Measurable.comp (fun _ _ ↦ trivial) Int.measurable_floor
  · apply MeasureTheory.ae_of_all
    convert hc with _ x; simp only [← Complex.norm_real]; simp

open MeasureTheory in
lemma hasDerivAt_Zeta0Integral {N : ℕ} (Npos : 0 < N) {s : ℂ} (hs : s ∈ {s | 0 < s.re}) :
  HasDerivAt (fun z ↦ ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-z - 1))
    (∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (- s - 1) * (- Real.log x)) s := by
  simp only [mem_setOf_eq] at hs
  set f : ℝ → ℂ := fun x ↦ (⌊x⌋ : ℂ) + 1 / 2 - x
  set F : ℂ → ℝ → ℂ := fun s x ↦ (x : ℂ) ^ (- s - 1) * f x
  set F' : ℂ → ℝ → ℂ := fun s x ↦ (x : ℂ) ^ (- s - 1) * (- Real.log x) * f x
  set ε := s.re / 2
  have ε_pos : 0 < ε := by aesop
  set bound : ℝ → ℝ := fun x ↦ |x ^ (- s.re / 2 - 1)| * |Real.log x|
  let μ : Measure ℝ := volume.restrict (Ioi (N : ℝ))
  have hF_meas : ∀ᶠ (z : ℂ) in 𝓝 s, AEStronglyMeasurable (F z) μ := by
    have : {z : ℂ | 0 < z.re} ∈ 𝓝 s := by
      rw [mem_nhds_iff]
      refine ⟨{z | 0 < z.re}, fun ⦃a⦄ a ↦ a, isOpen_lt continuous_const Complex.continuous_re, hs⟩
    filter_upwards [this] with z hz
    convert! integrableOn_of_Zeta0_fun Npos hz |>.aestronglyMeasurable using 1
    simp only [F, f]; ext x; ring_nf
  have hF_int : Integrable (F s) μ := by
    convert! integrableOn_of_Zeta0_fun Npos hs |>.integrable using 1
    simp only [F, f]; ext x; ring_nf
  have hF'_meas : AEStronglyMeasurable (F' s) μ := by
    convert! integrableOn_of_Zeta0_fun_log Npos hs |>.aestronglyMeasurable using 1
    simp only [F', f]; ext x; ring_nf
  have IoiSubIoi1 : (Ioi (N : ℝ)) ⊆ {x | 1 < x} :=
      fun x hx ↦ lt_of_le_of_lt (by simp only [Nat.one_le_cast]; omega) <| mem_Ioi.mp hx
  have measSetIoi1 : MeasurableSet {x : ℝ | 1 < x} := (isOpen_lt' 1).measurableSet
  have h_bound1 :
    ∀ᵐ (x : ℝ) ∂volume.restrict {x | 1 < x}, ∀ z ∈ Metric.ball s ε, ‖F' z x‖ ≤ bound x := by
    filter_upwards [self_mem_ae_restrict measSetIoi1] with x hx
    intro z hz
    simp only [F', f, bound]
    calc _ = ‖(x : ℂ) ^ (-z - 1)‖ * ‖-(Real.log x)‖ * ‖(⌊x⌋ + 1 / 2 - x)‖ := by
            simp only [mul_neg, one_div, neg_mul, norm_neg, norm_mul, norm_real, Real.norm_eq_abs,
              ← (by simp : (((⌊x⌋ + 2⁻¹ - x) : ℝ) : ℂ) = (⌊x⌋ : ℂ) + 2⁻¹ - ↑x),
              Complex.norm_real]
         _ = ‖x ^ (-z.re - 1)‖ * ‖-(Real.log x)‖ * ‖(⌊x⌋ + 1 / 2 - x)‖ := ?_
         _ = |x ^ (-z.re - 1)| * |(Real.log x)| * |(⌊x⌋ + 1 / 2 - x)| := by simp
         _ ≤ _ := ?_
    · congr! 2
      simp only [Real.norm_eq_abs, norm_cpow_eq_rpow_re_of_pos (by linarith),
        sub_re, neg_re, one_re]
      apply abs_eq_self.mpr ?_ |>.symm
      positivity
    · rw [mul_comm, ← mul_assoc]
      apply mul_le_mul_of_nonneg_right ?_ <| abs_nonneg _
      simp only [Metric.mem_ball, ε, Complex.dist_eq] at hz
      apply le_trans (b := 1 * |x ^ (-z.re - 1)|)
      · apply mul_le_mul_of_nonneg_right (le_trans (ZetaSum_aux1_3 _) (by norm_num)) <| abs_nonneg _
      · simp_rw [one_mul, Real.abs_rpow_of_nonneg (by linarith : 0 ≤ x)]
        apply Real.rpow_le_rpow_of_exponent_le <| le_abs.mpr (by left; exact hx.le)
        have := abs_le.mp <| le_trans (abs_re_le_norm (z-s)) hz.le
        simp only [sub_re, neg_le_sub_iff_le_add, tsub_le_iff_right] at this
        linarith [this.1]
  have h_bound : ∀ᵐ x ∂μ, ∀ z ∈ Metric.ball s ε, ‖F' z x‖ ≤ bound x := by
    apply ae_restrict_of_ae_restrict_of_subset IoiSubIoi1
    exact h_bound1
  have bound_integrable : Integrable bound μ := by
    simp only [bound]
    convert! integrable_log_over_pow (r := -s.re / 2) (by linarith) Npos using 0
  have h_diff : ∀ᵐ x ∂μ, ∀ z ∈ Metric.ball s ε, HasDerivAt (fun w ↦ F w x) (F' z x) z := by
    simp only [F, F', f]
    apply ae_restrict_of_ae_restrict_of_subset IoiSubIoi1
    filter_upwards [h_bound1, self_mem_ae_restrict measSetIoi1] with x _ one_lt_x
    intro z hz
    convert! HasDerivAt.mul_const (c := fun (w : ℂ) ↦ (x : ℂ) ^ (-w-1))
      (c' := (x : ℂ) ^ (-z-1) * -Real.log x) (d := (⌊x⌋ : ℝ) + 1 / 2 - x) ?_ using 1
    convert! HasDerivAt.comp (h := fun w ↦ -w-1) (h' := -1) (h₂ := fun w ↦ x ^ w)
      (h₂' := x ^ (-z-1) * Real.log x) (x := z) ?_ ?_ using 0
    · simp only [mul_neg, mul_one]; congr! 2
    · convert! HasDerivAt.const_cpow (c := (x : ℂ)) (f := fun w ↦ w) (f' := 1) (x := -z-1)
        (hasDerivAt_id _) ?_ using 1
      · simp only [mul_one, mul_eq_mul_left_iff, cpow_eq_zero_iff, ofReal_eq_zero, ne_eq]
        left
        rw [Complex.ofReal_log]
        linarith
      · right
        intro h
        simp only [Metric.mem_ball, ε, Complex.dist_eq,
          neg_eq_iff_eq_neg.mp <| sub_eq_zero.mp h] at hz
        have := (abs_le.mp <| le_trans (abs_re_le_norm (-1-s)) hz.le).1
        simp only [sub_re, neg_re, one_re, neg_le_sub_iff_le_add, le_neg_add_iff_add_le] at this
        linarith
    · apply hasDerivAt_id _ |>.neg |>.sub_const
  convert! (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := F) (F' := F') (x₀ := s)
    (s := Metric.ball s ε) (bound := bound) (μ := μ) (Metric.ball_mem_nhds s ε_pos)
    hF_meas hF_int hF'_meas h_bound bound_integrable h_diff).2 using 3
  · ext a; simp only [one_div, F, f]; ring_nf
  · simp only [one_div, mul_neg, neg_mul, neg_inj, F', f]; ring_nf

noncomputable def ζ₀' (N : ℕ) (s : ℂ) : ℂ :=
    ∑ n ∈ Finset.range (N + 1), -1 / (n : ℂ) ^ s * Real.log n +
    (-N ^ (1 - s) / (1 - s) ^ 2 + Real.log N * N ^ (1 - s) / (1 - s)) +
    Real.log N * N ^ (-s) / 2 +
    (1 * (∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (- s - 1)) +
    s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (- s - 1) * (- Real.log x))

lemma HasDerivAt_neg_cpow_over2 {N : ℕ} (Npos : 0 < N) (s : ℂ) :
    HasDerivAt (fun x : ℂ ↦ -(N : ℂ) ^ (-x) / 2) (-((- Real.log N) * (N : ℂ) ^ (-s)) / 2) s := by
  convert! hasDerivAt_neg' s |>.const_cpow (c := N) (by aesop) |>.neg |>.div_const _ using 1
  simp [mul_comm]

lemma HasDerivAt_cpow_over_var (N : ℕ) {z : ℂ} (z_ne_zero : z ≠ 0) :
    HasDerivAt (fun z ↦ -(N : ℂ) ^ z / z)
      (((N : ℂ) ^ z / z ^ 2) - (Real.log N * N ^ z / z)) z := by
  simp_rw [div_eq_mul_inv]
  convert! HasDerivAt.mul (c := fun z ↦ - (N : ℂ) ^ z) (d := fun z ↦ z⁻¹)
    (c' := - (N : ℂ) ^ z * Real.log N)
    (d' := - (z ^ 2)⁻¹) ?_ ?_ using 1
  · simp only [natCast_log, neg_mul, mul_neg, neg_neg]
    ring_nf
  · simp only [natCast_log, neg_mul]
    apply HasDerivAt.neg
    convert! HasDerivAt.const_cpow (c := (N : ℂ)) (f := id) (f' := 1) (x := z) (hasDerivAt_id z)
      (by simp [z_ne_zero]) using 1
    simp only [id_eq, mul_one]
  · exact hasDerivAt_inv z_ne_zero

lemma HasDerivAtZeta0 {N : ℕ} (Npos : 0 < N) {s : ℂ} (reS_pos : 0 < s.re) (s_ne_one : s ≠ 1) :
    HasDerivAt (riemannZeta0 N) (ζ₀' N s) s := by
  unfold riemannZeta0 ζ₀'
  apply HasDerivAt.fun_sum ?_ |>.add ?_ |>.add ?_ |>.add ?_
  · intro n _
    convert! hasDerivAt_neg' s |>.const_cpow (c := n) (by aesop) using 1
    all_goals (ring_nf; simp [cpow_neg])
  · convert! HasDerivAt.comp (h₂ := fun z ↦ -(N : ℂ) ^ z / z) (h := fun z ↦ 1 - z) (h' := -1)
      (h₂' := ((N : ℂ) ^ (1 - s) / (1 - s) ^ 2 - Real.log (N : ℝ) * (N : ℂ) ^ (1 - s) / (1 - s)))
      (x := s) ?_ ?_ using 1
    · ring_nf
    · exact HasDerivAt_cpow_over_var N (by rw [sub_ne_zero]; exact s_ne_one.symm)
    · convert! hasDerivAt_const s _ |>.sub (hasDerivAt_id _) using 1; simp
  · convert! HasDerivAt_neg_cpow_over2 Npos s using 1; simp only [natCast_log, neg_mul, neg_neg]
  · simp_rw [div_cpow_eq_cpow_neg, neg_add, ← sub_eq_add_neg]
    convert! hasDerivAt_id s |>.mul <| hasDerivAt_Zeta0Integral Npos reS_pos using 1

lemma HolomorphicOn_riemannZeta0 {N : ℕ} (N_pos : 0 < N) :
    HolomorphicOn (riemannZeta0 N) {s : ℂ | s ≠ 1 ∧ 0 < s.re} :=
  fun _ ⟨hs₁, hs₂⟩ ↦ (HasDerivAtZeta0 N_pos hs₂ hs₁).differentiableAt.differentiableWithinAt

lemma HolomorphicOn_riemannZeta :
    HolomorphicOn riemannZeta {s : ℂ | s ≠ 1} := by
  intro z hz
  simp only [mem_setOf_eq] at hz
  exact (differentiableAt_riemannZeta hz).differentiableWithinAt

lemma isPathConnected_aux : IsPathConnected {z : ℂ | z ≠ 1 ∧ 0 < z.re} := by
  use (2 : ℂ)
  constructor
  · simp
  intro w hw; simp only [ne_eq, mem_setOf_eq] at hw
  by_cases w_im : w.im = 0
  · apply JoinedIn.trans (y := 1 + I)
    · let f : ℝ → ℂ := fun t ↦ (1 + I) * t + 2 * (1 - t)
      have cont : Continuous f := by continuity
      apply JoinedIn.ofLine cont.continuousOn (by simp [f]) (by simp [f])
      simp only [unitInterval, ne_eq, image_subset_iff, preimage_setOf_eq, add_re, mul_re, one_re,
        I_re, add_zero, ofReal_re, one_mul, add_im, one_im, I_im, zero_add, ofReal_im, mul_zero,
        sub_zero, re_ofNat, sub_re, im_ofNat, sub_im, sub_self, f]
      intro x hx; simp only [mem_Icc] at hx
      refine ⟨?_, by linarith⟩
      intro h
      rw [Complex.ext_iff] at h; simp [(by apply And.right; simpa [w_im] using h : x = 0)] at h
    · let f : ℝ → ℂ := fun t ↦ w * t + (1 + I) * (1 - t)
      have cont : Continuous f := by continuity
      apply JoinedIn.ofLine cont.continuousOn (by simp [f]) (by simp [f])
      simp only [unitInterval, ne_eq, image_subset_iff, preimage_setOf_eq, add_re, mul_re,
        ofReal_re, ofReal_im, mul_zero, sub_zero, one_re, I_re, add_zero, sub_re, one_mul, add_im,
        one_im, I_im, zero_add, sub_im, sub_self, f]
      intro x hx; simp only [mem_Icc] at hx
      simp only [mem_setOf_eq]
      constructor
      · intro h
        refine hw.1 ?_
        rw [Complex.ext_iff] at h
        have : x = 1 := by linarith [(by apply And.right; simpa [w_im] using h : 1 - x = 0)]
        rw [Complex.ext_iff, one_re, one_im]; exact ⟨by simpa [this, w_im] using h, w_im⟩
      · by_cases hxx : x = 0
        · simp only [hxx]; linarith
        · have : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hxx)
          have : 0 ≤ 1 - x := by linarith
          have := hw.2
          positivity
  · let f : ℝ → ℂ := fun t ↦ w * t + 2 * (1 - t)
    have cont : Continuous f := by continuity
    apply JoinedIn.ofLine cont.continuousOn (by simp [f]) (by simp [f])
    simp only [unitInterval, ne_eq, image_subset_iff, preimage_setOf_eq, add_re, mul_re, ofReal_re,
      ofReal_im, mul_zero, sub_zero, re_ofNat, sub_re, one_re, im_ofNat, sub_im, one_im, sub_self,
      f]
    intro x hx; simp only [mem_Icc] at hx
    constructor
    · intro h
      rw [Complex.ext_iff] at h;
      simp [(by apply And.right; simpa [w_im] using h : x = 0)] at h
    · by_cases hxx : x = 0
      · simp only [hxx]; linarith
      · have : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hxx)
        have : 0 ≤ 1 - x := by linarith
        have := hw.2
        positivity

lemma Zeta0EqZeta {N : ℕ} (N_pos : 0 < N) {s : ℂ} (reS_pos : 0 < s.re) (s_ne_one : s ≠ 1) :
    riemannZeta0 N s = riemannZeta s := by
  let f := riemannZeta
  let g := riemannZeta0 N
  let U := {z : ℂ | z ≠ 1 ∧ 0 < z.re}
  have f_an : AnalyticOnNhd ℂ f U := by
    apply (HolomorphicOn_riemannZeta.analyticOnNhd isOpen_ne).mono
    simp only [ne_eq, setOf_subset_setOf, and_imp, U]
    exact fun a ha _ ↦ ha
  have g_an : AnalyticOnNhd ℂ g U := (HolomorphicOn_riemannZeta0 N_pos).analyticOnNhd isOpen_aux
  have preconU : IsPreconnected U := by
    apply IsConnected.isPreconnected
    apply (IsOpen.isConnected_iff_isPathConnected isOpen_aux).mpr isPathConnected_aux
  have h2 : (2 : ℂ) ∈ U := by simp [U]
  have s_mem : s ∈ U := by simp [U, reS_pos, s_ne_one]
  convert (AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq f_an g_an preconU h2 ?_ s_mem).symm
  have u_mem : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) := by
    apply mem_nhds_iff.mpr
    use {z : ℂ | 1 < z.re}
    simp only [setOf_subset_setOf, imp_self, forall_const, mem_setOf_eq, re_ofNat,
      Nat.one_lt_ofNat, and_true, true_and]
    exact isOpen_lt (by continuity) (by continuity)
  filter_upwards [u_mem]
  intro z hz
  simp only [f,g, zeta_eq_tsum_one_div_nat_cpow hz, riemannZeta0_apply]
  nth_rewrite 2 [neg_div]
  rw [← sub_eq_add_neg, ← ZetaSum_aux2 N_pos hz,
    ← (summable_one_div_nat_cpow.mpr hz).sum_add_tsum_nat_add (N + 1)]
  norm_cast

lemma DerivZeta0EqDerivZeta {N : ℕ} (N_pos : 0 < N) {s : ℂ} (reS_pos : 0 < s.re)
    (s_ne_one : s ≠ 1) :
    deriv (riemannZeta0 N) s = (deriv riemannZeta) s := by
  let U := {z : ℂ | z ≠ 1 ∧ 0 < z.re}
  have {x : ℂ} (hx : x ∈ U) : riemannZeta0 N x = riemannZeta x := by
    simp only [mem_setOf_eq, U] at hx; exact Zeta0EqZeta (N := N) N_pos hx.2 hx.1
  refine deriv_eqOn isOpen_aux ?_ (by simp [s_ne_one, reS_pos])
  intro x hx
  have hζ := HolomorphicOn_riemannZeta.mono (by aesop)|>.hasDerivAt (s := U) <|
    isOpen_aux.mem_nhds hx
  exact hζ.hasDerivWithinAt.congr (fun y hy ↦ this hy) (this hx)

lemma le_trans₄ {α : Type*} [Preorder α] {a b c d : α} : a ≤ b → b ≤ c → c ≤ d → a ≤ d :=
  fun hab hbc hcd ↦ le_trans (le_trans hab hbc) hcd

lemma lt_trans₄ {α : Type*} [Preorder α] {a b c d : α} : a < b → b < c → c < d → a < d :=
  fun hab hbc hcd ↦ lt_trans (lt_trans hab hbc) hcd

lemma norm_add₅_le {E : Type*} [SeminormedAddGroup E] (a : E) (b : E) (c : E) (d : E) (e : E) :
    ‖a + b + c + d + e‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖ := by
  apply le_trans <| norm_add_le (a + b + c + d) e
  simp only [add_le_add_iff_right]; apply norm_add₄_le

lemma norm_add₆_le {E : Type*} [SeminormedAddGroup E] (a : E) (b : E) (c : E) (d : E) (e : E)
    (f : E) :
    ‖a + b + c + d + e + f‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖ + ‖f‖ := by
  apply le_trans <| norm_add_le (a + b + c + d + e) f
  simp only [add_le_add_iff_right]; apply norm_add₅_le

lemma mul_le_mul₃ {α : Type*} {a b c d e f : α} [MulZeroClass α] [Preorder α] [PosMulMono α]
    [MulPosMono α] (h₁ : a ≤ b) (h₂ : c ≤ d) (h₃ : e ≤ f) (c0 : 0 ≤ c) (b0 : 0 ≤ b)
    (e0 : 0 ≤ e) : a * c * e ≤ b * d * f := by
  apply mul_le_mul (mul_le_mul h₁ h₂ c0 b0) h₃ e0 <| mul_nonneg b0 <| le_trans c0 h₂

lemma ZetaBnd_aux2 {n : ℕ} {t A σ : ℝ} (Apos : 0 < A) (σpos : 0 < σ) (n_le_t : n ≤ |t|)
    (σ_ge : (1 : ℝ) - A / Real.log |t| ≤ σ) :
    ‖(n : ℂ) ^ (-(σ + t * I))‖ ≤ (n : ℝ)⁻¹ * Real.exp A := by
  set s := σ + t * I
  by_cases n0 : n = 0
  · simp_rw [n0, CharP.cast_eq_zero, inv_zero, zero_mul]
    rw [Complex.zero_cpow ?_]
    · simp
    · exact fun h ↦ σpos.ne' <| zero_eq_neg.mp <| zero_re ▸ h ▸ (by simp [s])
  have n_gt_0 : 0 < n := Nat.pos_of_ne_zero n0
  have n_gt_0' : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr n_gt_0
  have n_ge_1 : 1 ≤ (n : ℝ) := Nat.one_le_cast.mpr <| Nat.succ_le_of_lt n_gt_0
  calc
    _ = |((n : ℝ) ^ (-σ))| := ?_
    _ ≤ Real.exp (Real.log n * -σ) := Real.abs_rpow_le_exp_log_mul (n : ℝ) (-σ)
    _ ≤ Real.exp (Real.log n *  -(1 - A / Real.log t)) := ?_
    _ ≤ Real.exp (- Real.log n + A) := Real.exp_le_exp_of_le ?_
    _ ≤ _ := by rw [Real.exp_add, Real.exp_neg, Real.exp_log n_gt_0']
  · have : ‖(n : ℂ) ^ (-s)‖ = n ^ (-s.re) := norm_cpow_eq_rpow_re_of_pos n_gt_0' (-s)
    rw [this, abs_eq_self.mpr <| Real.rpow_nonneg n_gt_0'.le _]; simp [s]
  · apply Real.exp_le_exp_of_le <| mul_le_mul_of_nonneg_left _ <| Real.log_nonneg n_ge_1
    rw [neg_sub, neg_le_sub_iff_le_add, add_comm, ← Real.log_abs]; linarith
  · simp only [neg_sub, le_neg_add_iff_add_le]
    ring_nf
    conv => rw [mul_comm, ← mul_assoc, ← Real.log_abs]; rhs; rw [← one_mul A]
    gcongr
    by_cases ht1 : |t| = 1
    · simp [ht1]
    apply (inv_mul_le_iff₀ ?_).mpr
    · convert! Real.log_le_log n_gt_0' n_le_t using 1; rw [mul_one]
    · exact Real.log_pos <| lt_of_le_of_ne (le_trans n_ge_1 n_le_t) <| fun t ↦ ht1 (t.symm)

lemma logt_gt_one {t : ℝ} (t_ge : 3 ≤ t) : 1 < Real.log t :=
  (Real.lt_log_iff_exp_lt (by linarith)).mpr (by linarith [Real.exp_one_lt_d9])

lemma UpperBnd_aux {A σ t : ℝ} (hA : A ∈ Ioc 0 (1 / 2)) (t_gt : 3 < |t|)
    (σ_ge : 1 - A / Real.log |t| ≤ σ) :
    let N := ⌊|t|⌋₊;
    0 < N ∧ N ≤ |t| ∧ 1 < Real.log |t| ∧ 1 - A < σ ∧ 0 < σ ∧ σ + t * I ≠ 1 := by
  intro N
  have Npos : 0 < N := Nat.floor_pos.mpr (by linarith)
  have N_le_t : N ≤ |t| := Nat.floor_le <| abs_nonneg _
  have logt_gt := logt_gt_one t_gt.le
  have σ_gt : 1 - A < σ := by
    apply lt_of_lt_of_le ((sub_lt_sub_iff_left (a := 1)).mpr ?_) σ_ge
    exact (div_lt_iff₀ (by linarith)).mpr <| lt_mul_right hA.1 logt_gt
  refine ⟨Npos, N_le_t, logt_gt, σ_gt, by linarith [hA.2], ?_⟩
  contrapose! t_gt
  simp only [Complex.ext_iff, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
    sub_self, add_zero, one_re, add_im, mul_im, zero_add, one_im] at t_gt
  norm_num [t_gt.2]

lemma UpperBnd_aux2 {A σ t : ℝ} (t_ge : 3 < |t|) (σ_ge : 1 - A / Real.log |t| ≤ σ) :
      |t| ^ (1 - σ) ≤ Real.exp A := by
  have : |t| ^ (1 - σ) ≤ |t| ^ (A / Real.log |t|) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  apply le_trans this ?_
  conv => lhs; lhs; rw [← Real.exp_log (by linarith : 0 < |t|)]
  rw [div_eq_mul_inv, Real.rpow_mul (by positivity), ← Real.exp_mul, ← Real.exp_mul, mul_comm,
    ← mul_assoc, inv_mul_cancel₀, one_mul]
  apply Real.log_ne_zero.mpr; split_ands <;> linarith

lemma riemannZeta0_zero_aux (N : ℕ) (Npos : 0 < N) :
    ∑ x ∈ Finset.Ico 0 N, ((x : ℝ))⁻¹ = ∑ x ∈ Finset.Ico 1 N, ((x : ℝ))⁻¹ := by
  have : Finset.Ico 1 N ⊆ Finset.Ico 0 N := by
    intro x hx
    simp only [Finset.mem_Ico, Nat.Ico_zero_eq_range, Finset.mem_range] at hx ⊢
    exact hx.2
  rw [← Finset.sum_sdiff (s₁ := Finset.Ico 1 N) (s₂ := Finset.Ico 0 N) this]
  have : Finset.Ico 0 N \ Finset.Ico 1 N = Finset.range 1 := by
    ext a
    simp only [Nat.Ico_zero_eq_range, Finset.mem_sdiff, Finset.mem_range, Finset.mem_Ico, not_and,
      not_lt, Finset.range_one, Finset.mem_singleton]
    exact ⟨fun _ ↦ by omega, fun ha ↦ ⟨by simp [ha, Npos], by omega⟩⟩
  rw [this]; simp

lemma UpperBnd_aux3 {A C σ t : ℝ} (hA : A ∈ Ioc 0 (1 / 2))
    (σ_ge : 1 - A / Real.log |t| ≤ σ) (t_gt : 3 < |t|) (hC : 2 ≤ C) : let N := ⌊|t|⌋₊;
    ‖∑ n ∈ Finset.range (N + 1), (n : ℂ) ^ (-(σ + t * I))‖ ≤
      Real.exp A * C * Real.log |t| := by
  intro N
  obtain ⟨Npos, N_le_t, _, _, σPos, _⟩ := UpperBnd_aux hA t_gt σ_ge
  have logt_gt := logt_gt_one t_gt.le
  have (n : ℕ) (hn : n ∈ Finset.range (N + 1)) := ZetaBnd_aux2 (n := n) hA.1 σPos ?_ σ_ge
  · replace := norm_sum_le_of_le (Finset.range (N + 1)) this
    rw [← Finset.sum_mul, mul_comm _ (Real.exp A)] at this
    rw [mul_assoc]
    apply le_trans this <| (mul_le_mul_iff_right₀ A.exp_pos).mpr ?_
    have : 1 + Real.log (N : ℝ) ≤ C * Real.log |t| := by
      by_cases hN : N = 1
      · simp only [hN, Nat.cast_one, Real.log_one, add_zero]
        have : 2 * 1 ≤ C * Real.log |t| := mul_le_mul hC logt_gt.le (by linarith) (by linarith)
        linarith
      · rw [(by ring : C * Real.log |t| = Real.log |t| + (C - 1) * Real.log |t|),
          ← one_mul <| Real.log (N: ℝ)]
        apply add_le_add logt_gt.le
        refine mul_le_mul (by linarith) ?_ (by positivity) (by linarith)
        exact Real.log_le_log (by positivity) N_le_t
    refine le_trans ?_ this
    convert! harmonic_eq_sum_Icc ▸ harmonic_le_one_add_log N
    · simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, Finset.range_eq_Ico]
      rw [riemannZeta0_zero_aux (N + 1) (by linarith)]; congr! 1
  · simp only [Finset.mem_range] at hn
    linarith [(by exact_mod_cast (by omega : n ≤ N) : (n : ℝ) ≤ N)]

lemma Nat.self_div_floor_bound {t : ℝ} (t_ge : 1 ≤ |t|) : let N := ⌊|t|⌋₊;
    (|t| / N) ∈ Icc 1 2 := by
  intro N
  have Npos : 0 < N := Nat.floor_pos.mpr (by linarith)
  have N_le_t : N ≤ |t| := Nat.floor_le <| abs_nonneg _
  constructor
  · apply le_div_iff₀ (by simp [Npos]) |>.mpr; simp [N_le_t]
  · apply div_le_iff₀ (by positivity) |>.mpr
    suffices |t| < N + 1 by linarith [(by exact_mod_cast (by omega) : 1 ≤ (N : ℝ))]
    apply Nat.lt_floor_add_one

lemma UpperBnd_aux5 {σ t : ℝ} (t_ge : 3 < |t|) (σ_le : σ ≤ 2) : (|t| / ⌊|t|⌋₊) ^ σ ≤ 4 := by
  obtain ⟨h₁, h₂⟩ := Nat.self_div_floor_bound (by linarith)
  calc _ ≤ ((|t| / ↑⌊|t|⌋₊) ^ (2 : ℝ)) := by gcongr
       _ ≤ (2 : ℝ) ^ (2 : ℝ) := by gcongr
       _ = 4 := by norm_num

lemma UpperBnd_aux6 {σ t : ℝ} (t_ge : 3 < |t|) (hσ : σ ∈ Ioc (1 / 2) 2)
    (neOne : σ + t * I ≠ 1) (Npos : 0 < ⌊|t|⌋₊) (N_le_t : ⌊|t|⌋₊ ≤ |t|) :
    ⌊|t|⌋₊ ^ (1 - σ) / ‖1 - (σ + t * I)‖ ≤ |t| ^ (1 - σ) * 2 ∧
    ⌊|t|⌋₊ ^ (-σ) / 2 ≤ |t| ^ (1 - σ) ∧ ⌊|t|⌋₊ ^ (-σ) / σ ≤ 8 * |t| ^ (-σ) := by
  have bnd := UpperBnd_aux5 t_ge hσ.2
  have bnd' : (|t| / ⌊|t|⌋₊) ^ σ ≤ 2 * |t| := by linarith
  split_ands
  · apply (div_le_iff₀ <| norm_pos_iff.mpr <| sub_ne_zero_of_ne neOne.symm).mpr
    conv => rw [mul_assoc]; rhs; rw [mul_comm]
    apply (div_le_iff₀ <| Real.rpow_pos_of_pos (by linarith) _).mp
    rw [div_rpow_eq_rpow_div_neg (by positivity) (by positivity), neg_sub]
    refine le_trans₄ ?_ bnd' ?_
    · exact Real.rpow_le_rpow_of_exponent_le (one_le_div (by positivity) |>.mpr N_le_t) (by simp)
    · apply (mul_le_mul_iff_right₀ (by norm_num)).mpr; simpa using abs_im_le_norm (1 - (σ + t * I))
  · apply div_le_iff₀ (by norm_num) |>.mpr
    rw [Real.rpow_sub (by linarith), Real.rpow_one, div_mul_eq_mul_div, mul_comm]
    apply div_le_iff₀ (by positivity) |>.mp
    convert! bnd' using 1
    rw [← Real.rpow_neg (by linarith), div_rpow_neg_eq_rpow_div (by positivity) (by positivity)]
  · apply div_le_iff₀ (by linarith [hσ.1]) |>.mpr
    rw [mul_assoc, mul_comm, mul_assoc]
    apply div_le_iff₀' (by positivity) |>.mp
    apply le_trans ?_ (by linarith [hσ.1] : 4 ≤ σ * 8)
    convert! bnd using 1; exact div_rpow_neg_eq_rpow_div (by positivity) (by positivity)

lemma ZetaUpperBnd' {A σ t : ℝ} (hA : A ∈ Ioc 0 (1 / 2)) (t_gt : 3 < |t|)
    (hσ : σ ∈ Icc (1 - A / Real.log |t|) 2) :
    let C := Real.exp A * (5 + 8 * 2); 
    let N := ⌊|t|⌋₊;
    let s := σ + t * I;
    ‖∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s‖ + ‖(N : ℂ) ^ (1 - s) / (1 - s)‖
    + ‖(N : ℂ) ^ (-s) / 2‖
    + ‖s * ∫ (x : ℝ) in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)‖
    ≤ C * Real.log |t| := by
  intros C N s
  obtain ⟨Npos, N_le_t, logt_gt, σ_gt, σPos, neOne⟩ := UpperBnd_aux hA t_gt hσ.1
  replace σ_gt : 1 / 2 < σ := by linarith [hA.2]
  calc
    _ ≤ Real.exp A * 2 * Real.log |t| + ‖N ^ (1 - s) / (1 - s)‖ + ‖(N : ℂ) ^ (-s) / 2‖ +
      ‖s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)‖ := ?_
    _ ≤ Real.exp A * 2 * Real.log |t| + ‖N ^ (1 - s) / (1 - s)‖ + ‖(N : ℂ) ^ (-s) / 2‖ +
      2 * |t| * N ^ (-σ) / σ  := ?_
    _ = Real.exp A * 2 * Real.log |t| + N ^ (1 - σ) / ‖(1 - s)‖ + N ^ (-σ) / 2 +
      2 * |t| * N ^ (-σ) / σ  := ?_
    _ ≤ Real.exp A * 2 * Real.log |t| + |t| ^ (1 - σ) * 2 +
        |t| ^ (1 - σ) + 2 * |t| * (8 * |t| ^ (-σ)) := ?_
    _ = Real.exp A * 2 * Real.log |t| + (3 + 8 * 2) * |t| ^ (1 - σ) := ?_
    _ ≤ Real.exp A * 2 * Real.log |t| + (3 + 8 * 2) * Real.exp A * 1 := ?_
    _ ≤ Real.exp A * 2 * Real.log |t| + (3 + 8 * 2) * Real.exp A * Real.log |t| := ?_
    _ = _ := by ring
  · simp only [add_le_add_iff_right, one_div_cpow_eq_cpow_neg]
    convert UpperBnd_aux3 (C := 2) hA hσ.1 t_gt le_rfl using 1
  · simp only [add_le_add_iff_left]; exact ZetaBnd_aux1 N (by linarith) ⟨σPos, hσ.2⟩ (by linarith)
  · simp only [norm_div, RCLike.norm_ofNat, s]
    congr <;> (convert norm_natCast_cpow_of_pos Npos _; simp)
  · have ⟨h₁, h₂, h₃⟩ := UpperBnd_aux6 t_gt ⟨σ_gt, hσ.2⟩ neOne Npos N_le_t
    gcongr
    rw [mul_div_assoc]
    gcongr
  · ring_nf; conv => lhs; rhs; lhs; rw [mul_comm |t|]
    rw [← Real.rpow_add_one (by positivity)]; ring_nf
  · simp only [Real.log_abs, add_le_add_iff_left, mul_one]
    exact mul_le_mul_iff_right₀ (by positivity) |>.mpr <| UpperBnd_aux2 t_gt hσ.1
  · simp only [add_le_add_iff_left]
    apply mul_le_mul_iff_right₀ (by norm_num [Real.exp_pos]) |>.mpr <| logt_gt.le

lemma ZetaUpperBnd :
    ∃ (A : ℝ) (_ : A ∈ Ioc 0 (1 / 2)) (C : ℝ) (_ : 0 < C), ∀ (σ : ℝ) (t : ℝ) (_ : 3 < |t|)
    (_ : σ ∈ Icc (1 - A / Real.log |t|) 2), ‖riemannZeta (σ + t * I)‖ ≤ C * Real.log |t| := by
  let A := (1 / 2 : ℝ)
  let C := Real.exp A * (5 + 8 * 2) 
  refine ⟨A, ⟨by norm_num, by norm_num⟩, C, (by positivity), ?_⟩
  intro σ t t_gt ⟨σ_ge, σ_le⟩
  obtain ⟨Npos, _, _, _, σPos, neOne⟩ := UpperBnd_aux ⟨by norm_num, by norm_num⟩ t_gt σ_ge
  rw [← Zeta0EqZeta Npos (by simp [σPos]) neOne]
  apply le_trans (by apply norm_add₄_le) ?_
  convert! ZetaUpperBnd' ⟨by norm_num, le_rfl⟩ t_gt ⟨σ_ge, σ_le⟩ using 1; simp

lemma norm_complex_log_ofNat (n : ℕ) : ‖(n : ℂ).log‖ = (n : ℝ).log := by
  have := Complex.ofReal_log (x := (n : ℝ)) (Nat.cast_nonneg n)
  rw [(by simp : ((n : ℝ) : ℂ) = (n : ℂ))] at this
  rw [← this, Complex.norm_of_nonneg]
  exact Real.log_natCast_nonneg n

lemma Real.log_natCast_monotone : Monotone (fun (n : ℕ) ↦ Real.log n) := by
  intro n m hnm
  cases n
  · simp only [CharP.cast_eq_zero, Real.log_zero, Real.log_natCast_nonneg]
  · apply Real.log_le_log <;> simp only [Nat.cast_add, Nat.cast_one]
    · exact Nat.cast_add_one_pos _
    · exact_mod_cast hnm

lemma Finset.Icc0_eq (N : ℕ) : Finset.Icc 0 N = {0} ∪ Finset.Icc 1 N := by
  refine Finset.ext_iff.mpr ?_
  intro a
  cases a
  · simp only [Finset.mem_Icc, le_refl, zero_le, and_self, Finset.mem_union, Finset.mem_singleton,
    nonpos_iff_eq_zero, one_ne_zero, and_true, or_false]
  · simp only [Finset.mem_Icc, le_add_iff_nonneg_left, zero_le, true_and, Finset.mem_union,
    Finset.mem_singleton, add_eq_zero, one_ne_zero, and_false, false_or]

lemma harmonic_eq_sum_Icc0_aux (N : ℕ) :
    ∑ i ∈ Finset.Icc 0 N, (i : ℝ)⁻¹ = ∑ i ∈ Finset.Icc 1 N, (i : ℝ)⁻¹ := by
  rw [Finset.Icc0_eq, Finset.sum_union]
  · simp only [Finset.sum_singleton, CharP.cast_eq_zero, inv_zero, zero_add]
  · simp only [Finset.disjoint_singleton_left, Finset.mem_Icc, nonpos_iff_eq_zero, one_ne_zero,
    zero_le, and_true, not_false_eq_true]

lemma harmonic_eq_sum_Icc0 (N : ℕ) : ∑ i ∈ Finset.Icc 0 N, (i : ℝ)⁻¹ = (harmonic N : ℝ) := by
  rw [harmonic_eq_sum_Icc0_aux, harmonic_eq_sum_Icc]
  simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]

lemma DerivUpperBnd_aux1 {A C σ t : ℝ} (hA : A ∈ Ioc 0 (1 / 2))
    (σ_ge : 1 - A / Real.log |t| ≤ σ) (t_gt : 3 < |t|) (hC : 2 ≤ C) : let N := ⌊|t|⌋₊;
    ‖∑ n ∈ Finset.range (N + 1), -1 / (n : ℂ) ^ (σ + t * I) * (Real.log n)‖
      ≤ Real.exp A * C * (Real.log |t|) ^ 2 := by
  intro N
  obtain ⟨Npos, N_le_t, _, _, σPos, _⟩ := UpperBnd_aux hA t_gt σ_ge
  have logt_gt := logt_gt_one t_gt.le
  have logN_pos : 0 ≤ Real.log N := Real.log_nonneg (by norm_cast)
  have fact0 {n : ℕ} (hn : n ≤ N) : n ≤ |t| := by linarith [(by exact_mod_cast hn : (n : ℝ) ≤ N)]
  have fact1 {n : ℕ} (hn : n ≤ N) :
    ‖(n : ℂ) ^ (-(σ + t * I))‖ ≤ (n : ℝ)⁻¹ * A.exp := ZetaBnd_aux2 hA.1 σPos (fact0 hn) σ_ge
  have fact2 {n : ℕ} (hn : n ≤ N) : Real.log n ≤ Real.log |t| := by
    cases n
    · simp only [CharP.cast_eq_zero, Real.log_zero]; linarith
    · exact Real.log_le_log (by exact_mod_cast Nat.add_one_pos _) (fact0 hn)
  have fact3 (n : ℕ) (hn : n ≤ N) :
    ‖-1 / (n : ℂ) ^ (σ + t * I) * (Real.log n)‖ ≤ (n : ℝ)⁻¹ * Real.exp A * (Real.log |t|) := by
    convert! mul_le_mul (fact1 hn) (fact2 hn) (Real.log_natCast_nonneg n) (by positivity)
    simp only [norm_mul, norm_div, norm_neg, norm_one, one_div, natCast_log, ← norm_inv, cpow_neg]
    congr; exact norm_complex_log_ofNat n
  have := norm_sum_le_of_le (Finset.range (N + 1))
    (by simp only [Finset.mem_range, Nat.lt_succ_iff]; exact fact3)
  rw [← Finset.sum_mul, ← Finset.sum_mul, mul_comm _ A.exp, mul_assoc] at this
  rw [mul_assoc]
  apply le_trans this <| (mul_le_mul_iff_right₀ A.exp_pos).mpr ?_
  rw [pow_two, ← mul_assoc, Finset.range_eq_Ico, ← Finset.Icc_eq_Ico, harmonic_eq_sum_Icc0]
  apply le_trans (mul_le_mul (h₁ := harmonic_le_one_add_log (n := N)) (le_refl (Real.log |t|))
    (by linarith) (by linarith))
  apply (mul_le_mul_iff_left₀ (by linarith)).mpr
  rw [(by ring : C * Real.log |t| = Real.log |t| + (C - 1) * Real.log |t|),
      ← one_mul <| Real.log (N: ℝ)]
  refine add_le_add logt_gt.le <| mul_le_mul (by linarith) ?_ (by positivity) (by linarith)
  exact Real.log_le_log (by positivity) N_le_t

lemma DerivUpperBnd_aux2 {A σ t : ℝ} (t_gt : 3 < |t|) (hσ : σ ∈ Icc (1 - A / |t|.log) 2) :
    let N := ⌊|t|⌋₊;
    let s := ↑σ + ↑t * I;
    0 < N → ↑N ≤ |t| → s ≠ 1 →
    1 / 2 < σ → ‖-↑N ^ (1 - s) / (1 - s) ^ 2‖ ≤ A.exp * 2 * (1 / 3) := by
  intro N s Npos N_le_t neOne σ_gt
  dsimp only [s]
  simp_rw [norm_div, norm_neg, norm_pow, norm_natCast_cpow_of_pos Npos _,
    sub_re, one_re, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
    mul_one, sub_self, add_zero]
  have h := UpperBnd_aux6 t_gt ⟨σ_gt, hσ.2⟩ neOne Npos N_le_t |>.1
  rw [(by ring_nf : N ^ (1 - σ) / ‖1 - (↑σ + ↑t * I)‖ ^ 2 =
          N ^ (1 - σ) / ‖1 - (↑σ + ↑t * I)‖ * 1 / ‖1 - (↑σ + ↑t * I)‖)]
  apply mul_le_mul ?_ ?_ (inv_nonneg.mpr <| norm_nonneg _) ?_
  · rw [mul_one]; exact le_trans h (by gcongr; exact UpperBnd_aux2 t_gt hσ.1)
  · rw [inv_eq_one_div, div_le_iff₀ <| norm_pos_iff.mpr <| sub_ne_zero_of_ne neOne.symm,
        mul_comm, ← mul_div_assoc, mul_one, le_div_iff₀ (by norm_num), one_mul]
    apply le_trans t_gt.le ?_
    rw [← abs_neg]; convert! abs_im_le_norm (1 - (σ + t * I)); simp
  · exact mul_nonneg (Real.exp_nonneg _) (by norm_num)

theorem DerivUpperBnd_aux3 {A σ t : ℝ} (t_gt : 3 < |t|) (hσ : σ ∈ Icc (1 - A / |t|.log) 2) :
    let N := ⌊|t|⌋₊;
    let s := ↑σ + ↑t * I;
    0 < N → ↑N ≤ |t| → s ≠ 1 → 1 / 2 < σ →
    ‖↑(N : ℝ).log * ↑N ^ (1 - s) / (1 - s)‖ ≤ A.exp * 2 * |t|.log := by
  intro N s Npos N_le_t neOne σ_gt
  rw [norm_div, norm_mul, mul_div_assoc, mul_comm]
  apply mul_le_mul ?_ ?_ (by positivity) (by positivity)
  · have h := UpperBnd_aux6 t_gt ⟨σ_gt, hσ.2⟩ neOne Npos N_le_t |>.1
    convert le_trans h ?_ using 1
    · simp [s, norm_natCast_cpow_of_pos Npos _, N]
    · gcongr; exact UpperBnd_aux2 t_gt hσ.1
  · rw [natCast_log, norm_complex_log_ofNat]
    exact Real.log_le_log (by positivity) N_le_t

theorem DerivUpperBnd_aux4 {A σ t : ℝ} (t_gt : 3 < |t|) (hσ : σ ∈ Icc (1 - A / |t|.log) 2) :
    let N := ⌊|t|⌋₊;
    let s := ↑σ + ↑t * I;
    0 < N → ↑N ≤ |t| → s ≠ 1 → 1 / 2 < σ →
    ‖↑(N : ℝ).log * (N : ℂ) ^ (-s) / 2‖ ≤ A.exp * |t|.log := by
  intro N s Npos N_le_t neOne σ_gt
  rw [norm_div, norm_mul, mul_div_assoc, mul_comm, RCLike.norm_ofNat]
  apply mul_le_mul ?_ ?_ (by positivity) (by positivity)
  · have h := UpperBnd_aux6 t_gt ⟨σ_gt, hσ.2⟩ neOne Npos N_le_t |>.2.1
    convert le_trans h (UpperBnd_aux2 t_gt hσ.1) using 1
    simp [s, norm_natCast_cpow_of_pos Npos _, N]
  · rw [natCast_log, norm_complex_log_ofNat]
    exact Real.log_le_log (by positivity) N_le_t

theorem DerivUpperBnd_aux5 {A σ t : ℝ} (t_gt : 3 < |t|) (hσ : σ ∈ Icc (1 - A / |t|.log) 2) :
    let N := ⌊|t|⌋₊;
    let s := ↑σ + ↑t * I;
    0 < N → 1 / 2 < σ →
    ‖1 * ∫ (x : ℝ) in Ioi (N : ℝ), (↑⌊x⌋ + 1 / 2 - ↑x) * (x : ℂ) ^ (-s - 1)‖ ≤
    1 / 3 * (2 * |t| * ↑N ^ (-σ) / σ) := by
  intro N s Npos σ_gt
  have neZero : s ≠ 0 := by
    contrapose! σ_gt
    simp only [Complex.ext_iff, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
      sub_self, add_zero, zero_re, add_im, mul_im, zero_add, zero_im, s] at σ_gt
    linarith
  have : 1 = 1 / s * s := by field_simp
  nth_rewrite 1 [this]
  rw [mul_assoc, norm_mul]
  apply mul_le_mul ?_ ?_ (by positivity) (by positivity)
  · simp only [s, norm_div, norm_one]
    apply one_div_le_one_div (norm_pos_iff.mpr neZero) (by norm_num) |>.mpr
    apply le_trans t_gt.le ?_
    convert! abs_im_le_norm (σ + t * I); simp
  · have hσ : σ ∈ Ioc 0 2 := ⟨(by linarith), hσ.2⟩
    simp only [s]
    have := ZetaBnd_aux1 N (by omega) hσ (by linarith)
    simp only [div_cpow_eq_cpow_neg] at this
    convert! this using 1; congr; funext x; ring_nf

theorem DerivUpperBnd_aux6 {A σ t : ℝ} (t_gt : 3 < |t|) (hσ : σ ∈ Icc (1 - A / |t|.log) 2) :
    let N := ⌊|t|⌋₊;
    0 < N → ↑N ≤ |t| → ↑σ + ↑t * I ≠ 1 → 1 / 2 < σ →
    2 * |t| * ↑N ^ (-σ) / σ ≤ 2 * (8 * A.exp) := by
  intro N Npos N_le_t neOne σ_gt
  rw [mul_div_assoc, mul_assoc]
  apply mul_le_mul_iff_right₀ (by norm_num) |>.mpr
  have h := UpperBnd_aux6 t_gt ⟨σ_gt, hσ.2⟩ neOne Npos N_le_t |>.2.2
  apply le_trans (mul_le_mul_iff_right₀ (a := |t|) (by positivity) |>.mpr h) ?_
  rw [← mul_assoc, mul_comm _ 8, mul_assoc]
  gcongr
  convert! UpperBnd_aux2 t_gt hσ.1 using 1
  rw [mul_comm, ← Real.rpow_add_one (by positivity)]; ring_nf

lemma DerivUpperBnd_aux7_1 {x σ t : ℝ} (hx : 1 ≤ x) :
    let s := ↑σ + ↑t * I;
    ‖(↑⌊x⌋ + 1 / 2 - ↑x) * (x : ℂ) ^ (-s - 1) * -↑x.log‖ = |(↑⌊x⌋ + 1 / 2 - x)| * x ^ (-σ - 1) * x.log := by
  have xpos : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have : ‖(x.log : ℂ)‖ = x.log := Complex.norm_of_nonneg <| Real.log_nonneg hx
  simp [← norm_real, this, Complex.norm_cpow_eq_rpow_re_of_pos xpos, ← Real.norm_eq_abs, ← ofReal_ofNat,
    ← ofReal_inv, ← ofReal_add, ← ofReal_sub, ← ofReal_intCast, one_div]

lemma DerivUpperBnd_aux7_2 {x σ : ℝ} (hx : 1 ≤ x) :
    |(↑⌊x⌋ + 1 / 2 - x)| * x ^ (-σ - 1) * x.log ≤ x ^ (-σ - 1) * x.log := by
  rw [← one_mul (x ^ (-σ - 1) * Real.log x), mul_assoc]
  apply mul_le_mul_of_nonneg_right _ (by bound)
  exact le_trans (ZetaSum_aux1_3 x) (by norm_num)

lemma DerivUpperBnd_aux7_3 {x σ : ℝ} (xpos : 0 < x) (σnz : σ ≠ 0) :
    HasDerivAt (fun t ↦ -(1 / σ ^ 2 * t ^ (-σ) + 1 / σ * t ^ (-σ) * Real.log t))
      (x ^ (-σ - 1) * Real.log x) x := by
  have h1 := Real.hasDerivAt_rpow_const (p := -σ) (Or.inl xpos.ne.symm)
  have h2 := h1.const_mul (1 / σ^2)
  have cancel : 1 / σ^2 * σ = 1 / σ := by field_simp
  rw [neg_mul, mul_neg, ← mul_assoc, cancel] at h2
  have h3 := Real.hasDerivAt_log xpos.ne.symm
  have h4 := HasDerivAt.mul (h1.const_mul (1 / σ)) h3
  have cancel := Real.rpow_add xpos (-σ) (-1)
  have : -σ + -1 = -σ - 1 := by rfl
  rw [← Real.rpow_neg_one x, mul_assoc (1 / σ) (x ^ (-σ)), ← cancel, this] at h4
  convert! h2.add h4 |>.neg using 1
  field_simp; ring

lemma DerivUpperBnd_aux7_3' {a σ : ℝ} (apos : 0 < a) (σnz : σ ≠ 0) :
    ∀ x ∈ Ici a, HasDerivAt (fun t ↦ -(1 / σ ^ 2 * t ^ (-σ) + 1 / σ * t ^ (-σ) * Real.log t))
      (x ^ (-σ - 1) * Real.log x) x := by
  intro x hx
  simp at hx
  exact DerivUpperBnd_aux7_3 (by linarith) σnz

lemma DerivUpperBnd_aux7_nonneg {a σ : ℝ} (ha : 1 ≤ a) :
    ∀ x ∈ Ioi a, 0 ≤ x ^ (-σ - 1) * Real.log x := by
  intro x hx
  simp at hx
  bound

lemma DerivUpperBnd_aux7_tendsto {σ : ℝ} (σpos : 0 < σ) :
    Tendsto (fun t ↦ -(1 / σ ^ 2 * t ^ (-σ) + 1 / σ * t ^ (-σ) * Real.log t)) atTop (nhds 0) := by
  have h1 := tendsto_rpow_neg_atTop σpos
  have h2 := h1.const_mul (1 / σ^2)
  have h3 : Tendsto (fun t : ℝ ↦ t ^ (-σ) * Real.log t) atTop (nhds 0) := by
    have := Real.tendsto_pow_log_div_pow_atTop σ 1 σpos
    simp only [Real.rpow_one] at this
    apply Tendsto.congr' _ this
    filter_upwards [eventually_ge_atTop 0] with x hx
    rw [mul_comm]
    apply div_rpow_eq_rpow_neg _ _ _ hx
  have h4 := h3.const_mul (1 / σ)
  have h5 := (h2.add h4).neg
  convert h5 using 1
  · ext; ring
  simp

open MeasureTheory in
lemma DerivUpperBnd_aux7_4 {a σ : ℝ} (σpos : 0 < σ) (ha : 1 ≤ a) :
    IntegrableOn (fun x ↦ x ^ (-σ - 1) * Real.log x) (Ioi a) volume := by
  apply integrableOn_Ioi_deriv_of_nonneg' (l := 0)
  · exact DerivUpperBnd_aux7_3' (by linarith) (by linarith)
  · exact DerivUpperBnd_aux7_nonneg ha
  · exact DerivUpperBnd_aux7_tendsto σpos

open MeasureTheory in
lemma DerivUpperBnd_aux7_5 {a σ : ℝ} (σpos : 0 < σ) (ha : 1 ≤ a) :
    IntegrableOn (fun x ↦ |(↑⌊x⌋ + (1 : ℝ) / 2 - x)| * x ^ (-σ - 1) * Real.log x)
      (Ioi a) volume := by
  simp_rw [mul_assoc]
  apply Integrable.bdd_mul (c := 1 / 2) <| DerivUpperBnd_aux7_4 σpos ha
  · exact Measurable.aestronglyMeasurable <| Measurable.abs measurable_floor_add_half_sub
  apply ae_of_all
  intro x
  simp only [Real.norm_eq_abs, _root_.abs_abs]
  exact  ZetaSum_aux1_3 x

open MeasureTheory in
lemma DerivUpperBnd_aux7_integral_eq {a σ : ℝ} (ha : 1 ≤ a) (σpos : 0 < σ) :
    ∫ (x : ℝ) in Ioi a, x ^ (-σ - 1) * Real.log x =
      1 / σ^2 * a ^ (-σ) + 1 / σ * a ^ (-σ) * Real.log a := by
  convert integral_Ioi_of_hasDerivAt_of_nonneg'
    (DerivUpperBnd_aux7_3' (by linarith) (by linarith))
    (DerivUpperBnd_aux7_nonneg ha) (DerivUpperBnd_aux7_tendsto σpos) using 1
  ring

open MeasureTheory in

theorem DerivUpperBnd_aux7 {A σ t : ℝ} (t_gt : 3 < |t|) (hσ : σ ∈ Icc (1 - A / |t|.log) 2) :
    let N := ⌊|t|⌋₊;
    let s := ↑σ + ↑t * I;
    0 < N → ↑N ≤ |t| → s ≠ 1 → 1 / 2 < σ →
    ‖s * ∫ (x : ℝ) in Ioi (N : ℝ), (↑⌊x⌋ + 1 / 2 - ↑x) * (x : ℂ) ^ (-s - 1) * -↑x.log‖ ≤
      6 * |t| * ↑N ^ (-σ) / σ * |t|.log := by
  intro N s Npos N_le_t neOne σ_gt
  have σpos : 0 < σ := lt_trans (by norm_num) σ_gt
  rw [norm_mul, (by ring : 6 * |t| * ↑N ^ (-σ) / σ * Real.log |t| = (2 * |t|) * (3 * ↑N ^ (-σ) / σ * Real.log |t|))]
  apply mul_le_mul _ _ (by positivity) (by positivity)
  · apply le_trans (by apply norm_add_le)
    simp [abs_of_pos σpos]
    linarith [hσ.2]
  apply le_trans (by apply norm_integral_le_integral_norm)
  calc ∫ (x : ℝ) in Ioi (N : ℝ), ‖(↑⌊x⌋ + 1 / 2 - ↑x) * (x : ℂ) ^ (-s - 1) * -↑x.log‖
    _ = ∫ (x : ℝ) in Ioi (N : ℝ), |(↑⌊x⌋ + 1 / 2 - x)| * x ^ (-σ - 1) * x.log := by
      apply setIntegral_congr_fun (by measurability)
      intro x hx
      simp only [mem_Ioi] at hx
      exact DerivUpperBnd_aux7_1 (lt_of_le_of_lt (mod_cast Npos) hx).le
    _ ≤ ∫ (x : ℝ) in Ioi (N : ℝ), x ^ (-σ - 1) * x.log := by
      apply setIntegral_mono_on _ _ (by measurability)
      · intro x hx
        exact DerivUpperBnd_aux7_2 (lt_of_le_of_lt (mod_cast Npos) hx).le
      · apply DerivUpperBnd_aux7_5 σpos (mod_cast Npos)
      apply DerivUpperBnd_aux7_4 σpos (mod_cast Npos)
    _ = 1 / σ^2 * N ^ (-σ) + 1 / σ * N ^ (-σ) * Real.log N :=
      DerivUpperBnd_aux7_integral_eq (mod_cast Npos) σpos
    _ ≤ 3 * ↑N ^ (-σ) / σ * |t|.log := by
      have h2 : 1 / σ * ↑N ^ (-σ) * Real.log ↑N ≤ ↑N ^ (-σ) / σ * Real.log |t| := calc
        _ = ↑N ^ (-σ) / σ * Real.log N := by ring
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact Real.log_le_log (mod_cast Npos) N_le_t
      have : 2 ≤ 2 * Real.log |t| := by
        nth_rewrite 1  [← mul_one 2]
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact logt_gt_one t_gt.le |>.le
      have h1 : 1 / σ^2 * ↑N ^ (-σ) ≤ 2 * ↑N ^ (-σ) / σ * Real.log |t| := calc
        1 / σ^2 * ↑N ^ (-σ) = (↑N ^ (-σ) / σ) * (1 / σ) := by ring
        _ ≤ ↑N ^ (-σ) / σ * (2 * Real.log |t|):= by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply le_trans _ this
          exact (one_div_le σpos (by norm_num)).mpr σ_gt.le
        _ = _ := by ring
      convert! add_le_add h1 h2 using 1
      ring

lemma ZetaDerivUpperBnd' {A σ t : ℝ} (hA : A ∈ Ioc 0 (1 / 2)) (t_gt : 3 < |t|)
    (hσ : σ ∈ Icc (1 - A / Real.log |t|) 2) :
    let C := Real.exp A * 59;
    let N := ⌊|t|⌋₊;
    let s := σ + t * I;
    ‖∑ n ∈ Finset.range (N + 1), -1 / (n : ℂ) ^ s * (Real.log n)‖ +
      ‖-(N : ℂ) ^ (1 - s) / (1 - s) ^ 2‖ +
      ‖(Real.log N) * (N : ℂ) ^ (1 - s) / (1 - s)‖ +
      ‖(Real.log N) * (N : ℂ) ^ (-s) / 2‖ +
      ‖(1 * ∫ (x : ℝ) in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-s - 1))‖ +
      ‖s * ∫ (x : ℝ) in Ioi (N : ℝ),
        (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-s - 1) * -(Real.log x)‖
        ≤ C * Real.log |t| ^ 2 := by
  intros C N s
  obtain ⟨Npos, N_le_t, logt_gt, σ_gt, _, neOne⟩ := UpperBnd_aux hA t_gt hσ.1
  replace σ_gt : 1 / 2 < σ := by linarith [hA.2]
  calc _ ≤ Real.exp A * 2 * (Real.log |t|) ^ 2 +
      ‖-(N : ℂ) ^ (1 - s) / (1 - s) ^ 2‖ +
      ‖(Real.log N) * (N : ℂ) ^ (1 - s) / (1 - s)‖ +
      ‖(Real.log N) * (N : ℂ) ^ (-s) / 2‖ +
      ‖(1 * ∫ (x : ℝ) in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-s - 1))‖ +
      ‖s * ∫ (x : ℝ) in Ioi (N : ℝ),
        (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-s - 1) * -(Real.log x)‖ := by
        gcongr; exact DerivUpperBnd_aux1 hA hσ.1 t_gt (by simp : (2 : ℝ) ≤ 2)
    _ ≤ Real.exp A * 2 * (Real.log |t|) ^ 2 +
      Real.exp A * 2 * (1 / 3) +
      ‖(Real.log N) * (N : ℂ) ^ (1 - s) / (1 - s)‖ +
      ‖(Real.log N) * (N : ℂ) ^ (-s) / 2‖ +
      ‖(1 * ∫ (x : ℝ) in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-s - 1))‖ +
      ‖s * ∫ (x : ℝ) in Ioi (N : ℝ),
        (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-s - 1) * -(Real.log x)‖ := by
        gcongr; exact DerivUpperBnd_aux2 t_gt hσ Npos N_le_t neOne σ_gt
    _ ≤ Real.exp A * 2 * (Real.log |t|) ^ 2 +
      Real.exp A * 2 * (1 / 3) +
      Real.exp A * 2 * (Real.log |t|) +
      ‖(Real.log N) * (N : ℂ) ^ (-s) / 2‖ +
      ‖(1 * ∫ (x : ℝ) in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-s - 1))‖ +
      ‖s * ∫ (x : ℝ) in Ioi (N : ℝ),
        (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-s - 1) * -(Real.log x)‖ := by
        gcongr; exact DerivUpperBnd_aux3 t_gt hσ Npos N_le_t neOne σ_gt
    _ ≤ Real.exp A * 2 * (Real.log |t|) ^ 2 +
      Real.exp A * 2 * (1 / 3) +
      Real.exp A * 2 * (Real.log |t|) +
      Real.exp A * (Real.log |t|) +
      ‖(1 * ∫ (x : ℝ) in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-s - 1))‖ +
      ‖s * ∫ (x : ℝ) in Ioi (N : ℝ),
        (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-s - 1) * -(Real.log x)‖ := by
        gcongr; exact DerivUpperBnd_aux4 t_gt hσ Npos N_le_t neOne σ_gt
    _ ≤ Real.exp A * 2 * (Real.log |t|) ^ 2 +
      Real.exp A * 2 * (1 / 3) +
      Real.exp A * 2 * (Real.log |t|) +
      Real.exp A * (Real.log |t|) +
      1 / 3 * (2 * |t| * N ^ (-σ) / σ) +
      ‖s * ∫ (x : ℝ) in Ioi (N : ℝ),
        (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-s - 1) * -(Real.log x)‖ := by
        gcongr; exact DerivUpperBnd_aux5 t_gt hσ Npos σ_gt
    _ ≤ Real.exp A * 2 * (Real.log |t|) ^ 2 +
      Real.exp A * 2 * (1 / 3) +
      Real.exp A * 2 * (Real.log |t|) +
      Real.exp A * (Real.log |t|) +
      1 / 3 * (2 * (8 * Real.exp A)) +
      ‖s * ∫ (x : ℝ) in Ioi (N : ℝ),
        (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-s - 1) * -(Real.log x)‖ := by
        gcongr; exact DerivUpperBnd_aux6 t_gt hσ Npos N_le_t neOne σ_gt
    _ ≤ Real.exp A * 2 * (Real.log |t|) ^ 2 +
      Real.exp A * 2 * (1 / 3) +
      Real.exp A * 2 * (Real.log |t|) +
      Real.exp A * (Real.log |t|) +
      1 / 3 * (2 * (8 * Real.exp A)) +
      (6 * |t| * N ^ (-σ) / σ) * (Real.log |t|) := by
        gcongr; exact DerivUpperBnd_aux7 t_gt hσ Npos N_le_t neOne σ_gt
    _ ≤ Real.exp A * 2 * (Real.log |t|) ^ 2 +
      Real.exp A * 2 * (1 / 3) +
      Real.exp A * 2 * (Real.log |t|) +
      Real.exp A * (Real.log |t|) +
      1 / 3 * (2 * (8 * Real.exp A)) +
      (6 * (8 * Real.exp A)) * (Real.log |t|) := by
        gcongr; convert mul_le_mul_of_nonneg_left (DerivUpperBnd_aux6 t_gt hσ Npos N_le_t neOne σ_gt) (by norm_num : (0 : ℝ) ≤ 3) using 1 <;> ring
    _ ≤ _ := by
      simp only [C]
      ring_nf
      rw [(by ring : A.exp * |t|.log ^ 2 * 59 = A.exp * |t|.log ^ 2 * 6 + A.exp * |t|.log ^ 2 * 51 +
        A.exp * |t|.log ^ 2 * 2)]
      nth_rewrite 1 [← mul_one A.exp]
      gcongr
      swap
      · nth_rewrite 1 [← mul_one |t|.log, (by ring : |t|.log ^ 2 = |t|.log * |t|.log)]
        gcongr
      nlinarith

lemma ZetaDerivUpperBnd :
    ∃ (A : ℝ) (_ : A ∈ Ioc 0 (1 / 2)) (C : ℝ) (_ : 0 < C), ∀ (σ : ℝ) (t : ℝ) (_ : 3 < |t|)
    (_ : σ ∈ Icc (1 - A / Real.log |t|) 2),
    ‖(deriv riemannZeta) (σ + t * I)‖ ≤ C * Real.log |t| ^ 2 := by
  obtain ⟨A, hA, _, _, _⟩ := ZetaUpperBnd
  let C := Real.exp A * 59
  refine ⟨A, hA, C, by positivity, ?_⟩
  intro σ t t_gt ⟨σ_ge, σ_le⟩
  obtain ⟨Npos, N_le_t, _, _, σPos, neOne⟩ := UpperBnd_aux hA t_gt σ_ge
  rw [← DerivZeta0EqDerivZeta Npos (by simp [σPos]) neOne]
  set N : ℕ := ⌊|t|⌋₊
  rw [(HasDerivAtZeta0 Npos (s := σ + t * I) (by simp [σPos]) neOne).deriv]
  dsimp only [ζ₀']
  rw [← add_assoc]
  set aa := ∑ n ∈ Finset.range (N + 1), -1 / (n : ℂ) ^ (σ + t * I) * (Real.log n)
  set bb := -(N : ℂ) ^ (1 - (σ + t * I)) / (1 - (σ + t * I)) ^ 2
  set cc := (Real.log N) * (N : ℂ) ^ (1 - (σ + t * I)) / (1 - (σ + t * I))
  set dd := (Real.log N) * (N : ℂ) ^ (-(σ + t * I)) / 2
  set ee := 1 * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(σ + t * I) - 1)
  set ff := (σ + t * I) * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(σ + t * I) - 1) * -(Real.log x)
  rw [(by ring : aa + (bb + cc) + dd + ee + ff = aa + bb + cc + dd + ee + ff)]
  apply le_trans (by apply norm_add₆_le) ?_
  convert ZetaDerivUpperBnd' hA t_gt ⟨σ_ge, σ_le⟩

lemma Tendsto_nhdsWithin_punctured_map_add {f : ℝ → ℝ} (a x : ℝ)
    (f_mono : StrictMono f) (f_iso : Isometry f) :
    Tendsto (fun y ↦ f y + a) (𝓝[>] x) (𝓝[>] (f x + a)) := by
  refine tendsto_iff_forall_eventually_mem.mpr ?_
  intro v hv
  simp only [mem_nhdsWithin] at hv
  obtain ⟨u, hu, hu2, hu3⟩ := hv
  let t := {x | f x + a ∈ u}
  have : t ∩ Ioi x ∈ 𝓝[>] x := by
    simp only [mem_nhdsWithin]
    use t
    simp only [subset_inter_iff, inter_subset_left, inter_subset_right, and_self,
      and_true, t, mem_setOf_eq]
    refine ⟨?_, by simp [hu2]⟩
    simp only [Metric.isOpen_iff, gt_iff_lt, mem_setOf_eq] at hu ⊢
    intro x hx
    obtain ⟨ε, εpos, hε⟩ := hu (f x + a) hx
    simp only [Metric.ball, setOf_subset_setOf] at hε ⊢
    exact ⟨ε, εpos, fun _ hy ↦ hε (by simp [isometry_iff_dist_eq.mp f_iso, hy])⟩
  filter_upwards [this]
  intro b hb
  simp only [mem_inter_iff, mem_setOf_eq, mem_Ioi, t] at hb
  refine hu3 ?_
  simp only [mem_inter_iff, mem_Ioi, add_lt_add_iff_right]
  exact ⟨hb.1, f_mono hb.2⟩

lemma Tendsto_nhdsWithin_punctured_add (a x : ℝ) :
    Tendsto (fun y ↦ y + a) (𝓝[>] x) (𝓝[>] (x + a)) :=
  Tendsto_nhdsWithin_punctured_map_add a x strictMono_id isometry_id

lemma riemannZeta_isBigO_near_one_horizontal :
    (fun x : ℝ ↦ riemannZeta (1 + x)) =O[𝓝[>] 0] (fun x ↦ (1 : ℂ) / x) := by
  have : (fun w : ℂ ↦ riemannZeta (1 + w)) =O[𝓝[≠] 0] (1 / ·) := by
    have H : Tendsto (fun w ↦ w * riemannZeta (1 + w)) (𝓝[≠] 0) (𝓝 1) := by
      convert Tendsto.comp (f := fun w ↦ 1 + w) riemannZeta_residue_one ?_ using 1
      · ext w
        simp only [Function.comp_apply, add_sub_cancel_left]
      · refine tendsto_iff_comap.mpr <| map_le_iff_le_comap.mp <| Eq.le ?_
        convert Homeomorph.map_punctured_nhds_eq (Homeomorph.addLeft (1 : ℂ)) 0 using 2 <;> simp
    exact ((Asymptotics.isBigO_mul_iff_isBigO_div eventually_mem_nhdsWithin).mp <|
      Tendsto.isBigO_one ℂ H).trans <| Asymptotics.isBigO_refl ..
  exact (isBigO_comp_ofReal_nhds_ne this).mono <| nhdsGT_le_nhdsNE 0

lemma ZetaNear1BndFilter :
    (fun σ : ℝ ↦ riemannZeta σ) =O[𝓝[>](1 : ℝ)] (fun σ ↦ (1 : ℂ) / (σ - 1)) := by
  have := Tendsto_nhdsWithin_punctured_add (a := -1) (x := 1)
  simp only [add_neg_cancel, ← sub_eq_add_neg] at this
  have := riemannZeta_isBigO_near_one_horizontal.comp_tendsto this
  convert this using 1 <;> {ext; simp}

lemma ZetaNear1BndExact :
    ∃ (c : ℝ) (_ : 0 < c), ∀ (σ : ℝ) (_ : σ ∈ Ioc 1 2), ‖riemannZeta σ‖ ≤ c / (σ - 1) := by
  have := ZetaNear1BndFilter
  rw [Asymptotics.isBigO_iff] at this
  obtain ⟨c, U, hU, V, hV, h⟩ := this
  obtain ⟨T, hT, T_open, h1T⟩ := mem_nhds_iff.mp hU
  obtain ⟨ε, εpos, hε⟩ := Metric.isOpen_iff.mp T_open 1 h1T
  simp only [Metric.ball] at hε
  replace hε : Ico 1 (1 + ε) ⊆ U := by
    refine subset_trans (subset_trans ?_ hε) hT
    intro x hx
    simp only [mem_Ico] at hx
    simp only [dist, abs_lt]
    exact ⟨by linarith, by linarith⟩
  let W := Icc (1 + ε) 2
  have W_compact : IsCompact {ofReal z | z ∈ W} :=
    IsCompact.image isCompact_Icc continuous_ofReal
  have cont : ContinuousOn riemannZeta {ofReal z | z ∈ W} := by
    apply HasDerivAt.continuousOn (f' := (deriv riemannZeta))
    intro σ hσ
    exact (differentiableAt_riemannZeta (by contrapose! hσ; simp [W, hσ, εpos])).hasDerivAt
  obtain ⟨C, hC⟩ := IsCompact.exists_bound_of_continuousOn W_compact cont
  let C' := max (C + 1) 1
  replace hC : ∀ (σ : ℝ), σ ∈ W → ‖riemannZeta σ‖ < C' := by
    intro σ hσ
    simp only [lt_max_iff, C']
    have := hC σ
    simp only [mem_setOf_eq, ofReal_inj, exists_eq_right] at this
    exact Or.inl <| lt_of_le_of_lt (this hσ) (by norm_num)
  have Cpos : 0 < C' := by simp [C']
  use max (2 * C') c, (by simp [Cpos])
  intro σ ⟨σ_ge, σ_le⟩
  by_cases hσ : σ ∈ U ∩ V
  · simp only [← h, mem_setOf_eq] at hσ
    apply le_trans hσ ?_
    norm_cast
    have : 0 ≤ 1 / (σ - 1) := by apply one_div_nonneg.mpr; linarith
    simp only [Real.norm_eq_abs, abs_eq_self.mpr this, mul_div, mul_one]
    exact div_le_div₀ (by simp [Cpos.le]) (by simp) (by linarith) (by rfl)
  · replace hσ : σ ∈ W := by
      simp only [mem_inter_iff, hV σ_ge, and_true] at hσ
      simp only [mem_Icc, σ_le, and_true, W]
      contrapose! hσ; exact hε ⟨σ_ge.le, hσ⟩
    apply le_trans (hC σ hσ).le ((le_div_iff₀ (by linarith)).mpr ?_)
    rw [le_max_iff, mul_comm 2]; exact Or.inl <| mul_le_mul_of_nonneg_left (by linarith) Cpos.le

lemma norm_zeta_product_ge_one {x : ℝ} (hx : 0 < x) (y : ℝ) :
    ‖riemannZeta (1 + x) ^ 3 * riemannZeta (1 + x + I * y) ^ 4 * riemannZeta (1 + x + 2 * I * y)‖ ≥ 1 := by
  have h₀ : 1 < ( 1 + x : ℂ).re := by simp[hx]
  have h₁ : 1 < (1 + x + I * y).re := by simp [hx]
  have h₂ : 1 < (1 + x + 2 * I * y).re := by simp [hx]
  simpa only [one_pow, norm_mul, norm_pow, DirichletCharacter.LSeries_modOne_eq,
    LSeries_one_eq_riemannZeta, h₀, h₁, h₂] using
    DirichletCharacter.norm_LSeries_product_ge_one (1 : DirichletCharacter ℂ 1) hx y

theorem ZetaLowerBound1_aux1 {σ t : ℝ} (this : 1 ≤ ‖riemannZeta σ‖ ^ (3 : ℝ) * ‖riemannZeta (σ + I * t)‖ ^ (4 : ℝ) * ‖riemannZeta (σ + 2 * I * t)‖) :
  ‖riemannZeta σ‖ ^ ((3 : ℝ) / 4) * ‖riemannZeta (σ + 2 * t * I)‖ ^ ((1 : ℝ) / 4) * ‖riemannZeta (σ + t * I)‖ ≥ 1 := by
  use (one_le_pow_iff_of_nonneg (by bound) four_ne_zero).1 (by_contra (this.not_gt ∘ ?_))
  simp_rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
  norm_num [mul_right_comm, mul_comm (t : ℂ), mul_pow]

lemma ZetaLowerBound1 {σ t : ℝ} (σ_gt : 1 < σ) :
    ‖riemannZeta σ‖ ^ ((3 : ℝ) / 4) * ‖riemannZeta (σ + 2 * t * I)‖ ^ ((1 : ℝ) / 4) * ‖riemannZeta (σ + t * I)‖ ≥ 1 := by
  
  have := norm_zeta_product_ge_one (x := σ - 1) (by linarith) t
  simp_rw [ge_iff_le, norm_mul, norm_pow, ofReal_sub, ofReal_one, add_sub_cancel, ← Real.rpow_natCast]
    at this
  apply ZetaLowerBound1_aux1 this

lemma ZetaLowerBound2 {σ t : ℝ} (σ_gt : 1 < σ) :
    1 / (‖riemannZeta σ‖ ^ ((3 : ℝ) / 4) * ‖riemannZeta (σ + 2 * t * I)‖ ^ ((1 : ℝ) / 4)) ≤ ‖riemannZeta (σ + t * I)‖ := by
  have := ZetaLowerBound1 (t := t) σ_gt
  exact (div_le_iff₀' (pos_of_mul_pos_left (one_pos.trans_le this) (norm_nonneg _) ) ).mpr this

theorem ZetaLowerBound3_aux1 (A : ℝ) (ha : A ∈ Ioc 0 (1 / 2)) (t : ℝ)
  (ht_2 : 3 < |2 * t|) : 0 < A / Real.log |2 * t| := by
  exact div_pos ha.1 <| Real.log_pos (by linarith)

theorem ZetaLowerBound3_aux2 {C : ℝ}
  {σ t : ℝ}
  (ζ_2t_bound : ‖riemannZeta (σ + (2 * t) * I)‖ ≤ C * Real.log |2 * t|) :
  ‖riemannZeta (σ + 2 * t * I)‖ ^ ((1 : ℝ) / 4) ≤ (C * Real.log |2 * t|) ^ ((1 : ℝ) / 4) := by
  bound

theorem ZetaLowerBound3_aux3 (C : ℝ) (c_near : ℝ) {σ : ℝ} (t : ℝ) (σ_gt : 1 < σ) :
  c_near ^ ((3 : ℝ) / 4) * ((-1 + σ) ^ ((3 : ℝ) / 4))⁻¹ * C ^ ((1 : ℝ) / 4) * Real.log |t * 2| ^ ((1 : ℝ) / 4) =
    c_near ^ ((3 : ℝ) / 4) * C ^ ((1 : ℝ) / 4) * Real.log |t * 2| ^ ((1 : ℝ) / 4) * (-1 + σ) ^ (-(3 : ℝ) / 4) := by
  exact (symm) (.trans (by rw [neg_div, Real.rpow_neg (by linarith)]) (by ring))

theorem ZetaLowerBound3_aux4 (C : ℝ) (hC : 0 < C)
  (c_near : ℝ) (hc_near : 0 < c_near) {σ : ℝ} (t : ℝ) (ht : 3 < |t|)
  (σ_gt : 1 < σ)
   :
  0 < c_near ^ ((3 : ℝ) / 4) * (σ - 1) ^ (-(3 : ℝ) / 4) * C ^ ((1 : ℝ) / 4) * Real.log |2 * t| ^ ((1 : ℝ) / 4) := by
  match sub_pos.mpr σ_gt with | S => match Real.log_pos (by simp; linarith : abs (2 *t) > 1) with | S => positivity

theorem ZetaLowerBound3_aux5
  {σ : ℝ} (t : ℝ)
  (this : ‖riemannZeta σ‖ ^ ((3 : ℝ) / 4) * ‖riemannZeta (σ + 2 * t * I)‖ ^ ((1 : ℝ) / 4) * ‖riemannZeta (σ + t * I)‖ ≥ 1) :
  0 < ‖riemannZeta σ‖ ^ ((3 : ℝ) / 4) * ‖riemannZeta (σ + 2 * t * I)‖ ^ ((1 : ℝ) / 4) :=
  pos_of_mul_pos_left (this.trans_lt' zero_lt_one) (norm_nonneg _)

lemma ZetaLowerBound3 :
    ∃ c > 0, ∀ {σ : ℝ} (_ : σ ∈ Ioc 1 2) (t : ℝ) (_ : 3 < |t|),
    c * (σ - 1) ^ ((3 : ℝ) / 4) / (Real.log |t|) ^ ((1 : ℝ) / 4) ≤ ‖riemannZeta (σ + t * I)‖ := by
  obtain ⟨A, ha, C, hC, h_upper⟩ := ZetaUpperBnd
  obtain ⟨c_near, hc_near, h_near⟩ := ZetaNear1BndExact

  use 1 / (c_near ^ ((3 : ℝ) / 4) * (2 * C) ^ ((1 : ℝ) / 4)), by positivity
  intro σ hσ t ht
  obtain ⟨σ_gt, σ_le⟩ := hσ

  have lower := ZetaLowerBound2 (t := t) σ_gt
  apply le_trans _ lower

  have ζ_σ_bound : ‖riemannZeta σ‖ ≤ c_near / (σ - 1) := by
    exact h_near σ ⟨σ_gt, σ_le⟩

  have ht_2 : 3 < |2 * t| := by simp only [abs_mul, Nat.abs_ofNat]; linarith

  have σ_in_range : σ ∈ Icc (1 - A / Real.log |2 * t|) 2 := by
    constructor
    · 
      have : 0 < A / Real.log |2 * t| := by
        exact ZetaLowerBound3_aux1 A ha t ht_2
      nlinarith
    · exact σ_le

  have ζ_2t_bound := h_upper σ (2 * t) ht_2 σ_in_range

  have denom_bound : ‖riemannZeta σ‖ ^ ((3 : ℝ) / 4) * ‖riemannZeta (σ + 2 * t * I)‖ ^ ((1 : ℝ) / 4) ≤
      (c_near / (σ - 1)) ^ ((3 : ℝ) / 4) * (C * Real.log |2 * t|) ^ ((1 : ℝ) / 4) := by
    apply mul_le_mul
    · apply Real.rpow_le_rpow (norm_nonneg _) ζ_σ_bound (by norm_num)
    · apply ZetaLowerBound3_aux2
      convert ζ_2t_bound
      norm_cast
    · apply Real.rpow_nonneg (norm_nonneg _)
    · apply Real.rpow_nonneg (div_nonneg (by linarith) (by linarith))

  have : (c_near / (σ - 1)) ^ ((3 : ℝ) / 4) * (C * Real.log |2 * t|) ^ ((1 : ℝ) / 4) =
         c_near ^ ((3 : ℝ) / 4) * (σ - 1) ^ (-(3 : ℝ) / 4) * C ^ ((1 : ℝ) / 4) * (Real.log |2 * t|) ^ ((1 : ℝ) / 4) := by
    rw [Real.div_rpow (by linarith) (by linarith), Real.mul_rpow (by linarith) (Real.log_nonneg (by linarith))]
    ring_nf
    exact ZetaLowerBound3_aux3 _ _ _ σ_gt
  rw [this] at denom_bound

  have pos_left : 0 < c_near ^ ((3 : ℝ) / 4) * (σ - 1) ^ (-(3 : ℝ) / 4) * C ^ ((1 : ℝ) / 4) * (Real.log |2 * t|) ^ ((1 : ℝ) / 4) := by
    apply ZetaLowerBound3_aux4 C hC c_near hc_near t ht σ_gt

  have pos_right : 0 < ‖riemannZeta σ‖ ^ ((3 : ℝ) / 4) * ‖riemannZeta (σ + 2 * t * I)‖ ^ ((1 : ℝ) / 4) := by
    
    apply ZetaLowerBound3_aux5 _ <| ZetaLowerBound1 (t := t) σ_gt

  use (div_le_div_of_nonneg_left zero_le_one pos_right denom_bound).trans' ?_
  simp_rw [abs_mul, abs_two, neg_div, Real.rpow_neg (sub_pos.2 σ_gt).le] at *
  have hlog : 0 < Real.log |t| := Real.log_pos <| ht.trans' <| by norm_num
  have : 0 < Real.log |t| ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hlog _
  have hlog2 : 0 < Real.log (2 * |t|) := Real.log_pos <| ht_2.trans' <| by norm_num
  have : 0 < Real.log (2 * |t|) ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hlog2 (1 / 4)
  field_simp
  rw [Real.mul_rpow two_pos.le hC.le]
  move_mul [C ^ (1 / 4)]
  rw [mul_le_mul_iff_left₀]
  swap
  · positivity
  rw [← Real.mul_rpow two_pos.le hlog.le]
  apply Real.rpow_le_rpow hlog2.le ?_ (by norm_num)
  rw [← Real.log_rpow (ht.trans' (by norm_num))]
  apply Real.log_le_log (ht_2.trans' (by norm_num))
  rw [Real.rpow_two, sq]
  gcongr
  exact ht.trans' (by norm_num) |>.le

lemma ZetaInvBound1 {σ t : ℝ} (σ_gt : 1 < σ) :
    1 / ‖riemannZeta (σ + t * I)‖ ≤ ‖riemannZeta σ‖ ^ ((3 : ℝ) / 4) * ‖riemannZeta (σ + 2 * t * I)‖ ^ ((1 : ℝ) / 4) := by
  apply (div_le_iff₀ ?_).mpr
  · apply (Real.rpow_le_rpow_iff (z := 4) (by norm_num) ?_ (by norm_num)).mp
    · simp only [Real.one_rpow]
      rw [Real.mul_rpow, Real.mul_rpow, ← Real.rpow_mul, ← Real.rpow_mul]
      · simp only [isUnit_iff_ne_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
          IsUnit.div_mul_cancel, Real.rpow_one]
        conv => rw [mul_assoc]; rhs; rhs; rw [mul_comm]
        rw [← mul_assoc]
        have := norm_zeta_product_ge_one (x := σ - 1) (by linarith) t
        simp_rw [ge_iff_le, norm_mul, norm_pow, ofReal_sub, ofReal_one, add_sub_cancel, ← Real.rpow_natCast] at this
        convert this using 3 <;> ring_nf
      any_goals ring_nf
      any_goals apply norm_nonneg
      any_goals apply Real.rpow_nonneg <| norm_nonneg _
      apply mul_nonneg <;> apply Real.rpow_nonneg <| norm_nonneg _
    · refine mul_nonneg (mul_nonneg ?_ ?_) ?_ <;> simp [Real.rpow_nonneg]
  · have s_ne_one : σ + t * I ≠ 1 := by
      contrapose! σ_gt; apply le_of_eq; apply And.left; simpa [Complex.ext_iff] using σ_gt
    simpa using riemannZeta_ne_zero_of_one_le_re (by simp [σ_gt.le])

lemma Ioi_union_Iio_mem_cocompact {a : ℝ} (ha : 0 ≤ a) : Ioi (a : ℝ) ∪ Iio (-a : ℝ) ∈ cocompact ℝ := by
  simp only [Filter.mem_cocompact]
  use Icc (-a) a
  constructor
  · exact isCompact_Icc
  · rw [@compl_subset_iff_union, ← union_assoc, Icc_union_Ioi_eq_Ici, union_comm, Iio_union_Ici]
    linarith

lemma lt_abs_mem_cocompact {a : ℝ} (ha : 0 ≤ a) : {t | a < |t|} ∈ cocompact ℝ := by
  convert Ioi_union_Iio_mem_cocompact ha using 1; ext t
  simp only [mem_setOf_eq, mem_union, mem_Ioi, mem_Iio, lt_abs, lt_neg]

lemma ZetaInvBound2 :
    ∃ C > 0, ∀ {σ : ℝ} (_ : σ ∈ Ioc 1 2) (t : ℝ) (_ : 3 < |t|),
    1 / ‖riemannZeta (σ + t * I)‖ ≤ C * (σ - 1) ^ (-(3 : ℝ) / 4) * (Real.log |t|) ^ ((1 : ℝ) / 4) := by
  obtain ⟨A, ha, C, hC, h⟩ := ZetaUpperBnd
  obtain ⟨c, hc, h_inv⟩ := ZetaNear1BndExact
  refine ⟨(2 * C) ^ ((1 : ℝ)/ 4) * c ^ ((3 : ℝ)/ 4), by positivity, ?_⟩
  intro σ hσ t t_gt
  obtain ⟨σ_gt, σ_le⟩ := hσ
  have ht' : 3 < |2 * t| := by simp only [abs_mul, Nat.abs_ofNat]; linarith
  have hnezero: ((σ - 1) / c) ^ (-3 / 4 : ℝ) ≠ 0 := by
    have : (σ - 1) / c ≠ 0 := ne_of_gt <| div_pos (by linarith) hc
    contrapose! this
    rwa [Real.rpow_eq_zero (div_nonneg (by linarith) hc.le) (by norm_num)] at this
  calc
    _ ≤ ‖‖riemannZeta σ‖ ^ (3 / 4 : ℝ) * ‖riemannZeta (↑σ + 2 * ↑t * I)‖ ^ (1 / 4 : ℝ)‖ := ?_
    _ ≤ ‖((σ - 1) / c) ^ (-3 / 4 : ℝ) * ‖riemannZeta (↑σ + 2 * ↑t * I)‖ ^ (1 / 4 : ℝ)‖ := ?_
    _ ≤ ‖((σ - 1) / c) ^ (-3 / 4 : ℝ) * C ^ (1 / 4 : ℝ) * (Real.log |2 * t|) ^ (1 / 4 : ℝ)‖ := ?_
    _ ≤ ‖((σ - 1) / c) ^ (-3 / 4 : ℝ) * C ^ (1 / 4 : ℝ) * (Real.log (|t| ^ 2)) ^ (1 / 4 : ℝ)‖ := ?_
    _ = ‖((σ - 1)) ^ (-3 / 4 : ℝ) * c ^ (3 / 4 : ℝ) * (C ^ (1 / 4 : ℝ) * (Real.log (|t| ^ 2)) ^ (1 / 4 : ℝ))‖ := ?_
    _ = ‖((σ - 1)) ^ (-3 / 4 : ℝ) * c ^ (3 / 4 : ℝ) * ((2 * C) ^ (1 / 4 : ℝ) * Real.log |t| ^ (1 / 4 : ℝ))‖ := ?_
    _ = _ := ?_
  · simp only [norm_mul]
    convert ZetaInvBound1 σ_gt using 2
    <;> exact abs_eq_self.mpr <| Real.rpow_nonneg (norm_nonneg _) _
  · have bnd1: ‖riemannZeta σ‖ ^ (3 / 4 : ℝ) ≤ ((σ - 1) / c) ^ (-(3 : ℝ) / 4) := by
      have : ((σ - 1) / c) ^ (-(3 : ℝ) / 4) = (((σ - 1) / c) ^ (-1 : ℝ)) ^ (3 / 4 : ℝ) := by
        rw [← Real.rpow_mul ?_]
        · ring_nf
        · exact div_nonneg (by linarith) hc.le
      rw [this]
      apply Real.rpow_le_rpow (by simp [norm_nonneg]) ?_ (by norm_num)
      convert! h_inv σ ⟨σ_gt, σ_le⟩ using 1; simp [Real.rpow_neg_one, inv_div]
    simp only [norm_mul]
    apply (mul_le_mul_iff_left₀ ?_).mpr
    · convert! bnd1 using 1
      · exact abs_eq_self.mpr <| Real.rpow_nonneg (norm_nonneg _) _
      · exact abs_eq_self.mpr <| Real.rpow_nonneg (div_nonneg (by linarith) hc.le) _
    · apply lt_iff_le_and_ne.mpr ⟨(by simp), ?_⟩
      have : riemannZeta (↑σ + 2 * ↑t * I) ≠ 0 := by
        apply riemannZeta_ne_zero_of_one_le_re (by simp [σ_gt.le])
      symm; exact fun h2 ↦ this (by simpa using h2)
  · replace h := h σ (2 * t) (by simpa using ht') ⟨?_, σ_le⟩
    · have : 0 ≤ Real.log |2 * t| := Real.log_nonneg (by linarith)
      conv => rhs; rw [mul_assoc, ← Real.mul_rpow hC.le this]
      rw [norm_mul, norm_mul]
      conv => rhs; rhs; rw [Real.norm_rpow_of_nonneg <| mul_nonneg hC.le this]
      conv => lhs; rhs; rw [Real.norm_rpow_of_nonneg <| norm_nonneg _]
      apply (mul_le_mul_iff_right₀ ?_).mpr
      · apply Real.rpow_le_rpow (norm_nonneg _) ?_ (by norm_num)
        convert h using 1
        · simp
        · rw [Real.norm_eq_abs, abs_eq_self.mpr <| mul_nonneg hC.le this]
      · simpa only [Real.norm_eq_abs, abs_pos]
    · linarith [(div_nonneg ha.1.le (Real.log_nonneg (by linarith)) : 0 ≤ A / Real.log |2 * t|)]
  · simp only [Real.log_abs, norm_mul]
    apply (mul_le_mul_iff_right₀ ?_).mpr
    · rw [← Real.log_abs, Real.norm_rpow_of_nonneg <| Real.log_nonneg (by linarith)]
      have : 1 ≤ |(|t| ^ 2)| := by
        simp only [_root_.sq_abs, _root_.abs_pow, one_le_sq_iff_one_le_abs]
        linarith
      conv => rhs; rw [← Real.log_abs, Real.norm_rpow_of_nonneg <| Real.log_nonneg this]
      apply Real.rpow_le_rpow (abs_nonneg _) ?_ (by norm_num)
      · rw [Real.norm_eq_abs, abs_eq_self.mpr <| Real.log_nonneg (by linarith)]
        rw [abs_eq_self.mpr <| Real.log_nonneg this, abs_mul, Real.log_abs, Nat.abs_ofNat]
        apply Real.log_le_log (mul_pos (by norm_num) (by linarith)) (by nlinarith)
    · apply mul_pos (abs_pos.mpr hnezero) (abs_pos.mpr ?_)
      have : C ≠ 0 := ne_of_gt hC
      contrapose! this; rwa [Real.rpow_eq_zero (by linarith) (by norm_num)] at this
  · have : (-3 : ℝ) / 4 = -((3 : ℝ)/ 4) := by norm_num
    simp only [norm_mul, mul_eq_mul_right_iff, this, ← mul_assoc]; left; left
    conv => lhs; rw [Real.div_rpow (by linarith) hc.le, Real.rpow_neg hc.le, div_inv_eq_mul, norm_mul]
  · simp only [Real.log_pow, Nat.cast_ofNat, norm_mul, Real.norm_eq_abs]
    congr! 1
    rw [Real.mul_rpow (by norm_num) hC.le, Real.mul_rpow (by norm_num) <|
        Real.log_nonneg (by linarith), abs_mul, abs_mul, ← mul_assoc, mul_comm _ |2 ^ (1 / 4)|]
  · simp only [norm_mul, Real.norm_eq_abs]
    have : (2 * C) ^ ((1 : ℝ)/ 4) * c ^ ((3 : ℝ)/ 4) =
      |(2 * C) ^ ((1 : ℝ)/ 4) * c ^ ((3 : ℝ)/ 4)| := by
      rw [abs_eq_self.mpr (by apply mul_nonneg <;> (apply Real.rpow_nonneg; linarith))]
    rw [this, abs_mul, abs_eq_self.mpr (by apply Real.rpow_nonneg; linarith), abs_eq_self.mpr (by positivity),
      abs_eq_self.mpr (by positivity), abs_eq_self.mpr (by apply Real.rpow_nonneg (Real.log_nonneg (by linarith)))]
    ring_nf

lemma deriv_fun_re {t : ℝ} {f : ℂ → ℂ} (diff : ∀ (σ : ℝ), DifferentiableAt ℂ f (↑σ + ↑t * I)) :
    (deriv fun {σ₂ : ℝ} ↦ f (σ₂ + t * I)) = fun (σ : ℝ) ↦ deriv f (σ + t * I) := by
  ext σ
  have := deriv_comp (h := fun (σ : ℝ) ↦ σ + t * I) (h₂ := f) σ (diff σ) ?_
  · simp only [deriv_add_const', _root_.deriv_ofReal, mul_one] at this
    exact this
  · apply DifferentiableAt.add_const _ <| differentiableAt_ofReal σ

lemma Zeta_eq_int_derivZeta {σ₁ σ₂ t : ℝ} (t_ne_zero : t ≠ 0) :
    (∫ σ in σ₁..σ₂, (deriv riemannZeta) (σ + t * I)) = riemannZeta (σ₂ + t * I) - riemannZeta (σ₁ + t * I) := by
  have diff : ∀ (σ : ℝ), DifferentiableAt ℂ riemannZeta (σ + t * I) := by
    intro σ
    refine differentiableAt_riemannZeta ?_
    contrapose! t_ne_zero; apply And.right; simpa [Complex.ext_iff] using t_ne_zero
  apply intervalIntegral.integral_deriv_eq_sub'
  · exact deriv_fun_re diff
  · intro s _
    apply DifferentiableAt.comp
    · exact (diff s).restrictScalars ℝ
    · exact DifferentiableAt.add_const (c := t * I) <| differentiableAt_ofReal _
  · apply ContinuousOn.comp (g := (deriv riemannZeta)) ?_ ?_ (mapsTo_image _ _)
    · apply HasDerivAt.continuousOn (f' := deriv <| (deriv riemannZeta))
      intro x hx
      apply hasDerivAt_deriv_iff.mpr
      replace hx : x ≠ 1 := by
        contrapose! hx
        simp only [hx, mem_image, Complex.ext_iff, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im,
          I_im, mul_one, sub_self, add_zero, one_re, add_im, mul_im, zero_add, one_im, not_exists,
          not_and]
        exact fun _ _ _ ↦ t_ne_zero
      exact differentiableAt_deriv_riemannZeta hx
    · exact continuous_ofReal.continuousOn.add continuousOn_const

lemma Zeta_diff_Bnd :
    ∃ (A : ℝ) (_ : A ∈ Ioc 0 (1 / 2)) (C : ℝ) (_ : 0 < C), ∀ (σ₁ σ₂ : ℝ) (t : ℝ) (_ : 3 < |t|)
    (_ : 1 - A / Real.log |t| ≤ σ₁) (_ : σ₂ ≤ 2) (_ : σ₁ < σ₂),
    ‖riemannZeta (σ₂ + t * I) - riemannZeta (σ₁ + t * I)‖ ≤  C * Real.log |t| ^ 2 * (σ₂ - σ₁) := by
  obtain ⟨A, hA, C, Cpos, hC⟩ := ZetaDerivUpperBnd
  refine ⟨A, hA, C, Cpos, ?_⟩
  intro σ₁ σ₂ t t_gt σ₁_ge σ₂_le σ₁_lt_σ₂
  have t_ne_zero : t ≠ 0 := by contrapose! t_gt; simp only [t_gt, abs_zero, Nat.ofNat_nonneg]
  rw [← Zeta_eq_int_derivZeta t_ne_zero]
  convert intervalIntegral.norm_integral_le_of_norm_le_const ?_ using 1
  · congr; rw [_root_.abs_of_nonneg (by linarith)]
  · intro σ hσ; rw [uIoc_of_le σ₁_lt_σ₂.le, mem_Ioc] at hσ
    exact hC σ t t_gt ⟨le_trans σ₁_ge hσ.1.le, le_trans hσ.2 σ₂_le⟩

lemma ZetaInvBnd_aux' {t : ℝ} (logt_gt_one : 1 < Real.log |t|) : Real.log |t| < Real.log |t| ^ (9 : ℝ) := by
  nth_rewrite 1 [← Real.rpow_one <| Real.log |t|]
  exact mod_cast Real.rpow_lt_rpow_left_iff (y := 1) (z := 9) logt_gt_one |>.mpr (by norm_num)

lemma ZetaInvBnd_aux {t : ℝ} (logt_gt_one : 1 < Real.log |t|) : Real.log |t| ≤ Real.log |t| ^ (9 : ℝ) :=
    ZetaInvBnd_aux' logt_gt_one |>.le

lemma ZetaInvBnd_aux2 {A C₁ C₂ : ℝ} (Apos : 0 < A) (C₁pos : 0 < C₁) (C₂pos : 0 < C₂)
    (hA : A ≤ 1 / 2 * (C₁ / (C₂ * 2)) ^ (4 : ℝ)) :
    0 < (C₁ * A ^ (3 / 4 : ℝ) - C₂ * 2 * A)⁻¹ := by
  simp only [inv_pos, sub_pos]
  apply div_lt_iff₀ (by positivity) |>.mp
  rw [div_eq_mul_inv, ← Real.rpow_neg (by positivity), mul_assoc]
  apply lt_div_iff₀' (by positivity) |>.mp
  nth_rewrite 1 [← Real.rpow_one A]
  rw [← Real.rpow_add (by positivity)]
  norm_num
  apply Real.rpow_lt_rpow_iff (z := 4) (by positivity) (by positivity) (by positivity) |>.mp
  rw [← Real.rpow_mul (by positivity)]
  norm_num
  apply lt_of_le_of_lt hA
  rw [div_mul_comm, mul_one, Real.rpow_ofNat]
  apply half_lt_self
  positivity

lemma ZetaInvBnd :
    ∃ (A : ℝ) (_ : A ∈ Ioc 0 (1 / 2)) (C : ℝ) (_ : 0 < C), ∀ (σ : ℝ) (t : ℝ) (_ : 3 < |t|)
    (_ : σ ∈ Ico (1 - A / (Real.log |t|) ^ (9 : ℝ)) (1 + A / (Real.log |t|) ^ (9 : ℝ))),
    1 / ‖riemannZeta (σ + t * I)‖ ≤ C * (Real.log |t|) ^ (7 : ℝ) := by
  obtain ⟨C', C'pos, hC₁⟩ := ZetaInvBound2
  obtain ⟨A', hA', C₂, C₂pos, hC₂⟩ := Zeta_diff_Bnd
  set C₁ := 1 / C'
  let A := min A' <| (1 / 2 : ℝ) * (C₁ / (C₂ * 2)) ^ (4 : ℝ)
  have Apos : 0 < A := by have := hA'.1; positivity
  have Ale : A ≤ 1 / 2 := by dsimp only [A]; apply min_le_iff.mpr; left; exact hA'.2
  set C := (C₁ * A ^ (3 / 4 : ℝ) - C₂ * 2 * A)⁻¹
  have Cpos : 0 < C := by
    refine ZetaInvBnd_aux2 (by positivity) (by positivity) (by positivity) ?_
    apply min_le_right
  refine ⟨A, ⟨Apos, by linarith [hA'.2]⟩ , C, Cpos, ?_⟩
  intro σ t t_gt hσ
  have logt_gt_one := logt_gt_one t_gt.le
  have σ_ge : 1 - A / Real.log |t| ≤ σ := by
    apply le_trans ?_ hσ.1
    suffices A / Real.log |t| ^ (9 : ℝ) ≤ A / Real.log |t| by linarith
    exact div_le_div₀ Apos.le (by rfl) (by positivity) <| ZetaInvBnd_aux logt_gt_one
  obtain ⟨_, _, neOne⟩ := UpperBnd_aux ⟨Apos, Ale⟩ t_gt σ_ge
  set σ' := 1 + A / Real.log |t| ^ (9 : ℝ)
  have σ'_gt : 1 < σ' := by simp only [σ', lt_add_iff_pos_right]; positivity
  have σ'_le : σ' ≤ 2 := by
    simp only [σ']
    suffices A / Real.log |t| ^ (9 : ℝ) < 1 by linarith
    apply div_lt_one (by positivity) |>.mpr
    exact lt_trans₄ (by linarith) logt_gt_one <| ZetaInvBnd_aux' logt_gt_one
  set s := σ + t * I
  set s' := σ' + t * I
  by_cases h0 : ‖riemannZeta s‖ ≠ 0
  swap
  · simp only [ne_eq, not_not] at h0; simp only [h0, div_zero]; positivity
  apply div_le_iff₀ (by positivity) |>.mpr <| div_le_iff₀' (by positivity) |>.mp ?_
  have pos_aux : 0 < (σ' - 1) := by linarith
  calc
    _ ≥ ‖riemannZeta s'‖ - ‖riemannZeta s - riemannZeta s'‖ := ?_
    _ ≥ C₁ * (σ' - 1) ^ ((3 : ℝ)/ 4) * Real.log |t|  ^ ((-1 : ℝ)/ 4) - C₂ * Real.log |t| ^ 2 * (σ' - σ) := ?_
    _ ≥ C₁ * (A / Real.log |t| ^ (9 : ℝ)) ^ ((3 : ℝ)/ 4) * Real.log |t| ^ ((-1 : ℝ)/ 4) - C₂ * Real.log |t| ^ (2 : ℝ) * 2 * A / Real.log |t| ^ (9 : ℝ) := ?_
    _ ≥ C₁ * A ^ ((3 : ℝ)/ 4) * Real.log |t| ^ (-7 : ℝ) - C₂ * 2 * A * Real.log |t| ^ (-7 : ℝ) := ?_
    _ = (C₁ * A ^ ((3 : ℝ)/ 4) - C₂ * 2 * A) * Real.log |t| ^ (-7 : ℝ) := by ring
    _ ≥ _ := ?_
  · apply ge_iff_le.mpr
    convert norm_sub_norm_le (a := riemannZeta s') (b := riemannZeta s' - riemannZeta s) using 1
    · rw [(by simp : riemannZeta s' - riemannZeta s = -(riemannZeta s - riemannZeta s'))]; simp only [norm_neg]
    · simp
  · apply sub_le_sub
    · have := one_div_le ?_ (by positivity) |>.mp <| hC₁ ⟨σ'_gt, σ'_le⟩ t t_gt
      · convert this using 1
        rw [one_div, mul_inv_rev, mul_comm, mul_inv_rev, mul_comm _ C'⁻¹]
        simp only [one_div C', C₁]
        congr <;> (rw [← Real.rpow_neg (by linarith), neg_div]); rw [neg_neg]
      · apply norm_pos_iff.mpr <| riemannZeta_ne_zero_of_one_lt_re (by simp [σ'_gt])
    · rw [(by simp : riemannZeta s - riemannZeta s' = -(riemannZeta s' - riemannZeta s)), norm_neg]
      refine hC₂ σ σ' t t_gt ?_ σ'_le <| by rw [Set.mem_Ico] at hσ; exact hσ.2
      apply le_trans ?_ hσ.1
      rw [tsub_le_iff_right, ← add_sub_right_comm, le_sub_iff_add_le, add_le_add_iff_left]
      exact div_le_div₀ hA'.1.le (by simp [A]) (by positivity) <| ZetaInvBnd_aux logt_gt_one
  · apply sub_le_sub (by simp only [add_sub_cancel_left, σ']; exact_mod_cast le_rfl) ?_
    rw [mul_div_assoc, mul_assoc _ 2 _]
    apply mul_le_mul (by exact_mod_cast le_rfl) ?_ (by linarith [hσ.2]) (by positivity)
    suffices h : σ' + (1 - A / Real.log |t| ^ (9 : ℝ)) ≤ (1 + A / Real.log |t| ^ (9 : ℝ)) + σ by
      simp only [tsub_le_iff_right]
      convert! le_sub_right_of_add_le h using 1; ring_nf
    exact add_le_add (by linarith) (by linarith [hσ.1])
  · simp_rw [tsub_le_iff_right, div_eq_mul_inv _ (Real.log |t| ^ (9 : ℝ))]
    rw [← Real.rpow_neg (by positivity), Real.mul_rpow (by positivity) (by positivity)]
    rw [← Real.rpow_mul (by positivity)]
    ring_nf
    conv => rhs; lhs; rw [mul_assoc, ← Real.rpow_add (by positivity)]
    rw [(by ring : C₂ * Real.log |t| ^ (2 : ℝ) * A * Real.log |t| ^ (-9 : ℝ) * 2 = C₂ * (Real.log |t| ^ (2 : ℝ) * Real.log |t| ^ (-9 : ℝ) ) * A * 2)]
    rw [← Real.rpow_add (by positivity)]; norm_num; group; exact le_rfl
  · apply div_le_iff₀ (by positivity) |>.mpr
    conv => rw [mul_assoc]; rhs; rhs; rw [mul_comm C, ← mul_assoc, ← Real.rpow_add (by positivity)]
    have := inv_inv C ▸ mul_inv_cancel₀ (a := C⁻¹) (by positivity) |>.symm.le
    simpa [C] using this

lemma ZetaLowerBnd :
    ∃ (A : ℝ) (_ : A ∈ Ioc 0 (1 / 2)) (c : ℝ) (_ : 0 < c),
    ∀ (σ : ℝ)
    (t : ℝ) (_ : 3 < |t|)
    (_ : σ ∈ Ico (1 - A / (Real.log |t|) ^ (9 : ℝ)) 1),
    c / (Real.log |t|) ^ (7 : ℝ) ≤ ‖riemannZeta (σ + t * I)‖ := by
  obtain ⟨C₁, C₁pos, hC₁⟩ := ZetaLowerBound3
  obtain ⟨A', hA', C₂, C₂pos, hC₂⟩ := Zeta_diff_Bnd

  let A := min A' ((C₁ / (4 * C₂)) ^ 4)
  have hA : A ∈ Ioc 0 (1 / 2) :=
    ⟨lt_min hA'.1 (by positivity), (min_le_left A' _).trans hA'.2⟩

  let C := C₁ * A ^ ((3:ℝ) /4) - 2 * C₂ * A
  have hc_pos : 0 < C := by
    have:= A.rpow_le_rpow hA.1.le (min_le_right _ _) (inv_pos.mpr four_pos).le
    erw [Real.pow_rpow_inv_natCast (div_pos C₁pos (mul_pos four_pos C₂pos)).le four_ne_zero,
      le_div_iff₀ (mul_pos four_pos C₂pos)] at this
    norm_num [mul_assoc, C, mul_left_comm, C₂pos, hA.1,
      (mul_le_mul_of_nonneg_right this (A.rpow_nonneg hA.1.le _)).trans_lt', ←A.rpow_add]

  refine ⟨A, hA, C, hc_pos, fun σ t L ⟨σ_low_bound, σ_le_one⟩=>?_⟩

  let σ' := 1 + A / Real.log |t| ^  (9 : ℝ)

  have triangular :  ‖riemannZeta (σ + t * I)‖ ≥  ‖riemannZeta (σ' + t * I)‖ -  ‖riemannZeta (σ + t * I) - riemannZeta (σ' + t * I)‖ := by
    apply sub_le_iff_le_add.mpr.comp (sub_sub_self @_ (@_ : ℂ)▸norm_sub_le _ _).trans
      (by rw [add_comm])

  have one_leLogT : 1 ≤ Real.log |t| := (logt_gt_one L.le).le
  have one_half_le_log_pow : 1 / 2 ≤ Real.log |t| ^ 9 :=
    one_half_lt_one.le.trans <| one_le_pow₀ one_leLogT

  have σ'_ge : 1 ≤ σ' := by
    simp_all only [gt_iff_lt, mem_Ioc, Real.log_abs, one_div, and_imp, tsub_le_iff_right,
      lt_inf_iff, div_pos_iff_of_pos_left, Nat.ofNat_pos, mul_pos_iff_of_pos_left, pow_pos,
      and_self, inf_le_iff, true_or, sub_pos, mem_Ico, and_true, ofReal_add, ofReal_one,
      ofReal_div, ge_iff_le, le_add_iff_nonneg_right, A, C, σ']
    apply div_nonneg
    · apply le_min
      · linarith
      · have : (C₁ / (4 * C₂)) ^ 4 = ((C₁ / (4 * C₂)) ^ 2) ^ 2 := by ring
        rw [this]
        apply sq_nonneg
    · positivity

  have right_sub :  -‖riemannZeta (σ + t * I) -  riemannZeta (σ' + t * I)‖ ≥ - C₂ * Real.log |t| ^ 2 * (σ' - σ) := by
    change - C₂ * Real.log |t| ^ 2 * (σ' - σ) ≤ -‖riemannZeta (σ + t * I) -  riemannZeta (σ' + t * I)‖
    have := hC₂ σ σ' t L ?_ ?_ ?_
    · convert! neg_le_neg this using 1
      · ring
      · congr! 1
        have : riemannZeta (↑σ + ↑t * I) - riemannZeta (↑σ' + ↑t * I) =
            - (riemannZeta (↑σ' + ↑t * I) - riemannZeta (↑σ + ↑t * I)) := by ring
        rw [this, norm_neg]
    · have : 1 - A' / Real.log |t| ≤ (1 : ℝ) - A / (Real.log |t|) ^ (9 : ℝ) := by
        gcongr
        · exact hA'.1.le
        · bound
        · rw [← Real.rpow_one (Real.log |t|), ← Real.rpow_mul (by linarith), one_mul]
          exact Real.rpow_le_rpow_of_exponent_le one_leLogT Nat.one_le_ofNat
      linarith
    · have : σ' ≤ 1 + A := by
        simp_all only [gt_iff_lt, mem_Ioc, Real.log_abs, one_div, and_imp, tsub_le_iff_right,
          lt_inf_iff, div_pos_iff_of_pos_left, Nat.ofNat_pos, mul_pos_iff_of_pos_left, pow_pos,
          and_self, inf_le_iff, true_or, sub_pos, mem_Ico, and_true, ofReal_add, ofReal_one,
          ofReal_div, ge_iff_le, le_add_iff_nonneg_right, add_le_add_iff_left, le_inf_iff,
          σ', A, C]
        have : 1 ≤ Real.log t ^ (9 : ℝ) := Real.one_le_rpow one_leLogT (Nat.ofNat_nonneg' 9)
        refine ⟨?_, ?_⟩
        · rw [← min_div_div_right]
          · rw [min_le_iff]
            left
            bound
          · exact le_trans (zero_le_one) this
        · rw [← min_div_div_right]
          · rw [min_le_iff]
            right
            bound
          · exact le_trans (zero_le_one) this
      · bound [hA.2]
    · linarith

  have right' : -‖riemannZeta (σ + t * I) -  riemannZeta (σ' + t * I)‖   ≥ - C₂ * 2 * A / Real.log |t| ^ 7 := by
    have := (abs t).log_pos (by bound)
    refine right_sub.trans' ((div_le_iff₀ (pow_pos this 7)).2 @?_|>.trans
      (mul_le_mul_of_nonpos_left (sub_le_sub_left σ_low_bound (1+_) )
        (by ·linear_combination C₂*this*(.log |t|))))
    exact (mod_cast (by linear_combination (2 *_* A) *div_self ↑(pow_pos this 09).ne'))

  have left_sub : ‖riemannZeta (σ' + t * I)‖ ≥ C₁ * (σ' - 1) ^ ((3:ℝ) /4) / Real.log |t| ^ 4 := by
    use (hC₁ ⟨lt_add_of_pos_right (1) (by bound[hA.1]),
      add_le_of_le_sub_left ((div_le_iff₀ (by bound)).2 (hA.2.trans (?_)))⟩ t L).trans' ?_
    · norm_num only [one_mul, Real.rpow_ofNat, one_half_le_log_pow]
    · simp_all only [gt_iff_lt, mem_Ioc, lt_inf_iff, div_pos_iff_of_pos_left, Nat.ofNat_pos,
        mul_pos_iff_of_pos_left, pow_pos, and_self, inf_le_iff, true_or, sub_pos, mem_Ico,
        ofReal_add, ofReal_one, ofReal_div, ge_iff_le, le_add_iff_nonneg_right, neg_mul,
        neg_le_neg_iff, add_sub_cancel_left, σ', A, C]
      gcongr
      have :  Real.log |t| ^ ((1 : ℝ) / 4) ≤ Real.log |t| ^ (4 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le one_leLogT (by norm_num)
      exact_mod_cast this

  have left' : ‖riemannZeta (σ' + t * I)‖ ≥ C₁ * A ^ ((3:ℝ) /4) / Real.log |t| ^ 7 := by
    contrapose! hC₁
    use σ', ⟨lt_add_of_pos_right 1<|by bound[hA'.1],
      add_le_of_le_sub_left ((div_le_iff₀ (by bound)).2 (hA.2.trans ?_))⟩, t, L, hC₁.trans_le ?_
    · norm_num only [one_mul, Real.rpow_ofNat, one_half_le_log_pow]
    · norm_num only [σ', add_sub_cancel_left, A.div_rpow hA.1.le, mul_div, pow_pos, L.trans',
        ←Real.rpow_natCast, ←Real.rpow_mul, le_of_lt, Real.log_pos, refl, div_div, ←Real.rpow_sub]
      rw [Real.div_rpow hA.1.le, ← Real.rpow_mul (by linarith), ← mul_div_assoc, div_div, ← Real.rpow_add (by linarith)]
      · norm_num
      · apply Real.rpow_nonneg (by linarith)
  have ineq : ‖riemannZeta (σ + t * I)‖ ≥ (C₁ * A ^ ((3:ℝ) /4) - C₂ * 2 * A) / Real.log |t| ^ 7 := by
    linear_combination left'+triangular+right'

  rw [mul_comm C₂] at ineq
  exact_mod_cast ineq

def ZetaZeroFreeGenProp (n : ℝ) : Prop := ∃ (A : ℝ) (_ : A ∈ Ioc 0 (1 / 2)),
    ∀ (σ : ℝ) (t : ℝ) (_ : 3 < |t|) (_ : σ ∈ Ico (1 - A / (Real.log |t|) ^ n) 1),
    riemannZeta (σ + t * I) ≠ 0

lemma ZetaZeroFree9 : ZetaZeroFreeGenProp 9 := by
  obtain ⟨A, hA, c, hc, h_lower⟩ := ZetaLowerBnd

  refine ⟨A, hA, ?_⟩

  intro σ t ht hσ h_zero

  have := h_lower σ t ht hσ

  rw [h_zero, norm_zero] at this

  have pos_bound : 0 < c / (Real.log |t|) ^ (7 : ℝ) := by
    apply div_pos hc
    apply Real.rpow_pos_of_pos
    apply Real.log_pos
    linarith
  linarith

lemma LogDerivZetaBnd :
    ∃ (A : ℝ) (_ : A ∈ Ioc 0 (1 / 2)) (C : ℝ) (_ : 0 < C), ∀ (σ : ℝ) (t : ℝ) (_ : 3 < |t|)
    (_ : σ ∈ Ico (1 - A / Real.log |t| ^ (9 : ℝ)) (1 + A / Real.log |t| ^ (9 : ℝ))),
      ‖(deriv riemannZeta) (σ + t * I) / riemannZeta (σ + t * I)‖ ≤ C * Real.log |t| ^ (9 : ℝ) := by
  obtain ⟨A, hA, C, hC, h⟩ := ZetaInvBnd
  obtain ⟨A', hA', C', hC', h'⟩ := ZetaDerivUpperBnd
  use min A A', ⟨lt_min hA.1 hA'.1, min_le_of_right_le hA'.2⟩, C * C', mul_pos hC hC'
  intro σ t t_gt ⟨σ_ge, σ_lt⟩
  have logt_gt : (1 : ℝ) < Real.log |t| := logt_gt_one t_gt.le
  have σ_ge' : 1 - A / Real.log |t| ^ (9 : ℝ) ≤ σ := by
    apply le_trans (tsub_le_tsub_left ?_ 1) σ_ge
    apply div_le_div_of_nonneg_right (min_le_left A A')
    apply Real.rpow_nonneg
    linarith
  have σ_ge'' : 1 - A' / Real.log |t| ≤ σ := by
    apply le_trans (tsub_le_tsub_left ?_ 1) σ_ge
    apply div_le_div₀ hA'.1.le (min_le_right A A') (lt_trans (by norm_num) logt_gt) ?_
    rw [← Real.rpow_one (Real.log |t|), ← Real.rpow_mul (by linarith), one_mul]
    exact Real.rpow_le_rpow_of_exponent_le logt_gt.le Nat.one_le_ofNat
  replace h := h σ t t_gt ⟨σ_ge', by calc
    σ < 1 + min A A' / Real.log |t| ^ (9 : ℝ) := σ_lt
    _ ≤ 1 + A / Real.log |t| ^ (9 : ℝ) := by gcongr; simp⟩
  replace h' := h' σ t t_gt ⟨σ_ge'', by
   calc
    σ ≤ 1 + min A A' / Real.log |t| ^ (9 : ℝ) := by linarith [σ_lt]
    _ ≤ 1 + (1/2) / Real.log |t| ^ (9 : ℝ) := by gcongr; simp [Set.mem_Ioc] at hA' hA ⊢ ; simp [hA.2]
    _ ≤ 1 + (1/2) / 1 := by
          gcongr
          calc
            1 ≤ Real.log |t| := by linarith
            _ ≤ (Real.log |t|) ^ (9 : ℝ) := Real.self_le_rpow_of_one_le (by linarith) (by linarith)
    _ ≤ 2 := by linarith
    ⟩
  simp only [norm_div]
  convert! mul_le_mul h h' (by simp) ?_ using 1 <;> (norm_cast; ring_nf); positivity

lemma ZetaNoZerosOn1Line (t : ℝ) : riemannZeta (1 + t * I) ≠ 0 := by
  refine riemannZeta_ne_zero_of_one_le_re ?_
  simp

lemma ZetaCont : ContinuousOn riemannZeta (univ \ {1}) := by
  apply continuousOn_of_forall_continuousAt (fun x hx ↦ ?_)
  apply DifferentiableAt.continuousAt (𝕜 := ℂ)
  convert differentiableAt_riemannZeta ?_
  simp only [Set.mem_sdiff, mem_univ, mem_singleton_iff, true_and] at hx
  exact hx

lemma ZetaNoZerosInBox (T : ℝ) :
    ∃ (σ : ℝ) (_ : σ < 1), ∀ (t : ℝ) (_ : |t| ≤ T)
    (σ' : ℝ) (_ : σ' ≥ σ), riemannZeta (σ' + t * I) ≠ 0 := by
  by_contra! h
  have hn (n : ℕ) := h (1 - 1 / (n + 1)) (sub_lt_self _ (by positivity))

  have : ∃ (tn : ℕ → ℝ) (σn : ℕ → ℝ), (∀ n, σn n ≤ 1) ∧
    (∀ n, (1 : ℝ) - 1 / (n + 1) ≤ σn n) ∧ (∀ n, |tn n| ≤ T) ∧
    (∀ n, riemannZeta (σn n + tn n * I) = 0) := by
    choose t ht σ' hσ' hζ using hn
    refine ⟨t, σ', ?_, hσ', ht, hζ⟩
    intro n
    by_contra! hσn
    have := riemannZeta_ne_zero_of_one_lt_re (s := σ' n + t n * I)
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, ne_eq] at this
    exact this hσn (hζ n)

  choose t σ' hσ'_le hσ'_ge ht hζ using this

  have σTo1 : Filter.Tendsto σ' Filter.atTop (𝓝 1) := by
    use sub_zero (1: ℝ)▸tendsto_order.2 ⟨fun A B=>? _,fun A B=>?_⟩
    · apply (((tendsto_inv_atTop_nhds_zero_nat.comp
        (Filter.tendsto_add_atTop_nat (1))).congr (by norm_num)).const_sub 1).eventually_const_lt
          B|>.mono (hσ'_ge ·|>.trans_lt')
    · norm_num[(hσ'_le _).trans_lt, B.trans_le']

  have : ∃ (t₀ : ℝ) (subseq : ℕ → ℕ),
      Filter.Tendsto (t ∘ subseq) Filter.atTop (𝓝 t₀) ∧
      Filter.Tendsto subseq Filter.atTop Filter.atTop := by
    refine (isCompact_Icc.isSeqCompact fun and => abs_le.1 (ht and)).imp fun and ⟨x, A, B, _⟩ => ?_
    use A, by omega, B.tendsto_atTop

  obtain ⟨t₀, subseq, tTendsto, subseqTendsto⟩ := this

  have σTo1 : Filter.Tendsto (σ' ∘ subseq) Filter.atTop (𝓝 1) :=
    σTo1.comp subseqTendsto

  have (n : ℕ) : riemannZeta (σ' (subseq n) + I * (t (subseq n))) = 0 := by
    convert hζ (subseq n) using 3
    ring

  have ToOneT0 : Filter.Tendsto (fun n ↦ (σ' (subseq n) : ℂ) + Complex.I * (t (subseq n))) Filter.atTop
      (𝓝[≠]((1 : ℂ) + I * t₀)) := by
    simp_rw [tendsto_nhdsWithin_iff, Function.comp_def] at tTendsto ⊢
    constructor
    · exact (σTo1.ofReal.add (tTendsto.ofReal.const_mul _)).trans (by simp)
    · filter_upwards with n
      apply ne_of_apply_ne riemannZeta
      rw [this]
      apply Ne.symm
      apply riemannZeta_ne_zero_of_one_le_re
      simp only [add_re, one_re, mul_re, I_re, ofReal_re, zero_mul, I_im, ofReal_im, mul_zero,
        sub_self, add_zero, le_refl]

  by_cases ht₀ : t₀ = 0
  · have ZetaBlowsUp : ∀ᶠ s in 𝓝[≠](1 : ℂ), ‖riemannZeta s‖ ≥ 1 := by
      simp_all only [ge_iff_le, one_div, tsub_le_iff_right, Function.comp_def, ofReal_zero,
        mul_zero, add_zero, norm_eq_sqrt_real_inner, Complex.inner, mul_re, conj_re, conj_im,
        mul_neg, sub_neg_eq_add, Real.one_le_sqrt, eventually_nhdsWithin_iff, mem_compl_iff,
        mem_singleton_iff]
      contrapose! h
      simp_all only [ne_eq]
      delta abs at*
      exfalso
      simp_rw [Metric.nhds_basis_ball.frequently_iff]at*
      choose! I A B using h
      choose a s using exists_seq_strictAnti_tendsto (0: ℝ)
      apply ((isCompact_closedBall _ _).isSeqCompact
        fun and=>(A _ (s.2.1 and)).le.trans (s.2.2.bddAbove_range.some_mem ⟨and, rfl⟩)).elim
      simp only [Metric.mem_ball, dist_eq_norm_sub] at A
      refine fun and ⟨a, H, S, M⟩=> ?_
      refine absurd (tendsto_nhds_unique M (tendsto_sub_nhds_zero_iff.1
        (( squeeze_zero_norm fun and=>le_of_lt (A _ (s.2.1 _) ) )
          (s.2.2.comp S.tendsto_atTop)))) fun and=>?_
      norm_num[*,Function.comp_def] at M
      have:=@riemannZeta_residue_one
      use one_ne_zero (tendsto_nhds_unique (this.comp (tendsto_nhdsWithin_iff.2
        ⟨ M,.of_forall (by norm_num[*])⟩)) ( squeeze_zero_norm ?_
          ((M.sub_const 1).norm.trans (by rw [sub_self,norm_zero]))))
      use fun and =>.trans (norm_mul_le_of_le ↑(le_rfl) (Complex.norm_def _▸Real.sqrt_le_one.mpr
        (B ↑_ (s.2.1 ↑_)).right.le)) (by rw [mul_one])

    have ZetaNonZ : ∀ᶠ s in 𝓝[≠](1 : ℂ), riemannZeta s ≠ 0 := by
      filter_upwards [ZetaBlowsUp]
      intro s hs hfalse
      rw [hfalse] at hs
      simp only [norm_zero, ge_iff_le] at hs
      linarith

    rw [ht₀] at ToOneT0
    simp only [ofReal_zero, mul_zero, add_zero] at ToOneT0
    rcases (ToOneT0.eventually ZetaNonZ).exists with ⟨n, hn⟩
    exact hn (this n)

  · have zetaIsZero : riemannZeta (1 + Complex.I * t₀) = 0 := by
      have cont := @ZetaCont
      use isClosed_singleton.isSeqClosed
        this
        (.comp
          (cont.continuousAt.comp (eventually_ne_nhds (by field_simp; simp [ht₀])).mono
            fun and=>.intro ⟨⟩)
          (ToOneT0.trans (inf_le_left)))

    exact riemannZeta_ne_zero_of_one_le_re (s := 1 + I * t₀) (by simp) zetaIsZero

lemma LogDerivZetaHoloOn {S : Set ℂ} (s_ne_one : 1 ∉ S)
    (nonzero : ∀ s ∈ S, riemannZeta s ≠ 0) :
    HolomorphicOn (fun s ↦ (deriv riemannZeta) s / riemannZeta s) S := by
  apply DifferentiableOn.div _ _ nonzero <;> intro s hs <;> apply DifferentiableAt.differentiableWithinAt
  · apply differentiableAt_deriv_riemannZeta
    exact ne_of_mem_of_not_mem hs s_ne_one
  · apply differentiableAt_riemannZeta
    exact ne_of_mem_of_not_mem hs s_ne_one

theorem LogDerivZetaHolcSmallT :
    ∃ (σ₂ : ℝ) (_ : σ₂ < 1), HolomorphicOn (fun (s : ℂ) ↦ (deriv riemannZeta) s / (riemannZeta s))
      (( [[ σ₂, 2 ]] ×ℂ [[ -3, 3 ]]) \ {1}) := by
  obtain ⟨σ₂, hσ₂_lt_one, hζ_ne_zero⟩ := ZetaNoZerosInBox 3
  refine ⟨σ₂, hσ₂_lt_one, ?_⟩
  let U := ([[σ₂, 2]] ×ℂ [[-3, 3]]) \ {1}
  have s_in_U_im_le3 : ∀ s ∈ U, |s.im| ≤ 3 := by
    intro s hs
    rw [Set.mem_sdiff_singleton] at hs
    rcases hs with ⟨hbox, _hne⟩
    rcases hbox with ⟨hre, him⟩
    simp only [Set.mem_preimage] at him
    obtain ⟨him_lower, him_upper⟩ := him
    apply abs_le.2
    simp only [neg_le_self_iff, Nat.ofNat_nonneg, inf_of_le_left] at him_lower
    simp only [neg_le_self_iff, Nat.ofNat_nonneg, sup_of_le_right] at him_upper
    exact ⟨him_lower, him_upper⟩

  have s_in_U_re_ges2 : ∀ s ∈ U, σ₂ ≤ s.re := by
    intro s hs
    rw [Set.mem_sdiff_singleton] at hs
    rcases hs with ⟨hbox, _hne⟩
    rcases hbox with ⟨hre, _him⟩
    simp only [Set.mem_preimage] at hre
    obtain ⟨hre_lower, hre_upper⟩ := hre
    have : min σ₂ 2 = σ₂ := by
      apply min_eq_left
      linarith [hσ₂_lt_one]
    rwa [← this]

  apply LogDerivZetaHoloOn
  · exact Set.notMem_sdiff_of_mem rfl
  · intro s hs
    rw[← re_add_im s]
    apply hζ_ne_zero
    · apply s_in_U_im_le3 _ hs
    · apply s_in_U_re_ges2 _ hs

lemma LogDerivZetaHolcSmallT' : ∃ (σ₂ : ℝ)
  (_ : σ₂ ∈ Ioo 0 1), HolomorphicOn (fun (s : ℂ) ↦ (deriv riemannZeta) s / (riemannZeta s))
    (( [[ σ₂, 2 ]] ×ℂ [[ -3, 3 ]]) \ {1}) := by
  obtain ⟨σ₂', σ₂'_lt_one, holo2'⟩ := LogDerivZetaHolcSmallT
  let σ₂ : ℝ := max σ₂' (1 / 2)
  have σ₂_pos : 0 < σ₂ := by bound
  have σ₂_lt_one : σ₂ < 1 := by bound
  refine ⟨σ₂, ⟨σ₂_pos, σ₂_lt_one⟩, holo2'.mono (fun s hs ↦ ?_)⟩
  simp only [neg_le_self_iff, Nat.ofNat_nonneg, uIcc_of_le, Set.mem_sdiff, mem_reProdIm, mem_Icc,
    mem_singleton_iff] at hs ⊢
  refine ⟨?_, hs.2⟩
  refine ⟨?_, hs.1.2⟩
  rcases hs.1.1 with ⟨left, right⟩
  constructor
  · apply le_trans _ left
    apply min_le_min_right
    apply le_max_left
  · rw [max_eq_right (by linarith)] at right ⊢
    exact right

def LogDerivZetaHolcLargeTGenProp (n : ℝ) : Prop := ∃ (A : ℝ) (_ : A ∈ Ioc 0 (1 / 2)),
    ∀ (T : ℝ) (_ : 3 ≤ T),
    HolomorphicOn (fun (s : ℂ) ↦ (deriv riemannZeta) s / (riemannZeta s))
      (( (Icc ((1 : ℝ) - A / Real.log T ^ n) 2)  ×ℂ (Icc (-T) T) ) \ {1})

lemma LogDerivZetaHolcLargeTGen {n : ℝ} (ZetaZeroFree : ZetaZeroFreeGenProp n) (n_pos : 0 < n) :
  LogDerivZetaHolcLargeTGenProp n := by
  obtain ⟨A, A_inter, restOfZetaZeroFree⟩ := ZetaZeroFree
  obtain ⟨σ₁, σ₁_lt_one, noZerosInBox⟩ := ZetaNoZerosInBox 3
  let A₀ := min A ((1 - σ₁) * Real.log 3 ^ n)
  refine ⟨A₀, ?_, ?_⟩
  · constructor
    · apply lt_min A_inter.1
      bound
    · exact le_trans (min_le_left _ _) A_inter.2
  intro T hT
  apply LogDerivZetaHoloOn
  · exact Set.notMem_sdiff_of_mem rfl
  intro s hs
  rcases le_or_gt 1 s.re with one_le|lt_one
  · exact riemannZeta_ne_zero_of_one_le_re one_le
  rw [← re_add_im s]
  have := Complex.mem_reProdIm.mp hs.1
  rcases lt_or_ge 3 |s.im| with gt3|le3
  · apply restOfZetaZeroFree _ _ gt3
    refine ⟨?_, lt_one⟩
    calc
      _ ≤ 1 - A₀ / Real.log T ^ n := by
        gcongr
        · exact A_inter.1.le
        · bound
        · bound
        · bound
        · exact abs_le.mpr ⟨this.2.1, this.2.2⟩
      _ ≤ _:= by exact this.1.1
  · apply noZerosInBox _ le3
    calc
      _ ≥ 1 - A₀ / Real.log T ^ n := by exact this.1.1
      _ ≥ 1 - A₀ / Real.log 3 ^ n := by
        gcongr
        apply le_min A_inter.1.le
        bound
      _ ≥ 1 - (((1 - σ₁) * Real.log 3 ^ n)) / Real.log 3 ^ n := by
        gcongr
        apply min_le_right
      _ = _ := by field_simp; simp

theorem LogDerivZetaHolcLargeT9 : LogDerivZetaHolcLargeTGenProp 9 := by
  apply LogDerivZetaHolcLargeTGen ZetaZeroFree9 Nat.ofNat_pos'

theorem summable_complex_then_summable_real_part (f : ℕ → ℂ)
    (h : Summable f) : Summable (fun n ↦ (f n).re) := by
  rcases h with ⟨s, hs⟩
  exact ⟨s.re,  hasSum_re hs⟩

open ArithmeticFunction (vonMangoldt)

open scoped ComplexOrder in
theorem dlog_riemannZeta_bdd_on_vertical_lines_generalized
    (σ₀ σ₁ t : ℝ) (σ₀_gt_one : 1 < σ₀) (σ₀_lt_σ₁ : σ₀ ≤ σ₁) :
    ‖(- (deriv riemannZeta) (σ₁ + t * I) / riemannZeta (σ₁ + t * I))‖ ≤ ‖(deriv riemannZeta) σ₀ / riemannZeta σ₀‖ := by
  let s₁ := σ₁ + t * I
  have s₁_re_eq_sigma : s₁.re = σ₁ := by
    rw [add_re, ofReal_re, mul_I_re, ofReal_im]
    ring

  have s₀_re_eq_sigma : (↑σ₀ : ℂ).re = σ₀ := by
    rw [ofReal_re]

  let s₀ := σ₀

  have σ₁_gt_one : 1 < σ₁ := by exact lt_of_le_of_lt' σ₀_lt_σ₁ σ₀_gt_one
  have s₀_gt_one : 1 < (↑σ₀ : ℂ).re := by exact σ₀_gt_one

  have s₁_re_geq_one : 1 < s₁.re := by exact lt_of_lt_of_eq σ₁_gt_one (id (Eq.symm s₁_re_eq_sigma))
  rw [← (ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div s₁_re_geq_one)]
  unfold LSeries

  have summable_von_mangoldt_at_σ₀ : Summable (fun i ↦ LSeries.term (fun n ↦ ↑(vonMangoldt n)) σ₀ i) := by
    exact ArithmeticFunction.LSeriesSummable_vonMangoldt σ₀_gt_one

  have summable_re_von_mangoldt_at_σ₀ :
      Summable (fun i ↦ (LSeries.term (fun n ↦ ↑(vonMangoldt n)) σ₀ i).re) := by
    exact summable_complex_then_summable_real_part (LSeries.term (fun n ↦ ↑(vonMangoldt n)) σ₀)
      summable_von_mangoldt_at_σ₀

  have summable_abs_value : Summable (fun i ↦ ‖LSeries.term (fun n ↦ ↑(vonMangoldt n)) s₁ i‖) := by
    rw [summable_norm_iff]
    exact ArithmeticFunction.LSeriesSummable_vonMangoldt s₁_re_geq_one
  apply le_trans <| norm_tsum_le_tsum_norm summable_abs_value
  rw [← norm_neg, ← neg_div, ← ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div s₀_gt_one]
  unfold LSeries
  rw [← re_eq_norm.mpr, re_tsum summable_von_mangoldt_at_σ₀]
  · apply Summable.tsum_mono summable_abs_value summable_re_von_mangoldt_at_σ₀
    intro n
    beta_reduce
    apply le_trans <| LSeries.norm_term_le_of_re_le_re (s := σ₀) _ _ _
    · rw [re_eq_norm.mpr]
      apply LSeries.term_nonneg
      exact_mod_cast ArithmeticFunction.vonMangoldt_nonneg
    · rwa [s₁_re_eq_sigma, s₀_re_eq_sigma]
  · apply tsum_nonneg
    intro n
    apply LSeries.term_nonneg
    exact_mod_cast ArithmeticFunction.vonMangoldt_nonneg

theorem triv_bound_zeta :  ∃C ≥ 0, ∀(σ₀ t : ℝ), 1 < σ₀ →
    ‖- (deriv riemannZeta) (σ₀ + t * I) / riemannZeta (σ₀ + t * I)‖ ≤ (σ₀ - 1)⁻¹ + C := by
  let ⟨U, ⟨U_in_nhds, zeta_residue_on_U⟩⟩ := riemannZetaLogDerivResidue
  let ⟨open_in_U, ⟨open_in_U_subs_U, open_in_U_is_open, one_in_open_U⟩⟩ :=
    mem_nhds_iff.mp U_in_nhds
  let ⟨ε₀, ⟨ε_pos, metric_ball_around_1_is_in_U'⟩⟩ :=
    EMetric.isOpen_iff.mp open_in_U_is_open (1 : ℂ) one_in_open_U

  let ε := if ε₀ = ⊤ then ENNReal.ofReal 1 else ε₀
  have O1 : ε ≠ ⊤ := by
    unfold ε
    by_cases h : ε₀ = ⊤ <;> simp [*]

  have metric_ball_around_1_is_in_U :
    Metric.eball (1 : ℂ) ε ⊆ U := by
      unfold ε
      by_cases h : ε₀ = ⊤
      · simp only [↓reduceIte, ENNReal.ofReal_one, h]
        have T : Metric.eball (1 : ℂ) 1 ⊆ Metric.eball 1 ε₀ := by
          simp [*]
        exact subset_trans (subset_trans T metric_ball_around_1_is_in_U') open_in_U_subs_U

      · simp only [h, ↓reduceIte]
        exact subset_trans metric_ball_around_1_is_in_U' open_in_U_subs_U

  have O2 : ε ≠ 0 := by
    unfold ε
    by_cases h : ε₀ = ⊤
    · simp [*]
    · simp only [↓reduceIte, ne_eq, h]
      exact pos_iff_ne_zero.mp ε_pos

  let metric_ball_around_1 := Metric.eball (1 : ℂ) ε
  let ε_div_two := ε / 2
  let boundary := ENNReal.toReal (1 + ε_div_two)

  let ⟨bound, ⟨bound_pos, bound_prop⟩⟩ :=
      BddAbove.exists_ge zeta_residue_on_U 0

  have boundary_geq_one : 1 < boundary := by
      unfold boundary
      have Z : (1 : ENNReal).toReal = 1 := by rfl
      rw [←Z]
      have U : ε_div_two ≠ ⊤ := by
        refine ENNReal.div_ne_top O1 ?_
        simp
      simp only [ENNReal.toReal_one, ne_eq, ENNReal.one_ne_top, not_false_eq_true,
        ENNReal.toReal_add _ U, lt_add_iff_pos_right, gt_iff_lt]
      refine ENNReal.toReal_pos ?_ ?_
      · unfold ε_div_two
        simp [*]
      · exact U

  let const : ℝ := bound
  let final_const : ℝ := (boundary - 1)⁻¹ + const
  have final_const_pos : final_const ≥ 0 := by bound
  have const_le_final_const : const ≤ final_const := by bound

  refine ⟨final_const, final_const_pos, fun σ₀ t σ₀_gt ↦ ?_⟩
  have U4 : ENNReal.ofReal 1 ≠ ⊤ := by exact ENNReal.ofReal_ne_top
  have Z0 : ε_div_two.toReal < ε.toReal := by
    exact ENNReal.toReal_strict_mono O1 <| ENNReal.half_lt_self O2 O1

  by_cases! h : σ₀ ≤ boundary
  · have σ₀_in_ball : (↑σ₀ : ℂ) ∈ metric_ball_around_1 := by
      unfold metric_ball_around_1
      unfold Metric.eball
      simp only [mem_setOf_eq]
      rw [edist_dist, dist_eq_norm]
      norm_cast
      have U : 0 ≤ σ₀ - 1 := by linarith
      simp only [Real.norm_of_nonneg U, gt_iff_lt]
      simp only [ENNReal.ofReal_lt_iff_lt_toReal U O1]
      calc
        _ ≤ boundary - 1 := by linarith
        _ = ENNReal.toReal (1 + ε_div_two) - 1 := rfl
        _ = ENNReal.toReal (1 + ε_div_two) - ENNReal.toReal (ENNReal.ofReal 1) := by simp
        _ ≤ ENNReal.toReal (1 + ε_div_two - ENNReal.ofReal 1) := ENNReal.le_toReal_sub U4
        _ = ENNReal.toReal (ε_div_two) := by
          simp only [ENNReal.ofReal_one, ENNReal.addLECancellable_iff_ne, ne_eq,
            ENNReal.one_ne_top, not_false_eq_true, AddLECancellable.add_tsub_cancel_left]
        _ < ε.toReal := Z0

    have σ₀_in_U : (↑σ₀ : ℂ) ∈ (U \ {1}) := by
      refine Set.mem_sdiff_singleton.mpr ?_
      constructor
      · exact metric_ball_around_1_is_in_U σ₀_in_ball
      · by_contra a
        have U : σ₀ = 1 := by exact ofReal_eq_one.mp a
        rw [U] at σ₀_gt
        linarith

    have bdd := Set.forall_mem_image.mp bound_prop (σ₀_in_U)
    simp only [Function.comp_apply, Pi.sub_apply, Pi.neg_apply, Pi.div_apply] at bdd

    calc
      _ ≤ ‖(deriv riemannZeta) σ₀ / riemannZeta σ₀‖ := by
        exact dlog_riemannZeta_bdd_on_vertical_lines_generalized σ₀ σ₀ t (σ₀_gt) (by simp)
      _ = ‖- (deriv riemannZeta) σ₀ / riemannZeta σ₀‖ := by simp only [Complex.norm_div, norm_neg]
      _ = ‖(- (deriv riemannZeta) σ₀ / riemannZeta σ₀ - (σ₀ - 1)⁻¹) + (σ₀ - 1)⁻¹‖ := by
        simp only [Complex.norm_div, norm_neg, ofReal_inv, ofReal_sub, ofReal_one, sub_add_cancel]
      _ ≤ ‖(- (deriv riemannZeta) σ₀ / riemannZeta σ₀ - (σ₀ - 1)⁻¹)‖ + ‖(σ₀ - 1)⁻¹‖ := by
        have Z := norm_add_le (- (deriv riemannZeta) σ₀ / riemannZeta σ₀ - (σ₀ - 1)⁻¹) ((σ₀ - 1)⁻¹)
        norm_cast at Z
      _ ≤ const + ‖(σ₀ - 1)⁻¹‖ := by
        have U := add_le_add_left bdd ‖(σ₀ - 1)⁻¹‖
        ring_nf at U
        ring_nf
        norm_cast at U
        norm_cast
      _ ≤ const + (σ₀ - 1)⁻¹ := by
        simp [norm_inv]
        have pos : 0 ≤ σ₀ - 1 := by
          linarith
        simp [abs_of_nonneg pos]
      _ = (σ₀ - 1)⁻¹ + const := by
        rw [add_comm]
      _ ≤ (σ₀ - 1)⁻¹ + final_const := by
        simp [const_le_final_const]

  · have boundary_in_ball : (↑boundary : ℂ) ∈ metric_ball_around_1 := by
      unfold metric_ball_around_1
      unfold Metric.eball
      simp only [mem_setOf_eq]
      rw [edist_dist, dist_eq_norm]
      norm_cast
      have U : 0 ≤ boundary - 1 := by linarith
      simp only [Real.norm_of_nonneg U, gt_iff_lt]
      simp only [ENNReal.ofReal_lt_iff_lt_toReal U O1]
      calc
        _ = ENNReal.toReal (1 + ε_div_two) - 1 := rfl
        _ = ENNReal.toReal (1 + ε_div_two) - ENNReal.toReal (ENNReal.ofReal 1) := by simp
        _ ≤ ENNReal.toReal (1 + ε_div_two - ENNReal.ofReal 1) := ENNReal.le_toReal_sub U4
        _ = ENNReal.toReal (ε_div_two) := by
          simp only [ENNReal.ofReal_one, ENNReal.addLECancellable_iff_ne, ne_eq,
            ENNReal.one_ne_top, not_false_eq_true, AddLECancellable.add_tsub_cancel_left]
        _ < ε.toReal := Z0

    have boundary_in_U : (↑boundary : ℂ) ∈ U \ {1} := by
      refine Set.mem_sdiff_singleton.mpr ?_
      constructor
      · exact metric_ball_around_1_is_in_U boundary_in_ball
      · by_contra a
        norm_cast at a
        norm_cast at boundary_geq_one
        simp [←a] at boundary_geq_one

    have bdd := Set.forall_mem_image.mp bound_prop (boundary_in_U)

    calc
      _ ≤ ‖(deriv riemannZeta) boundary / riemannZeta boundary‖ := by
        exact dlog_riemannZeta_bdd_on_vertical_lines_generalized boundary σ₀ t
          (boundary_geq_one) (by linarith)
      _ = ‖- (deriv riemannZeta) boundary / riemannZeta boundary‖ := by simp only [Complex.norm_div, norm_neg]
      _ = ‖(- (deriv riemannZeta) boundary / riemannZeta boundary - (boundary - 1)⁻¹) + (boundary - 1)⁻¹‖ := by
        simp only [Complex.norm_div, norm_neg, ofReal_inv, ofReal_sub, ofReal_one, sub_add_cancel]
      _ ≤ ‖(- (deriv riemannZeta) boundary / riemannZeta boundary - (boundary - 1)⁻¹)‖ + ‖(boundary - 1)⁻¹‖ := by
        have Z := norm_add_le (- (deriv riemannZeta) boundary / riemannZeta boundary - (boundary - 1)⁻¹) ((boundary - 1)⁻¹)
        norm_cast at Z
      _ ≤ const + ‖(boundary - 1)⁻¹‖ := by
        have U9 := add_le_add_left bdd ‖(boundary - 1)⁻¹‖
        ring_nf at U9
        ring_nf
        norm_cast at U9
        norm_cast
        simpa [*] using! U9
      _ ≤ const + (boundary - 1)⁻¹ := by
        simp [norm_inv]
        have pos : 0 ≤ boundary - 1 := by
          linarith
        simp [abs_of_nonneg pos]
      _ = (boundary - 1)⁻¹ + const := by
        rw [add_comm]
      _ = final_const := by rfl
      _ ≤ _ := by bound

def LogDerivZetaBndUnifGenProp (n₁ n₂ : ℝ) : Prop := ∃ (A : ℝ) (_ : A ∈ Ioc 0 (1 / 2))
  (C : ℝ) (_ : 0 < C), ∀ (σ : ℝ) (t : ℝ) (_ : 3 < |t|)
    (_ : σ ∈ Ici (1 - A / Real.log |t| ^ n₁)), ‖(deriv riemannZeta) (σ + t * I) / riemannZeta (σ + t * I)‖ ≤
      C * Real.log |t| ^ n₂

lemma LogDerivZetaBndUnif99 : LogDerivZetaBndUnifGenProp 9 9 := by
  let ⟨A, pf_A, C, C_pos, ζbd_in⟩ := LogDerivZetaBnd
  let ⟨C_triv, ⟨pf_C_triv, ζbd_out⟩⟩ := triv_bound_zeta
  have T0 : A > 0 := pf_A.1

  have ha : 1 ≤ A⁻¹ := by
    simp only [one_div, mem_Ioc, true_and, T0] at pf_A
    have U := (inv_le_inv₀ (by positivity) (by positivity)).mpr pf_A
    simp only [inv_inv] at U
    linarith

  refine ⟨A, pf_A, ((1 + C + C_triv) * A⁻¹), (by positivity), fun σ t hyp_t hyp_σ ↦ ?_⟩
  have logt_gt' : (1 : ℝ) < Real.log |t| ^ (9 : ℝ) := by
    calc
      1 < Real.log |t| := logt_gt_one hyp_t.le
      _ ≤ (Real.log |t|) ^ (9 : ℝ) := ZetaInvBnd_aux (logt_gt_one hyp_t.le)

  have logt_gt'' : (1 : ℝ) < 1 + A / Real.log |t| ^ (9 : ℝ) := by
    simp only [lt_add_iff_pos_right, div_pos_iff_of_pos_left, T0]
    positivity

  have T1 : ∀⦃σ : ℝ⦄, 1 + A / Real.log |t| ^ (9 : ℝ) ≤ σ → 1 < σ := by
    intros
    linarith

  have T2 : ∀⦃σ : ℝ⦄, 1 + A / Real.log |t| ^ (9 : ℝ) ≤ σ → A / Real.log |t| ^ (9 : ℝ) ≤ σ - 1 := by
    intro σ' hyp_σ'
    calc
      A / Real.log |t| ^ (9 : ℝ) = (1 + A / Real.log |t| ^ (9 : ℝ)) - 1 := by ring_nf
      _ ≤ σ' - 1 := by gcongr

  by_cases h : σ ∈ Ico (1 - A / Real.log |t| ^ (9 : ℝ)) (1 + A / Real.log |t| ^ (9 : ℝ))
  · calc
      ‖(deriv riemannZeta) (↑σ + ↑t * I) / riemannZeta (↑σ + ↑t * I)‖ ≤ C * Real.log |t| ^ 9 := ζbd_in σ t hyp_t h
      _ ≤ ((1 + C + C_triv) * A⁻¹) * Real.log |t| ^ (9 : ℝ) := by
          gcongr
          · calc
              C ≤ 1 + C := by simp only [le_add_iff_nonneg_left, zero_le_one]
              _ ≤ (1 + C + C_triv) * 1 := by simp only [mul_one, le_add_iff_nonneg_right]; positivity
              _ ≤ (1 + C + C_triv) * A⁻¹ := by gcongr

  · simp only [mem_Ico, tsub_le_iff_right, not_and, not_lt, mem_Ici] at h hyp_σ
    replace h := h hyp_σ
    calc
      ‖(deriv riemannZeta) (σ + t * I) / riemannZeta (σ + t * I)‖ = ‖-(deriv riemannZeta) (σ + t * I) / riemannZeta (σ + t * I)‖ := by simp only [Complex.norm_div,
        norm_neg]
      _ ≤ (σ - 1)⁻¹ + C_triv := ζbd_out σ t (by exact T1 h)
      _ ≤ (A / Real.log |t| ^ (9 : ℝ))⁻¹ + C_triv := by
          gcongr
          · exact T2 h
      _ ≤ (A / Real.log |t| ^ (9 : ℝ))⁻¹ + C_triv * A⁻¹ := by
          gcongr
          exact le_mul_of_one_le_right pf_C_triv ha
      _ ≤ (1 + C_triv) * A⁻¹ * Real.log |t| ^ (9 : ℝ) := by
          simp only [inv_div]
          ring_nf
          gcongr
          · simp only [inv_pos, le_mul_iff_one_le_left, T0]
            linarith
      _ ≤ (1 + C + C_triv) * A⁻¹ * Real.log |t| ^ (9 : ℝ) := by gcongr; simp only [le_add_iff_nonneg_right]; positivity
end

/- Adapted from PrimeNumberTheoremAnd/ZetaConj.lean. -/
section
open scoped Complex ComplexConjugate

theorem deriv_conj_conj' (f : ℂ → ℂ) (p : ℂ) :
    deriv (fun z ↦ conj (f (conj z))) (conj p) = conj (deriv f p) := by
  trans deriv (conj ∘ f ∘ conj) (conj p)
  · rfl
  simp

theorem deriv_riemannZeta_conj (s : ℂ) :
    deriv riemannZeta (conj s) = conj (deriv riemannZeta s) := by
  simp [← deriv_conj_conj']

theorem logDerivZeta_conj (s : ℂ) :
    (deriv riemannZeta / riemannZeta) (conj s) = conj ((deriv riemannZeta / riemannZeta) s) := by
  simp [deriv_riemannZeta_conj, riemannZeta_conj]

theorem logDerivZeta_conj' (s : ℂ) :
    (logDeriv riemannZeta) (conj s) = conj (logDeriv riemannZeta s) := logDerivZeta_conj s

theorem intervalIntegral_conj {f : ℝ → ℂ} {a b : ℝ} :
    ∫ (x : ℝ) in a..b, conj (f x) = conj (∫ (x : ℝ) in a..b, f x) := by
  rw [intervalIntegral.intervalIntegral_eq_integral_uIoc, integral_conj, ← RCLike.conj_smul,
    ← intervalIntegral.intervalIntegral_eq_integral_uIoc]
end

/- Adapted from PrimeNumberTheoremAnd/Mathlib/Algebra/Notation/Support.lean. -/
section
namespace Function

variable {α : Type*} [Zero α]

theorem support_id : support (id : α → α) = {0}ᶜ := by
  ext; simp

theorem support_id' {α : Type*} [Zero α] : support (fun x : α ↦ x) = {0}ᶜ :=
  support_id

end Function
end

/- Adapted from PrimeNumberTheoremAnd/SmoothExistence.lean. -/
section
open MeasureTheory Set Real
open scoped ContDiff

lemma smooth_urysohn_support_Ioo {a b c d : ℝ} (h1 : a < b) (h3 : c < d) :
    ∃ Ψ : ℝ → ℝ, (ContDiff ℝ ∞ Ψ) ∧ (HasCompactSupport Ψ) ∧
    Set.indicator (Set.Icc b c) 1 ≤ Ψ ∧ Ψ ≤ Set.indicator (Set.Ioo a d) 1 ∧
    (Function.support Ψ = Set.Ioo a d) := by
  have := exists_contMDiff_zero_iff_one_iff_of_isClosed (n := ⊤)
    (modelWithCornersSelf ℝ ℝ) (s := Set.Iic a ∪ Set.Ici d) (t := Set.Icc b c)
    (IsClosed.union isClosed_Iic isClosed_Ici) isClosed_Icc
    (by
      simp_rw [Set.disjoint_union_left, Set.disjoint_iff, Set.subset_def,
        Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc, Set.mem_empty_iff_false,
        and_imp, imp_false, not_le, Set.mem_Ici]
      constructor <;> intros <;> linarith)
  obtain ⟨Ψ, hΨSmooth, hΨrange, hΨ0, hΨ1⟩ := this
  simp only [Set.mem_union, Set.mem_Iic, Set.mem_Ici, Set.mem_Icc] at *
  use Ψ
  simp only [range_subset_iff, mem_Icc] at hΨrange
  refine ⟨ContMDiff.contDiff hΨSmooth, ?_, ?_, ?_, ?_⟩
  · apply HasCompactSupport.of_support_subset_isCompact (K := Set.Icc a d) isCompact_Icc
    simp only [Function.support_subset_iff, ne_eq, mem_Icc, ← hΨ0, not_or]
    bound
  · apply Set.indicator_le'
    · intro x hx
      rw [hΨ1 x |>.mp, Pi.one_apply]
      simpa using hx
    · exact fun x _ ↦ (hΨrange x).1
  · intro x
    apply Set.le_indicator_apply
    · exact fun _ ↦ (hΨrange x).2
    · intro hx
      rw [← hΨ0 x |>.mp]
      simpa [-not_and, mem_Ioo, not_and_or, not_lt] using hx
  · ext x
    simp only [Function.mem_support, ne_eq, mem_Ioo, ← hΨ0, not_or, not_le]

lemma SmoothExistence :
    ∃ (ν : ℝ → ℝ), (ContDiff ℝ ∞ ν) ∧ (∀ x, 0 ≤ ν x) ∧
    ν.support ⊆ Icc (1 / 2) 2 ∧ ∫ x in Ici 0, ν x / x = 1 := by
  suffices h : ∃ (ν : ℝ → ℝ), (ContDiff ℝ ∞ ν) ∧ (∀ x, 0 ≤ ν x) ∧
      ν.support ⊆ Set.Icc (1 / 2) 2 ∧ 0 < ∫ x in Set.Ici 0, ν x / x by
    obtain ⟨ν, hν, hνnonneg, hνsupp, hνpos⟩ := h
    let c := (∫ x in Ici 0, ν x / x)
    use fun y ↦ ν y / c
    refine ⟨hν.div_const c, fun y ↦ div_nonneg (hνnonneg y) (le_of_lt hνpos), ?_, ?_⟩
    · rw [Function.support_div, Function.support_const (ne_of_lt hνpos).symm, inter_univ]
      convert hνsupp
    · simp only [div_right_comm _ c _, integral_div c, div_self <| ne_of_gt hνpos, c]
  have := smooth_urysohn_support_Ioo (a := 1 / 2) (b := 1) (c := 3 / 2) (d := 2)
    (by linarith) (by linarith)
  obtain ⟨ν, hνContDiff, _, hν0, hν1, hνSupport⟩ := this
  use ν, hνContDiff
  unfold indicator at hν0 hν1
  simp only [mem_Icc, Pi.one_apply, Pi.le_def, mem_Ioo] at hν0 hν1
  simp only [hνSupport, subset_def, mem_Ioo, mem_Icc, and_imp]
  split_ands
  · exact fun x ↦ le_trans (by simp [apply_ite]) (hν0 x)
  · exact fun y hy hy' ↦ ⟨by linarith, by linarith⟩
  · rw [integral_pos_iff_support_of_nonneg]
    · simp only [Function.support_div, measurableSet_Ici, Measure.restrict_apply',
        hνSupport, Function.support_id']
      have : (Ioo (1 / 2 : ℝ) 2 ∩ {0}ᶜ ∩ Ici 0) = Ioo (1 / 2) 2 := by
        ext x
        simp only [one_div, mem_inter_iff, mem_Ioo, mem_compl_iff, mem_singleton_iff, mem_Ici]
        bound
      simp only [this, volume_Ioo, ENNReal.ofReal_pos, sub_pos, gt_iff_lt]
      linarith
    · simp_rw [Pi.le_def, Pi.zero_apply]
      intro y
      by_cases h : y ∈ Function.support ν
      · apply div_nonneg <| le_trans (by simp [apply_ite]) (hν0 y)
        rw [hνSupport, mem_Ioo] at h
        linarith [h.left]
      · simp only [Function.mem_support, ne_eq, not_not] at h
        simp [h]
    · have : (fun x ↦ ν x / x).support ⊆ Icc (1 / 2) 2 := by
        rw [Function.support_div, hνSupport]
        exact (inter_subset_left).trans Ioo_subset_Icc_self
      apply (integrableOn_iff_integrable_of_support_subset this).mp
      apply ContinuousOn.integrableOn_compact isCompact_Icc
      apply hνContDiff.continuous.continuousOn.div continuousOn_id ?_
      simp only [mem_Icc, ne_eq, and_imp, id_eq]
      intros; linarith
end

/- Adapted from PrimeNumberTheoremAnd/MediumPNT.lean. -/
section
open Set Function Filter Complex Real

open ArithmeticFunction (vonMangoldt)
open scoped Chebyshev

namespace Chebyshev

theorem psi_eq_sum_range (x : ℝ) :
    ψ x = ∑ n ∈ Finset.range (⌊x⌋₊ + 1), vonMangoldt n := by
  rw [psi_eq_sum_Icc, Nat.range_succ_eq_Icc_zero]

end Chebyshev

noncomputable abbrev ChebyshevPsi (x : ℝ) : ℝ :=
  Chebyshev.psi x

theorem LogDerivativeDirichlet (s : ℂ) (hs : 1 < s.re) :
    - deriv riemannZeta s / riemannZeta s = ∑' n, vonMangoldt n / (n : ℂ) ^ s := by
  rw [← ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs]
  dsimp [LSeries, LSeries.term]
  nth_rewrite 2 [Summable.tsum_eq_add_tsum_ite (b := 0) ?_]
  · simp
  · have := ArithmeticFunction.LSeriesSummable_vonMangoldt hs
    dsimp [LSeriesSummable] at this
    convert! this; rename ℕ => n
    by_cases h : n = 0 <;> simp [LSeries.term, h]

noncomputable abbrev SmoothedChebyshevIntegrand
    (SmoothingF : ℝ → ℝ) (ε : ℝ) (X : ℝ) : ℂ → ℂ :=
  fun s ↦ (- deriv riemannZeta s) / riemannZeta s *
    mellin (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) s * (X : ℂ) ^ s

noncomputable def SmoothedChebyshev (SmoothingF : ℝ → ℝ) (ε : ℝ) (X : ℝ) : ℂ :=
  VerticalIntegral' (SmoothedChebyshevIntegrand SmoothingF ε X) ((1 : ℝ) + (Real.log X)⁻¹)

open ComplexConjugate

lemma smoothedChebyshevIntegrand_conj
    {SmoothingF : ℝ → ℝ} {ε X : ℝ} (Xpos : 0 < X) (s : ℂ) :
    SmoothedChebyshevIntegrand SmoothingF ε X (conj s) =
      conj (SmoothedChebyshevIntegrand SmoothingF ε X s) := by
  unfold SmoothedChebyshevIntegrand
  simp only [map_mul, map_div₀, map_neg]
  congr
  · exact deriv_riemannZeta_conj s
  · exact riemannZeta_conj s
  · unfold mellin
    rw[← integral_conj]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro x xpos
    simp only [smul_eq_mul, map_mul, Complex.conj_ofReal]
    congr
    nth_rw 1 [← map_one conj]
    rw[← map_sub, Complex.cpow_conj, Complex.conj_ofReal]
    rw[Complex.arg_ofReal_of_nonneg xpos.le]
    exact Real.pi_ne_zero.symm
  · rw[Complex.cpow_conj, Complex.conj_ofReal]
    rw[Complex.arg_ofReal_of_nonneg Xpos.le]
    exact Real.pi_ne_zero.symm

open MeasureTheory

lemma SmoothedChebyshevDirichlet_aux_integrable {SmoothingF : ℝ → ℝ}
    (diffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (SmoothingFpos : ∀ x > 0, 0 ≤ SmoothingF x)
    (suppSmoothingF : support SmoothingF ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ (x : ℝ) in Ioi 0, SmoothingF x / x = 1)
    {ε : ℝ} (εpos : 0 < ε) (ε_lt_one : ε < 1) {σ : ℝ} (σ_gt : 1 < σ) (σ_le : σ ≤ 2) :
    MeasureTheory.Integrable
      (fun (y : ℝ) ↦ mellin (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (σ + y * I)) := by
  obtain ⟨c, cpos, hc⟩ := MellinOfSmooth1b diffSmoothingF suppSmoothingF
  apply Integrable.mono' (g := (fun t ↦ c / ε * 1 / (1 + t ^ 2)))
  · apply Integrable.const_mul integrable_inv_one_add_sq
  · apply Continuous.aestronglyMeasurable
    apply continuous_iff_continuousAt.mpr
    intro x
    have := Smooth1MellinDifferentiable diffSmoothingF suppSmoothingF ⟨εpos, ε_lt_one⟩
      SmoothingFpos mass_one (s := σ + x * I) (by simp only [add_re, ofReal_re, mul_re, I_re,
        mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero]; linarith) |>.continuousAt
    fun_prop
  · filter_upwards [] with t
    calc
      _≤ c / ε * 1 / (σ^2 + t^2) := by
        convert hc (σ / 2) (by linarith) (σ + t * I) (by simp only [add_re, ofReal_re, mul_re,
          I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero, half_le_self_iff]; linarith)
          (by simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
            sub_self, add_zero]; linarith) ε εpos  ε_lt_one using 1
        simp only [mul_one, Complex.sq_norm, normSq_apply, add_re, ofReal_re, mul_re, I_re,
          mul_zero, ofReal_im, I_im, sub_self, add_zero, add_im, mul_im, zero_add, mul_inv_rev]
        ring_nf
      _ ≤ _ := by
        gcongr; nlinarith

lemma SmoothedChebyshevDirichlet_aux_tsum_integral {SmoothingF : ℝ → ℝ}
    (diffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (SmoothingFpos : ∀ x > 0, 0 ≤ SmoothingF x)
    (suppSmoothingF : support SmoothingF ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ (x : ℝ) in Ioi 0, SmoothingF x / x = 1) {X : ℝ}
    (X_pos : 0 < X) {ε : ℝ} (εpos : 0 < ε)
    (ε_lt_one : ε < 1) {σ : ℝ} (σ_gt : 1 < σ) (σ_le : σ ≤ 2) :
    ∫ (t : ℝ),
      ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n) / (n : ℂ) ^ (σ + t * I) *
        mellin (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (σ + t * I) * (X : ℂ) ^ (σ + t * I) =
    ∑' (n : ℕ),
      ∫ (t : ℝ), (ArithmeticFunction.vonMangoldt n) / (n : ℂ) ^ (σ + ↑t * I) *
        mellin (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (σ + ↑t * I) * (X : ℂ) ^ (σ + t * I) := by

  have cont_mellin_smooth : Continuous fun (a : ℝ) ↦
      mellin (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (σ + ↑a * I) := by
    rw [← continuousOn_univ]
    refine ContinuousOn.comp' ?_ ?_ ?_ (t := {z : ℂ | 0 < z.re })
    · refine continuousOn_of_forall_continuousAt ?_
      intro z hz
      exact (Smooth1MellinDifferentiable diffSmoothingF suppSmoothingF ⟨εpos, ε_lt_one⟩
        SmoothingFpos mass_one hz).continuousAt
    · fun_prop
    · simp only [mapsTo_univ_iff, mem_setOf_eq, add_re, ofReal_re, mul_re, I_re, mul_zero,
        ofReal_im, I_im, mul_one, sub_self, add_zero, forall_const]; linarith

  have abs_two : ∀ a : ℝ, ∀ i : ℕ, ‖(i : ℂ) ^ ((σ : ℂ) + ↑a * I)‖₊ = i ^ σ := by
    intro a i
    simp_rw [← norm_toNNReal]
    rw [norm_natCast_cpow_of_re_ne_zero _ (by simp only [add_re, ofReal_re, mul_re, I_re, mul_zero,
      ofReal_im, I_im, mul_one, sub_self, add_zero, ne_eq]; linarith)]
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, Real.toNNReal_of_nonneg <| rpow_nonneg (y := σ) (x := i) (by linarith)]
    norm_cast

  rw [MeasureTheory.integral_tsum]
  · have x_neq_zero : X ≠ 0 := by linarith
    intro i
    by_cases i_eq_zero : i = 0
    · simpa [i_eq_zero] using aestronglyMeasurable_const
    · apply Continuous.aestronglyMeasurable
      have ht : Continuous (fun t : ℝ => (σ:ℂ)+(t:ℂ)*I) := by fun_prop
      have hi : (i:ℂ) ≠ 0 := by exact_mod_cast i_eq_zero
      have hX : (X:ℂ) ≠ 0 := by exact_mod_cast x_neq_zero
      exact ((continuous_const.div (ht.const_cpow (Or.inl hi))
        (fun _ => Complex.cpow_ne_zero_iff.mpr (Or.inl hi))).mul cont_mellin_smooth).mul
        (ht.const_cpow (Or.inl hX))
  · rw [← lt_top_iff_ne_top]
    simp_rw [enorm_mul, enorm_eq_nnnorm, nnnorm_div, ← norm_toNNReal,
      Complex.norm_cpow_eq_rpow_re_of_pos X_pos, norm_toNNReal, abs_two]
    simp only [nnnorm_real, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
      sub_self, add_zero]
    simp_rw [MeasureTheory.lintegral_mul_const' (r := ↑(X ^ σ).toNNReal) (hr := by simp),
      ENNReal.tsum_mul_right]
    apply ENNReal.mul_lt_top ?_ ENNReal.coe_lt_top

    conv =>
      arg 1
      arg 1
      intro i
      rw [MeasureTheory.lintegral_const_mul' (hr := by simp)]

    rw [ENNReal.tsum_mul_right]
    apply ENNReal.mul_lt_top
    · rw [lt_top_iff_ne_top, ENNReal.tsum_coe_ne_top_iff_summable_coe]
      push_cast
      convert (ArithmeticFunction.LSeriesSummable_vonMangoldt (s := σ)
        (by simp only [ofReal_re]; linarith)).norm
      rw [LSeries.term_def]
      split_ifs with h <;> simp[h]
    · simp_rw [← enorm_eq_nnnorm]
      rw [← MeasureTheory.hasFiniteIntegral_iff_enorm]
      exact SmoothedChebyshevDirichlet_aux_integrable diffSmoothingF SmoothingFpos suppSmoothingF
            mass_one εpos ε_lt_one σ_gt σ_le |>.hasFiniteIntegral

theorem SmoothedChebyshevDirichlet {SmoothingF : ℝ → ℝ}
    (diffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (SmoothingFpos : ∀ x > 0, 0 ≤ SmoothingF x)
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi (0 : ℝ), SmoothingF x / x = 1)
    {X : ℝ} (X_gt : 3 < X) {ε : ℝ} (εpos : 0 < ε) (ε_lt_one : ε < 1) :
    SmoothedChebyshev SmoothingF ε X =
      ∑' n, ArithmeticFunction.vonMangoldt n * Smooth1 SmoothingF ε (n / X) := by
  dsimp [SmoothedChebyshev, SmoothedChebyshevIntegrand, VerticalIntegral', VerticalIntegral]
  set σ : ℝ := 1 + (Real.log X)⁻¹
  have log_gt : 1 < Real.log X := logt_gt_one X_gt.le
  have σ_gt : 1 < σ := by
    simp only [σ]
    have : 0 < (Real.log X)⁻¹ := by
      simp only [inv_pos]
      linarith
    linarith
  have σ_le : σ ≤ 2 := by
    simp only [σ]
    have : (Real.log X)⁻¹ < 1 := inv_lt_one_of_one_lt₀ log_gt
    linarith
  calc
    _ = 1 / (2 * π * I) * (I * ∫ (t : ℝ), ∑' n, vonMangoldt n / (n : ℂ) ^ (σ + ↑t * I) *
      mellin (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (σ + ↑t * I) * X ^ (σ + ↑t * I)) := ?_
    _ = 1 / (2 * π * I) * (I * ∑' n, ∫ (t : ℝ), vonMangoldt n / (n : ℂ) ^ (σ + ↑t * I) *
      mellin (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (σ + ↑t * I) * X ^ (σ + ↑t * I)) := ?_
    _ = 1 / (2 * π * I) * (I * ∑' n, vonMangoldt n * ∫ (t : ℝ),
      mellin (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (σ + ↑t * I) *
        (X / (n : ℂ)) ^ (σ + ↑t * I)) := ?_
    _ = 1 / (2 * π) * (∑' n, vonMangoldt n * ∫ (t : ℝ),
      mellin (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (σ + ↑t * I) *
        (X / (n : ℂ)) ^ (σ + ↑t * I)) := ?_
    _ = ∑' n, vonMangoldt n * (1 / (2 * π) * ∫ (t : ℝ),
      mellin (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (σ + ↑t * I) *
        (X / (n : ℂ)) ^ (σ + ↑t * I)) := ?_
    _ = ∑' n, vonMangoldt n * (1 / (2 * π) * ∫ (t : ℝ),
      mellin (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (σ + ↑t * I) *
        ((n : ℂ) / X) ^ (-(σ + ↑t * I))) := ?_
    _ = _ := ?_
  · congr; ext t
    rw [LogDerivativeDirichlet]
    · rw [← tsum_mul_right, ← tsum_mul_right]
    · simp [σ_gt]
  · congr
    exact SmoothedChebyshevDirichlet_aux_tsum_integral diffSmoothingF SmoothingFpos
      suppSmoothingF mass_one (by linarith) εpos ε_lt_one σ_gt σ_le
  · field_simp; congr; ext n; rw [← MeasureTheory.integral_const_mul]; congr; ext t
    by_cases n_ne_zero : n = 0
    · simp [n_ne_zero]
    rw [mul_div_assoc, mul_assoc]
    congr
    rw [(div_eq_iff ?_).mpr]
    · have := @mul_cpow_ofReal_nonneg (a := X / (n : ℝ)) (b := (n : ℝ)) (r := σ + I * t) ?_ ?_
      · push_cast at this ⊢
        rw [← this, div_mul_cancel₀]
        · simp only [ne_eq, Nat.cast_eq_zero, n_ne_zero, not_false_eq_true]
      · apply div_nonneg (by linarith : 0 ≤ X); simp
      · simp
    · simp only [ne_eq, cpow_eq_zero_iff, Nat.cast_eq_zero, n_ne_zero, false_and,
        not_false_eq_true]
  · conv => rw [← mul_assoc, div_mul]; lhs; lhs; rhs; simp
  · simp_rw [← tsum_mul_left, ← mul_assoc, mul_comm]
  · have ht (t : ℝ) : -(σ + t * I) = (-1) * (σ + t * I) := by simp
    have hn (n : ℂ) : (n / X) ^ (-1 : ℂ) = X / n := by simp [cpow_neg_one]
    have (n : ℕ) : (log ((n : ℂ) / (X : ℂ)) * -1).im = 0 := by
      simp [Complex.log_im, arg_eq_zero_iff, div_nonneg (Nat.cast_nonneg _) (by linarith : 0 ≤ X)]
    have h (n : ℕ) (t : ℝ) : ((n : ℂ) / X) ^ ((-1 : ℂ) * (σ + t * I)) =
        ((n / X) ^ (-1 : ℂ)) ^ (σ + ↑t * I) := by
      rw [cpow_mul] <;> {rw [this n]; simp [Real.pi_pos, Real.pi_nonneg]}
    conv => rhs; lhs; intro n; rhs; rhs; rhs; intro t; rhs; rw [ht t, h n t]; lhs; rw [hn]
  · push_cast
    congr
    ext n
    by_cases n_zero : n = 0
    · simp [n_zero]
    have n_pos : 0 < n := by
      simpa only [n_zero, gt_iff_lt, false_or] using (Nat.eq_zero_or_pos n)
    congr
    have := mellinInv_mellin_eq σ (f := fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (x := n / X)
      ?_ ?_ ?_ ?_
    · beta_reduce at this
      dsimp [mellinInv, VerticalIntegral] at this
      convert! this using 4
      · norm_cast
      · rw [mul_comm]
        norm_cast
    · exact div_pos (by exact_mod_cast n_pos) (by linarith : 0 < X)
    · apply Smooth1MellinConvergent diffSmoothingF suppSmoothingF ⟨εpos, ε_lt_one⟩
        SmoothingFpos mass_one
      simp only [ofReal_re]
      linarith
    · dsimp [VerticalIntegrable]
      apply SmoothedChebyshevDirichlet_aux_integrable diffSmoothingF SmoothingFpos
        suppSmoothingF mass_one εpos ε_lt_one σ_gt σ_le
    · refine ContinuousAt.comp (g := ofReal) RCLike.continuous_ofReal.continuousAt ?_
      exact Smooth1ContinuousAt diffSmoothingF SmoothingFpos suppSmoothingF
        εpos (by positivity)

theorem SmoothedChebyshevClose_aux {Smooth1 : (ℝ → ℝ) → ℝ → ℝ → ℝ} (SmoothingF : ℝ → ℝ)
    (c₁ : ℝ) (c₁_pos : 0 < c₁) (c₁_lt : c₁ < 1)
    (c₂ : ℝ) (c₂_pos : 0 < c₂) (c₂_lt : c₂ < 2)
    (hc₂ : ∀ (ε x : ℝ), ε ∈ Ioo 0 1 → 1 + c₂ * ε ≤ x → Smooth1 SmoothingF ε x = 0)
    (C : ℝ) (C_eq : C = 6 * (3 * c₁ + c₂))
    (ε : ℝ) (ε_pos : 0 < ε) (ε_lt_one : ε < 1)
    (X : ℝ) (X_pos : 0 < X) (X_gt_three : 3 < X)
    (X_bound_1 : 1 ≤ X * ε * c₁) (X_bound_2 : 1 ≤ X * ε * c₂)
    (smooth1BddAbove : ∀ (n : ℕ), 0 < n → Smooth1 SmoothingF ε (↑n / X) ≤ 1)
    (smooth1BddBelow : ∀ (n : ℕ), 0 < n → Smooth1 SmoothingF ε (↑n / X) ≥ 0)
    (smoothIs1 : ∀ (n : ℕ), 0 < n → ↑n ≤ X * (1 - c₁ * ε) →
      Smooth1 SmoothingF ε (↑n / X) = 1)
    (smoothIs0 : ∀ (n : ℕ), 1 + c₂ * ε ≤ ↑n / X → Smooth1 SmoothingF ε (↑n / X) = 0) :
  ‖(↑((∑' (n : ℕ), ArithmeticFunction.vonMangoldt n * Smooth1 SmoothingF ε (↑n / X))) : ℂ) -
      ψ X‖ ≤
    C * ε * X * Real.log X := by
  norm_cast

  let F := Smooth1 SmoothingF ε

  let n₀ := ⌈X * (1 - c₁ * ε)⌉₊

  have n₀_pos : 0 < n₀ := by
    simp only [Nat.ceil_pos, n₀]
    subst C_eq
    simp_all only [mem_Ioo, and_imp, ge_iff_le, implies_true, mul_pos_iff_of_pos_left, sub_pos]
    exact mul_lt_one_of_nonneg_of_lt_one_left c₁_pos.le c₁_lt ε_lt_one.le

  have n₀_inside_le_X : X * (1 - c₁ * ε) ≤ X := by
    nth_rewrite 2 [← mul_one X]
    apply mul_le_mul_of_nonneg_left _ X_pos.le
    apply sub_le_self
    positivity

  have n₀_le : n₀ ≤ X * ((1 - c₁ * ε)) + 1 := by
    simp only [n₀]
    exact le_of_lt (Nat.ceil_lt_add_one (by bound))

  have n₀_gt : X * ((1 - c₁ * ε)) ≤ n₀ := by
    simp only [n₀]
    exact Nat.le_ceil (X * (1 - c₁ * ε))

  have sumΛ : Summable (fun (n : ℕ) ↦ vonMangoldt n * F (n / X)) := by
    exact (summable_of_ne_finset_zero fun a s=>mul_eq_zero_of_right _
    (hc₂ _ _ (⟨ε_pos, ε_lt_one⟩) ((le_div_iff₀ X_pos).2 (Nat.ceil_le.1 (not_lt.1
    (s ∘ Finset.mem_range.2))))))

  have sumΛn₀ (n₀ : ℕ) : Summable (fun n ↦ vonMangoldt (n + n₀) * F ((n + n₀) / X)) := by
    exact_mod_cast sumΛ.comp_injective fun Q => by omega

  rw[← Summable.sum_add_tsum_nat_add' (k := n₀) (mod_cast sumΛn₀ n₀)]

  let n₁ := ⌊X * (1 + c₂ * ε)⌋₊

  have n₁_pos : 0 < n₁ := by
    dsimp only [n₁]
    apply Nat.le_floor
    rw[Nat.succ_eq_add_one, zero_add]
    norm_cast
    apply one_le_mul_of_one_le_of_one_le (by linarith)
    apply le_add_of_nonneg_right
    positivity

  have n₁_ge : X * (1 + c₂ * ε) - 1 ≤ n₁ := by
    simp only [tsub_le_iff_right, n₁]
    exact le_of_lt (Nat.lt_floor_add_one (X * (1 + c₂ * ε)))

  have n₁_le : (n₁ : ℝ) ≤ X * (1 + c₂ * ε) := by
    simp only [n₁]
    exact Nat.floor_le (by bound)

  have n₁_ge_n₀ : n₀ ≤ n₁ := by
    exact_mod_cast le_imp_le_of_le_of_le n₀_le n₁_ge (by linarith)

  have n₁_sub_n₀ : (n₁ : ℝ) - n₀ ≤ X * ε * (c₂ + c₁) := by
    calc
      (n₁ : ℝ) - n₀ ≤ X * (1 + c₂ * ε) - n₀ := by
                        exact sub_le_sub_right n₁_le ↑n₀
       _            ≤ X * (1 + c₂ * ε) - (X * (1 - c₁ * ε)) := by
          exact tsub_le_tsub_left n₀_gt (X * (1 + c₂ * ε))
       _            = X * ε * (c₂ + c₁) := by ring

  rw[show (∑' (n : ℕ), vonMangoldt (n + n₀ : ) * F ((n + n₀ : ) / X)) =
      (∑ n ∈ Finset.range (n₁ - n₀), vonMangoldt (n + n₀) * F ((n + n₀) / X)) +
      (∑' (n : ℕ), vonMangoldt (n + n₁ : ) * F ((n + n₁ : ) / X)) by
    rw[← Summable.sum_add_tsum_nat_add' (k := n₁ - n₀)]
    · congr! 5
      · simp only [Nat.cast_add]
      · omega
      · congr! 1
        norm_cast
        omega
    · convert sumΛn₀ ((n₁ - n₀) + n₀) using 4
      · omega
      · congr! 1
        norm_cast
        omega]

  rw [show(∑' (n : ℕ), vonMangoldt (n + n₁) * F (↑(n + n₁) / X)) = vonMangoldt (n₁) * F (↑n₁ / X) by
    have : (∑' (n : ℕ), vonMangoldt (n + n₁) * F (↑(n + n₁) / X)) =
        vonMangoldt (n₁) * F (↑n₁ / X) + (∑' (n : ℕ), vonMangoldt (n + 1 + n₁) * F (↑(n + 1 + n₁) / X)) := by
      let fTemp := fun n ↦ vonMangoldt (n + n₁) * F ((↑n + ↑n₁) / X)
      have hTemp (n : ℕ): fTemp n = vonMangoldt (n + n₁) * F (↑(n + n₁) / X) := by rw[Nat.cast_add]
      rw[← tsum_congr hTemp, ← tsum_congr fun n ↦ (hTemp (n + 1))]
      have : vonMangoldt n₁ * F (↑n₁ / X) = fTemp 0 := by
        dsimp only [fTemp]
        rw[← Nat.cast_add, zero_add]
      rw[this]
      exact Summable.tsum_eq_zero_add (sumΛn₀ n₁)
    rw[this]
    apply add_eq_left.mpr
    convert tsum_zero with n
    convert mul_zero _
    apply smoothIs0
    rw[← mul_le_mul_iff_left₀ X_pos]
    rw [(by field_simp : ↑(n + 1 + n₁) / X * X = ↑(n + 1 + n₁)),
      (by ring : (1 + c₂ * ε) * X = 1 + (X * (1 + c₂ * ε) - 1)), Nat.cast_add, Nat.cast_add]
    bound]

  have X_le_floor_add_one : X ≤ ↑⌊X + 1⌋₊ := by
    rw[Nat.floor_add_one (by linarith), Nat.cast_add, Nat.cast_one]
    apply le_trans <| Nat.le_ceil X
    exact_mod_cast Nat.ceil_le_floor_add_one X

  have floor_X_add_one_le_self : ↑⌊X + 1⌋₊ ≤ X + 1 := Nat.floor_le (by positivity)

  rw [show ψ X =
      (∑ x ∈ Finset.range n₀, vonMangoldt x) +
      ∑ x ∈ Finset.range (⌊X + 1⌋₊ - n₀), vonMangoldt (x + ↑n₀) by
    field_simp
    simp only [add_comm _ n₀]
    rw [← Finset.sum_range_add, Nat.add_sub_of_le, Chebyshev.psi_eq_sum_range,
      Nat.floor_add_one X_pos.le]
    dsimp only [n₀]
    exact Nat.ceil_le.mpr (by linarith)]

  rw [show ∑ n ∈ Finset.range n₀, vonMangoldt n * F (↑n / X) =
      ∑ n ∈ Finset.range n₀, vonMangoldt n by
    apply Finset.sum_congr rfl
    intro n hn
    obtain rfl|n_zero := eq_or_ne n 0
    · simp only [ArithmeticFunction.map_zero, CharP.cast_eq_zero, zero_div, zero_mul]
    · convert mul_one _
      apply smoothIs1 n (Nat.zero_lt_of_ne_zero n_zero) ?_
      simp only [Finset.mem_range, n₀] at hn
      exact Nat.lt_ceil.mp hn |>.le]
  have vonBnd1 :
    ∀ n ∈ Finset.range (n₁ - n₀), ‖vonMangoldt (n + n₀)‖ ≤ Real.log (X * (1 + c₂ * ε)) := by
    intro n hn
    have n_add_n0_le_n1: (n : ℝ) + n₀ ≤ n₁ := by
      apply le_of_lt
      rw[Finset.mem_range] at hn
      rw[← add_lt_add_iff_right (-↑n₀), add_neg_cancel_right, add_comm, ← sub_eq_neg_add]
      exact_mod_cast hn
    have inter1: ‖ vonMangoldt (n + n₀)‖ ≤ Real.log (↑n + ↑n₀) := by
      rw[Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, ← Nat.cast_add]
      apply ArithmeticFunction.vonMangoldt_le_log
    have inter2: Real.log (↑n + ↑n₀) ≤ Real.log (↑n₁) := by
      exact_mod_cast Real.log_le_log (by positivity) n_add_n0_le_n1
    have inter3: Real.log (↑n₁) ≤ Real.log (X * (1 + c₂ * ε)) := by
      exact Real.log_le_log (by bound) (by linarith)
    exact le_imp_le_of_le_of_le inter1 inter3 inter2

  have bnd1 :
    ∑ n ∈ Finset.range (n₁ - n₀), ‖vonMangoldt (n + n₀)‖ * ‖F ((↑n + ↑n₀) / X)‖
    ≤ (n₁ - n₀) * Real.log (X * (1 + c₂ * ε)) := by
    have : (n₁ - n₀) * Real.log (X * (1 + c₂ * ε)) =
        (∑ n ∈ Finset.range (n₁ - n₀), Real.log (X * (1 + c₂ * ε))) := by
      rw[← Nat.cast_sub]
      · nth_rewrite 1 [← Finset.card_range (n₁ - n₀)]
        rw[Finset.cast_card, Finset.sum_const, smul_one_mul]
        exact Eq.symm (Finset.sum_const (Real.log (X * (1 + c₂ * ε))))
      exact n₁_ge_n₀
    rw [this]
    apply Finset.sum_le_sum
    intro n hn
    rw [← mul_one (Real.log (X * (1 + c₂ * ε)))]
    apply mul_le_mul (vonBnd1 _ hn) _ (norm_nonneg _) (log_nonneg (by bound))
    rw[Real.norm_of_nonneg, ← Nat.cast_add]
    · dsimp only [F]
      apply smooth1BddAbove
      bound
    rw[← Nat.cast_add]
    dsimp only [F]
    apply smooth1BddBelow
    bound

  have bnd2 :
    ∑ x ∈ Finset.range (⌊X + 1⌋₊ - n₀), ‖vonMangoldt (x + n₀)‖ ≤ (⌊X + 1⌋₊ - n₀) * Real.log (X + 1) := by
    have : (⌊X + 1⌋₊ - n₀) * Real.log (X + 1) =
        (∑ n ∈ Finset.range (⌊X + 1⌋₊ - n₀), Real.log (X + 1)) := by
      rw[← Nat.cast_sub]
      · nth_rewrite 1 [← Finset.card_range (⌊X + 1⌋₊ - n₀)]
        rw[Finset.cast_card, Finset.sum_const, smul_one_mul]
        exact Eq.symm (Finset.sum_const (Real.log (X + 1)))
      simp only [Nat.ceil_le, n₀]
      exact Preorder.le_trans (X * (1 - c₁ * ε)) X (↑⌊X + 1⌋₊) n₀_inside_le_X
        X_le_floor_add_one
    rw[this]
    apply Finset.sum_le_sum
    intro n hn
    have n_add_n0_le_X_add_one: (n : ℝ) + n₀ ≤ X + 1 := by
      rw[Finset.mem_range] at hn
      rw [← add_le_add_iff_right (-↑n₀), add_assoc, ← sub_eq_add_neg, sub_self, add_zero,
        ← sub_eq_add_neg]
      have temp: (n : ℝ) < ⌊X + 1⌋₊ - n₀ := by
        rw [← Nat.cast_sub, Nat.cast_lt]
        · exact hn
        simp only [Nat.ceil_le, n₀]
        exact le_trans n₀_inside_le_X X_le_floor_add_one
      have : ↑⌊X + 1⌋₊ - ↑n₀ ≤ X + 1 - ↑n₀ := by
        apply sub_le_sub_right floor_X_add_one_le_self
      exact le_of_lt (lt_of_le_of_lt' this temp)
    have inter1: ‖ vonMangoldt (n + n₀)‖ ≤ Real.log (↑n + ↑n₀) := by
      rw[Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, ← Nat.cast_add]
      apply ArithmeticFunction.vonMangoldt_le_log
    apply le_trans inter1
    exact_mod_cast Real.log_le_log (by positivity) (n_add_n0_le_X_add_one)

  clear vonBnd1

  have inter1 : Real.log (X * (1 + c₂ * ε)) ≤ Real.log (3 * X) := by
    apply Real.log_le_log (by positivity)
    have const_le_2: 1 + c₂ * ε ≤ 3 := by
      have : (3 : ℝ) = 1 + 2 := by ring
      rw[this]
      apply add_le_add_right
      rw[← mul_one 2]
      exact mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
    rw[mul_comm]
    exact mul_le_mul const_le_2 (by rfl) (by positivity) (by positivity)

  calc
    _ = ‖∑ n ∈ Finset.range (n₁ - n₀), vonMangoldt (n + n₀) * F ((↑n + ↑n₀) / X) -
          ∑ x ∈ Finset.range (⌊X + 1⌋₊ - n₀), vonMangoldt (x + n₀) + vonMangoldt n₁ * F (↑n₁ / X)‖ := by
      congr 1
      ring
    _ ≤ (∑ n ∈ Finset.range (n₁ - n₀), ‖vonMangoldt (n + n₀)‖ * ‖F ((↑n + ↑n₀) / X)‖) +
        ∑ x ∈ Finset.range (⌊X + 1⌋₊ - n₀), ‖vonMangoldt (x + n₀)‖ +
        ‖vonMangoldt n₁‖ * ‖F (↑n₁ / X)‖ := by
      apply norm_add_le_of_le
      · apply norm_sub_le_of_le
        · apply norm_sum_le_of_le
          intro b hb
          exact norm_mul_le_of_le (by rfl) (by rfl)
        apply norm_sum_le_of_le
        intro b hb
        rfl
      exact_mod_cast norm_mul_le_of_le (by rfl) (by rfl)
    _ ≤ 2 * (X * ε * (3 * c₁ + c₂)) * Real.log X + Real.log (3 * X) := by
      apply add_le_add
      · apply le_trans <| add_le_add bnd1 bnd2
        rw [(by ring : 2 * (X * ε * (3 * c₁ + c₂)) = 2 * (X * ε * (c₁ + c₂)) + 4 * (X * ε * c₁)), add_mul]
        apply add_le_add
        · calc
            _ ≤ (X * ε * (c₂ + c₁)) * (Real.log (X) + Real.log (3)) := by
              apply mul_le_mul n₁_sub_n₀ _ (log_nonneg (by linarith)) (by positivity)
              rw[← Real.log_mul (by positivity) (by positivity)]
              nth_rewrite 3 [mul_comm]
              exact inter1
            _ ≤ 2 * ((X * ε * (c₂ + c₁)) * Real.log X) := by
              rw[two_mul, mul_add]
              bound
            _ = _ := by ring
        calc
          _ ≤ 2 * (X * ε * c₁) * (Real.log (X) + Real.log (3)) := by
            apply mul_le_mul _ _ (log_nonneg (by linarith)) (by positivity)
            · rw [(by ring : 2 * (X * ε * c₁) = (X * (1 + ε * c₁)) - (X * (1 - ε * c₁)))]
              apply sub_le_sub
              · apply le_trans floor_X_add_one_le_self
                ring_nf
                rw[add_comm, add_le_add_iff_left]
                exact X_bound_1
              nth_rewrite 2 [mul_comm]
              exact n₀_gt
            rw[← Real.log_mul (by positivity) (by norm_num), mul_comm]
            exact Real.log_le_log (by positivity) (by linarith)
          _ = 2 * (X * ε * c₁ * Real.log X) + 2 * (X * ε * c₁ * Real.log 3) := by ring
          _ ≤ 2 * (X * ε * c₁ * Real.log X) + 2 * (X * ε * c₁ * Real.log X) := by gcongr
          _ = _ := by ring
      · apply le_trans _ inter1
        rw[← mul_one (Real.log (X * (1 + c₂ * ε)))]
        apply mul_le_mul _ _ (norm_nonneg _) (log_nonneg (by bound))
        · rw[Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
          exact le_trans ArithmeticFunction.vonMangoldt_le_log <|
            Real.log_le_log (mod_cast n₁_pos) n₁_le
        rw[Real.norm_of_nonneg <| smooth1BddBelow _ n₁_pos]
        apply smooth1BddAbove _ n₁_pos
    _ ≤ 2 * (X * ε * (3 * c₁ + c₂)) * (Real.log X + (Real.log X + Real.log 3)) := by
      rw [← Real.log_mul (by positivity) (by positivity), mul_comm X 3]
      nth_rewrite 2 [mul_add]
      apply add_le_add_right
      nth_rewrite 1 [← one_mul (Real.log (3 * X))]
      apply mul_le_mul_of_nonneg_right _ (log_nonneg (by linarith))
      linarith
    _ = 4 * (X * ε * (3 * c₁ + c₂)) * Real.log X +
          2 * (X * ε * (3 * c₁ + c₂)) * Real.log 3 := by ring
    _ ≤ 4 * (X * ε * (3 * c₁ + c₂)) * Real.log X +
          2 * (X * ε * (3 * c₁ + c₂)) * Real.log X := by gcongr
    _ = _ := by
      rw [C_eq]
      ring

theorem SmoothedChebyshevClose {SmoothingF : ℝ → ℝ}
    (diffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1) :
    ∃ C > 0, ∀ (X : ℝ) (_ : 3 < X) (ε : ℝ) (_ : 0 < ε) (_ : ε < 1) (_ : 2 < X * ε),
    ‖SmoothedChebyshev SmoothingF ε X - ψ X‖ ≤ C * ε * X * Real.log X := by
  obtain ⟨c₁, c₁_pos, c₁_eq, hc₁⟩ := Smooth1Properties_below suppSmoothingF mass_one

  obtain ⟨c₂, c₂_pos, c₂_eq, hc₂⟩ := Smooth1Properties_above suppSmoothingF

  have c₁_lt : c₁ < 1 := by
    rw[c₁_eq]
    exact lt_trans (Real.log_two_lt_d9) (by norm_num)

  have c₂_lt : c₂ < 2 := by
    rw[c₂_eq]
    nth_rewrite 3 [← mul_one 2]
    apply mul_lt_mul'
    · rfl
    · exact lt_trans (Real.log_two_lt_d9) (by norm_num)
    · exact Real.log_nonneg (by norm_num)
    · positivity

  let C : ℝ := 6 * (3 * c₁ + c₂)
  have C_eq : C = 6 * (3 * c₁ + c₂) := rfl

  clear_value C

  have Cpos : 0 < C := by
    rw [C_eq]
    positivity

  refine ⟨C, Cpos, fun X X_ge_C ε εpos ε_lt_one ↦ ?_⟩

  have X_gt_zero : (0 : ℝ) < X := by linarith

  have n_on_X_pos {n : ℕ} (npos : 0 < n) :
      0 < n / X := by
    have : (0 : ℝ) < n := by exact_mod_cast npos
    positivity

  have smooth1BddAbove (n : ℕ) (npos : 0 < n) :
      Smooth1 SmoothingF ε (n / X) ≤ 1 :=
    Smooth1LeOne SmoothingFnonneg mass_one εpos (n_on_X_pos npos)

  have smooth1BddBelow (n : ℕ) (npos : 0 < n) :
      Smooth1 SmoothingF ε (n / X) ≥ 0 :=
    Smooth1Nonneg SmoothingFnonneg (n_on_X_pos npos) εpos

  have smoothIs1 (n : ℕ) (npos : 0 < n) (n_le : n ≤ X * (1 - c₁ * ε)) :
      Smooth1 SmoothingF ε (↑n / X) = 1 := by
    apply hc₁ (ε := ε) (n / X) εpos (n_on_X_pos npos)
    exact (div_le_iff₀' X_gt_zero).mpr n_le

  have smoothIs0 (n : ℕ) (n_le : (1 + c₂ * ε) ≤ n / X) :=
    hc₂ (ε := ε) (n / X) ⟨εpos, ε_lt_one⟩ n_le

  have ε_pos: ε > 0 := by linarith
  have X_pos: X > 0 := by linarith
  have X_gt_three : 3 < X := by linarith

  intro X_bound

  have X_bound_1 : 1 ≤ X * ε * c₁ := by
    rw[c₁_eq, ← div_le_iff₀]
    · have : 1 / Real.log 2 < 2 := by
        nth_rewrite 2 [← one_div_one_div 2]
        rw[one_div_lt_one_div]
        · exact lt_of_le_of_lt (by norm_num) (Real.log_two_gt_d9)
        · exact Real.log_pos (by norm_num)
        norm_num
      exact le_of_lt (gt_trans X_bound this)
    exact Real.log_pos (by norm_num)

  have X_bound_2 : 1 ≤ X * ε * c₂ := by
    rw[c₂_eq, ← div_le_iff₀]
    · have : 1 / (2 * Real.log 2) < 2 := by
        nth_rewrite 3 [← one_div_one_div 2]
        · rw[one_div_lt_one_div, ← one_mul (1 / 2)]
          · apply mul_lt_mul
            · norm_num
            · apply le_of_lt
              exact lt_trans (by norm_num) (Real.log_two_gt_d9)
            repeat norm_num
          · norm_num
            exact Real.log_pos (by norm_num)
          · norm_num
      exact le_of_lt (gt_trans X_bound this)
    norm_num
    exact Real.log_pos (by norm_num)

  rw [SmoothedChebyshevDirichlet diffSmoothingF SmoothingFnonneg suppSmoothingF
    mass_one (by linarith) εpos ε_lt_one]

  convert SmoothedChebyshevClose_aux SmoothingF c₁ c₁_pos c₁_lt c₂ c₂_pos c₂_lt hc₂ C C_eq ε
    ε_pos ε_lt_one X X_pos X_gt_three X_bound_1 X_bound_2 smooth1BddAbove smooth1BddBelow
    smoothIs1 smoothIs0

def LogDerivZetaHasBound (n₁ n₂ : ℝ) (A C : ℝ) : Prop := ∀ (σ : ℝ) (t : ℝ) (_ : 3 < |t|)
    (_ : σ ∈ Ici (1 - A / Real.log |t| ^ n₁)), ‖(deriv riemannZeta) (σ + t * I) / riemannZeta (σ + t * I)‖ ≤
    C * Real.log |t| ^ n₂

noncomputable def I₁ (SmoothingF : ℝ → ℝ) (ε X T : ℝ) : ℂ :=
  (1 / (2 * π * I)) * (I * (∫ t : ℝ in Iic (-T),
      SmoothedChebyshevIntegrand SmoothingF ε X ((1 + (Real.log X)⁻¹) + t * I)))

noncomputable def I₂ (SmoothingF : ℝ → ℝ) (ε T X σ₁ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * ((∫ σ in σ₁..(1 + (Real.log X)⁻¹),
    SmoothedChebyshevIntegrand SmoothingF ε X (σ - T * I)))

noncomputable def I₃₇ (SmoothingF : ℝ → ℝ) (ε T X σ₁ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * (I * (∫ t in (-T)..T,
    SmoothedChebyshevIntegrand SmoothingF ε X (σ₁ + t * I)))

noncomputable def I₈ (SmoothingF : ℝ → ℝ) (ε T X σ₁ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * ((∫ σ in σ₁..(1 + (Real.log X)⁻¹),
    SmoothedChebyshevIntegrand SmoothingF ε X (σ + T * I)))

noncomputable def I₉ (SmoothingF : ℝ → ℝ) (ε X T : ℝ) : ℂ :=
  (1 / (2 * π * I)) * (I * (∫ t : ℝ in Ici T,
      SmoothedChebyshevIntegrand SmoothingF ε X ((1 + (Real.log X)⁻¹) + t * I)))

noncomputable def I₃ (SmoothingF : ℝ → ℝ) (ε T X σ₁ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * (I * (∫ t in (-T)..(-3),
    SmoothedChebyshevIntegrand SmoothingF ε X (σ₁ + t * I)))

noncomputable def I₇ (SmoothingF : ℝ → ℝ) (ε T X σ₁ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * (I * (∫ t in (3 : ℝ)..T,
    SmoothedChebyshevIntegrand SmoothingF ε X (σ₁ + t * I)))

noncomputable def I₄ (SmoothingF : ℝ → ℝ) (ε X σ₁ σ₂ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * ((∫ σ in σ₂..σ₁,
    SmoothedChebyshevIntegrand SmoothingF ε X (σ - 3 * I)))

noncomputable def I₆ (SmoothingF : ℝ → ℝ) (ε X σ₁ σ₂ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * ((∫ σ in σ₂..σ₁,
    SmoothedChebyshevIntegrand SmoothingF ε X (σ + 3 * I)))

noncomputable def I₅ (SmoothingF : ℝ → ℝ) (ε X σ₂ : ℝ) : ℂ :=
  (1 / (2 * π * I)) *
    (I * (∫ t in (-3)..3, SmoothedChebyshevIntegrand SmoothingF ε X (σ₂ + t * I)))

theorem realDiff_of_complexDiff {f : ℂ → ℂ} (s : ℂ) (hf : DifferentiableAt ℂ f s) :
    ContinuousAt (fun (x : ℝ) ↦ f (s.re + x * I)) s.im := by
  apply ContinuousAt.comp _ (by fun_prop)
  convert hf.continuousAt
  simp

def LogDerivZetaIsHoloSmall (σ₂ : ℝ) : Prop :=
    HolomorphicOn (fun (s : ℂ) ↦ (deriv riemannZeta) s / (riemannZeta s))
    (((uIcc σ₂ 2)  ×ℂ (uIcc (-3) 3)) \ {1})

theorem dlog_riemannZeta_bdd_on_vertical_lines_explicit {σ₀ : ℝ} (σ₀_gt : 1 < σ₀) :
  ∀(t : ℝ), ‖(-(deriv riemannZeta) (σ₀ + t * I) / riemannZeta (σ₀ + t * I))‖ ≤ ‖((deriv riemannZeta) σ₀ / riemannZeta σ₀)‖ :=
  fun _ ↦ dlog_riemannZeta_bdd_on_vertical_lines_generalized _ _ _ σ₀_gt <| le_refl _

theorem dlog_riemannZeta_bdd_on_vertical_lines {σ₀ : ℝ} (σ₀_gt : 1 < σ₀) :
    ∃ c > 0, ∀(t : ℝ), ‖(deriv riemannZeta) (σ₀ + t * I) / riemannZeta (σ₀ + t * I)‖ ≤ c := by
  refine ⟨1 + ‖((deriv riemannZeta) σ₀ / riemannZeta σ₀)‖, (by positivity), fun t ↦ ?_⟩
  have := dlog_riemannZeta_bdd_on_vertical_lines_explicit σ₀_gt t
  rw [neg_div, norm_neg] at this
  exact le_trans this (lt_one_add _).le

theorem SmoothedChebyshevPull1_aux_integrable {SmoothingF : ℝ → ℝ} {ε : ℝ} (ε_pos : 0 < ε)
    (ε_lt_one : ε < 1)
    {X : ℝ} (X_gt : 3 < X)
    {σ₀ : ℝ} (σ₀_gt : 1 < σ₀) (σ₀_le_2 : σ₀ ≤ 2)
    (suppSmoothingF : support SmoothingF ⊆ Icc (1 / 2) 2)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ (x : ℝ) in Ioi 0, SmoothingF x / x = 1)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    :
    Integrable (fun (t : ℝ) ↦
      SmoothedChebyshevIntegrand SmoothingF ε X (σ₀ + (t : ℂ) * I)) volume := by
  obtain ⟨C, C_pos, hC⟩ := dlog_riemannZeta_bdd_on_vertical_lines σ₀_gt
  let c : ℝ := C * X ^ σ₀
  have : ∀ t, ‖(fun (t : ℝ) ↦ (- deriv riemannZeta (σ₀ + (t : ℂ) * I)) /
    riemannZeta (σ₀ + (t : ℂ) * I) *
    (X : ℂ) ^ (σ₀ + (t : ℂ) * I)) t‖ ≤ c := by
    intro t
    simp only [Complex.norm_mul, c]
    gcongr
    · convert! hC t using 1
      simp
    · rw [Complex.norm_cpow_eq_rpow_re_of_nonneg]
      · simp
      · linarith
      · simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
          add_zero, ne_eq]
        linarith
  convert (SmoothedChebyshevDirichlet_aux_integrable ContDiffSmoothingF SmoothingFnonneg
    suppSmoothingF mass_one ε_pos ε_lt_one σ₀_gt σ₀_le_2).bdd_mul
      (c := c) ?_ (ae_of_all _ this) using 2
  · unfold SmoothedChebyshevIntegrand
    ring
  · apply Continuous.aestronglyMeasurable
    rw [← continuousOn_univ]
    intro t _
    let s := σ₀ + (t : ℂ) * I
    have s_ne_one : s ≠ 1 := by
      intro h
      
      have : σ₀ = 1 := by
        have := congr_arg Complex.re h
        simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
          sub_self, add_zero, one_re, s] at this
        exact this
      
      linarith [σ₀_gt]
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.mul
    · have diffζ := differentiableAt_riemannZeta s_ne_one
      apply ContinuousAt.div
      · apply ContinuousAt.neg
        have : DifferentiableAt ℂ (fun s ↦ deriv riemannZeta s) s :=
          differentiableAt_deriv_riemannZeta s_ne_one
        convert realDiff_of_complexDiff (s := σ₀ + (t : ℂ) * I) this <;> simp
      · convert realDiff_of_complexDiff (s := σ₀ + (t : ℂ) * I) diffζ <;> simp
      · apply riemannZeta_ne_zero_of_one_lt_re
        simp [σ₀_gt]
    · apply ContinuousAt.comp _ (by fun_prop)
      apply continuousAt_const_cpow
      norm_cast
      linarith

lemma BddAboveOnRect {g : ℂ → ℂ} {z w : ℂ} (holoOn : HolomorphicOn g (z.Rectangle w)) :
    BddAbove (norm ∘ g '' (z.Rectangle w)) := by
  have compact_rect : IsCompact (z.Rectangle w) := by
    apply IsCompact.reProdIm <;> apply isCompact_uIcc
  refine IsCompact.bddAbove_image compact_rect ?_
  apply holoOn.continuousOn.norm

theorem SmoothedChebyshevPull1 {SmoothingF : ℝ → ℝ} {ε : ℝ} (ε_pos : 0 < ε)
    (ε_lt_one : ε < 1)
    (X : ℝ) (X_gt : 3 < X)
    {T : ℝ} (T_pos : 0 < T) {σ₁ : ℝ}
    (σ₁_pos : 0 < σ₁) (σ₁_lt_one : σ₁ < 1)
    (holoOn : HolomorphicOn ((deriv riemannZeta) / riemannZeta) ((Icc σ₁ 2) ×ℂ (Icc (-T) T) \ {1}))
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF) :
    SmoothedChebyshev SmoothingF ε X =
      I₁ SmoothingF ε X T -
      I₂ SmoothingF ε T X σ₁ +
      I₃₇ SmoothingF ε T X σ₁ +
      I₈ SmoothingF ε T X σ₁ +
      I₉ SmoothingF ε X T
      + mellin (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) 1 * X := by
  unfold SmoothedChebyshev
  unfold VerticalIntegral'
  have X_eq_gt_one : 1 < 1 + (Real.log X)⁻¹ := by
    nth_rewrite 1 [← add_zero 1]
    bound
  have X_eq_lt_two : (1 + (Real.log X)⁻¹) < 2 := by
    rw[← one_add_one_eq_two]
    gcongr
    exact inv_lt_one_of_one_lt₀ <| logt_gt_one X_gt.le
  have X_eq_le_two : 1 + (Real.log X)⁻¹ ≤ 2 := X_eq_lt_two.le
  rw [verticalIntegral_split_three (a := -T) (b := T)]
  swap
  · exact SmoothedChebyshevPull1_aux_integrable ε_pos ε_lt_one X_gt X_eq_gt_one
      X_eq_le_two suppSmoothingF SmoothingFnonneg mass_one ContDiffSmoothingF
  · have temp : ↑(1 + (Real.log X)⁻¹) = (1 : ℂ) + ↑(Real.log X)⁻¹ := by simp
    unfold I₁
    simp only [smul_eq_mul, mul_add, temp, sub_eq_add_neg, add_assoc, add_left_cancel_iff]
    unfold I₉
    nth_rewrite 6 [add_comm]
    simp only [← add_assoc]
    rw [add_right_cancel_iff,
        ← add_right_inj (1 / (2 * ↑π * I) *
          -VIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) (1 + (Real.log X)⁻¹) (-T) T),
        ← mul_add, ← sub_eq_neg_add, sub_self, mul_zero]
    unfold VIntegral I₂ I₃₇ I₈
    simp only [smul_eq_mul, temp, ← add_assoc, ← mul_neg, ← mul_add]
    let fTempRR : ℝ → ℝ → ℂ := fun x ↦ fun y ↦
      SmoothedChebyshevIntegrand SmoothingF ε X ((x : ℝ) + (y : ℝ) * I)
    let fTempC : ℂ → ℂ := fun z ↦ fTempRR z.re z.im
    have : ∫ (y : ℝ) in -T..T,
        SmoothedChebyshevIntegrand SmoothingF ε X (1 + ↑(Real.log X)⁻¹ + ↑y * I) =
        ∫ (y : ℝ) in -T..T, fTempRR (1 + (Real.log X)⁻¹) y := by
        unfold fTempRR
        simp only [temp]
    rw[this]
    have : ∫ (σ₀ : ℝ) in σ₁..1 + (Real.log X)⁻¹,
        SmoothedChebyshevIntegrand SmoothingF ε X (↑σ₀ - ↑T * I) =
        ∫ (x : ℝ) in σ₁..1 + (Real.log X)⁻¹, fTempRR x (-T) := by
        unfold fTempRR
        simp only [ofReal_neg, neg_mul, sub_eq_add_neg]
    rw[this]
    have : ∫ (t : ℝ) in -T..T,
        SmoothedChebyshevIntegrand SmoothingF ε X (↑σ₁ + ↑t * I) =
        ∫ (y : ℝ) in -T..T, fTempRR σ₁ y := rfl
    rw[this]
    have : ∫ (σ₀ : ℝ) in σ₁..1 + (Real.log X)⁻¹,
        SmoothedChebyshevIntegrand SmoothingF ε X (↑σ₀ + ↑T * I) =
        ∫ (x : ℝ) in σ₁..1 + (Real.log X)⁻¹, fTempRR x T := rfl
    rw[this]
    have : (((I * -∫ (y : ℝ) in -T..T, fTempRR (1 + (Real.log X)⁻¹) y) +
        -∫ (x : ℝ) in σ₁..1 + (Real.log X)⁻¹, fTempRR x (-T)) +
        I * ∫ (y : ℝ) in -T..T, fTempRR σ₁ y) +
        ∫ (x : ℝ) in σ₁..1 + (Real.log X)⁻¹, fTempRR x T =
        -(2 * ↑π * I) * RectangleIntegral' fTempC (σ₁ - T * I) (1 + ↑(Real.log X)⁻¹ + T * I) := by
        unfold RectangleIntegral' RectangleIntegral HIntegral VIntegral fTempC
        simp only [mul_neg, one_div, mul_inv_rev, inv_I, neg_mul, sub_im, ofReal_im, mul_im,
          ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero, zero_sub, ofReal_neg, add_re,
          neg_re, mul_re, sub_self, neg_zero, add_im, neg_im, zero_add, sub_re, sub_zero,
          ofReal_inv, one_re, inv_re, normSq_ofReal, div_self_mul_self', one_im, inv_im,
          zero_div, ofReal_add, ofReal_one, smul_eq_mul, neg_neg]
        ring_nf
        simp only [I_sq, neg_mul, one_mul, ne_eq, ofReal_eq_zero, pi_ne_zero, not_false_eq_true,
          mul_inv_cancel_right₀, sub_neg_eq_add, I_pow_three]
        ring_nf
    rw[this]
    field_simp
    rw[mul_comm, eq_comm, neg_add_eq_zero]

    have pInRectangleInterior :
        (Rectangle (σ₁ - ↑T * I) (1 + (Real.log X)⁻¹ + T * I) ∈ nhds 1) := by
      refine rectangle_mem_nhds_iff.mpr ?_
      refine mem_reProdIm.mpr ?_
      simp only [sub_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
        sub_zero, ofReal_inv, add_re, one_re, inv_re, normSq_ofReal, div_self_mul_self', add_zero,
        sub_im, mul_im, zero_sub, add_im, one_im, inv_im, neg_zero, zero_div, zero_add]
      constructor
      · unfold uIoo
        rw [min_eq_left (by linarith), max_eq_right (by linarith)]
        exact mem_Ioo.mpr ⟨σ₁_lt_one, (by linarith)⟩
      · unfold uIoo
        rw [min_eq_left (by linarith), max_eq_right (by linarith)]
        exact mem_Ioo.mpr ⟨(by linarith), (by linarith)⟩

    apply ResidueTheoremOnRectangleWithSimplePole'
    · simp; linarith
    · simp; linarith
    · simp only [one_div]
      exact pInRectangleInterior
    · apply DifferentiableOn.mul
      · apply DifferentiableOn.mul
        · simp only [re_add_im]
          have : (fun z ↦ -(deriv riemannZeta) z / riemannZeta z) = -((deriv riemannZeta) / riemannZeta) := by ext; simp; ring
          rw [this]
          apply DifferentiableOn.neg
          apply holoOn.mono
          apply Set.sdiff_subset_sdiff_left
          apply reProdIm_subset_iff'.mpr
          left
          simp only [sub_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
            sub_zero, one_div, ofReal_inv, add_re, one_re, inv_re, normSq_ofReal,
            div_self_mul_self', add_zero, sub_im, mul_im, zero_sub, add_im, one_im, inv_im,
            neg_zero, zero_div, zero_add]
          constructor <;> apply uIcc_subset_Icc <;> constructor <;> linarith
        · intro s hs
          apply DifferentiableAt.differentiableWithinAt
          simp only [re_add_im]
          apply Smooth1MellinDifferentiable ContDiffSmoothingF suppSmoothingF ⟨ε_pos, ε_lt_one⟩
            SmoothingFnonneg mass_one
          have := mem_reProdIm.mp hs.1 |>.1
          simp only [sub_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
            sub_zero, one_div, ofReal_inv, add_re, one_re, inv_re, normSq_ofReal,
            div_self_mul_self', add_zero] at this
          rw [uIcc_of_le (by linarith)] at this
          linarith [this.1]
      · intro s hs
        apply DifferentiableAt.differentiableWithinAt
        simp only [re_add_im]
        apply DifferentiableAt.const_cpow (by fun_prop)
        left
        norm_cast
        linarith
    · let U : Set ℂ := Rectangle (σ₁ - ↑T * I) (1 + (Real.log X)⁻¹ + T * I)
      let f : ℂ → ℂ := fun z ↦ -(deriv riemannZeta) z / riemannZeta z
      let g : ℂ → ℂ := fun z ↦ mellin (fun x ↦ ↑(Smooth1 SmoothingF ε x)) z * ↑X ^ z
      unfold fTempC fTempRR SmoothedChebyshevIntegrand
      simp only [re_add_im]
      have g_holc : HolomorphicOn g U := by
        intro u uInU
        apply DifferentiableAt.differentiableWithinAt
        simp only [g]
        apply DifferentiableAt.mul
        · apply Smooth1MellinDifferentiable ContDiffSmoothingF suppSmoothingF ⟨ε_pos, ε_lt_one⟩
            SmoothingFnonneg mass_one
          simp only [ofReal_inv, U] at uInU
          unfold Rectangle at uInU
          rw[Complex.mem_reProdIm] at uInU
          have := uInU.1
          simp only [sub_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
            sub_zero, add_re, one_re, inv_re, normSq_ofReal, div_self_mul_self', add_zero] at this
          rw [uIcc_of_le (by linarith)] at this
          linarith [this.1]
        · unfold HPow.hPow instHPow
          apply DifferentiableAt.const_cpow differentiableAt_fun_id
          left
          norm_cast
          linarith
      have f_near_p : (f - fun (z : ℂ) => 1 * (z - 1)⁻¹) =O[nhdsWithin 1 {1}ᶜ] (1 : ℂ → ℂ) := by
        simp only [one_mul, f]
        exact riemannZetaLogDerivResidueBigO
      convert ResidueMult g_holc pInRectangleInterior f_near_p using 1
      ext
      simp [f, g]
      ring

lemma interval_membership (r : ℝ) (a b : ℝ) (h1 : r ∈ Set.Icc (min a b) (max a b)) (h2 : a < b) :
    a ≤ r ∧ r ≤ b := by
  
  have min_eq : min a b = a := min_eq_left (le_of_lt h2)
  have max_eq : max a b = b := max_eq_right (le_of_lt h2)
  rw [min_eq, max_eq] at h1
  rw [← @mem_Icc]
  exact h1

lemma verticalIntegral_split_three_finite {s a b e σ : ℝ} {f : ℂ → ℂ}
    (hf : IntegrableOn (fun t : ℝ ↦ f (σ + t * I)) (Icc s e))
    (hab: s < a ∧ a < b ∧ b < e):
    VIntegral f σ s e =
    VIntegral f σ s a +
    VIntegral f σ a b +
    VIntegral f σ b e := by
  dsimp [VIntegral]
  rw [← intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)] at hf
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := a),
    ← intervalIntegral.integral_add_adjacent_intervals (a := a) (b := b)]
  · ring
  all_goals
    apply IntervalIntegrable.mono_set hf
    apply uIcc_subset_uIcc <;> apply mem_uIcc_of_le <;> linarith

lemma verticalIntegral_split_three_finite' {s a b e σ : ℝ} {f : ℂ → ℂ}
    (hf : IntegrableOn (fun t : ℝ ↦ f (σ + t * I)) (Icc s e))
    (hab: s < a ∧ a < b ∧ b < e):
    (1 : ℂ) / (2 * π * I) * (VIntegral f σ s e) =
    (1 : ℂ) / (2 * π * I) * (VIntegral f σ s a) +
    (1 : ℂ) / (2 * π * I) * (VIntegral f σ a b) +
    (1 : ℂ) / (2 * π * I) * (VIntegral f σ b e) := by
  have : (1 : ℂ) / (2 * π * I) * (VIntegral f σ s a) +
      (1 : ℂ) / (2 * π * I) * (VIntegral f σ a b) +
      (1 : ℂ) / (2 * π * I) * (VIntegral f σ b e) =
        (1 : ℂ) / (2 * π * I) * ((VIntegral f σ s a) +
    (VIntegral f σ a b) +
    (VIntegral f σ b e)) := by ring
  rw [this]
  clear this
  rw [← verticalIntegral_split_three_finite hf hab]

theorem SmoothedChebyshevPull2_aux1 {T σ₁ : ℝ} (σ₁lt : σ₁ < 1)
  (holoOn : HolomorphicOn ((deriv riemannZeta) / riemannZeta) (Icc σ₁ 2 ×ℂ Icc (-T) T \ {1})) :
  ContinuousOn (fun (t : ℝ) ↦ -(deriv riemannZeta) (σ₁ + t * I) / riemannZeta (σ₁ + t * I)) (Icc (-T) T) := by
  rw [show (fun (t : ℝ) ↦ -(deriv riemannZeta) (↑σ₁ + ↑t * I) / riemannZeta (↑σ₁ + ↑t * I)) =
      -((deriv riemannZeta) / riemannZeta) ∘ (fun (t : ℝ) ↦ ↑σ₁ + ↑t * I) by ext; simp; ring_nf]
  apply ContinuousOn.neg
  apply holoOn.continuousOn.comp (by fun_prop)
  intro t ht
  simp only [Set.mem_sdiff, mem_singleton_iff]
  constructor
  · apply mem_reProdIm.mpr
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, add_im, mul_im, zero_add, left_mem_Icc, ht, and_true]
    linarith
  · intro h
    replace h := congr_arg re h
    simp at h
    linarith

theorem SmoothedChebyshevPull2 {SmoothingF : ℝ → ℝ} {ε : ℝ} (ε_pos : 0 < ε) (ε_lt_one : ε < 1)
    (X : ℝ) (_ : 3 < X)
    {T : ℝ} (T_pos : 3 < T) {σ₁ σ₂ : ℝ}
    (σ₂_pos : 0 < σ₂) (σ₁_lt_one : σ₁ < 1)
    (σ₂_lt_σ₁ : σ₂ < σ₁)
    (holoOn : HolomorphicOn ((deriv riemannZeta) / riemannZeta) ((Icc σ₁ 2) ×ℂ (Icc (-T) T) \ {1}))
    (holoOn2 : HolomorphicOn (SmoothedChebyshevIntegrand SmoothingF ε X)
      (Icc σ₂ 2 ×ℂ Icc (-3) 3 \ {1}))
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1)
    (diff_SmoothingF : ContDiff ℝ 1 SmoothingF) :
    I₃₇ SmoothingF ε T X σ₁ =
      I₃ SmoothingF ε T X σ₁ -
      I₄ SmoothingF ε X σ₁ σ₂ +
      I₅ SmoothingF ε X σ₂ +
      I₆ SmoothingF ε X σ₁ σ₂ +
      I₇ SmoothingF ε T X σ₁ := by
  let z : ℂ := σ₂ - 3 * I
  let w : ℂ := σ₁ + 3 * I
  have σ₁_pos : 0 < σ₁ := by linarith

  have sub : z.Rectangle w ⊆ Icc σ₂ 2 ×ℂ Icc (-3) 3 \ {1} := by
    
    intro x hx
    constructor
    · 
      simp only [Rectangle, uIcc] at hx
      rw [Complex.mem_reProdIm] at hx ⊢
      obtain ⟨hx_re, hx_im⟩ := hx
      
      have hzw_re : z.re < w.re := by
        simpa [z, w] using σ₂_lt_σ₁
      have x_re_bounds : z.re ≤ x.re ∧ x.re ≤ w.re := by
        exact interval_membership x.re z.re w.re hx_re hzw_re
      have x_re_in_Icc : x.re ∈ Icc σ₂ 2 := by
        have ⟨h_left, h_right⟩ := x_re_bounds
        have h_left' : σ₂ ≤ x.re := by
          simpa [z] using h_left
        have h_right' : x.re ≤ 2 := by
          apply le_trans h_right
          have : w.re ≤ 2 := by
            simp [w]
            linarith
          exact this
        exact ⟨h_left', h_right'⟩
      
      have hzw_im : z.im < w.im := by
        norm_num [z, w]
      have x_im_bounds : z.im ≤ x.im ∧ x.im ≤ w.im := by
        exact interval_membership x.im z.im w.im hx_im hzw_im
      have x_im_in_Icc : x.im ∈ Icc (-3) 3 := by
        have ⟨h_left, h_right⟩ := x_im_bounds
        have h_left' : -3 ≤ x.im := by
          simpa [z] using h_left
        have h_right' : x.im ≤ 3 := by
          simpa [w] using h_right
        exact ⟨h_left', h_right'⟩
      exact ⟨x_re_in_Icc, x_im_in_Icc⟩
    
    · simp only [mem_singleton_iff]
      
      have x_re_upper: x.re ≤ σ₁ := by
        simp only [Rectangle, uIcc] at hx
        rw [Complex.mem_reProdIm] at hx
        obtain ⟨hx_re, _⟩ := hx
        
        have hzw_re : z.re < w.re := by
          simpa [z, w] using σ₂_lt_σ₁
        have x_re_bounds : z.re ≤ x.re ∧ x.re ≤ w.re := by
          exact interval_membership x.re z.re w.re hx_re hzw_re
        have x_re_upper' : x.re ≤ w.re := x_re_bounds.2
        have hw_re : w.re = σ₁ := by simp [w]
        linarith
      
      have h_x_ne_one : x ≠ 1 := by
        intro h_eq
        have h_re : x.re = 1 := by rw [h_eq, Complex.one_re]
        have h1 : 1 ≤ σ₁ := by
          rw [← h_re]
          exact x_re_upper
        linarith
      exact h_x_ne_one
  have zero_over_box := HolomorphicOn.vanishesOnRectangle holoOn2 sub
  have splitting : I₃₇ SmoothingF ε T X σ₁ =
    I₃ SmoothingF ε T X σ₁ + I₅ SmoothingF ε X σ₁ + I₇ SmoothingF ε T X σ₁ := by
    unfold I₃₇ I₃ I₅ I₇
    apply verticalIntegral_split_three_finite'
    · apply ContinuousOn.integrableOn_Icc
      unfold SmoothedChebyshevIntegrand
      apply ContinuousOn.mul
      · apply ContinuousOn.mul
        · apply SmoothedChebyshevPull2_aux1 σ₁_lt_one holoOn
        · apply continuousOn_of_forall_continuousAt
          intro t t_mem
          have := Smooth1MellinDifferentiable diff_SmoothingF suppSmoothingF ⟨ε_pos, ε_lt_one⟩
            SmoothingFnonneg mass_one (s := ↑σ₁ + ↑t * I) (by simpa)
          simpa using realDiff_of_complexDiff _ this
      · apply continuousOn_of_forall_continuousAt
        intro t t_mem
        apply ContinuousAt.comp
        · refine continuousAt_const_cpow' ?_
          intro h
          have : σ₁ = 0 := by
            have h_real : (↑σ₁ + ↑t * I).re = (0 : ℂ).re := by
              rw [h]
            simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
              sub_self, add_zero, zero_re] at h_real
            exact h_real
          linarith
        · 
          apply ContinuousAt.add
          · exact continuousAt_const
          · apply ContinuousAt.mul
            · apply continuous_ofReal.continuousAt
            · exact continuousAt_const
    · refine ⟨by linarith, by linarith, by linarith⟩
  calc I₃₇ SmoothingF ε T X σ₁ =
        I₃₇ SmoothingF ε T X σ₁ - (1 / (2 * π * I)) * (0 : ℂ) := by simp
    _ = I₃₇ SmoothingF ε T X σ₁ - (1 / (2 * π * I)) *
        (RectangleIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z w) := by rw [← zero_over_box]
    _ = I₃₇ SmoothingF ε T X σ₁ - (1 / (2 * π * I)) *
        (HIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z.re w.re z.im
        - HIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z.re w.re w.im
        + VIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) w.re z.im w.im
        - VIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z.re z.im w.im) := by
      simp [RectangleIntegral]
    _ = I₃₇ SmoothingF ε T X σ₁ -
        ((1 / (2 * π * I)) * HIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z.re w.re z.im
        - (1 / (2 * π * I)) * HIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z.re w.re w.im
        + (1 / (2 * π * I)) * VIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) w.re z.im w.im
        - (1 / (2 * π * I)) *
            VIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z.re z.im w.im) := by ring
    _ = I₃₇ SmoothingF ε T X σ₁ - (I₄ SmoothingF ε X σ₁ σ₂
    - (1 / (2 * π * I)) * HIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z.re w.re w.im
    + (1 / (2 * π * I)) * VIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) w.re z.im w.im
    - (1 / (2 * π * I)) * VIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z.re z.im w.im) := by
      simp only [one_div, mul_inv_rev, inv_I, neg_mul, HIntegral, sub_im, ofReal_im, mul_im,
        re_ofNat, I_im, mul_one, im_ofNat, I_re, mul_zero, add_zero, zero_sub, ofReal_neg,
        ofReal_ofNat, sub_re, ofReal_re, mul_re, sub_self, sub_zero, add_re, add_im, zero_add,
        sub_neg_eq_add, I₄, sub_right_inj, add_left_inj, neg_inj, mul_eq_mul_left_iff, mul_eq_zero,
        I_ne_zero, inv_eq_zero, ofReal_eq_zero, OfNat.ofNat_ne_zero, or_false, false_or, z, w]
      left
      rfl
    _ = I₃₇ SmoothingF ε T X σ₁ - (I₄ SmoothingF ε X σ₁ σ₂
    - I₆ SmoothingF ε X σ₁ σ₂
    + (1 / (2 * π * I)) * VIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) w.re z.im w.im
    - (1 / (2 * π * I)) * VIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z.re z.im w.im) := by
      simp only [one_div, mul_inv_rev, inv_I, neg_mul, HIntegral, add_im, ofReal_im, mul_im,
        re_ofNat, I_im, mul_one, im_ofNat, I_re, mul_zero, add_zero, zero_add, ofReal_ofNat, sub_re,
        ofReal_re, mul_re, sub_self, sub_zero, add_re, sub_neg_eq_add, sub_im, zero_sub, I₆, w, z]
    _ = I₃₇ SmoothingF ε T X σ₁ - (I₄ SmoothingF ε X σ₁ σ₂
    - I₆ SmoothingF ε X σ₁ σ₂
    + I₅ SmoothingF ε X σ₁
    - (1 / (2 * π * I)) * VIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z.re z.im w.im) := by
      simp only [one_div, mul_inv_rev, inv_I, neg_mul, VIntegral, add_re, ofReal_re, mul_re,
        re_ofNat, I_re, mul_zero, im_ofNat, I_im, mul_one, sub_self, add_zero, sub_im, ofReal_im,
        mul_im, zero_sub, add_im, zero_add, smul_eq_mul, sub_re, sub_zero, sub_neg_eq_add, I₅,
        w, z]
    _ = I₃₇ SmoothingF ε T X σ₁ - (I₄ SmoothingF ε X σ₁ σ₂
    - I₆ SmoothingF ε X σ₁ σ₂
    + I₅ SmoothingF ε X σ₁
    - I₅ SmoothingF ε X σ₂) := by
      simp only [I₅, one_div, mul_inv_rev, inv_I, neg_mul, VIntegral, sub_re, ofReal_re, mul_re,
        re_ofNat, I_re, mul_zero, im_ofNat, I_im, mul_one, sub_self, sub_zero, sub_im, ofReal_im,
        mul_im, add_zero, zero_sub, add_im, zero_add, smul_eq_mul, sub_neg_eq_add, z, w]
    
    _ = I₃ SmoothingF ε T X σ₁
    + I₅ SmoothingF ε X σ₁
    + I₇ SmoothingF ε T X σ₁
    - (I₄ SmoothingF ε X σ₁ σ₂
    - I₆ SmoothingF ε X σ₁ σ₂
    + I₅ SmoothingF ε X σ₁
    - I₅ SmoothingF ε X σ₂) := by
      rw [splitting]
    _ = I₃ SmoothingF ε T X σ₁
    - I₄ SmoothingF ε X σ₁ σ₂
    + I₅ SmoothingF ε X σ₂
    + I₆ SmoothingF ε X σ₁ σ₂
    + I₇ SmoothingF ε T X σ₁ := by
      ring

theorem ZetaBoxEval {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF) :
    ∃ C, ∀ᶠ ε in (nhdsWithin 0 (Ioi 0)), ∀ X : ℝ, 0 ≤ X →
    ‖mellin (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) 1 * X - X‖ ≤ C * ε * X := by
  have := MellinOfSmooth1c ContDiffSmoothingF suppSmoothingF mass_one
  clear suppSmoothingF mass_one ContDiffSmoothingF
  rw[Asymptotics.isBigO_iff] at this
  obtain ⟨C, hC⟩ := this
  use C
  have εpos : ∀ᶠ (ε : ℝ) in nhdsWithin 0 (Ioi 0), ε > 0 :=
    eventually_mem_of_tendsto_nhdsWithin fun ⦃U⦄ hU ↦ hU
  filter_upwards [hC, εpos] with ε hC εpos
  rw[id_eq, norm_of_nonneg (le_of_lt εpos)] at hC
  intro X Xnne
  nth_rw 2 [← one_mul (X : ℂ)]
  rw[← sub_mul, norm_mul, norm_real, norm_of_nonneg Xnne]
  exact mul_le_mul_of_nonneg_right hC Xnne

theorem poisson_kernel_integrable (x : ℝ) (hx : x ≠ 0) :
  MeasureTheory.Integrable (fun (t : ℝ) ↦ (‖x + t * I‖^2)⁻¹) := by
  
  have h1 : ∀ t : ℝ, ‖x + t * I‖^2 = x^2 + t^2 := by
    intro t
    rw [← normSq_eq_norm_sq, normSq_add_mul_I]
  
  simp_rw [h1]
  apply integrable_comp_mul_left_iff _ hx |>.mp
  have : (fun t ↦ (x ^ 2 + (x * t) ^ 2) ⁻¹) = (fun t ↦ (1 / x ^ 2) * (1 + t ^ 2) ⁻¹) := by
    ext
    field_simp
  rw [this]
  apply integrable_inv_one_add_sq.const_mul

theorem ae_volume_of_contains_compl_singleton_zero
  (s : Set ℝ)
  (h : (univ : Set ℝ) \ {0} ⊆ s) :
  s ∈ (MeasureTheory.ae volume) := by
  
  have h_zero_null : volume ({0} : Set ℝ) = 0 := by
    exact volume_singleton

  have h_compl_subset : sᶜ ⊆ {0} := by
    intro x hx

    by_contra h_not_zero
    have : x ∈ univ \ {0} := ⟨trivial, h_not_zero⟩
    exact hx (h this)

  have h_compl_measure : volume sᶜ ≤ volume ({0} : Set ℝ) :=
    measure_mono h_compl_subset

  have h_compl_zero : volume sᶜ = 0 := by
    rw [h_zero_null] at h_compl_measure
    exact le_antisymm h_compl_measure (by positivity)

  rwa [mem_ae_iff]

theorem integral_evaluation (x : ℝ) (T : ℝ) (T_large : 3 < T) :
    ∫ (t : ℝ) in Iic (-T), (‖x + t * I‖ ^ 2)⁻¹ ≤ T⁻¹ := by
  have T00 : ∀ (x t : ℝ), t^2 ≤ ‖x + t * I‖^2 := by
    intro x t
    rw [Complex.norm_add_mul_I x t]
    ring_nf
    rw [Real.sq_sqrt _]
    · simp only [le_add_iff_nonneg_right]; positivity
    · positivity

  have T0 : ∀ (x t : ℝ), t ≠ 0 → (‖x + t * I‖^2)⁻¹ ≤ (t^2)⁻¹ := by
    intro x t hyp
    have U0 : 0 < t^2 := by positivity
    have U1 : 0 < ‖x + t * I‖^2 := by
      rw [Complex.norm_add_mul_I x t,
        Real.sq_sqrt _]

      · positivity
      · positivity
    rw [inv_le_inv₀ U1 U0]
    exact (T00 x t)

  have T1 : (fun (t : ℝ) ↦ (‖x + t * I‖^2)⁻¹) ≤ᶠ[ae (volume.restrict (Iic (-T)))] (fun (t : ℝ) ↦ (t^2)⁻¹) := by
    unfold Filter.EventuallyLE
    unfold Filter.Eventually
    simp_all only [ne_eq, measurableSet_Iic, ae_restrict_eq]
    refine mem_inf_of_left ?_
    · refine Filter.mem_sets.mp ?_
      · have U :  {x_1 : ℝ | x_1 ≠ 0} ⊆ {x_1 : ℝ | (‖x + x_1 * I‖ ^ 2)⁻¹ ≤ (x_1 ^ 2)⁻¹}  := by
          rw [Set.setOf_subset_setOf]
          intro t hyp_t
          exact T0 x t hyp_t
        have U1 : {x_1 : ℝ | x_1 ≠ 0} = (univ \ {0}) := by
          apply Set.ext
          intro x
          simp_all only [ne_eq, setOf_subset_setOf, not_false_eq_true, implies_true,
            mem_setOf_eq, Set.mem_sdiff, mem_univ, mem_singleton_iff, true_and]

        rw [U1] at U
        exact ae_volume_of_contains_compl_singleton_zero _ U

  have T3 : Integrable (fun (t : ℝ) ↦ (t^2)⁻¹) (volume.restrict (Iic (-T))) := by
    have D3 := integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1)
      (by linarith : 0 < T) |>.comp_neg
    simp only [rpow_neg_ofNat, Int.reduceNeg, zpow_neg, neg_Ioi] at D3
    have D4 :=
      (integrableOn_Iic_iff_integrableOn_Iio'
        (by
          refine EReal.coe_ennreal_ne_coe_ennreal_iff.mp ?_
          simp_all only [ne_eq, measurableSet_Iic, ae_restrict_eq, measure_singleton,
            EReal.coe_ennreal_zero, EReal.coe_ennreal_top, EReal.zero_ne_top, not_false_eq_true])).mpr D3
    simp_all only [ne_eq, measurableSet_Iic, ae_restrict_eq]
    unfold IntegrableOn at D4
    have eq_fun : (fun (x : ℝ) ↦ ((-x)^2)⁻¹) = fun x ↦ (x^2)⁻¹ := by
      funext x
      simp_all only [even_two, Even.neg_pow]
    simp_all only [even_two, Even.neg_pow]
    norm_cast at D4
    simp_all only [even_two, Even.neg_pow]

  calc
    _ ≤ ∫ (t : ℝ) in Iic (-T), (t^2)⁻¹  := by
      apply MeasureTheory.integral_mono_of_nonneg _ T3 T1
      filter_upwards [] with x
      simp
    _ = _ := by
      rw [← integral_comp_neg_Ioi]
      conv => lhs; arg 2; ext x; rw [show ((-x) ^ 2)⁻¹ = x ^ (-2 : ℝ) by simp [zpow_ofNat]]
      rw[integral_Ioi_rpow_of_lt (by norm_num) (by linarith)]
      ring_nf
      rw [rpow_neg_one]

lemma IBound_aux1 (X₀ : ℝ) (X₀pos : X₀ > 0) {k : ℝ} (k_pos : 0 < k) : ∃ C ≥ 1, ∀ X ≥ X₀, Real.log X ^ k ≤ C * X := by
  
  have ⟨M, hM⟩ := Filter.eventually_atTop.mp (isLittleO_log_rpow_rpow_atTop k zero_lt_one).eventuallyLE
  
  let f := fun X ↦ Real.log X ^ k / X
  set I := Icc X₀ M with defI
  have : 0 ∉ I := notMem_Icc_of_lt X₀pos
  have f_cont : ContinuousOn f (Icc X₀ M) := by
    unfold f
    refine ContinuousOn.div₀ (ContinuousOn.rpow (continuousOn_log.mono ?_) continuousOn_const (fun _ _ ↦ Or.inr k_pos)) (continuousOn_id' _) (fun x hx h ↦ ?_)
    · simp only [subset_compl_singleton_iff, ← defI, this, not_false_eq_true]
    · rw [← defI, h] at hx
      exact this hx
  have ⟨C₁, hC₁⟩ := isCompact_Icc.exists_bound_of_continuousOn f_cont
  use max C₁ 1, le_max_right C₁ 1
  intro X hX
  have Xpos : X > 0 := lt_of_lt_of_le X₀pos hX
  by_cases hXM : X ≤ M
  · rw[← div_le_iff₀ Xpos]
    calc
      f X ≤ ‖f X‖ := le_norm_self _
      _ ≤ C₁ := hC₁ X ⟨hX, hXM⟩
      _ ≤ max C₁ 1 := le_max_left C₁ 1
  · calc
      Real.log X ^ k ≤ ‖Real.log X ^ k‖ := le_norm_self _
      _ ≤ ‖X ^ 1‖ := by exact_mod_cast hM X (by linarith[hXM])
      _ = 1 * X := by
        rw[pow_one, one_mul]
        apply norm_of_nonneg
        exact Xpos.le
      _ ≤ max C₁ 1 * X := by
        rw[mul_le_mul_iff_left₀ Xpos]
        exact le_max_right C₁ 1

def I1BoundGenProp (SmoothingF : ℝ → ℝ) : Prop := ∃ C > 0, ∀(ε : ℝ) (_ : 0 < ε)
    (_ : ε < 1)
    (X : ℝ) (_ : 3 < X)
    {T : ℝ} (_ : 3 < T),
    ‖I₁ SmoothingF ε X T‖ ≤ C * X * Real.log X / (ε * T)

theorem I1Bound
    {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2) (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1) :
    I1BoundGenProp SmoothingF := by

  obtain ⟨M, ⟨M_is_pos, M_bounds_mellin_hard⟩⟩ :=
    MellinOfSmooth1b ContDiffSmoothingF suppSmoothingF

  have G0 : ∃K > 0, ∀(t σ : ℝ), 1 < σ → σ < 2 → ‖(deriv riemannZeta) (σ + t * I) / riemannZeta (σ + t * I)‖ ≤ K * (σ - 1)⁻¹ := by
    let ⟨K', ⟨K'_pos, K'_bounds_zeta⟩⟩ := triv_bound_zeta
    use (2 * (K' + 1))
    use (by positivity)
    intro t σ cond cond2

    have T0 : 0 < K' + 1 := by positivity
    have T1 : 1 ≤ (σ - 1)⁻¹ := by
      have U : σ - 1 ≤ 1 := by linarith
      have U1 := (inv_le_inv₀ (by positivity) (by exact sub_pos.mpr cond)).mpr U
      simp_all only [one_div, support_subset_iff, ne_eq, mem_Icc, mul_inv_rev, ge_iff_le, Complex.norm_div,
        norm_neg, tsub_le_iff_right, inv_one]

    have T : (K' + 1) * 1 ≤ (K' + 1) * (σ - 1)⁻¹ :=
      by
        exact (mul_le_mul_iff_right₀ T0).mpr T1
    have U := calc
      ‖(deriv riemannZeta) (σ + t * I) / riemannZeta (σ + t * I)‖ = ‖-(deriv riemannZeta) (σ + t * I) / riemannZeta (σ + t * I)‖ := by
        rw [← norm_neg _, mul_comm, neg_div' _ _]
      _ ≤ (σ - 1)⁻¹ + K' := K'_bounds_zeta σ t cond
      _ ≤ (σ - 1)⁻¹ + (K' + 1) := by aesop
      _ ≤ (K' + 1) * (σ - 1)⁻¹ + (K' + 1) := by aesop
      _ ≤ (K' + 1) * (σ - 1)⁻¹ + (K' + 1) * (σ - 1)⁻¹ := by linarith
      _ = 2 * (K' + 1) * (σ - 1)⁻¹ := by
        ring_nf

    exact U

  obtain ⟨K, ⟨K_is_pos, K_bounds_zeta_at_any_t'⟩⟩ := G0

  have C_final_pos : |π|⁻¹ * 2⁻¹ * (Real.exp 1 * K * M) > 0 := by
    positivity

  use (|π|⁻¹ * 2⁻¹ * (Real.exp 1 * K * M))
  use C_final_pos

  intro eps eps_pos eps_less_one X X_large T T_large

  let pts_re := 1 + (Real.log X)⁻¹
  let pts := fun (t : ℝ) ↦ (pts_re + t * I)

  have pts_re_triv : ∀(t : ℝ), (pts t).re = pts_re := by
    intro t
    unfold pts
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero]

  have pts_re_ge_one : 1 < pts_re := by
    unfold pts_re
    simp only [lt_add_iff_pos_right, inv_pos]
    have U : 1 < X := by linarith
    exact Real.log_pos U

  have pts_re_le_one : pts_re < 2 := by
    unfold pts_re
    have Z : Real.log 3 < Real.log X :=
      by
        refine log_lt_log ?_ X_large
        simp only [Nat.ofNat_pos]

    have Z01 : 1 < Real.log 3 := logt_gt_one le_rfl
    have Zpos0 : 0 < Real.log 3 := by positivity
    have Zpos1 : 0 < Real.log X := by calc
      0 < Real.log 3 := Zpos0
      _ < Real.log X := Z

    have Z1 : (Real.log X)⁻¹ < (Real.log 3)⁻¹ := (inv_lt_inv₀ Zpos1 Zpos0).mpr Z

    have Z02 : (Real.log 3)⁻¹ < 1 := by
      have T01 := (inv_lt_inv₀ ?_ ?_).mpr Z01
      · simp only [inv_one] at T01
        exact T01
      · exact Zpos0
      simp only [zero_lt_one]

    have Z2 : 1 + (Real.log X)⁻¹ < 1 + (Real.log 3)⁻¹ := by
      exact (add_lt_add_iff_left 1).mpr Z1

    have Z3 : 1 + (Real.log 3)⁻¹ < 2 := by
      calc
        1 + (Real.log 3)⁻¹ < 1 + 1 := by linarith
        _ = 2 := by ring_nf

    calc
      1 + (Real.log X)⁻¹ < 1 + (Real.log 3)⁻¹ := Z2
      _ < 2 := Z3

  have inve : (pts_re - 1)⁻¹ = Real.log X := by
    unfold pts_re
    simp_all only [one_div, support_subset_iff, ne_eq, mem_Icc, mul_inv_rev, gt_iff_lt,
      Complex.norm_div, add_sub_cancel_left, inv_inv]

  have K_bounds_zeta_at_any_t :
      ∀(t : ℝ), ‖(deriv riemannZeta) (pts t) / riemannZeta (pts t)‖ ≤ K * Real.log X := by
    intro t
    rw [←inve]
    exact K_bounds_zeta_at_any_t' t pts_re pts_re_ge_one pts_re_le_one

  have pts_re_pos : pts_re > 0 := by
    unfold pts_re
    positivity

  have triv_pts_lo_bound : ∀(t : ℝ), pts_re ≤ (pts t).re := by
    intro t
    unfold pts_re
    exact Eq.ge (pts_re_triv t)

  have triv_pts_up_bound : ∀(t : ℝ), (pts t).re ≤ 2 := by
    intro t
    unfold pts
    refine EReal.coe_le_coe_iff.mp ?_
    · simp_all only [one_div, support_subset_iff, ne_eq, mem_Icc, mul_inv_rev, gt_iff_lt,
      Complex.norm_div, le_refl, implies_true, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im,
      I_im, mul_one, sub_self, add_zero, EReal.coe_le_coe_iff]
      exact le_of_lt pts_re_le_one

  have pts_re_ge_1 : pts_re > 1 := by
    unfold pts_re
    exact pts_re_ge_one

  have X_pos_triv : 0 < X := by positivity

  let f := fun (t : ℝ) ↦ SmoothedChebyshevIntegrand SmoothingF eps X (pts t)

  have G : ∀(t : ℝ), ‖f t‖ ≤ (K * M) * Real.log X * (eps * ‖pts t‖^2)⁻¹ * X^pts_re := by

    intro t

    let M_bounds_mellin_easy := fun (t : ℝ) ↦
      M_bounds_mellin_hard pts_re pts_re_pos (pts t) (triv_pts_lo_bound t) (triv_pts_up_bound t)
        eps eps_pos eps_less_one

    let zeta_part := (fun (t : ℝ) ↦ -(deriv riemannZeta) (pts t) / riemannZeta (pts t))
    let mellin_part := (fun (t : ℝ) ↦ mellin (fun x ↦ (Smooth1 SmoothingF eps x : ℂ)) (pts t))
    let X_part := (fun (t : ℝ) ↦ (↑X : ℂ) ^ (pts t))

    let g := fun (t : ℝ) ↦ (zeta_part t) * (mellin_part t) * (X_part t)

    have X_part_eq : ∀(t : ℝ), ‖X_part t‖ = X^pts_re := by
      intro t
      have U := Complex.norm_cpow_eq_rpow_re_of_pos (X_pos_triv) (pts t)
      rw [pts_re_triv t] at U
      exact U

    have X_part_bound : ∀(t : ℝ), ‖X_part t‖ ≤ X^pts_re := by
      intro t
      rw [←X_part_eq]

    have mellin_bound : ∀(t : ℝ), ‖mellin_part t‖ ≤ M * (eps * ‖pts t‖ ^ 2)⁻¹ := by
      intro t
      exact M_bounds_mellin_easy t

    have X_part_and_mellin_bound :
        ∀(t : ℝ), ‖mellin_part t * X_part t‖ ≤ M * (eps * ‖pts t‖^2)⁻¹ * X^pts_re := by
      intro t
      exact norm_mul_le_of_le (mellin_bound t) (X_part_bound t)

    have T2 : ∀(t : ℝ), ‖zeta_part t‖ = ‖(deriv riemannZeta) (pts t) / riemannZeta (pts t)‖ := by
      intro t
      unfold zeta_part
      simp only [Complex.norm_div, norm_neg]

    have zeta_bound : ∀(t : ℝ), ‖zeta_part t‖ ≤ K * Real.log X := by
      intro t
      unfold zeta_part
      rw [T2]
      exact K_bounds_zeta_at_any_t t

    have g_bound : ∀(t : ℝ), ‖zeta_part t * (mellin_part t * X_part t)‖ ≤
        (K * Real.log X) * (M * (eps * ‖pts t‖^2)⁻¹ * X^pts_re) := by
      intro t
      exact norm_mul_le_of_le (zeta_bound t) (X_part_and_mellin_bound t)

    have T1 : f = g := rfl

    have final_bound_pointwise :
        ‖f t‖ ≤ K * Real.log X * (M * (eps * ‖pts t‖^2)⁻¹ * X^pts_re) := by
      rw [T1]
      unfold g
      rw [mul_assoc]
      exact g_bound t

    have trivialize :
        K * Real.log X * (M * (eps * ‖pts t‖^2)⁻¹ * X^pts_re) =
          (K * M) * Real.log X * (eps * ‖pts t‖^2)⁻¹ * X^pts_re := by ring_nf

    rw [trivialize] at final_bound_pointwise
    exact final_bound_pointwise

  have σ₀_gt : 1 < pts_re := pts_re_ge_1
  have σ₀_le_2 : pts_re ≤ 2 := by
    unfold pts_re
    
    exact
      Preorder.le_trans (1 + (Real.log X)⁻¹) (pts (SmoothingF (SmoothingF M))).re 2
        (triv_pts_lo_bound (SmoothingF (SmoothingF M)))
        (triv_pts_up_bound (SmoothingF (SmoothingF M)))

  have f_integrable := SmoothedChebyshevPull1_aux_integrable eps_pos eps_less_one X_large σ₀_gt
    σ₀_le_2 suppSmoothingF SmoothingFnonneg mass_one ContDiffSmoothingF

  have S : X^pts_re = rexp 1 * X := by
    unfold pts_re

    calc
      X ^ (1 + (Real.log X)⁻¹) = X * X ^ ((Real.log X)⁻¹) := by
        refine rpow_one_add' ?_ ?_
        · positivity
        · exact Ne.symm (ne_of_lt pts_re_pos)
      _ = X * rexp 1 := by
        refine (mul_right_inj' ?_).mpr ?_
        · exact Ne.symm (ne_of_lt X_pos_triv)
        · refine rpow_inv_log X_pos_triv ?_
          · by_contra h
            simp_all only [one_div, support_subset_iff, ne_eq, mem_Icc, mul_inv_rev, gt_iff_lt,
              Complex.norm_div, Nat.not_ofNat_lt_one]
      _ = rexp 1 * X := by ring_nf

  have pts_re_neq_zero : pts_re ≠ 0 := by
    by_contra h
    rw [h] at pts_re_ge_1
    simp only [gt_iff_lt] at pts_re_ge_1
    norm_cast at pts_re_ge_1

  have Z :=
    by
      calc
        ‖∫ (t : ℝ) in Iic (-T), f t‖ ≤ ∫ (t : ℝ) in Iic (-T), ‖f t‖ := MeasureTheory.norm_integral_le_integral_norm f
        _ ≤ ∫ (t : ℝ) in Iic (-T), (K * M) * Real.log X * (eps * ‖pts t‖ ^ 2)⁻¹ * X ^ pts_re := by
            refine integral_mono ?_ ?_ (fun t ↦ G t)
            · refine Integrable.norm ?_
              · unfold f
                exact MeasureTheory.Integrable.restrict f_integrable
            · have equ : ∀(t : ℝ), (K * M) * Real.log X * (eps * ‖pts t‖ ^ 2)⁻¹ * X ^ pts_re = (K * M) * Real.log X * eps⁻¹ * X ^ pts_re * (‖pts t‖^2)⁻¹ := by
                   intro t; ring_nf
              have fun_equ : (fun (t : ℝ) ↦ ((K * M) * Real.log X * (eps * ‖pts t‖ ^ 2)⁻¹ * X ^ pts_re)) = (fun (t : ℝ) ↦ ((K * M) * Real.log X * eps⁻¹ * X ^ pts_re * (‖pts t‖^2)⁻¹)) := by
                   funext t
                   exact equ t

              rw [fun_equ]
              have simple_int : MeasureTheory.Integrable (fun (t : ℝ) ↦ (‖pts t‖^2)⁻¹)
                := by
                   unfold pts
                   exact poisson_kernel_integrable pts_re (pts_re_neq_zero)

              have U := MeasureTheory.Integrable.const_mul simple_int
                ((K * M) * Real.log X * eps⁻¹ * X ^ pts_re)
              refine MeasureTheory.Integrable.restrict ?_
              exact U
        _ = (K * M) * Real.log X * X ^ pts_re * eps⁻¹ *
              ∫ (t : ℝ) in Iic (-T), (‖pts t‖ ^ 2)⁻¹ := by
              have simpli_fun :
                  (fun (t : ℝ) ↦ (K * M) * Real.log X * (eps * ‖pts t‖ ^ 2)⁻¹ * X ^ pts_re) =
                    (fun (t : ℝ) ↦ ((K * M) * Real.log X * X ^ pts_re * eps⁻¹ * (‖pts t‖^2)⁻¹)) :=
                by funext t; ring_nf
              rw [simpli_fun]
              exact MeasureTheory.integral_const_mul ((K * M) * Real.log X * X ^ pts_re * eps⁻¹)
                (fun (t : ℝ) ↦ (‖pts t‖^2)⁻¹)
        _ ≤ (K * M) * Real.log X * X ^ pts_re * eps⁻¹ * T⁻¹ := by
              have U := integral_evaluation (pts_re) T (T_large)
              unfold pts
              simp only [ge_iff_le]
              have U2 : 0 ≤ (K * M) * Real.log X * X ^ pts_re * eps⁻¹ := by
                simp_all only [one_div, support_subset_iff, ne_eq, mem_Icc, mul_inv_rev, gt_iff_lt,
                  Complex.norm_div, le_refl, implies_true, inv_pos, mul_nonneg_iff_of_pos_right]
                refine Left.mul_nonneg ?_ ?_
                · refine Left.mul_nonneg ?_ ?_
                  · exact Left.mul_nonneg (by positivity) (by positivity)
                  · refine log_nonneg ?_
                    · linarith
                · refine Left.mul_nonneg ?_ ?_
                  · exact exp_nonneg 1
                  · exact le_of_lt X_pos_triv
              exact mul_le_mul_of_nonneg_left U U2
        _ = (Real.exp 1 * K * M) * Real.log X * X * eps⁻¹ * T⁻¹ := by
          rw [S]
          ring_nf
        _ = (Real.exp 1 * K * M) * X * Real.log X / (eps * T) := by ring_nf

  unfold I₁
  unfold f at Z
  unfold pts at Z
  have Z3 : (↑pts_re : ℂ) = 1 + (Real.log X)⁻¹ := by unfold pts_re; norm_cast
  rw [Z3] at Z
  rw [Complex.norm_mul (1 / (2 * ↑π * I)) _]
  simp only [one_div, mul_inv_rev, inv_I, neg_mul, norm_neg, Complex.norm_mul, norm_I, norm_inv,
    norm_real, norm_eq_abs, Complex.norm_ofNat, one_mul, ofReal_inv, ge_iff_le]
  have Z2 : 0 ≤ |π|⁻¹ * 2⁻¹ := by positivity
  simp only [ofReal_inv] at Z
  simp only [ge_iff_le]
  have Z4 := mul_le_mul_of_nonneg_left Z Z2
  ring_nf
  ring_nf at Z4
  exact Z4

lemma I9I1 {SmoothingF : ℝ → ℝ} {ε X T : ℝ} (Xpos : 0 < X) :
    I₉ SmoothingF ε X T = conj (I₁ SmoothingF ε X T) := by
  unfold I₉ I₁
  simp only [map_mul, map_div₀, conj_I, conj_ofReal, conj_ofNat, map_one]
  rw [neg_mul, mul_neg, ← neg_mul]
  congr
  · ring
  · rw [← integral_conj, ← integral_comp_neg_Ioi, integral_Ici_eq_integral_Ioi]
    apply setIntegral_congr_fun <| measurableSet_Ioi
    intro t ht
    simp only
    rw[← smoothedChebyshevIntegrand_conj Xpos]
    simp

def I9BoundGenProp (SmoothingF : ℝ → ℝ) : Prop := ∃ C > 0, ∀{ε : ℝ} (_ : 0 < ε)
    (_ : ε < 1)
    (X : ℝ) (_ : 3 < X)
    {T : ℝ} (_ : 3 < T),
    ‖I₉ SmoothingF ε X T‖ ≤ C * X * Real.log X / (ε * T)

theorem I9Bound
    {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2) (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1) :
    I9BoundGenProp SmoothingF := by
  obtain ⟨C, Cpos, bound⟩ := I1Bound suppSmoothingF ContDiffSmoothingF SmoothingFnonneg mass_one
  refine ⟨C, Cpos, ?_⟩
  intro ε εpos ε_lt_one X X_gt T T_gt
  specialize bound ε εpos ε_lt_one X X_gt T_gt
  rwa [I9I1 (by linarith), norm_conj]

lemma one_add_inv_log {X : ℝ} (X_ge : 3 ≤ X) : (1 + (Real.log X)⁻¹) < 2 := by
  rw[← one_add_one_eq_two]
  refine (add_lt_add_iff_left 1).mpr ?_
  refine inv_lt_one_of_one_lt₀ (logt_gt_one X_ge)

def I2BoundGenProp (n : ℝ) (SmoothingF : ℝ → ℝ) (A : ℝ) : Prop := ∃ (C : ℝ) (_ : 0 < C),
    ∀(X : ℝ) (_ : 3 < X) {ε : ℝ} (_ : 0 < ε)
    (_ : ε < 1) {T : ℝ} (_ : 3 < T),
    let σ₁ : ℝ := 1 - A / (Real.log T) ^ n
    ‖I₂ SmoothingF ε T X σ₁‖ ≤ C * X / (ε * T)

lemma I2GenBound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    {n₁ n₂ : ℝ} (n₁_pos : 0 < n₁) (n₂_pos : 0 < n₂) {A C₂ : ℝ} (has_bound : LogDerivZetaHasBound n₁ n₂ A C₂) (C₂pos : 0 < C₂) (A_in : A ∈ Ioc 0 (1 / 2)) :
    I2BoundGenProp n₁ SmoothingF A := by
  have ⟨C₁, C₁pos, Mbd⟩ := MellinOfSmooth1b ContDiffSmoothingF suppSmoothingF
  have := (IBound_aux1 3 (by norm_num) n₂_pos)
  obtain ⟨C₃, ⟨C₃_gt, hC₃⟩⟩ := this

  let C' : ℝ := C₁ * C₂ * C₃ * rexp 1
  have : C' > 0 := by positivity
  use ‖1/(2*π*I)‖ * (2 * C'), by
    refine Right.mul_pos ?_ ?_
    · rw[norm_pos_iff]
      simp[pi_ne_zero]
    · simp[this]
  intro X X_gt ε ε_pos ε_lt_one T T_gt σ₁
  have Xpos : 0 < X := lt_trans (by simp only [Nat.ofNat_pos]) X_gt
  have Tpos : 0 < T := lt_trans (by norm_num) T_gt
  unfold I₂
  rw[norm_mul, mul_assoc (c := X), ← mul_div]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have interval_length_nonneg : σ₁ ≤ 1 + (Real.log X)⁻¹ := by
    dsimp[σ₁]
    rw[sub_le_iff_le_add]
    nth_rw 1 [← add_zero 1]
    rw[add_assoc]
    apply add_le_add_right
    refine Left.add_nonneg ?_ ?_
    · rw[inv_nonneg, log_nonneg_iff Xpos]
      exact le_trans (by norm_num) (le_of_lt X_gt)
    · refine div_nonneg ?_ ?_
      · exact A_in.1.le
      apply Real.rpow_nonneg
      rw[log_nonneg_iff Tpos]
      exact le_trans (by norm_num) (le_of_lt T_gt)
  have σ₁pos : 0 < σ₁ := by
    rw[sub_pos]
    calc
      A / Real.log T ^ n₁ ≤ 1 / 2 / Real.log T ^ n₁ := by
        refine div_le_div_of_nonneg_right (A_in.2) ?_
        apply Real.rpow_nonneg
        rw[log_nonneg_iff Tpos]
        exact le_trans (by norm_num) (le_of_lt T_gt)
      _ ≤ 1 / 2 / 1 := by
        refine div_le_div_of_nonneg_left (by norm_num) (by norm_num) (Real.one_le_rpow ?_ n₁_pos.le)
        rw[Real.le_log_iff_exp_le Tpos]
        linarith [Real.exp_one_lt_d9]
      _ < 1 := by norm_num
  suffices ∀ σ ∈ Ioc σ₁ (1 + (Real.log X)⁻¹),
      ‖SmoothedChebyshevIntegrand SmoothingF ε X (↑σ - ↑T * I)‖ ≤ C' * X / (ε * T) by
    calc
      ‖∫ (σ : ℝ) in σ₁..1 + (Real.log X)⁻¹,
          SmoothedChebyshevIntegrand SmoothingF ε X (↑σ - ↑T * I)‖ ≤
          C' * X / (ε * T) * |1 + (Real.log X)⁻¹ - σ₁| := by
        refine intervalIntegral.norm_integral_le_of_norm_le_const ?_
        convert this using 3
        apply uIoc_of_le
        exact interval_length_nonneg
      _ ≤ C' * X / (ε * T) * 2 := by
        apply mul_le_mul_of_nonneg_left
        · rw[abs_of_nonneg (sub_nonneg.mpr interval_length_nonneg)]
          calc
            1 + (Real.log X)⁻¹ - σ₁ ≤ 1 + (Real.log X)⁻¹ := by linarith
            _ ≤ 2 := (one_add_inv_log X_gt.le).le
        positivity
      _ = 2 * C' * X / (ε * T) := by ring
  intro σ hσ
  unfold SmoothedChebyshevIntegrand
  have log_deriv_zeta_bound : ‖(deriv riemannZeta) (σ - T * I) / riemannZeta (σ - T * I)‖ ≤ C₂ * (C₃ * T) := by
    calc
      ‖(deriv riemannZeta) (σ - (T : ℝ) * I) / riemannZeta (σ - (T : ℝ) * I)‖ = ‖(deriv riemannZeta) (σ + (-T : ℝ) * I) / riemannZeta (σ + (-T : ℝ) * I)‖ := by
        have Z : σ - (T : ℝ) * I = σ + (- T : ℝ) * I := by simp; ring_nf
        simp [Z]
      _ ≤ C₂ * Real.log |-T| ^ n₂ := has_bound σ (-T)
          (by simp only [abs_neg]; rw [abs_of_pos Tpos]; exact T_gt)
          (by unfold σ₁ at hσ; simp only [mem_Ioc, abs_neg, log_abs, mem_Ici,
            tsub_le_iff_right] at hσ ⊢; replace hσ := hσ.1; linarith)
      _ ≤ C₂ * Real.log T ^ n₂ := by simp
      _ ≤ C₂ * (C₃ * T) := by gcongr; exact hC₃ T (by linarith)

  calc
    ‖-(deriv riemannZeta) (σ - T * I) / riemannZeta (σ - T * I) * mellin (fun x ↦ (Smooth1 SmoothingF ε x : ℂ))
        (σ - T * I) * X ^ (σ - T * I)‖ =
        ‖-(deriv riemannZeta) (σ - T * I) / riemannZeta (σ - T * I)‖ * ‖mellin (fun x ↦ (Smooth1 SmoothingF ε x : ℂ))
        (σ - T * I)‖ * ‖(X : ℂ) ^ (σ - T * I)‖ := by
      repeat rw[norm_mul]
    _ ≤ C₂ * (C₃ * T) * (C₁ * (ε * ‖σ - T * I‖ ^ 2)⁻¹) * (rexp 1 * X) := by
      apply mul_le_mul₃
      · rw[neg_div, norm_neg]
        exact log_deriv_zeta_bound
      · refine Mbd σ₁ σ₁pos _ ?_ ?_ ε ε_pos ε_lt_one
        · simp only [mem_Ioc, sub_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
            sub_self, sub_zero, σ₁] at hσ ⊢
          linarith
        · simp only [mem_Ioc, sub_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
            sub_self, sub_zero, σ₁] at hσ ⊢
          linarith[one_add_inv_log X_gt.le]
      · rw[cpow_def_of_ne_zero]
        · rw[norm_exp,← ofReal_log, re_ofReal_mul]
          · simp only [sub_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
              sub_zero]
            rw [← le_log_iff_exp_le, Real.log_mul (exp_ne_zero 1), Real.log_exp, ← le_div_iff₀', add_comm, add_div, div_self, one_div]
            · exact hσ.2
            · refine (Real.log_pos ?_).ne.symm
              linarith
            · apply Real.log_pos
              linarith
            · linarith
            · positivity
          · positivity
        · exact_mod_cast Xpos.ne.symm
      · positivity
      · positivity
      · positivity
    _ = (C' * X * T) / (ε * ‖σ - T * I‖ ^ 2) := by ring
    _ ≤ C' * X / (ε * T) := by
      have : ‖σ - T * I‖ ^ 2 ≥ T ^ 2 := by
        calc
          ‖σ - T * I‖ ^ 2 = ‖σ + (-T : ℝ) * I‖ ^ 2 := by
            congr 2
            push_cast
            ring
          _ = normSq (σ + (-T : ℝ) * I) := (normSq_eq_norm_sq _).symm
          _ = σ^2 + (-T)^2 := by
            rw[Complex.normSq_add_mul_I]
          _ ≥ T^2 := by
            rw[neg_sq]
            exact le_add_of_nonneg_left (sq_nonneg _)
      calc
        C' * X * T / (ε * ‖↑σ - ↑T * I‖ ^ 2) ≤ C' * X * T / (ε * T ^ 2) := by
          rw[div_le_div_iff_of_pos_left, mul_le_mul_iff_right₀]
          · exact this
          · exact ε_pos
          · positivity
          · apply mul_pos ε_pos
            exact lt_of_lt_of_le (pow_pos Tpos 2) this
          · positivity
        _ = C' * X / (ε * T) := by
          field_simp

lemma I8I2 {SmoothingF : ℝ → ℝ}
    {X ε T σ₁ : ℝ} (T_gt : 3 < T) :
    I₈ SmoothingF ε X T σ₁ = -conj (I₂ SmoothingF ε X T σ₁) := by
  unfold I₂ I₈
  rw[map_mul, ← neg_mul]
  congr
  · simp[conj_ofNat]
  · rw[← intervalIntegral_conj]
    apply intervalIntegral.integral_congr
    intro σ hσ
    simp only []
    rw[← smoothedChebyshevIntegrand_conj]
    · simp only [map_sub, conj_ofReal, map_mul, conj_I, mul_neg, sub_neg_eq_add]
    · exact lt_trans (by norm_num) T_gt

def I8BoundGenProp (n : ℝ) (SmoothingF : ℝ → ℝ) (A : ℝ) : Prop := ∃ (C : ℝ) (_ : 0 < C),
    ∀(X : ℝ) (_ : 3 < X) {ε : ℝ} (_: 0 < ε)
    (_ : ε < 1)
    {T : ℝ} (_ : 3 < T),
    let σ₁ : ℝ := 1 - A / (Real.log T) ^ n
    ‖I₈ SmoothingF ε T X σ₁‖ ≤ C * X / (ε * T)

lemma I8GenBound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    {n₁ n₂ : ℝ} (n₁_pos : 0 < n₁) (n₂_pos : 0 < n₂) {A C₂ : ℝ} (has_bound : LogDerivZetaHasBound n₁ n₂ A C₂) (C₂_pos : 0 < C₂) (A_in : A ∈ Ioc 0 (1 / 2)) :
    I8BoundGenProp n₁ SmoothingF A := by
  obtain ⟨C, hC, i2Bound⟩ := I2GenBound suppSmoothingF ContDiffSmoothingF n₁_pos n₂_pos has_bound C₂_pos A_in
  use C, hC
  intro X hX ε hε0 hε1 T hT σ₁
  let i2Bound := i2Bound X hX hε0 hε1 hT
  rw[I8I2 hX, norm_neg, norm_conj]
  exact i2Bound

lemma Real.log_le_const_mul_rpow {c x : ℝ} (hc : 0 < c) (hx : 0 < x) :
    Real.log x ≤ c * x ^ (1 / c) := by
  have h := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hx (1 / c)); rw [Real.log_rpow hx] at h
  have h' := mul_le_mul_of_nonneg_left h hc.le; field_simp at h'
  nlinarith [Real.rpow_pos_of_pos hx (1 / c)]

lemma log_pow_over_xsq_integral_bounded :
  ∀ n : ℝ, (n_pos : 0 < n) →
    ∃ C : ℝ, 0 < C ∧ ∀ T > 3, ∫ x in Ioo 3 T, (Real.log x) ^ n / x ^ 2 < C := by
  intro n n_pos
  set c : ℝ := 2 * n with cDef
  have cpos : 0 < c := by linarith
  set g : ℝ → ℝ := fun x => c ^ n * x ^ (-(3 / 2) : ℝ) with gDef
  have g_nonneg : ∀ x ∈ Ioi (3 : ℝ), 0 ≤ g x := by
    intro x hx; simp only [mem_Ioi] at hx
    exact mul_nonneg (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg (by linarith) _)
  have gInt_nonneg : 0 ≤ ∫ x in Ioi (3 : ℝ), g x := setIntegral_nonneg measurableSet_Ioi g_nonneg
  have g_integrable : IntegrableOn g (Ioi 3) :=
    Integrable.const_mul (integrableOn_Ioi_rpow_of_lt (by linarith) (by linarith)) _
  have g_mono : ∀ x ∈ Ioi (3 : ℝ), Real.log x ^ n / x ^ 2 ≤ g x := by
    intro x hx; simp only [mem_Ioi] at hx
    have xpos : 0 < x := by linarith
    have logxPos : 0 < Real.log x := by
      rw [Real.log_pos_iff xpos.le]
      linarith
    have logBnd := Real.rpow_le_rpow logxPos.le (Real.log_le_const_mul_rpow cpos xpos) n_pos.le
    rw [Real.mul_rpow cpos.le (Real.rpow_nonneg xpos.le _), ← Real.rpow_mul xpos.le, cDef] at logBnd
    field_simp at logBnd
    have : - ((3 : ℝ) / 2) = (1 / 2) - 2 := by norm_num
    simp only [cDef, gDef, this, Real.rpow_sub xpos, ← mul_div_assoc, rpow_ofNat]
    exact (div_le_div_iff_of_pos_right (sq_pos_iff.mpr (ne_of_gt xpos))).mpr logBnd
  refine ⟨1 + (∫ x in Ioi (3 : ℝ), g x), by linarith, fun T _ => ?_⟩
  calc
    _ ≤ ∫ (x : ℝ) in Ioo 3 T, g x := by
      refine setIntegral_mono_on (IntegrableOn.mono_set (ContinuousOn.integrableOn_Icc
        (ContinuousOn.div (ContinuousOn.rpow_const (ContinuousOn.log (continuousOn_id' _)
        (fun x hx ↦ ?_)) ?_) (ContinuousOn.fun_pow (continuousOn_id' _) _)
        (fun x hx ↦ pow_ne_zero _ ?_))) Ioo_subset_Icc_self)
        (IntegrableOn.mono_set g_integrable Ioo_subset_Ioi_self) measurableSet_Ioo
        (fun x hx ↦ g_mono x hx.1)
      · linarith [hx.1]
      · simp only [mem_Icc, ne_eq, log_eq_zero, not_or, n_pos.le, or_true, implies_true]
      · linarith [hx.1]
    _ ≤ ∫ (x : ℝ) in Ioi 3, g x := by
      refine setIntegral_mono_set g_integrable ?_ (LE.le.eventuallyLE Ioo_subset_Ioi_self)
      exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun x hx ↦ g_nonneg x hx)
  linarith

def I3BoundGenProp (n : ℝ) (SmoothingF : ℝ → ℝ) (A : ℝ) : Prop := ∃ (C : ℝ) (_ : 0 < C),
    ∀ (X : ℝ) (_ : 3 < X)
      {ε : ℝ} (_ : 0 < ε) (_ : ε < 1)
      {T : ℝ} (_ : 3 < T),
      let σ₁ : ℝ := 1 - A / (Real.log T) ^ n
      ‖I₃ SmoothingF ε T X σ₁‖ ≤ C * X * X ^ (- A / (Real.log T ^ n)) / ε

set_option maxHeartbeats 400000 in

theorem I3GenBound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    {n₁ n₂ : ℝ} (n₁_pos : 0 < n₁) (n₂_pos : 0 < n₂) {A Cζ : ℝ} (hCζ : LogDerivZetaHasBound n₁ n₂ A Cζ) (Cζpos : 0 < Cζ) (hA : A ∈ Ioc 0 (1 / 2)) :
    I3BoundGenProp n₁ SmoothingF A := by
  obtain ⟨CM, CMpos, CMhyp⟩ := MellinOfSmooth1b ContDiffSmoothingF suppSmoothingF
  obtain ⟨Cint, Cintpos, Cinthyp⟩ := log_pow_over_xsq_integral_bounded n₂ n₂_pos
  use Cint * CM * Cζ
  have : Cint * CM > 0 := mul_pos Cintpos CMpos
  have : Cint * CM * Cζ > 0 := mul_pos this Cζpos
  use this
  intro X Xgt3 ε εgt0 εlt1 T Tgt3 σ₁
  unfold I₃
  unfold SmoothedChebyshevIntegrand

  have Xpos := zero_lt_three.trans Xgt3
  have Tgt3' : -T < -3 := neg_lt_neg_iff.mpr Tgt3

  have t_bounds : ∀ t ∈ Ioo (-T) (-3), 3 < |t| ∧ |t| < T := by
    intro t ht
    have : |t| = -t := by
      refine abs_of_neg ?_
      exact ht.2.trans (by norm_num)
    rw [← Set.neg_mem_Ioo_iff, mem_Ioo] at ht
    rwa [this]

  have logt2gt1_bounds :
      ∀ t, t ∈ Set.Icc (-T) (-3) → Real.log |t| ^ n₂ > 1 := by
    intro t ht
    refine Real.one_lt_rpow ?_ n₂_pos
    have : |t| = -t := by
        refine abs_of_neg ?_
        exact ht.2.trans_lt (by norm_num)
    rw [this, Real.lt_log_iff_exp_lt (by linarith [ht.2])]
    linarith [ht.2, Real.exp_one_lt_d9]

  have Aoverlogt2gtAoverlogT2_bounds : ∀ t, 3 < |t| ∧ |t| < T →
        A / Real.log |t| ^ n₁ > A / Real.log T ^ n₁ := by
    intro t ht
    refine div_lt_div_of_pos_left hA.1 ?_ ?_
    · exact zero_lt_one.trans <| Real.one_lt_rpow (logt_gt_one ht.1.le) n₁_pos
    · have h1 := log_lt_log (zero_lt_three.trans ht.1) ht.2
      have h2 := logt_gt_one ht.1.le
      have h3 : 0 ≤ Real.log |t| := zero_le_one.trans h2.le
      apply Real.rpow_lt_rpow h3 h1 n₁_pos

  have AoverlogT1in0half: A / Real.log T ^ n₁ ∈ Ioo 0 (1/2) := by
    have logT1gt1 : 1 < Real.log T ^ n₁ := by
      have logt_gt_one : 1 < Real.log T := logt_gt_one Tgt3.le
      exact Real.one_lt_rpow logt_gt_one n₁_pos
    have logT9pos := zero_lt_one.trans logT1gt1
    constructor
    · exact div_pos hA.1 logT9pos
    · rw [div_lt_comm₀ logT9pos one_half_pos, div_lt_iff₀' one_half_pos]
      apply hA.2.trans_lt
      rwa [lt_mul_iff_one_lt_right one_half_pos]

  have σ₁lt1 : σ₁ < 1 := by
    unfold σ₁
    linarith[AoverlogT1in0half.1]

  have σ₁pos : 0 < σ₁ := by
    unfold σ₁
    linarith[AoverlogT1in0half.2]

  have quotient_bound :
      ∀ t ∈ Ioo (-T) (-3), Real.log |t| ^ n₂ / (σ₁ ^ 2 + t ^ 2) ≤ Real.log |t| ^ n₂ / t ^ 2 := by
    intro t ht
    have loght := logt2gt1_bounds t (Ioo_subset_Icc_self ht)
    have logpos : Real.log |t| ^ n₂ > 0 := zero_lt_one.trans loght
    have denom_le : t ^ 2 ≤ σ₁ ^ 2 + t ^ 2 := (le_add_iff_nonneg_left _).mpr <| sq_nonneg σ₁
    have denom_pos : 0 < t ^ 2 := by
      apply sq_pos_of_ne_zero
      rintro rfl
      norm_num [mem_Ioo] at ht
    have denom2_pos : 0 < σ₁ ^ 2 + t ^ 2 := add_pos_of_nonneg_of_pos (sq_nonneg _) denom_pos
    exact (div_le_div_iff_of_pos_left logpos denom2_pos denom_pos).mpr denom_le

  have MellinBound : ∀ (t : ℝ),
      ‖mellin (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (σ₁ + t * I)‖ ≤
        CM * (ε * ‖(σ₁ + t * I)‖ ^ 2)⁻¹ := by
    intro t
    refine CMhyp σ₁ σ₁pos _ ?_ ?_ _ εgt0 εlt1 <;> simp [σ₁lt1.le.trans one_le_two]

  have logzetabnd : ∀ t : ℝ, 3 < |t| ∧ |t| < T → ‖(deriv riemannZeta) (↑σ₁ + ↑t * I) / riemannZeta (↑σ₁ + ↑t * I)‖ ≤ Cζ * Real.log (|t| : ℝ) ^ n₂ := by
    intro t tbounds
    apply hCζ
    · exact tbounds.1
    · unfold σ₁
      rw [mem_Ici, sub_le_sub_iff_left]
      exact (Aoverlogt2gtAoverlogT2_bounds t tbounds).le

  let f t := (-(deriv riemannZeta) (↑σ₁ + ↑t * I) / riemannZeta (↑σ₁ + ↑t * I)) *
        mellin (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₁ + ↑t * I) *
        ↑X ^ (↑σ₁ + ↑t * I)

  let g t := Cζ * CM * Real.log |t| ^ n₂ / (ε * ‖↑σ₁ + ↑t * I‖ ^ 2) * X ^ σ₁

  have bound_integral : ∀ t ∈ Ioo (-T) (-3), ‖f t‖ ≤ g t := by
    intro t ht
    unfold f

    have : ‖(-(deriv riemannZeta) (↑σ₁ + ↑t * I) / riemannZeta (↑σ₁ + ↑t * I)) *
            mellin (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑σ₁ + ↑t * I) *
            ↑X ^ (↑σ₁ + ↑t * I)‖ ≤ ‖(deriv riemannZeta) (↑σ₁ + ↑t * I) / riemannZeta (↑σ₁ + ↑t * I)‖ *
            ‖mellin (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑σ₁ + ↑t * I)‖ *
            ‖(↑(X : ℝ) : ℂ) ^ (↑σ₁ + ↑t * I)‖ := by
      simp [norm_neg]

    have : ‖(deriv riemannZeta) (↑σ₁ + ↑t * I) / riemannZeta (↑σ₁ + ↑t * I)‖ *
            ‖mellin (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑σ₁ + ↑t * I)‖ *
            ‖(↑X : ℂ) ^ (↑σ₁ + ↑t * I)‖ ≤ (Cζ * Real.log |t| ^ n₂) *
            (CM * (ε * ‖↑σ₁ + ↑t * I‖ ^ 2)⁻¹) * X ^ σ₁:= by
      have Xσ_bound : ‖↑(X : ℂ) ^ (↑σ₁ + ↑t * I)‖ = X ^ σ₁ := by
        simp [norm_cpow_eq_rpow_re_of_pos Xpos]
      obtain ⟨ht_gt3, ht_ltT⟩ := t_bounds _ ht
      have logtgt1 : 1 < Real.log |t| := logt_gt_one ht_gt3.le
      have hζ := logzetabnd t ⟨ht_gt3, ht_ltT⟩
      have h𝓜 := MellinBound t
      rw[Xσ_bound]
      gcongr

    have : (Cζ * Real.log |t| ^ n₂) * (CM * (ε * ‖↑σ₁ + ↑t * I‖ ^ 2)⁻¹) * X ^ σ₁ = g t := by
      unfold g
      ring_nf
    linarith

  have int_with_f :
      ∫ (t : ℝ) in (-T)..(-3),
        -(deriv riemannZeta) (↑σ₁ + ↑t * I) / riemannZeta (↑σ₁ + ↑t * I) *
          mellin (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₁ + ↑t * I) *
          ↑X ^ (↑σ₁ + ↑t * I) =
      ∫ (t : ℝ) in (-T)..(-3), f t := by
    simp only [f]
  rw[int_with_f]

  apply (norm_mul_le _ _).trans
  rw [Complex.norm_mul, Complex.norm_I, one_mul]

  have : ‖1 / (2 * ↑π * I)‖ * ‖∫ (t : ℝ) in (-T)..(-3), f ↑t‖ ≤ ‖∫ (t : ℝ) in (-T)..(-3), f ↑t‖ := by
    apply mul_le_of_le_one_left
    · apply norm_nonneg
    · simp only [one_div, norm_inv]
      apply inv_le_one_of_one_le₀
      simp only [Complex.norm_mul, Complex.norm_ofNat, norm_real, norm_eq_abs, pi_nonneg,
        abs_of_nonneg, norm_I, mul_one]
      apply one_le_mul_of_one_le_of_one_le one_le_two
      exact le_trans (by norm_num) pi_gt_three.le
  apply le_trans this

  apply le_trans (intervalIntegral.norm_integral_le_integral_norm Tgt3'.le)

  have ne_zero_of_mem_uIcc (x) (hx : x ∈ uIcc (-T) (-3)) : x ≠ 0 := by
    rintro rfl
    norm_num [mem_uIcc] at hx
    linarith

  have cont1 : ContinuousOn (fun t ↦ Real.log |t| ^ n₂) (uIcc (-T) (-3)) := by
    exact ContinuousOn.rpow (ContinuousOn.log continuous_abs.continuousOn (fun x hx ↦ abs_ne_zero.mpr (ne_zero_of_mem_uIcc x hx))) continuousOn_const (fun _ _ ↦ Or.inr n₂_pos)

  have g_cont : ContinuousOn g (uIcc (-T) (-3)) := by
    unfold g
    refine .mul ?_ continuousOn_const
    refine ContinuousOn.div ?_ ?_ ?_
    · exact continuousOn_const.mul cont1
    · fun_prop
    · intro x hx
      apply mul_ne_zero εgt0.ne'
      have : 0 < σ₁ ^ 2 + x ^ 2 := add_pos_of_pos_of_nonneg (sq_pos_of_pos σ₁pos) (sq_nonneg x)
      simp only [Complex.sq_norm, normSq_add_mul_I, ne_eq, this.ne', not_false_eq_true]

  have int_normf_le_int_g: ∫ (t : ℝ) in (-T)..(-3), ‖f ↑t‖
                        ≤ ∫ (t : ℝ) in (-T)..(-3), g ↑t := by
    by_cases h_int : IntervalIntegrable (fun t : ℝ ↦ ‖f t‖) volume (-T) (-3)
    · exact intervalIntegral.integral_mono_on_of_le_Ioo
        Tgt3'.le h_int g_cont.intervalIntegrable bound_integral
    · rw [intervalIntegral.integral_undef h_int]
      apply intervalIntegral.integral_nonneg Tgt3'.le
      intro t ht
      unfold g
      have := logt2gt1_bounds t ht
      positivity

  apply le_trans int_normf_le_int_g
  unfold g

  simp only [σ₁]

  have : X ^ (1 - A / Real.log T ^ n₁) = X * X ^ (- A / Real.log T ^ n₁) := by
    rw [sub_eq_add_neg, Real.rpow_add Xpos, Real.rpow_one, neg_div]

  rw[this]

  have Bound_of_log_int: ∫ (t : ℝ) in (-T)..(-3), Real.log |t| ^ n₂ / (ε * ‖↑σ₁ + ↑t * I‖ ^ 2) ≤ Cint / ε := by
    have : ∫ (t : ℝ) in (-T)..(-3), Real.log |t| ^ n₂ / (ε * ‖↑σ₁ + ↑t * I‖ ^ 2)
        = (1 / ε) * ∫ t in (-T)..(-3), Real.log |t| ^ n₂ / ‖↑σ₁ + ↑t * I‖ ^ 2 := by
      rw [← intervalIntegral.integral_const_mul]
      congr with t
      field_simp [εgt0]
    rw[this]

    have bound : ∫ t in (-T)..(-3), Real.log |t| ^ n₂ / ‖↑σ₁ + ↑t * I‖ ^ 2 ≤ Cint := by
      simp_rw [Complex.sq_norm, normSq_add_mul_I]

      have : ∫ t in (-T)..(-3), Real.log |t| ^ n₂ / (σ₁ ^ 2 + t ^ 2)
            ≤ ∫ t in (-T)..(-3), Real.log |t| ^ n₂ /  t ^ 2 := by
        refine intervalIntegral.integral_mono_on_of_le_Ioo Tgt3'.le ?_ ?_ ?_
        · have cont : ContinuousOn (fun t ↦ Real.log |t| ^ n₂ / (σ₁ ^ 2 + t ^ 2)) (Set.uIcc (-T) (-3)) := by
            refine ContinuousOn.div cont1 ?_ ?_
            · refine ContinuousOn.add ?_ ?_
              · exact continuousOn_const
              · refine ContinuousOn.pow ?_ 2
                exact continuousOn_id' _
            · intro t ht
              have h1 : 0 < t ^ 2 := pow_two_pos_of_ne_zero (ne_zero_of_mem_uIcc t ht)
              have h2 : 0 < σ₁ ^ 2 := sq_pos_of_pos σ₁pos
              exact (add_pos_of_pos_of_nonneg h2 h1.le).ne'
          apply cont.intervalIntegrable
        · have cont : ContinuousOn (fun t ↦ Real.log |t| ^ n₂ / t ^ 2) (Set.uIcc (-T) (-3)) := by
            refine ContinuousOn.div cont1 ?_ ?_
            · refine ContinuousOn.pow ?_ 2
              exact continuousOn_id' _
            · intro t ht
              exact pow_ne_zero 2 (ne_zero_of_mem_uIcc t ht)
          apply cont.intervalIntegrable
        · intro x hx
          exact quotient_bound x hx
      apply le_trans this
      rw [← intervalIntegral.integral_comp_neg]
      simp only [abs_neg, log_abs, even_two, Even.neg_pow]
      rw [intervalIntegral.integral_of_le Tgt3.le, MeasureTheory.integral_Ioc_eq_integral_Ioo]
      exact (Cinthyp T Tgt3).le
    rw [mul_comm,
      ← mul_div_assoc, mul_one]

    exact (div_le_div_iff_of_pos_right εgt0).mpr bound

  have factor_out_constants :
  ∫ (t : ℝ) in (-T)..(-3), Cζ * CM * Real.log |t| ^ n₂ / (ε * ‖↑σ₁ + ↑t * I‖ ^ 2) * (X * X ^ (-A / Real.log T ^ n₁))
  = Cζ * CM * (X * X ^ (-A / Real.log T ^ n₁)) * ∫ (t : ℝ) in (-T)..(-3), Real.log |t| ^ n₂ / (ε * ‖↑σ₁ + ↑t * I‖ ^ 2) := by
     rw [mul_assoc, ← mul_assoc (Cζ * CM), ← mul_assoc]
     field_simp
     simp only [log_abs]
     rw [← intervalIntegral.integral_const_mul]
     apply intervalIntegral.integral_congr
     intro t ht
     ring_nf

  rw [factor_out_constants]

  have : Cζ * CM * (X * X ^ (-A / Real.log T ^ n₁)) * ∫ (t : ℝ) in (-T)..(-3), Real.log |t| ^ n₂ / (ε * ‖↑σ₁ + ↑t * I‖ ^ 2)
        ≤ Cζ * CM * ((X : ℝ) * X ^ (-A / Real.log T ^ n₁)) * (Cint / ε) := by
    apply mul_le_mul_of_nonneg_left
    · exact Bound_of_log_int
    · positivity

  apply le_trans this
  ring_nf
  field_simp
  rfl

lemma I7I3 {SmoothingF : ℝ → ℝ} {ε X T σ₁ : ℝ} (Xpos : 0 < X) :
    I₇ SmoothingF ε T X σ₁ = conj (I₃ SmoothingF ε T X σ₁) := by
  unfold I₃ I₇
  simp only [map_mul, map_div₀, conj_I, conj_ofReal, conj_ofNat, map_one]
  rw [neg_mul, mul_neg, ← neg_mul]
  congr
  · ring
  · rw [← intervalIntegral_conj, ← intervalIntegral.integral_comp_neg]
    apply intervalIntegral.integral_congr
    intro t ht
    simp only
    rw [← smoothedChebyshevIntegrand_conj Xpos]
    simp

def I7BoundGenProp (n : ℝ) (SmoothingF : ℝ → ℝ) (A : ℝ) : Prop := ∃ (C : ℝ) (_ : 0 < C),
    ∀ (X : ℝ) (_ : 3 < X)
      {ε : ℝ} (_ : 0 < ε) (_ : ε < 1)
      {T : ℝ} (_ : 3 < T),
      let σ₁ : ℝ := 1 - A / (Real.log T) ^ n
      ‖I₇ SmoothingF ε T X σ₁‖ ≤ C * X * X ^ (- A / (Real.log T ^ n)) / ε

theorem I7GenBound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    {n₁ n₂ : ℝ} (n₁_pos : 0 < n₁) (n₂_pos : 0 < n₂) {A Cζ : ℝ} (hCζ : LogDerivZetaHasBound n₁ n₂ A Cζ) (Cζpos : 0 < Cζ) (hA : A ∈ Ioc 0 (1 / 2)) :
    I7BoundGenProp n₁ SmoothingF A := by
  obtain ⟨C, Cpos, bound⟩ := I3GenBound suppSmoothingF ContDiffSmoothingF n₁_pos n₂_pos hCζ Cζpos hA
  refine ⟨C, Cpos, fun X X_gt ε εpos ε_lt_one T T_gt ↦ ?_⟩
  specialize bound X X_gt εpos ε_lt_one T_gt
  intro σ₁
  rwa [I7I3 (by linarith), norm_conj]

def I4BoundGenProp (n : ℝ) (SmoothingF : ℝ → ℝ) (A σ₂ : ℝ) : Prop := ∃ (C : ℝ) (_ : 0 ≤ C) (Tlb : ℝ) (_ : 3 < Tlb),
    ∀ (X : ℝ) (_ : 3 < X)
    {ε : ℝ} (_ : 0 < ε) (_ : ε < 1)
    {T : ℝ} (_ : Tlb < T),
    let σ₁ : ℝ := 1 - A / (Real.log T) ^ n
    ‖I₄ SmoothingF ε X σ₁ σ₂‖ ≤ C * X * X ^ (- A / (Real.log T ^ n)) / ε

lemma I4GenBound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    {σ₂ : ℝ} (h_logDeriv_holo : LogDerivZetaIsHoloSmall σ₂) (hσ₂ : σ₂ ∈ Ioo 0 1)
    {n : ℝ} (n_pos : n > 0) {A : ℝ} (hA : A ∈ Ioc 0 (1 / 2)) :
    I4BoundGenProp n SmoothingF A σ₂ := by
  have reOne : re 1 = 1 := rfl
  have imOne : im 1 = 0 := rfl
  have reThree : re 3 = 3 := rfl
  have imThree : im 3 = 0 := rfl

  unfold I4BoundGenProp I₄ SmoothedChebyshevIntegrand

  let S : Set ℝ := (fun (t : ℝ) ↦ ↑‖-(deriv riemannZeta) (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I) / riemannZeta (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I)‖₊) '' Icc 0 1
  let C' : ℝ := sSup S
  have bddAboveS : BddAbove S := by
    refine IsCompact.bddAbove ?_
    unfold S
    refine IsCompact.image_of_continuousOn ?_ ?_
    · exact isCompact_Icc
    · refine ContinuousOn.norm ?_
      have : (fun (t : ℝ) ↦ -(deriv riemannZeta) (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I) / riemannZeta (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I)) =
        (fun (t : ℝ) ↦ -((deriv riemannZeta) (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I) / riemannZeta (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I))) := by
        apply funext
        intro x
        apply neg_div
      rw[this]
      refine ContinuousOn.neg ?_
      have : (fun (t : ℝ) ↦ (deriv riemannZeta) (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I) / riemannZeta (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I)) =
        (((deriv riemannZeta) / riemannZeta) ∘ (fun (t : ℝ) ↦ (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I))) := rfl
      rw[this]
      apply h_logDeriv_holo.continuousOn.comp' (by fun_prop)
      unfold MapsTo
      intro x xInIcc
      simp only [neg_le_self_iff, Nat.ofNat_nonneg, uIcc_of_le, Set.mem_sdiff, mem_singleton_iff]
      have : ¬↑σ₂ + ↑x * (1 - ↑σ₂) - 3 * I = 1 := by
        by_contra h
        rw[Complex.ext_iff, sub_re, add_re, sub_im, add_im] at h
        repeat rw[mul_im] at h
        repeat rw[mul_re] at h
        rw[sub_im, sub_re, reOne, imOne, reThree, imThree, I_im, I_re] at h
        repeat rw[ofReal_re] at h
        repeat rw[ofReal_im] at h
        ring_nf at h
        obtain ⟨_, ripGoal⟩ := h
        linarith
      refine ⟨?_, this⟩
      rw [mem_reProdIm]
      simp only [sub_re, add_re, ofReal_re, mul_re, one_re, ofReal_im, sub_im, one_im, sub_self,
        mul_zero, sub_zero, re_ofNat, I_re, im_ofNat, I_im, mul_one, add_im, mul_im, zero_mul,
        add_zero, zero_sub, mem_Icc, le_refl, neg_le_self_iff, Nat.ofNat_nonneg, and_self, and_true]
      rw [Set.uIcc_of_le]
      · rw [mem_Icc]
        constructor
        · simp only [le_add_iff_nonneg_right]
          apply mul_nonneg
          · exact xInIcc.1
          · linarith [hσ₂.2]
        · have : σ₂ + x * (1 - σ₂) = σ₂ * (1 - x) + x := by ring
          rw [this]
          clear this
          have : (2 : ℝ) = 1 * 1 + 1 := by norm_num
          rw [this]
          clear this
          gcongr
          · linarith [xInIcc.2]
          · exact hσ₂.2.le
          · linarith [xInIcc.1]
          · exact xInIcc.2
      · linarith [hσ₂.2]

  have CPrimeNonneg : 0 ≤ C' := by
    apply Real.sSup_nonneg
    intro x x_in_S
    obtain ⟨t, ht, rfl⟩ := x_in_S
    exact NNReal.coe_nonneg _

  obtain ⟨D, Dpos, MellinSmooth1bBound⟩ := MellinOfSmooth1b ContDiffSmoothingF suppSmoothingF
  let C : ℝ := C' * D / sInf ((fun t => ‖ σ₂ + (t : ℝ) * (1 - σ₂) - 3 * I ‖₊ ^ 2) '' Set.Icc 0 1)
  use C
  have sInfPos : 0 < sInf ((fun (t : ℝ) ↦ ‖↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I‖₊ ^ 2) '' Icc 0 1) := by
    refine (IsCompact.lt_sInf_iff_of_continuous ?_ ?_ ?_ 0).mpr ?_
    · exact isCompact_Icc
    · exact Nonempty.of_subtype
    · have : (fun (t : ℝ) ↦ ‖↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I‖₊ ^ 2) =
        (fun (t : ℝ) ↦ ‖↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I‖₊ * ‖↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I‖₊) := by
        apply funext
        intro x
        rw[pow_two]
      rw[this]
      have : ContinuousOn (fun (t : ℝ) ↦ ‖↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I‖₊) (Icc 0 1) := by
        refine ContinuousOn.nnnorm ?_
        refine ContinuousOn.sub ?_ (by exact continuousOn_const)
        refine ContinuousOn.add (by exact continuousOn_const) ?_
        exact ContinuousOn.mul (by exact Complex.continuous_ofReal.continuousOn) (by exact continuousOn_const)
      exact ContinuousOn.mul (by exact this) (by exact this)
    · intro x xLoc
      apply pow_pos
      have temp : |(↑σ₂ + ↑x * (1 - ↑σ₂) - 3 * I).im| ≤
        ‖↑σ₂ + ↑x * (1 - ↑σ₂) - 3 * I‖₊ := by apply Complex.abs_im_le_norm
      rw[sub_im, add_im, mul_im, mul_im, I_re, I_im, sub_im, sub_re] at temp
      repeat rw[ofReal_re] at temp
      repeat rw[ofReal_im] at temp
      rw[reThree, imOne] at temp
      ring_nf at temp ⊢
      rw[(by ring : σ₂ - σ₂ * x + x - I * 3 = σ₂ - σ₂ * x + (x - I * 3))] at temp ⊢
      rw[abs_of_neg, neg_neg] at temp
      · have : (3 : NNReal) ≤ ‖↑σ₂ - ↑σ₂ * ↑x + (↑x - I * 3)‖₊ := temp
        positivity
      · rw[neg_lt_zero]
        norm_num
  have CNonneg : 0 ≤ C := by
    unfold C
    apply mul_nonneg
    · exact mul_nonneg (by exact CPrimeNonneg) (by exact Dpos.le)
    · rw[inv_nonneg]
      norm_cast
      convert sInfPos.le using 5
      norm_cast
  use CNonneg

  let Tlb : ℝ := max 4 (max (rexp (A ^ (n : ℝ)⁻¹)) (rexp ((A / (1 - σ₂)) ^ (n : ℝ)⁻¹)))
  use Tlb

  have : 3 < Tlb := by
    unfold Tlb
    rw[lt_max_iff]
    refine Or.inl ?_
    norm_num
  use this

  intro X X_gt_three ε ε_pos ε_lt_one T T_gt_Tlb σ₁
  have σ₂_le_σ₁ : σ₂ ≤ σ₁ := by
    have logTlb_pos : 0 < Real.log Tlb := by
      rw[← Real.log_one]
      exact log_lt_log (by norm_num) (by linarith)
    have logTlb_nonneg : 0 ≤ Real.log Tlb := le_of_lt (by exact logTlb_pos)
    have expr_nonneg : 0 ≤ A / (1 - σ₂) := by
      apply div_nonneg
      · linarith [hA.1]
      · rw[sub_nonneg]
        exact le_of_lt hσ₂.2
    have temp : σ₂ ≤ 1 - A / Real.log Tlb ^ n := by
      have : rexp ((A / (1 - σ₂)) ^ (n : ℝ)⁻¹) ≤ Tlb := by
        unfold Tlb
        nth_rewrite 2 [max_comm]
        rw[max_left_comm]
        apply le_max_of_le_left (by rfl)
      rw[← Real.le_log_iff_exp_le] at this
      · have h1 : 0 ≤ (A / (1 - σ₂)) ^ (n : ℝ)⁻¹ := by apply Real.rpow_nonneg (by exact expr_nonneg)
        rw[← Real.rpow_le_rpow_iff h1 logTlb_nonneg n_pos] at this
        have h: ((A / (1 - σ₂)) ^ (n : ℝ)⁻¹) ^ (n : ℝ) = A / (1 - σ₂) := by
          apply rpow_inv_rpow (by exact expr_nonneg)
          exact Ne.symm (Std.ne_of_lt n_pos)
        rw[h, div_le_iff₀, mul_comm, ← div_le_iff₀] at this
        · linarith
        · exact rpow_pos_of_pos (by exact logTlb_pos) _
        · rw[sub_pos]
          exact hσ₂.2
      · positivity
    have : 1 - A / Real.log Tlb ^ n ≤ 1 - A / Real.log T ^ n := by
      apply sub_le_sub (by rfl)
      apply div_le_div₀
      · exact le_of_lt (by exact hA.1)
      · rfl
      · apply Real.rpow_pos_of_pos
        apply Real.log_pos
        linarith
      · exact Real.rpow_le_rpow logTlb_nonneg (log_le_log (by linarith) T_gt_Tlb.le) n_pos.le
    exact le_trans temp this
  have minσ₂σ₁ : min σ₂ σ₁ = σ₂ := min_eq_left (by exact σ₂_le_σ₁)
  have maxσ₂σ₁ : max σ₂ σ₁ = σ₁ := max_eq_right (by exact σ₂_le_σ₁)
  have σ₁_lt_one : σ₁ < 1 := by
    rw[← sub_zero 1]
    unfold σ₁
    apply sub_lt_sub_left
    apply div_pos (by exact hA.1)
    apply Real.rpow_pos_of_pos
    rw[← Real.log_one]
    exact log_lt_log (by norm_num) (by linarith)

  rw[norm_mul, ← one_mul C]
  have : 1 * C * X * X ^ (-A / Real.log T ^ n) / ε = 1 * (C * X * X ^ (-A / Real.log T ^ n) / ε) := by ring
  rw[this]
  apply mul_le_mul
  · rw[norm_div, norm_one]
    repeat rw[norm_mul]
    rw[Complex.norm_two, Complex.norm_real, Real.norm_of_nonneg pi_nonneg, Complex.norm_I, mul_one]
    have : 1 / (2 * π) < 1 / 6 := by
      rw[_root_.one_div_lt_one_div]
      · refine (div_lt_iff₀' ?_).mp ?_
        · norm_num
        ring_nf
        refine gt_iff_lt.mpr ?_
        exact Real.pi_gt_three
      · positivity
      · norm_num
    exact le_of_lt (lt_trans this (by norm_num))
  · let f : ℝ → ℂ := fun σ ↦ (-(deriv riemannZeta) (↑σ - 3 * I) / riemannZeta (↑σ - 3 * I) * mellin (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ - 3 * I) * ↑X ^ (↑σ - 3 * I))
    have temp : ‖∫ (σ : ℝ) in σ₂..σ₁, -(deriv riemannZeta) (↑σ - 3 * I) / riemannZeta (↑σ - 3 * I) * mellin (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ - 3 * I) * ↑X ^ (↑σ - 3 * I)‖ ≤
      C * X * X ^ (-A / Real.log T ^ n) / ε * |σ₁ - σ₂| := by
      have : ∀ x ∈ Set.uIoc σ₂ σ₁, ‖f x‖ ≤ C * X * X ^ (-A / Real.log T ^ n) / ε := by
        intro x xInIoc
        let t : ℝ := (x - σ₂) / (1 - σ₂)
        have tInIcc : t ∈ Icc 0 1 := by
          unfold t
          constructor
          · apply div_nonneg
            · rw[sub_nonneg]
              unfold uIoc at xInIoc
              rw[minσ₂σ₁] at xInIoc
              exact le_of_lt (by exact xInIoc.1)
            · rw[sub_nonneg]
              apply le_of_lt (by exact hσ₂.2)
          · rw[div_le_one]
            · refine sub_le_sub ?_ (by rfl)
              unfold uIoc at xInIoc
              rw[maxσ₂σ₁] at xInIoc
              apply le_trans xInIoc.2
              exact le_of_lt (by exact σ₁_lt_one)
            · rw[sub_pos]
              exact hσ₂.2
        have tExpr : (↑σ₂ + t * (1 - ↑σ₂) - 3 * I) = (↑x - 3 * I) := by
          unfold t
          simp only [ofReal_div, ofReal_sub, ofReal_one, sub_left_inj]
          rw[div_mul_comm, div_self]
          · simp only [one_mul, add_sub_cancel]
          · refine sub_ne_zero_of_ne ?_
            apply Ne.symm
            rw[Complex.ofReal_ne_one]
            exact ne_of_lt (by exact hσ₂.2)
        unfold f
        simp only [Complex.norm_mul]
        have : C * X * X ^ (-A / Real.log T ^ n) / ε =
          (C / ε) * (X * X ^ (-A / Real.log T ^ n)) := by ring
        rw[this]
        have temp : ‖-(deriv riemannZeta) (↑x - 3 * I) / riemannZeta (↑x - 3 * I)‖ * ‖mellin (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑x - 3 * I)‖ ≤
          C / ε := by
          unfold C
          rw[div_div]
          nth_rewrite 2 [div_eq_mul_inv]
          have temp : ‖-(deriv riemannZeta) (↑x - 3 * I) / riemannZeta (↑x - 3 * I)‖ ≤ C' := by
            unfold C'
            have : ‖-(deriv riemannZeta) (↑x - 3 * I) / riemannZeta (↑x - 3 * I)‖ ∈
              (fun (t : ℝ) ↦ ↑‖-(deriv riemannZeta) (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I) / riemannZeta (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I)‖₊) '' Icc 0 1 := by
              rw[Set.mem_image]
              use t
              constructor
              · exact tInIcc
              · rw[tExpr]
                rfl
            exact le_csSup (by exact bddAboveS) (by exact this)
          have : ‖mellin (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑x - 3 * I)‖ ≤
            D * ((sInf ((fun (t : ℝ) ↦ ‖↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I‖₊ ^ 2) '' Icc 0 1)) * ε)⁻¹ := by
            nth_rewrite 3 [mul_comm]
            let s : ℂ := x - 3 * I
            have : mellin (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑x - 3 * I) =
              mellin (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) s := rfl
            rw[this]
            have temp : σ₂ ≤ s.re := by
              unfold s
              rw[sub_re, mul_re, I_re, I_im, reThree, imThree, ofReal_re]
              ring_nf
              apply le_of_lt
              unfold uIoc at xInIoc
              rw[minσ₂σ₁] at xInIoc
              exact xInIoc.1
            have : s.re ≤ 2 := by
              unfold s
              rw[sub_re, mul_re, I_re, I_im, reThree, imThree, ofReal_re]
              ring_nf
              have : x < 1 := by
                unfold uIoc at xInIoc
                rw[maxσ₂σ₁] at xInIoc
                exact lt_of_le_of_lt xInIoc.2 σ₁_lt_one
              linarith
            have temp : ‖mellin (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) s‖ ≤ D * (ε * ‖s‖ ^ 2)⁻¹ := by
              exact MellinSmooth1bBound σ₂ hσ₂.1 s temp this ε ε_pos ε_lt_one
            have : D * (ε * ‖s‖ ^ 2)⁻¹ ≤ D * (ε * ↑(sInf ((fun (t : ℝ) ↦ ‖↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I‖₊ ^ 2) '' Icc 0 1)))⁻¹ := by
              refine mul_le_mul (by rfl) ?_ ?_ (by exact le_of_lt (by exact Dpos))
              · rw[inv_le_inv₀]
                · apply mul_le_mul (by rfl)
                  · rw[NNReal.coe_sInf]
                    apply csInf_le
                    · apply NNReal.bddBelow_coe
                    · unfold s
                      rw[Set.mem_image]
                      let xNorm : NNReal := ‖x - 3 * I‖₊ ^ 2
                      use xNorm
                      constructor
                      · rw[Set.mem_image]
                        use t
                        exact ⟨tInIcc, by rw[tExpr]⟩
                      · rfl
                  · exact le_of_lt (by exact sInfPos)
                  · exact le_of_lt (by exact ε_pos)
                · apply mul_pos (ε_pos)
                  refine sq_pos_of_pos ?_
                  refine norm_pos_iff.mpr ?_
                  refine ne_zero_of_re_pos ?_
                  unfold s
                  rw[sub_re, mul_re, I_re, I_im, reThree, imThree, ofReal_re]
                  ring_nf
                  unfold uIoc at xInIoc
                  rw[minσ₂σ₁] at xInIoc
                  exact lt_trans hσ₂.1 xInIoc.1
                · exact mul_pos (ε_pos) (sInfPos)
              · rw[inv_nonneg]
                apply mul_nonneg (by exact le_of_lt (by exact ε_pos))
                exact sq_nonneg ‖s‖
            exact le_trans temp this
          rw[mul_assoc]
          apply mul_le_mul (by exact temp) (by exact this)
          · have this : 0 ≤ |(mellin (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑x - 3 * I)).re| := by
              apply abs_nonneg
            exact le_trans this (by refine Complex.abs_re_le_norm ?_)
          · exact CPrimeNonneg
        have : ‖(X : ℂ) ^ (↑x - 3 * I)‖ ≤
          X * X ^ (-A / Real.log T ^ n) := by
          nth_rewrite 2 [← Real.rpow_one X]
          rw[← Real.rpow_add]
          · rw[Complex.norm_cpow_of_ne_zero]
            · rw[sub_re, sub_im, mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im, reThree, imThree]
              ring_nf
              rw[Complex.norm_of_nonneg]
              · rw[Complex.arg_ofReal_of_nonneg]
                · rw[zero_mul, neg_zero, Real.exp_zero]
                  simp only [inv_one, mul_one]
                  refine rpow_le_rpow_of_exponent_le ?_ ?_
                  · linarith
                  · unfold uIoc at xInIoc
                    rw[maxσ₂σ₁] at xInIoc
                    unfold σ₁ at xInIoc
                    ring_nf at xInIoc
                    exact xInIoc.2
                · positivity
              · positivity
            · refine ne_zero_of_re_pos ?_
              rw[ofReal_re]
              positivity
          · positivity
        apply mul_le_mul
        · exact temp
        · exact this
        · rw[Complex.norm_cpow_eq_rpow_re_of_pos]
          · rw[sub_re, mul_re, ofReal_re, I_re, I_im, reThree, imThree]
            ring_nf
            apply Real.rpow_nonneg
            positivity
          · positivity
        · exact div_nonneg CNonneg (le_of_lt ε_pos)
      exact intervalIntegral.norm_integral_le_of_norm_le_const this
    have : C * X * X ^ (-A / Real.log T ^ n) / ε * |σ₁ - σ₂| ≤
      C * X * X ^ (-A / Real.log T ^ n) / ε := by
      have : |σ₁ - σ₂| ≤ 1 := by
        rw[abs_of_nonneg]
        · rw[← sub_zero 1]
          exact sub_le_sub σ₁_lt_one.le hσ₂.1.le
        · rw[sub_nonneg]
          exact σ₂_le_σ₁
      bound
    exact le_trans temp this
  · simp only [norm_nonneg]
  norm_num

lemma I6I4 {SmoothingF : ℝ → ℝ} {ε X σ₁ σ₂ : ℝ} (Xpos : 0 < X) :
    I₆ SmoothingF ε X σ₁ σ₂ = -conj (I₄ SmoothingF ε X σ₁ σ₂) := by
  unfold I₆ I₄
  simp only [map_mul, map_div₀, conj_ofReal, conj_I, map_one, conj_ofNat]
  rw [← neg_mul]
  congr
  · ring
  · rw [← intervalIntegral_conj]
    apply intervalIntegral.integral_congr
    intro σ hσ
    simp only
    rw[← smoothedChebyshevIntegrand_conj Xpos]
    simp [conj_ofNat]

def I6BoundGenProp (n : ℝ) (SmoothingF : ℝ → ℝ) (A σ₂ : ℝ) : Prop := ∃ (C : ℝ) (_ : 0 ≤ C) (Tlb : ℝ) (_ : 3 < Tlb),
    ∀ (X : ℝ) (_ : 3 < X)
    {ε : ℝ} (_ : 0 < ε) (_ : ε < 1)
    {T : ℝ} (_ : Tlb < T),
    let σ₁ : ℝ := 1 - A / (Real.log T) ^ n
    ‖I₆ SmoothingF ε X σ₁ σ₂‖ ≤ C * X * X ^ (- A / (Real.log T ^ n)) / ε

lemma I6GenBound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    {σ₂ : ℝ} (h_logDeriv_holo : LogDerivZetaIsHoloSmall σ₂) (hσ₂ : σ₂ ∈ Ioo 0 1)
    {n : ℝ} (n_pos : 0 < n) {A : ℝ} (hA : A ∈ Ioc 0 (1 / 2)) :
    I6BoundGenProp n SmoothingF A σ₂ := by
  obtain ⟨C, Cpos, Tlb, Tlb_gt, bound⟩ := I4GenBound suppSmoothingF ContDiffSmoothingF h_logDeriv_holo hσ₂ n_pos hA
  refine ⟨C, Cpos, Tlb, Tlb_gt, fun X X_gt ε εpos ε_lt_one T T_gt ↦ ?_⟩
  specialize bound X X_gt εpos ε_lt_one T_gt
  intro σ₁
  rwa [I6I4 (by linarith), norm_neg, norm_conj]

def I5BoundGenProp (SmoothingF : ℝ → ℝ) (σ₂ : ℝ) : Prop := ∃ (C : ℝ) (_ : 0 < C),
    ∀ (X : ℝ) (_ : 3 < X) {ε : ℝ} (_ : 0 < ε) (_ : ε < 1),
    ‖I₅ SmoothingF ε X σ₂‖ ≤ C * X ^ σ₂ / ε

lemma I5Bound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    {σ₂ : ℝ} (h_logDeriv_holo : LogDerivZetaIsHoloSmall σ₂) (hσ₂ : σ₂ ∈ Ioo 0 1) :
    I5BoundGenProp SmoothingF σ₂ := by
  unfold LogDerivZetaIsHoloSmall HolomorphicOn at h_logDeriv_holo
  let zeta'_zeta_on_line := fun (t : ℝ) ↦ (deriv riemannZeta) (σ₂ + t * I) / riemannZeta (σ₂ + t * I)

  have subst : {σ₂} ×ℂ uIcc (-3) 3 ⊆ (uIcc σ₂ 2 ×ℂ uIcc (-3) 3) \ {1} := by
    simp! only [neg_le_self_iff, Nat.ofNat_nonneg, uIcc_of_le]
    simp_all only [one_div, support_subset_iff, ne_eq, mem_Icc, neg_le_self_iff,
      Nat.ofNat_nonneg, uIcc_of_le]
    intro z hyp_z
    simp only [mem_reProdIm, mem_singleton_iff, mem_Icc] at hyp_z
    simp only [Set.mem_sdiff, mem_reProdIm, mem_Icc, mem_singleton_iff]
    constructor
    · constructor
      · rw [hyp_z.1]
        apply left_mem_uIcc
      · exact hyp_z.2
    · push Not
      by_contra h
      rw [h] at hyp_z
      simp only [one_re, one_im, Left.neg_nonpos_iff, Nat.ofNat_nonneg, and_self, and_true] at hyp_z
      linarith [hσ₂.2]

  have zeta'_zeta_cont := (h_logDeriv_holo.mono subst).continuousOn

  have is_compact' : IsCompact ({σ₂} ×ℂ uIcc (-3) 3) := by
    refine IsCompact.reProdIm ?_ ?_
    · exact isCompact_singleton
    · exact isCompact_uIcc

  let ⟨zeta_bound, zeta_prop⟩ :=
    IsCompact.exists_bound_of_continuousOn (is_compact') zeta'_zeta_cont

  let ⟨M, ⟨M_is_pos, M_bounds_mellin_hard⟩⟩ :=
    MellinOfSmooth1b ContDiffSmoothingF suppSmoothingF

  clear is_compact' zeta'_zeta_cont subst zeta'_zeta_on_line h_logDeriv_holo

  unfold I5BoundGenProp I₅ SmoothedChebyshevIntegrand

  let mellin_prop : ∀ (t ε : ℝ),
  0 < ε → ε < 1 → ‖mellin (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑σ₂ + ↑t * I)‖ ≤ M * (ε * ‖↑σ₂ + ↑t * I‖ ^ 2)⁻¹  :=
    fun (t : ℝ) ↦ (M_bounds_mellin_hard σ₂ (by linarith[hσ₂.1]) (σ₂ + t * I) (by simp only [add_re,
      ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero, le_refl]) (by simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero]; linarith[hσ₂.2]))

  simp only [mul_inv_rev] at mellin_prop

  let Const := 1 + (σ₂^2)⁻¹ * (abs zeta_bound) * M

  let C := |π|⁻¹ * 2⁻¹ * 6 * Const
  use C
  have C_pos : 0 < C := by positivity
  use C_pos

  clear C_pos

  intros X X_gt ε ε_pos ε_lt_one

  have mellin_bound := fun (t : ℝ) ↦ mellin_prop t ε ε_pos ε_lt_one

  have U: 0 < σ₂^2 := by
    exact sq_pos_of_pos (by linarith[hσ₂.1])

  have easy_bound : ∀(t : ℝ), (‖↑σ₂ + ↑t * I‖^2)⁻¹ ≤ (σ₂^2)⁻¹ :=
    by
      intro t
      rw [inv_le_inv₀]
      · rw [Complex.sq_norm, Complex.normSq_apply]
        simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
          add_zero, add_im, mul_im, zero_add]
        ring_nf
        simp only [le_add_iff_nonneg_right]
        exact zpow_two_nonneg t
      · rw [Complex.sq_norm, Complex.normSq_apply]
        simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
          add_zero, add_im, mul_im, zero_add]
        ring_nf
        positivity
      positivity

  have T1 : ∀(t : ℝ), t ∈ uIoc (-3) (3 : ℝ) → ‖-(deriv riemannZeta) (↑σ₂ + ↑t * I) / riemannZeta (↑σ₂ + ↑t * I) * mellin (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₂ + ↑t * I) *
          (↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖ ≤ Const * ε⁻¹ * X ^ σ₂ := by
    intro t hyp_t
    have Z := by
      calc
        ‖(-(deriv riemannZeta) (↑σ₂ + ↑t * I) / riemannZeta (↑σ₂ + ↑t * I)) * (mellin (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑σ₂ + ↑t * I)) *
        (↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖ = ‖-(deriv riemannZeta) (↑σ₂ + ↑t * I) / riemannZeta (↑σ₂ + ↑t * I)‖ * ‖mellin (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑σ₂ + ↑t * I)‖ * ‖(↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖  := by simp only [Complex.norm_mul,
          Complex.norm_div, norm_neg]
        _ ≤ ‖(deriv riemannZeta) (↑σ₂ + ↑t * I) / riemannZeta (↑σ₂ + ↑t * I)‖ * ‖mellin (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑σ₂ + ↑t * I)‖ * ‖(↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖ := by simp only [Complex.norm_div,
          norm_neg, le_refl]
        _ ≤ zeta_bound *  ‖mellin (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑σ₂ + ↑t * I)‖ * ‖(↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖  :=
          by
            have U := zeta_prop (↑σ₂ + t * I) (by
                simp only [neg_le_self_iff, Nat.ofNat_nonneg, uIcc_of_le]
                simp only [mem_reProdIm, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
                  mul_one, sub_self, add_zero, mem_singleton_iff, add_im, mul_im, zero_add, mem_Icc]
                constructor
                · trivial
                · refine mem_Icc.mp ?_
                  · refine mem_Icc_of_Ioc ?_
                    · have T : (-3 : ℝ) ≤ 3 := by simp only [neg_le_self_iff, Nat.ofNat_nonneg]
                      rw [←Set.uIoc_of_le T]
                      exact hyp_t)
            simp only [Complex.norm_div] at U
            simp only [Complex.norm_div, ge_iff_le]
            linear_combination U * ‖mellin (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑σ₂ + ↑t * I)‖ * ‖(↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖
        _ ≤ abs zeta_bound * ‖mellin (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑σ₂ + ↑t * I)‖ * ‖(↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖  := by
          have U : zeta_bound ≤ abs zeta_bound := by simp only [le_abs_self]
          linear_combination (U * ‖mellin (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑σ₂ + ↑t * I)‖ * ‖(↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖  )
        _ ≤ abs zeta_bound * M * ((‖↑σ₂ + ↑t * I‖ ^ 2)⁻¹ * ε⁻¹) * ‖(↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖  := by
          have U := mellin_bound t
          linear_combination (abs zeta_bound) * U * ‖(↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖
        _ ≤ abs zeta_bound * M * (σ₂^2)⁻¹ * ε⁻¹ * ‖(↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖  := by
          linear_combination (abs zeta_bound * M * easy_bound t * ε⁻¹ * ‖(↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖)
        _ = abs zeta_bound * M * (σ₂^2)⁻¹ * ε⁻¹ * X ^ (σ₂) := by
          rw [Complex.norm_cpow_eq_rpow_re_of_pos]
          · simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
              sub_self, add_zero]
          positivity
        _ ≤ Const * ε⁻¹ * X ^ σ₂ := by
          unfold Const
          ring_nf
          simp only [inv_pow, le_add_iff_nonneg_right, inv_pos, mul_nonneg_iff_of_pos_left, ε_pos]
          positivity

    exact Z

  simp only [one_div, mul_inv_rev, inv_I, neg_mul, norm_neg, Complex.norm_mul, norm_I, norm_inv,
    norm_real, norm_eq_abs, Complex.norm_ofNat, one_mul, ge_iff_le]
  have Z :=
    intervalIntegral.norm_integral_le_of_norm_le_const T1
  simp only [ge_iff_le]

  have S : |π|⁻¹ * 2⁻¹ * (Const * ε⁻¹ * X ^ σ₂ * |3 + 3|) = C * X ^ σ₂ / ε := by
    unfold C
    ring_nf

  simp only [sub_neg_eq_add] at Z
  simp only [← S, ge_iff_le]
  linear_combination (|π|⁻¹ * 2⁻¹ * Z)

def LogDerivZetaBoundedAndHoloGenProp (n₁ n₂ : ℝ) : Prop := ∃ A C : ℝ, 0 < C ∧ A ∈ Ioc 0 (1 / 2) ∧ LogDerivZetaHasBound n₁ n₂ A C
    ∧ ∀ (T : ℝ) (_ : 3 ≤ T),
    HolomorphicOn (fun (s : ℂ) ↦ (deriv riemannZeta) s / (riemannZeta s))
    (( (Icc ((1 : ℝ) - A / Real.log T ^ n₁) 2)  ×ℂ (Icc (-T) T) ) \ {1})

lemma LogDerivZetaBoundedAndHoloGen {n₁ n₂ : ℝ}
  (LogDerivZetaBndUnif : LogDerivZetaBndUnifGenProp n₁ n₂)
  (LogDerivZetaHolcLargeT : LogDerivZetaHolcLargeTGenProp n₁) :
  LogDerivZetaBoundedAndHoloGenProp n₁ n₂ := by
  obtain ⟨A₁, A₁_in, C, C_pos, zeta_bnd⟩ := LogDerivZetaBndUnif
  obtain ⟨A₂, A₂_in, holo⟩ := LogDerivZetaHolcLargeT
  refine ⟨min A₁ A₂, C, C_pos, ?_, ?_, ?_⟩
  · exact ⟨lt_min A₁_in.1 A₂_in.1, le_trans (min_le_left _ _) A₁_in.2⟩
  · intro σ T hT hσ
    apply zeta_bnd _ _ hT
    apply mem_Ici.mpr (le_trans _ hσ)
    gcongr
    · bound
    · apply min_le_left
  · intro T hT
    apply (holo _ hT).mono
    intro s hs
    simp only [Set.mem_sdiff, mem_singleton_iff, mem_reProdIm] at hs ⊢
    refine ⟨?_, hs.2⟩
    refine ⟨?_, hs.1.2⟩
    refine ⟨?_, hs.1.1.2⟩
    apply le_trans _ hs.1.1.1
    gcongr
    · bound
    · apply min_le_right

lemma LogDerivZetaBoundedAndHolo99 : LogDerivZetaBoundedAndHoloGenProp 9 9 := by
  exact LogDerivZetaBoundedAndHoloGen LogDerivZetaBndUnif99 LogDerivZetaHolcLargeT9

lemma MellinOfSmooth1cExplicit {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (suppν : ν.support ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi 0, ν x / x = 1) :
    ∃ ε₀ c : ℝ, 0 < ε₀ ∧ 0 < c ∧
    ∀ ε ∈ Ioo 0 ε₀, ‖mellin (fun x ↦ (Smooth1 ν ε x : ℂ)) 1 - 1‖ ≤ c * ε := by
  have := MellinOfSmooth1c diffν suppν mass_one
  rw [Asymptotics.isBigO_iff'] at this
  rcases this with ⟨c, cpos, hc⟩
  unfold Filter.Eventually at hc
  rw [mem_nhdsGT_iff_exists_Ioo_subset] at hc
  rcases hc with ⟨ε₀, ε₀pos, h⟩
  refine ⟨ε₀, c, ε₀pos, cpos, fun ε hε ↦ ?_⟩
  specialize h hε
  rw [mem_setOf_eq, id_eq, norm_of_nonneg hε.1.le] at h
  exact h

open Filter Topology

lemma x_ε_to_inf (c : ℝ) {B : ℝ} (B_le : B < 1) : Tendsto
    (fun x ↦ x * Real.exp (-c * (Real.log x) ^ B)) atTop atTop := by
  have coeff_to_zero {B : ℝ} (B_le : B < 1) :
      Tendsto (fun x ↦ Real.log x ^ (B - 1)) atTop (𝓝 0) := by
    have B_minus_1_neg : B - 1 < 0 := by linarith
    rw [← Real.zero_rpow (ne_of_lt B_minus_1_neg),
      zero_rpow (ne_of_lt B_minus_1_neg)]

    have one_minus_B_pos : 0 < 1 - B := by linarith
    rw [show B - 1 = -(1 - B) by ring]
    have : ∀ᶠ (x : ℝ) in atTop, Real.log x ^ (-(1 - B)) = (Real.log x ^ ((1 - B)))⁻¹ := by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
      apply Real.rpow_neg
      exact Real.log_nonneg hx
    rw [tendsto_congr' this]
    apply tendsto_inv_atTop_zero.comp
    apply (tendsto_rpow_atTop one_minus_B_pos).comp
    exact tendsto_log_atTop

  have log_sub_log_pow_inf (c : ℝ) {B : ℝ} (B_le : B < 1) :
      Tendsto (fun (x : ℝ) ↦ Real.log x - c * Real.log x ^ B) atTop atTop := by
    have factor_form : ∀ x > 1, Real.log x - c * Real.log x ^ B =
        Real.log x * (1 - c * Real.log x ^ (B - 1)) := by
      intro x hx
      ring_nf
      congr! 1
      rw [mul_assoc, mul_comm (Real.log x), mul_assoc]
      congr! 1
      have log_pos : 0 < Real.log x := Real.log_pos hx
      rw [(by simp : Real.log x ^ (-1 + B) * Real.log x =
        Real.log x ^ (-1 + B) * (Real.log x) ^ (1 : ℝ))]
      rw [← Real.rpow_add log_pos]
      ring_nf
    have coeff_to_one : Tendsto (fun x ↦ 1 - c * Real.log x ^ (B - 1)) atTop (𝓝 1) := by
      specialize coeff_to_zero B_le
      apply Tendsto.const_mul c at coeff_to_zero
      convert (tendsto_const_nhds (x := (1 : ℝ)) (f := (atTop : Filter ℝ))).sub coeff_to_zero
      ring

    have eventually_factored : ∀ᶠ x in atTop, Real.log x - c * Real.log x ^ B =
    Real.log x * (1 - c * Real.log x ^ (B - 1)) := by
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
      exact factor_form x hx

    rw [tendsto_congr' eventually_factored]
    apply Tendsto.atTop_mul_pos (by norm_num : (0 : ℝ) < 1) tendsto_log_atTop  coeff_to_one

  have x_εx_eq (c B : ℝ) : ∀ᶠ (x : ℝ) in atTop, x * rexp (-c * Real.log x ^ B) =
        rexp (Real.log x - c * Real.log x ^ B) := by
    filter_upwards [eventually_gt_atTop 0] with x hx_pos
    conv =>
      enter [1, 1]
      rw [(Real.exp_log hx_pos).symm]
    rw [← Real.exp_add]
    ring_nf

  rw [tendsto_congr' (x_εx_eq c B)]
  exact tendsto_exp_atTop.comp (log_sub_log_pow_inf c B_le)

lemma GenStrengthPNT {n₁ n₂ : ℝ}
  (LogDerivZetaBoundedAndHolo : LogDerivZetaBoundedAndHoloGenProp n₁ n₂)
  (n₁_pos : 0 < n₁) (n₂_pos : 0 < n₂) : ∃ c > 0,
  (ψ - id) =O[atTop]
    fun (x : ℝ) ↦ x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / (1 + n₁))) := by
  have ⟨ν, ContDiffν, ν_nonneg', ν_supp, ν_massOne'⟩ := SmoothExistence
  have ContDiff1ν : ContDiff ℝ 1 ν := by exact ContDiffν.of_le (by simp)
  have ν_nonneg : ∀ x > 0, 0 ≤ ν x := fun x _ ↦ ν_nonneg' x
  have ν_massOne : ∫ x in Ioi 0, ν x / x = 1 := by rwa [← integral_Ici_eq_integral_Ioi]
  obtain ⟨A, C_bnd, C_bnd_pos, A_in_Ioc, zeta_bnd, holo1⟩ := LogDerivZetaBoundedAndHolo
  obtain ⟨σ₂, σ₂InIoo, holo2⟩ := LogDerivZetaHolcSmallT'
  obtain ⟨c_close, c_close_pos, h_close⟩ := SmoothedChebyshevClose ContDiff1ν ν_supp ν_nonneg ν_massOne
  obtain ⟨ε_main, C_main, ε_main_pos, C_main_pos, h_main⟩  := MellinOfSmooth1cExplicit ContDiff1ν ν_supp ν_massOne

  obtain ⟨c₁, c₁pos, hc₁⟩ := I1Bound ν_supp ContDiff1ν ν_nonneg ν_massOne
  obtain ⟨c₂, c₂pos, hc₂⟩ := I2GenBound ν_supp ContDiff1ν n₁_pos n₂_pos zeta_bnd C_bnd_pos A_in_Ioc
  obtain ⟨c₃, c₃pos, hc₃⟩ := I3GenBound ν_supp ContDiff1ν n₁_pos n₂_pos zeta_bnd C_bnd_pos A_in_Ioc
  obtain ⟨c₅, c₅pos, hc₅⟩ := I5Bound ν_supp ContDiff1ν holo2  σ₂InIoo
  obtain ⟨c₇, c₇pos, hc₇⟩ := I7GenBound ν_supp ContDiff1ν n₁_pos n₂_pos zeta_bnd C_bnd_pos A_in_Ioc
  obtain ⟨c₈, c₈pos, hc₈⟩ := I8GenBound ν_supp ContDiff1ν n₁_pos n₂_pos zeta_bnd C_bnd_pos A_in_Ioc
  obtain ⟨c₉, c₉pos, hc₉⟩ := I9Bound ν_supp ContDiff1ν ν_nonneg ν_massOne

  obtain ⟨c₄, c₄pos, Tlb₄, Tlb₄bnd, hc₄⟩ := I4GenBound ν_supp ContDiff1ν holo2 σ₂InIoo n₁_pos A_in_Ioc
  obtain ⟨c₆, c₆pos, Tlb₆, Tlb₆bnd, hc₆⟩ := I6GenBound ν_supp ContDiff1ν holo2 σ₂InIoo n₁_pos A_in_Ioc

  let C' := c_close + C_main
  let C'' := c₁ + c₂ + c₈ + c₉
  let C''' := c₃ + c₄ + c₆ + c₇

  let c : ℝ := A ^ ((1 : ℝ) / (1 + n₁)) / 4
  have cpos : 0 < c := by
    simp_all only [one_div, support_subset_iff, ne_eq, mem_Icc, gt_iff_lt, mem_Ioo, and_imp,
      mem_Ioc, Nat.ofNat_pos, neg_le_self_iff, Nat.ofNat_nonneg, uIcc_of_le,
      div_pos_iff_of_pos_right, c]
    obtain ⟨left, right⟩ := A_in_Ioc
    positivity
  refine ⟨c, cpos, ?_⟩
  rw [Asymptotics.isBigO_iff]
  let C : ℝ := C' + C'' + C''' + c₅
  refine ⟨C, ?_⟩

  let c_εx : ℝ := A ^ ((1 : ℝ) / (1 + n₁)) / 2
  have c_εx_pos : 0 < c_εx := by
    simp_all only [one_div, support_subset_iff, ne_eq, mem_Icc, gt_iff_lt, mem_Ioo, and_imp,
      mem_Ioc, Nat.ofNat_pos, neg_le_self_iff, Nat.ofNat_nonneg, uIcc_of_le,
      div_pos_iff_of_pos_right, c, c_εx]
  let c_Tx : ℝ := A ^ ((1 : ℝ) / (1 + n₁))
  have c_Tx_pos : 0 < c_Tx := by
    simp_all only [one_div, support_subset_iff, ne_eq, mem_Icc, gt_iff_lt, mem_Ioo, and_imp,
      mem_Ioc, Nat.ofNat_pos, neg_le_self_iff, Nat.ofNat_nonneg, uIcc_of_le,
      div_pos_iff_of_pos_right, c, c_εx, c_Tx]

  let εx := (fun x ↦ Real.exp (-c_εx * (Real.log x) ^ ((1 : ℝ) / (1 + n₁))))
  let Tx := (fun x ↦ Real.exp (c_Tx * (Real.log x) ^ ((1 : ℝ) / (1 + n₁))))

  have one_div_succ_n₁_pos : 0 < (1 : ℝ) / (1 + n₁) := by
    simp only [one_div, inv_pos]
    linarith

  have one_div_succ_n₁_lt_one : (1 : ℝ) / (1 + n₁) < 1 := by
    rw [one_div, inv_lt_one₀ (one_div_pos.mp one_div_succ_n₁_pos)]
    norm_num [n₁_pos]

  have Tx_to_inf : Tendsto Tx atTop atTop := by
    unfold Tx
    apply tendsto_exp_atTop.comp
    apply Tendsto.pos_mul_atTop c_Tx_pos tendsto_const_nhds
    exact (tendsto_rpow_atTop one_div_succ_n₁_pos).comp Real.tendsto_log_atTop

  have ex_to_zero : Tendsto εx atTop (𝓝 0) := by
    unfold εx
    apply Real.tendsto_exp_atBot.comp
    have this (x) : -c_εx * Real.log x ^ ((1 : ℝ) / (1 + n₁)) = -(c_εx * Real.log x ^ ((1 : ℝ) / (1 + n₁))) := by
      ring
    simp_rw [this]
    rw [tendsto_neg_atBot_iff]
    apply Tendsto.const_mul_atTop c_εx_pos
    exact (tendsto_rpow_atTop one_div_succ_n₁_pos).comp tendsto_log_atTop

  have eventually_εx_lt_one : ∀ᶠ (x : ℝ) in atTop, εx x < 1 := by
    apply (tendsto_order.mp ex_to_zero).2
    norm_num

  have eventually_2_lt : ∀ᶠ (x : ℝ) in atTop, 2 < x * εx x := by
    have := x_ε_to_inf c_εx one_div_succ_n₁_lt_one
    exact this.eventually_gt_atTop 2

  have eventually_T_gt_3 : ∀ᶠ (x : ℝ) in atTop, 3 < Tx x := by
    exact Tx_to_inf.eventually_gt_atTop 3

  have eventually_T_gt_Tlb₄ : ∀ᶠ (x : ℝ) in atTop, Tlb₄ < Tx x := by
    exact Tx_to_inf.eventually_gt_atTop _
  have eventually_T_gt_Tlb₆ : ∀ᶠ (x : ℝ) in atTop, Tlb₆ < Tx x := by
    exact Tx_to_inf.eventually_gt_atTop _

  have eventually_σ₂_lt_σ₁ : ∀ᶠ (x : ℝ) in atTop, σ₂ < 1 - A / (Real.log (Tx x)) ^ n₁ := by
    apply (tendsto_order.mp ?_).1
    · exact σ₂InIoo.2
    have := tendsto_inv_atTop_zero.comp ((tendsto_rpow_atTop n₁_pos).comp
      (tendsto_log_atTop.comp Tx_to_inf))
    have := Tendsto.const_mul (b := A) this
    convert (tendsto_const_nhds (x := (1 : ℝ))).sub this using 2
    · simp only [comp_apply, div_eq_mul_inv]
    · simp

  have eventually_ε_lt_ε_main : ∀ᶠ (x : ℝ) in atTop, εx x < ε_main := by
    apply (tendsto_order.mp ex_to_zero).2
    assumption

  have event_logX_ge : ∀ᶠ (x : ℝ) in atTop, 1 ≤ Real.log x := by
    apply Real.tendsto_log_atTop.eventually_ge_atTop

  have event_1_aux_1 {const1 const2 : ℝ} (const1pos : 0 < const1) (const2pos : 0 < const2) :
    ∀ᶠ (x : ℝ) in atTop,
    rexp (-const1 * Real.log x ^ const2) * Real.log x ≤
    rexp 0 := by
      have := ((isLittleO_log_rpow_atTop const2pos).bound const1pos)
      have : ∀ᶠ (x : ℝ) in atTop, Real.log (Real.log x) ≤
          const1 * (Real.log x) ^ const2 := by
        have := tendsto_log_atTop.eventually this
        filter_upwards [this, eventually_gt_atTop 10] with x hx x_gt
        convert hx using 1
        · rw [Real.norm_of_nonneg]
          exact Real.log_nonneg (logt_gt_one (by linarith)).le
        · congr! 1
          rw [Real.norm_of_nonneg]
          apply Real.rpow_nonneg
          apply Real.log_nonneg
          linarith
      have loglogx :  ∀ᶠ (x : ℝ) in atTop,
          Real.log x = rexp (Real.log (Real.log x)) := by
        filter_upwards [eventually_gt_atTop 3] with x hx
        rw [Real.exp_log]
        apply Real.log_pos
        linarith
      filter_upwards [loglogx, this] with x loglogx hx
      conv =>
        enter [1, 2]
        rw [loglogx]
      rw [← Real.exp_add]
      apply Real.exp_monotone
      grw [hx]
      simp

  have event_1_aux {const1 const1' const2 : ℝ} (const1bnds : const1' < const1)
    (const2pos : 0 < const2) :
    ∀ᶠ (x : ℝ) in atTop,
    rexp (-const1 * Real.log x ^ const2) * Real.log x ≤
    rexp (-const1' * Real.log x ^ const2) := by
      have : 0 < const1 - const1' := by linarith
      filter_upwards [event_1_aux_1 this const2pos] with x hx
      have : rexp (-const1 * Real.log x ^ const2) * Real.log x
        = rexp (-(const1') * Real.log x ^ const2)
          * rexp (-(const1 - const1') * Real.log x ^ const2) * Real.log x := by
          congr! 1
          rw [← Real.exp_add]
          congr! 1
          ring
      rw [this,
        mul_assoc]

      grw [hx]
      simp

  have event_1 : ∀ᶠ (x : ℝ) in atTop, C' * (εx x) * x * Real.log x ≤
      C' * x * rexp (-c * Real.log x ^ ((1 : ℝ) / (1 + n₁))) := by
    unfold c εx c_εx
    have const1bnd : (A ^ ((1 : ℝ) / (1 + n₁)) / 4) < (A ^ ((1 : ℝ) / (1 + n₁)) / 2) := by
        linarith
    have this (x) :
      C' * rexp (-(A ^ ((1 : ℝ) / (1 + n₁)) / 2) * Real.log x ^ ((1 : ℝ) / (1 + n₁))) * x * Real.log x =
      C' * x * (rexp (-(A ^ ((1 : ℝ) / (1 + n₁)) / 2) * Real.log x ^ ((1 : ℝ) / (1 + n₁))) * Real.log x) := by ring
    simp_rw [this]
    filter_upwards [event_1_aux const1bnd one_div_succ_n₁_pos, eventually_gt_atTop 3] with x x_bnd x_gt
    grw [x_bnd]

  have event_2 : ∀ᶠ (x : ℝ) in atTop, C'' * x * Real.log x / (εx x * Tx x) ≤
      C'' * x * rexp (-c * Real.log x ^ ((1 : ℝ) / (1 + n₁))) := by
    unfold c εx c_εx Tx c_Tx
    set const2 : ℝ := 1 / (1 + n₁)
    have const2bnd : 0 < const2 := one_div_succ_n₁_pos
    set const1 := (A ^ const2 / 2)
    set const1' := (A ^ const2 / 4)
    have this (x) : -(-const1 * Real.log x ^ const2 + A ^ const2 * Real.log x ^ const2) =
      -(A ^ const2 - const1) * Real.log x ^ const2 := by ring
    simp_rw [← Real.exp_add, div_eq_mul_inv, ← Real.exp_neg, this]
    have const1bnd : const1' < (A ^ const2 - const1) := by
      unfold const1' const1
      linarith
    filter_upwards [event_1_aux const1bnd const2bnd, eventually_gt_atTop 3] with x x_bnd x_gt
    rw [mul_assoc]
    conv =>
      enter [1, 2]
      rw [mul_comm]
    grw [x_bnd]

  have event_3_aux {const1 const1' const2 : ℝ} (const2_eq : const2 = 1 / (1 + n₁))
    (const1_eq : const1 = (A ^ const2 / 2)) (const1'_eq : const1' = (A ^ const2 / 4)) :
    ∀ᶠ (x : ℝ) in atTop,
      x ^ (-A / Real.log (rexp (A ^ const2 * Real.log x ^ const2)) ^ (n₁ : ℝ)) *
      rexp (-(-const1 * Real.log x ^ const2)) ≤
      rexp (-const1' * Real.log x ^ const2) := by
    have : ∀ᶠ (x : ℝ) in atTop, x = rexp (Real.log x) := by
      filter_upwards [eventually_gt_atTop 0] with x hx
      rw [Real.exp_log hx]
    filter_upwards [this, eventually_gt_atTop 3] with x hx x_gt_3
    have logxpos : 0 < Real.log x := by apply Real.log_pos; linarith
    conv =>
      enter [1, 1, 1]
      rw [hx]
    rw [← Real.exp_mul, Real.log_exp, Real.mul_rpow]
    · have {y : ℝ} (ypos : 0 < y) : y / (y ^ const2) ^ (n₁ : ℝ) = y ^ const2 := by
        rw [← Real.rpow_mul ypos.le,
          div_eq_mul_inv]

        rw [← Real.rpow_neg ypos.le]
        conv =>
          enter [1, 1]
          rw [← Real.rpow_one y]
        rw [← Real.rpow_add ypos, const2_eq]
        field_simp
        ring_nf
      rw [div_mul_eq_div_div, neg_div, this (A_in_Ioc.1), mul_div]
      conv =>
        enter [1, 1, 1, 1]
        rw [mul_comm]
      rw [← mul_div, this (y := Real.log x) logxpos, ← Real.exp_add]
      apply Real.exp_monotone
      have : -A ^ const2 * Real.log x ^ const2 + -(-const1 * Real.log x ^ const2)
       = (-(A ^ const2 - const1) * Real.log x ^ const2) := by ring
      rw [this]
      gcongr
      rw [const1'_eq, const1_eq]
      have : 0 ≤ A ^ const2 := by
        apply Real.rpow_nonneg A_in_Ioc.1.le
      linarith
    · rw [const2_eq]
      positivity
    · apply Real.rpow_nonneg
      apply Real.log_nonneg
      linarith

  have event_3 : ∀ᶠ (x : ℝ) in atTop, C''' * x * x ^ (-A / Real.log (Tx x) ^ n₁) / (εx x) ≤
      C''' * x * rexp (-c * Real.log x ^ ((1 : ℝ) / (1 + n₁))) := by
    unfold c Tx c_Tx εx c_εx
    set const2 : ℝ := 1 / (1 + n₁) with const2eq
    set const1 := (A ^ const2 / 2) with const1eq
    set const1' := (A ^ const2 / 4) with const1'eq
    conv =>
      enter [1, x, 1]
      rw [div_eq_mul_inv, ← Real.exp_neg]
    filter_upwards [event_3_aux const2eq const1eq const1'eq,
      eventually_gt_atTop 3] with x x_bnd x_gt
    have this (x) : C''' * x * x ^ (-A / Real.log (rexp (A ^ const2 * Real.log x ^ const2)) ^ n₁)
        * rexp (-(-const1 * Real.log x ^ const2))
      = C''' * x * (x ^ (-A / Real.log (rexp (A ^ const2 * Real.log x ^ const2)) ^ (n₁ : ℝ))
        * rexp (-(-const1 * Real.log x ^ const2))) := by
      ring
    rw [this]
    grw [x_bnd]

  have event_4_aux4 {pow2 : ℝ} (pow2_neg : pow2 < 0) {c : ℝ} (cpos : 0 < c) (c' : ℝ) :
      Tendsto (fun x ↦ c' * Real.log x ^ pow2) atTop (𝓝 0) := by
    rw [← mul_zero c']
    apply Tendsto.const_mul
    have := tendsto_rpow_neg_atTop (y := -pow2) (by linarith)
    rw [neg_neg] at this
    apply this.comp
    exact Real.tendsto_log_atTop

  have event_4_aux3 {pow2 : ℝ} (pow2_neg : pow2 < 0) {c : ℝ} (cpos : 0 < c) (c' : ℝ) :
      ∀ᶠ (x : ℝ) in atTop, c' * (Real.log x) ^ pow2 < c := by
    apply (event_4_aux4 pow2_neg cpos c').eventually_lt_const
    exact cpos

  have event_4_aux2 {c1 : ℝ} (c1pos : 0 < c1) (c2 : ℝ) {pow1 : ℝ} (pow1_lt : pow1 < 1) :
      ∀ᶠ (x : ℝ) in atTop, 0 ≤ Real.log x * (c1 - c2 * (Real.log x) ^ (pow1 - 1)) := by
    filter_upwards [eventually_gt_atTop 3 , event_4_aux3 (by linarith : pow1 - 1 < 0)
      (by linarith : 0 < c1 / 2) c2] with x x_gt hx
    have : 0 ≤ Real.log x := by
      apply Real.log_nonneg
      linarith
    apply mul_nonneg this
    linarith

  have event_4_aux1 {const1 : ℝ} (const1_lt : const1 < 1) (const2 const3 : ℝ)
      {pow1 : ℝ} (pow1_lt : pow1 < 1) : ∀ᶠ (x : ℝ) in atTop,
      const1 * Real.log x + const2 * Real.log x ^ pow1
        ≤ Real.log x - const3 * Real.log x ^ pow1 := by
    filter_upwards [event_4_aux2 (by linarith : 0 < 1 - const1) (const2 + const3) pow1_lt,
      eventually_gt_atTop 3] with x hx x_gt
    have :
      Real.log x - const3 * Real.log x ^ pow1 - (const1 * Real.log x + const2 * Real.log x ^ pow1)
      = (1 - const1) * Real.log x - (const2 + const3) * Real.log x ^ pow1 := by ring
    rw [← sub_nonneg, this]
    convert hx using 1
    ring_nf
    congr! 1
    · have : Real.log x * const2 * Real.log x ^ (-1 + pow1)
          = const2 * Real.log x ^ pow1 := by
        rw [mul_assoc, mul_comm, mul_assoc]
        congr! 1
        conv =>
          enter [1, 2]
          rw [← Real.rpow_one (Real.log x)]
        rw [← Real.rpow_add (Real.log_pos (by linarith))]
        ring_nf
      rw [this]
    have : Real.log x * const3 * Real.log x ^ (-1 + pow1)
        = const3 * Real.log x ^ pow1 := by
      rw [mul_assoc, mul_comm, mul_assoc]
      congr! 1
      conv =>
        enter [1, 2]
        rw [← Real.rpow_one (Real.log x)]
      rw [← Real.rpow_add (Real.log_pos (by linarith))]
      ring_nf
    rw [this]

  have event_4_aux : ∀ᶠ (x : ℝ) in atTop,
      c₅ * rexp (σ₂ * Real.log x + (A ^ ((1 : ℝ) / (1 + n₁)) / 2) * Real.log x ^ ((1 : ℝ) / (1 + n₁))) ≤
      c₅ * rexp (Real.log x - (A ^ ((1 : ℝ) / (1 + n₁)) / 4) * Real.log x ^ ((1 : ℝ) / (1 + n₁))) := by
    filter_upwards [eventually_gt_atTop 3, event_4_aux1 σ₂InIoo.2 (A ^ ((1 : ℝ) / (1 + n₁)) / 2)
      (A ^ ((1 : ℝ) / (1 + n₁)) / 4) one_div_succ_n₁_lt_one] with x x_gt hx
    rw [mul_le_mul_iff_right₀ c₅pos]
    apply Real.exp_monotone
    convert hx

  have event_4 : ∀ᶠ (x : ℝ) in atTop, c₅ * x ^ σ₂ / (εx x) ≤
      c₅ * x * rexp (-c * Real.log x ^ ((1 : ℝ) / (1 + n₁))) := by
    unfold εx c_εx c
    filter_upwards [event_4_aux, eventually_gt_atTop 0] with x hx xpos
    convert hx using 1
    · rw [← mul_div]
      congr! 1
      rw [div_eq_mul_inv, ← Real.exp_neg]
      conv =>
        enter [1, 1, 1]
        rw [← Real.exp_log xpos]
      rw [← exp_mul, ← Real.exp_add]
      ring_nf
    · rw [mul_assoc]
      congr! 1
      conv =>
        enter [1, 1]
        rw [← Real.exp_log xpos]
      rw [← Real.exp_add]
      ring_nf

  filter_upwards [eventually_gt_atTop 3, eventually_εx_lt_one, eventually_2_lt,
    eventually_T_gt_3, eventually_T_gt_Tlb₄, eventually_T_gt_Tlb₆,
      eventually_σ₂_lt_σ₁, eventually_ε_lt_ε_main, event_logX_ge, event_1, event_2,
      event_3, event_4] with X X_gt_3 ε_lt_one ε_X T_gt_3 T_gt_Tlb₄ T_gt_Tlb₆
      σ₂_lt_σ₁ ε_lt_ε_main logX_ge event_1 event_2 event_3 event_4

  clear eventually_εx_lt_one eventually_2_lt eventually_T_gt_3 eventually_T_gt_Tlb₄
    eventually_T_gt_Tlb₆ eventually_σ₂_lt_σ₁ eventually_ε_lt_ε_main event_logX_ge

  let ε : ℝ := εx X
  have ε_pos : 0 < ε := by positivity
  specialize h_close X X_gt_3 ε ε_pos ε_lt_one ε_X
  let ψ_ε_of_X := SmoothedChebyshev ν ε X

  let T : ℝ := Tx X
  specialize holo1 T T_gt_3.le
  let σ₁ : ℝ := 1 - A / (Real.log T) ^ n₁
  have σ₁pos : 0 < σ₁ := by calc
    1 - A / (Real.log T) ^ n₁ >= 1 - (1/2) / 1 ^ n₁ := by
      gcongr
      · exact A_in_Ioc.2
      · exact (logt_gt_one T_gt_3.le).le
    _ > 0 := by norm_num
  have σ₁_lt_one : σ₁ < 1 := by
    apply sub_lt_self
    apply div_pos A_in_Ioc.1
    bound

  rw [uIcc_of_le (by linarith), uIcc_of_le (by linarith)] at holo2

  have holo2a : HolomorphicOn (SmoothedChebyshevIntegrand ν ε X)
      (Icc σ₂ 2 ×ℂ Icc (-3) 3 \ {1}) := by
    apply DifferentiableOn.mul
    · apply DifferentiableOn.mul
      · rw [(by ext; ring : (fun s ↦ -(deriv riemannZeta) s / riemannZeta s) = (fun s ↦ -((deriv riemannZeta) s / riemannZeta s)))]
        apply DifferentiableOn.neg holo2
      · intro s hs
        apply DifferentiableAt.differentiableWithinAt
        apply Smooth1MellinDifferentiable ContDiff1ν ν_supp ⟨ε_pos, ε_lt_one⟩ ν_nonneg ν_massOne
        linarith [mem_reProdIm.mp hs.1 |>.1.1, σ₂InIoo.1]
    · intro s hs
      apply DifferentiableAt.differentiableWithinAt
      apply DifferentiableAt.const_cpow (by fun_prop)
      left
      norm_cast
      linarith
  have ψ_ε_diff : ‖ψ_ε_of_X - mellin (fun x ↦ (Smooth1 ν ε x : ℂ)) 1 * X‖ ≤ ‖I₁ ν ε X T‖ + ‖I₂ ν ε T X σ₁‖
    + ‖I₃ ν ε T X σ₁‖ + ‖I₄ ν ε X σ₁ σ₂‖ + ‖I₅ ν ε X σ₂‖ + ‖I₆ ν ε X σ₁ σ₂‖ + ‖I₇ ν ε T X σ₁‖
    + ‖I₈ ν ε T X σ₁‖ + ‖I₉ ν ε X T‖ := by
    unfold ψ_ε_of_X
    rw [SmoothedChebyshevPull1 ε_pos ε_lt_one X X_gt_3 (T := T) (by linarith)
      σ₁pos σ₁_lt_one holo1 ν_supp ν_nonneg ν_massOne ContDiff1ν]
    rw [SmoothedChebyshevPull2 ε_pos ε_lt_one X X_gt_3 (T := T) (by linarith)
      σ₂InIoo.1 σ₁_lt_one σ₂_lt_σ₁ holo1 holo2a ν_supp ν_nonneg ν_massOne ContDiff1ν]
    ring_nf
    iterate 5
      apply le_trans (by apply norm_add_le)
      gcongr
    rw [(by ring : I₁ ν ε X T - I₂ ν ε T X σ₁ + I₃ ν ε T X σ₁ - I₄ ν ε X σ₁ σ₂ = (I₁ ν ε X T - I₂ ν ε T X σ₁) + (I₃ ν ε T X σ₁ - I₄ ν ε X σ₁ σ₂))]
    apply le_trans (by apply norm_add_le)
    rw [(by ring : ‖I₁ ν ε X T‖ + ‖I₂ ν ε T X σ₁‖ + ‖I₃ ν ε T X σ₁‖ + ‖I₄ ν ε X σ₁ σ₂‖ =
      (‖I₁ ν ε X T‖ + ‖I₂ ν ε T X σ₁‖) + (‖I₃ ν ε T X σ₁‖ + ‖I₄ ν ε X σ₁ σ₂‖))]
    gcongr <;> apply le_trans (by apply norm_sub_le) <;> rfl
  specialize h_main ε ⟨ε_pos, ε_lt_ε_main⟩
  have main : ‖mellin (fun x ↦ (Smooth1 ν ε x : ℂ)) 1 * X - X‖ ≤ C_main * ε * X := by
    nth_rewrite 2 [← one_mul X]
    push_cast
    rw [← sub_mul, norm_mul]
    gcongr
    rw [norm_real, norm_of_nonneg (by linarith)]
  specialize hc₁ ε ε_pos ε_lt_one X X_gt_3 T_gt_3
  specialize hc₂ X X_gt_3 ε_pos ε_lt_one T_gt_3
  specialize hc₃ X X_gt_3 ε_pos ε_lt_one T_gt_3
  specialize hc₅ X X_gt_3 ε_pos ε_lt_one
  specialize hc₇ X X_gt_3 ε_pos ε_lt_one T_gt_3
  specialize hc₈ X X_gt_3 ε_pos ε_lt_one T_gt_3
  specialize hc₉ ε_pos ε_lt_one X X_gt_3 T_gt_3
  specialize hc₄ X X_gt_3 ε_pos ε_lt_one T_gt_Tlb₄
  specialize hc₆ X X_gt_3 ε_pos ε_lt_one T_gt_Tlb₆

  clear ν_nonneg ν_massOne ContDiff1ν ν_supp holo2

  have C'bnd : c_close * ε * X * Real.log X + C_main * ε * X ≤ C' * ε * X * Real.log X := by
    have : C_main * ε * X * 1 ≤ C_main * ε * X * Real.log X := by
      gcongr
    linarith

  have C''bnd : c₁ * X * Real.log X / (ε * T) + c₂ * X / (ε * T) + c₈ * X / (ε * T)
    + c₉ * X * Real.log X / (ε * T) ≤ C'' * X * Real.log X / (ε * T) := by
    unfold C''
    rw [(by ring : (c₁ + c₂ + c₈ + c₉) * X * Real.log X / (ε * T)
      = c₁ * X * Real.log X / (ε * T) + c₂ * X * Real.log X / (ε * T)
        + c₈ * X * Real.log X / (ε * T) + c₉ * X * Real.log X / (ε * T))]
    have : c₂ * X / (ε * T) * 1 ≤ c₂ * X / (ε * T) * Real.log X := by
      gcongr
    have : c₂ * X / (ε * T) ≤ c₂ * X * Real.log X / (ε * T) := by
      ring_nf at this ⊢
      linarith
    grw [this]
    have : c₈ * X / (ε * T) * 1 ≤ c₈ * X / (ε * T) * Real.log X := by
      gcongr
    have : c₈ * X / (ε * T) ≤ c₈ * X * Real.log X / (ε * T) := by
      ring_nf at this ⊢
      linarith
    grw [this]

  have C'''bnd : c₃ * X * X ^ (-A / Real.log T ^ n₁) / ε
                    + c₄ * X * X ^ (-A / Real.log T ^ n₁) / ε
                    + c₆ * X * X ^ (-A / Real.log T ^ n₁) / ε
                    + c₇ * X * X ^ (-A / Real.log T ^ n₁) / ε
                  ≤ C''' * X * X ^ (-A / Real.log T ^ n₁) / ε := by
    apply le_of_eq
    ring

  calc
    _         = ‖(ψ X - ψ_ε_of_X) + (ψ_ε_of_X - X)‖ := by ring_nf; norm_cast
    _         ≤ ‖ψ X - ψ_ε_of_X‖ + ‖ψ_ε_of_X - X‖ := norm_add_le _ _
    _         = ‖ψ X - ψ_ε_of_X‖ + ‖(ψ_ε_of_X - mellin (fun x ↦ (Smooth1 ν ε x : ℂ)) 1 * X)
                  + (mellin (fun x ↦ (Smooth1 ν ε x : ℂ)) 1 * X - X)‖ := by ring_nf
    _         ≤ ‖ψ X - ψ_ε_of_X‖ + ‖ψ_ε_of_X - mellin (fun x ↦ (Smooth1 ν ε x : ℂ)) 1 * X‖
                  + ‖mellin (fun x ↦ (Smooth1 ν ε x : ℂ)) 1 * X - X‖ := by
                    rw [add_assoc]
                    gcongr
                    apply norm_add_le
    _         = ‖ψ X - ψ_ε_of_X‖ + ‖mellin (fun x ↦ (Smooth1 ν ε x : ℂ)) 1 * X - X‖
                  + ‖ψ_ε_of_X - mellin (fun x ↦ (Smooth1 ν ε x : ℂ)) 1 * X‖ := by ring
    _         ≤ ‖ψ X - ψ_ε_of_X‖ + ‖mellin (fun x ↦ (Smooth1 ν ε x : ℂ)) 1 * X - X‖
                  + (‖I₁ ν ε X T‖ + ‖I₂ ν ε T X σ₁‖ + ‖I₃ ν ε T X σ₁‖ + ‖I₄ ν ε X σ₁ σ₂‖
                  + ‖I₅ ν ε X σ₂‖ + ‖I₆ ν ε X σ₁ σ₂‖ + ‖I₇ ν ε T X σ₁‖ + ‖I₈ ν ε T X σ₁‖
                  + ‖I₉ ν ε X T‖) := by gcongr
    _         ≤ c_close * ε * X * Real.log X + C_main * ε * X
                  + (c₁ * X * Real.log X / (ε * T) + c₂ * X / (ε * T)
                  + c₃ * X * X ^ (-A / Real.log T ^ n₁) / ε
                  + c₄ * X * X ^ (-A / Real.log T ^ n₁) / ε
                  + c₅ * X ^ σ₂ / ε
                  + c₆ * X * X ^ (-A / Real.log T ^ n₁) / ε
                  + c₇ * X * X ^ (-A / Real.log T ^ n₁) / ε
                  + c₈ * X / (ε * T)
                  + c₉ * X * Real.log X / (ε * T)) := by
      gcongr
      convert! h_close using 1
      rw [← norm_neg]
      congr
      ring
    _         =  (c_close * ε * X * Real.log X + C_main * ε * X)
                  + ((c₁ * X * Real.log X / (ε * T) + c₂ * X / (ε * T)
                  + c₈ * X / (ε * T)
                  + c₉ * X * Real.log X / (ε * T))
                  + (c₃ * X * X ^ (-A / Real.log T ^ n₁) / ε
                  + c₄ * X * X ^ (-A / Real.log T ^ n₁) / ε
                  + c₆ * X * X ^ (-A / Real.log T ^ n₁) / ε
                  + c₇ * X * X ^ (-A / Real.log T ^ n₁) / ε)
                  + c₅ * X ^ σ₂ / ε
                  ) := by ring
    _         ≤ C' * ε * X * Real.log X
                  + (C'' * X * Real.log X / (ε * T)
                  + C''' * X * X ^ (-A / Real.log T ^ n₁) / ε
                  + c₅ * X ^ σ₂ / ε
                  ) := by
      gcongr
    _        = C' * ε * X * Real.log X
                  + C'' * X * Real.log X / (ε * T)
                  + C''' * X * X ^ (-A / Real.log T ^ n₁) / ε
                  + c₅ * X ^ σ₂ / ε
                    := by ring
    _        ≤ C' * X * rexp (-c * Real.log X ^ ((1 : ℝ) / (1 + n₁)))
                  + C'' * X * rexp (-c * Real.log X ^ ((1 : ℝ) / (1 + n₁)))
                  + C''' * X * rexp (-c * Real.log X ^ ((1 : ℝ) / (1 + n₁)))
                  + c₅ * X * rexp (-c * Real.log X ^ ((1 : ℝ) / (1 + n₁)))
                    := by
      gcongr
    _        = C * X * rexp (-c * Real.log X ^ ((1 : ℝ) / (1 + n₁)))
                    := by ring
    _        = _ := by
      rw [Real.norm_of_nonneg]
      · rw [← mul_assoc]
      · positivity

theorem MediumPNT : ∃ c > 0,
    (ψ - id) =O[atTop]
      fun (x : ℝ) ↦ x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)) := by
  have := GenStrengthPNT LogDerivZetaBoundedAndHolo99 (by linarith) (by linarith); ring_nf at this
  simpa only [gt_iff_lt, one_div, neg_mul] using this
end

/- Preliminaries for counting primes in logarithmically short intervals. -/
namespace H1ShortPrimes

open Filter Real Asymptotics

def PNTInput : Prop := ∃ c : ℝ, 0 < c ∧
    (Chebyshev.psi - id) =O[atTop]
      (fun x : ℝ => x * exp (-c * (log x) ^ ((1 : ℝ) / 10)))

private lemma log_exp_small {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) (B : ℕ) :
    ∀ᶠ x : ℝ in atTop, exp (-c*(log x)^(1/10:ℝ))*(log x)^B ≤ ε := by
  have hu := (tendsto_rpow_atTop (by norm_num : 0 < (1/10:ℝ))).comp tendsto_log_atTop
  have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (10*(B:ℝ)) c hc).comp hu
  filter_upwards [ht.eventually_le_const hε,tendsto_log_atTop.eventually_ge_atTop 0] with x hx hl
  change ((log x)^(1/10:ℝ))^(10*(B:ℝ)) * exp (-c*(log x)^(1/10:ℝ)) ≤ ε at hx
  rw [←rpow_mul hl, show (1/10:ℝ)*(10*(B:ℝ)) = B by ring,rpow_natCast] at hx
  simpa only [mul_comm] using hx

theorem theta_error (h : PNTInput) (B : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, |Chebyshev.theta x-x| *(log x)^B ≤ ε*x := by
  obtain ⟨c,hc,h⟩ := h
  obtain ⟨C,hC,hb⟩ := h.exists_pos
  have he := log_exp_small hc (div_pos hε (show 0 < 2*C by positivity)) B
  have hs := (isLittleO_log_rpow_rpow_atTop (B+1) (by norm_num : (0:ℝ)<1/2)).bound
    (by positivity : (0:ℝ) < ε/4)
  filter_upwards [hb.bound,he,hs,eventually_ge_atTop 2] with x hp he hs hx
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hl := log_nonneg hx1
  change ‖Chebyshev.psi x - x‖ ≤ C*‖x * exp (-c*(log x)^(1/10:ℝ))‖ at hp
  rw [Real.norm_eq_abs,Real.norm_eq_abs, abs_of_pos (mul_pos hx0 (Real.exp_pos _))] at hp
  change ‖(log x)^((B:ℝ)+1)‖ ≤ ε/4*‖x^(1/2:ℝ)‖ at hs
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (by positivity),
    abs_of_nonneg (by positivity),] at hs
  have hs' : (log x)^(B+1) ≤ ε/4*√x := by
    rw [show (B:ℝ)+1 = ((B+1:ℕ):ℝ) by push_cast; ring, Real.rpow_natCast,←sqrt_eq_rpow] at hs
    exact hs
  have hψ : |Chebyshev.psi x-x| *(log x)^B ≤ (ε/2)*x := calc
    _ ≤ (C*(x*exp (-c*(log x)^(1/10:ℝ))))*(log x)^B :=
      mul_le_mul_of_nonneg_right hp (pow_nonneg hl _)
    _ = (C*x)*(exp (-c*(log x)^(1/10:ℝ))*(log x)^B) := by ring
    _ ≤ (C*x)*(ε/(2*C)) := mul_le_mul_of_nonneg_left he (by positivity)
    _ = _ := by field_simp
  have hθ := Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log hx1
  have hsqrt : (2*√x*log x)*(log x)^B ≤ (ε/2)*x := calc
    _ = 2*√x*(log x)^(B+1) := by rw [pow_succ]; ring
    _ ≤ 2*√x*(ε/4*√x) := mul_le_mul_of_nonneg_left hs' (by positivity)
    _ = _ := by nlinarith [Real.sq_sqrt hx0.le]
  have htri : |Chebyshev.theta x-x| ≤ |Chebyshev.psi x-Chebyshev.theta x|+
      |Chebyshev.psi x-x| := by
    rw [abs_sub_comm (Chebyshev.psi x) (Chebyshev.theta x)]
    exact abs_sub_le _ _ _
  have hmul := mul_le_mul_of_nonneg_right htri (pow_nonneg hl B)
  have ha := (mul_le_mul_of_nonneg_right hθ (pow_nonneg hl B)).trans hsqrt
  linarith

noncomputable def width (B : ℕ) (x : ℝ) := x / (log x)^B

noncomputable def shortBand (n B : ℕ) :=
  (Nat.primesLE ⌊(n:ℝ)+width B n⌋₊) \ Nat.primesLE n

theorem short_supply (H : PNTInput) (B : ℕ) :
    ∀ᶠ n : ℕ in atTop, width B n ≤ 4*(shortBand n B).card*log n := by
  have ht := theta_error H B (by norm_num : (0:ℝ) < 1/8)
  have cast : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  obtain ⟨T,hT⟩ := eventually_atTop.mp ht
  filter_upwards [cast.eventually_ge_atTop T,(tendsto_log_atTop.comp cast).eventually_ge_atTop 1,
    eventually_ge_atTop 2] with n hn hl hn2
  have hnR : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
  change 1 ≤ log (n:ℝ) at hl
  let w := width B n
  let y := (n:ℝ)+w
  have hpow : 1 ≤ (log (n:ℝ))^B := one_le_pow₀ hl
  have hw : 0 < w := by dsimp [w,width]; positivity
  have hw' : w ≤ n := (div_le_self hnR.le hpow)
  have hny : (n:ℝ) ≤ y := by dsimp [y]; linarith
  have hy2 : y ≤ 2*(n:ℝ) := by dsimp [y]; linarith
  have hyl : log (n:ℝ) ≤ log y := log_le_log hnR hny
  have h1 := hT n hn
  have h2 := hT y (hn.trans hny)
  have h1' : |Chebyshev.theta n - n| ≤ w/8 := by
    dsimp [w,width]; rw [div_div, le_div_iff₀ (by positivity)]; linarith
  have h2' : |Chebyshev.theta y - y| ≤ w/4 := by
    dsimp [w,width]; rw [div_div, le_div_iff₀ (by positivity)]
    have hlog := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by linarith : 0 ≤ log (n:ℝ)) hyl B) (abs_nonneg (Chebyshev.theta y-y))
    linarith
  have hd : w/2 ≤ Chebyshev.theta y - Chebyshev.theta n := by
    have hy : y = (n:ℝ)+w := rfl
    linarith [(abs_le.mp h1').2,(abs_le.mp h2').1]
  have hs : Nat.primesLE n ⊆ Nat.primesLE ⌊y⌋₊ := by
    intro p hp
    obtain ⟨hle,hpr⟩ := Nat.mem_primesLE.mp hp
    exact Nat.mem_primesLE.mpr ⟨hle.trans (Nat.le_floor hny),hpr⟩
  have hsum : Chebyshev.theta y - Chebyshev.theta n =
      ∑ p ∈ shortBand n B, log (p:ℝ) := by
    rw [Chebyshev.theta_eq_sum_primesLE,Chebyshev.theta_eq_sum_primesLE_log]
    exact sub_eq_of_eq_add (Finset.sum_sdiff hs).symm
  have hlog' : log y ≤ 2*log n := calc
    _ ≤ log (2*(n:ℝ)) := log_le_log (hnR.trans_le hny) hy2
    _ ≤ _ := by
      rw [log_mul (by norm_num) hnR.ne']
      linarith [log_le_log (by norm_num : (0:ℝ)<2) (by exact_mod_cast hn2 : (2:ℝ) ≤ n)]
  have hsum' : (∑ p ∈ shortBand n B, log (p:ℝ)) ≤ (shortBand n B).card*(2*log n) := calc
    _ ≤ ∑ _p ∈ shortBand n B, 2*log n := Finset.sum_le_sum fun p hp => by
      obtain ⟨hp',_⟩ := Finset.mem_sdiff.mp hp
      obtain ⟨hle,hpr⟩ := Nat.mem_primesLE.mp hp'
      exact (log_le_log (by exact_mod_cast hpr.pos)
        ((Nat.cast_le.mpr hle).trans (Nat.floor_le (hnR.trans_le hny).le))).trans hlog'
    _ = _ := by simp
  change w ≤ _
  linarith

end H1ShortPrimes

namespace H1PrimeSupply

theorem supply (B : ℕ) : ∀ᶠ n : ℕ in Filter.atTop,
    H1ShortPrimes.width B n ≤ 4*(H1ShortPrimes.shortBand n B).card*Real.log n :=
  H1ShortPrimes.short_supply MediumPNT B

end H1PrimeSupply

theorem OMA.PNT.h1 (δ : ℝ) (hδ : 0<δ) : ∃ T : ℕ, ∀ n : ℕ, T≤n →
    ∃ p : ℕ, p.Prime ∧ n<p ∧ (p:ℝ) ≤ (1+δ)*(n:ℝ) := by
  have cast : Filter.Tendsto (fun n : ℕ => (n:ℝ)) Filter.atTop Filter.atTop := tendsto_natCast_atTop_atTop
  apply Filter.eventually_atTop.mp
  filter_upwards [H1PrimeSupply.supply 1,(Real.tendsto_log_atTop.comp cast).eventually_ge_atTop (δ⁻¹+1),
    Filter.eventually_ge_atTop 2] with n h hl hn
  change δ⁻¹+1 ≤ Real.log (n:ℝ) at hl
  have hh : 0 < Real.log (n:ℝ) := by linarith [inv_pos.mpr hδ]
  let w := H1ShortPrimes.width 1 n
  have hw : 0<w := by dsimp [w,H1ShortPrimes.width]; positivity
  have hc : 0<(H1ShortPrimes.shortBand n 1).card := by
    by_contra! hz
    have hz' : (H1ShortPrimes.shortBand n 1).card=0 := by omega
    rw [hz'] at h
    simp only [Nat.cast_zero,mul_zero,zero_mul] at h
    change w ≤ 0 at h
    linarith
  obtain ⟨p,hp⟩ := Finset.card_pos.mp hc
  obtain ⟨hpy,hpn⟩ := Finset.mem_sdiff.mp hp
  obtain ⟨hle,hpr⟩ := Nat.mem_primesLE.mp hpy
  have hp' : n<p := by by_contra! he; exact hpn (Nat.mem_primesLE.mpr ⟨he,hpr⟩)
  have hscale : w≤δ*n := by
    dsimp [w,H1ShortPrimes.width]; rw [pow_one,div_le_iff₀ hh]
    have hh' := mul_le_mul_of_nonneg_left (show δ⁻¹≤Real.log (n:ℝ) by linarith) hδ.le
    rw [mul_inv_cancel₀ hδ.ne'] at hh'
    nlinarith only [mul_le_mul_of_nonneg_right hh' (Nat.cast_nonneg n)]
  refine ⟨p,hpr,hp',?_⟩
  have hcast := (Nat.cast_le.mpr hle : (p:ℝ) ≤ ⌊(n:ℝ)+w⌋₊)
  have htop := hcast.trans (Nat.floor_le (by positivity))
  nlinarith

namespace OMA.Erdos137Low

/-- Every prime power in a binomial coefficient is bounded by its top index. -/
lemma choose_upper {N w b : ℕ} (hN : 0 < N) (hw : w ≤ N)
    (hall : ∀ p ∈ (N.choose w).primeFactors, p ≤ b) :
    N.choose w ≤ N ^ Nat.primeCounting b := by
  have hnz := (Nat.choose_pos hw).ne'
  have hsub : (N.choose w).primeFactors ⊆ Nat.primesLE b := fun p hp =>
    Nat.mem_primesLE.mpr ⟨hall p hp, Nat.prime_of_mem_primeFactors hp⟩
  calc
    N.choose w = ∏ p ∈ (N.choose w).primeFactors, p ^ (N.choose w).factorization p :=
      (Nat.prod_factorization_pow_eq_self hnz).symm
    _ ≤ ∏ _p ∈ (N.choose w).primeFactors, N :=
      Finset.prod_le_prod' fun _ _ => Nat.pow_factorization_choose_le hN
    _ = N ^ (N.choose w).primeFactors.card := Finset.prod_const _
    _ ≤ N ^ Nat.primeCounting b := Nat.pow_le_pow_right hN
      (by simpa only [Nat.primesLE_card_eq_primeCounting] using Finset.card_le_card hsub)

/-- Compare the descending product with its smallest factor, and bound the factorial by w^w. -/
lemma choose_lower {t w K : ℕ} (hw : 0 < w) (hK : K * w ≤ t) :
    K ^ w ≤ (t + w).choose w := by
  have h1 := Nat.pow_sub_le_descFactorial (t + w) w
  rw [Nat.descFactorial_eq_factorial_mul_choose] at h1
  have h2 : (K * w) ^ w ≤ (t + w + 1 - w) ^ w :=
    Nat.pow_le_pow_left (by omega) w
  rw [mul_pow] at h2
  have h3 := Nat.mul_le_mul_right ((t + w).choose w) (Nat.factorial_le_pow w)
  have h4 : w ^ w * K ^ w ≤ w ^ w * (t + w).choose w := by
    rw [Nat.mul_comm (w ^ w) (K ^ w)]
    exact h2.trans (h1.trans h3)
  exact Nat.le_of_mul_le_mul_left h4 (pow_pos hw w)

lemma of_large_factor {t w b p : ℕ} (hbig : b < p)
    (hp : p ∈ ((t+w).choose w).primeFactors) :
    ∃ x q : ℕ, t < x ∧ x ≤ t+w ∧ b < q ∧ q.Prime ∧ q ∣ x := by
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hd : p ∣ (t+w).descFactorial w := by
    rw [Nat.descFactorial_eq_factorial_mul_choose]
    exact Dvd.dvd.mul_left (Nat.dvd_of_mem_primeFactors hp) _
  rw [Nat.descFactorial_eq_prod_range] at hd
  obtain ⟨i, hi, hpi⟩ := (hprime.prime.dvd_finsetProd_iff _).mp hd
  rw [Finset.mem_range] at hi
  exact ⟨t+w-i, p, by omega, by omega, hbig, hprime, hpi⟩

theorem low_height : ∀ a : ℕ, 0 < a → ∀ᶠ b in Filter.atTop, ∀ t : ℕ, b ≤ t → t + b / a ≤ b ^ 2 →
    ∃ x p : ℕ, t < x ∧ x ≤ t + b / a ∧ b < p ∧ p.Prime ∧ p ∣ x := by
  intro a ha
  let C : ℝ := Real.log 4 + 1
  have hC : 0 < C := by dsimp [C]; positivity
  obtain ⟨K, hK⟩ := exists_nat_gt (Real.exp (4 * (a : ℝ) * C))
  have hKpos : 0 < (K : ℝ) := (Real.exp_pos _).trans hK
  have hlogK : 4 * (a : ℝ) * C < Real.log K := by
    simpa using Real.log_lt_log (Real.exp_pos _) hK
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha
  let δ : ℝ := 1 / (2 * a * K)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨T, hT⟩ := OMA.PNT.h1 δ hδ
  have hcast : Filter.Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop := tendsto_natCast_atTop_atTop
  have hpc := hcast.eventually
    (Chebyshev.eventually_primeCounting_le (ε := 1) (by norm_num))
  filter_upwards [hpc, Filter.eventually_ge_atTop (max (max T a) 2)] with b hπ hb
  intro t hbt htop
  let w := b / a
  have hw : 0 < w := Nat.div_pos (by omega) ha
  have hwb : w ≤ b := Nat.div_le_self _ _
  have hround : b ≤ 2 * a * w := by
    have h1 : b < a * (w + 1) := Nat.lt_mul_div_succ b ha
    have h2 := Nat.mul_le_mul_left a (show w + 1 ≤ 2*w by omega)
    nlinarith only [h1, h2]
  have hroundR : (b : ℝ) ≤ 2 * a * w := by exact_mod_cast hround
  by_cases ht : t ≤ K * b
  · obtain ⟨p, hp, htp, hpend⟩ := hT t (by omega)
    have hscale : (t : ℝ) ≤ (2 * (a : ℝ) * K) * w := calc
      (t : ℝ) ≤ K * (b : ℝ) := by exact_mod_cast ht
      _ ≤ K * (2 * (a : ℝ) * w) := mul_le_mul_of_nonneg_left hroundR hKpos.le
      _ = _ := by ring
    have hstep : δ * (t : ℝ) ≤ w := by
      dsimp [δ]
      rw [one_div, ← div_eq_inv_mul]
      exact (div_le_iff₀ (by positivity)).mpr (by nlinarith only [hscale])
    refine ⟨p, p, htp, ?_, hbt.trans_lt htp, hp, dvd_rfl⟩
    change p ≤ t + w
    exact_mod_cast (show (p : ℝ) ≤ t + (w : ℝ) by nlinarith only [hpend, hstep])
  · by_contra hnone
    have hmax (p : ℕ) (hp : p ∈ ((t+w).choose w).primeFactors) : p ≤ b :=
      le_of_not_gt fun h => hnone (of_large_factor h hp)
    have hlow := choose_lower hw ((Nat.mul_le_mul_left K hwb).trans (by omega : K*b ≤ t))
    have hupp := choose_upper (by omega : 0 < t+w) (by omega : w ≤ t+w) hmax
    have hpow : K ^ w ≤ (b ^ 2) ^ Nat.primeCounting b :=
      hlow.trans (hupp.trans (Nat.pow_le_pow_left htop _))
    have hpR : (K : ℝ) ^ w ≤ ((b : ℝ) ^ 2) ^ Nat.primeCounting b := by exact_mod_cast hpow
    have hlog := Real.log_le_log (pow_pos hKpos w) hpR
    simp only [Real.log_pow] at hlog
    change (Nat.primeCounting ⌊(b : ℝ)⌋₊ : ℝ) ≤ C * b / Real.log b at hπ
    rw [Nat.floor_natCast] at hπ
    have hbR : (1 : ℝ) < b := by exact_mod_cast (show 1 < b by omega)
    have hπ' := (le_div_iff₀ (Real.log_pos hbR)).mp hπ
    have hbad := mul_lt_mul_of_pos_left hlogK (show 0 < (w : ℝ) by exact_mod_cast hw)
    have hroundC := mul_le_mul_of_nonneg_left hroundR hC.le
    norm_num at hlog
    nlinarith only [hlog, hπ', hbad, hroundC]

end OMA.Erdos137Low

/- An unconditional cubic-height case of the long-block conjecture.
Above the square threshold a binomial coefficient forces many distinct prime divisors.
If a prime p larger than the interval length occurs twice, its unique multiple is d*p^2.
The same d cannot account for two such primes, since successive squares are too far apart. -/

namespace Erdos137Cubic

open OMA.R_Erdos137_erdos_137_variants_multiple_powerful_factors_R2

lemma square_count {m n b Q : ℕ} {s : Finset ℕ} (hb : 0 < b) (hnb : n ≤ b) (ht : m+n ≤ b^2*Q)
    (hlarge : ∀ p ∈ s, b < p)
    (hw : ∀ p ∈ s, ∃ d : ℕ, m < p^2*d ∧ p^2*d ≤ m+n) :
    s.card ≤ Q := by
  classical
  choose d hleft hright using (fun p : s => hw p p.property)
  have hpos (p : s) : 0 < d p := by
    by_contra! h
    have hz : d p = 0 := by omega
    have := hleft p
    simp [hz] at this
  have hle (p : s) : d p ≤ Q := by
    have hbig := hlarge p p.property
    have hprod := Nat.mul_le_mul_right (d p) (Nat.pow_le_pow_left hbig.le 2)
    exact Nat.le_of_mul_le_mul_left (hprod.trans ((hright p).trans ht)) (pow_pos hb _)
  let f (p : s) : Fin Q := ⟨d p - 1, by have := hpos p; have := hle p; omega⟩
  have different (p q : s) (hpq : (p : ℕ) < q) (heq : d p = d q) : False := by
    have hp := hnb.trans_lt (hlarge p p.property)
    have hgap : (p : ℕ)^2+(n+1) ≤ (q : ℕ)^2 := by
      nlinarith only [Nat.mul_self_le_mul_self (show (p : ℕ)+1 ≤ q by omega),hp]
    have hg := Nat.mul_le_mul_right (d p) hgap
    rw [Nat.add_mul] at hg
    have hh : n+1 ≤ (n+1)*d p := Nat.le_mul_of_pos_right _ (hpos p)
    have h1 := hleft p
    have h2 := hright q
    rw [← heq] at h2
    omega
  have hinj : Function.Injective f := by
    intro p q h
    have h' : d p - 1 = d q - 1 := congrArg Fin.val h
    have he : d p = d q := by have := hpos p; have := hpos q; omega
    apply Subtype.ext
    rcases lt_trichotomy (p : ℕ) q with hlt | heq | hgt
    · exact (different p q hlt he).elim
    · exact heq
    · exact (different q p hgt he.symm).elim
  simpa using Fintype.card_le_of_injective f hinj

lemma large_support {m n : ℕ} (hn : 8 ≤ n) (hl : n^2 < m+n) (hu : m+n ≤ n^4) :
    n ≤ 8 * ((m+n).choose n).primeFactors.card := by
  let B := (m+n).choose n
  let F := B.primeFactors
  have hn' : 1 < n := by omega
  have hhalf : n ≤ (n/2)^2 := by
    have ha : 3 ≤ n/2 := by omega
    have hb : n ≤ 2*(n/2)+1 := by omega
    nlinarith only [ha, hb, Nat.mul_le_mul_left (n/2) ha]
  have hsmall : n/2*n ≤ m := by
    have h1 : n/2+1 ≤ n := by omega
    nlinarith only [Nat.mul_le_mul_right n h1, hl]
  have hlow := OMA.Erdos137Low.choose_lower (by omega : 0 < n) hsmall
  have hupper : B ≤ (m+n)^F.card := calc
    B = ∏ p ∈ F, p ^ B.factorization p :=
      (Nat.prod_factorization_pow_eq_self (Nat.choose_pos (by omega : n ≤ m+n)).ne').symm
    _ ≤ ∏ _p ∈ F, (m+n) :=
      Finset.prod_le_prod' fun p _ => Nat.pow_factorization_choose_le (by omega)
    _ = _ := Finset.prod_const _
  have hpow : n ^ n ≤ n ^ (8 * F.card) := calc
    n^n ≤ ((n/2)^2)^n := Nat.pow_le_pow_left hhalf _
    _ = ((n/2)^n)^2 := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    _ ≤ B^2 := Nat.pow_le_pow_left hlow _
    _ ≤ ((n^4)^F.card)^2 := Nat.pow_le_pow_left
      (hupper.trans (Nat.pow_le_pow_left hu _)) _
    _ = n^(8*F.card) := by rw [← pow_mul, ← pow_mul]; congr 1; ring
  exact le_of_not_gt fun h => (Nat.pow_lt_pow_right hn' h).not_ge hpow

lemma term_of_factor {m n p : ℕ} (hp : p ∈ ((m+n).choose n).primeFactors) :
    ∃ x ∈ Finset.Ioc m (m+n), p ∣ x := by
  have hd : p ∣ (m+n).descFactorial n := by
    rw [Nat.descFactorial_eq_factorial_mul_choose]
    exact Dvd.dvd.mul_left (Nat.dvd_of_mem_primeFactors hp) _
  rw [Nat.descFactorial_eq_prod_range] at hd
  obtain ⟨i, hi, hpi⟩ := ((Nat.prime_of_mem_primeFactors hp).prime.dvd_finsetProd_iff _).mp hd
  rw [Finset.mem_range] at hi
  exact ⟨m+n-i, Finset.mem_Ioc.mpr ⟨by omega, by omega⟩, hpi⟩

lemma high_interval {m n b k Q : ℕ} (hn : 8 ≤ n) (hnb : n ≤ b) (hlo : n^2 < m+n)
    (hhi : m+n ≤ n^4) (hq : m+n ≤ b^2*Q)
    (hcount : 8 * (Nat.primeCounting b + Q + k) ≤ n) :
    ∃ P : Finset ℕ, P.card = k ∧ ∀ p ∈ P, p.Prime ∧
      p ∣ (∏ x ∈ Finset.Ioc m (m+n), x) ∧ ¬ p^2 ∣ (∏ x ∈ Finset.Ioc m (m+n), x) := by
  classical
  let F := ((m+n).choose n).primeFactors
  let s := F.filter (fun p => p ≤ b)
  let L := F.filter (fun p => ¬p ≤ b)
  let repeated (p : ℕ) := ∃ x ∈ Finset.Ioc m (m+n), p^2 ∣ x
  let bad := L.filter repeated
  let good := L.filter (fun p => ¬repeated p)
  have hs : s.card ≤ Nat.primeCounting b := by
    rw [← Nat.primesLE_card_eq_primeCounting]
    apply Finset.card_le_card
    intro p hp
    obtain ⟨hp,hpn⟩ := Finset.mem_filter.mp hp
    exact Nat.mem_primesLE.mpr ⟨hpn,Nat.prime_of_mem_primeFactors hp⟩
  have hb : bad.card ≤ Q := by
    apply square_count (m := m) (n := n) (by omega) hnb hq
    · intro p hp
      exact lt_of_not_ge (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
    · intro p hp
      obtain ⟨x,hx,d,hd⟩ := (Finset.mem_filter.mp hp).2
      obtain ⟨hl,hr⟩ := Finset.mem_Ioc.mp hx
      exact ⟨d,hd ▸ hl,hd ▸ hr⟩
  have hsplit : s.card + L.card = F.card := Finset.card_filter_add_card_filter_not ..
  have hsplit' : bad.card + good.card = L.card := Finset.card_filter_add_card_filter_not ..
  have hF : n ≤ 8*F.card := large_support hn hlo hhi
  obtain ⟨P,hsub,hcard⟩ := Finset.exists_subset_card_eq (show k ≤ good.card by omega)
  refine ⟨P,hcard,?_⟩
  intro p hp
  obtain ⟨hpL,hgood⟩ := Finset.mem_filter.mp (hsub hp)
  obtain ⟨hpF,hpn⟩ := Finset.mem_filter.mp hpL
  obtain ⟨x,hx,hd⟩ := term_of_factor hpF
  have hprime := Nat.prime_of_mem_primeFactors hpF
  exact ⟨hprime,transfer_factor (Or.inl (hnb.trans (le_of_lt (lt_of_not_ge hpn)))) hx hprime hd
    (fun h => hgood ⟨x,hx,h⟩)⟩

/-- The packing argument in the first reduction, with its square-threshold hypothesis discharged. -/
theorem low_interval (k : ℕ) : ∀ᶠ n in Filter.atTop, ∀ m : ℕ, 0 < m → m+n ≤ n^2 →
    ∃ P : Finset ℕ, P.card = k ∧ ∀ p ∈ P, p.Prime ∧
      p ∣ (∏ x ∈ Finset.Ioc m (m+n), x) ∧ ¬ p^2 ∣ (∏ x ∈ Finset.Ioc m (m+n), x) := by
  classical
  obtain ⟨B,hB⟩ := Filter.eventually_atTop.1 (OMA.Erdos137Low.low_height (k+1) (by omega))
  apply Filter.eventually_atTop.2
  refine ⟨max (2*B) 8, ?_⟩
  intro n hn m hm hwhole
  let b := min n ((m + n) / 2)
  let s := m + n - b
  let w := b / (k + 1)
  have hbn : b ≤ n := min_le_left _ _
  have hbh : b ≤ (m + n) / 2 := min_le_right _ _
  have hBb : B ≤ b := le_min (by omega) (by omega)
  have hsb : b ≤ s := by dsimp [s]; omega
  have hsm : m ≤ s := by dsimp [s]; omega
  have htop : s + b = m + n := by dsimp [s]; omega
  have hthreshold : m+n ≤ b^2 := by
    by_cases h : n ≤ (m+n)/2
    · simpa [b,min_eq_left h] using hwhole
    · have heq : b = (m+n)/2 := min_eq_right (by omega)
      have hge : 3 ≤ b := by omega
      have hmax : m+n ≤ 2*b+1 := by omega
      nlinarith only [Nat.mul_le_mul_right b hge,hge,hmax]
  have hblock (t : ℕ) (ht : b ≤ t) (hfit : t+w ≤ m+n) :
      ∃ x p : ℕ, t < x ∧ x ≤ t+w ∧ b < p ∧ p.Prime ∧ p ∣ x ∧ ¬ p^2 ∣ x := by
    obtain ⟨x,p,hx,hx',hb,hp,hd⟩ := hB b hBb t ht (hfit.trans hthreshold)
    refine ⟨x,p,hx,hx',hb,hp,hd,?_⟩
    intro h
    have h1 := Nat.le_of_dvd (by omega : 0 < x) h
    have h2 : b^2 < p^2 := Nat.pow_lt_pow_left hb (by decide)
    omega
  have hpack : k * w ≤ b := calc
    k * w ≤ (k + 1) * w := Nat.mul_le_mul_right w (by omega)
    _ ≤ b := by simpa [w, Nat.mul_comm] using Nat.div_mul_le_self b (k + 1)
  have hblocks (i : Fin k) := hblock (s + i.val * w) (by omega) (by
    have hi := (Nat.mul_le_mul_right w (Nat.succ_le_of_lt i.isLt)).trans hpack
    rw [Nat.succ_mul] at hi
    omega)
  choose x p hleft hright hbig hprime hd hsq using hblocks
  have hmem (i : Fin k) : x i ∈ Finset.Ioc m (m + n) := by
    have hstop := Nat.mul_le_mul_right w (Nat.succ_le_of_lt i.isLt)
    rw [Nat.succ_mul] at hstop
    exact Finset.mem_Ioc.mpr ⟨by have := hleft i; omega, by have := hright i; omega⟩
  have hsize (i : Fin k) : n ≤ p i ∨ m + n < 2 * p i := by
    have hi := hbig i
    by_cases h : n ≤ (m + n) / 2
    · rw [show b = n from min_eq_left h] at hi
      exact Or.inl (by omega)
    · rw [show b = (m + n) / 2 from min_eq_right (by omega)] at hi
      exact Or.inr (by omega)
  have hmono : StrictMono x := by
    intro i j hij
    have hstep := Nat.mul_le_mul_right w (Nat.succ_le_of_lt (show i.val < j.val from hij))
    rw [Nat.succ_mul] at hstep
    have hi := hright i
    have hj := hleft j
    omega
  have hinj : Function.Injective p := by
    intro i j heq
    exact hmono.injective (unique_multiple (hsize i) (hmem i) (hmem j) (hd i) (heq ▸ hd j))
  refine ⟨Finset.univ.image p, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  · intro q hq
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hq
    exact ⟨hprime i, transfer_factor (hsize i) (hmem i) (hprime i) (hd i) (hsq i)⟩

/-- A convenient natural-number form of the elementary prime-counting upper estimate. -/
lemma sparse_primes (M : ℕ) : ∀ᶠ n : ℕ in Filter.atTop, M * Nat.primeCounting n ≤ n := by
  have hcast : Filter.Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop
  have hpc := hcast.eventually (Chebyshev.eventually_primeCounting_le (ε := 1) (by norm_num))
  have hlog := (Real.tendsto_log_atTop.comp hcast).eventually_ge_atTop ((M : ℝ)*(Real.log 4+1))
  filter_upwards [hpc,hlog,Filter.eventually_ge_atTop 2] with n hp hl hn
  have hlogpos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  change (M : ℝ)*(Real.log 4+1) ≤ Real.log (n : ℝ) at hl
  change (Nat.primeCounting ⌊(n : ℝ)⌋₊ : ℝ) ≤ (Real.log 4+1) * n / Real.log n at hp
  rw [Nat.floor_natCast] at hp
  have hp' := (le_div_iff₀ hlogpos).mp hp
  have hlt := mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg (Nat.primeCounting n) : (0:ℝ) ≤ _)
  have hpos : 0 < Real.log 4+1 := by positivity
  exact_mod_cast (le_of_mul_le_mul_right (a := Real.log 4+1) (b := (M : ℝ)*Nat.primeCounting n)
    (c := (n : ℝ)) (by nlinarith only [hp',hlt]) hpos)

/-- For each fixed multiplier A and requested count k, the full exponent-one conclusion
holds for every sufficiently long interval ending at most A times the cube of its length. -/
theorem cubic_height (A k : ℕ) : ∀ᶠ n in Filter.atTop, ∀ m : ℕ, 0 < m → m+n ≤ A*n^3 →
    ∃ P : Finset ℕ, P.card = k ∧ ∀ p ∈ P, p.Prime ∧
      p ∣ (∏ x ∈ Finset.Ioc m (m+n), x) ∧ ¬ p^2 ∣ (∏ x ∈ Finset.Ioc m (m+n), x) := by
  let C := 32*(A+1)
  have hc : 0 < C := by dsimp [C]; omega
  obtain ⟨T,hT⟩ := Filter.eventually_atTop.1 (sparse_primes (C*32))
  filter_upwards [low_interval k,Filter.eventually_ge_atTop (max (max T A) (32*(k+1)))] with n low hn
  intro m hm ht
  by_cases h : m+n ≤ n^2
  · exact low m hm h
  have hnb : n ≤ C*n := Nat.le_mul_of_pos_left _ hc
  have hπ : 32*Nat.primeCounting (C*n) ≤ n := by
    apply Nat.le_of_mul_le_mul_left (c := C) _ hc
    simpa [Nat.mul_assoc] using hT (C*n) (by omega)
  have hhi : m+n ≤ n^4 := calc
    m+n ≤ A*n^3 := ht
    _ ≤ n*n^3 := Nat.mul_le_mul_right _ (by omega)
    _ = _ := by ring
  apply high_interval (b := C*n) (Q := n/32+1) (by omega) hnb (by omega) hhi ?_ (by omega)
  have hr : n ≤ 32*(n/32+1) := by omega
  have hcoeff : 32*A ≤ C^2 := calc
    32*A ≤ C := by dsimp [C]; omega
    _ ≤ C^2 := Nat.le_self_pow (by decide) _
  have hm' : 32*(m+n) ≤ 32*((C*n)^2*(n/32+1)) := calc
    32*(m+n) ≤ 32*(A*n^3) := Nat.mul_le_mul_left _ ht
    _ = (32*A)*n^2*n := by ring
    _ ≤ C^2*n^2*n := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hcoeff)
    _ ≤ C^2*n^2*(32*(n/32+1)) := Nat.mul_le_mul_left _ hr
    _ = _ := by ring
  omega

end Erdos137Cubic

/- Divided differences on integer nodes, for a reciprocal and a squared reciprocal. -/
namespace H1Divided

noncomputable def dd (u : ℕ → ℕ) (v : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, i => v i
  | r+1, i => (dd u v r (i+1)-dd u v r i) / ((u (i+r+1):ℝ) - u i)

private lemma gap_ge {u : ℕ → ℕ} (hu : StrictMono u) (i r : ℕ) :
    (1:ℝ) ≤ (u (i+r+1):ℝ) - u i := by
  have h := hu (show i < i+r+1 by omega)
  have h' : u i+1 ≤ u (i+r+1) := h
  have hc : (u i:ℝ)+1 ≤ u (i+r+1) := by exact_mod_cast h'
  linarith

theorem error_bound {u : ℕ → ℕ} (hu : StrictMono u) (v z : ℕ → ℝ) (δ : ℝ)
    (r i : ℕ) (h : ∀ k ≤ r, |v (i+k)-z (i+k)| ≤ δ) :
    |dd u v r i-dd u z r i| ≤ 2^r*δ := by
  induction r generalizing i with
  | zero => simpa [dd] using h 0 (by omega)
  | succ r ih =>
    let g := (u (i+r+1):ℝ) - u i
    have hg : 1 ≤ g := gap_ge hu _ _
    have h1 := ih (i+1) (by
      intro k hk
      rw [show i+1+k=i+(k+1) by omega]
      exact h (k+1) (by omega))
    have h0 := ih i (fun k hk => h k (by omega))
    have hid : dd u v (r+1) i-dd u z (r+1) i =
        ((dd u v r (i+1)-dd u z r (i+1))-(dd u v r i-dd u z r i))/g := by
      simp only [dd,g]; ring
    rw [hid,abs_div,abs_of_pos (by linarith : 0 < g)]
    refine (div_le_self (abs_nonneg _) hg).trans ?_
    exact (abs_sub _ _).trans (by rw [pow_succ]; linarith only [h1,h0])

theorem integral_scaled {u : ℕ → ℕ} (hu : StrictMono u) (z : ℕ → ℤ) (L : ℕ)
    (r i : ℕ) (h : ∀ a b : ℕ, i ≤ a → a < b → b ≤ i+r → u b-u a ∣ L) :
    ∃ w : ℤ, (L:ℝ)^r * dd u (fun j => (z j:ℝ)) r i = w := by
  induction r generalizing i with
  | zero => exact ⟨z i,by simp [dd]⟩
  | succ r ih =>
    obtain ⟨z1,h1⟩ := ih (i+1) (fun a b ha hab hb => h a b (by omega) hab (by omega))
    obtain ⟨z0,h0⟩ := ih i (fun a b ha hab hb => h a b ha hab (by omega))
    obtain ⟨q,hq⟩ := h i (i+r+1) (by omega) (by omega) (by omega)
    have hnat := hu (show i < i+r+1 by omega)
    have hqR : (L:ℝ) = ((u (i+r+1):ℝ)-u i)*q := by
      rw [←Nat.cast_sub hnat.le, ←Nat.cast_mul, hq]
    have hg : (u (i+r+1):ℝ)-u i ≠ 0 := by have := gap_ge hu i r; linarith
    refine ⟨(q:ℤ)*(z1-z0),?_⟩
    push_cast
    simp only [dd,pow_succ]
    rw [mul_div_assoc',div_eq_iff hg,←h1,←h0]
    linear_combination ((L:ℝ)^r*(dd u (fun j => (z j:ℝ)) r (i+1) - dd u (fun j => (z j:ℝ)) r i)) * hqR

noncomputable def invProduct (x : ℕ → ℝ) (i r : ℕ) : ℝ :=
  ∏ k ∈ Finset.range (r+1), (x (i+k))⁻¹

noncomputable def invSum (x : ℕ → ℝ) (i r : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (r+1), (x (i+k))⁻¹

private lemma end_products (x : ℕ → ℝ) (hx : ∀ i, x i ≠ 0) (i r : ℕ) :
    invProduct x (i+1) r = invProduct x i (r+1)*x i ∧
    invProduct x i r = invProduct x i (r+1)*x (i+r+1) := by
  constructor
  · simp only [invProduct,Finset.prod_range_succ' (n := r+1)]
    simp [Nat.add_assoc,Nat.add_comm 1, hx]
  · simp only [invProduct,Finset.prod_range_succ (n := r+1)]
    rw [Nat.add_assoc]
    field_simp [hx]

private lemma end_sums (x : ℕ → ℝ) (i r : ℕ) :
    invSum x (i+1) r = invSum x i (r+1)-(x i)⁻¹ ∧
    invSum x i r = invSum x i (r+1)-(x (i+r+1))⁻¹ := by
  constructor
  · simp only [invSum,Finset.sum_range_succ' (n := r+1)]
    simp [Nat.add_assoc,Nat.add_comm 1]
  · simp only [invSum,Finset.sum_range_succ (n := r+1)]
    simp [Nat.add_assoc]

/-- The two exact divided differences, for all orders. The factors in each
product have the same sign when the affine denominator is positive. -/
theorem reciprocal_differences {u : ℕ → ℕ} (hu : StrictMono u) {a h : ℝ}
    (hx : ∀ i, a+h*u i ≠ 0) (N : ℝ) (r i : ℕ) :
    let x := fun i => a+h*u i
    dd u (fun j => N/(x j)) r i = N*(-h)^r*invProduct x i r ∧
    dd u (fun j => N/(x j)^2) r i = N*(-h)^r*invProduct x i r*invSum x i r := by
  let x := fun i => a+h*u i
  change dd u (fun j => N/(x j)) r i = N*(-h)^r*invProduct x i r ∧
    dd u (fun j => N/(x j)^2) r i = N*(-h)^r*invProduct x i r*invSum x i r
  induction r generalizing i with
  | zero => simp [dd,invProduct,invSum,div_eq_mul_inv,pow_two,mul_assoc]
  | succ r ih =>
    let g := (u (i+r+1):ℝ) - u i
    have hg : g ≠ 0 := by have hh : 1 ≤ g := gap_ge hu i r; linarith
    have hid : x (i+r+1)-x i = h*g := by dsimp [x,g]; ring
    obtain ⟨p1,p0⟩ := end_products x hx i r
    obtain ⟨s1,s0⟩ := end_sums x i r
    obtain ⟨ia,ib⟩ := ih (i+1)
    obtain ⟨ja,jb⟩ := ih i
    constructor
    · change (_ - _)/g = _
      rw [ia,ja,p1,p0,div_eq_iff hg,pow_succ]
      linear_combination -(N*(-h)^r*invProduct x i (r+1))*hid
    · change (_ - _)/g = _
      rw [ib,jb,p1,p0,s1,s0,div_eq_iff hg,pow_succ]
      have ha := mul_inv_cancel₀ (hx i)
      have hb := mul_inv_cancel₀ (hx (i+r+1))
      linear_combination -(N*(-h)^r*invProduct x i (r+1)*invSum x i (r+1))*hid -
        (N*(-h)^r*invProduct x i (r+1))*ha + (N*(-h)^r*invProduct x i (r+1))*hb

end H1Divided

/- Integer divided differences rule out dense clusters of near-integer values. -/
namespace H1Cell
open H1Divided

def commonDen (u : ℕ → ℕ) (r : ℕ) : ℕ :=
  ∏ i ∈ Finset.range (r+1), ∏ j ∈ Finset.range (r+1), max 1 (u j-u i)

lemma den_pos (u : ℕ → ℕ) (r : ℕ) : 0 < commonDen u r :=
  Finset.prod_pos fun i _ => Finset.prod_pos fun j _ => lt_of_lt_of_le (by decide : 0 < 1) (le_max_left _ _)

lemma den_dvd {u : ℕ → ℕ} (hu : StrictMono u) {r i j : ℕ} (hij : i < j) (hj : j ≤ r) :
    u j-u i ∣ commonDen u r := by
  have hle : 1 ≤ u j-u i := Nat.sub_pos_of_lt (hu hij)
  have h₁ := Finset.dvd_prod_of_mem (fun b => max 1 (u b-u i))
    (Finset.mem_range.mpr (by omega : j < r+1))
  rw [max_eq_right hle] at h₁
  exact h₁.trans (Finset.dvd_prod_of_mem
    (fun a => ∏ b ∈ Finset.range (r+1), max 1 (u b-u a)) (Finset.mem_range.mpr (by omega)))

lemma den_bound {u : ℕ → ℕ} {r M : ℕ} (hM : 1 ≤ M) (hb : ∀ i ≤ r, u i ≤ M) :
    (commonDen u r)^r ≤ M^((r+1)*(r+1)*r) := by
  have hrow (i : ℕ) : (∏ j ∈ Finset.range (r+1), max 1 (u j-u i)) ≤ M^(r+1) := calc
    _ ≤ ∏ _j ∈ Finset.range (r+1), M := Finset.prod_le_prod' (fun j hj =>
      max_le hM ((Nat.sub_le _ _).trans (hb _ (by have := Finset.mem_range.mp hj; omega))))
    _ = _ := by simp
  have hL : commonDen u r ≤ (M^(r+1))^(r+1) := calc
    _ ≤ ∏ _i ∈ Finset.range (r+1), M^(r+1) := Finset.prod_le_prod' (fun i _ => hrow i)
    _ = _ := by simp
  simpa only [←pow_mul] using Nat.pow_le_pow_left hL r

/-- The rounded divided difference either vanishes or has absolute value
at least the reciprocal of a controlled integer. -/
theorem impossible {u : ℕ → ℕ} (hu : StrictMono u) {r M : ℕ} (hM : 1 ≤ M)
    (hb : ∀ i ≤ r, u i ≤ M) (f : ℕ → ℝ) (z : ℕ → ℤ) (δ : ℝ)
    (hz : ∀ i ≤ r, |f i - (z i:ℝ)| ≤ δ)
    (lower : 2^r*δ < |dd u f r 0|)
    (upper : (M:ℝ)^((r+1)*(r+1)*r)*(|dd u f r 0|+2^r*δ) < 1) : False := by
  let L := commonDen u r
  have hL : 0 < L := den_pos _ _
  have herr := error_bound hu f (fun i => (z i:ℝ)) δ r 0 (by simpa using hz)
  obtain ⟨w,hw⟩ := integral_scaled hu z L r 0 (fun a b ha hab hb => den_dvd hu hab (by omega))
  let v := dd u (fun i => (z i:ℝ)) r 0
  have hv : v ≠ 0 := by
    intro h
    change |dd u f r 0-v| ≤ _ at herr
    rw [h,sub_zero] at herr
    linarith
  have hLr : 0 < (L:ℝ)^r := by exact_mod_cast pow_pos hL r
  have hw' : w ≠ 0 := by
    intro h
    change (L:ℝ)^r*v = _ at hw
    rw [h,Int.cast_zero] at hw
    exact (mul_ne_zero hLr.ne' hv) hw
  have h1 : (1:ℝ) ≤ |(w:ℝ)| := by exact_mod_cast (show (1:ℤ) ≤ |w| from (abs_pos.mpr hw' : 0 < |w|))
  have hvb : |v| ≤ |dd u f r 0|+2^r*δ := by
    have h := abs_sub (dd u f r 0) (dd u f r 0-v)
    rw [sub_sub_cancel] at h
    linarith
  have hdb : (L:ℝ)^r ≤ (M:ℝ)^((r+1)*(r+1)*r) := by exact_mod_cast den_bound hM hb
  rw [←hw,abs_mul,abs_of_pos hLr] at h1
  exact upper.not_ge (h1.trans (mul_le_mul hdb hvb (abs_nonneg _) (by positivity)))

private lemma prod_bounds {x : ℕ → ℝ} {n : ℝ} {r : ℕ} (hn : 0 < n)
    (hx : ∀ i ≤ r, n ≤ x i ∧ x i ≤ 2*n) :
    ((2*n)^(r+1))⁻¹ ≤ invProduct x 0 r ∧ invProduct x 0 r ≤ (n^(r+1))⁻¹ := by
  constructor
  · calc
      _ = ∏ _k ∈ Finset.range (r+1), (2*n)⁻¹ := by rw [Finset.prod_const,Finset.card_range,inv_pow]
      _ ≤ ∏ k ∈ Finset.range (r+1), (x k)⁻¹ := Finset.prod_le_prod (fun k _ => by positivity) (fun k hk =>
        inv_le_inv₀ (by positivity : 0 < 2*n) (hn.trans_le (hx k (by have := Finset.mem_range.mp hk; omega)).1) |>.mpr (by simpa using (hx k (by have := Finset.mem_range.mp hk; omega)).2))
      _ = _ := by simp [invProduct]
  · calc
      _ ≤ ∏ _k ∈ Finset.range (r+1), n⁻¹ := by
        unfold invProduct
        simp only [Nat.zero_add]
        apply Finset.prod_le_prod
        · intro k hk
          have hh := hn.trans_le (hx k (by have := Finset.mem_range.mp hk; omega)).1
          positivity
        · intro k hk
          obtain ⟨lo,_⟩ := hx k (by have := Finset.mem_range.mp hk; omega)
          exact (inv_le_inv₀ (hn.trans_le lo) hn).mpr lo
      _ = _ := by simp

private lemma sum_bounds {x : ℕ → ℝ} {n : ℝ} {r : ℕ} (hn : 0 < n)
    (hx : ∀ i ≤ r, n ≤ x i ∧ x i ≤ 2*n) :
    (2*n)⁻¹ ≤ invSum x 0 r ∧ invSum x 0 r ≤ (r+1:ℕ)*n⁻¹ := by
  unfold invSum
  simp only [Nat.zero_add]
  have one : (2*n)⁻¹ ≤ (x 0)⁻¹ :=
    (inv_le_inv₀ (by positivity : 0 < 2*n) (hn.trans_le (hx 0 (by omega)).1)).mpr (hx 0 (by omega)).2
  constructor
  · refine one.trans (Finset.single_le_sum (f := fun t => (x t)⁻¹) (fun k hk => ?_) (Finset.mem_range.mpr (by omega : 0 < r+1)))
    have hh := hn.trans_le (hx k (by have := Finset.mem_range.mp hk; omega)).1
    positivity
  · calc
      _ ≤ ∑ _k ∈ Finset.range (r+1), n⁻¹ := Finset.sum_le_sum (fun k hk => by
        obtain ⟨lo,_⟩ := hx k (by have := Finset.mem_range.mp hk; omega)
        exact (inv_le_inv₀ (hn.trans_le lo) hn).mpr lo)
      _ = _ := by simp

theorem reciprocal_bounds {u : ℕ → ℕ} (hu : StrictMono u) {N a h n : ℝ}
    (hN : 0 < N) (ha : 0 < a) (hh : 0 < h) (hn : 0 < n) (r j : ℕ)
    (hj : j = 1 ∨ j = 2) (hx : ∀ i ≤ r, n ≤ a+h*u i ∧ a+h*u i ≤ 2*n) :
    let v := fun i => N/(a+h*u i)^j
    (N*h^r)/(2*n)^(r+j) ≤ |dd u v r 0| ∧
     |dd u v r 0| ≤ (r+1:ℕ)*(N*h^r)/n^(r+j) := by
  let x := fun i => a+h*u i
  have hxp (i : ℕ) : 0 < x i := by dsimp [x]; positivity
  have hr := reciprocal_differences hu (fun i => (hxp i).ne') N r 0
  have hp := prod_bounds (x := x) hn hx
  have hs := sum_bounds (x := x) hn hx
  have hP : 0 ≤ invProduct x 0 r := (by positivity : 0 ≤ ((2*n)^(r+1))⁻¹).trans hp.1
  have hS : 0 ≤ invSum x 0 r := (by positivity : 0 ≤ (2*n)⁻¹).trans hs.1
  have hcoef : 0 < N*h^r := by positivity
  have hrr : 1 ≤ (r+1:ℕ) := by omega
  have hr1 : dd u (fun i => N/x i) r 0 = N*(-h)^r*invProduct x 0 r := hr.1
  have hr2 : dd u (fun i => N/(x i)^2) r 0 = N*(-h)^r*invProduct x 0 r*invSum x 0 r := hr.2
  have hrR : (1:ℝ) ≤ (r+1:ℕ) := by exact_mod_cast hrr
  rcases hj with rfl|rfl
  · change _ ≤ |dd u (fun i => N/(x i)^1) r 0| ∧ |dd u (fun i => N/(x i)^1) r 0| ≤ _
    simp only [pow_one]
    rw [hr1]
    simp only [abs_mul,abs_pow,abs_neg,abs_of_pos hN,abs_of_pos hh,abs_of_nonneg hP,
      div_eq_mul_inv]
    exact ⟨mul_le_mul_of_nonneg_left hp.1 hcoef.le,
      (mul_le_mul_of_nonneg_left hp.2 hcoef.le).trans (mul_le_mul_of_nonneg_right
        (le_mul_of_one_le_left hcoef.le hrR) (by positivity))⟩
  · change _ ≤ |dd u (fun i => N/(x i)^2) r 0| ∧ |dd u (fun i => N/(x i)^2) r 0| ≤ _
    rw [hr2]
    simp only [abs_mul,abs_pow,abs_neg,abs_of_pos hN,abs_of_pos hh,abs_of_nonneg hP,abs_of_nonneg hS]
    constructor
    · calc
        _ = N*h^r*((2*n)^(r+1))⁻¹*(2*n)⁻¹ := by rw [pow_succ (2*n) (r+1)]; simp only [div_eq_mul_inv,mul_inv_rev]; ring
        _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left hp.1 hcoef.le) hs.1 (by positivity)
          (mul_nonneg hcoef.le hP)
    · calc
        _ ≤ N*h^r*(n^(r+1))⁻¹*((r+1:ℕ)*n⁻¹) := mul_le_mul
          (mul_le_mul_of_nonneg_left hp.2 hcoef.le) hs.2 hS (by positivity)
        _ = _ := by rw [pow_succ n (r+1)]; simp only [div_eq_mul_inv,mul_inv_rev]; ring

end H1Cell

namespace H1Count
open H1Divided

def Near (N p j : ℕ) (δ : ℝ) : Prop := ∃ z : ℤ, |(N:ℝ)/(p:ℝ)^j-z| ≤ δ

noncomputable def bad (N n H j : ℕ) (δ : ℝ) : Finset ℕ := by
  classical
  exact (Finset.Ioc n (n+H)).filter (fun p => Near N p j δ)

theorem cell_card {N n a s M r j : ℕ} {δ : ℝ} (hN : 0 < N) (hn : 0 < n)
    (ha : 0 < a) (hs : 0 < s) (hM : 0 < M) (hj : j = 1 ∨ j = 2)
    (lo : 2^r*δ < (N:ℝ)*(s:ℝ)^r/(2*n)^(r+j))
    (hi : (M:ℝ)^((r+1)*(r+1)*r)*((r+1:ℕ)*((N:ℝ)*(s:ℝ)^r)/(n:ℝ)^(r+j)+2^r*δ) < 1)
    (S : Finset ℕ) (hS : ∀ v ∈ S, v < M ∧ n ≤ a+s*v ∧ a+s*v ≤ 2*n ∧ Near N (a+s*v) j δ) :
    S.card ≤ r := by
  classical
  by_contra! hc
  obtain ⟨T,hTS,hT⟩ := Finset.exists_subset_card_eq (show r+1 ≤ S.card by omega)
  let e := T.orderEmbOfFin hT
  have hem (i : Fin (r+1)) := hS (e i) (hTS (T.orderEmbOfFin_mem hT i))
  let u (i : ℕ) := if h : i<r+1 then e ⟨i,h⟩ else M+i
  have hu : StrictMono u := by
    intro i j hij
    by_cases hj' : j < r+1
    · have hi' : i < r+1 := by omega
      simp only [u,dif_pos hi',dif_pos hj']
      exact e.strictMono (show (⟨i,hi'⟩ : Fin (r+1)) < ⟨j,hj'⟩ from hij)
    · by_cases hi' : i < r+1
      · simp only [u,dif_pos hi',dif_neg hj']
        have hh := (hem ⟨i,hi'⟩).1
        omega
      · simp only [u,dif_neg hi',dif_neg hj']
        omega
  have hall (i : ℕ) (hi : i ≤ r) : u i < M ∧ n ≤ a+s*u i ∧ a+s*u i ≤ 2*n ∧ Near N (a+s*u i) j δ := by
    have hh : i < r+1 := by omega
    simpa only [u,dif_pos hh] using hem ⟨i,hh⟩
  let z (i : ℕ) := if hi : i ≤ r then (hall i hi).2.2.2.choose else 0
  let f (i : ℕ) := (N:ℝ)/((a:ℝ)+(s:ℝ)*u i)^j
  have hfb := H1Cell.reciprocal_bounds (u := u) hu (N := (N:ℝ)) (a := (a:ℝ)) (h := (s:ℝ))
    (n := (n:ℝ)) (by exact_mod_cast hN) (by exact_mod_cast ha) (by exact_mod_cast hs)
    (by exact_mod_cast hn) r j hj (fun i hi => by
      exact ⟨by exact_mod_cast (hall i hi).2.1, by exact_mod_cast (hall i hi).2.2.1⟩)
  apply H1Cell.impossible hu hM (fun i hi => (hall i hi).1.le) f z δ
  · intro i hi
    simpa only [z,dif_pos hi,f,Nat.cast_add,Nat.cast_mul] using (hall i hi).2.2.2.choose_spec
  · exact lo.trans_le hfb.1
  · exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left (add_le_add hfb.2 le_rfl) (by positivity)) hi

theorem bad_card {N n H s M r j : ℕ} {δ : ℝ} (hN : 0 < N) (hn : 0 < n)
    (hH : H ≤ n) (hs : 0 < s) (hM : 0 < M) (hj : j = 1 ∨ j = 2)
    (lo : 2^r*δ < (N:ℝ)*(s:ℝ)^r/(2*n)^(r+j))
    (hi : (M:ℝ)^((r+1)*(r+1)*r)*((r+1:ℕ)*((N:ℝ)*(s:ℝ)^r)/(n:ℝ)^(r+j)+2^r*δ) < 1) :
    ((bad N n H j δ).card:ℝ) ≤ r*((H:ℝ)/M+s) := by
  classical
  let A (b v : ℕ) := n+1+b*M*s+v
  let S (b v : ℕ) := (Finset.range M).filter (fun u => A b v+s*u ∈ bad N n H j δ)
  let F (b v : ℕ) := (S b v).image (fun u => A b v+s*u)
  have hF (b v : ℕ) : (F b v).card ≤ r := by
    apply Finset.card_image_le.trans
    apply cell_card hN hn (show 0 < A b v by dsimp [A]; omega) hs hM hj lo hi
    intro u hu
    obtain ⟨hum,hp⟩ := Finset.mem_filter.mp hu
    obtain ⟨hp,hnear⟩ := Finset.mem_filter.mp (show A b v+s*u ∈ bad N n H j δ from hp)
    obtain ⟨h1,h2⟩ := Finset.mem_Ioc.mp hp
    exact ⟨Finset.mem_range.mp hum,h1.le,by omega,hnear⟩
  let B := H/(s*M)+1
  have cover : bad N n H j δ ⊆ (Finset.range B).biUnion (fun b => (Finset.range s).biUnion (F b)) := by
    intro p hp
    obtain ⟨hp1,hp2⟩ := Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1
    let t := p-(n+1)
    let q := t/s
    let b := q/M
    let u := q%M
    let v := t%s
    have ht : t ≤ H := by dsimp [t]; omega
    have hb : b < B := by
      dsimp [b,q,B]
      rw [Nat.div_div_eq_div_mul]
      have hh := Nat.div_le_div_right (c := s*M) ht
      omega
    have hv : v < s := Nat.mod_lt _ hs
    have hu : u < M := Nat.mod_lt _ hM
    have ht' : v+s*q = t := Nat.mod_add_div t s
    have hq : u+M*b = q := Nat.mod_add_div q M
    have he : A b v+s*u = p := by
      have ht2 : v+s*u+b*M*s=t := by rw [←ht',←hq]; ring
      dsimp [A,t] at *
      omega
    refine Finset.mem_biUnion.mpr ⟨b,Finset.mem_range.mpr hb,?_⟩
    refine Finset.mem_biUnion.mpr ⟨v,Finset.mem_range.mpr hv,?_⟩
    exact Finset.mem_image.mpr ⟨u,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hu,he ▸ hp⟩,he⟩
  have hbc : (bad N n H j δ).card ≤ B*(s*r) := by
    refine (Finset.card_le_card cover).trans ?_
    simpa only [Finset.card_range] using Finset.card_biUnion_le_card_mul (Finset.range B)
      (fun b => (Finset.range s).biUnion (F b)) (s*r) (fun b _ => by
        simpa only [Finset.card_range] using Finset.card_biUnion_le_card_mul (Finset.range s)
          (F b) r (fun v _ => hF b v))
  have hq := Nat.div_mul_le_self H (s*M)
  have hqR : (H/(s*M):ℕ)*(s:ℝ)*(M:ℝ) ≤ H := by exact_mod_cast (by simpa [Nat.mul_assoc] using hq : H/(s*M)*s*M ≤ H)
  have hM' : 0 < (M:ℝ) := by exact_mod_cast hM
  have hh := (le_div_iff₀ hM').mpr hqR
  calc
    _ ≤ (B:ℝ)*((s:ℝ)*r) := by exact_mod_cast hbc
    _ = (r:ℝ)*((H/(s*M):ℕ)*(s:ℝ)+s) := by dsimp [B]; push_cast; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add hh le_rfl) (by positivity)

end H1Count

namespace H1Scale
open Filter Real

lemma log_power_small (A : ℕ) (C : ℝ) (hC : 0 < C) :
    ∀ᶠ n : ℕ in atTop, C * (log (n:ℝ))^A ≤ n := by
  have h := (isLittleO_log_rpow_rpow_atTop (A:ℝ) (by norm_num : (0:ℝ)<1)).bound (inv_pos.mpr hC)
  have hc : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [hc.eventually h,eventually_ge_atTop 1] with n hn hn1
  change ‖(log (n:ℝ))^(A:ℝ)‖ ≤ C⁻¹*‖(n:ℝ)^(1:ℝ)‖ at hn
  have hl : 0 ≤ log (n:ℝ) := log_nonneg (by exact_mod_cast hn1)
  rw [rpow_natCast,rpow_one,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (by positivity),
    abs_of_nonneg (by positivity)] at hn
  have hh := mul_le_mul_of_nonneg_left hn hC.le
  rwa [←mul_assoc,mul_inv_cancel₀ hC.ne',one_mul] at hh

lemma stride {n N W : ℝ} {r j : ℕ} (hn : 0<n) (hN : 0<N) (hW : 0<W) (hr : 0<r)
    (big : 2^r*(4*(r+1:ℕ)*W*N) ≤ n^(r+j)) :
    ∃ s : ℕ, 0<s ∧
      (4*(r+1:ℕ)*W)*(N*(s:ℝ)^r/n^(r+j)) ≤ 1 ∧
      1 ≤ (4*(r+1:ℕ)*W)*2^r*(N*(s:ℝ)^r/n^(r+j)) := by
  let C : ℝ := 4*(r+1:ℕ)*W
  let Z := n^(r+j)/(C*N)
  let X := Z^((r:ℝ)⁻¹)
  have hC : 0<C := by dsimp [C]; positivity
  have hZ : 0<Z := by dsimp [Z]; positivity
  have hX : 0<X := by dsimp [X]; positivity
  have hx : X^r=Z := rpow_inv_natCast_pow hZ.le hr.ne'
  have hb : (2:ℝ)^r ≤ Z := (le_div_iff₀ (mul_pos hC hN)).mpr big
  have h2 : 2 ≤ X := (pow_le_pow_iff_left₀ (by norm_num) hX.le hr.ne').mp (hx ▸ hb)
  let s := ⌊X⌋₊
  have hs : (s:ℝ) ≤ X := Nat.floor_le hX.le
  have h2s : X ≤ 2*(s:ℝ) := by have := Nat.lt_floor_add_one X; dsimp [s]; linarith
  have hs' : 0 < s := by exact Nat.lt_of_lt_of_le (by decide : 0<2) (Nat.le_floor h2)
  have hu := pow_le_pow_left₀ (by positivity : 0 ≤ (s:ℝ)) hs r
  have hl := pow_le_pow_left₀ hX.le h2s r
  rw [hx] at hu hl
  rw [mul_pow] at hl
  have hnP : 0<n^(r+j) := pow_pos hn _
  have hu' := (le_div_iff₀ (mul_pos hC hN)).mp hu
  have hl' := (div_le_iff₀ (mul_pos hC hN)).mp hl
  refine ⟨s,hs',?_,?_⟩
  · change C*(N*(s:ℝ)^r/n^(r+j)) ≤ 1
    rw [mul_div_assoc',div_le_iff₀ hnP,one_mul]
    linarith only [show C*(N*(s:ℝ)^r)=(s:ℝ)^r*(C*N) by ring,hu']
  · change 1 ≤ C*2^r*(N*(s:ℝ)^r/n^(r+j))
    rw [mul_div_assoc',le_div_iff₀ hnP,one_mul]
    linarith only [show C*2^r*(N*(s:ℝ)^r)=2^r*(s:ℝ)^r*(C*N) by ring,hl']

lemma stride_short {n N W T : ℝ} {s r j : ℕ} (hn : 1 ≤ n) (hW : 1 ≤ W)
    (hT : 0 < T) (hTn : T^r ≤ n) (hr : 0 < r) (hj : j ≤ 2)
    (hN : n^3 ≤ N) (upper : (4*(r+1:ℕ)*W)*(N*(s:ℝ)^r/n^(r+j)) ≤ 1) :
    (s:ℝ)*T ≤ n := by
  have hn' : 0<n := by linarith
  have hN' : 0<N := (pow_pos hn' 3).trans_le hN
  have hC : (1:ℝ) ≤ 4*(r+1:ℕ)*W := by
    have ha : (1:ℝ) ≤ (r+1:ℕ) := by exact_mod_cast (show 1 ≤ r+1 by omega)
    nlinarith [mul_le_mul_of_nonneg_right ha (by linarith : 0≤W)]
  have hy : N*(s:ℝ)^r/n^(r+j) ≤ 1 :=
    (le_mul_of_one_le_left (by positivity) hC).trans upper
  have hy' := (div_le_one (pow_pos hn' _)).mp hy
  have hctrl : n^3*((s:ℝ)*T)^r ≤ n^3*n^r := calc
    _ = (n^3*(s:ℝ)^r)*T^r := by rw [mul_pow]; ring
    _ ≤ (N*(s:ℝ)^r)*n := mul_le_mul (mul_le_mul_of_nonneg_right hN (by positivity)) hTn (by positivity) (by positivity)
    _ ≤ n^(r+j)*n := mul_le_mul_of_nonneg_right hy' hn'.le
    _ ≤ n^(r+2)*n := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hn (by omega)) hn'.le
    _ = n^3*n^r := by rw [pow_add]; ring
  exact (pow_le_pow_iff_left₀ (by positivity) hn'.le hr.ne').mp (le_of_mul_le_mul_left hctrl (pow_pos hn' 3))

def K (r : ℕ) := (r+1)*(r+1)*r
def B (r : ℕ) := 2*K r+1

theorem bad_small (D : ℕ) :
    let r := D+3
    ∀ᶠ n : ℕ in atTop, ∀ N : ℕ, n^3 ≤ N → N ≤ n^D → ∀ j : ℕ, (j=1 ∨ j=2) →
      ((H1Count.bad N n ⌊H1ShortPrimes.width (B r) n⌋₊ j ((log (n:ℝ))^(B r))⁻¹).card:ℝ)*
        (100*log n) ≤ 2*H1ShortPrimes.width (B r) n := by
  let r := D+3
  let k := K r
  let b := B r
  let C : ℝ := 4*(r+1:ℕ)
  let A : ℝ := 2^r*C*2^k
  let E : ℝ := C*2^r*2^(r+2)*2^r*2^k
  have hr : 0<r := by dsimp [r]; omega
  have hC : 0<C := by dsimp [C]; positivity
  have hA : 0<A := by dsimp [A]; positivity
  have hE : 0<E := by dsimp [E]; positivity
  have hnr : 0 < (r:ℝ) := by exact_mod_cast hr
  have cast : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have logs := tendsto_log_atTop.comp cast
  filter_upwards [logs.eventually_ge_atTop (max (E+1) (100*(r:ℝ)+1)),eventually_ge_atTop 2,
    log_power_small (2*k) A hA, log_power_small ((b+1)*r) ((100*(r:ℝ))^r) (by positivity)] with n hlog hn2 hbig hshort
  intro N hlo hhi j hj
  let L := log (n:ℝ)
  change max (E+1) (100*(r:ℝ)+1) ≤ L at hlog
  have hL1 : 1 ≤ L := by have := (le_max_right (E+1) (100*(r:ℝ)+1)).trans hlog; linarith
  have hL : 0<L := by linarith
  have hn : 1 ≤ (n:ℝ) := by exact_mod_cast (show 1≤n by omega)
  have hn' : (0:ℝ)<n := by linarith
  have hN : (n:ℝ)^3 ≤ (N:ℝ) := by exact_mod_cast hlo
  have hN' : (0:ℝ)<N := (pow_pos hn' 3).trans_le hN
  let M := ⌈L^2⌉₊
  let W := (M:ℝ)^k
  have hMlo : L^2 ≤ (M:ℝ) := Nat.le_ceil _
  have hM1 : (1:ℝ) ≤ M := (one_le_pow₀ hL1).trans hMlo
  have hM : 0<M := by exact_mod_cast (lt_of_lt_of_le (by norm_num : (0:ℝ)<1) hM1)
  have hMhi : (M:ℝ) ≤ 2*L^2 := by
    have hm := Nat.ceil_lt_add_one (by positivity : 0 ≤ L^2)
    dsimp [M]; linarith [one_le_pow₀ (n:=2) hL1]
  have hW : 1 ≤ W := one_le_pow₀ hM1
  have hW' : 0 < W := by linarith
  have hWb : W ≤ 2^k * L^(2*k) := by
    have hh := pow_le_pow_left₀ (by positivity : (0:ℝ)≤M) hMhi k
    simpa only [mul_pow,←pow_mul] using hh
  have hj2 : j≤2 := by omega
  have hsz : 2^r*(C*W*(N:ℝ)) ≤ (n:ℝ)^(r+j) := calc
    _ = (2^r*C*W)*N := by ring
    _ ≤ (A*L^(2*k))*N := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      dsimp [A]; nlinarith only [mul_le_mul_of_nonneg_left hWb (show 0 ≤ 2^r*C by positivity)]
    _ ≤ (n:ℝ)*(n:ℝ)^D := mul_le_mul hbig (by exact_mod_cast hhi) (by positivity) hn'.le
    _ = (n:ℝ)^(D+1) := by rw [pow_succ]; ring
    _ ≤ _ := pow_le_pow_right₀ hn (by dsimp [r]; omega)
  obtain ⟨s,hs,hu,hl⟩ := stride hn' hN' hW' hr hsz
  let y := (N:ℝ)*(s:ℝ)^r/(n:ℝ)^(r+j)
  change C*W*y ≤ 1 at hu
  change 1 ≤ C*W*2^r*y at hl
  let δ := (L^b)⁻¹
  have hd : 0<δ := by dsimp [δ]; positivity
  have herr : C*W*2^r*2^(r+j)*(2^r*δ) < 1 := by
    dsimp [δ]
    rw [←mul_assoc,←div_eq_mul_inv,div_lt_one (pow_pos hL _)]
    have hp : (2:ℝ)^(r+j) ≤ 2^(r+2) := pow_le_pow_right₀ (by norm_num) (by omega)
    have hh : C*W*2^r*2^(r+j)*2^r ≤ E*L^(2*k) := calc
      _ ≤ C*(2^k*L^(2*k))*2^r*2^(r+2)*2^r := by gcongr
      _ = _ := by dsimp [E]; ring
    have hEb : E<L := by have := (le_max_left (E+1) (100*(r:ℝ)+1)).trans hlog; linarith
    change _ < L^(2*k+1)
    rw [pow_succ]
    exact hh.trans_lt (by simpa only [pow_succ L (2*k),mul_comm] using mul_lt_mul_of_pos_right hEb (pow_pos hL (2*k)))
  have hfactor : 0 < C*W*2^r := by positivity
  have hlow : 2^r*δ < (N:ℝ)*(s:ℝ)^r/(2*n)^(r+j) := by
    have hy : 2^(r+j)*(2^r*δ)<y := by
      apply lt_of_mul_lt_mul_left (a := C*W*2^r)
      · calc
          _ = C*W*2^r*2^(r+j)*(2^r*δ) := by ring
          _ < _ := herr.trans_le hl
      · positivity
    rw [mul_pow]
    change _ < _ / (2^(r+j)*(n:ℝ)^(r+j))
    rw [lt_div_iff₀ (by positivity)]
    have hz := (lt_div_iff₀ (pow_pos hn' (r+j))).mp hy
    linarith only [hz,show 2^r*δ*(2^(r+j)*(n:ℝ)^(r+j)) = (2^(r+j)*(2^r*δ))*(n:ℝ)^(r+j) by ring]
  have hsmallW : W*(2^r*δ) < 1/2 := by
    have hC4 : 4 ≤ C := by dsimp [C]; push_cast; linarith
    have hbase : 2 ≤ C*2^r*(2:ℝ)^(r+j) :=
      (show (2:ℝ)≤C by linarith).trans ((le_mul_of_one_le_right hC.le (one_le_pow₀ (by norm_num))).trans
        (le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by norm_num))))
    have haux := mul_le_mul_of_nonneg_right hbase (show 0 ≤ W*(2^r*δ) by positivity)
    nlinarith only [haux,herr]
  have hupper : W*((r+1:ℕ)*((N:ℝ)*(s:ℝ)^r)/(n:ℝ)^(r+j)+2^r*δ)<1 := by
    have hz : W*((r+1:ℕ)*((N:ℝ)*(s:ℝ)^r)/(n:ℝ)^(r+j)) = C*W*y/4 := by dsimp [C,y]; ring
    rw [mul_add,hz]; linarith
  let w := H1ShortPrimes.width b n
  have hwidth : w ≤ n := div_le_self hn'.le (one_le_pow₀ hL1)
  have hH : ⌊w⌋₊ ≤ n := Nat.floor_le_of_le hwidth
  have count := H1Count.bad_card (N:=N) (H:=⌊w⌋₊) (n:=n) (s:=s) (M:=M) (r:=r) (j:=j) (δ:=δ)
    (by exact_mod_cast hN') (by omega) hH hs hM hj hlow hupper
  let T := 100*(r:ℝ)*L^(b+1)
  have hT : 0<T := by dsimp [T]; positivity
  have hTn : T^r ≤ n := by simpa only [T,mul_pow,←pow_mul] using hshort
  have hsT := stride_short hn hW hT hTn hr hj2 hN hu
  have hsTerm : (s:ℝ)*(100*r*L) ≤ w := by
    change _ ≤ (n:ℝ)/L^b
    rw [le_div_iff₀ (pow_pos hL _)]
    calc
      _ = (s:ℝ)*T := by dsimp [T]; rw [pow_succ]; ring
      _ ≤ _ := hsT
  have hcoef : 100*(r:ℝ)*L ≤ M := by
    have hh := (le_max_right (E+1) (100*(r:ℝ)+1)).trans hlog
    nlinarith [mul_le_mul_of_nonneg_right (by linarith : 100*(r:ℝ)≤L) hL.le]
  have hMr : (0:ℝ)<M := by exact_mod_cast hM
  have hw : 0<w := by change 0<(n:ℝ)/L^b; positivity
  have hterm : ((⌊w⌋₊:ℕ):ℝ)/M*(100*r*L) ≤ w := calc
    _ ≤ (w/M)*(M:ℝ) := mul_le_mul (div_le_div_of_nonneg_right (Nat.floor_le hw.le) hMr.le)
      hcoef (by positivity) (by positivity)
    _ = w := div_mul_cancel₀ _ hMr.ne'
  change _ * (100*L) ≤ 2*w
  calc
    _ ≤ ((r:ℝ)*(((⌊w⌋₊:ℕ):ℝ)/M+s))*(100*L) := mul_le_mul_of_nonneg_right count (by positivity)
    _ ≤ _ := by linarith only [show ((r:ℝ)*(((⌊w⌋₊:ℕ):ℝ)/M+s))*(100*L) =
                    ((⌊w⌋₊:ℕ):ℝ)/M*(100*r*L)+(s:ℝ)*(100*r*L) by ring, hterm,hsTerm]

end H1Scale

namespace H1Finish
open H1Count H1Scale H1ShortPrimes Filter Real
open OMA.R_Erdos137_erdos_137_variants_multiple_powerful_factors_R2

lemma good_prime {n m p : ℕ} {δ : ℝ} (hn : 0<n) (hp : p.Prime) (hnp : n<p)
    (hpw : (p:ℝ) ≤ n+(n:ℝ)*δ) (hδ : 0 ≤ δ) (hδn : 1 ≤ (n:ℝ)*δ)
    (h1 : ¬ Near (m+n) p 1 δ) (h2 : ¬ Near (m+n) p 2 δ) :
    p ∣ (∏ y ∈ Finset.Ioc m (m+n), y) ∧ ¬p^2 ∣ (∏ y ∈ Finset.Ioc m (m+n), y) := by
  let N := m+n
  let i := N%p
  let q := N/p
  let x := p*q
  have hei : i+p*q=N := Nat.mod_add_div N p
  have hi := Nat.mod_lt N hp.pos
  have hpr : (0:ℝ)<p := by exact_mod_cast hp.pos
  have hnr : (0:ℝ)<n := by exact_mod_cast hn
  have hnp' : (n:ℝ)≤p := by exact_mod_cast hnp.le
  have hxr : (i:ℝ)+(p:ℝ)*(q:ℝ)=(N:ℝ) := by exact_mod_cast hei
  have hit : i<n := by
    by_contra! hmiss
    apply h1
    refine ⟨(q:ℤ)+1,?_⟩
    change |(N:ℝ)/(p:ℝ)^1-((q:ℤ)+1:ℤ)| ≤ δ
    push_cast
    rw [pow_one,abs_le]
    have hi' : (i:ℝ)<p := by exact_mod_cast hi
    have hmiss' : (n:ℝ) ≤ i := by exact_mod_cast hmiss
    have hpδ := mul_le_mul_of_nonneg_right hnp' hδ
    constructor
    · rw [le_sub_iff_add_le,le_div_iff₀ hpr]
      nlinarith only [hxr,hmiss',hpw,hpδ]
    · rw [sub_le_iff_le_add,div_le_iff₀ hpr]
      nlinarith only [hxr,hi',mul_nonneg hpr.le hδ]
  have hx : x ∈ Finset.Ioc m (m+n) := by
    apply Finset.mem_Ioc.mpr
    change m < p*q ∧ p*q ≤ m+n
    change i+p*q=m+n at hei
    omega
  apply transfer_factor (Or.inl hnp.le) hx hp (dvd_mul_right p q)
  rintro ⟨d,hd⟩
  apply h2
  refine ⟨(d:ℤ),?_⟩
  have he : i+p^2*d=N := by change x=p^2*d at hd; simpa only [←hd] using hei
  have he' : (i:ℝ)+(p:ℝ)^2*(d:ℝ)=(N:ℝ) := by exact_mod_cast he
  have hp2 := pow_pos hpr 2
  have hev : (N:ℝ)/(p:ℝ)^2-d=(i:ℝ)/(p:ℝ)^2 := by field_simp; linarith only [he']
  change |(N:ℝ)/(p:ℝ)^2-((d:ℤ):ℝ)|≤δ
  rw [Int.cast_natCast,hev,abs_of_nonneg (by positivity),div_le_iff₀ hp2]
  have hn2 : (n:ℝ)^2 ≤ (p:ℝ)^2 := pow_le_pow_left₀ hnr.le hnp' 2
  have hi' : (i:ℝ)≤n := by exact_mod_cast hit.le
  nlinarith only [hi',mul_le_mul_of_nonneg_left hδn hnr.le,mul_le_mul_of_nonneg_right hn2 hδ]

theorem high (D k : ℕ) : ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, n^3 ≤ m+n → m+n ≤ n^D →
    ∃ P : Finset ℕ, P.card = k ∧ ∀ p ∈ P, p.Prime ∧
      p ∣ (∏ y ∈ Finset.Ioc m (m+n), y) ∧ ¬p^2 ∣ (∏ y ∈ Finset.Ioc m (m+n), y) := by
  classical
  let b := B (D+3)
  have cast : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [H1PrimeSupply.supply b,bad_small D,
    log_power_small (b+1) (100*(k+1:ℕ)) (by positivity),log_power_small b 1 (by norm_num),
    (tendsto_log_atTop.comp cast).eventually_ge_atTop 1,eventually_ge_atTop 2] with n supply ctrl hk hdelta hL hn
  intro m hlo hhi
  let N := m+n
  let L := log (n:ℝ)
  let w := width b n
  let δ := (L^b)⁻¹
  let H := ⌊w⌋₊
  let A := shortBand n b
  let F := bad N n H 1 δ
  let G := bad N n H 2 δ
  let good := A \ (F ∪ G)
  change 1 ≤ L at hL
  have hL' : 0<L := by linarith
  have hw : 0<w := by dsimp [w,width]; change 0 < (n:ℝ)/L^b; positivity
  have hδ : 0<δ := by dsimp [δ]; positivity
  have hδn : 1 ≤ (n:ℝ)*δ := by
    change 1 ≤ (n:ℝ)*(L^b)⁻¹
    rw [←div_eq_mul_inv,one_le_div (pow_pos hL' _)]
    simpa only [one_mul] using hdelta
  have hbound : (k:ℝ)*(100*L) ≤ w := by
    change _ ≤ (n:ℝ)/L^b
    rw [le_div_iff₀ (pow_pos hL' _)]
    have hh : (k:ℝ) ≤ (k+1:ℕ) := by exact_mod_cast (Nat.le_succ k)
    calc
      _ = 100*(k:ℝ)*L^(b+1) := by rw [pow_succ]; ring
      _ ≤ 100*(k+1:ℕ)*L^(b+1) := by gcongr
      _ ≤ _ := hk
  have hf : (F.card:ℝ)*(100*L)≤2*w := ctrl N hlo hhi 1 (Or.inl rfl)
  have hg : (G.card:ℝ)*(100*L)≤2*w := ctrl N hlo hhi 2 (Or.inr rfl)
  have hdis : A.card ≤ good.card+(F.card+G.card) := by
    have hpart := Finset.card_sdiff_add_card_inter A (F ∪ G)
    have hs := (Finset.card_le_card (Finset.inter_subset_right (s₁:=A) (s₂:=F ∪ G))).trans (Finset.card_union_le F G)
    dsimp [good]; omega
  have hsize : k ≤ good.card := by
    change w ≤ 4*(A.card:ℝ)*L at supply
    have hpart : (A.card:ℝ)≤good.card+(F.card+G.card:ℕ) := by exact_mod_cast hdis
    push_cast at hpart
    by_contra! ht
    have hlt : (good.card:ℝ)<k := by exact_mod_cast ht
    have hpos : 0<100*L := by positivity
    nlinarith only [mul_le_mul_of_nonneg_right hpart hpos.le,mul_lt_mul_of_pos_right hlt hpos,
      hbound,hf,hg,supply,hw]
  obtain ⟨P,hP,hcard⟩ := Finset.exists_subset_card_eq hsize
  refine ⟨P,hcard,?_⟩
  intro p hp
  obtain ⟨hA,hbad⟩ := Finset.mem_sdiff.mp (hP hp)
  obtain ⟨hy,hn'⟩ := Finset.mem_sdiff.mp hA
  obtain ⟨hle,hpr⟩ := Nat.mem_primesLE.mp hy
  have hnp : n<p := by by_contra! h; exact hn' (Nat.mem_primesLE.mpr ⟨h,hpr⟩)
  have htop : ⌊(n:ℝ)+w⌋₊=n+H := by rw [add_comm,Nat.floor_add_natCast hw.le,add_comm]
  have hpio : p ∈ Finset.Ioc n (n+H) := Finset.mem_Ioc.mpr ⟨hnp,htop ▸ hle⟩
  have hpw : (p:ℝ) ≤ n+(n:ℝ)*δ := by
    have hh := (Nat.cast_le.mpr hle : (p:ℝ) ≤ ⌊(n:ℝ)+w⌋₊)
    exact hh.trans (by simpa only [w,width,δ,L,div_eq_mul_inv] using Nat.floor_le (by positivity : 0 ≤ (n:ℝ)+w))
  refine ⟨hpr,good_prime (by omega) hpr hnp hpw hδ.le hδn ?_ ?_⟩
  · intro hh
    exact hbad (Finset.mem_union_left G (Finset.mem_filter.mpr ⟨hpio,hh⟩))
  · intro hh
    exact hbad (Finset.mem_union_right F (Finset.mem_filter.mpr ⟨hpio,hh⟩))

theorem polynomial : OMA.R_Erdos137_erdos_137_variants_multiple_powerful_factors_R2.H1 := by
  intro D k
  let E := max D 1+1
  filter_upwards [Erdos137Cubic.cubic_height 1 k, high E k,eventually_ge_atTop 2] with n low large hn
  intro m hm hD
  by_cases h : m+n ≤ n^3
  · exact low m hm (by simpa using h)
  · apply large m (by omega)
    have hn1 : 1 ≤ n := by omega
    have hn' : n ≤ n^(max D 1) := by simpa only [pow_one] using Nat.pow_le_pow_right hn1 (le_max_right D 1)
    have hm' := hD.trans (Nat.pow_le_pow_right hn1 (le_max_left D 1))
    dsimp [E]; rw [pow_succ]
    nlinarith only [hm',hn',Nat.mul_le_mul_left (n^(max D 1)) hn]

end H1Finish

theorem OMA.solution : OMA.R_Erdos137_erdos_137_variants_multiple_powerful_factors_R2.H1 :=
  H1Finish.polynomial
