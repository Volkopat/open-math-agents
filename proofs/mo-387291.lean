import OMAStatements.S_mo_387291
/-
Port of OpenAI, openai/math@3344da59991ed94f9ba711217b29c1d760badfa6, lean/OAI/Analysis/SphereIsometry. Modules bundled, imports and conditional simp lemmas adapted for Lean 4.33.1. Compactness and basis argument added for Taras Banakh’s question.
Credit: @my-other-github-account (port).
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
-- Adapted from OAI.Analysis.SphereIsometry.Model

namespace OAI

noncomputable section

namespace Tingley

universe u v

abbrev UnitSphere (X : Type u) [NormedAddCommGroup X] := {x : X // ‖x‖ = 1}

variable {X : Type u} {Y : Type v}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]

def normalize (x : X) (hx : x ≠ 0) : UnitSphere X :=
  ⟨‖x‖⁻¹ • x, norm_smul_inv_norm hx⟩

end Tingley

end

end OAI

-- Adapted from OAI.Analysis.SphereIsometry.Basic

namespace OAI

/-!
# Sphere maps and the maximal cross-radius defect

The sphere carries the ambient distance. All defects below use the actual sphere
isometry and ordinary real scalar multiplication; no extension law is assumed.
-/

noncomputable section

namespace Tingley

universe u v

variable {X : Type u} {Y : Type v}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]

omit [NormedSpace ℝ X] in
@[simp] theorem UnitSphere.norm_coe (x : UnitSphere X) : ‖(x : X)‖ = 1 := x.property

@[simp] theorem normalize_coe (x : X) (hx : x ≠ 0) :
    (normalize x hx : X) = ‖x‖⁻¹ • x := rfl

theorem norm_smul_normalize (x : X) (hx : x ≠ 0) :
    ‖x‖ • (normalize x hx : X) = x := by
  rw [normalize_coe, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx), one_smul]

instance UnitSphere.instNonempty [Nontrivial X] : Nonempty (UnitSphere X) := by
  obtain ⟨x, hx⟩ := exists_ne (0 : X)
  exact ⟨normalize x hx⟩

omit [NormedSpace ℝ X] [NormedSpace ℝ Y] in
theorem sphere_norm_sub (f : UnitSphere X ≃ᵢ UnitSphere Y) (x y : UnitSphere X) :
    ‖(f x : Y) - (f y : Y)‖ = ‖(x : X) - (y : X)‖ := by
  simpa only [Subtype.dist_eq, dist_eq_norm] using f.dist_eq x y

def signedDefect (f : UnitSphere X ≃ᵢ UnitSphere Y) (q : ℝ)
    (x y : UnitSphere X) : ℝ :=
  ‖(f x : Y) - q • (f y : Y)‖ - ‖(x : X) - q • (y : X)‖

def HasDefectBound (f : UnitSphere X ≃ᵢ UnitSphere Y) (M : ℝ) : Prop :=
  ∀ q ∈ Set.Icc (0 : ℝ) 1, ∀ x y : UnitSphere X, |signedDefect f q x y| ≤ M

def absoluteDefects (f : UnitSphere X ≃ᵢ UnitSphere Y) : Set ℝ :=
  {d | ∃ q ∈ Set.Icc (0 : ℝ) 1, ∃ x y : UnitSphere X, d = |signedDefect f q x y|}

def maxDefect (f : UnitSphere X ≃ᵢ UnitSphere Y) : ℝ := sSup (absoluteDefects f)

@[simp] theorem signedDefect_zero (f : UnitSphere X ≃ᵢ UnitSphere Y)
    (x y : UnitSphere X) : signedDefect f 0 x y = 0 := by
  simp [signedDefect]

@[simp] theorem signedDefect_one (f : UnitSphere X ≃ᵢ UnitSphere Y)
    (x y : UnitSphere X) : signedDefect f 1 x y = 0 := by
  simp [signedDefect, sphere_norm_sub]

theorem signedDefect_symm (f : UnitSphere X ≃ᵢ UnitSphere Y)
    (q : ℝ) (x y : UnitSphere X) :
    signedDefect f.symm q (f x) (f y) = -signedDefect f q x y := by
  simp only [signedDefect, IsometryEquiv.symm_apply_apply]
  ring

theorem HasDefectBound.symm {f : UnitSphere X ≃ᵢ UnitSphere Y} {M : ℝ}
    (h : HasDefectBound f M) : HasDefectBound f.symm M := by
  intro q hq x y
  obtain ⟨a, rfl⟩ := f.surjective x
  obtain ⟨b, rfl⟩ := f.surjective y
  simpa only [signedDefect_symm, abs_neg] using h q hq a b

theorem norm_sub_smul_lipschitz (x : X) (y : UnitSphere X) (q r : ℝ) :
    |‖x - q • (y : X)‖ - ‖x - r • (y : X)‖| ≤ |q - r| := by
  calc
    |‖x - q • (y : X)‖ - ‖x - r • (y : X)‖| ≤
        ‖(x - q • (y : X)) - (x - r • (y : X))‖ := abs_norm_sub_norm_le _ _
    _ = ‖(r - q) • (y : X)‖ := by
      congr 1
      rw [sub_smul]
      abel
    _ = |q - r| := by simp [norm_smul, Real.norm_eq_abs, abs_sub_comm]

theorem signedDefect_lipschitz (f : UnitSphere X ≃ᵢ UnitSphere Y)
    (q r : ℝ) (x y : UnitSphere X) :
    |signedDefect f q x y - signedDefect f r x y| ≤ 2 * |q - r| := by
  have hx := norm_sub_smul_lipschitz (x : X) y q r
  have hy := norm_sub_smul_lipschitz (f x : Y) (f y) q r
  have ht := abs_sub
    (‖(f x : Y) - q • (f y : Y)‖ - ‖(f x : Y) - r • (f y : Y)‖)
    (‖(x : X) - q • (y : X)‖ - ‖(x : X) - r • (y : X)‖)
  have he : signedDefect f q x y - signedDefect f r x y =
      (‖(f x : Y) - q • (f y : Y)‖ - ‖(f x : Y) - r • (f y : Y)‖) -
      (‖(x : X) - q • (y : X)‖ - ‖(x : X) - r • (y : X)‖) := by
    unfold signedDefect
    ring
  rw [he]
  linarith

theorem signedDefect_le_endpoints (f : UnitSphere X ≃ᵢ UnitSphere Y)
    {q : ℝ} (hq : q ∈ Set.Icc (0 : ℝ) 1) (x y : UnitSphere X) :
    |signedDefect f q x y| ≤ 2 * q ∧
      |signedDefect f q x y| ≤ 2 * (1 - q) := by
  constructor
  · simpa [abs_of_nonneg hq.1] using signedDefect_lipschitz f q 0 x y
  · simpa [abs_of_nonpos (sub_nonpos.mpr hq.2)] using
      signedDefect_lipschitz f q 1 x y

theorem signedDefect_abs_le_one (f : UnitSphere X ≃ᵢ UnitSphere Y)
    {q : ℝ} (hq : q ∈ Set.Icc (0 : ℝ) 1) (x y : UnitSphere X) :
    |signedDefect f q x y| ≤ 1 := by
  obtain ⟨h0, h1⟩ := signedDefect_le_endpoints f hq x y
  linarith

theorem absoluteDefects_bddAbove (f : UnitSphere X ≃ᵢ UnitSphere Y) :
    BddAbove (absoluteDefects f) := by
  refine ⟨1, ?_⟩
  rintro d ⟨q, hq, x, y, rfl⟩
  exact signedDefect_abs_le_one f hq x y

theorem zero_mem_absoluteDefects [Nonempty (UnitSphere X)]
    (f : UnitSphere X ≃ᵢ UnitSphere Y) : 0 ∈ absoluteDefects f := by
  let x : UnitSphere X := Classical.choice inferInstance
  exact ⟨0, ⟨le_rfl, zero_le_one⟩, x, x, by simp⟩

theorem hasDefectBound_maxDefect (f : UnitSphere X ≃ᵢ UnitSphere Y) :
    HasDefectBound f (maxDefect f) := by
  intro q hq x y
  exact le_csSup (absoluteDefects_bddAbove f) ⟨q, hq, x, y, rfl⟩

theorem maxDefect_nonneg [Nonempty (UnitSphere X)]
    (f : UnitSphere X ≃ᵢ UnitSphere Y) : 0 ≤ maxDefect f :=
  le_csSup (absoluteDefects_bddAbove f) (zero_mem_absoluteDefects f)

theorem absoluteDefects_symm (f : UnitSphere X ≃ᵢ UnitSphere Y) :
    absoluteDefects f.symm = absoluteDefects f := by
  ext d
  constructor
  · rintro ⟨q, hq, x, y, hd⟩
    obtain ⟨a, rfl⟩ := f.surjective x
    obtain ⟨b, rfl⟩ := f.surjective y
    exact ⟨q, hq, a, b, by simpa only [signedDefect_symm, abs_neg] using hd⟩
  · rintro ⟨q, hq, x, y, hd⟩
    exact ⟨q, hq, f x, f y, by simpa only [signedDefect_symm, abs_neg] using hd⟩

@[simp] theorem maxDefect_symm (f : UnitSphere X ≃ᵢ UnitSphere Y) :
    maxDefect f.symm = maxDefect f := by
  unfold maxDefect
  rw [absoluteDefects_symm]

theorem signedDefect_eq_zero_of_bound_zero {f : UnitSphere X ≃ᵢ UnitSphere Y}
    (h : HasDefectBound f 0) {q : ℝ} (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (x y : UnitSphere X) : signedDefect f q x y = 0 := by
  exact abs_nonpos_iff.mp (h q hq x y)

end Tingley

end

end OAI

-- Adapted from OAI.Analysis.SphereIsometry.UnitRepresentatives

namespace OAI

/-!
# Unit representatives, including the zero vector

The fallback unit vector is used only at zero. The exact error identity permits
normalization of arbitrary representatives of a unit ultranorm class.
-/

noncomputable section
namespace Tingley

universe u
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

def unitize (e : UnitSphere X) (a : X) : UnitSphere X := by
  classical
  exact if ha : a = 0 then e else normalize a ha

@[simp] theorem unitize_zero (e : UnitSphere X) : unitize e 0 = e := by
  simp [unitize]

theorem unitize_of_ne_zero (e : UnitSphere X) {a : X} (ha : a ≠ 0) :
    unitize e a = normalize a ha := by
  simp [unitize, ha]

theorem norm_smul_unitize (e : UnitSphere X) (a : X) :
    ‖a‖ • (unitize e a : X) = a := by
  by_cases ha : a = 0
  · simp [ha]
  · rw [unitize_of_ne_zero e ha]
    exact norm_smul_normalize a ha

theorem sub_unitize (e : UnitSphere X) (a : X) :
    a - (unitize e a : X) = (‖a‖ - 1) • (unitize e a : X) := by
  rw [sub_smul, norm_smul_unitize, one_smul]

theorem norm_sub_unitize (e : UnitSphere X) (a : X) :
    ‖a - (unitize e a : X)‖ = |‖a‖ - 1| := by
  rw [sub_unitize, norm_smul, Real.norm_eq_abs, UnitSphere.norm_coe, mul_one]

end Tingley

end

end OAI

-- Adapted from OAI.Analysis.SphereIsometry.UltraRealLimit

namespace OAI

/-!
# Real ultralimits of bounded sequences

Every bounded real sequence converges along an ultrafilter, by compactness of a
closed real interval. All identities below use this convergence or an explicitly
given limit, so they do not depend on the fallback value of `limUnder`.
-/

noncomputable section

open Filter
open scoped Topology

namespace Tingley

/-- A real sequence has a uniform absolute-value bound. -/
def RealSeqBounded (f : ℕ → ℝ) : Prop :=
  ∃ B : ℝ, ∀ n, |f n| ≤ B

namespace RealSeqBounded

variable {f g : ℕ → ℝ}

theorem add (hf : RealSeqBounded f) (hg : RealSeqBounded g) :
    RealSeqBounded (fun n => f n + g n) := by
  obtain ⟨B, hB⟩ := hf
  obtain ⟨C, hC⟩ := hg
  exact ⟨B + C, fun n => (abs_add_le (f n) (g n)).trans (add_le_add (hB n) (hC n))⟩

theorem neg (hf : RealSeqBounded f) : RealSeqBounded (fun n => -f n) := by
  obtain ⟨B, hB⟩ := hf
  refine ⟨B, fun n => ?_⟩
  simpa only [abs_neg] using hB n

theorem sub (hf : RealSeqBounded f) (hg : RealSeqBounded g) :
    RealSeqBounded (fun n => f n - g n) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem const_mul (c : ℝ) (hf : RealSeqBounded f) :
    RealSeqBounded (fun n => c * f n) := by
  obtain ⟨B, hB⟩ := hf
  refine ⟨|c| * B, fun n => ?_⟩
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hB n) (abs_nonneg c)

theorem abs (hf : RealSeqBounded f) : RealSeqBounded (fun n => |f n|) := by
  obtain ⟨B, hB⟩ := hf
  refine ⟨B, fun n => ?_⟩
  simpa only [abs_abs] using hB n

end RealSeqBounded

/-- The chosen real limit along an ultrafilter. Use `tendsto_realULim` to establish
that this value is a limit for a bounded sequence. -/
def realULim (U : Ultrafilter ℕ) (f : ℕ → ℝ) : ℝ :=
  Filter.limUnder (U : Filter ℕ) f

variable {f g : ℕ → ℝ}

/-- Bounded real sequences converge along every ultrafilter. -/
theorem tendsto_realULim (U : Ultrafilter ℕ) (hf : RealSeqBounded f) :
    Tendsto f (U : Filter ℕ) (𝓝 (realULim U f)) := by
  obtain ⟨B, hB⟩ := hf
  have hmem : Set.Icc (-B) B ∈ Ultrafilter.map f U := by
    change ∀ᶠ n in (U : Filter ℕ), f n ∈ Set.Icc (-B) B
    exact Filter.Eventually.of_forall fun n => abs_le.mp (hB n)
  obtain ⟨a, _ha, hlim⟩ :=
    isCompact_Icc.ultrafilter_le_nhds' (Ultrafilter.map f U) hmem
  have ha : Tendsto f (U : Filter ℕ) (𝓝 a) := hlim
  exact tendsto_nhds_limUnder ⟨a, ha⟩

/-- A known limit determines the chosen ultralimit, without a boundedness premise. -/
theorem realULim_eq_of_tendsto (U : Ultrafilter ℕ) {a : ℝ}
    (h : Tendsto f (U : Filter ℕ) (𝓝 a)) : realULim U f = a :=
  h.limUnder_eq

@[simp]
theorem realULim_const (U : Ultrafilter ℕ) (c : ℝ) :
    realULim U (fun _ : ℕ => c) = c :=
  realULim_eq_of_tendsto U tendsto_const_nhds

theorem realULim_add (U : Ultrafilter ℕ) (hf : RealSeqBounded f)
    (hg : RealSeqBounded g) :
    realULim U (fun n => f n + g n) = realULim U f + realULim U g :=
  realULim_eq_of_tendsto U ((tendsto_realULim U hf).add (tendsto_realULim U hg))

theorem realULim_sub (U : Ultrafilter ℕ) (hf : RealSeqBounded f)
    (hg : RealSeqBounded g) :
    realULim U (fun n => f n - g n) = realULim U f - realULim U g :=
  realULim_eq_of_tendsto U ((tendsto_realULim U hf).sub (tendsto_realULim U hg))

theorem realULim_const_mul (U : Ultrafilter ℕ) (c : ℝ) (hf : RealSeqBounded f) :
    realULim U (fun n => c * f n) = c * realULim U f :=
  realULim_eq_of_tendsto U ((tendsto_realULim U hf).const_mul c)

theorem realULim_abs (U : Ultrafilter ℕ) (hf : RealSeqBounded f) :
    realULim U (fun n => |f n|) = |realULim U f| :=
  realULim_eq_of_tendsto U (tendsto_realULim U hf).abs

/-- Eventual inequalities pass to the limits of bounded real sequences. -/
theorem realULim_le_realULim (U : Ultrafilter ℕ) (hf : RealSeqBounded f)
    (hg : RealSeqBounded g) (h : ∀ᶠ n in (U : Filter ℕ), f n ≤ g n) :
    realULim U f ≤ realULim U g :=
  le_of_tendsto_of_tendsto (tendsto_realULim U hf) (tendsto_realULim U hg) h

theorem realULim_le_of_eventually_le (U : Ultrafilter ℕ) (hf : RealSeqBounded f)
    {c : ℝ} (h : ∀ᶠ n in (U : Filter ℕ), f n ≤ c) : realULim U f ≤ c :=
  le_of_tendsto (tendsto_realULim U hf) h

/-- The actual free ultrafilter used for the bounded-sequence quotient. -/
def freeUltrafilter : Ultrafilter ℕ := Filter.hyperfilter ℕ

theorem freeUltrafilter_le_atTop : (freeUltrafilter : Filter ℕ) ≤ Filter.atTop :=
  Nat.hyperfilter_le_atTop

/-- Ordinary sequential convergence also holds along the fixed free ultrafilter. -/
theorem tendsto_freeUltrafilter_of_tendsto_atTop {α : Type*} [TopologicalSpace α]
    {a : ℕ → α} {x : α} (h : Tendsto a atTop (𝓝 x)) :
    Tendsto a (freeUltrafilter : Filter ℕ) (𝓝 x) :=
  h.mono_left freeUltrafilter_le_atTop

end Tingley

end

end OAI

-- Adapted from OAI.Analysis.SphereIsometry.UltraNormed

namespace OAI

/-!
# Bounded sequences with the ultralimit seminorm

The carrier below is a fresh wrapper, not the bounded submodule with its
inherited product topology. Only algebra is transported to the wrapper. Its
topology is then constructed from the ultralimit seminorm. The separation
quotient therefore identifies zero ultradistance, not eventual equality.
-/

noncomputable section

namespace Tingley

universe u

variable (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The algebraic submodule of uniformly bounded sequences. -/
def boundedSequenceSubmodule : Submodule ℝ (ℕ → X) where
  carrier := {a | ∃ B : ℝ, 0 ≤ B ∧ ∀ n, ‖a n‖ ≤ B}
  zero_mem' := ⟨0, le_rfl, by simp⟩
  add_mem' := by
    rintro a b ⟨A, hA, ha⟩ ⟨B, hB, hb⟩
    refine ⟨A + B, add_nonneg hA hB, fun n => ?_⟩
    exact (norm_add_le (a n) (b n)).trans (add_le_add (ha n) (hb n))
  smul_mem' := by
    rintro r a ⟨A, hA, ha⟩
    refine ⟨‖r‖ * A, mul_nonneg (norm_nonneg r) hA, fun n => ?_⟩
    simpa only [Pi.smul_apply, norm_smul] using
      mul_le_mul_of_nonneg_left (ha n) (norm_nonneg r)

/-- A fresh carrier on which only the ultralimit topology will be installed. -/
structure UltraSequence (U : Ultrafilter ℕ) (X : Type u)
    [NormedAddCommGroup X] [NormedSpace ℝ X] where
  val : boundedSequenceSubmodule X

namespace UltraSequence

variable (U : Ultrafilter ℕ)

/-- Algebraic identification; it transports no topology. -/
def algebraEquiv : UltraSequence U X ≃ boundedSequenceSubmodule X where
  toFun := UltraSequence.val
  invFun := UltraSequence.mk
  left_inv a := by cases a; rfl
  right_inv a := rfl

instance instAddCommGroup : AddCommGroup (UltraSequence U X) :=
  (algebraEquiv X U).addCommGroup

instance instModule : Module ℝ (UltraSequence U X) :=
  ({ algebraEquiv X U with map_add' := fun _ _ => rfl } :
    UltraSequence U X ≃+ boundedSequenceSubmodule X).module ℝ

instance instCoeFun : CoeFun (UltraSequence U X) (fun _ => ℕ → X) :=
  ⟨fun a => a.val.val⟩

variable {X U}

theorem ext {a b : UltraSequence U X} (h : ∀ n, a n = b n) : a = b := by
  have hv : a.val = b.val := Subtype.ext (funext h)
  cases a
  cases b
  cases hv
  rfl

/-- Construct a sequence from an actual uniform norm bound. -/
def ofBounded (U : Ultrafilter ℕ) (a : ℕ → X)
    (ha : ∃ B : ℝ, 0 ≤ B ∧ ∀ n, ‖a n‖ ≤ B) : UltraSequence U X :=
  ⟨⟨a, ha⟩⟩

@[simp] theorem ofBounded_apply (U : Ultrafilter ℕ) (a : ℕ → X)
    (ha : ∃ B : ℝ, 0 ≤ B ∧ ∀ n, ‖a n‖ ≤ B) (n : ℕ) :
    ofBounded U a ha n = a n := rfl

@[simp] theorem zero_apply (n : ℕ) : (0 : UltraSequence U X) n = 0 := rfl

@[simp] theorem add_apply (a b : UltraSequence U X) (n : ℕ) :
    (a + b) n = a n + b n := rfl

@[simp] theorem neg_apply (a : UltraSequence U X) (n : ℕ) : (-a) n = -a n := rfl

@[simp] theorem sub_apply (a b : UltraSequence U X) (n : ℕ) :
    (a - b) n = a n - b n := rfl

@[simp] theorem smul_apply (r : ℝ) (a : UltraSequence U X) (n : ℕ) :
    (r • a) n = r • a n := rfl

theorem bounded (a : UltraSequence U X) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n, ‖a n‖ ≤ B := a.val.property

theorem norm_bounded (a : UltraSequence U X) : RealSeqBounded (fun n => ‖a n‖) := by
  obtain ⟨B, _, hB⟩ := a.bounded
  exact ⟨B, fun n => by simpa only [abs_norm] using hB n⟩

/-- The actual ultralimit of coordinate norms. -/
def ultranorm (a : UltraSequence U X) : ℝ := realULim U (fun n => ‖a n‖)

theorem ultranorm_add_le (a b : UltraSequence U X) :
    ultranorm (a + b) ≤ ultranorm a + ultranorm b := by
  have h := realULim_le_realULim U (a + b).norm_bounded
    (a.norm_bounded.add b.norm_bounded)
    (Filter.Eventually.of_forall (fun n => norm_add_le (a n) (b n)))
  simpa only [ultranorm, add_apply, realULim_add U a.norm_bounded b.norm_bounded] using h

theorem ultranorm_smul (r : ℝ) (a : UltraSequence U X) :
    ultranorm (r • a) = ‖r‖ * ultranorm a := by
  simp only [ultranorm, smul_apply, norm_smul]
  exact realULim_const_mul U ‖r‖ a.norm_bounded

variable (X U)

/-- The proved seminorm; no bounded-vector convergence is asserted. -/
def seminorm : Seminorm ℝ (UltraSequence U X) :=
  Seminorm.of ultranorm ultranorm_add_le ultranorm_smul

instance instSeminormedAddCommGroup : SeminormedAddCommGroup (UltraSequence U X) :=
  (seminorm X U).toAddGroupSeminorm.toSeminormedAddCommGroup

instance instNormedSpace : NormedSpace ℝ (UltraSequence U X) where
  norm_smul_le r a := (ultranorm_smul r a).le

variable {X U}

/-- Constant bounded sequences. -/
def constant (U : Ultrafilter ℕ) (x : X) : UltraSequence U X :=
  ofBounded U (fun _ => x) ⟨‖x‖, norm_nonneg x, fun _ => le_rfl⟩

@[simp] theorem constant_apply (U : Ultrafilter ℕ) (x : X) (n : ℕ) :
    constant U x n = x := rfl

end UltraSequence

/-- The normed space obtained by identifying sequences at zero ultradistance. -/
abbrev UltraQuotient (U : Ultrafilter ℕ) (X : Type u)
    [NormedAddCommGroup X] [NormedSpace ℝ X] :=
  SeparationQuotient (UltraSequence U X)

variable {X} (U : Ultrafilter ℕ)

/-- Projection to the zero-ultranorm quotient. -/
def classOf (a : UltraSequence U X) : UltraQuotient U X := SeparationQuotient.mk a

theorem classOf_surjective (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X] :
    Function.Surjective (classOf U (X := X)) :=
  SeparationQuotient.surjective_mk

@[simp] theorem classOf_zero : classOf U (0 : UltraSequence U X) = 0 := rfl

@[simp] theorem classOf_add (a b : UltraSequence U X) :
    classOf U (a + b) = classOf U a + classOf U b := rfl

@[simp] theorem classOf_neg (a : UltraSequence U X) : classOf U (-a) = -classOf U a := rfl

@[simp] theorem classOf_sub (a b : UltraSequence U X) :
    classOf U (a - b) = classOf U a - classOf U b := rfl

@[simp] theorem classOf_smul (r : ℝ) (a : UltraSequence U X) :
    classOf U (r • a) = r • classOf U a := rfl

theorem norm_classOf (a : UltraSequence U X) :
    ‖classOf U a‖ = realULim U (fun n => ‖a n‖) := rfl

theorem norm_sub_classOf (a b : UltraSequence U X) :
    ‖classOf U a - classOf U b‖ = realULim U (fun n => ‖a n - b n‖) := by
  rw [← classOf_sub, norm_classOf]
  rfl

theorem classOf_eq_iff (a b : UltraSequence U X) :
    classOf U a = classOf U b ↔ realULim U (fun n => ‖a n - b n‖) = 0 := by
  rw [← norm_sub_classOf, norm_eq_zero, sub_eq_zero]

/-- Constant sequences embed the original space isometrically and linearly. -/
def constantEmbedding : X →ₗᵢ[ℝ] UltraQuotient U X where
  toFun x := classOf U (UltraSequence.constant U x)
  map_add' x y := by
    rw [← classOf_add]
    congr 1
  map_smul' r x := by
    rw [← classOf_smul]
    congr 1
  norm_map' x := by
    change ‖classOf U (UltraSequence.constant U x)‖ = ‖x‖
    rw [norm_classOf]
    exact realULim_const U ‖x‖

@[simp] theorem constantEmbedding_apply (x : X) :
    constantEmbedding U x = classOf U (UltraSequence.constant U x) := rfl

instance ultraQuotient_nontrivial [Nontrivial X] : Nontrivial (UltraQuotient U X) :=
  (constantEmbedding U (X := X)).injective.nontrivial

/-- The actual Banach completion of the normed ultralimit quotient. -/
abbrev UltraCompletion (U : Ultrafilter ℕ) (X : Type u)
    [NormedAddCommGroup X] [NormedSpace ℝ X] :=
  UniformSpace.Completion (UltraQuotient U X)

instance ultraCompletion_nontrivial [Nontrivial X] : Nontrivial (UltraCompletion U X) :=
  (UniformSpace.Completion.toComplₗᵢ : UltraQuotient U X →ₗᵢ[ℝ]
    UltraCompletion U X).injective.nontrivial

end Tingley

end

end OAI

-- Adapted from OAI.Analysis.SphereIsometry.UltraSphere

namespace OAI

/-!
# The actual sphere map on the ultranorm quotient

Unit representatives exist even when the original coordinates vanish. The map
and its inverse are induced coordinatewise, and every fixed real radius has the
exact ultralimit defect formula.
-/

noncomputable section
namespace Tingley
open Filter
open scoped Topology

universe u v
variable {X : Type u} {Y : Type v}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Every sequence of unit vectors is uniformly bounded. -/
def unitSequence (U : Ultrafilter ℕ) (s : ℕ → UnitSphere X) : UltraSequence U X :=
  UltraSequence.ofBounded U (fun n => (s n : X)) ⟨1, zero_le_one, fun n => by simp⟩

@[simp] theorem unitSequence_apply (U : Ultrafilter ℕ) (s : ℕ → UnitSphere X) (n : ℕ) :
    unitSequence U s n = (s n : X) := rfl

/-- The actual class of a sequence of unit vectors. -/
def unitClass (U : Ultrafilter ℕ) (s : ℕ → UnitSphere X) : UnitSphere (UltraQuotient U X) :=
  ⟨classOf U (unitSequence U s), by simp only [norm_classOf, unitSequence_apply,
    UnitSphere.norm_coe, realULim_const]⟩

@[simp] theorem unitClass_val (U : Ultrafilter ℕ) (s : ℕ → UnitSphere X) :
    (unitClass U s : UltraQuotient U X) = classOf U (unitSequence U s) := rfl

theorem norm_sub_unitClass (U : Ultrafilter ℕ) (s t : ℕ → UnitSphere X) :
    ‖(unitClass U s : UltraQuotient U X) - (unitClass U t : UltraQuotient U X)‖ =
      realULim U (fun n => ‖(s n : X) - (t n : X)‖) := by
  simpa only [unitClass_val, unitSequence_apply] using
    norm_sub_classOf U (unitSequence U s) (unitSequence U t)

theorem unitClass_eq_iff (U : Ultrafilter ℕ) (s t : ℕ → UnitSphere X) :
    unitClass U s = unitClass U t ↔ realULim U (fun n => ‖(s n : X) - (t n : X)‖) = 0 := by
  rw [Subtype.ext_iff]
  exact classOf_eq_iff U (unitSequence U s) (unitSequence U t)

theorem unitClass_surjective [Nontrivial X] (U : Ultrafilter ℕ) :
    Function.Surjective (unitClass U : (ℕ → UnitSphere X) → UnitSphere (UltraQuotient U X)) := by
  classical
  intro z
  obtain ⟨a, ha⟩ := classOf_surjective U X (z : UltraQuotient U X)
  let e : UnitSphere X := Classical.choice inferInstance
  let s : ℕ → UnitSphere X := fun n => unitize e (a n)
  have ha1 : realULim U (fun n => ‖a n‖) = 1 := by
    rw [← norm_classOf, ha]
    exact z.property
  have hlim : Tendsto (fun n => ‖a n‖) (U : Filter ℕ) (𝓝 (1 : ℝ)) := by
    simpa only [ha1] using tendsto_realULim U (UltraSequence.norm_bounded a)
  have he : realULim U (fun n => ‖a n - (s n : X)‖) = 0 := by
    apply realULim_eq_of_tendsto U
    simpa only [s, norm_sub_unitize, sub_self, abs_zero] using
      (hlim.sub (tendsto_const_nhds (x := (1 : ℝ)))).abs
  refine ⟨s, ?_⟩
  apply Subtype.ext
  change classOf U (unitSequence U s) = (z : UltraQuotient U X)
  rw [← ha]
  exact ((classOf_eq_iff U a (unitSequence U s)).2 he).symm

/-- Choice selects actual unit representatives after surjectivity is proved. -/
def unitRep [Nontrivial X] (U : Ultrafilter ℕ) (z : UnitSphere (UltraQuotient U X)) :
    ℕ → UnitSphere X :=
  Classical.choose (unitClass_surjective U z)

@[simp] theorem unitRep_spec [Nontrivial X] (U : Ultrafilter ℕ)
    (z : UnitSphere (UltraQuotient U X)) : unitClass U (unitRep U z) = z :=
  Classical.choose_spec (unitClass_surjective U z)

theorem unitClass_map_eq (U : Ultrafilter ℕ) (f : UnitSphere X ≃ᵢ UnitSphere Y)
    (s t : ℕ → UnitSphere X) (h : unitClass U s = unitClass U t) :
    unitClass U (fun n => f (s n)) = unitClass U (fun n => f (t n)) := by
  apply (unitClass_eq_iff U _ _).2
  simpa only [sphere_norm_sub] using (unitClass_eq_iff U s t).1 h

def ultraSphereMap [Nontrivial X] (U : Ultrafilter ℕ) (f : UnitSphere X ≃ᵢ UnitSphere Y)
    (z : UnitSphere (UltraQuotient U X)) : UnitSphere (UltraQuotient U Y) :=
  unitClass U (fun n => f (unitRep U z n))

@[simp] theorem ultraSphereMap_unitClass [Nontrivial X] (U : Ultrafilter ℕ)
    (f : UnitSphere X ≃ᵢ UnitSphere Y) (s : ℕ → UnitSphere X) :
    ultraSphereMap U f (unitClass U s) = unitClass U (fun n => f (s n)) :=
  unitClass_map_eq U f _ s (unitRep_spec U (unitClass U s))

theorem ultraSphereMap_isometry [Nontrivial X] (U : Ultrafilter ℕ)
    (f : UnitSphere X ≃ᵢ UnitSphere Y) : Isometry (ultraSphereMap U f) := by
  apply Isometry.of_dist_eq
  intro z w
  calc
    dist (ultraSphereMap U f z) (ultraSphereMap U f w) =
        dist (unitClass U (unitRep U z)) (unitClass U (unitRep U w)) := by
      simp only [ultraSphereMap, Subtype.dist_eq, dist_eq_norm, norm_sub_unitClass,
        sphere_norm_sub]
    _ = dist z w := by rw [unitRep_spec, unitRep_spec]

/-- Surjectivity comes from the actual coordinatewise inverse, not from isometry alone. -/
def ultraSphereEquiv [Nontrivial X] [Nontrivial Y] (U : Ultrafilter ℕ)
    (f : UnitSphere X ≃ᵢ UnitSphere Y) :
    UnitSphere (UltraQuotient U X) ≃ᵢ UnitSphere (UltraQuotient U Y) where
  toFun := ultraSphereMap U f
  invFun := ultraSphereMap U f.symm
  left_inv z := by
    obtain ⟨s, rfl⟩ := unitClass_surjective U z
    simp only [ultraSphereMap_unitClass, IsometryEquiv.symm_apply_apply]
  right_inv z := by
    obtain ⟨s, rfl⟩ := unitClass_surjective U z
    simp only [ultraSphereMap_unitClass, IsometryEquiv.apply_symm_apply]
  isometry_toFun := ultraSphereMap_isometry U f

@[simp] theorem ultraSphereEquiv_unitClass [Nontrivial X] [Nontrivial Y]
    (U : Ultrafilter ℕ) (f : UnitSphere X ≃ᵢ UnitSphere Y) (s : ℕ → UnitSphere X) :
    ultraSphereEquiv U f (unitClass U s) = unitClass U (fun n => f (s n)) :=
  ultraSphereMap_unitClass U f s

@[simp] theorem ultraSphereEquiv_symm [Nontrivial X] [Nontrivial Y]
    (U : Ultrafilter ℕ) (f : UnitSphere X ≃ᵢ UnitSphere Y) :
    (ultraSphereEquiv U f).symm = ultraSphereEquiv U f.symm := by
  ext z
  rfl

/-- The radius-scaled norm is inherited from the linear quotient projection. -/
theorem norm_sub_smul_unitClass (U : Ultrafilter ℕ) (q : ℝ) (s t : ℕ → UnitSphere X) :
    ‖(unitClass U s : UltraQuotient U X) - q • (unitClass U t : UltraQuotient U X)‖ =
      realULim U (fun n => ‖(s n : X) - q • (t n : X)‖) := by
  change ‖classOf U (unitSequence U s) - q • classOf U (unitSequence U t)‖ = _
  rw [← classOf_smul, ← classOf_sub, norm_classOf]
  rfl

theorem unitPairNorm_bounded (q : ℝ) (s t : ℕ → UnitSphere X) :
    RealSeqBounded (fun n => ‖(s n : X) - q • (t n : X)‖) := by
  refine ⟨1 + |q|, fun n => ?_⟩
  rw [abs_of_nonneg (norm_nonneg _)]
  calc
    ‖(s n : X) - q • (t n : X)‖ ≤ ‖(s n : X)‖ + ‖q • (t n : X)‖ := norm_sub_le _ _
    _ = 1 + |q| := by simp only [norm_smul, Real.norm_eq_abs, UnitSphere.norm_coe, mul_one]

theorem signedDefect_sequence_bounded (f : UnitSphere X ≃ᵢ UnitSphere Y)
    (q : ℝ) (s t : ℕ → UnitSphere X) :
    RealSeqBounded (fun n => signedDefect f q (s n) (t n)) :=
  (unitPairNorm_bounded q (fun n => f (s n)) (fun n => f (t n))).sub
    (unitPairNorm_bounded q s t)

/-- Exact defect formula at every fixed real radius. -/
theorem signedDefect_ultraSphereEquiv [Nontrivial X] [Nontrivial Y]
    (U : Ultrafilter ℕ) (f : UnitSphere X ≃ᵢ UnitSphere Y) (q : ℝ)
    (s t : ℕ → UnitSphere X) :
    signedDefect (ultraSphereEquiv U f) q (unitClass U s) (unitClass U t) =
      realULim U (fun n => signedDefect f q (s n) (t n)) := by
  simp only [signedDefect, ultraSphereEquiv_unitClass, norm_sub_smul_unitClass]
  exact (realULim_sub U
    (unitPairNorm_bounded q (fun n => f (s n)) (fun n => f (t n)))
    (unitPairNorm_bounded q s t)).symm

/-- One ultrafilter transfers the bound for each arbitrarily chosen real radius. -/
theorem HasDefectBound.ultraSphereEquiv [Nontrivial X] [Nontrivial Y]
    {f : UnitSphere X ≃ᵢ UnitSphere Y} {M : ℝ} (h : HasDefectBound f M)
    (U : Ultrafilter ℕ) : HasDefectBound (ultraSphereEquiv U f) M := by
  intro q hq z w
  obtain ⟨s, rfl⟩ := unitClass_surjective U z
  obtain ⟨t, rfl⟩ := unitClass_surjective U w
  rw [signedDefect_ultraSphereEquiv, ← realULim_abs U (signedDefect_sequence_bounded f q s t)]
  exact realULim_le_of_eventually_le U (signedDefect_sequence_bounded f q s t).abs
    (Filter.Eventually.of_forall fun n => h q hq (s n) (t n))

end Tingley

end

end OAI

-- Adapted from OAI.Analysis.SphereIsometry.DefectSequence

namespace OAI

/-!
# A positive signed extremal sequence at a fixed radius

One fixed free ultrafilter chooses the orientation and the radius. The conclusion
is convergence along that actual filter, not an asserted compactness of spheres.
-/

noncomputable section
namespace Tingley
open Filter
open scoped Topology

universe u v
variable {X : Type u} {Y : Type v}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Uniform radius control replaces a varying radius by its actual scalar limit. -/
theorem tendsto_signedDefect_fixed_radius
    (f : UnitSphere X ≃ᵢ UnitSphere Y) (x y : ℕ → UnitSphere X)
    (q : ℕ → ℝ) {l : Filter ℕ} {t M : ℝ}
    (hq : Tendsto q l (𝓝 t))
    (hD : Tendsto (fun n => signedDefect f (q n) (x n) (y n)) l (𝓝 M)) :
    Tendsto (fun n => signedDefect f t (x n) (y n)) l (𝓝 M) := by
  have herr : Tendsto (fun n => 2 * |q n - t|) l (𝓝 0) := by
    simpa using ((hq.sub (tendsto_const_nhds (x := t))).abs.const_mul 2)
  have hlo := hD.sub herr
  have hhi := hD.add herr
  simp only [sub_zero, add_zero] at hlo hhi
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hhi
  · intro n
    change signedDefect f (q n) (x n) (y n) - 2 * |q n - t| ≤
      signedDefect f t (x n) (y n)
    have h := (abs_le.mp (signedDefect_lipschitz f (q n) t (x n) (y n))).2
    linarith
  · intro n
    change signedDefect f t (x n) (y n) ≤
      signedDefect f (q n) (x n) (y n) + 2 * |q n - t|
    have h := (abs_le.mp (signedDefect_lipschitz f (q n) t (x n) (y n))).1
    linarith

/-- Positive limiting defect forces a strictly interior radius. -/
theorem radius_interior_of_positive_defect_limit
    (f : UnitSphere X ≃ᵢ UnitSphere Y) (x y : ℕ → UnitSphere X)
    (U : Ultrafilter ℕ) {t M : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hM : 0 < M)
    (hD : Tendsto (fun n => signedDefect f t (x n) (y n)) (U : Filter ℕ) (𝓝 M)) :
    t ∈ Set.Ioo (0 : ℝ) 1 := by
  have habs : Tendsto (fun n => |signedDefect f t (x n) (y n)|)
      (U : Filter ℕ) (𝓝 M) := by
    simpa only [abs_of_pos hM] using hD.abs
  have h0 : M ≤ 2 * t :=
    le_of_tendsto_of_tendsto' habs tendsto_const_nhds
      (fun n => (signedDefect_le_endpoints f ht (x n) (y n)).1)
  have h1 : M ≤ 2 * (1 - t) :=
    le_of_tendsto_of_tendsto' habs tendsto_const_nhds
      (fun n => (signedDefect_le_endpoints f ht (x n) (y n)).2)
  constructor <;> linarith

/-- The absolute supremum has actual fixed-radius signed witnesses in one orientation. -/
theorem exists_fixed_radius_defect_sequence [Nontrivial X]
    (f : UnitSphere X ≃ᵢ UnitSphere Y) (hM : 0 < maxDefect f) :
    ∃ t : ℝ, t ∈ Set.Ioo (0 : ℝ) 1 ∧
      ((∃ x y : ℕ → UnitSphere X,
          Tendsto (fun n => signedDefect f t (x n) (y n))
            (freeUltrafilter : Filter ℕ) (𝓝 (maxDefect f))) ∨
       (∃ x y : ℕ → UnitSphere Y,
          Tendsto (fun n => signedDefect f.symm t (x n) (y n))
            (freeUltrafilter : Filter ℕ) (𝓝 (maxDefect f)))) := by
  classical
  obtain ⟨d, _, hdlim, hdmem⟩ := exists_seq_tendsto_sSup
    (show (absoluteDefects f).Nonempty from ⟨0, zero_mem_absoluteDefects f⟩)
    (absoluteDefects_bddAbove f)
  change ∀ n, ∃ q ∈ Set.Icc (0 : ℝ) 1,
    ∃ x y : UnitSphere X, d n = |signedDefect f q x y| at hdmem
  choose q hq x y hd using hdmem
  have habs : Tendsto (fun n => |signedDefect f (q n) (x n) (y n)|)
      (freeUltrafilter : Filter ℕ) (𝓝 (maxDefect f)) := by
    have h := tendsto_freeUltrafilter_of_tendsto_atTop hdlim
    have heq : d = fun n => |signedDefect f (q n) (x n) (y n)| := funext hd
    simpa only [heq, maxDefect] using h
  have hqb : RealSeqBounded q := by
    refine ⟨1, fun n => ?_⟩
    simpa only [abs_of_nonneg (hq n).1] using (hq n).2
  let t := realULim freeUltrafilter q
  have hqt : Tendsto q (freeUltrafilter : Filter ℕ) (𝓝 t) :=
    tendsto_realULim freeUltrafilter hqb
  have ht : t ∈ Set.Icc (0 : ℝ) 1 := by
    exact ⟨le_of_tendsto_of_tendsto' tendsto_const_nhds hqt (fun n => (hq n).1),
      le_of_tendsto_of_tendsto' hqt tendsto_const_nhds (fun n => (hq n).2)⟩
  rcases freeUltrafilter.em (fun n => 0 ≤ signedDefect f (q n) (x n) (y n)) with hpos | hneg
  · have hsign : Tendsto (fun n => signedDefect f (q n) (x n) (y n))
        (freeUltrafilter : Filter ℕ) (𝓝 (maxDefect f)) := by
      apply habs.congr'
      filter_upwards [hpos] with n hn
      exact abs_of_nonneg hn
    have hfixed := tendsto_signedDefect_fixed_radius f x y q hqt hsign
    exact ⟨t, radius_interior_of_positive_defect_limit f x y freeUltrafilter ht hM hfixed,
      Or.inl ⟨x, y, hfixed⟩⟩
  · have hsign : Tendsto (fun n => signedDefect f.symm (q n) (f (x n)) (f (y n)))
        (freeUltrafilter : Filter ℕ) (𝓝 (maxDefect f)) := by
      apply habs.congr'
      filter_upwards [hneg] with n hn
      rw [signedDefect_symm, abs_of_nonpos (le_of_lt (lt_of_not_ge hn))]
    have hfixed := tendsto_signedDefect_fixed_radius f.symm
      (fun n => f (x n)) (fun n => f (y n)) q hqt hsign
    exact ⟨t, radius_interior_of_positive_defect_limit f.symm
      (fun n => f (x n)) (fun n => f (y n)) freeUltrafilter ht hM hfixed,
      Or.inr ⟨_, _, hfixed⟩⟩

end Tingley

end

end OAI

-- Adapted from OAI.Analysis.SphereIsometry.SphereCompletion

namespace OAI

/-!
# Unit spheres and completion

The unit sphere of a normed space is dense in the unit sphere of its ambient
completion. This identifies its metric completion with that completed sphere.
An actual sphere isometry and its inverse therefore extend to the completed
spheres, with exact preservation of the ambient fixed-radius defect.

No completeness of the original spaces, compactness, or separability is used.
-/

noncomputable section

open UniformSpace

namespace Tingley

universe u v

variable {E : Type u} {F : Type v}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A unit sphere is complete when its ambient normed space is complete. -/
instance UnitSphere.instCompleteSpace [CompleteSpace E] : CompleteSpace (UnitSphere E) :=
  (isClosed_eq continuous_norm continuous_const).completeSpace_coe

/-- The canonical ambient completion embedding restricted to the unit sphere. -/
def sphereCoe (E : Type u) [NormedAddCommGroup E] :
    UnitSphere E → UnitSphere (Completion E) := fun x =>
  ⟨(x : E), by simpa only [Completion.norm_coe] using x.property⟩

omit [NormedSpace ℝ E] in
@[simp] theorem sphereCoe_val (x : UnitSphere E) :
    (sphereCoe E x : Completion E) = ((x : E) : Completion E) := rfl

theorem sphereCoe_isometry (E : Type u) [NormedAddCommGroup E] :
    Isometry (sphereCoe E) := by
  apply Isometry.of_dist_eq
  intro x y
  change dist ((x : E) : Completion E) ((y : E) : Completion E) =
    dist (x : E) (y : E)
  exact Completion.dist_eq (x : E) (y : E)

private theorem norm_normalize_sub (x : E) (hx : x ≠ 0) :
    ‖(normalize x hx : E) - x‖ = |1 - ‖x‖| := by
  calc
    _ = ‖(1 - ‖x‖) • (normalize x hx : E)‖ := by
      congr 1
      rw [sub_smul, one_smul, norm_smul_normalize]
    _ = |1 - ‖x‖| := by
      rw [norm_smul, Real.norm_eq_abs, UnitSphere.norm_coe, mul_one]

/-- Normalizing close old vectors proves density in the completed unit sphere. -/
theorem sphereCoe_denseRange (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    DenseRange (sphereCoe E) := by
  refine Metric.denseRange_iff.mpr ?_
  intro z ε hε
  have hδ : 0 < min (1 : ℝ) (ε / 2) := lt_min zero_lt_one (by linarith)
  obtain ⟨x, hdx⟩ :=
    (Completion.denseRange_coe : DenseRange ((↑) : E → Completion E)).exists_dist_lt
      (z : Completion E) hδ
  have habs : |1 - ‖x‖| ≤ dist (z : Completion E) (x : Completion E) := by
    simpa only [UnitSphere.norm_coe, Completion.norm_coe, dist_eq_norm] using
      abs_norm_sub_norm_le (z : Completion E) (x : Completion E)
  have hnorm : 0 < ‖x‖ := by
    have ha := (le_abs_self (1 - ‖x‖)).trans habs
    have hb := hdx.trans_le (min_le_left (1 : ℝ) (ε / 2))
    linarith
  have hx : x ≠ 0 := norm_pos_iff.mp hnorm
  have hrad : dist (x : Completion E) ((normalize x hx : E) : Completion E) =
      |1 - ‖x‖| := by
    rw [dist_comm, Completion.dist_eq, dist_eq_norm, norm_normalize_sub]
  have hsmall := hdx.trans_le (min_le_right (1 : ℝ) (ε / 2))
  refine ⟨normalize x hx, ?_⟩
  change dist (z : Completion E) ((normalize x hx : E) : Completion E) < ε
  calc
    _ ≤ dist (z : Completion E) (x : Completion E) +
        dist (x : Completion E) ((normalize x hx : E) : Completion E) :=
      dist_triangle _ _ _
    _ = dist (z : Completion E) (x : Completion E) + |1 - ‖x‖| := by rw [hrad]
    _ ≤ 2 * dist (z : Completion E) (x : Completion E) := by linarith
    _ < ε := by linarith

private def sphereCompletionMap (E : Type u) [NormedAddCommGroup E] :
    Completion (UnitSphere E) → UnitSphere (Completion E) :=
  Completion.extension (sphereCoe E)

private theorem sphereCompletionMap_isometry (E : Type u) [NormedAddCommGroup E] :
    Isometry (sphereCompletionMap E) :=
  (sphereCoe_isometry E).completion_extension

omit [NormedSpace ℝ E] in
private theorem sphereCompletionMap_coe (x : UnitSphere E) :
    sphereCompletionMap E (x : Completion (UnitSphere E)) = sphereCoe E x :=
  Completion.extension_coe (sphereCoe_isometry E).uniformContinuous x

private theorem sphereCompletionMap_surjective
    (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    Function.Surjective (sphereCompletionMap E) := by
  have hclosed : IsClosed (Set.range (sphereCompletionMap E)) :=
    (sphereCompletionMap_isometry E).isClosedEmbedding.isClosed_range
  exact isClosed_property (sphereCoe_denseRange E) hclosed fun x =>
    ⟨(x : Completion (UnitSphere E)), sphereCompletionMap_coe x⟩

/-- The metric completion of the old sphere is the sphere of the ambient completion. -/
def sphereCompletionEquiv (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    Completion (UnitSphere E) ≃ᵢ UnitSphere (Completion E) :=
  { Equiv.ofBijective (sphereCompletionMap E)
      ⟨(sphereCompletionMap_isometry E).injective, sphereCompletionMap_surjective E⟩ with
    isometry_toFun := sphereCompletionMap_isometry E }

@[simp] theorem sphereCompletionEquiv_coe (x : UnitSphere E) :
    sphereCompletionEquiv E (x : Completion (UnitSphere E)) = sphereCoe E x :=
  sphereCompletionMap_coe x

@[simp] theorem sphereCompletionEquiv_symm_coe (x : UnitSphere E) :
    (sphereCompletionEquiv E).symm (sphereCoe E x) =
      (x : Completion (UnitSphere E)) := by
  apply (sphereCompletionEquiv E).injective
  simp only [IsometryEquiv.apply_symm_apply, sphereCompletionEquiv_coe]

private def sphereIsometryCompletion (f : UnitSphere E ≃ᵢ UnitSphere F) :
    Completion (UnitSphere E) ≃ᵢ Completion (UnitSphere F) where
  toFun := Completion.map f
  invFun := Completion.map f.symm
  left_inv x := by
    have h := congr_fun
      (Completion.map_comp f.symm.isometry.uniformContinuous f.isometry.uniformContinuous) x
    rw [f.symm_comp_self, Completion.map_id] at h
    exact h
  right_inv y := by
    have h := congr_fun
      (Completion.map_comp f.isometry.uniformContinuous f.symm.isometry.uniformContinuous) y
    rw [f.self_comp_symm, Completion.map_id] at h
    exact h
  isometry_toFun := f.isometry.completion_map

/-- Extend the actual sphere isometry and its inverse through the sphere completions. -/
def completedSphereEquiv (f : UnitSphere E ≃ᵢ UnitSphere F) :
    UnitSphere (Completion E) ≃ᵢ UnitSphere (Completion F) :=
  ((sphereCompletionEquiv E).symm.trans (sphereIsometryCompletion f)).trans
    (sphereCompletionEquiv F)

@[simp] theorem completedSphereEquiv_coe (f : UnitSphere E ≃ᵢ UnitSphere F)
    (x : UnitSphere E) :
    completedSphereEquiv f (sphereCoe E x) = sphereCoe F (f x) := by
  change sphereCompletionEquiv F
    (Completion.map f ((sphereCompletionEquiv E).symm (sphereCoe E x))) = sphereCoe F (f x)
  rw [sphereCompletionEquiv_symm_coe, Completion.map_coe f.isometry.uniformContinuous,
    sphereCompletionEquiv_coe]

@[simp] theorem completedSphereEquiv_symm (f : UnitSphere E ≃ᵢ UnitSphere F) :
    (completedSphereEquiv f).symm = completedSphereEquiv f.symm := by
  apply IsometryEquiv.ext
  intro y
  rfl

/-- The canonical ambient embedding preserves all real scalar difference norms. -/
theorem norm_completion_sub_smul (x y : E) (q : ℝ) :
    ‖(x : Completion E) - q • (y : Completion E)‖ = ‖x - q • y‖ := by
  rw [← Completion.coe_smul, ← Completion.coe_sub, Completion.norm_coe]

/-- The defect on embedded old points is preserved for every real scalar. -/
@[simp] theorem signedDefect_completedSphereEquiv_coe
    (f : UnitSphere E ≃ᵢ UnitSphere F) (q : ℝ) (x y : UnitSphere E) :
    signedDefect (completedSphereEquiv f) q (sphereCoe E x) (sphereCoe E y) =
      signedDefect f q x y := by
  unfold signedDefect
  rw [completedSphereEquiv_coe, completedSphereEquiv_coe]
  simp only [sphereCoe_val, norm_completion_sub_smul]

/-- The fixed-radius signed defect is continuous on pairs of unit points. -/
theorem continuous_signedDefect_pair (f : UnitSphere E ≃ᵢ UnitSphere F) (q : ℝ) :
    Continuous (fun p : UnitSphere E × UnitSphere E => signedDefect f q p.1 p.2) := by
  have hx : Continuous (fun p : UnitSphere E × UnitSphere E => (p.1 : E)) :=
    continuous_subtype_val.comp continuous_fst
  have hy : Continuous (fun p : UnitSphere E × UnitSphere E => (p.2 : E)) :=
    continuous_subtype_val.comp continuous_snd
  have hfx : Continuous (fun p : UnitSphere E × UnitSphere E => (f p.1 : F)) :=
    continuous_subtype_val.comp (f.continuous.comp continuous_fst)
  have hfy : Continuous (fun p : UnitSphere E × UnitSphere E => (f p.2 : F)) :=
    continuous_subtype_val.comp (f.continuous.comp continuous_snd)
  exact (hfx.sub (hfy.const_smul q)).norm.sub (hx.sub (hy.const_smul q)).norm

/-- Every fixed-radius bound passes to all pairs in the completed spheres. -/
theorem HasDefectBound.completedSphereEquiv {f : UnitSphere E ≃ᵢ UnitSphere F} {M : ℝ}
    (h : HasDefectBound f M) : HasDefectBound (completedSphereEquiv f) M := by
  intro q hq x y
  have hclosed : IsClosed {p : UnitSphere (Completion E) × UnitSphere (Completion E) |
      |signedDefect (Tingley.completedSphereEquiv f) q p.1 p.2| ≤ M} :=
    isClosed_le (continuous_signedDefect_pair (Tingley.completedSphereEquiv f) q).abs continuous_const
  exact isClosed_property2
    (p := fun a b : UnitSphere (Completion E) =>
      |signedDefect (Tingley.completedSphereEquiv f) q a b| ≤ M)
    (sphereCoe_denseRange E) hclosed
    (fun a b => by simpa only [signedDefect_completedSphereEquiv_coe] using h q hq a b) x y

end Tingley

end

end OAI

-- Adapted from OAI.Analysis.SphereIsometry.DefectAttainment

namespace OAI

/-!
# Positive maximal defect is attained on actual completed ultranorm spaces

The final spaces, sphere isometry, inverse, and bound are all constructed. The
orientation disjunction keeps the same original maximal absolute defect.
-/

noncomputable section
namespace Tingley
open Filter
open scoped Topology

universe u v
variable {X : Type u} {Y : Type v}
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [Nontrivial X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y] [Nontrivial Y]

/-- The actual coordinatewise sphere equivalence followed by ambient completion. -/
def completedUltraSphereEquiv (U : Ultrafilter ℕ) (f : UnitSphere X ≃ᵢ UnitSphere Y) :
    UnitSphere (UltraCompletion U X) ≃ᵢ UnitSphere (UltraCompletion U Y) :=
  completedSphereEquiv (ultraSphereEquiv U f)

@[simp] theorem completedUltraSphereEquiv_symm (U : Ultrafilter ℕ)
    (f : UnitSphere X ≃ᵢ UnitSphere Y) :
    (completedUltraSphereEquiv U f).symm = completedUltraSphereEquiv U f.symm := by
  simp only [completedUltraSphereEquiv, completedSphereEquiv_symm, ultraSphereEquiv_symm]

/-- Exact fixed-radius formula on the canonical embedded unit classes. -/
theorem signedDefect_completedUltraSphereEquiv (U : Ultrafilter ℕ)
    (f : UnitSphere X ≃ᵢ UnitSphere Y) (q : ℝ) (s t : ℕ → UnitSphere X) :
    signedDefect (completedUltraSphereEquiv U f) q
      (sphereCoe (UltraQuotient U X) (unitClass U s))
      (sphereCoe (UltraQuotient U X) (unitClass U t)) =
        realULim U (fun n => signedDefect f q (s n) (t n)) := by
  exact (signedDefect_completedSphereEquiv_coe (ultraSphereEquiv U f) q
    (unitClass U s) (unitClass U t)).trans (signedDefect_ultraSphereEquiv U f q s t)

theorem HasDefectBound.completedUltraSphereEquiv
    {f : UnitSphere X ≃ᵢ UnitSphere Y} {M : ℝ} (h : HasDefectBound f M)
    (U : Ultrafilter ℕ) : HasDefectBound (completedUltraSphereEquiv U f) M :=
  (h.ultraSphereEquiv U).completedSphereEquiv

/-- Positive original maximal absolute defect is attained, with the same global
bound, in one orientation on explicitly constructed nonzero real Banach spaces. -/
theorem positive_maxDefect_attained_or_inverse
    (f : UnitSphere X ≃ᵢ UnitSphere Y) (hM : 0 < maxDefect f) :
    let F := completedUltraSphereEquiv freeUltrafilter f
    HasDefectBound F (maxDefect f) ∧
    HasDefectBound F.symm (maxDefect f) ∧
    ∃ t : ℝ, t ∈ Set.Ioo (0 : ℝ) 1 ∧
      ((∃ x y : UnitSphere (UltraCompletion freeUltrafilter X),
          signedDefect F t x y = maxDefect f) ∨
       (∃ x y : UnitSphere (UltraCompletion freeUltrafilter Y),
          signedDefect F.symm t x y = maxDefect f)) := by
  have hbound := (hasDefectBound_maxDefect f).completedUltraSphereEquiv freeUltrafilter
  refine ⟨hbound, hbound.symm, ?_⟩
  obtain ⟨t, ht, hseq | hseq⟩ := exists_fixed_radius_defect_sequence f hM
  · obtain ⟨s, r, hlim⟩ := hseq
    refine ⟨t, ht, Or.inl ⟨sphereCoe _ (unitClass freeUltrafilter s),
      sphereCoe _ (unitClass freeUltrafilter r), ?_⟩⟩
    rw [signedDefect_completedUltraSphereEquiv]
    exact realULim_eq_of_tendsto freeUltrafilter hlim
  · obtain ⟨s, r, hlim⟩ := hseq
    refine ⟨t, ht, Or.inr ⟨sphereCoe _ (unitClass freeUltrafilter s),
      sphereCoe _ (unitClass freeUltrafilter r), ?_⟩⟩
    rw [completedUltraSphereEquiv_symm, signedDefect_completedUltraSphereEquiv]
    exact realULim_eq_of_tendsto freeUltrafilter hlim

end Tingley

end

end OAI

-- Adapted from OAI.Analysis.SphereIsometry.RadialContact

namespace OAI

/-!
# Contact of a ray from an interior point with the unit sphere

The contact radius exists by the intermediate value theorem on a real interval.
A quantitative comparison proves both uniqueness and Lipschitz continuity. No
compactness of the ambient unit ball or support functional is used.
-/

noncomputable section

namespace Tingley

universe u

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Comparison of two contacts, with the radii in increasing order. The vectors
need not be unit vectors for this estimate. -/
theorem contact_comparison_ordered (c v w : X) {r s : ℝ}
    (hr : 0 ≤ r) (hrs : r ≤ s)
    (hvr : ‖c + r • v‖ = 1) (hws : ‖c + s • w‖ = 1) :
    (1 - ‖c‖) * (s - r) ≤ (r * s) * ‖v - w‖ := by
  have hs : 0 ≤ s := hr.trans hrs
  have hsr : 0 ≤ s - r := sub_nonneg.mpr hrs
  have hprod : 0 ≤ r * s := mul_nonneg hr hs
  have he : s • (c + r • v) =
      (s - r) • c + r • (c + s • w) + (r * s) • (v - w) := by
    simp only [smul_add, sub_smul, smul_sub, smul_smul, mul_comm s r]
    abel
  have hbound : s ≤ (s - r) * ‖c‖ + r + (r * s) * ‖v - w‖ := by
    calc
      s = ‖s • (c + r • v)‖ := by
        rw [norm_smul, Real.norm_of_nonneg hs, hvr, mul_one]
      _ = ‖(s - r) • c + r • (c + s • w) + (r * s) • (v - w)‖ :=
        congrArg norm he
      _ ≤ ‖(s - r) • c + r • (c + s • w)‖ + ‖(r * s) • (v - w)‖ :=
        norm_add_le _ _
      _ ≤ (‖(s - r) • c‖ + ‖r • (c + s • w)‖) + ‖(r * s) • (v - w)‖ :=
        add_le_add_left (norm_add_le _ _) _
      _ = (s - r) * ‖c‖ + r + (r * s) * ‖v - w‖ := by
        simp only [norm_smul, Real.norm_of_nonneg hsr, Real.norm_of_nonneg hr,
          Real.norm_of_nonneg hprod, hws, mul_one]
  nlinarith [hbound]

/-- A symmetric contact comparison, still independent of unit-norm assumptions
on the two direction vectors. -/
theorem contact_comparison (c v w : X) {r s : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hvr : ‖c + r • v‖ = 1) (hws : ‖c + s • w‖ = 1) :
    (1 - ‖c‖) * |r - s| ≤ (r * s) * ‖v - w‖ := by
  rcases le_total r s with hrs | hsr
  · calc
      (1 - ‖c‖) * |r - s| = (1 - ‖c‖) * (s - r) := by
        rw [abs_of_nonpos (sub_nonpos.mpr hrs)]
        ring
      _ ≤ (r * s) * ‖v - w‖ := contact_comparison_ordered c v w hr hrs hvr hws
  · rw [abs_of_nonneg (sub_nonneg.mpr hsr)]
    simpa only [mul_comm s r, norm_sub_rev w v] using
      contact_comparison_ordered c w v hs hsr hws hvr

/-- Nonnegative contacts in the same direction are unique when the center is
strictly inside the unit ball. -/
theorem contact_unique (c : X) (hc : ‖c‖ < 1) (v : X) {r s : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hvr : ‖c + r • v‖ = 1) (hvs : ‖c + s • v‖ = 1) : r = s := by
  have h := contact_comparison c v v hr hs hvr hvs
  rw [sub_self, norm_zero, mul_zero] at h
  have hL : 0 < 1 - ‖c‖ := sub_pos.mpr hc
  have hz : |r - s| ≤ 0 := by
    apply le_of_not_gt
    intro hpos
    exact (not_lt_of_ge h) (mul_pos hL hpos)
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hz (abs_nonneg _)))

/-- Every nonnegative contact in a unit direction has the exact radial
bounds, independently of how the contact was obtained. -/
theorem contact_bounds (c : X) (v : UnitSphere X) {r : ℝ}
    (hr : 0 ≤ r) (hcontact : ‖c + r • (v : X)‖ = 1) :
    1 - ‖c‖ ≤ r ∧ r ≤ 1 + ‖c‖ := by
  have hn : ‖r • (v : X)‖ = r := by
    rw [norm_smul, Real.norm_of_nonneg hr, v.property, mul_one]
  have hlo := norm_add_le c (r • (v : X))
  rw [hcontact, hn] at hlo
  have hhi := norm_sub_le (c + r • (v : X)) c
  have he : (c + r • (v : X)) - c = r • (v : X) := by abel
  rw [he, hn, hcontact] at hhi
  constructor <;> linarith

/-- The genuine positive contact on each ray from an interior center. Existence
uses only a compact real interval, never compactness of the ambient sphere. -/
theorem existsUnique_radialContact (c : X) (hc : ‖c‖ < 1)
    (v : UnitSphere X) : ∃! r : ℝ, 0 < r ∧ ‖c + r • (v : X)‖ = 1 := by
  have hL : 0 < 1 - ‖c‖ := sub_pos.mpr hc
  have hU : 0 ≤ 1 + ‖c‖ := by linarith [norm_nonneg c]
  have hLU : 1 - ‖c‖ ≤ 1 + ‖c‖ := by linarith [norm_nonneg c]
  have hleft : ‖c + (1 - ‖c‖) • (v : X)‖ ≤ 1 := by
    calc
      ‖c + (1 - ‖c‖) • (v : X)‖ ≤ ‖c‖ + ‖(1 - ‖c‖) • (v : X)‖ :=
        norm_add_le _ _
      _ = 1 := by
        rw [norm_smul, Real.norm_of_nonneg hL.le, v.property, mul_one]
        ring
  have hright : 1 ≤ ‖c + (1 + ‖c‖) • (v : X)‖ := by
    have h := norm_sub_le (c + (1 + ‖c‖) • (v : X)) c
    have he : (c + (1 + ‖c‖) • (v : X)) - c = (1 + ‖c‖) • (v : X) := by abel
    rw [he, norm_smul, Real.norm_of_nonneg hU, v.property, mul_one] at h
    linarith
  have hcont : Continuous (fun t : ℝ => ‖c + t • (v : X)‖) :=
    (continuous_const.add (continuous_id.smul continuous_const)).norm
  obtain ⟨r, hr, hcontact⟩ :=
    intermediate_value_Icc hLU hcont.continuousOn ⟨hleft, hright⟩
  have hrpos : 0 < r := hL.trans_le hr.1
  refine ⟨r, ⟨hrpos, hcontact⟩, ?_⟩
  intro s hs
  exact contact_unique c hc (v : X) hs.1.le hrpos.le hs.2 hcontact

/-- The radius is chosen from the proved existence theorem. -/
def radialRadius (c : X) (hc : ‖c‖ < 1) (v : UnitSphere X) : ℝ :=
  Classical.choose (existsUnique_radialContact c hc v).exists

theorem radialRadius_spec (c : X) (hc : ‖c‖ < 1) (v : UnitSphere X) :
    0 < radialRadius c hc v ∧ ‖c + radialRadius c hc v • (v : X)‖ = 1 :=
  Classical.choose_spec (existsUnique_radialContact c hc v).exists

theorem radialRadius_pos (c : X) (hc : ‖c‖ < 1) (v : UnitSphere X) :
    0 < radialRadius c hc v := (radialRadius_spec c hc v).1

theorem norm_radialRadius (c : X) (hc : ‖c‖ < 1) (v : UnitSphere X) :
    ‖c + radialRadius c hc v • (v : X)‖ = 1 := (radialRadius_spec c hc v).2

theorem radialRadius_bounds (c : X) (hc : ‖c‖ < 1) (v : UnitSphere X) :
    1 - ‖c‖ ≤ radialRadius c hc v ∧ radialRadius c hc v ≤ 1 + ‖c‖ :=
  contact_bounds c v (radialRadius_pos c hc v).le (norm_radialRadius c hc v)

theorem radialRadius_unique (c : X) (hc : ‖c‖ < 1) (v : UnitSphere X)
    {r : ℝ} (hr : 0 ≤ r) (hcontact : ‖c + r • (v : X)‖ = 1) :
    r = radialRadius c hc v :=
  contact_unique c hc (v : X) hr (radialRadius_pos c hc v).le
    hcontact (norm_radialRadius c hc v)

/-- The quantitative comparison for the chosen contact radii. -/
theorem radialRadius_comparison (c : X) (hc : ‖c‖ < 1) (v w : UnitSphere X) :
    (1 - ‖c‖) * |radialRadius c hc v - radialRadius c hc w| ≤
      (radialRadius c hc v * radialRadius c hc w) * ‖(v : X) - (w : X)‖ :=
  contact_comparison c (v : X) (w : X)
    (radialRadius_pos c hc v).le (radialRadius_pos c hc w).le
    (norm_radialRadius c hc v) (norm_radialRadius c hc w)

theorem radialRadius_sub_le (c : X) (hc : ‖c‖ < 1) (v w : UnitSphere X) :
    |radialRadius c hc v - radialRadius c hc w| ≤
      ((1 + ‖c‖)^2 / (1 - ‖c‖)) * ‖(v : X) - (w : X)‖ := by
  have hU : 0 ≤ 1 + ‖c‖ := by linarith [norm_nonneg c]
  have hproduct : radialRadius c hc v * radialRadius c hc w ≤ (1 + ‖c‖)^2 := by
    calc
      radialRadius c hc v * radialRadius c hc w ≤ (1 + ‖c‖) * radialRadius c hc w :=
        mul_le_mul_of_nonneg_right (radialRadius_bounds c hc v).2
          (radialRadius_pos c hc w).le
      _ ≤ (1 + ‖c‖) * (1 + ‖c‖) :=
        mul_le_mul_of_nonneg_left (radialRadius_bounds c hc w).2 hU
      _ = (1 + ‖c‖)^2 := by ring
  have hscaled : |radialRadius c hc v - radialRadius c hc w| * (1 - ‖c‖) ≤
      (1 + ‖c‖)^2 * ‖(v : X) - (w : X)‖ := by
    calc
      |radialRadius c hc v - radialRadius c hc w| * (1 - ‖c‖) =
          (1 - ‖c‖) * |radialRadius c hc v - radialRadius c hc w| := mul_comm _ _
      _ ≤ (radialRadius c hc v * radialRadius c hc w) * ‖(v : X) - (w : X)‖ :=
        radialRadius_comparison c hc v w
      _ ≤ (1 + ‖c‖)^2 * ‖(v : X) - (w : X)‖ :=
        mul_le_mul_of_nonneg_right hproduct (norm_nonneg _)
  calc
    |radialRadius c hc v - radialRadius c hc w| ≤
        ((1 + ‖c‖)^2 * ‖(v : X) - (w : X)‖) / (1 - ‖c‖) :=
      (le_div_iff₀ (sub_pos.mpr hc)).mpr hscaled
    _ = ((1 + ‖c‖)^2 / (1 - ‖c‖)) * ‖(v : X) - (w : X)‖ := by ring

/-- The radius is globally Lipschitz on the unit sphere for each fixed interior
center, even in an infinite-dimensional normed space. -/
theorem lipschitz_radialRadius (c : X) (hc : ‖c‖ < 1) :
    LipschitzWith (Real.toNNReal ((1 + ‖c‖)^2 / (1 - ‖c‖))) (radialRadius c hc) := by
  apply LipschitzWith.of_dist_le'
  intro v w
  simpa only [Real.dist_eq, Subtype.dist_eq, dist_eq_norm, Real.norm_eq_abs] using radialRadius_sub_le c hc v w

theorem continuous_radialRadius (c : X) (hc : ‖c‖ < 1) :
    Continuous (radialRadius c hc) := (lipschitz_radialRadius c hc).continuous

/-- The actual point of contact, retaining its unit-sphere subtype proof. -/
def radialContact (c : X) (hc : ‖c‖ < 1) (v : UnitSphere X) : UnitSphere X :=
  ⟨c + radialRadius c hc v • (v : X), norm_radialRadius c hc v⟩

@[simp] theorem radialContact_coe (c : X) (hc : ‖c‖ < 1) (v : UnitSphere X) :
    (radialContact c hc v : X) = c + radialRadius c hc v • (v : X) := rfl

theorem continuous_radialContact (c : X) (hc : ‖c‖ < 1) :
    Continuous (radialContact c hc) :=
  (continuous_const.add ((continuous_radialRadius c hc).smul continuous_subtype_val)).subtype_mk _

end Tingley

end

end OAI

-- Adapted from OAI.Analysis.SphereIsometry.ReturnMap

namespace OAI

/-!
# The actual radial return map

For fixed `f`, `y` and `0 < t < 1`, the two interior centers are `t • y`
and `t • f y`. The map follows the two radial contacts.
The opposite direction is literal vector negation, with no antipodality
assumption on `f`. The ambient extensions are continuous on the unit sphere;
no continuity away from that sphere is asserted.
-/

noncomputable section

namespace Tingley

universe u v

variable {X : Type u} {Y : Type v}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Literal negation of a unit vector. -/
def sphereNeg (v : UnitSphere X) : UnitSphere X :=
  ⟨-(v : X), by simpa only [norm_neg] using v.property⟩

omit [NormedSpace ℝ X] in
@[simp] theorem sphereNeg_coe (v : UnitSphere X) :
    (sphereNeg v : X) = -(v : X) := rfl

omit [NormedSpace ℝ X] in
theorem continuous_sphereNeg : Continuous (sphereNeg : UnitSphere X → UnitSphere X) :=
  continuous_subtype_val.neg.subtype_mk _

theorem norm_smul_unitSphere (y : UnitSphere X) (t : ℝ) (ht : 0 ≤ t) :
    ‖t • (y : X)‖ = t := by
  rw [norm_smul, Real.norm_of_nonneg ht, y.property, mul_one]

theorem returnCenter_lt_one (y : UnitSphere X) (t : ℝ) (ht : 0 < t ∧ t < 1) :
    ‖t • (y : X)‖ < 1 := by
  rw [norm_smul_unitSphere y t ht.1.le]
  exact ht.2

/-- Distances from any unit point to either interior center have uniform bounds. -/
theorem norm_unit_sub_center_bounds (x y : UnitSphere X) (t : ℝ) (ht : 0 ≤ t) :
    1 - t ≤ ‖(x : X) - t • (y : X)‖ ∧
      ‖(x : X) - t • (y : X)‖ ≤ 1 + t := by
  constructor
  · simpa only [x.property, norm_smul_unitSphere y t ht] using
      norm_sub_norm_le (x : X) (t • (y : X))
  · simpa only [x.property, norm_smul_unitSphere y t ht] using
      norm_sub_le (x : X) (t • (y : X))

theorem unit_sub_center_ne_zero (x y : UnitSphere X) (t : ℝ)
    (ht : 0 < t ∧ t < 1) : (x : X) - t • (y : X) ≠ 0 := by
  intro h
  have hbound := (norm_unit_sub_center_bounds x y t ht.1.le).1
  rw [h, norm_zero] at hbound
  linarith [ht.2]

theorem center_sub_unit_ne_zero (x y : UnitSphere X) (t : ℝ)
    (ht : 0 < t ∧ t < 1) : t • (y : X) - (x : X) ≠ 0 :=
  sub_ne_zero.mpr (Ne.symm (sub_ne_zero.mp (unit_sub_center_ne_zero x y t ht)))

/-- The first radial radius. The isometry is an explicit common parameter even
though this first contact only uses the domain center. -/
def pRadius (_f : UnitSphere X ≃ᵢ UnitSphere Y) (y : UnitSphere X)
    (t : ℝ) (ht : 0 < t ∧ t < 1) (v : UnitSphere X) : ℝ :=
  radialRadius (t • (y : X)) (returnCenter_lt_one y t ht) v

variable (f : UnitSphere X ≃ᵢ UnitSphere Y) (y : UnitSphere X)
variable (t : ℝ) (ht : 0 < t ∧ t < 1)

/-- The first contact point `t y + p v`. -/
def xPoint (v : UnitSphere X) : UnitSphere X :=
  ⟨t • (y : X) + pRadius f y t ht v • (v : X),
    norm_radialRadius (t • (y : X)) (returnCenter_lt_one y t ht) v⟩

def sRadius (v : UnitSphere X) : ℝ :=
  ‖(f (xPoint f y t ht v) : Y) - t • (f y : Y)‖

/-- The image-side outward unit direction. -/
def wDirection (v : UnitSphere X) : UnitSphere Y :=
  normalize ((f (xPoint f y t ht v) : Y) - t • (f y : Y))
    (unit_sub_center_ne_zero (f (xPoint f y t ht v)) (f y) t ht)

/-- The second radial contact uses the negative of the actual direction `w`. -/
def uRadius (v : UnitSphere X) : ℝ :=
  radialRadius (t • (f y : Y)) (returnCenter_lt_one (f y) t ht)
    (sphereNeg (wDirection f y t ht v))

def zPoint (v : UnitSphere X) : UnitSphere X :=
  f.symm (radialContact (t • (f y : Y)) (returnCenter_lt_one (f y) t ht)
    (sphereNeg (wDirection f y t ht v)))

def rRadius (v : UnitSphere X) : ℝ :=
  ‖(zPoint f y t ht v : X) - t • (y : X)‖

/-- The genuine return map on the unit sphere. -/
def returnSphere (v : UnitSphere X) : UnitSphere X :=
  normalize (t • (y : X) - (zPoint f y t ht v : X))
    (center_sub_unit_ne_zero (zPoint f y t ht v) y t ht)

omit [NormedSpace ℝ Y] in
theorem pRadius_pos (v : UnitSphere X) : 0 < pRadius f y t ht v :=
  radialRadius_pos (t • (y : X)) (returnCenter_lt_one y t ht) v

omit [NormedSpace ℝ Y] in
theorem pRadius_bounds (v : UnitSphere X) :
    1 - t ≤ pRadius f y t ht v ∧ pRadius f y t ht v ≤ 1 + t := by
  simpa only [pRadius, norm_smul_unitSphere y t ht.1.le] using
    radialRadius_bounds (t • (y : X)) (returnCenter_lt_one y t ht) v

theorem sRadius_bounds (v : UnitSphere X) :
    1 - t ≤ sRadius f y t ht v ∧ sRadius f y t ht v ≤ 1 + t :=
  norm_unit_sub_center_bounds (f (xPoint f y t ht v)) (f y) t ht.1.le

theorem sRadius_pos (v : UnitSphere X) : 0 < sRadius f y t ht v :=
  (sub_pos.mpr ht.2).trans_le (sRadius_bounds f y t ht v).1

theorem uRadius_pos (v : UnitSphere X) : 0 < uRadius f y t ht v :=
  radialRadius_pos (t • (f y : Y)) (returnCenter_lt_one (f y) t ht)
    (sphereNeg (wDirection f y t ht v))

theorem uRadius_bounds (v : UnitSphere X) :
    1 - t ≤ uRadius f y t ht v ∧ uRadius f y t ht v ≤ 1 + t := by
  simpa only [uRadius, norm_smul_unitSphere (f y) t ht.1.le] using
    radialRadius_bounds (t • (f y : Y)) (returnCenter_lt_one (f y) t ht)
      (sphereNeg (wDirection f y t ht v))

theorem rRadius_bounds (v : UnitSphere X) :
    1 - t ≤ rRadius f y t ht v ∧ rRadius f y t ht v ≤ 1 + t :=
  norm_unit_sub_center_bounds (zPoint f y t ht v) y t ht.1.le

theorem rRadius_pos (v : UnitSphere X) : 0 < rRadius f y t ht v :=
  (sub_pos.mpr ht.2).trans_le (rRadius_bounds f y t ht v).1

theorem radii_bounds (v : UnitSphere X) :
    pRadius f y t ht v ∈ Set.Icc (1 - t) (1 + t) ∧
      sRadius f y t ht v ∈ Set.Icc (1 - t) (1 + t) ∧
      uRadius f y t ht v ∈ Set.Icc (1 - t) (1 + t) ∧
      rRadius f y t ht v ∈ Set.Icc (1 - t) (1 + t) :=
  ⟨pRadius_bounds f y t ht v, sRadius_bounds f y t ht v,
    uRadius_bounds f y t ht v, rRadius_bounds f y t ht v⟩

omit [NormedSpace ℝ Y] in
theorem xPoint_eq (v : UnitSphere X) :
    (xPoint f y t ht v : X) = t • (y : X) + pRadius f y t ht v • (v : X) := rfl

theorem fxPoint_eq (v : UnitSphere X) :
    (f (xPoint f y t ht v) : Y) =
      t • (f y : Y) + sRadius f y t ht v • (wDirection f y t ht v : Y) := by
  have h : sRadius f y t ht v • (wDirection f y t ht v : Y) =
      (f (xPoint f y t ht v) : Y) - t • (f y : Y) :=
    norm_smul_normalize _ _
  rw [h]
  abel

theorem fzPoint_eq (v : UnitSphere X) :
    (f (zPoint f y t ht v) : Y) =
      t • (f y : Y) - uRadius f y t ht v • (wDirection f y t ht v : Y) := by
  simp only [zPoint, IsometryEquiv.apply_symm_apply, radialContact_coe,
    sphereNeg_coe, smul_neg, sub_eq_add_neg, uRadius]

theorem zPoint_eq (v : UnitSphere X) :
    (zPoint f y t ht v : X) =
      t • (y : X) - rRadius f y t ht v • (returnSphere f y t ht v : X) := by
  have h : ‖t • (y : X) - (zPoint f y t ht v : X)‖ •
      (returnSphere f y t ht v : X) = t • (y : X) - (zPoint f y t ht v : X) :=
    norm_smul_normalize _ _
  rw [norm_sub_rev] at h
  change rRadius f y t ht v • (returnSphere f y t ht v : X) = _ at h
  rw [h]
  abel

omit [NormedSpace ℝ Y] in
theorem norm_xPoint_sub_center (v : UnitSphere X) :
    ‖(xPoint f y t ht v : X) - t • (y : X)‖ = pRadius f y t ht v := by
  rw [xPoint_eq, add_sub_cancel_left, norm_smul,
    Real.norm_of_nonneg (pRadius_pos f y t ht v).le, v.property, mul_one]

theorem norm_zPoint_sub_center (v : UnitSphere X) :
    ‖(zPoint f y t ht v : X) - t • (y : X)‖ = rRadius f y t ht v := rfl

omit [NormedSpace ℝ Y] in
/-- Radial uniqueness recovers any given unit endpoint from its direction. -/
theorem pRadius_normalize_sub (x : UnitSphere X) :
    pRadius f y t ht (normalize ((x : X) - t • (y : X))
      (unit_sub_center_ne_zero x y t ht)) = ‖(x : X) - t • (y : X)‖ := by
  symm
  apply radialRadius_unique (t • (y : X)) (returnCenter_lt_one y t ht) _ (norm_nonneg _)
  rw [norm_smul_normalize]
  have he : t • (y : X) + ((x : X) - t • (y : X)) = (x : X) := by abel
  rw [he]
  exact x.property

omit [NormedSpace ℝ Y] in
theorem xPoint_normalize_sub (x : UnitSphere X) :
    xPoint f y t ht (normalize ((x : X) - t • (y : X))
      (unit_sub_center_ne_zero x y t ht)) = x := by
  apply Subtype.ext
  rw [xPoint_eq, pRadius_normalize_sub, norm_smul_normalize]
  abel

omit [NormedSpace ℝ Y] in
theorem xPoint_surjective : Function.Surjective (xPoint f y t ht) := by
  intro x
  exact ⟨normalize ((x : X) - t • (y : X)) (unit_sub_center_ne_zero x y t ht),
    xPoint_normalize_sub f y t ht x⟩

/-- Normalizing a continuous everywhere-nonzero map preserves continuity. -/
theorem continuous_normalize_map {A : Type*} [TopologicalSpace A]
    (g : A → X) (hg : Continuous g) (hzero : ∀ a, g a ≠ 0) :
    Continuous (fun a => normalize (g a) (hzero a)) := by
  exact ((hg.norm.inv₀ (fun a => norm_ne_zero_iff.mpr (hzero a))).smul hg).subtype_mk _

omit [NormedSpace ℝ Y] in
theorem continuous_pRadius : Continuous (pRadius f y t ht) :=
  continuous_radialRadius (t • (y : X)) (returnCenter_lt_one y t ht)

omit [NormedSpace ℝ Y] in
theorem continuous_xPoint : Continuous (xPoint f y t ht) :=
  continuous_radialContact (t • (y : X)) (returnCenter_lt_one y t ht)

theorem continuous_sRadius : Continuous (sRadius f y t ht) :=
  ((continuous_subtype_val.comp (f.continuous.comp (continuous_xPoint f y t ht))).sub
    continuous_const).norm

theorem continuous_wDirection : Continuous (wDirection f y t ht) :=
  continuous_normalize_map _
    ((continuous_subtype_val.comp (f.continuous.comp (continuous_xPoint f y t ht))).sub
      continuous_const)
    (fun v => unit_sub_center_ne_zero (f (xPoint f y t ht v)) (f y) t ht)

theorem continuous_zPoint : Continuous (zPoint f y t ht) :=
  f.symm.continuous.comp
    ((continuous_radialContact (t • (f y : Y)) (returnCenter_lt_one (f y) t ht)).comp
      (continuous_sphereNeg.comp (continuous_wDirection f y t ht)))

theorem continuous_returnSphere : Continuous (returnSphere f y t ht) :=
  continuous_normalize_map _
    (continuous_const.sub (continuous_subtype_val.comp (continuous_zPoint f y t ht)))
    (fun v => center_sub_unit_ne_zero (zPoint f y t ht v) y t ht)

/-- Total ambient functions, used only on the sphere by the convex-set argument. -/
def pAmbient (v : X) : ℝ :=
  if hv : ‖v‖ = 1 then pRadius f y t ht ⟨v, hv⟩ else 0

def sAmbient (v : X) : ℝ :=
  if hv : ‖v‖ = 1 then sRadius f y t ht ⟨v, hv⟩ else 0

def uAmbient (v : X) : ℝ :=
  if hv : ‖v‖ = 1 then uRadius f y t ht ⟨v, hv⟩ else 0

def rAmbient (v : X) : ℝ :=
  if hv : ‖v‖ = 1 then rRadius f y t ht ⟨v, hv⟩ else 0

def returnAmbient (v : X) : X :=
  if hv : ‖v‖ = 1 then (returnSphere f y t ht ⟨v, hv⟩ : X) else 0

omit [NormedSpace ℝ Y] in
@[simp] theorem pAmbient_coe (v : UnitSphere X) :
    pAmbient f y t ht (v : X) = pRadius f y t ht v := by
  simp only [pAmbient, v.property, dif_pos]

@[simp] theorem sAmbient_coe (v : UnitSphere X) :
    sAmbient f y t ht (v : X) = sRadius f y t ht v := by
  simp only [sAmbient, v.property, dif_pos]

@[simp] theorem uAmbient_coe (v : UnitSphere X) :
    uAmbient f y t ht (v : X) = uRadius f y t ht v := by
  simp only [uAmbient, v.property, dif_pos]

@[simp] theorem rAmbient_coe (v : UnitSphere X) :
    rAmbient f y t ht (v : X) = rRadius f y t ht v := by
  simp only [rAmbient, v.property, dif_pos]

@[simp] theorem returnAmbient_coe (v : UnitSphere X) :
    returnAmbient f y t ht (v : X) = (returnSphere f y t ht v : X) := by
  simp only [returnAmbient, v.property, dif_pos]

theorem continuousOn_returnAmbient :
    ContinuousOn (returnAmbient f y t ht) {v : X | ‖v‖ = 1} := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  have he : ({v : X | ‖v‖ = 1}).domRestrict (returnAmbient f y t ht) =
      fun v : UnitSphere X => (returnSphere f y t ht v : X) := by
    funext v
    exact returnAmbient_coe f y t ht v
  rw [he]
  exact continuous_subtype_val.comp (continuous_returnSphere f y t ht)

end Tingley

end

end OAI

-- Adapted from OAI.Analysis.SphereIsometry.Supports

namespace OAI

/-!
# Supporting functionals

Supports are continuous real linear functionals of norm at most one which attain
the norm at the specified vector. Hahn–Banach supplies supports and extends them
from any subspace. Restriction and extension relate assertions about every ambient
support to assertions about every support on a finite span.

The results here hold in arbitrary real normed spaces, including the zero space.
-/

namespace Tingley

universe u

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- A norm-bounded real functional attaining the norm at a vector. -/
def SupportAt (φ : X →L[ℝ] ℝ) (a : X) : Prop :=
  ‖φ‖ ≤ 1 ∧ φ a = ‖a‖

/-- The norm-at-most-one formulation also supplies a support at zero. -/
theorem exists_support (a : X) : ∃ φ : X →L[ℝ] ℝ, SupportAt φ a :=
  exists_dual_vector'' ℝ a

theorem abs_apply_le_norm {φ : X →L[ℝ] ℝ} (hφ : ‖φ‖ ≤ 1) (x : X) :
    |φ x| ≤ ‖x‖ := by
  simpa only [Real.norm_eq_abs, one_mul] using φ.le_of_opNorm_le hφ x

theorem apply_le_norm {φ : X →L[ℝ] ℝ} (hφ : ‖φ‖ ≤ 1) (x : X) :
    φ x ≤ ‖x‖ :=
  (le_abs_self (φ x)).trans (abs_apply_le_norm hφ x)

@[simp] theorem supportAt_zero_iff (φ : X →L[ℝ] ℝ) :
    SupportAt φ (0 : X) ↔ ‖φ‖ ≤ 1 := by
  simp [SupportAt]

theorem SupportAt.smul_nonneg {φ : X →L[ℝ] ℝ} {a : X}
    (h : SupportAt φ a) {c : ℝ} (hc : 0 ≤ c) : SupportAt φ (c • a) := by
  refine ⟨h.1, ?_⟩
  simp only [map_smul, smul_eq_mul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc, h.2]

theorem supportAt_pos_smul_iff (φ : X →L[ℝ] ℝ) (a : X)
    {c : ℝ} (hc : 0 < c) : SupportAt φ (c • a) ↔ SupportAt φ a := by
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    have heq := h.2
    rw [map_smul, smul_eq_mul, norm_smul, Real.norm_eq_abs, abs_of_pos hc] at heq
    exact mul_left_cancel₀ (ne_of_gt hc) heq
  · intro h
    exact h.smul_nonneg hc.le

@[simp] theorem supportAt_neg_iff (φ : X →L[ℝ] ℝ) (a : X) :
    SupportAt (-φ) (-a) ↔ SupportAt φ a := by
  simp [SupportAt]

theorem SupportAt.neg {φ : X →L[ℝ] ℝ} {a : X} (h : SupportAt φ a) :
    SupportAt (-φ) (-a) :=
  (supportAt_neg_iff φ a).2 h

theorem SupportAt.subgradient {φ : X →L[ℝ] ℝ} {a : X}
    (h : SupportAt φ a) (z : X) : φ (z - a) ≤ ‖z‖ - ‖a‖ := by
  rw [map_sub, h.2]
  exact sub_le_sub_right (apply_le_norm h.1 z) ‖a‖

/-- Hahn–Banach extends from any real subspace without changing the norm. -/
theorem extension_norm_eq (U : Submodule ℝ X) (φ : U →L[ℝ] ℝ) :
    ∃ Φ : X →L[ℝ] ℝ, (∀ u : U, Φ (u : X) = φ u) ∧ ‖Φ‖ = ‖φ‖ :=
  _root_.exists_extension_norm_eq U φ

theorem supportAt_extension (U : Submodule ℝ X) (a : U)
    (φ : U →L[ℝ] ℝ) (h : SupportAt φ a) :
    ∃ Φ : X →L[ℝ] ℝ,
      (∀ u : U, Φ (u : X) = φ u) ∧ SupportAt Φ (a : X) := by
  obtain ⟨Φ, hΦ, hnorm⟩ := extension_norm_eq U φ
  exact ⟨Φ, hΦ, ⟨hnorm.trans_le h.1, (hΦ a).trans h.2⟩⟩

theorem norm_restrict_le (U : Submodule ℝ X) (φ : X →L[ℝ] ℝ) :
    ‖φ.comp U.subtypeL‖ ≤ ‖φ‖ :=
  (φ.comp U.subtypeL).opNorm_le_bound (norm_nonneg φ) fun u => φ.le_opNorm (u : X)

theorem SupportAt.restrict (U : Submodule ℝ X)
    {φ : X →L[ℝ] ℝ} (a : U) (h : SupportAt φ (a : X)) :
    SupportAt (φ.comp U.subtypeL) a :=
  ⟨(norm_restrict_le U φ).trans h.1, h.2⟩

/-- Universal assertions about support evaluations can be made on any subspace
containing the two vectors. This permits using the dual of their finite span. -/
theorem forall_supportAt_apply_iff_submodule (U : Submodule ℝ X)
    (a b : U) (P : ℝ → Prop) :
    (∀ φ : X →L[ℝ] ℝ, SupportAt φ (a : X) → P (φ (b : X))) ↔
    (∀ ψ : U →L[ℝ] ℝ, SupportAt ψ a → P (ψ b)) := by
  constructor
  · intro h ψ hψ
    obtain ⟨Φ, hΦ, hsupport⟩ := supportAt_extension U a ψ hψ
    simpa only [hΦ b] using h Φ hsupport
  · intro h Φ hΦ
    exact h (Φ.comp U.subtypeL) (SupportAt.restrict U a hΦ)

/-- Triangle equality is equivalent to the existence of a common support. -/
theorem norm_add_eq_iff_exists_common_supportAt (x y : X) :
    ‖x + y‖ = ‖x‖ + ‖y‖ ↔
      ∃ φ : X →L[ℝ] ℝ, SupportAt φ x ∧ SupportAt φ y := by
  constructor
  · intro heq
    obtain ⟨φ, hφ⟩ := exists_support (x + y)
    have hx := apply_le_norm hφ.1 x
    have hy := apply_le_norm hφ.1 y
    have hsum : φ x + φ y = ‖x‖ + ‖y‖ := by
      calc
        φ x + φ y = φ (x + y) := (map_add φ x y).symm
        _ = ‖x + y‖ := hφ.2
        _ = ‖x‖ + ‖y‖ := heq
    refine ⟨φ, ⟨hφ.1, ?_⟩, ⟨hφ.1, ?_⟩⟩
    · linarith
    · linarith
  · rintro ⟨φ, hx, hy⟩
    apply le_antisymm (norm_add_le x y)
    have h := apply_le_norm hx.1 (x + y)
    rwa [map_add, hx.2, hy.2] at h

/-- Positive weighted triangle equality for unit vectors gives one functional
taking value one at both vectors. No strict convexity is required. -/
theorem common_support_of_norm_add_eq {v w : X}
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) {α β : ℝ}
    (hα : 0 < α) (hβ : 0 < β)
    (heq : ‖α • v + β • w‖ = α + β) :
    ∃ φ : X →L[ℝ] ℝ, ‖φ‖ ≤ 1 ∧ φ v = 1 ∧ φ w = 1 := by
  have hsum : ‖α • v + β • w‖ = ‖α • v‖ + ‖β • w‖ := by
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos hα, abs_of_pos hβ,
      hv, hw, mul_one] using heq
  obtain ⟨φ, hvφ, hwφ⟩ :=
    (norm_add_eq_iff_exists_common_supportAt (α • v) (β • w)).mp hsum
  have hv' := (supportAt_pos_smul_iff φ v hα).mp hvφ
  have hw' := (supportAt_pos_smul_iff φ w hβ).mp hwφ
  exact ⟨φ, hv'.1, hv'.2.trans hv, hw'.2.trans hw⟩

end Tingley

end OAI

-- Adapted from OAI.Analysis.SphereIsometry.PositiveConvexFace

namespace OAI

/-!
# Positive combinations in a common support face

A norm-bounded functional that is one on a strictly positive barycenter is
one on every vertex. The resulting simultaneous support keeps the enlarged
convex hull in the unit sphere. For an infinite sequence, finite-prefix hull
containment passes to a closed ambient set without choosing a common support
for the entire sequence.
-/

noncomputable section

open scoped BigOperators
open Set

namespace Tingley

section Scalar

variable {ι : Type*} [Fintype ι]

theorem eq_one_of_positive_weighted_sum (weights b : ι → ℝ)
    (hpos : ∀ i, 0 < weights i) (hsum : ∑ i, weights i = 1)
    (hb : ∀ i, b i ≤ 1) (hsaturated : ∑ i, weights i * b i = 1) :
    ∀ i, b i = 1 := by
  classical
  have hnonneg : ∀ i ∈ (Finset.univ : Finset ι), 0 ≤ weights i * (1 - b i) :=
    fun i _ => mul_nonneg (hpos i).le (sub_nonneg.mpr (hb i))
  have hzero : ∑ i, weights i * (1 - b i) = 0 := by
    calc
      _ = (∑ i, weights i) - ∑ i, weights i * b i := by
        simp only [mul_sub, mul_one, Finset.sum_sub_distrib]
      _ = 0 := by rw [hsum, hsaturated, sub_self]
  intro i
  have hi := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hzero i
    (Finset.mem_univ i)
  exact (sub_eq_zero.mp ((mul_eq_zero.mp hi).resolve_left (ne_of_gt (hpos i)))).symm

end Scalar

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

section FiniteCombination

variable {ι : Type*} [Fintype ι]

theorem support_eq_one_of_positive_sum (φ : X →L[ℝ] ℝ) (hφ : ‖φ‖ ≤ 1)
    (weights : ι → ℝ) (v : ι → X)
    (hpos : ∀ i, 0 < weights i) (hsum : ∑ i, weights i = 1)
    (hv : ∀ i, ‖v i‖ ≤ 1) (ha : φ (∑ i, weights i • v i) = 1) :
    ∀ i, φ (v i) = 1 := by
  apply eq_one_of_positive_weighted_sum weights (fun i => φ (v i)) hpos hsum
  · exact fun i => (apply_le_norm hφ (v i)).trans (hv i)
  · simpa only [map_sum, map_smul, smul_eq_mul] using ha

end FiniteCombination

/-- The closed unit ball cut by the level-one hyperplane of one functional. -/
def supportFace (φ : X →L[ℝ] ℝ) : Set X :=
  {x | ‖x‖ ≤ 1 ∧ φ x = 1}

theorem convex_supportFace (φ : X →L[ℝ] ℝ) : Convex ℝ (supportFace φ) := by
  rintro x ⟨hx, hφx⟩ y ⟨hy, hφy⟩ a b ha hb hab
  constructor
  · calc
      ‖a • x + b • y‖ ≤ ‖a • x‖ + ‖b • y‖ := norm_add_le _ _
      _ = a * ‖x‖ + b * ‖y‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
      _ ≤ a * 1 + b * 1 :=
        add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)
      _ = 1 := by simpa only [mul_one] using hab
  · simpa only [map_add, map_smul, smul_eq_mul, hφx, hφy, mul_one] using hab

theorem supportFace_subset_sphere (φ : X →L[ℝ] ℝ) (hφ : ‖φ‖ ≤ 1) :
    supportFace φ ⊆ {x : X | ‖x‖ = 1} := by
  intro x hx
  exact le_antisymm hx.1 (hx.2 ▸ apply_le_norm hφ x)

theorem convexHull_subset_supportFace (φ : X →L[ℝ] ℝ)
    {S : Set X} (hS : S ⊆ supportFace φ) :
    convexHull ℝ S ⊆ supportFace φ :=
  convexHull_min hS (convex_supportFace φ)

section Enlargement

variable {ι : Type*} [Fintype ι]

theorem enlarged_convexHull_in_supportFace (φ : X →L[ℝ] ℝ) (hφ : ‖φ‖ ≤ 1)
    (weights : ι → ℝ) (v : ι → X) (w : X)
    (hpos : ∀ i, 0 < weights i) (hsum : ∑ i, weights i = 1)
    (hv : ∀ i, ‖v i‖ = 1) (hw : ‖w‖ = 1)
    (ha : φ (∑ i, weights i • v i) = 1) (hwφ : φ w = 1) :
    convexHull ℝ (insert w (Set.range v)) ⊆ {x : X | ‖x‖ = 1 ∧ φ x = 1} := by
  have hall := support_eq_one_of_positive_sum φ hφ weights v hpos hsum
    (fun i => (hv i).le) ha
  have hvertices : insert w (Set.range v) ⊆ supportFace φ := by
    intro x hx
    rcases hx with rfl | ⟨i, rfl⟩
    · exact ⟨hw.le, hwφ⟩
    · exact ⟨(hv i).le, hall i⟩
  intro x hx
  have hxface := convexHull_subset_supportFace φ hvertices hx
  exact ⟨supportFace_subset_sphere φ hφ hxface, hxface.2⟩

/-- The actual geometric propagation rule can now be applied to every new hull point. -/
theorem convexHull_insert_subset_of_common_support (φ : X →L[ℝ] ℝ) (hφ : ‖φ‖ ≤ 1)
    (weights : ι → ℝ) (v : ι → X) (w : X) (E : Set X)
    (hpos : ∀ i, 0 < weights i) (hsum : ∑ i, weights i = 1)
    (hv : ∀ i, ‖v i‖ = 1) (hw : ‖w‖ = 1)
    (ha : φ (∑ i, weights i • v i) = 1) (hwφ : φ w = 1)
    (hprop : ∀ x, ‖x‖ = 1 → φ x = 1 → x ∈ E) :
    convexHull ℝ (insert w (Set.range v)) ⊆ E := by
  intro x hx
  have h := enlarged_convexHull_in_supportFace φ hφ weights v w hpos hsum hv hw ha hwφ hx
  exact hprop x h.1 h.2

end Enlargement

end Tingley

end

end OAI

-- Adapted from OAI.Analysis.SphereIsometry.ExtremalPropagation

namespace OAI

/-!
# The actual extremal return set and finite-hull propagation

The set is defined by equality in the original sphere-map defect. Its
closedness, return identities and simultaneous support propagation are proved
from that definition and the global absolute defect bound.
-/

noncomputable section

open Set
open scoped BigOperators

namespace Tingley

variable {X Y : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]

variable (f : UnitSphere X ≃ᵢ UnitSphere Y) (y : UnitSphere X)
variable (t : ℝ) (ht : 0 < t ∧ t < 1) (M : ℝ)

def extremalSphere : Set (UnitSphere X) :=
  {v | sRadius f y t ht v - pRadius f y t ht v = M}

def extremalSet : Set X :=
  Subtype.val '' extremalSphere f y t ht M

@[simp] theorem mem_extremalSet_coe (v : UnitSphere X) :
    (v : X) ∈ extremalSet f y t ht M ↔ v ∈ extremalSphere f y t ht M := by
  constructor
  · rintro ⟨w, hw, heq⟩
    have : w = v := Subtype.ext heq
    simpa only [this] using hw
  · intro hv
    exact ⟨v, hv, rfl⟩

theorem norm_eq_one_of_mem_extremalSet {v : X}
    (hv : v ∈ extremalSet f y t ht M) : ‖v‖ = 1 := by
  obtain ⟨w, _, rfl⟩ := hv
  exact w.property

theorem isClosed_extremalSphere : IsClosed (extremalSphere f y t ht M) :=
  isClosed_eq ((continuous_sRadius f y t ht).sub (continuous_pRadius f y t ht))
    continuous_const

theorem isClosed_extremalSet : IsClosed (extremalSet f y t ht M) := by
  have hs : IsClosed {v : X | ‖v‖ = 1} := isClosed_eq continuous_norm continuous_const
  exact hs.isClosedMap_subtype_val _ (isClosed_extremalSphere f y t ht M)

theorem sRadius_eq_add {v : UnitSphere X}
    (hv : v ∈ extremalSphere f y t ht M) :
    sRadius f y t ht v = pRadius f y t ht v + M := by
  change sRadius f y t ht v - pRadius f y t ht v = M at hv
  linarith

theorem signedDefect_xPoint (v : UnitSphere X) :
    signedDefect f t (xPoint f y t ht v) y =
      sRadius f y t ht v - pRadius f y t ht v := by
  unfold signedDefect
  rw [norm_xPoint_sub_center]
  rfl

theorem extremalSphere_nonempty_of_attained (x₀ : UnitSphere X)
    (hatt : signedDefect f t x₀ y = M) :
    (extremalSphere f y t ht M).Nonempty := by
  obtain ⟨v, hv⟩ := xPoint_surjective f y t ht x₀
  refine ⟨v, ?_⟩
  change sRadius f y t ht v - pRadius f y t ht v = M
  rw [← signedDefect_xPoint, hv]
  exact hatt

theorem extremalSet_nonempty_of_attained (x₀ : UnitSphere X)
    (hatt : signedDefect f t x₀ y = M) :
    (extremalSet f y t ht M).Nonempty := by
  obtain ⟨v, hv⟩ := extremalSphere_nonempty_of_attained f y t ht M x₀ hatt
  exact ⟨(v : X), (mem_extremalSet_coe f y t ht M v).mpr hv⟩

theorem norm_fzPoint_sub_center (v : UnitSphere X) :
    ‖(f (zPoint f y t ht v) : Y) - t • (f y : Y)‖ = uRadius f y t ht v := by
  rw [fzPoint_eq]
  have he : t • (f y : Y) - uRadius f y t ht v • (wDirection f y t ht v : Y) -
      t • (f y : Y) = -(uRadius f y t ht v • (wDirection f y t ht v : Y)) := by
    abel
  rw [he, norm_neg, norm_smul, Real.norm_of_nonneg (uRadius_pos f y t ht v).le,
    UnitSphere.norm_coe, mul_one]

theorem signedDefect_zPoint (v : UnitSphere X) :
    signedDefect f t (zPoint f y t ht v) y =
      uRadius f y t ht v - rRadius f y t ht v := by
  unfold signedDefect
  rw [norm_fzPoint_sub_center, norm_zPoint_sub_center]

theorem norm_xPoint_sub_zPoint (v : UnitSphere X) :
    ‖(xPoint f y t ht v : X) - (zPoint f y t ht v : X)‖ =
      ‖pRadius f y t ht v • (v : X) +
        rRadius f y t ht v • (returnSphere f y t ht v : X)‖ := by
  congr 1
  rw [xPoint_eq, zPoint_eq]
  abel

theorem norm_fxPoint_sub_fzPoint (v : UnitSphere X) :
    ‖(f (xPoint f y t ht v) : Y) - (f (zPoint f y t ht v) : Y)‖ =
      sRadius f y t ht v + uRadius f y t ht v := by
  rw [fxPoint_eq, fzPoint_eq]
  have he : (t • (f y : Y) + sRadius f y t ht v • (wDirection f y t ht v : Y)) -
      (t • (f y : Y) - uRadius f y t ht v • (wDirection f y t ht v : Y)) =
      (sRadius f y t ht v + uRadius f y t ht v) • (wDirection f y t ht v : Y) := by
    rw [add_smul]
    abel
  rw [he, norm_smul, Real.norm_of_nonneg
    (add_nonneg (sRadius_pos f y t ht v).le (uRadius_pos f y t ht v).le),
    UnitSphere.norm_coe, mul_one]

theorem extremal_radius_identities (hb : HasDefectBound f M) {v : UnitSphere X}
    (hv : v ∈ extremalSphere f y t ht M) :
    rRadius f y t ht v - uRadius f y t ht v = M ∧
    pRadius f y t ht v + rRadius f y t ht v =
      sRadius f y t ht v + uRadius f y t ht v ∧
    ‖pRadius f y t ht v • (v : X) +
      rRadius f y t ht v • (returnSphere f y t ht v : X)‖ =
      pRadius f y t ht v + rRadius f y t ht v := by
  have hback := (abs_le.mp (hb t ⟨ht.1.le, ht.2.le⟩ (zPoint f y t ht v) y)).1
  rw [signedDefect_zPoint] at hback
  have hs := sRadius_eq_add f y t ht M hv
  have hn : ‖pRadius f y t ht v • (v : X) +
      rRadius f y t ht v • (returnSphere f y t ht v : X)‖ =
      sRadius f y t ht v + uRadius f y t ht v := by
    rw [← norm_xPoint_sub_zPoint, ← sphere_norm_sub f, norm_fxPoint_sub_fzPoint]
  have htri := norm_add_le (pRadius f y t ht v • (v : X))
    (rRadius f y t ht v • (returnSphere f y t ht v : X))
  simp only [norm_smul, Real.norm_of_nonneg (pRadius_pos f y t ht v).le,
    Real.norm_of_nonneg (rRadius_pos f y t ht v).le, UnitSphere.norm_coe,
    mul_one] at htri
  have hr : rRadius f y t ht v - uRadius f y t ht v = M := by linarith
  have hsum : pRadius f y t ht v + rRadius f y t ht v =
      sRadius f y t ht v + uRadius f y t ht v := by linarith
  exact ⟨hr, hsum, hn.trans hsum.symm⟩

theorem rRadius_eq_add (hb : HasDefectBound f M) {v : UnitSphere X}
    (hv : v ∈ extremalSphere f y t ht M) :
    rRadius f y t ht v = uRadius f y t ht v + M := by
  have h := (extremal_radius_identities f y t ht M hb hv).1
  linarith

theorem extremal_common_support (hb : HasDefectBound f M) {v : UnitSphere X}
    (hv : v ∈ extremalSphere f y t ht M) :
    ∃ φ : X →L[ℝ] ℝ, ‖φ‖ ≤ 1 ∧ φ (v : X) = 1 ∧
      φ (returnSphere f y t ht v : X) = 1 :=
  common_support_of_norm_add_eq v.property (returnSphere f y t ht v).property
    (pRadius_pos f y t ht v) (rRadius_pos f y t ht v)
    (extremal_radius_identities f y t ht M hb hv).2.2

theorem mem_extremal_of_common_support_return (hb : HasDefectBound f M)
    {v : UnitSphere X} (hv : v ∈ extremalSphere f y t ht M)
    (l : UnitSphere X) (φ : X →L[ℝ] ℝ) (hφ : ‖φ‖ ≤ 1)
    (hl : φ (l : X) = 1) (hg : φ (returnSphere f y t ht v : X) = 1) :
    l ∈ extremalSphere f y t ht M := by
  have hlow : pRadius f y t ht l + rRadius f y t ht v ≤
      ‖(xPoint f y t ht l : X) - (zPoint f y t ht v : X)‖ := by
    have he : (xPoint f y t ht l : X) - (zPoint f y t ht v : X) =
        pRadius f y t ht l • (l : X) +
          rRadius f y t ht v • (returnSphere f y t ht v : X) := by
      rw [xPoint_eq, zPoint_eq]
      abel
    rw [he]
    have heval : φ (pRadius f y t ht l • (l : X) +
        rRadius f y t ht v • (returnSphere f y t ht v : X)) =
        pRadius f y t ht l + rRadius f y t ht v := by
      simp only [map_add, map_smul, smul_eq_mul, hl, hg, mul_one]
    rw [← heval]
    exact apply_le_norm hφ _
  have hupp : ‖(xPoint f y t ht l : X) - (zPoint f y t ht v : X)‖ ≤
      sRadius f y t ht l + uRadius f y t ht v := by
    rw [← sphere_norm_sub f, fxPoint_eq, fzPoint_eq]
    have he : (t • (f y : Y) + sRadius f y t ht l • (wDirection f y t ht l : Y)) -
        (t • (f y : Y) - uRadius f y t ht v • (wDirection f y t ht v : Y)) =
        sRadius f y t ht l • (wDirection f y t ht l : Y) +
          uRadius f y t ht v • (wDirection f y t ht v : Y) := by abel
    rw [he]
    simpa only [norm_smul, Real.norm_of_nonneg (sRadius_pos f y t ht l).le,
      Real.norm_of_nonneg (uRadius_pos f y t ht v).le, UnitSphere.norm_coe,
      mul_one] using norm_add_le
        (sRadius f y t ht l • (wDirection f y t ht l : Y))
        (uRadius f y t ht v • (wDirection f y t ht v : Y))
  have hdef := (abs_le.mp (hb t ⟨ht.1.le, ht.2.le⟩ (xPoint f y t ht l) y)).2
  rw [signedDefect_xPoint] at hdef
  have hr := (extremal_radius_identities f y t ht M hb hv).1
  change sRadius f y t ht l - pRadius f y t ht l = M
  linarith

theorem positive_prefix_extension (hb : HasDefectBound f M)
    (n : ℕ) (V : Fin (n + 1) → X) (weights : Fin (n + 1) → ℝ)
    (hV : convexHull ℝ (Set.range V) ⊆ extremalSet f y t ht M)
    (hpos : ∀ i, 0 < weights i) (hsum : ∑ i, weights i = 1) :
    convexHull ℝ (Set.range (Fin.snoc V
      (returnAmbient f y t ht (∑ i, weights i • V i)))) ⊆ extremalSet f y t ht M := by
  let a : X := ∑ i, weights i • V i
  have haE : a ∈ extremalSet f y t ht M := hV
    (mem_convexHull_of_exists_fintype weights V (fun i => (hpos i).le) hsum
      (fun i => ⟨i, rfl⟩) rfl)
  have ha : ‖a‖ = 1 := norm_eq_one_of_mem_extremalSet f y t ht M haE
  let av : UnitSphere X := ⟨a, ha⟩
  have hav : av ∈ extremalSphere f y t ht M :=
    (mem_extremalSet_coe f y t ht M av).mp haE
  obtain ⟨φ, hφ, hφa, hφg⟩ := extremal_common_support f y t ht M hb hav
  have hG : returnAmbient f y t ht a = (returnSphere f y t ht av : X) :=
    returnAmbient_coe f y t ht av
  have hfaces : convexHull ℝ
      (insert (returnAmbient f y t ht a) (Set.range V)) ⊆ extremalSet f y t ht M := by
    apply convexHull_insert_subset_of_common_support φ hφ weights V
      (returnAmbient f y t ht a) (extremalSet f y t ht M) hpos hsum
    · intro i
      exact norm_eq_one_of_mem_extremalSet f y t ht M
        (hV (subset_convexHull ℝ (Set.range V) ⟨i, rfl⟩))
    · rw [hG]
      exact (returnSphere f y t ht av).property
    · exact hφa
    · rw [hG]
      exact hφg
    · intro x hx hφx
      have hext := mem_extremal_of_common_support_return f y t ht M hb hav
        ⟨x, hx⟩ φ hφ hφx hφg
      exact (mem_extremalSet_coe f y t ht M ⟨x, hx⟩).mpr hext
  apply Set.Subset.trans (convexHull_mono ?_) hfaces
  rintro x ⟨i, rfl⟩
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.snoc_last]
    exact Set.mem_insert _ _
  · simp only [Fin.snoc_castSucc]
    exact Set.mem_insert_of_mem _ ⟨j, rfl⟩

end Tingley

end

end OAI

-- Adapted from OAI.Analysis.SphereIsometry.PositiveScheduling

namespace OAI

/-! A fixed positive coefficient schedule, dense for every bounded sequence. -/

noncomputable section

open scoped BigOperators
open Set Finset

namespace Tingley

/-- A rational probability vector on an initial, nonempty list of indices. -/
abbrev RationalPrefix :=
  Σ m : ℕ, {q : Fin (m + 1) → ℚ // (∀ i, 0 ≤ q i) ∧ ∑ i, q i = 1}

/-- Extend a finite vector by zero, using the actual natural-number indices. -/
def prefixZeroExtend {A : Type*} [Zero A] {k : ℕ} (f : Fin k → A) (i : ℕ) : A :=
  if h : i < k then f ⟨i, h⟩ else 0

@[simp] theorem prefixZeroExtend_apply {A : Type*} [Zero A] {k : ℕ}
    (f : Fin k → A) (i : Fin k) : prefixZeroExtend f i.val = f i := by
  simp [prefixZeroExtend, i.isLt]

theorem sum_prefixZeroExtend {A : Type*} [AddCommMonoid A] {k n : ℕ}
    (f : Fin k → A) (hkn : k ≤ n) :
    (∑ i : Fin n, prefixZeroExtend f i.val) = ∑ i, f i := by
  rw [Fin.sum_univ_eq_sum_range, Finset.sum_fin_eq_sum_range]
  symm
  apply Finset.sum_subset (Finset.range_mono hkn)
  intro i _ hi
  simp only [Finset.mem_range] at hi
  simp [hi]

/-- A failed or premature code is replaced by the point mass at the first index. -/
def baseStageWeights (n : ℕ) : Fin (n + 1) → ℚ :=
  match Encodable.decode (α := RationalPrefix) (Nat.unpair n).1 with
  | none => fun i => if i = 0 then 1 else 0
  | some q => if q.1 ≤ n then fun i => prefixZeroExtend q.2.val i.val
      else fun i => if i = 0 then 1 else 0

theorem baseStageWeights_nonneg (n : ℕ) (i : Fin (n + 1)) :
    0 ≤ baseStageWeights n i := by
  cases hdecode : Encodable.decode (α := RationalPrefix) (Nat.unpair n).1 with
  | none =>
    simp only [baseStageWeights, hdecode]
    split_ifs <;> norm_num
  | some q =>
    by_cases h : q.1 ≤ n
    · simp only [baseStageWeights, hdecode, if_pos h]
      unfold prefixZeroExtend
      split_ifs
      · exact q.2.property.1 _
      · exact le_rfl
    · simp only [baseStageWeights, hdecode, if_neg h]
      split_ifs <;> norm_num

theorem baseStageWeights_sum (n : ℕ) : ∑ i, baseStageWeights n i = 1 := by
  cases hdecode : Encodable.decode (α := RationalPrefix) (Nat.unpair n).1 with
  | none => simp [baseStageWeights, hdecode]
  | some q =>
    by_cases h : q.1 ≤ n
    · simp only [baseStageWeights, hdecode, if_pos h]
      rw [sum_prefixZeroExtend q.2.val (Nat.add_le_add_right h 1)]
      exact q.2.property.2
    · simp [baseStageWeights, hdecode, h]

theorem baseStageWeights_pair (q : RationalPrefix) (r : ℕ) (hr : q.1 ≤ r) :
    baseStageWeights (Nat.pair (Encodable.encode q) r) =
      fun i => prefixZeroExtend q.2.val i.val := by
  have hq : q.1 ≤ Nat.pair (Encodable.encode q) r := hr.trans (Nat.right_le_pair _ _)
  simp [baseStageWeights, hq]

def stageMixing (n : ℕ) : ℝ := 1 / ((n : ℝ) + 2)

theorem stageMixing_pos (n : ℕ) : 0 < stageMixing n := by
  unfold stageMixing
  positivity

theorem stageMixing_lt_one (n : ℕ) : stageMixing n < 1 := by
  unfold stageMixing
  rw [div_lt_one (by positivity : (0 : ℝ) < (n : ℝ) + 2)]
  linarith [show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n]

/-- Mix with the uniform vector on *all* available indices. -/
def positiveStageWeights (n : ℕ) (i : Fin (n + 1)) : ℝ :=
  (1 - stageMixing n) * (baseStageWeights n i : ℝ) +
    stageMixing n / ((n : ℝ) + 1)

theorem positiveStageWeights_pos (n : ℕ) (i : Fin (n + 1)) :
    0 < positiveStageWeights n i := by
  have hb : (0 : ℝ) ≤ (baseStageWeights n i : ℝ) := by
    exact_mod_cast baseStageWeights_nonneg n i
  exact add_pos_of_nonneg_of_pos
    (mul_nonneg (sub_nonneg.mpr (stageMixing_lt_one n).le) hb)
    (div_pos (stageMixing_pos n) (by positivity))

theorem positiveStageWeights_sum (n : ℕ) : ∑ i, positiveStageWeights n i = 1 := by
  have hb : (∑ i, (baseStageWeights n i : ℝ)) = 1 := by
    exact_mod_cast baseStageWeights_sum n
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  simp only [positiveStageWeights, Finset.sum_add_distrib, ← Finset.mul_sum,
    hb, mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add,
    Nat.cast_one]
  field_simp [hn]
  ring

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

def stageMean (v : ℕ → X) (n : ℕ) : X :=
  ∑ i : Fin (n + 1), positiveStageWeights n i • v i.val

def rationalPrefixMean (v : ℕ → X) (q : RationalPrefix) : X :=
  ∑ i : Fin (q.1 + 1), (q.2.val i : ℝ) • v i.val

theorem norm_probability_sum_le {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (z : ι → X) (hw : ∀ i, 0 ≤ w i)
    (hsum : ∑ i, w i = 1) (B : ℝ) (hz : ∀ i, ‖z i‖ ≤ B) :
    ‖∑ i, w i • z i‖ ≤ B := by
  calc
    ‖∑ i, w i • z i‖ ≤ ∑ i, ‖w i • z i‖ := norm_sum_le _ _
    _ = ∑ i, w i * ‖z i‖ := by simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg, hw]
    _ ≤ ∑ i, w i * B := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hz i) (hw i)
    _ = B := by rw [← Finset.sum_mul, hsum, one_mul]

private theorem sum_padded_mean (v : ℕ → X) (q : RationalPrefix) {n : ℕ}
    (hq : q.1 ≤ n) :
    (∑ i : Fin (n+1), (prefixZeroExtend (A := ℚ) q.2.val i.val : ℝ) • v i.val) =
      rationalPrefixMean v q := by
  have he (i : ℕ) : (prefixZeroExtend (A := ℚ) q.2.val i : ℝ) • v i =
      prefixZeroExtend (fun j : Fin (q.1+1) => (q.2.val j : ℝ) • v j.val) i := by
    unfold prefixZeroExtend
    split <;> simp
  simp_rw [he]
  exact sum_prefixZeroExtend _ (Nat.add_le_add_right hq 1)

private theorem norm_stageMean_sub_rational_le (v : ℕ → X)
    (B : ℝ) (hv : ∀ i, ‖v i‖ ≤ B) (q : RationalPrefix) (r : ℕ) (hr : q.1 ≤ r) :
    ‖stageMean v (Nat.pair (Encodable.encode q) r) - rationalPrefixMean v q‖ ≤
      2 * B / ((Nat.pair (Encodable.encode q) r : ℝ) + 2) := by
  let n := Nat.pair (Encodable.encode q) r
  let U : X := ∑ i : Fin (n+1), (1 / ((n : ℝ)+1)) • v i.val
  have hq : q.1 ≤ n := hr.trans (Nat.right_le_pair _ _)
  have hQ : ‖rationalPrefixMean v q‖ ≤ B := by
    refine norm_probability_sum_le (fun i => (q.2.val i : ℝ))
      (fun i => v i.val) ?_ ?_ B ?_
    · intro i
      exact_mod_cast q.2.property.1 i
    · exact_mod_cast q.2.property.2
    · intro i; exact hv i.val
  have hU : ‖U‖ ≤ B := by
    refine norm_probability_sum_le (fun _ : Fin (n+1) => 1 / ((n : ℝ)+1))
      (fun i => v i.val) ?_ ?_ B ?_
    · intro i; positivity
    · simp [Finset.sum_const, nsmul_eq_mul, Nat.cast_add, Nat.cast_one,
        ne_of_gt (show (0 : ℝ) < (n : ℝ)+1 by positivity)]
    · intro i; exact hv i.val
  have hbase := baseStageWeights_pair q r hr
  have he : stageMean v n =
      (1-stageMixing n) • rationalPrefixMean v q + stageMixing n • U := by
    unfold stageMean positiveStageWeights
    rw [hbase]
    simp_rw [add_smul, mul_smul, div_eq_mul_inv, mul_smul]
    rw [Finset.sum_add_distrib, ← Finset.smul_sum, ← Finset.smul_sum]
    rw [sum_padded_mean v q hq]
    simp [U, div_eq_mul_inv]
  have hd : stageMean v n - rationalPrefixMean v q =
      stageMixing n • (U-rationalPrefixMean v q) := by
    rw [he, sub_smul, one_smul, smul_sub]
    abel
  calc
    ‖stageMean v n-rationalPrefixMean v q‖ =
        stageMixing n * ‖U-rationalPrefixMean v q‖ := by
          rw [hd, norm_smul, Real.norm_eq_abs, abs_of_pos (stageMixing_pos n)]
    _ ≤ stageMixing n * (B+B) :=
      mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add hU hQ))
        (stageMixing_pos n).le
    _ = 2*B/((n:ℝ)+2) := by unfold stageMixing; ring

theorem exists_late_stageMean_close_rational
    (v : ℕ → X) (B : ℝ) (hB : 0 ≤ B) (hv : ∀ i, ‖v i‖ ≤ B)
    (q : RationalPrefix) (δ : ℝ) (hδ : 0 < δ) (N : ℕ) :
    ∃ n, N ≤ n ∧ ‖stageMean v n-rationalPrefixMean v q‖ < δ := by
  obtain ⟨K, hK⟩ := exists_nat_gt (2*B/δ)
  let r := max K (max N q.1)
  let n := Nat.pair (Encodable.encode q) r
  have hrK : K ≤ r := le_max_left _ _
  have hrN : N ≤ r := (le_max_left _ _).trans (le_max_right _ _)
  have hrq : q.1 ≤ r := (le_max_right _ _).trans (le_max_right _ _)
  have hrn : r ≤ n := Nat.right_le_pair _ _
  refine ⟨n, hrN.trans hrn, (norm_stageMean_sub_rational_le v B hv q r hrq).trans_lt ?_⟩
  have hKn : (K : ℝ) ≤ (n : ℝ) := by exact_mod_cast hrK.trans hrn
  apply (div_lt_iff₀ (show (0 : ℝ) < (n : ℝ)+2 by positivity)).2
  have hk' : 2*B < (K:ℝ)*δ := (div_lt_iff₀ hδ).1 hK
  nlinarith

/-- Rational simplex approximation by flooring the tail and assigning the residual to index zero. -/
theorem exists_rational_simplex_l1_close
    (m : ℕ) (α : Fin (m+1) → ℝ) (hα : ∀ i, 0 ≤ α i)
    (hsum : ∑ i, α i = 1) (δ : ℝ) (hδ : 0 < δ) :
    ∃ q : Fin (m+1) → ℚ, (∀ i, 0 ≤ q i) ∧ (∑ i, q i = 1) ∧
      (∑ i, |(q i : ℝ)-α i|) < δ := by
  obtain ⟨N, hN⟩ := exists_nat_gt (2*((m:ℝ)+1)/δ)
  have hNpos : (0 : ℝ) < (N:ℝ) :=
    lt_trans (by positivity : (0:ℝ) < 2*((m:ℝ)+1)/δ) hN
  have hN0 : (N:ℝ) ≠ 0 := ne_of_gt hNpos
  let b : Fin m → ℚ := fun i => (⌊(N:ℝ)*α i.succ⌋₊ : ℚ) / (N:ℚ)
  have hb0 (i : Fin m) : 0 ≤ b i := by dsimp [b]; positivity
  have hbcast (i : Fin m) : (b i : ℝ) =
      (⌊(N:ℝ)*α i.succ⌋₊ : ℝ)/(N:ℝ) := by simp [b]
  have hble (i : Fin m) : (b i : ℝ) ≤ α i.succ := by
    rw [hbcast, div_le_iff₀ hNpos]
    simpa [mul_comm] using Nat.floor_le (mul_nonneg hNpos.le (hα i.succ))
  have hberr (i : Fin m) : α i.succ-(b i : ℝ) < 1/(N:ℝ) := by
    rw [hbcast]
    have hf := Nat.lt_floor_add_one ((N:ℝ)*α i.succ)
    apply (lt_div_iff₀ hNpos).2
    rw [sub_mul, div_mul_cancel₀ _ hN0]
    nlinarith
  have hsumα : α 0 + ∑ i : Fin m, α i.succ = 1 := by
    simpa only [Fin.sum_univ_succ] using hsum
  have htail : (∑ i : Fin m, (b i : ℝ)) ≤ ∑ i : Fin m, α i.succ :=
    Finset.sum_le_sum fun i _ => hble i
  have hres : (0 : ℝ) ≤ 1-∑ i : Fin m, (b i : ℝ) := by
    have := hα 0
    linarith
  let q : Fin (m+1) → ℚ := Fin.cons (1-∑ i, b i) b
  refine ⟨q, ?_, ?_, ?_⟩
  · intro i
    refine Fin.cases ?_ (fun j => hb0 j) i
    change (0:ℚ) ≤ 1-∑ i, b i
    exact_mod_cast hres
  · simp [q, Fin.sum_univ_succ]
  · have herrsum : (∑ i : Fin m, (α i.succ-(b i : ℝ))) ≤ (m:ℝ)/(N:ℝ) := by
      calc
        _ ≤ ∑ _i : Fin m, 1/(N:ℝ) := Finset.sum_le_sum fun i _ => (hberr i).le
        _ = _ := by simp [nsmul_eq_mul, div_eq_mul_inv]
    have hfirst : (1-∑ i : Fin m, (b i : ℝ))-α 0 =
        ∑ i : Fin m, (α i.succ-(b i : ℝ)) := by
      rw [Finset.sum_sub_distrib]
      linarith
    have hfirst0 : 0 ≤ (1-∑ i : Fin m, (b i : ℝ))-α 0 := by
      rw [hfirst]
      exact Finset.sum_nonneg fun i _ => sub_nonneg.mpr (hble i)
    have hnorm : (∑ i, |(q i : ℝ)-α i|) =
        2 * ∑ i : Fin m, (α i.succ-(b i : ℝ)) := by
      rw [Fin.sum_univ_succ]
      simp only [q, Fin.cons_zero, Fin.cons_succ, Rat.cast_sub, Rat.cast_one,
        Rat.cast_sum, abs_of_nonneg hfirst0]
      rw [hfirst]
      have htailabs : (∑ i : Fin m, |(b i : ℝ)-α i.succ|) =
          ∑ i : Fin m, (α i.succ-(b i : ℝ)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [abs_of_nonpos (sub_nonpos.mpr (hble i))]
        ring
      rw [htailabs]
      ring
    rw [hnorm]
    have hsmall : 2*(m:ℝ)/(N:ℝ) < δ := by
      apply (div_lt_iff₀ hNpos).2
      have := (div_lt_iff₀ hδ).1 hN
      nlinarith
    calc
      _ ≤ 2*((m:ℝ)/(N:ℝ)) := mul_le_mul_of_nonneg_left herrsum (by norm_num)
      _ = 2*(m:ℝ)/(N:ℝ) := by ring
      _ < δ := hsmall

theorem stageMean_mem_convexHull (v : ℕ → X) (n : ℕ) :
    stageMean v n ∈ convexHull ℝ (Set.range v) := by
  exact mem_convexHull_of_exists_fintype (positiveStageWeights n)
    (fun i => v i.val) (fun i => (positiveStageWeights_pos n i).le)
    (positiveStageWeights_sum n) (fun i => ⟨i.val, rfl⟩) rfl

theorem rationalPrefixMean_mem_closure (v : ℕ → X) (B : ℝ)
    (hB : 0 ≤ B) (hv : ∀ i, ‖v i‖ ≤ B) (q : RationalPrefix) :
    rationalPrefixMean v q ∈ closure (Set.range (stageMean v)) := by
  apply Metric.mem_closure_iff.2
  intro δ hδ
  obtain ⟨n, _, hn⟩ := exists_late_stageMean_close_rational v B hB hv q δ hδ 0
  exact ⟨stageMean v n, ⟨n, rfl⟩, by simpa [dist_eq_norm, norm_sub_rev] using hn⟩

theorem prefixMean_mem_closure (v : ℕ → X) (B : ℝ)
    (hB : 0 ≤ B) (hv : ∀ i, ‖v i‖ ≤ B) (m : ℕ)
    (α : Fin (m+1) → ℝ) (hα : ∀ i, 0 ≤ α i) (hsum : ∑ i, α i = 1) :
    (∑ i : Fin (m+1), α i • v i.val) ∈ closure (Set.range (stageMean v)) := by
  apply closure_minimal (fun _ hx => hx) isClosed_closure
  apply Metric.mem_closure_iff.2
  intro δ hδ
  have hBp : 0 < B+1 := by linarith
  obtain ⟨q, hq0, hq1, hqerr⟩ :=
    exists_rational_simplex_l1_close m α hα hsum (δ/(B+1)) (div_pos hδ hBp)
  let Q : RationalPrefix := ⟨m, q, hq0, hq1⟩
  refine ⟨rationalPrefixMean v Q, rationalPrefixMean_mem_closure v B hB hv Q, ?_⟩
  have hbary : ‖(∑ i : Fin (m+1), α i • v i.val)-rationalPrefixMean v Q‖ ≤
      (∑ i, |(q i : ℝ)-α i|)*(B+1) := by
    unfold rationalPrefixMean
    change ‖(∑ i : Fin (m+1), α i • v i.val)-∑ i, (q i : ℝ) • v i.val‖ ≤ _
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ i : Fin (m+1), ‖α i • v i.val-(q i:ℝ) • v i.val‖ := norm_sum_le _ _
      _ = ∑ i : Fin (m+1), |(q i:ℝ)-α i| *‖v i.val‖ := by
        apply Finset.sum_congr rfl
        intro i _
        rw [← sub_smul, norm_smul, Real.norm_eq_abs, abs_sub_comm]
      _ ≤ ∑ i : Fin (m+1), |(q i:ℝ)-α i| *(B+1) := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_left ((hv i.val).trans (by linarith)) (abs_nonneg _)
      _ = _ := by rw [Finset.sum_mul]
  rw [dist_eq_norm]
  exact hbary.trans_lt ((lt_div_iff₀ hBp).1 hqerr)

/-- Every finite convex combination of a sequence fits in one initial prefix. -/
theorem convexHull_range_subset_of_prefixes (v : ℕ → X) (E : Set X)
    (hprefix : ∀ n, convexHull ℝ (Set.range (fun i : Fin (n+1) => v i.val)) ⊆ E) :
    convexHull ℝ (Set.range v) ⊆ E := by
  let H (n : ℕ) := convexHull ℝ (Set.range (fun i : Fin (n+1) => v i.val))
  have hmono : Monotone H := by
    intro n m hnm
    apply convexHull_mono
    rintro x ⟨i, rfl⟩
    exact ⟨⟨i.val, lt_of_lt_of_le i.isLt (Nat.add_le_add_right hnm 1)⟩, rfl⟩
  have hdir : Directed (· ⊆ ·) H := fun n m =>
    ⟨max n m, hmono (le_max_left _ _), hmono (le_max_right _ _)⟩
  have hconv : Convex ℝ (⋃ n, H n) := hdir.convex_iUnion (fun _ => convex_convexHull _ _)
  have hbase : Set.range v ⊆ ⋃ n, H n := by
    rintro x ⟨n, rfl⟩
    exact Set.mem_iUnion.2 ⟨n, subset_convexHull ℝ _ ⟨Fin.last n, rfl⟩⟩
  intro x hx
  obtain ⟨n, hn⟩ := Set.mem_iUnion.1 (convexHull_min hbase hconv hx)
  exact hprefix n hn

theorem closure_range_stageMean_eq (v : ℕ → X) (B : ℝ)
    (hB : 0 ≤ B) (hv : ∀ i, ‖v i‖ ≤ B) :
    closure (Set.range (stageMean v)) = closure (convexHull ℝ (Set.range v)) := by
  apply Set.Subset.antisymm
  · apply closure_mono
    rintro x ⟨n, rfl⟩
    exact stageMean_mem_convexHull v n
  · apply closure_minimal _ isClosed_closure
    apply convexHull_range_subset_of_prefixes v
    intro m x hx
    rw [convexHull_range_eq_exists_affineCombination] at hx
    obtain ⟨s, w, hw0, hw1, hcomb⟩ := hx
    let α : Fin (m+1) → ℝ := fun i => if i ∈ s then w i else 0
    have hα0 : ∀ i, 0 ≤ α i := by
      intro i
      dsimp [α]
      split_ifs with hi
      · exact hw0 i hi
      · exact le_rfl
    have hα1 : ∑ i, α i = 1 := by simpa [α] using hw1
    have he : (∑ i, α i • v i.val) = x := by
      rw [Finset.affineCombination_eq_linear_combination _ _ _ hw1] at hcomb
      simpa [α, ite_smul] using hcomb
    rw [← he]
    exact prefixMean_mem_closure v B hB hv m α hα0 hα1

end Tingley

end

end OAI

-- Adapted from OAI.Analysis.SphereIsometry.InvariantConvexSet

namespace OAI

/-!
A closed invariant convex set from proved finite-prefix growth. The input
growth theorem is instantiated by the geometric common-support argument;
the recursion, positive scheduling, density and invariance are proved here.
-/

noncomputable section

open scoped BigOperators
open Set

namespace Tingley

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Ordinary finite-prefix recursion; no admissibility proof enters the data. -/
def recursivePrefix (G : X → X) (v₀ : X) : (n : ℕ) → (Fin (n+1) → X)
  | 0 => fun _ => v₀
  | n+1 => Fin.snoc (α := fun _ : Fin (n+2) => X) (recursivePrefix G v₀ n)
      (G (∑ i, positiveStageWeights n i • recursivePrefix G v₀ n i))

def recursiveVector (G : X → X) (v₀ : X) (n : ℕ) : X :=
  recursivePrefix G v₀ n (Fin.last n)

@[simp] theorem recursiveVector_zero (G : X → X) (v₀ : X) :
    recursiveVector G v₀ 0 = v₀ := rfl

theorem recursivePrefix_eq_vector (G : X → X) (v₀ : X)
    (n : ℕ) (i : Fin (n+1)) :
    recursivePrefix G v₀ n i = recursiveVector G v₀ i.val := by
  induction n with
  | zero =>
      have hi : i.val = 0 := by omega
      simp [recursivePrefix]
  | succ n ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rfl
      · simpa only [recursivePrefix, Fin.snoc_castSucc, Fin.val_castSucc] using ih j

theorem recursiveVector_succ (G : X → X) (v₀ : X) (n : ℕ) :
    recursiveVector G v₀ (n+1) = G (stageMean (recursiveVector G v₀) n) := by
  unfold recursiveVector
  rw [recursivePrefix, Fin.snoc_last]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [recursivePrefix_eq_vector]
  rfl

/-- The geometric one-step conclusion for the invariant convex set. -/
def PositivePrefixGrowth (G : X → X) (E : Set X) : Prop :=
  ∀ (n : ℕ) (p : Fin (n+1) → X) (w : Fin (n+1) → ℝ),
    convexHull ℝ (Set.range p) ⊆ E →
    (∀ i, 0 < w i) → (∑ i, w i = 1) →
    convexHull ℝ (Set.range
      (Fin.snoc (α := fun _ : Fin (n+2) => X) p (G (∑ i, w i • p i)))) ⊆ E

theorem recursivePrefix_hull_subset (G : X → X) (E : Set X) (v₀ : X)
    (hv₀ : v₀ ∈ E) (hstep : PositivePrefixGrowth G E) (n : ℕ) :
    convexHull ℝ (Set.range (recursivePrefix G v₀ n)) ⊆ E := by
  induction n with
  | zero =>
      have hr : Set.range (recursivePrefix G v₀ 0) = {v₀} := by
        ext x
        constructor
        · rintro ⟨i, rfl⟩; rfl
        · intro hx
          exact ⟨0, hx.symm⟩
      rw [hr, convexHull_singleton]
      exact Set.singleton_subset_iff.mpr hv₀
  | succ n ih =>
      exact hstep n (recursivePrefix G v₀ n) (positiveStageWeights n) ih
        (positiveStageWeights_pos n) (positiveStageWeights_sum n)

theorem recursiveVector_prefix_hull_subset (G : X → X) (E : Set X) (v₀ : X)
    (hv₀ : v₀ ∈ E) (hstep : PositivePrefixGrowth G E) (n : ℕ) :
    convexHull ℝ (Set.range (fun i : Fin (n+1) => recursiveVector G v₀ i.val)) ⊆ E := by
  have he : (fun i : Fin (n+1) => recursiveVector G v₀ i.val) =
      recursivePrefix G v₀ n := by
    funext i
    exact (recursivePrefix_eq_vector G v₀ n i).symm
  rw [he]
  exact recursivePrefix_hull_subset G E v₀ hv₀ hstep n

theorem recursiveVector_mem (G : X → X) (E : Set X) (v₀ : X)
    (hv₀ : v₀ ∈ E) (hstep : PositivePrefixGrowth G E) (n : ℕ) :
    recursiveVector G v₀ n ∈ E :=
  recursivePrefix_hull_subset G E v₀ hv₀ hstep n
    (subset_convexHull ℝ _ ⟨Fin.last n, rfl⟩)

/-- The closed convex hull of the one actual recursively constructed sequence. -/
def recursiveConvexSet (G : X → X) (v₀ : X) : Set X :=
  closure (convexHull ℝ (Set.range (recursiveVector G v₀)))

theorem recursiveConvexSet_subset (G : X → X) (E : Set X) (v₀ : X)
    (hv₀ : v₀ ∈ E) (hE : IsClosed E) (hstep : PositivePrefixGrowth G E) :
    recursiveConvexSet G v₀ ⊆ E := by
  apply closure_minimal _ hE
  exact convexHull_range_subset_of_prefixes _ E
    (recursiveVector_prefix_hull_subset G E v₀ hv₀ hstep)

theorem recursiveConvexSet_nonempty (G : X → X) (v₀ : X) :
    (recursiveConvexSet G v₀).Nonempty := by
  refine ⟨recursiveVector G v₀ 0, subset_closure ?_⟩
  exact subset_convexHull ℝ _ ⟨0, rfl⟩

theorem isClosed_recursiveConvexSet (G : X → X) (v₀ : X) :
    IsClosed (recursiveConvexSet G v₀) := isClosed_closure

theorem convex_recursiveConvexSet (G : X → X) (v₀ : X) :
    Convex ℝ (recursiveConvexSet G v₀) := (convex_convexHull ℝ _).closure

theorem recursiveConvexSet_invariant (G : X → X) (E : Set X) (v₀ : X)
    (hv₀ : v₀ ∈ E) (hE : IsClosed E) (hunit : ∀ x ∈ E, ‖x‖ = 1)
    (hG : ContinuousOn G E) (hstep : PositivePrefixGrowth G E) :
    Set.MapsTo G (recursiveConvexSet G v₀) (recursiveConvexSet G v₀) := by
  let v := recursiveVector G v₀
  have hv : ∀ n, ‖v n‖ ≤ (1 : ℝ) :=
    fun n => (hunit _ (recursiveVector_mem G E v₀ hv₀ hstep n)).le
  have hdense : closure (Set.range (stageMean v)) = recursiveConvexSet G v₀ :=
    closure_range_stageMean_eq v 1 (by norm_num) hv
  have himage : Set.MapsTo G (Set.range (stageMean v)) (recursiveConvexSet G v₀) := by
    rintro x ⟨n, rfl⟩
    rw [← recursiveVector_succ G v₀ n]
    exact subset_closure (subset_convexHull ℝ _ ⟨n+1, rfl⟩)
  have hcont : ContinuousOn G (closure (Set.range (stageMean v))) := by
    rw [hdense]
    exact hG.mono (recursiveConvexSet_subset G E v₀ hv₀ hE hstep)
  have h := himage.closure_of_continuousOn hcont
  rw [hdense, (isClosed_recursiveConvexSet G v₀).closure_eq] at h
  exact h

/-- No density or invariant-set premise: both are obtained from the positive recursion. -/
theorem exists_invariant_closed_convex (G : X → X) (E : Set X) (v₀ : X)
    (hv₀ : v₀ ∈ E) (hE : IsClosed E) (hunit : ∀ x ∈ E, ‖x‖ = 1)
    (hG : ContinuousOn G E) (hstep : PositivePrefixGrowth G E) :
    ∃ C : Set X, C.Nonempty ∧ IsClosed C ∧ Bornology.IsBounded C ∧
      Convex ℝ C ∧ C ⊆ E ∧ Set.MapsTo G C C := by
  have hsub := recursiveConvexSet_subset G E v₀ hv₀ hE hstep
  refine ⟨recursiveConvexSet G v₀, recursiveConvexSet_nonempty G v₀,
    isClosed_recursiveConvexSet G v₀, ?_, convex_recursiveConvexSet G v₀, hsub,
    recursiveConvexSet_invariant G E v₀ hv₀ hE hunit hG hstep⟩
  apply isBounded_iff_forall_norm_le.mpr
  exact ⟨1, fun x hx => (hunit x (hsub hx)).le⟩

end Tingley

end

end OAI

-- Adapted from OAI.Analysis.SphereIsometry.AlignmentSet

namespace OAI

/-!
# The actual closed convex invariant subset of the extremal sphere

The generic positive scheduling theorem is instantiated with the proved
common-support hull growth. No convexity of the full extremal set is assumed.
-/

noncomputable section

namespace Tingley

variable {X Y : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem exists_return_invariant_convex
    (f : UnitSphere X ≃ᵢ UnitSphere Y) (y x₀ : UnitSphere X)
    (t M : ℝ) (ht : 0 < t ∧ t < 1)
    (hb : HasDefectBound f M) (hatt : signedDefect f t x₀ y = M) :
    ∃ C : Set X, C.Nonempty ∧ IsClosed C ∧ Bornology.IsBounded C ∧
      Convex ℝ C ∧ C ⊆ extremalSet f y t ht M ∧
      ContinuousOn (returnAmbient f y t ht) C ∧
      Set.MapsTo (returnAmbient f y t ht) C C := by
  obtain ⟨v₀, hv₀⟩ := extremalSet_nonempty_of_attained f y t ht M x₀ hatt
  have hcont : ContinuousOn (returnAmbient f y t ht) (extremalSet f y t ht M) :=
    (continuousOn_returnAmbient f y t ht).mono
      (fun _ hv => norm_eq_one_of_mem_extremalSet f y t ht M hv)
  obtain ⟨C, hCne, hCc, hCb, hCconv, hCE, hGC⟩ :=
    exists_invariant_closed_convex (returnAmbient f y t ht)
      (extremalSet f y t ht M) v₀ hv₀ (isClosed_extremalSet f y t ht M)
      (fun _ hv => norm_eq_one_of_mem_extremalSet f y t ht M hv) hcont
      (positive_prefix_extension f y t ht M hb)
  exact ⟨C, hCne, hCc, hCb, hCconv, hCE, hcont.mono hCE, hGC⟩

end Tingley

end

end OAI

-- Adapted from OAI.Analysis.SphereIsometry.ReturnMapEstimate

namespace OAI

/-!
# The actual return map's two-point estimate

The two triangle-inequality comparisons retain the unprimed radius multiplying
both direction differences. The sphere isometry connects the actual endpoints;
no pairwise estimate for an arbitrary map is assumed.
-/

noncomputable section

namespace Tingley

universe u v

variable {X : Type u} {Y : Type v}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Changing both the scalar and a unit vector, retaining the first scalar
in front of the direction difference. -/
theorem norm_smul_sub_smul_le_first (a b : ℝ) (ha : 0 ≤ a)
    (v w : UnitSphere X) :
    ‖a • (v : X) - b • (w : X)‖ ≤ a * ‖(v : X) - (w : X)‖ + |a - b| := by
  have he : a • (v : X) - b • (w : X) =
      a • ((v : X) - (w : X)) + (a - b) • (w : X) := by
    simp only [smul_sub, sub_smul]
    abel
  calc
    ‖a • (v : X) - b • (w : X)‖ =
        ‖a • ((v : X) - (w : X)) + (a - b) • (w : X)‖ := congrArg norm he
    _ ≤ ‖a • ((v : X) - (w : X))‖ + ‖(a - b) • (w : X)‖ := norm_add_le _ _
    _ = a * ‖(v : X) - (w : X)‖ + |a - b| := by
      rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_eq_abs,
        w.property, mul_one]

/-- Recovering the direction difference from two differently scaled unit
vectors, again retaining the first scalar. -/
theorem first_mul_norm_sub_le_smul_sub (a b : ℝ) (ha : 0 ≤ a)
    (v w : UnitSphere X) :
    a * ‖(v : X) - (w : X)‖ ≤ ‖a • (v : X) - b • (w : X)‖ + |a - b| := by
  have he : a • ((v : X) - (w : X)) =
      (a • (v : X) - b • (w : X)) + (b - a) • (w : X) := by
    simp only [smul_sub, sub_smul]
    abel
  calc
    a * ‖(v : X) - (w : X)‖ = ‖a • ((v : X) - (w : X))‖ := by
      rw [norm_smul, Real.norm_of_nonneg ha]
    _ = ‖(a • (v : X) - b • (w : X)) + (b - a) • (w : X)‖ :=
      congrArg norm he
    _ ≤ ‖a • (v : X) - b • (w : X)‖ + ‖(b - a) • (w : X)‖ := norm_add_le _ _
    _ = ‖a • (v : X) - b • (w : X)‖ + |a - b| := by
      rw [norm_smul, Real.norm_eq_abs, w.property, mul_one, abs_sub_comm b a]

/-- The scalar elimination used after the two actual endpoint comparisons.
Only the radii by which we divide require strict positivity. -/
theorem return_pair_scalar_elimination
    (r s u p A B Dg Dw Dv : ℝ) (hr : 0 < r) (hs : 0 < s) (hu : 0 ≤ u)
    (hg : r * Dg ≤ 2 * A + u * Dw)
    (hw : s * Dw ≤ 2 * B + p * Dv) :
    Dg ≤ (u * p / (r * s)) * Dv + 2 * A / r + 2 * u * B / (r * s) := by
  have hw' : Dw ≤ (2 * B + p * Dv) / s := by
    apply (le_div_iff₀ hs).2
    simpa only [mul_comm Dw s] using hw
  calc
    Dg ≤ (2 * A + u * Dw) / r := by
      apply (le_div_iff₀ hr).2
      simpa only [mul_comm Dg r] using hg
    _ ≤ (2 * A + u * ((2 * B + p * Dv) / s)) / r :=
      div_le_div_of_nonneg_right
        (add_le_add_right (mul_le_mul_of_nonneg_left hw' hu) _) hr.le
    _ = (u * p / (r * s)) * Dv + 2 * A / r + 2 * u * B / (r * s) := by
      field_simp [ne_of_gt hr, ne_of_gt hs]
      ring

/-- The exact two-point estimate for the constructed return map on its actual
extremal sphere set. Both endpoint comparisons use the original sphere isometry. -/
theorem returnSphere_pair_estimate
    (f : UnitSphere X ≃ᵢ UnitSphere Y) (y : UnitSphere X)
    (t : ℝ) (ht : 0 < t ∧ t < 1) (M : ℝ) (hb : HasDefectBound f M)
    {v v' : UnitSphere X}
    (hv : v ∈ extremalSphere f y t ht M)
    (hv' : v' ∈ extremalSphere f y t ht M) :
    ‖(returnSphere f y t ht v : X) - (returnSphere f y t ht v' : X)‖ ≤
      (uRadius f y t ht v * pRadius f y t ht v /
        (rRadius f y t ht v * sRadius f y t ht v)) * ‖(v : X) - (v' : X)‖ +
      2 * |uRadius f y t ht v - uRadius f y t ht v'| / rRadius f y t ht v +
      2 * uRadius f y t ht v * |pRadius f y t ht v - pRadius f y t ht v'| /
        (rRadius f y t ht v * sRadius f y t ht v) := by
  let p := pRadius f y t ht
  let s := sRadius f y t ht
  let u := uRadius f y t ht
  let r := rRadius f y t ht
  let g := returnSphere f y t ht
  let w := wDirection f y t ht
  let x := xPoint f y t ht
  let z := zPoint f y t ht
  have hx (a : UnitSphere X) : (x a : X) = t • (y : X) + p a • (a : X) :=
    xPoint_eq f y t ht a
  have hz (a : UnitSphere X) : (z a : X) = t • (y : X) - r a • (g a : X) :=
    zPoint_eq f y t ht a
  have hfx (a : UnitSphere X) : (f (x a) : Y) =
      t • (f y : Y) + s a • (w a : Y) := fxPoint_eq f y t ht a
  have hfz (a : UnitSphere X) : (f (z a) : Y) =
      t • (f y : Y) - u a • (w a : Y) := fzPoint_eq f y t ht a
  have hr : 0 < r v := rRadius_pos f y t ht v
  have hs : 0 < s v := sRadius_pos f y t ht v
  have hu : 0 ≤ u v := (uRadius_pos f y t ht v).le
  have hp : 0 ≤ p v := (pRadius_pos f y t ht v).le
  have hrdiff : r v - r v' = u v - u v' := by
    have h := rRadius_eq_add f y t ht M hb hv
    have h' := rRadius_eq_add f y t ht M hb hv'
    change r v = u v + M at h
    change r v' = u v' + M at h'
    linarith
  have hsdiff : s v - s v' = p v - p v' := by
    have h := sRadius_eq_add f y t ht M hv
    have h' := sRadius_eq_add f y t ht M hv'
    change s v = p v + M at h
    change s v' = p v' + M at h'
    linarith
  have hR : ‖r v • (g v : X) - r v' • (g v' : X)‖ =
      ‖u v • (w v : Y) - u v' • (w v' : Y)‖ := by
    calc
      ‖r v • (g v : X) - r v' • (g v' : X)‖ = ‖(z v' : X) - (z v : X)‖ := by
        congr 1
        rw [hz v', hz v]
        abel
      _ = ‖(f (z v') : Y) - (f (z v) : Y)‖ :=
        (sphere_norm_sub f (z v') (z v)).symm
      _ = ‖u v • (w v : Y) - u v' • (w v' : Y)‖ := by
        congr 1
        rw [hfz v', hfz v]
        abel
  have hS : ‖s v • (w v : Y) - s v' • (w v' : Y)‖ =
      ‖p v • (v : X) - p v' • (v' : X)‖ := by
    calc
      ‖s v • (w v : Y) - s v' • (w v' : Y)‖ =
          ‖(f (x v) : Y) - (f (x v') : Y)‖ := by
        congr 1
        rw [hfx v, hfx v']
        abel
      _ = ‖(x v : X) - (x v' : X)‖ := sphere_norm_sub f (x v) (x v')
      _ = ‖p v • (v : X) - p v' • (v' : X)‖ := by
        congr 1
        rw [hx v, hx v']
        abel
  have hG : r v * ‖(g v : X) - (g v' : X)‖ ≤
      2 * |u v - u v'| + u v * ‖(w v : Y) - (w v' : Y)‖ := by
    have h₁ := first_mul_norm_sub_le_smul_sub (r v) (r v') hr.le (g v) (g v')
    have h₂ := norm_smul_sub_smul_le_first (u v) (u v') hu (w v) (w v')
    rw [hR, hrdiff] at h₁
    linarith
  have hW : s v * ‖(w v : Y) - (w v' : Y)‖ ≤
      2 * |p v - p v'| + p v * ‖(v : X) - (v' : X)‖ := by
    have h₁ := first_mul_norm_sub_le_smul_sub (s v) (s v') hs.le (w v) (w v')
    have h₂ := norm_smul_sub_smul_le_first (p v) (p v') hp v v'
    rw [hS, hsdiff] at h₁
    linarith
  exact return_pair_scalar_elimination (r v) (s v) (u v) (p v)
    |u v - u v'| |p v - p v'| ‖(g v : X) - (g v' : X)‖
    ‖(w v : Y) - (w v' : Y)‖ ‖(v : X) - (v' : X)‖ hr hs hu hG hW

/-- The same estimate for the totalized ambient map. Membership in the actual
extremal set ensures that every ambient function takes its sphere branch. -/
theorem returnAmbient_pair_estimate
    (f : UnitSphere X ≃ᵢ UnitSphere Y) (y : UnitSphere X)
    (t : ℝ) (ht : 0 < t ∧ t < 1) (M : ℝ) (hb : HasDefectBound f M)
    {v v' : X} (hv : v ∈ extremalSet f y t ht M)
    (hv' : v' ∈ extremalSet f y t ht M) :
    ‖returnAmbient f y t ht v - returnAmbient f y t ht v'‖ ≤
      (uAmbient f y t ht v * pAmbient f y t ht v /
        (rAmbient f y t ht v * sAmbient f y t ht v)) * ‖v - v'‖ +
      2 * |uAmbient f y t ht v - uAmbient f y t ht v'| / rAmbient f y t ht v +
      2 * uAmbient f y t ht v * |pAmbient f y t ht v - pAmbient f y t ht v'| /
        (rAmbient f y t ht v * sAmbient f y t ht v) := by
  obtain ⟨a, ha, rfl⟩ := hv
  obtain ⟨b, hb', rfl⟩ := hv'
  simpa only [returnAmbient_coe, pAmbient_coe, sAmbient_coe, uAmbient_coe,
    rAmbient_coe] using returnSphere_pair_estimate f y t ht M hb ha hb'

/-- Restriction to any subset of the actual extremal set, including the closed
invariant convex set constructed from the positive schedule. -/
theorem returnAmbient_pair_estimate_on
    (f : UnitSphere X ≃ᵢ UnitSphere Y) (y : UnitSphere X)
    (t : ℝ) (ht : 0 < t ∧ t < 1) (M : ℝ) (hb : HasDefectBound f M)
    (C : Set X) (hC : C ⊆ extremalSet f y t ht M)
    {v v' : X} (hv : v ∈ C) (hv' : v' ∈ C) :
    ‖returnAmbient f y t ht v - returnAmbient f y t ht v'‖ ≤
      (uAmbient f y t ht v * pAmbient f y t ht v /
        (rAmbient f y t ht v * sAmbient f y t ht v)) * ‖v - v'‖ +
      2 * |uAmbient f y t ht v - uAmbient f y t ht v'| / rAmbient f y t ht v +
      2 * uAmbient f y t ht v * |pAmbient f y t ht v - pAmbient f y t ht v'| /
        (rAmbient f y t ht v * sAmbient f y t ht v) :=
  returnAmbient_pair_estimate f y t ht M hb (hC hv) (hC hv')

end Tingley

end

end OAI

-- Adapted from OAI.Analysis.SphereIsometry.DiameterBounds

namespace OAI

/-! # Pairwise diameter bounds

The predicate records the distance between every pair of points. It does not
use the real-valued diameter of a possibly unbounded set.
-/

namespace Tingley

variable {E : Type*} [PseudoMetricSpace E]

/-- Every pair of points in a set is at distance at most the given radius. -/
def DiameterLE (A : Set E) (δ : ℝ) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, dist x y ≤ δ

namespace DiameterLE

variable {A B : Set E} {δ ε : ℝ}

theorem mono_set (h : DiameterLE B δ) (hAB : A ⊆ B) : DiameterLE A δ :=
  fun x hx y hy => h x (hAB hx) y (hAB hy)

theorem mono_radius (h : DiameterLE A δ) (hδε : δ ≤ ε) : DiameterLE A ε :=
  fun x hx y hy => (h x hx y hy).trans hδε

theorem closure (h : DiameterLE A δ) : DiameterLE (closure A) δ := by
  intro x hx y hy
  exact isClosed_Iic.closure_subset
    (map_mem_closure₂ continuous_dist hx hy (fun _ ha _ hb => h _ ha _ hb))

end DiameterLE

end Tingley

end OAI

-- Adapted from OAI.Analysis.SphereIsometry.KuratowskiBasic

namespace OAI

/-! # The Kuratowski measure from finite diameter covers

The infimum uses positive real radii. The boundedness
hypotheses ensure that its defining set is nonempty. No compactness theorem
or fixed-point principle is part of this definition.
-/

namespace Tingley

variable {E : Type*} [PseudoMetricSpace E]

/-- A finite family of sets of pairwise diameter at most the given radius. -/
def FiniteDiameterCover (H : Set E) (δ : ℝ) : Prop :=
  ∃ n : ℕ, ∃ A : Fin n → Set E,
    (H ⊆ ⋃ i, A i) ∧ ∀ i, DiameterLE (A i) δ

namespace FiniteDiameterCover

variable {H A B : Set E} {δ ε : ℝ}

theorem of_fintype {ι : Type*} [Fintype ι] (U : ι → Set E)
    (hc : H ⊆ ⋃ i, U i) (hd : ∀ i, DiameterLE (U i) δ) :
    FiniteDiameterCover H δ := by
  classical
  let e := Fintype.equivFin ι
  refine ⟨Fintype.card ι, fun j => U (e.symm j), ?_, fun j => hd (e.symm j)⟩
  intro x hx
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hc hx)
  exact Set.mem_iUnion.mpr ⟨e i, by simpa only [Equiv.symm_apply_apply] using hi⟩

theorem empty (δ : ℝ) : FiniteDiameterCover (∅ : Set E) δ := by
  refine ⟨0, fun _ => ∅, Set.empty_subset _, ?_⟩
  intro i
  exact Fin.elim0 i

theorem mono_set (hc : FiniteDiameterCover B δ) (hAB : A ⊆ B) :
    FiniteDiameterCover A δ := by
  obtain ⟨n, U, hcover, hd⟩ := hc
  exact ⟨n, U, hAB.trans hcover, hd⟩

theorem mono_radius (hc : FiniteDiameterCover H δ) (hδε : δ ≤ ε) :
    FiniteDiameterCover H ε := by
  obtain ⟨n, U, hcover, hd⟩ := hc
  exact ⟨n, U, hcover, fun i => (hd i).mono_radius hδε⟩

theorem closure (hc : FiniteDiameterCover H δ) :
    FiniteDiameterCover (closure H) δ := by
  obtain ⟨n, U, hcover, hd⟩ := hc
  refine ⟨n, fun i => _root_.closure (U i), ?_, fun i => (hd i).closure⟩
  intro x hx
  have hx' : x ∈ _root_.closure (⋃ i, U i) := closure_mono hcover hx
  simpa only [closure_iUnion_of_finite] using hx'

end FiniteDiameterCover

/-- Positive radii admitting a finite diameter cover. -/
def coverRadii (H : Set E) : Set ℝ :=
  {δ | 0 < δ ∧ FiniteDiameterCover H δ}

/-- The Kuratowski measure of noncompactness, on bounded sets. -/
noncomputable def chi (H : Set E) : ℝ := sInf (coverRadii H)

theorem coverRadii_bddBelow (H : Set E) : BddBelow (coverRadii H) :=
  ⟨0, fun _ hδ => hδ.1.le⟩

theorem coverRadii_nonempty {H : Set E} (hH : Bornology.IsBounded H) :
    (coverRadii H).Nonempty := by
  obtain ⟨R, hR⟩ := Metric.isBounded_iff.mp hH
  have hc : FiniteDiameterCover H (max R 1) := by
    refine ⟨1, fun _ => H, ?_, ?_⟩
    · intro x hx
      exact Set.mem_iUnion.mpr ⟨0, hx⟩
    · intro i x hx y hy
      exact (hR hx hy).trans (le_max_left R 1)
  exact ⟨max R 1, lt_of_lt_of_le zero_lt_one (le_max_right R 1), hc⟩

theorem chi_nonneg {H : Set E} (hH : Bornology.IsBounded H) : 0 ≤ chi H :=
  le_csInf (coverRadii_nonempty hH) (fun _ hδ => hδ.1.le)

theorem chi_le_of_cover {H : Set E} {δ : ℝ}
    (hδ : 0 ≤ δ) (hc : FiniteDiameterCover H δ) : chi H ≤ δ := by
  by_contra hnot
  have hlt : δ < chi H := lt_of_not_ge hnot
  let ε : ℝ := (chi H - δ) / 2
  have hε : 0 < ε := by dsimp only [ε]; linarith
  have hmem : δ + ε ∈ coverRadii H :=
    ⟨by linarith, hc.mono_radius (by linarith)⟩
  have hupper : chi H ≤ δ + ε := csInf_le (coverRadii_bddBelow H) hmem
  dsimp only [ε] at hupper
  linarith

@[simp] theorem chi_empty : chi (∅ : Set E) = 0 := by
  apply le_antisymm
  · exact chi_le_of_cover le_rfl (FiniteDiameterCover.empty 0)
  · exact chi_nonneg Bornology.isBounded_empty

theorem chi_mono {A B : Set E} (hB : Bornology.IsBounded B) (hAB : A ⊆ B) :
    chi A ≤ chi B := by
  apply csInf_le_csInf (coverRadii_bddBelow A) (coverRadii_nonempty hB)
  intro δ hδ
  exact ⟨hδ.1, hδ.2.mono_set hAB⟩

theorem exists_cover_of_chi_lt {H : Set E} {ε : ℝ}
    (hH : Bornology.IsBounded H) (hε : chi H < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ < ε ∧ FiniteDiameterCover H δ := by
  obtain ⟨δ, hδ, hδε⟩ :=
    (csInf_lt_iff (coverRadii_bddBelow H) (coverRadii_nonempty hH)).mp hε
  exact ⟨δ, hδ.1, hδε, hδ.2⟩

theorem chi_closure {H : Set E} (hH : Bornology.IsBounded H) :
    chi (closure H) = chi H := by
  apply le_antisymm
  · apply le_csInf (coverRadii_nonempty hH)
    intro δ hδ
    exact chi_le_of_cover hδ.1.le hδ.2.closure
  · exact chi_mono hH.closure subset_closure

end Tingley

end OAI

-- Adapted from OAI.Analysis.SphereIsometry.ReturnMapBounds

namespace OAI

/-! Scalar estimates for the return map, before taking finite diameter covers. -/

namespace Tingley

theorem radius_ratio_le_factor {p s M U : ℝ} (hs : 0 < s)
    (hM : 0 ≤ M) (hsU : s ≤ U) (hsp : s = p + M) :
    p / s ≤ 1 - M / U := by
  calc
    p / s = (s - M) / s := congrArg (fun q : ℝ => q / s) (by linarith)
    _ = 1 - M / s := by rw [sub_div, div_self (ne_of_gt hs)]
    _ ≤ 1 - M / U :=
      sub_le_sub_left (div_le_div_of_nonneg_left hM hs hsU) 1

theorem return_coefficient_le {p s u r M U : ℝ}
    (hp : 0 ≤ p) (_hu : 0 ≤ u) (hr : 0 < r) (hs : 0 < s)
    (hM : 0 ≤ M) (hrU : r ≤ U) (hsU : s ≤ U)
    (hrm : r = u + M) (hsm : s = p + M) :
    u * p / (r * s) ≤ (1 - M / U) ^ 2 := by
  have hpq := radius_ratio_le_factor hs hM hsU hsm
  have huq := radius_ratio_le_factor hr hM hrU hrm
  have hp0 : 0 ≤ p / s := div_nonneg hp hs.le
  have hq0 : 0 ≤ 1 - M / U := hp0.trans hpq
  calc
    u * p / (r * s) = (u / r) * (p / s) := by rw [div_mul_div_comm]
    _ ≤ (1 - M / U) * (1 - M / U) := mul_le_mul huq hpq hp0 hq0
    _ = (1 - M / U) ^ 2 := by ring

theorem return_pair_error_le {a r s u du dp : ℝ}
    (ha : 0 < a) (har : a ≤ r) (has : a ≤ s)
    (hur : u ≤ r) (hdu : 0 ≤ du) (hdp : 0 ≤ dp) :
    2 * du / r + 2 * u * dp / (r * s) ≤ (2 / a) * (du + dp) := by
  have hr : 0 < r := ha.trans_le har
  have hs : 0 < s := ha.trans_le has
  have he₁ : 2 * du / r ≤ 2 * du / a :=
    div_le_div_of_nonneg_left (mul_nonneg zero_le_two hdu) ha har
  have he₂ : 2 * u * dp / (r * s) ≤ 2 * dp / a := by
    calc
      2 * u * dp / (r * s) = (u / r) * (2 * dp / s) := by
        field_simp [ne_of_gt hr, ne_of_gt hs]
      _ ≤ 1 * (2 * dp / s) :=
        mul_le_mul_of_nonneg_right ((div_le_one₀ hr).mpr hur)
          (div_nonneg (mul_nonneg zero_le_two hdp) hs.le)
      _ = 2 * dp / s := one_mul _
      _ ≤ 2 * dp / a :=
        div_le_div_of_nonneg_left (mul_nonneg zero_le_two hdp) ha has
  calc
    2 * du / r + 2 * u * dp / (r * s) ≤ 2 * du / a + 2 * dp / a :=
      add_le_add he₁ he₂
    _ = (2 / a) * (du + dp) := by ring

theorem return_pair_uniform_bound {a U M p s u r D Dg du dp : ℝ}
    (ha : 0 < a) (hM : 0 ≤ M)
    (hp : 0 ≤ p) (hu : 0 ≤ u)
    (har : a ≤ r) (has : a ≤ s) (hrU : r ≤ U) (hsU : s ≤ U)
    (hrm : r = u + M) (hsm : s = p + M)
    (hD : 0 ≤ D) (hdu : 0 ≤ du) (hdp : 0 ≤ dp)
    (hpair : Dg ≤ (u * p / (r * s)) * D +
      2 * du / r + 2 * u * dp / (r * s)) :
    Dg ≤ (1 - M / U) ^ 2 * D + (2 / a) * (du + dp) := by
  have hr : 0 < r := ha.trans_le har
  have hs : 0 < s := ha.trans_le has
  have hur : u ≤ r := by linarith
  have hcoeff := return_coefficient_le hp hu hr hs hM hrU hsU hrm hsm
  have herr := return_pair_error_le ha har has hur hdu hdp
  calc
    Dg ≤ (u * p / (r * s)) * D +
        2 * du / r + 2 * u * dp / (r * s) := hpair
    _ = (u * p / (r * s)) * D +
        (2 * du / r + 2 * u * dp / (r * s)) := by ring
    _ ≤ (1 - M / U) ^ 2 * D + (2 / a) * (du + dp) :=
      add_le_add (mul_le_mul_of_nonneg_right hcoeff hD) herr

/-- The exact square factor, with its strict upper bound. -/
theorem return_factor_mem_Ico {t M : ℝ} (ht0 : 0 < t)
    (hM : 0 < M) (hMU : M < 1 + t) :
    (1 - M / (1 + t)) ^ 2 ∈ Set.Ico (0 : ℝ) 1 := by
  have hU : 0 < 1 + t := by linarith
  have hq0 : 0 < M / (1 + t) := div_pos hM hU
  have hq1 : M / (1 + t) < 1 := by
    apply (div_lt_iff₀ hU).mpr
    simpa using hMU
  have hprod : 0 < (1 - M / (1 + t)) * (M / (1 + t)) :=
    mul_pos (by linarith) hq0
  exact ⟨sq_nonneg _, by nlinarith⟩

/-- Nonemptiness is used only to bound M by one actual positive radius. -/
theorem return_contraction_factor_mem_Ico {X : Type*}
    {C : Set X} {p s : X → ℝ} {t M : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) (hM : 0 < M) (hCne : C.Nonempty)
    (hp : ∀ v ∈ C, 1 - t ≤ p v)
    (hsU : ∀ v ∈ C, s v ≤ 1 + t)
    (hsm : ∀ v ∈ C, s v = p v + M) :
    (1 - M / (1 + t)) ^ 2 ∈ Set.Ico (0 : ℝ) 1 := by
  obtain ⟨v, hv⟩ := hCne
  have hpv := hp v hv
  have hsv := hsU v hv
  have heq := hsm v hv
  apply return_factor_mem_Ico ht0 hM
  linarith

end Tingley

end OAI

-- Adapted from OAI.Analysis.SphereIsometry.ScalarBins

namespace OAI

/-!
# Finite scalar bins

A bounded interval is covered by explicitly indexed half-open intervals of
length `η`. The extra final bin includes the top endpoint even when `U / η`
is an integer.
-/

namespace Tingley

/-- Cover `[0,U]` by finitely many scalar bins with pairwise distance at most
`η` inside each bin. The construction also works when `U = 0`. -/
theorem exists_finite_scalar_bins {U η : ℝ} (_hU : 0 ≤ U) (hη : 0 < η) :
    ∃ N : ℕ, ∃ B : Fin N → Set ℝ,
      Set.Icc 0 U ⊆ ⋃ k, B k ∧
      ∀ k, ∀ x ∈ B k, ∀ y ∈ B k, |x - y| ≤ η := by
  let N : ℕ := Nat.floor (U / η) + 1
  let B : Fin N → Set ℝ := fun k =>
    Set.Ico ((k.val : ℝ) * η) (((k.val : ℝ) + 1) * η)
  refine ⟨N, B, ?_, ?_⟩
  · intro x hx
    have hkU : Nat.floor (x / η) ≤ Nat.floor (U / η) :=
      Nat.floor_mono (div_le_div_of_nonneg_right hx.2 hη.le)
    have hkN : Nat.floor (x / η) < N := Nat.lt_succ_of_le hkU
    refine Set.mem_iUnion.mpr ⟨⟨Nat.floor (x / η), hkN⟩, ?_⟩
    change (Nat.floor (x / η) : ℝ) * η ≤ x ∧
      x < ((Nat.floor (x / η) : ℝ) + 1) * η
    exact ⟨(le_div_iff₀ hη).mp (Nat.floor_le (div_nonneg hx.1 hη.le)),
      (div_lt_iff₀ hη).mp (Nat.lt_floor_add_one (x / η))⟩
  · intro k x hx y hy
    change (k.val : ℝ) * η ≤ x ∧ x < ((k.val : ℝ) + 1) * η at hx
    change (k.val : ℝ) * η ≤ y ∧ y < ((k.val : ℝ) + 1) * η at hy
    rw [add_mul, one_mul] at hx hy
    apply abs_le.mpr
    constructor <;> linarith only [hx.1, hx.2, hy.1, hy.2]

end Tingley

end OAI

-- Adapted from OAI.Analysis.SphereIsometry.ReturnMapNoncompactness

namespace OAI

/-!
# The return map contracts noncompactness on every subset

Finite scalar bins refine diameter covers after each piece is intersected
with the given subset. A positive-error argument then passes to the exact
Kuratowski infimum. Neither the subset nor its covering pieces need be compact.
-/

noncomputable section

namespace Tingley

/-- A finite refinement by two bounded scalar observables. -/
theorem finiteDiameterCover_image_of_scalar_bins
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {C H : Set X} {g : X → Y} {p u : X → ℝ} {U a γ δ η : ℝ}
    (hHC : H ⊆ C) (hU : 0 ≤ U) (ha : 0 < a) (hγ : 0 ≤ γ)
    (hp : ∀ v ∈ C, p v ∈ Set.Icc 0 U)
    (hu : ∀ v ∈ C, u v ∈ Set.Icc 0 U)
    (hpair : ∀ v ∈ C, ∀ v' ∈ C,
      dist (g v) (g v') ≤ γ * dist v v' +
        (2 / a) * (|u v - u v'| + |p v - p v'|))
    (hc : FiniteDiameterCover H δ) (hη : 0 < η) :
    FiniteDiameterCover (g '' H) (γ * δ + 4 * η / a) := by
  obtain ⟨n, A, hcover, hdiam⟩ := hc
  obtain ⟨N, B, hBcover, hBdiam⟩ := exists_finite_scalar_bins hU hη
  let Q : (Fin n × Fin N × Fin N) → Set X := fun ijk =>
    H ∩ A ijk.1 ∩ p ⁻¹' B ijk.2.1 ∩ u ⁻¹' B ijk.2.2
  apply FiniteDiameterCover.of_fintype (fun ijk => g '' Q ijk)
  · rintro y ⟨v, hvH, rfl⟩
    obtain ⟨i, hvi⟩ := Set.mem_iUnion.mp (hcover hvH)
    obtain ⟨j, hvj⟩ := Set.mem_iUnion.mp (hBcover (hp v (hHC hvH)))
    obtain ⟨k, hvk⟩ := Set.mem_iUnion.mp (hBcover (hu v (hHC hvH)))
    exact Set.mem_iUnion.mpr
      ⟨(i, j, k), v, ⟨⟨⟨hvH, hvi⟩, hvj⟩, hvk⟩, rfl⟩
  · rintro ijk y ⟨v, hv, rfl⟩ z ⟨v', hv', rfl⟩
    change v ∈ H ∩ A ijk.1 ∩ p ⁻¹' B ijk.2.1 ∩ u ⁻¹' B ijk.2.2 at hv
    change v' ∈ H ∩ A ijk.1 ∩ p ⁻¹' B ijk.2.1 ∩ u ⁻¹' B ijk.2.2 at hv'
    rcases hv with ⟨⟨⟨hvH, hvA⟩, hvp⟩, hvu⟩
    rcases hv' with ⟨⟨⟨hvH', hvA'⟩, hvp'⟩, hvu'⟩
    have hpd : |p v - p v'| ≤ η := hBdiam ijk.2.1 _ hvp _ hvp'
    have hud : |u v - u v'| ≤ η := hBdiam ijk.2.2 _ hvu _ hvu'
    have herr : (2 / a) * (|u v - u v'| + |p v - p v'|) ≤ 4 * η / a := by
      calc
        (2 / a) * (|u v - u v'| + |p v - p v'|) ≤ (2 / a) * (η + η) :=
          mul_le_mul_of_nonneg_left (add_le_add hud hpd) (div_nonneg zero_le_two ha.le)
        _ = 4 * η / a := by ring
    exact (hpair v (hHC hvH) v' (hHC hvH')).trans
      (add_le_add (mul_le_mul_of_nonneg_left (hdiam ijk.1 v hvA v' hvA') hγ) herr)

/-- The exact all-subsets contraction, including the empty subset. The scalar
relations and the two-point estimate are supplied by the actual return map. -/
theorem chi_return_image_le
    {X : Type*} [PseudoMetricSpace X]
    {C : Set X} {g : X → X} {p s u r : X → ℝ} {t M : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) (hM : 0 < M)
    (hCne : C.Nonempty) (hCb : Bornology.IsBounded C)
    (_hgC : Set.MapsTo g C C)
    (hbounds : ∀ v ∈ C,
      (1 - t ≤ p v ∧ p v ≤ 1 + t) ∧
      (1 - t ≤ s v ∧ s v ≤ 1 + t) ∧
      (1 - t ≤ u v ∧ u v ≤ 1 + t) ∧
      (1 - t ≤ r v ∧ r v ≤ 1 + t))
    (hs : ∀ v ∈ C, s v = p v + M)
    (hr : ∀ v ∈ C, r v = u v + M)
    (hpair : ∀ v ∈ C, ∀ v' ∈ C,
      dist (g v) (g v') ≤
        (u v * p v / (r v * s v)) * dist v v' +
        2 * |u v - u v'| / r v +
        2 * u v * |p v - p v'| / (r v * s v))
    {H : Set X} (hHC : H ⊆ C) :
    chi (g '' H) ≤ (1 - M / (1 + t)) ^ 2 * chi H := by
  let γ : ℝ := (1 - M / (1 + t)) ^ 2
  have ha : 0 < 1 - t := sub_pos.mpr ht1
  have hU : 0 ≤ 1 + t := by linarith
  have hfactor := return_contraction_factor_mem_Ico ht0 ht1 hM hCne
    (fun v hv => (hbounds v hv).1.1)
    (fun v hv => (hbounds v hv).2.1.2) hs
  have hγ : 0 ≤ γ := hfactor.1
  have hγ1 : γ ≤ 1 := hfactor.2.le
  have hp : ∀ v ∈ C, p v ∈ Set.Icc 0 (1 + t) := by
    intro v hv
    exact ⟨ha.le.trans (hbounds v hv).1.1, (hbounds v hv).1.2⟩
  have hu : ∀ v ∈ C, u v ∈ Set.Icc 0 (1 + t) := by
    intro v hv
    exact ⟨ha.le.trans (hbounds v hv).2.2.1.1, (hbounds v hv).2.2.1.2⟩
  have hpair' : ∀ v ∈ C, ∀ v' ∈ C,
      dist (g v) (g v') ≤ γ * dist v v' +
        (2 / (1 - t)) * (|u v - u v'| + |p v - p v'|) := by
    intro v hv v' hv'
    exact return_pair_uniform_bound ha hM.le (hp v hv).1 (hu v hv).1
      (hbounds v hv).2.2.2.1 (hbounds v hv).2.1.1
      (hbounds v hv).2.2.2.2 (hbounds v hv).2.1.2
      (hr v hv) (hs v hv) dist_nonneg (abs_nonneg _) (abs_nonneg _)
      (hpair v hv v' hv')
  have happrox : ∀ ε : ℝ, 0 < ε → chi (g '' H) ≤ γ * chi H + ε := by
    intro ε hε
    have hε2 : 0 < ε / 2 := half_pos hε
    obtain ⟨δ, hδ0, hδ, hc⟩ := exists_cover_of_chi_lt (hCb.subset hHC)
      (show chi H < chi H + ε / 2 by linarith)
    let η : ℝ := ε * (1 - t) / 8
    have hη : 0 < η := div_pos (mul_pos hε ha) (by norm_num)
    have hc' := finiteDiameterCover_image_of_scalar_bins hHC hU ha hγ hp hu hpair' hc hη
    have hR : 0 ≤ γ * δ + 4 * η / (1 - t) :=
      add_nonneg (mul_nonneg hγ hδ0.le)
        (div_nonneg (mul_nonneg (by norm_num) hη.le) ha.le)
    have herror : 4 * η / (1 - t) = ε / 2 := by
      dsimp only [η]
      field_simp [ne_of_gt ha]
      ring
    calc
      chi (g '' H) ≤ γ * δ + 4 * η / (1 - t) := chi_le_of_cover hR hc'
      _ = γ * δ + ε / 2 := by rw [herror]
      _ ≤ γ * (chi H + ε / 2) + ε / 2 :=
        add_le_add_left (mul_le_mul_of_nonneg_left hδ.le hγ) _
      _ ≤ γ * chi H + ε := by
        have hh := mul_le_mul_of_nonneg_right hγ1 hε2.le
        nlinarith
  change chi (g '' H) ≤ γ * chi H
  by_contra hnot
  have hgap : 0 < chi (g '' H) - γ * chi H := sub_pos.mpr (lt_of_not_ge hnot)
  have hh := happrox ((chi (g '' H) - γ * chi H) / 2) (half_pos hgap)
  linarith

end Tingley

end

end OAI

-- Adapted from OAI.Analysis.SphereIsometry.ProbabilitySimplex

namespace OAI

/-!
# Finite probability simplices

The coordinates are nonnegative real numbers with sum one. The positive-coordinate
selection lemma is the boundary-compatible labelling rule used in Sperner's argument.
-/

open scoped BigOperators

namespace Tingley

def probabilitySimplexSet (ι : Type*) [Fintype ι] : Set (ι → ℝ) :=
  {weights | (∀ index, 0 ≤ weights index) ∧ ∑ index, weights index = 1}

theorem convex_probabilitySimplexSet (ι : Type*) [Fintype ι] :
    Convex ℝ (probabilitySimplexSet ι) := by
  intro left hleft right hright first second hfirst hsecond hsum
  refine ⟨fun index => add_nonneg (mul_nonneg hfirst (hleft.1 index))
    (mul_nonneg hsecond (hright.1 index)), ?_⟩
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
    ← Finset.mul_sum, hleft.2, hright.2, mul_one, hsum]

theorem single_mem_probabilitySimplexSet {ι : Type*} [Fintype ι] [DecidableEq ι]
    (index : ι) : Pi.single index 1 ∈ probabilitySimplexSet ι :=
  ⟨le_update_iff.2 ⟨zero_le_one, fun _ _ => le_rfl⟩, by simp⟩

theorem mem_Icc_of_mem_probabilitySimplexSet {ι : Type*} [Fintype ι]
    {weights : ι → ℝ} (hweights : weights ∈ probabilitySimplexSet ι) (index : ι) :
    weights index ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨hweights.1 index, hweights.2 ▸
    Finset.single_le_sum (fun other _ => hweights.1 other) (Finset.mem_univ index)⟩

abbrev ProbabilitySimplex (ι : Type*) [Fintype ι] := ↥(probabilitySimplexSet ι)

instance probabilitySimplex_compactSpace (ι : Type*) [Fintype ι] :
    CompactSpace (ProbabilitySimplex ι) := by
  apply isCompact_iff_compactSpace.mp
  apply IsCompact.of_isClosed_subset
    (isCompact_Icc : IsCompact (Set.Icc (0 : ι → ℝ) 1))
  · change IsClosed ({weights : ι → ℝ | ∀ index, 0 ≤ weights index} ∩
      {weights | ∑ index, weights index = 1})
    apply IsClosed.inter
    · rw [Set.ofPred_forall]
      exact isClosed_iInter fun index =>
        isClosed_le continuous_const (continuous_apply index)
    · exact isClosed_eq (by fun_prop) continuous_const
  · intro weights hweights
    exact ⟨fun index => (mem_Icc_of_mem_probabilitySimplexSet hweights index).1,
      fun index => (mem_Icc_of_mem_probabilitySimplexSet hweights index).2⟩

namespace ProbabilitySimplex

variable {ι : Type*} [Fintype ι]

theorem coordinate_nonneg (a : ProbabilitySimplex ι) (i : ι) : 0 ≤ a.val i :=
  a.property.1 i

theorem sum_coordinates (a : ProbabilitySimplex ι) : ∑ i, a.val i = 1 :=
  a.property.2

noncomputable def pointMass (i : ι) : ProbabilitySimplex ι := by
  classical
  exact ⟨Pi.single i 1, single_mem_probabilitySimplexSet i⟩

instance [Nonempty ι] : Nonempty (ProbabilitySimplex ι) :=
  ⟨pointMass (Classical.choice ‹Nonempty ι›)⟩

theorem exists_positive_coordinate (a : ProbabilitySimplex ι) :
    ∃ i, 0 < a.val i := by
  classical
  by_contra h
  have hz : a.val = 0 := by
    funext i
    exact le_antisymm (le_of_not_gt (fun hi => h ⟨i, hi⟩)) (a.coordinate_nonneg i)
  have hs := a.sum_coordinates
  simp [hz] at hs

end ProbabilitySimplex

theorem exists_positive_dominating_coordinate {ι : Type*} [Fintype ι]
    (a b : ProbabilitySimplex ι) :
    ∃ i, 0 < a.val i ∧ b.val i ≤ a.val i := by
  classical
  by_contra h
  have hstrict : ∀ i, 0 < a.val i → a.val i < b.val i := by
    intro i hi
    exact lt_of_not_ge (fun hle => h ⟨i, hi, hle⟩)
  have hweak : ∀ i, a.val i ≤ b.val i := by
    intro i
    by_cases hi : 0 < a.val i
    · exact (hstrict i hi).le
    · have hz : a.val i = 0 :=
        le_antisymm (le_of_not_gt hi) (a.coordinate_nonneg i)
      rw [hz]
      exact b.coordinate_nonneg i
  obtain ⟨i, hi⟩ := a.exists_positive_coordinate
  have hsum : (∑ j, a.val j) < ∑ j, b.val j :=
    Finset.sum_lt_sum (fun j _ => hweak j) ⟨i, Finset.mem_univ i, hstrict i hi⟩
  rw [a.sum_coordinates, b.sum_coordinates] at hsum
  exact (lt_irrefl (1 : ℝ)) hsum

end Tingley

end OAI

-- Adapted from OAI.Analysis.SphereIsometry.SimplexLimit

namespace OAI

/-!
# Extracting a fixed point from shrinking labelled simplex cells

The analytic limit step of the simplex fixed-point argument starts with
a concrete family of simplex points, one for each coordinate at every subdivision level.
The finite Sperner argument supplies this family, and the subdivision estimates supply its
shrinking diameter. No fixed-point principle is assumed here.
-/

open Filter
open scoped BigOperators Topology

namespace Tingley

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Relabelling the coordinates is a homeomorphism of probability simplexes. -/
def probabilitySimplexReindex (e : ι ≃ κ) : ProbabilitySimplex ι ≃ₜ ProbabilitySimplex κ where
  toFun x :=
    ⟨fun j => x.val (e.symm j),
      ⟨fun j => x.property.1 _, (e.symm.sum_comp x.val).trans x.property.2⟩⟩
  invFun y :=
    ⟨fun i => y.val (e i),
      ⟨fun i => y.property.1 _, (e.sum_comp y.val).trans y.property.2⟩⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    exact congrArg x.val (e.symm_apply_apply i)
  right_inv y := by
    apply Subtype.ext
    funext j
    exact congrArg y.val (e.apply_symm_apply j)
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_pi fun j =>
      (continuous_apply (e.symm j)).comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_pi fun i =>
      (continuous_apply (e i)).comp continuous_subtype_val

@[simp]
theorem probabilitySimplexReindex_apply_val (e : ι ≃ κ) (x : ProbabilitySimplex ι) (j : κ) :
    (probabilitySimplexReindex e x).val j = x.val (e.symm j) := rfl

@[simp]
theorem probabilitySimplexReindex_symm_apply_val (e : ι ≃ κ) (y : ProbabilitySimplex κ) (i : ι) :
    ((probabilitySimplexReindex e).symm y).val i = y.val (e i) := rfl

variable [Nonempty ι]

/-- Coordinate inequalities at points in shrinking cells produce an actual fixed point.

Only one sequence is passed to compactness. The mesh estimate forces all the coordinate-labelled
sequences along that same subsequence to converge to the same simplex point. -/
theorem probabilitySimplex_fixedPoint_of_shrinking_family
    (P : ProbabilitySimplex ι → ProbabilitySimplex ι) (hP : Continuous P)
    (a : ℕ → ι → ProbabilitySimplex ι) (δ : ℕ → ℝ)
    (hδ : Tendsto δ atTop (𝓝 0))
    (hmesh : ∀ k i j, dist (a k i) (a k j) ≤ δ k)
    (hcoordinate : ∀ k i, (P (a k i)).val i ≤ (a k i).val i) :
    ∃ x, P x = x := by
  classical
  let i₀ : ι := Classical.choice inferInstance
  obtain ⟨x, φ, hφ, hx⟩ := CompactSpace.tendsto_subseq (fun k => a k i₀)
  have hδφ : Tendsto (fun k => δ (φ k)) atTop (𝓝 0) :=
    hδ.comp hφ.tendsto_atTop
  have ha : ∀ i, Tendsto (fun k => a (φ k) i) atTop (𝓝 x) := by
    intro i
    apply hx.congr_dist
    exact squeeze_zero (fun _ => dist_nonneg)
      (fun k => hmesh (φ k) i₀ i) hδφ
  have hle : ∀ i, (P x).val i ≤ x.val i := by
    intro i
    have hc : Continuous (fun y : ProbabilitySimplex ι => y.val i) :=
      (continuous_apply i).comp continuous_subtype_val
    exact le_of_tendsto_of_tendsto'
      (((hc.comp hP).tendsto x).comp (ha i))
      ((hc.tendsto x).comp (ha i))
      (fun k => hcoordinate (φ k) i)
  have hsum : (∑ i, (x.val i - (P x).val i)) = 0 := by
    rw [Finset.sum_sub_distrib, x.property.2, (P x).property.2, sub_self]
  have hzero : ∀ i ∈ Finset.univ, x.val i - (P x).val i = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sub_nonneg.mpr (hle i))).mp hsum
  refine ⟨x, ?_⟩
  apply Subtype.ext
  funext i
  exact (sub_eq_zero.mp (hzero i (Finset.mem_univ i))).symm

end Tingley

end OAI

-- Adapted from OAI.Analysis.SphereIsometry.FiniteComplex

namespace OAI

/-!
# Finite complexes and their actual face-chain subdivision

The empty face is included. A subdivision vertex is always a nonempty old
face, and a subdivision face is an actual finite inclusion-chain.
-/

noncomputable section

namespace Tingley

universe u v

structure FiniteComplex (V : Type u) [Fintype V] [DecidableEq V] where
  faces : Finset (Finset V)
  empty_mem : ∅ ∈ faces
  down_closed : ∀ {s t}, s ∈ faces → t ⊆ s → t ∈ faces

namespace FiniteComplex

variable {V : Type u} [Fintype V] [DecidableEq V]

def full : FiniteComplex V where
  faces := Finset.univ
  empty_mem := Finset.mem_univ _
  down_closed := fun _ _ => Finset.mem_univ _

@[simp] theorem mem_full (s : Finset V) : s ∈ (full : FiniteComplex V).faces :=
  Finset.mem_univ _

abbrev FaceVertex (K : FiniteComplex V) :=
  {s : Finset V // s ∈ K.faces ∧ s.Nonempty}

instance (K : FiniteComplex V) : Fintype (FaceVertex K) := by
  classical
  unfold FaceVertex
  infer_instance

def chain (K : FiniteComplex V) (c : Finset (FaceVertex K)) : Prop :=
  ∀ a ∈ c, ∀ b ∈ c, a.val ⊆ b.val ∨ b.val ⊆ a.val

theorem chain_mono {K : FiniteComplex V} {c d : Finset (FaceVertex K)}
    (hc : K.chain c) (hd : d ⊆ c) : K.chain d :=
  fun a ha b hb => hc a (hd ha) b (hd hb)

def sd (K : FiniteComplex V) : FiniteComplex (FaceVertex K) := by
  classical
  exact
    { faces := Finset.univ.filter K.chain
      empty_mem := by simp [chain]
      down_closed := by
        intro s t hs hts
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, K.chain_mono (Finset.mem_filter.mp hs).2 hts⟩ }

@[simp] theorem mem_sd_iff {K : FiniteComplex V} {c : Finset (FaceVertex K)} :
    c ∈ K.sd.faces ↔ K.chain c := by
  classical
  simp [sd]

def topCells (K : FiniteComplex V) (m : ℕ) : Finset (Finset V) :=
  K.faces.filter (fun s => s.card = m + 1)

def codimFaces (K : FiniteComplex V) (m : ℕ) : Finset (Finset V) :=
  K.faces.filter (fun s => s.card = m)

def incidentTop (K : FiniteComplex V) (m : ℕ) (s : Finset V) : Finset (Finset V) :=
  (K.topCells m).filter (fun t => s ⊆ t)

@[simp] theorem mem_topCells {K : FiniteComplex V} {m : ℕ} {s : Finset V} :
    s ∈ K.topCells m ↔ s ∈ K.faces ∧ s.card = m + 1 :=
  Finset.mem_filter

@[simp] theorem mem_codimFaces {K : FiniteComplex V} {m : ℕ} {s : Finset V} :
    s ∈ K.codimFaces m ↔ s ∈ K.faces ∧ s.card = m :=
  Finset.mem_filter

@[simp] theorem mem_incidentTop {K : FiniteComplex V} {m : ℕ}
    {s t : Finset V} :
    t ∈ K.incidentTop m s ↔ t ∈ K.faces ∧ t.card = m + 1 ∧ s ⊆ t := by
  simp [incidentTop, and_assoc]

def CardBound (K : FiniteComplex V) (m : ℕ) : Prop :=
  ∀ s ∈ K.faces, s.card ≤ m + 1

variable {I : Type v} [DecidableEq I]

def faceCarrier (carrier : V → Finset I) (s : Finset V) : Finset I :=
  s.biUnion carrier

omit [Fintype V] [DecidableEq V] in
@[simp] theorem mem_faceCarrier {carrier : V → Finset I} {s : Finset V} {i : I} :
    i ∈ faceCarrier carrier s ↔ ∃ v ∈ s, i ∈ carrier v :=
  Finset.mem_biUnion

omit [Fintype V] [DecidableEq V] in
theorem faceCarrier_mono (carrier : V → Finset I) {s t : Finset V} (h : s ⊆ t) :
    faceCarrier carrier s ⊆ faceCarrier carrier t :=
  Finset.biUnion_subset_biUnion_of_subset_left _ h

omit [Fintype V] [DecidableEq V] in
@[simp] theorem faceCarrier_empty (carrier : V → Finset I) :
    faceCarrier carrier ∅ = ∅ := rfl

omit [Fintype V] [DecidableEq V] in
@[simp] theorem faceCarrier_singleton (carrier : V → Finset I) (v : V) :
    faceCarrier carrier {v} = carrier v := by
  simp [faceCarrier]

def sdCarrier (K : FiniteComplex V) (carrier : V → Finset I) :
    FaceVertex K → Finset I := fun s => faceCarrier carrier s.val

end FiniteComplex

end Tingley

end

end OAI

-- Adapted from OAI.Analysis.SphereIsometry.BarycentricFlags

namespace OAI

/-! # Ranks and carriers of finite face-chains -/

noncomputable section

namespace Tingley.FiniteComplex

universe u v
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {K : FiniteComplex V}

theorem chain_eq_of_card_eq {c : Finset (FaceVertex K)} (hc : K.chain c)
    {a b : FaceVertex K} (ha : a ∈ c) (hb : b ∈ c) (h : a.val.card = b.val.card) :
    a = b := by
  apply Subtype.ext
  rcases hc a ha b hb with hab | hba
  · exact Finset.eq_of_subset_of_card_le hab h.ge
  · exact (Finset.eq_of_subset_of_card_le hba h.le).symm

theorem chain_subset_of_card_le {c : Finset (FaceVertex K)} (hc : K.chain c)
    {a b : FaceVertex K} (ha : a ∈ c) (hb : b ∈ c) (h : a.val.card ≤ b.val.card) :
    a.val ⊆ b.val := by
  rcases hc a ha b hb with hab | hba
  · exact hab
  · intro x hx
    rw [Finset.eq_of_subset_of_card_le hba h]
    exact hx

def ranks (K : FiniteComplex V) (c : Finset (FaceVertex K)) : Finset ℕ :=
  c.image (fun a => a.val.card)

@[simp] theorem mem_ranks {c : Finset (FaceVertex K)} {r : ℕ} :
    r ∈ K.ranks c ↔ ∃ a ∈ c, a.val.card = r :=
  Finset.mem_image

theorem card_ranks {c : Finset (FaceVertex K)} (hc : K.chain c) :
    (K.ranks c).card = c.card := by
  apply Finset.card_image_of_injOn
  intro a ha b hb hab
  exact chain_eq_of_card_eq hc ha hb hab

theorem ranks_subset {m : ℕ} (hK : K.CardBound m) (c : Finset (FaceVertex K)) :
    K.ranks c ⊆ Finset.Icc 1 (m + 1) := by
  intro r hr
  obtain ⟨a, _, rfl⟩ := mem_ranks.mp hr
  exact Finset.mem_Icc.mpr
    ⟨Finset.card_pos.mpr a.property.2, hK a.val a.property.1⟩

theorem missing_rank {m : ℕ} (hK : K.CardBound m) {c : Finset (FaceVertex K)}
    (hc : c ∈ K.sd.codimFaces m) :
    ∃ r, 1 ≤ r ∧ r ≤ m + 1 ∧ K.ranks c = (Finset.Icc 1 (m + 1)).erase r := by
  obtain ⟨hchain, hcard⟩ := mem_codimFaces.mp hc
  have hsub := ranks_subset hK c
  have hd : ((Finset.Icc 1 (m + 1)) \ K.ranks c).card = 1 := by
    rw [Finset.card_sdiff_of_subset hsub, card_ranks (mem_sd_iff.mp hchain), hcard]
    simp
  obtain ⟨r, hr⟩ := Finset.card_eq_one.mp hd
  have hrmem : r ∈ (Finset.Icc 1 (m + 1)) \ K.ranks c := by
    rw [hr]
    exact Finset.mem_singleton_self _
  obtain ⟨hrI, hrnot⟩ := Finset.mem_sdiff.mp hrmem
  refine ⟨r, (Finset.mem_Icc.mp hrI).1, (Finset.mem_Icc.mp hrI).2, ?_⟩
  ext q
  constructor
  · intro hq
    exact Finset.mem_erase.mpr ⟨fun hqr => hrnot (hqr ▸ hq), hsub hq⟩
  · intro hq
    obtain ⟨hqr, hqI⟩ := Finset.mem_erase.mp hq
    by_contra hnot
    have : q ∈ (Finset.Icc 1 (m + 1)) \ K.ranks c :=
      Finset.mem_sdiff.mpr ⟨hqI, hnot⟩
    rw [hr] at this
    exact hqr (Finset.mem_singleton.mp this)

theorem exists_greatest {c : Finset (FaceVertex K)} (hc : K.chain c)
    (hne : c.Nonempty) : ∃ a ∈ c, ∀ b ∈ c, b.val ⊆ a.val := by
  obtain ⟨a, ha, hmax⟩ := c.exists_max_image (fun b => b.val.card) hne
  exact ⟨a, ha, fun b hb => chain_subset_of_card_le hc hb ha (hmax b hb)⟩

theorem card_le_greatest {c : Finset (FaceVertex K)} (hc : K.chain c)
    {a : FaceVertex K} (_ha : a ∈ c) (hmax : ∀ b ∈ c, b.val ⊆ a.val) :
    c.card ≤ a.val.card := by
  have hsub : K.ranks c ⊆ Finset.Icc 1 a.val.card := by
    intro r hr
    obtain ⟨b, hb, rfl⟩ := mem_ranks.mp hr
    exact Finset.mem_Icc.mpr
      ⟨Finset.card_pos.mpr b.property.2, Finset.card_le_card (hmax b hb)⟩
  have h := Finset.card_le_card hsub
  rw [card_ranks hc] at h
  simpa using h

variable {I : Type v} [DecidableEq I]

theorem faceCarrier_sd_eq_greatest {carrier : V → Finset I}
    {c : Finset (FaceVertex K)} {a : FaceVertex K} (ha : a ∈ c)
    (hmax : ∀ b ∈ c, b.val ⊆ a.val) :
    faceCarrier (K.sdCarrier carrier) c = faceCarrier carrier a.val := by
  apply Finset.Subset.antisymm
  · intro i hi
    obtain ⟨b, hb, hbi⟩ := mem_faceCarrier.mp hi
    exact faceCarrier_mono carrier (hmax b hb) hbi
  · intro i hi
    exact mem_faceCarrier.mpr ⟨a, ha, hi⟩

theorem sd_card_le_carrier {carrier : V → Finset I}
    (hK : ∀ s ∈ K.faces, s.card ≤ (faceCarrier carrier s).card)
    {c : Finset (FaceVertex K)} (hc : c ∈ K.sd.faces) :
    c.card ≤ (faceCarrier (K.sdCarrier carrier) c).card := by
  rcases c.eq_empty_or_nonempty with rfl | hne
  · simp
  · obtain ⟨a, ha, hmax⟩ := exists_greatest (mem_sd_iff.mp hc) hne
    rw [faceCarrier_sd_eq_greatest ha hmax]
    exact (card_le_greatest (mem_sd_iff.mp hc) ha hmax).trans (hK a.val a.property.1)

end Tingley.FiniteComplex

end

end OAI

-- Adapted from OAI.Analysis.SphereIsometry.SubdivisionData

namespace OAI

/-! # The concrete recursively iterated subdivision of a finite simplex -/

noncomputable section

namespace Tingley

structure CarrierComplex (I : Type) [DecidableEq I] where
  Vertex : Type
  [vertexFintype : Fintype Vertex]
  [vertexDecidableEq : DecidableEq Vertex]
  complex : FiniteComplex Vertex
  carrier : Vertex → Finset I

instance {I : Type} [DecidableEq I] (D : CarrierComplex I) : Fintype D.Vertex := D.vertexFintype
instance {I : Type} [DecidableEq I] (D : CarrierComplex I) : DecidableEq D.Vertex := D.vertexDecidableEq

namespace CarrierComplex

variable {I : Type} [DecidableEq I]

def sd (D : CarrierComplex I) : CarrierComplex I where
  Vertex := FiniteComplex.FaceVertex D.complex
  complex := D.complex.sd
  carrier := D.complex.sdCarrier D.carrier

def initial (I : Type) [Fintype I] [DecidableEq I] : CarrierComplex I where
  Vertex := I
  complex := FiniteComplex.full
  carrier := fun i => {i}

end CarrierComplex

def iterData (I : Type) [Fintype I] [DecidableEq I] : ℕ → CarrierComplex I
  | 0 => CarrierComplex.initial I
  | n + 1 => (iterData I n).sd

abbrev IterVertex (m k : ℕ) := (iterData (Fin (m + 1)) k).Vertex

def iterComplex (m k : ℕ) : Finset (Finset (IterVertex m k)) :=
  (iterData (Fin (m + 1)) k).complex.faces

def iterCarrier (m k : ℕ) : IterVertex m k → Finset (Fin (m + 1)) :=
  (iterData (Fin (m + 1)) k).carrier

def topCells (m k : ℕ) : Finset (Finset (IterVertex m k)) :=
  (iterData (Fin (m + 1)) k).complex.topCells m

def codimFaces (m k : ℕ) : Finset (Finset (IterVertex m k)) :=
  (iterData (Fin (m + 1)) k).complex.codimFaces m

def faceCarrier (m k : ℕ) (s : Finset (IterVertex m k)) : Finset (Fin (m + 1)) :=
  FiniteComplex.faceCarrier (iterCarrier m k) s

def incidentTop (m k : ℕ) (s : Finset (IterVertex m k)) :
    Finset (Finset (IterVertex m k)) :=
  (iterData (Fin (m + 1)) k).complex.incidentTop m s

@[simp] theorem mem_topCells {m k : ℕ} {s : Finset (IterVertex m k)} :
    s ∈ topCells m k ↔ s ∈ iterComplex m k ∧ s.card = m + 1 :=
  FiniteComplex.mem_topCells

@[simp] theorem mem_codimFaces {m k : ℕ} {s : Finset (IterVertex m k)} :
    s ∈ codimFaces m k ↔ s ∈ iterComplex m k ∧ s.card = m :=
  FiniteComplex.mem_codimFaces

@[simp] theorem mem_incidentTop {m k : ℕ} {s t : Finset (IterVertex m k)} :
    t ∈ incidentTop m k s ↔
      t ∈ iterComplex m k ∧ t.card = m + 1 ∧ s ⊆ t :=
  FiniteComplex.mem_incidentTop

theorem iterData_card_le_carrier (I : Type) [Fintype I] [DecidableEq I] (k : ℕ) :
    ∀ s ∈ (iterData I k).complex.faces,
      s.card ≤ (FiniteComplex.faceCarrier (iterData I k).carrier s).card := by
  induction k with
  | zero =>
      intro s hs
      simp [iterData, CarrierComplex.initial, FiniteComplex.faceCarrier]
      exact (congrArg (fun t : Finset I => t.card)
        (Finset.biUnion_singleton_eq_self (s := s))).ge
  | succ k ih =>
      intro s hs
      exact FiniteComplex.sd_card_le_carrier ih hs

theorem iter_card_le_carrier {m k : ℕ} {s : Finset (IterVertex m k)}
    (hs : s ∈ iterComplex m k) : s.card ≤ (faceCarrier m k s).card :=
  iterData_card_le_carrier (Fin (m + 1)) k s hs

theorem iter_card_le {m k : ℕ} {s : Finset (IterVertex m k)}
    (hs : s ∈ iterComplex m k) : s.card ≤ m + 1 := by
  have h := (iter_card_le_carrier hs).trans (Finset.card_le_univ (faceCarrier m k s))
  simpa using h

theorem top_faceCarrier {m k : ℕ} {s : Finset (IterVertex m k)}
    (hs : s ∈ topCells m k) : faceCarrier m k s = Finset.univ := by
  obtain ⟨hs, hcard⟩ := mem_topCells.mp hs
  apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
  simpa [hcard] using iter_card_le_carrier hs

end Tingley

end

end OAI

-- Adapted from OAI.Analysis.SphereIsometry.BarycentricBasic

namespace OAI

/-!
# Finite barycenters

The point attached to a nonempty face in barycentric subdivision is its
ordinary finite average. The definition also assigns zero to the empty set.
-/

noncomputable section

open scoped BigOperators

namespace Tingley

variable {V W E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

def finiteBarycenter (p : V → E) (S : Finset V) : E :=
  (S.card : ℝ)⁻¹ • ∑ v ∈ S, p v

theorem finiteBarycenter_eq_centerMass (p : V → E) (S : Finset V) :
    finiteBarycenter p S = S.centerMass (fun _ => (1 : ℝ)) p := by
  simp [finiteBarycenter, Finset.centerMass]

@[simp] theorem finiteBarycenter_empty (p : V → E) :
    finiteBarycenter p ∅ = 0 := by
  simp [finiteBarycenter]

@[simp] theorem finiteBarycenter_singleton (p : V → E) (v : V) :
    finiteBarycenter p {v} = p v := by
  simp [finiteBarycenter]

theorem finiteBarycenter_mem_convex {K : Set E} (hK : Convex ℝ K)
    {p : V → E} {S : Finset V} (hs : S.Nonempty)
    (hp : ∀ v ∈ S, p v ∈ K) : finiteBarycenter p S ∈ K := by
  rw [finiteBarycenter_eq_centerMass]
  apply hK.centerMass_mem
  · intro v hv
    exact zero_le_one
  · simpa using (Nat.cast_pos.mpr (Finset.card_pos.mpr hs) : 0 < (S.card : ℝ))
  · exact hp

theorem finiteBarycenter_mem_convexHull {p : V → E} {S T : Finset V}
    (hs : S.Nonempty) (hst : S ⊆ T) :
    finiteBarycenter p S ∈ convexHull ℝ (p '' (↑T : Set V)) := by
  apply finiteBarycenter_mem_convex (convex_convexHull ℝ _) hs
  intro v hv
  exact subset_convexHull ℝ _ ⟨v, hst hv, rfl⟩

theorem finiteBarycenter_apply {ι : Type*} [Fintype ι]
    (p : V → ι → ℝ) (S : Finset V) (i : ι) :
    finiteBarycenter p S i = (S.card : ℝ)⁻¹ * ∑ v ∈ S, p v i := by
  simp [finiteBarycenter, Finset.sum_apply]

end Tingley

end

end OAI

-- Adapted from OAI.Analysis.SphereIsometry.BarycentricSupport

namespace OAI

/-!
# Supports of finite barycenters

A nonempty average of simplex vectors is a simplex vector. Its strict-positive
coordinate support is exactly the union of the supports being averaged.
These statements concern the actual finite average and require no geometric
coverage assumption.
-/

noncomputable section

open scoped BigOperators Classical

namespace Tingley

variable {V ι : Type*} [Fintype ι]

/-- The coordinates at which a vector is strictly positive. -/
def positiveCarrier (x : ι → ℝ) : Finset ι :=
  Finset.univ.filter (fun i => 0 < x i)

@[simp] theorem mem_positiveCarrier {x : ι → ℝ} {i : ι} :
    i ∈ positiveCarrier x ↔ 0 < x i := by
  simp [positiveCarrier]

/-- A nonempty finite average stays in the standard simplex. -/
theorem finiteBarycenter_mem_stdSimplex (p : V → ι → ℝ) {S : Finset V}
    (hs : S.Nonempty) (hp : ∀ v ∈ S, p v ∈ probabilitySimplexSet ι) :
    finiteBarycenter p S ∈ probabilitySimplexSet ι := by
  exact finiteBarycenter_mem_convex (convex_probabilitySimplexSet ι) hs hp

/-- A coordinate of a nonempty nonnegative average is positive exactly when
one of the averaged coordinates is positive. -/
theorem finiteBarycenter_pos_iff (p : V → ι → ℝ) {S : Finset V}
    (hs : S.Nonempty) (hp : ∀ v ∈ S, ∀ i, 0 ≤ p v i) (i : ι) :
    0 < finiteBarycenter p S i ↔ ∃ v ∈ S, 0 < p v i := by
  have hcard : 0 < (S.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hs)
  have hinv : 0 < (S.card : ℝ)⁻¹ := inv_pos.mpr hcard
  rw [finiteBarycenter_apply]
  constructor
  · intro h
    have hsum : 0 < ∑ v ∈ S, p v i := pos_of_mul_pos_right h hinv.le
    by_contra hn
    have hzero : ∀ v ∈ S, p v i = 0 := by
      intro v hv
      apply le_antisymm _ (hp v hv i)
      exact le_of_not_gt (fun hpos => hn ⟨v, hv, hpos⟩)
    have heq : ∑ v ∈ S, p v i = 0 := Finset.sum_eq_zero hzero
    rw [heq] at hsum
    exact (lt_irrefl (0 : ℝ)) hsum
  · intro h
    exact mul_pos hinv (Finset.sum_pos' (fun v hv => hp v hv i) h)

/-- The support of a nonempty nonnegative average is the exact support union. -/
theorem positiveCarrier_finiteBarycenter (p : V → ι → ℝ) {S : Finset V}
    (hs : S.Nonempty) (hp : ∀ v ∈ S, ∀ i, 0 ≤ p v i) :
    positiveCarrier (finiteBarycenter p S) =
      S.biUnion (fun v => positiveCarrier (p v)) := by
  ext i
  simp only [mem_positiveCarrier, Finset.mem_biUnion]
  exact finiteBarycenter_pos_iff p hs hp i

end Tingley

end

end OAI

-- Adapted from OAI.Analysis.SphereIsometry.ConvexDiameter

namespace OAI

/-! # Diameter bounds for convex hulls

Convex hulls preserve diameter bounds.
-/

namespace Tingley

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

/-- Taking a convex hull preserves a pairwise diameter bound. -/
theorem DiameterLE.convexHull {A : Set E} {δ : ℝ} (h : DiameterLE A δ) :
    DiameterLE (convexHull ℝ A) δ := by
  intro x hx y hy
  obtain ⟨x', hx', y', hy', hxy⟩ := convexHull_exists_dist_ge2 hx hy
  exact hxy.trans (h x' hx' y' hy')

/-- A norm bound on a set also holds on its convex hull. -/
theorem norm_le_of_mem_convexHull {A : Set E} {R : ℝ}
    (hR : ∀ x ∈ A, ‖x‖ ≤ R) {x : E} (hx : x ∈ convexHull ℝ A) : ‖x‖ ≤ R := by
  have hsub : A ⊆ Metric.closedBall (0 : E) R := by
    intro y hy
    simpa only [Metric.mem_closedBall, dist_zero_right] using hR y hy
  have hxball := convexHull_min hsub (convex_closedBall (0 : E) R) hx
  simpa only [Metric.mem_closedBall, dist_zero_right] using hxball

end Tingley

end OAI

-- Adapted from OAI.Analysis.SphereIsometry.BarycentricMesh

namespace OAI

/-!
# The mesh estimate for barycentric subdivision

The larger face is split into the smaller face and its complement. Its
barycenter is the corresponding weighted average, giving the exact factor
`1 - S.card / T.card`. A dimension bound gives the uniform contraction.
-/

noncomputable section

open scoped BigOperators

namespace Tingley

variable {V E : Type*} [DecidableEq V] [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [DecidableEq V] in
theorem norm_finiteBarycenter_sub_le_of_subsets {p : V → E}
    {S R T : Finset V} {D : ℝ} (hs : S.Nonempty) (hr : R.Nonempty)
    (hst : S ⊆ T) (hrt : R ⊆ T)
    (hpair : ∀ u ∈ T, ∀ v ∈ T, ‖p u - p v‖ ≤ D) :
    ‖finiteBarycenter p S - finiteBarycenter p R‖ ≤ D := by
  have hdiam : DiameterLE (p '' (↑T : Set V)) D := by
    rintro x ⟨u, hu, rfl⟩ y ⟨v, hv, rfl⟩
    simpa only [dist_eq_norm] using hpair u hu v hv
  have h := hdiam.convexHull
    (finiteBarycenter p S) (finiteBarycenter_mem_convexHull hs hst)
    (finiteBarycenter p R) (finiteBarycenter_mem_convexHull hr hrt)
  simpa only [dist_eq_norm] using h

theorem finiteBarycenter_partition {p : V → E} {S T : Finset V}
    (hs : S.Nonempty) (hst : S ⊆ T) (hr : (T \ S).Nonempty) :
    finiteBarycenter p T =
      ((S.card : ℝ) / (T.card : ℝ)) • finiteBarycenter p S +
      (((T \ S).card : ℝ) / (T.card : ℝ)) • finiteBarycenter p (T \ S) := by
  classical
  have hs0 : (S.card : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Finset.card_pos.mpr hs))
  have hr0 : ((T \ S).card : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Finset.card_pos.mpr hr))
  have ht0 : (T.card : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Finset.card_pos.mpr (hs.mono hst)))
  have hS : ((S.card : ℝ) / (T.card : ℝ)) • finiteBarycenter p S =
      (T.card : ℝ)⁻¹ • ∑ v ∈ S, p v := by
    rw [finiteBarycenter, smul_smul]
    congr 1
    field_simp [hs0, ht0]
  have hR : (((T \ S).card : ℝ) / (T.card : ℝ)) •
      finiteBarycenter p (T \ S) =
      (T.card : ℝ)⁻¹ • ∑ v ∈ T \ S, p v := by
    rw [finiteBarycenter, smul_smul]
    congr 1
    field_simp [hr0, ht0]
  rw [hS, hR, ← smul_add]
  unfold finiteBarycenter
  congr 1
  simpa only [add_comm] using (Finset.sum_sdiff (f := p) hst).symm

theorem norm_finiteBarycenter_sub_le_card {p : V → E}
    {S T : Finset V} {D : ℝ} (hs : S.Nonempty) (hst : S ⊆ T)
    (hpair : ∀ u ∈ T, ∀ v ∈ T, ‖p u - p v‖ ≤ D) :
    ‖finiteBarycenter p S - finiteBarycenter p T‖ ≤
      (1 - (S.card : ℝ) / (T.card : ℝ)) * D := by
  classical
  have ht : T.Nonempty := hs.mono hst
  have htpos : 0 < (T.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr ht)
  by_cases heq : S = T
  · subst S
    simp [ne_of_gt htpos]
  have hr : (T \ S).Nonempty := Finset.sdiff_nonempty.mpr (by
    intro hts
    exact heq (Finset.Subset.antisymm hst hts))
  have hcard : ((T \ S).card : ℝ) + (S.card : ℝ) = (T.card : ℝ) := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hst
  have hfrac : ((T \ S).card : ℝ) / (T.card : ℝ) =
      1 - (S.card : ℝ) / (T.card : ℝ) := by
    apply (div_eq_iff (ne_of_gt htpos)).2
    rw [sub_mul, one_mul, div_mul_cancel₀ _ (ne_of_gt htpos)]
    linarith
  have hnonneg : 0 ≤ ((T \ S).card : ℝ) / (T.card : ℝ) :=
    div_nonneg (Nat.cast_nonneg _) htpos.le
  have hid : finiteBarycenter p S - finiteBarycenter p T =
      (((T \ S).card : ℝ) / (T.card : ℝ)) •
        (finiteBarycenter p S - finiteBarycenter p (T \ S)) := by
    calc
      finiteBarycenter p S - finiteBarycenter p T =
          (1 - (S.card : ℝ) / (T.card : ℝ)) • finiteBarycenter p S -
            (((T \ S).card : ℝ) / (T.card : ℝ)) •
              finiteBarycenter p (T \ S) := by
        rw [finiteBarycenter_partition hs hst hr, sub_smul, one_smul]
        abel
      _ = _ := by rw [← hfrac, smul_sub]
  rw [hid, norm_smul, Real.norm_eq_abs, abs_of_nonneg hnonneg]
  calc
    ((T \ S).card : ℝ) / (T.card : ℝ) *
        ‖finiteBarycenter p S - finiteBarycenter p (T \ S)‖ ≤
        ((T \ S).card : ℝ) / (T.card : ℝ) * D :=
      mul_le_mul_of_nonneg_left
        (norm_finiteBarycenter_sub_le_of_subsets hs hr hst Finset.sdiff_subset hpair)
        hnonneg
    _ = _ := by rw [hfrac]

theorem norm_finiteBarycenter_sub_le_mesh {p : V → E}
    {S T : Finset V} {D : ℝ} (m : ℕ) (hD : 0 ≤ D)
    (hs : S.Nonempty) (hst : S ⊆ T) (hcard : T.card ≤ m + 1)
    (hpair : ∀ u ∈ T, ∀ v ∈ T, ‖p u - p v‖ ≤ D) :
    ‖finiteBarycenter p S - finiteBarycenter p T‖ ≤
      ((m : ℝ) / (m + 1 : ℝ)) * D := by
  have ht : T.Nonempty := hs.mono hst
  have htpos : 0 < (T.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr ht)
  have hmpos : 0 < (m + 1 : ℝ) := by positivity
  have hsone : (1 : ℝ) ≤ (S.card : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr (Finset.card_pos.mpr hs))
  have htcard : (T.card : ℝ) ≤ (m + 1 : ℝ) := by exact_mod_cast hcard
  have hlow : 1 / (m + 1 : ℝ) ≤ (S.card : ℝ) / (T.card : ℝ) := by
    calc
      1 / (m + 1 : ℝ) ≤ 1 / (T.card : ℝ) :=
        one_div_le_one_div_of_le htpos htcard
      _ ≤ (S.card : ℝ) / (T.card : ℝ) :=
        (div_le_div_iff_of_pos_right htpos).2 hsone
  have hfactor : 1 - (S.card : ℝ) / (T.card : ℝ) ≤
      (m : ℝ) / (m + 1 : ℝ) := by
    have heq : (m : ℝ) / (m + 1 : ℝ) = 1 - 1 / (m + 1 : ℝ) := by
      apply (div_eq_iff (ne_of_gt hmpos)).2
      rw [sub_mul, one_mul, div_mul_cancel₀ _ (ne_of_gt hmpos)]
      ring
    rw [heq]
    linarith
  exact (norm_finiteBarycenter_sub_le_card hs hst hpair).trans
    (mul_le_mul_of_nonneg_right hfactor hD)

end Tingley

end

end OAI

-- Adapted from OAI.Analysis.SphereIsometry.BarycentricPoints

/-!
# Geometric vertices of barycentric subdivision

Finite averages give simplex membership, exact coordinate support,
naturality, and shrinking mesh.
-/

-- Adapted from OAI.Analysis.SphereIsometry.IteratedPoints

namespace OAI

/-!
# Actual geometric points of iterated subdivision

Initial vertices are coordinate unit vectors. Every later vertex is the finite
barycenter of the nonempty old face that it represents. Simplex membership,
exact carriers, and the geometric mesh bound follow from this recursive formula.
-/

noncomputable section

namespace Tingley

/-- The actual geometric realization of every recursively constructed vertex. -/
def iterDataPoint (I : Type) [Fintype I] [DecidableEq I] :
    (k : ℕ) → (iterData I k).Vertex → I → ℝ
  | 0, v => Pi.single v 1
  | k + 1, v => finiteBarycenter (iterDataPoint I k) v.val

@[simp] theorem iterDataPoint_zero (I : Type) [Fintype I] [DecidableEq I] (v : I) :
    iterDataPoint I 0 v = Pi.single v 1 := rfl

@[simp] theorem iterDataPoint_succ (I : Type) [Fintype I] [DecidableEq I]
    (k : ℕ) (v : (iterData I (k + 1)).Vertex) :
    iterDataPoint I (k + 1) v = finiteBarycenter (iterDataPoint I k) v.val := rfl

/-- The recursion produces simplex vectors at every level. -/
theorem iterDataPoint_mem_stdSimplex (I : Type) [Fintype I] [DecidableEq I] :
    ∀ (k : ℕ) (v : (iterData I k).Vertex),
      iterDataPoint I k v ∈ probabilitySimplexSet I := by
  intro k
  induction k with
  | zero =>
      intro v
      exact single_mem_probabilitySimplexSet v
  | succ k ih =>
      intro v
      exact finiteBarycenter_mem_stdSimplex (iterDataPoint I k) v.property.2
        (fun u _ => ih u)

/-- The recursively defined combinatorial carrier is exactly the set of
strict-positive coordinates of the actual recursive point. -/
theorem positiveCarrier_iterDataPoint (I : Type) [Fintype I] [DecidableEq I] :
    ∀ (k : ℕ) (v : (iterData I k).Vertex),
      positiveCarrier (iterDataPoint I k v) = (iterData I k).carrier v := by
  intro k
  induction k with
  | zero =>
      intro v
      change positiveCarrier (Pi.single v (1 : ℝ)) = {v}
      ext i
      by_cases hi : v = i
      · subst i
        simp [positiveCarrier]
      · simp [positiveCarrier, Pi.single_apply, Ne.symm hi]
  | succ k ih =>
      intro v
      change positiveCarrier (finiteBarycenter (iterDataPoint I k) v.val) =
        v.val.biUnion (fun u => (iterData I k).carrier u)
      rw [positiveCarrier_finiteBarycenter (iterDataPoint I k) v.property.2
        (fun u _ i => (iterDataPoint_mem_stdSimplex I k u).1 i)]
      ext i
      simp only [Finset.mem_biUnion, ih]

/-- The coordinate form used by the simplex fixed-point argument. -/
abbrev iterPoint (m k : ℕ) : IterVertex m k → Fin (m + 1) → ℝ :=
  iterDataPoint (Fin (m + 1)) k

@[simp] theorem iterPoint_zero (m : ℕ) (v : Fin (m + 1)) :
    iterPoint m 0 v = Pi.single v 1 := rfl

@[simp] theorem iterPoint_succ (m k : ℕ) (v : IterVertex m (k + 1)) :
    iterPoint m (k + 1) v = finiteBarycenter (iterPoint m k) v.val := rfl

theorem iterPoint_mem_stdSimplex (m k : ℕ) (v : IterVertex m k) :
    iterPoint m k v ∈ probabilitySimplexSet (Fin (m + 1)) :=
  iterDataPoint_mem_stdSimplex (Fin (m + 1)) k v

theorem positiveCarrier_iterPoint (m k : ℕ) (v : IterVertex m k) :
    positiveCarrier (iterPoint m k v) = iterCarrier m k v :=
  positiveCarrier_iterDataPoint (Fin (m + 1)) k v

/-- Exact boundary compatibility of the coordinate labelling rule. -/
theorem iterPoint_pos_iff (m k : ℕ) (v : IterVertex m k) (i : Fin (m + 1)) :
    0 < iterPoint m k v i ↔ i ∈ iterCarrier m k v := by
  rw [← mem_positiveCarrier, positiveCarrier_iterPoint]

/-- Any two probability vectors have distance at most one in the ambient sup norm. -/
theorem norm_sub_le_one_of_mem_stdSimplex {I : Type*} [Fintype I]
    {x y : I → ℝ} (hx : x ∈ probabilitySimplexSet I) (hy : y ∈ probabilitySimplexSet I) :
    ‖x - y‖ ≤ 1 := by
  rw [← dist_eq_norm]
  apply (dist_pi_le_iff zero_le_one).mpr
  intro i
  have hxi := mem_Icc_of_mem_probabilitySimplexSet hx i
  have hyi := mem_Icc_of_mem_probabilitySimplexSet hy i
  rw [Real.dist_eq]
  apply abs_le.mpr
  constructor <;> linarith [hxi.1, hxi.2, hyi.1, hyi.2]

/-- The mesh of each actual level-k face is bounded by the kth power of the
barycentric contraction factor. No face coverage assertion is assumed. -/
theorem iterPoint_mesh (m : ℕ) :
    ∀ (k : ℕ) (s : Finset (IterVertex m k)), s ∈ iterComplex m k →
      ∀ u ∈ s, ∀ v ∈ s,
        ‖iterPoint m k u - iterPoint m k v‖ ≤
          ((m : ℝ) / (m + 1 : ℝ)) ^ k := by
  intro k
  induction k with
  | zero =>
      intro s _ u _ v _
      simpa only [pow_zero] using norm_sub_le_one_of_mem_stdSimplex
        (iterPoint_mem_stdSimplex m 0 u) (iterPoint_mem_stdSimplex m 0 v)
  | succ k ih =>
      intro s hs u hu v hv
      have hchain : (iterData (Fin (m + 1)) k).complex.chain s :=
        FiniteComplex.mem_sd_iff.mp hs
      have hD : 0 ≤ ((m : ℝ) / (m + 1 : ℝ)) ^ k :=
        pow_nonneg (div_nonneg (Nat.cast_nonneg m)
          (add_nonneg (Nat.cast_nonneg m) zero_le_one)) k
      rcases hchain u hu v hv with huv | hvu
      · have h := norm_finiteBarycenter_sub_le_mesh (p := iterPoint m k) m hD
          u.property.2 huv (iter_card_le (m := m) (k := k) v.property.1)
          (ih v.val v.property.1)
        simpa only [iterPoint_succ, pow_succ'] using h
      · have h := norm_finiteBarycenter_sub_le_mesh (p := iterPoint m k) m hD
          v.property.2 hvu (iter_card_le (m := m) (k := k) u.property.1)
          (ih u.val u.property.1)
        calc
          ‖iterPoint m (k + 1) u - iterPoint m (k + 1) v‖ =
              ‖iterPoint m (k + 1) v - iterPoint m (k + 1) u‖ := norm_sub_rev _ _
          _ ≤ ((m : ℝ) / (m + 1 : ℝ)) ^ (k + 1) := by
            simpa only [iterPoint_succ, pow_succ'] using h

end Tingley

end

end OAI

-- Adapted from OAI.Analysis.SphereIsometry.SpernerFacet

namespace OAI

/-!
# The local facet count in geometric Sperner's lemma

A simplex with `m + 1` vertices has an odd number of facets labelled by all
labels except the last precisely when the simplex is fully labelled. The
proof below identifies the good facets explicitly: one in the fully labelled
case, and two whenever a good facet exists but the simplex is not full.
-/

namespace Tingley

/-- The labels on the distinguished boundary face. -/
def spernerSmallLabels (m : ℕ) : Finset (Fin (m + 1)) :=
  Finset.univ.erase (Fin.last m)

@[simp] theorem mem_spernerSmallLabels {m : ℕ} {i : Fin (m + 1)} :
    i ∈ spernerSmallLabels m ↔ i ≠ Fin.last m := by
  simp [spernerSmallLabels]

@[simp] theorem card_spernerSmallLabels (m : ℕ) :
    (spernerSmallLabels m).card = m := by
  simp [spernerSmallLabels]

variable {V : Type*} [DecidableEq V] {m : ℕ}

/-- The codimension-one subsets carrying every label except the last. -/
def spernerGoodFacets (m : ℕ) (label : V → Fin (m + 1)) (σ : Finset V) :
    Finset (Finset V) :=
  σ.powerset.filter fun τ => τ.card = m ∧ τ.image label = spernerSmallLabels m

omit [DecidableEq V] in
@[simp] theorem mem_spernerGoodFacets {label : V → Fin (m + 1)}
    {σ τ : Finset V} :
    τ ∈ spernerGoodFacets m label σ ↔
      τ ⊆ σ ∧ τ.card = m ∧ τ.image label = spernerSmallLabels m := by
  simp [spernerGoodFacets]

omit [DecidableEq V] in
/-- A good facet has one vertex of each of its labels. -/
theorem spernerGoodFacet_injOn {label : V → Fin (m + 1)}
    {σ τ : Finset V} (hτ : τ ∈ spernerGoodFacets m label σ) :
    Set.InjOn label (↑τ : Set V) := by
  obtain ⟨_, hc, hi⟩ := mem_spernerGoodFacets.mp hτ
  apply Finset.card_image_iff.mp
  rw [hi, card_spernerSmallLabels, hc]

/-- A fully labelled simplex has exactly one distinguished good facet. -/
theorem spernerGoodFacets_card_of_full (label : V → Fin (m + 1))
    (σ : Finset V) (hσ : σ.card = m + 1)
    (hfull : σ.image label = Finset.univ) :
    (spernerGoodFacets m label σ).card = 1 := by
  classical
  have hinj : Set.InjOn label (↑σ : Set V) := by
    apply Finset.card_image_iff.mp
    simp [hfull, hσ]
  have hlast : Fin.last m ∈ σ.image label := by
    rw [hfull]
    exact Finset.mem_univ _
  obtain ⟨w, hwσ, hwlabel⟩ := Finset.mem_image.mp hlast
  have hcard : (σ.erase w).card = m := by
    simpa [hσ] using (Finset.card_erase_of_mem hwσ)
  have himage : (σ.erase w).image label = spernerSmallLabels m := by
    ext i
    constructor
    · intro hi
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hi
      apply mem_spernerSmallLabels.mpr
      intro hvl
      exact (Finset.mem_erase.mp hv).1
        (hinj (Finset.mem_erase.mp hv).2 hwσ (hvl.trans hwlabel.symm))
    · intro hi
      have hine : i ≠ Fin.last m := mem_spernerSmallLabels.mp hi
      have hiσ : i ∈ σ.image label := by simp [hfull]
      obtain ⟨v, hvσ, hvi⟩ := Finset.mem_image.mp hiσ
      refine Finset.mem_image.mpr ⟨v, Finset.mem_erase.mpr ⟨?_, hvσ⟩, hvi⟩
      intro hvw
      apply hine
      calc
        i = label v := hvi.symm
        _ = label w := congrArg label hvw
        _ = Fin.last m := hwlabel
  have hgood : σ.erase w ∈ spernerGoodFacets m label σ :=
    mem_spernerGoodFacets.mpr ⟨Finset.erase_subset _ _, hcard, himage⟩
  have hfamily : spernerGoodFacets m label σ = {σ.erase w} := by
    ext τ
    constructor
    · intro hτ
      obtain ⟨hτσ, hτcard, hτimage⟩ := mem_spernerGoodFacets.mp hτ
      have hwnot : w ∉ τ := by
        intro hwτ
        have hwmem : label w ∈ spernerSmallLabels m := by
          rw [← hτimage]
          exact Finset.mem_image.mpr ⟨w, hwτ, rfl⟩
        exact (mem_spernerSmallLabels.mp hwmem) hwlabel
      have hsub : τ ⊆ σ.erase w := Finset.subset_erase.mpr ⟨hτσ, hwnot⟩
      apply Finset.mem_singleton.mpr
      exact Finset.eq_of_subset_of_card_le hsub (by rw [hcard, hτcard])
    · intro hτ
      have hτeq : τ = σ.erase w := Finset.mem_singleton.mp hτ
      simpa [hτeq] using hgood
  rw [hfamily, Finset.card_singleton]

/-- In a non-full simplex, one good facet determines exactly two good facets.
The second is obtained by exchanging the extra vertex with its equal-label
partner in the first facet. -/
theorem spernerGoodFacets_card_of_nonempty_not_full
    (label : V → Fin (m + 1)) (σ : Finset V) (hσ : σ.card = m + 1)
    (hfull : σ.image label ≠ Finset.univ)
    (hne : (spernerGoodFacets m label σ).Nonempty) :
    (spernerGoodFacets m label σ).card = 2 := by
  classical
  obtain ⟨τ, hτ⟩ := hne
  obtain ⟨hτσ, hτcard, hτimage⟩ := mem_spernerGoodFacets.mp hτ
  obtain ⟨w, hwτ, hwσeq⟩ := Finset.exists_eq_insert_iff.mpr
    (show τ ⊆ σ ∧ τ.card + 1 = σ.card from ⟨hτσ, by rw [hτcard, hσ]⟩)
  have hwσ : w ∈ σ := hwσeq ▸ Finset.mem_insert_self w τ
  have hwlabel : label w ≠ Fin.last m := by
    intro hwlast
    apply hfull
    rw [← hwσeq, Finset.image_insert, hwlast, hτimage, spernerSmallLabels]
    exact Finset.insert_erase (Finset.mem_univ _)
  have hwimage : label w ∈ τ.image label := by
    rw [hτimage]
    exact mem_spernerSmallLabels.mpr hwlabel
  obtain ⟨u, huτ, hulabel⟩ := Finset.mem_image.mp hwimage
  have huw : u ≠ w := by
    intro huw
    exact hwτ (huw ▸ huτ)
  let υ : Finset V := insert w (τ.erase u)
  have hwυ : w ∈ υ := Finset.mem_insert_self _ _
  have hυcard : υ.card = m := by
    have hw : w ∉ τ.erase u := fun h => hwτ (Finset.erase_subset _ _ h)
    dsimp only [υ]
    rw [Finset.card_insert_of_notMem hw, Finset.card_erase_add_one huτ, hτcard]
  have hυimage : υ.image label = spernerSmallLabels m := by
    calc
      υ.image label = insert (label w) ((τ.erase u).image label) :=
        Finset.image_insert _ _ _
      _ = insert (label u) ((τ.erase u).image label) := by rw [hulabel]
      _ = (insert u (τ.erase u)).image label := (Finset.image_insert _ _ _).symm
      _ = τ.image label := by rw [Finset.insert_erase huτ]
      _ = spernerSmallLabels m := hτimage
  have hυσ : υ ⊆ σ := by
    intro v hv
    rcases Finset.mem_insert.mp hv with hv | hv
    · exact hv.symm ▸ hwσ
    · exact hτσ (Finset.erase_subset _ _ hv)
  have hυgood : υ ∈ spernerGoodFacets m label σ :=
    mem_spernerGoodFacets.mpr ⟨hυσ, hυcard, hυimage⟩
  have hτυ : τ ≠ υ := by
    intro heq
    exact hwτ (heq.symm ▸ hwυ)
  have hfamily : spernerGoodFacets m label σ = {τ, υ} := by
    ext η
    constructor
    · intro hη
      obtain ⟨hησ, hηcard, _⟩ := mem_spernerGoodFacets.mp hη
      have hηinsert : η ⊆ insert w τ := by simpa only [hwσeq] using hησ
      by_cases hwη : w ∈ η
      · have huη : u ∉ η := by
          intro huη
          exact huw ((spernerGoodFacet_injOn hη) huη hwη hulabel)
        have hηυ : η ⊆ υ := by
          intro v hvη
          rcases Finset.mem_insert.mp (hηinsert hvη) with hvw | hvτ
          · exact Finset.mem_insert.mpr (Or.inl hvw)
          · apply Finset.mem_insert.mpr
            right
            apply Finset.mem_erase.mpr
            refine ⟨?_, hvτ⟩
            intro hvu
            exact huη (hvu ▸ hvη)
        have hηeq : η = υ := Finset.eq_of_subset_of_card_le hηυ
          (by rw [hυcard, hηcard])
        simp only [Finset.mem_insert, Finset.mem_singleton]
        exact Or.inr hηeq
      · have hητ : η ⊆ τ := by
          intro v hvη
          rcases Finset.mem_insert.mp (hηinsert hvη) with hvw | hvτ
          · exact False.elim (hwη (hvw ▸ hvη))
          · exact hvτ
        have hηeq : η = τ := Finset.eq_of_subset_of_card_le hητ
          (by rw [hτcard, hηcard])
        simp only [Finset.mem_insert, Finset.mem_singleton]
        exact Or.inl hηeq
    · intro hη
      rcases Finset.mem_insert.mp hη with hη | hη
      · simpa [hη] using hτ
      · have hηeq : η = υ := Finset.mem_singleton.mp hη
        simpa [hηeq] using hυgood
  rw [hfamily]
  simp [hτυ]

/-- The local mod-two incidence identity, valid also in dimension zero. -/
theorem spernerGoodFacets_card_mod_two (label : V → Fin (m + 1))
    (σ : Finset V) (hσ : σ.card = m + 1) :
    ((spernerGoodFacets m label σ).card : ZMod 2) =
      if σ.image label = Finset.univ then 1 else 0 := by
  classical
  by_cases hfull : σ.image label = Finset.univ
  · simpa only [if_pos hfull, spernerGoodFacets_card_of_full label σ hσ hfull]
      using (Nat.cast_one : ((1 : ℕ) : ZMod 2) = 1)
  · rw [if_neg hfull]
    by_cases hne : (spernerGoodFacets m label σ).Nonempty
    · simpa only [spernerGoodFacets_card_of_nonempty_not_full label σ hσ hfull hne]
        using (ZMod.natCast_self 2)
    · have hempty : spernerGoodFacets m label σ = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hne
      simp [hempty]

end Tingley

end OAI

-- Adapted from OAI.Analysis.SphereIsometry.SpernerIncidence

namespace OAI

/-!
# Counting labelled incidences in a finite complex

The two orders of summation count the same actual top-cell/facet pairs. Local
facet parity leaves the fully labelled top cells on one side. Degree two
facets cancel on the other side, leaving only the degree one boundary facets.
-/

open scoped BigOperators

namespace Tingley.FiniteComplex

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem goodFacets_eq_codim_filter (K : FiniteComplex V) (m : ℕ)
    (label : V → Fin (m + 1)) {σ : Finset V} (hσ : σ ∈ K.topCells m) :
    (K.codimFaces m).filter
        (fun τ => τ ⊆ σ ∧ τ.image label = spernerSmallLabels m) =
      spernerGoodFacets m label σ := by
  classical
  ext τ
  rw [Finset.mem_filter, mem_spernerGoodFacets]
  constructor
  · rintro ⟨hτ, hsub, hlabel⟩
    exact ⟨hsub, (mem_codimFaces.mp hτ).2, hlabel⟩
  · rintro ⟨hsub, hcard, hlabel⟩
    exact ⟨mem_codimFaces.mpr
      ⟨K.down_closed (mem_topCells.mp hσ).1 hsub, hcard⟩, hsub, hlabel⟩

/-- Finite incidence parity, before the boundary restriction is identified with
the lower-dimensional simplex. All hypotheses concern finite face incidence. -/
theorem sperner_count_mod_two (K : FiniteComplex V) (m : ℕ)
    (label : V → Fin (m + 1)) (boundary : Finset V → Prop)
    [DecidablePred boundary]
    (hdegree : ∀ τ ∈ K.codimFaces m,
      (K.incidentTop m τ).card = if boundary τ then 1 else 2) :
    (((K.topCells m).filter (fun σ => σ.image label = Finset.univ)).card : ZMod 2) =
      (((K.codimFaces m).filter
        (fun τ => τ.image label = spernerSmallLabels m ∧ boundary τ)).card : ZMod 2) := by
  classical
  have hrow : ∀ σ ∈ K.topCells m,
      (∑ τ ∈ K.codimFaces m,
        if τ ⊆ σ ∧ τ.image label = spernerSmallLabels m then (1 : ZMod 2) else 0) =
      if σ.image label = Finset.univ then 1 else 0 := by
    intro σ hσ
    rw [Finset.sum_boole, goodFacets_eq_codim_filter K m label hσ]
    exact spernerGoodFacets_card_mod_two label σ (mem_topCells.mp hσ).2
  have hcolumn : ∀ τ ∈ K.codimFaces m,
      (∑ σ ∈ K.topCells m,
        if τ ⊆ σ ∧ τ.image label = spernerSmallLabels m then (1 : ZMod 2) else 0) =
      if τ.image label = spernerSmallLabels m ∧ boundary τ then 1 else 0 := by
    intro τ hτ
    by_cases hg : τ.image label = spernerSmallLabels m
    · simp only [hg, and_true, true_and]
      rw [Finset.sum_boole]
      change ((K.incidentTop m τ).card : ZMod 2) = if boundary τ then 1 else 0
      rw [hdegree τ hτ]
      by_cases hb : boundary τ
      · simp [hb]
      · simp only [hb, ite_false]
        exact ZMod.natCast_self 2
    · simp [hg]
  calc
    (((K.topCells m).filter (fun σ => σ.image label = Finset.univ)).card : ZMod 2) =
        ∑ σ ∈ K.topCells m,
          if σ.image label = Finset.univ then (1 : ZMod 2) else 0 :=
      Finset.natCast_card_filter _ _
    _ = ∑ σ ∈ K.topCells m, ∑ τ ∈ K.codimFaces m,
          if τ ⊆ σ ∧ τ.image label = spernerSmallLabels m then (1 : ZMod 2) else 0 :=
      Finset.sum_congr rfl (fun σ hσ => (hrow σ hσ).symm)
    _ = ∑ τ ∈ K.codimFaces m, ∑ σ ∈ K.topCells m,
          if τ ⊆ σ ∧ τ.image label = spernerSmallLabels m then (1 : ZMod 2) else 0 :=
      Finset.sum_comm
    _ = ∑ τ ∈ K.codimFaces m,
          if τ.image label = spernerSmallLabels m ∧ boundary τ then (1 : ZMod 2) else 0 :=
      Finset.sum_congr rfl hcolumn
    _ = (((K.codimFaces m).filter
          (fun τ => τ.image label = spernerSmallLabels m ∧ boundary τ)).card : ZMod 2) :=
      Finset.sum_boole _ _

/-- An odd number of good boundary facets gives an odd number of fully labelled cells. -/
theorem sperner_odd_of_boundary_odd (K : FiniteComplex V) (m : ℕ)
    (label : V → Fin (m + 1)) (boundary : Finset V → Prop)
    [DecidablePred boundary]
    (hdegree : ∀ τ ∈ K.codimFaces m,
      (K.incidentTop m τ).card = if boundary τ then 1 else 2)
    (hboundary : Odd (((K.codimFaces m).filter
      (fun τ => τ.image label = spernerSmallLabels m ∧ boundary τ)).card)) :
    Odd (((K.topCells m).filter (fun σ => σ.image label = Finset.univ)).card) := by
  apply ZMod.natCast_eq_one_iff_odd.mp
  rw [sperner_count_mod_two K m label boundary hdegree]
  exact ZMod.natCast_eq_one_iff_odd.mpr hboundary

end Tingley.FiniteComplex

end OAI

-- Adapted from OAI.Analysis.SphereIsometry.SpernerBoundary

namespace OAI

/-!
# Boundary labels and restriction of the finite Sperner count

Admissible labels lie in the union of the vertex carriers. A good boundary
facet therefore has exactly the carrier omitting the last coordinate. Mapping
lower-dimensional faces through a vertex embedding preserves the label count
after the coordinate embedding `Fin.castSucc`.
-/

namespace Tingley

variable {V W I : Type*} [DecidableEq V] [DecidableEq W] [DecidableEq I]

omit [DecidableEq V] in
/-- Vertexwise carrier membership implies membership in the face carrier. -/
theorem sperner_label_image_subset_carrier (label : V → I)
    (carrier : V → Finset I) (σ : Finset V)
    (hlabel : ∀ v ∈ σ, label v ∈ carrier v) :
    σ.image label ⊆ σ.biUnion carrier := by
  intro i hi
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hi
  exact Finset.mem_biUnion.mpr ⟨v, hv, hlabel v hv⟩

omit [DecidableEq V] in
/-- A good boundary facet can only lie on the original face missing the last
coordinate. The conclusion follows from containment and equal cardinality. -/
theorem carrier_eq_spernerSmallLabels {m : ℕ} (label : V → Fin (m + 1))
    (carrier : V → Finset (Fin (m + 1))) (σ : Finset V)
    (hlabel : ∀ v ∈ σ, label v ∈ carrier v)
    (hgood : σ.image label = spernerSmallLabels m)
    (hcard : (σ.biUnion carrier).card = m) :
    σ.biUnion carrier = spernerSmallLabels m := by
  have hsub : spernerSmallLabels m ⊆ σ.biUnion carrier := by
    rw [← hgood]
    exact sperner_label_image_subset_carrier label carrier σ hlabel
  exact (Finset.eq_of_subset_of_card_le hsub
    (by rw [hcard, card_spernerSmallLabels])).symm

omit [DecidableEq V] in
/-- For a good face, the boundary cardinality condition is equivalent to
omission of the last coordinate from its carrier. -/
theorem good_carrier_card_iff_last_not_mem {m : ℕ} (label : V → Fin (m + 1))
    (carrier : V → Finset (Fin (m + 1))) (σ : Finset V)
    (hlabel : ∀ v ∈ σ, label v ∈ carrier v)
    (hgood : σ.image label = spernerSmallLabels m) :
    (σ.biUnion carrier).card = m ↔ Fin.last m ∉ σ.biUnion carrier := by
  constructor
  · intro hcard
    rw [carrier_eq_spernerSmallLabels label carrier σ hlabel hgood hcard]
    simp
  · intro hlast
    have hsub : σ.biUnion carrier ⊆ spernerSmallLabels m := by
      intro i hi
      apply mem_spernerSmallLabels.mpr
      intro hilast
      exact hlast (hilast ▸ hi)
    have hsup : spernerSmallLabels m ⊆ σ.biUnion carrier := by
      rw [← hgood]
      exact sperner_label_image_subset_carrier label carrier σ hlabel
    rw [Finset.Subset.antisymm hsub hsup, card_spernerSmallLabels]

omit [DecidableEq V] in
/-- Among good faces, all boundary faces are exactly those on the last face.
This is the filter identity used before transporting the incidence count. -/
theorem good_boundary_filter_eq_last_face_filter {m : ℕ}
    (label : V → Fin (m + 1)) (carrier : V → Finset (Fin (m + 1)))
    (faces : Finset (Finset V)) (hlabel : ∀ v, label v ∈ carrier v) :
    faces.filter (fun σ => σ.image label = spernerSmallLabels m ∧
        (σ.biUnion carrier).card = m) =
      (faces.filter (fun σ => Fin.last m ∉ σ.biUnion carrier)).filter
        (fun σ => σ.image label = spernerSmallLabels m) := by
  classical
  ext σ
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hσ, hg, hc⟩
    exact ⟨⟨hσ, (good_carrier_card_iff_last_not_mem label carrier σ
      (fun v _ => hlabel v) hg).mp hc⟩, hg⟩
  · rintro ⟨⟨hσ, hl⟩, hg⟩
    exact ⟨hσ, hg, (good_carrier_card_iff_last_not_mem label carrier σ
      (fun v _ => hlabel v) hg).mpr hl⟩

/-- Remove the last coordinate from labels on an embedded boundary face. -/
def spernerRestrictedLabel {n : ℕ} (e : W ↪ V) (label : V → Fin (n + 1))
    (hne : ∀ w, label (e w) ≠ Fin.last n) : W → Fin n :=
  fun w => (label (e w)).castPred (hne w)

omit [DecidableEq V] [DecidableEq W] in
@[simp] theorem castSucc_spernerRestrictedLabel {n : ℕ} (e : W ↪ V)
    (label : V → Fin (n + 1)) (hne : ∀ w, label (e w) ≠ Fin.last n) (w : W) :
    (spernerRestrictedLabel e label hne w).castSucc = label (e w) :=
  Fin.castSucc_castPred _ _

/-- The smaller label set is exactly the image of the smaller coordinate type. -/
theorem image_univ_castSucc_eq_spernerSmallLabels (n : ℕ) :
    (Finset.univ : Finset (Fin n)).image Fin.castSucc = spernerSmallLabels n := by
  ext i
  constructor
  · intro hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
    exact mem_spernerSmallLabels.mpr j.castSucc_ne_last
  · intro hi
    obtain ⟨j, hj⟩ := Fin.eq_castSucc_of_ne_last (mem_spernerSmallLabels.mp hi)
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj⟩

omit [DecidableEq W] in
/-- Compatible vertex and coordinate embeddings commute with the label image. -/
theorem mapped_label_image_eq {n : ℕ} (e : W ↪ V)
    (label : V → Fin (n + 1)) (lowerLabel : W → Fin n)
    (hlabel : ∀ w, label (e w) = (lowerLabel w).castSucc) (σ : Finset W) :
    (σ.map e).image label = (σ.image lowerLabel).image Fin.castSucc := by
  rw [Finset.map_eq_image, Finset.image_image, Finset.image_image]
  apply Finset.image_congr
  intro w _
  exact hlabel w

omit [DecidableEq W] in
/-- A mapped face is good exactly when its lower-dimensional face is full. -/
theorem mapped_fully_labelled_iff {n : ℕ} (e : W ↪ V)
    (label : V → Fin (n + 1)) (lowerLabel : W → Fin n)
    (hlabel : ∀ w, label (e w) = (lowerLabel w).castSucc) (σ : Finset W) :
    (σ.map e).image label = spernerSmallLabels n ↔
      σ.image lowerLabel = Finset.univ := by
  rw [mapped_label_image_eq e label lowerLabel hlabel σ,
    ← image_univ_castSucc_eq_spernerSmallLabels n]
  exact Finset.image_inj (Fin.castSucc_injective n)

omit [DecidableEq V] [DecidableEq W] in
/-- Restricting an admissible embedded label preserves membership in the
lower-dimensional carrier. -/
theorem restricted_label_mem_carrier {n : ℕ} (e : W ↪ V)
    (label : V → Fin (n + 1)) (hne : ∀ w, label (e w) ≠ Fin.last n)
    (carrier : W → Finset (Fin n))
    (hlabel : ∀ w, label (e w) ∈ (carrier w).image Fin.castSucc) (w : W) :
    spernerRestrictedLabel e label hne w ∈ carrier w := by
  obtain ⟨i, hi, hieq⟩ := Finset.mem_image.mp (hlabel w)
  have heq : i = spernerRestrictedLabel e label hne w :=
    Fin.castSucc_injective n
      (hieq.trans (castSucc_spernerRestrictedLabel e label hne w).symm)
  simpa only [heq] using hi

omit [DecidableEq W] in
/-- A finite family of faces can be filtered before or after an injective
vertex map, without changing its cardinality. -/
theorem mapped_family_filter_card (e : W ↪ V)
    (lowerFamily : Finset (Finset W)) (higherFamily : Finset (Finset V))
    (p : Finset W → Prop) (q : Finset V → Prop)
    [DecidablePred p] [DecidablePred q]
    (hfamily : higherFamily = lowerFamily.image (fun σ => σ.map e))
    (hpred : ∀ σ ∈ lowerFamily, q (σ.map e) ↔ p σ) :
    (higherFamily.filter q).card = (lowerFamily.filter p).card := by
  classical
  have hfilter : lowerFamily.filter (fun σ => q (σ.map e)) = lowerFamily.filter p :=
    Finset.filter_congr hpred
  rw [hfamily, Finset.filter_image, hfilter]
  exact Finset.card_image_of_injective _ (Finset.map_injective e)

omit [DecidableEq W] in
/-- Exact transport of the good-face count under a raw face-family bijection. -/
theorem mapped_good_family_card {n : ℕ} (e : W ↪ V)
    (label : V → Fin (n + 1)) (lowerLabel : W → Fin n)
    (hlabel : ∀ w, label (e w) = (lowerLabel w).castSucc)
    (lowerFamily : Finset (Finset W)) (higherFamily : Finset (Finset V))
    (hfamily : higherFamily = lowerFamily.image (fun σ => σ.map e)) :
    (higherFamily.filter (fun τ => τ.image label = spernerSmallLabels n)).card =
      (lowerFamily.filter (fun σ => σ.image lowerLabel = Finset.univ)).card := by
  classical
  exact mapped_family_filter_card e lowerFamily higherFamily _ _ hfamily
    (fun σ _ => mapped_fully_labelled_iff e label lowerLabel hlabel σ)

omit [DecidableEq W] in
/-- Count transport in the `Finset.map` form produced by the subdivision
restriction theorem. -/
theorem mapped_good_family_card_of_map {n : ℕ} (e : W ↪ V)
    (label : V → Fin (n + 1)) (lowerLabel : W → Fin n)
    (hlabel : ∀ w, label (e w) = (lowerLabel w).castSucc)
    (lowerFamily : Finset (Finset W)) (higherFamily : Finset (Finset V))
    (hfamily : higherFamily = lowerFamily.map (Finset.mapEmbedding e).toEmbedding) :
    (higherFamily.filter (fun τ => τ.image label = spernerSmallLabels n)).card =
      (lowerFamily.filter (fun σ => σ.image lowerLabel = Finset.univ)).card := by
  classical
  apply mapped_good_family_card e label lowerLabel hlabel lowerFamily higherFamily
  calc
    higherFamily = lowerFamily.map (Finset.mapEmbedding e).toEmbedding := hfamily
    _ = lowerFamily.image (fun σ => σ.map e) := Finset.map_eq_image _ _

end Tingley

end OAI

-- Adapted from OAI.Analysis.SphereIsometry.BarycentricRestriction

namespace OAI

/-! # Embeddings of complexes and exact restriction under subdivision -/

noncomputable section

namespace Tingley.FiniteComplex

universe u v w z
variable {V : Type u} {W : Type v} [Fintype V] [Fintype W]
variable [DecidableEq V] [DecidableEq W]

structure Embedding (K : FiniteComplex V) (L : FiniteComplex W) where
  toEmbedding : V ↪ W
  map_mem_iff : ∀ s : Finset V, s.map toEmbedding ∈ L.faces ↔ s ∈ K.faces

namespace Embedding

variable {K : FiniteComplex V} {L : FiniteComplex W}

def full (e : V ↪ W) : Embedding (FiniteComplex.full : FiniteComplex V)
    (FiniteComplex.full : FiniteComplex W) where
  toEmbedding := e
  map_mem_iff := fun _ => by simp

def faceMap (e : Embedding K L) : FaceVertex K ↪ FaceVertex L where
  toFun s := ⟨s.val.map e.toEmbedding,
    (e.map_mem_iff s.val).mpr s.property.1, Finset.map_nonempty.mpr s.property.2⟩
  inj' := by
    intro a b h
    apply Subtype.ext
    exact Finset.map_injective e.toEmbedding (congrArg Subtype.val h)

@[simp] theorem faceMap_val (e : Embedding K L) (s : FaceVertex K) :
    (e.faceMap s).val = s.val.map e.toEmbedding := rfl

def sd (e : Embedding K L) : Embedding K.sd L.sd where
  toEmbedding := e.faceMap
  map_mem_iff := by
    intro c
    rw [mem_sd_iff, mem_sd_iff]
    constructor
    · intro hc a ha b hb
      have h := hc (e.faceMap a) (Finset.mem_map.mpr ⟨a, ha, rfl⟩)
        (e.faceMap b) (Finset.mem_map.mpr ⟨b, hb, rfl⟩)
      exact h.imp Finset.map_subset_map.mp Finset.map_subset_map.mp
    · intro hc a ha b hb
      obtain ⟨a', ha', rfl⟩ := Finset.mem_map.mp ha
      obtain ⟨b', hb', rfl⟩ := Finset.mem_map.mp hb
      exact (hc a' ha' b' hb').imp Finset.map_subset_map.mpr Finset.map_subset_map.mpr

def preimage (e : Embedding K L) (s : Finset W) : Finset V :=
  Finset.univ.filter (fun v => e.toEmbedding v ∈ s)

@[simp] theorem mem_preimage (e : Embedding K L) {s : Finset W} {v : V} :
    v ∈ e.preimage s ↔ e.toEmbedding v ∈ s := by
  simp [preimage]

theorem map_preimage (e : Embedding K L) (s : Finset W)
    (hs : ∀ w ∈ s, ∃ v, e.toEmbedding v = w) :
    (e.preimage s).map e.toEmbedding = s := by
  ext w
  constructor
  · intro hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hw
    exact (e.mem_preimage).mp hv
  · intro hw
    obtain ⟨v, rfl⟩ := hs w hw
    exact Finset.mem_map.mpr ⟨v, e.mem_preimage.mpr hw, rfl⟩

theorem exists_face_preimage (e : Embedding K L) {s : Finset W} (hs : s ∈ L.faces)
    (hrange : ∀ w ∈ s, ∃ v, e.toEmbedding v = w) :
    ∃ t ∈ K.faces, t.map e.toEmbedding = s := by
  refine ⟨e.preimage s, ?_, e.map_preimage s hrange⟩
  apply (e.map_mem_iff _).mp
  rwa [e.map_preimage s hrange]

variable {I : Type w} {J : Type z} [DecidableEq I] [DecidableEq J]

theorem faceCarrier_map (e : Embedding K L) (i : I ↪ J)
    {cV : V → Finset I} {cW : W → Finset J}
    (h : ∀ v, cW (e.toEmbedding v) = (cV v).map i) (s : Finset V) :
    faceCarrier cW (s.map e.toEmbedding) = (faceCarrier cV s).map i := by
  ext j
  constructor
  · intro hj
    obtain ⟨w, hw, hj⟩ := mem_faceCarrier.mp hj
    obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hw
    rw [h] at hj
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hj
    exact Finset.mem_map.mpr ⟨a, mem_faceCarrier.mpr ⟨v, hv, ha⟩, rfl⟩
  · intro hj
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hj
    obtain ⟨v, hv, ha⟩ := mem_faceCarrier.mp ha
    refine mem_faceCarrier.mpr ⟨e.toEmbedding v,
      Finset.mem_map.mpr ⟨v, hv, rfl⟩, ?_⟩
    rw [h]
    exact Finset.mem_map.mpr ⟨a, ha, rfl⟩

theorem sdCarrier_faceMap (e : Embedding K L) (i : I ↪ J)
    {cV : V → Finset I} {cW : W → Finset J}
    (h : ∀ v, cW (e.toEmbedding v) = (cV v).map i) (s : FaceVertex K) :
    L.sdCarrier cW (e.faceMap s) = (K.sdCarrier cV s).map i :=
  e.faceCarrier_map i h s.val

theorem faceMap_range_iff (e : Embedding K L) {cW : W → Finset J} {A : Finset J}
    (h : ∀ w, cW w ⊆ A ↔ ∃ v, e.toEmbedding v = w) (s : FaceVertex L) :
    L.sdCarrier cW s ⊆ A ↔ ∃ t : FaceVertex K, e.faceMap t = s := by
  constructor
  · intro hs
    have hvertices : ∀ w ∈ s.val, ∃ v, e.toEmbedding v = w := by
      intro w hw
      apply (h w).mp
      intro j hj
      exact hs (mem_faceCarrier.mpr ⟨w, hw, hj⟩)
    obtain ⟨t, ht, hts⟩ := e.exists_face_preimage s.property.1 hvertices
    have hne : t.Nonempty := by
      have : (t.map e.toEmbedding).Nonempty := hts.symm ▸ s.property.2
      exact Finset.map_nonempty.mp this
    refine ⟨⟨t, ht, hne⟩, ?_⟩
    exact Subtype.ext hts
  · rintro ⟨t, rfl⟩
    intro j hj
    obtain ⟨w, hw, hj⟩ := mem_faceCarrier.mp hj
    obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hw
    exact (h _).mpr ⟨v, rfl⟩ hj

theorem face_range_iff (e : Embedding K L) {cW : W → Finset J} {A : Finset J}
    (h : ∀ w, cW w ⊆ A ↔ ∃ v, e.toEmbedding v = w) {s : Finset W}
    (hs : s ∈ L.faces) :
    faceCarrier cW s ⊆ A ↔ ∃ t ∈ K.faces, t.map e.toEmbedding = s := by
  constructor
  · intro hsub
    apply e.exists_face_preimage hs
    intro w hw
    apply (h w).mp
    intro j hj
    exact hsub (mem_faceCarrier.mpr ⟨w, hw, hj⟩)
  · rintro ⟨t, ht, rfl⟩
    intro j hj
    obtain ⟨w, hw, hj⟩ := mem_faceCarrier.mp hj
    obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hw
    exact (h _).mpr ⟨v, rfl⟩ hj

end Embedding

end Tingley.FiniteComplex

end

end OAI

-- Adapted from OAI.Analysis.SphereIsometry.SubdivisionRestriction

namespace OAI

/-! # The exact original-face restriction of every concrete subdivision -/

noncomputable section

namespace Tingley

variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

def iterEmbedding (e : I ↪ J) : (k : ℕ) →
    FiniteComplex.Embedding (iterData I k).complex (iterData J k).complex
  | 0 => FiniteComplex.Embedding.full e
  | k + 1 => (iterEmbedding e k).sd

theorem iterEmbedding_carrier (e : I ↪ J) (k : ℕ)
    (v : (iterData I k).Vertex) :
    (iterData J k).carrier ((iterEmbedding e k).toEmbedding v) =
      ((iterData I k).carrier v).map e := by
  induction k with
  | zero =>
      change I at v
      change ({e v} : Finset J) = ({v} : Finset I).map e
      exact (Finset.map_singleton e v).symm
  | succ k ih =>
      exact (iterEmbedding e k).sdCarrier_faceMap e ih v

theorem iterEmbedding_range_iff (e : I ↪ J) (k : ℕ)
    (v : (iterData J k).Vertex) :
    (iterData J k).carrier v ⊆ Finset.univ.map e ↔
      ∃ w, (iterEmbedding e k).toEmbedding w = v := by
  induction k with
  | zero =>
      change J at v
      change ({v} : Finset J) ⊆ Finset.univ.map e ↔ ∃ w : I, e w = v
      simp only [Finset.singleton_subset_iff, Finset.mem_map,
        Finset.mem_univ, true_and]
  | succ k ih => exact (iterEmbedding e k).faceMap_range_iff ih v

theorem iterEmbedding_faceCarrier (e : I ↪ J) (k : ℕ)
    (s : Finset (iterData I k).Vertex) :
    FiniteComplex.faceCarrier (iterData J k).carrier
        (s.map (iterEmbedding e k).toEmbedding) =
      (FiniteComplex.faceCarrier (iterData I k).carrier s).map e :=
  (iterEmbedding e k).faceCarrier_map e (iterEmbedding_carrier e k) s

theorem iterEmbedding_face_range_iff (e : I ↪ J) (k : ℕ)
    {s : Finset (iterData J k).Vertex} (hs : s ∈ (iterData J k).complex.faces) :
    FiniteComplex.faceCarrier (iterData J k).carrier s ⊆ Finset.univ.map e ↔
      ∃ t ∈ (iterData I k).complex.faces, t.map (iterEmbedding e k).toEmbedding = s :=
  (iterEmbedding e k).face_range_iff (iterEmbedding_range_iff e k) hs

def lastFaceEmbedding (m k : ℕ) : IterVertex m k ↪ IterVertex (m + 1) k :=
  (iterEmbedding (Fin.castSuccEmb : Fin (m + 1) ↪ Fin ((m + 1) + 1)) k).toEmbedding

theorem lastFace_carrier (m k : ℕ) (v : IterVertex m k) :
    iterCarrier (m + 1) k (lastFaceEmbedding m k v) =
      (iterCarrier m k v).map Fin.castSuccEmb :=
  iterEmbedding_carrier Fin.castSuccEmb k v

theorem lastFace_faceCarrier (m k : ℕ) (s : Finset (IterVertex m k)) :
    faceCarrier (m + 1) k (s.map (lastFaceEmbedding m k)) =
      (faceCarrier m k s).map Fin.castSuccEmb :=
  iterEmbedding_faceCarrier Fin.castSuccEmb k s

theorem lastFace_range_iff (m k : ℕ) (v : IterVertex (m + 1) k) :
    Fin.last (m + 1) ∉ iterCarrier (m + 1) k v ↔
      ∃ w, lastFaceEmbedding m k w = v := by
  have h := iterEmbedding_range_iff
    (Fin.castSuccEmb : Fin (m + 1) ↪ Fin ((m + 1) + 1)) k v
  simpa only [iterCarrier, lastFaceEmbedding, Finset.map_eq_image,
    Fin.coe_castSuccEmb, Fin.image_castSucc, Finset.subset_compl_singleton] using h

theorem lastFace_mem_iff (m k : ℕ) (s : Finset (IterVertex m k)) :
    s.map (lastFaceEmbedding m k) ∈ iterComplex (m + 1) k ↔ s ∈ iterComplex m k :=
  (iterEmbedding Fin.castSuccEmb k).map_mem_iff s

theorem lastFace_face_range_iff {m k : ℕ} {s : Finset (IterVertex (m + 1) k)}
    (hs : s ∈ iterComplex (m + 1) k) :
    Fin.last (m + 1) ∉ faceCarrier (m + 1) k s ↔
      ∃ t ∈ iterComplex m k, t.map (lastFaceEmbedding m k) = s := by
  have h := iterEmbedding_face_range_iff
    (Fin.castSuccEmb : Fin (m + 1) ↪ Fin ((m + 1) + 1)) k hs
  simpa only [faceCarrier, iterCarrier, iterComplex, lastFaceEmbedding,
    Finset.map_eq_image, Fin.coe_castSuccEmb, Fin.image_castSucc,
    Finset.subset_compl_singleton] using h

theorem lastFace_map_top_mem (m k : ℕ) {s : Finset (IterVertex m k)}
    (hs : s ∈ topCells m k) :
    s.map (lastFaceEmbedding m k) ∈ codimFaces (m + 1) k := by
  obtain ⟨hsface, hscard⟩ := mem_topCells.mp hs
  exact mem_codimFaces.mpr ⟨(lastFace_mem_iff m k s).mpr hsface, by simpa using hscard⟩

theorem lastFace_top_image (m k : ℕ) :
    (topCells m k).map (Finset.mapEmbedding (lastFaceEmbedding m k)).toEmbedding =
      (codimFaces (m + 1) k).filter
        (fun s => Fin.last (m + 1) ∉ faceCarrier (m + 1) k s) := by
  ext s
  constructor
  · intro hs
    obtain ⟨t, ht, rfl⟩ := Finset.mem_map.mp hs
    apply Finset.mem_filter.mpr
    refine ⟨lastFace_map_top_mem m k ht, ?_⟩
    change Fin.last (m + 1) ∉ faceCarrier (m + 1) k (t.map (lastFaceEmbedding m k))
    rw [lastFace_faceCarrier]
    simp only [Finset.mem_map, not_exists, not_and]
    intro i hi
    exact Fin.castSucc_ne_last i
  · intro hs
    obtain ⟨hscodim, hboundary⟩ := Finset.mem_filter.mp hs
    obtain ⟨hsface, hscard⟩ := mem_codimFaces.mp hscodim
    obtain ⟨t, htface, hts⟩ := (lastFace_face_range_iff hsface).mp hboundary
    apply Finset.mem_map.mpr
    refine ⟨t, mem_topCells.mpr ⟨htface, ?_⟩, hts⟩
    have hcard := congrArg Finset.card hts
    simpa [hscard] using hcard

end Tingley

end

end OAI

-- Adapted from OAI.Analysis.SphereIsometry.BarycentricIncidence

namespace OAI

/-!
# Codimension-one incidence in the actual face-chain subdivision

Completions of a flag are counted by inserting its unique missing rank.
An interior missing rank has two completions. A missing top rank inherits
the incidence count of the greatest old face.
-/

noncomputable section

namespace Tingley.FiniteComplex

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {K : FiniteComplex V}

theorem chain_insert_iff {c : Finset (FaceVertex K)} {a : FaceVertex K} :
    K.chain (insert a c) ↔ K.chain c ∧
      ∀ b ∈ c, a.val ⊆ b.val ∨ b.val ⊆ a.val := by
  classical
  constructor
  · intro h
    exact ⟨K.chain_mono h (Finset.subset_insert _ _),
      fun b hb => h a (Finset.mem_insert_self _ _) b (Finset.mem_insert_of_mem hb)⟩
  · rintro ⟨hc, ha⟩ b hb d hd
    rcases Finset.mem_insert.mp hb with hba | hbc
    · subst b
      rcases Finset.mem_insert.mp hd with hda | hdc
      · subst d
        exact Or.inl (Finset.Subset.refl _)
      · exact ha d hdc
    · rcases Finset.mem_insert.mp hd with hda | hdc
      · subst d
        exact (ha b hbc).symm
      · exact hc b hbc d hdc

def insertionVertices (K : FiniteComplex V) (c : Finset (FaceVertex K)) :
    Finset (FaceVertex K) := by
  classical
  exact Finset.univ.filter (fun a => a ∉ c ∧ K.chain (insert a c))

@[simp] theorem mem_insertionVertices {c : Finset (FaceVertex K)} {a : FaceVertex K} :
    a ∈ K.insertionVertices c ↔ a ∉ c ∧ K.chain (insert a c) := by
  classical
  simp [insertionVertices]

theorem incidentTop_sd_eq_image_insert {m : ℕ} {c : Finset (FaceVertex K)}
    (hc : c.card = m) :
    K.sd.incidentTop m c = (K.insertionVertices c).image (fun a => insert a c) := by
  classical
  ext d
  constructor
  · intro hd
    obtain ⟨hdface, hdcard, hcd⟩ := mem_incidentTop.mp hd
    obtain ⟨a, ha, had⟩ := Finset.exists_eq_insert_iff.mpr
      (show c ⊆ d ∧ c.card + 1 = d.card from ⟨hcd, by omega⟩)
    apply Finset.mem_image.mpr
    refine ⟨a, mem_insertionVertices.mpr ⟨ha, ?_⟩, had⟩
    rw [had]
    exact mem_sd_iff.mp hdface
  · intro hd
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨ha, hchain⟩ := mem_insertionVertices.mp ha
    exact mem_incidentTop.mpr ⟨mem_sd_iff.mpr hchain,
      by rw [Finset.card_insert_of_notMem ha, hc], Finset.subset_insert _ _⟩

theorem incidentTop_sd_card_eq_insertionVertices {m : ℕ}
    {c : Finset (FaceVertex K)} (hc : c.card = m) :
    (K.sd.incidentTop m c).card = (K.insertionVertices c).card := by
  classical
  rw [incidentTop_sd_eq_image_insert hc]
  apply Finset.card_image_of_injOn
  intro a ha b hb hab
  exact (Finset.insert_inj (mem_insertionVertices.mp ha).1).mp hab

theorem rank_ne_of_missing {m r : ℕ} {c : Finset (FaceVertex K)}
    (hr : K.ranks c = (Finset.Icc 1 (m + 1)).erase r)
    {a : FaceVertex K} (ha : a ∈ c) : a.val.card ≠ r := by
  have h : a.val.card ∈ K.ranks c := mem_ranks.mpr ⟨a, ha, rfl⟩
  rw [hr] at h
  exact (Finset.mem_erase.mp h).1

theorem insertionVertices_card_eq_missing {m r : ℕ} (hK : K.CardBound m)
    {c : Finset (FaceVertex K)}
    (hr : K.ranks c = (Finset.Icc 1 (m + 1)).erase r)
    {a : FaceVertex K} (ha : a ∈ K.insertionVertices c) : a.val.card = r := by
  classical
  obtain ⟨hanot, hchain⟩ := mem_insertionVertices.mp ha
  by_contra har
  have hmem : a.val.card ∈ K.ranks c := by
    rw [hr]
    exact Finset.mem_erase.mpr ⟨har, Finset.mem_Icc.mpr
      ⟨Finset.card_pos.mpr a.property.2, hK a.val a.property.1⟩⟩
  obtain ⟨b, hb, hba⟩ := mem_ranks.mp hmem
  have hab : a = b := chain_eq_of_card_eq hchain (Finset.mem_insert_self _ _)
    (Finset.mem_insert_of_mem hb) hba.symm
  apply hanot
  rw [hab]
  exact hb

/-- Count possible inserted old faces between two consecutive retained ranks. -/
theorem card_insertionVertices_eq_sdiff {c : Finset (FaceVertex K)}
    {L U : Finset V} (hU : U ∈ K.faces) (hLU : L ⊆ U)
    (hmem : ∀ a : FaceVertex K, a ∈ K.insertionVertices c ↔
      L ⊆ a.val ∧ a.val ⊆ U ∧ a.val.card = L.card + 1) :
    (K.insertionVertices c).card = (U \ L).card := by
  classical
  let f : ∀ a ∈ U \ L, FaceVertex K := fun a ha =>
    ⟨insert a L,
      K.down_closed hU (Finset.insert_subset_iff.mpr ⟨(Finset.mem_sdiff.mp ha).1, hLU⟩),
      ⟨a, Finset.mem_insert_self _ _⟩⟩
  have hf : ∀ a ha, f a ha ∈ K.insertionVertices c := by
    intro a ha
    apply (hmem _).mpr
    exact ⟨Finset.subset_insert _ _,
      Finset.insert_subset_iff.mpr ⟨(Finset.mem_sdiff.mp ha).1, hLU⟩,
      Finset.card_insert_of_notMem (Finset.mem_sdiff.mp ha).2⟩
  have hinj : ∀ a ha b hb, f a ha = f b hb → a = b := by
    intro a ha b hb hab
    have heq : insert a L = insert b L := congrArg Subtype.val hab
    exact (Finset.insert_inj (Finset.mem_sdiff.mp ha).2).mp heq
  have hsurj : ∀ b ∈ K.insertionVertices c, ∃ a ha, f a ha = b := by
    intro b hb
    obtain ⟨hLb, hbU, hbcard⟩ := (hmem b).mp hb
    obtain ⟨a, haL, hab⟩ := Finset.exists_eq_insert_iff.mpr
      (show L ⊆ b.val ∧ L.card + 1 = b.val.card from ⟨hLb, hbcard.symm⟩)
    have haU : a ∈ U := by
      apply hbU
      rw [← hab]
      exact Finset.mem_insert_self _ _
    refine ⟨a, Finset.mem_sdiff.mpr ⟨haU, haL⟩, ?_⟩
    apply Subtype.ext
    exact hab
  exact (Finset.card_bij f hf hinj hsurj).symm

/-- An omitted rank strictly below the top has exactly two completions. -/
theorem incidentTop_sd_card_two_of_missing_rank {m r : ℕ} (hK : K.CardBound m)
    {c : Finset (FaceVertex K)} (hc : c ∈ K.sd.codimFaces m)
    (hr₁ : 1 ≤ r) (hrm : r ≤ m)
    (hr : K.ranks c = (Finset.Icc 1 (m + 1)).erase r) :
    (K.sd.incidentTop m c).card = 2 := by
  classical
  obtain ⟨hcface, hccard⟩ := mem_codimFaces.mp hc
  have hcchain := mem_sd_iff.mp hcface
  have hUr : r + 1 ∈ K.ranks c := by
    rw [hr]
    exact Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩
  obtain ⟨U, hUc, hUcard⟩ := mem_ranks.mp hUr
  obtain ⟨L, hLcard, hLU, hLmem, hgap⟩ :
      ∃ L : Finset V, L.card + 1 = r ∧ L ⊆ U.val ∧
        (L = ∅ ∨ ∃ a ∈ c, a.val = L) ∧
        ∀ b ∈ c, b.val ⊆ L ∨ U.val ⊆ b.val := by
    by_cases hrone : r = 1
    · refine ⟨∅, by simp [hrone], Finset.empty_subset _, Or.inl rfl, ?_⟩
      intro b hb
      right
      apply chain_subset_of_card_le hcchain hUc hb
      have hbpos := Finset.card_pos.mpr b.property.2
      have hbne := rank_ne_of_missing hr hb
      omega
    · have hLr : r - 1 ∈ K.ranks c := by
        rw [hr]
        exact Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩
      obtain ⟨L, hLc, hLc_card⟩ := mem_ranks.mp hLr
      refine ⟨L.val, by omega,
        chain_subset_of_card_le hcchain hLc hUc (by omega),
        Or.inr ⟨L, hLc, rfl⟩, ?_⟩
      intro b hb
      have hbne := rank_ne_of_missing hr hb
      by_cases hbsmall : b.val.card ≤ L.val.card
      · exact Or.inl (chain_subset_of_card_le hcchain hb hLc hbsmall)
      · exact Or.inr (chain_subset_of_card_le hcchain hUc hb (by omega))
  have hmem : ∀ a : FaceVertex K, a ∈ K.insertionVertices c ↔
      L ⊆ a.val ∧ a.val ⊆ U.val ∧ a.val.card = L.card + 1 := by
    intro a
    constructor
    · intro ha
      have hacard := insertionVertices_card_eq_missing hK hr ha
      have hachain := (mem_insertionVertices.mp ha).2
      refine ⟨?_, chain_subset_of_card_le hachain (Finset.mem_insert_self _ _)
        (Finset.mem_insert_of_mem hUc) (by omega), by omega⟩
      rcases hLmem with hLempty | ⟨b, hbc, hbL⟩
      · rw [hLempty]
        exact Finset.empty_subset _
      · rw [← hbL]
        apply chain_subset_of_card_le hachain (Finset.mem_insert_of_mem hbc)
          (Finset.mem_insert_self _ _)
        have hbcard : b.val.card = L.card := congrArg Finset.card hbL
        omega
    · rintro ⟨hLa, haU, hacard⟩
      apply mem_insertionVertices.mpr
      refine ⟨?_, chain_insert_iff.mpr ⟨hcchain, ?_⟩⟩
      · intro hac
        exact rank_ne_of_missing hr hac (by omega)
      · intro b hb
        rcases hgap b hb with hbL | hUb
        · exact Or.inr (hbL.trans hLa)
        · exact Or.inl (haU.trans hUb)
  rw [incidentTop_sd_card_eq_insertionVertices hccard,
    card_insertionVertices_eq_sdiff U.property.1 hLU hmem,
    Finset.card_sdiff_of_subset hLU, hUcard]
  omega

/-- If the omitted rank is the top rank, completions are exactly the old
top faces containing the retained rank-`m` face. -/
theorem incidentTop_sd_card_eq_of_missing_top {m : ℕ} (hK : K.CardBound m)
    {c : Finset (FaceVertex K)} (hc : c ∈ K.sd.codimFaces m)
    (hr : K.ranks c = (Finset.Icc 1 (m + 1)).erase (m + 1))
    {T : FaceVertex K} (hTc : T ∈ c) (hTcard : T.val.card = m) :
    (K.sd.incidentTop m c).card = (K.incidentTop m T.val).card := by
  classical
  obtain ⟨hcface, hccard⟩ := mem_codimFaces.mp hc
  have hcchain := mem_sd_iff.mp hcface
  have hmax : ∀ b ∈ c, b.val ⊆ T.val := by
    intro b hb
    apply chain_subset_of_card_le hcchain hb hTc
    have hbcard := hK b.val b.property.1
    have hbne := rank_ne_of_missing hr hb
    omega
  let f : ∀ W ∈ K.incidentTop m T.val, FaceVertex K := fun W hW =>
    ⟨W, (mem_incidentTop.mp hW).1,
      Finset.card_pos.mp (by have h := (mem_incidentTop.mp hW).2.1; omega)⟩
  have hf : ∀ W hW, f W hW ∈ K.insertionVertices c := by
    intro W hW
    obtain ⟨hWface, hWcard, hTW⟩ := mem_incidentTop.mp hW
    apply mem_insertionVertices.mpr
    refine ⟨?_, chain_insert_iff.mpr ⟨hcchain, ?_⟩⟩
    · intro hWc
      have hle := Finset.card_le_card (hmax (f W hW) hWc)
      change W.card ≤ T.val.card at hle
      omega
    · intro b hb
      exact Or.inr ((hmax b hb).trans hTW)
  have hinj : ∀ W hW U hU, f W hW = f U hU → W = U := by
    intro W hW U hU h
    exact congrArg Subtype.val h
  have hsurj : ∀ a ∈ K.insertionVertices c,
      ∃ W hW, f W hW = a := by
    intro a ha
    have hacard := insertionVertices_card_eq_missing hK hr ha
    have hTa : T.val ⊆ a.val :=
      chain_subset_of_card_le (mem_insertionVertices.mp ha).2
        (Finset.mem_insert_of_mem hTc) (Finset.mem_insert_self _ _) (by omega)
    have hav : a.val ∈ K.incidentTop m T.val :=
      mem_incidentTop.mpr ⟨a.property.1, hacard, hTa⟩
    exact ⟨a.val, hav, Subtype.ext rfl⟩
  rw [incidentTop_sd_card_eq_insertionVertices hccard]
  exact (Finset.card_bij f hf hinj hsurj).symm

theorem incidentTop_sd_missing_top_data {m : ℕ} (hm : 0 < m) (hK : K.CardBound m)
    {c : Finset (FaceVertex K)} (hc : c ∈ K.sd.codimFaces m)
    (hr : K.ranks c = (Finset.Icc 1 (m + 1)).erase (m + 1)) :
    ∃ T ∈ c, T.val.card = m ∧ (∀ b ∈ c, b.val ⊆ T.val) ∧
      (K.sd.incidentTop m c).card = (K.incidentTop m T.val).card := by
  have hmrank : m ∈ K.ranks c := by
    rw [hr]
    exact Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr ⟨hm, by omega⟩⟩
  obtain ⟨T, hTc, hTcard⟩ := mem_ranks.mp hmrank
  refine ⟨T, hTc, hTcard, ?_, incidentTop_sd_card_eq_of_missing_top hK hc hr hTc hTcard⟩
  intro b hb
  apply chain_subset_of_card_le (mem_sd_iff.mp (mem_codimFaces.mp hc).1) hb hTc
  have hbcard := hK b.val b.property.1
  have hbne := rank_ne_of_missing hr hb
  omega

/-- The complete positive-dimensional codimension-one alternative. The first
case also records a retained old top face for transferring carrier information. -/
theorem incidentTop_sd_cases {m : ℕ} (hm : 0 < m) (hK : K.CardBound m)
    {c : Finset (FaceVertex K)} (hc : c ∈ K.sd.codimFaces m) :
    ((K.sd.incidentTop m c).card = 2 ∧
      ∃ T ∈ c, T.val.card = m + 1 ∧ ∀ b ∈ c, b.val ⊆ T.val) ∨
    (∃ T ∈ c, T.val.card = m ∧ (∀ b ∈ c, b.val ⊆ T.val) ∧
      (K.sd.incidentTop m c).card = (K.incidentTop m T.val).card) := by
  obtain ⟨r, hr₁, hr₂, hr⟩ := missing_rank hK hc
  by_cases hrm : r ≤ m
  · left
    refine ⟨incidentTop_sd_card_two_of_missing_rank hK hc hr₁ hrm hr, ?_⟩
    have hmrank : m + 1 ∈ K.ranks c := by
      rw [hr]
      exact Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩⟩
    obtain ⟨T, hTc, hTcard⟩ := mem_ranks.mp hmrank
    refine ⟨T, hTc, hTcard, ?_⟩
    intro b hb
    apply chain_subset_of_card_le (mem_sd_iff.mp (mem_codimFaces.mp hc).1) hb hTc
    rw [hTcard]
    exact hK b.val b.property.1
  · right
    have hre : r = m + 1 := by omega
    subst r
    exact incidentTop_sd_missing_top_data hm hK hc hr

end Tingley.FiniteComplex

end

end OAI

-- Adapted from OAI.Analysis.SphereIsometry.SubdivisionIncidence

namespace OAI

/-!
# Incidence counts for the concrete iterated simplex

The missing-rank alternative for an actual flag transports the old boundary
count, or gives two completions around a retained old top face. Iteration
therefore gives one incident top cell on the original boundary and two in
the interior.
-/

noncomputable section

namespace Tingley

/-- At depth zero the unique top cell is the full original vertex set. -/
theorem incidentTop_zero_eq_singleton (m : ℕ) (s : Finset (IterVertex m 0)) :
    incidentTop m 0 s = {Finset.univ} := by
  classical
  change Finset (Fin (m + 1)) at s
  change (FiniteComplex.full : FiniteComplex (Fin (m + 1))).incidentTop m s =
    {Finset.univ}
  ext t
  rw [FiniteComplex.mem_incidentTop, Finset.mem_singleton]
  constructor
  · rintro ⟨_, ht, _⟩
    exact t.eq_univ_of_card (by simpa only [Fintype.card_fin] using ht)
  · rintro rfl
    exact ⟨FiniteComplex.mem_full _, Finset.card_fin _, Finset.subset_univ _⟩

/-- The initial carrier of a face is that face itself. -/
theorem faceCarrier_zero (m : ℕ) (s : Finset (IterVertex m 0)) :
    faceCarrier m 0 s = s := by
  change Finset (Fin (m + 1)) at s
  change s.biUnion (fun i => {i}) = s
  exact Finset.biUnion_singleton_eq_self

/-- Actual codimension-one incidence for every positive-dimensional iterated
standard simplex. The boundary condition refers to the original coordinates. -/
theorem incidentTop_card_eq_if_boundary {m k : ℕ} (hm : 0 < m) :
    ∀ {s : Finset (IterVertex m k)}, s ∈ codimFaces m k →
      (incidentTop m k s).card =
        if (faceCarrier m k s).card = m then 1 else 2 := by
  classical
  induction k with
  | zero =>
      intro s hs
      have hcard := (mem_codimFaces.mp hs).2
      have hface : (faceCarrier m 0 s).card = m :=
        (congrArg (fun t : Finset (Fin (m + 1)) => t.card)
          (faceCarrier_zero m s)).trans hcard
      rw [incidentTop_zero_eq_singleton, Finset.card_singleton, if_pos hface]
  | succ k ih =>
      intro s hs
      let K := (iterData (Fin (m + 1)) k).complex
      have hK : K.CardBound m := by
        intro t ht
        exact iter_card_le ht
      change s ∈ K.sd.codimFaces m at hs
      rcases FiniteComplex.incidentTop_sd_cases hm hK hs with
        ⟨hcount, T, hTs, hTcard, hmax⟩ | ⟨T, hTs, hTcard, hmax, hcount⟩
      · have hcarrier : faceCarrier m (k + 1) s = faceCarrier m k T.val :=
          FiniteComplex.faceCarrier_sd_eq_greatest hTs hmax
        have htop : T.val ∈ topCells m k :=
          mem_topCells.mpr ⟨T.property.1, hTcard⟩
        have hnot : (Finset.univ : Finset (Fin (m + 1))).card ≠ m := by simp
        rw [hcarrier, top_faceCarrier htop, if_neg hnot]
        exact hcount
      · have hcarrier : faceCarrier m (k + 1) s = faceCarrier m k T.val :=
          FiniteComplex.faceCarrier_sd_eq_greatest hTs hmax
        have hcodim : T.val ∈ codimFaces m k :=
          mem_codimFaces.mpr ⟨T.property.1, hTcard⟩
        calc
          (incidentTop m (k + 1) s).card = (incidentTop m k T.val).card := hcount
          _ = if (faceCarrier m k T.val).card = m then 1 else 2 := ih hcodim
          _ = if (faceCarrier m (k + 1) s).card = m then 1 else 2 := by rw [hcarrier]

end Tingley

end

end OAI

-- Adapted from OAI.Analysis.SphereIsometry.BarycentricZero

namespace OAI

/-!
# The zero-dimensional subdivision and its empty codimension-one face

The subdivision of a zero-dimensional complex has one vertex for each old
singleton face. In particular, iterated subdivision of the point has one
top face, incident to its unique empty codimension-one face.
-/

noncomputable section

namespace Tingley.FiniteComplex

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {K : FiniteComplex V}

@[simp] theorem incidentTop_empty (K : FiniteComplex V) (m : ℕ) :
    K.incidentTop m ∅ = K.topCells m := by
  classical
  ext s
  simp [incidentTop]

theorem sd_topCells_zero_card (hK : K.CardBound 0) :
    (K.sd.topCells 0).card = (K.topCells 0).card := by
  classical
  let v : ∀ s ∈ K.topCells 0, FaceVertex K := fun s hs =>
    ⟨s, (mem_topCells.mp hs).1,
      Finset.card_pos.mp (by have h := (mem_topCells.mp hs).2; omega)⟩
  let f : ∀ s ∈ K.topCells 0, Finset (FaceVertex K) := fun s hs => {v s hs}
  have hf : ∀ s hs, f s hs ∈ K.sd.topCells 0 := by
    intro s hs
    apply mem_topCells.mpr
    constructor
    · apply mem_sd_iff.mpr
      change K.chain {v s hs}
      simp [chain]
    · change ({v s hs} : Finset (FaceVertex K)).card = 0 + 1
      simp
  have hinj : ∀ s hs t ht, f s hs = f t ht → s = t := by
    intro s hs t ht h
    have hv : v s hs = v t ht := Finset.singleton_inj.mp h
    exact congrArg Subtype.val hv
  have hsurj : ∀ c ∈ K.sd.topCells 0, ∃ s hs, f s hs = c := by
    intro c hc
    obtain ⟨hcface, hccard⟩ := mem_topCells.mp hc
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp (show c.card = 1 by omega)
    have hacard : a.val.card = 0 + 1 := by
      have hlo := Finset.card_pos.mpr a.property.2
      have hhi := hK a.val a.property.1
      omega
    have ha : a.val ∈ K.topCells 0 := mem_topCells.mpr ⟨a.property.1, hacard⟩
    refine ⟨a.val, ha, ?_⟩
    change ({v a.val ha} : Finset (FaceVertex K)) = {a}
    congr 1
  exact (Finset.card_bij f hf hinj hsurj).symm

end Tingley.FiniteComplex

namespace Tingley

theorem iter_topCells_zero_card (k : ℕ) : (topCells 0 k).card = 1 := by
  classical
  induction k with
  | zero =>
      change ((FiniteComplex.full : FiniteComplex (Fin 1)).topCells 0).card = 1
      have hfull : (FiniteComplex.full : FiniteComplex (Fin 1)).topCells 0 =
          {Finset.univ} := by
        ext s
        simp only [FiniteComplex.mem_topCells, FiniteComplex.mem_full,
          true_and, Finset.mem_singleton]
        constructor
        · intro hs
          apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
          simpa using hs.ge
        · rintro rfl
          simp
      rw [hfull]
      simp
  | succ k ih =>
      change (((iterData (Fin 1) k).complex).sd.topCells 0).card = 1
      have hK : (iterData (Fin 1) k).complex.CardBound 0 := by
        intro s hs
        exact iter_card_le (m := 0) (k := k) hs
      rw [FiniteComplex.sd_topCells_zero_card hK]
      exact ih

end Tingley

end

end OAI

-- Adapted from OAI.Analysis.SphereIsometry.Sperner

namespace OAI

/-!
# Geometric Sperner parity for the concrete iterated subdivisions

The labels belong to the actual recursively constructed vertex carriers.
The incidence theorem and the exact original-face restriction discharge the
finite counting hypotheses. Induction on dimension proves an odd number of
fully labelled top cells at every subdivision depth.
-/

namespace Tingley

theorem iterated_sperner_odd (m k : ℕ)
    (label : IterVertex m k → Fin (m + 1))
    (hlabel : ∀ v, label v ∈ iterCarrier m k v) :
    Odd (((topCells m k).filter
      (fun σ => σ.image label = Finset.univ)).card) := by
  classical
  induction m with
  | zero =>
      have hfull : ∀ σ ∈ topCells 0 k, σ.image label = Finset.univ := by
        intro σ hσ
        have hcard : σ.card = 1 := (mem_topCells.mp hσ).2
        have hne : σ.Nonempty := Finset.card_pos.mp (by rw [hcard]; exact Nat.zero_lt_one)
        obtain ⟨v, hv⟩ := hne
        apply Finset.eq_univ_iff_forall.mpr
        intro i
        refine Finset.mem_image.mpr ⟨v, hv, ?_⟩
        apply Fin.ext
        exact (Nat.lt_one_iff.mp (label v).isLt).trans
          (Nat.lt_one_iff.mp i.isLt).symm
      have hfilter : (topCells 0 k).filter
          (fun σ => σ.image label = Finset.univ) = topCells 0 k :=
        Finset.filter_eq_self.mpr hfull
      rw [hfilter, iter_topCells_zero_card]
      exact ⟨0, rfl⟩
  | succ m ih =>
      let e := lastFaceEmbedding m k
      have hne : ∀ v, label (e v) ≠ Fin.last (m + 1) := by
        intro v hv
        have hlast : Fin.last (m + 1) ∉ iterCarrier (m + 1) k (e v) :=
          (lastFace_range_iff m k (e v)).mpr ⟨v, rfl⟩
        exact hlast (hv ▸ hlabel (e v))
      let lowerLabel : IterVertex m k → Fin (m + 1) :=
        spernerRestrictedLabel e label hne
      have hcast : ∀ v, label (e v) = (lowerLabel v).castSucc :=
        fun v => (castSucc_spernerRestrictedLabel e label hne v).symm
      have hlower : ∀ v, lowerLabel v ∈ iterCarrier m k v := by
        apply restricted_label_mem_carrier e label hne (iterCarrier m k)
        intro v
        have h := hlabel (e v)
        change label (lastFaceEmbedding m k v) ∈
          iterCarrier (m + 1) k (lastFaceEmbedding m k v) at h
        rw [lastFace_carrier] at h
        simpa only [e, Finset.map_eq_image, Fin.coe_castSuccEmb] using h
      have hboundaryCard :
          (((codimFaces (m + 1) k).filter
            (fun τ => τ.image label = spernerSmallLabels (m + 1) ∧
              (faceCarrier (m + 1) k τ).card = m + 1)).card) =
          (((topCells m k).filter
            (fun σ => σ.image lowerLabel = Finset.univ)).card) := by
        change (((codimFaces (m + 1) k).filter
          (fun τ => τ.image label = spernerSmallLabels (m + 1) ∧
            (τ.biUnion (iterCarrier (m + 1) k)).card = m + 1)).card) = _
        rw [good_boundary_filter_eq_last_face_filter label
          (iterCarrier (m + 1) k) (codimFaces (m + 1) k) hlabel]
        exact mapped_good_family_card_of_map e label lowerLabel hcast
          (topCells m k)
          ((codimFaces (m + 1) k).filter
            (fun τ => Fin.last (m + 1) ∉ faceCarrier (m + 1) k τ))
          (lastFace_top_image m k).symm
      apply FiniteComplex.sperner_odd_of_boundary_odd
        (iterData (Fin ((m + 1) + 1)) k).complex (m + 1) label
        (fun τ => (faceCarrier (m + 1) k τ).card = m + 1)
      · intro τ hτ
        exact incidentTop_card_eq_if_boundary (Nat.succ_pos m) hτ
      · change Odd (((codimFaces (m + 1) k).filter
          (fun τ => τ.image label = spernerSmallLabels (m + 1) ∧
            (faceCarrier (m + 1) k τ).card = m + 1)).card)
        rw [hboundaryCard]
        exact ih lowerLabel hlower

/-- Each actual subdivision contains an actual fully labelled top cell. -/
theorem iterated_sperner_exists (m k : ℕ)
    (label : IterVertex m k → Fin (m + 1))
    (hlabel : ∀ v, label v ∈ iterCarrier m k v) :
    ∃ σ, σ ∈ topCells m k ∧ σ.image label = Finset.univ := by
  classical
  have hodd := iterated_sperner_odd m k label hlabel
  have hcard : ((topCells m k).filter
      (fun σ => σ.image label = Finset.univ)).card ≠ 0 := by
    intro hzero
    rw [hzero] at hodd
    simp at hodd
  obtain ⟨σ, hσ⟩ := Finset.card_ne_zero.mp hcard
  exact ⟨σ, (Finset.mem_filter.mp hσ).1, (Finset.mem_filter.mp hσ).2⟩

end Tingley

end OAI

-- Adapted from OAI.Analysis.SphereIsometry.SimplexFixedPoint

namespace OAI

/-!
# Fixed points in finite probability simplexes

The finite-coordinate theorem constructs its approximating points from the actual iterated
subdivision and the proved Sperner theorem. Positive coordinates enforce the boundary condition
on labels. The shrinking mesh and the labelled inequalities then give an exact fixed point.
Coordinate reindexing transports the result to every nonempty finite index type.
-/

open Filter
open scoped Topology

namespace Tingley

/-- Every continuous self-map of a probability simplex with `m + 1` coordinates has a fixed
point. The construction includes `m = 0`, the one-point simplex. -/
theorem continuous_fin_probabilitySimplex_fixedPoint (m : ℕ)
    (P : ProbabilitySimplex (Fin (m + 1)) → ProbabilitySimplex (Fin (m + 1)))
    (hP : Continuous P) : ∃ a, P a = a := by
  classical
  let point : (k : ℕ) → IterVertex m k → ProbabilitySimplex (Fin (m + 1)) :=
    fun k v => ⟨iterPoint m k v, iterPoint_mem_stdSimplex m k v⟩
  let label : (k : ℕ) → IterVertex m k → Fin (m + 1) :=
    fun k v => Classical.choose
      (exists_positive_dominating_coordinate (point k v) (P (point k v)))
  have hlabel (k : ℕ) (v : IterVertex m k) :
      0 < (point k v).val (label k v) ∧
        (P (point k v)).val (label k v) ≤ (point k v).val (label k v) :=
    Classical.choose_spec
      (exists_positive_dominating_coordinate (point k v) (P (point k v)))
  have hcarrier (k : ℕ) (v : IterVertex m k) : label k v ∈ iterCarrier m k v :=
    (iterPoint_pos_iff m k v (label k v)).mp (hlabel k v).1
  have hcells (k : ℕ) :
      ∃ s, s ∈ topCells m k ∧ s.image (label k) = Finset.univ :=
    iterated_sperner_exists m k (label k) (hcarrier k)
  let cell (k : ℕ) : Finset (IterVertex m k) := Classical.choose (hcells k)
  have hcell_mem (k : ℕ) : cell k ∈ topCells m k :=
    (Classical.choose_spec (hcells k)).1
  have hcell_labels (k : ℕ) : (cell k).image (label k) = Finset.univ :=
    (Classical.choose_spec (hcells k)).2
  have hvertices (k : ℕ) (i : Fin (m + 1)) :
      ∃ v, v ∈ cell k ∧ label k v = i := by
    apply Finset.mem_image.mp
    rw [hcell_labels k]
    exact Finset.mem_univ i
  let vertex (k : ℕ) (i : Fin (m + 1)) : IterVertex m k :=
    Classical.choose (hvertices k i)
  have hvertex_mem (k : ℕ) (i : Fin (m + 1)) : vertex k i ∈ cell k :=
    (Classical.choose_spec (hvertices k i)).1
  have hvertex_label (k : ℕ) (i : Fin (m + 1)) : label k (vertex k i) = i :=
    (Classical.choose_spec (hvertices k i)).2
  let a : ℕ → Fin (m + 1) → ProbabilitySimplex (Fin (m + 1)) :=
    fun k i => point k (vertex k i)
  have hden : (0 : ℝ) < (m : ℝ) + 1 :=
    add_pos_of_nonneg_of_pos (Nat.cast_nonneg m) zero_lt_one
  have hq₀ : (0 : ℝ) ≤ (m : ℝ) / ((m : ℝ) + 1) :=
    div_nonneg (Nat.cast_nonneg m) hden.le
  have hq₁ : (m : ℝ) / ((m : ℝ) + 1) < 1 :=
    (div_lt_one hden).mpr (lt_add_of_pos_right (m : ℝ) zero_lt_one)
  apply probabilitySimplex_fixedPoint_of_shrinking_family P hP a
    (fun k => ((m : ℝ) / ((m : ℝ) + 1)) ^ k)
    (tendsto_pow_atTop_nhds_zero_of_lt_one hq₀ hq₁)
  · intro k i j
    change dist (iterPoint m k (vertex k i)) (iterPoint m k (vertex k j)) ≤
      ((m : ℝ) / ((m : ℝ) + 1)) ^ k
    rw [dist_eq_norm]
    exact iterPoint_mesh m k (cell k) (mem_topCells.mp (hcell_mem k)).1
      (vertex k i) (hvertex_mem k i) (vertex k j) (hvertex_mem k j)
  · intro k i
    change (P (point k (vertex k i))).val i ≤ (point k (vertex k i)).val i
    simpa only [hvertex_label k i] using (hlabel k (vertex k i)).2

/-- Every continuous self-map of a probability simplex indexed by a nonempty finite type has
a fixed point. All geometric and finite-incidence inputs are discharged by the finite theorem. -/
theorem continuous_probabilitySimplex_fixedPoint
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (P : ProbabilitySimplex ι → ProbabilitySimplex ι) (hP : Continuous P) :
    ∃ a, P a = a := by
  classical
  let m := Fintype.card ι - 1
  have hc : Fintype.card ι = m + 1 := by
    dsimp [m]
    exact (Nat.sub_add_cancel (Nat.succ_le_of_lt
      (Fintype.card_pos : 0 < Fintype.card ι))).symm
  let e : ι ≃ Fin (m + 1) := Fintype.equivFinOfCardEq hc
  let h := probabilitySimplexReindex e
  let Q : ProbabilitySimplex (Fin (m + 1)) → ProbabilitySimplex (Fin (m + 1)) :=
    fun b => h (P (h.symm b))
  have hQ : Continuous Q :=
    h.continuous.comp (hP.comp h.symm.continuous)
  obtain ⟨b, hb⟩ := continuous_fin_probabilitySimplex_fixedPoint m Q hQ
  refine ⟨h.symm b, ?_⟩
  simpa only [Q, Homeomorph.symm_apply_apply] using congrArg h.symm hb

end Tingley

end OAI

-- Adapted from OAI.Analysis.SphereIsometry.CompactApproximation

namespace OAI

/-!
# Finite-net approximate fixed points on a compact convex set

The coefficient map is the explicit normalization of the weights
`max (δ - dist (P i) y) 0`.  The simplex fixed point is applied to this
actual map composed with the actual barycenter and the given self-map.
-/

noncomputable section

namespace Tingley

open Set
open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι]

def compactNetWeight (P : ι → E) (δ : ℝ) (y : E) (i : ι) : ℝ :=
  max (δ - dist (P i) y) 0

def compactNetTotal (P : ι → E) (δ : ℝ) (y : E) : ℝ :=
  ∑ i, compactNetWeight P δ y i

def compactNetCoefficients (P : ι → E) (δ : ℝ) (y : E) (i : ι) : ℝ :=
  compactNetWeight P δ y i / compactNetTotal P δ y

omit [NormedSpace ℝ E] [Fintype ι] in
theorem compactNetWeight_nonneg (P : ι → E) (δ : ℝ) (y : E) (i : ι) :
    0 ≤ compactNetWeight P δ y i := le_max_right _ _

omit [NormedSpace ℝ E] [Fintype ι] in
theorem compactNetWeight_pos {P : ι → E} {δ : ℝ} {y : E} {i : ι}
    (hi : dist (P i) y < δ) : 0 < compactNetWeight P δ y i :=
  (sub_pos.mpr hi).trans_le (le_max_left _ _)

omit [NormedSpace ℝ E] in
theorem compactNetTotal_pos {P : ι → E} {δ : ℝ} {y : E}
    (hnet : ∃ i, dist (P i) y < δ) : 0 < compactNetTotal P δ y := by
  obtain ⟨i, hi⟩ := hnet
  apply Finset.sum_pos'
  · intro j _hj
    exact compactNetWeight_nonneg P δ y j
  · exact ⟨i, Finset.mem_univ i, compactNetWeight_pos hi⟩

omit [NormedSpace ℝ E] in
theorem compactNetCoefficients_nonneg {P : ι → E} {δ : ℝ} {y : E}
    (hnet : ∃ i, dist (P i) y < δ) (i : ι) :
    0 ≤ compactNetCoefficients P δ y i :=
  div_nonneg (compactNetWeight_nonneg P δ y i) (compactNetTotal_pos hnet).le

omit [NormedSpace ℝ E] in
theorem compactNetCoefficients_sum {P : ι → E} {δ : ℝ} {y : E}
    (hnet : ∃ i, dist (P i) y < δ) :
    ∑ i, compactNetCoefficients P δ y i = 1 := by
  unfold compactNetCoefficients
  simp only [div_eq_mul_inv, ← Finset.sum_mul]
  exact mul_inv_cancel₀ (compactNetTotal_pos hnet).ne'

omit [NormedSpace ℝ E] in
theorem compactNetCoefficients_pos {P : ι → E} {δ : ℝ} {y : E} {i : ι}
    (hnet : ∃ j, dist (P j) y < δ) (hi : dist (P i) y < δ) :
    0 < compactNetCoefficients P δ y i :=
  div_pos (compactNetWeight_pos hi) (compactNetTotal_pos hnet)

omit [NormedSpace ℝ E] in
theorem compactNetCoefficients_active {P : ι → E} {δ : ℝ} {y : E} {i : ι}
    (hi : 0 < compactNetCoefficients P δ y i) : dist (P i) y < δ := by
  by_contra h
  have hw : compactNetWeight P δ y i = 0 :=
    max_eq_right (sub_nonpos.mpr (le_of_not_gt h))
  simp only [compactNetCoefficients, hw, zero_div] at hi
  exact (lt_irrefl 0) hi

def compactNetCoefficientMap (P : ι → E) (δ : ℝ) {K : Set E}
    (hnet : ∀ y ∈ K, ∃ i, dist (P i) y < δ) : K → ProbabilitySimplex ι :=
  fun y => ⟨compactNetCoefficients P δ (y : E),
    compactNetCoefficients_nonneg (hnet y y.property),
    compactNetCoefficients_sum (hnet y y.property)⟩

omit [NormedSpace ℝ E] in
theorem continuous_compactNetCoefficientMap (P : ι → E) (δ : ℝ) {K : Set E}
    (hnet : ∀ y ∈ K, ∃ i, dist (P i) y < δ) :
    Continuous (compactNetCoefficientMap P δ hnet) := by
  have hw (i : ι) : Continuous (fun y : K => compactNetWeight P δ (y : E) i) :=
    (continuous_const.sub (continuous_const.dist continuous_subtype_val)).max continuous_const
  have hD : Continuous (fun y : K => compactNetTotal P δ (y : E)) :=
    continuous_finsetSum Finset.univ (fun i _hi => hw i)
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  exact (hw i).div₀ hD (fun y => (compactNetTotal_pos (hnet y y.property)).ne')

def compactNetBarycenter (P : ι → E) (a : ProbabilitySimplex ι) : E :=
  ∑ i, (a : ι → ℝ) i • P i

theorem compactNetBarycenter_mem {K : Set E} (hconv : Convex ℝ K)
    {P : ι → E} (hP : ∀ i, P i ∈ K) (a : ProbabilitySimplex ι) :
    compactNetBarycenter P a ∈ K :=
  hconv.sum_mem (fun i _hi => a.property.1 i) a.property.2 (fun i _hi => hP i)

theorem continuous_compactNetBarycenter (P : ι → E) :
    Continuous (compactNetBarycenter P) := by
  apply continuous_finsetSum Finset.univ
  intro i _hi
  exact ((continuous_apply i).comp continuous_subtype_val).smul continuous_const

/-- The normalized finite-net average is strictly less than the net radius
away from its argument. Zero weights are allowed. -/
theorem compactNet_sum_sub_lt {P : ι → E} {δ : ℝ} {y : E}
    (hnet : ∃ i, dist (P i) y < δ) :
    ‖(∑ i, compactNetCoefficients P δ y i • P i) - y‖ < δ := by
  have hs := compactNetCoefficients_sum hnet
  have hn := compactNetCoefficients_nonneg hnet
  have heq : (∑ i, compactNetCoefficients P δ y i • P i) - y =
      ∑ i, compactNetCoefficients P δ y i • (P i - y) := by
    simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hs, one_smul]
  have hle (i : ι) : compactNetCoefficients P δ y i * dist (P i) y ≤
      compactNetCoefficients P δ y i * δ := by
    by_cases hi : compactNetCoefficients P δ y i = 0
    · simp only [hi, zero_mul, le_refl]
    · have hip : 0 < compactNetCoefficients P δ y i :=
        lt_of_le_of_ne (hn i) (Ne.symm hi)
      exact (mul_lt_mul_of_pos_left (compactNetCoefficients_active hip) hip).le
  obtain ⟨i, hi⟩ := hnet
  have his : compactNetCoefficients P δ y i * dist (P i) y <
      compactNetCoefficients P δ y i * δ :=
    mul_lt_mul_of_pos_left hi (compactNetCoefficients_pos ⟨i, hi⟩ hi)
  calc
    ‖(∑ j, compactNetCoefficients P δ y j • P j) - y‖ =
        ‖∑ j, compactNetCoefficients P δ y j • (P j - y)‖ := congrArg norm heq
    _ ≤ ∑ j, ‖compactNetCoefficients P δ y j • (P j - y)‖ := norm_sum_le _ _
    _ = ∑ j, compactNetCoefficients P δ y j * dist (P j) y := by
      apply Finset.sum_congr rfl
      intro j _hj
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hn j), dist_eq_norm]
    _ < ∑ j, compactNetCoefficients P δ y j * δ :=
      Finset.sum_lt_sum (fun j _hj => hle j) ⟨i, Finset.mem_univ i, his⟩
    _ = δ := by rw [← Finset.sum_mul, hs, one_mul]

/-- The simplex theorem, applied to the actual normalized net weights,
produces approximate fixed points for any compact convex self-map. -/
theorem exists_approximate_fixedPoint_of_isCompact_convex
    {K : Set E} (hK : IsCompact K) (hne : K.Nonempty) (hconv : Convex ℝ K)
    {g : E → E} (hg : ContinuousOn g K) (hmap : MapsTo g K K)
    {δ : ℝ} (hδ : 0 < δ) : ∃ x ∈ K, ‖x - g x‖ < δ := by
  classical
  obtain ⟨S, hSK, hSfinite, hcover⟩ := hK.finite_cover_balls hδ
  let : Fintype S := hSfinite.fintype
  let P : S → E := Subtype.val
  have hnet : ∀ y ∈ K, ∃ i : S, dist (P i) y < δ := by
    intro y hy
    obtain ⟨p, hp⟩ := Set.mem_iUnion.mp (hcover hy)
    obtain ⟨hpS, hpy⟩ := Set.mem_iUnion.mp hp
    exact ⟨⟨p, hpS⟩, Metric.mem_ball'.mp hpy⟩
  obtain ⟨y₀, hy₀⟩ := hne
  obtain ⟨i₀, _hi₀⟩ := hnet y₀ hy₀
  let : Nonempty S := ⟨i₀⟩
  have hP : ∀ i, P i ∈ K := fun i => hSK i.property
  let bary : ProbabilitySimplex S → K :=
    fun a => ⟨compactNetBarycenter P a, compactNetBarycenter_mem hconv hP a⟩
  have hbary : Continuous bary := (continuous_compactNetBarycenter P).subtype_mk _
  let gK : K → K := hmap.restrict g K K
  have hgK : Continuous gK := hg.mapsToRestrict hmap
  let Q : ProbabilitySimplex S → ProbabilitySimplex S :=
    compactNetCoefficientMap P δ hnet ∘ gK ∘ bary
  have hQ : Continuous Q :=
    (continuous_compactNetCoefficientMap P δ hnet).comp (hgK.comp hbary)
  obtain ⟨a, ha⟩ := continuous_probabilitySimplex_fixedPoint Q hQ
  have hcoeff : (a : S → ℝ) = compactNetCoefficients P δ (g (bary a : E)) := by
    have hh := congrArg (fun z : ProbabilitySimplex S => (z : S → ℝ)) ha
    change compactNetCoefficients P δ (g (bary a : E)) = (a : S → ℝ) at hh
    exact hh.symm
  refine ⟨(bary a : E), (bary a).property, ?_⟩
  have happ := compactNet_sum_sub_lt (hnet (g (bary a : E)) (hmap (bary a).property))
  rw [← hcoeff] at happ
  exact happ

end Tingley

end

end OAI

-- Adapted from OAI.Analysis.SphereIsometry.CompactConvexFixedPoint

namespace OAI

/-!
# Compact convex fixed points

Finite-net approximate fixed points force the minimum of the continuous
displacement function to be zero. Ambient completeness is not required.
-/

noncomputable section

namespace Tingley

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
theorem exists_fixedPoint_of_isCompact_of_approximate
    {K : Set E} (hK : IsCompact K) (hne : K.Nonempty)
    {g : E → E} (hg : ContinuousOn g K)
    (happrox : ∀ δ : ℝ, 0 < δ → ∃ x ∈ K, ‖x - g x‖ < δ) :
    ∃ x ∈ K, g x = x := by
  have hd : ContinuousOn (fun x => ‖x - g x‖) K := (continuousOn_id.sub hg).norm
  obtain ⟨z, hz, hmin⟩ := hK.exists_isMinOn hne hd
  have hzero : ‖z - g z‖ = 0 := by
    by_contra hnezero
    have hpos : 0 < ‖z - g z‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm hnezero)
    obtain ⟨x, hx, hsmall⟩ := happrox ‖z - g z‖ hpos
    exact (not_lt_of_ge ((isMinOn_iff.mp hmin) x hx)) hsmall
  exact ⟨z, hz, (sub_eq_zero.mp (norm_eq_zero.mp hzero)).symm⟩

/-- The compact-convex fixed-point theorem, obtained from the explicit
finite-net coefficient map and the proved simplex theorem. -/
theorem exists_fixedPoint_of_isCompact_convex
    {K : Set E} (hK : IsCompact K) (hne : K.Nonempty) (hconv : Convex ℝ K)
    {g : E → E} (hg : ContinuousOn g K) (hmap : MapsTo g K K) :
    ∃ x ∈ K, g x = x := by
  apply exists_fixedPoint_of_isCompact_of_approximate hK hne hg
  intro δ hδ
  exact exists_approximate_fixedPoint_of_isCompact_convex hK hne hconv hg hmap hδ

/-- An explicit ambient representative of a subtype self-map. Its values
outside the subtype are immaterial; only continuity on that subtype is used. -/
def extendSelfMap {K : Set E} (g : K → K) (x : E) : E := by
  classical
  exact if hx : x ∈ K then (g ⟨x, hx⟩ : E) else x

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem extendSelfMap_of_mem {K : Set E} (g : K → K) {x : E} (hx : x ∈ K) :
    extendSelfMap g x = (g ⟨x, hx⟩ : E) := by
  simp only [extendSelfMap, dif_pos hx]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
@[simp] theorem extendSelfMap_coe {K : Set E} (g : K → K) (x : K) :
    extendSelfMap g (x : E) = (g x : E) :=
  extendSelfMap_of_mem g x.property

end Tingley

end

end OAI

-- Adapted from OAI.Analysis.SphereIsometry.CoefficientBins

namespace OAI

/-!
# Finite bins for probability coefficients

An integer floor grid partitions the coefficient simplex into finitely many
parts of arbitrarily small l1 diameter. The proof uses only the Archimedean
property and finite sums, and also applies when the coefficient index is empty.
-/

open scoped BigOperators

namespace Tingley

/-- Nonnegative coefficients with total mass one. -/
def CoefficientSimplex (n : ℕ) : Set (Fin n → ℝ) :=
  {w | (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1}

private theorem coefficient_le_one {n : ℕ} {w : Fin n → ℝ}
    (hw : w ∈ CoefficientSimplex n) (i : Fin n) : w i ≤ 1 := by
  calc
    w i ≤ ∑ j, w j :=
      Finset.single_le_sum (fun j _ => hw.1 j) (Finset.mem_univ i)
    _ = 1 := hw.2

private theorem abs_sub_lt_of_same_floor {K a b : ℝ} {q : ℕ}
    (hK : 0 < K) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hqa : Nat.floor (K * a) = q) (hqb : Nat.floor (K * b) = q) :
    |a - b| < 1 / K := by
  have ha' := (Nat.floor_eq_iff (mul_nonneg hK.le ha)).mp hqa
  have hb' := (Nat.floor_eq_iff (mul_nonneg hK.le hb)).mp hqb
  have hab : a - b < 1 / K := by
    apply (lt_div_iff₀' hK).mpr
    nlinarith only [ha'.2, hb'.1]
  have hba : b - a < 1 / K := by
    apply (lt_div_iff₀' hK).mpr
    nlinarith only [hb'.2, ha'.1]
  exact abs_lt.mpr ⟨by linarith only [hba], hab⟩

/-- A finite family of coefficient bins with l1 diameter at most `η`.

The label type has `(K + 1)^n` elements. The last coordinate label retains
coefficients equal to one. For `n = 0`, the simplex and all bins are empty;
no nonemptiness hypothesis on the coefficient index is needed.
-/
theorem exists_coefficient_bins (n : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ K : ℕ, ∃ bins : (Fin n → Fin (K + 1)) → Set (Fin n → ℝ),
      (∀ w ∈ CoefficientSimplex n, ∃ q, w ∈ bins q) ∧
      (∀ q, ∀ w ∈ bins q, ∀ v ∈ bins q, ∑ i, |w i - v i| ≤ η) := by
  obtain ⟨K, hgrid⟩ := exists_nat_gt ((n : ℝ) / η)
  have hK : (0 : ℝ) < K :=
    lt_of_le_of_lt (div_nonneg (Nat.cast_nonneg n) hη.le) hgrid
  have hsmall : (n : ℝ) / K < η := by
    apply (div_lt_iff₀ hK).mpr
    simpa only [mul_comm] using (div_lt_iff₀ hη).mp hgrid
  let bins : (Fin n → Fin (K + 1)) → Set (Fin n → ℝ) := fun q =>
    {w | w ∈ CoefficientSimplex n ∧
      ∀ i, Nat.floor ((K : ℝ) * w i) = (q i).val}
  refine ⟨K, bins, ?_, ?_⟩
  · intro w hw
    have hcode (i : Fin n) : Nat.floor ((K : ℝ) * w i) < K + 1 := by
      apply Nat.lt_succ_of_le
      apply Nat.floor_le_of_le
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (coefficient_le_one hw i) hK.le
    let q : Fin n → Fin (K + 1) := fun i =>
      ⟨Nat.floor ((K : ℝ) * w i), hcode i⟩
    refine ⟨q, ?_⟩
    change w ∈ CoefficientSimplex n ∧
      ∀ i, Nat.floor ((K : ℝ) * w i) = (q i).val
    exact ⟨hw, fun _ => rfl⟩
  · intro q w hw v hv
    change (w ∈ CoefficientSimplex n ∧
      ∀ i, Nat.floor ((K : ℝ) * w i) = (q i).val) at hw
    change (v ∈ CoefficientSimplex n ∧
      ∀ i, Nat.floor ((K : ℝ) * v i) = (q i).val) at hv
    have hcoord (i : Fin n) : |w i - v i| < 1 / (K : ℝ) :=
      abs_sub_lt_of_same_floor hK (hw.1.1 i) (hv.1.1 i) (hw.2 i) (hv.2 i)
    calc
      ∑ i, |w i - v i| ≤ ∑ _i : Fin n, 1 / (K : ℝ) :=
        Finset.sum_le_sum (fun i _ => (hcoord i).le)
      _ = (n : ℝ) / K := by
        rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul, mul_one_div]
      _ ≤ η := hsmall.le

end Tingley

end OAI

-- Adapted from OAI.Analysis.SphereIsometry.ConvexCoverRegroup

namespace OAI

/-!
# Regrouping a convex hull over a finite cover

For a finite family of nonempty sets, every point in the convex hull of their
union is a convex combination with one point from each individual convex hull.
The proof establishes convexity of the represented set. Zero coefficients are
handled by choosing points inside the corresponding sets, without assuming
that those sets contain the origin.
-/

namespace Tingley

open scoped BigOperators

variable {E ι : Type*} [AddCommGroup E] [Module ℝ E] [Fintype ι]

/-- Points represented by probability weights and one point in each member of
a finite family of sets. Membership is required even at zero-weight indices. -/
def finiteMixtures (B : ι → Set E) : Set E :=
  {x | ∃ (w : ι → ℝ) (z : ι → E),
    (∀ i, 0 ≤ w i) ∧ (∑ i, w i) = 1 ∧
    (∀ i, z i ∈ B i) ∧ (∑ i, w i • z i) = x}

/-- Mixing probability-weighted representations preserves representation when
each coordinate set is convex. No nonemptiness premise is needed here. -/
theorem convex_finiteMixtures (B : ι → Set E) (hB : ∀ i, Convex ℝ (B i)) :
    Convex ℝ (finiteMixtures B) := by
  classical
  rintro x ⟨wx, zx, hwx, hwxsum, hzx, hx⟩
    y ⟨wy, zy, hwy, hwysum, hzy, hy⟩ a b ha hb hab
  have hex (i : ι) :
      ∃ u ∈ B i, (a * wx i + b * wy i) • u =
        (a * wx i) • zx i + (b * wy i) • zy i :=
    (hB i).exists_mem_add_smul_eq (hzx i) (hzy i)
      (mul_nonneg ha (hwx i)) (mul_nonneg hb (hwy i))
  choose u hu hueq using hex
  refine ⟨fun i => a * wx i + b * wy i, u, ?_, ?_, hu, ?_⟩
  · intro i
    exact add_nonneg (mul_nonneg ha (hwx i)) (mul_nonneg hb (hwy i))
  · calc
      (∑ i, (a * wx i + b * wy i)) =
          a * (∑ i, wx i) + b * (∑ i, wy i) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ = 1 := by simp only [hwxsum, hwysum, mul_one, hab]
  · calc
      (∑ i, (a * wx i + b * wy i) • u i) =
          ∑ i, ((a * wx i) • zx i + (b * wy i) • zy i) :=
        Finset.sum_congr rfl fun i _ => hueq i
      _ = a • (∑ i, wx i • zx i) + b • (∑ i, wy i • zy i) := by
        simp only [Finset.sum_add_distrib, mul_smul, Finset.smul_sum]
      _ = a • x + b • y := by rw [hx, hy]

/-- Regroup a point of a convex hull along an arbitrary finite cover by
nonempty sets. Cover members may be infinite, overlapping, or nonclosed. -/
theorem convexHull_cover_representation
    (H : Set E) (A : ι → Set E)
    (hne : ∀ i, (A i).Nonempty)
    (hcover : ∀ x ∈ H, ∃ i, x ∈ A i)
    {x : E} (hx : x ∈ convexHull ℝ H) :
    ∃ (w : ι → ℝ) (z : ι → E),
      (∀ i, 0 ≤ w i) ∧ (∑ i, w i) = 1 ∧
      (∀ i, z i ∈ convexHull ℝ (A i)) ∧
      (∑ i, w i • z i) = x := by
  classical
  choose base hbase using hne
  have hcontains : H ⊆ finiteMixtures (fun i => convexHull ℝ (A i)) := by
    intro y hy
    obtain ⟨j, hj⟩ := hcover y hy
    refine ⟨fun i => if i = j then 1 else 0,
      fun i => if i = j then y else base i, ?_, ?_, ?_, ?_⟩
    · intro i
      by_cases hij : i = j <;> simp [hij]
    · simp
    · intro i
      by_cases hij : i = j
      · subst i
        simpa only [if_pos rfl, ite_true] using subset_convexHull ℝ (A j) hj
      · simpa only [if_neg hij] using subset_convexHull ℝ (A i) (hbase i)
    · rw [Finset.sum_eq_single_of_mem j (Finset.mem_univ j)]
      · simp
      · intro i _ hij
        simp [hij]
  exact convexHull_min hcontains
    (convex_finiteMixtures _ fun i => convex_convexHull ℝ (A i)) hx

end Tingley

end OAI

-- Adapted from OAI.Analysis.SphereIsometry.KuratowskiConvexHull

namespace OAI

/-! # Convex-hull invariance of the Kuratowski measure

Finite coefficient bins give actual finite covers of a convex hull. Cover
pieces are first intersected with the bounded original set; empty pieces are
replaced by a singleton from that set. Thus every coordinate has a valid point,
including coordinates with zero weight, and one norm bound controls all pieces.
-/

namespace Tingley

open scoped BigOperators

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

/-- A diameter bound and a coefficient `l1` bound control finite mixtures. -/
theorem dist_weighted_mixtures_le {ι : Type*} [Fintype ι]
    (w v : ι → ℝ) (z u : ι → E) (δ R η : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hmass : (∑ i, w i) = 1)
    (hdiam : ∀ i, dist (z i) (u i) ≤ δ)
    (hnorm : ∀ i, ‖u i‖ ≤ R) (hR : 0 ≤ R)
    (hcoeff : (∑ i, |w i - v i|) ≤ η) :
    dist (∑ i, w i • z i) (∑ i, v i • u i) ≤ δ + R * η := by
  have hterm (i : ι) :
      ‖w i • z i - v i • u i‖ ≤ w i * δ + |w i - v i| * R := by
    calc
      ‖w i • z i - v i • u i‖ =
          ‖w i • (z i - u i) + (w i - v i) • u i‖ := by
        rw [smul_sub, sub_smul, sub_add_sub_cancel]
      _ ≤ ‖w i • (z i - u i)‖ + ‖(w i - v i) • u i‖ := norm_add_le _ _
      _ = w i * dist (z i) (u i) + |w i - v i| * ‖u i‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg (hw i),
          Real.norm_eq_abs, ← dist_eq_norm]
      _ ≤ w i * δ + |w i - v i| * R :=
        add_le_add (mul_le_mul_of_nonneg_left (hdiam i) (hw i))
          (mul_le_mul_of_nonneg_left (hnorm i) (abs_nonneg _))
  calc
    dist (∑ i, w i • z i) (∑ i, v i • u i) =
        ‖∑ i, (w i • z i - v i • u i)‖ := by
      rw [dist_eq_norm, Finset.sum_sub_distrib]
    _ ≤ ∑ i, ‖w i • z i - v i • u i‖ := norm_sum_le _ _
    _ ≤ ∑ i, (w i * δ + |w i - v i| * R) :=
      Finset.sum_le_sum fun i _ => hterm i
    _ = (∑ i, w i) * δ + (∑ i, |w i - v i|) * R := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
    _ = δ + R * (∑ i, |w i - v i|) := by
      rw [hmass, one_mul, mul_comm (∑ i, |w i - v i|) R]
    _ ≤ δ + R * η :=
      add_le_add_right (mul_le_mul_of_nonneg_left hcoeff hR) δ

/-- Construct a finite convex-hull cover with arbitrarily small coefficient
error, using a fixed norm bound on the original set. -/
theorem finiteDiameterCover_convexHull_of_norm_le
    {H : Set E} {δ R η : ℝ}
    (hδ : 0 ≤ δ) (hR : 0 ≤ R) (hη : 0 < η)
    (hnorm : ∀ x ∈ H, ‖x‖ ≤ R) (hc : FiniteDiameterCover H δ) :
    FiniteDiameterCover (convexHull ℝ H) (δ + R * η) := by
  classical
  by_cases hH : H.Nonempty
  · obtain ⟨x₀, hx₀⟩ := hH
    obtain ⟨n, U, hcover, hdiam⟩ := hc
    let A : Fin n → Set E := fun i =>
      if (U i ∩ H).Nonempty then U i ∩ H else {x₀}
    have hne (i : Fin n) : (A i).Nonempty := by
      by_cases hi : (U i ∩ H).Nonempty
      · simpa only [A, if_pos hi] using hi
      · simp only [A, if_neg hi, Set.singleton_nonempty]
    have hsub (i : Fin n) : A i ⊆ H := by
      intro x hx
      by_cases hi : (U i ∩ H).Nonempty
      · have hx' : x ∈ U i ∩ H := by simpa only [A, if_pos hi] using hx
        exact hx'.2
      · have hx' : x = x₀ := by
          simpa only [A, if_neg hi, Set.mem_singleton_iff] using hx
        simpa only [hx'] using hx₀
    have hAdiam (i : Fin n) : DiameterLE (A i) δ := by
      intro x hx y hy
      by_cases hi : (U i ∩ H).Nonempty
      · have hx' : x ∈ U i ∩ H := by simpa only [A, if_pos hi] using hx
        have hy' : y ∈ U i ∩ H := by simpa only [A, if_pos hi] using hy
        exact hdiam i x hx'.1 y hy'.1
      · have hx' : x = x₀ := by
          simpa only [A, if_neg hi, Set.mem_singleton_iff] using hx
        have hy' : y = x₀ := by
          simpa only [A, if_neg hi, Set.mem_singleton_iff] using hy
        simpa only [hx', hy', dist_self] using hδ
    have hAcover : ∀ x ∈ H, ∃ i, x ∈ A i := by
      intro x hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover hx)
      have hni : (U i ∩ H).Nonempty := ⟨x, hi, hx⟩
      exact ⟨i, by simpa only [A, if_pos hni] using (show x ∈ U i ∩ H from ⟨hi, hx⟩)⟩
    have hAnorm (i : Fin n) {x : E} (hx : x ∈ convexHull ℝ (A i)) : ‖x‖ ≤ R :=
      norm_le_of_mem_convexHull (fun y hy => hnorm y (hsub i hy)) hx
    obtain ⟨K, bins, hbins_cover, hbins_diam⟩ := exists_coefficient_bins n η hη
    let B : (Fin n → Fin (K + 1)) → Set E := fun q =>
      {x | ∃ (w : Fin n → ℝ) (z : Fin n → E),
        w ∈ bins q ∧ (∀ i, 0 ≤ w i) ∧ (∑ i, w i) = 1 ∧
        (∀ i, z i ∈ convexHull ℝ (A i)) ∧ (∑ i, w i • z i) = x}
    apply FiniteDiameterCover.of_fintype B
    · intro x hx
      obtain ⟨w, z, hw, hsum, hz, hrepr⟩ :=
        convexHull_cover_representation H A hne hAcover hx
      obtain ⟨q, hq⟩ := hbins_cover w ⟨hw, hsum⟩
      exact Set.mem_iUnion.mpr ⟨q, w, z, hq, hw, hsum, hz, hrepr⟩
    · intro q x hx y hy
      obtain ⟨w, z, hwbin, hw, hwsum, hz, hxrepr⟩ := hx
      obtain ⟨v, u, hvbin, hv, hvsum, hu, hyrepr⟩ := hy
      rw [← hxrepr, ← hyrepr]
      exact dist_weighted_mixtures_le w v z u δ R η hw hwsum
        (fun i => (hAdiam i).convexHull (z i) (hz i) (u i) (hu i))
        (fun i => hAnorm i (hu i)) hR (hbins_diam q w hwbin v hvbin)
  · have hHe : H = ∅ := Set.not_nonempty_iff_eq_empty.mp hH
    simpa only [hHe, convexHull_empty] using
      (FiniteDiameterCover.empty (E := E) (δ + R * η))

/-- Convexification preserves the Kuratowski measure of every bounded set. -/
theorem chi_convexHull {H : Set E} (hH : Bornology.IsBounded H) :
    chi (convexHull ℝ H) = chi H := by
  apply le_antisymm
  · obtain ⟨R, hR, hnorm⟩ := hH.exists_pos_norm_le
    apply le_csInf (coverRadii_nonempty hH)
    intro δ hδ
    apply le_of_forall_pos_le_add
    intro ε hε
    have hc := finiteDiameterCover_convexHull_of_norm_le hδ.1.le hR.le
      (div_pos hε hR) hnorm hδ.2
    have hrad : δ + R * (ε / R) = δ + ε := by
      rw [mul_div_cancel₀ ε hR.ne']
    have hb := chi_le_of_cover (add_nonneg hδ.1.le
      (mul_nonneg hR.le (div_pos hε hR).le)) hc
    simpa only [hrad] using hb
  · exact chi_mono (isBounded_convexHull.mpr hH) (subset_convexHull ℝ H)

/-- Taking the closed convex hull also preserves the Kuratowski measure. -/
theorem chi_closedConvexHull {H : Set E} (hH : Bornology.IsBounded H) :
    chi (closure (convexHull ℝ H)) = chi H := by
  rw [chi_closure (isBounded_convexHull.mpr hH), chi_convexHull hH]

end Tingley

end OAI

-- Adapted from OAI.Analysis.SphereIsometry.CondensingIteration

namespace OAI

/-!
# The closed-convex image iteration

Starting from a closed convex invariant set `C`, the actual successor set is
the closure of the convex hull of its image under `g`. All boundedness claims
come from containment in `C`. No boundedness-preservation property of an
arbitrary continuous map is used.
-/

noncomputable section

namespace Tingley

open Set Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The literal closed-convex image operator used in the condensing argument. -/
def condensingStep (g : E → E) (H : Set E) : Set E :=
  closure (convexHull ℝ (g '' H))

/-- The iteration begins at `C` and takes actual closed-convex images. -/
def condensingSequence (C : Set E) (g : E → E) : ℕ → Set E
  | 0 => C
  | n + 1 => condensingStep g (condensingSequence C g n)

@[simp] theorem condensingSequence_zero (C : Set E) (g : E → E) :
    condensingSequence C g 0 = C := rfl

@[simp] theorem condensingSequence_succ (C : Set E) (g : E → E) (n : ℕ) :
    condensingSequence C g (n + 1) = condensingStep g (condensingSequence C g n) := rfl

theorem condensingStep_mono (g : E → E) : Monotone (condensingStep g) := by
  intro H J hHJ
  exact closure_mono (convexHull_mono (image_mono hHJ))

theorem image_subset_condensingStep (g : E → E) (H : Set E) :
    g '' H ⊆ condensingStep g H :=
  (subset_convexHull ℝ (g '' H)).trans subset_closure

theorem condensingStep_subset {C : Set E} {g : E → E}
    (hclosed : IsClosed C) (hconv : Convex ℝ C) (hmap : MapsTo g C C) :
    condensingStep g C ⊆ C := by
  apply closure_minimal _ hclosed
  apply convexHull_min _ hconv
  rintro y ⟨x, hx, rfl⟩
  exact hmap hx

theorem condensingSequence_succ_subset {C : Set E} {g : E → E}
    (hclosed : IsClosed C) (hconv : Convex ℝ C) (hmap : MapsTo g C C) (n : ℕ) :
    condensingSequence C g (n + 1) ⊆ condensingSequence C g n := by
  induction n with
  | zero => exact condensingStep_subset hclosed hconv hmap
  | succ n ih => exact condensingStep_mono g ih

theorem condensingSequence_antitone {C : Set E} {g : E → E}
    (hclosed : IsClosed C) (hconv : Convex ℝ C) (hmap : MapsTo g C C) :
    Antitone (condensingSequence C g) :=
  antitone_nat_of_succ_le (condensingSequence_succ_subset hclosed hconv hmap)

theorem condensingSequence_subset {C : Set E} {g : E → E}
    (hclosed : IsClosed C) (hconv : Convex ℝ C) (hmap : MapsTo g C C) (n : ℕ) :
    condensingSequence C g n ⊆ C :=
  condensingSequence_antitone hclosed hconv hmap (Nat.zero_le n)

/-- Every image point belongs to the next set, before using antitonicity. -/
theorem condensingSequence_image_subset_succ (C : Set E) (g : E → E) (n : ℕ) :
    g '' condensingSequence C g n ⊆ condensingSequence C g (n + 1) :=
  image_subset_condensingStep g (condensingSequence C g n)

theorem condensingSequence_nonempty {C : Set E} (g : E → E)
    (hne : C.Nonempty) (n : ℕ) : (condensingSequence C g n).Nonempty := by
  induction n with
  | zero => exact hne
  | succ n ih =>
      obtain ⟨x, hx⟩ := ih
      exact ⟨g x, condensingSequence_image_subset_succ C g n (mem_image_of_mem g hx)⟩

theorem condensingSequence_isClosed {C : Set E} (g : E → E)
    (hclosed : IsClosed C) (n : ℕ) : IsClosed (condensingSequence C g n) := by
  cases n with
  | zero => exact hclosed
  | succ n => exact isClosed_closure

theorem condensingSequence_convex {C : Set E} (g : E → E)
    (hconv : Convex ℝ C) (n : ℕ) : Convex ℝ (condensingSequence C g n) := by
  cases n with
  | zero => exact hconv
  | succ n => exact (convex_convexHull ℝ (g '' condensingSequence C g n)).closure

theorem condensingSequence_isBounded {C : Set E} {g : E → E}
    (hclosed : IsClosed C) (hconv : Convex ℝ C) (hmap : MapsTo g C C)
    (hbounded : Bornology.IsBounded C) (n : ℕ) :
    Bornology.IsBounded (condensingSequence C g n) :=
  hbounded.subset (condensingSequence_subset hclosed hconv hmap n)

theorem condensingSequence_mapsTo {C : Set E} {g : E → E}
    (hclosed : IsClosed C) (hconv : Convex ℝ C) (hmap : MapsTo g C C) (n : ℕ) :
    MapsTo g (condensingSequence C g n) (condensingSequence C g n) := by
  intro x hx
  exact condensingSequence_succ_subset hclosed hconv hmap n
    (condensingSequence_image_subset_succ C g n (mem_image_of_mem g hx))

theorem condensingSequence_image_subset {C : Set E} {g : E → E}
    (hclosed : IsClosed C) (hconv : Convex ℝ C) (hmap : MapsTo g C C) (n : ℕ) :
    g '' condensingSequence C g n ⊆ C := by
  rintro y ⟨x, hx, rfl⟩
  exact hmap (condensingSequence_subset hclosed hconv hmap n hx)

theorem condensingSequence_image_isBounded {C : Set E} {g : E → E}
    (hclosed : IsClosed C) (hconv : Convex ℝ C) (hmap : MapsTo g C C)
    (hbounded : Bornology.IsBounded C) (n : ℕ) :
    Bornology.IsBounded (g '' condensingSequence C g n) :=
  hbounded.subset (condensingSequence_image_subset hclosed hconv hmap n)

/-- The hull step leaves the actual Kuratowski measure of its bounded image unchanged. -/
theorem condensingSequence_chi_succ_eq {C : Set E} {g : E → E}
    (hclosed : IsClosed C) (hconv : Convex ℝ C) (hmap : MapsTo g C C)
    (hbounded : Bornology.IsBounded C) (n : ℕ) :
    chi (condensingSequence C g (n + 1)) = chi (g '' condensingSequence C g n) := by
  exact chi_closedConvexHull
    (condensingSequence_image_isBounded hclosed hconv hmap hbounded n)

theorem condensingSequence_chi_succ_le {C : Set E} {g : E → E}
    (hclosed : IsClosed C) (hconv : Convex ℝ C) (hmap : MapsTo g C C)
    (hbounded : Bornology.IsBounded C) {γ : ℝ}
    (hχ : ∀ H : Set E, H ⊆ C → chi (g '' H) ≤ γ * chi H) (n : ℕ) :
    chi (condensingSequence C g (n + 1)) ≤ γ * chi (condensingSequence C g n) := by
  rw [condensingSequence_chi_succ_eq hclosed hconv hmap hbounded n]
  exact hχ _ (condensingSequence_subset hclosed hconv hmap n)

/-- Geometric decay allows `γ = 0`; no division by the contraction factor occurs. -/
theorem condensingSequence_chi_le {C : Set E} {g : E → E}
    (hclosed : IsClosed C) (hconv : Convex ℝ C) (hmap : MapsTo g C C)
    (hbounded : Bornology.IsBounded C) {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hχ : ∀ H : Set E, H ⊆ C → chi (g '' H) ≤ γ * chi H) (n : ℕ) :
    chi (condensingSequence C g n) ≤ γ ^ n * chi C := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        chi (condensingSequence C g (n + 1)) ≤ γ * chi (condensingSequence C g n) :=
          condensingSequence_chi_succ_le hclosed hconv hmap hbounded hχ n
        _ ≤ γ * (γ ^ n * chi C) := mul_le_mul_of_nonneg_left ih hγ0
        _ = γ ^ (n + 1) * chi C := by rw [pow_succ', mul_assoc]

theorem condensingSequence_chi_nonneg {C : Set E} {g : E → E}
    (hclosed : IsClosed C) (hconv : Convex ℝ C) (hmap : MapsTo g C C)
    (hbounded : Bornology.IsBounded C) (n : ℕ) :
    0 ≤ chi (condensingSequence C g n) :=
  chi_nonneg (condensingSequence_isBounded hclosed hconv hmap hbounded n)

/-- The actual sequence has Kuratowski measure tending to zero for `0 ≤ γ < 1`. -/
theorem condensingSequence_chi_tendsto_zero {C : Set E} {g : E → E}
    (hclosed : IsClosed C) (hconv : Convex ℝ C) (hmap : MapsTo g C C)
    (hbounded : Bornology.IsBounded C) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hχ : ∀ H : Set E, H ⊆ C → chi (g '' H) ≤ γ * chi H) :
    Tendsto (fun n => chi (condensingSequence C g n)) atTop (𝓝 0) := by
  apply squeeze_zero
    (condensingSequence_chi_nonneg hclosed hconv hmap hbounded)
    (condensingSequence_chi_le hclosed hconv hmap hbounded hγ0 hχ)
  simpa only [zero_mul] using
    (tendsto_pow_atTop_nhds_zero_of_lt_one hγ0 hγ1).mul_const (chi C)

end Tingley

end

end OAI

-- Adapted from OAI.Analysis.SphereIsometry.KuratowskiTotalBounded

namespace OAI

/-!
# Finite diameter covers and total boundedness

The Kuratowski cover predicate is equivalent to arbitrarily fine finite metric
covers. Its zero value characterizes total boundedness on bounded sets. A
selected point from each member of a nested family has totally bounded range
when sufficiently late members admit arbitrarily fine diameter covers.
-/

noncomputable section

open Set

namespace Tingley

universe u

variable {E : Type u} [PseudoMetricSpace E]

/-- Total boundedness is equivalent to finite pairwise-diameter covers at every
positive scale. No completeness or nonemptiness hypothesis is needed. -/
theorem totallyBounded_iff_finiteDiameterCover {H : Set E} :
    TotallyBounded H ↔ ∀ ε : ℝ, 0 < ε → FiniteDiameterCover H ε := by
  classical
  constructor
  · intro hH ε hε
    obtain ⟨t, ht, hcover⟩ :=
      Metric.totallyBounded_iff.mp hH (ε / 2) (half_pos hε)
    let : Fintype t := ht.fintype
    refine FiniteDiameterCover.of_fintype
      (fun c : t => Metric.ball (c : E) (ε / 2)) ?_ ?_
    · intro x hx
      obtain ⟨c, hct, hxc⟩ := Set.mem_iUnion₂.mp (hcover hx)
      exact Set.mem_iUnion.mpr ⟨⟨c, hct⟩, hxc⟩
    · intro c x hx y hy
      have hxy : dist x y < ε := calc
        dist x y ≤ dist x (c : E) + dist y (c : E) := dist_triangle_right _ _ _
        _ < ε / 2 + ε / 2 :=
          add_lt_add (Metric.mem_ball.mp hx) (Metric.mem_ball.mp hy)
        _ = ε := add_halves ε
      exact hxy.le
  · intro hcover
    apply Metric.totallyBounded_of_finite_discretization
    intro ε hε
    obtain ⟨n, A, hA, hdiam⟩ := hcover (ε / 2) (half_pos hε)
    have hmem : ∀ x : H, ∃ i : Fin n, (x : E) ∈ A i :=
      fun x => Set.mem_iUnion.mp (hA x.property)
    let label : H → Fin n := fun x => Classical.choose (hmem x)
    have hlabel : ∀ x : H, (x : E) ∈ A (label x) :=
      fun x => Classical.choose_spec (hmem x)
    refine ⟨ULift.{u} (Fin n), inferInstance,
      (fun x => ⟨label x⟩), ?_⟩
    intro x y hxy
    have heq : label x = label y :=
      congrArg (fun z : ULift.{u} (Fin n) => z.down) hxy
    have hy : (y : E) ∈ A (label x) := by
      rw [heq]
      exact hlabel y
    exact (hdiam (label x) (x : E) (hlabel x) (y : E) hy).trans_lt
      (half_lt_self hε)

/-- Cover the entire selected range by finitely many prefix singletons and a
small cover of a sufficiently late member. The cutoff may depend on the scale;
no fixed member of the original family is assumed totally bounded. -/
theorem totallyBounded_range_of_nested_finiteDiameterCover
    (C : ℕ → Set E) (hanti : Antitone C)
    (x : ℕ → E) (hx : ∀ n, x n ∈ C n)
    (hsmall : ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, FiniteDiameterCover (C N) ε) :
    TotallyBounded (Set.range x) := by
  classical
  apply totallyBounded_iff_finiteDiameterCover.mpr
  intro ε hε
  obtain ⟨N, k, A, hcover, hdiam⟩ := hsmall ε hε
  let B : Sum (Fin N) (Fin k) → Set E :=
    Sum.elim (fun i => {x (i : ℕ)}) A
  refine FiniteDiameterCover.of_fintype B ?_ ?_
  · rintro y ⟨n, rfl⟩
    by_cases hn : n < N
    · exact Set.mem_iUnion.mpr ⟨Sum.inl ⟨n, hn⟩, rfl⟩
    · have hxn : x n ∈ C N := hanti (Nat.le_of_not_gt hn) (hx n)
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover hxn)
      exact Set.mem_iUnion.mpr ⟨Sum.inr i, hi⟩
  · intro i
    cases i with
    | inl i =>
      change DiameterLE ({x (i : ℕ)} : Set E) ε
      intro y hy z hz
      rcases Set.mem_singleton_iff.mp hy with rfl
      rcases Set.mem_singleton_iff.mp hz with rfl
      simpa only [dist_self] using hε.le
    | inr i =>
      exact hdiam i

end Tingley

end

end OAI

-- Adapted from OAI.Analysis.SphereIsometry.KuratowskiNested

namespace OAI

/-!
# Nested sets with vanishing Kuratowski measure

Small finite diameter covers make the range of a selected sequence totally
bounded. Its compact closure supplies a point in all the nested closed sets.
The whole intersection is compact by its own arbitrarily fine finite covers.
-/

noncomputable section

open Filter Set
open scoped Topology

namespace Tingley

section Pseudometric

variable {E : Type*} [PseudoMetricSpace E] [CompleteSpace E]

/-- A nested sequence with arbitrarily fine finite diameter covers has a
nonempty compact intersection. No original member is assumed compact. -/
theorem nonempty_isCompact_iInter_of_finiteDiameterCover
    (C : ℕ → Set E) (hanti : Antitone C)
    (hne : ∀ n, (C n).Nonempty)
    (hclosed : ∀ n, IsClosed (C n))
    (hsmall : ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, FiniteDiameterCover (C N) ε) :
    (⋂ n, C n).Nonempty ∧ IsCompact (⋂ n, C n) := by
  classical
  let x : ℕ → E := fun n => Classical.choose (hne n)
  have hx : ∀ n, x n ∈ C n := fun n => Classical.choose_spec (hne n)
  have htotal : TotallyBounded (range x) :=
    totallyBounded_range_of_nested_finiteDiameterCover C hanti x hx hsmall
  let K : Set E := closure (range x)
  have hKclosed : IsClosed K := isClosed_closure
  have hKcompact : IsCompact K :=
    TotallyBounded.isCompact_of_isClosed htotal.closure hKclosed
  let D : ℕ → Set E := fun n => K ∩ C n
  have hDanti : ∀ n, D (n + 1) ⊆ D n := by
    intro n z hz
    exact ⟨hz.1, hanti (Nat.le_succ n) hz.2⟩
  have hDnonempty : ∀ n, (D n).Nonempty := by
    intro n
    exact ⟨x n, subset_closure (mem_range_self n), hx n⟩
  have hDclosed : ∀ n, IsClosed (D n) :=
    fun n => hKclosed.inter (hclosed n)
  have hDcompact : IsCompact (D 0) := hKcompact.inter_right (hclosed 0)
  have hnonempty : (⋂ n, C n).Nonempty := by
    obtain ⟨z, hz⟩ :=
      IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
        D hDanti hDnonempty hDcompact hDclosed
    refine ⟨z, mem_iInter.mpr ?_⟩
    intro n
    exact (mem_iInter.mp hz n).2
  have hinter : TotallyBounded (⋂ n, C n) := by
    apply totallyBounded_iff_finiteDiameterCover.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := hsmall ε hε
    exact hN.mono_set (fun z hz => mem_iInter.mp hz N)
  exact ⟨hnonempty,
    TotallyBounded.isCompact_of_isClosed hinter (isClosed_iInter hclosed)⟩

end Pseudometric

section Metric

variable {E : Type*} [MetricSpace E] [CompleteSpace E]

/-- A decreasing sequence of nonempty closed sets in a complete metric space
has a nonempty compact intersection when its Kuratowski measures tend to zero.
Boundedness of the first set supplies boundedness at every later index. -/
theorem nonempty_isCompact_iInter_of_chi_tendsto_zero
    (C : ℕ → Set E)
    (hanti : Antitone C)
    (hne : ∀ n, (C n).Nonempty)
    (hclosed : ∀ n, IsClosed (C n))
    (hbound : Bornology.IsBounded (C 0))
    (hchi : Tendsto (fun n => chi (C n)) atTop (𝓝 0)) :
    (⋂ n, C n).Nonempty ∧ IsCompact (⋂ n, C n) := by
  have hbounded : ∀ n, Bornology.IsBounded (C n) :=
    fun n => hbound.subset (hanti (Nat.zero_le n))
  apply nonempty_isCompact_iInter_of_finiteDiameterCover C hanti hne hclosed
  intro ε hε
  obtain ⟨N, hN⟩ := (hchi.eventually (gt_mem_nhds hε)).exists
  obtain ⟨δ, _hδ, hδε, hcover⟩ := exists_cover_of_chi_lt (hbounded N) hN
  exact ⟨N, hcover.mono_radius hδε.le⟩

end Metric

end Tingley

end

end OAI

-- Adapted from OAI.Analysis.SphereIsometry.CondensingFixedPoint

namespace OAI

/-!
# Fixed points from a Kuratowski contraction

The compact invariant set is the intersection of the actual iterated
closed-convex images. All of its required properties are proved from the
original closed bounded convex invariant set and the all-subsets estimate.
-/

noncomputable section

namespace Tingley

open Set Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A continuous self-map satisfying the actual all-subsets Kuratowski
contraction has a fixed point. No compactness premise on `C` is required. -/
theorem exists_fixedPoint_of_kuratowski_contraction
    {C : Set E} (hne : C.Nonempty) (hclosed : IsClosed C)
    (hbounded : Bornology.IsBounded C) (hconv : Convex ℝ C)
    {g : E → E} (hg : ContinuousOn g C) (hmap : MapsTo g C C)
    {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hχ : ∀ H : Set E, H ⊆ C → chi (g '' H) ≤ γ * chi H) :
    ∃ x ∈ C, g x = x := by
  let K : Set E := ⋂ n, condensingSequence C g n
  have hdecay := condensingSequence_chi_tendsto_zero hclosed hconv hmap hbounded hγ0 hγ1 hχ
  obtain ⟨hKne, hKcompact⟩ := nonempty_isCompact_iInter_of_chi_tendsto_zero
    (condensingSequence C g)
    (condensingSequence_antitone hclosed hconv hmap)
    (condensingSequence_nonempty g hne)
    (condensingSequence_isClosed g hclosed)
    hbounded hdecay
  have hKconv : Convex ℝ K := convex_iInter (condensingSequence_convex g hconv)
  have hKC : K ⊆ C := by
    intro x hx
    exact (mem_iInter.mp hx) 0
  have hKmap : MapsTo g K K := by
    intro x hx
    apply mem_iInter.mpr
    intro n
    exact condensingSequence_mapsTo hclosed hconv hmap n ((mem_iInter.mp hx) n)
  obtain ⟨x, hx, hfix⟩ := exists_fixedPoint_of_isCompact_convex hKcompact hKne hKconv
    (hg.mono hKC) hKmap
  exact ⟨x, hKC hx, hfix⟩

end Tingley

end

end OAI

-- Adapted from OAI.Analysis.SphereIsometry.ReturnMapFixedPoint

namespace OAI

/-!
# A fixed point from the return map's radius estimates

The finite-bin noncompactness estimate and the proved condensing fixed-point
theorem discharge the analytic step from the elementary geometric data.
Continuity is needed only on the actual invariant closed convex set.
-/

namespace Tingley

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [CompleteSpace X]

/-- The radius bounds and two-point estimate imply an actual fixed point.
The hypotheses contain neither a noncompactness estimate nor a fixed-point
principle: both are supplied by the preceding constructive proofs. -/
theorem exists_fixedPoint_of_return_estimate
    {C : Set X} {g : X → X} {p s u r : X → ℝ} {t M : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) (hM : 0 < M)
    (hCne : C.Nonempty) (hCclosed : IsClosed C)
    (hCb : Bornology.IsBounded C) (hCconvex : Convex ℝ C)
    (hg : ContinuousOn g C) (hgC : Set.MapsTo g C C)
    (hbounds : ∀ v ∈ C,
      (1 - t ≤ p v ∧ p v ≤ 1 + t) ∧
      (1 - t ≤ s v ∧ s v ≤ 1 + t) ∧
      (1 - t ≤ u v ∧ u v ≤ 1 + t) ∧
      (1 - t ≤ r v ∧ r v ≤ 1 + t))
    (hs : ∀ v ∈ C, s v = p v + M)
    (hr : ∀ v ∈ C, r v = u v + M)
    (hpair : ∀ v ∈ C, ∀ v' ∈ C,
      dist (g v) (g v') ≤
        (u v * p v / (r v * s v)) * dist v v' +
        2 * |u v - u v'| / r v +
        2 * u v * |p v - p v'| / (r v * s v)) :
    ∃ x ∈ C, g x = x := by
  have hfactor := return_contraction_factor_mem_Ico ht0 ht1 hM hCne
    (fun v hv => (hbounds v hv).1.1)
    (fun v hv => (hbounds v hv).2.1.2) hs
  apply exists_fixedPoint_of_kuratowski_contraction hCne hCclosed hCb
    hCconvex hg hgC hfactor.1 hfactor.2
  intro H hHC
  exact chi_return_image_le ht0 ht1 hM hCne hCb hgC hbounds hs hr hpair hHC

end Tingley

end OAI

-- Adapted from OAI.Analysis.SphereIsometry.AlignedConfiguration

namespace OAI

/-!
# Aligned sphere chords

The record retains the four actual endpoint equations. Its inverse exchanges the
endpoints and negates the two direction vectors literally; it uses no oddness
property of the sphere isometry.
-/

noncomputable section

namespace Tingley

universe u v

variable {X : Type u} {Y : Type v}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]

structure AlignedConfiguration
    (f : UnitSphere X ≃ᵢ UnitSphere Y) (y : UnitSphere X) (t M : ℝ) where
  x : UnitSphere X
  z : UnitSphere X
  v : UnitSphere X
  w : UnitSphere Y
  p : ℝ
  r : ℝ
  s : ℝ
  u : ℝ
  p_pos : 0 < p
  r_pos : 0 < r
  s_pos : 0 < s
  u_pos : 0 < u
  x_eq : (x : X) = t • (y : X) + p • (v : X)
  z_eq : (z : X) = t • (y : X) - r • (v : X)
  fx_eq : (f x : Y) = t • (f y : Y) + s • (w : Y)
  fz_eq : (f z : Y) = t • (f y : Y) - u • (w : Y)
  s_sub_p : s - p = M
  r_sub_u : r - u = M
  chord_sum : p + r = s + u
  chord_le_two : p + r ≤ 2

namespace AlignedConfiguration

variable {f : UnitSphere X ≃ᵢ UnitSphere Y} {y : UnitSphere X} {t M : ℝ}
variable (C : AlignedConfiguration f y t M)

def d : ℝ := C.p + C.r

def A : ℝ := C.p / C.d

def B : ℝ := C.u / C.d

theorem d_pos : 0 < C.d := add_pos C.p_pos C.r_pos

theorem d_ne_zero : C.d ≠ 0 := ne_of_gt C.d_pos

theorem d_eq_s_add_u : C.d = C.s + C.u := C.chord_sum

theorem A_pos : 0 < C.A := div_pos C.p_pos C.d_pos

theorem B_lt_one : C.B < 1 := by
  apply (div_lt_one C.d_pos).2
  rw [C.d_eq_s_add_u]
  linarith [C.s_pos]

theorem A_add_B : C.A + C.B = 1 - M / C.d := by
  dsimp only [A, B]
  rw [← add_div, eq_sub_iff_add_eq, ← add_div]
  have hsum : C.p + C.u + M = C.d := by
    dsimp only [d]
    linarith [C.r_sub_u]
  rw [hsum, div_self C.d_ne_zero]

theorem A_add_B_lt_one (hM : 0 < M) : C.A + C.B < 1 := by
  rw [C.A_add_B]
  have hMd := div_pos hM C.d_pos
  linarith

theorem one_sub_B : 1 - C.B = C.s / C.d := by
  apply (eq_div_iff C.d_ne_zero).2
  dsimp only [B]
  rw [sub_mul, one_mul, div_mul_cancel₀ _ C.d_ne_zero, C.d_eq_s_add_u]
  ring

theorem p_eq_d_mul_A : C.p = C.d * C.A := by
  simpa only [A, mul_comm] using (div_mul_cancel₀ C.p C.d_ne_zero).symm

theorem chord_identity : C.s * C.r - C.u * C.p = M * C.d := by
  calc
    C.s * C.r - C.u * C.p = (C.s - C.p) * C.r + C.p * (C.r - C.u) := by ring
    _ = M * C.r + C.p * M := by rw [C.s_sub_p, C.r_sub_u]
    _ = M * C.d := by dsimp only [d]; ring

/-- Exchange the endpoints and literally negate both chord directions. -/
def inverse : AlignedConfiguration f.symm (f y) t M where
  x := f C.z
  z := f C.x
  v := ⟨-(C.w : Y), by simp⟩
  w := ⟨-(C.v : X), by simp⟩
  p := C.u
  r := C.s
  s := C.r
  u := C.p
  p_pos := C.u_pos
  r_pos := C.s_pos
  s_pos := C.r_pos
  u_pos := C.p_pos
  x_eq := by simpa only [smul_neg, sub_eq_add_neg] using C.fz_eq
  z_eq := by simpa only [smul_neg, sub_neg_eq_add] using C.fx_eq
  fx_eq := by
    simpa only [IsometryEquiv.symm_apply_apply, smul_neg, sub_eq_add_neg] using C.z_eq
  fz_eq := by
    simpa only [IsometryEquiv.symm_apply_apply, smul_neg, sub_neg_eq_add] using C.x_eq
  s_sub_p := C.r_sub_u
  r_sub_u := C.s_sub_p
  chord_sum := by linarith [C.chord_sum]
  chord_le_two := by linarith [C.chord_sum, C.chord_le_two]

@[simp] theorem inverse_x : C.inverse.x = f C.z := rfl

@[simp] theorem inverse_z : C.inverse.z = f C.x := rfl

@[simp] theorem inverse_v_coe : (C.inverse.v : Y) = -(C.w : Y) := rfl

@[simp] theorem inverse_w_coe : (C.inverse.w : X) = -(C.v : X) := rfl

@[simp] theorem inverse_p : C.inverse.p = C.u := rfl

@[simp] theorem inverse_r : C.inverse.r = C.s := rfl

@[simp] theorem inverse_s : C.inverse.s = C.r := rfl

@[simp] theorem inverse_u : C.inverse.u = C.p := rfl

@[simp] theorem inverse_d : C.inverse.d = C.d := by
  change C.u + C.s = C.p + C.r
  linarith [C.chord_sum]

@[simp] theorem inverse_A : C.inverse.A = C.B := by
  simp only [A, B, inverse_p, inverse_d]

@[simp] theorem inverse_B : C.inverse.B = C.A := by
  simp only [A, B, inverse_u, inverse_d]

end AlignedConfiguration

end Tingley

end

end OAI

-- Adapted from OAI.Analysis.SphereIsometry.Alignment

namespace OAI

/-!
# Alignment from an attained positive defect

The actual positive schedule supplies the invariant convex set; the actual
return-map estimate and the proved fixed-point theorem supply its fixed point.
The original center and scalar remain unchanged throughout the construction.
-/

noncomputable section

namespace Tingley

variable {X Y : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- A fixed point of the genuine sphere return map gives the exact four chords. -/
def aligned_of_return_fixed
    (f : UnitSphere X ≃ᵢ UnitSphere Y) (y : UnitSphere X)
    (t M : ℝ) (ht : 0 < t ∧ t < 1) (hb : HasDefectBound f M)
    (v : UnitSphere X) (hv : v ∈ extremalSphere f y t ht M)
    (hfixed : returnSphere f y t ht v = v) : AlignedConfiguration f y t M where
  x := xPoint f y t ht v
  z := zPoint f y t ht v
  v := v
  w := wDirection f y t ht v
  p := pRadius f y t ht v
  r := rRadius f y t ht v
  s := sRadius f y t ht v
  u := uRadius f y t ht v
  p_pos := pRadius_pos f y t ht v
  r_pos := rRadius_pos f y t ht v
  s_pos := sRadius_pos f y t ht v
  u_pos := uRadius_pos f y t ht v
  x_eq := xPoint_eq f y t ht v
  z_eq := by simpa only [hfixed] using zPoint_eq f y t ht v
  fx_eq := fxPoint_eq f y t ht v
  fz_eq := fzPoint_eq f y t ht v
  s_sub_p := hv
  r_sub_u := (extremal_radius_identities f y t ht M hb hv).1
  chord_sum := (extremal_radius_identities f y t ht M hb hv).2.1
  chord_le_two := by
    calc
      pRadius f y t ht v + rRadius f y t ht v =
          ‖pRadius f y t ht v • (v : X) +
            rRadius f y t ht v • (returnSphere f y t ht v : X)‖ :=
        (extremal_radius_identities f y t ht M hb hv).2.2.symm
      _ = ‖(xPoint f y t ht v : X) - (zPoint f y t ht v : X)‖ :=
        (norm_xPoint_sub_zPoint f y t ht v).symm
      _ ≤ ‖(xPoint f y t ht v : X)‖ + ‖(zPoint f y t ht v : X)‖ := norm_sub_le _ _
      _ = 2 := by rw [UnitSphere.norm_coe, UnitSphere.norm_coe]; norm_num

/-- Alignment has no supplied invariant-set, contraction or fixed-point premise. -/
theorem exists_alignedConfiguration [CompleteSpace X]
    (f : UnitSphere X ≃ᵢ UnitSphere Y) (y x₀ : UnitSphere X)
    (t M : ℝ) (ht : 0 < t ∧ t < 1) (hM : 0 < M)
    (hb : HasDefectBound f M) (hatt : signedDefect f t x₀ y = M) :
    Nonempty (AlignedConfiguration f y t M) := by
  obtain ⟨C, hCne, hCclosed, hCb, hCconvex, hCE, hg, hgC⟩ :=
    exists_return_invariant_convex f y x₀ t M ht hb hatt
  have hbounds : ∀ v ∈ C,
      (1 - t ≤ pAmbient f y t ht v ∧ pAmbient f y t ht v ≤ 1 + t) ∧
      (1 - t ≤ sAmbient f y t ht v ∧ sAmbient f y t ht v ≤ 1 + t) ∧
      (1 - t ≤ uAmbient f y t ht v ∧ uAmbient f y t ht v ≤ 1 + t) ∧
      (1 - t ≤ rAmbient f y t ht v ∧ rAmbient f y t ht v ≤ 1 + t) := by
    intro v hv
    obtain ⟨a, _, rfl⟩ := hCE hv
    simpa only [pAmbient_coe, sAmbient_coe, uAmbient_coe, rAmbient_coe, Set.mem_Icc] using
      radii_bounds f y t ht a
  have hs : ∀ v ∈ C, sAmbient f y t ht v = pAmbient f y t ht v + M := by
    intro v hv
    obtain ⟨a, ha, rfl⟩ := hCE hv
    simpa only [sAmbient_coe, pAmbient_coe] using sRadius_eq_add f y t ht M ha
  have hr : ∀ v ∈ C, rAmbient f y t ht v = uAmbient f y t ht v + M := by
    intro v hv
    obtain ⟨a, ha, rfl⟩ := hCE hv
    simpa only [rAmbient_coe, uAmbient_coe] using rRadius_eq_add f y t ht M hb ha
  have hpair : ∀ v ∈ C, ∀ v' ∈ C,
      dist (returnAmbient f y t ht v) (returnAmbient f y t ht v') ≤
        (uAmbient f y t ht v * pAmbient f y t ht v /
          (rAmbient f y t ht v * sAmbient f y t ht v)) * dist v v' +
        2 * |uAmbient f y t ht v - uAmbient f y t ht v'| / rAmbient f y t ht v +
        2 * uAmbient f y t ht v * |pAmbient f y t ht v - pAmbient f y t ht v'| /
          (rAmbient f y t ht v * sAmbient f y t ht v) := by
    intro v hv v' hv'
    simpa only [dist_eq_norm] using
      returnAmbient_pair_estimate_on f y t ht M hb C hCE hv hv'
  obtain ⟨v, hv, hfixed⟩ := exists_fixedPoint_of_return_estimate
    ht.1 ht.2 hM hCne hCclosed hCb hCconvex hg hgC hbounds hs hr hpair
  obtain ⟨a, ha, rfl⟩ := hCE hv
  have hfixedSphere : returnSphere f y t ht a = a := by
    apply Subtype.ext
    simpa only [returnAmbient_coe] using hfixed
  exact ⟨aligned_of_return_fixed f y t M ht hb a ha hfixedSphere⟩

end Tingley

end

end OAI

-- Adapted from OAI.Analysis.SphereIsometry.ChordSecant

namespace OAI

/-! The secant estimate for every supporting functional of an aligned chord. -/

noncomputable section

namespace Tingley

variable {X Y : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- The lower support bound uses the actual unit endpoint, and holds for every
support at an earlier positive point of the same affine line. -/
theorem support_direction_lower {v y : X} {p t θ : ℝ}
    (hy : ‖y‖ = 1) (hp : 0 < p) (ht : 0 < t)
    (hθ : 0 < θ) (hθβ : θ ≤ t / p)
    (hx : ‖p • v + t • y‖ = 1)
    (φ : X →L[ℝ] ℝ) (hφ : SupportAt φ (v + θ • y)) :
    (1 - t) / p ≤ φ v := by
  have hpb : p * (t / p) = t := by field_simp [hp.ne']
  have hscale : p • (v + (t / p) • y) = p • v + t • y := by
    rw [smul_add, smul_smul, hpb]
  have hn : p * ‖v + (t / p) • y‖ = 1 := by
    rw [← norm_smul_of_nonneg hp.le, hscale, hx]
  have endpoint_lower : ∀ ψ : X →L[ℝ] ℝ,
      SupportAt ψ (v + (t / p) • y) → 1 - t ≤ p * ψ v := by
    intro ψ hψ
    have hyψ : ψ y ≤ 1 := by simpa only [hy] using apply_le_norm hψ.1 y
    have he := congrArg (fun a : ℝ => p * a) hψ.2
    simp only [map_add, map_smul, smul_eq_mul] at he
    rw [mul_add, ← mul_assoc, hpb, hn] at he
    have htψ := mul_le_mul_of_nonneg_left hyψ ht.le
    nlinarith
  apply (div_le_iff₀ hp).2
  rcases lt_or_eq_of_le hθβ with hlt | heq
  · obtain ⟨ψ, hψ⟩ := exists_support (v + (t / p) • y)
    have h₁ := apply_le_norm hφ.1 (v + (t / p) • y)
    have h₂ := apply_le_norm hψ.1 (v + θ • y)
    rw [← hψ.2] at h₁
    rw [← hφ.2] at h₂
    simp only [map_add, map_smul, smul_eq_mul] at h₁ h₂
    have hk : 0 ≤ ψ y - φ y := by
      by_contra hk
      have hprod := mul_neg_of_pos_of_neg (sub_pos.mpr hlt) (lt_of_not_ge hk)
      nlinarith
    have hprod := mul_nonneg hθ.le hk
    have hv : ψ v ≤ φ v := by nlinarith
    have hvp := mul_le_mul_of_nonneg_left hv hp.le
    have hend := endpoint_lower ψ hψ
    nlinarith
  · have hend := endpoint_lower φ (by simpa only [heq] using hφ)
    nlinarith

namespace AlignedConfiguration

variable {f : UnitSphere X ≃ᵢ UnitSphere Y} {y : UnitSphere X} {t M : ℝ}
variable (C : AlignedConfiguration f y t M)

def secantStep : ℝ := min (t / C.s) ((1 - t) / C.u)
def secantTheta : ℝ := C.secantStep * C.s / C.p
def secantSlope : ℝ :=
  (‖(C.r / C.u) • (C.v : X) + C.secantStep • (y : X)‖ -
    ‖(C.p / C.s) • (C.v : X) + C.secantStep • (y : X)‖) /
    (C.r / C.u - C.p / C.s)

theorem secantStep_pos (ht : 0 < t ∧ t < 1) : 0 < C.secantStep :=
  lt_min (div_pos ht.1 C.s_pos) (div_pos (sub_pos.mpr ht.2) C.u_pos)

theorem secantTheta_pos (ht : 0 < t ∧ t < 1) : 0 < C.secantTheta :=
  div_pos (mul_pos (C.secantStep_pos ht) C.s_pos) C.p_pos

theorem secantTheta_le (_ht : 0 < t ∧ t < 1) : C.secantTheta ≤ t / C.p := by
  apply (div_le_div_iff_of_pos_right C.p_pos).2
  calc
    C.secantStep * C.s ≤ (t / C.s) * C.s :=
      mul_le_mul_of_nonneg_right (min_le_left _ _) C.s_pos.le
    _ = t := div_mul_cancel₀ _ C.s_pos.ne'

theorem secant_denominator_pos (hM : 0 < M) : 0 < C.r / C.u - C.p / C.s := by
  have hid := C.chord_identity
  have hprod : 0 < M * C.d := mul_pos hM C.d_pos
  have hlt : C.p / C.s < C.r / C.u := by
    apply (div_lt_div_iff₀ C.s_pos C.u_pos).2
    nlinarith
  exact sub_pos.mpr hlt

theorem step_comparison_iff : t / C.s ≤ (1 - t) / C.u ↔ C.B ≤ 1 - t := by
  rw [div_le_div_iff₀ C.s_pos C.u_pos]
  change t * C.u ≤ (1 - t) * C.s ↔ C.u / C.d ≤ 1 - t
  rw [div_le_iff₀ C.d_pos]
  have hd : C.d = C.s + C.u := C.chord_sum
  rw [hd]
  constructor <;> intro h <;> nlinarith

theorem secantStep_eq_smallB (hB : C.B ≤ 1 - t) : C.secantStep = t / C.s :=
  min_eq_left ((C.step_comparison_iff).2 hB)

theorem secantStep_eq_largeB (_ht : 0 < t ∧ t < 1) (hB : 1 - t < C.B) :
    C.secantStep = (1 - t) / C.u := by
  apply min_eq_right
  exact (lt_of_not_ge fun h => (not_le_of_gt hB) ((C.step_comparison_iff).1 h)).le

theorem secant_radii_mem (ht : 0 < t ∧ t < 1) :
    t - C.s * C.secantStep ∈ Set.Icc (0 : ℝ) 1 ∧
      t + C.u * C.secantStep ∈ Set.Icc (0 : ℝ) 1 := by
  have hh := (C.secantStep_pos ht).le
  have hs := mul_le_mul_of_nonneg_right
    (show C.secantStep ≤ t / C.s from min_le_left _ _) C.s_pos.le
  have hu := mul_le_mul_of_nonneg_right
    (show C.secantStep ≤ (1 - t) / C.u from min_le_right _ _) C.u_pos.le
  rw [div_mul_cancel₀ _ C.s_pos.ne'] at hs
  rw [div_mul_cancel₀ _ C.u_pos.ne'] at hu
  have hsh := mul_nonneg C.s_pos.le hh
  have huh := mul_nonneg C.u_pos.le hh
  constructor <;> constructor <;> nlinarith [ht.1, ht.2]

theorem secant_defect_first :
    signedDefect f (t - C.s * C.secantStep) C.x y =
      C.s * (‖(C.w : Y) + C.secantStep • (f y : Y)‖ -
        ‖(C.p / C.s) • (C.v : X) + C.secantStep • (y : X)‖) := by
  have hsp : C.s * (C.p / C.s) = C.p := by field_simp [C.s_pos.ne']
  have hx : (C.x : X) - (t - C.s * C.secantStep) • (y : X) =
      C.s • ((C.p / C.s) • (C.v : X) + C.secantStep • (y : X)) := by
    rw [C.x_eq, smul_add, smul_smul, hsp]
    module
  have hfx : (f C.x : Y) - (t - C.s * C.secantStep) • (f y : Y) =
      C.s • ((C.w : Y) + C.secantStep • (f y : Y)) := by
    rw [C.fx_eq]
    module
  rw [signedDefect, hx, hfx, norm_smul_of_nonneg C.s_pos.le,
    norm_smul_of_nonneg C.s_pos.le]
  ring

theorem secant_defect_opposite :
    -signedDefect f (t + C.u * C.secantStep) C.z y =
      C.u * (‖(C.r / C.u) • (C.v : X) + C.secantStep • (y : X)‖ -
        ‖(C.w : Y) + C.secantStep • (f y : Y)‖) := by
  have hur : C.u * (C.r / C.u) = C.r := by field_simp [C.u_pos.ne']
  have hz : (C.z : X) - (t + C.u * C.secantStep) • (y : X) =
      -(C.u • ((C.r / C.u) • (C.v : X) + C.secantStep • (y : X))) := by
    rw [C.z_eq, smul_add, smul_smul, hur]
    module
  have hfz : (f C.z : Y) - (t + C.u * C.secantStep) • (f y : Y) =
      -(C.u • ((C.w : Y) + C.secantStep • (f y : Y))) := by
    rw [C.fz_eq]
    module
  rw [signedDefect, hz, hfz, norm_neg, norm_neg,
    norm_smul_of_nonneg C.u_pos.le, norm_smul_of_nonneg C.u_pos.le]
  ring

theorem secant_weighted_identity (hM : 0 < M) :
    M * C.secantSlope =
      (C.u * signedDefect f (t - C.s * C.secantStep) C.x y +
        C.s * (-signedDefect f (t + C.u * C.secantStep) C.z y)) / C.d := by
  rw [C.secant_defect_first, C.secant_defect_opposite]
  unfold secantSlope
  have hd : C.r / C.u - C.p / C.s = M * C.d / (C.u * C.s) := by
    have hid := C.chord_identity
    field_simp [C.u_pos.ne', C.s_pos.ne']
    nlinarith
  rw [hd]
  field_simp [hM.ne', C.d_pos.ne', C.u_pos.ne', C.s_pos.ne']
  ring

theorem secant_upper_smallB (hM : 0 < M) (ht : 0 < t ∧ t < 1)
    (hb : HasDefectBound f M) (hB : C.B ≤ 1 - t) :
    C.secantSlope ≤ 1 - C.B := by
  have hq := (C.secant_radii_mem ht).2
  have hd := (abs_le.mp (hb _ hq C.z y)).1
  have hz : t - C.s * C.secantStep = 0 := by
    rw [C.secantStep_eq_smallB hB]
    field_simp [C.s_pos.ne']
    ring
  have hi := C.secant_weighted_identity hM
  rw [hz, signedDefect_zero, mul_zero, zero_add] at hi
  have hle : C.s * (-signedDefect f (t + C.u * C.secantStep) C.z y) ≤
      C.s * M := mul_le_mul_of_nonneg_left (by linarith) C.s_pos.le
  have hi' := (eq_div_iff C.d_pos.ne').1 hi
  rw [C.one_sub_B]
  apply (le_div_iff₀ C.d_pos).2
  apply (mul_le_mul_iff_right₀ hM).mp
  calc
    M * (C.secantSlope * C.d) = (M * C.secantSlope) * C.d := by ring
    _ = C.s * (-signedDefect f (t + C.u * C.secantStep) C.z y) := hi'
    _ ≤ C.s * M := hle
    _ = M * C.s := mul_comm _ _

theorem secant_upper_largeB (hM : 0 < M) (ht : 0 < t ∧ t < 1)
    (hb : HasDefectBound f M) (hB : 1 - t < C.B) :
    C.secantSlope ≤ C.B := by
  have hq := (C.secant_radii_mem ht).1
  have hd := (abs_le.mp (hb _ hq C.x y)).2
  have ho : t + C.u * C.secantStep = 1 := by
    rw [C.secantStep_eq_largeB ht hB]
    field_simp [C.u_pos.ne']
    ring
  have hi := C.secant_weighted_identity hM
  rw [ho, signedDefect_one, neg_zero, mul_zero, add_zero] at hi
  have hle := mul_le_mul_of_nonneg_left hd C.u_pos.le
  have hi' := (eq_div_iff C.d_pos.ne').1 hi
  change C.secantSlope ≤ C.u / C.d
  apply (le_div_iff₀ C.d_pos).2
  apply (mul_le_mul_iff_right₀ hM).mp
  calc
    M * (C.secantSlope * C.d) = (M * C.secantSlope) * C.d := by ring
    _ = C.u * signedDefect f (t - C.s * C.secantStep) C.x y := hi'
    _ ≤ C.u * M := hle
    _ = M * C.u := mul_comm _ _

/-- No support is selected in this statement: it applies to every norm-bounded
functional norming the displayed vector, including the support reused in the
strictness argument. -/
theorem secant_bounds (hM : 0 < M) (ht : 0 < t ∧ t < 1)
    (hb : HasDefectBound f M) (φ : X →L[ℝ] ℝ)
    (hφ : SupportAt φ ((C.v : X) + C.secantTheta • (y : X))) :
    (1 - t) / C.p ≤ φ C.v ∧ φ C.v ≤ C.secantSlope ∧
      (C.B ≤ 1 - t → C.secantSlope ≤ 1 - C.B) ∧
      (1 - t < C.B → C.secantSlope ≤ C.B) := by
  have hlower : (1 - t) / C.p ≤ φ C.v := by
    apply support_direction_lower y.property C.p_pos ht.1
      (C.secantTheta_pos ht) (C.secantTheta_le ht) _ φ hφ
    rw [add_comm, ← C.x_eq]
    exact C.x.property
  have hα : 0 < C.p / C.s := div_pos C.p_pos C.s_pos
  have hαθ : (C.p / C.s) * C.secantTheta = C.secantStep := by
    unfold secantTheta
    field_simp [C.p_pos.ne', C.s_pos.ne']
  have hscale : (C.p / C.s) • ((C.v : X) + C.secantTheta • (y : X)) =
      (C.p / C.s) • (C.v : X) + C.secantStep • (y : X) := by
    rw [smul_add, smul_smul, hαθ]
  have hlo : SupportAt φ
      ((C.p / C.s) • (C.v : X) + C.secantStep • (y : X)) := by
    rw [← hscale]
    exact hφ.smul_nonneg hα.le
  have hdiff :
      ((C.r / C.u) • (C.v : X) + C.secantStep • (y : X)) -
        ((C.p / C.s) • (C.v : X) + C.secantStep • (y : X)) =
      (C.r / C.u - C.p / C.s) • (C.v : X) := by module
  have hsec := hlo.subgradient
    ((C.r / C.u) • (C.v : X) + C.secantStep • (y : X))
  rw [hdiff, map_smul, smul_eq_mul] at hsec
  have hupper : φ C.v ≤ C.secantSlope := by
    apply (le_div_iff₀ (C.secant_denominator_pos hM)).2
    nlinarith
  exact ⟨hlower, hupper, C.secant_upper_smallB hM ht hb,
    C.secant_upper_largeB hM ht hb⟩

theorem small_secant_product (hM : 0 < M) (ht : 0 < t ∧ t < 1)
    (hb : HasDefectBound f M) (hB : C.B ≤ 1 - t) :
    1 - t ≤ C.d * C.A * (1 - C.B) := by
  obtain ⟨φ, hφ⟩ := exists_support ((C.v : X) + C.secantTheta • (y : X))
  obtain ⟨hlower, hsec, hsmall, _⟩ := C.secant_bounds hM ht hb φ hφ
  have hle := hlower.trans (hsec.trans (hsmall hB))
  calc
    1 - t ≤ (1 - C.B) * C.p := (div_le_iff₀ C.p_pos).1 hle
    _ = C.d * C.A * (1 - C.B) := by rw [← C.p_eq_d_mul_A]; ring

end AlignedConfiguration
end Tingley

end

end OAI

-- Adapted from OAI.Analysis.SphereIsometry.RadialPerturbation

namespace OAI

/-!
# Small radial perturbations from strict support signs

Compactness is used only on the continuous dual of the span of two vectors.
The public result has no finite-dimensional or completeness hypothesis on the
ambient real normed space.
-/

noncomputable section

namespace Tingley

private theorem exists_dual_gap_of_supportAt_neg
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {v y : V}
    (hv : ‖v‖ = 1)
    (hneg : ∀ φ : V →L[ℝ] ℝ, SupportAt φ v → φ y < 0) :
    ∃ c : ℝ, 0 ≤ c ∧ c < 1 ∧
      ∀ φ : V →L[ℝ] ℝ, ‖φ‖ ≤ 1 → 0 ≤ φ y → φ v ≤ c := by
  classical
  let K : Set (V →L[ℝ] ℝ) :=
    Metric.closedBall 0 1 ∩ {φ | 0 ≤ φ y}
  have heval (z : V) : Continuous (fun φ : V →L[ℝ] ℝ => φ z) :=
    continuous_id.clm_apply continuous_const
  have hK : IsCompact K :=
    (isCompact_closedBall (0 : V →L[ℝ] ℝ) 1).inter_right
      (isClosed_le continuous_const (heval y))
  have hzero : (0 : V →L[ℝ] ℝ) ∈ K := by simp [K]
  obtain ⟨φ₀, hφ₀, hmax⟩ := hK.exists_isMaxOn ⟨0, hzero⟩ (heval v).continuousOn
  have hφnorm : ‖φ₀‖ ≤ 1 := by
    simpa only [mem_closedBall_zero_iff] using hφ₀.1
  have hc_le : φ₀ v ≤ 1 := by
    simpa only [hv] using apply_le_norm hφnorm v
  have hc_lt : φ₀ v < 1 := by
    by_contra hnot
    have heq : φ₀ v = 1 := le_antisymm hc_le (le_of_not_gt hnot)
    have hs : SupportAt φ₀ v := ⟨hφnorm, heq.trans hv.symm⟩
    exact (not_lt_of_ge hφ₀.2) (hneg φ₀ hs)
  refine ⟨φ₀ v, ?_, hc_lt, ?_⟩
  · simpa using (isMaxOn_iff.mp hmax) 0 hzero
  · intro φ hφ hy
    apply (isMaxOn_iff.mp hmax) φ
    exact ⟨mem_closedBall_zero_iff.mpr hφ, hy⟩

private theorem exists_radial_perturbation_lt_finiteDimensional
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {v y : V} {p : ℝ}
    (hv : ‖v‖ = 1) (hp : 0 < p)
    (hneg : ∀ φ : V →L[ℝ] ℝ, SupportAt φ v → φ y < 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ η : ℝ, 0 < η → η < δ →
      ‖p • v + η • y‖ < p := by
  obtain ⟨c, _hc0, hc, hgap⟩ := exists_dual_gap_of_supportAt_neg hv hneg
  have hden : 0 < ‖y‖ + 1 := by linarith [norm_nonneg y]
  refine ⟨p * (1 - c) / (‖y‖ + 1),
    div_pos (mul_pos hp (sub_pos.mpr hc)) hden, ?_⟩
  intro η hη hηδ
  obtain ⟨φ, hφ⟩ := exists_support (p • v + η • y)
  have hnorm : ‖p • v + η • y‖ = p * φ v + η * φ y := by
    calc
      ‖p • v + η • y‖ = φ (p • v + η • y) := hφ.2.symm
      _ = p * φ v + η * φ y := by simp only [map_add, map_smul, smul_eq_mul]
  rw [hnorm]
  by_cases hnegative : φ y < 0
  · have hunit : φ v ≤ 1 := by simpa only [hv] using apply_le_norm hφ.1 v
    have hfirst : p * φ v ≤ p * 1 := mul_le_mul_of_nonneg_left hunit hp.le
    have hsecond : η * φ y < 0 := mul_neg_of_pos_of_neg hη hnegative
    nlinarith only [hfirst, hsecond]
  · have hvbound : φ v ≤ c := hgap φ hφ.1 (le_of_not_gt hnegative)
    have hybound : φ y ≤ ‖y‖ := apply_le_norm hφ.1 y
    have hfirst : p * φ v ≤ p * c := mul_le_mul_of_nonneg_left hvbound hp.le
    have hsecond : η * φ y ≤ η * ‖y‖ := mul_le_mul_of_nonneg_left hybound hη.le
    have hmul : η * (‖y‖ + 1) < p * (1 - c) := (lt_div_iff₀ hden).mp hηδ
    have hstrict : p * c + η * ‖y‖ < p := by nlinarith only [hmul, hη]
    linarith only [hfirst, hsecond, hstrict]

/-- Strict negativity on the perturbing vector for every support at a unit
vector makes all sufficiently small positive radial perturbations shorter.
Only the span of the two specified vectors is made finite-dimensional. -/
theorem exists_radial_perturbation_lt
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {v y : X} {p : ℝ} (hv : ‖v‖ = 1) (hp : 0 < p)
    (hneg : ∀ φ : X →L[ℝ] ℝ, SupportAt φ v → φ y < 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ η : ℝ, 0 < η → η < δ →
      ‖p • v + η • y‖ < p := by
  classical
  let V : Submodule ℝ X := Submodule.span ℝ ({v, y} : Set X)
  have hv_mem : v ∈ V := Submodule.subset_span (by simp)
  have hy_mem : y ∈ V := Submodule.subset_span (by simp)
  let v₀ : V := ⟨v, hv_mem⟩
  let y₀ : V := ⟨y, hy_mem⟩
  have : FiniteDimensional ℝ V :=
    FiniteDimensional.span_of_finite ℝ ((Set.finite_singleton y).insert v)
  have hv₀ : ‖v₀‖ = 1 := hv
  have hneg₀ : ∀ φ : V →L[ℝ] ℝ, SupportAt φ v₀ → φ y₀ < 0 :=
    (forall_supportAt_apply_iff_submodule V v₀ y₀ (fun r : ℝ => r < 0)).mp hneg
  obtain ⟨δ, hδ, hsmall⟩ := exists_radial_perturbation_lt_finiteDimensional hv₀ hp hneg₀
  refine ⟨δ, hδ, ?_⟩
  intro η hη hηδ
  exact hsmall η hη hηδ

/-- The perturbation may also be chosen below any prescribed positive cap. -/
theorem exists_radial_perturbation_lt_with_cap
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {v y : X} {p t : ℝ} (hv : ‖v‖ = 1) (hp : 0 < p) (ht : 0 < t)
    (hneg : ∀ φ : X →L[ℝ] ℝ, SupportAt φ v → φ y < 0) :
    ∃ η : ℝ, 0 < η ∧ η < t ∧ ‖p • v + η • y‖ < p := by
  obtain ⟨δ, hδ, hsmall⟩ := exists_radial_perturbation_lt hv hp hneg
  have hm : 0 < min t δ := lt_min ht hδ
  have hη : 0 < min t δ / 2 := by linarith
  have hηt : min t δ / 2 < t := by linarith [min_le_left t δ]
  have hηδ : min t δ / 2 < δ := by linarith [min_le_right t δ]
  exact ⟨min t δ / 2, hη, hηt, hsmall _ hη hηδ⟩

end Tingley

end

end OAI

-- Adapted from OAI.Analysis.SphereIsometry.LargeChord

namespace OAI

/-!
# Excluding large aligned-chord ratios

The secant estimate holds for every support. Reusing a support in the equality
case makes the sign strict, and the literal inverse configuration gives the
opposite image sign. A small radial perturbation then violates the actual defect
bound. No compactness assumption on either ambient space is used here.
-/

noncomputable section

namespace Tingley
namespace AlignedConfiguration

variable {X Y : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable {f : UnitSphere X ≃ᵢ UnitSphere Y} {y : UnitSphere X} {t M : ℝ}
variable (C : AlignedConfiguration f y t M)

/-- The large-ratio secant bound controls both the product and the size of the
support perturbation. All quantities come from the given configuration. -/
theorem largeB_product_bounds (hM : 0 < M) (ht : 0 < t ∧ t < 1)
    (hb : HasDefectBound f M) (hlarge : 1 - t < C.B) :
    1 - t ≤ C.A * C.u ∧ C.secantTheta ≤ 1 - C.B := by
  obtain ⟨φ, hφ⟩ := exists_support ((C.v : X) + C.secantTheta • (y : X))
  have hs := C.secant_bounds hM ht hb φ hφ
  have hle : (1 - t) / C.p ≤ C.B :=
    hs.1.trans (hs.2.1.trans (hs.2.2.2 hlarge))
  have hproduct : 1 - t ≤ C.A * C.u := by
    calc
      1 - t ≤ C.B * C.p := (div_le_iff₀ C.p_pos).mp hle
      _ = C.A * C.u := by unfold A B; ring
  refine ⟨hproduct, ?_⟩
  rw [secantTheta, C.secantStep_eq_largeB ht hlarge, C.one_sub_B]
  apply (div_le_iff₀ C.p_pos).mpr
  calc
    ((1 - t) / C.u) * C.s ≤ C.A * C.s :=
      mul_le_mul_of_nonneg_right ((div_le_iff₀ C.u_pos).mpr hproduct) C.s_pos.le
    _ = (C.s / C.d) * C.p := by unfold A; ring

/-- A large `B` makes every support at the original chord direction strictly
negative on the base vector, and forces `A` into the same large regime. -/
theorem largeB_forces_largeA_and_negative_support
    (hM : 0 < M) (ht : 0 < t ∧ t < 1) (hb : HasDefectBound f M)
    (hlarge : 1 - t < C.B) :
    1 - t < C.A ∧
      ∀ L : X →L[ℝ] ℝ, SupportAt L (C.v : X) → L (y : X) < 0 := by
  obtain ⟨hproduct, hθB⟩ := C.largeB_product_bounds hM ht hb hlarge
  have hθ : 0 < C.secantTheta := C.secantTheta_pos ht
  have hnegative : ∀ L : X →L[ℝ] ℝ,
      SupportAt L (C.v : X) → L (y : X) < 0 := by
    intro L hL
    have hLv : L (C.v : X) = 1 := hL.2.trans C.v.property
    obtain ⟨φ, hφ⟩ := exists_support ((C.v : X) + C.secantTheta • (y : X))
    have hs := C.secant_bounds hM ht hb φ hφ
    have hφv : φ (C.v : X) ≤ C.B := hs.2.1.trans (hs.2.2.2 hlarge)
    have hφy : φ (y : X) ≤ 1 := by
      simpa only [UnitSphere.norm_coe] using apply_le_norm hφ.1 (y : X)
    have hφeval : φ (C.v : X) + C.secantTheta * φ (y : X) =
        ‖(C.v : X) + C.secantTheta • (y : X)‖ := by
      simpa only [map_add, map_smul, smul_eq_mul] using hφ.2
    have hleft : 1 + C.secantTheta * L (y : X) ≤
        ‖(C.v : X) + C.secantTheta • (y : X)‖ := by
      simpa only [map_add, map_smul, smul_eq_mul, hLv] using
        apply_le_norm hL.1 ((C.v : X) + C.secantTheta • (y : X))
    have hφterm : C.secantTheta * φ (y : X) ≤ C.secantTheta := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hφy hθ.le
    have hnorm : ‖(C.v : X) + C.secantTheta • (y : X)‖ ≤
        C.B + C.secantTheta := by
      linarith only [hφeval, hφv, hφterm]
    have hstrict : 1 + C.secantTheta * L (y : X) - C.secantTheta < C.B := by
      by_contra hnot
      have hLperturbed : SupportAt L ((C.v : X) + C.secantTheta • (y : X)) := by
        refine ⟨hL.1, ?_⟩
        simp only [map_add, map_smul, smul_eq_mul, hLv]
        have hreverse := le_of_not_gt hnot
        linarith only [hleft, hnorm, hreverse]
      have hsL := C.secant_bounds hM ht hb L hLperturbed
      have hbad : 1 ≤ C.B := by
        simpa only [hLv] using hsL.2.1.trans (hsL.2.2.2 hlarge)
      exact (not_le_of_gt C.B_lt_one) hbad
    have hmul : C.secantTheta * L (y : X) < C.secantTheta * 0 := by
      linarith only [hstrict, hθB]
    exact (mul_lt_mul_iff_right₀ hθ).mp hmul
  refine ⟨?_, hnegative⟩
  obtain ⟨L, hL⟩ := exists_support (C.v : X)
  have hj : L (y : X) < 0 := hnegative L hL
  have hLv : L (C.v : X) = 1 := hL.2.trans C.v.property
  have hz : C.r • (C.v : X) - t • (y : X) = -(C.z : X) := by
    rw [C.z_eq]
    abel
  have hznorm : ‖C.r • (C.v : X) - t • (y : X)‖ = 1 := by
    rw [hz, norm_neg, UnitSphere.norm_coe]
  have hr : C.r - t * L (y : X) ≤ 1 := by
    simpa only [map_sub, map_smul, smul_eq_mul, hLv, mul_one, hznorm] using
      apply_le_norm hL.1 (C.r • (C.v : X) - t • (y : X))
  have htj : t * L (y : X) < 0 := mul_neg_of_pos_of_neg ht.1 hj
  have hr1 : C.r < 1 := by linarith only [hr, htj]
  have hu1 : C.u < 1 := by linarith only [hr1, C.r_sub_u, hM]
  have hproduct_lt : C.A * C.u < C.A := by
    simpa only [mul_one] using mul_lt_mul_of_pos_left hu1 C.A_pos
  exact hproduct.trans_lt hproduct_lt

/-- The inverse uses literal negated directions. In particular, obtaining the
positive image sign does not assume that the sphere map preserves antipodes. -/
theorem largeB_support_signs (hM : 0 < M) (ht : 0 < t ∧ t < 1)
    (hb : HasDefectBound f M) (hlarge : 1 - t < C.B) :
    (∀ L : X →L[ℝ] ℝ, SupportAt L (C.v : X) → L (y : X) < 0) ∧
      (∀ K : Y →L[ℝ] ℝ, SupportAt K (C.w : Y) → 0 < K (f y : Y)) := by
  obtain ⟨hA, hnegative⟩ :=
    C.largeB_forces_largeA_and_negative_support hM ht hb hlarge
  have hlarge_inverse : 1 - t < C.inverse.B := by
    simpa only [inverse_B] using hA
  have hinverse :=
    (C.inverse.largeB_forces_largeA_and_negative_support hM ht hb.symm
      hlarge_inverse).2
  refine ⟨hnegative, ?_⟩
  intro K hK
  have hKneg : SupportAt (-K) (C.inverse.v : Y) := by
    simpa only [inverse_v_coe] using hK.neg
  have h := hinverse (-K) hKneg
  change -(K (f y : Y)) < 0 at h
  linarith only [h]

/-- A small decrease of the radius strictly increases both contributions to the
signed defect, contradicting its global bound. -/
theorem largeB_impossible (hM : 0 < M) (ht : 0 < t ∧ t < 1)
    (hb : HasDefectBound f M) (hlarge : 1 - t < C.B) : False := by
  obtain ⟨hnegative, hpositive⟩ := C.largeB_support_signs hM ht hb hlarge
  obtain ⟨η, hη, hηt, hshort⟩ :=
    exists_radial_perturbation_lt_with_cap C.v.property C.p_pos ht.1 hnegative
  obtain ⟨K, hK⟩ := exists_support (C.w : Y)
  have hKw : K (C.w : Y) = 1 := hK.2.trans C.w.property
  have hKb : 0 < K (f y : Y) := hpositive K hK
  have hlong : C.s < ‖C.s • (C.w : Y) + η • (f y : Y)‖ := by
    have hle := apply_le_norm hK.1 (C.s • (C.w : Y) + η • (f y : Y))
    simp only [map_add, map_smul, smul_eq_mul, hKw, mul_one] at hle
    have hterm : 0 < η * K (f y : Y) := mul_pos hη hKb
    linarith only [hle, hterm]
  have hq : t - η ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact (sub_pos.mpr hηt).le
    · linarith only [ht.2, hη]
  have hx : (C.x : X) - (t - η) • (y : X) =
      C.p • (C.v : X) + η • (y : X) := by
    rw [C.x_eq, sub_smul]
    abel
  have hfx : (f C.x : Y) - (t - η) • (f y : Y) =
      C.s • (C.w : Y) + η • (f y : Y) := by
    rw [C.fx_eq, sub_smul]
    abel
  have hbound := (abs_le.mp (hb (t - η) hq C.x y)).2
  rw [signedDefect, hfx, hx] at hbound
  linarith only [hbound, hshort, hlong, C.s_sub_p]

/-- Both ratios lie in the small regime. The first component is obtained by
applying the already-proved contradiction to the exact inverse configuration. -/
theorem small_ratios (hM : 0 < M) (ht : 0 < t ∧ t < 1)
    (hb : HasDefectBound f M) : C.A ≤ 1 - t ∧ C.B ≤ 1 - t := by
  constructor
  · have h : C.inverse.B ≤ 1 - t :=
      le_of_not_gt (C.inverse.largeB_impossible hM ht hb.symm)
    simpa only [inverse_B] using h
  · exact le_of_not_gt (C.largeB_impossible hM ht hb)

end AlignedConfiguration
end Tingley

end

end OAI

-- Adapted from OAI.Analysis.SphereIsometry.SmallChord

namespace OAI

/-!
# The small-chord contradiction

The scalar estimates imply nonnegative coefficients in two exact identities
between the actual chord vectors. Applying the norm triangle inequality to
those identities contradicts preservation of the distance between the base
point and the opposite endpoint. No convexity or monotonicity property of an
abstract auxiliary function is assumed.
-/

namespace Tingley

/-- The two small-regime estimates and the strict chord imbalance force the
radial deficit to be strictly below one half. -/
theorem smallChord_epsilon_lt_half {A B d ε : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hAB : A + B < 1) (hd : d ≤ 2)
    (heA : ε ≤ d * A * (1 - B)) (heB : ε ≤ d * B * (1 - A)) :
    ε < 1 / 2 := by
  have step (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hsum : a + b < 1)
      (he : ε ≤ d * a * (1 - b)) : ε < 1 / 2 := by
    have hahalf : a < 1 / 2 := by linarith
    have hb1 : b < 1 := by linarith
    have hprod0 : 0 ≤ a * (1 - b) :=
      mul_nonneg ha.le (sub_nonneg.mpr hb1.le)
    have hprod : a * (1 - b) ≤ a * (1 - a) :=
      mul_le_mul_of_nonneg_left (by linarith) ha.le
    have hsquare : 0 < (1 / 2 - a) ^ 2 :=
      sq_pos_of_pos (by linarith)
    have hquarter : a * (1 - b) < 1 / 4 := by nlinarith
    have hscale : d * (a * (1 - b)) ≤ 2 * (a * (1 - b)) :=
      mul_le_mul_of_nonneg_right hd hprod0
    nlinarith [he, hscale, hquarter]
  rcases le_total A B with h | h
  · exact step A B hA h hAB heA
  · exact step B A hB h (by linarith) heB

/-- The scalar conclusions needed by the two actual vector identities.
The second coefficient is permitted to vanish. -/
theorem smallChord_coefficients {A B d ε t p r s u : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hAB : A + B < 1)
    (hd : 0 < d) (hd2 : d ≤ 2) (hεt : ε + t = 1)
    (hdr : d = p + r) (hds : d = s + u)
    (hpA : p = d * A) (huB : u = d * B)
    (hAe : A ≤ ε) (hBe : B ≤ ε)
    (heA : ε ≤ d * A * (1 - B)) (heB : ε ≤ d * B * (1 - A)) :
    ε < 1 / 2 ∧ 0 < r * t - p * ε ∧ 0 ≤ s * ε - u * t ∧ p < s := by
  have hehalf := smallChord_epsilon_lt_half hA hB hAB hd2 heA heB
  have hAt : A < t := by linarith
  have hr : r = d - p := by linarith
  have hs : s = d - u := by linarith
  have he : ε = 1 - t := by linarith
  have ht : t = 1 - ε := by linarith
  have hα : r * t - p * ε = d * (t - A) := by
    rw [hr, hpA, he]
    ring
  have hβ : s * ε - u * t = d * (ε - B) := by
    rw [hs, huB, ht]
    ring
  have hgap : s - p = d * (1 - A - B) := by
    rw [hs, hpA, huB]
    ring
  refine ⟨hehalf, ?_, ?_, ?_⟩
  · rw [hα]
    exact mul_pos hd (sub_pos.mpr hAt)
  · rw [hβ]
    exact mul_nonneg hd.le (sub_nonneg.mpr hBe)
  · have hgap_pos : 0 < s - p := by
      rw [hgap]
      exact mul_pos hd (by linarith)
    linarith

/-- Two norm triangle inequalities on the actual chord vectors are incompatible
with the chord imbalance and the preserved base-to-endpoint distance. -/
theorem smallChord_norm_contradiction
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (y v : X) (b w : Y) {t ε p r s u d : ℝ}
    (hεt : ε + t = 1) (hε : 0 < ε) (hd : 0 < d)
    (hp : 0 < p) (hr : 0 < r) (hs : 0 < s) (hu : 0 < u)
    (hdr : d = p + r) (hds : d = s + u) (hps : p < s)
    (hy : ‖y‖ = 1) (hb : ‖b‖ = 1)
    (hx : ‖t • y + p • v‖ = 1) (hfx : ‖t • b + s • w‖ = 1)
    (hα : 0 ≤ r * t - p * ε) (hβ : 0 ≤ s * ε - u * t)
    (hiso : ‖ε • y + r • v‖ = ‖ε • b + u • w‖) : False := by
  let V : X := ε • y + r • v
  let W : Y := ε • b + u • w
  have hVW : ‖V‖ = ‖W‖ := hiso
  have hleftId : r • (t • y + p • v) = p • V + (r * t - p * ε) • y := by
    dsimp only [V]
    module
  have hrightId : s • W = u • (t • b + s • w) + (s * ε - u * t) • b := by
    dsimp only [W]
    module
  have hleft : r ≤ p * ‖V‖ + (r * t - p * ε) := by
    calc
      r = ‖r • (t • y + p • v)‖ := by
        rw [norm_smul_of_nonneg hr.le, hx, mul_one]
      _ = ‖p • V + (r * t - p * ε) • y‖ := congrArg norm hleftId
      _ ≤ ‖p • V‖ + ‖(r * t - p * ε) • y‖ := norm_add_le _ _
      _ = p * ‖V‖ + (r * t - p * ε) := by
        rw [norm_smul_of_nonneg hp.le, norm_smul_of_nonneg hα, hy, mul_one]
  have hright : s * ‖W‖ ≤ u + (s * ε - u * t) := by
    calc
      s * ‖W‖ = ‖s • W‖ := (norm_smul_of_nonneg hs.le W).symm
      _ = ‖u • (t • b + s • w) + (s * ε - u * t) • b‖ := congrArg norm hrightId
      _ ≤ ‖u • (t • b + s • w)‖ + ‖(s * ε - u * t) • b‖ := norm_add_le _ _
      _ = u + (s * ε - u * t) := by
        simp only [norm_smul_of_nonneg hu.le, norm_smul_of_nonneg hβ, hfx, hb, mul_one]
  have ht : t = 1 - ε := by linarith
  have hrearrange : r - (r * t - p * ε) = ε * d := by
    rw [ht, hdr]
    ring
  have hurearrange : u + (s * ε - u * t) = ε * d := by
    rw [ht, hds]
    ring
  have hlower : ε * d ≤ p * ‖V‖ := by linarith
  have hupper : s * ‖V‖ ≤ ε * d := by rw [hVW]; linarith
  have hpositive : 0 < ε * d := mul_pos hε hd
  have hVpos : 0 < ‖V‖ := by
    by_contra h
    have hVnonpos : ‖V‖ ≤ 0 := le_of_not_gt h
    have hpV : p * ‖V‖ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hp.le hVnonpos
    linarith
  exact (not_lt_of_ge (hupper.trans hlower)) (mul_lt_mul_of_pos_right hps hVpos)

/-- The small regime contradicts preservation of the actual opposite-endpoint
distance. All scalar guards of the norm argument are derived here. -/
theorem smallChord_contradiction
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (y v : X) (b w : Y) {t ε p r s u d A B : ℝ}
    (ht1 : t < 1) (he : ε = 1 - t)
    (hp : 0 < p) (hr : 0 < r) (hs : 0 < s) (hu : 0 < u)
    (hdr : d = p + r) (hds : d = s + u) (hd2 : d ≤ 2)
    (hA : A = p / d) (hB : B = u / d) (hAB : A + B < 1)
    (hAe : A ≤ ε) (hBe : B ≤ ε)
    (heA : ε ≤ d * A * (1 - B)) (heB : ε ≤ d * B * (1 - A))
    (hy : ‖y‖ = 1) (hb : ‖b‖ = 1)
    (hx : ‖t • y + p • v‖ = 1) (hfx : ‖t • b + s • w‖ = 1)
    (hiso : ‖ε • y + r • v‖ = ‖ε • b + u • w‖) : False := by
  have hd : 0 < d := by rw [hdr]; exact add_pos hp hr
  have hApos : 0 < A := by rw [hA]; exact div_pos hp hd
  have hBpos : 0 < B := by rw [hB]; exact div_pos hu hd
  have hpA : p = d * A := by rw [hA, mul_div_cancel₀ p (ne_of_gt hd)]
  have huB : u = d * B := by rw [hB, mul_div_cancel₀ u (ne_of_gt hd)]
  have hεt : ε + t = 1 := by linarith
  have hε : 0 < ε := by linarith
  obtain ⟨_, hα, hβ, hps⟩ := smallChord_coefficients hApos hBpos hAB hd hd2 hεt
    hdr hds hpA huB hAe hBe heA heB
  exact smallChord_norm_contradiction y v b w hεt hε hd hp hr hs hu hdr hds hps
    hy hb hx hfx hα.le hβ hiso

end Tingley

end OAI

-- Adapted from OAI.Analysis.SphereIsometry.ChordContradiction

namespace OAI

/-! A genuinely aligned positive-defect configuration is impossible. -/

namespace Tingley

variable {X Y : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable {f : UnitSphere X ≃ᵢ UnitSphere Y} {y : UnitSphere X} {t M : ℝ}

/-- The global bound and the actual aligned chords contradict one another.
The two small-regime inequalities are proved from the original and literal
inverse configurations; neither is an additional caller premise. -/
theorem alignedConfiguration_impossible (hM : 0 < M) (ht : 0 < t ∧ t < 1)
    (hb : HasDefectBound f M) (C : AlignedConfiguration f y t M) : False := by
  obtain ⟨hA, hB⟩ := C.small_ratios hM ht hb
  have heA := C.small_secant_product hM ht hb hB
  have heB : 1 - t ≤ C.d * C.B * (1 - C.A) := by
    have hA' : C.inverse.B ≤ 1 - t := by
      simpa only [AlignedConfiguration.inverse_B] using hA
    have h := C.inverse.small_secant_product hM ht hb.symm hA'
    simpa only [AlignedConfiguration.inverse_d, AlignedConfiguration.inverse_A,
      AlignedConfiguration.inverse_B] using h
  have hx : ‖t • (y : X) + C.p • (C.v : X)‖ = 1 := by
    rw [← C.x_eq]
    exact C.x.property
  have hfx : ‖t • (f y : Y) + C.s • (C.w : Y)‖ = 1 := by
    rw [← C.fx_eq]
    exact (f C.x).property
  have hleft : (1 - t) • (y : X) + C.r • (C.v : X) = (y : X) - (C.z : X) := by
    rw [C.z_eq]
    module
  have hright : (1 - t) • (f y : Y) + C.u • (C.w : Y) =
      (f y : Y) - (f C.z : Y) := by
    rw [C.fz_eq]
    module
  have hiso : ‖(1 - t) • (y : X) + C.r • (C.v : X)‖ =
      ‖(1 - t) • (f y : Y) + C.u • (C.w : Y)‖ := by
    rw [hleft, hright]
    exact (sphere_norm_sub f y C.z).symm
  exact smallChord_contradiction (y : X) (C.v : X) (f y : Y) (C.w : Y)
    (t := t) (ε := 1 - t) (d := C.d) (A := C.A) (B := C.B)
    ht.2 rfl C.p_pos C.r_pos C.s_pos C.u_pos rfl C.chord_sum C.chord_le_two
    rfl rfl (C.A_add_B_lt_one hM) hA hB heA heB y.property (f y).property hx hfx hiso

end Tingley

end OAI

-- Adapted from OAI.Analysis.SphereIsometry.RadialExtension

namespace OAI

/-!
# The radial extension of a sphere isometry with zero defect

The extension is defined on actual vectors, including zero. A zero cross-radius
bound gives its all-pairs isometry; sphere surjectivity gives its surjectivity.
Mazur–Ulam then supplies real linearity. Uniqueness is proved against arbitrary
real-linear extensions, without assuming they are continuous or surjective.
-/

noncomputable section

namespace Tingley

universe u v

variable {X : Type u} {Y : Type v}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- The actual radial extension, with a separate zero branch. -/
def radialExtension (f : UnitSphere X ≃ᵢ UnitSphere Y) (x : X) : Y := by
  classical
  exact if hx : x = 0 then 0 else ‖x‖ • (f (normalize x hx) : Y)

@[simp] theorem radialExtension_zero (f : UnitSphere X ≃ᵢ UnitSphere Y) :
    radialExtension f 0 = 0 := by
  simp [radialExtension]

theorem radialExtension_of_ne_zero (f : UnitSphere X ≃ᵢ UnitSphere Y)
    (x : X) (hx : x ≠ 0) :
    radialExtension f x = ‖x‖ • (f (normalize x hx) : Y) := by
  simp only [radialExtension, dif_neg hx]

@[simp] theorem radialExtension_norm (f : UnitSphere X ≃ᵢ UnitSphere Y) (x : X) :
    ‖radialExtension f x‖ = ‖x‖ := by
  by_cases hx : x = 0
  · subst x
    simp only [radialExtension_zero, norm_zero]
  · rw [radialExtension_of_ne_zero f x hx,
      norm_smul_of_nonneg (norm_nonneg x), UnitSphere.norm_coe, mul_one]

/-- Every nonnegative radial representation has the expected image. -/
theorem radialExtension_smul_unit (f : UnitSphere X ≃ᵢ UnitSphere Y)
    (r : ℝ) (hr : 0 ≤ r) (u : UnitSphere X) :
    radialExtension f (r • (u : X)) = r • (f u : Y) := by
  by_cases hr0 : r = 0
  · subst r
    simp only [zero_smul, radialExtension_zero]
  · have hn : ‖r • (u : X)‖ = r := by
      rw [norm_smul_of_nonneg hr, UnitSphere.norm_coe, mul_one]
    have hne : r • (u : X) ≠ 0 := by
      intro h
      apply hr0
      rw [← hn, h, norm_zero]
    have hnormalize : normalize (r • (u : X)) hne = u := by
      apply Subtype.ext
      change ‖r • (u : X)‖⁻¹ • (r • (u : X)) = (u : X)
      rw [hn, smul_smul, inv_mul_cancel₀ hr0, one_smul]
    rw [radialExtension_of_ne_zero f _ hne, hn, hnormalize]

@[simp] theorem radialExtension_unit (f : UnitSphere X ≃ᵢ UnitSphere Y)
    (u : UnitSphere X) : radialExtension f (u : X) = (f u : Y) := by
  simpa only [one_smul] using radialExtension_smul_unit f 1 zero_le_one u

/-- The zero bound gives exact preservation at every radius in the closed unit interval. -/
theorem crossRadius_eq_of_zero_defect (f : UnitSphere X ≃ᵢ UnitSphere Y)
    (h0 : HasDefectBound f 0) (q : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (u v : UnitSphere X) :
    ‖(f u : Y) - q • (f v : Y)‖ = ‖(u : X) - q • (v : X)‖ := by
  exact sub_eq_zero.mp (signedDefect_eq_zero_of_bound_zero h0 hq u v)

/-- Factor by the larger positive radius; the smaller radius may be zero. -/
theorem scaled_norm_sub_eq (f : UnitSphere X ≃ᵢ UnitSphere Y)
    (h0 : HasDefectBound f 0) (u v : UnitSphere X) (a b : ℝ)
    (ha : 0 < a) (hb : 0 ≤ b) (hba : b ≤ a) :
    ‖a • (f u : Y) - b • (f v : Y)‖ = ‖a • (u : X) - b • (v : X)‖ := by
  have hq : b / a ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hb ha.le, (div_le_one ha).mpr hba⟩
  have hab : a * (b / a) = b := by
    rw [div_eq_mul_inv, mul_left_comm, mul_inv_cancel₀ (ne_of_gt ha), mul_one]
  calc
    ‖a • (f u : Y) - b • (f v : Y)‖ =
        ‖a • ((f u : Y) - (b / a) • (f v : Y))‖ := by
      rw [smul_sub, smul_smul, hab]
    _ = a * ‖(f u : Y) - (b / a) • (f v : Y)‖ :=
      norm_smul_of_nonneg ha.le _
    _ = a * ‖(u : X) - (b / a) • (v : X)‖ := by
      rw [crossRadius_eq_of_zero_defect f h0 (b / a) hq u v]
    _ = ‖a • ((u : X) - (b / a) • (v : X))‖ :=
      (norm_smul_of_nonneg ha.le _).symm
    _ = ‖a • (u : X) - b • (v : X)‖ := by
      rw [smul_sub, smul_smul, hab]

/-- Every pair is covered, including zero vectors and either order of radii. -/
theorem radialExtension_norm_sub (f : UnitSphere X ≃ᵢ UnitSphere Y)
    (h0 : HasDefectBound f 0) (x y : X) :
    ‖radialExtension f x - radialExtension f y‖ = ‖x - y‖ := by
  by_cases hx : x = 0
  · subst x
    simpa only [radialExtension_zero, zero_sub, norm_neg] using radialExtension_norm f y
  by_cases hy : y = 0
  · subst y
    simpa only [radialExtension_zero, sub_zero] using radialExtension_norm f x
  have hordered (a b : X) (ha : a ≠ 0) (hb : b ≠ 0) (hba : ‖b‖ ≤ ‖a‖) :
      ‖radialExtension f a - radialExtension f b‖ = ‖a - b‖ := by
    have h := scaled_norm_sub_eq f h0 (normalize a ha) (normalize b hb)
      ‖a‖ ‖b‖ (norm_pos_iff.mpr ha) (norm_nonneg b) hba
    rw [norm_smul_normalize, norm_smul_normalize] at h
    simpa only [radialExtension_of_ne_zero f a ha,
      radialExtension_of_ne_zero f b hb] using h
  rcases le_total ‖y‖ ‖x‖ with hle | hle
  · exact hordered x y hx hy hle
  · calc
      ‖radialExtension f x - radialExtension f y‖ =
          ‖radialExtension f y - radialExtension f x‖ := norm_sub_rev _ _
      _ = ‖y - x‖ := hordered y x hy hx hle
      _ = ‖x - y‖ := norm_sub_rev _ _

theorem radialExtension_isometry (f : UnitSphere X ≃ᵢ UnitSphere Y)
    (h0 : HasDefectBound f 0) : Isometry (radialExtension f) := by
  apply Isometry.of_dist_eq
  intro x y
  simpa only [dist_eq_norm] using radialExtension_norm_sub f h0 x y

/-- Surjectivity follows directly from the actual inverse on unit spheres. -/
theorem radialExtension_surjective (f : UnitSphere X ≃ᵢ UnitSphere Y) :
    Function.Surjective (radialExtension f) := by
  intro y
  by_cases hy : y = 0
  · subst y
    exact ⟨0, radialExtension_zero f⟩
  · refine ⟨‖y‖ • (f.symm (normalize y hy) : X), ?_⟩
    rw [radialExtension_smul_unit f ‖y‖ (norm_nonneg y), f.apply_symm_apply]
    exact norm_smul_normalize y hy

/-- The metric equivalence is built only after isometry and surjectivity are proved. -/
def radialIsometryEquiv (f : UnitSphere X ≃ᵢ UnitSphere Y)
    (h0 : HasDefectBound f 0) : X ≃ᵢ Y where
  toEquiv := Equiv.ofBijective (radialExtension f)
    ⟨(radialExtension_isometry f h0).injective, radialExtension_surjective f⟩
  isometry_toFun := radialExtension_isometry f h0

@[simp] theorem coe_radialIsometryEquiv (f : UnitSphere X ≃ᵢ UnitSphere Y)
    (h0 : HasDefectBound f 0) : ⇑(radialIsometryEquiv f h0) = radialExtension f := rfl

@[simp] theorem radialIsometryEquiv_apply (f : UnitSphere X ≃ᵢ UnitSphere Y)
    (h0 : HasDefectBound f 0) (x : X) :
    radialIsometryEquiv f h0 x = radialExtension f x := rfl

/-- Mazur–Ulam applied to the derived whole-space isometry fixing zero. -/
def radialLinearIsometryEquiv (f : UnitSphere X ≃ᵢ UnitSphere Y)
    (h0 : HasDefectBound f 0) : X ≃ₗᵢ[ℝ] Y :=
  (radialIsometryEquiv f h0).toRealLinearIsometryEquivOfMapZero
    (by change radialExtension f 0 = 0; exact radialExtension_zero f)

@[simp] theorem coe_radialLinearIsometryEquiv (f : UnitSphere X ≃ᵢ UnitSphere Y)
    (h0 : HasDefectBound f 0) :
    ⇑(radialLinearIsometryEquiv f h0) = radialExtension f := rfl

@[simp] theorem radialLinearIsometryEquiv_apply (f : UnitSphere X ≃ᵢ UnitSphere Y)
    (h0 : HasDefectBound f 0) (x : X) :
    radialLinearIsometryEquiv f h0 x = radialExtension f x := rfl

@[simp] theorem radialLinearIsometryEquiv_unit (f : UnitSphere X ≃ᵢ UnitSphere Y)
    (h0 : HasDefectBound f 0) (u : UnitSphere X) :
    radialLinearIsometryEquiv f h0 (u : X) = (f u : Y) :=
  radialExtension_unit f u

/-- Any real-linear extension has the radial formula, without additional hypotheses on it. -/
theorem linear_extension_eq_radial (f : UnitSphere X ≃ᵢ UnitSphere Y)
    (L : X →ₗ[ℝ] Y) (hL : ∀ u : UnitSphere X, L (u : X) = (f u : Y)) (x : X) :
    L x = radialExtension f x := by
  by_cases hx : x = 0
  · subst x
    simp only [map_zero, radialExtension_zero]
  · calc
      L x = L (‖x‖ • (normalize x hx : X)) :=
        congrArg L (norm_smul_normalize x hx).symm
      _ = ‖x‖ • L (normalize x hx : X) := L.map_smul _ _
      _ = ‖x‖ • (f (normalize x hx) : Y) := by rw [hL]
      _ = radialExtension f x := (radialExtension_of_ne_zero f x hx).symm

end Tingley

end

end OAI

-- Adapted from OAI.Analysis.SphereIsometry.Extension

namespace OAI

/-!
# The unique real-linear extension of an onto sphere isometry

The intermediate hypotheses of the separate constructions are discharged here:
positive original defect produces an actual attained defect in completed normed
quotients, alignment produces actual opposite chords, and the chord theorem
rules them out. The original radial extension consequently preserves distance.
-/

noncomputable section

namespace Tingley

universe u v

variable {X : Type u} {Y : Type v}
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

theorem no_attained_positive_defect
    {X : Type u} {Y : Type v}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (f : UnitSphere X ≃ᵢ UnitSphere Y) (t M : ℝ)
    (ht : 0 < t ∧ t < 1) (hM : 0 < M) (hb : HasDefectBound f M)
    (x y : UnitSphere X) (hatt : signedDefect f t x y = M) : False := by
  obtain ⟨C⟩ := exists_alignedConfiguration f y x t M ht hM hb hatt
  exact alignedConfiguration_impossible hM ht hb C

variable [Nontrivial X] [Nontrivial Y]

theorem maxDefect_eq_zero
    {X : Type u} {Y : Type v}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    [Nontrivial X] [Nontrivial Y]
    (f : UnitSphere X ≃ᵢ UnitSphere Y) : maxDefect f = 0 := by
  apply le_antisymm ?_ (maxDefect_nonneg f)
  by_contra hn
  have hM : 0 < maxDefect f := lt_of_not_ge hn
  obtain ⟨hb, hi, t, ht, ha⟩ := positive_maxDefect_attained_or_inverse f hM
  rcases ha with ⟨x, y, hxy⟩ | ⟨x, y, hxy⟩
  · exact no_attained_positive_defect _ t (maxDefect f) ⟨ht.1, ht.2⟩ hM hb x y hxy
  · exact no_attained_positive_defect _ t (maxDefect f) ⟨ht.1, ht.2⟩ hM hi x y hxy

theorem hasDefectBound_zero (f : UnitSphere X ≃ᵢ UnitSphere Y) : HasDefectBound f 0 := by
  simpa only [maxDefect_eq_zero] using hasDefectBound_maxDefect f

/-- The actual unconditional extension, with the original radial function. -/
def extension (f : UnitSphere X ≃ᵢ UnitSphere Y) : X ≃ₗᵢ[ℝ] Y :=
  radialLinearIsometryEquiv f (hasDefectBound_zero f)

@[simp] theorem extension_apply (f : UnitSphere X ≃ᵢ UnitSphere Y) (x : X) :
    extension f x = radialExtension f x := rfl

@[simp] theorem extension_zero (f : UnitSphere X ≃ᵢ UnitSphere Y) :
    extension f 0 = 0 := radialExtension_zero f

@[simp] theorem extension_unit (f : UnitSphere X ≃ᵢ UnitSphere Y) (x : UnitSphere X) :
    extension f (x : X) = (f x : Y) := radialExtension_unit f x

theorem extension_radial (f : UnitSphere X ≃ᵢ UnitSphere Y) (x : X) (hx : x ≠ 0) :
    extension f x = ‖x‖ • (f (normalize x hx) : Y) :=
  radialExtension_of_ne_zero f x hx

theorem extension_surjective (f : UnitSphere X ≃ᵢ UnitSphere Y) :
    Function.Surjective (extension f) := (extension f).surjective

theorem extension_unique (f : UnitSphere X ≃ᵢ UnitSphere Y)
    (L : X →ₗ[ℝ] Y) (hL : ∀ x : UnitSphere X, L (x : X) = (f x : Y)) :
    L = (extension f).toLinearEquiv.toLinearMap := by
  apply LinearMap.ext
  intro x
  exact linear_extension_eq_radial f L hL x

/-- An ordinary onto sphere isometry is a genuine sphere isometry equivalence. -/
def sphereIsometryEquiv (f : UnitSphere X → UnitSphere Y)
    (hf : Isometry f) (hs : Function.Surjective f) : UnitSphere X ≃ᵢ UnitSphere Y where
  toEquiv := Equiv.ofBijective f ⟨hf.injective, hs⟩
  isometry_toFun := hf

/-- Radial formula, surjectivity, and uniqueness among all real-linear extensions. -/
theorem tingley_sphere_isometry_full
    (f : UnitSphere X → UnitSphere Y) (hf : Isometry f) (hs : Function.Surjective f) :
    ∃ T : X ≃ₗᵢ[ℝ] Y,
      (∀ u : UnitSphere X, T (u : X) = (f u : Y)) ∧
      T 0 = 0 ∧
      (∀ x : X, ∀ hx : x ≠ 0, T x = ‖x‖ • (f (normalize x hx) : Y)) ∧
      Function.Surjective T ∧
      (∀ L : X →ₗ[ℝ] Y, (∀ u : UnitSphere X, L (u : X) = (f u : Y)) →
        L = T.toLinearEquiv.toLinearMap) := by
  let e := sphereIsometryEquiv f hf hs
  refine ⟨extension e, extension_unit e, extension_zero e,
    extension_radial e, extension_surjective e, ?_⟩
  intro L hL
  exact extension_unique e L hL

end Tingley

end

end OAI

private theorem compact_onto {A : Type*} [MetricSpace A] [CompactSpace A]
    (f : A → A) (hf : Isometry f) : Function.Surjective f := by
  intro x
  change x ∈ Set.range f
  rw [← (isCompact_range hf.continuous).isClosed.closure_eq, Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨a, φ, hm, ht⟩ := CompactSpace.tendsto_subseq (fun n : ℕ => f^[n] x)
  obtain ⟨N,hN⟩ := Metric.cauchySeq_iff.mp ht.cauchySeq ε hε
  have h := hN N le_rfl (N+1) (by omega)
  change dist (f^[φ N] x) (f^[φ (N+1)] x) < ε at h
  obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_lt (hm (Nat.lt_succ_self N))
  have hiter (m : ℕ) : Isometry f^[m] := by
    induction m with
    | zero => exact isometry_id
    | succ m ih => exact ih.comp hf
  refine ⟨f (f^[k] x), ⟨_,rfl⟩, ?_⟩
  rw [hk, show φ N + k + 1 = φ N + (k+1) by omega, Function.iterate_add_apply,
    (hiter _).dist_eq, Function.iterate_succ_apply'] at h
  exact h

theorem OMA.solution : type_of% @OMA.S_mo_387291.main := by
  intro n X _ _ _ _ _ hd e he f hf hfix
  funext x
  haveI : Nontrivial X := ⟨⟨(x : X),0,fun h => by simpa [h] using x.property⟩⟩
  have hc : IsCompact {v : X | ‖v‖ = 1} := by
    simpa [Metric.sphere, dist_zero_right] using isCompact_sphere (0 : X) 1
  letI : CompactSpace {v : X // ‖v‖ = 1} := isCompact_iff_compactSpace.mp hc
  obtain ⟨T,hT,_⟩ := OAI.Tingley.tingley_sphere_isometry_full f hf (compact_onto f hf)
  let b := basisOfLinearIndependentOfCardEqFinrank' (fun i => (e i : X)) he (by simpa using hd.symm)
  have hL : T.toLinearEquiv.toLinearMap = LinearMap.id := b.ext (fun i => by
    simp only [b, coe_basisOfLinearIndependentOfCardEqFinrank']
    change T (e i : X) = (e i : X)
    rw [hT, hfix])
  apply Subtype.ext
  change (f x : X) = (x : X)
  rw [← hT]
  exact LinearMap.congr_fun hL _
