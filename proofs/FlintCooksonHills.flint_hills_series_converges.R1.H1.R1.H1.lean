import OMAReductions.R_FlintCooksonHills_flint_hills_series_converges_R1_H1_R1
import Mathlib

/-!
Specializes the parameter construction in OpenAI's The irrationality
exponent of pi is 2, commit 3344da59991ed94f9ba711217b29c1d760badfa6.
The Parameters, Sigma, DimensionLimits, and Dimension modules and the
initial-scale lemma are combined for the single-file project checker.
-/

/-
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

namespace OAI

namespace PiExponent

theorem exists_rational_parameters (ν : ℝ) (hν : 2 < ν) :
    ∃ θ A B C : ℚ,
      0 < (θ : ℝ) ∧ (θ : ℝ) < A ∧ (A : ℝ) < B ∧ (B : ℝ) < 1 ∧
      ν * ((A : ℝ) - θ) > 1 - θ ∧
      1 < (C : ℝ) ∧ (B : ℝ) < 1 / C ∧
      (B : ℝ) < C * θ ∧ (C : ℝ) * θ < 1 := by
  have hνpos : 0 < ν := by linarith
  have hdiv : 1 / ν < (1 / 2 : ℝ) :=
    (div_lt_iff₀ hνpos).2 (by linarith)
  obtain ⟨b, hbl, hbu⟩ := exists_rat_btwn (show (1 / 2 : ℝ) < 1 - 1 / ν by linarith)
  have hbpos : 0 < (b : ℝ) := by linarith
  have hb1 : (b : ℝ) < 1 := by
    have := one_div_pos.mpr hνpos
    linarith
  have hνb : ν * (b : ℝ) < ν - 1 := calc
    _ < ν * (1 - 1 / ν) := mul_lt_mul_of_pos_left hbu hνpos
    _ = ν - 1 := by field_simp
  have hcoeff : 0 < ν * (1 - (b : ℝ)) - 1 := by nlinarith
  have hδtop : 0 < min (1 : ℝ) ((2 * (b : ℝ) - 1) / ((b : ℝ) * b)) :=
    lt_min (by norm_num) (div_pos (by linarith) (mul_pos hbpos hbpos))
  obtain ⟨δ, hδpos, hδtop⟩ := exists_rat_btwn hδtop
  have hδ1 : (δ : ℝ) < 1 := lt_of_lt_of_le hδtop (min_le_left _ _)
  have hδsmall : (δ : ℝ) < (2 * (b : ℝ) - 1) / ((b : ℝ) * b) :=
    lt_of_lt_of_le hδtop (min_le_right _ _)
  have hδprod : (δ : ℝ) * ((b : ℝ) * b) < 2 * (b : ℝ) - 1 :=
    (lt_div_iff₀ (mul_pos hbpos hbpos)).mp hδsmall
  let θ : ℚ := 1 - δ
  let A : ℚ := 1 - b * δ
  have hθcast : (θ : ℝ) = 1 - (δ : ℝ) := by simp [θ]
  have hAcast : (A : ℝ) = 1 - (b : ℝ) * δ := by simp [A]
  have hθpos : 0 < (θ : ℝ) := by rw [hθcast]; linarith
  have hθA : (θ : ℝ) < A := by
    rw [hθcast, hAcast]
    nlinarith [mul_pos (sub_pos.mpr hb1) hδpos]
  have hApos : 0 < (A : ℝ) := lt_trans hθpos hθA
  have hA1 : (A : ℝ) < 1 := by
    rw [hAcast]
    nlinarith [mul_pos hbpos hδpos]
  have hAsq : (A : ℝ) ^ 2 < θ := by
    rw [hAcast, hθcast]
    nlinarith [mul_pos hδpos (sub_pos.mpr hδprod)]
  have hgap : 1 - (θ : ℝ) < ν * ((A : ℝ) - θ) := by
    rw [hAcast, hθcast]
    nlinarith [mul_pos hcoeff hδpos]
  have hCinterval : (A : ℝ) / θ < 1 / A := by
    apply (div_lt_div_iff₀ hθpos hApos).2
    nlinarith
  obtain ⟨C, hClo, hChi⟩ := exists_rat_btwn hCinterval
  have hC1 : 1 < (C : ℝ) := by
    have : (1 : ℝ) < (A : ℝ) / θ := (lt_div_iff₀ hθpos).2 (by simpa using hθA)
    exact lt_trans this hClo
  have hCpos : 0 < (C : ℝ) := by linarith
  have hACθ : (A : ℝ) < (C : ℝ) * θ := (div_lt_iff₀ hθpos).mp hClo
  have hCA : (C : ℝ) * A < 1 := (lt_div_iff₀ hApos).mp hChi
  have hAinvC : (A : ℝ) < 1 / C := (lt_div_iff₀ hCpos).2 (by nlinarith)
  have hCθ1 : (C : ℝ) * θ < 1 := by nlinarith [mul_lt_mul_of_pos_left hθA hCpos]
  have hBinterval : (A : ℝ) < min (1 / (C : ℝ)) ((C : ℝ) * θ) :=
    lt_min hAinvC hACθ
  obtain ⟨B, hBlo, hBhi⟩ := exists_rat_btwn hBinterval
  have hBinv : (B : ℝ) < 1 / C := lt_of_lt_of_le hBhi (min_le_left _ _)
  have hBCθ : (B : ℝ) < (C : ℝ) * θ := lt_of_lt_of_le hBhi (min_le_right _ _)
  exact ⟨θ, A, B, C, hθpos, hθA, hBlo, lt_trans hBCθ hCθ1,
    hgap, hC1, hBinv, hBCθ, hCθ1⟩

theorem exists_eta_preserving_exponent_gap
    (nu theta A : ℝ) (hnu : 2 < nu) (hA : 0 < A)
    (hgap : 1 - theta < nu * (A - theta)) :
    ∃ eta : ℝ, 0 < eta ∧ eta < 1 ∧
      0 < nu * (A * (1 - eta) - theta) - (1 - theta) := by
  let gap : ℝ := nu * (A - theta) - (1 - theta)
  have hgap_pos : 0 < gap := by dsimp [gap]; linarith
  have hnu_pos : 0 < nu := by linarith
  have hden_pos : 0 < 2 * nu * A := by positivity
  let eta : ℝ := min (1 / 2) (gap / (2 * nu * A))
  have heta_pos : 0 < eta := by
    dsimp [eta]
    exact lt_min (by norm_num) (div_pos hgap_pos hden_pos)
  have heta_half : eta ≤ 1 / 2 := min_le_left _ _
  have heta_lt_one : eta < 1 := by linarith
  have heta_gap : eta ≤ gap / (2 * nu * A) := min_le_right _ _
  have hscaled : eta * (2 * nu * A) ≤ gap :=
    (le_div_iff₀ hden_pos).mp heta_gap
  refine ⟨eta, heta_pos, heta_lt_one, ?_⟩
  dsimp [gap] at hgap_pos hscaled
  nlinarith

structure Parameters (ν : ℝ) where
  theta : ℚ
  A : ℚ
  B : ℚ
  C : ℚ
  eta : ℝ
  theta_pos : 0 < (theta : ℝ)
  theta_lt_A : (theta : ℝ) < A
  A_lt_B : (A : ℝ) < B
  B_lt_one : (B : ℝ) < 1
  approximation_gap : 1 - (theta : ℝ) < ν * ((A : ℝ) - theta)
  one_lt_C : 1 < (C : ℝ)
  B_lt_inv_C : (B : ℝ) < 1 / C
  B_lt_C_theta : (B : ℝ) < (C : ℝ) * theta
  C_theta_lt_one : (C : ℝ) * theta < 1
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  gap_pos : 0 < ν * ((A : ℝ) * (1 - eta) - theta) - (1 - theta)

theorem exists_parameters (ν : ℝ) (hν : 2 < ν) : Nonempty (Parameters ν) := by
  obtain ⟨theta, A, B, C, htheta, hthetaA, hAB, hB, hgap, hC, hBinv, hBC, hCtheta⟩ :=
    exists_rational_parameters ν hν
  obtain ⟨eta, heta, heta1, hgapeta⟩ := exists_eta_preserving_exponent_gap
    ν theta A hν (lt_trans htheta hthetaA) hgap
  exact ⟨⟨theta, A, B, C, eta, htheta, hthetaA, hAB, hB, hgap, hC,
    hBinv, hBC, hCtheta, heta, heta1, hgapeta⟩⟩

namespace Parameters

variable {ν : ℝ} (p : Parameters ν)

theorem A_pos : 0 < (p.A : ℝ) := lt_trans p.theta_pos p.theta_lt_A

theorem B_pos : 0 < (p.B : ℝ) := lt_trans p.A_pos p.A_lt_B

theorem C_pos : 0 < (p.C : ℝ) := lt_trans zero_lt_one p.one_lt_C

theorem A_lt_one : (p.A : ℝ) < 1 := lt_trans p.A_lt_B p.B_lt_one

theorem theta_lt_one : (p.theta : ℝ) < 1 := lt_trans p.theta_lt_A p.A_lt_one

theorem CB_lt_one : (p.C : ℝ) * p.B < 1 := by
  have h := (lt_div_iff₀ p.C_pos).mp p.B_lt_inv_C
  simpa only [mul_comm] using h

theorem one_lt_C_theta_div_B : 1 < (p.C : ℝ) * p.theta / p.B := by
  apply (lt_div_iff₀ p.B_pos).2
  simpa using p.B_lt_C_theta

theorem one_lt_B_div_A : 1 < (p.B : ℝ) / p.A := by
  apply (lt_div_iff₀ p.A_pos).2
  simpa using p.A_lt_B

end Parameters

end PiExponent

end OAI

namespace OAI

namespace PiExponent

theorem exists_small_rational_sigma
    (m : ℕ) (α β θ : ℝ) (hα : α < 1) (hβ : β < 1) (hθ : θ < 1) :
    ∃ σ : ℚ, 0 < (σ : ℝ) ∧
      (1 + 3 * (σ : ℝ)) ^ (m + 1) * α < 1 ∧
      (1 + 3 * (σ : ℝ)) ^ m * β < 1 ∧
      (1 + (σ : ℝ)) * θ < 1 := by
  have hopenα : IsOpen {s : ℝ | (1 + 3 * s) ^ (m + 1) * α < 1} :=
    isOpen_lt (by fun_prop) continuous_const
  have hopenβ : IsOpen {s : ℝ | (1 + 3 * s) ^ m * β < 1} :=
    isOpen_lt (by fun_prop) continuous_const
  have hopenθ : IsOpen {s : ℝ | (1 + s) * θ < 1} :=
    isOpen_lt (by fun_prop) continuous_const
  have hopen : IsOpen {s : ℝ |
      (1 + 3 * s) ^ (m + 1) * α < 1 ∧
      (1 + 3 * s) ^ m * β < 1 ∧
      (1 + s) * θ < 1} :=
    hopenα.inter (hopenβ.inter hopenθ)
  have hzero : (0 : ℝ) ∈ {s : ℝ |
      (1 + 3 * s) ^ (m + 1) * α < 1 ∧
      (1 + 3 * s) ^ m * β < 1 ∧
      (1 + s) * θ < 1} := by
    simpa using And.intro hα (And.intro hβ hθ)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen 0 hzero
  obtain ⟨σ, hσ0, hσε⟩ := exists_rat_btwn hε
  have hσmem : (σ : ℝ) ∈ Metric.ball 0 ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hσ0]
    exact hσε
  exact ⟨σ, hσ0, hball hσmem⟩

end PiExponent

end OAI

namespace OAI

open Filter Topology

namespace PiExponent

 theorem tendsto_nat_add_one_div_pow {r : ℝ} (hr : 1 < r) :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1) / r ^ n) atTop (𝓝 0) := by
  have h₁ := tendsto_pow_const_div_const_pow_of_one_lt 1 hr
  have h₀ := tendsto_pow_const_div_const_pow_of_one_lt 0 hr
  simpa only [pow_one, pow_zero, ← add_div, zero_add] using h₁.add h₀

 theorem tendsto_pow_div_nat_add_one {r : ℝ} (hr : 1 < r) :
    Tendsto (fun n : ℕ => r ^ n / ((n : ℝ) + 1)) atTop atTop := by
  have hpos : ∀ᶠ n : ℕ in atTop, 0 < ((n : ℝ) + 1) / r ^ n :=
    Filter.Eventually.of_forall fun n =>
      div_pos (by positivity) (pow_pos (zero_lt_one.trans hr) n)
  have hwithin : Tendsto (fun n : ℕ => ((n : ℝ) + 1) / r ^ n)
      atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_nat_add_one_div_pow hr, hpos⟩
  have hinv := hwithin.inv_tendsto_nhdsGT_zero
  change Tendsto (fun n : ℕ => (((n : ℝ) + 1) / r ^ n)⁻¹) atTop atTop at hinv
  simpa only [inv_div] using hinv

end PiExponent

end OAI

namespace OAI

noncomputable section

open Filter
open scoped Topology

namespace PiExponent

def dimensionK (C : ℝ) (m : ℕ) : ℕ := ⌊C ^ m⌋₊

def dimensionW (B : ℝ) (m : ℕ) : ℝ := (B ^ m)⁻¹

def dimensionV (theta B C : ℝ) (m : ℕ) : ℝ :=
  2 * (dimensionK C m : ℝ) * theta ^ m * dimensionW B m

theorem dimensionK_le (C : ℝ) (hC : 0 ≤ C) (m : ℕ) :
    (dimensionK C m : ℝ) ≤ C ^ m :=
  Nat.floor_le (pow_nonneg hC m)

theorem dimensionK_one_le (C : ℝ) (hC : 1 ≤ C) (m : ℕ) :
    1 ≤ dimensionK C m := by
  exact (Nat.one_le_floor_iff _).2 (one_le_pow₀ hC)

theorem dimensionW_pos (B : ℝ) (hB : 0 < B) (m : ℕ) :
    0 < dimensionW B m := by
  exact inv_pos.mpr (pow_pos hB m)

theorem dimensionV_pos (theta B C : ℝ) (htheta : 0 < theta)
    (hB : 0 < B) (hC : 1 ≤ C) (m : ℕ) :
    0 < dimensionV theta B C m := by
  have hK : 0 < (dimensionK C m : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (dimensionK_one_le C hC m))
  exact mul_pos (mul_pos (mul_pos (by norm_num) hK) (pow_pos htheta m))
    (dimensionW_pos B hB m)

theorem dimension_volume (theta B C : ℝ) (htheta : 0 < theta)
    (hB : 0 < B) (hC : 1 ≤ C) (m : ℕ) :
    (dimensionK C m : ℝ) * (dimensionW B m / dimensionV theta B C m) *
      theta ^ m = 1 / 2 := by
  have hK : (dimensionK C m : ℝ) ≠ 0 := by
    exact ne_of_gt (by exact_mod_cast
      (lt_of_lt_of_le Nat.zero_lt_one (dimensionK_one_le C hC m)))
  have ht : theta ^ m ≠ 0 := ne_of_gt (pow_pos htheta m)
  have hw : dimensionW B m ≠ 0 := ne_of_gt (dimensionW_pos B hB m)
  unfold dimensionV
  field_simp

theorem dimensionK_div_W_le (B C : ℝ) (hB : 0 < B) (hC : 0 ≤ C) (m : ℕ) :
    (dimensionK C m : ℝ) / dimensionW B m ≤ (C * B) ^ m := by
  rw [dimensionW, div_inv_eq_mul, mul_pow]
  exact mul_le_mul_of_nonneg_right (dimensionK_le C hC m) (pow_pos hB m).le

theorem dimensionV_geometric_lower (theta B C : ℝ) (htheta : 0 < theta)
    (hB : 0 < B) (m : ℕ) (hlarge : 2 ≤ C ^ m) :
    (C * theta / B) ^ m ≤ dimensionV theta B C m := by
  have hfloor : C ^ m < (dimensionK C m : ℝ) + 1 := Nat.lt_floor_add_one _
  have hK : C ^ m ≤ 2 * (dimensionK C m : ℝ) := by linarith
  rw [div_pow, mul_pow, div_eq_mul_inv]
  unfold dimensionV dimensionW
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hK (pow_pos htheta m).le)
    (inv_pos.mpr (pow_pos hB m)).le

theorem dimension_volume_lt_one (theta C : ℝ) (htheta : 0 < theta)
    (hC : 0 ≤ C) (hsmall : C * theta < 1) (m : ℕ) (hm : 1 ≤ m) :
    (dimensionK C m : ℝ) * theta ^ m < 1 := by
  calc
    (dimensionK C m : ℝ) * theta ^ m ≤ C ^ m * theta ^ m :=
      mul_le_mul_of_nonneg_right (dimensionK_le C hC m) (pow_pos htheta m).le
    _ = (C * theta) ^ m := (mul_pow _ _ _).symm
    _ < 1 := pow_lt_one₀ (mul_nonneg hC htheta.le) hsmall (by omega)

theorem dimension_error_le (theta B C a b : ℝ) (htheta : 0 < theta)
    (hB : 0 < B) (hC : 0 ≤ C) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (m : ℕ) (hlarge : 2 ≤ C ^ m) :
    (a * (m : ℝ) + b) / dimensionV theta B C m +
        100 * (dimensionK C m : ℝ) / dimensionW B m ≤
      (a * (m : ℝ) + b) / (C * theta / B) ^ m + 100 * (C * B) ^ m := by
  have hr : 0 < (C * theta / B) ^ m := by
    have hCp : 0 < C := by
      by_contra hn
      have hz : C = 0 := le_antisymm (le_of_not_gt hn) hC
      subst C
      rcases m with _ | m <;> norm_num at hlarge
    positivity
  apply add_le_add
  · exact div_le_div_of_nonneg_left (by positivity) hr
      (dimensionV_geometric_lower theta B C htheta hB m hlarge)
  · rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (dimensionK_div_W_le B C hB hC m) (by norm_num)

theorem dimension_collision_identity (theta A B C eta : ℝ)
    (htheta : 0 < theta) (hA : 0 < A) (hB : 0 < B) (hC : 1 ≤ C) (m : ℕ) :
    eta ^ 2 * (dimensionK C m : ℝ) * theta ^ m /
        (((m : ℝ) + 1) * dimensionV theta B C m * A ^ m) =
      eta ^ 2 * (B / A) ^ m / (2 * ((m : ℝ) + 1)) := by
  have hK : (dimensionK C m : ℝ) ≠ 0 := by
    exact ne_of_gt (by exact_mod_cast
      (lt_of_lt_of_le Nat.zero_lt_one (dimensionK_one_le C hC m)))
  have ht : theta ^ m ≠ 0 := ne_of_gt (pow_pos htheta m)
  have hA' : A ^ m ≠ 0 := ne_of_gt (pow_pos hA m)
  have hB' : B ^ m ≠ 0 := ne_of_gt (pow_pos hB m)
  have hm : (m : ℝ) + 1 ≠ 0 := by positivity
  unfold dimensionV dimensionW
  rw [div_pow]
  field_simp

theorem tendsto_dimension_error_majorant (theta B C a b : ℝ)
    (hB : 0 < B) (hC : 0 < C) (hsmall : C * B < 1)
    (hlarge : 1 < C * theta / B) :
    Tendsto (fun m : ℕ => (a * (m : ℝ) + b) / (C * theta / B) ^ m +
      100 * (C * B) ^ m) atTop (𝓝 0) := by
  have h₁ := tendsto_pow_const_div_const_pow_of_one_lt 1 hlarge
  have h₀ := tendsto_pow_const_div_const_pow_of_one_lt 0 hlarge
  have hlin : Tendsto (fun m : ℕ => (a * (m : ℝ) + b) /
      (C * theta / B) ^ m) atTop (𝓝 0) := by
    convert (h₁.const_mul a).add (h₀.const_mul b) using 1
    · ext m
      simp only [pow_one, pow_zero]
      ring
    · simp
  have hgeom := tendsto_pow_atTop_nhds_zero_of_lt_one (mul_pos hC hB).le hsmall
  simpa only [mul_zero, add_zero] using hlin.add (hgeom.const_mul 100)

theorem tendsto_dimension_collision (A B eta : ℝ)
    (hratio : 1 < B / A) (heta : 0 < eta) :
    Tendsto (fun m : ℕ => eta ^ 2 * (B / A) ^ m /
      (2 * ((m : ℝ) + 1))) atTop atTop := by
  have h := (tendsto_pow_div_nat_add_one hratio).const_mul_atTop
    (show 0 < eta ^ 2 / 2 by positivity)
  convert h using 1
  ext m
  rw [mul_div_mul_comm]

theorem exists_dimension_margin (theta A B C eta a b epsilon target : ℝ)
    (htheta : 0 < theta) (hB : 0 < B) (hC : 1 < C)
    (hsmall : C * B < 1) (hlarge : 1 < C * theta / B)
    (hratio : 1 < B / A) (heta : 0 < eta)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hepsilon : 0 < epsilon) :
    ∃ m : ℕ, 1 ≤ m ∧
      (a * (m : ℝ) + b) / dimensionV theta B C m +
        100 * (dimensionK C m : ℝ) / dimensionW B m < epsilon ∧
      target < eta ^ 2 * (B / A) ^ m / (2 * ((m : ℝ) + 1)) := by
  have herrors := (tendsto_dimension_error_majorant theta B C a b hB
    (zero_lt_one.trans hC) hsmall hlarge).eventually (gt_mem_nhds hepsilon)
  have hcollision := (tendsto_dimension_collision A B eta hratio heta).eventually
    (eventually_gt_atTop target)
  have hfloor := (tendsto_pow_atTop_atTop_of_one_lt hC).eventually
    (eventually_ge_atTop (2 : ℝ))
  have hgood : ∀ᶠ m : ℕ in atTop, 1 ≤ m ∧
      (a * (m : ℝ) + b) / dimensionV theta B C m +
        100 * (dimensionK C m : ℝ) / dimensionW B m < epsilon ∧
      target < eta ^ 2 * (B / A) ^ m / (2 * ((m : ℝ) + 1)) := by
    filter_upwards [herrors, hcollision, hfloor, eventually_ge_atTop 1]
      with m herror hcollision hfloor hm
    exact ⟨hm, (dimension_error_le theta B C a b htheta hB
      (zero_lt_one.trans hC).le ha hb m hfloor).trans_lt herror, hcollision⟩
  exact hgood.exists

end PiExponent

end

end OAI

namespace OAI.PiExponent

theorem exists_initial_scale (nu theta epsilon : ℝ) (_htheta : 0 < theta)
    (hepsilon : 0 < epsilon) :
    ∃ F0 : ℝ, 0 < F0 ∧ 2 / theta < F0 ∧ nu / F0 < epsilon / 3 := by
  obtain ⟨N, hN⟩ := exists_nat_gt (max 1 (max (2 / theta) (3 * nu / epsilon)))
  have hF : 1 < (N : ℝ) := lt_of_le_of_lt (le_max_left _ _) hN
  have hthetaF : 2 / theta < (N : ℝ) :=
    lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hN
  have hnuF : 3 * nu / epsilon < (N : ℝ) :=
    lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hN
  refine ⟨N, by linarith, hthetaF, ?_⟩
  apply (div_lt_iff₀ (show (0 : ℝ) < N by linarith)).2
  have := (div_lt_iff₀ hepsilon).mp hnuF
  nlinarith

end OAI.PiExponent

open OAI.PiExponent in
theorem OMA.solution : OMA.R_FlintCooksonHills_flint_hills_series_converges_R1_H1_R1.H1 := by
  intro nu hnu
  obtain ⟨P⟩ := exists_parameters nu hnu
  let gap : ℝ := nu * ((P.A : ℝ) * (1 - P.eta) - P.theta) - (1 - P.theta)
  have hgap : 0 < gap := P.gap_pos
  let eps : ℝ := min (gap / 2) (1 / 2)
  have epsPos : 0 < eps := lt_min (by positivity) (by norm_num)
  have epsGap : eps < gap := (min_le_left _ _).trans_lt (by linarith)
  have epsHalf : eps ≤ 1 / 2 := min_le_right _ _
  obtain ⟨F, Fpos, Ftheta, Fmargin⟩ := exists_initial_scale nu P.theta eps P.theta_pos epsPos
  let lambda := Real.log 4 + 4
  let coeff := Real.log 2 / 4
  have lambdaPos : 0 < lambda := by dsimp [lambda]; positivity
  have coeffPos : 0 < coeff := by dsimp [coeff]; positivity
  obtain ⟨m, hm, dim, coll⟩ := exists_dimension_margin
    P.theta P.A P.B P.C P.eta (lambda * F) (2 * Real.log 2)
    (eps / 3) (2 / coeff) P.theta_pos P.B_pos P.one_lt_C
    P.CB_lt_one P.one_lt_C_theta_div_B P.one_lt_B_div_A P.eta_pos
    (mul_pos lambdaPos Fpos).le (by positivity) (by positivity)
  let K := dimensionK (P.C : ℝ) m
  have centers : (K : ℝ) * (P.theta : ℝ) ^ m < 1 :=
    dimension_volume_lt_one P.theta P.C P.theta_pos P.C_pos.le P.C_theta_lt_one m hm
  obtain ⟨sig, sigPos, sigVol, sigK, sigTheta⟩ :=
    exists_small_rational_sigma m (1 / 2) ((K : ℝ) * (P.theta : ℝ) ^ m)
      P.theta (by norm_num) centers P.theta_lt_one
  have collision : 2 < coeff *
      (P.eta ^ 2 * (K : ℝ) * (P.theta : ℝ) ^ m /
        (((m : ℝ) + 1) * dimensionV P.theta P.B P.C m * (P.A : ℝ) ^ m)) := by
    dsimp only [K]
    rw [dimension_collision_identity P.theta P.A P.B P.C P.eta
      P.theta_pos P.A_pos P.B_pos P.one_lt_C.le]
    exact (div_lt_iff₀ coeffPos).mp coll |>.trans_eq (mul_comm _ _)
  exact ⟨P.theta, P.A, P.B, P.C, sig, P.eta, eps, F, m,
    P.theta_pos, P.theta_lt_A, P.A_lt_B, P.B_lt_one, P.one_lt_C, P.B_lt_inv_C,
    P.B_lt_C_theta, P.C_theta_lt_one, P.eta_pos, P.eta_lt_one, epsPos, epsHalf,
    epsGap, Ftheta, Fmargin, hm, dim, collision, sigPos, sigVol, sigK, sigTheta⟩
