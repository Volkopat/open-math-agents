import OMAReductions.R_Green84_green_84_variants_littlewood_R1
import Mathlib
/- Adapted from OpenAI math, commit 3344da59991ed94f9ba711217b29c1d760badfa6.
Source modules: Model,Gaussian,Rounding,BinaryPacket,Curvature,Cutoff,QuadraticTail,Spreading,ProductProbability,Nibble,Matching,Averages,FiniteRank,Chunks,DependentMoments,SlotGraph,SlotParameters,IntervalPacking.
Port and exact-target bridge by my-other-github-account.
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

namespace AsymptoticallyMinimalLittlewood

/-- The Littlewood polynomial of length N, evaluated at z. -/
def littlewoodValue {N : ℕ} (ε : Fin N → ℝ) (z : ℂ) : ℂ :=
  ∑ k : Fin N, (ε k : ℂ) * z ^ (k : ℕ)

/-- Real signs in every consecutive degree 0,...,N-1. -/
def IsRealSigning {N : ℕ} (ε : Fin N → ℝ) : Prop :=
  ∀ k, ε k = -1 ∨ ε k = 1

def MainStatement : Prop :=
  ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
    ∃ ε : Fin N → ℝ, IsRealSigning ε ∧
      ∀ z : ℂ, ‖z‖ = 1 → ‖littlewoodValue ε z‖ ≤ (1 + η) * Real.sqrt N

end AsymptoticallyMinimalLittlewood

end OAI



namespace OAI

namespace AsymptoticallyMinimalLittlewood
noncomputable section

open MeasureTheory Complex Real FourierTransform Filter Topology
open scoped FourierTransform SchwartzMap ContDiff

theorem integral_schwartz_mul_gaussian
    (f : 𝓢(ℝ, ℂ)) {b : ℂ} (hb : 0 < b.re) (c : ℂ) :
    (∫ x : ℝ, f x * Complex.exp (-Real.pi * b * (x : ℂ) ^ 2 +
      2 * Real.pi * c * (x : ℂ))) =
    1 / b ^ (1 / 2 : ℂ) * ∫ ξ : ℝ, (𝓕⁻ f : 𝓢(ℝ, ℂ)) ξ *
      Complex.exp (-Real.pi / b * ((ξ : ℂ) + Complex.I * c) ^ 2) := by
  have hG : Integrable (fun x : ℝ ↦
      Complex.exp (-Real.pi * b * (x : ℂ) ^ 2 + 2 * Real.pi * c * (x : ℂ))) := by
    have hp : 0 < ((Real.pi : ℂ) * b).re := by
      simpa using mul_pos Real.pi_pos hb
    simpa only [neg_mul, add_zero] using
      integrable_cexp_quadratic hp (2 * Real.pi * c) 0
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (L := innerₗ ℝ) (μ := volume) (ν := volume)
    Real.continuous_fourierChar continuous_inner
    (𝓕⁻ f : 𝓢(ℝ, ℂ)).integrable hG
  have heq : (∫ x : ℝ, (𝓕 (𝓕⁻ f : 𝓢(ℝ, ℂ))) x *
      Complex.exp (-Real.pi * b * (x : ℂ) ^ 2 + 2 * Real.pi * c * (x : ℂ))) =
      ∫ ξ : ℝ, (𝓕⁻ f : 𝓢(ℝ, ℂ)) ξ *
        (𝓕 (fun x : ℝ ↦ Complex.exp (-Real.pi * b * (x : ℂ) ^ 2 +
          2 * Real.pi * c * (x : ℂ)))) ξ := by
    simpa only [flip_innerₗ, smul_eq_mul] using! h
  rw [FourierTransform.fourier_fourierInv_eq] at heq
  rw [heq, fourier_gaussian_pi' hb c]
  simp_rw [← mul_assoc, mul_comm ((𝓕⁻ f : 𝓢(ℝ, ℂ)) _) (1 / b ^ (1 / 2 : ℂ)), mul_assoc]
  exact integral_const_mul _ _

/-- The damping kernel has modulus at most one on the closed right half-plane. -/
theorem norm_damped_quadratic_le_one {b : ℂ} (hb : 0 ≤ b.re) (u x : ℝ) :
    ‖Complex.exp (-Real.pi * b * (x : ℂ) ^ 2 -
      2 * Real.pi * Complex.I * u * x)‖ ≤ 1 := by
  rw [Complex.norm_exp, Real.exp_le_one_iff]
  have hre : (-Real.pi * b * (x : ℂ) ^ 2 -
      2 * Real.pi * Complex.I * u * x).re = -Real.pi * b.re * x ^ 2 := by
    simp [Complex.mul_re, Complex.mul_im, pow_two]
  rw [hre]
  exact mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr Real.pi_pos.le) hb) (sq_nonneg _)

/-- The Fourier-side Gaussian also has modulus at most one. -/
theorem norm_damped_fourier_le_one {b : ℂ} (hb : 0 ≤ b.re) (y : ℝ) :
    ‖Complex.exp (-Real.pi / b * (y : ℂ) ^ 2)‖ ≤ 1 := by
  rw [Complex.norm_exp, Real.exp_le_one_iff]
  have hre : (-Real.pi / b * (y : ℂ) ^ 2).re =
      -Real.pi * (b.re / Complex.normSq b) * y ^ 2 := by
    simp [div_eq_mul_inv, Complex.mul_re, Complex.mul_im, pow_two,
      Complex.inv_re]
  rw [hre]
  exact mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr Real.pi_pos.le)
      (div_nonneg hb (Complex.normSq_nonneg _))) (sq_nonneg _)

theorem integral_schwartz_mul_gaussian_boundary
    (f : 𝓢(ℝ, ℂ)) {b : ℂ} (hb : 0 ≤ b.re) (hb0 : b ≠ 0) (u : ℝ) :
    (∫ x : ℝ, f x * Complex.exp (-Real.pi * b * (x : ℂ) ^ 2 -
      2 * Real.pi * Complex.I * u * x)) =
    1 / b ^ (1 / 2 : ℂ) * ∫ ξ : ℝ, (𝓕⁻ f : 𝓢(ℝ, ℂ)) ξ *
      Complex.exp (-Real.pi / b * ((ξ : ℂ) + u) ^ 2) := by
  let bn : ℕ → ℂ := fun n ↦ b + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)
  have hbn (n : ℕ) : 0 < (bn n).re := by
    dsimp [bn]
    simpa using add_pos_of_nonneg_of_pos hb (by positivity : 0 < 1 / ((n : ℝ) + 1))
  have hbnlim : Filter.Tendsto bn Filter.atTop (𝓝 b) := by
    have hz := Complex.continuous_ofReal.tendsto 0 |>.comp
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa [bn] using tendsto_const_nhds.add hz
  have hblim : b ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    by_cases h : b.im = 0
    · left
      have hr : b.re ≠ 0 := by
        intro hr
        exact hb0 (Complex.ext hr h)
      exact lt_of_le_of_ne hb (Ne.symm hr)
    · exact Or.inr h
  have hcpow : Filter.Tendsto (fun n ↦ 1 / (bn n) ^ (1 / 2 : ℂ))
      Filter.atTop (𝓝 (1 / b ^ (1 / 2 : ℂ))) := by
    exact tendsto_const_nhds.div
      (continuousAt_cpow_const hblim |>.tendsto.comp hbnlim)
      (Complex.cpow_ne_zero_iff.mpr (Or.inl hb0))
  have hl : Filter.Tendsto
      (fun n ↦ ∫ x : ℝ, f x * Complex.exp (-Real.pi * bn n * (x : ℂ) ^ 2 -
        2 * Real.pi * Complex.I * u * x)) Filter.atTop
      (𝓝 (∫ x : ℝ, f x * Complex.exp (-Real.pi * b * (x : ℂ) ^ 2 -
        2 * Real.pi * Complex.I * u * x))) := by
    apply tendsto_integral_of_dominated_convergence (fun x ↦ ‖f x‖)
    · intro n
      apply Continuous.aestronglyMeasurable
      fun_prop
    · exact f.integrable.norm
    · intro n
      filter_upwards with x
      rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (norm_damped_quadratic_le_one (hbn n).le u x)
    · filter_upwards with x
      exact tendsto_const_nhds.mul
        (Complex.continuous_exp.tendsto _ |>.comp
          (((tendsto_const_nhds.mul hbnlim).mul tendsto_const_nhds).sub
            tendsto_const_nhds))
  have hr : Filter.Tendsto
      (fun n ↦ ∫ ξ : ℝ, (𝓕⁻ f : 𝓢(ℝ, ℂ)) ξ *
        Complex.exp (-Real.pi / bn n * ((ξ : ℂ) + u) ^ 2)) Filter.atTop
      (𝓝 (∫ ξ : ℝ, (𝓕⁻ f : 𝓢(ℝ, ℂ)) ξ *
        Complex.exp (-Real.pi / b * ((ξ : ℂ) + u) ^ 2))) := by
    apply tendsto_integral_of_dominated_convergence (fun ξ ↦ ‖(𝓕⁻ f : 𝓢(ℝ, ℂ)) ξ‖)
    · intro n
      apply Continuous.aestronglyMeasurable
      fun_prop
    · exact (𝓕⁻ f : 𝓢(ℝ, ℂ)).integrable.norm
    · intro n
      filter_upwards with ξ
      rw [norm_mul]
      apply mul_le_of_le_one_right (norm_nonneg _)
      simpa only [Complex.ofReal_add] using norm_damped_fourier_le_one (hbn n).le (ξ + u)
    · filter_upwards with ξ
      exact tendsto_const_nhds.mul
        (Complex.continuous_exp.tendsto _ |>.comp
          ((tendsto_const_nhds.div hbnlim hb0).mul tendsto_const_nhds))
  have heq (n : ℕ) :
      (∫ x : ℝ, f x * Complex.exp (-Real.pi * bn n * (x : ℂ) ^ 2 -
        2 * Real.pi * Complex.I * u * x)) =
      1 / (bn n) ^ (1 / 2 : ℂ) * ∫ ξ : ℝ, (𝓕⁻ f : 𝓢(ℝ, ℂ)) ξ *
        Complex.exp (-Real.pi / bn n * ((ξ : ℂ) + u) ^ 2) := by
    convert integral_schwartz_mul_gaussian f (hbn n) (-Complex.I * u) using 1 <;>
      simp [← mul_assoc, sub_eq_add_neg]
  exact tendsto_nhds_unique hl ((hcpow.mul hr).congr' (Filter.Eventually.of_forall (fun n ↦ (heq n).symm)))

def realPhase (x : ℝ) : ℂ := Complex.exp (Complex.I * (x : ℂ))

@[simp] theorem norm_realPhase (x : ℝ) : ‖realPhase x‖ = 1 := by
  simp [realPhase, Complex.norm_exp, Complex.mul_re]

/-- Multiplication by a continuous real phase preserves integrability. -/
theorem integrable_schwartz_phase (f : 𝓢(ℝ, ℂ)) (p : ℝ → ℝ)
    (hp : Continuous p) : Integrable (fun x ↦ f x * realPhase (p x)) := by
  apply f.integrable.norm.mono'
  · apply Continuous.aestronglyMeasurable
    unfold realPhase
    exact f.continuous.mul (Complex.continuous_exp.comp
      (continuous_const.mul (Complex.continuous_ofReal.comp hp)))
  · filter_upwards with x
    simp

/-- Quadratic Fourier identity with an undamped, nonzero real curvature. -/
theorem integral_schwartz_quadratic_exact (f : 𝓢(ℝ, ℂ))
    {t : ℝ} (ht : t ≠ 0) (u : ℝ) :
    (∫ x : ℝ, f x * realPhase (Real.pi * t * x ^ 2 - 2 * Real.pi * u * x)) =
    1 / (-Complex.I * (t : ℂ)) ^ (1 / 2 : ℂ) *
      ∫ ξ : ℝ, (𝓕⁻ f : 𝓢(ℝ, ℂ)) ξ * realPhase (-Real.pi / t * (ξ + u) ^ 2) := by
  have hb0 : -Complex.I * (t : ℂ) ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) (Complex.ofReal_ne_zero.mpr ht)
  have hb : 0 ≤ (-Complex.I * (t : ℂ)).re := by simp
  convert integral_schwartz_mul_gaussian_boundary f hb hb0 u using 1
  · apply integral_congr_ae
    filter_upwards with x
    congr 1
    unfold realPhase
    congr 1
    push_cast
    ring
  · congr 1
    apply integral_congr_ae
    filter_upwards with ξ
    congr 1
    unfold realPhase
    congr 1
    push_cast
    field_simp
    simp [Complex.I_sq]
    ring

/-- Fourier inversion specialized to the linear factor in the quadratic formula. -/
theorem integral_schwartz_inverse_linear (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    (∫ ξ : ℝ, (𝓕⁻ f : 𝓢(ℝ, ℂ)) ξ * realPhase (-2 * Real.pi * ξ * x)) = f x := by
  have h := congrArg (fun g : 𝓢(ℝ, ℂ) ↦ g x)
    (show (𝓕 (𝓕⁻ f : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ)) = f from
      FourierTransform.fourier_fourierInv_eq f)
  rw [SchwartzMap.fourier_coe, Real.fourier_real_eq_integral_exp_smul] at h
  convert h using 1
  apply integral_congr_ae
  filter_upwards with ξ
  simp only [smul_eq_mul, realPhase, mul_comm]

/-- The remaining quadratic Fourier multiplier differs from one by at most
π ξ² / |t|, uniformly in the stationary point. -/
theorem norm_quadratic_multiplier_sub_one {t : ℝ} (ξ : ℝ) :
    ‖realPhase (-Real.pi / t * ξ ^ 2) - 1‖ ≤ Real.pi / |t| * ξ ^ 2 := by
  calc
    _ ≤ ‖-Real.pi / t * ξ ^ 2‖ := Real.norm_exp_I_mul_ofReal_sub_one_le
    _ = _ := by
      simp only [Real.norm_eq_abs, abs_mul, abs_div, abs_neg, abs_of_pos Real.pi_pos,
        abs_of_nonneg (sq_nonneg ξ)]

@[simp] theorem realPhase_add (x y : ℝ) :
    realPhase (x + y) = realPhase x * realPhase y := by
  simp [realPhase, Complex.ofReal_add, mul_add, Complex.exp_add]

theorem uniform_quadratic_error (f : 𝓢(ℝ, ℂ)) {t : ℝ} (ht : t ≠ 0) (u : ℝ) :
    ∃ E : ℂ,
      ‖E‖ ≤ Real.pi / |t| * (∫ ξ : ℝ, ξ ^ 2 * ‖(𝓕⁻ f : 𝓢(ℝ, ℂ)) ξ‖) ∧
      (∫ x : ℝ, f x * realPhase (Real.pi * t * x ^ 2 - 2 * Real.pi * u * x)) =
        (1 / (-Complex.I * (t : ℂ)) ^ (1 / 2 : ℂ) *
          realPhase (-Real.pi / t * u ^ 2)) * (f (u / t) + E) := by
  let p : ℝ → ℝ := fun ξ ↦ -2 * Real.pi * ξ * (u / t)
  let q : ℝ → ℝ := fun ξ ↦ -Real.pi / t * ξ ^ 2
  let d : ℝ → ℂ := fun ξ ↦ (𝓕⁻ f : 𝓢(ℝ, ℂ)) ξ * realPhase (p ξ) * (realPhase (q ξ) - 1)
  have hp : Continuous p := by unfold p; fun_prop
  have hq : Continuous q := by unfold q; fun_prop
  have hl := integrable_schwartz_phase (𝓕⁻ f : 𝓢(ℝ, ℂ)) p hp
  have ht' := integrable_schwartz_phase (𝓕⁻ f : 𝓢(ℝ, ℂ)) (fun ξ ↦ p ξ + q ξ) (hp.add hq)
  have hd : Integrable d := by
    convert ht'.sub hl using 1
    ext ξ
    simp only [d, realPhase_add, Pi.sub_apply]
    ring
  refine ⟨∫ ξ, d ξ, ?_, ?_⟩
  · have hm : Integrable (fun ξ : ℝ ↦ ξ ^ 2 * ‖(𝓕⁻ f : 𝓢(ℝ, ℂ)) ξ‖) := by
      have h : Integrable (fun ξ : ℝ ↦ ‖ξ‖ ^ 2 * ‖(𝓕⁻ f : 𝓢(ℝ, ℂ)) ξ‖) :=
        (𝓕⁻ f : 𝓢(ℝ, ℂ)).integrable_pow_mul volume 2
      simpa only [Real.norm_eq_abs, sq_abs] using h
    calc
      ‖∫ ξ, d ξ‖ ≤ ∫ ξ, ‖d ξ‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ ξ : ℝ, (Real.pi / |t|) * (ξ ^ 2 * ‖(𝓕⁻ f : 𝓢(ℝ, ℂ)) ξ‖) := by
        apply integral_mono hd.norm (hm.const_mul _)
        intro ξ
        simp only [d, norm_mul, norm_realPhase, mul_one]
        calc
          _ ≤ ‖(𝓕⁻ f : 𝓢(ℝ, ℂ)) ξ‖ * (Real.pi / |t| * ξ ^ 2) :=
            mul_le_mul_of_nonneg_left (norm_quadratic_multiplier_sub_one ξ) (norm_nonneg _)
          _ = _ := by ring
      _ = _ := integral_const_mul _ _
  · have hlin : (∫ ξ : ℝ, (𝓕⁻ f : 𝓢(ℝ, ℂ)) ξ * realPhase (p ξ)) = f (u / t) :=
      integral_schwartz_inverse_linear f (u / t)
    have hsum : (∫ ξ : ℝ, (𝓕⁻ f : 𝓢(ℝ, ℂ)) ξ * realPhase (p ξ + q ξ)) =
        f (u / t) + ∫ ξ, d ξ := by
      rw [← hlin, ← integral_add hl hd]
      apply integral_congr_ae
      filter_upwards with ξ
      simp only [d, realPhase_add]
      ring
    have hphase (ξ : ℝ) :
        realPhase (-Real.pi / t * (ξ + u) ^ 2) =
          realPhase (-Real.pi / t * u ^ 2) * realPhase (p ξ + q ξ) := by
      rw [← realPhase_add]
      congr 1
      dsimp [p, q]
      ring
    rw [integral_schwartz_quadratic_exact f ht u]
    simp_rw [hphase]
    have hi : (∫ ξ : ℝ, (𝓕⁻ f : 𝓢(ℝ, ℂ)) ξ *
          (realPhase (-Real.pi / t * u ^ 2) * realPhase (p ξ + q ξ))) =
        realPhase (-Real.pi / t * u ^ 2) *
          (∫ ξ : ℝ, (𝓕⁻ f : 𝓢(ℝ, ℂ)) ξ * realPhase (p ξ + q ξ)) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with ξ
      ring
    rw [hi, hsum]
    ring

/-- The prefactor in uniform quadratic integration has precisely the required
modulus. No pointwise lower estimate for a Littlewood polynomial is involved. -/
theorem norm_quadratic_prefactor (t u : ℝ) :
    ‖1 / (-Complex.I * (t : ℂ)) ^ (1 / 2 : ℂ) *
        realPhase (-Real.pi / t * u ^ 2)‖ = 1 / Real.sqrt |t| := by
  rw [norm_mul, norm_realPhase, mul_one, norm_div, norm_one]
  congr 1
  have hexp : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
  rw [hexp, Complex.norm_cpow_real]
  simp only [norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs]
  exact (Real.sqrt_eq_rpow _).symm

/-- The argument of the nonzero imaginary curvature, on the principal branch. -/
theorem arg_negative_imaginary {t : ℝ} (ht : t ≠ 0) :
    Complex.arg (-Complex.I * (t : ℂ)) = -Real.sign t * Real.pi / 2 := by
  rcases lt_or_gt_of_ne ht with ht | ht
  · have heq : -Complex.I * (t : ℂ) = Complex.I * ((-t : ℝ) : ℂ) := by
      push_cast
      ring
    rw [heq, Complex.arg_mul_real (neg_pos.mpr ht), Complex.arg_I,
      Real.sign_of_neg ht]
    ring
  · rw [Complex.arg_mul_real ht, Complex.arg_neg_I, Real.sign_of_pos ht]
    ring

theorem quadratic_prefactor_eq {t : ℝ} (ht : t ≠ 0) (u : ℝ) :
    (1 / (-Complex.I * (t : ℂ)) ^ (1 / 2 : ℂ)) *
        realPhase (-Real.pi / t * u ^ 2) =
      realPhase (Real.pi * Real.sign t / 4 - Real.pi * u ^ 2 / t) /
        (Real.sqrt |t| : ℂ) := by
  have he : -(1 / 2 : ℂ) = ((-(1 / 2) : ℝ) : ℂ) := by norm_num
  rw [one_div, ← Complex.cpow_neg, he, Complex.cpow_ofReal]
  rw [norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
    Real.rpow_neg (abs_nonneg t), ← Real.sqrt_eq_rpow, arg_negative_imaginary ht]
  have harg : (-Real.sign t * Real.pi / 2) * (-(1 / 2)) =
      Real.pi * Real.sign t / 4 := by ring
  rw [harg]
  have hphase (x : ℝ) : (Real.cos x : ℂ) + (Real.sin x : ℂ) * Complex.I = realPhase x := by
    unfold realPhase
    rw [mul_comm Complex.I, Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
  rw [hphase]
  rw [mul_assoc, ← realPhase_add]
  have heq : Real.pi * Real.sign t / 4 + -Real.pi / t * u ^ 2 =
      Real.pi * Real.sign t / 4 - Real.pi * u ^ 2 / t := by ring
  rw [heq]
  push_cast
  ring

theorem uniform_quadratic_integration (g : ℝ → ℂ) (hg : HasCompactSupport g)
    (hgs : ContDiff ℝ ∞ g) {β : ℝ} (hβ : β ≠ 0) {T : ℝ} (hT : 0 < T) (u : ℝ) :
    ∃ E : ℂ,
      ‖E‖ ≤ (Real.pi / |β| * (∫ ξ : ℝ, ξ ^ 2 *
        ‖(𝓕⁻ (hg.toSchwartzMap hgs) : 𝓢(ℝ, ℂ)) ξ‖)) / T ∧
      (∫ x : ℝ, g x * realPhase (2 * Real.pi * (T * β * x ^ 2 / 2 - u * x))) =
        (realPhase (2 * Real.pi * (Real.sign β / 8 - u ^ 2 / (2 * T * β))) /
          (Real.sqrt (T * |β|) : ℂ)) * (g (u / (T * β)) + E) := by
  obtain ⟨E, hE, hEq⟩ := uniform_quadratic_error (hg.toSchwartzMap hgs)
    (mul_ne_zero hT.ne' hβ) u
  refine ⟨E, ?_, ?_⟩
  · convert hE using 1
    rw [abs_mul, abs_of_pos hT]
    ring
  · rw [quadratic_prefactor_eq (mul_ne_zero hT.ne' hβ)] at hEq
    have hs : Real.sign (T * β) = Real.sign β := by
      rcases lt_or_gt_of_ne hβ with hβ | hβ
      · rw [Real.sign_of_neg (mul_neg_of_pos_of_neg hT hβ), Real.sign_of_neg hβ]
      · rw [Real.sign_of_pos (mul_pos hT hβ), Real.sign_of_pos hβ]
    have hnorm : |T * β| = T * |β| := by rw [abs_mul, abs_of_pos hT]
    simp only [hs, hnorm, HasCompactSupport.toSchwartzMap] at hEq
    convert hEq using 1
    · apply integral_congr_ae
      filter_upwards with x
      congr 2
      ring
    · congr 2
      congr 1
      ring

end
end AsymptoticallyMinimalLittlewood

end OAI



namespace OAI

universe u v w

namespace AsymptoticallyMinimalLittlewood
noncomputable section
open MeasureTheory Complex Real FourierTransform Filter Topology
open scoped FourierTransform SchwartzMap ContDiff

/-- A Boolean encoding of a real sign. -/
def boolSign (b : Bool) : ℝ := if b then 1 else -1

@[simp] theorem abs_boolSign (b : Bool) : |boolSign b| = 1 := by
  cases b <;> norm_num [boolSign]

/-- Elementary Rademacher MGF bound for one bounded coefficient. -/
theorem bool_exp_sum_le {a : ℝ} (ha : |a| ≤ 1) (t : ℝ) :
    (∑ b : Bool, Real.exp (t * a * boolSign b)) ≤ 2 * Real.exp (t ^ 2 / 2) := by
  simp only [Fintype.sum_bool, boolSign, ite_true, Bool.false_eq_true,
    ite_false, mul_one, mul_neg_one]
  calc
    Real.exp (t * a) + Real.exp (-(t * a)) = 2 * Real.cosh (t * a) := by
      rw [Real.cosh_eq]; ring
    _ ≤ 2 * Real.exp ((t * a) ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left (Real.cosh_le_exp_half_sq _) (by norm_num)
    _ ≤ 2 * Real.exp (t ^ 2 / 2) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Real.exp_le_exp.mpr
      have ha2 : a ^ 2 ≤ 1 := by nlinarith [sq_abs a, abs_nonneg a]
      nlinarith [mul_nonneg (sq_nonneg t) (sub_nonneg.mpr ha2)]

/-- MGF bound for all signings of a bounded real row, with counting measure. -/
theorem signing_exp_sum_le {α : Type u} [Fintype α] [DecidableEq α] (a : α → ℝ)
    (ha : ∀ k, |a k| ≤ 1) (t : ℝ) :
    (∑ x : α → Bool, Real.exp (t * ∑ k, a k * boolSign (x k))) ≤
      2 ^ Fintype.card α * Real.exp (t ^ 2 * Fintype.card α / 2) := by
  classical
  calc
    _ = ∏ k : α, ∑ b : Bool, Real.exp (t * a k * boolSign b) := by
      rw [Fintype.prod_sum]
      apply Finset.sum_congr rfl
      intro x hx
      rw [← Real.exp_sum]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ ≤ ∏ _k : α, 2 * Real.exp (t ^ 2 / 2) := by
      apply Finset.prod_le_prod
      · intro k hk; positivity
      · intro k hk; exact bool_exp_sum_le (ha k) t
    _ = _ := by
      simp only [Finset.prod_const, Finset.card_univ, mul_pow]
      rw [← Real.exp_nat_mul]
      congr 2
      ring

/-- A pointwise bound for the cost of quantizing a row sum. -/
theorem round_abs_le_exp_pair {x d t : ℝ} (hd : 0 < d) (ht : 0 ≤ t)
    (htd : 4 ≤ t * d) :
    |(round (x / d) : ℝ)| ≤
      Real.exp (t * x - t * d / 4) + Real.exp (-t * x - t * d / 4) := by
  by_cases hq : round (x / d) = 0
  · rw [hq, Int.cast_zero, abs_zero]
    positivity
  have hq1 : (1 : ℝ) ≤ |(round (x / d) : ℝ)| := by
    have hi : (1 : ℤ) ≤ |round (x / d)| := by
      have := abs_pos.mpr hq
      omega
    exact_mod_cast hi
  have hbound : |(round (x / d) : ℝ)| ≤ |x| / d + 1 / 2 := by
    calc
      _ ≤ |x / d| + |x / d - (round (x / d) : ℝ)| := by
        have h := abs_add_le (x / d) (-(x / d - (round (x / d) : ℝ)))
        simp only [abs_neg] at h
        convert h using 1; congr 1; ring
      _ ≤ _ := by
        rw [abs_div, abs_of_pos hd]
        gcongr
        exact abs_sub_round (x / d)
  have hxd : (|(round (x / d) : ℝ)| - 1 / 2) * d ≤ |x| := by
    have := (le_div_iff₀ hd).mp (by linarith :
      |(round (x / d) : ℝ)| - 1 / 2 ≤ |x| / d)
    exact this
  have hcost : |(round (x / d) : ℝ)| ≤ t * |x| - t * d / 4 := by
    have hmul := mul_le_mul_of_nonneg_left hxd ht
    have hprod := mul_nonneg (sub_nonneg.mpr hq1) (sub_nonneg.mpr htd)
    nlinarith
  have hxexp : |(round (x / d) : ℝ)| ≤ Real.exp (t * |x| - t * d / 4) := by
    nlinarith [Real.add_one_le_exp (t * |x| - t * d / 4)]
  apply hxexp.trans
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_of_nonneg hx]
    exact le_add_of_nonneg_right (Real.exp_pos _).le
  · rw [abs_of_neg hx, mul_neg, ← neg_mul]
    exact le_add_of_nonneg_left (Real.exp_pos _).le

/-- Counting-measure bound for the average quantization cost of a bounded row. -/
theorem signing_round_sum_le {α : Type u} [Fintype α] [DecidableEq α] (a : α → ℝ)
    (ha : ∀ k, |a k| ≤ 1) {d t : ℝ} (hd : 0 < d) (ht : 0 ≤ t)
    (htd : 4 ≤ t * d) :
    (∑ x : α → Bool, |(round ((∑ k, a k * boolSign (x k)) / d) : ℝ)|) ≤
      2 ^ Fintype.card α * (2 * Real.exp (t ^ 2 * Fintype.card α / 2 - t * d / 4)) := by
  classical
  calc
    _ ≤ ∑ x : α → Bool,
        (Real.exp (t * (∑ k, a k * boolSign (x k)) - t * d / 4) +
        Real.exp (-t * (∑ k, a k * boolSign (x k)) - t * d / 4)) := by
      exact Finset.sum_le_sum fun x hx ↦ round_abs_le_exp_pair hd ht htd
    _ = (Real.exp (-(t * d / 4))) *
        ((∑ x : α → Bool, Real.exp (t * ∑ k, a k * boolSign (x k))) +
        (∑ x : α → Bool, Real.exp (-t * ∑ k, a k * boolSign (x k)))) := by
      simp_rw [Real.exp_sub, div_eq_mul_inv, ← Real.exp_neg]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
      ring
    _ ≤ Real.exp (-(t * d / 4)) *
        (2 ^ Fintype.card α * Real.exp (t ^ 2 * Fintype.card α / 2) +
        2 ^ Fintype.card α * Real.exp ((-t) ^ 2 * Fintype.card α / 2)) := by
      exact mul_le_mul_of_nonneg_left
        (add_le_add (signing_exp_sum_le a ha t) (signing_exp_sum_le a ha (-t)))
        (Real.exp_pos _).le
    _ = _ := by
      simp only [neg_sq, Real.exp_sub, div_eq_mul_inv, Real.exp_neg]
      ring

/-- The geometric partition function for integer quantization labels. -/
theorem int_geometric_sum_le (S : Finset ℤ) {q : ℝ} (hq : 0 ≤ q) (hq' : q ≤ 1 / 2) :
    (∑ z ∈ S, q ^ z.natAbs) ≤ Real.exp (4 * q) := by
  have hq1 : q < 1 := by linarith
  have hnat : HasSum (fun n : ℕ ↦ q ^ (n : ℤ).natAbs) (1 - q)⁻¹ := by
    simpa using hasSum_geometric_of_lt_one hq hq1
  have hneg : HasSum (fun n : ℕ ↦ q ^ (-(n : ℤ)).natAbs) (1 - q)⁻¹ := by
    simpa using hasSum_geometric_of_lt_one hq hq1
  have hfull := HasSum.of_nat_of_neg (f := fun z : ℤ ↦ q ^ z.natAbs) hnat hneg
  have hsum : (∑ z ∈ S, q ^ z.natAbs) ≤ (1 - q)⁻¹ + (1 - q)⁻¹ - 1 := by
    simpa using (hfull.summable.sum_le_tsum S (fun z hz ↦ pow_nonneg hq _)).trans_eq
      hfull.tsum_eq
  have hden : 0 < 1 - q := by linarith
  have hinv : (1 - q)⁻¹ ≤ (2 : ℝ) := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hden).mpr
    linarith
  have hid : (1 - q)⁻¹ + (1 - q)⁻¹ - 1 = 1 + 2 * q * (1 - q)⁻¹ := by
    field_simp [ne_of_gt hden]
    ring
  have hrat : (1 - q)⁻¹ + (1 - q)⁻¹ - 1 ≤ 1 + 4 * q := by
    rw [hid]
    have := mul_le_mul_of_nonneg_left hinv (show 0 ≤ 2 * q by positivity)
    nlinarith
  exact hsum.trans (hrat.trans (by simpa [add_comm] using Real.add_one_le_exp (4 * q)))

/-- Each integer code has exponentially decaying weight. -/
theorem int_exp_sum_le (S : Finset ℤ) (a : ℝ) (ha : Real.exp (-a) ≤ 1 / 2) :
    (∑ z ∈ S, Real.exp (-a * |(z : ℝ)|)) ≤ Real.exp (4 * Real.exp (-a)) := by
  have heq (z : ℤ) : Real.exp (-a * |(z : ℝ)|) = Real.exp (-a) ^ z.natAbs := by
    have hc : (z.natAbs : ℝ) = |(z : ℝ)| := by
      rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]
    rw [← hc, mul_comm, Real.exp_nat_mul]
  simp_rw [heq]
  exact int_geometric_sum_le S (Real.exp_pos _).le ha

/-- Finite families of quantization codes inherit a product partition bound. -/
theorem code_exp_sum_le {β : Type v} [Fintype β] [DecidableEq β]
    (C : Finset (β → ℤ)) (a : ℝ) (ha : Real.exp (-a) ≤ 1 / 2) :
    (∑ c ∈ C, Real.exp (-a * ∑ i, |(c i : ℝ)|)) ≤
      Real.exp (4 * Fintype.card β * Real.exp (-a)) := by
  classical
  let S : β → Finset ℤ := fun i ↦ C.image (fun c ↦ c i)
  have hsub : C ⊆ Fintype.piFinset S := by
    intro c hc
    exact Fintype.mem_piFinset.mpr fun i ↦ Finset.mem_image.mpr ⟨c, hc, rfl⟩
  calc
    _ ≤ ∑ c ∈ Fintype.piFinset S, Real.exp (-a * ∑ i, |(c i : ℝ)|) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ ↦ (Real.exp_pos _).le)
    _ = ∏ i : β, ∑ z ∈ S i, Real.exp (-a * |(z : ℝ)|) := by
      simp_rw [Finset.mul_sum, Real.exp_sum]
      exact (Finset.prod_univ_sum S (fun _ z ↦ Real.exp (-a * |(z : ℝ)|))).symm
    _ ≤ ∏ _i : β, Real.exp (4 * Real.exp (-a)) := by
      apply Finset.prod_le_prod
      · intro i hi; positivity
      · intro i hi; exact int_exp_sum_le (S i) a ha
    _ = _ := by
      simp only [Finset.prod_const, Finset.card_univ]
      rw [← Real.exp_nat_mul]
      congr 1
      ring

/-- A cost bound controls the number of possible quantization codes. -/
theorem code_card_le {β : Type v} [Fintype β] [DecidableEq β]
    (C : Finset (β → ℤ)) {a M : ℝ} (ha0 : 0 ≤ a)
    (ha : Real.exp (-a) ≤ 1 / 2) (hM : ∀ c ∈ C, (∑ i, |(c i : ℝ)|) ≤ M) :
    (C.card : ℝ) ≤ Real.exp (a * M + 4 * Fintype.card β * Real.exp (-a)) := by
  have hlow : (C.card : ℝ) * Real.exp (-a * M) ≤
      ∑ c ∈ C, Real.exp (-a * ∑ i, |(c i : ℝ)|) := by
    calc
      _ = ∑ _c ∈ C, Real.exp (-a * M) := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro c hc
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left (hM c hc) (neg_nonpos.mpr ha0))
  have hfull := mul_le_mul_of_nonneg_left (hlow.trans (code_exp_sum_le C a ha))
    (Real.exp_pos (a * M)).le
  rw [← mul_assoc, mul_comm (Real.exp (a * M)) (C.card : ℝ), mul_assoc,
    ← Real.exp_add, show a * M + -a * M = 0 by ring, Real.exp_zero, mul_one,
    ← Real.exp_add] at hfull
  exact hfull

/-- Partition function of Hamming distance on the Boolean cube. -/
theorem hamming_exp_sum {α : Type u} [Fintype α] [DecidableEq α]
    (x : α → Bool) (a : ℝ) :
    (∑ y : α → Bool, Real.exp (-a * hammingDist x y)) =
      (1 + Real.exp (-a)) ^ Fintype.card α := by
  classical
  have hcast (y : α → Bool) : (hammingDist x y : ℝ) =
      ∑ k : α, if x k ≠ y k then (1 : ℝ) else 0 := by
    exact (Finset.sum_boole (fun k ↦ x k ≠ y k) Finset.univ).symm
  simp_rw [hcast, Finset.mul_sum, Real.exp_sum]
  rw [← Fintype.prod_sum (fun k b ↦ Real.exp (-a * if x k ≠ b then (1 : ℝ) else 0))]
  have hstep (k : α) : (∑ b : Bool, Real.exp (-a * if x k ≠ b then (1 : ℝ) else 0)) =
      1 + Real.exp (-a) := by
    cases x k <;> simp [add_comm]
  simp_rw [hstep]
  simp

/-- A small Hamming ball occupies exponentially less than the whole cube. -/
theorem hamming_small_family_card {α : Type u} [Fintype α] [DecidableEq α]
    (G : Finset (α → Bool)) (x : α → Bool)
    (hG : ∀ y ∈ G, (hammingDist x y : ℝ) ≤ (Fintype.card α : ℝ) / 16) :
    (G.card : ℝ) ≤ Real.exp (3 * Fintype.card α / 8) := by
  have he2 : Real.exp (-2) ≤ 1 / 4 := by
    rw [Real.exp_neg]
    apply (inv_le_comm₀ (Real.exp_pos _) (by norm_num)).mpr
    have h2 : 2 ≤ Real.exp 1 := by have := Real.add_one_le_exp 1; norm_num at this; exact this
    have hh := mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 2) h2
    rw [← Real.exp_add] at hh
    norm_num at hh ⊢
    exact hh
  have hsum : (∑ y : α → Bool, Real.exp (-2 * hammingDist x y)) ≤
      Real.exp (Fintype.card α / 4) := by
    rw [hamming_exp_sum]
    calc
      _ ≤ Real.exp (1 / 4) ^ Fintype.card α := by
        apply pow_le_pow_left₀ (by positivity)
        linarith [Real.add_one_le_exp (1 / 4)]
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  have hlow : (G.card : ℝ) * Real.exp (-(Fintype.card α : ℝ) / 8) ≤
      ∑ y : α → Bool, Real.exp (-2 * hammingDist x y) := by
    calc
      _ = ∑ _y ∈ G, Real.exp (-(Fintype.card α : ℝ) / 8) := by simp
      _ ≤ ∑ y ∈ G, Real.exp (-2 * hammingDist x y) := by
        apply Finset.sum_le_sum
        intro y hy
        apply Real.exp_le_exp.mpr
        have := hG y hy
        linarith
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun _ _ _ ↦ (Real.exp_pos _).le)
  have h := mul_le_mul_of_nonneg_left (hlow.trans hsum)
    (Real.exp_pos ((Fintype.card α : ℝ) / 8)).le
  have heq : (Fintype.card α : ℝ) / 8 + -(Fintype.card α : ℝ) / 8 = 0 := by ring
  rw [← mul_assoc, mul_comm (Real.exp _) (G.card : ℝ), mul_assoc, ← Real.exp_add,
    heq, Real.exp_zero, mul_one, ← Real.exp_add] at h
  convert h using 1
  congr 1
  ring

/-- A nonnegative cost with small average is small on at least half a finite set. -/
theorem card_good_cost {γ : Type w} [Fintype γ] [DecidableEq γ]
    (f : γ → ℝ) (hf : ∀ x, 0 ≤ f x) {M : ℝ} (hM : 0 < M)
    (hsum : (∑ x, f x) ≤ (Fintype.card γ : ℝ) * M / 2) :
    (Fintype.card γ : ℝ) / 2 ≤ ((Finset.univ.filter fun x ↦ f x ≤ M).card : ℝ) := by
  classical
  let G := Finset.univ.filter fun x ↦ f x ≤ M
  let B := Finset.univ.filter fun x ↦ ¬ f x ≤ M
  have hcard : G.card + B.card = Fintype.card γ := by
    exact Finset.card_filter_add_card_filter_not _
  have hlow : (B.card : ℝ) * M ≤ ∑ x, f x := by
    calc
      _ = ∑ _x ∈ B, M := by simp
      _ ≤ ∑ x ∈ B, f x := by
        apply Finset.sum_le_sum
        intro x hx
        exact (lt_of_not_ge (Finset.mem_filter.mp hx).2).le
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun x _ _ ↦ hf x)
  have hc : (G.card : ℝ) + (B.card : ℝ) = Fintype.card γ := by exact_mod_cast hcard
  change _ ≤ (G.card : ℝ)
  nlinarith

/-- A large set of Boolean vectors contains a far pair with the same low-cost code. -/
theorem exists_same_code_far {α : Type u} {β : Type v} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (G : Finset (α → Bool))
    (code : (α → Bool) → β → ℤ) {a M : ℝ} (ha0 : 0 ≤ a)
    (ha : Real.exp (-a) ≤ 1 / 2)
    (hcost : ∀ x ∈ G, (∑ i, |(code x i : ℝ)|) ≤ M)
    (hlarge : Real.exp (a * M + 4 * Fintype.card β * Real.exp (-a) +
      3 * Fintype.card α / 8) < (G.card : ℝ)) :
    ∃ x ∈ G, ∃ y ∈ G, code x = code y ∧
      (Fintype.card α : ℝ) / 16 < (hammingDist x y : ℝ) := by
  classical
  by_contra h
  have hnear : ∀ x ∈ G, ∀ y ∈ G, code x = code y →
      (hammingDist x y : ℝ) ≤ (Fintype.card α : ℝ) / 16 := by
    intro x hx y hy hxy
    by_contra! hn
    exact h ⟨x, hx, y, hy, hxy, hn⟩
  let C := G.image code
  have hC : (C.card : ℝ) ≤ Real.exp (a * M + 4 * Fintype.card β * Real.exp (-a)) := by
    apply code_card_le C ha0 ha
    intro c hc
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hc
    exact hcost x hx
  have hfiber (c : β → ℤ) (hc : c ∈ C) :
      ((G.filter fun x ↦ code x = c).card : ℝ) ≤ Real.exp (3 * Fintype.card α / 8) := by
    obtain ⟨x, hx, hxc⟩ := Finset.mem_image.mp hc
    apply hamming_small_family_card _ x
    intro y hy
    obtain ⟨hy, hyc⟩ := Finset.mem_filter.mp hy
    exact hnear x hx y hy (hxc.trans hyc.symm)
  have htotal : (G.card : ℝ) ≤ (C.card : ℝ) * Real.exp (3 * Fintype.card α / 8) := by
    calc
      _ = ∑ c ∈ C, ((G.filter fun x ↦ code x = c).card : ℝ) := by
        simpa using (Finset.sum_fiberwise_of_maps_to
          (fun x hx ↦ Finset.mem_image.mpr ⟨x, hx, rfl⟩ : ∀ x ∈ G, code x ∈ C)
          (fun _ ↦ (1 : ℝ))).symm
      _ ≤ ∑ _c ∈ C, Real.exp (3 * Fintype.card α / 8) := Finset.sum_le_sum hfiber
      _ = _ := by simp
  have hbound := htotal.trans (mul_le_mul_of_nonneg_right hC
    (Real.exp_pos (3 * Fintype.card α / 8)).le)
  rw [← Real.exp_add] at hbound
  exact (not_lt_of_ge hbound) hlarge

/-- Numerical entropy estimates, with fixed generous absolute constants. -/
theorem entropy_log_parameters {s R : ℝ} (hs : 0 < s) (hsR : s ≤ R) :
    let L := Real.log (16 * R / s)
    1 / 2 ≤ L ∧ Real.exp (-4 * L) ≤ 1 / 2 ∧
      2 * R * Real.exp (-128 * L) ≤ s / (512 * L) ∧
      4 * R * Real.exp (-4 * L) ≤ s / 64 := by
  dsimp only
  let L := Real.log (16 * R / s)
  change 1 / 2 ≤ L ∧ _
  have hR : 0 < R := hs.trans_le hsR
  have hratio : (16 : ℝ) ≤ 16 * R / s := (le_div_iff₀ hs).mpr (by nlinarith)
  have hratio0 : 0 < 16 * R / s := by positivity
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at this ⊢
    exact this
  have hL : (1 / 2 : ℝ) ≤ L := hlog2.trans (Real.log_le_log (by norm_num) (by linarith))
  have hL0 : 0 < L := by linarith
  have heq : Real.exp (-L) = s / (16 * R) := by
    dsimp [L]
    rw [Real.exp_neg, Real.exp_log hratio0, inv_div]
  have he : Real.exp (-L) ≤ 1 / 16 := by
    rw [heq]
    apply (div_le_iff₀ (by positivity : 0 < 16 * R)).mpr
    nlinarith
  have hbase : R * Real.exp (-L) = s / 16 := by
    rw [heq]
    field_simp

  have hfour : Real.exp (-4 * L) = Real.exp (-L) ^ 4 := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hdecay : Real.exp (-4 * L) ≤ 1 / 2 := by
    rw [hfour]
    calc
      _ ≤ (1 / 16 : ℝ) ^ 4 := pow_le_pow_left₀ (Real.exp_pos _).le he 4
      _ ≤ _ := by norm_num
  have hpart : 4 * R * Real.exp (-4 * L) ≤ s / 64 := by
    have hp : Real.exp (-L) ^ 3 ≤ 1 / 16 := by
      calc
        _ ≤ (1 / 16 : ℝ) ^ 3 := pow_le_pow_left₀ (Real.exp_pos _).le he 3
        _ ≤ _ := by norm_num
    calc
      _ = 4 * (R * Real.exp (-L)) * Real.exp (-L) ^ 3 := by rw [hfour]; ring
      _ = s / 4 * Real.exp (-L) ^ 3 := by rw [hbase]; ring
      _ ≤ s / 4 * (1 / 16) := mul_le_mul_of_nonneg_left hp (by positivity)
      _ = _ := by ring
  have hexp : 64 * L ≤ Real.exp (127 * L) := by
    nlinarith [Real.add_one_le_exp (127 * L)]
  have hmul : Real.exp (-128 * L) * (64 * L) ≤ Real.exp (-L) := by
    calc
      _ ≤ Real.exp (-128 * L) * Real.exp (127 * L) :=
        mul_le_mul_of_nonneg_left hexp (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hmean : 2 * R * Real.exp (-128 * L) ≤ s / (512 * L) := by
    apply (le_div_iff₀ (by positivity : 0 < 512 * L)).mpr
    calc
      _ = 16 * R * (Real.exp (-128 * L) * (64 * L)) := by ring
      _ ≤ 16 * R * Real.exp (-L) := mul_le_mul_of_nonneg_left hmul (by positivity)
      _ = s := by nlinarith [hbase]
  exact ⟨hL, hdecay, hmean, hpart⟩

/-- The Boolean cube is larger than the entropy bounds used above. -/
theorem exp_small_lt_half_cube {n : ℕ} (hn : 32 ≤ n) :
    Real.exp (13 * n / 32) < (2 : ℝ) ^ n / 2 := by
  have hl : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at this ⊢
    exact this
  have hu : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at this ⊢
    exact this
  have hn' : (32 : ℝ) ≤ n := by exact_mod_cast hn
  have hlt : 13 * (n : ℝ) / 32 < n * Real.log 2 - Real.log 2 := by
    have := mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    nlinarith
  calc
    _ < Real.exp (n * Real.log 2 - Real.log 2) := Real.exp_lt_exp.mpr hlt
    _ = _ := by rw [Real.exp_sub, Real.exp_nat_mul, Real.exp_log (by norm_num)]

/-- Entropy supplies two widely separated signings with identical rounded row sums. -/
theorem exists_signings_same_round {α : Type u} {β : Type v} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (B : β → α → ℝ)
    (hB : ∀ i k, |B i k| ≤ 1) (hs : 32 ≤ Fintype.card α)
    (hsR : Fintype.card α ≤ Fintype.card β) :
    let d := 64 * Real.sqrt ((Fintype.card α : ℝ) *
      Real.log (16 * Fintype.card β / Fintype.card α))
    ∃ x y : α → Bool, (Fintype.card α : ℝ) / 16 < (hammingDist x y : ℝ) ∧
      ∀ i, round ((∑ k, B i k * boolSign (x k)) / d) =
        round ((∑ k, B i k * boolSign (y k)) / d) := by
  classical
  let s : ℝ := Fintype.card α
  let R : ℝ := Fintype.card β
  let L := Real.log (16 * R / s)
  let d := 64 * Real.sqrt (s * L)
  let t := d / (4 * s)
  let M := s / (256 * L)
  have hs0 : 0 < s := by dsimp [s]; exact_mod_cast (by omega : 0 < Fintype.card α)
  have hsR' : s ≤ R := by dsimp [s, R]; exact_mod_cast hsR
  obtain ⟨hL, hdecay, hmean, hpart⟩ := entropy_log_parameters hs0 hsR'
  change 1 / 2 ≤ L at hL
  have hL0 : 0 < L := by linarith
  have hd : 0 < d := by dsimp [d]; positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hd2 : d ^ 2 = 4096 * s * L := by
    dsimp [d]
    nlinarith [Real.sq_sqrt (show 0 ≤ s * L by positivity)]
  have htd_eq : t * d = 1024 * L := by
    dsimp [t]
    rw [div_mul_eq_mul_div]
    apply (div_eq_iff (show 4 * s ≠ 0 by positivity)).mpr
    nlinarith [hd2]
  have htd : 4 ≤ t * d := by rw [htd_eq]; linarith
  have hexponent : t ^ 2 * s / 2 - t * d / 4 = -128 * L := by
    rw [htd_eq]
    have ht2 : t ^ 2 * s = 256 * L := by
      calc
        _ = d ^ 2 / (16 * s) := by dsimp [t]; field_simp; ring
        _ = 256 * L := by rw [hd2]; field_simp; ring
    rw [ht2]
    ring
  let code : (α → Bool) → β → ℤ := fun x i ↦
    round ((∑ k, B i k * boolSign (x k)) / d)
  let cost : (α → Bool) → ℝ := fun x ↦ ∑ i, |(code x i : ℝ)|
  have hcost0 : ∀ x, 0 ≤ cost x := fun x ↦ Finset.sum_nonneg fun i _ ↦ abs_nonneg _
  have hcostsum : (∑ x, cost x) ≤ (2 : ℝ) ^ Fintype.card α * M / 2 := by
    have hrow (i : β) : (∑ x : α → Bool, |(code x i : ℝ)|) ≤
        (2 : ℝ) ^ Fintype.card α * (2 * Real.exp (-128 * L)) := by
      have h := signing_round_sum_le (B i) (hB i) hd ht htd
      change _ ≤ (2 : ℝ) ^ Fintype.card α * (2 * Real.exp (t ^ 2 * s / 2 - t * d / 4)) at h
      rwa [hexponent] at h
    calc
      _ = ∑ i, ∑ x : α → Bool, |(code x i : ℝ)| := Finset.sum_comm
      _ ≤ ∑ _i : β, (2 : ℝ) ^ Fintype.card α * (2 * Real.exp (-128 * L)) :=
        Finset.sum_le_sum fun i _ ↦ hrow i
      _ = (2 : ℝ) ^ Fintype.card α * (2 * R * Real.exp (-128 * L)) := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        dsimp [R]
        ring
      _ ≤ (2 : ℝ) ^ Fintype.card α * (s / (512 * L)) :=
        mul_le_mul_of_nonneg_left hmean (by positivity)
      _ = _ := by dsimp [M]; ring
  let G := Finset.univ.filter fun x ↦ cost x ≤ M
  have hM : 0 < M := by dsimp [M]; positivity
  have hG : (2 : ℝ) ^ Fintype.card α / 2 ≤ (G.card : ℝ) := by
    have hc : (Fintype.card (α → Bool) : ℝ) = (2 : ℝ) ^ Fintype.card α := by simp
    have hh := card_good_cost cost hcost0 hM
    rw [hc] at hh
    exact hh hcostsum
  have haM : (4 * L) * M = s / 64 := by
    dsimp [M]
    field_simp
    ring
  have hlarge : Real.exp ((4 * L) * M + 4 * Fintype.card β * Real.exp (-(4 * L)) +
      3 * Fintype.card α / 8) < (G.card : ℝ) := by
    apply lt_of_lt_of_le _ hG
    apply lt_of_le_of_lt _ (exp_small_lt_half_cube hs)
    apply Real.exp_le_exp.mpr
    rw [haM]
    change s / 64 + 4 * R * Real.exp (-(4 * L)) + 3 * s / 8 ≤ 13 * s / 32
    have hp : 4 * R * Real.exp (-(4 * L)) ≤ s / 64 := by simpa only [neg_mul] using hpart
    linarith
  obtain ⟨x, hx, y, hy, hxy, hfar⟩ := exists_same_code_far G code
    (show 0 ≤ 4 * L by positivity) (by simpa only [neg_mul] using hdecay)
    (fun x hx ↦ (Finset.mem_filter.mp hx).2) hlarge
  exact ⟨x, y, hfar, fun i ↦ congrFun hxy i⟩

/-- A zero-start partial coloring fixes a fixed positive fraction of all coordinates. -/
theorem exists_partial_coloring {α : Type u} {β : Type v} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (B : β → α → ℝ)
    (hB : ∀ i k, |B i k| ≤ 1) (hs : 0 < Fintype.card α)
    (hsR : Fintype.card α ≤ Fintype.card β) :
    ∃ z : α → ℝ, (∀ k, z k = -1 ∨ z k = 0 ∨ z k = 1) ∧
      (Fintype.card α : ℝ) / 16 ≤ ((Finset.univ.filter fun k ↦ z k ≠ 0).card : ℝ) ∧
      ∀ i, |∑ k, B i k * z k| ≤ 64 * Real.sqrt ((Fintype.card α : ℝ) *
        Real.log (16 * Fintype.card β / Fintype.card α)) := by
  classical
  let s : ℝ := Fintype.card α
  let L := Real.log (16 * Fintype.card β / s)
  have hs0 : 0 < s := by dsimp [s]; exact_mod_cast hs
  have hsR' : s ≤ (Fintype.card β : ℝ) := by dsimp [s]; exact_mod_cast hsR
  have hL := (entropy_log_parameters hs0 hsR').1
  change 1 / 2 ≤ L at hL
  have hL0 : 0 < L := by linarith
  by_cases hn : 32 ≤ Fintype.card α
  · obtain ⟨x, y, hfar, heq⟩ := exists_signings_same_round B hB hn hsR
    let z : α → ℝ := fun k ↦ (boolSign (x k) - boolSign (y k)) / 2
    let d := 64 * Real.sqrt (s * L)
    have hd : 0 < d := by dsimp [d]; positivity
    have hz (k : α) : z k = -1 ∨ z k = 0 ∨ z k = 1 := by
      dsimp [z]
      cases x k <;> cases y k <;> norm_num [boolSign]
    have hcard : (Finset.univ.filter fun k ↦ z k ≠ 0).card = hammingDist x y := by
      unfold hammingDist
      congr 1
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      dsimp [z]
      cases x k <;> cases y k <;> norm_num [boolSign]
    refine ⟨z, hz, ?_, ?_⟩
    · rw [hcard]
      exact hfar.le
    · intro i
      let u := ∑ k, B i k * boolSign (x k)
      let v := ∑ k, B i k * boolSign (y k)
      have hq : round (u / d) = round (v / d) := heq i
      have hdiff : |u / d - v / d| ≤ 1 := by
        calc
          _ = |(u / d - (round (u / d) : ℝ)) + ((round (u / d) : ℝ) - v / d)| := by
            congr 1
            ring
          _ ≤ |u / d - (round (u / d) : ℝ)| + |(round (u / d) : ℝ) - v / d| := abs_add_le _ _
          _ ≤ 1 := by
            rw [hq, abs_sub_comm (round (v / d) : ℝ)]
            have hu := abs_sub_round (u / d)
            rw [hq] at hu
            linarith [abs_sub_round (v / d)]
      have huv : |u - v| ≤ d := by
        rw [← sub_div, abs_div, abs_of_pos hd] at hdiff
        have := (div_le_iff₀ hd).mp hdiff
        linarith
      change _ ≤ d
      calc
        _ = |(u - v) / 2| := by
          congr 1
          dsimp [u, v, z]
          simp only [← mul_div_assoc, mul_sub]
          rw [← Finset.sum_div, Finset.sum_sub_distrib]
        _ = |u - v| / 2 := by rw [abs_div]; norm_num
        _ ≤ d / 2 := by gcongr
        _ ≤ d := by linarith
  · refine ⟨fun _ ↦ 1, fun _ ↦ Or.inr (Or.inr rfl), ?_, ?_⟩
    · simp only [ne_eq, one_ne_zero, not_false_eq_true, Finset.filter_true,
        Finset.card_univ]
      nlinarith [(Nat.cast_nonneg (Fintype.card α) : (0 : ℝ) ≤ Fintype.card α)]
    · intro i
      have hsum : |∑ k, B i k * (1 : ℝ)| ≤ s := by
        calc
          _ ≤ ∑ k, |B i k * (1 : ℝ)| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _k : α, (1 : ℝ) := Finset.sum_le_sum fun k _ ↦ by simpa using hB i k
          _ = s := by simp [s]
      apply hsum.trans
      change s ≤ 64 * Real.sqrt (s * L)
      have hs32 : s ≤ 32 := by dsimp [s]; exact_mod_cast (by omega : Fintype.card α ≤ 32)
      have hq : (Real.sqrt (s * L)) ^ 2 = s * L := Real.sq_sqrt (by positivity)
      have hp := Real.sqrt_nonneg (s * L)
      nlinarith [mul_nonneg hs0.le (sub_nonneg.mpr hs32), mul_le_mul_of_nonneg_left hL hs0.le]

/-- The logarithmic discrepancy potential contracts on shortening the remaining columns. -/
theorem discrepancy_potential_contract {s u R : ℝ} (hs : 0 < s) (hsR : s ≤ R)
    (hu0 : 0 ≤ u) (hu : u ≤ (15 / 16) * s) :
    Real.sqrt (u * Real.log (16 * R / u)) ≤
      (63 / 64) * Real.sqrt (s * Real.log (16 * R / s)) := by
  by_cases hu_eq : u = 0
  · rw [hu_eq]
    simp only [zero_mul, Real.sqrt_zero]
    positivity
  have hu_pos : 0 < u := lt_of_le_of_ne hu0 (Ne.symm hu_eq)
  have hR : 0 < R := hs.trans_le hsR
  let L := Real.log (16 * R / s)
  have hratio : (16 : ℝ) ≤ 16 * R / s := (le_div_iff₀ hs).mpr (by nlinarith)
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at this ⊢
    exact this
  have hlog16 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    norm_num
  have hL : 2 ≤ L := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 16) hratio
    rw [hlog16] at hh
    change _ ≤ L at hh
    linarith
  have hL0 : 0 ≤ L := by linarith
  have hlog : Real.log (16 * R / u) = L + Real.log (s / u) := by
    have hid : 16 * R / u = (16 * R / s) * (s / u) := by field_simp
    rw [hid, Real.log_mul (by positivity : 16 * R / s ≠ 0) (by positivity : s / u ≠ 0)]
  have hsmall : u * Real.log (s / u) ≤ s - u := by
    calc
      _ ≤ u * (s / u - 1) := mul_le_mul_of_nonneg_left
        (Real.log_le_sub_one_of_pos (by positivity)) hu0
      _ = _ := by field_simp
  have hsq : u * Real.log (16 * R / u) ≤ (31 / 32) * (s * L) := by
    rw [hlog, mul_add]
    have hprod := mul_le_mul_of_nonneg_right hu (show 0 ≤ L - 1 by linarith)
    have hLs := mul_le_mul_of_nonneg_left hL hs.le
    nlinarith
  apply (Real.sqrt_le_left (by positivity : 0 ≤ (63 / 64) * Real.sqrt (s * L))).mpr
  have hsqrt := Real.sq_sqrt (mul_nonneg hs.le hL0)
  change u * Real.log (16 * R / u) ≤ ((63 / 64) * Real.sqrt (s * L)) ^ 2
  nlinarith [mul_nonneg hs.le hL0]

/-- Iterating the zero-start partial coloring proves the square-root logarithmic matrix bound. -/
theorem matrix_signing_raw (n : ℕ) :
    ∀ {α : Type u} {β : Type v} [Fintype α] [DecidableEq α]
      [Fintype β] [DecidableEq β], Fintype.card α = n →
      ∀ B : β → α → ℝ, (∀ i k, |B i k| ≤ 1) → Fintype.card α ≤ Fintype.card β →
      ∃ ξ : α → ℝ, (∀ k, ξ k = -1 ∨ ξ k = 1) ∧
        ∀ i, |∑ k, B i k * ξ k| ≤ 4096 * Real.sqrt ((Fintype.card α : ℝ) *
          Real.log (16 * Fintype.card β / Fintype.card α)) := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro α β _ _ _ _ hn B hB hsR
    by_cases hn0 : n = 0
    · have hc : Fintype.card α = 0 := hn.trans hn0
      let : IsEmpty α := Fintype.card_eq_zero_iff.mp hc
      refine ⟨fun _ ↦ 1, fun _ ↦ Or.inr rfl, ?_⟩
      intro i
      simp
    have hs : 0 < Fintype.card α := by omega
    have hs0 : (0 : ℝ) < Fintype.card α := by exact_mod_cast hs
    obtain ⟨z, hz, hfix, herr⟩ := exists_partial_coloring B hB hs hsR
    let U := {k : α // z k = 0}
    have hpartitionNat : Fintype.card U + (Finset.univ.filter fun k ↦ z k ≠ 0).card =
        Fintype.card α := by
      dsimp [U]
      rw [Fintype.card_subtype]
      exact Finset.card_filter_add_card_filter_not _
    have hpartition : (Fintype.card U : ℝ) +
        ((Finset.univ.filter fun k ↦ z k ≠ 0).card : ℝ) = Fintype.card α := by
      exact_mod_cast hpartitionNat
    have hUbound : (Fintype.card U : ℝ) ≤ (15 / 16) * Fintype.card α := by linarith
    have hUlt : Fintype.card U < n := by
      have hh : (Fintype.card U : ℝ) < Fintype.card α := by nlinarith
      have hh' : Fintype.card U < Fintype.card α := by exact_mod_cast hh
      omega
    have hUR : Fintype.card U ≤ Fintype.card β := by
      exact (Fintype.card_subtype_le (fun k ↦ z k = 0)).trans hsR
    obtain ⟨ξ, hξ, hξerr⟩ := ih (Fintype.card U) hUlt (α := U) (β := β) rfl
      (fun i k ↦ B i k) (fun i k ↦ hB i k) hUR
    let w : α → ℝ := fun k ↦ if hk : z k = 0 then ξ ⟨k, hk⟩ else z k
    have hw (k : α) : w k = -1 ∨ w k = 1 := by
      by_cases hk : z k = 0
      · simpa only [w, dif_pos hk] using hξ ⟨k, hk⟩
      · simp only [w, dif_neg hk]
        rcases hz k with hm | hzero | hp
        · exact Or.inl hm
        · exact (hk hzero).elim
        · exact Or.inr hp
    have hsum (i : β) : (∑ k, B i k * w k) = (∑ k, B i k * z k) +
        ∑ k : U, B i k * ξ k := by
      have hpart (f : α → ℝ) : (∑ k, f k) =
          (∑ k : U, f k) + ∑ k : {k : α // z k ≠ 0}, f k :=
        (Fintype.sum_subtype_add_sum_subtype (fun k ↦ z k = 0) f).symm
      rw [hpart (fun k ↦ B i k * w k), hpart (fun k ↦ B i k * z k)]
      have hzero : (∑ k : U, B i k * z k) = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        rw [k.property, mul_zero]
      have hwU : (∑ k : U, B i k * w k) = ∑ k : U, B i k * ξ k := by
        apply Finset.sum_congr rfl
        intro k hk
        simp [w, k.property]
      have hwc : (∑ k : {k : α // z k ≠ 0}, B i k * w k) =
          ∑ k : {k : α // z k ≠ 0}, B i k * z k := by
        apply Finset.sum_congr rfl
        intro k hk
        simp [w, k.property]
      rw [hzero, zero_add, hwU, hwc, add_comm]
    refine ⟨w, hw, fun i ↦ ?_⟩
    let P := Real.sqrt ((Fintype.card α : ℝ) *
      Real.log (16 * Fintype.card β / Fintype.card α))
    have hcontract := discrepancy_potential_contract hs0
      (show (Fintype.card α : ℝ) ≤ Fintype.card β by exact_mod_cast hsR)
      (Nat.cast_nonneg (Fintype.card U)) hUbound
    change _ ≤ (63 / 64) * P at hcontract
    rw [hsum]
    calc
      _ ≤ |∑ k, B i k * z k| + |∑ k : U, B i k * ξ k| := abs_add_le _ _
      _ ≤ 64 * P + 4096 * Real.sqrt ((Fintype.card U : ℝ) *
          Real.log (16 * Fintype.card β / Fintype.card U)) := add_le_add (herr i) (hξerr i)
      _ ≤ 64 * P + 4096 * ((63 / 64) * P) := by gcongr
      _ = _ := by change _ = 4096 * P; ring

theorem matrix_signing {α : Type u} {β : Type v} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (B : β → α → ℝ)
    (hB : ∀ i k, |B i k| ≤ 1) (hsR : Fintype.card α ≤ Fintype.card β) :
    ∃ ξ : α → ℝ, (∀ k, ξ k = -1 ∨ ξ k = 1) ∧
      ∀ i, |∑ k, B i k * ξ k| ≤ 8192 * Real.sqrt ((Fintype.card α : ℝ) *
        Real.log (2 * Fintype.card β / Fintype.card α)) := by
  obtain ⟨ξ, hξ, herr⟩ := matrix_signing_raw (Fintype.card α) rfl B hB hsR
  refine ⟨ξ, hξ, fun i ↦ (herr i).trans ?_⟩
  by_cases hs : Fintype.card α = 0
  · simp [hs]
  have hs0 : (0 : ℝ) < Fintype.card α := by exact_mod_cast Nat.pos_of_ne_zero hs
  have hR0 : (0 : ℝ) < Fintype.card β := hs0.trans_le (by exact_mod_cast hsR)
  let x : ℝ := Fintype.card β / Fintype.card α
  have hx : 1 ≤ x := (le_div_iff₀ hs0).mpr (by simpa using (show (Fintype.card α : ℝ) ≤ Fintype.card β by exact_mod_cast hsR))
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx
  have h16 : Real.log (16 * x) ≤ 4 * Real.log (2 * x) := by
    rw [Real.log_mul (by norm_num) hx0.ne', Real.log_mul (by norm_num) hx0.ne',
      show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    norm_num
    linarith
  have hlog2x : 0 ≤ Real.log (2 * x) := Real.log_nonneg (by linarith)
  have hsq : Real.sqrt ((Fintype.card α : ℝ) * Real.log (16 * x)) ≤
      2 * Real.sqrt ((Fintype.card α : ℝ) * Real.log (2 * x)) := by
    apply (Real.sqrt_le_left (by positivity)).mpr
    have hh := Real.sq_sqrt (mul_nonneg hs0.le hlog2x)
    nlinarith [mul_le_mul_of_nonneg_left h16 hs0.le]
  dsimp [x] at hsq
  simp only [← mul_div_assoc] at hsq
  nlinarith

/-- Reversing a signing preserves discrepancy and allows its total sum to be nonpositive. -/
theorem matrix_signing_nonpos {α : Type u} {β : Type v}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (B : β → α → ℝ) (hB : ∀ i k, |B i k| ≤ 1)
    (hsR : Fintype.card α ≤ Fintype.card β) :
    ∃ ξ : α → ℝ, (∀ k, ξ k = -1 ∨ ξ k = 1) ∧ (∑ k, ξ k) ≤ 0 ∧
      ∀ i, |∑ k, B i k * ξ k| ≤ 8192 * Real.sqrt ((Fintype.card α : ℝ) *
        Real.log (2 * Fintype.card β / Fintype.card α)) := by
  obtain ⟨ξ, hξ, herr⟩ := matrix_signing B hB hsR
  by_cases hsum : (∑ k, ξ k) ≤ 0
  · exact ⟨ξ, hξ, hsum, herr⟩
  refine ⟨fun k ↦ -ξ k, ?_, ?_, ?_⟩
  · intro k
    rcases hξ k with hk | hk <;> simp [hk]
  · rw [Finset.sum_neg_distrib]
    linarith
  · intro i
    simpa only [mul_neg, Finset.sum_neg_distrib, abs_neg] using herr i

/-- The small mass controls the discrepancy potential at every dyadic scale. -/
theorem dyadic_potential_bound {s μ R : ℝ} (hμ : 0 < μ) (hμR : 2 * μ ≤ R)
    (hs : 0 ≤ s) (j : ℕ) (hsmass : s ≤ 2 ^ j * μ) :
    Real.sqrt (s * Real.log (2 * R / s)) / 2 ^ j ≤
      (3 / 4) ^ j * Real.sqrt (μ * Real.log (2 * R / μ)) := by
  have hR : 0 < R := by linarith
  have hratio : (4 : ℝ) ≤ 2 * R / μ := (le_div_iff₀ hμ).mpr (by linarith)
  let L := Real.log (2 * R / μ)
  have hL : 1 ≤ L := by
    have h2 := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    have h4 := Real.log_le_log (by norm_num : (0 : ℝ) < 4) hratio
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow] at h4
    norm_num at h2 h4
    dsimp [L]
    linarith
  have hφ : 0 ≤ μ * L := mul_nonneg hμ.le (by linarith)
  have hpow : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  have hf : s * Real.log (2 * R / s) ≤ 2 ^ j * (μ * L) := by
    by_cases hz : s = 0
    · rw [hz, zero_mul]
      positivity
    have hs0 : 0 < s := lt_of_le_of_ne hs (Ne.symm hz)
    have hid : 2 * R / s = (2 * R / μ) * (μ / s) := by field_simp
    rw [hid, Real.log_mul (by positivity : 2 * R / μ ≠ 0)
      (by positivity : μ / s ≠ 0), mul_add]
    have hlog := mul_le_mul_of_nonneg_left
      (Real.log_le_sub_one_of_pos (show 0 < μ / s by positivity)) hs
    have heq : s * (μ / s - 1) = μ - s := by field_simp
    rw [heq] at hlog
    have hmult := mul_le_mul_of_nonneg_right hsmass (show 0 ≤ L - 1 by linarith)
    change s * L + s * Real.log (μ / s) ≤ _
    nlinarith [mul_le_mul_of_nonneg_right hpow hμ.le]
  have hscale : (2 : ℝ) ^ j ≤ ((3 / 4) ^ j * 2 ^ j) ^ 2 := by
    calc
      (2 : ℝ) ^ j ≤ (9 / 4) ^ j := pow_le_pow_left₀ (by norm_num) (by norm_num) j
      _ = _ := by rw [← mul_pow, ← pow_mul, mul_comm j 2, pow_mul]; norm_num
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ j)).mpr
  apply (Real.sqrt_le_left (by positivity)).mpr
  have hroot := Real.sq_sqrt hφ
  change s * Real.log (2 * R / s) ≤ ((3 / 4) ^ j * Real.sqrt (μ * L) * 2 ^ j) ^ 2
  calc
    _ ≤ 2 ^ j * (μ * L) := hf
    _ ≤ (((3 / 4) ^ j * 2 ^ j) ^ 2) * (μ * L) := mul_le_mul_of_nonneg_right hscale hφ
    _ = _ := by calc
      _ = ((3 / 4) ^ j * 2 ^ j) ^ 2 * (Real.sqrt (μ * L)) ^ 2 := by rw [hroot]
      _ = _ := by ring

/-- One mass-nonincreasing dyadic rounding step, on the exact odd coordinates. -/
theorem dyadic_round_step {α : Type u} {β : Type v}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (A : β → α → ℝ) (hA : ∀ i k, |A i k| ≤ 1)
    (hαβ : Fintype.card α ≤ Fintype.card β)
    (a : α → ℕ) (j : ℕ) (ha : ∀ k, a k ≤ 2 ^ (j + 1))
    {μ : ℝ} (hμ : 0 < μ) (hμR : 2 * μ ≤ Fintype.card β)
    (hmass : (∑ k, (a k : ℝ) / 2 ^ (j + 1)) ≤ μ) :
    ∃ b : α → ℕ, (∀ k, b k ≤ 2 ^ j) ∧
      (∑ k, (b k : ℝ) / 2 ^ j) ≤ (∑ k, (a k : ℝ) / 2 ^ (j + 1)) ∧
      ∀ i, |∑ k, A i k * ((b k : ℝ) / 2 ^ j - (a k : ℝ) / 2 ^ (j + 1))| ≤
        8192 * ((3 / 4) ^ (j + 1) * Real.sqrt
          (μ * Real.log (2 * Fintype.card β / μ))) := by
  classical
  let U := {k : α // a k % 2 = 1}
  have hUβ : Fintype.card U ≤ Fintype.card β :=
    (Fintype.card_subtype_le _).trans hαβ
  obtain ⟨ξ, hξ, hξsum, hξerr⟩ := matrix_signing_nonpos
    (fun i (k : U) ↦ A i k) (fun i k ↦ hA i k) hUβ
  let b : α → ℕ := fun k ↦ a k / 2 +
    if hk : a k % 2 = 1 then (if ξ ⟨k, hk⟩ = 1 then 1 else 0) else 0
  let ζ : α → ℝ := fun k ↦ if hk : a k % 2 = 1 then ξ ⟨k, hk⟩ else 0
  have hb (k : α) : b k ≤ 2 ^ j := by
    have hak := ha k
    rw [pow_succ] at hak
    dsimp [b]
    by_cases hk : a k % 2 = 1
    · rw [dif_pos hk]
      split_ifs <;> omega
    · rw [dif_neg hk]
      omega
  have hnumer (k : α) : 2 * (b k : ℝ) - a k = ζ k := by
    by_cases hk : a k % 2 = 1
    · dsimp [b, ζ]
      rw [dif_pos hk, dif_pos hk]
      rcases hξ ⟨k, hk⟩ with hm | hp
      · rw [hm]
        norm_num
        have hn : 2 * (a k / 2) + 1 = a k := by omega
        have hn' : 2 * ((a k / 2 : ℕ) : ℝ) + 1 = a k := by exact_mod_cast hn
        linarith
      · rw [hp]
        norm_num

        have hn : 2 * (a k / 2) + 1 = a k := by omega
        have hn' : 2 * ((a k / 2 : ℕ) : ℝ) + 1 = a k := by exact_mod_cast hn
        linarith
    · dsimp [b, ζ]
      rw [dif_neg hk, dif_neg hk]
      norm_num
      have hn : 2 * (a k / 2) = a k := by omega
      have hn' : 2 * ((a k / 2 : ℕ) : ℝ) = a k := by exact_mod_cast hn
      linarith
  have hdiff (k : α) : (b k : ℝ) / 2 ^ j - (a k : ℝ) / 2 ^ (j + 1) =
      ζ k / 2 ^ (j + 1) := by
    rw [pow_succ]
    have hp : (2 : ℝ) ^ j ≠ 0 := by positivity
    field_simp
    nlinarith [hnumer k]
  have hζsum (f : α → ℝ) : (∑ k, f k * ζ k) = ∑ k : U, f k * ξ k := by
    rw [← Fintype.sum_subtype_add_sum_subtype (fun k ↦ a k % 2 = 1)]
    have hzero : (∑ k : {k : α // ¬ a k % 2 = 1}, f k * ζ k) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      simp [ζ, k.property]
    rw [hzero, add_zero]
    apply Finset.sum_congr rfl
    intro k hk
    simp [ζ, k.property]
  have hmass' : (∑ k, (b k : ℝ) / 2 ^ j) ≤ ∑ k, (a k : ℝ) / 2 ^ (j + 1) := by
    have hsumdiff : (∑ k, (b k : ℝ) / 2 ^ j) - (∑ k, (a k : ℝ) / 2 ^ (j + 1)) =
        (∑ k : U, ξ k) / 2 ^ (j + 1) := by
      rw [← Finset.sum_sub_distrib]
      simp_rw [hdiff]
      rw [← Finset.sum_div]
      congr 1
      simpa using hζsum (fun _ ↦ 1)
    have hh : (∑ k : U, ξ k) / 2 ^ (j + 1) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hξsum (by positivity)
    linarith
  have hsmass : (Fintype.card U : ℝ) ≤ 2 ^ (j + 1) * μ := by
    have hsumU : (Fintype.card U : ℝ) ≤ ∑ k : U, (a k : ℝ) := by
      calc
        _ = ∑ _k : U, (1 : ℝ) := by simp
        _ ≤ _ := Finset.sum_le_sum fun k _ ↦ by
          have hk : 1 ≤ a k := by have := k.property; omega
          exact_mod_cast hk
    have hsumall : (∑ k : U, (a k : ℝ)) ≤ ∑ k : α, (a k : ℝ) := by
      have hh := Fintype.sum_subtype_add_sum_subtype (fun k ↦ a k % 2 = 1) (fun k ↦ (a k : ℝ))
      have hp : 0 ≤ ∑ k : {k : α // ¬ a k % 2 = 1}, (a k : ℝ) := by positivity
      change (∑ k : U, (a k : ℝ)) + _ = _ at hh
      linarith
    rw [← Finset.sum_div] at hmass
    have hm := (div_le_iff₀ (show (0 : ℝ) < 2 ^ (j + 1) by positivity)).mp hmass
    linarith
  refine ⟨b, hb, hmass', fun i ↦ ?_⟩
  have hsum : (∑ k, A i k * ((b k : ℝ) / 2 ^ j - (a k : ℝ) / 2 ^ (j + 1))) =
      (∑ k : U, A i k * ξ k) / 2 ^ (j + 1) := by
    simp_rw [hdiff, ← mul_div_assoc]
    rw [← Finset.sum_div, hζsum]
  rw [hsum, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ (j + 1))]
  calc
    _ ≤ (8192 * Real.sqrt ((Fintype.card U : ℝ) *
        Real.log (2 * Fintype.card β / Fintype.card U))) / 2 ^ (j + 1) :=
      div_le_div_of_nonneg_right (hξerr i) (by positivity)
    _ = 8192 * (Real.sqrt ((Fintype.card U : ℝ) *
        Real.log (2 * Fintype.card β / Fintype.card U)) / 2 ^ (j + 1)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (dyadic_potential_bound hμ hμR (Nat.cast_nonneg _) (j + 1) hsmass) (by norm_num)

/-- Iteration of the dyadic steps. The mass bound is maintained, not reset at each scale. -/
theorem dyadic_round {α : Type u} {β : Type v}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (A : β → α → ℝ) (hA : ∀ i k, |A i k| ≤ 1)
    (hαβ : Fintype.card α ≤ Fintype.card β)
    {μ : ℝ} (hμ : 0 < μ) (hμR : 2 * μ ≤ Fintype.card β) (j : ℕ) :
    ∀ a : α → ℕ, (∀ k, a k ≤ 2 ^ j) →
      (∑ k, (a k : ℝ) / 2 ^ j) ≤ μ →
      ∃ b : α → ℕ, (∀ k, b k ≤ 1) ∧
        (∑ k, (b k : ℝ)) ≤ (∑ k, (a k : ℝ) / 2 ^ j) ∧
        ∀ i, |∑ k, A i k * ((b k : ℝ) - (a k : ℝ) / 2 ^ j)| ≤
          8192 * (3 * (1 - (3 / 4) ^ j) * Real.sqrt
            (μ * Real.log (2 * Fintype.card β / μ))) := by
  induction j with
  | zero =>
    intro a ha hmass
    refine ⟨a, by simpa using ha, by simp, ?_⟩
    intro i
    simp
  | succ j ih =>
    intro a ha hmass
    obtain ⟨b, hb, hmassb, herrb⟩ := dyadic_round_step A hA hαβ a j ha hμ hμR hmass
    obtain ⟨c, hc, hmassc, herrc⟩ := ih b hb (hmassb.trans hmass)
    refine ⟨c, hc, hmassc.trans hmassb, fun i ↦ ?_⟩
    have hsplit : (∑ k, A i k * ((c k : ℝ) - (a k : ℝ) / 2 ^ (j + 1))) =
        (∑ k, A i k * ((c k : ℝ) - (b k : ℝ) / 2 ^ j)) +
        ∑ k, A i k * ((b k : ℝ) / 2 ^ j - (a k : ℝ) / 2 ^ (j + 1)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    rw [hsplit]
    calc
      _ ≤ |∑ k, A i k * ((c k : ℝ) - (b k : ℝ) / 2 ^ j)| +
          |∑ k, A i k * ((b k : ℝ) / 2 ^ j - (a k : ℝ) / 2 ^ (j + 1))| := abs_add_le _ _
      _ ≤ 8192 * (3 * (1 - (3 / 4) ^ j) * Real.sqrt
            (μ * Real.log (2 * Fintype.card β / μ))) +
          8192 * ((3 / 4) ^ (j + 1) * Real.sqrt
            (μ * Real.log (2 * Fintype.card β / μ))) := add_le_add (herrc i) (herrb i)
      _ = _ := by rw [pow_succ]; ring

/-- Defect-sensitive rounding on a real matrix, prior to the circle discretization. -/
theorem matrix_defect_rounding {α : Type u} {β : Type v}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (A : β → α → ℝ) (hA : ∀ i k, |A i k| ≤ 1)
    (hαβ : Fintype.card α ≤ Fintype.card β)
    (p : α → ℝ) (hp : ∀ k, 0 ≤ p k ∧ p k ≤ 1)
    {μ : ℝ} (hμ : 0 < μ) (hμR : 2 * μ ≤ Fintype.card β)
    (hmass : (∑ k, p k) ≤ μ) :
    ∃ p' : α → ℝ, (∀ k, p' k = 0 ∨ p' k = 1) ∧ (∑ k, p' k) ≤ ∑ k, p k ∧
      ∀ i, |∑ k, A i k * (p' k - p k)| ≤
        1 + 24576 * Real.sqrt (μ * Real.log (2 * Fintype.card β / μ)) := by
  classical
  let j := Fintype.card α
  have hjNat : j ≤ 2 ^ j := by
    have hh : ∀ n : ℕ, n ≤ 2 ^ n := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        have hp : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by norm_num)
        rw [pow_succ]
        omega
    exact hh j
  have hj : (Fintype.card α : ℝ) / 2 ^ j ≤ 1 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ j)).mpr
    simp only [one_mul]
    exact_mod_cast hjNat
  let a : α → ℕ := fun k ↦ ⌊2 ^ j * p k⌋₊
  have ha_le (k : α) : (a k : ℝ) ≤ 2 ^ j * p k := Nat.floor_le (mul_nonneg (by positivity) (hp k).1)
  have ha_lt (k : α) : 2 ^ j * p k < (a k : ℝ) + 1 := Nat.lt_floor_add_one _
  have habound (k : α) : a k ≤ 2 ^ j := by
    have hh : (a k : ℝ) ≤ (2 : ℝ) ^ j := (ha_le k).trans
      (by nlinarith [hp k, show (0 : ℝ) ≤ 2 ^ j by positivity])
    exact_mod_cast hh
  have ha_frac (k : α) : (a k : ℝ) / 2 ^ j ≤ p k :=
    (div_le_iff₀ (by positivity)).mpr (by simpa [mul_comm] using ha_le k)
  have ha_err (k : α) : |(a k : ℝ) / 2 ^ j - p k| ≤ 1 / 2 ^ j := by
    rw [abs_of_nonpos (sub_nonpos.mpr (ha_frac k))]
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ j)).mpr
    have heq : -((a k : ℝ) / 2 ^ j - p k) * 2 ^ j = 2 ^ j * p k - a k := by
      field_simp ; ring
    rw [heq]
    linarith [ha_lt k]
  have hmass_a : (∑ k, (a k : ℝ) / 2 ^ j) ≤ ∑ k, p k :=
    Finset.sum_le_sum fun k _ ↦ ha_frac k
  have hinit (i : β) : |∑ k, A i k * ((a k : ℝ) / 2 ^ j - p k)| ≤ 1 := by
    calc
      _ ≤ ∑ k, |A i k * ((a k : ℝ) / 2 ^ j - p k)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k : α, (1 : ℝ) / 2 ^ j := Finset.sum_le_sum fun k _ ↦ by
        rw [abs_mul]
        exact (mul_le_mul (hA i k) (ha_err k) (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
      _ = (Fintype.card α : ℝ) / 2 ^ j := by simp [div_eq_mul_inv]
      _ ≤ 1 := hj
  obtain ⟨b, hb, hmassb, herrb⟩ := dyadic_round A hA hαβ hμ hμR j a habound
    (hmass_a.trans hmass)
  refine ⟨fun k ↦ (b k : ℝ), ?_, hmassb.trans hmass_a, fun i ↦ ?_⟩
  · intro k
    have hh : b k = 0 ∨ b k = 1 := by have := hb k; omega
    rcases hh with hh | hh <;> simp [hh]
  · have hsplit : (∑ k, A i k * ((b k : ℝ) - p k)) =
        (∑ k, A i k * ((b k : ℝ) - (a k : ℝ) / 2 ^ j)) +
        ∑ k, A i k * ((a k : ℝ) / 2 ^ j - p k) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    rw [hsplit]
    have hroot := Real.sqrt_nonneg (μ * Real.log (2 * Fintype.card β / μ))
    calc
      _ ≤ |∑ k, A i k * ((b k : ℝ) - (a k : ℝ) / 2 ^ j)| +
          |∑ k, A i k * ((a k : ℝ) / 2 ^ j - p k)| := abs_add_le _ _
      _ ≤ 8192 * (3 * (1 - (3 / 4) ^ j) * Real.sqrt
            (μ * Real.log (2 * Fintype.card β / μ))) + 1 := add_le_add (herrb i) (hinit i)
      _ ≤ _ := by nlinarith [mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4) j) hroot]

open scoped ComplexConjugate
open Finset

/-- Orthogonality of the exact full root-of-unity grid. -/
theorem grid_power_orthogonality {M a b : ℕ} [NeZero M] (ha : a < M) (hb : b < M) :
    (∑ j : ZMod M, ZMod.stdAddChar j ^ a * conj (ZMod.stdAddChar j ^ b)) =
      if a = b then (M : ℂ) else 0 := by
  have hpow (n : ℕ) (j : ZMod M) : ZMod.stdAddChar j ^ n =
      ZMod.stdAddChar ((n : ZMod M) * j) := by
    rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul]
  have hconj (j : ZMod M) : conj (ZMod.stdAddChar j) = ZMod.stdAddChar (-j) := by
    rw [AddChar.map_neg_eq_inv, ZMod.stdAddChar_apply]
    exact (Circle.coe_inv_eq_conj (ZMod.toCircle j)).symm
  simp_rw [hpow, hconj, ← AddChar.map_add_eq_mul, ← sub_eq_add_neg, ← sub_mul]
  have hzero : ((a : ZMod M) - b = 0) ↔ a = b := by
    rw [sub_eq_zero, ZMod.natCast_eq_natCast_iff]
    simp only [Nat.ModEq, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  by_cases hab : a = b
  · subst b
    simp
  · rw [if_neg hab]
    exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar M (mt hzero.mp hab))

/-- Mean square of a translated Dirichlet kernel on an oversampling grid. -/
theorem grid_dirichlet_square {M n : ℕ} [NeZero M] (hn : n ≤ M)
    {z : ℂ} (hz : ‖z‖ = 1) :
    (∑ j : ZMod M, ‖∑ a : Fin n, z ^ (a : ℕ) * conj (ZMod.stdAddChar j ^ (a : ℕ))‖ ^ 2) =
      (M : ℝ) * n := by
  have hcomplex : (∑ j : ZMod M,
      (∑ a : Fin n, z ^ (a : ℕ) * conj (ZMod.stdAddChar j ^ (a : ℕ))) *
      conj (∑ a : Fin n, z ^ (a : ℕ) * conj (ZMod.stdAddChar j ^ (a : ℕ)))) =
      (M : ℂ) * n := by
    simp only [map_sum, map_mul, Complex.conj_conj, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Eq.trans ?_ (show (∑ a : Fin n, (M : ℂ)) = (M : ℂ) * n by simp [mul_comm])
    apply Finset.sum_congr rfl
    intro a ha
    rw [Finset.sum_comm]
    calc
      (∑ b : Fin n, ∑ j : ZMod M,
          z ^ (b : ℕ) * conj (ZMod.stdAddChar j ^ (b : ℕ)) *
            (conj (z ^ (a : ℕ)) * ZMod.stdAddChar j ^ (a : ℕ))) =
        ∑ b : Fin n, (z ^ (b : ℕ) * conj (z ^ (a : ℕ))) *
          (∑ j : ZMod M, ZMod.stdAddChar j ^ (a : ℕ) *
            conj (ZMod.stdAddChar j ^ (b : ℕ))) := by
          apply Finset.sum_congr rfl
          intro b hb
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          ring
      _ = ∑ b : Fin n, if b = a then (z ^ (a : ℕ) * conj (z ^ (a : ℕ))) * M else 0 := by
        apply Finset.sum_congr rfl
        intro b hb
        rw [grid_power_orthogonality (a.isLt.trans_le hn) (b.isLt.trans_le hn)]
        by_cases heq : b = a
        · subst b
          simp
        · have hval : (b : ℕ) ≠ (a : ℕ) := fun h ↦ heq (Fin.ext h)
          simp [heq, Ne.symm hval]
      _ = (M : ℂ) := by
        simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_pow, hz]
        simp
  have hreal := congrArg Complex.re hcomplex
  simpa only [Complex.mul_conj, Complex.normSq_eq_norm_sq, ← Complex.ofReal_pow,
    ← Complex.ofReal_sum, Complex.ofReal_re, Complex.mul_re,
    Complex.natCast_re, Complex.natCast_im, mul_zero, sub_zero] using hreal

/-- A rotated, finite Dirichlet kernel on the root grid. -/
def gridDirichlet {M : ℕ} [NeZero M] (n : ℕ) (z : ℂ) (j : ZMod M) : ℂ :=
  ∑ a : Fin n, z ^ (a : ℕ) * conj (ZMod.stdAddChar j ^ (a : ℕ))

/-- The cross-Dirichlet kernel reproduces each required nonnegative frequency. -/
theorem grid_reproduce_monomial {M N : ℕ} [NeZero M] (hNM : 2 * N ≤ M)
    (k : Fin N) {z : ℂ} (hz : ‖z‖ = 1) :
    (∑ j : ZMod M, ZMod.stdAddChar j ^ (k : ℕ) * gridDirichlet (2 * N) z j *
      conj (gridDirichlet N z j)) = (M : ℂ) * N * z ^ (k : ℕ) := by
  have hb (b : Fin N) : (∑ j : ZMod M,
      ZMod.stdAddChar j ^ (k : ℕ) * gridDirichlet (2 * N) z j *
        (conj (z ^ (b : ℕ)) * ZMod.stdAddChar j ^ (b : ℕ))) =
      (M : ℂ) * z ^ (k : ℕ) := by
    have hkb : (k : ℕ) + b < 2 * N := by omega
    let a₀ : Fin (2 * N) := ⟨(k : ℕ) + b, hkb⟩
    simp only [gridDirichlet, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    calc
      (∑ a : Fin (2 * N), ∑ j : ZMod M,
          ZMod.stdAddChar j ^ (k : ℕ) *
            (z ^ (a : ℕ) * conj (ZMod.stdAddChar j ^ (a : ℕ))) *
              (conj (z ^ (b : ℕ)) * ZMod.stdAddChar j ^ (b : ℕ))) =
        ∑ a : Fin (2 * N), (z ^ (a : ℕ) * conj (z ^ (b : ℕ))) *
          (∑ j : ZMod M, ZMod.stdAddChar j ^ ((k : ℕ) + b) *
            conj (ZMod.stdAddChar j ^ (a : ℕ))) := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        rw [pow_add]
        ring
      _ = ∑ a : Fin (2 * N), if a = a₀ then
          (z ^ ((k : ℕ) + b) * conj (z ^ (b : ℕ))) * M else 0 := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [grid_power_orthogonality (hkb.trans_le hNM) (a.isLt.trans_le hNM)]
        by_cases heq : a = a₀
        · subst a
          simp [a₀]
        · have hval : (k : ℕ) + b ≠ (a : ℕ) := fun h ↦ heq (Fin.ext h.symm)
          simp [heq, hval]
      _ = (M : ℂ) * z ^ (k : ℕ) := by
        simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
        rw [pow_add, mul_assoc (z ^ (k : ℕ)) (z ^ (b : ℕ)) (conj (z ^ (b : ℕ))),
          Complex.mul_conj, Complex.normSq_eq_norm_sq,
          norm_pow, hz]
        simp [mul_comm]
  calc
    _ = ∑ j : ZMod M, ∑ b : Fin N,
        ZMod.stdAddChar j ^ (k : ℕ) * gridDirichlet (2 * N) z j *
          (conj (z ^ (b : ℕ)) * ZMod.stdAddChar j ^ (b : ℕ)) := by
      apply Finset.sum_congr rfl
      intro j hj
      simp only [gridDirichlet, map_sum, map_mul, Complex.conj_conj, Finset.mul_sum]
    _ = ∑ b : Fin N, ∑ j : ZMod M,
        ZMod.stdAddChar j ^ (k : ℕ) * gridDirichlet (2 * N) z j *
          (conj (z ^ (b : ℕ)) * ZMod.stdAddChar j ^ (b : ℕ)) := Finset.sum_comm
    _ = ∑ _b : Fin N, (M : ℂ) * z ^ (k : ℕ) := Finset.sum_congr rfl (fun b _ ↦ hb b)
    _ = _ := by simp; ring

/-- No logarithmic loss: an oversampled analytic polynomial is controlled on the whole circle. -/
theorem polynomial_grid_bound {N M : ℕ} [NeZero M] (hN : 0 < N) (hNM : 2 * N ≤ M)
    (c : Fin N → ℂ) {G : ℝ} (hG : 0 ≤ G)
    (hgrid : ∀ j : ZMod M, ‖∑ k : Fin N, c k * ZMod.stdAddChar j ^ (k : ℕ)‖ ≤ G)
    {z : ℂ} (hz : ‖z‖ = 1) :
    ‖∑ k : Fin N, c k * z ^ (k : ℕ)‖ ≤ 2 * G := by
  have hid : (M : ℂ) * N * (∑ k : Fin N, c k * z ^ (k : ℕ)) =
      ∑ j : ZMod M, (∑ k : Fin N, c k * ZMod.stdAddChar j ^ (k : ℕ)) *
        gridDirichlet (2 * N) z j * conj (gridDirichlet N z j) := by
    rw [Finset.mul_sum]
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k hk
    calc
      _ = c k * ((M : ℂ) * N * z ^ (k : ℕ)) := by ring
      _ = c k * (∑ j : ZMod M, ZMod.stdAddChar j ^ (k : ℕ) *
          gridDirichlet (2 * N) z j * conj (gridDirichlet N z j)) := by
        rw [grid_reproduce_monomial hNM k hz]
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
  have h2N := grid_dirichlet_square (n := 2 * N) hNM hz
  have hN' := grid_dirichlet_square (n := N) (by omega : N ≤ M) hz
  change (∑ j : ZMod M, ‖gridDirichlet (2 * N) z j‖ ^ 2) = _ at h2N
  change (∑ j : ZMod M, ‖gridDirichlet N z j‖ ^ 2) = _ at hN'
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (ZMod M))
    (fun j ↦ ‖gridDirichlet (2 * N) z j‖) (fun j ↦ ‖gridDirichlet N z j‖)
  rw [h2N, hN'] at hcs
  have hMpos : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hkernel : (∑ j : ZMod M, ‖gridDirichlet (2 * N) z j‖ *
      ‖gridDirichlet N z j‖) ≤ 2 * M * N := by
    push_cast at hcs
    nlinarith [mul_pos hMpos hNpos]
  have hnorm : (M : ℝ) * N * ‖∑ k : Fin N, c k * z ^ (k : ℕ)‖ =
      ‖∑ j : ZMod M, (∑ k : Fin N, c k * ZMod.stdAddChar j ^ (k : ℕ)) *
        gridDirichlet (2 * N) z j * conj (gridDirichlet N z j)‖ := by
    rw [← hid, norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_natCast]
  have hbound : (M : ℝ) * N * ‖∑ k : Fin N, c k * z ^ (k : ℕ)‖ ≤
      G * (2 * M * N) := by
    rw [hnorm]
    calc
      _ ≤ ∑ j : ZMod M, ‖(∑ k : Fin N, c k * ZMod.stdAddChar j ^ (k : ℕ)) *
          gridDirichlet (2 * N) z j * conj (gridDirichlet N z j)‖ := norm_sum_le _ _
      _ ≤ ∑ j : ZMod M, G * (‖gridDirichlet (2 * N) z j‖ *
          ‖gridDirichlet N z j‖) := Finset.sum_le_sum fun j _ ↦ by
        rw [norm_mul, norm_mul, RCLike.norm_conj]
        nlinarith [mul_le_mul_of_nonneg_right (hgrid j)
          (mul_nonneg (norm_nonneg (gridDirichlet (2 * N) z j)) (norm_nonneg (gridDirichlet N z j)))]
      _ = G * (∑ j : ZMod M, ‖gridDirichlet (2 * N) z j‖ *
          ‖gridDirichlet N z j‖) := (Finset.mul_sum ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hkernel hG
  nlinarith [mul_pos hMpos hNpos]

def defectMass {N : ℕ} (X : Fin N → ℝ) : ℝ :=
  (∑ k : Fin N, (1 - |X k|)) / 2

theorem defect_rounding {N : ℕ} (hN : 1 ≤ N) (X : Fin N → ℝ)
    (hX : ∀ k, |X k| ≤ 1) :
    ∃ ε : Fin N → ℝ, IsRealSigning ε ∧
      ∀ z : ℂ, ‖z‖ = 1 →
        ‖littlewoodValue ε z - littlewoodValue X z‖ ≤
          196608 * (1 + Real.sqrt (defectMass X * Real.log (80 * N / defectMass X))) := by
  classical
  let μ := defectMass X
  have hμ0 : 0 ≤ μ := by
    dsimp [μ, defectMass]
    exact div_nonneg (Finset.sum_nonneg fun k _ ↦ sub_nonneg.mpr (hX k)) (by norm_num)
  have hμN : 2 * μ ≤ N := by
    have hh : (∑ k : Fin N, (1 - |X k|)) ≤ ∑ _k : Fin N, (1 : ℝ) :=
      Finset.sum_le_sum fun k _ ↦ by linarith [abs_nonneg (X k)]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hh
    dsimp [μ, defectMass]
    linarith
  by_cases hμzero : μ = 0
  · have hsumzero : (∑ k : Fin N, (1 - |X k|)) = 0 := by dsimp [μ, defectMass] at hμzero; linarith
    have hxone (k : Fin N) : |X k| = 1 := by
      have hk := (Finset.sum_eq_zero_iff_of_nonneg
        (fun k (_ : k ∈ (Finset.univ : Finset (Fin N))) ↦ sub_nonneg.mpr (hX k))).mp hsumzero k (Finset.mem_univ k)
      linarith
    refine ⟨X, ?_, ?_⟩
    · intro k
      by_cases hk : 0 ≤ X k
      · exact Or.inr (by simpa only [abs_of_nonneg hk] using hxone k)
      · exact Or.inl (by have := hxone k; rw [abs_of_neg (lt_of_not_ge hk)] at this; linarith)
    · intro z hz
      rw [sub_self, norm_zero]
      positivity
  have hμ : 0 < μ := lt_of_le_of_ne hμ0 (Ne.symm hμzero)
  let σ : Fin N → ℝ := fun k ↦ if 0 ≤ X k then 1 else -1
  let p : Fin N → ℝ := fun k ↦ (1 - |X k|) / 2
  have hσ (k : Fin N) : σ k = -1 ∨ σ k = 1 := by dsimp [σ]; split_ifs <;> simp
  have hσabs (k : Fin N) : |σ k| = 1 := by rcases hσ k with hk | hk <;> simp [hk]
  have hp (k : Fin N) : 0 ≤ p k ∧ p k ≤ 1 := by
    dsimp [p]
    constructor <;> linarith [hX k, abs_nonneg (X k)]
  have hXp (k : Fin N) : σ k * (1 - 2 * p k) = X k := by
    dsimp [σ, p]
    split_ifs with hk
    · rw [abs_of_nonneg hk]
      ring
    · rw [abs_of_neg (lt_of_not_ge hk)]
      ring
  have hmass : (∑ k, p k) = μ := by dsimp [p, μ, defectMass]; rw [Finset.sum_div]
  let M := 20 * N
  have hM : M ≠ 0 := by dsimp [M]; omega
  let : NeZero M := ⟨hM⟩
  let A : (ZMod M × Bool) → Fin N → ℝ := fun i k ↦
    σ k * (if i.2 then (ZMod.stdAddChar i.1 ^ (k : ℕ)).im else (ZMod.stdAddChar i.1 ^ (k : ℕ)).re)
  have hrootnorm (j : ZMod M) : ‖ZMod.stdAddChar j‖ = 1 := Circle.norm_coe (ZMod.toCircle j)
  have hA (i : ZMod M × Bool) (k : Fin N) : |A i k| ≤ 1 := by
    dsimp [A]
    rw [abs_mul, hσabs, one_mul]
    split_ifs
    · calc
        _ ≤ ‖ZMod.stdAddChar i.1 ^ (k : ℕ)‖ := Complex.abs_im_le_norm _
        _ = 1 := by rw [norm_pow, hrootnorm]; simp
    · calc
        _ ≤ ‖ZMod.stdAddChar i.1 ^ (k : ℕ)‖ := Complex.abs_re_le_norm _
        _ = 1 := by rw [norm_pow, hrootnorm]; simp
  have hcard : Fintype.card (ZMod M × Bool) = 40 * N := by
    simp [Fintype.card_prod, ZMod.card, M]
    omega
  have hNR : Fintype.card (Fin N) ≤ Fintype.card (ZMod M × Bool) := by rw [hcard, Fintype.card_fin]; omega
  have hμR : 2 * μ ≤ Fintype.card (ZMod M × Bool) := by
    rw [hcard]
    push_cast
    nlinarith [show (0 : ℝ) ≤ N from Nat.cast_nonneg N]
  obtain ⟨p', hp', hmass', herr⟩ := matrix_defect_rounding A hA hNR p hp hμ hμR hmass.le
  let ε : Fin N → ℝ := fun k ↦ σ k * (1 - 2 * p' k)
  have hε : IsRealSigning ε := by
    intro k
    rcases hp' k with hp'k | hp'k <;> rcases hσ k with hσk | hσk <;> norm_num [IsRealSigning, ε, hp'k, hσk]
  let D := 1 + 24576 * Real.sqrt (μ * Real.log (80 * N / μ))
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have herr' (i : ZMod M × Bool) : |∑ k, A i k * (p' k - p k)| ≤ D := by
    have hh := herr i
    rw [hcard] at hh
    push_cast at hh
    convert hh using 1; dsimp [D]; congr 3; ring_nf
  let E : ZMod M → ℂ := fun j ↦ ∑ k, ((σ k * (p' k - p k) : ℝ) : ℂ) * ZMod.stdAddChar j ^ (k : ℕ)
  have hEre (j : ZMod M) : (E j).re = ∑ k, A (j, false) k * (p' k - p k) := by
    dsimp [E, A]
    simp only [Complex.re_sum, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  have hEim (j : ZMod M) : (E j).im = ∑ k, A (j, true) k * (p' k - p k) := by
    dsimp [E, A]
    simp only [Complex.im_sum, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  have hEnorm (j : ZMod M) : ‖E j‖ ≤ 2 * D := by
    calc
      _ ≤ |(E j).re| + |(E j).im| := Complex.norm_le_abs_re_add_abs_im _
      _ ≤ D + D := by rw [hEre, hEim]; exact add_le_add (herr' (j, false)) (herr' (j, true))
      _ = _ := by ring
  have hcoef (k : Fin N) : ε k - X k = -2 * (σ k * (p' k - p k)) := by
    have hh := hXp k
    dsimp [ε]
    nlinarith
  have hgrid (j : ZMod M) : ‖∑ k : Fin N, ((ε k - X k : ℝ) : ℂ) *
      ZMod.stdAddChar j ^ (k : ℕ)‖ ≤ 4 * D := by
    have heq : (∑ k : Fin N, ((ε k - X k : ℝ) : ℂ) * ZMod.stdAddChar j ^ (k : ℕ)) =
        (-2 : ℂ) * E j := by
      dsimp [E]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [hcoef]
      push_cast
      ring
    rw [heq, norm_mul]
    norm_num
    nlinarith [hEnorm j]
  refine ⟨ε, hε, fun z hz ↦ ?_⟩
  have hpoly := polynomial_grid_bound (M := M) (by omega : 0 < N)
    (by dsimp [M]; omega : 2 * N ≤ M) (fun k ↦ ((ε k - X k : ℝ) : ℂ))
    (show 0 ≤ 4 * D by positivity) hgrid hz
  have heq : littlewoodValue ε z - littlewoodValue X z =
      ∑ k : Fin N, ((ε k - X k : ℝ) : ℂ) * z ^ (k : ℕ) := by
    dsimp [littlewoodValue]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    push_cast
    ring
  rw [heq]
  apply hpoly.trans
  dsimp [D, μ]
  nlinarith [Real.sqrt_nonneg (defectMass X * Real.log (80 * N / defectMass X))]

end

end AsymptoticallyMinimalLittlewood

end OAI



namespace OAI

universe uE uX

namespace AsymptoticallyMinimalLittlewood
namespace Auxiliary
noncomputable section
open MeasureTheory Filter Topology Complex
open scoped BigOperators ComplexConjugate ENNReal
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

lemma integral_circle_fourier (n : ℤ) :
    (∫ x : UnitAddCircle, fourier n x) = if n=0 then 1 else 0 := by
  have hh := congrFun (fourierCoeff_fourier (T := (1:ℝ)) n) 0
  simpa [fourierCoeff, Pi.single_apply, eq_comm] using! hh

def cosine (x : UnitAddCircle) : ℝ := (fourier 1 x).re

lemma cosine_continuous : Continuous cosine := Complex.continuous_re.comp (fourier 1).continuous

lemma cosine_abs_le (x : UnitAddCircle) : |cosine x| ≤ 1 := by
  simpa only [cosine, fourier_apply, Circle.norm_coe] using Complex.abs_re_le_norm (fourier 1 x)

lemma cosine_cast (x : UnitAddCircle) :
    (cosine x : ℂ) = (fourier 1 x + fourier (-1) x)/2 := by
  rw [fourier_neg]
  apply Complex.ext <;> simp [cosine]

lemma integral_cosine : (∫ x : UnitAddCircle, cosine x) = 0 := by
  have hi : Integrable (fun x : UnitAddCircle ↦ fourier 1 x) := (fourier 1).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  change (∫ x : UnitAddCircle, (fourier 1 x).re) = 0
  have hr : (∫ x : UnitAddCircle, (fourier 1 x).re) = (∫ x : UnitAddCircle, fourier 1 x).re := by
    simpa using! integral_re hi
  rw [hr, integral_circle_fourier]
  norm_num

lemma integral_cosine_sq : (∫ x : UnitAddCircle, cosine x ^ 2) = 1/2 := by
  have hp (x : UnitAddCircle) : ((cosine x ^ 2 : ℝ) : ℂ) =
      (fourier 2 x + 2 + fourier (-2) x)/4 := by
    rw [Complex.ofReal_pow, cosine_cast, div_pow, add_sq]
    have h1 : fourier (1:ℤ) x * fourier 1 x = fourier 2 x := by
      rw [← fourier_add]; norm_num
    have h2 : fourier (-1:ℤ) x * fourier (-1) x = fourier (-2) x := by
      rw [← fourier_add]; norm_num
    have h3 : fourier (1:ℤ) x * fourier (-1) x = 1 := by rw [← fourier_add]; norm_num
    rw [pow_two, pow_two, h1, h2]
    calc
      _ = (fourier 2 x + 2*(fourier 1 x*fourier (-1) x) + fourier (-2) x)/4 := by ring
      _ = _ := by rw [h3]; ring
  have hh : ((∫ x : UnitAddCircle, cosine x ^ 2 : ℝ) : ℂ) = (1/2:ℂ) := by
    have hr : (∫ x : UnitAddCircle, ((cosine x ^ 2 : ℝ) : ℂ)) =
        ((∫ x : UnitAddCircle, cosine x^2 : ℝ) : ℂ) := by
      simpa using! (integral_ofReal (𝕜 := ℂ) (μ := (volume : Measure UnitAddCircle)) (f := fun x : UnitAddCircle ↦ cosine x^(2:ℕ)))
    rw [← hr]
    simp_rw [hp]
    rw [integral_div, integral_add, integral_add, integral_circle_fourier,
      integral_circle_fourier, integral_const]
    · norm_num
    all_goals apply Continuous.integrable_of_hasCompactSupport (by fun_prop) (HasCompactSupport.of_compactSpace _)
  have hr := congrArg Complex.re hh
  simpa using hr

lemma integral_pi_cons {n : ℕ} {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : (Fin (n+1) → UnitAddCircle) → E) (hf : Integrable f) :
    (∫ x, f x) = ∫ u : UnitAddCircle, ∫ y : Fin n → UnitAddCircle, f (Fin.cons u y) := by
  have he := (volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) ↦ UnitAddCircle) 0).symm
  have hi := he.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _) |>.mpr hf
  rw [← he.integral_comp' f]
  change (∫ z, f ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) ↦ UnitAddCircle) 0).symm z) ∂(volume.prod volume)) = _
  have hp := integral_prod _ hi
  dsimp only [Function.comp_def] at hp
  rw [hp]
  congr 1
  ext u
  congr 1
  ext y
  congr 1
  ext i
  simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    ]

def binary : (n : ℕ) → (Fin n → UnitAddCircle) → ℝ
  | 0, _ => 0
  | n+1, x => binary n (Fin.tail x) + (1-binary n (Fin.tail x)^2)/2*cosine (x 0)

lemma binary_continuous (n : ℕ) : Continuous (binary n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
      have ht : Continuous (fun x : Fin (n+1) → UnitAddCircle ↦ Fin.tail x) := by fun_prop
      exact (ih.comp ht).add (((continuous_const.sub ((ih.comp ht).pow 2)).div_const 2).mul
        (cosine_continuous.comp (continuous_apply 0)))

lemma binary_abs_le (n : ℕ) (x : Fin n → UnitAddCircle) : |binary n x| ≤ 1 := by
  induction n with
  | zero => simp [binary]
  | succ n ih =>
      have hz := ih (Fin.tail x)
      have hc := cosine_abs_le (x 0)
      have hsq : binary n (Fin.tail x)^2 ≤ 1 := (sq_le_one_iff_abs_le_one _).mpr hz
      have hcoeff : 0 ≤ (1-binary n (Fin.tail x)^2)/2 := by linarith
      have hstep : (1-binary n (Fin.tail x)^2)/2 ≤ 1-|binary n (Fin.tail x)| := by
        nlinarith [sq_abs (binary n (Fin.tail x)), sq_nonneg (1-|binary n (Fin.tail x)|)]
      calc
        |binary (n+1) x| ≤ |binary n (Fin.tail x)| + |(1-binary n (Fin.tail x)^2)/2*cosine (x 0)| := abs_add_le _ _
        _ = |binary n (Fin.tail x)| + (1-binary n (Fin.tail x)^2)/2*|cosine (x 0)| := by rw [abs_mul, abs_of_nonneg hcoeff]
        _ ≤ |binary n (Fin.tail x)| + (1-binary n (Fin.tail x)^2)/2 := by nlinarith
        _ ≤ 1 := by linarith

lemma binary_cons (n : ℕ) (u : UnitAddCircle) (y : Fin n → UnitAddCircle) :
    binary (n+1) (Fin.cons u y) = binary n y+(1-binary n y^2)/2*cosine u := by
  simp [binary]

def energy (n : ℕ) : ℝ := ∫ x : Fin n → UnitAddCircle, binary n x^2

lemma energy_bounds (n : ℕ) : 0 ≤ energy n ∧ energy n ≤ 1 := by
  refine ⟨integral_nonneg (fun x ↦ sq_nonneg _), ?_⟩
  calc
    energy n ≤ ∫ _ : Fin n → UnitAddCircle, (1:ℝ) := by
      apply integral_mono (((binary_continuous n).pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) (integrable_const _)
      intro x
      exact (sq_le_one_iff_abs_le_one _).mpr (binary_abs_le n x)
    _ = 1 := by simp

lemma integrable_cont {X : Type uX} {E : Type uE} [TopologicalSpace X] [MeasurableSpace X]
    [CompactSpace X] [OpensMeasurableSpace X] [NormedAddCommGroup E]
    {μ : Measure X} [IsFiniteMeasureOnCompacts μ] {f : X → E} (h : Continuous f) :
    Integrable f μ := h.integrable_of_hasCompactSupport (.of_compactSpace _)

lemma integral_pi_cons_rev {n : ℕ} {E : Type uE} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : (Fin (n+1) → UnitAddCircle) → E) (hf : Continuous f) :
    (∫ x, f x) = ∫ y : Fin n → UnitAddCircle, ∫ u : UnitAddCircle, f (Fin.cons u y) := by
  rw [integral_pi_cons f (integrable_cont hf)]
  apply integral_integral_swap
  apply integrable_cont
  exact hf.comp (by fun_prop)

lemma integral_cosine_linear (a b : ℝ) :
    (∫ u : UnitAddCircle, a+b*cosine u) = a := by
  rw [integral_add (integrable_const _) ((integrable_cont cosine_continuous).const_mul _),
    integral_const_mul, integral_cosine]
  simp

lemma integral_cosine_square (a b : ℝ) :
    (∫ u : UnitAddCircle, (a+b*cosine u)^2) = a^2+b^2/2 := by
  have h (u : UnitAddCircle) : (a+b*cosine u)^2 = a^2+2*a*b*cosine u+b^2*cosine u^2 := by ring
  simp_rw [h]
  rw [integral_add, integral_add, integral_const_mul, integral_const_mul,
    integral_cosine, integral_cosine_sq]
  · simp; ring
  all_goals apply integrable_cont; (have hc := cosine_continuous; fun_prop)

lemma binary_mean_zero (n : ℕ) : (∫ x : Fin n → UnitAddCircle, binary n x) = 0 := by
  induction n with
  | zero => simp [binary]
  | succ n ih =>
    rw [integral_pi_cons_rev _ (binary_continuous _)]
    simp_rw [binary_cons, integral_cosine_linear]
    exact ih

lemma energy_succ (n : ℕ) : energy (n+1) = energy n +
    (1/8)*∫ y : Fin n → UnitAddCircle, (1-binary n y^2)^2 := by
  unfold energy
  rw [integral_pi_cons_rev (fun x : Fin (n+1) → UnitAddCircle ↦ binary (n+1) x^2) (by (have hc := binary_continuous (n+1); fun_prop))]
  simp_rw [binary_cons, integral_cosine_square]
  have h (y : Fin n → UnitAddCircle) : binary n y^2+((1-binary n y^2)/2)^2/2 =
      binary n y^2+(1/8)*(1-binary n y^2)^2 := by ring
  simp_rw [h]
  rw [integral_add (integrable_cont (by (have hc := binary_continuous n; fun_prop))) (integrable_cont (by (have hc := binary_continuous n; fun_prop))), integral_const_mul]

lemma energy_increment (n : ℕ) : energy n+(1-energy n)^2/8 ≤ energy (n+1) := by
  have h0 : (0:ℝ) ≤ ∫ y : Fin n → UnitAddCircle, (energy n-binary n y^2)^2 :=
    integral_nonneg (fun y ↦ sq_nonneg (energy n-binary n y^2))
  have hpoint (y : Fin n → UnitAddCircle) : (energy n-binary n y^2)^2 =
      (1-binary n y^2)^2 + 2*(1-energy n)*binary n y^2 + (energy n^2-1) := by ring
  simp_rw [hpoint] at h0
  rw [integral_add, integral_add, integral_const_mul, integral_const] at h0
  · simp only [probReal_univ, smul_eq_mul, one_mul] at h0
    change 0 ≤ (∫ y : Fin n → UnitAddCircle, (1-binary n y^2)^2) +
      2*(1-energy n)*energy n+(energy n^2-1) at h0
    rw [energy_succ]
    nlinarith
  all_goals apply integrable_cont; (have hc := binary_continuous n; fun_prop)

lemma energy_monotone : Monotone energy := by
  apply monotone_nat_of_le_succ
  intro n
  exact le_trans (by nlinarith [sq_nonneg (1-energy n)]) (energy_increment n)

lemma exists_binary_energy {δ : ℝ} (hδ : 0 < δ) :
    ∃ d : ℕ, 2 ≤ d ∧ 1-δ ≤ energy d := by
  by_contra hc
  have hall : ∀ n : ℕ, energy n < 1-δ := by
    intro n
    have hm : energy (max 2 n) < 1-δ := by
      by_contra h
      exact hc ⟨max 2 n, le_max_left _ _, le_of_not_gt h⟩
    exact lt_of_le_of_lt (energy_monotone (le_max_right _ _)) hm
  have hgrowth : ∀ n : ℕ, (n:ℝ)*(δ^2/8) ≤ energy n := by
    intro n
    induction n with
    | zero => simpa using (energy_bounds 0).1
    | succ n ih =>
      have hi := energy_increment n
      have hb := hall n
      rw [Nat.cast_succ]
      nlinarith [sq_nonneg (1-energy n-δ)]
  obtain ⟨n,hn⟩ := exists_nat_gt (8/δ^2)
  have hpos : 0 < δ^2 := sq_pos_of_pos hδ
  have hnum : 1 < (n:ℝ)*(δ^2/8) := by
    have hh := (div_lt_iff₀ hpos).mp hn
    nlinarith
  linarith [hgrowth n, (energy_bounds n).2]

open UnitAddTorus

def primitive : (n : ℕ) → (Fin n → ℤ) → Prop
  | 0, _ => False
  | n+1, s => s 0 = 1 ∨ s 0 = -1 ∨ (s 0 = 0 ∧ primitive n (Fin.tail s))

def spectrumSpan {n : ℕ} (P : (Fin n → ℤ) → Prop) :
    Submodule ℂ ((Fin n → UnitAddCircle) → ℂ) :=
  Submodule.span ℂ ((fun s ↦ (mFourier s : (Fin n → UnitAddCircle) → ℂ)) '' {s | P s})

lemma spectrumSpan_mono {n : ℕ} {P Q : (Fin n → ℤ) → Prop} (h : ∀ s, P s → Q s) :
    spectrumSpan P ≤ spectrumSpan Q := by
  apply Submodule.span_mono
  rintro _ ⟨s,hs,rfl⟩
  exact ⟨s,h s hs,rfl⟩

lemma character_mem {n : ℕ} {P : (Fin n → ℤ) → Prop} {s : Fin n → ℤ} (h : P s) :
    (mFourier s : (Fin n → UnitAddCircle) → ℂ) ∈ spectrumSpan P :=
  Submodule.subset_span ⟨s,h,rfl⟩

lemma character_cons {n : ℕ} (k : ℤ) (s : Fin n → ℤ) (x : Fin (n+1) → UnitAddCircle) :
    mFourier (Fin.cons k s) x = fourier k (x 0)*mFourier s (Fin.tail x) := by
  simp [mFourier, Fin.prod_univ_succ, Fin.tail]

lemma spectrumSpan_lift {n : ℕ} {P : (Fin n → ℤ) → Prop}
    {Q : (Fin (n+1) → ℤ) → Prop} (k : ℤ)
    (h : ∀ s, P s → Q (Fin.cons k s)) {f : (Fin n → UnitAddCircle) → ℂ}
    (hf : f ∈ spectrumSpan P) :
    (fun x : Fin (n+1) → UnitAddCircle ↦ fourier k (x 0)*f (Fin.tail x)) ∈ spectrumSpan Q := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨s,hs,rfl⟩ := hf
    simpa only [← character_cons] using character_mem (h s hs)
  | zero =>
    simp only [Pi.zero_apply, mul_zero]
    exact (spectrumSpan Q).zero_mem
  | add f g hf hg ihf ihg =>
    convert (spectrumSpan Q).add_mem ihf ihg using 1
    ext x
    simp [mul_add]
  | smul a f hf ih =>
    convert (spectrumSpan Q).smul_mem a ih using 1
    ext x
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

lemma allSpectrum_mul {n : ℕ} {f g : (Fin n → UnitAddCircle) → ℂ}
    (hf : f ∈ spectrumSpan (fun _ ↦ True)) (hg : g ∈ spectrumSpan (fun _ ↦ True)) :
    f*g ∈ spectrumSpan (fun _ ↦ True) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨s,_,rfl⟩ := hf
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨t,_,rfl⟩ := hg
      convert character_mem (P := fun _ ↦ True) (s := s+t) trivial using 1
      ext x
      exact (mFourier_add).symm
    | zero => simp
    | add g h hg hh ihg ihh => simpa [mul_add] using (spectrumSpan (n := n) (fun _ ↦ True)).add_mem ihg ihh
    | smul a g hg ih => simpa [mul_smul_comm] using (spectrumSpan (n := n) (fun _ ↦ True)).smul_mem a ih
  | zero => simp
  | add f h hf hh ihf ihh => simpa [add_mul] using (spectrumSpan (n := n) (fun _ ↦ True)).add_mem ihf ihh
  | smul a f hf ih => simpa [smul_mul_assoc] using (spectrumSpan (n := n) (fun _ ↦ True)).smul_mem a ih

lemma allSpectrum_one (n : ℕ) : (1 : (Fin n → UnitAddCircle) → ℂ) ∈ spectrumSpan (fun _ ↦ True) := by
  simpa only [mFourier_zero, ContinuousMap.coe_one] using
    character_mem (P := fun _ ↦ True) (s := (0 : Fin n → ℤ)) trivial

lemma binary_spectrum (n : ℕ) :
    (fun x : Fin n → UnitAddCircle ↦ (binary n x : ℂ)) ∈ spectrumSpan (primitive n) := by
  induction n with
  | zero =>
    simp only [binary, Complex.ofReal_zero]
    exact (spectrumSpan (primitive 0)).zero_mem
  | succ n ih =>
    have ho := spectrumSpan_lift (Q := primitive (n+1)) 0
      (fun s hs ↦ by simp [primitive, hs]) ih
    have ha := spectrumSpan_mono (Q := fun _ ↦ True) (fun _ _ ↦ trivial) ih
    have hn := (spectrumSpan (n := n) (fun _ ↦ True)).sub_mem (allSpectrum_one n) (allSpectrum_mul ha ha)
    have hp := spectrumSpan_lift (Q := primitive (n+1)) 1 (fun s hs ↦ by simp [primitive]) hn
    have hm := spectrumSpan_lift (Q := primitive (n+1)) (-1) (fun s hs ↦ by simp [primitive]) hn
    convert (spectrumSpan (primitive (n+1))).add_mem ho
      ((spectrumSpan (primitive (n+1))).smul_mem (1/4:ℂ)
        ((spectrumSpan (primitive (n+1))).add_mem hp hm)) using 1
    ext x
    simp only [binary, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_div,
      Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_pow, Complex.ofReal_ofNat,
      Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.one_apply, Pi.smul_apply, fourier_zero,
      one_mul, smul_eq_mul, cosine_cast]
    ring

lemma primitive_ne_zero {n : ℕ} {s : Fin n → ℤ} (h : primitive n s) : s ≠ 0 := by
  induction n with
  | zero => exact h.elim
  | succ n ih =>
    intro hs
    subst hs
    simp only [primitive, Pi.zero_apply, zero_ne_one, false_or] at h
    rcases h with h | ⟨_,h⟩
    · norm_num at h
    · exact ih h rfl

lemma primitive_neg {n : ℕ} {s : Fin n → ℤ} (h : primitive n s) : primitive n (-s) := by
  induction n with
  | zero => exact h.elim
  | succ n ih =>
    rcases h with h | h | ⟨h,hs⟩
    · exact Or.inr (Or.inl (by simp [h]))
    · exact Or.inl (by simp [h])
    · exact Or.inr (Or.inr ⟨by simp [h], by change primitive n (-Fin.tail s); exact ih hs⟩)

lemma primitive_parallel_scalar {n : ℕ} {s t : Fin n → ℤ}
    (hs : primitive n s) (ht : primitive n t) {c : ℝ}
    (he : ∀ i, (s i : ℝ) = c*(t i : ℝ)) : c=1 ∨ c = -1 := by
  have hc : c ≠ 0 := by
    intro hc
    apply primitive_ne_zero hs
    ext i
    exact_mod_cast (by simpa [hc] using he i : (s i : ℝ) = 0)
  induction n with
  | zero => exact hs.elim
  | succ n ih =>
    by_cases ht0 : t 0 = 0
    · have hs0 : s 0 = 0 := by exact_mod_cast (by simpa [ht0] using he 0 : (s 0 : ℝ) = 0)
      have hs' : primitive n (Fin.tail s) := by simpa [primitive, hs0] using hs
      have ht' : primitive n (Fin.tail t) := by simpa [primitive, ht0] using ht
      exact ih hs' ht' (fun i ↦ he i.succ)
    · have hs0 : s 0 ≠ 0 := by
        intro hs0
        have hz := he 0
        rw [hs0, Int.cast_zero] at hz
        have htR : (t 0 : ℝ) ≠ 0 := by exact_mod_cast ht0
        exact (mul_ne_zero hc htR) hz.symm
      have htsign : t 0 = 1 ∨ t 0 = -1 := by
        rcases ht with h | h | ⟨h,_⟩
        · exact Or.inl h
        · exact Or.inr h
        · exact (ht0 h).elim
      have hssign : s 0 = 1 ∨ s 0 = -1 := by
        rcases hs with h | h | ⟨h,_⟩
        · exact Or.inl h
        · exact Or.inr h
        · exact (hs0 h).elim
      rcases htsign with h | h <;> rcases hssign with h' | h'
      all_goals have hz := he 0; norm_num [h,h'] at hz; first | left; linarith | right; linarith

lemma exists_binary_coefficients (n : ℕ) :
    ∃ c : (Fin n → ℤ) →₀ ℂ, (∀ s ∈ c.support, primitive n s) ∧
      ∀ x, (binary n x : ℂ) = ∑ s ∈ c.support, c s*mFourier s x := by
  classical
  obtain ⟨c,hc,he⟩ := (Finsupp.mem_span_image_iff_linearCombination ℂ).mp (binary_spectrum n)
  refine ⟨c, ?_, ?_⟩
  · exact fun s hs ↦ ((Finsupp.mem_supported ℂ c).mp hc) hs
  · intro x
    have hh := congrFun he x
    simpa [Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_apply, smul_eq_mul] using hh.symm

lemma integral_character {n : ℕ} (s : Fin n → ℤ) :
    (∫ x : Fin n → UnitAddCircle, mFourier s x) = if s=0 then 1 else 0 := by
  classical
  simp only [mFourier, ContinuousMap.coe_mk, integral_fintype_prod_volume_eq_prod]
  simp_rw [integral_circle_fourier]
  by_cases hs : s=0
  · simp [hs]
  · rw [if_neg hs]
    obtain ⟨i,hi⟩ := Function.ne_iff.mp hs
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simpa using hi

lemma coeff_finite_sum {n : ℕ} (c : (Fin n → ℤ) →₀ ℂ) (s : Fin n → ℤ) :
    mFourierCoeff (fun x ↦ ∑ t ∈ c.support, c t*mFourier t x) s = c s := by
  classical
  unfold mFourierCoeff
  simp only [smul_eq_mul, Finset.mul_sum]
  rw [integral_finsetSum]
  · have he (t : Fin n → ℤ) :
        (fun x : Fin n → UnitAddCircle ↦ mFourier (-s) x*(c t*mFourier t x)) =
        (fun x ↦ c t*mFourier (t-s) x) := by
      ext x
      rw [sub_eq_add_neg, mFourier_add]
      ring
    simp_rw [he, integral_const_mul, integral_character]
    have hz (t : Fin n → ℤ) : t-s=0 ↔ t=s := sub_eq_zero
    simp_rw [hz, mul_ite, mul_one, mul_zero]
    exact Finset.sum_ite_eq' _ _ _ |>.trans (by split_ifs with h <;> simp_all)
  · intro t ht
    apply integrable_cont
    fun_prop

lemma coeff_real_neg {n : ℕ} (f : (Fin n → UnitAddCircle) → ℝ) (s : Fin n → ℤ) :
    mFourierCoeff (fun x ↦ (f x : ℂ)) (-s) = conj (mFourierCoeff (fun x ↦ (f x : ℂ)) s) := by
  unfold mFourierCoeff
  trans ∫ x : Fin n → UnitAddCircle, conj (mFourier (-s) x*(f x : ℂ))
  · apply integral_congr_ae
    filter_upwards [] with x
    simp [mFourier_neg]
  · simpa only [smul_eq_mul] using! integral_conj

lemma parseval_continuous {n : ℕ} (f : C((Fin n → UnitAddCircle), ℂ)) :
    HasSum (fun s ↦ ‖mFourierCoeff f s‖^2) (∫ x, ‖f x‖^2) := by
  have hh := hasSum_sq_mFourierCoeff (f.toLp 2 volume ℂ)
  simp only [mFourierCoeff_toLp] at hh
  convert hh using 1
  apply integral_congr_ae
  filter_upwards [f.coeFn_toLp (p := 2) (𝕜 := ℂ) volume] with x hx
  rw [hx]

lemma binary_coefficients_energy {n : ℕ} (c : (Fin n → ℤ) →₀ ℂ)
    (he : ∀ x, (binary n x : ℂ) = ∑ s ∈ c.support, c s*mFourier s x) :
    (∑ s ∈ c.support, ‖c s‖^2) = energy n := by
  classical
  let f : C((Fin n → UnitAddCircle),ℂ) := ⟨fun x ↦ (binary n x : ℂ), by (have hc := binary_continuous n; fun_prop)⟩
  have hf : ∀ s, mFourierCoeff f s = c s := by
    intro s
    convert coeff_finite_sum c s using 1
    exact congrArg (fun g ↦ mFourierCoeff g s) (funext he)
  have hh := parseval_continuous f
  simp_rw [hf] at hh
  have he' : (∫ x, ‖f x‖^2) = energy n := by
    apply integral_congr_ae
    filter_upwards [] with x
    simp [f, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [he'] at hh
  have hs : HasSum (fun s ↦ ‖c s‖^2) (∑ s ∈ c.support, ‖c s‖^2) :=
    hasSum_sum_of_ne_finset_zero (fun s hs ↦ by simp [Finsupp.notMem_support_iff.mp hs])
  exact hs.unique hh

def positive : (n : ℕ) → (Fin n → ℤ) → Prop
  | 0, _ => False
  | n+1, s => s 0=1 ∨ (s 0=0 ∧ positive n (Fin.tail s))

lemma positive_primitive {n : ℕ} {s : Fin n → ℤ} (h : positive n s) :
    primitive n s := by
  induction n with
  | zero => exact h.elim
  | succ n ih =>
    rcases h with h | ⟨h,ht⟩
    · exact Or.inl h
    · exact Or.inr (Or.inr ⟨h,ih ht⟩)

lemma positive_not_neg {n : ℕ} {s : Fin n → ℤ} (h : positive n s) :
    ¬ positive n (-s) := by
  induction n with
  | zero => exact h.elim
  | succ n ih =>
    intro hn
    rcases h with h | ⟨h,ht⟩ <;> rcases hn with hn | ⟨hn,hnt⟩
    · simp [h] at hn
    · simp [h] at hn
    · simp [h] at hn
    · exact ih ht hnt

lemma primitive_positive_or_neg {n : ℕ} {s : Fin n → ℤ} (h : primitive n s) :
    positive n s ∨ positive n (-s) := by
  induction n with
  | zero => exact h.elim
  | succ n ih =>
    rcases h with h | h | ⟨h,ht⟩
    · exact Or.inl (Or.inl h)
    · exact Or.inr (Or.inl (by simp [h]))
    · rcases ih ht with hp | hp
      · exact Or.inl (Or.inr ⟨h,hp⟩)
      · exact Or.inr (Or.inr ⟨by simp [h],hp⟩)

lemma positive_parallel_eq {n : ℕ} {s t : Fin n → ℤ}
    (hs : positive n s) (ht : positive n t) {c : ℝ}
    (he : ∀ i, (s i : ℝ) = c*(t i : ℝ)) : s=t ∧ c=1 := by
  rcases primitive_parallel_scalar (positive_primitive hs) (positive_primitive ht) he with hc | hc
  · refine ⟨?_,hc⟩
    ext i
    exact_mod_cast (by simpa [hc] using he i : (s i : ℝ)=(t i : ℝ))
  · have hh : s = -t := by
      ext i
      exact_mod_cast (by simpa [hc] using he i : (s i : ℝ) = -(t i : ℝ))
    exact (positive_not_neg ht (hh ▸ hs)).elim

lemma binary_coefficients_conj {n : ℕ} (c : (Fin n → ℤ) →₀ ℂ)
    (he : ∀ x, (binary n x : ℂ) = ∑ s ∈ c.support, c s*mFourier s x) (s : Fin n → ℤ) :
    c (-s) = conj (c s) := by
  have hf (t : Fin n → ℤ) : mFourierCoeff (fun x ↦ (binary n x : ℂ)) t = c t := by
    convert coeff_finite_sum c t using 1
    exact congrArg (fun g ↦ mFourierCoeff g t) (funext he)
  simpa only [hf] using coeff_real_neg (binary n) s

lemma binary_support_neg {n : ℕ} (c : (Fin n → ℤ) →₀ ℂ)
    (he : ∀ x, (binary n x : ℂ) = ∑ s ∈ c.support, c s*mFourier s x) (s : Fin n → ℤ) :
    -s ∈ c.support ↔ s ∈ c.support := by
  simp only [Finsupp.mem_support_iff, binary_coefficients_conj c he, map_ne_zero]

lemma coefficient_support_pairs {n : ℕ} (c : (Fin n → ℤ) →₀ ℂ)
    (hp : ∀ s ∈ c.support, primitive n s)
    (he : ∀ x, (binary n x : ℂ) = ∑ s ∈ c.support, c s*mFourier s x) :
    ∃ S : Finset (Fin n → ℤ), (∀ s ∈ S, positive n s) ∧
      ∀ s, s ∈ c.support ↔ s ∈ S ∨ -s ∈ S := by
  classical
  refine ⟨c.support.filter (positive n),?_,?_⟩
  · exact fun s hs ↦ (Finset.mem_filter.mp hs).2
  · intro s
    simp only [Finset.mem_filter, binary_support_neg c he, ← and_or_left]
    exact ⟨fun hs ↦ ⟨hs,primitive_positive_or_neg (hp s hs)⟩,fun h ↦ h.1⟩

end
end Auxiliary
end AsymptoticallyMinimalLittlewood

end OAI



namespace OAI

universe uV uI

namespace AsymptoticallyMinimalLittlewood
namespace Curvature
noncomputable section
open scoped BigOperators Topology
open Filter

lemma separating_kernel {V : Type uV} [AddCommGroup V] [Module ℝ V]
    (f g : V →ₗ[ℝ] ℝ) (hf : f ≠ 0) (hfg : ∀ c : ℝ, g ≠ c • f) :
    ∃ x, f x = 0 ∧ g x ≠ 0 := by
  obtain ⟨e,he⟩ : ∃ e, f e ≠ 0 := by
    by_contra h
    push Not at h
    exact hf (LinearMap.ext h)
  by_contra h
  push Not at h
  apply hfg (g e/f e)
  ext x
  have hz : f (x-(f x/f e) • e) = 0 := by simp [he]
  have hg := h (x-(f x/f e) • e) hz
  simp only [map_sub, map_smul, LinearMap.smul_apply, smul_eq_mul] at hg ⊢
  field_simp [he] at hg ⊢
  nlinarith

lemma exists_generic {I : Type uI} {V : Type uV} [Finite I] [AddCommGroup V] [Module ℝ V]
    (f : I → V →ₗ[ℝ] ℝ) (hf : ∀ i, f i ≠ 0) :
    ∃ x, ∀ i, f i x ≠ 0 := by
  apply Module.Dual.exists_forall_ne_zero_of_forall_exists
  intro i
  by_contra hn
  push Not at hn
  exact hf i (LinearMap.ext hn)

lemma exists_kernel_vectors {I : Type uI} {V : Type uV} [Fintype I] [DecidableEq I]
    [AddCommGroup V] [Module ℝ V] (f : I → V →ₗ[ℝ] ℝ)
    (hf : ∀ i, f i ≠ 0) (hpair : ∀ i j, i ≠ j → ∀ c : ℝ, f i ≠ c • f j) :
    ∃ b : I → V, (∀ i, f i (b i) = 0) ∧ (∀ i j, i ≠ j → f i (b j) ≠ 0) := by
  have h (j : I) : ∃ x, f j x=0 ∧ ∀ i, i ≠ j → f i x ≠ 0 := by
    let J := {i : I // i ≠ j}
    obtain ⟨x,hx,hall⟩ := Module.Dual.exists_forall_mem_ne_zero_of_forall_exists
      (LinearMap.ker (f j)) (fun i : J ↦ f i.val) (by
        intro i
        obtain ⟨y,hy,hy'⟩ := separating_kernel (f j) (f i.val) (hf j) (hpair _ _ i.property)
        exact ⟨y,hy,hy'⟩)
    exact ⟨x,hx,fun i hi ↦ hall ⟨i,hi⟩⟩
  choose b hb hc using h
  exact ⟨b,hb,fun i j hij ↦ hc j i hij⟩

/-- Given any prescribed positive factors A_i, the products of curvatures
can be made simultaneously (1±delta) tau A_i, with all curvatures nonzero.
The theorem is used with A_i=|c_i|^2/rho_i. -/
theorem determinant_tuning {I : Type uI} {V : Type uV} [Fintype I] [DecidableEq I]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (f : I → V →ₗ[ℝ] ℝ) (hf : ∀ i, f i ≠ 0)
    (hpair : ∀ i j, i ≠ j → ∀ c : ℝ, f i ≠ c • f j)
    (A : I → ℝ) (hA : ∀ i, 0 < A i) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ τ : ℝ, 0 < τ ∧ ∃ b : I → V,
      (∀ i j, f i (b j) ≠ 0) ∧
      ∀ i, (1-δ)*τ*A i ≤ ∏ j, |f i (b j)| ∧
        (∏ j, |f i (b j)|) ≤ (1+δ)*τ*A i := by
  obtain ⟨b0,hb0,hb0'⟩ := exists_kernel_vectors f hf hpair
  obtain ⟨e,he⟩ := exists_generic f hf
  let P0 (i : I) : ℝ := ∏ j ∈ Finset.univ.erase i, |f i (b0 j)|
  have hP0 (i : I) : 0 < P0 i := by
    apply Finset.prod_pos
    intro j hj
    exact abs_pos.mpr (hb0' i j (Finset.ne_of_mem_erase hj).symm)
  let b1 (i : I) : V := (A i/(f i e*P0 i)) • e
  have hb1 (i : I) : f i (b1 i) = A i/P0 i := by
    dsimp [b1]
    rw [map_smul, smul_eq_mul]
    field_simp [he i, (hP0 i).ne']
  let b (t : ℝ) (j : I) : V := b0 j+t • b1 j
  let P (i : I) (t : ℝ) : ℝ := |f i (b1 i)| * ∏ j ∈ Finset.univ.erase i, |f i (b t j)|
  have hP (i : I) : Continuous (P i) := by
    dsimp [P,b]
    have hh := (f i).continuous_of_finiteDimensional
    fun_prop
  have hPzero (i : I) : P i 0 = A i := by
    dsimp [P,b]
    simp only [zero_smul, add_zero, hb1]
    rw [abs_of_pos (div_pos (hA i) (hP0 i))]
    change A i/P0 i*P0 i = A i
    exact div_mul_cancel₀ _ (hP0 i).ne'
  have hevent : ∀ᶠ t : ℝ in 𝓝 0, ∀ i, |P i t-A i| < δ*A i := by
    rw [Filter.eventually_all]
    intro i
    have hh := (hP i).continuousAt.eventually (Metric.ball_mem_nhds (P i 0) (mul_pos hδ (hA i)))
    simpa [Metric.mem_ball, Real.dist_eq, hPzero] using hh
  obtain ⟨ε,hε,hball⟩ := Metric.eventually_nhds_iff.mp hevent
  let τ : ℝ := ε/2
  have hτ : 0 < τ := by dsimp [τ]; linarith
  have hd : dist τ 0 < ε := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hτ]
    dsimp [τ]
    linarith
  have hcl := hball hd
  have hprod (i : I) : (∏ j, |f i (b τ j)|) = τ*P i τ := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    dsimp [b,P]
    rw [map_add, hb0, zero_add, map_smul, smul_eq_mul, abs_mul, abs_of_pos hτ]
    ring
  have hpos (i : I) : 0 < ∏ j, |f i (b τ j)| := by
    rw [hprod]
    apply mul_pos hτ
    have hh := (abs_lt.mp (hcl i)).1
    nlinarith [hA i]
  refine ⟨τ,hτ,b τ,?_,?_⟩
  · intro i j hz
    have hh : (∏ j, |f i (b τ j)|) = 0 := Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hz])
    linarith [hpos i]
  · intro i
    rw [hprod]
    have hp := abs_lt.mp (hcl i)
    constructor <;> nlinarith [mul_pos hτ (sub_pos.mpr hp.2),
      mul_pos hτ (sub_pos.mpr hp.1)]

end
end Curvature
end AsymptoticallyMinimalLittlewood

end OAI



namespace OAI

/-! Smooth cutoffs of nearly full squared mass, required by both the spreading
and sampling constructions. -/
namespace AsymptoticallyMinimalLittlewood
namespace Cutoff
noncomputable section
open MeasureTheory Set
open scoped Topology ContDiff

lemma bump_mass (g : ContDiffBump (0 : ℝ)) :
    2*g.rIn ≤ ∫ x : ℝ, g x ^ 2 := by
  have hs : HasCompactSupport (fun x : ℝ ↦ g x ^ 2) := by
    simpa only [pow_two, Pi.mul_def] using
      (g.hasCompactSupport.mul_right (f' := (g : ℝ → ℝ)))
  have hi : Integrable (fun x : ℝ ↦ g x ^ 2) :=
    ((show ContDiff ℝ ∞ g from g.contDiff).continuous.pow 2).integrable_of_hasCompactSupport hs
  have hmono : (∫ x in Icc (-g.rIn) g.rIn, g x ^ 2) ≤ ∫ x : ℝ, g x ^ 2 :=
    setIntegral_le_integral hi (Filter.Eventually.of_forall (fun x ↦ sq_nonneg _))
  have hone : (∫ x in Icc (-g.rIn) g.rIn, g x ^ 2) = 2*g.rIn := by
    calc
      _ = ∫ _ : ℝ in Icc (-g.rIn) g.rIn, (1 : ℝ) := by
        apply setIntegral_congr_fun measurableSet_Icc
        intro x hx
        have hx' : x ∈ Metric.closedBall (0 : ℝ) g.rIn := by
          simpa [Metric.mem_closedBall, Real.dist_eq, abs_le] using hx
        simp only [g.one_of_mem_closedBall hx', one_pow]
      _ = 2*g.rIn := by
        simp [sub_neg_eq_add, g.rIn_pos.le]
        ring
  rwa [hone] at hmono

theorem unit_cutoff {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧
      (∃ α : ℝ, 0 < α ∧ α < 1/2 ∧ tsupport g ⊆ Icc (-α) α) ∧
      (∀ x, 0 ≤ g x ∧ g x ≤ 1) ∧
      1-ε < ∫ x : ℝ, g x ^ 2 := by
  obtain ⟨a,ha0,ha1⟩ := exists_between (show max (0:ℝ) ((1-ε)/2) < 1/2 by
    rw [max_lt_iff]; constructor <;> linarith)
  have ha : 0<a := lt_of_le_of_lt (le_max_left _ _) ha0
  have ham : (1-ε)/2<a := lt_of_le_of_lt (le_max_right _ _) ha0
  obtain ⟨b,hab,hb⟩ := exists_between ha1
  let g : ContDiffBump (0 : ℝ) := ⟨a,b,ha,hab⟩
  refine ⟨g,g.contDiff,g.hasCompactSupport,⟨b,ha.trans hab,hb,?_⟩,
    fun x ↦ ⟨g.nonneg,g.le_one⟩,?_⟩
  · rw [g.tsupport_eq]
    intro x hx
    simpa [Metric.mem_closedBall, Real.dist_eq, abs_le, g] using hx
  · have h := bump_mass g
    change 2*a ≤ _ at h
    linarith

end
end Cutoff
end AsymptoticallyMinimalLittlewood

end OAI



namespace OAI

universe uI uZ

namespace AsymptoticallyMinimalLittlewood
namespace QuadraticTail
noncomputable section
open MeasureTheory Filter Topology Complex
open scoped BigOperators ContDiff

def phase (t u x : ℝ) : ℂ :=
  Complex.exp (Complex.I * (2*Real.pi*(t*x^2/2-u*x) : ℝ))

def amp (g : ℝ → ℂ) (t u : ℝ) (k : ℕ) (x : ℝ) : ℂ :=
  g x / ((t*x-u : ℝ) : ℂ)^k

def osc (g : ℝ → ℂ) (t u : ℝ) (k : ℕ) : ℂ :=
  ∫ x : ℝ, amp g t u k x * phase t u x

lemma phase_norm (t u x : ℝ) : ‖phase t u x‖ = 1 := by
  rw [phase, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, mul_zero, sub_zero, Real.exp_zero]

lemma phase_smooth (t u : ℝ) : ContDiff ℝ ∞ (phase t u) := by
  have hc : ContDiff ℝ ∞ (fun x : ℝ ↦ 2*Real.pi*(t*x^2/2-u*x)) := by fun_prop
  exact ((contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ ↦ Complex.I)).mul
    (Complex.ofRealCLM.contDiff.comp hc)).cexp

lemma phase_deriv (t u x : ℝ) : HasDerivAt (phase t u)
    (2*Real.pi*Complex.I*((t*x-u : ℝ) : ℂ)*phase t u x) x := by
  have hr : HasDerivAt (fun y : ℝ ↦ 2*Real.pi*(t*y^2/2-u*y))
      (2*Real.pi*(t*x-u)) x := by
    convert (((((hasDerivAt_id x).pow 2).const_mul t).div_const 2).sub
      ((hasDerivAt_id x).const_mul u)).const_mul (2*Real.pi) using 1 <;> first | rfl | (dsimp; ring)
  have hh := (hr.ofReal_comp.const_mul Complex.I).cexp
  change HasDerivAt (phase t u) _ x at hh
  convert hh using 1
  dsimp only [phase]
  push_cast
  ring

lemma amp_smooth {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (t u : ℝ) (k : ℕ)
    (havoid : ∀ x ∈ tsupport g, t*x-u ≠ 0) : ContDiff ℝ ∞ (amp g t u k) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases h : t*x-u = 0
  · have hx : x ∉ tsupport g := fun hx ↦ havoid x hx h
    rw [notMem_tsupport_iff_eventuallyEq] at hx
    apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℝ ↦ (0:ℂ)) x).congr_of_eventuallyEq
    filter_upwards [hx] with y hy
    simp [amp, hy]
  · have hr : ContDiff ℝ ∞ (fun y : ℝ ↦ t*y-u) := by fun_prop
    have hd : ContDiff ℝ ∞ (fun y : ℝ ↦ ((t*y-u : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp hr
    simpa only [amp, div_eq_mul_inv, Pi.inv_apply] using! hg.contDiffAt.mul
      ((hd.contDiffAt.pow k).inv (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr h)))

lemma amp_support (g : ℝ → ℂ) (t u : ℝ) (k : ℕ) :
    tsupport (amp g t u k) ⊆ tsupport g := by
  apply closure_mono
  intro x hx
  change amp g t u k x ≠ 0 at hx
  change g x ≠ 0
  intro h
  exact hx (by simp [amp, h])

lemma amp_compact {g : ℝ → ℂ} (hg : HasCompactSupport g) (t u : ℝ) (k : ℕ) :
    HasCompactSupport (amp g t u k) :=
  hg.mono' ((subset_tsupport _).trans (amp_support g t u k))

lemma amp_deriv {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (t u : ℝ) (k : ℕ)
    (havoid : ∀ x ∈ tsupport g, t*x-u ≠ 0) (x : ℝ) :
    HasDerivAt (amp g t u (k+1))
      (amp (deriv g) t u (k+1) x - ((k+1 : ℕ) : ℂ)*(t : ℂ)*amp g t u (k+2) x) x := by
  by_cases h : t*x-u = 0
  · have hx : x ∉ tsupport g := fun hx ↦ havoid x hx h
    have hz : g =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hx
    have hd : deriv g x = 0 := by
      exact (hz.hasDerivAt_iff.mpr (hasDerivAt_const x (0 : ℂ))).deriv
    simp only [amp, hd, h, Complex.ofReal_zero, zero_pow (by omega : k+1 ≠ 0),
      zero_pow (by omega : k+2 ≠ 0), div_zero, mul_zero, sub_zero]
    apply (hasDerivAt_const x (0 : ℂ)).congr_of_eventuallyEq
    filter_upwards [hz] with y hy
    simp [amp, hy]
  · have hd : HasDerivAt (fun y : ℝ ↦ ((t*y-u : ℝ) : ℂ)) (t : ℂ) x := by
      simpa using (((hasDerivAt_id x).const_mul t).sub_const u).ofReal_comp
    have hh := (hg.differentiable (by norm_num) x).hasDerivAt.div (hd.pow (k+1))
      (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr h))
    change HasDerivAt (amp g t u (k+1)) _ x at hh
    convert hh using 1
    simp only [amp, Pi.pow_apply, Nat.add_sub_cancel]
    have hc : ((t*x-u : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h
    rw [show k+2=(k+1)+1 by omega, pow_succ, pow_succ]
    field_simp [hc]
    ring

lemma osc_integrable {g : ℝ → ℂ} (hg : HasCompactSupport g) (hgs : ContDiff ℝ ∞ g)
    (t u : ℝ) (k : ℕ) (havoid : ∀ x ∈ tsupport g, t*x-u ≠ 0) :
    Integrable (fun x ↦ amp g t u k x * phase t u x) :=
  ((amp_smooth hgs t u k havoid).continuous.mul (phase_smooth t u).continuous).integrable_of_hasCompactSupport
    ((amp_compact hg t u k).mul_right)

lemma osc_parts {g : ℝ → ℂ} (hg : HasCompactSupport g) (hgs : ContDiff ℝ ∞ g)
    (t u : ℝ) (k : ℕ) (havoid : ∀ x ∈ tsupport g, t*x-u ≠ 0) :
    (2*Real.pi*Complex.I)*osc g t u k =
      -(osc (deriv g) t u (k+1) - ((k+1 : ℕ) : ℂ)*(t : ℂ)*osc g t u (k+2)) := by
  have hgd : ContDiff ℝ ∞ (deriv g) := (contDiff_infty_iff_deriv.mp hgs).2
  have havd : ∀ x ∈ tsupport (deriv g), t*x-u ≠ 0 :=
    fun x hx ↦ havoid x (tsupport_deriv_subset hx)
  have hi1 := osc_integrable hg hgs t u k havoid
  have hi2 := osc_integrable hg.deriv hgd t u (k+1) havd
  have hi3 := osc_integrable hg hgs t u (k+2) havoid
  have hprod (x : ℝ) : amp g t u (k+1) x *
      (2*Real.pi*Complex.I*((t*x-u : ℝ) : ℂ)*phase t u x) =
      (2*Real.pi*Complex.I)*(amp g t u k x*phase t u x) := by
    by_cases h : t*x-u=0
    · have hx : g x=0 := Function.notMem_support.mp (fun hx ↦ havoid x (subset_tsupport _ hx) h)
      simp [amp, hx]
    · dsimp [amp]
      have hc : ((t*x-u : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h
      rw [pow_succ]
      field_simp [hc]
  have hprod2 (x : ℝ) : (amp (deriv g) t u (k+1) x -
      ((k+1 : ℕ) : ℂ)*(t : ℂ)*amp g t u (k+2) x)*phase t u x =
      amp (deriv g) t u (k+1) x*phase t u x -
      (((k+1 : ℕ) : ℂ)*(t : ℂ))*(amp g t u (k+2) x*phase t u x) := by ring
  have hh := MeasureTheory.integral_bilinear_hasDerivAt_right_eq_neg_left_of_integrable
    (L := ContinuousLinearMap.mul ℝ ℂ)
    (fun x _ ↦ amp_deriv hgs t u k havoid x)
    (fun x _ ↦ phase_deriv t u x)
    (show Integrable (fun x ↦ amp g t u (k+1) x *
      (2*Real.pi*Complex.I*((t*x-u : ℝ) : ℂ)*phase t u x)) volume by
      simp_rw [hprod]; exact hi1.const_mul _)
    (show Integrable (fun x ↦ (amp (deriv g) t u (k+1) x -
      ((k+1 : ℕ) : ℂ)*(t : ℂ)*amp g t u (k+2) x)*phase t u x) volume by
      simp_rw [hprod2]; exact hi2.sub (hi3.const_mul _))
    (osc_integrable hg hgs t u (k+1) havoid)
  change (∫ x : ℝ, amp g t u (k+1) x *
      (2*Real.pi*Complex.I*((t*x-u : ℝ) : ℂ)*phase t u x)) =
    -(∫ x : ℝ, (amp (deriv g) t u (k+1) x -
      ((k+1 : ℕ) : ℂ)*(t : ℂ)*amp g t u (k+2) x)*phase t u x) at hh
  simp_rw [hprod, hprod2] at hh
  rw [integral_const_mul, integral_sub hi2 (hi3.const_mul _), integral_const_mul] at hh
  exact hh

lemma osc_bound_zero {g : ℝ → ℂ} (hg : HasCompactSupport g) (hgs : ContDiff ℝ ∞ g)
    {c M : ℝ} (hc : 0 < c) (hM : 0 < M) (t u : ℝ) (k : ℕ)
    (hsep : ∀ x ∈ tsupport g, c*M ≤ |t*x-u|) :
    M^k * ‖osc g t u k‖ ≤ (∫ x : ℝ, ‖g x‖) / c^k := by
  have hav : ∀ x ∈ tsupport g, t*x-u ≠ 0 := by
    intro x hx hz
    have := hsep x hx
    rw [hz, abs_zero] at this
    nlinarith [mul_pos hc hM]
  have hi := osc_integrable hg hgs t u k hav
  have hpoint (x : ℝ) : M^k * ‖amp g t u k x*phase t u x‖ ≤ ‖g x‖ / c^k := by
    by_cases hx : g x=0
    · simp [amp, hx]
    · have hx' := subset_tsupport g hx
      have hz : 0 < |t*x-u| := lt_of_lt_of_le (mul_pos hc hM) (hsep x hx')
      rw [norm_mul, phase_norm, mul_one, amp, norm_div, norm_pow, Complex.norm_real]
      rw [Real.norm_eq_abs, ← mul_div_assoc, div_le_div_iff₀ (pow_pos hz _) (pow_pos hc _)]
      have hp := pow_le_pow_left₀ (le_of_lt (mul_pos hc hM)) (hsep x hx') k
      rw [mul_pow] at hp
      nlinarith [mul_le_mul_of_nonneg_left hp (norm_nonneg (g x))]
  calc
    M^k * ‖osc g t u k‖ ≤ M^k * ∫ x : ℝ, ‖amp g t u k x*phase t u x‖ :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (pow_nonneg hM.le _)
    _ = ∫ x : ℝ, M^k * ‖amp g t u k x*phase t u x‖ := (integral_const_mul _ _).symm
    _ ≤ ∫ x : ℝ, ‖g x‖ / c^k := integral_mono (hi.norm.const_mul _)      ((hgs.continuous.norm.integrable_of_hasCompactSupport hg.norm).div_const _) hpoint
    _ = (∫ x : ℝ, ‖g x‖) / c^k := integral_div _ _

/-- Uniform repeated nonstationary integration by parts, with the support condition
on the actual amplitude. The parameters may vary, but c and B stay fixed. -/
theorem polynomial_decay (l : ℕ) (c B : ℝ) (hc : 0 < c) (hB : 0 ≤ B) :
    ∀ (g : ℝ → ℂ), HasCompactSupport g → ContDiff ℝ ∞ g → ∀ k : ℕ,
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t u M : ℝ), 0 < M → |t| ≤ B*M →
      (∀ x ∈ tsupport g, c*M ≤ |t*x-u|) → M^(k+l)*‖osc g t u k‖ ≤ C := by
  induction l with
  | zero =>
      intro g hg hgs k
      refine ⟨(∫ x : ℝ, ‖g x‖)/c^k, div_nonneg (integral_nonneg (fun x ↦ norm_nonneg _))
        (pow_nonneg hc.le _), ?_⟩
      intro t u M hM ht hs
      simpa using osc_bound_zero hg hgs hc hM t u k hs
  | succ l ih =>
      intro g hg hgs k
      have hgd : ContDiff ℝ ∞ (deriv g) := (contDiff_infty_iff_deriv.mp hgs).2
      obtain ⟨C1, hC1, h1⟩ := ih (deriv g) hg.deriv hgd (k+1)
      obtain ⟨C2, hC2, h2⟩ := ih g hg hgs (k+2)
      refine ⟨(C1+(k+1)*B*C2)/(2*Real.pi), by positivity, ?_⟩
      intro t u M hM ht hs
      have hav : ∀ x ∈ tsupport g, t*x-u ≠ 0 := by
        intro x hx hz
        have := hs x hx
        rw [hz, abs_zero] at this
        nlinarith [mul_pos hc hM]
      have hs' : ∀ x ∈ tsupport (deriv g), c*M ≤ |t*x-u| :=
        fun x hx ↦ hs x (tsupport_deriv_subset hx)
      have hh1 := h1 t u M hM ht hs'
      have hh2 := h2 t u M hM ht hs
      have hnorm : (2*Real.pi)*‖osc g t u k‖ ≤
          ‖osc (deriv g) t u (k+1)‖+(k+1)*|t| * ‖osc g t u (k+2)‖ := by
        have he := congrArg norm (osc_parts hg hgs t u k hav)
        have htriangle := norm_sub_le (osc (deriv g) t u (k+1))
          (((k+1 : ℕ) : ℂ)*(t : ℂ)*osc g t u (k+2))
        simp only [norm_mul, norm_neg, Complex.norm_I, mul_one, Complex.norm_ofNat,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, Complex.norm_natCast] at he htriangle
        push_cast at he htriangle
        linarith
      have hterm : M^(k+l+1)*|t| * ‖osc g t u (k+2)‖ ≤ B*C2 := by
        calc
          _ ≤ M^(k+l+1)*(B*M)*‖osc g t u (k+2)‖ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht (pow_nonneg hM.le _)) (norm_nonneg _)
          _ = B*(M^(k+2+l)*‖osc g t u (k+2)‖) := by
            rw [show k+2+l=(k+l+1)+1 by omega, pow_succ]; ring
          _ ≤ B*C2 := mul_le_mul_of_nonneg_left hh2 hB
      rw [le_div_iff₀ (by positivity : 0 < 2*Real.pi)]
      have hp := mul_le_mul_of_nonneg_left hnorm (pow_nonneg hM.le (k+l+1))
      have hk : (0:ℝ) ≤ k+1 := by positivity
      have hterm' := mul_le_mul_of_nonneg_left hterm hk
      have e1 : k+1+l=k+l+1 := by omega
      rw [e1] at hh1
      have e2 : k+(l+1)=k+l+1 := by omega
      rw [e2]
      nlinarith only [hp, hh1, hterm']

/-- Off-box decay in precisely the regime used to truncate the spread spectrum. -/
theorem offbox_decay {g : ℝ → ℂ} (hg : HasCompactSupport g) (hgs : ContDiff ℝ ∞ g)
    {α β : ℝ} (hα : 0 ≤ α) (hα' : α < 1/2) (hβ : β ≠ 0)
    (hsupp : tsupport g ⊆ Set.Icc (-α) α) (l : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T w : ℝ, 0 < T → T*|β|/2 < |w| →
      (T+|w|)^l * ‖∫ x : ℝ, g x*phase (T*β) w x‖ ≤ C := by
  let c : ℝ := (1-2*α)/(1+2/|β|)
  have hb : 0 < |β| := abs_pos.mpr hβ
  have hc : 0 < c := by
    dsimp [c]
    exact div_pos (by linarith) (by positivity)
  obtain ⟨C,hC,htail⟩ := polynomial_decay l c |β| hc (abs_nonneg _) g hg hgs 0
  refine ⟨C,hC,?_⟩
  intro T w hT hw
  have hM : 0 < T+|w| := by positivity
  have ht : |T*β| ≤ |β| *(T+|w|) := by
    rw [abs_mul, abs_of_pos hT]; nlinarith [mul_nonneg (abs_nonneg β) (abs_nonneg w)]
  have hs : ∀ x ∈ tsupport g, c*(T+|w|) ≤ |T*β*x-w| := by
    intro x hx
    have hx' : |x| ≤ α := abs_le.mpr (hsupp hx)
    have h1 : c*(T+|w|) ≤ (1-2*α)*|w| := by
      dsimp [c]
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : 0 < 1+2/|β|)]
      have hw' : T ≤ 2*|w|/|β| := by rw [le_div_iff₀ hb]; linarith
      have hh := mul_le_mul_of_nonneg_left hw' (by linarith : 0 ≤ 1-2*α)
      convert add_le_add_right hh ((1-2*α)*|w|) using 1 <;> ring
    have hab : |T*β*x| ≤ T*|β| *α := by
      rw [abs_mul, abs_mul, abs_of_pos hT]
      exact mul_le_mul_of_nonneg_left hx' (by positivity)
    have htri : |w| ≤ |T*β*x-w| + |T*β*x| := by
      have hh := abs_add_le (w-T*β*x) (T*β*x)
      rw [sub_add_cancel, abs_sub_comm] at hh
      exact hh
    have hmul := mul_le_mul_of_nonneg_right (le_of_lt hw) hα
    linarith
  have hh := htail (T*β) w (T+|w|) hM ht hs
  simpa [osc, amp] using hh

lemma phase_fourier (t x : ℝ) (w : ℤ) :
    fourier (-w) (x : UnitAddCircle) * phase t 0 x = phase t w x := by
  rw [fourier_coe_apply, phase, phase, ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma cutoff_zero {g : ℝ → ℂ} {α x : ℝ}
    (hs : tsupport g ⊆ Set.Icc (-α) α) (hx : x ∉ Set.Icc (-α) α) : g x=0 :=
  image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hs h))

def circleChirp (g : ℝ → ℂ) (t : ℝ) : UnitAddCircle → ℂ :=
  AddCircle.liftIoc 1 (-1/2) (fun x ↦ g x*phase t 0 x)

lemma circleChirp_continuous {g : ℝ → ℂ} (hg : Continuous g) {α : ℝ}
    (hα : α<1/2) (hs : tsupport g ⊆ Set.Icc (-α) α) (t : ℝ) :
    Continuous (circleChirp g t) := by
  apply AddCircle.liftIoc_continuous
  · have hleft : g (-1/2)=0 := cutoff_zero hs (by intro h; rcases h with ⟨h1,h2⟩; linarith)
    have hright : g (-1/2+1)=0 := cutoff_zero hs (by intro h; rcases h with ⟨h1,h2⟩; linarith)
    simp only [hleft,hright,zero_mul]
  · exact (hg.mul (phase_smooth t 0).continuous).continuousOn

lemma circleChirp_coefficient {g : ℝ → ℂ} {α : ℝ}
    (hα : α<1/2) (hs : tsupport g ⊆ Set.Icc (-α) α) (t : ℝ) (w : ℤ) :
    fourierCoeff (circleChirp g t) w = ∫ x : ℝ, g x*phase t w x := by
  rw [fourierCoeff_eq_intervalIntegral _ w (-1/2)]
  simp only [div_self (one_ne_zero : (1:ℝ) ≠ 0), one_smul]
  rw [intervalIntegral.integral_of_le (by norm_num : (-1/2:ℝ)≤ -1/2+1)]
  calc
    _ = ∫ x in Set.Ioc (-1/2:ℝ) (-1/2+1), g x*phase t w x := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro x hx
      dsimp only [circleChirp]
      rw [AddCircle.liftIoc_coe_apply hx, smul_eq_mul]
      calc
        _ = g x*(fourier (-w) (x : UnitAddCircle)*phase t 0 x) := by ring
        _ = _ := by rw [phase_fourier]
    _ = _ := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have hz : g x=0 := cutoff_zero hs (by
        intro ⟨hx1,hx2⟩
        apply hx
        constructor <;> linarith)
      rw [hz,zero_mul]

def latticeWeight (w : ℤ) : ℝ := 1/(1+|(w:ℝ)|)^2

lemma latticeWeight_pos (w : ℤ) : 0 < latticeWeight w := by
  dsimp [latticeWeight]
  positivity

lemma latticeWeight_summable : Summable latticeWeight := by
  have hn : Summable (fun n : ℕ ↦ 1/(1+(n:ℝ))^2) := by
    have h := (summable_nat_add_iff 1).mpr
      (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2:ℕ)))
    simpa only [Nat.cast_add, Nat.cast_one, add_comm] using h
  have hpos : (fun n : ℕ ↦ latticeWeight (n : ℤ)) = (fun n : ℕ ↦ 1/(1+(n:ℝ))^2) := by
    funext n
    simp [latticeWeight]
  have hneg : (fun n : ℕ ↦ latticeWeight (-(n : ℤ))) = (fun n : ℕ ↦ 1/(1+(n:ℝ))^2) := by
    funext n
    simp [latticeWeight]
  exact Summable.of_nat_of_neg (hpos ▸ hn) (hneg ▸ hn)

noncomputable def box (T β : ℝ) : Finset ℤ :=
  Finset.Icc (-⌊T*|β|/2⌋) ⌊T*|β|/2⌋

lemma mem_box (T β : ℝ) (w : ℤ) :
    w ∈ box T β ↔ |(w:ℝ)| ≤ T*|β|/2 := by
  rw [box, Finset.mem_Icc, ← abs_le, ← Int.cast_abs, ← Int.le_floor]

lemma box_card_le {T : ℝ} (hT : 0≤T) (β : ℝ) :
    ((box T β).card : ℝ) ≤ T*|β|+1 := by
  have hfloor : 0 ≤ ⌊T*|β|/2⌋ := Int.floor_nonneg.mpr (by positivity)
  have hc := Int.card_Icc_of_le (-⌊T*|β|/2⌋) ⌊T*|β|/2⌋ (show -⌊T*|β|/2⌋ ≤ ⌊T*|β|/2⌋+1 by omega)
  have hcR : ((box T β).card : ℝ) = 2*(⌊T*|β|/2⌋ : ℝ)+1 := by
    simp only [box]
    exact_mod_cast (by omega : (Finset.Icc (-⌊T*|β|/2⌋) ⌊T*|β|/2⌋).card =
      (2*⌊T*|β|/2⌋+1 : ℤ))
  rw [hcR]
  linarith [Int.floor_le (T*|β|/2)]

/-- A summable majorant for the discarded one-dimensional Fourier tail.
This uses three integrations by parts (or n+2 for the stronger form), and
avoids an unjustified summation of stationary-phase errors. -/
theorem offbox_weighted {g : ℝ → ℂ} (hg : HasCompactSupport g)
    (hgs : ContDiff ℝ ∞ g) {α : ℝ} (hα0 : 0≤α) (hα : α<1/2)
    (hs : tsupport g ⊆ Set.Icc (-α) α) {β : ℝ} (hβ : β ≠ 0) (n : ℕ) :
    ∃ C : ℝ, 0≤C ∧ ∀ T : ℝ, 1≤T → ∀ w : ℤ, w ∉ box T β →
      ‖∫ x : ℝ, g x*phase (T*β) w x‖ ≤ C / T^n * latticeWeight w := by
  obtain ⟨C,hC,hbound⟩ := offbox_decay hg hgs hα0 hα hβ hs (n+2)
  refine ⟨C,hC,?_⟩
  intro T hT w hw
  have hTpos : 0<T := lt_of_lt_of_le zero_lt_one hT
  have hw' : T*|β|/2 < |(w:ℝ)| := lt_of_not_ge (by simpa only [← mem_box] using hw)
  have hb := hbound T w hTpos hw'
  have hp : T^n*(1+|(w:ℝ)|)^2 ≤ (T+|(w:ℝ)|)^(n+2) := by
    rw [pow_add]
    apply mul_le_mul
    · exact pow_le_pow_left₀ hTpos.le (le_add_of_nonneg_right (abs_nonneg _)) n
    · exact pow_le_pow_left₀ (by positivity) (by linarith : 1+|(w:ℝ)|≤T+|(w:ℝ)|) 2
    · positivity
    · positivity
  have hh : T^n*(1+|(w:ℝ)|)^2*‖∫ x : ℝ, g x*phase (T*β) w x‖ ≤ C :=
    (mul_le_mul_of_nonneg_right hp (norm_nonneg _)).trans hb
  dsimp only [latticeWeight]
  calc
    _ ≤ C/(T^n*(1+|(w:ℝ)|)^2) := (le_div_iff₀ (by positivity)).mpr (by nlinarith only [hh])
    _ = _ := by rw [div_mul_eq_div_div]; ring

lemma circle_fourier_norm (w : ℤ) (z : UnitAddCircle) : ‖fourier w z‖=1 :=
  Circle.norm_coe _

/-- Uniform truncation from a summable majorant outside one finite box. -/
lemma fourier_truncation_error (f : C(UnitAddCircle,ℂ)) (S : Finset ℤ)
    (b : ℤ → ℝ) (hb : Summable b) (hb0 : ∀ w, 0≤b w)
    (hbound : ∀ w, w ∉ S → ‖fourierCoeff f w‖ ≤ b w) (z : UnitAddCircle) :
    ‖(∑ w ∈ S, fourierCoeff f w*fourier w z)-f z‖ ≤ ∑' w, b w := by
  classical
  have hcomp : Summable (fun w : {w : ℤ // w ∉ S} ↦ fourierCoeff f w.val) := by
    exact (hb.subtype _).of_norm_bounded (fun w ↦ hbound w.val w.property)
  have hh : Summable (fourierCoeff f) := (S.summable_compl_iff).mp hcomp
  have hs := has_pointwise_sum_fourier_series_of_summable hh z
  simp only [smul_eq_mul] at hs
  have hterm := hs.summable
  have he := hterm.sum_add_tsum_compl (s := S)
  rw [hs.tsum_eq] at he
  change (∑ w ∈ S, fourierCoeff f w*fourier w z) +
    (∑' w : {w : ℤ // w ∉ S}, fourierCoeff f w.val*fourier w.val z) = f z at he
  have heq : (∑ w ∈ S, fourierCoeff f w*fourier w z)-f z =
      -(∑' w : {w : ℤ // w ∉ S}, fourierCoeff f w.val*fourier w.val z) := by
    linear_combination he
  rw [heq, norm_neg]
  have hbc : Summable (fun w : {w : ℤ // w ∉ S} ↦ b w.val) := hb.subtype _
  calc
    _ ≤ ∑' w : {w : ℤ // w ∉ S}, b w.val := by
      apply ((hterm.subtype _).hasSum).norm_le_of_bounded hbc.hasSum
      intro w
      change ‖fourierCoeff f w.val * fourier w.val z‖ ≤ b w.val
      rw [norm_mul, circle_fourier_norm, mul_one]
      exact hbound w.val w.property
    _ ≤ ∑' w, b w := by
      exact hbc.tsum_le_tsum_of_inj Subtype.val Subtype.val_injective
        (fun w _ ↦ hb0 w) (fun _ ↦ le_rfl) hb

def rowTrunc (g : ℝ → ℂ) (T β : ℝ) (z : UnitAddCircle) : ℂ :=
  ∑ w ∈ box T β, (∫ x : ℝ, g x*phase (T*β) w x)*fourier w z

theorem rowTrunc_error {g : ℝ → ℂ} (hg : HasCompactSupport g)
    (hgs : ContDiff ℝ ∞ g) {α : ℝ} (hα0 : 0≤α) (hα : α<1/2)
    (hs : tsupport g ⊆ Set.Icc (-α) α) {β : ℝ} (hβ : β ≠ 0) :
    ∃ C : ℝ, 0≤C ∧ ∀ T : ℝ, 1≤T → ∀ z : UnitAddCircle,
      ‖rowTrunc g T β z-circleChirp g (T*β) z‖ ≤ C/T := by
  obtain ⟨C,hC,hbound⟩ := offbox_weighted hg hgs hα0 hα hs hβ 1
  refine ⟨C*(∑' w, latticeWeight w),mul_nonneg hC (tsum_nonneg (fun w ↦ (latticeWeight_pos w).le)),?_⟩
  intro T hT z
  let f : C(UnitAddCircle,ℂ) := ⟨circleChirp g (T*β),circleChirp_continuous hgs.continuous hα hs _⟩
  have hf (w : ℤ) : fourierCoeff f w = ∫ x : ℝ, g x*phase (T*β) w x :=
    circleChirp_coefficient hα hs _ _
  have hh := fourier_truncation_error f (box T β) (fun w ↦ C/T*latticeWeight w)
    (latticeWeight_summable.mul_left (C/T))
    (fun w ↦ mul_nonneg (div_nonneg hC (by linarith)) (latticeWeight_pos w).le)
    (fun w hw ↦ by rw [hf]; simpa only [pow_one] using hbound T hT w hw) z
  change ‖(∑ w ∈ box T β, fourierCoeff f w*fourier w z)-f z‖ ≤ _ at hh
  simp only [hf, tsum_mul_left] at hh
  convert hh using 1 <;> (try dsimp [rowTrunc, f])
  ring

lemma circleChirp_norm {g : ℝ → ℂ} (hg : ∀ x, ‖g x‖ ≤ 1)
    (t : ℝ) (z : UnitAddCircle) : ‖circleChirp g t z‖ ≤ 1 := by
  dsimp [circleChirp, AddCircle.liftIoc, Function.comp_def, Set.domRestrict]
  rw [norm_mul, phase_norm, mul_one]
  exact hg _

lemma circleChirp_mass {g : ℝ → ℂ} {α : ℝ} (hα : α<1/2)
    (hs : tsupport g ⊆ Set.Icc (-α) α) (t : ℝ) :
    (∫ z : UnitAddCircle, ‖circleChirp g t z‖^2 ∂AddCircle.haarAddCircle) =
      ∫ x : ℝ, ‖g x‖^2 := by
  rw [AddCircle.integral_haarAddCircle]
  simp only [inv_one, one_smul]
  rw [← AddCircle.integral_preimage 1 (-1/2)]
  calc
    _ = ∫ x in Set.Ioc (-1/2:ℝ) (-1/2+1), ‖g x‖^2 := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro x hx
      change ‖circleChirp g t (x : UnitAddCircle)‖^2 = ‖g x‖^2
      rw [circleChirp, AddCircle.liftIoc_coe_apply hx, norm_mul, phase_norm, mul_one]
    _ = _ := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have hz : g x=0 := cutoff_zero hs (by
        intro ⟨hx1,hx2⟩
        apply hx
        constructor <;> linarith)
      simp [hz]

lemma circle_parseval (f : C(UnitAddCircle,ℂ)) :
    HasSum (fun w : ℤ ↦ ‖fourierCoeff f w‖^2)
      (∫ z : UnitAddCircle, ‖f z‖^2 ∂AddCircle.haarAddCircle) := by
  have hh := hasSum_sq_fourierCoeff (f.toLp 2 AddCircle.haarAddCircle ℂ)
  simp only [fourierCoeff_toLp] at hh
  convert hh using 1
  apply integral_congr_ae
  filter_upwards [f.coeFn_toLp (p := 2) (𝕜 := ℂ) AddCircle.haarAddCircle] with x hx
  rw [hx]

lemma coefficient_norm_le_one (f : C(UnitAddCircle,ℂ)) (hf : ∀ z, ‖f z‖≤1)
    (w : ℤ) : ‖fourierCoeff f w‖ ≤ 1 := by
  unfold fourierCoeff
  calc
    _ ≤ ∫ z : UnitAddCircle, ‖fourier (-w) z • f z‖ ∂AddCircle.haarAddCircle :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ _z : UnitAddCircle, (1:ℝ) ∂AddCircle.haarAddCircle := by
      apply integral_mono
      · exact (show Continuous (fun z ↦ ‖fourier (-w) z • f z‖) by fun_prop).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
      · exact integrable_const _
      · intro z
        simpa only [norm_smul, circle_fourier_norm, one_mul] using hf z
    _ = 1 := by simp

/-- Retained squared Fourier mass loses only O(1/T), uniformly in the
quadratic modulation. This is the scalar Parseval ingredient for spreading. -/
theorem row_mass_error {g : ℝ → ℂ} (hg : HasCompactSupport g)
    (hgs : ContDiff ℝ ∞ g) (hg1 : ∀ x, ‖g x‖≤1) {α : ℝ}
    (hα0 : 0≤α) (hα : α<1/2) (hs : tsupport g ⊆ Set.Icc (-α) α)
    {β : ℝ} (hβ : β ≠ 0) :
    ∃ C : ℝ, 0≤C ∧ ∀ T : ℝ, 1≤T →
      (∫ x : ℝ, ‖g x‖^2) - C/T ≤
        ∑ w ∈ box T β, ‖∫ x : ℝ, g x*phase (T*β) w x‖^2 := by
  obtain ⟨C,hC,hbound⟩ := offbox_weighted hg hgs hα0 hα hs hβ 1
  refine ⟨C*(∑' w, latticeWeight w),mul_nonneg hC (tsum_nonneg (fun w ↦ (latticeWeight_pos w).le)),?_⟩
  intro T hT
  let f : C(UnitAddCircle,ℂ) := ⟨circleChirp g (T*β),circleChirp_continuous hgs.continuous hα hs _⟩
  have hf (w : ℤ) : fourierCoeff f w = ∫ x : ℝ, g x*phase (T*β) w x :=
    circleChirp_coefficient hα hs _ _
  have hp := circle_parseval f
  change HasSum _ (∫ z : UnitAddCircle, ‖circleChirp g (T*β) z‖^2 ∂AddCircle.haarAddCircle) at hp
  rw [circleChirp_mass hα hs] at hp
  have he := hp.summable.sum_add_tsum_compl (s := box T β)
  rw [hp.tsum_eq] at he
  change (∑ w ∈ box T β, ‖fourierCoeff f w‖^2) +
    (∑' w : {w : ℤ // w ∉ box T β}, ‖fourierCoeff f w.val‖^2) = _ at he
  have ht : (∑' w : {w : ℤ // w ∉ box T β}, ‖fourierCoeff f w.val‖^2) ≤
      C/T*(∑' w, latticeWeight w) := by
    calc
      _ ≤ ∑' w : {w : ℤ // w ∉ box T β}, C/T*latticeWeight w.val := by
        apply (hp.summable.subtype _).tsum_le_tsum
        · intro w
          have hn := coefficient_norm_le_one f (circleChirp_norm hg1 _) w.val
          have hb := hbound T hT w.val w.property
          change ‖fourierCoeff f w.val‖^2 ≤ _
          rw [hf]
          have hn' := norm_nonneg (fourierCoeff f w.val)
          rw [hf] at hn hn'
          simpa only [pow_one] using (show ‖∫ x : ℝ, g x*phase (T*β) w.val x‖^2 ≤
            C/T^1*latticeWeight w.val by nlinarith only [hn,hn',hb])
        · exact (latticeWeight_summable.mul_left (C/T)).subtype _
      _ ≤ ∑' w : ℤ, C/T*latticeWeight w := by
        exact ((latticeWeight_summable.mul_left (C/T)).subtype _).tsum_le_tsum_of_inj
          Subtype.val Subtype.val_injective
          (fun w _ ↦ mul_nonneg (div_nonneg hC (by linarith)) (latticeWeight_pos w).le)
          (fun _ ↦ le_rfl) (latticeWeight_summable.mul_left (C/T))
      _ = _ := tsum_mul_left
  simp_rw [hf] at he ht
  have heq : C/T*(∑' w, latticeWeight w) = (C*(∑' w, latticeWeight w))/T := by ring
  rw [heq] at ht
  linarith

/-- Tensoring finitely many uniformly bounded approximations preserves a
uniform O(1/T) error; both target functions may depend on T. -/
lemma finite_product_error {I : Type uI} {Z : Type uZ} (S : Finset I)
    (f h : I → ℝ → Z → ℂ)
    (hh : ∀ i ∈ S, ∀ T z, ‖h i T z‖≤1)
    (hf : ∀ i ∈ S, ∃ C : ℝ, 0≤C ∧ ∀ T, 1≤T → ∀ z, ‖f i T z-h i T z‖≤C/T) :
    ∃ C : ℝ, 0≤C ∧ ∀ T, 1≤T → ∀ z,
      ‖(∏ i ∈ S, f i T z)-(∏ i ∈ S, h i T z)‖ ≤ C/T := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0,le_rfl,by simp⟩
  | @insert i S hi ih =>
      obtain ⟨C,hC,hc⟩ := hf i (Finset.mem_insert_self _ _)
      obtain ⟨D,hD,hd⟩ := ih
        (fun j hj ↦ hh j (Finset.mem_insert_of_mem hj))
        (fun j hj ↦ hf j (Finset.mem_insert_of_mem hj))
      refine ⟨(1+C)*D+C,by positivity,?_⟩
      intro T hT z
      have hT0 : 0<T := by linarith
      have hn : ‖f i T z‖ ≤ 1+C := by
        have hb := norm_sub_norm_le (f i T z) (h i T z)
        have hc' := hc T hT z
        have hh' := hh i (Finset.mem_insert_self _ _) T z
        have hcT : C/T≤C := (div_le_self hC hT)
        linarith
      have hp : ‖∏ j ∈ S, h j T z‖≤1 := by
        rw [norm_prod]
        exact Finset.prod_le_one (fun j _ ↦ norm_nonneg (h j T z)) (fun j hj ↦ hh j (Finset.mem_insert_of_mem hj) T z)
      rw [Finset.prod_insert hi, Finset.prod_insert hi]
      calc
        _ = ‖f i T z*((∏ j ∈ S, f j T z)-(∏ j ∈ S, h j T z)) +
          (f i T z-h i T z)*(∏ j ∈ S, h j T z)‖ := by congr 1; ring
        _ ≤ ‖f i T z‖*‖(∏ j ∈ S, f j T z)-(∏ j ∈ S, h j T z)‖ +
          ‖f i T z-h i T z‖*‖∏ j ∈ S, h j T z‖ := by
            simpa only [norm_mul] using norm_add_le
              (f i T z*((∏ j ∈ S, f j T z)-(∏ j ∈ S, h j T z)))
              ((f i T z-h i T z)*(∏ j ∈ S, h j T z))
        _ ≤ (1+C)*(D/T)+(C/T)*1 := by
          apply add_le_add
          · exact mul_le_mul hn (hd T hT z) (norm_nonneg _) (by positivity)
          · exact mul_le_mul (hc T hT z) hp (norm_nonneg _) (by positivity)
        _ = _ := by ring

end
end QuadraticTail
end AsymptoticallyMinimalLittlewood

end OAI



namespace OAI

universe uI uE uJ uK

namespace AsymptoticallyMinimalLittlewood
namespace Spreading
noncomputable section
open QuadraticTail MeasureTheory Filter Topology Complex
open scoped BigOperators ContDiff FourierTransform SchwartzMap

/-- The uniform stationary-phase bound in the squared, scale-invariant form
needed for every retained spread Fourier coefficient. -/
lemma quadratic_norm_scaled {g : ℝ → ℂ} (hg : HasCompactSupport g)
    (hgs : ContDiff ℝ ∞ g) (hg1 : ∀ x, ‖g x‖≤1)
    {β : ℝ} (hβ : β≠0) :
    ∃ C : ℝ, 0≤C ∧ ∀ T, 0<T → ∀ u : ℝ,
      T*|β| *‖∫ x : ℝ, g x*phase (T*β) u x‖^2 ≤ (1+C/T)^2 := by
  let C := Real.pi / |β| * (∫ ξ : ℝ, ξ^2 * ‖(𝓕⁻ (hg.toSchwartzMap hgs) : 𝓢(ℝ,ℂ)) ξ‖)
  have hC : 0≤C := mul_nonneg (div_nonneg Real.pi_pos.le (abs_nonneg _))
    (integral_nonneg (fun ξ ↦ mul_nonneg (sq_nonneg _) (norm_nonneg _)))
  refine ⟨C,hC,?_⟩
  intro T hT u
  obtain ⟨E,hE,he⟩ := uniform_quadratic_integration g hg hgs hβ hT u
  change ‖E‖≤C/T at hE
  change (∫ x : ℝ, g x*phase (T*β) u x) = _ at he
  have hphase : ‖realPhase (2*Real.pi*(Real.sign β/8-u^2/(2*T*β)))‖ = 1 := by
    exact norm_realPhase _
  have hsqrt : 0<Real.sqrt (T*|β|) := Real.sqrt_pos.mpr (mul_pos hT (abs_pos.mpr hβ))
  have hn : ‖g (u/(T*β))+E‖≤1+C/T :=
    (norm_add_le _ _).trans (add_le_add (hg1 _) hE)
  have hnorm : ‖∫ x : ℝ, g x*phase (T*β) u x‖ =
      ‖g (u/(T*β))+E‖/Real.sqrt (T*|β|) := by
    rw [he,norm_mul,norm_div,hphase,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hsqrt]
    ring
  rw [hnorm,div_pow,Real.sq_sqrt (mul_pos hT (abs_pos.mpr hβ)).le]
  have hc : 0≤1+C/T := by positivity
  have hn2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
  calc
    _ = ‖g (u/(T*β))+E‖^2 := by field_simp
    _ ≤ _ := hn2

variable {I : Type uI} [Fintype I] [DecidableEq I]

def multiBox (B : ℝ) (β : I → ℝ) : Finset (I → ℤ) :=
  Fintype.piFinset (fun i ↦ box B (β i))

def determinant (β : I → ℝ) : ℝ := ∏ i, |β i|

omit [DecidableEq I] in
lemma determinant_pos {β : I → ℝ} (hβ : ∀ i, β i≠0) : 0<determinant β :=
  Finset.prod_pos (fun i _ ↦ abs_pos.mpr (hβ i))

lemma multiBox_card_bound {B : ℝ} (hB : 0<B) (β : I → ℝ) :
    ((multiBox B β).card : ℝ) ≤ B^(Fintype.card I) * ∏ i, (|β i|+1/B) := by
  rw [multiBox,Fintype.card_piFinset,Nat.cast_prod]
  calc
    _ ≤ ∏ i, (B*|β i|+1) := Finset.prod_le_prod (fun i _ ↦ Nat.cast_nonneg _)
      (fun i _ ↦ box_card_le hB.le _)
    _ = ∏ i, B*(|β i|+1/B) := by
      apply Finset.prod_congr rfl
      intro i _
      field_simp
    _ = _ := by rw [Finset.prod_mul_distrib]; simp

lemma multiBox_eventual_card {β : I → ℝ} (hβ : ∀ i, β i≠0)
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ B : ℝ in atTop, ((multiBox B β).card : ℝ) ≤
      (1+ε)*B^(Fintype.card I)*determinant β := by
  have hd := determinant_pos hβ
  have hi : Tendsto (fun B : ℝ ↦ 1/B) atTop (𝓝 0) := by
    simpa only [one_div] using tendsto_inv_atTop_zero
  have hp : Tendsto (fun B : ℝ ↦ ∏ i, (|β i|+1/B)) atTop (𝓝 (determinant β)) := by
    simpa only [add_zero,determinant] using tendsto_finsetProd Finset.univ
      (fun i _ ↦ tendsto_const_nhds.add hi)
  have hg : ∀ᶠ B : ℝ in atTop, (∏ i, (|β i|+1/B)) ≤ (1+ε)*determinant β :=
    (hp.eventually (eventually_lt_nhds (by nlinarith : determinant β < (1+ε)*determinant β))).mono (fun _ h ↦ h.le)
  filter_upwards [hg,eventually_gt_atTop (0:ℝ)] with B hb hB
  calc
    _ ≤ B^(Fintype.card I)*(∏ i, (|β i|+1/B)) := multiBox_card_bound hB β
    _ ≤ B^(Fintype.card I)*((1+ε)*determinant β) := mul_le_mul_of_nonneg_left hb (pow_nonneg hB.le _)
    _ = _ := by ring

omit [DecidableEq I] in

lemma tensor_coefficient_eventual {g : ℝ → ℂ} (hg : HasCompactSupport g)
    (hgs : ContDiff ℝ ∞ g) (hg1 : ∀ x, ‖g x‖≤1) {β : I → ℝ}
    (hβ : ∀ i, β i≠0) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ B : ℝ in atTop, ∀ u : I → ℤ,
      B^(Fintype.card I)*determinant β *
        ‖∏ i, (∫ x : ℝ, g x*phase (B*β i) (u i) x)‖^2 ≤ 1+ε := by
  choose C hC hc using (fun i ↦ quadratic_norm_scaled hg hgs hg1 (hβ i))
  have hi : Tendsto (fun B : ℝ ↦ 1/B) atTop (𝓝 0) := by
    simpa only [one_div] using tendsto_inv_atTop_zero
  have hp : Tendsto (fun B : ℝ ↦ ∏ i, (1+C i/B)^2) atTop (𝓝 1) := by
    have h (i : I) : Tendsto (fun B : ℝ ↦ (1+C i/B)^2) atTop (𝓝 1) := by
      have hci : Tendsto (fun B : ℝ ↦ C i/B) atTop (𝓝 0) := by
        simpa using (tendsto_const_nhds.div_atTop tendsto_id)
      simpa using ((tendsto_const_nhds (x := (1 : ℝ))).add hci).pow 2
    simpa using tendsto_finsetProd Finset.univ (fun i _ ↦ h i)
  have hp' : ∀ᶠ B : ℝ in atTop, (∏ i, (1+C i/B)^2) ≤ 1+ε :=
    (hp.eventually (eventually_lt_nhds (by linarith : (1:ℝ) < 1+ε))).mono (fun _ h ↦ h.le)
  filter_upwards [hp',eventually_gt_atTop (0:ℝ)] with B hb hB
  intro u
  calc
    _ = ∏ i, (B*|β i| *‖∫ x : ℝ, g x*phase (B*β i) (u i) x‖^2) := by
      rw [norm_prod,← Finset.prod_pow]
      simp only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,determinant]
    _ ≤ ∏ i, (1+C i/B)^2 := Finset.prod_le_prod
      (fun i _ ↦ mul_nonneg (mul_nonneg hB.le (abs_nonneg _)) (sq_nonneg _))
      (fun i _ ↦ hc i B hB (u i))
    _ ≤ _ := hb

lemma row_mass_le {g : ℝ → ℂ} (hgs : Continuous g) {α : ℝ}
    (hα : α<1/2) (hs : tsupport g ⊆ Set.Icc (-α) α) (T β : ℝ) :
    (∑ w ∈ box T β, ‖∫ x : ℝ, g x*phase (T*β) w x‖^2) ≤
      ∫ x : ℝ, ‖g x‖^2 := by
  let f : C(UnitAddCircle,ℂ) := ⟨circleChirp g (T*β),circleChirp_continuous hgs hα hs _⟩
  have hp := circle_parseval f
  have hb := hp.summable.sum_le_tsum (box T β) (fun w _ ↦ sq_nonneg _)
  rw [hp.tsum_eq] at hb
  change (∑ w ∈ box T β, ‖fourierCoeff (circleChirp g (T*β)) w‖^2) ≤
    ∫ z : UnitAddCircle, ‖circleChirp g (T*β) z‖^2 ∂AddCircle.haarAddCircle at hb
  simpa only [circleChirp_coefficient hα hs,circleChirp_mass hα hs] using hb

lemma row_mass_tendsto {g : ℝ → ℂ} (hg : HasCompactSupport g)
    (hgs : ContDiff ℝ ∞ g) (hg1 : ∀ x, ‖g x‖≤1) {α : ℝ}
    (hα0 : 0≤α) (hα : α<1/2) (hs : tsupport g ⊆ Set.Icc (-α) α)
    {β : ℝ} (hβ : β≠0) :
    Tendsto (fun T : ℝ ↦ ∑ w ∈ box T β,
      ‖∫ x : ℝ, g x*phase (T*β) w x‖^2) atTop (𝓝 (∫ x : ℝ, ‖g x‖^2)) := by
  obtain ⟨C,hC,h⟩ := row_mass_error hg hgs hg1 hα0 hα hs hβ
  have hi : Tendsto (fun T : ℝ ↦ C/T) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (by simpa using tendsto_const_nhds.sub hi) tendsto_const_nhds
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT using h T hT
  · exact Eventually.of_forall (fun T ↦ row_mass_le hgs.continuous hα hs T β)

lemma tensor_mass_tendsto {g : ℝ → ℂ} (hg : HasCompactSupport g)
    (hgs : ContDiff ℝ ∞ g) (hg1 : ∀ x, ‖g x‖≤1) {α : ℝ}
    (hα0 : 0≤α) (hα : α<1/2) (hs : tsupport g ⊆ Set.Icc (-α) α)
    {β : I → ℝ} (hβ : ∀ i, β i≠0) :
    Tendsto (fun B : ℝ ↦ ∑ u ∈ multiBox B β,
      ‖∏ i, (∫ x : ℝ, g x*phase (B*β i) (u i) x)‖^2)
      atTop (𝓝 ((∫ x : ℝ, ‖g x‖^2)^(Fintype.card I))) := by
  have he (B : ℝ) : (∑ u ∈ multiBox B β,
      ‖∏ i, (∫ x : ℝ, g x*phase (B*β i) (u i) x)‖^2) =
      ∏ i, (∑ w ∈ box B (β i), ‖∫ x : ℝ, g x*phase (B*β i) w x‖^2) := by
    simp only [norm_prod,← Finset.prod_pow,multiBox]
    exact (Finset.prod_univ_sum (fun i : I ↦ box B (β i))
      (fun (i : I) (w : ℤ) ↦ ‖∫ x : ℝ, g x*phase (B*β i) w x‖^2)).symm
  simp_rw [he]
  simpa using tendsto_finsetProd Finset.univ
    (fun i _ ↦ row_mass_tendsto hg hgs hg1 hα0 hα hs (hβ i))

omit [DecidableEq I] in
lemma tensor_uniform_error {g : ℝ → ℂ} (hg : HasCompactSupport g)
    (hgs : ContDiff ℝ ∞ g) (hg1 : ∀ x, ‖g x‖≤1) {α : ℝ}
    (hα0 : 0≤α) (hα : α<1/2) (hs : tsupport g ⊆ Set.Icc (-α) α)
    {β : I → ℝ} (hβ : ∀ i, β i≠0) :
    ∃ C : ℝ, 0≤C ∧ ∀ B : ℝ, 1≤B → ∀ z : I → UnitAddCircle,
      ‖(∏ i, rowTrunc g B (β i) (z i))-
        (∏ i, circleChirp g (B*β i) (z i))‖ ≤ C/B := by
  apply finite_product_error (I := I) (Z := I → UnitAddCircle) Finset.univ
    (fun (i : I) (B : ℝ) (z : I → UnitAddCircle) ↦ rowTrunc g B (β i) (z i))
    (fun (i : I) (B : ℝ) (z : I → UnitAddCircle) ↦ circleChirp g (B*β i) (z i))
  · intro i _ B z
    exact circleChirp_norm hg1 _ _
  · intro i _
    obtain ⟨C,hC,h⟩ := rowTrunc_error hg hgs hα0 hα hs (hβ i)
    exact ⟨C,hC,fun B hB z ↦ h B hB (z i)⟩

end
end Spreading
end AsymptoticallyMinimalLittlewood

namespace AsymptoticallyMinimalLittlewood
namespace Auxiliary
noncomputable section
open scoped BigOperators Topology ContDiff ComplexConjugate
open MeasureTheory Filter Finset UnitAddTorus Complex

lemma support_pair_sum {n : ℕ} (c : (Fin n → ℤ) →₀ ℂ)
    (S : Finset (Fin n → ℤ)) (hp : ∀ s ∈ S, positive n s)
    (hc : ∀ s, s ∈ c.support ↔ s ∈ S ∨ -s ∈ S)
    {E : Type uE} [AddCommMonoid E] (f : (Fin n → ℤ) → E) :
    ∑ s ∈ c.support, f s = ∑ s ∈ S, (f s+f (-s)) := by
  classical
  have hd : Disjoint S (S.image Neg.neg) := by
    rw [Finset.disjoint_left]
    intro s hs hn
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hn
    exact positive_not_neg (hp t ht) (hp _ hs)
  have he : c.support = S ∪ S.image Neg.neg := by
    ext s
    simpa only [Finset.mem_union, Finset.mem_image, neg_eq_iff_eq_neg,
      exists_eq_right] using hc s
  rw [he, Finset.sum_union hd, Finset.sum_image (by
    intro x _ y _ h; exact neg_injective h), Finset.sum_add_distrib]

lemma binary_positive_data {δ : ℝ} (hδ : 0<δ) (hδ1 : δ<1) :
    ∃ n : ℕ, ∃ S : Finset (Fin n → ℤ), S.Nonempty ∧
      (∀ s ∈ S, positive n s) ∧ ∃ c : (Fin n → ℤ) → ℂ,
      (∀ s ∈ S, c s≠0) ∧
      (∀ x : Fin n → UnitAddCircle,
        (binary n x : ℂ) = (∑ s ∈ S, c s*mFourier s x) +
          conj (∑ s ∈ S, c s*mFourier s x)) ∧
      1-δ ≤ 2*∑ s ∈ S, ‖c s‖^2 ∧ 2*∑ s ∈ S, ‖c s‖^2 ≤ 1 := by
  classical
  obtain ⟨n,hn,he⟩ := exists_binary_energy hδ
  obtain ⟨c,hp,hc⟩ := exists_binary_coefficients n
  obtain ⟨S,hS,hSp⟩ := coefficient_support_pairs c hp hc
  have hm : 2*∑ s ∈ S, ‖c s‖^2 = energy n := by
    rw [← binary_coefficients_energy c hc, support_pair_sum c S hS hSp]
    simp only [binary_coefficients_conj c hc, norm_conj]
    rw [Finset.sum_add_distrib]
    ring
  have hSn : S.Nonempty := by
    by_contra hz
    have hz' : S=∅ := Finset.not_nonempty_iff_eq_empty.mp hz
    rw [hz'] at hm
    simp only [Finset.sum_empty,mul_zero] at hm
    linarith
  refine ⟨n,S,hSn,hS,c,?_,?_,by linarith,by rw [hm]; exact (energy_bounds n).2⟩
  · intro s hs
    exact Finsupp.mem_support_iff.mp ((hSp s).mpr (Or.inl hs))
  · intro x
    rw [hc, support_pair_sum c S hS hSp, Finset.sum_add_distrib]
    congr 1
    simp only [map_sum,map_mul,binary_coefficients_conj c hc,mFourier_neg]

def rowForm {n : ℕ} (s : Fin n → ℤ) : (Fin n → ℝ) →ₗ[ℝ] ℝ :=
  ∑ k, (s k : ℝ) • LinearMap.proj k

lemma rowForm_apply {n : ℕ} (s : Fin n → ℤ) (x : Fin n → ℝ) :
    rowForm s x = ∑ k, (s k : ℝ)*x k := by simp [rowForm]

lemma rowForm_injective {n : ℕ} : Function.Injective (@rowForm n) := by
  classical
  intro s t h
  ext k
  have hh := congrArg (fun f : (Fin n → ℝ) →ₗ[ℝ] ℝ ↦ f (Pi.single k 1)) h
  simp [rowForm_apply, Pi.single_apply, mul_ite] at hh
  exact_mod_cast hh

lemma positive_rowForm_ne_zero {n : ℕ} {s : Fin n → ℤ} (hs : positive n s) :
    rowForm s ≠ 0 := by
  intro hz
  apply primitive_ne_zero (positive_primitive hs)
  apply rowForm_injective
  simpa [rowForm] using hz

lemma positive_rowForm_nonparallel {n : ℕ} {s t : Fin n → ℤ}
    (hs : positive n s) (ht : positive n t) (hne : s ≠ t) (c : ℝ) :
    rowForm s ≠ c • rowForm t := by
  classical
  intro he
  apply hne
  apply (positive_parallel_eq hs ht (c := c) ?_).1
  intro k
  have hh := congrArg (fun f : (Fin n → ℝ) →ₗ[ℝ] ℝ ↦ f (Pi.single k 1)) he
  simpa [rowForm_apply, Pi.single_apply, mul_ite] using hh

end
end Auxiliary
end AsymptoticallyMinimalLittlewood

namespace AsymptoticallyMinimalLittlewood.Auxiliary
noncomputable section
open scoped BigOperators Topology ContDiff ComplexConjugate
open MeasureTheory Filter Finset UnitAddTorus Complex QuadraticTail Spreading

lemma mFourier_norm_apply {J : Type uJ} [Fintype J] (s : J → ℤ)
    (x : J → UnitAddCircle) : ‖mFourier s x‖=1 := by
  simp only [mFourier, ContinuousMap.coe_mk, norm_prod, fourier_apply, Circle.norm_coe, Finset.prod_const_one]

lemma mFourier_add_point {J : Type uJ} [Fintype J] (s : J → ℤ)
    (x y : J → UnitAddCircle) : mFourier s (x+y)=mFourier s x*mFourier s y := by
  simp only [mFourier, ContinuousMap.coe_mk,Pi.add_apply,fourier_apply,
    zsmul_add,AddCircle.toCircle_add,Circle.coe_mul,Finset.prod_mul_distrib]

lemma mFourier_real {J : Type uJ} [Fintype J] (s : J → ℤ) (x : J → ℝ) :
    mFourier s (fun j ↦ (x j : UnitAddCircle)) =
      Complex.exp (Complex.I*(2*Real.pi*(∑ j, (s j : ℝ)*x j) : ℝ)) := by
  simp only [mFourier,ContinuousMap.coe_mk,fourier_coe_apply,Complex.ofReal_one,div_one]
  rw [← Complex.exp_sum]
  congr 1
  simp only [Complex.ofReal_mul,Complex.ofReal_sum,Complex.ofReal_intCast,Complex.ofReal_ofNat,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma phase_tensor_character {n : ℕ} {J : Type uJ} [Fintype J]
    (s : Fin n → ℤ) (b : J → Fin n → ℝ) (B : ℝ) (z : J → ℝ) :
    (∏ j, phase (B*rowForm s (b j)) 0 (z j)) =
      mFourier s (fun k ↦ ((B/2*∑ j, b j k*z j^2 : ℝ) : UnitAddCircle)) := by
  rw [mFourier_real]
  simp only [phase,sub_zero,zero_mul,← Complex.exp_sum]
  congr 1
  simp only [Complex.ofReal_mul,Complex.ofReal_sum,Complex.ofReal_div,
    Complex.ofReal_ofNat,Complex.ofReal_pow,rowForm_apply]
  push_cast
  simp only [Finset.mul_sum,Finset.sum_mul,Finset.sum_div]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma spread_half_bound {n : ℕ} {J : Type uJ} [Fintype J]
    (S : Finset (Fin n → ℤ)) (c : (Fin n → ℤ) → ℂ)
    (hc : ∀ y : Fin n → UnitAddCircle,
      (binary n y : ℂ) = (∑ s ∈ S, c s*mFourier s y)+
        conj (∑ s ∈ S, c s*mFourier s y))
    (g : ℝ → ℝ) (hg : ∀ x, 0≤g x ∧ g x≤1)
    (b : J → Fin n → ℝ) (B : ℝ) (y : Fin n → UnitAddCircle)
    (z : J → UnitAddCircle) :
    ‖(∑ s∈S, c s*mFourier s y*∏ j, circleChirp (fun x ↦ (g x : ℂ))
      (B*rowForm s (b j)) (z j)) +
      conj (∑ s∈S, c s*mFourier s y*∏ j, circleChirp (fun x ↦ (g x : ℂ))
      (B*rowForm s (b j)) (z j))‖ ≤ 1 := by
  let x : J → ℝ := fun j ↦ AddCircle.equivIoc 1 (-1/2) (z j)
  let u : Fin n → UnitAddCircle := fun k ↦ ((B/2*∑ j, b j k*x j^2 : ℝ) : UnitAddCircle)
  let A : ℝ := ∏ j, g (x j)
  have hA0 : 0≤A := Finset.prod_nonneg (fun j _ ↦ (hg _).1)
  have hA1 : A≤1 := Finset.prod_le_one (fun j _ ↦ (hg _).1) (fun j _ ↦ (hg _).2)
  have he : (∑ s∈S, c s*mFourier s y*∏ j, circleChirp (fun x ↦ (g x : ℂ))
      (B*rowForm s (b j)) (z j)) = (A : ℂ)*∑ s∈S, c s*mFourier s (y+u) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    have hp : (∏ j, circleChirp (fun x ↦ (g x : ℂ)) (B*rowForm s (b j)) (z j)) =
        (A : ℂ)*mFourier s u := by
      change (∏ j, (g (x j) : ℂ)*phase (B*rowForm s (b j)) 0 (x j)) = _
      rw [Finset.prod_mul_distrib,phase_tensor_character]
      simp only [A,Complex.ofReal_prod,u]
    rw [hp,mFourier_add_point]
    ring
  rw [he,map_mul,conj_ofReal,← mul_add,← hc]
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hA0,
    Complex.norm_real,Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left (binary_abs_le n _) hA0).trans (by simpa using hA1)

end
end AsymptoticallyMinimalLittlewood.Auxiliary

namespace AsymptoticallyMinimalLittlewood.Auxiliary
noncomputable section
open scoped BigOperators Topology ContDiff ComplexConjugate
open MeasureTheory Filter Finset UnitAddTorus Complex QuadraticTail Spreading

lemma tensor_trunc_expand {J : Type uJ} [Fintype J] [DecidableEq J]
    (g : ℝ → ℂ) (B : ℝ) (β : J → ℝ) (z : J → UnitAddCircle) :
    (∏ j, rowTrunc g B (β j) (z j)) =
      ∑ u∈multiBox B β, (∏ j, ∫ x : ℝ, g x*phase (B*β j) (u j) x)*mFourier u z := by
  classical
  simp only [rowTrunc,multiBox,mFourier,ContinuousMap.coe_mk,← Finset.prod_mul_distrib]
  exact Finset.prod_univ_sum _ _

lemma cutoff_power {D : ℕ} {δ : ℝ} (hδ : 0<δ) (hδ1 : δ<1) :
    ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧
      (∃ α : ℝ, 0<α ∧ α<1/2 ∧ tsupport g ⊆ Set.Icc (-α) α) ∧
      (∀ x, 0≤g x ∧ g x≤1) ∧
      1-δ < (∫ x : ℝ, g x^2)^D := by
  have hD : (0:ℝ)<D+1 := by positivity
  let ε : ℝ := δ/(D+1)
  have hε : 0<ε := div_pos hδ hD
  have hε1 : ε<1 := by dsimp [ε]; rw [div_lt_one hD]; have : (0:ℝ)≤D := Nat.cast_nonneg _; linarith
  obtain ⟨g,hgs,hgc,hga,hg,hm⟩ := Cutoff.unit_cutoff hε
  refine ⟨g,hgs,hgc,hga,hg,?_⟩
  have hb := one_add_mul_le_pow (a := -ε) (by linarith : (-2:ℝ)≤-ε) D
  have hp : (1-ε)^D ≤ (∫ x : ℝ, g x^2)^D := pow_le_pow_left₀ (by linarith) hm.le _
  have hi : (D : ℝ)*ε<δ := by dsimp [ε]; rw [← mul_div_assoc, div_lt_iff₀ hD]; nlinarith
  have hh : 1-δ < 1+(D:ℝ)*(-ε) := by linarith
  exact hh.trans_le (hb.trans (by simpa only [sub_eq_add_neg] using hp))

lemma spread_trunc_eventual_bound {n : ℕ} {J : Type uJ} [Fintype J] [DecidableEq J]
    (S : Finset (Fin n → ℤ)) (c : (Fin n → ℤ) → ℂ)
    (hc : ∀ y : Fin n → UnitAddCircle,
      (binary n y : ℂ) = (∑ s∈S, c s*mFourier s y)+conj (∑ s∈S, c s*mFourier s y))
    {g : ℝ → ℝ} (hgs : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (hg : ∀ x, 0≤g x ∧ g x≤1) {α : ℝ} (hα0 : 0≤α) (hα : α<1/2)
    (hga : tsupport g ⊆ Set.Icc (-α) α)
    (b : J → Fin n → ℝ) (hb : ∀ s∈S, ∀ j, rowForm s (b j)≠0)
    {δ : ℝ} (hδ : 0<δ) :
    ∀ᶠ B : ℝ in atTop, ∀ y : Fin n → UnitAddCircle, ∀ z : J → UnitAddCircle,
      ‖(∑ s∈S, c s*mFourier s y*∏ j, rowTrunc (fun x ↦ (g x : ℂ)) B (rowForm s (b j)) (z j))+
        conj (∑ s∈S, c s*mFourier s y*∏ j, rowTrunc (fun x ↦ (g x : ℂ)) B (rowForm s (b j)) (z j))‖ ≤ 1+δ := by
  classical
  have hsupp : tsupport (fun x ↦ (g x : ℂ)) = tsupport g := by
    unfold tsupport
    apply congrArg closure
    ext x
    change ((g x : ℂ)≠0) ↔ g x≠0
    exact Complex.ofReal_ne_zero
  have hgc' : HasCompactSupport (fun x ↦ (g x : ℂ)) := by simpa only [HasCompactSupport,hsupp] using hgc
  have hgs' : ContDiff ℝ ∞ (fun x ↦ (g x : ℂ)) := Complex.ofRealCLM.contDiff.comp hgs
  have hg' : ∀ x, ‖(g x : ℂ)‖≤1 := by intro x; simpa [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hg x).1] using (hg x).2
  have hga' : tsupport (fun x ↦ (g x : ℂ)) ⊆ Set.Icc (-α) α := by
    simpa only [hsupp] using hga
  have hh (s : S) : ∃ C : ℝ, 0≤C ∧ ∀ B : ℝ, 1≤B → ∀ z : J → UnitAddCircle,
      ‖(∏ j, rowTrunc (fun x ↦ (g x : ℂ)) B (rowForm s.val (b j)) (z j))-
        (∏ j, circleChirp (fun x ↦ (g x : ℂ)) (B*rowForm s.val (b j)) (z j))‖≤C/B :=
    tensor_uniform_error hgc' hgs' hg' hα0 hα hga' (hb s.val s.property)
  choose C hC hE using hh
  let A : ℝ := ∑ s : S, ‖c s.val‖*C s
  have hlim : Tendsto (fun B : ℝ ↦ 2*A/B) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  filter_upwards [hlim.eventually (eventually_lt_nhds hδ),eventually_ge_atTop (1:ℝ)] with B hBδ hB
  intro y z
  let T : ℂ := ∑ s∈S, c s*mFourier s y*∏ j, rowTrunc (fun x ↦ (g x : ℂ)) B (rowForm s (b j)) (z j)
  let G : ℂ := ∑ s∈S, c s*mFourier s y*∏ j, circleChirp (fun x ↦ (g x : ℂ)) (B*rowForm s (b j)) (z j)
  have hTG : ‖T-G‖≤A/B := by
    dsimp [T,G]
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ s∈S, ‖c s*mFourier s y*((∏ j, rowTrunc (fun x ↦ (g x : ℂ)) B (rowForm s (b j)) (z j))-
        (∏ j, circleChirp (fun x ↦ (g x : ℂ)) (B*rowForm s (b j)) (z j)))‖ := by
          simp only [mul_sub]; exact norm_sum_le _ _
      _ = ∑ s : S, ‖c s.val‖*‖(∏ j, rowTrunc (fun x ↦ (g x : ℂ)) B (rowForm s.val (b j)) (z j))-
        (∏ j, circleChirp (fun x ↦ (g x : ℂ)) (B*rowForm s.val (b j)) (z j))‖ := by
          simp only [norm_mul,mFourier_norm_apply,mul_one]
          exact (Finset.sum_attach _ _).symm
      _ ≤ ∑ s : S, ‖c s.val‖*(C s/B) := Finset.sum_le_sum (fun s _ ↦ mul_le_mul_of_nonneg_left (hE s B hB z) (norm_nonneg _))
      _ = A/B := by simp only [A,mul_div_assoc,Finset.sum_div]
  have hm := spread_half_bound S c hc g hg b B y z
  change ‖G+conj G‖≤1 at hm
  change ‖T+conj T‖≤1+δ
  have hd : ‖(T+conj T)-(G+conj G)‖≤2*(A/B) := by
    calc
      _ = ‖(T-G)+conj (T-G)‖ := by congr 1; simp only [map_sub]; ring
      _ ≤ ‖T-G‖+‖conj (T-G)‖ := norm_add_le _ _
      _ ≤ 2*(A/B) := by rw [norm_conj]; linarith
  have ht := norm_add_le ((T+conj T)-(G+conj G)) (G+conj G)
  rw [sub_add_cancel] at ht
  have he : 2*(A/B)=2*A/B := by ring
  rw [he] at hd
  linarith

end
end AsymptoticallyMinimalLittlewood.Auxiliary

namespace AsymptoticallyMinimalLittlewood.Auxiliary
noncomputable section
open scoped BigOperators Topology ContDiff ComplexConjugate
open MeasureTheory Filter Finset UnitAddTorus Complex QuadraticTail Spreading

structure RawData (I J : Type) [Fintype I] [Fintype J] (δ : ℝ) where
  frequency : I → J → ℤ
  coefficient : I → ℂ
  velocity : J → ℝ
  nonzero : ∀ i, frequency i ≠ 0
  nonparallel : ∀ i i', i≠i' → ∀ t : ℝ,
    ¬∀ j, (frequency i j : ℝ)=t*(frequency i' j : ℝ)
  bounded : ∀ y : J → UnitAddCircle,
    ‖(∑ i, coefficient i*mFourier (frequency i) y)+
      conj (∑ i, coefficient i*mFourier (frequency i) y)‖≤1
  energy : (1-3*δ)^2 ≤ 2*∑ i, ‖coefficient i‖^2
  curvature : ∀ i, (∑ j, (frequency i j : ℝ)*velocity j)≠0
  width : 2*∑ i, |∑ j, (frequency i j : ℝ)*velocity j| < 1
  size : ∀ i, ‖coefficient i‖^2 ≤ ((1+δ)^3/(1-δ))*
    |∑ j, (frequency i j : ℝ)*velocity j|

structure FinitePacket (δ : ℝ) where
  I : Type
  J : Type
  fintypeI : Fintype I
  fintypeJ : Fintype J
  nonemptyI : Nonempty I
  data : @RawData I J fintypeI fintypeJ δ

instance {δ : ℝ} (p : FinitePacket δ) : Fintype p.I := p.fintypeI
instance {δ : ℝ} (p : FinitePacket δ) : Fintype p.J := p.fintypeJ
instance {δ : ℝ} (p : FinitePacket δ) : Nonempty p.I := p.nonemptyI

lemma mFourier_sum_type {J : Type uJ} {K : Type uK} [Fintype J] [Fintype K]
    (s : J → ℤ) (u : K → ℤ) (x : J ⊕ K → UnitAddCircle) :
    mFourier (Sum.elim s u) x = mFourier s (x ∘ Sum.inl)*mFourier u (x ∘ Sum.inr) := by
  simp only [mFourier,ContinuousMap.coe_mk,Fintype.prod_sum_type,Sum.elim_inl,
    Sum.elim_inr,Function.comp_apply]

lemma spread_numeric_coefficient {δ τ P Δ ρ U V : ℝ}
    (hδ : 0<δ) (hδ1 : δ<1) (hτ : 0<τ) (hP : 0<P) (hρ : 0<ρ)
    (_hU : 0≤U) (hV : 0≤V)
    (hdet : (1-δ)*τ*U/ρ ≤ Δ) (hdisc : P*Δ*V≤(1+δ)^2) :
    U*V/(1+δ)^2 ≤ ((1+δ)^3/(1-δ))*(ρ/(τ*P*(1+δ)^3)) := by
  have hd0 : 0<1-δ := sub_pos.mpr hδ1
  have hd1 : 0<1+δ := by linarith
  have hd2 := mul_le_mul_of_nonneg_right hdet (mul_nonneg hP.le hV)
  have hd3 := mul_le_mul_of_nonneg_left hdisc hρ.le
  have he : ((1-δ)*τ*U/ρ)*(P*V)*ρ=(1-δ)*τ*P*(U*V) := by field_simp
  have hd4 := mul_le_mul_of_nonneg_right hd2 hρ.le
  rw [he] at hd4
  have hraw : (1-δ)*τ*P*(U*V)≤ρ*(1+δ)^2 := by nlinarith only [hd3,hd4]
  have hr : ((1+δ)^3/(1-δ))*(ρ/(τ*P*(1+δ)^3))=ρ/((1-δ)*τ*P) := by
    field_simp
  rw [hr]
  apply (div_le_div_iff₀ (sq_pos_of_pos hd1) (by positivity)).mpr
  nlinarith only [hraw]

lemma spread_numeric_width {δ τ P Δ ρ U L : ℝ}
    (hδ : 0<δ) (hτ : 0<τ) (hP : 0<P) (hρ : 0<ρ)
    (hdet : Δ ≤ (1+δ)*τ*U/ρ) (hcard : L≤(1+δ)*P*Δ) :
    L*(ρ/(τ*P*(1+δ)^3))≤U/(1+δ) := by
  have hd1 : 0<1+δ := by linarith
  have h1 := mul_le_mul_of_nonneg_left hdet (mul_nonneg hd1.le hP.le)
  have h2 := mul_le_mul_of_nonneg_right (hcard.trans h1) hρ.le
  have he : (1+δ)*P*((1+δ)*τ*U/ρ)*ρ=τ*P*(1+δ)^2*U := by field_simp
  rw [he] at h2
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ (by positivity) hd1).mpr
  have hh := mul_le_mul_of_nonneg_right h2 hd1.le
  nlinarith only [hh]

lemma spread_numeric_energy {δ : ℝ} (hδ : 0<δ) (hδ1 : δ<1/20) :
    (1-3*δ)^2 ≤ ((1-δ)*(1-2*δ))/(1+δ)^2 := by
  have h1 : 0≤1-3*δ := by linarith
  have h2 : 0≤1-2*δ := by linarith
  have hd : 0<1+δ := by linarith
  apply (le_div_iff₀ (sq_pos_of_pos hd)).mpr
  have hh : (1-3*δ)*(1+δ)≤1-2*δ := by nlinarith [sq_nonneg δ]
  have hsq : ((1-3*δ)*(1+δ))^2≤(1-2*δ)^2 := sq_le_sq₀ (mul_nonneg h1 hd.le) h2 |>.mpr hh
  nlinarith [mul_nonneg hδ.le h2]

end
end AsymptoticallyMinimalLittlewood.Auxiliary

namespace AsymptoticallyMinimalLittlewood.Auxiliary
noncomputable section
open scoped BigOperators Topology ContDiff ComplexConjugate
open MeasureTheory Filter Finset UnitAddTorus Complex QuadraticTail Spreading

/-- The full Fourier-spreading construction, before adjoining a harmless zero
coefficient to ensure that the packing catalogue has at least two rows. -/
theorem exists_auxiliary_packet {δ : ℝ} (hδ : 0<δ) (hδ20 : δ<1/20) :
    Nonempty (FinitePacket δ) := by
  classical
  have hδ1 : δ<1 := by linarith
  have hd : 0<1+δ := by linarith
  obtain ⟨n,S,hSn,hS,c,hc,hpoly,hElo,hEhi⟩ := binary_positive_data hδ hδ1
  let I := ↥S
  have : Nonempty I := ⟨⟨hSn.choose,hSn.choose_spec⟩⟩
  let f : I → (Fin n → ℝ) →ₗ[ℝ] ℝ := fun i ↦ rowForm i.val
  have hf (i : I) : f i≠0 := positive_rowForm_ne_zero (hS i.val i.property)
  have hfp (i j : I) (hij : i≠j) (t : ℝ) : f i≠t • f j :=
    positive_rowForm_nonparallel (hS i.val i.property) (hS j.val j.property)
      (fun h ↦ hij (Subtype.ext h)) t
  obtain ⟨γ,hγ⟩ := Curvature.exists_generic f hf
  let ρ : I → ℝ := fun i ↦ |f i γ|
  have hρ (i : I) : 0<ρ i := abs_pos.mpr (hγ i)
  have hc0 (i : I) : 0<‖c i.val‖^2 := sq_pos_of_pos (norm_pos_iff.mpr (hc i.val i.property))
  obtain ⟨τ,hτ,b,hb,hdet⟩ := Curvature.determinant_tuning f hf hfp
    (fun i ↦ ‖c i.val‖^2/ρ i) (fun i ↦ div_pos (hc0 i) (hρ i)) hδ hδ1
  let β : I → I → ℝ := fun i j ↦ f i (b j)
  have hβ (i j : I) : β i j≠0 := hb i j
  obtain ⟨g,hgs,hgc,⟨α,hα0,hα,hga⟩,hg,hgm⟩ := cutoff_power (D := Fintype.card I) hδ hδ1
  let g' : ℝ → ℂ := fun x ↦ (g x : ℂ)
  have hgs' : ContDiff ℝ ∞ g' := Complex.ofRealCLM.contDiff.comp hgs
  have hgc' : HasCompactSupport g' := hgc.comp_left (g := (Complex.ofReal : ℝ → ℂ)) (by simp)
  have hg' : ∀ x, ‖g' x‖≤1 := by
    intro x
    simpa [g',Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hg x).1] using (hg x).2
  have hga' : tsupport g' ⊆ Set.Icc (-α) α :=
    (tsupport_comp_subset (g := (Complex.ofReal : ℝ → ℂ)) (by simp) g).trans hga
  have hm' : 1-δ < (∫ x : ℝ, ‖g' x‖^2)^(Fintype.card I) := by
    simpa only [g',Complex.norm_real,Real.norm_eq_abs,sq_abs] using hgm
  have hcards : ∀ᶠ B : ℝ in atTop, ∀ i : I,
      ((multiBox B (β i)).card : ℝ)≤(1+δ)*B^(Fintype.card I)*determinant (β i) := by
    rw [Filter.eventually_all]
    exact fun i ↦ multiBox_eventual_card (hβ i) hδ
  have hε : 0<(1+δ)^2-1 := by nlinarith
  have hcoeffs : ∀ᶠ B : ℝ in atTop, ∀ i : I, ∀ u : I → ℤ,
      B^(Fintype.card I)*determinant (β i)*
        ‖∏ j, (∫ x : ℝ, g' x*phase (B*β i j) (u j) x)‖^2 ≤ (1+δ)^2 := by
    rw [Filter.eventually_all]
    intro i
    simpa only [add_sub_cancel] using tensor_coefficient_eventual hgc' hgs' hg' (hβ i) hε
  have hmasses : ∀ᶠ B : ℝ in atTop, ∀ i : I,
      1-2*δ ≤ ∑ u∈multiBox B (β i), ‖∏ j, (∫ x : ℝ, g' x*phase (B*β i j) (u j) x)‖^2 := by
    rw [Filter.eventually_all]
    intro i
    exact ((tensor_mass_tendsto hgc' hgs' hg' hα0.le hα hga' (hβ i)).eventually
      (eventually_gt_nhds (by linarith : 1-2*δ<(∫ x : ℝ, ‖g' x‖^2)^(Fintype.card I)))).mono (fun _ h ↦ h.le)
  have hbound := spread_trunc_eventual_bound S c hpoly hgs hgc hg hα0.le hα hga b
    (by intro s hs j; exact hb ⟨s,hs⟩ j) hδ
  obtain ⟨B,hBc,hBs,hBm,hBd,hB⟩ :=
    (hcards.and (hcoeffs.and (hmasses.and (hbound.and (eventually_ge_atTop (1:ℝ)))))).exists
  have hB0 : 0<B := lt_of_lt_of_le zero_lt_one hB
  let U (i : I) := multiBox B (β i)
  let Q := (i : I) × ↥(U i)
  let J := Fin n ⊕ I
  let A : Q → J → ℤ := fun q ↦ Sum.elim q.1.val q.2.val
  let T (i : I) (u : I → ℤ) : ℂ := ∏ j, (∫ x : ℝ, g' x*phase (B*β i j) (u j) x)
  let C : Q → ℂ := fun q ↦ c q.1.val*T q.1 q.2.val/(1+δ : ℂ)
  let P : ℝ := B^(Fintype.card I)
  have hP : 0<P := pow_pos hB0 _
  let den : ℝ := τ*P*(1+δ)^3
  have hden : 0<den := by dsimp [den]; positivity
  let v : J → ℝ := Sum.elim (fun k ↦ γ k/den) (fun _ ↦ 0)
  have hcurv (q : Q) : (∑ j, (A q j : ℝ)*v j)=f q.1 γ/den := by
    simp only [J,A,v,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,mul_zero,
      Finset.sum_const_zero,add_zero,← mul_div_assoc,← Finset.sum_div]
    simp only [f,rowForm_apply]
  have hwidth (q : Q) : |∑ j, (A q j : ℝ)*v j|=ρ q.1/den := by
    rw [hcurv,abs_div,abs_of_pos hden]
  have hC (q : Q) : ‖C q‖^2=‖c q.1.val‖^2*‖T q.1 q.2.val‖^2/(1+δ)^2 := by
    dsimp [C]
    rw [norm_div,norm_mul,div_pow,mul_pow]
    norm_cast
    rw [Real.norm_eq_abs,abs_of_pos hd]
  have hsum : (∑ q : Q, ‖C q‖^2)=
      (∑ i : I, ‖c i.val‖^2*(∑ u∈U i, ‖T i u‖^2))/(1+δ)^2 := by
    simp only [Q,Fintype.sum_sigma,hC]
    simp only [← Finset.sum_div,← Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    exact (Finset.sum_subtype (U i) (fun _ ↦ Iff.rfl) (fun u ↦ ‖T i u‖^2)).symm
  have hElo' : 1-δ≤2*∑ i : I, ‖c i.val‖^2 := by
    simpa only [← Finset.sum_coe_sort S] using hElo
  have hEhi' : 2*∑ i : I, ‖c i.val‖^2≤1 := by
    simpa only [← Finset.sum_coe_sort S] using hEhi
  have helo : (1-3*δ)^2≤2*∑ q : Q, ‖C q‖^2 := by
    have h2 : 0≤1-2*δ := by linarith
    have hterm : (∑ i : I, ‖c i.val‖^2)*(1-2*δ)≤∑ i : I, ‖c i.val‖^2*(∑ u∈U i, ‖T i u‖^2) := by
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (hBm i) (sq_nonneg _)
    have he := mul_le_mul_of_nonneg_right hElo' h2
    rw [hsum]
    apply (spread_numeric_energy hδ hδ20).trans
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right (by nlinarith only [hterm,he]) (sq_nonneg _)
  have hwterm (i : I) : ((U i).card : ℝ)*(ρ i/den)≤‖c i.val‖^2/(1+δ) := by
    apply spread_numeric_width hδ hτ hP (hρ i)
    · simpa only [determinant,β,mul_div_assoc] using (hdet i).2
    · exact hBc i
  have hwsum : 2*(∑ q : Q, |∑ j, (A q j : ℝ)*v j|)≤1/(1+δ) := by
    simp only [hwidth,Q,Fintype.sum_sigma,Finset.sum_const,Finset.card_univ,
      nsmul_eq_mul,Fintype.card_coe]
    calc
      _ ≤ 2*(∑ i : I, ‖c i.val‖^2/(1+δ)) := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ ↦ hwterm i)) (by norm_num)
      _ = (2*∑ i : I, ‖c i.val‖^2)/(1+δ) := by rw [← Finset.sum_div]; ring
      _ ≤ 1/(1+δ) := div_le_div_of_nonneg_right hEhi' hd.le
  have hsup (y : J → UnitAddCircle) :
      ‖(∑ q : Q, C q*mFourier (A q) y)+conj (∑ q : Q, C q*mFourier (A q) y)‖≤1 := by
    let Z : ℂ := ∑ s∈S, c s*mFourier s (y ∘ Sum.inl)*
      ∏ j : I, rowTrunc g' B (rowForm s (b j)) (y (Sum.inr j))
    have hZ : ‖Z+conj Z‖≤1+δ := hBd (y ∘ Sum.inl) (y ∘ Sum.inr)
    have he : (∑ q : Q, C q*mFourier (A q) y)=Z/(1+δ : ℂ) := by
      rw [Fintype.sum_sigma]
      have hi (i : I) : (∑ u : U i, C ⟨i,u⟩*mFourier (A ⟨i,u⟩) y)=
          (c i.val*mFourier i.val (y ∘ Sum.inl)*(∏ j : I, rowTrunc g' B (β i j) (y (Sum.inr j))))/(1+δ : ℂ) := by
        rw [tensor_trunc_expand]
        change (∑ u : U i, (c i.val*T i u.val/(1+δ : ℂ))*mFourier (Sum.elim i.val u.val) y)=_
        simp only [mFourier_sum_type,Finset.mul_sum,Finset.sum_div]
        rw [← Finset.sum_coe_sort (U i)]
        apply Finset.sum_congr rfl
        intro u _
        dsimp [T, Function.comp_def]
        ring
      simp_rw [hi]
      rw [← Finset.sum_div]
      congr 1
      simpa only [Z,β,f] using Finset.sum_coe_sort S
        (fun s ↦ c s*mFourier s (y ∘ Sum.inl)*∏ j : I, rowTrunc g' B (rowForm s (b j)) (y (Sum.inr j)))
    rw [he,map_div₀,map_add,map_one,conj_ofReal,← add_div,norm_div]
    have he' : ‖(1:ℂ)+(δ:ℂ)‖=1+δ := by
      rw [← Complex.ofReal_one,← Complex.ofReal_add,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hd]
    rw [he',div_le_one hd]
    exact hZ
  have hQ : Nonempty Q := by
    let i : I := Classical.choice inferInstance
    have hu : (0 : I → ℤ)∈U i := by
      simp only [U,multiBox,Fintype.mem_piFinset,Pi.zero_apply,mem_box,Int.cast_zero,abs_zero]
      intro j
      positivity
    exact ⟨⟨i,⟨0,hu⟩⟩⟩
  refine ⟨⟨Q,J,inferInstance,inferInstance,hQ,⟨A,C,v,?_,?_,hsup,helo,?_,?_,?_⟩⟩⟩
  · intro q hz
    apply primitive_ne_zero (positive_primitive (hS q.1.val q.1.property))
    funext k
    exact congrFun hz (Sum.inl k)
  · rintro ⟨s,u⟩ ⟨t,w⟩ hne a ha
    have hh := positive_parallel_eq (hS s.val s.property) (hS t.val t.property)
      (fun k ↦ ha (Sum.inl k))
    have hst : s=t := Subtype.ext hh.1
    subst t
    have huw : u=w := by
      apply Subtype.ext
      funext j
      have hj := ha (Sum.inr j)
      change (u.val j : ℝ)=a*(w.val j : ℝ) at hj
      rw [hh.2,one_mul] at hj
      exact_mod_cast hj
    exact hne (by rw [huw])
  · intro q
    rw [hcurv]
    exact div_ne_zero (hγ q.1) hden.ne'
  · apply hwsum.trans_lt
    exact (div_lt_one hd).mpr (by linarith)
  · intro q
    rw [hC,hwidth]
    apply spread_numeric_coefficient hδ hδ1 hτ hP (hρ q.1) (sq_nonneg _) (sq_nonneg _)
    · simpa only [determinant,β,mul_div_assoc] using (hdet q.1).1
    · exact hBs q.1 q.2.val

end
end AsymptoticallyMinimalLittlewood.Auxiliary

end OAI



namespace OAI

universe uE uI

namespace AsymptoticallyMinimalLittlewood
namespace Nibble
open scoped BigOperators
open Finset

section ProductSpace
variable {E : Type uE} [Fintype E] [DecidableEq E]

def coinWeight (p : ℝ) (s : E → Bool) : ℝ :=
  ∏ e, if s e then p else 1 - p

def expectation (p : ℝ) (f : (E → Bool) → ℝ) : ℝ :=
  ∑ s, coinWeight p s * f s

def noHit (A : Finset E) (s : E → Bool) : ℝ :=
  ∏ e ∈ A, if s e then 0 else 1

lemma expectation_prod (p : ℝ) (g : E → Bool → ℝ) :
    expectation p (fun s ↦ ∏ e, g e (s e)) =
      ∏ e, (p * g e true + (1 - p) * g e false) := by
  dsimp [expectation, coinWeight]
  simp only [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun e b ↦ (if b then p else 1 - p) * g e b)]
  simp

lemma coinWeight_sum (p : ℝ) : (∑ s : E → Bool, coinWeight p s) = 1 := by
  have h := expectation_prod (E := E) p (fun _ _ ↦ 1)
  simpa [expectation] using h

omit [DecidableEq E] in
lemma coinWeight_nonneg {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (s : E → Bool) :
    0 ≤ coinWeight p s := by
  apply Finset.prod_nonneg
  intro e he
  split_ifs <;> linarith

lemma expectation_const (p c : ℝ) : expectation (E := E) p (fun _ ↦ c) = c := by
  simp only [expectation, ← Finset.sum_mul, coinWeight_sum, one_mul]

lemma expectation_add (p : ℝ) (f g : (E → Bool) → ℝ) :
    expectation p (fun s ↦ f s + g s) = expectation p f + expectation p g := by
  simp [expectation, mul_add, Finset.sum_add_distrib]

lemma expectation_sub (p : ℝ) (f g : (E → Bool) → ℝ) :
    expectation p (fun s ↦ f s - g s) = expectation p f - expectation p g := by
  simp [expectation, mul_sub, Finset.sum_sub_distrib]

lemma expectation_mul_const (p : ℝ) (f : (E → Bool) → ℝ) (c : ℝ) :
    expectation p (fun s ↦ f s * c) = expectation p f * c := by
  simp [expectation, ← mul_assoc, Finset.sum_mul]

lemma expectation_const_mul (p c : ℝ) (f : (E → Bool) → ℝ) :
    expectation p (fun s ↦ c * f s) = c * expectation p f := by
  simpa only [mul_comm c] using expectation_mul_const p f c

lemma expectation_sum {I : Type uI} (p : ℝ) (S : Finset I) (f : I → (E → Bool) → ℝ) :
    expectation p (fun s ↦ ∑ i ∈ S, f i s) = ∑ i ∈ S, expectation p (f i) := by
  simp only [expectation, Finset.mul_sum]
  exact Finset.sum_comm

lemma expectation_mono {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    {f g : (E → Bool) → ℝ} (h : ∀ s, f s ≤ g s) : expectation p f ≤ expectation p g := by
  exact Finset.sum_le_sum fun s _ ↦ mul_le_mul_of_nonneg_left (h s) (coinWeight_nonneg hp hp1 s)

lemma expectation_nonneg {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    {f : (E → Bool) → ℝ} (hf : ∀ s, 0 ≤ f s) : 0 ≤ expectation p f := by
  simpa only [expectation_const] using expectation_mono hp hp1 hf

lemma exists_le_expectation {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (f : (E → Bool) → ℝ) : ∃ s, f s ≤ expectation p f := by
  by_contra h
  push Not at h
  have hh : expectation (E := E) p (fun _ ↦ expectation p f) < expectation p f := by
    apply Finset.sum_lt_sum
    · intro s hs
      exact mul_le_mul_of_nonneg_left (h s).le (coinWeight_nonneg hp hp1 s)
    · have hex : ∃ s : E → Bool, 0 < coinWeight p s := by
        by_contra hn
        push Not at hn
        have hz : (∑ s : E → Bool, coinWeight p s) ≤ 0 := Finset.sum_nonpos fun s _ ↦ hn s
        rw [coinWeight_sum] at hz
        linarith
      obtain ⟨s, hs⟩ := hex
      exact ⟨s, Finset.mem_univ s, mul_lt_mul_of_pos_left (h s) hs⟩
  rw [expectation_const] at hh
  exact (lt_irrefl _ hh)

lemma noHit_eq (A : Finset E) (s : E → Bool) :
    noHit A s = if ∀ e ∈ A, s e = false then 1 else 0 := by
  dsimp [noHit]
  split_ifs with h
  · apply Finset.prod_eq_one
    intro e he
    simp [h e he]
  · push Not at h
    obtain ⟨e, he, hs⟩ := h
    apply Finset.prod_eq_zero he
    cases hh : s e <;> simp_all

lemma noHit_nonneg (A : Finset E) (s : E → Bool) : 0 ≤ noHit A s := by
  rw [noHit_eq]
  split_ifs <;> norm_num

lemma noHit_le_one (A : Finset E) (s : E → Bool) : noHit A s ≤ 1 := by
  rw [noHit_eq]
  split_ifs <;> norm_num

lemma noHit_union (A B : Finset E) (s : E → Bool) :
    noHit (A ∪ B) s = noHit A s * noHit B s := by
  simp only [noHit_eq, Finset.mem_union, or_imp, forall_and]
  split_ifs <;> simp_all

lemma expectation_noHit (p : ℝ) (A : Finset E) :
    expectation p (noHit A) = (1 - p) ^ A.card := by
  have heq (s : E → Bool) : noHit A s =
      ∏ e : E, if e ∈ A then (if s e then (0 : ℝ) else 1) else 1 := by
    rw [Finset.prod_ite_mem]
    simp [noHit]
  change expectation p (fun s ↦ noHit A s) = _
  simp_rw [heq]
  rw [expectation_prod p (fun e b ↦ if e ∈ A then (if b then (0 : ℝ) else 1) else 1)]
  calc
    _ = ∏ e : E, if e ∈ A then 1 - p else 1 := by
      apply Finset.prod_congr rfl
      intro e he
      by_cases h : e ∈ A <;> simp [h]
    _ = _ := by rw [Finset.prod_ite_mem]; simp

lemma one_sub_pow_le {p : ℝ} (_hp : 0 ≤ p) (hp1 : p ≤ 1) (n : ℕ) :
    1 - (1 - p) ^ n ≤ n * p := by
  have h := one_add_mul_le_pow (by linarith : -2 ≤ -p) n
  simp only [← sub_eq_add_neg] at h
  linarith

lemma noHit_covariance_le {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (A B : Finset E) :
    expectation p (fun s ↦ noHit A s * noHit B s) -
      expectation p (noHit A) * expectation p (noHit B) ≤ p * (A ∩ B).card := by
  simp_rw [← noHit_union, expectation_noHit]
  rw [← pow_add]
  have hc := Finset.card_union_add_card_inter A B
  rw [← hc, pow_add]
  have hq : 0 ≤ 1 - p := by linarith
  have hq1 : 1 - p ≤ 1 := by linarith
  have hpow : (1 - p) ^ (A ∪ B).card ≤ 1 := pow_le_one₀ hq hq1
  have hdec : 0 ≤ 1 - (1 - p) ^ (A ∩ B).card := by
    linarith [pow_le_one₀ hq hq1 (n := (A ∩ B).card)]
  have hmul := mul_le_mul_of_nonneg_right hpow hdec
  have hh := one_sub_pow_le hp hp1 (A ∩ B).card
  nlinarith

/-- The second-moment estimate used for every residual degree. Each test set
has size at most L and each independent edge-bit occurs in at most K tests. -/
lemma noHit_sum_variance {I : Type uI} [DecidableEq I] {p : ℝ}
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (S : Finset I) (A : I → Finset E)
    {K L : ℝ} (hK0 : 0 ≤ K) (hL : ∀ i ∈ S, ((A i).card : ℝ) ≤ L)
    (hK : ∀ e, ((S.filter fun i ↦ e ∈ A i).card : ℝ) ≤ K) :
    let Y : (E → Bool) → ℝ := fun s ↦ ∑ i ∈ S, noHit (A i) s
    expectation p (fun s ↦ (Y s - expectation p Y) ^ 2) ≤
      p * S.card * L * K := by
  classical
  dsimp only
  let Y : (E → Bool) → ℝ := fun s ↦ ∑ i ∈ S, noHit (A i) s
  change expectation p (fun s ↦ (Y s - expectation p Y) ^ 2) ≤ _
  have hid : expectation p (fun s ↦ (Y s - expectation p Y) ^ 2) =
      expectation p (fun s ↦ Y s ^ 2) - expectation p Y ^ 2 := by
    simp_rw [sub_sq]
    rw [expectation_add, expectation_sub, expectation_const,
      expectation_mul_const, expectation_const_mul]
    ring
  rw [hid]
  have hsq (s : E → Bool) : Y s ^ 2 = ∑ i ∈ S, ∑ j ∈ S, noHit (A i) s * noHit (A j) s := by
    dsimp [Y]
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
  simp_rw [hsq, expectation_sum]
  have hmean : expectation p Y ^ 2 =
      ∑ i ∈ S, ∑ j ∈ S, expectation p (noHit (A i)) * expectation p (noHit (A j)) := by
    dsimp [Y]
    rw [expectation_sum, pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
  rw [hmean, ← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i ∈ S, ∑ j ∈ S, p * ((A i ∩ A j).card : ℝ) :=
      Finset.sum_le_sum fun i hi ↦ Finset.sum_le_sum fun j hj ↦ noHit_covariance_le hp hp1 _ _
    _ ≤ ∑ i ∈ S, p * (L * K) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [← Finset.mul_sum]
      apply mul_le_mul_of_nonneg_left _ hp
      have hid' : (∑ j ∈ S, (A i ∩ A j).card) =
          ∑ e ∈ A i, (S.filter fun j ↦ e ∈ A j).card := by
        simp only [← Finset.filter_mem_eq_inter, Finset.card_eq_sum_ones, Finset.sum_filter]
        rw [Finset.sum_comm]
      have hb : (∑ j ∈ S, ((A i ∩ A j).card : ℝ)) ≤ L * K := by
        have hcast : (∑ j ∈ S, ((A i ∩ A j).card : ℝ)) =
            ∑ e ∈ A i, ((S.filter fun j ↦ e ∈ A j).card : ℝ) := by exact_mod_cast hid'
        rw [hcast]
        calc
          _ ≤ ∑ _e ∈ A i, K := Finset.sum_le_sum fun e _ ↦ hK e
          _ = (A i).card * K := by simp
          _ ≤ _ := mul_le_mul_of_nonneg_right (hL i hi) hK0
      exact hb
    _ = _ := by simp; ring

lemma pow_bonferroni {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (n : ℕ) :
    (1 - p) ^ n - (1 - n * p) ≤ (n * p) ^ 2 / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hl := one_sub_pow_le hp hp1 n
    have hstep := mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr hp1)
    have he := mul_nonneg hp (sq_nonneg ((n : ℝ) * p))
    rw [pow_succ]
    push_cast
    nlinarith [sq_nonneg p]

lemma markov_indicator {p t : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (_ht : 0 ≤ t)
    (f : (E → Bool) → ℝ) (hf : ∀ s, 0 ≤ f s) :
    t * expectation p (fun s ↦ if t < f s then 1 else 0) ≤ expectation p f := by
  rw [← expectation_const_mul]
  apply expectation_mono hp hp1
  intro s
  split_ifs with h <;> simp_all
  exact h.le

lemma chebyshev_indicator {p t : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (ht : 0 ≤ t)
    (f : (E → Bool) → ℝ) :
    t ^ 2 * expectation p (fun s ↦ if t < |f s - expectation p f| then 1 else 0) ≤
      expectation p (fun s ↦ (f s - expectation p f) ^ 2) := by
  rw [← expectation_const_mul]
  apply expectation_mono hp hp1
  intro s
  split_ifs with h
  · simp only [mul_one]
    nlinarith [sq_abs (f s - expectation p f)]
  · simp only [mul_zero]
    positivity

lemma exists_of_three_bad_bounds {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (P Q R : (E → Bool) → Prop) [DecidablePred P] [DecidablePred Q] [DecidablePred R]
    (hP : expectation p (fun s ↦ if P s then 1 else 0) ≤ 1 / 4)
    (hQ : expectation p (fun s ↦ if Q s then 1 else 0) ≤ 1 / 4)
    (hR : expectation p (fun s ↦ if R s then 1 else 0) ≤ 1 / 4) :
    ∃ s, ¬ P s ∧ ¬ Q s ∧ ¬ R s := by
  obtain ⟨s, hs⟩ := exists_le_expectation hp hp1 (fun s ↦
    (if P s then (1 : ℝ) else 0) + (if Q s then 1 else 0) + (if R s then 1 else 0))
  rw [expectation_add, expectation_add] at hs
  refine ⟨s, ?_, ?_, ?_⟩ <;> intro h
  all_goals split_ifs at hs <;> linarith

lemma noHit_mean_error {I : Type uI} {p M B L : ℝ}
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hL : 0 ≤ L)
    (S : Finset I) (A : I → Finset E)
    (hcard : ∀ i ∈ S, |((A i).card : ℝ) - M| ≤ B)
    (hupper : ∀ i ∈ S, ((A i).card : ℝ) ≤ L) :
    |expectation p (fun s ↦ ∑ i ∈ S, noHit (A i) s) - S.card * (1 - p * M)| ≤
      S.card * (p * B + (p * L)^2 / 2) := by
  rw [expectation_sum]
  have hc : (S.card : ℝ) * (1 - p * M) = ∑ _i ∈ S, (1 - p * M) := by simp; ring
  rw [hc, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i ∈ S, |expectation p (noHit (A i)) - (1 - p * M)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ S, (p * B + (p * L)^2/2) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [expectation_noHit]
      have hbon := pow_bonferroni hp hp1 (A i).card
      have hlo := one_sub_pow_le hp hp1 (A i).card
      have herr := hcard i hi
      have hbound := hupper i hi
      have hpv : 0 ≤ ((A i).card : ℝ) * p := mul_nonneg (Nat.cast_nonneg _) hp
      have hpl : ((A i).card : ℝ) * p ≤ L * p := mul_le_mul_of_nonneg_right hbound hp
      have hsq : (((A i).card : ℝ) * p)^2 ≤ (L*p)^2 := sq_le_sq₀ hpv (mul_nonneg hL hp) |>.mpr hpl
      have hm := mul_le_mul_of_nonneg_left (abs_le.mp herr).1 hp
      have hM := mul_le_mul_of_nonneg_left (abs_le.mp herr).2 hp
      apply abs_le.mpr
      constructor <;> nlinarith [sq_nonneg (p*L)]
    _ = _ := by simp; ring

/-- A Bernoulli indicator, for counting selected edges. -/
def selectedIndicator (e : E) (s : E → Bool) : ℝ := if s e then 1 else 0

omit [Fintype E] [DecidableEq E] in
lemma selectedIndicator_eq (e : E) (s : E → Bool) :
    selectedIndicator e s = 1 - noHit {e} s := by
  cases h : s e <;> simp [selectedIndicator, noHit, h]

omit [Fintype E] [DecidableEq E] in
lemma selectedIndicator_nonneg (e : E) (s : E → Bool) : 0 ≤ selectedIndicator e s := by
  dsimp [selectedIndicator]
  split_ifs <;> norm_num

lemma expectation_selected (p : ℝ) (e : E) : expectation p (selectedIndicator e) = p := by
  change expectation p (fun s ↦ selectedIndicator e s) = _
  simp_rw [selectedIndicator_eq]
  rw [expectation_sub, expectation_const, expectation_noHit]
  simp

lemma expectation_selected_mul (p : ℝ) (e f : E) (hef : e ≠ f) :
    expectation p (fun s ↦ selectedIndicator e s * selectedIndicator f s) = p^2 := by
  have heq (s : E → Bool) : selectedIndicator e s * selectedIndicator f s =
      1 - noHit {e} s - noHit {f} s + noHit ({e} ∪ {f}) s := by
    rw [noHit_union, selectedIndicator_eq, selectedIndicator_eq]
    ring
  simp_rw [heq]
  rw [expectation_add, expectation_sub, expectation_sub, expectation_const]
  simp only [expectation_noHit, Finset.card_singleton, pow_one]
  have hcard : ({e} ∪ {f} : Finset E).card = 2 := by simp [hef]
  rw [hcard]
  ring

/-- Simultaneous second-moment control of many local tests, one global test,
and a nonnegative collision count. No randomness remains in the conclusion. -/
lemma exists_controlled_outcome {I : Type uI} [DecidableEq I] {p : ℝ}
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (U : Finset I)
    (Y : I → (E → Bool) → ℝ) (Z W : (E → Bool) → ℝ)
    {V Vz M t b u c : ℝ} (ht : 0 < t) (hb : 0 < b) (hu : 0 < u) (hc : 0 < c)
    (hY : ∀ i ∈ U, expectation p (fun s ↦ (Y i s - expectation p (Y i))^2) ≤ V)
    (hZ : expectation p (fun s ↦ (Z s - expectation p Z)^2) ≤ Vz)
    (hW0 : ∀ s, 0 ≤ W s) (hW : expectation p W ≤ M)
    (hV : 4 * U.card * V ≤ t^2*b) (hVz : 4*Vz ≤ u^2) (hM : 4*M ≤ c) :
    ∃ s, (((U.filter fun i ↦ t < |Y i s - expectation p (Y i)|).card : ℝ) ≤ b) ∧
      |Z s - expectation p Z| ≤ u ∧ W s ≤ c := by
  classical
  let B : (E → Bool) → ℝ := fun s ↦
    ((U.filter fun i ↦ t < |Y i s - expectation p (Y i)|).card : ℝ)
  have hB0 (s : E → Bool) : 0 ≤ B s := Nat.cast_nonneg _
  have hB : t^2 * expectation p B ≤ U.card*V := by
    have heq : B = fun s ↦ ∑ i ∈ U, if t < |Y i s - expectation p (Y i)| then (1 : ℝ) else 0 := by
      funext s
      simp only [B, Finset.card_eq_sum_ones, Finset.sum_filter, Nat.cast_sum,
        Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    rw [heq, expectation_sum, Finset.mul_sum]
    calc
      _ ≤ ∑ _i ∈ U, V := Finset.sum_le_sum fun i hi ↦
        (chebyshev_indicator hp hp1 ht.le (Y i)).trans (hY i hi)
      _ = _ := by simp
  have hP : expectation p (fun s ↦ if b < B s then 1 else 0) ≤ 1/4 := by
    have hm := markov_indicator hp hp1 hb.le B hB0
    have he := mul_le_mul_of_nonneg_left hm (sq_nonneg t)
    have hpos : 0 < t^2*b := mul_pos (sq_pos_of_pos ht) hb
    nlinarith
  have hQ : expectation p (fun s ↦ if u < |Z s - expectation p Z| then 1 else 0) ≤ 1/4 := by
    have hh := (chebyshev_indicator hp hp1 hu.le Z).trans hZ
    have hpos := sq_pos_of_pos hu
    nlinarith
  have hR : expectation p (fun s ↦ if c < W s then 1 else 0) ≤ 1/4 := by
    have hh := (markov_indicator hp hp1 hc.le W hW0).trans hW
    nlinarith
  obtain ⟨s, hsP, hsQ, hsR⟩ := exists_of_three_bad_bounds hp hp1
    (fun s ↦ b < B s) (fun s ↦ u < |Z s - expectation p Z|) (fun s ↦ c < W s)
    hP hQ hR
  exact ⟨s, le_of_not_gt hsP, le_of_not_gt hsQ, le_of_not_gt hsR⟩

end ProductSpace

end Nibble
end AsymptoticallyMinimalLittlewood

end OAI



namespace OAI

universe uI uE uV

namespace AsymptoticallyMinimalLittlewood
namespace Nibble
open scoped BigOperators
open Finset
section SetUnions
variable {I : Type uI} {E : Type uE} [DecidableEq I] [DecidableEq E]

omit [DecidableEq I] in
lemma card_biUnion_upper (S : Finset I) (A : I → Finset E) {D : ℝ}
    (hD : ∀ i ∈ S, ((A i).card : ℝ) ≤ D) :
    ((S.biUnion A).card : ℝ) ≤ S.card * D := by
  calc
    _ ≤ ∑ i ∈ S, ((A i).card : ℝ) := by exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ S, D := Finset.sum_le_sum hD
    _ = _ := by simp

lemma card_biUnion_lower (S : Finset I) (A : I → Finset E) {C : ℝ} (hC : 0 ≤ C)
    (hpair : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → ((A i ∩ A j).card : ℝ) ≤ C) :
    (∑ i ∈ S, ((A i).card : ℝ)) ≤ ((S.biUnion A).card : ℝ) + (S.card : ℝ) ^ 2 * C := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    have hiS : ∀ j ∈ S, ((A i ∩ A j).card : ℝ) ≤ C := fun j hj ↦
      hpair i (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj)
        (by intro h; subst j; contradiction)
    have hh := card_biUnion_upper S (fun j ↦ A i ∩ A j) hiS
    rw [← Finset.inter_biUnion] at hh
    have hcard := Finset.card_union_add_card_inter (A i) (S.biUnion A)
    have hcard' : ((A i ∪ S.biUnion A).card : ℝ) + (A i ∩ S.biUnion A).card =
        (A i).card + (S.biUnion A).card := by exact_mod_cast hcard
    have hind := ih (fun j hj k hk hjk ↦
      hpair j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk) hjk)
    rw [Finset.sum_insert hi, Finset.biUnion_insert, Finset.card_insert_of_notMem hi]
    push_cast
    nlinarith [show (0 : ℝ) ≤ S.card from Nat.cast_nonneg _]

end SetUnions

section Hypergraph
variable {V : Type uV} {E : Type uE} [DecidableEq V] [Fintype E] [DecidableEq E]

def incident (S : Finset E) (A : E → Finset V) (v : V) : Finset E :=
  S.filter fun e ↦ v ∈ A e

def hits (S : Finset E) (A : E → Finset V) (W : Finset V) : Finset E :=
  W.biUnion (incident S A)

omit [Fintype E] [DecidableEq E] in
@[simp] lemma mem_incident (S : Finset E) (A : E → Finset V) (v : V) (e : E) :
    e ∈ incident S A v ↔ e ∈ S ∧ v ∈ A e := by simp [incident]

omit [Fintype E] in
@[simp] lemma mem_hits (S : Finset E) (A : E → Finset V) (W : Finset V) (e : E) :
    e ∈ hits S A W ↔ e ∈ S ∧ ∃ v ∈ W, v ∈ A e := by
  simp only [hits, Finset.mem_biUnion, mem_incident]
  aesop

omit [Fintype E] in
lemma hits_card_upper (S : Finset E) (A : E → Finset V) (W : Finset V) {D : ℝ}
    (hD : ∀ v ∈ W, ((incident S A v).card : ℝ) ≤ D) :
    ((hits S A W).card : ℝ) ≤ W.card * D := card_biUnion_upper W _ hD

omit [Fintype E] in
lemma hits_card_deviation (S : Finset E) (A : E → Finset V) (W : Finset V)
    {D e C : ℝ} (hC : 0 ≤ C)
    (hD : ∀ v ∈ W, |((incident S A v).card : ℝ) - D| ≤ e)
    (hpair : ∀ v ∈ W, ∀ w ∈ W, v ≠ w →
      ((incident S A v ∩ incident S A w).card : ℝ) ≤ C) :
    |((hits S A W).card : ℝ) - W.card * D| ≤ W.card * e + (W.card : ℝ) ^ 2 * C := by
  have hupper := hits_card_upper S A W (D := D + e) (fun v hv ↦ by
    have := (abs_le.mp (hD v hv)).2
    linarith)
  have hlower := card_biUnion_lower W (incident S A) hC hpair
  have hsum : W.card * (D - e) ≤ ∑ v ∈ W, ((incident S A v).card : ℝ) := by
    calc
      _ = ∑ _v ∈ W, (D - e) := by simp; ring
      _ ≤ _ := Finset.sum_le_sum fun v hv ↦ by have := (abs_le.mp (hD v hv)).1; linarith
  change (∑ v ∈ W, ((incident S A v).card : ℝ)) ≤
    ((hits S A W).card : ℝ) + (W.card : ℝ)^2 * C at hlower
  apply abs_le.mpr
  constructor <;> nlinarith [mul_nonneg (sq_nonneg (W.card : ℝ)) hC]

omit [Fintype E] in
lemma residual_test_frequency (S : Finset E) (A : E → Finset V) (v : V) (f : E) :
    ((incident S A v).filter fun e ↦ f ∈ hits S A ((A e).erase v)) =
      if f ∈ S then ((A f).erase v).biUnion (fun w ↦ incident S A v ∩ incident S A w) else ∅ := by
  ext e
  simp only [Finset.mem_filter, mem_incident, mem_hits, Finset.mem_erase,
    ]
  split_ifs <;> simp_all ; aesop

/-- Codegrees control the influence of each edge-bit on a residual degree. -/
lemma residual_degree_variance (U : Finset V) (S : Finset E) (A : E → Finset V)
    {r : ℕ} {D C p : ℝ} (hD : 0 ≤ D) (hC : 0 ≤ C)
    (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hsub : ∀ e ∈ S, A e ⊆ U) (hr : ∀ e ∈ S, (A e).card ≤ r)
    (hdeg : ∀ v ∈ U, ((incident S A v).card : ℝ) ≤ D)
    (hcodeg : ∀ v ∈ U, ∀ w ∈ U, v ≠ w →
      ((incident S A v ∩ incident S A w).card : ℝ) ≤ C)
    (v : V) (hv : v ∈ U) :
    let Y : (E → Bool) → ℝ := fun s ↦
      ∑ e ∈ incident S A v, noHit (hits S A ((A e).erase v)) s
    expectation p (fun s ↦ (Y s - expectation p Y)^2) ≤ p * (r : ℝ)^2 * D^2 * C := by
  classical
  let T := fun e ↦ hits S A ((A e).erase v)
  have hL : ∀ e ∈ incident S A v, ((T e).card : ℝ) ≤ r * D := by
    intro e he
    obtain ⟨heS, hve⟩ := mem_incident S A v e |>.mp he
    apply (hits_card_upper S A ((A e).erase v) (fun w hw ↦
      hdeg w (hsub e heS (Finset.mem_of_mem_erase hw)))).trans
    apply mul_le_mul_of_nonneg_right _ hD
    exact_mod_cast (Finset.card_erase_le.trans (hr e heS))
  have hK : ∀ f, (((incident S A v).filter fun e ↦ f ∈ T e).card : ℝ) ≤ r * C := by
    intro f
    dsimp [T]
    rw [residual_test_frequency]
    split_ifs with hf
    · apply (card_biUnion_upper ((A f).erase v) (fun w ↦ incident S A v ∩ incident S A w)
        (fun w hw ↦ hcodeg v hv w (hsub f hf (Finset.mem_of_mem_erase hw))
          (Ne.symm (Finset.mem_erase.mp hw).1))).trans
      apply mul_le_mul_of_nonneg_right _ hC
      exact_mod_cast (Finset.card_erase_le.trans (hr f hf))
    · simp only [Finset.card_empty, Nat.cast_zero]
      positivity
  have hb := noHit_sum_variance hp hp1 (incident S A v) T (by positivity : 0 ≤ (r : ℝ)*C) hL hK
  apply hb.trans
  have hd := hdeg v hv
  have hm := mul_le_mul_of_nonneg_right hd (show 0 ≤ p * (r : ℝ)^2 * D * C by positivity)
  nlinarith

/-- Count the vertices missed by the selected edges. -/
def untouched (U : Finset V) (S : Finset E) (A : E → Finset V) (s : E → Bool) : Finset V :=
  U.filter fun v ↦ ∀ e ∈ incident S A v, s e = false

lemma untouched_card (U : Finset V) (S : Finset E) (A : E → Finset V) (s : E → Bool) :
    ((untouched U S A s).card : ℝ) = ∑ v ∈ U, noHit (incident S A v) s := by
  simp only [untouched, Finset.card_eq_sum_ones, Finset.sum_filter, noHit_eq,
    Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

lemma untouched_variance (U : Finset V) (S : Finset E) (A : E → Finset V)
    {r : ℕ} {D p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : ∀ e ∈ S, (A e).card ≤ r)
    (hdeg : ∀ v ∈ U, ((incident S A v).card : ℝ) ≤ D) :
    let Y : (E → Bool) → ℝ := fun s ↦ ((untouched U S A s).card : ℝ)
    expectation p (fun s ↦ (Y s - expectation p Y)^2) ≤ p * U.card * D * r := by
  dsimp only
  simp_rw [untouched_card]
  apply noHit_sum_variance hp hp1 U (incident S A) (Nat.cast_nonneg r) hdeg
  intro e
  by_cases he : e ∈ S
  · have hsub : (U.filter fun v ↦ e ∈ incident S A v) ⊆ A e := by
      intro v hv
      exact (mem_incident S A v e |>.mp (Finset.mem_filter.mp hv).2).2
    exact_mod_cast (Finset.card_le_card hsub).trans (hr e he)
  · have hz : (U.filter fun v ↦ e ∈ incident S A v) = ∅ := by
      ext v
      simp [he]
    rw [hz]
    simp

lemma untouched_mean_upper (U : Finset V) (S : Finset E) (A : E → Finset V)
    {D Emax p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (hE : 0 ≤ Emax)
    (hdeg : ∀ v ∈ U, D ≤ ((incident S A v).card : ℝ) ∧
      ((incident S A v).card : ℝ) ≤ Emax) :
    expectation p (fun s ↦ ((untouched U S A s).card : ℝ)) ≤
      U.card * (1 - p * D + (p * Emax)^2 / 2) := by
  simp_rw [untouched_card]
  rw [expectation_sum]
  calc
    _ ≤ ∑ _v ∈ U, (1 - p * D + (p * Emax)^2 / 2) := by
      apply Finset.sum_le_sum
      intro v hv
      rw [expectation_noHit]
      have hb := pow_bonferroni hp hp1 (incident S A v).card
      have hd := mul_le_mul_of_nonneg_left (hdeg v hv).1 hp
      have hu := mul_le_mul_of_nonneg_left (hdeg v hv).2 hp
      have hs : (p * ((incident S A v).card : ℝ))^2 ≤ (p*Emax)^2 :=
        (sq_le_sq₀ (by positivity) (mul_nonneg hp hE)).mpr hu
      nlinarith
    _ = _ := by simp; ring

lemma residual_degree_mean (U : Finset V) (S : Finset E) (A : E → Finset V)
    {r : ℕ} (hr0 : 1 ≤ r) {D ε C p : ℝ} (hD : 0 ≤ D) (he : 0 ≤ ε) (hC : 0 ≤ C)
    (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hsub : ∀ e ∈ S, A e ⊆ U) (hr : ∀ e ∈ S, (A e).card = r)
    (hdeg : ∀ v ∈ U, |((incident S A v).card : ℝ) - D| ≤ ε)
    (hcodeg : ∀ v ∈ U, ∀ w ∈ U, v ≠ w →
      ((incident S A v ∩ incident S A w).card : ℝ) ≤ C)
    (v : V) (_hv : v ∈ U) :
    |expectation p (fun s ↦ ∑ e ∈ incident S A v, noHit (hits S A ((A e).erase v)) s) -
      (incident S A v).card * (1 - p * ((r-1 : ℕ) : ℝ) * D)| ≤
      (incident S A v).card * (p * ((r : ℝ)*ε + (r : ℝ)^2*C) +
        (p * ((r : ℝ)*(D+ε)))^2/2) := by
  have htcard (e : E) (heS : e ∈ incident S A v) : ((A e).erase v).card = r-1 := by
    rw [Finset.card_erase_of_mem (mem_incident S A v e |>.mp heS).2, hr e
      (mem_incident S A v e |>.mp heS).1]
  have hrle : ((r-1 : ℕ) : ℝ) ≤ (r : ℝ) := by exact_mod_cast Nat.sub_le r 1
  have hcard : ∀ e ∈ incident S A v,
      |((hits S A ((A e).erase v)).card : ℝ) - ((r-1 : ℕ) : ℝ)*D| ≤
        (r : ℝ)*ε + (r : ℝ)^2*C := by
    intro e heS
    have hsube : ∀ w ∈ (A e).erase v, w ∈ U := fun w hw ↦
      hsub e (mem_incident S A v e |>.mp heS).1 (Finset.mem_of_mem_erase hw)
    have hb := hits_card_deviation S A ((A e).erase v) hC
      (fun w hw ↦ hdeg w (hsube w hw))
      (fun w hw z hz hwz ↦ hcodeg w (hsube w hw) z (hsube z hz) hwz)
    rw [htcard e heS] at hb
    apply hb.trans
    exact add_le_add (mul_le_mul_of_nonneg_right hrle he)
      (mul_le_mul_of_nonneg_right ((sq_le_sq₀ (Nat.cast_nonneg _) (Nat.cast_nonneg _)).mpr hrle) hC)
  have hupper : ∀ e ∈ incident S A v,
      ((hits S A ((A e).erase v)).card : ℝ) ≤ (r : ℝ)*(D+ε) := by
    intro e heS
    apply (hits_card_upper S A ((A e).erase v) (D := D+ε) ?_).trans
    · rw [htcard e heS]
      exact mul_le_mul_of_nonneg_right hrle (add_nonneg hD he)
    · intro w hw
      have hh := (abs_le.mp (hdeg w (hsub e (mem_incident S A v e |>.mp heS).1
        (Finset.mem_of_mem_erase hw)))).2
      linarith
  simpa only [mul_assoc] using noHit_mean_error hp hp1
    (by positivity : 0 ≤ (r : ℝ)*(D+ε)) (incident S A v)
    (fun e ↦ hits S A ((A e).erase v)) hcard hupper

/-- Edges remaining after a vertex deletion. -/
def restrictEdges (S : Finset E) (A : E → Finset V) (W : Finset V) : Finset E :=
  S.filter fun e ↦ A e ⊆ W

omit [Fintype E] [DecidableEq E] in
lemma incident_restrict (S : Finset E) (A : E → Finset V) (W : Finset V) (v : V) :
    incident (restrictEdges S A W) A v = (incident S A v).filter fun e ↦ A e ⊆ W := by
  ext e
  simp [incident, restrictEdges, and_left_comm, and_comm]

lemma residual_degree_eq (U : Finset V) (S : Finset E) (A : E → Finset V)
    (hsub : ∀ e ∈ S, A e ⊆ U) (s : E → Bool) (v : V) (hv : v ∈ untouched U S A s) :
    ((incident (restrictEdges S A (untouched U S A s)) A v).card : ℝ) =
      ∑ e ∈ incident S A v, noHit (hits S A ((A e).erase v)) s := by
  have hvs : ∀ e ∈ incident S A v, s e = false := (Finset.mem_filter.mp hv).2
  rw [incident_restrict]
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Nat.cast_sum, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero, noHit_eq]
  apply Finset.sum_congr rfl
  intro e he
  congr 1
  apply propext
  constructor
  · intro hW f hf
    obtain ⟨hfS, w, hw, hwe⟩ := mem_hits S A ((A e).erase v) f |>.mp hf
    exact (Finset.mem_filter.mp (hW (Finset.mem_of_mem_erase hw))).2 f
      (mem_incident S A w f |>.mpr ⟨hfS, hwe⟩)
  · intro hN w hw
    apply Finset.mem_filter.mpr
    refine ⟨hsub e (mem_incident S A v e |>.mp he).1 hw, ?_⟩
    intro f hf
    by_cases hwv : w = v
    · exact hvs f (hwv ▸ hf)
    · exact hN f (mem_hits S A ((A e).erase v) f |>.mpr
        ⟨(mem_incident S A w f |>.mp hf).1, w, Finset.mem_erase.mpr ⟨hwv, hw⟩,
          (mem_incident S A w f |>.mp hf).2⟩)

omit [Fintype E] in
lemma degree_loss_deleting (U B : Finset V) (S : Finset E) (A : E → Finset V)
    {C : ℝ} (_hC : 0 ≤ C) (hsub : ∀ e ∈ S, A e ⊆ U)
    (v : V) (hc : ∀ w ∈ B, v ≠ w → ((incident S A v ∩ incident S A w).card : ℝ) ≤ C)
    (hv : v ∉ B) :
    ((incident S A v).card : ℝ) - B.card*C ≤
      ((incident (restrictEdges S A (U \ B)) A v).card : ℝ) := by
  classical
  have hd : incident S A v \ incident (restrictEdges S A (U \ B)) A v ⊆
      B.biUnion (fun w ↦ incident S A v ∩ incident S A w) := by
    intro e he
    obtain ⟨he, hn⟩ := Finset.mem_sdiff.mp he
    have hin := mem_incident S A v e |>.mp he
    have hnon : ¬ A e ⊆ U \ B := by
      intro h
      apply hn
      rw [incident_restrict]
      exact Finset.mem_filter.mpr ⟨he, h⟩
    obtain ⟨w, hw, hwB⟩ := Finset.not_subset.mp hnon
    have hwB' : w ∈ B := by simpa [Finset.mem_sdiff, hsub e hin.1 hw] using hwB
    exact Finset.mem_biUnion.mpr ⟨w, hwB', Finset.mem_inter.mpr
      ⟨he, mem_incident S A w e |>.mpr ⟨hin.1, hw⟩⟩⟩
  have hb := (show (((incident S A v \ incident (restrictEdges S A (U \ B)) A v).card) : ℝ) ≤
      (B.biUnion (fun w ↦ incident S A v ∩ incident S A w)).card from
        Nat.cast_le.mpr (Finset.card_le_card hd)).trans
    (card_biUnion_upper B _ (fun w hw ↦ hc w hw (fun h ↦ hv (h ▸ hw))))
  have hcard := Finset.card_le_card_sdiff_add_card (s := incident S A v)
    (t := incident (restrictEdges S A (U \ B)) A v)
  have hcard' : ((incident S A v).card : ℝ) ≤
    (incident S A v \ incident (restrictEdges S A (U \ B)) A v).card +
      (incident (restrictEdges S A (U \ B)) A v).card := by exact_mod_cast hcard
  linarith

/-- The selected edges that meet no other selected edge. -/
def isolated (S : Finset E) (A : E → Finset V) (s : E → Bool) : Finset E :=
  S.filter fun e ↦ s e = true ∧ ∀ f ∈ S, f ≠ e → s f = true → Disjoint (A e) (A f)

def colliding (S : Finset E) (A : E → Finset V) (s : E → Bool) : Finset E :=
  S.filter fun e ↦ s e = true ∧ ∃ f ∈ S, f ≠ e ∧ s f = true ∧ ¬ Disjoint (A e) (A f)

def collisionCount (U : Finset V) (S : Finset E) (A : E → Finset V) (s : E → Bool) : ℝ :=
  ∑ v ∈ U, ∑ e ∈ incident S A v, ∑ f ∈ (incident S A v).erase e,
    selectedIndicator e s * selectedIndicator f s

omit [Fintype E] in
lemma collisionCount_nonneg (U : Finset V) (S : Finset E) (A : E → Finset V) (s : E → Bool) :
    0 ≤ collisionCount U S A s := by
  apply Finset.sum_nonneg
  intro v hv
  apply Finset.sum_nonneg
  intro e he
  apply Finset.sum_nonneg
  intro f hf
  exact mul_nonneg (selectedIndicator_nonneg e s) (selectedIndicator_nonneg f s)

lemma collisionCount_mean (U : Finset V) (S : Finset E) (A : E → Finset V)
    {p D : ℝ} (hD : 0 ≤ D) (hdeg : ∀ v ∈ U, ((incident S A v).card : ℝ) ≤ D) :
    expectation p (collisionCount U S A) ≤ p^2 * U.card * D^2 := by
  change expectation p (fun s ↦ ∑ v ∈ U, ∑ e ∈ incident S A v,
    ∑ f ∈ (incident S A v).erase e, selectedIndicator e s * selectedIndicator f s) ≤ _
  simp_rw [expectation_sum]
  calc
    _ ≤ ∑ v ∈ U, (p^2 * D^2) := by
      apply Finset.sum_le_sum
      intro v hv
      calc
        _ = ∑ e ∈ incident S A v, ∑ f ∈ (incident S A v).erase e, p^2 := by
          apply Finset.sum_congr rfl
          intro e he
          apply Finset.sum_congr rfl
          intro f hf
          exact expectation_selected_mul p e f (Ne.symm (Finset.mem_erase.mp hf).1)
        _ ≤ ∑ e ∈ incident S A v, (incident S A v).card * p^2 := by
          apply Finset.sum_le_sum
          intro e he
          simp only [Finset.sum_const, nsmul_eq_mul]
          exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr Finset.card_erase_le) (sq_nonneg p)
        _ = p^2 * ((incident S A v).card : ℝ)^2 := by simp; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left
          ((sq_le_sq₀ (Nat.cast_nonneg _) hD).mpr (hdeg v hv)) (sq_nonneg p)
    _ = _ := by simp; ring

omit [Fintype E] in
lemma colliding_card_le (U : Finset V) (S : Finset E) (A : E → Finset V)
    (hsub : ∀ e ∈ S, A e ⊆ U) (s : E → Bool) :
    ((colliding S A s).card : ℝ) ≤ collisionCount U S A s := by
  classical
  let T : E → V → ℝ := fun e v ↦ if v ∈ A e then
    ∑ f ∈ (incident S A v).erase e, selectedIndicator e s * selectedIndicator f s else 0
  have hT : ∀ e v, 0 ≤ T e v := by
    intro e v
    dsimp [T]
    split_ifs
    · exact Finset.sum_nonneg fun f _ ↦
        mul_nonneg (selectedIndicator_nonneg e s) (selectedIndicator_nonneg f s)
    · rfl
  have hid : collisionCount U S A s = ∑ e ∈ S, ∑ v ∈ U, T e v := by
    dsimp [collisionCount, T, incident]
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
  rw [hid]
  simp only [colliding, Finset.card_eq_sum_ones, Finset.sum_filter, Nat.cast_sum,
    Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  apply Finset.sum_le_sum
  intro e he
  split_ifs with h
  · obtain ⟨hs, f, hf, hfe, hfs, hinter⟩ := h
    obtain ⟨v, hve, hvf⟩ := Finset.not_disjoint_iff.mp hinter
    have hvU := hsub e he hve
    have hfinc : f ∈ (incident S A v).erase e :=
      Finset.mem_erase.mpr ⟨hfe, mem_incident S A v f |>.mpr ⟨hf, hvf⟩⟩
    have hb : (1 : ℝ) ≤ T e v := by
      dsimp [T]
      rw [if_pos hve]
      have hh := Finset.single_le_sum (fun g hg ↦
        mul_nonneg (selectedIndicator_nonneg e s) (selectedIndicator_nonneg g s)) hfinc
      simpa [selectedIndicator, hs, hfs] using hh
    exact hb.trans (Finset.single_le_sum (fun w _ ↦ hT e w) hvU)
  · exact Finset.sum_nonneg fun v hv ↦ hT e v

lemma isolated_pairwise (S : Finset E) (A : E → Finset V) (s : E → Bool) :
    (isolated S A s : Set E).Pairwise (fun e f ↦ Disjoint (A e) (A f)) := by
  intro e he f hf hef
  have hE := Finset.mem_filter.mp he
  have hF := Finset.mem_filter.mp hf
  exact hE.2.2 f hF.1 hef.symm hF.2.1

lemma isolated_untouched_disjoint (U : Finset V) (S : Finset E) (A : E → Finset V)
    (s : E → Bool) : Disjoint ((isolated S A s).biUnion A) (untouched U S A s) := by
  apply Finset.disjoint_left.mpr
  intro v hv hvW
  obtain ⟨e, he, hve⟩ := Finset.mem_biUnion.mp hv
  have heS := (Finset.mem_filter.mp he).1
  have hsel := (Finset.mem_filter.mp he).2.1
  have hno := (Finset.mem_filter.mp hvW).2 e (mem_incident S A v e |>.mpr ⟨heS, hve⟩)
  simp_all

lemma wasted_vertices_le (U : Finset V) (S : Finset E) (A : E → Finset V)
    {r : ℕ} (hsub : ∀ e ∈ S, A e ⊆ U) (hr : ∀ e ∈ S, (A e).card ≤ r)
    (s : E → Bool) :
    ((U \ (untouched U S A s ∪ (isolated S A s).biUnion A)).card : ℝ) ≤
      r * collisionCount U S A s := by
  classical
  have hsubset : U \ (untouched U S A s ∪ (isolated S A s).biUnion A) ⊆
      (colliding S A s).biUnion A := by
    intro v hv
    obtain ⟨hvU, hvnot⟩ := Finset.mem_sdiff.mp hv
    have hnot : ¬ ∀ e ∈ incident S A v, s e = false := by
      intro hh
      exact hvnot (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hvU, hh⟩))
    push Not at hnot
    obtain ⟨e, he, hse⟩ := hnot
    have hse' : s e = true := by cases hs : s e <;> simp_all
    have heS := (mem_incident S A v e |>.mp he).1
    have hve := (mem_incident S A v e |>.mp he).2
    have hnotiso : e ∉ isolated S A s := by
      intro hh
      exact hvnot (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨e, hh, hve⟩))
    have hcounter : ¬ ∀ f ∈ S, f ≠ e → s f = true → Disjoint (A e) (A f) := by
      intro hh
      exact hnotiso (Finset.mem_filter.mpr ⟨heS, hse', hh⟩)
    push Not at hcounter
    exact Finset.mem_biUnion.mpr ⟨e, Finset.mem_filter.mpr ⟨heS, hse', hcounter⟩, hve⟩
  calc
    _ ≤ (((colliding S A s).biUnion A).card : ℝ) := by exact_mod_cast Finset.card_le_card hsubset
    _ ≤ (colliding S A s).card * (r : ℝ) := card_biUnion_upper _ _ fun e he ↦
      Nat.cast_le.mpr (hr e (Finset.mem_filter.mp he).1)
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left (colliding_card_le U S A hsub s) (Nat.cast_nonneg r)
      simpa only [mul_comm] using hh

lemma nibble_budget_inequalities {n r D C a K : ℝ}
    (hn : 0 < n) (_hr : 0 ≤ r) (hD : 0 < D) (_hC : 0 ≤ C)
    (ha : 0 < a) (hK : 0 ≤ K) (hcode : n*C ≤ K*D)
    (hsize : 512*r ≤ a*n) (hmany : 16*r^2*(K+1)^2 ≤ a^5*n) :
    4*n*(4*a*r^2*D*C) ≤ (a^2*D)^2 * (a^2*n/(K+1)) ∧
    4*(2*a*n*r) ≤ (a*n/8)^2 := by
  have hK1 : 0 < K+1 := by linarith
  have hh : 16*r^2*K*(K+1) ≤ a^5*n := by
    calc
      _ ≤ 16*r^2*(K+1)*(K+1) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith : K ≤ K+1)
          (by positivity : 0 ≤ 16*r^2)) hK1.le
      _ = 16*r^2*(K+1)^2 := by ring
      _ ≤ _ := hmany
  have hdiv : 16*r^2*K ≤ a^5*n/(K+1) := (le_div_iff₀ hK1).mpr hh
  constructor
  · calc
      _ = (16*a*r^2*D)*(n*C) := by ring
      _ ≤ (16*a*r^2*D)*(K*D) := mul_le_mul_of_nonneg_left hcode (by positivity)
      _ = (a*D^2)*(16*r^2*K) := by ring
      _ ≤ (a*D^2)*(a^5*n/(K+1)) := mul_le_mul_of_nonneg_left hdiv (by positivity)
      _ = _ := by ring
  · have hh := mul_le_mul_of_nonneg_left hsize (show 0 ≤ a*n by positivity)
    nlinarith only [hh]

lemma nibble_bad_loss {n D C a K : ℝ} (hD : 0 ≤ D) (hK : 0 ≤ K)
    (hcode : n*C ≤ K*D) :
    (a^2*n/(K+1))*C ≤ a^2*D := by
  have hK1 : 0 < K+1 := by linarith
  rw [div_mul_eq_mul_div, div_le_iff₀ hK1]
  have hh := mul_le_mul_of_nonneg_left hcode (sq_nonneg a)
  nlinarith only [hh, mul_nonneg (sq_nonneg a) hD]

lemma residual_mean_estimate (U : Finset V) (S : Finset E) (A : E → Finset V)
    {r : ℕ} (hr0 : 1 ≤ r) {D ε C p a : ℝ}
    (hD : 0 < D) (he : 0 ≤ ε) (heD : ε ≤ D) (hC : 0 ≤ C) (hCa : C ≤ a*D)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (ha : 0 ≤ a) (hpa : p*D = a)
    (hra : (r : ℝ)*a ≤ 1)
    (hsub : ∀ e ∈ S, A e ⊆ U) (hr : ∀ e ∈ S, (A e).card = r)
    (hdeg : ∀ v ∈ U, |((incident S A v).card : ℝ) - D| ≤ ε)
    (hcodeg : ∀ v ∈ U, ∀ w ∈ U, v ≠ w →
      ((incident S A v ∩ incident S A w).card : ℝ) ≤ C)
    (v : V) (hv : v ∈ U) :
    |expectation p (fun s ↦ ∑ e ∈ incident S A v, noHit (hits S A ((A e).erase v)) s) -
      (1 - ((r-1 : ℕ) : ℝ)*a)*D| ≤ (1+2*(r : ℝ)*a)*ε + 6*(r : ℝ)^2*a^2*D := by
  let d : ℝ := (incident S A v).card
  let q : ℝ := 1 - ((r-1 : ℕ) : ℝ)*a
  have hd0 : 0 ≤ d := Nat.cast_nonneg _
  have hd : d ≤ 2*D := by have := (abs_le.mp (hdeg v hv)).2; dsimp [d]; linarith
  have hq1 : q ≤ 1 := by
    dsimp [q]
    linarith [mul_nonneg (Nat.cast_nonneg (r-1)) ha]
  have hq0 : 0 ≤ q := by
    have hrl : ((r-1 : ℕ) : ℝ) ≤ (r : ℝ) := by exact_mod_cast Nat.sub_le r 1
    have hh := mul_le_mul_of_nonneg_right hrl ha
    dsimp [q]
    linarith
  have hmean := residual_degree_mean U S A hr0 hD.le he hC hp hp1 hsub hr hdeg hcodeg v hv
  have hqeq : 1 - p*((r-1 : ℕ) : ℝ)*D = q := by dsimp [q]; nlinarith only [hpa]
  rw [hqeq] at hmean
  have hglobal : p * ((r : ℝ)*(D+ε)) ≤ 2*a*r := by
    calc
      _ ≤ p*((r : ℝ)*(2*D)) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (by linarith : D+ε ≤ 2*D) (Nat.cast_nonneg _)) hp
      _ = _ := by nlinarith only [hpa]
  have hsq : (p*((r : ℝ)*(D+ε)))^2/2 ≤ 2*a^2*(r : ℝ)^2 := by
    have hh := (sq_le_sq₀ (show 0 ≤ p*((r : ℝ)*(D+ε)) by positivity)
      (show 0 ≤ 2*a*r by positivity)).mpr hglobal
    nlinarith only [hh]
  have hC' : p*(r : ℝ)^2*C ≤ a^2*(r : ℝ)^2 := by
    calc
      _ ≤ p*(r : ℝ)^2*(a*D) := mul_le_mul_of_nonneg_left hCa (by positivity)
      _ = _ := by linear_combination a * (r : ℝ)^2 * hpa
  have hinner : p*((r : ℝ)*ε+(r : ℝ)^2*C)+(p*((r : ℝ)*(D+ε)))^2/2 ≤
      p*(r : ℝ)*ε+3*a^2*(r : ℝ)^2 := by nlinarith only [hC', hsq]
  have hbound : d * (p*((r : ℝ)*ε+(r : ℝ)^2*C)+(p*((r : ℝ)*(D+ε)))^2/2) ≤
      2*(r : ℝ)*a*ε+6*(r : ℝ)^2*a^2*D := by
    calc
      _ ≤ d*(p*(r : ℝ)*ε+3*a^2*(r : ℝ)^2) := mul_le_mul_of_nonneg_left hinner hd0
      _ ≤ (2*D)*(p*(r : ℝ)*ε+3*a^2*(r : ℝ)^2) := mul_le_mul_of_nonneg_right hd (by positivity)
      _ = _ := by linear_combination 2 * (r : ℝ) * ε * hpa
  have hcenter : |d*q-q*D| ≤ ε := by
    have hh : |d*q-q*D| = |d-D| * q := by
      rw [show d*q-q*D = (d-D)*q by ring, abs_mul, abs_of_nonneg hq0]
    rw [hh]
    exact (mul_le_mul_of_nonneg_left hq1 (abs_nonneg _)).trans (by simpa [d] using hdeg v hv)
  calc
    _ ≤ |expectation p (fun s ↦ ∑ e ∈ incident S A v, noHit (hits S A ((A e).erase v)) s) - d*q| +
        |d*q-q*D| := abs_sub_le _ _ _
    _ ≤ (2*(r : ℝ)*a*ε+6*(r : ℝ)^2*a^2*D)+ε := add_le_add (hmean.trans hbound) hcenter
    _ = _ := by ring

omit [Fintype E] [DecidableEq E] in
lemma incident_restrict_subset (S : Finset E) (A : E → Finset V) (W : Finset V) (v : V) :
    incident (restrictEdges S A W) A v ⊆ incident S A v := by
  rw [incident_restrict]
  exact Finset.filter_subset _ _

lemma one_round (U : Finset V) (S : Finset E) (A : E → Finset V)
    {r : ℕ} (hr0 : 1 ≤ r) {D ε C a K : ℝ}
    (hD : 1 ≤ D) (he : 0 ≤ ε) (hequarter : ε ≤ D/4) (hC : 0 ≤ C)
    (ha : 0 < a) (ha16 : a ≤ 1/16) (hra : (r : ℝ)*a ≤ 1/4)
    (hK : 0 ≤ K) (hcode : U.card*C ≤ K*D) (hCa : C ≤ a*D)
    (hsize : 512*(r : ℝ) ≤ a*U.card)
    (hmany : 16*(r : ℝ)^2*(K+1)^2 ≤ a^5*U.card)
    (hsub : ∀ e ∈ S, A e ⊆ U) (hr : ∀ e ∈ S, (A e).card = r)
    (hdeg : ∀ v ∈ U, |((incident S A v).card : ℝ) - D| ≤ ε)
    (hcodeg : ∀ v ∈ U, ∀ w ∈ U, v ≠ w →
      ((incident S A v ∩ incident S A w).card : ℝ) ≤ C) :
    ∃ W : Finset V, ∃ T M : Finset E,
      W ⊆ U ∧ T ⊆ S ∧ (∀ e ∈ T, A e ⊆ W) ∧ M ⊆ S ∧
      (M : Set E).Pairwise (fun e f ↦ Disjoint (A e) (A f)) ∧
      Disjoint W (M.biUnion A) ∧
      ((W.card : ℝ) ≤ (1-a/2)*U.card) ∧
      (((U \ (W ∪ M.biUnion A)).card : ℝ) ≤ (16*(r : ℝ)+1)*a^2*U.card) ∧
      ∀ v ∈ W, |((incident T A v).card : ℝ) - (1-((r-1 : ℕ) : ℝ)*a)*D| ≤
        (1+2*(r : ℝ)*a)*ε + 8*(r : ℝ)^2*a^2*D := by
  classical
  let n : ℝ := U.card
  let p : ℝ := a/D
  let Y : V → (E → Bool) → ℝ := fun v s ↦
    ∑ e ∈ incident S A v, noHit (hits S A ((A e).erase v)) s
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr0
  have hD0 : 0 < D := by linarith
  have heD : ε ≤ D := by linarith
  have hn : 0 < n := by dsimp [n]; nlinarith only [hsize, hr1, ha]
  have hn0 : 0 ≤ n := hn.le
  have hp : 0 ≤ p := div_nonneg ha.le hD0.le
  have hp1 : p ≤ 1 := (div_le_one hD0).mpr (by linarith)
  have hpa : p*D = a := div_mul_cancel₀ a hD0.ne'
  have hK1 : 0 < K+1 := by linarith
  have hmax : ∀ v ∈ U, ((incident S A v).card : ℝ) ≤ D+ε := by
    intro v hv
    have := (abs_le.mp (hdeg v hv)).2
    linarith
  have hmult : p*(D+ε) ≤ 2*a := by
    have hh := mul_le_mul_of_nonneg_left heD hp
    nlinarith only [hh, hpa]
  have hmul0 : 0 ≤ p*(D+ε) := by positivity
  have hsq : (p*(D+ε))^2 ≤ 4*a^2 := by
    have hh := (sq_le_sq₀ hmul0 (by positivity : 0 ≤ 2*a)).mpr hmult
    nlinarith only [hh]
  have hY : ∀ v ∈ U, expectation p (fun s ↦ (Y v s - expectation p (Y v))^2) ≤
      4*a*(r : ℝ)^2*D*C := by
    intro v hv
    have hh := residual_degree_variance U S A (by linarith : 0 ≤ D+ε) hC hp hp1 hsub
      (fun e he ↦ (hr e he).le) hmax hcodeg v hv
    apply hh.trans
    have hsq' : (D+ε)^2 ≤ (2*D)^2 := (sq_le_sq₀ (by positivity) (by positivity)).mpr (by linarith)
    calc
      _ = (p*(r : ℝ)^2*C)*(D+ε)^2 := by ring
      _ ≤ (p*(r : ℝ)^2*C)*(2*D)^2 := mul_le_mul_of_nonneg_left hsq' (by positivity)
      _ = _ := by linear_combination 4*(r : ℝ)^2*D*C*hpa
  have hZ : expectation p (fun s ↦ (((untouched U S A s).card : ℝ) -
      expectation p (fun s ↦ ((untouched U S A s).card : ℝ)))^2) ≤ 2*a*n*r := by
    apply (untouched_variance U S A hp hp1 (fun e he ↦ (hr e he).le) hmax).trans
    calc
      _ ≤ p*n*(2*D)*r := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith : D+ε ≤ 2*D)
          (by positivity : 0 ≤ p*n)) (Nat.cast_nonneg r)
      _ = _ := by linear_combination 2*n*(r : ℝ)*hpa
  have hCollision : expectation p (collisionCount U S A) ≤ 4*a^2*n := by
    apply (collisionCount_mean U S A (by linarith : 0 ≤ D+ε) hmax).trans
    have hh := mul_le_mul_of_nonneg_left hsq hn0
    nlinarith only [hh]
  have hbudgets := nibble_budget_inequalities hn (Nat.cast_nonneg r) hD0 hC ha hK hcode hsize hmany
  obtain ⟨s, hsB, hsZ, hsC⟩ := exists_controlled_outcome hp hp1 U Y
    (fun s ↦ ((untouched U S A s).card : ℝ)) (collisionCount U S A)
    (t := a^2*D) (b := a^2*n/(K+1)) (u := a*n/8) (c := 16*a^2*n)
    (by positivity) (by positivity) (by positivity) (by positivity)
    hY hZ (collisionCount_nonneg U S A) hCollision hbudgets.1 hbudgets.2 (by ring_nf; rfl)
  let B : Finset V := U.filter fun v ↦ a^2*D < |Y v s - expectation p (Y v)|
  let U₀ := untouched U S A s
  let W := U₀ \ B
  let S₀ := restrictEdges S A U₀
  let T := restrictEdges S₀ A W
  let M := isolated S A s
  have hU₀ : U₀ ⊆ U := Finset.filter_subset _ _
  have hW₀ : W ⊆ U₀ := Finset.sdiff_subset
  have hS₀ : S₀ ⊆ S := Finset.filter_subset _ _
  have hT₀ : T ⊆ S₀ := Finset.filter_subset _ _
  have hsub₀ : ∀ e ∈ S₀, A e ⊆ U₀ := fun e he ↦ (Finset.mem_filter.mp he).2
  have hTW : ∀ e ∈ T, A e ⊆ W := fun e he ↦ (Finset.mem_filter.mp he).2
  have hMS : M ⊆ S := Finset.filter_subset _ _
  have hBcard : (B.card : ℝ) ≤ a^2*n/(K+1) := hsB
  have hbmax : a^2*n/(K+1) ≤ a^2*n := by
    rw [div_le_iff₀ hK1]
    nlinarith only [mul_nonneg (show 0 ≤ a^2*n by positivity) hK]
  have hmeanZ : expectation p (fun s ↦ ((untouched U S A s).card : ℝ)) ≤ n*(1-5*a/8) := by
    apply (untouched_mean_upper U S A hp hp1 (by linarith : 0 ≤ D+ε) (D := D-ε) ?_).trans
    · apply mul_le_mul_of_nonneg_left _ hn0
      have hpe : p*ε ≤ a/4 := by
        have hh := mul_le_mul_of_nonneg_left hequarter hp
        nlinarith only [hh, hpa]
      have haa := mul_nonneg ha.le (sub_nonneg.mpr ha16)
      nlinarith only [hpe, hpa, hsq, haa]
    · intro v hv
      have hb := abs_le.mp (hdeg v hv)
      constructor <;> linarith
  have hUcard : (U₀.card : ℝ) ≤ (1-a/2)*n := by
    have hh := (abs_le.mp hsZ).2
    dsimp [U₀]
    linarith
  have hwaste0 : ((U \ (U₀ ∪ M.biUnion A)).card : ℝ) ≤ r*collisionCount U S A s :=
    wasted_vertices_le U S A hsub (fun e he ↦ (hr e he).le) s
  have hwaste : ((U \ (W ∪ M.biUnion A)).card : ℝ) ≤ (16*(r : ℝ)+1)*a^2*n := by
    have hset : U \ (W ∪ M.biUnion A) ⊆ (U \ (U₀ ∪ M.biUnion A)) ∪ B := by
      intro v hv
      simp only [W, Finset.mem_sdiff, Finset.mem_union] at *
      tauto
    have hcard : ((U \ (W ∪ M.biUnion A)).card : ℝ) ≤
        (U \ (U₀ ∪ M.biUnion A)).card + B.card := by
      exact_mod_cast (Finset.card_le_card hset).trans (Finset.card_union_le _ _)
    have hc := mul_le_mul_of_nonneg_left hsC (Nat.cast_nonneg r)
    nlinarith only [hcard, hwaste0, hBcard, hbmax, hc]
  refine ⟨W, T, M, hW₀.trans hU₀, hT₀.trans hS₀, hTW, hMS,
    isolated_pairwise S A s,
    (isolated_untouched_disjoint U S A s).symm.mono_left hW₀,
    (Nat.cast_le.mpr (Finset.card_le_card hW₀)).trans hUcard, hwaste, ?_⟩
  intro v hv
  obtain ⟨hv₀, hvB⟩ := Finset.mem_sdiff.mp hv
  have hvU := hU₀ hv₀
  have htest : |Y v s - expectation p (Y v)| ≤ a^2*D := by
    apply le_of_not_gt
    intro hh
    exact hvB (Finset.mem_filter.mpr ⟨hvU, hh⟩)
  have hmeanY := residual_mean_estimate U S A hr0 hD0 he heD hC hCa hp hp1 ha.le hpa
    (by linarith : (r : ℝ)*a ≤ 1) hsub hr hdeg hcodeg v hvU
  have hdegeq : ((incident S₀ A v).card : ℝ) = Y v s :=
    residual_degree_eq U S A hsub s v hv₀
  have hdegree0 : |((incident S₀ A v).card : ℝ) - (1-((r-1 : ℕ) : ℝ)*a)*D| ≤
      (1+2*(r : ℝ)*a)*ε + 6*(r : ℝ)^2*a^2*D + a^2*D := by
    rw [hdegeq]
    exact (abs_sub_le (Y v s) (expectation p (Y v)) _).trans (by linarith)
  have hc₀ : ∀ w ∈ B, v ≠ w → ((incident S₀ A v ∩ incident S₀ A w).card : ℝ) ≤ C := by
    intro w hw hvw
    apply (Nat.cast_le.mpr (Finset.card_le_card (Finset.inter_subset_inter
      (incident_restrict_subset S A U₀ v) (incident_restrict_subset S A U₀ w)))).trans
    exact hcodeg v hvU w (Finset.mem_filter.mp hw).1 hvw
  have hloss := degree_loss_deleting U₀ B S₀ A hC hsub₀ v hc₀ hvB
  change ((incident S₀ A v).card : ℝ) - B.card*C ≤ ((incident T A v).card : ℝ) at hloss
  have hBCloss : B.card*C ≤ a^2*D :=
    (mul_le_mul_of_nonneg_right hBcard hC).trans (nibble_bad_loss hD0.le hK hcode)
  have hupper : ((incident T A v).card : ℝ) ≤ (incident S₀ A v).card :=
    Nat.cast_le.mpr (Finset.card_le_card (incident_restrict_subset S₀ A W v))
  have hrerr : 2*a^2*D ≤ 2*(r : ℝ)^2*a^2*D := by
    have hh : (2 : ℝ) ≤ 2*(r : ℝ)^2 := by nlinarith only [hr1]
    have hh' := mul_le_mul_of_nonneg_right hh (show 0 ≤ a^2*D by positivity)
    nlinarith only [hh']
  apply abs_le.mpr
  have hlow0 := (abs_le.mp hdegree0).1
  have hupp0 := (abs_le.mp hdegree0).2
  constructor <;> nlinarith only [hloss, hBCloss, hupper, hrerr, hlow0, hupp0]

omit [Fintype E] [DecidableEq E] in
lemma incident_mono {S T : Finset E} (h : S ⊆ T) (A : E → Finset V) (v : V) :
    incident S A v ⊆ incident T A v := by
  intro e he
  obtain ⟨he, hv⟩ := mem_incident S A v e |>.mp he
  exact mem_incident T A v e |>.mpr ⟨h he, hv⟩

/-- The bookkeeping invariant of a partial matching and its active graph. -/
structure PackingState (U : Finset V) (S : Finset E) (A : E → Finset V) where
  vertices : Finset V
  edges : Finset E
  chosen : Finset E
  vertices_sub : vertices ⊆ U
  edges_sub : edges ⊆ S
  support : ∀ e ∈ edges, A e ⊆ vertices
  chosen_sub : chosen ⊆ S
  matching : (chosen : Set E).Pairwise (fun e f ↦ Disjoint (A e) (A f))
  separation : Disjoint vertices (chosen.biUnion A)

namespace PackingState

noncomputable def initial (U : Finset V) (S : Finset E) (A : E → Finset V)
    (hsub : ∀ e ∈ S, A e ⊆ U) : PackingState U S A where
  vertices := U
  edges := S
  chosen := ∅
  vertices_sub := Finset.Subset.refl _
  edges_sub := Finset.Subset.refl _
  support := hsub
  chosen_sub := Finset.empty_subset _
  matching := by simp
  separation := by simp

noncomputable def compose {U : Finset V} {S : Finset E} {A : E → Finset V}
    (P : PackingState U S A) (Q : PackingState P.vertices P.edges A) : PackingState U S A where
  vertices := Q.vertices
  edges := Q.edges
  chosen := P.chosen ∪ Q.chosen
  vertices_sub := Q.vertices_sub.trans P.vertices_sub
  edges_sub := Q.edges_sub.trans P.edges_sub
  support := Q.support
  chosen_sub := Finset.union_subset P.chosen_sub (Q.chosen_sub.trans P.edges_sub)
  matching := by
    have hcross (e : E) (he : e ∈ P.chosen) (f : E) (hf : f ∈ Q.chosen) :
        Disjoint (A e) (A f) := by
      apply P.separation.symm.mono
      · intro v hv
        exact Finset.mem_biUnion.mpr ⟨e, he, hv⟩
      · exact P.support f (Q.chosen_sub hf)
    intro e he f hf hef
    rcases Finset.mem_union.mp he with he | he <;> rcases Finset.mem_union.mp hf with hf | hf
    · exact P.matching he hf hef
    · exact hcross e he f hf
    · exact (hcross f hf e he).symm
    · exact Q.matching he hf hef
  separation := by
    rw [Finset.union_biUnion]
    exact Finset.disjoint_union_right.mpr
      ⟨P.separation.mono_left Q.vertices_sub, Q.separation⟩

omit [Fintype E] in
lemma compose_waste {U : Finset V} {S : Finset E} {A : E → Finset V}
    (P : PackingState U S A) (Q : PackingState P.vertices P.edges A) :
    ((U \ ((P.compose Q).vertices ∪ (P.compose Q).chosen.biUnion A)).card : ℝ) ≤
      (U \ (P.vertices ∪ P.chosen.biUnion A)).card +
      (P.vertices \ (Q.vertices ∪ Q.chosen.biUnion A)).card := by
  have hsub : U \ ((P.compose Q).vertices ∪ (P.compose Q).chosen.biUnion A) ⊆
      (U \ (P.vertices ∪ P.chosen.biUnion A)) ∪
      (P.vertices \ (Q.vertices ∪ Q.chosen.biUnion A)) := by
    intro v hv
    simp only [compose, Finset.union_biUnion, Finset.mem_sdiff, Finset.mem_union] at *
    tauto
  exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

end PackingState

/-- Iteration with stopping when the requested small residual has already
been reached. All choices are finite and use the one-round theorem. -/
lemma nibble_iteration (U : Finset V) (S : Finset E) (A : E → Finset V)
    {r : ℕ} (hr0 : 1 ≤ r) (k : ℕ) {D ε C a K d : ℝ}
    (hD : 0 < D) (he : 0 ≤ ε) (hC : 0 ≤ C)
    (ha : 0 < a) (ha16 : a ≤ 1/16) (hra : (r : ℝ)*a ≤ 1/4)
    (hK : 0 ≤ K) (_hd : 0 < d)
    (hDmin : 1 ≤ (1-((r-1 : ℕ) : ℝ)*a)^k*D)
    (hecap : (1+2*(r : ℝ)*a)^k*(ε+8*(r : ℝ)^2*a^2*D*k) ≤
      (1-((r-1 : ℕ) : ℝ)*a)^k*D/4)
    (hCmin : C ≤ a*((1-((r-1 : ℕ) : ℝ)*a)^k*D))
    (hcode : U.card*C ≤ K*((1-((r-1 : ℕ) : ℝ)*a)^k*D))
    (hsize : 512*(r : ℝ) ≤ a*d*U.card)
    (hmany : 16*(r : ℝ)^2*(K+1)^2 ≤ a^5*d*U.card)
    (hcontract : (1-a/2)^k ≤ d)
    (hsub : ∀ e ∈ S, A e ⊆ U) (hr : ∀ e ∈ S, (A e).card = r)
    (hdeg : ∀ v ∈ U, |((incident S A v).card : ℝ) - D| ≤ ε)
    (hcodeg : ∀ v ∈ U, ∀ w ∈ U, v ≠ w →
      ((incident S A v ∩ incident S A w).card : ℝ) ≤ C) :
    ∃ P : PackingState U S A,
      ((P.vertices.card : ℝ) ≤ d*U.card) ∧
      (((U \ (P.vertices ∪ P.chosen.biUnion A)).card : ℝ) ≤
        k*(16*(r : ℝ)+1)*a^2*U.card) := by
  classical
  let q : ℝ := 1-((r-1 : ℕ) : ℝ)*a
  let g : ℝ := 1+2*(r : ℝ)*a
  let b : ℝ := 1-a/2
  let er : ℕ → ℝ := fun i ↦ g^i*(ε+8*(r : ℝ)^2*a^2*D*i)
  let c : ℝ := (16*(r : ℝ)+1)*a^2
  have hr0' : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have hrle : ((r-1 : ℕ) : ℝ) ≤ (r : ℝ) := by exact_mod_cast Nat.sub_le r 1
  have hq0 : 0 ≤ q := by
    have hh := mul_le_mul_of_nonneg_right hrle ha.le
    dsimp [q]
    linarith
  have hq1 : q ≤ 1 := by dsimp [q]; linarith [mul_nonneg (Nat.cast_nonneg (r-1)) ha.le]
  have hg : 1 ≤ g := by dsimp [g]; nlinarith only [mul_nonneg hr0' ha.le]
  have hg0 : 0 ≤ g := by linarith
  have hb0 : 0 ≤ b := by dsimp [b]; linarith
  have hc0 : 0 ≤ c := by dsimp [c]; positivity
  have hDibounds (i : ℕ) (hi : i ≤ k) : q^k*D ≤ q^i*D ∧ q^i*D ≤ D := by
    constructor
    · exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hq0 hq1 hi) hD.le
    · exact (mul_le_mul_of_nonneg_right (pow_le_one₀ hq0 hq1) hD.le).trans_eq (one_mul D)
  have hernonneg (i : ℕ) : 0 ≤ er i := by dsimp [er]; positivity
  have herbounds (i : ℕ) (hi : i ≤ k) : er i ≤ q^i*D/4 := by
    have herle : er i ≤ er k := by
      apply mul_le_mul
      · exact pow_le_pow_right₀ hg hi
      · have hh : (i : ℝ) ≤ k := by exact_mod_cast hi
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hh
          (show 0 ≤ 8*(r : ℝ)^2*a^2*D by positivity))
      · positivity
      · positivity
    exact (herle.trans hecap).trans (div_le_div_of_nonneg_right (hDibounds i hi).1 (by norm_num))
  have herrec (i : ℕ) : g*er i+8*(r : ℝ)^2*a^2*(q^i*D) ≤ er (i+1) := by
    have hiD : q^i*D ≤ D :=
      (mul_le_mul_of_nonneg_right (pow_le_one₀ hq0 hq1) hD.le).trans_eq (one_mul D)
    have hgpow : 1 ≤ g^(i+1) := one_le_pow₀ hg
    have hcD : 0 ≤ 8*(r : ℝ)^2*a^2*D := by positivity
    have hh : 8*(r : ℝ)^2*a^2*(q^i*D) ≤ g^(i+1)*(8*(r : ℝ)^2*a^2*D) := by
      calc
        _ ≤ 8*(r : ℝ)^2*a^2*D := mul_le_mul_of_nonneg_left hiD (by positivity)
        _ ≤ _ := by simpa using mul_le_mul_of_nonneg_right hgpow hcD
    have heq : er (i+1) = g*er i + g^(i+1)*(8*(r : ℝ)^2*a^2*D) := by
      dsimp [er]
      rw [pow_succ]
      push_cast
      ring
    rw [heq]
    exact add_le_add le_rfl hh
  have hiter : ∀ i ≤ k, ∃ P : PackingState U S A,
      (((P.vertices.card : ℝ) ≤ d*U.card) ∨
        ((P.vertices.card : ℝ) ≤ b^i*U.card) ∧
        ∀ v ∈ P.vertices, |((incident P.edges A v).card : ℝ)-q^i*D| ≤ er i) ∧
      (((U \ (P.vertices ∪ P.chosen.biUnion A)).card : ℝ) ≤ i*c*U.card) := by
    intro i
    induction i with
    | zero =>
      intro hi
      refine ⟨PackingState.initial U S A hsub, Or.inr ⟨?_, ?_⟩, ?_⟩
      · simp [PackingState.initial]
      · simpa [PackingState.initial, er] using hdeg
      · simp [PackingState.initial]
    | succ i ih =>
      intro hik
      have hik' : i ≤ k := (Nat.le_succ i).trans hik
      obtain ⟨P, hP, hwasteP⟩ := ih hik'
      rcases hP with hsmall | ⟨hcount, hregular⟩
      · refine ⟨P, Or.inl hsmall, hwasteP.trans ?_⟩
        have hh : (i : ℝ) ≤ (i+1 : ℕ) := by exact_mod_cast Nat.le_succ i
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hh hc0) (Nat.cast_nonneg U.card)
      · by_cases hsmall : (P.vertices.card : ℝ) ≤ d*U.card
        · refine ⟨P, Or.inl hsmall, hwasteP.trans ?_⟩
          have hh : (i : ℝ) ≤ (i+1 : ℕ) := by exact_mod_cast Nat.le_succ i
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hh hc0) (Nat.cast_nonneg U.card)
        have hlarge : d*U.card < (P.vertices.card : ℝ) := lt_of_not_ge hsmall
        have hni : (P.vertices.card : ℝ) ≤ U.card := Nat.cast_le.mpr (Finset.card_le_card P.vertices_sub)
        have hDi : 1 ≤ q^i*D := hDmin.trans (hDibounds i hik').1
        have hcodei : P.vertices.card*C ≤ K*(q^i*D) :=
          (mul_le_mul_of_nonneg_right hni hC).trans
            (hcode.trans (mul_le_mul_of_nonneg_left (hDibounds i hik').1 hK))
        have hsizei : 512*(r : ℝ) ≤ a*P.vertices.card := by
          have hh := mul_le_mul_of_nonneg_left hlarge.le ha.le
          nlinarith only [hsize, hh]
        have hmanyi : 16*(r : ℝ)^2*(K+1)^2 ≤ a^5*P.vertices.card := by
          have hh := mul_le_mul_of_nonneg_left hlarge.le (show 0 ≤ a^5 by positivity)
          nlinarith only [hmany, hh]
        have hcodegi : ∀ v ∈ P.vertices, ∀ w ∈ P.vertices, v ≠ w →
            ((incident P.edges A v ∩ incident P.edges A w).card : ℝ) ≤ C := by
          intro v hv w hw hvw
          apply (Nat.cast_le.mpr (Finset.card_le_card (Finset.inter_subset_inter
            (incident_mono P.edges_sub A v) (incident_mono P.edges_sub A w)))).trans
          exact hcodeg v (P.vertices_sub hv) w (P.vertices_sub hw) hvw
        obtain ⟨W, T, M, hWU, hTS, hTW, hMS, hmatch, hsep, hWcard, hwaste, hreg⟩ :=
          one_round P.vertices P.edges A hr0 hDi (hernonneg i) (herbounds i hik') hC
            ha ha16 hra hK hcodei
            (hCmin.trans (mul_le_mul_of_nonneg_left (hDibounds i hik').1 ha.le))
            hsizei hmanyi P.support (fun e he ↦ hr e (P.edges_sub he)) hregular hcodegi
        let Q : PackingState P.vertices P.edges A := ⟨W,T,M,hWU,hTS,hTW,hMS,hmatch,hsep⟩
        refine ⟨P.compose Q, Or.inr ⟨?_, ?_⟩, ?_⟩
        · change (W.card : ℝ) ≤ b^(i+1)*U.card
          calc
            _ ≤ b*P.vertices.card := hWcard
            _ ≤ b*(b^i*U.card) := mul_le_mul_of_nonneg_left hcount hb0
            _ = _ := by rw [pow_succ]; ring
        · intro v hv
          change |((incident T A v).card : ℝ)-q^(i+1)*D| ≤ er (i+1)
          have hh := hreg v hv
          have heq : (1-((r-1 : ℕ) : ℝ)*a)*(q^i*D) = q^(i+1)*D := by
            change q*(q^i*D) = _
            rw [pow_succ]
            ring
          rw [heq] at hh
          exact hh.trans (herrec i)
        · apply (PackingState.compose_waste P Q).trans
          change (U \ (P.vertices ∪ P.chosen.biUnion A)).card +
            ((P.vertices \ (W ∪ M.biUnion A)).card : ℝ) ≤ (i+1 : ℕ)*c*U.card
          have hh := mul_le_mul_of_nonneg_left hni hc0
          change ((P.vertices \ (W ∪ M.biUnion A)).card : ℝ) ≤ c*P.vertices.card at hwaste
          push_cast
          nlinarith only [hwasteP, hwaste, hh]
  obtain ⟨P, hP, hwaste⟩ := hiter k le_rfl
  refine ⟨P, ?_, ?_⟩
  · rcases hP with hsmall | ⟨hbound, _⟩
    · exact hsmall
    · exact hbound.trans (mul_le_mul_of_nonneg_right hcontract (Nat.cast_nonneg U.card))
  · simpa only [c, mul_assoc] using hwaste

open Filter Topology

/-- Fixed nibble parameters, chosen in the order required by packing:
first the tolerated residual, then finitely many rounds, then regularity. -/
lemma nibble_parameters (r : ℕ) {d : ℝ} (hd : 0 < d) :
    ∃ (a : ℝ) (k : ℕ) (e : ℝ), 0 < a ∧ a ≤ 1/16 ∧
      (r : ℝ)*a ≤ 1/4 ∧ 0 < e ∧
      0 < (1-((r-1 : ℕ) : ℝ)*a)^k ∧
      (1+2*(r : ℝ)*a)^k*(e+8*(r : ℝ)^2*a^2*k) ≤
        (1-((r-1 : ℕ) : ℝ)*a)^k/4 ∧
      (1-a/2)^k ≤ d ∧ k*(16*(r : ℝ)+1)*a^2 ≤ d := by
  obtain ⟨M, hM⟩ := exists_pow_lt_of_lt_one hd
    (Real.exp_lt_one_iff.mpr (show (-1/2 : ℝ) < 0 by norm_num))
  let Q : ℝ := Real.exp (-((r-1 : ℕ) : ℝ))^M
  let G : ℝ := Real.exp (2*(r : ℝ))^M
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hG : 0 < G := by dsimp [G]; positivity
  let e : ℝ := Q/(16*G)
  have he : 0 < e := by dsimp [e]; positivity
  have ha0 : Tendsto (fun n : ℕ ↦ (1 : ℝ)/n) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop |>.congr (by simp)
  have ha2k : Tendsto (fun n : ℕ ↦ ((1 : ℝ)/n)^2*(n*M : ℕ)) atTop (𝓝 0) := by
    apply (show Tendsto (fun n : ℕ ↦ (1 : ℝ)/n * M) atTop (𝓝 0) by
      simpa using ha0.mul_const (M : ℝ)).congr' _
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    push_cast
    field_simp
  have hq : Tendsto (fun n : ℕ ↦ (1-((r-1 : ℕ) : ℝ)*(1/n))^(n*M))
      atTop (𝓝 Q) := by
    simpa only [pow_mul, div_eq_mul_inv, one_mul, sub_eq_add_neg, neg_mul]
      using (Real.tendsto_one_add_div_pow_exp (-((r-1 : ℕ) : ℝ))).pow M
  have hg : Tendsto (fun n : ℕ ↦ (1+2*(r : ℝ)*(1/n))^(n*M))
      atTop (𝓝 G) := by
    simpa only [pow_mul, div_eq_mul_inv, one_mul]
      using (Real.tendsto_one_add_div_pow_exp (2*(r : ℝ))).pow M
  have hb : Tendsto (fun n : ℕ ↦ (1-(1/(n : ℝ))/2)^(n*M))
      atTop (𝓝 (Real.exp (-1/2)^M)) := by
    convert (Real.tendsto_one_add_div_pow_exp (-1/2)).pow M using 1
    ext n
    rw [pow_mul]
    congr 2
    ring
  have herr : Tendsto (fun n : ℕ ↦
      (1+2*(r : ℝ)*(1/n))^(n*M)*(e+8*(r : ℝ)^2*(1/n)^2*(n*M : ℕ)))
      atTop (𝓝 (G*e)) := by
    have ht : Tendsto (fun n : ℕ ↦ e+8*(r : ℝ)^2*((1/(n : ℝ))^2*(n*M : ℕ)))
        atTop (𝓝 e) := by
      simpa using tendsto_const_nhds.add (ha2k.const_mul (8*(r : ℝ)^2))
    simpa only [mul_assoc] using hg.mul ht
  have hw : Tendsto (fun n : ℕ ↦ (n*M : ℕ)*(16*(r : ℝ)+1)*(1/(n : ℝ))^2)
      atTop (𝓝 0) := by
    convert ha2k.const_mul (16*(r : ℝ)+1) using 1 <;> (try {ext n; ring_nf})
  have hgap : G*e < Q/4 := by dsimp [e]; field_simp; nlinarith
  have hparams : ∀ᶠ n : ℕ in atTop,
      0 < (1 : ℝ)/n ∧ (1 : ℝ)/n ≤ 1/16 ∧
      (r : ℝ)*(1/n) ≤ 1/4 ∧
      0 < (1-((r-1 : ℕ) : ℝ)*(1/n))^(n*M) ∧
      (1+2*(r : ℝ)*(1/n))^(n*M)*(e+8*(r : ℝ)^2*(1/n)^2*(n*M : ℕ)) ≤
        (1-((r-1 : ℕ) : ℝ)*(1/n))^(n*M)/4 ∧
      (1-(1/(n : ℝ))/2)^(n*M) ≤ d ∧
      (n*M : ℕ)*(16*(r : ℝ)+1)*(1/(n : ℝ))^2 ≤ d := by
    filter_upwards [eventually_ge_atTop 1, ha0.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/16)),
      (ha0.const_mul (r : ℝ)).eventually (gt_mem_nhds (by norm_num : (r : ℝ)*0 < 1/4)),
      hq.eventually (lt_mem_nhds hQ),
      herr.eventually_lt (hq.div_const 4) hgap,
      hb.eventually (gt_mem_nhds hM), hw.eventually (gt_mem_nhds hd)] with n hn ha hr hq' he1 hb' hw'
    have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    refine ⟨by positivity, ha.le, hr.le, hq', ?_, hb'.le, hw'.le⟩
    exact he1.le
  obtain ⟨n, hn⟩ := hparams.exists
  exact ⟨1/(n : ℝ), n*M, e, hn.1, hn.2.1, hn.2.2.1, he, hn.2.2.2⟩

theorem almost_perfect_matching (r : ℕ) (hr : 1 ≤ r) {K₀ η : ℝ}
    (hK₀ : 0 ≤ K₀) (hη : 0 < η) :
    ∃ e T : ℝ, 0 < e ∧ 0 < T ∧
    ∀ {V E : Type} [DecidableEq V] [Fintype E] [DecidableEq E],
    ∀ (U : Finset V) (S : Finset E) (A : E → Finset V) (D C : ℝ),
      T ≤ D → T ≤ (U.card : ℝ) → 0 ≤ C → C ≤ e*D →
      U.card*C ≤ K₀*D →
      (∀ i ∈ S, A i ⊆ U) → (∀ i ∈ S, (A i).card = r) →
      (∀ v ∈ U, |((incident S A v).card : ℝ)-D| ≤ e*D) →
      (∀ v ∈ U, ∀ w ∈ U, v ≠ w →
        ((incident S A v ∩ incident S A w).card : ℝ) ≤ C) →
      ∃ M ⊆ S, (M : Set E).Pairwise (fun i j ↦ Disjoint (A i) (A j)) ∧
        (1-η)*(U.card : ℝ) ≤ r*(M.card : ℝ) := by
  let d : ℝ := η/4
  have hd : 0 < d := by dsimp [d]; positivity
  obtain ⟨a,k,e₀,ha,ha16,hra,he₀,hq,hecap,hcontract,hwaste⟩ := nibble_parameters r hd
  let q : ℝ := (1-((r-1 : ℕ) : ℝ)*a)^k
  let K : ℝ := K₀/q
  have hq0 : 0 < q := hq
  have hK : 0 ≤ K := div_nonneg hK₀ hq0.le
  let e : ℝ := min e₀ (a*q)
  have he : 0 < e := lt_min he₀ (mul_pos ha hq0)
  let T : ℝ := max (1/q) (max (512*(r : ℝ)/(a*d))
    (16*(r : ℝ)^2*(K+1)^2/(a^5*d)))
  have hT1 : 1/q ≤ T := le_max_left _ _
  have hT2 : 512*(r : ℝ)/(a*d) ≤ T := (le_max_left _ _).trans (le_max_right _ _)
  have hT3 : 16*(r : ℝ)^2*(K+1)^2/(a^5*d) ≤ T :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hT : 0 < T := (by positivity : 0 < (1 : ℝ)/q).trans_le hT1
  refine ⟨e,T,he,hT,?_⟩
  intro V E instV instF instE U S A D C hD hn hC hCe hcode hsub hunif hdeg hcodeg
  have hD0 : 0 < D := hT.trans_le hD
  have hDmin : 1 ≤ q*D := by
    have hh := (div_le_iff₀ hq0).mp (hT1.trans hD)
    nlinarith only [hh]
  have hcap : (1+2*(r : ℝ)*a)^k*(e₀*D+8*(r : ℝ)^2*a^2*D*k) ≤ q*D/4 := by
    have hh := mul_le_mul_of_nonneg_right hecap hD0.le
    dsimp [q]
    nlinarith only [hh]
  have hCmin : C ≤ a*(q*D) := by
    calc C ≤ e*D := hCe
         _ ≤ (a*q)*D := mul_le_mul_of_nonneg_right (min_le_right _ _) hD0.le
         _ = _ := by ring
  have hcod : U.card*C ≤ K*(q*D) := by
    have heq : K*(q*D)=K₀*D := by dsimp [K]; field_simp
    rw [heq]
    exact hcode
  have hsize : 512*(r : ℝ) ≤ a*d*U.card := by
    have hh := (div_le_iff₀ (mul_pos ha hd)).mp (hT2.trans hn)
    nlinarith only [hh]
  have hmany : 16*(r : ℝ)^2*(K+1)^2 ≤ a^5*d*U.card := by
    have hh := (div_le_iff₀ (mul_pos (pow_pos ha _) hd)).mp (hT3.trans hn)
    nlinarith only [hh]
  have hdeg' : ∀ v ∈ U, |((incident S A v).card : ℝ)-D| ≤ e₀*D := by
    intro v hv
    exact (hdeg v hv).trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hD0.le)
  obtain ⟨P,hP,hwP⟩ := nibble_iteration U S A hr k hD0
    (mul_nonneg he₀.le hD0.le) hC ha ha16 hra hK hd hDmin hcap hCmin hcod
      hsize hmany hcontract hsub hunif hdeg' hcodeg
  refine ⟨P.chosen,P.chosen_sub,P.matching,?_⟩
  have hcard : (P.chosen.biUnion A).card = P.chosen.card*r := by
    rw [Finset.card_biUnion P.matching]
    calc
      _ = ∑ _i ∈ P.chosen, r := Finset.sum_congr rfl (fun i hi ↦ hunif i (P.chosen_sub hi))
      _ = _ := by simp
  have hsubset : P.vertices ∪ P.chosen.biUnion A ⊆ U := by
    refine Finset.union_subset P.vertices_sub ?_
    intro v hv
    obtain ⟨i,hi,hvi⟩ := Finset.mem_biUnion.mp hv
    exact hsub i (P.chosen_sub hi) hvi
  have hcount := Finset.card_sdiff_add_card_eq_card hsubset
  rw [Finset.card_union_of_disjoint P.separation, hcard] at hcount
  have hcount' : ((U \ (P.vertices ∪ P.chosen.biUnion A)).card : ℝ) +
      (P.vertices.card : ℝ) + P.chosen.card*r = U.card := by
    have hh : ((U \ (P.vertices ∪ P.chosen.biUnion A)).card : ℝ) +
      ((P.vertices.card : ℝ) + P.chosen.card*r) = U.card := by exact_mod_cast hcount
    linarith
  have hww := mul_le_mul_of_nonneg_right hwaste (Nat.cast_nonneg U.card)
  dsimp [d] at hP hww
  nlinarith only [hP,hwP,hww,hcount', show (0 : ℝ) ≤ U.card from Nat.cast_nonneg _, hη]

end Hypergraph

end Nibble
end AsymptoticallyMinimalLittlewood

end OAI



namespace OAI

universe uV uE

namespace AsymptoticallyMinimalLittlewood.Nibble
noncomputable section
open scoped BigOperators
open Finset
variable {V : Type uV} {E : Type uE} [DecidableEq V] [Fintype E] [DecidableEq E]

omit [Fintype E] in
lemma pruned_degree_near (U B : Finset V) (S : Finset E) (A : E → Finset V)
    {D C e : ℝ} (hC : 0≤C) (hsub : ∀ i∈S, A i⊆U)
    (hdeg : ∀ v∈U\B, |((incident S A v).card : ℝ)-D|≤e*D/2)
    (hcode : ∀ v∈U, ∀ w∈U, v≠w → ((incident S A v∩incident S A w).card : ℝ)≤C)
    (hB : B⊆U) (hsmall : (B.card : ℝ)*C≤e*D/2) :
    ∀ v∈U\B, |((incident (restrictEdges S A (U\B)) A v).card : ℝ)-D|≤e*D := by
  intro v hv
  obtain ⟨hvU,hvB⟩ := Finset.mem_sdiff.mp hv
  obtain ⟨hlo,hhi⟩ := abs_le.mp (hdeg v hv)
  have hloss := degree_loss_deleting U B S A hC hsub v
    (fun w hw hne ↦ hcode v hvU w (hB hw) hne) hvB
  have hu : ((incident (restrictEdges S A (U\B)) A v).card : ℝ)≤(incident S A v).card := by
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro y hy
    rw [incident_restrict] at hy
    exact (Finset.mem_filter.mp hy).1
  have heD : 0≤e*D := by
    have hh := (abs_nonneg (((incident S A v).card : ℝ)-D)).trans (hdeg v hv)
    linarith
  apply abs_le.mpr
  constructor <;> linarith

lemma matching_after_pruning (r : ℕ) (hr : 1≤r) {K₀ η : ℝ}
    (hK₀ : 0≤K₀) (hη : 0<η) :
    ∃ e T : ℝ, 0<e ∧ 0<T ∧
    ∀ {V E : Type} [DecidableEq V] [Fintype E] [DecidableEq E],
    ∀ (U B : Finset V) (S : Finset E) (A : E → Finset V) (D C : ℝ),
      B⊆U → T≤D → T≤((U\B).card : ℝ) → 0≤C → C≤e*D →
      U.card*C≤K₀*D → B.card*C≤e*D/2 →
      (∀ i∈S, A i⊆U) → (∀ i∈S, (A i).card=r) →
      (∀ v∈U\B, |((incident S A v).card : ℝ)-D|≤e*D/2) →
      (∀ v∈U, ∀ w∈U, v≠w → ((incident S A v∩incident S A w).card : ℝ)≤C) →
      ∃ M⊆S, (M : Set E).Pairwise (fun i j ↦ Disjoint (A i) (A j)) ∧
        (1-η)*((U\B).card : ℝ)≤r*(M.card : ℝ) := by
  obtain ⟨e,T,he,hT,h⟩ := almost_perfect_matching r hr hK₀ hη
  refine ⟨e,T,he,hT,?_⟩
  intro V E instV instF instE U B S A D C hB hD hn hC hCe hcode hsmall hsub hunif hdeg hpair
  have hcard : ((U\B).card : ℝ)≤U.card := Nat.cast_le.mpr (Finset.card_le_card Finset.sdiff_subset)
  obtain ⟨M,hM,hdis,hsize⟩ := h (U\B) (restrictEdges S A (U\B)) A D C hD hn hC hCe
    ((mul_le_mul_of_nonneg_right hcard hC).trans hcode)
    (fun i hi ↦ (Finset.mem_filter.mp hi).2)
    (fun i hi ↦ hunif i (Finset.mem_filter.mp hi).1)
    (pruned_degree_near U B S A hC hsub hdeg hpair hB hsmall) (by
      intro v hv w hw hvw
      apply (Nat.cast_le.mpr (Finset.card_le_card (show
        incident (restrictEdges S A (U\B)) A v∩incident (restrictEdges S A (U\B)) A w ⊆
          incident S A v∩incident S A w from ?_))).trans
        (hpair v (Finset.mem_sdiff.mp hv).1 w (Finset.mem_sdiff.mp hw).1 hvw)
      intro i hi
      simp only [Finset.mem_inter,incident_restrict,Finset.mem_filter] at hi ⊢
      exact ⟨hi.1.1,hi.2.1⟩)
  exact ⟨M,fun i hi ↦ (Finset.mem_filter.mp (hM hi)).1,hdis,hsize⟩

end
end AsymptoticallyMinimalLittlewood.Nibble

end OAI



namespace OAI

universe uΩ uI uΛ uK uA uJ uY

namespace AsymptoticallyMinimalLittlewood
namespace Packing
noncomputable section
open scoped BigOperators
open Finset

section Average
variable {Ω : Type uΩ} [Fintype Ω] [Nonempty Ω]

def avg (f : Ω → ℝ) : ℝ := (∑ ω, f ω)/(Fintype.card Ω)

lemma avg_const (c : ℝ) : avg (fun _ : Ω ↦ c) = c := by
  simp [avg, Fintype.card_ne_zero]
omit [Nonempty Ω] in
lemma avg_add (f g : Ω → ℝ) : avg (fun ω ↦ f ω+g ω)=avg f+avg g := by
  simp [avg,Finset.sum_add_distrib,add_div]
omit [Nonempty Ω] in
lemma avg_sub (f g : Ω → ℝ) : avg (fun ω ↦ f ω-g ω)=avg f-avg g := by
  simp [avg,Finset.sum_sub_distrib,sub_div]
omit [Nonempty Ω] in
lemma avg_mul_const (f : Ω → ℝ) (c : ℝ) : avg (fun ω ↦ f ω*c)=avg f*c := by
  simp [avg,← Finset.sum_mul]; ring
omit [Nonempty Ω] in
lemma avg_const_mul (c : ℝ) (f : Ω → ℝ) : avg (fun ω ↦ c*f ω)=c*avg f := by
  simpa only [mul_comm c] using avg_mul_const f c
omit [Nonempty Ω] in
lemma avg_mono {f g : Ω → ℝ} (h : ∀ ω, f ω≤g ω) : avg f≤avg g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun ω _ ↦ h ω)) (Nat.cast_nonneg _)
lemma avg_nonneg {f : Ω → ℝ} (h : ∀ ω, 0≤f ω) : 0≤avg f := by
  simpa only [avg_const] using avg_mono h
omit [Nonempty Ω] in
lemma avg_sum {I : Type uI} (S : Finset I) (f : I → Ω → ℝ) :
    avg (fun ω ↦ ∑ i ∈ S, f i ω)=∑ i ∈ S, avg (f i) := by
  dsimp [avg]
  rw [Finset.sum_comm,Finset.sum_div]
omit [Nonempty Ω] in
lemma avg_abs {f : Ω → ℝ} : |avg f|≤avg (fun ω ↦ |f ω|) := by
  have hc : |(Fintype.card Ω : ℝ)|=(Fintype.card Ω : ℝ) := abs_of_nonneg (Nat.cast_nonneg _)
  rw [avg,abs_div,hc]
  exact div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (Nat.cast_nonneg _)
lemma exists_le_avg (f : Ω → ℝ) : ∃ ω, f ω≤avg f := by
  have he : (∑ ω, f ω) = ∑ _ω : Ω, avg f := by
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,avg]
    field_simp
  obtain ⟨ω,_,h⟩ := Finset.exists_le_of_sum_le (Finset.univ_nonempty (α := Ω)) he.le
  exact ⟨ω,h⟩

omit [Nonempty Ω] in
lemma avg_comm {Λ : Type uΛ} [Fintype Λ] [Nonempty Λ] (f : Ω → Λ → ℝ) :
    avg (fun ω ↦ avg (f ω))=avg (fun x ↦ avg (fun ω ↦ f ω x)) := by
  dsimp [avg]
  simp only [← Finset.sum_div]
  rw [Finset.sum_comm]
  ring

omit [Nonempty Ω] in
lemma avg_prod_type {Λ : Type uΛ} [Fintype Λ] [Nonempty Λ] (f : Ω × Λ → ℝ) :
    avg f = avg (fun ω ↦ avg (fun x ↦ f (ω,x))) := by
  simp only [avg,Fintype.card_prod,Nat.cast_mul,Fintype.sum_prod_type,← Finset.sum_div]
  ring

lemma avg_prod_coordinate {K : Type uK} {A : Type uA} [Fintype K] [DecidableEq K] [Fintype A] [Nonempty A]
    (f : K → A → ℝ) : avg (fun ω : K → A ↦ ∏ k, f k (ω k)) = ∏ k, avg (f k) := by
  dsimp [avg]
  rw [← Fintype.prod_sum,Finset.prod_div_distrib]
  simp

lemma avg_prod_injective {K : Type uK} {J : Type uJ} {A : Type uA} [Fintype K] [DecidableEq K] [Fintype J] [Fintype A]
    [Nonempty A] (κ : J → K) (hκ : Function.Injective κ) (f : J → A → ℝ) :
    avg (fun ω : K → A ↦ ∏ j, f j (ω (κ j))) = ∏ j, avg (f j) := by
  classical
  let g : K → A → ℝ := fun k a ↦ if h : ∃ j, κ j=k then f h.choose a else 1
  have hg (j : J) (a : A) : g (κ j) a=f j a := by
    dsimp [g]
    split_ifs with h
    · congr 1
      exact hκ h.choose_spec
    · exact (h ⟨j,rfl⟩).elim
  have hprod (ω : K → A) : (∏ k, g k (ω k)) = ∏ j, f j (ω (κ j)) := by
    symm
    apply Fintype.prod_of_injective κ hκ
    · intro k hk
      simp [g,show ¬∃j, κ j=k from hk]
    · intro j
      exact (hg j (ω (κ j))).symm
  have hprod' : (∏ k, avg (g k)) = ∏ j, avg (f j) := by
    symm
    apply Fintype.prod_of_injective κ hκ
    · intro k hk
      simp [g,show ¬∃j,κ j=k from hk,avg_const]
    · intro j
      exact congrArg avg (funext (fun a ↦ (hg j a).symm))
  rw [← hprod']
  convert avg_prod_coordinate g using 1
  exact congrArg avg (funext (fun ω ↦ (hprod ω).symm))

/-- Good configurations contribute exactly c; all bad configurations carry
only a bounded contribution. This is the uniform first/second moment input. -/
lemma avg_error_on_bad (f : Ω → ℝ) (good : Ω → Prop) [DecidablePred good]
    {c : ℝ} (hc : 0≤c) (hc1 : c≤1) (hf : ∀ ω, 0≤f ω ∧ f ω≤1)
    (he : ∀ ω, good ω → f ω=c) :
    |avg f-c| ≤ avg (fun ω ↦ if good ω then 0 else 1) := by
  rw [← avg_const (Ω := Ω) c,← avg_sub]
  exact avg_abs.trans (avg_mono (fun ω ↦ by
    by_cases h : good ω
    · simp [h,he ω h]
    · simp only [h,ite_false]
      rw [abs_le]
      constructor <;> linarith [(hf ω).1,(hf ω).2]))

lemma avg_square_error {Z : Ω → ℝ} {p a : ℝ} (hp : 0≤p) (hp1 : p≤1)
    (hmean : |avg Z-p|≤a) (hsecond : |avg (fun ω ↦ Z ω^2)-p^2|≤a) :
    avg (fun ω ↦ (Z ω-p)^2) ≤ 3*a := by
  have he : avg (fun ω ↦ (Z ω-p)^2) =
      avg (fun ω ↦ Z ω^2)-2*p*avg Z+p^2 := by
    calc
      _ = avg (fun ω ↦ Z ω^2-(2*p)*Z ω+p^2) := by congr 1; funext ω; ring
      _ = _ := by rw [avg_add,avg_sub,avg_const_mul,avg_const]
  rw [he]
  have ha : 0≤a := (abs_nonneg _).trans hmean
  have hm := (abs_le.mp hmean).1
  have hs := (abs_le.mp hsecond).2
  nlinarith

omit [Nonempty Ω] in
lemma avg_chebyshev {Z : Ω → ℝ} (p : ℝ) {t : ℝ} (ht : 0<t) :
    avg (fun ω ↦ if t≤|Z ω-p| then 1 else 0) ≤
      avg (fun ω ↦ (Z ω-p)^2)/t^2 := by
  rw [le_div_iff₀ (sq_pos_of_pos ht),← avg_mul_const]
  apply avg_mono
  intro ω
  split_ifs with h
  · nlinarith [sq_abs (Z ω-p)]
  · simp only [zero_mul]; positivity

omit [Nonempty Ω] in
lemma avg_mul_avg {Λ : Type uΛ} [Fintype Λ] [Nonempty Λ]
    (f : Ω → ℝ) (g : Λ → ℝ) :
    avg f*avg g = avg (fun x : Ω × Λ ↦ f x.1*g x.2) := by
  rw [avg_prod_type]
  simp_rw [avg_const_mul,avg_mul_const]

omit [Nonempty Ω] in
lemma avg_square {Y : Type uY} [Fintype Y] [Nonempty Y] (f : Y → Ω → ℝ) :
    avg (fun ω ↦ (avg (fun y ↦ f y ω))^2) =
      avg (fun yy : Y × Y ↦ avg (fun ω ↦ f yy.1 ω*f yy.2 ω)) := by
  simp_rw [pow_two,avg_mul_avg]
  exact avg_comm _

/-- Unconditional moments suffice: pruning all atypical candidate centers
only enlarges the deleted set, so no conditional-probability axiom is used. -/
lemma moments_from_good {Y : Type uY} [Fintype Y] [Nonempty Y]
    (f : Y → Ω → ℝ) (good : Y → Prop) (good₂ : Y × Y → Prop)
    [DecidablePred good] [DecidablePred good₂] {p a : ℝ}
    (hp : 0≤p) (hp1 : p≤1) (hf : ∀ y ω, 0≤f y ω ∧ f y ω≤1)
    (hfirst : ∀ y, good y → avg (f y)=p)
    (hsecond : ∀ yy, good₂ yy → avg (fun ω ↦ f yy.1 ω*f yy.2 ω)=p^2)
    (hbad : avg (fun y ↦ if good y then 0 else 1)≤a)
    (hbad₂ : avg (fun yy ↦ if good₂ yy then 0 else 1)≤a) :
    avg (fun ω ↦ (avg (fun y ↦ f y ω)-p)^2) ≤ 3*a := by
  have hb (y) : 0≤avg (f y) ∧ avg (f y)≤1 :=
    ⟨avg_nonneg (fun ω ↦ (hf y ω).1),by
      rw [← avg_const (Ω := Ω) 1]; exact avg_mono (fun ω ↦ (hf y ω).2)⟩
  have hb₂ (yy : Y × Y) : 0≤avg (fun ω ↦ f yy.1 ω*f yy.2 ω) ∧
      avg (fun ω ↦ f yy.1 ω*f yy.2 ω)≤1 := by
    constructor
    · exact avg_nonneg (fun ω ↦ mul_nonneg (hf _ _).1 (hf _ _).1)
    · rw [← avg_const (Ω := Ω) 1]
      exact avg_mono (fun ω ↦ (mul_le_of_le_one_left (hf _ _).1 (hf _ _).2).trans (hf _ _).2)
  apply avg_square_error hp hp1
  · rw [avg_comm]
    exact (avg_error_on_bad _ good hp hp1 hb hfirst).trans hbad
  · rw [avg_square]
    exact (avg_error_on_bad _ good₂ (sq_nonneg _) (by nlinarith) hb₂ hsecond).trans hbad₂

lemma exists_few_bad_centers {I : Type uI} [Fintype I] (Z : I → Ω → ℝ)
    (p : ℝ) {t a : ℝ} (ht : 0<t)
    (hZ : ∀ i, avg (fun ω ↦ (Z i ω-p)^2)≤a) :
    ∃ ω, ((Finset.univ.filter (fun i ↦ t≤|Z i ω-p|)).card : ℝ) ≤
      Fintype.card I*a/t^2 := by
  classical
  let W : Ω → ℝ := fun ω ↦ ∑ i : I, if t≤|Z i ω-p| then 1 else 0
  obtain ⟨ω,hω⟩ := exists_le_avg W
  refine ⟨ω,?_⟩
  have he : ((Finset.univ.filter (fun i ↦ t≤|Z i ω-p|)).card : ℝ)=W ω := by
    simp [W,Finset.sum_boole]
  rw [he]
  apply hω.trans
  dsimp [W]
  rw [avg_sum]
  calc
    _ ≤ ∑ _i : I, a/t^2 := Finset.sum_le_sum (fun i _ ↦
      (avg_chebyshev p ht).trans (div_le_div_of_nonneg_right (hZ i) (sq_nonneg t)))
    _ = _ := by simp; ring

omit [Nonempty Ω] in
lemma avg_indicator {P : Ω → Prop} [DecidablePred P] :
    avg (fun ω ↦ if P ω then 1 else 0) =
      ((Finset.univ.filter P).card : ℝ)/Fintype.card Ω := by
  simp [avg,Finset.sum_boole]

omit [Nonempty Ω] in
lemma avg_bad_union {I : Type uI} (S : Finset I) (P : I → Ω → Prop)
    [∀ i, DecidablePred (P i)] :
    avg (fun ω ↦ if ∃ i∈S, P i ω then 1 else 0) ≤
      ∑ i∈S, avg (fun ω ↦ if P i ω then 1 else 0) := by
  classical
  rw [← avg_sum]
  apply avg_mono
  intro ω
  split_ifs with h
  · obtain ⟨i,hi,hP⟩ := h
    exact (show (1 : ℝ) ≤ (if P i ω then 1 else 0) by simp [hP]).trans
      (Finset.single_le_sum (f := fun j ↦ if P j ω then (1 : ℝ) else 0)
        (fun j _ ↦ by split_ifs <;> norm_num) hi)
  · exact Finset.sum_nonneg (fun j _ ↦ by split_ifs <;> norm_num)

end Average
end
end Packing
end AsymptoticallyMinimalLittlewood

end OAI



namespace OAI

universe uK uV uι uW uJ

namespace AsymptoticallyMinimalLittlewood
namespace Packing
noncomputable section
open scoped BigOperators
open Finset

section Linear
variable {K : Type uK} {V : Type uV} [Field K] [AddCommGroup V] [Module K V]

lemma functional_surjective {f : V →ₗ[K] K} (hf : f≠0) : Function.Surjective f := by
  obtain ⟨e,he⟩ : ∃ e, f e≠0 := by
    by_contra h; push Not at h; exact hf (LinearMap.ext h)
  intro a
  refine ⟨(a/f e) • e,?_⟩
  simp [he]

lemma nonparallel_pair_surjective {f g : V →ₗ[K] K} (hf : f≠0)
    (hfg : ∀ c : K, g≠c • f) : Function.Surjective (f.prod g) := by
  obtain ⟨e,he⟩ := functional_surjective hf (1 : K)
  have hk : ∃ y, f y=0 ∧ g y≠0 := by
    by_contra h
    push Not at h
    apply hfg (g e)
    ext x
    have hfx : f (x-f x • e)=0 := by simp [he]
    have hg := h _ hfx
    simp only [map_sub,map_smul,smul_eq_mul] at hg
    change g x=g e*f x
    exact (sub_eq_zero.mp hg).trans (mul_comm _ _)
  obtain ⟨y,hy,hgy⟩ := hk
  rintro ⟨a,b⟩
  refine ⟨a • e + ((b-a*g e)/g y) • y,?_⟩
  ext <;> simp [LinearMap.prod_apply,he,hy,hgy]

lemma pair_surjective_or_proportional {f g : V →ₗ[K] K} (hf : f≠0) :
    Function.Surjective (f.prod g) ∨ ∃ c : K, g=c • f := by
  classical
  by_cases h : ∃ c : K, g=c • f
  · exact Or.inr h
  · exact Or.inl (nonparallel_pair_surjective hf (by simpa using h))

def dotForm {ι : Type uι} [Fintype ι] (a : ι → K) : (ι → K) →ₗ[K] K where
  toFun := dotProduct a
  map_add' := fun x y ↦ dotProduct_add a x y
  map_smul' := fun c x ↦ by simp [dotProduct, Finset.mul_sum, mul_left_comm]

@[simp] lemma dotForm_apply {ι : Type uι} [Fintype ι] (a x : ι → K) :
    dotForm a x=dotProduct a x := rfl

lemma pair_surjective_of_minor {ι : Type uι} [Fintype ι]
    (a b : ι → K) {i j : ι} (h : a i*b j-a j*b i≠0) :
    Function.Surjective ((dotForm a).prod (dotForm b)) := by
  classical
  have ha : dotForm a≠0 := by
    intro hz
    have hai : a i=0 := by
      simpa using congrArg (fun f : (ι → K) →ₗ[K] K ↦ f (Pi.single i 1)) hz
    have haj : a j=0 := by
      simpa using congrArg (fun f : (ι → K) →ₗ[K] K ↦ f (Pi.single j 1)) hz
    exact h (by simp [hai,haj])
  apply nonparallel_pair_surjective ha
  intro c hc
  have hbi : b i=c*a i := by
    simpa using congrArg (fun f : (ι → K) →ₗ[K] K ↦ f (Pi.single i 1)) hc
  have hbj : b j=c*a j := by
    simpa using congrArg (fun f : (ι → K) →ₗ[K] K ↦ f (Pi.single j 1)) hc
  apply h
  rw [hbi,hbj]
  ring

lemma exists_nonzero_minor {ι : Type uι} (a b : ι → K)
    (ha : a≠0) (hnp : ∀ c : K, b≠c • a) :
    ∃ i j, a i*b j-a j*b i≠0 := by
  classical
  obtain ⟨i,hi⟩ : ∃ i, a i≠0 := by
    by_contra h; push Not at h; exact ha (funext h)
  by_contra h
  push Not at h
  apply hnp (b i/a i)
  ext j
  have he := h i j
  change b j=(b i/a i)*a j
  field_simp
  linear_combination he

end Linear

section Counting
variable {V : Type uV} {W : Type uW} [AddGroup V] [AddGroup W] [Fintype V] [Fintype W]
  [DecidableEq V] [DecidableEq W]

def fiber (f : V → W) (w : W) : Finset V := Finset.univ.filter (fun v ↦ f v=w)

omit [AddGroup V] [AddGroup W] [Fintype W] [DecidableEq V] in
@[simp] lemma mem_fiber {f : V → W} {v : V} {w : W} : v∈fiber f w ↔ f v=w := by
  simp [fiber]

omit [Fintype W] [DecidableEq V] in
lemma fiber_card_eq (f : V →+ W) (hf : Function.Surjective f) (x y : W) :
    (fiber f x).card=(fiber f y).card :=
  AddMonoidHom.card_fiber_eq_of_mem_range f (hf x) (hf y)

omit [DecidableEq V] in
lemma fiber_card_mul (f : V →+ W) (hf : Function.Surjective f) (w : W) :
    Fintype.card W*(fiber f w).card=Fintype.card V := by
  have hc : Fintype.card V=∑ y : W, (fiber f y).card := by
    simpa only [Finset.card_univ,fiber] using
      (Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset V))
        (t := (Finset.univ : Finset W)) (f := f) (by simp))
  simp_rw [fiber_card_eq f hf _ w] at hc
  simpa using hc.symm

omit [Fintype W] [DecidableEq V] in
lemma fiber_nonempty (f : V →+ W) (hf : Function.Surjective f) (w : W) :
    (fiber f w).Nonempty := by
  obtain ⟨v,hv⟩ := hf w
  exact ⟨v,by simp [hv]⟩

omit [DecidableEq V] in
lemma fiber_le_card (f : V →+ W) (hf : Function.Surjective f) (w : W) :
    Fintype.card W ≤ Fintype.card V := by
  rw [← fiber_card_mul f hf w]
  exact Nat.le_mul_of_pos_right _ (fiber_nonempty f hf w).card_pos

end Counting

section PairCounting
variable {K : Type uK} {V : Type uV} [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Module K V] [Fintype V] [DecidableEq V]

omit [Fintype K] [DecidableEq V] in
lemma joint_fiber_eq (f g : V →ₗ[K] K) (s t : K) :
    (fiber f s).filter (fun v ↦ g v=t) = fiber (f.prod g) (s,t) := by
  ext v
  simp [fiber,Prod.ext_iff]

omit [Fintype K] [DecidableEq V] in
lemma conditional_fiber_card (f g : V →ₗ[K] K)
    (hfg : Function.Surjective (f.prod g)) (s t u : K) :
    ((fiber f s).filter (fun v ↦ g v=t)).card =
    ((fiber f s).filter (fun v ↦ g v=u)).card := by
  simp only [joint_fiber_eq]
  exact fiber_card_eq (f.prod g).toAddMonoidHom hfg _ _

omit [DecidableEq V] in
lemma conditional_fiber_count (f g : V →ₗ[K] K)
    (hfg : Function.Surjective (f.prod g)) (s t : K) :
    Fintype.card K*((fiber f s).filter (fun v ↦ g v=t)).card=(fiber f s).card := by
  have h := Finset.card_eq_sum_card_fiberwise (s := fiber f s)
    (t := (Finset.univ : Finset K)) (f := g) (by simp)
  simp_rw [conditional_fiber_card f g hfg s _ t] at h
  simpa using h.symm

omit [Fintype K] [DecidableEq V] in
lemma conditional_card_event (f g : V →ₗ[K] K)
    (hfg : Function.Surjective (f.prod g)) (s : K) (S : Finset K) :
    ((fiber f s).filter (fun v ↦ g v∈S)).card =
      S.card*((fiber f s).filter (fun v ↦ g v=0)).card := by
  have h := Finset.card_eq_sum_card_fiberwise
    (s := (fiber f s).filter (fun v ↦ g v∈S)) (t := S) (f := g)
    (by intro v hv; exact (Finset.mem_filter.mp hv).2)
  have he (t : K) (ht : t ∈ S) :
      (((fiber f s).filter (fun v ↦ g v∈S)).filter (fun v ↦ g v=t))=
      ((fiber f s).filter (fun v ↦ g v=t)) := by
    ext v
    simp only [Finset.mem_filter]
    constructor
    · exact fun h ↦ ⟨h.1.1,h.2⟩
    · rintro ⟨hv,hv'⟩; exact ⟨⟨hv,hv' ▸ ht⟩,hv'⟩
  rw [h]
  calc
    _ = ∑ _t ∈ S, ((fiber f s).filter (fun v ↦ g v=0)).card := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [he t ht,conditional_fiber_card f g hfg s t 0]
    _ = _ := by simp

lemma scalar_preimage_card {c : K} (hc : c≠0) (S : Finset K) :
    (Finset.univ.filter (fun s : K ↦ c*s∈S)).card≤S.card := by
  apply Finset.card_le_card_of_injOn (fun s ↦ c*s)
  · intro s hs
    exact (Finset.mem_filter.mp hs).2
  · intro s hs t ht hst
    exact mul_left_cancel₀ hc hst

omit [DecidableEq V] in
/-- The exceptional centers have a concrete linear bound in the size of the
short-residue set. No joint independence of three or more rows is asserted. -/
lemma exceptional_centers {J : Type uJ} [Fintype J] [DecidableEq J]
    (f : J → V →ₗ[K] K) (hpair : ∀ j l, j≠l → Function.Surjective ((f j).prod (f l)))
    (i : J) (hfi : f i≠0) (S : Finset K) :
    ∃ E : Finset K, E.card≤2*(Fintype.card J)^2*S.card ∧
      ∀ s : K, s∉E → ∀ j l, j≠l → ∀ e : Bool,
      Function.Surjective ((f i).prod (if e then f j+f l else f j-f l)) ∨
      ∃ c : K, (if e then f j+f l else f j-f l)=c • f i ∧ c*s∉S := by
  classical
  let g : (J × J) × Bool → V →ₗ[K] K := fun a ↦
    if a.2 then f a.1.1+f a.1.2 else f a.1.1-f a.1.2
  let E₀ : (J × J) × Bool → Finset K := fun a ↦
    if h : ∃ c : K, c≠0 ∧ g a=c • f i then
      Finset.univ.filter (fun s ↦ h.choose*s∈S) else ∅
  let E := Finset.univ.biUnion E₀
  have hcard (a) : (E₀ a).card≤S.card := by
    dsimp [E₀]
    split_ifs with h
    · exact scalar_preimage_card h.choose_spec.1 S
    · simp
  have hE : E.card≤2*(Fintype.card J)^2*S.card := by
    calc
      _ ≤ ∑ a : (J × J) × Bool, (E₀ a).card := Finset.card_biUnion_le
      _ ≤ ∑ _a : (J × J) × Bool, S.card := Finset.sum_le_sum (fun a _ ↦ hcard a)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
          Fintype.card_bool, nsmul_eq_mul, Nat.cast_id]; ring
  refine ⟨E,hE,?_⟩
  intro s hs j l hjl e
  let a : (J × J) × Bool := ((j,l),e)
  have hg : g a≠0 := by
    obtain ⟨v,hv⟩ := hpair j l hjl (1,0)
    have hvj : f j v=1 := congrArg Prod.fst hv
    have hvl : f l v=0 := congrArg Prod.snd hv
    intro hz
    have hz' := congrArg (fun h : V →ₗ[K] K ↦ h v) hz
    cases e <;> simp [g,a,hvj,hvl] at hz'
  rcases pair_surjective_or_proportional (g := g a) hfi with h | ⟨c,hc⟩
  · exact Or.inl h
  · have hc0 : c≠0 := by intro hz; apply hg; simp [hc,hz]
    refine Or.inr ⟨c,hc,?_⟩
    have hex : ∃ d : K, d≠0 ∧ g a=d • f i := ⟨c,hc0,hc⟩
    have hec : hex.choose=c := by
      obtain ⟨v,hv⟩ := functional_surjective hfi 1
      have hh := congrArg (fun h : V →ₗ[K] K ↦ h v) (hex.choose_spec.2.symm.trans hc)
      simpa [hv] using hh
    intro hcs
    apply hs
    apply Finset.mem_biUnion.mpr
    refine ⟨a,Finset.mem_univ _,?_⟩
    dsimp [E₀]
    rw [dif_pos hex]
    simp [hec,hcs]

end PairCounting
section PrimeRanks

lemma int_cast_ne_zero_of_large_prime {q : ℕ} [Fact q.Prime] {z : ℤ}
    (hz : z≠0) (hq : z.natAbs<q) : (z : ZMod q)≠0 := by
  intro h
  have hd : (q : ℤ) ∣ z := (ZMod.intCast_zmod_eq_zero_iff_dvd z q).mp h
  apply hz
  exact Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd (by simpa using hq)

lemma pair_surjective_integer_minor {ι : Type uι} [Fintype ι]
    (a b : ι → ℤ) {i j : ι} (h : a i*b j-a j*b i≠0)
    {q : ℕ} [Fact q.Prime] (hq : (a i*b j-a j*b i).natAbs<q) :
    Function.Surjective ((dotForm (fun k ↦ (a k : ZMod q))).prod
      (dotForm (fun k ↦ (b k : ZMod q)))) := by
  apply pair_surjective_of_minor (i := i) (j := j)
  convert int_cast_ne_zero_of_large_prime h hq using 1 ; push_cast ; rfl

/-- The excluded-prime set is replaced by a concrete size threshold; this
suffices because only existence of one sufficiently large prime is needed. -/
lemma integer_rows_eventual_pair_rank {ι : Type uι} {J : Type uJ} [Fintype ι] [Fintype J]
    (a : J → ι → ℤ)
    (ha : ∀ j, (fun k ↦ (a j k : ℚ)) ≠ 0)
    (hnp : ∀ j l, j≠l → ∀ c : ℚ,
      (fun k ↦ (a l k : ℚ)) ≠ c • (fun k ↦ (a j k : ℚ))) :
    ∃ Q : ℕ, ∀ q : ℕ, ∀ (_hq : Fact q.Prime), Q<q →
      ∀ j l, j≠l → Function.Surjective
        ((dotForm (fun k ↦ (a j k : ZMod q))).prod
         (dotForm (fun k ↦ (a l k : ZMod q)))) := by
  classical
  let Q := ∑ j : J, ∑ l : J, ∑ k : ι, ∑ h : ι, (a j k*a l h-a j h*a l k).natAbs
  refine ⟨Q,?_⟩
  intro q hq hQ j l hjl
  obtain ⟨k,h,hm⟩ := exists_nonzero_minor (fun k ↦ (a j k : ℚ))
    (fun k ↦ (a l k : ℚ)) (ha j) (hnp j l hjl)
  have hi : a j k*a l h-a j h*a l k≠0 := by
    intro hz
    apply hm
    exact_mod_cast hz
  apply pair_surjective_integer_minor _ _ hi
  apply lt_of_le_of_lt _ hQ
  calc
    _ ≤ ∑ h : ι, (a j k*a l h-a j h*a l k).natAbs :=
      Finset.single_le_sum (f := fun h : ι ↦ (a j k*a l h-a j h*a l k).natAbs)
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ h)
    _ ≤ ∑ k : ι, ∑ h : ι, (a j k*a l h-a j h*a l k).natAbs :=
      Finset.single_le_sum (f := fun k : ι ↦ ∑ h : ι, (a j k*a l h-a j h*a l k).natAbs)
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ k)
    _ ≤ ∑ l : J, ∑ k : ι, ∑ h : ι, (a j k*a l h-a j h*a l k).natAbs :=
      Finset.single_le_sum (f := fun l : J ↦ ∑ k : ι, ∑ h : ι, (a j k*a l h-a j h*a l k).natAbs)
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ l)
    _ ≤ Q := by
      dsimp [Q]
      exact Finset.single_le_sum (f := fun j : J ↦ ∑ l : J, ∑ k : ι, ∑ h : ι, (a j k*a l h-a j h*a l k).natAbs)
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ j)

end PrimeRanks

end
end Packing
end AsymptoticallyMinimalLittlewood

end OAI



namespace OAI

universe uJ

namespace AsymptoticallyMinimalLittlewood
namespace Packing
noncomputable section
open scoped BigOperators
open Finset

lemma choose_odd_lengths {J : Type uJ} [Fintype J] [Nonempty J]
    (w : J → ℝ) (hw : ∀ j, 0<w j) (hs : 2*∑ j, w j<1) :
    ∃ d : J → ℕ, ∀ i, w i < (2*(d i : ℝ)+1)/(2*∑ j, (2*(d j : ℝ)+1)) := by
  let r : ℝ := Fintype.card J
  have hr : 0<r := Nat.cast_pos.mpr Fintype.card_pos
  let M : ℝ := (3*r+1)/(1-2*∑ j, w j)
  have hM : 0<M := by dsimp [M]; positivity
  let d : J → ℕ := fun j ↦ ⌈M*w j⌉₊
  have hdi (i : J) : M*w i ≤ (d i : ℝ) := Nat.le_ceil _
  have hdi' (i : J) : (d i : ℝ)<M*w i+1 := Nat.ceil_lt_add_one (mul_pos hM (hw i)).le
  have hL : (∑ j, (2*(d j : ℝ)+1)) < M := by
    have hlt : (∑ j, (2*(d j : ℝ)+1)) < ∑ j, (2*(M*w j)+3) := by
      apply Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty)
      intro j _; linarith [hdi' j]
    have he : (∑ j, (2*(M*w j)+3)) = 2*M*(∑ j, w j)+3*r := by
      simp only [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,
        Finset.card_univ,nsmul_eq_mul]
      dsimp [r]; ring
    rw [he] at hlt
    have heM : M*(1-2*∑ j, w j)=3*r+1 := by
      dsimp [M]; field_simp [ne_of_gt (sub_pos.mpr hs)]
    nlinarith
  refine ⟨d,?_⟩
  intro i
  have hL0 : 0<(∑ j, (2*(d j : ℝ)+1)) :=
    Finset.sum_pos (fun j _ ↦ by positivity) Finset.univ_nonempty
  rw [lt_div_iff₀ (by positivity)]
  have hmul := mul_lt_mul_of_pos_right hL (hw i)
  nlinarith [hdi i]

variable {r : ℕ}
def slotPrefix (L : Fin r → ℕ) (i : Fin r) : ℕ := ∑ j ∈ Finset.Iio i, L j

def periodLength (L : Fin r → ℕ) : ℕ := ∑ j, L j

lemma prefix_add_length_le (L : Fin r → ℕ) (i : Fin r) :
    slotPrefix L i+L i ≤ periodLength L := by
  classical
  have hi : i∉Finset.Iio i := by simp
  dsimp [slotPrefix,periodLength]
  rw [add_comm,← Finset.sum_insert hi]
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)

lemma prefix_separated (L : Fin r → ℕ) {i j : Fin r} (hij : i<j) :
    slotPrefix L i+L i ≤ slotPrefix L j := by
  classical
  have hi : i∉Finset.Iio i := by simp
  change (∑ k ∈ Finset.Iio i, L k)+L i ≤ ∑ k ∈ Finset.Iio j, L k
  rw [add_comm,← Finset.sum_insert hi]
  apply Finset.sum_le_sum_of_subset
  intro k hk
  rcases Finset.mem_insert.mp hk with h | h
  · subst k; simpa using hij
  · exact Finset.mem_Iio.mpr (lt_trans (Finset.mem_Iio.mp h) hij)

/-- Site immediately to the left of a slot. The actual sites are
left+1,...,left+L_i. Each full chunk keeps R-1 translated periods. -/
def slotLeft (L : Fin r → ℕ) (R : ℕ) (shift chunk period : ℕ) (i : Fin r) : ℕ :=
  chunk*(R*periodLength L)+period*periodLength L+shift+slotPrefix L i

lemma slotLeft_bounds (L : Fin r → ℕ) (R : ℕ) {shift chunk period : ℕ}
    (hs : shift<periodLength L) (hp : period+1<R) (i : Fin r) :
    chunk*(R*periodLength L) ≤ slotLeft L R shift chunk period i ∧
    slotLeft L R shift chunk period i+L i < (chunk+1)*(R*periodLength L) := by
  have hi := prefix_add_length_le L i
  have hp' : (period+2)*periodLength L ≤ R*periodLength L :=
    Nat.mul_le_mul_right _ (by omega)
  dsimp [slotLeft]
  constructor
  · omega
  · simp only [Nat.add_mul] at hp' ⊢
    omega

lemma slots_separated_same_chunk (L : Fin r → ℕ) (R shift chunk : ℕ)
    {p q : ℕ} {i j : Fin r} (h : p<q ∨ p=q ∧ i<j) :
    slotLeft L R shift chunk p i+L i ≤ slotLeft L R shift chunk q j := by
  have hi := prefix_add_length_le L i
  dsimp [slotLeft]
  rcases h with h | ⟨rfl,h⟩
  · have hp : (p+1)*periodLength L ≤ q*periodLength L :=
      Nat.mul_le_mul_right _ (by omega)
    simp only [Nat.add_mul,Nat.one_mul] at hp
    omega
  · have hj := prefix_separated L h
    omega

lemma slots_separated_chunks (L : Fin r → ℕ) (R : ℕ) {s t k l p q : ℕ}
    (hs : s<periodLength L) (hp : p+1<R) (hkl : k<l) (i j : Fin r) :
    slotLeft L R s k p i+L i < slotLeft L R t l q j := by
  have hleft := (slotLeft_bounds L R (chunk := k) hs hp i).2
  have hle : (k+1)*(R*periodLength L) ≤ l*(R*periodLength L) :=
    Nat.mul_le_mul_right _ (by omega)
  dsimp [slotLeft] at *
  omega

def signedSite (q : ℕ) (e : Bool) (x : ℕ) : ZMod q := if e then x else -x

lemma signedSite_injective {q A x y : ℕ} (hq : 2*A<q)
    (hx : 0<x) (hxA : x≤A) (hy : 0<y) (hyA : y≤A) (e f : Bool) :
    signedSite q e x=signedSite q f y ↔ e=f ∧ x=y := by
  have hxy : x+y<q := by omega
  have hn : (x : ZMod q)≠-(y : ZMod q) := by
    intro h
    have hz : ((x+y : ℕ) : ZMod q)=0 := by push_cast; rw [h]; simp
    have hd := (ZMod.natCast_eq_zero_iff _ _).mp hz
    have he := Nat.eq_zero_of_dvd_of_lt hd hxy
    omega
  have heq : (x : ZMod q)=(y : ZMod q) ↔ x=y := by
    rw [ZMod.natCast_eq_natCast_iff']
    rw [Nat.mod_eq_of_lt (by omega : x<q),Nat.mod_eq_of_lt (by omega : y<q)]
  cases e <;> cases f <;> simp [signedSite,heq,hn, neg_eq_iff_eq_neg]

abbrev oddLengths (d : Fin r → ℕ) : Fin r → ℕ := fun i ↦ 2*d i+1

def siteCenter (d : Fin r → ℕ) (R shift chunk period : ℕ) (i : Fin r) : ℕ :=
  slotLeft (oddLengths d) R shift chunk period i+d i+1

lemma periodLength_pos (d : Fin r → ℕ) (i : Fin r) : 0<periodLength (oddLengths d) := by
  have h := prefix_add_length_le (oddLengths d) i
  dsimp [oddLengths] at h
  omega

lemma centerOffset_bounds (d : Fin r → ℕ) (i : Fin r) :
    0<slotPrefix (oddLengths d) i+d i+1 ∧
    slotPrefix (oddLengths d) i+d i+1≤periodLength (oddLengths d) := by
  have h := prefix_add_length_le (oddLengths d) i
  dsimp [oddLengths] at h
  omega

lemma siteCenter_bounds (d : Fin r → ℕ) {R shift chunk period : ℕ}
    (hs : shift<periodLength (oddLengths d)) (hp : period+1<R) (i : Fin r) :
    chunk*(R*periodLength (oddLengths d)) < siteCenter d R shift chunk period i ∧
    siteCenter d R shift chunk period i < (chunk+1)*(R*periodLength (oddLengths d)) := by
  obtain ⟨hlo,hhi⟩ := slotLeft_bounds (oddLengths d) R (chunk := chunk) hs hp i
  dsimp [siteCenter,oddLengths] at *
  omega

lemma siteCenter_chunk (d : Fin r → ℕ) {R shift chunk period : ℕ}
    (hs : shift<periodLength (oddLengths d)) (hp : period+1<R) (i : Fin r) :
    siteCenter d R shift chunk period i / (R*periodLength (oddLengths d)) = chunk := by
  have hR : 0<R := by omega
  have hL := periodLength_pos d i
  have hc := (siteCenter_bounds d (chunk := 0) hs hp i).2
  dsimp [siteCenter,slotLeft] at hc ⊢
  simp only [Nat.zero_mul,Nat.zero_add,Nat.zero_add,Nat.one_mul] at hc
  have he : chunk*(R*periodLength (oddLengths d))+period*periodLength (oddLengths d)+shift+
      slotPrefix (oddLengths d) i+d i+1 =
      (period*periodLength (oddLengths d)+shift+slotPrefix (oddLengths d) i+d i+1)+
      chunk*(R*periodLength (oddLengths d)) := by omega
  rw [he,Nat.add_mul_div_right _ _ (mul_pos hR hL),Nat.div_eq_of_lt hc]
  simp

lemma interior_center_exists (d : Fin r → ℕ) {R t : ℕ}
    (ht : t<(R-2)*periodLength (oddLengths d)) (i : Fin r) :
    ∃ p s : ℕ, p+1<R ∧ s<periodLength (oddLengths d) ∧
      p*periodLength (oddLengths d)+s+slotPrefix (oddLengths d) i+d i+1 =
        periodLength (oddLengths d)+1+t := by
  let L := periodLength (oddLengths d)
  let c := slotPrefix (oddLengths d) i+d i+1
  have hL : 0<L := periodLength_pos d i
  have hc := centerOffset_bounds d i
  change 0<c ∧ c≤L at hc
  let u := L+1+t-c
  have hR : 2<R := by
    by_contra h
    have he : R-2=0 := by omega
    rw [he,Nat.zero_mul] at ht
    omega
  have hu : u<(R-1)*L := by
    have he : (R-1)*L=(R-2)*L+L := by
      rw [show R-1=(R-2)+1 by omega,Nat.add_mul,Nat.one_mul]
    dsimp [u,L] at *
    omega
  refine ⟨u/L,u%L,?_,Nat.mod_lt _ hL,?_⟩
  · have hh := (Nat.div_lt_iff_lt_mul hL).mpr hu
    omega
  · have he := Nat.mod_add_div u L
    rw [Nat.mul_comm L] at he
    have hcu : c≤L+1+t := by omega
    dsimp [u,c,L] at *
    omega

def interiorSite (d : Fin r → ℕ) (R k t : ℕ) : ℕ :=
  k*(R*periodLength (oddLengths d))+periodLength (oddLengths d)+1+t

lemma interiorSite_bounds (d : Fin r → ℕ) {R k t : ℕ} (i : Fin r)
    (ht : t<(R-2)*periodLength (oddLengths d)) :
    k*(R*periodLength (oddLengths d)) < interiorSite d R k t ∧
    interiorSite d R k t < (k+1)*(R*periodLength (oddLengths d)) := by
  obtain ⟨p,s,hp,hs,he⟩ := interior_center_exists d ht i
  have he' : interiorSite d R k t=siteCenter d R s k p i := by
    dsimp [interiorSite,siteCenter,slotLeft]
    omega
  rw [he']
  exact siteCenter_bounds d hs hp i

lemma interiorSite_chunk (d : Fin r → ℕ) {R k t : ℕ} (i : Fin r)
    (ht : t<(R-2)*periodLength (oddLengths d)) :
    interiorSite d R k t/(R*periodLength (oddLengths d))=k := by
  obtain ⟨p,s,hp,hs,he⟩ := interior_center_exists d ht i
  have he' : interiorSite d R k t=siteCenter d R s k p i := by
    dsimp [interiorSite,siteCenter,slotLeft]
    omega
  rw [he']
  exact siteCenter_chunk d hs hp i

lemma interior_signed_injective (d : Fin r → ℕ) (R K q : ℕ) (i : Fin r)
    (hq : 2*(K*(R*periodLength (oddLengths d)))<q) :
    Function.Injective (fun x : (Fin K × Fin ((R-2)*periodLength (oddLengths d))) × Bool ↦
      signedSite q x.2 (interiorSite d R x.1.1 x.1.2)) := by
  rintro ⟨⟨k,t⟩,e⟩ ⟨⟨l,u⟩,f⟩ he
  have hk := interiorSite_bounds d (k := (k : ℕ)) i t.isLt
  have hl := interiorSite_bounds d (k := (l : ℕ)) i u.isLt
  have hk' : interiorSite d R k t ≤ K*(R*periodLength (oddLengths d)) :=
    hk.2.le.trans (Nat.mul_le_mul_right _ (by omega))
  have hl' : interiorSite d R l u ≤ K*(R*periodLength (oddLengths d)) :=
    hl.2.le.trans (Nat.mul_le_mul_right _ (by omega))
  obtain ⟨hef,he'⟩ := (signedSite_injective hq (by omega) hk' (by omega) hl' e f).mp he
  have hkl : (k : ℕ)=(l : ℕ) := by
    have hc := congrArg (fun c ↦ c/(R*periodLength (oddLengths d))) he'
    simpa only [interiorSite_chunk d i t.isLt,interiorSite_chunk d i u.isLt] using hc
  have htu : (t : ℕ)=(u : ℕ) := by
    dsimp [interiorSite] at he'
    rw [hkl] at he'
    omega
  cases Fin.ext hkl
  cases Fin.ext htu
  cases hef
  rfl

abbrev SlotChoices (d : Fin r → ℕ) (K : ℕ) :=
  Fin K → Fin (periodLength (oddLengths d)) × Bool

def slotHit (d : Fin r → ℕ) (R K q : ℕ) (i : Fin r)
    (ω : SlotChoices d K) (u : ZMod q) : Prop :=
  ∃ k : Fin K, ∃ p : Fin (R-1),
    u=signedSite q (ω k).2 (siteCenter d R (ω k).1 k p i)

lemma interior_hit_coordinate (d : Fin r → ℕ) (R K q : ℕ) (i : Fin r)
    (hq : 2*(K*(R*periodLength (oddLengths d)))<q)
    (k : Fin K) (t : Fin ((R-2)*periodLength (oddLengths d))) (e : Bool) :
    ∃ s : Fin (periodLength (oddLengths d)), ∀ ω : SlotChoices d K,
      slotHit d R K q i ω (signedSite q e (interiorSite d R k t)) ↔ ω k=(s,e) := by
  obtain ⟨p,s,hp,hs,he⟩ := interior_center_exists d t.isLt i
  let p₀ : Fin (R-1) := ⟨p,by omega⟩
  let s₀ : Fin (periodLength (oddLengths d)) := ⟨s,hs⟩
  have he' : interiorSite d R k t=siteCenter d R s₀ k p₀ i := by
    dsimp [interiorSite,siteCenter,slotLeft,s₀,p₀]
    omega
  refine ⟨s₀,?_⟩
  intro ω
  constructor
  · rintro ⟨l,u,hu⟩
    have hk := interiorSite_bounds d (k := (k : ℕ)) i t.isLt
    have hl := siteCenter_bounds d (R := R) (chunk := (l : ℕ)) (period := (u : ℕ)) (ω l).1.isLt (by have := u.isLt; omega) i
    have hk' : interiorSite d R k t≤K*(R*periodLength (oddLengths d)) :=
      hk.2.le.trans (Nat.mul_le_mul_right _ (by omega))
    have hl' : siteCenter d R (ω l).1 l u i≤K*(R*periodLength (oddLengths d)) :=
      hl.2.le.trans (Nat.mul_le_mul_right _ (by omega))
    obtain ⟨hes,hc⟩ := (signedSite_injective hq (by omega) hk' (by omega) hl' e (ω l).2).mp hu
    have hkl : (k : ℕ)=(l : ℕ) := by
      have hc' := congrArg (fun n ↦ n/(R*periodLength (oddLengths d))) hc
      simpa only [interiorSite_chunk d i t.isLt,
        siteCenter_chunk d (R := R) (period := (u : ℕ)) (ω l).1.isLt (by have := u.isLt; omega) i] using hc'
    have hkl' : k=l := Fin.ext hkl
    subst l
    have hp' : p*periodLength (oddLengths d)+s=
        (u : ℕ)*periodLength (oddLengths d)+(ω k).1 := by
      rw [he'] at hc
      dsimp [siteCenter,slotLeft,p₀,s₀] at hc
      omega
    have hmod := congrArg (fun n ↦ n%periodLength (oddLengths d)) hp'
    rw [Nat.add_mod, Nat.mul_mod_left, Nat.zero_add, Nat.mod_mod,
      Nat.mod_eq_of_lt hs, Nat.add_mod, Nat.mul_mod_left, Nat.zero_add,
      Nat.mod_mod, Nat.mod_eq_of_lt (ω k).1.isLt] at hmod
    apply Prod.ext
    · exact Fin.ext hmod.symm
    · exact hes.symm
  · intro hω
    refine ⟨k,p₀,?_⟩
    rw [hω]
    exact congrArg (signedSite q e) he'

/-- The finite residue neighborhood used to detect same-chunk collisions. -/
def shortResidues (q B : ℕ) : Finset (ZMod q) :=
  (Finset.Icc (-(B : ℤ)) B).image (fun c : ℤ ↦ (c : ZMod q))

lemma shortResidues_card (q B : ℕ) : (shortResidues q B).card≤2*B+1 := by
  apply Finset.card_image_le.trans
  simp [Int.card_Icc]
  omega

lemma same_chunk_collision (d : Fin r → ℕ) (R q : ℕ) (i : Fin r)
    {k t u : ℕ} (ht : t<(R-2)*periodLength (oddLengths d))
    (hu : u<(R-2)*periodLength (oddLengths d)) (e f : Bool) :
    signedSite q e (interiorSite d R k t)+signedSite q f (interiorSite d R k u)
      ∈shortResidues q (R*periodLength (oddLengths d)) ∨
    signedSite q e (interiorSite d R k t)-signedSite q f (interiorSite d R k u)
      ∈shortResidues q (R*periodLength (oddLengths d)) := by
  have ht' := interiorSite_bounds d (k := k) i ht
  have hu' := interiorSite_bounds d (k := k) i hu
  simp only [Nat.add_mul, Nat.one_mul] at ht' hu'
  let a : ℤ := interiorSite d R k t
  let b : ℤ := interiorSite d R k u
  have hdiff : a-b∈Finset.Icc (-(R*periodLength (oddLengths d) : ℕ) : ℤ)
      (R*periodLength (oddLengths d)) := by
    simp only [Finset.mem_Icc]
    dsimp [a,b]

    constructor <;> omega
  have hdiff' : b-a∈Finset.Icc (-(R*periodLength (oddLengths d) : ℕ) : ℤ)
      (R*periodLength (oddLengths d)) := by
    simp only [Finset.mem_Icc] at hdiff ⊢
    constructor <;> omega
  have hd : ((a-b : ℤ) : ZMod q)∈shortResidues q (R*periodLength (oddLengths d)) :=
    Finset.mem_image.mpr ⟨a-b,hdiff,rfl⟩
  have hd' : ((b-a : ℤ) : ZMod q)∈shortResidues q (R*periodLength (oddLengths d)) :=
    Finset.mem_image.mpr ⟨b-a,hdiff',rfl⟩
  dsimp [a,b] at hd hd'
  push_cast at hd hd'
  cases e <;> cases f <;> simp only [signedSite,Bool.false_eq_true,↓reduceIte]
  · exact Or.inr (by simpa only [sub_eq_add_neg,neg_neg,add_comm] using hd')
  · exact Or.inl (by simpa only [sub_eq_add_neg,add_comm] using hd')
  · exact Or.inl (by simpa only [sub_eq_add_neg] using hd)
  · exact Or.inr hd

end
end Packing
end AsymptoticallyMinimalLittlewood

namespace AsymptoticallyMinimalLittlewood.Packing
noncomputable section
open scoped BigOperators
open Finset
variable {r : ℕ}

abbrev InteriorCatalog (d : Fin r → ℕ) (R K : ℕ) :=
  Fin K × Fin ((R-2)*periodLength (oddLengths d)) × Bool

def catalogValue (d : Fin r → ℕ) (R K q : ℕ) (c : InteriorCatalog d R K) : ZMod q :=
  signedSite q c.2.2 (interiorSite d R c.1 c.2.1)

def catalogSet (d : Fin r → ℕ) (R K q : ℕ) : Finset (ZMod q) :=
  Finset.univ.image (catalogValue d R K q)

lemma catalogValue_injective (d : Fin r → ℕ) (R K q : ℕ) (i : Fin r)
    (hq : 2*(K*(R*periodLength (oddLengths d)))<q) :
    Function.Injective (catalogValue d R K q) := by
  rintro ⟨k,t,b⟩ ⟨l,u,e⟩ h
  have hh : ((k,t),b)=((l,u),e) := interior_signed_injective d R K q i hq h
  obtain ⟨hkt,hbe⟩ := Prod.mk.inj hh
  cases hkt
  cases hbe
  rfl

lemma catalogSet_card (d : Fin r → ℕ) (R K q : ℕ) (i : Fin r)
    (hq : 2*(K*(R*periodLength (oddLengths d)))<q) :
    (catalogSet d R K q).card=2*K*((R-2)*periodLength (oddLengths d)) := by
  rw [catalogSet,Finset.card_image_of_injective _ (catalogValue_injective d R K q i hq)]
  simp only [Finset.card_univ,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool]
  ring

lemma catalog_chunk_system (d : Fin r → ℕ) (R K q : ℕ) [NeZero q] (i₀ : Fin r)
    (hK : 0<K) (hq : 2*(K*(R*periodLength (oddLengths d)))<q) :
    ∃ chunk : ZMod q → Fin K,
      (∀ c : InteriorCatalog d R K, chunk (catalogValue d R K q c)=c.1) ∧
      (∀ i t, t∈catalogSet d R K q →
        ∃ a : Fin (periodLength (oddLengths d)) × Bool,
          ∀ ω : SlotChoices d K, slotHit d R K q i ω t ↔ ω (chunk t)=a) ∧
      (∀ k, (Finset.univ.filter (fun t : ZMod q ↦ chunk t=k)).card≤
        q-(catalogSet d R K q).card+2*((R-2)*periodLength (oddLengths d))) ∧
      (∀ t∈catalogSet d R K q, ∀ u∈catalogSet d R K q, chunk t=chunk u →
        t+u∈shortResidues q (R*periodLength (oddLengths d)) ∨
        t-u∈shortResidues q (R*periodLength (oddLengths d))) := by
  classical
  let chunk : ZMod q → Fin K := fun t ↦
    if h : ∃ c : InteriorCatalog d R K, catalogValue d R K q c=t then h.choose.1
    else ⟨0,hK⟩
  have hinj := catalogValue_injective d R K q i₀ hq
  have hchunk (c : InteriorCatalog d R K) : chunk (catalogValue d R K q c)=c.1 := by
    dsimp [chunk]
    split_ifs with h
    · exact congrArg Prod.fst (hinj h.choose_spec)
    · exact (h ⟨c,rfl⟩).elim
  refine ⟨chunk,hchunk,?_,?_,?_⟩
  · intro i t ht
    obtain ⟨c,_,rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨s,hs⟩ := interior_hit_coordinate d R K q i hq c.1 c.2.1 c.2.2
    refine ⟨(s,c.2.2),?_⟩
    rw [hchunk]
    exact hs
  · intro k
    let T : Finset (ZMod q) := Finset.univ.image (fun c :
      Fin ((R-2)*periodLength (oddLengths d)) × Bool ↦ catalogValue d R K q (k,c))
    have hsub : (Finset.univ.filter (fun t : ZMod q ↦ chunk t=k)) ⊆
        ((Finset.univ : Finset (ZMod q)) \ catalogSet d R K q) ∪ T := by
      intro t ht
      by_cases hg : t∈catalogSet d R K q
      · obtain ⟨c,_,rfl⟩ := Finset.mem_image.mp hg
        have hk : c.1=k := by simpa only [Finset.mem_filter,Finset.mem_univ,true_and,hchunk] using ht
        apply Finset.mem_union_right
        exact Finset.mem_image.mpr ⟨c.2,Finset.mem_univ _,by cases hk; rfl⟩
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hg⟩)
    have hT : T.card≤2*((R-2)*periodLength (oddLengths d)) := by
      apply Finset.card_image_le.trans_eq
      simp only [Finset.card_univ,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool]
      ring
    calc
      _ ≤ (((Finset.univ : Finset (ZMod q)) \ catalogSet d R K q) ∪ T).card := Finset.card_le_card hsub
      _ ≤ ((Finset.univ : Finset (ZMod q)) \ catalogSet d R K q).card+T.card := Finset.card_union_le _ _
      _ ≤ _ := by
        rw [Finset.card_sdiff,Finset.inter_univ,Finset.card_univ,ZMod.card]
        omega
  · intro t ht u hu htu
    obtain ⟨c,_,rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨e,_,rfl⟩ := Finset.mem_image.mp hu
    have hce : c.1=e.1 := by simpa only [hchunk] using htu
    dsimp [catalogValue]
    rw [hce]
    exact same_chunk_collision d R q i₀ c.2.1.isLt e.2.1.isLt c.2.2 e.2.2

lemma actual_centers_injective (d : Fin r → ℕ) (R K q : ℕ) (i : Fin r)
    (hq : 2*(K*(R*periodLength (oddLengths d)))<q) (ω : SlotChoices d K) :
    Function.Injective (fun c : Fin K × Fin (R-1) ↦
      signedSite q (ω c.1).2 (siteCenter d R (ω c.1).1 c.1 c.2 i)) := by
  intro c e h
  have hc : (c.2 : ℕ)+1<R := by have := c.2.isLt; omega
  have he : (e.2 : ℕ)+1<R := by have := e.2.isLt; omega
  have hcb := siteCenter_bounds d (R := R) (chunk := (c.1 : ℕ)) (ω c.1).1.isLt hc i
  have heb := siteCenter_bounds d (R := R) (chunk := (e.1 : ℕ)) (ω e.1).1.isLt he i
  have hcB : siteCenter d R (ω c.1).1 c.1 c.2 i≤K*(R*periodLength (oddLengths d)) :=
    hcb.2.le.trans (Nat.mul_le_mul_right _ (by have := c.1.isLt; omega))
  have heB : siteCenter d R (ω e.1).1 e.1 e.2 i≤K*(R*periodLength (oddLengths d)) :=
    heb.2.le.trans (Nat.mul_le_mul_right _ (by have := e.1.isLt; omega))
  have hs := ((signedSite_injective hq (by omega) hcB (by omega) heB _ _).mp h).2
  have hk : c.1=e.1 := by
    apply Fin.ext
    have hh := congrArg (fun n ↦ n/(R*periodLength (oddLengths d))) hs
    simpa only [siteCenter_chunk d (ω c.1).1.isLt hc i,
      siteCenter_chunk d (ω e.1).1.isLt he i] using hh
  have hp : c.2=e.2 := by
    apply Fin.ext
    rw [hk] at hs
    dsimp [siteCenter,slotLeft] at hs
    have hmul : (c.2 : ℕ)*periodLength (oddLengths d)=
        (e.2 : ℕ)*periodLength (oddLengths d) := by omega
    exact Nat.eq_of_mul_eq_mul_right (periodLength_pos d i) hmul
  exact Prod.ext hk hp

open Classical

lemma slotHit_card (d : Fin r → ℕ) (R K q : ℕ) [NeZero q] (i : Fin r)
    (hq : 2*(K*(R*periodLength (oddLengths d)))<q) (ω : SlotChoices d K) :
    (Finset.univ.filter (fun t : ZMod q ↦ slotHit d R K q i ω t)).card=K*(R-1) := by
  classical
  have he : (Finset.univ.filter (fun t : ZMod q ↦ slotHit d R K q i ω t))=
      Finset.univ.image (fun c : Fin K × Fin (R-1) ↦
        signedSite q (ω c.1).2 (siteCenter d R (ω c.1).1 c.1 c.2 i)) := by
    apply Finset.ext
    intro t

    rw [Finset.mem_filter]
    simp only [Finset.mem_univ,true_and,Finset.mem_image,slotHit]
    constructor
    · rintro ⟨k,p,h⟩; exact ⟨(k,p),h.symm⟩
    · rintro ⟨⟨k,p⟩,h⟩; exact ⟨k,p,h.symm⟩
  rw [he,Finset.card_image_of_injective _ (actual_centers_injective d R K q i hq ω)]
  simp

end
end AsymptoticallyMinimalLittlewood.Packing

end OAI



namespace OAI

universe uκ uA uJ uY uV uK uΩ uI

namespace AsymptoticallyMinimalLittlewood.Packing
noncomputable section
open scoped BigOperators
open Finset

section ProductMoments
variable {κ : Type uκ} {A : Type uA} {J : Type uJ} {Y : Type uY} [Fintype κ] [DecidableEq κ] [Fintype A] [Nonempty A] [DecidableEq A]
  [Fintype J] [Fintype Y] [Nonempty Y]

omit [Nonempty A] in
lemma avg_singleton (a : A) : avg (fun x : A ↦ if x=a then (1 : ℝ) else 0) =
    1/(Fintype.card A : ℝ) := by
  classical
  simp [avg]

lemma avg_independent_selections (c : J → κ) (hc : Function.Injective c) (a : J → A) :
    avg (fun ω : κ → A ↦ ∏ j, if ω (c j)=a j then (1 : ℝ) else 0) =
      (1/(Fintype.card A : ℝ))^(Fintype.card J) := by
  classical
  rw [avg_prod_injective c hc (fun j x ↦ if x=a j then (1 : ℝ) else 0)]
  simp only [avg_singleton,Finset.prod_const,Finset.card_univ]

lemma avg_double_selections (c d : J → κ) (hc : Function.Injective c)
    (hd : Function.Injective d) (hcd : ∀ j l, c j≠d l) (a b : J → A) :
    avg (fun ω : κ → A ↦
      (∏ j, if ω (c j)=a j then (1 : ℝ) else 0)*
      (∏ j, if ω (d j)=b j then (1 : ℝ) else 0)) =
      ((1/(Fintype.card A : ℝ))^(Fintype.card J))^2 := by
  classical
  let c' : J ⊕ J → κ := Sum.elim c d
  let a' : J ⊕ J → A := Sum.elim a b
  have hc' : Function.Injective c' := by
    intro i j hij
    cases i with
    | inl i => cases j with
      | inl j => exact congrArg Sum.inl (hc hij)
      | inr j => exact (hcd i j hij).elim
    | inr i => cases j with
      | inl j => exact (hcd j i hij.symm).elim
      | inr j => exact congrArg Sum.inr (hd hij)
  have h := avg_independent_selections c' hc' a'
  calc
    _ = avg (fun ω : κ → A ↦ ∏ j : J ⊕ J, if ω (c' j)=a' j then (1 : ℝ) else 0) := by
      congr 1; funext ω
      rw [Fintype.prod_sum_type]
      rfl
    _ = _ := by
      rw [h,Fintype.card_sum,pow_add,pow_two]

lemma avg_fst (F : Y → ℝ) : avg (fun yy : Y × Y ↦ F yy.1)=avg F := by
  calc
    _ = avg (fun y : Y ↦ avg (fun _ : Y ↦ F y)) :=
      avg_prod_type (Ω := Y) (Λ := Y) (fun yy : Y × Y ↦ F yy.1)
    _ = _ := by simp only [avg_const]

lemma avg_snd (F : Y → ℝ) : avg (fun yy : Y × Y ↦ F yy.2)=avg F := by
  calc
    _ = avg (fun _ : Y ↦ avg F) :=
      avg_prod_type (Ω := Y) (Λ := Y) (fun yy : Y × Y ↦ F yy.2)
    _ = _ := avg_const _

omit [Fintype κ] in
lemma bad_pair_avg_bound (c : Y → J → κ) (good : Y → Prop) [DecidablePred good]
    {b d : ℝ}
    (hb : avg (fun y ↦ if good y then (0 : ℝ) else 1)≤b)
    (hd : avg (fun yy : Y × Y ↦ if ∃ j l, c yy.1 j=c yy.2 l then (1 : ℝ) else 0)≤d) :
    avg (fun yy : Y × Y ↦ if good yy.1 ∧ good yy.2 ∧ ∀ j l, c yy.1 j≠c yy.2 l
      then (0 : ℝ) else 1)≤2*b+d := by
  classical
  let good₂ : Y × Y → Prop := fun yy ↦ good yy.1 ∧ good yy.2 ∧ ∀ j l, c yy.1 j≠c yy.2 l
  change avg (fun yy ↦ if good₂ yy then (0 : ℝ) else 1)≤2*b+d
  calc
    _ ≤ avg (fun yy : Y × Y ↦ (if good yy.1 then 0 else 1)+
        (if good yy.2 then 0 else 1)+
        (if ∃ j l, c yy.1 j=c yy.2 l then 1 else 0)) := by
      apply avg_mono
      intro yy
      by_cases h₁ : good yy.1
      · by_cases h₂ : good yy.2
        · by_cases h₃ : ∃ j l, c yy.1 j=c yy.2 l
          · simp only [good₂,h₁,h₂,true_and,ite_true,zero_add]
            split_ifs <;> norm_num
          · have h₄ : ∀ j l, c yy.1 j≠c yy.2 l := by
              intro j l h; exact h₃ ⟨j,l,h⟩
            simp [good₂,h₁,h₂,h₄]
        · simp only [good₂,h₁,h₂,true_and,false_and,ite_false,ite_true,zero_add]
          split_ifs <;> norm_num
      · simp only [good₂,h₁,false_and,ite_false]
        split_ifs <;> norm_num
    _ = 2*avg (fun y ↦ if good y then 0 else 1)+
        avg (fun yy : Y × Y ↦ if ∃ j l, c yy.1 j=c yy.2 l then 1 else 0) := by
      rw [avg_add,avg_add]
      rw [avg_fst (fun y : Y ↦ if good y then (0 : ℝ) else 1),
        avg_snd (fun y : Y ↦ if good y then (0 : ℝ) else 1)]
      ring
    _ ≤ _ := by linarith

/-- A finite dependent-row moment estimate.  Dependence is charged only to
same-chunk collisions; rows on distinct chunks use independent coordinates. -/
lemma selections_variance (f : J → Y → (κ → A) → ℝ)
    (c : Y → J → κ) (a : Y → J → A) (good : Y → Prop)
    [DecidablePred good] {b d : ℝ}
    (hf : ∀ j y ω, 0≤f j y ω ∧ f j y ω≤1)
    (hc : ∀ y, good y → Function.Injective (c y))
    (ha : ∀ y, good y → ∀ j ω,
      f j y ω=(if ω (c y j)=a y j then 1 else 0))
    (hb : avg (fun y ↦ if good y then 0 else 1)≤b)
    (hd : avg (fun yy : Y × Y ↦
      if ∃ j l, c yy.1 j=c yy.2 l then 1 else 0)≤d) :
    avg (fun ω : κ → A ↦
      (avg (fun y ↦ ∏ j, f j y ω)-(1/(Fintype.card A : ℝ))^(Fintype.card J))^2)
        ≤ 3*(2*b+d) := by
  classical
  let p : ℝ := (1/(Fintype.card A : ℝ))^(Fintype.card J)
  let good₂ : Y × Y → Prop := fun yy ↦ good yy.1 ∧ good yy.2 ∧
    ∀ j l, c yy.1 j≠c yy.2 l
  have hb0 : 0≤b := (avg_nonneg (by intro y; split_ifs <;> norm_num)).trans hb
  have hd0 : 0≤d := (avg_nonneg (by intro yy; split_ifs <;> norm_num)).trans hd
  have hp : 0≤p := by dsimp [p]; positivity
  have hp1 : p≤1 := by
    apply pow_le_one₀ (by positivity)
    apply (div_le_one (by exact_mod_cast Fintype.card_pos)).mpr
    exact_mod_cast Fintype.card_pos (α := A)
  have hfirst (y : Y) (hy : good y) : avg (fun ω ↦ ∏ j, f j y ω)=p := by
    simp_rw [ha y hy]
    exact avg_independent_selections (c y) (hc y hy) (a y)
  have hsecond (yy : Y × Y) (hy : good₂ yy) :
      avg (fun ω ↦ (∏ j, f j yy.1 ω)*(∏ j, f j yy.2 ω))=p^2 := by
    simp_rw [ha yy.1 hy.1,ha yy.2 hy.2.1]
    exact avg_double_selections _ _ (hc _ hy.1) (hc _ hy.2.1) hy.2.2 _ _
  have hbad₂ : avg (fun yy ↦ if good₂ yy then 0 else 1)≤2*b+d :=
    bad_pair_avg_bound c good hb hd
  exact moments_from_good (fun y ω ↦ ∏ j, f j y ω) good good₂ hp hp1
    (fun y ω ↦ ⟨Finset.prod_nonneg (fun j _ ↦ (hf j y ω).1),
      Finset.prod_le_one (fun j _ ↦ (hf j y ω).1) (fun j _ ↦ (hf j y ω).2)⟩)
    hfirst hsecond (by linarith) hbad₂

end ProductMoments
end
end AsymptoticallyMinimalLittlewood.Packing

namespace AsymptoticallyMinimalLittlewood.Packing
noncomputable section
open scoped BigOperators
open Finset

lemma avg_finset {V : Type uV} [Fintype V] (S : Finset V) (F : V → ℝ) :
    avg (fun v : S ↦ F v)=(∑ v∈S,F v)/(S.card : ℝ) := by
  simp only [avg,Fintype.card_coe,Finset.sum_coe_sort]

section ConditionalAverage
variable {K : Type uK} {V : Type uV} [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Module K V] [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
lemma avg_fibers (f : V →ₗ[K] K) (hf : Function.Surjective f) (F : V → ℝ) :
    avg (fun s : K ↦ avg (fun v : fiber f s ↦ F v))=avg F := by
  classical
  have hcard (s : K) : (fiber f s).card=(fiber f 0).card :=
    fiber_card_eq f.toAddMonoidHom hf s 0
  simp_rw [avg_finset (fiber f _) F, hcard]
  dsimp [avg]
  rw [← Finset.sum_div,div_div]
  have he : ((fiber f 0).card : ℝ)*Fintype.card K=Fintype.card V := by
    have h : Fintype.card K*(fiber f (0 : K)).card=Fintype.card V :=
      fiber_card_mul f.toAddMonoidHom hf 0
    exact_mod_cast (by simpa only [Nat.mul_comm] using h)
  rw [he]
  congr 1
  simp only [fiber,Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

omit [DecidableEq V] in
lemma avg_fiber_event (f g : V →ₗ[K] K)
    (hfg : Function.Surjective (f.prod g)) (s : K) (S : Finset K) :
    avg (fun v : fiber f s ↦ if g v∈S then (1 : ℝ) else 0)=
      (S.card : ℝ)/Fintype.card K := by
  classical
  rw [avg_finset (fiber f s) (fun v ↦ if g v∈S then (1 : ℝ) else 0)]
  simp only [Finset.sum_boole]
  have hc := conditional_card_event f g hfg s S
  rw [hc,Nat.cast_mul]
  have hn := conditional_fiber_count f g hfg s 0
  have hF : 0<(fiber f s).card := by
    apply Finset.card_pos.mpr
    obtain ⟨y,hy⟩ := hfg (s,0)
    refine ⟨y,?_⟩
    exact mem_fiber.mpr (congrArg Prod.fst hy)
  have hK : (Fintype.card K : ℝ)≠0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hF' : ((fiber f s).card : ℝ)≠0 := by positivity
  have hn' : (Fintype.card K : ℝ)*((fiber f s).filter (fun v ↦ g v=0)).card=
      (fiber f s).card := by exact_mod_cast hn
  field_simp
  nlinarith only [hn']

omit [DecidableEq V] in
lemma avg_uniform_event (f : V →ₗ[K] K) (hf : Function.Surjective f) (S : Finset K) :
    avg (fun v : V ↦ if f v∈S then (1 : ℝ) else 0)=
      (S.card : ℝ)/Fintype.card K := by
  rw [← avg_fibers f hf]
  have hh (s : K) : avg (fun v : fiber f s ↦ if f v∈S then (1 : ℝ) else 0)=
      if s∈S then 1 else 0 := by
    have : Nonempty (fiber f s) := (fiber_nonempty f.toAddMonoidHom hf s).coe_sort
    simp_rw [mem_fiber.mp (Subtype.property _)]
    exact avg_const _
  simp_rw [hh]
  simp [avg]

omit [DecidableEq V] in
lemma avg_cross_chunks {κ : Type uκ} [DecidableEq κ]
    (f g h : V →ₗ[K] K) (hfg : Function.Surjective (f.prod g))
    (chunk : K → κ) (s : K) {B : ℝ}
    (hB : ∀ k, ((Finset.univ.filter (fun t : K ↦ chunk t=k)).card : ℝ)≤B) :
    avg (fun yy : fiber f s × fiber f s ↦
      if chunk (g yy.1)=chunk (h yy.2) then (1 : ℝ) else 0) ≤
      B/Fintype.card K := by
  have : Nonempty (fiber f s) := by
    obtain ⟨y,hy⟩ := hfg (s,0)
    exact ⟨⟨y,mem_fiber.mpr (congrArg Prod.fst hy)⟩⟩
  rw [avg_prod_type,avg_comm]
  apply (avg_mono (fun y ↦ ?_)).trans_eq (avg_const _)
  have he := avg_fiber_event f g hfg s (Finset.univ.filter (fun t ↦ chunk t=chunk (h y)))
  simp only [Finset.mem_filter,Finset.mem_univ,true_and] at he
  rw [he]
  exact div_le_div_of_nonneg_right (hB _) (Nat.cast_nonneg _)

end ConditionalAverage
end
end AsymptoticallyMinimalLittlewood.Packing

namespace AsymptoticallyMinimalLittlewood.Packing
noncomputable section
open scoped BigOperators
open Finset

section GoodRows
variable {K : Type uK} {V : Type uV} {J : Type uJ} {κ : Type uκ} [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Module K V] [Fintype V] [DecidableEq V]
  [Fintype J] [DecidableEq J]

def rowsGood (g : J → V →ₗ[K] K) (G S : Finset K) (y : V) : Prop :=
  (∀ j, g j y∈G) ∧ ∀ j l, j≠l → g j y+g l y∉S ∧ g j y-g l y∉S

noncomputable local instance rowsGoodDecidable (g : J → V →ₗ[K] K) (G S : Finset K) (y : V) :
    Decidable (rowsGood g G S y) := Classical.propDecidable _

omit [Fintype K] [DecidableEq K] [Fintype V] [DecidableEq V] in
lemma sum_form_surjective (f g : V →ₗ[K] K)
    (hfg : Function.Surjective (f.prod g)) : Function.Surjective (f+g) := by
  classical
  intro s
  obtain ⟨v,hv⟩ := hfg (s,0)
  exact ⟨v,by simp [show f v=s from congrArg Prod.fst hv,
    show g v=0 from congrArg Prod.snd hv]⟩

omit [Fintype K] [DecidableEq K] [Fintype V] [DecidableEq V] in
lemma sub_form_surjective (f g : V →ₗ[K] K)
    (hfg : Function.Surjective (f.prod g)) : Function.Surjective (f-g) := by
  classical
  intro s
  obtain ⟨v,hv⟩ := hfg (s,0)
  exact ⟨v,by simp [show f v=s from congrArg Prod.fst hv,
    show g v=0 from congrArg Prod.snd hv]⟩

omit [Fintype K] [DecidableEq K] [Fintype V] [DecidableEq V] [Fintype J] in
lemma rowsGood_injective (g : J → V →ₗ[K] K) (G S : Finset K) (chunk : K → κ)
    (hchunk : ∀ t∈G, ∀ u∈G, chunk t=chunk u → t+u∈S ∨ t-u∈S)
    {y : V} (hy : rowsGood g G S y) : Function.Injective (fun j ↦ chunk (g j y)) := by
  classical
  intro j l hjl
  by_contra hne
  rcases hchunk _ (hy.1 j) _ (hy.1 l) hjl with h | h
  · exact (hy.2 j l hne).1 h
  · exact (hy.2 j l hne).2 h

omit [Fintype K] [Fintype V] [DecidableEq V] in
lemma rows_bad_indicator (g : J → V →ₗ[K] K) (G S : Finset K) (y : V) :
    (if rowsGood g G S y then (0 : ℝ) else 1) ≤
      (∑ j, if g j y∉G then (1 : ℝ) else 0)+
      ∑ jl : J × J, if jl.1≠jl.2 then
        (if g jl.1 y+g jl.2 y∈S then (1 : ℝ) else 0)+
        (if g jl.1 y-g jl.2 y∈S then 1 else 0) else 0 := by
  classical
  have hnon (P : Prop) : 0≤(if P then (1 : ℝ) else 0) := by split_ifs <;> norm_num
  have hn₁ : 0≤∑ j, if g j y∉G then (1 : ℝ) else 0 := Finset.sum_nonneg (fun j _ ↦ by split_ifs <;> norm_num)
  have hn₂ : 0≤∑ jl : J × J, if jl.1≠jl.2 then
      (if g jl.1 y+g jl.2 y∈S then (1 : ℝ) else 0)+
      (if g jl.1 y-g jl.2 y∈S then 1 else 0) else 0 := by
    apply Finset.sum_nonneg
    intro jl _
    split_ifs <;> norm_num
  split_ifs with h
  · linarith
  · by_cases hloc : ∀ j, g j y∈G
    · obtain ⟨j,l,hjl,hbad⟩ : ∃ j l, j≠l ∧ ¬(g j y+g l y∉S ∧ g j y-g l y∉S) := by
        have hh : ¬ ∀ j l, j≠l → g j y+g l y∉S ∧ g j y-g l y∉S :=
          fun hh ↦ h ⟨hloc,hh⟩
        obtain ⟨j,hj⟩ := not_forall.mp hh
        obtain ⟨l,hl⟩ := not_forall.mp hj
        obtain ⟨hne,hbad⟩ := Classical.not_imp.mp hl
        exact ⟨j,l,hne,hbad⟩
      have hp : (1 : ℝ)≤(if g j y+g l y∈S then 1 else 0)+
          (if g j y-g l y∈S then 1 else 0) := by
        split_ifs <;> simp_all
      have hs := Finset.single_le_sum (f := fun jl : J × J ↦ if jl.1≠jl.2 then
        (if g jl.1 y+g jl.2 y∈S then (1 : ℝ) else 0)+
        (if g jl.1 y-g jl.2 y∈S then 1 else 0) else 0)
        (fun jl _ ↦ by split_ifs <;> norm_num) (Finset.mem_univ (j,l))
      simp only [if_pos hjl] at hs
      linarith
    · obtain ⟨j,hj⟩ := not_forall.mp hloc
      have hs := Finset.single_le_sum (f := fun j ↦ if g j y∉G then (1 : ℝ) else 0)
        (fun j _ ↦ by split_ifs <;> norm_num) (Finset.mem_univ j)
      simp only [hj,not_false_eq_true,ite_true] at hs
      linarith

omit [DecidableEq V] in
lemma avg_bad_rows (g : J → V →ₗ[K] K)
    (hg : ∀ j, Function.Surjective (g j))
    (hpair : ∀ j l, j≠l → Function.Surjective ((g j).prod (g l)))
    (G S : Finset K) :
    avg (fun y ↦ if rowsGood g G S y then (0 : ℝ) else 1) ≤
      (Fintype.card J : ℝ)*(Fintype.card K-G.card)/Fintype.card K+
        2*(Fintype.card J : ℝ)^2*S.card/Fintype.card K := by
  classical
  have : Nonempty V := ⟨0⟩
  apply (avg_mono (rows_bad_indicator g G S)).trans
  rw [avg_add,avg_sum,avg_sum]
  have hloc (j : J) : avg (fun y ↦ if g j y∉G then (1 : ℝ) else 0)=
      (Fintype.card K-G.card : ℝ)/Fintype.card K := by
    have he := avg_uniform_event (g j) (hg j) (Finset.univ \ G)
    simp only [Finset.mem_sdiff,Finset.mem_univ,true_and,Finset.card_sdiff,
      Finset.inter_univ,Finset.card_univ] at he
    rw [Nat.cast_sub (Finset.card_le_univ G)] at he
    exact he
  have hpair' (jl : J × J) : avg (fun y ↦ if jl.1≠jl.2 then
      (if g jl.1 y+g jl.2 y∈S then (1 : ℝ) else 0)+
      (if g jl.1 y-g jl.2 y∈S then 1 else 0) else 0) ≤
        2*(S.card : ℝ)/Fintype.card K := by
    by_cases hjl : jl.1≠jl.2
    · simp only [if_pos hjl,avg_add]
      have hs := avg_uniform_event (g jl.1+g jl.2) (sum_form_surjective _ _ (hpair _ _ hjl)) S
      have hd := avg_uniform_event (g jl.1-g jl.2) (sub_form_surjective _ _ (hpair _ _ hjl)) S
      simp only [LinearMap.add_apply,LinearMap.sub_apply] at hs hd
      rw [hs,hd]
      ring_nf
      exact le_refl _
    · simp only [if_neg hjl,avg_const]
      positivity
  simp_rw [hloc]
  apply add_le_add_right (Finset.sum_le_sum (fun jl _ ↦ hpair' jl)) _ |>.trans_eq
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,nsmul_eq_mul,Nat.cast_mul]
  ring

omit [DecidableEq J] [DecidableEq V] in
lemma avg_cross_rows [DecidableEq κ] (f : V →ₗ[K] K) (g : J → V →ₗ[K] K)
    (hfg : ∀ j, Function.Surjective (f.prod (g j)))
    (hf : Function.Surjective f) (chunk : K → κ) (s : K) {B : ℝ}
    (hB : ∀ k, ((Finset.univ.filter (fun t : K ↦ chunk t=k)).card : ℝ)≤B) :
    avg (fun yy : fiber f s × fiber f s ↦
      if ∃ j l, chunk (g j yy.1)=chunk (g l yy.2) then (1 : ℝ) else 0) ≤
        (Fintype.card J : ℝ)^2*B/Fintype.card K := by
  classical
  have : Nonempty (fiber f s) := (fiber_nonempty f.toAddMonoidHom hf s).coe_sort
  calc
    _ = avg (fun yy : fiber f s × fiber f s ↦
        if ∃ jl∈(Finset.univ : Finset (J × J)), chunk (g jl.1 yy.1)=chunk (g jl.2 yy.2)
        then (1 : ℝ) else 0) := by simp
    _ ≤ ∑ jl : J × J, avg (fun yy : fiber f s × fiber f s ↦
        if chunk (g jl.1 yy.1)=chunk (g jl.2 yy.2) then (1 : ℝ) else 0) := avg_bad_union _ _
    _ ≤ ∑ _jl : J × J, B/Fintype.card K := Finset.sum_le_sum (fun jl _ ↦
      avg_cross_chunks f (g jl.1) (g jl.2) (hfg jl.1) chunk s hB)
    _ = _ := by simp [Fintype.card_prod,pow_two]; ring

end GoodRows
end
end AsymptoticallyMinimalLittlewood.Packing

namespace AsymptoticallyMinimalLittlewood.Packing
noncomputable section
open scoped BigOperators
open Finset

section AveragedVariance
variable {K : Type uK} {V : Type uV} {J : Type uJ} {κ : Type uκ} {A : Type uA} [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Module K V] [Fintype V] [DecidableEq V]
  [Fintype J] [DecidableEq J] [Fintype κ] [DecidableEq κ]
  [Fintype A] [Nonempty A] [DecidableEq A]

omit [DecidableEq V] in
/-- Averaging over the anchored coordinate removes even the exceptional
centers. This quantitative statement is used before pruning the slot graph. -/
lemma averaged_density_variance (f : V →ₗ[K] K) (g : J → V →ₗ[K] K)
    (hf : Function.Surjective f)
    (hg : ∀ j, Function.Surjective (g j))
    (hfg : ∀ j, Function.Surjective (f.prod (g j)))
    (hpair : ∀ j l, j≠l → Function.Surjective ((g j).prod (g l)))
    (G S : Finset K) (chunk : K → κ)
    (hchunk : ∀ t∈G, ∀ u∈G, chunk t=chunk u → t+u∈S ∨ t-u∈S)
    (hit : J → K → (κ → A) → Prop) [∀ j t ω, Decidable (hit j t ω)]
    (hhit : ∀ j t, t∈G → ∃ a : A, ∀ ω, hit j t ω ↔ ω (chunk t)=a)
    {B : ℝ} (hB : ∀ k, ((Finset.univ.filter (fun t : K ↦ chunk t=k)).card : ℝ)≤B) :
    avg (fun ω : κ → A ↦ avg (fun s : K ↦
      (avg (fun y : fiber f s ↦ ∏ j, if hit j (g j y) ω then (1 : ℝ) else 0)-
        (1/(Fintype.card A : ℝ))^(Fintype.card J))^2)) ≤
      3*(2*((Fintype.card J : ℝ)*(Fintype.card K-G.card)/Fintype.card K+
          2*(Fintype.card J : ℝ)^2*S.card/Fintype.card K)+
        (Fintype.card J : ℝ)^2*B/Fintype.card K) := by
  classical
  let GoodLabel (j : J) (t : K) (a : A) : Prop := t ∈ G → ∀ ω, hit j t ω ↔ ω (chunk t) = a
  have ha : ∀ j t, ∃ a : A, GoodLabel j t a := by
    intro j t
    by_cases ht : t∈G
    · obtain ⟨a,ha⟩ := hhit j t ht
      exact ⟨a,fun _ ↦ ha⟩
    · exact ⟨Classical.arbitrary A,fun h ↦ (ht h).elim⟩
  choose a ha using ha
  have hs (s : K) :
      avg (fun ω : κ → A ↦
        (avg (fun y : fiber f s ↦ ∏ j, if hit j (g j y) ω then (1 : ℝ) else 0)-
          (1/(Fintype.card A : ℝ))^(Fintype.card J))^2) ≤
        3*(2*avg (fun y : fiber f s ↦ if rowsGood g G S y then (0 : ℝ) else 1)+
          (Fintype.card J : ℝ)^2*B/Fintype.card K) := by
    have : Nonempty (fiber f s) := (fiber_nonempty f.toAddMonoidHom hf s).coe_sort
    apply selections_variance
      (fun j (y : fiber f s) ω ↦ if hit j (g j y) ω then (1 : ℝ) else 0)
      (fun y j ↦ chunk (g j y)) (fun y j ↦ a j (g j y))
      (fun y ↦ rowsGood g G S y)
    · intro j y ω; split_ifs <;> norm_num
    · intro y hy; exact rowsGood_injective g G S chunk hchunk hy
    · intro y hy j ω
      simp only [ha j (g j y) (hy.1 j) ω]
    · exact le_refl _
    · exact avg_cross_rows f g hfg hf chunk s hB
  rw [avg_comm]
  apply (avg_mono hs).trans
  have he := avg_fibers f hf (fun y ↦ if rowsGood g G S y then (0 : ℝ) else 1)
  rw [avg_const_mul,avg_add,avg_const_mul,avg_const,he]
  have hb := avg_bad_rows g hg hpair G S
  linarith

end AveragedVariance
end
end AsymptoticallyMinimalLittlewood.Packing

namespace AsymptoticallyMinimalLittlewood.Packing
noncomputable section
open scoped BigOperators
open Finset

lemma exists_few_bad_centers_total {Ω : Type uΩ} {I : Type uI} [Fintype Ω] [Nonempty Ω]
    [Fintype I] (Z : I → Ω → ℝ) (p : ℝ) {t a : ℝ} (ht : 0<t)
    (hZ : (∑ i, avg (fun ω ↦ (Z i ω-p)^2))≤a) :
    ∃ ω, ((Finset.univ.filter (fun i ↦ t≤|Z i ω-p|)).card : ℝ) ≤ a/t^2 := by
  classical
  let W : Ω → ℝ := fun ω ↦ ∑ i : I, if t≤|Z i ω-p| then 1 else 0
  obtain ⟨ω,hω⟩ := exists_le_avg W
  refine ⟨ω,?_⟩
  have he : ((Finset.univ.filter (fun i ↦ t≤|Z i ω-p|)).card : ℝ)=W ω := by
    simp [W,Finset.sum_boole]
  rw [he]
  apply hω.trans
  dsimp [W]
  rw [avg_sum]
  calc
    _ ≤ ∑ i, avg (fun ω ↦ (Z i ω-p)^2)/t^2 :=
      Finset.sum_le_sum (fun i _ ↦ avg_chebyshev p ht)
    _ = (∑ i, avg (fun ω ↦ (Z i ω-p)^2))/t^2 := (Finset.sum_div _ _ _).symm
    _ ≤ _ := div_le_div_of_nonneg_right hZ (sq_nonneg _)

lemma exists_few_bad_centers_averaged {Ω : Type uΩ} {I : Type uI} {K : Type uK} [Fintype Ω] [Nonempty Ω]
    [Fintype I] [Fintype K] [Nonempty K] (Z : I → K → Ω → ℝ)
    (p : ℝ) {t a : ℝ} (ht : 0<t)
    (hZ : ∀ i, avg (fun ω ↦ avg (fun s ↦ (Z i s ω-p)^2))≤a) :
    ∃ ω, ((Finset.univ.filter (fun v : I × K ↦ t≤|Z v.1 v.2 ω-p|)).card : ℝ) ≤
      Fintype.card I*Fintype.card K*a/t^2 := by
  classical
  apply exists_few_bad_centers_total (Ω := Ω) (I := I × K)
    (fun (v : I × K) (ω : Ω) ↦ Z v.1 v.2 ω) p (a := Fintype.card I*Fintype.card K*a) ht
  rw [Fintype.sum_prod_type]
  calc
    _ ≤ ∑ _i : I, (Fintype.card K : ℝ)*a := by
      apply Finset.sum_le_sum
      intro i _
      have hi := hZ i
      rw [avg_comm,avg] at hi
      have hcard : (0 : ℝ)<Fintype.card K := by exact_mod_cast Fintype.card_pos (α := K)
      simpa only [mul_comm a] using ((div_le_iff₀ hcard).mp hi)
    _ = _ := by simp; ring

end
end AsymptoticallyMinimalLittlewood.Packing

end OAI



namespace OAI

universe uI uK uV uJ

namespace AsymptoticallyMinimalLittlewood.Packing
noncomputable section
open scoped BigOperators
open Finset
open Nibble
section SlotGraph
variable {I : Type uI} {K : Type uK} {V : Type uV} [Fintype I] [DecidableEq I] [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Module K V] [Fintype V] [DecidableEq V]

def slotVertices (hit : I → K → Prop) [∀ i t, Decidable (hit i t)] : Finset (I × K) :=
  Finset.univ.filter (fun v ↦ hit v.1 v.2)

def slotEdges (g : I → V →ₗ[K] K) (hit : I → K → Prop) [∀ i t, Decidable (hit i t)] : Finset V :=
  Finset.univ.filter (fun y ↦ ∀ i, hit i (g i y))

def slotSupport (g : I → V →ₗ[K] K) (y : V) : Finset (I × K) :=
  Finset.univ.image (fun i ↦ (i,g i y))

omit [Fintype K] [Fintype V] [DecidableEq V] in
@[simp] lemma mem_slotSupport (g : I → V →ₗ[K] K) (y : V) (i : I) (t : K) :
    (i,t)∈slotSupport g y ↔ g i y=t := by
  simp [slotSupport,Prod.ext_iff]

omit [Fintype K] [Fintype V] [DecidableEq V] in
lemma slotSupport_card (g : I → V →ₗ[K] K) (y : V) :
    (slotSupport g y).card=Fintype.card I := by
  rw [slotSupport,Finset.card_image_of_injective]
  · exact Finset.card_univ
  · intro i j h; exact congrArg Prod.fst h

omit [DecidableEq V] in
lemma slotSupport_subset (g : I → V →ₗ[K] K) (hit : I → K → Prop)
    [∀ i t, Decidable (hit i t)] {y : V} (hy : y∈slotEdges g hit) :
    slotSupport g y⊆slotVertices hit := by
  intro v hv
  rcases v with ⟨i,t⟩
  obtain rfl := mem_slotSupport g y i t |>.mp hv
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hy).2 i⟩

omit [DecidableEq I] [Field K] [DecidableEq K] in
lemma slotVertices_card (hit : I → K → Prop) [∀ i t, Decidable (hit i t)] :
    (slotVertices hit).card=∑ i, (Finset.univ.filter (hit i)).card := by
  classical
  simp only [slotVertices,Finset.card_filter,Fintype.sum_prod_type]

omit [Fintype K] [DecidableEq V] in
lemma slot_degree_fiber (g : I → V →ₗ[K] K) (hit : I → K → Prop)
    [∀ i t, Decidable (hit i t)] (i : I) (s : K) (hs : hit i s) :
    incident (slotEdges g hit) (slotSupport g) (i,s)=
      (fiber (g i) s).filter (fun y ↦ ∀ j : {j : I // j≠i}, hit j (g j y)) := by
  classical
  apply Finset.ext
  intro y
  simp only [mem_incident,slotEdges,Finset.mem_filter,Finset.mem_univ,true_and,
    mem_slotSupport,mem_fiber]
  constructor
  · rintro ⟨hy,hys⟩; exact ⟨hys,fun j ↦ hy j⟩
  · rintro ⟨hys,hy⟩
    refine ⟨?_,hys⟩
    intro j
    by_cases hj : j=i
    · subst j; simpa [hys] using hs
    · exact hy ⟨j,hj⟩

omit [Fintype K] in
lemma slot_codegree_subset (g : I → V →ₗ[K] K) (hit : I → K → Prop)
    [∀ i t, Decidable (hit i t)] (i j : I) (s t : K) :
    incident (slotEdges g hit) (slotSupport g) (i,s) ∩
      incident (slotEdges g hit) (slotSupport g) (j,t) ⊆
        (fiber (g i) s).filter (fun y ↦ g j y=t) := by
  intro y hy
  obtain ⟨hyi,hyj⟩ := Finset.mem_inter.mp hy
  exact Finset.mem_filter.mpr ⟨mem_fiber.mpr (mem_slotSupport _ _ _ _ |>.mp
    (mem_incident _ _ _ _ |>.mp hyi).2),mem_slotSupport _ _ _ _ |>.mp
    (mem_incident _ _ _ _ |>.mp hyj).2⟩

omit [Fintype K] [DecidableEq V] in
lemma slot_same_row_disjoint (g : I → V →ₗ[K] K) (hit : I → K → Prop)
    [∀ i t, Decidable (hit i t)] (i : I) {s t : K} (hst : s≠t) :
    Disjoint (incident (slotEdges g hit) (slotSupport g) (i,s))
      (incident (slotEdges g hit) (slotSupport g) (i,t)) := by
  apply Finset.disjoint_left.mpr
  intro y hys hyt
  exact hst ((mem_slotSupport _ _ _ _ |>.mp (mem_incident _ _ _ _ |>.mp hys).2).symm.trans
    (mem_slotSupport _ _ _ _ |>.mp (mem_incident _ _ _ _ |>.mp hyt).2))

lemma slot_codegree (g : I → V →ₗ[K] K) (hit : I → K → Prop)
    [∀ i t, Decidable (hit i t)]
    (hg : ∀ i, Function.Surjective (g i))
    (hpair : ∀ i j, i≠j → Function.Surjective ((g i).prod (g j)))
    (v w : I × K) (hvw : v≠w) :
    ((incident (slotEdges g hit) (slotSupport g) v ∩
      incident (slotEdges g hit) (slotSupport g) w).card : ℝ) ≤
        Fintype.card V/(Fintype.card K : ℝ)^2 := by
  rcases v with ⟨i,s⟩
  rcases w with ⟨j,t⟩
  by_cases hij : i=j
  · subst j
    have hst : s≠t := fun h ↦ hvw (Prod.ext rfl h)
    rw [Finset.disjoint_iff_inter_eq_empty.mp (slot_same_row_disjoint g hit i hst)]
    simp only [Finset.card_empty,Nat.cast_zero]
    positivity
  · have hcard := Finset.card_le_card (slot_codegree_subset g hit i j s t)
    have hcount := conditional_fiber_count (g i) (g j) (hpair i j hij) s t
    have htotal := fiber_card_mul (g i).toAddMonoidHom (hg i) s
    have hq : (0 : ℝ)<Fintype.card K := by exact_mod_cast Fintype.card_pos (α := K)
    apply (Nat.cast_le.mpr hcard : (_ : ℝ)≤_).trans_eq
    apply (eq_div_iff (ne_of_gt (sq_pos_of_pos hq))).mpr
    have hc : (Fintype.card K : ℝ)*((fiber (g i) s).filter (fun y ↦ g j y=t)).card=
        (fiber (g i) s).card := by exact_mod_cast hcount
    have ht : (Fintype.card K : ℝ)*(fiber (g i) s).card=Fintype.card V := by exact_mod_cast htotal
    nlinarith

lemma prod_indicator_eq {J : Type uJ} [Fintype J] (P : J → Prop) [DecidablePred P] :
    (∏ j, if P j then (1 : ℝ) else 0) = if ∀ j, P j then 1 else 0 := by
  classical
  by_cases h : ∀ j, P j
  · simp [h]
  · obtain ⟨j,hj⟩ := not_forall.mp h
    rw [if_neg h]
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    exact if_neg hj

def slotDensity (g : I → V →ₗ[K] K) (hit : I → K → Prop)
    [∀ i t, Decidable (hit i t)] (i : I) (s : K) : ℝ :=
  avg (fun y : fiber (g i) s ↦ ∏ j : {j : I // j≠i}, if hit j (g j y) then (1 : ℝ) else 0)

omit [Fintype K] [DecidableEq V] in
lemma slotDensity_eq (g : I → V →ₗ[K] K) (hit : I → K → Prop)
    [∀ i t, Decidable (hit i t)] (i : I) (s : K) :
    slotDensity g hit i s=
      (((fiber (g i) s).filter (fun y ↦ ∀ j : {j : I // j≠i}, hit j (g j y))).card : ℝ)/
        (fiber (g i) s).card := by
  classical
  simp only [slotDensity,prod_indicator_eq,avg,Fintype.card_coe]
  rw [Finset.sum_boole, Finset.univ_eq_attach,
    Finset.filter_attach (fun y : V ↦ ∀ j : {j : I // j≠i}, hit j (g j y)),
    Finset.card_map, Finset.card_attach]

omit [DecidableEq V] in
lemma slot_degree_density (g : I → V →ₗ[K] K) (hit : I → K → Prop)
    [∀ i t, Decidable (hit i t)] (hg : ∀ i, Function.Surjective (g i))
    (i : I) (s : K) (hs : hit i s) :
    ((incident (slotEdges g hit) (slotSupport g) (i,s)).card : ℝ)=
      (Fintype.card V/(Fintype.card K : ℝ))*slotDensity g hit i s := by
  rw [slot_degree_fiber g hit i s hs,slotDensity_eq]
  have hc : (Fintype.card K : ℝ)*(fiber (g i) s).card = Fintype.card V :=
    by exact_mod_cast (fiber_card_mul (g i).toAddMonoidHom (hg i) s)
  have hF : (0 : ℝ)<(fiber (g i) s).card := by
    exact_mod_cast (fiber_nonempty (g i).toAddMonoidHom (hg i) s).card_pos
  have hq : (0 : ℝ)<Fintype.card K := by exact_mod_cast Fintype.card_pos (α := K)
  rw [← hc,mul_div_cancel_left₀ _ hq.ne']
  exact (mul_div_cancel₀ _ hF.ne').symm

omit [DecidableEq V] in
lemma slot_degree_near (g : I → V →ₗ[K] K) (hit : I → K → Prop)
    [∀ i t, Decidable (hit i t)] (hg : ∀ i, Function.Surjective (g i))
    (i : I) (s : K) (hs : hit i s) {p e : ℝ}
    (hne : |slotDensity g hit i s-p|≤e*p) :
    |((incident (slotEdges g hit) (slotSupport g) (i,s)).card : ℝ)-
      (Fintype.card V/(Fintype.card K : ℝ))*p| ≤
        e*((Fintype.card V/(Fintype.card K : ℝ))*p) := by
  rw [slot_degree_density g hit hg i s hs,← mul_sub,abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ)≤Fintype.card V/(Fintype.card K : ℝ))]
  have h := mul_le_mul_of_nonneg_left hne (by positivity : (0 : ℝ)≤Fintype.card V/(Fintype.card K : ℝ))
  nlinarith only [h]

end SlotGraph
end
end AsymptoticallyMinimalLittlewood.Packing

namespace AsymptoticallyMinimalLittlewood.Packing
noncomputable section
open scoped BigOperators
open Finset Nibble
section RandomMatching
variable {I : Type} [Fintype I] [DecidableEq I]

lemma random_slot_matching (hr : 1≤Fintype.card I) {K₀ η : ℝ}
    (hK₀ : 0≤K₀) (hη : 0<η) (hη₁ : η≤1) :
    ∃ e T : ℝ, 0<e ∧ 0<T ∧
    ∀ {K V Ω : Type} [Field K] [Fintype K] [DecidableEq K]
      [AddCommGroup V] [Module K V] [Fintype V] [DecidableEq V] [Fintype Ω] [Nonempty Ω],
    ∀ (g : I → V →ₗ[K] K) (hit : I → K → Ω → Prop)
      [∀ i s ω, Decidable (hit i s ω)] (p a b n : ℝ),
      (∀ i, Function.Surjective (g i)) →
      (∀ i j, i≠j → Function.Surjective ((g i).prod (g j))) →
      0<p → 0≤b →
      (∀ i, avg (fun ω ↦ avg (fun s ↦ (slotDensity g (fun j t ↦ hit j t ω) i s-p)^2))≤a) →
      Fintype.card I*Fintype.card K*a/(e*p/2)^2≤b →
      (∀ ω, ((slotVertices (fun i t ↦ hit i t ω)).card : ℝ)=n) →
      T≤(Fintype.card V/(Fintype.card K : ℝ))*p → T≤n-b →
      Fintype.card V/(Fintype.card K : ℝ)^2≤e*((Fintype.card V/(Fintype.card K : ℝ))*p) →
      n*(Fintype.card V/(Fintype.card K : ℝ)^2)≤K₀*((Fintype.card V/(Fintype.card K : ℝ))*p) →
      b*(Fintype.card V/(Fintype.card K : ℝ)^2)≤e*((Fintype.card V/(Fintype.card K : ℝ))*p)/2 →
      ∃ ω, ∃ M⊆slotEdges g (fun i t ↦ hit i t ω),
        (M : Set V).Pairwise (fun y z ↦ Disjoint (slotSupport g y) (slotSupport g z)) ∧
        (1-η)*(n-b)≤Fintype.card I*(M.card : ℝ) := by
  classical
  obtain ⟨e,T,he,hT,hmatch⟩ := matching_after_pruning
    (Fintype.card I) hr hK₀ hη
  refine ⟨e,T,he,hT,?_⟩
  intro K V Ω instK instFK instDK instV instMV instFV instDV instFΩ instNΩ g hit inst p a b n hg hpair hp hb hvar hbad hn hD hsize hCe hcode hsmall
  obtain ⟨ω,hω⟩ := exists_few_bad_centers_averaged
    (fun i s ω ↦ slotDensity g (fun j t ↦ hit j t ω) i s) p
    (show 0<e*p/2 by positivity) hvar
  let U := slotVertices (fun i t ↦ hit i t ω)
  let B := U.filter (fun v ↦ e*p/2≤|slotDensity g (fun j t ↦ hit j t ω) v.1 v.2-p|)
  have hBU : B⊆U := Finset.filter_subset _ _
  have hB : (B.card : ℝ)≤b := by
    apply le_trans _ (hω.trans hbad)
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro v hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hv).2⟩
  have hnB : n-b≤((U\B).card : ℝ) := by
    rw [Finset.card_sdiff_of_subset hBU, Nat.cast_sub (Finset.card_le_card hBU)]
    dsimp [U]
    rw [hn ω]
    linarith
  have hC : (0 : ℝ)≤Fintype.card V/(Fintype.card K : ℝ)^2 := by positivity
  obtain ⟨M,hM,hdis,hMsize⟩ := hmatch U B (slotEdges g (fun i t ↦ hit i t ω))
    (slotSupport g) ((Fintype.card V/(Fintype.card K : ℝ))*p)
    (Fintype.card V/(Fintype.card K : ℝ)^2) hBU hD (hsize.trans hnB) hC hCe
    (by simpa only [U,hn ω] using hcode)
    ((mul_le_mul_of_nonneg_right hB hC).trans hsmall)
    (fun y hy ↦ slotSupport_subset g _ hy)
    (fun y _ ↦ slotSupport_card g y) (by
      rintro ⟨i,s⟩ hv
      obtain ⟨hvU,hvB⟩ := Finset.mem_sdiff.mp hv
      have hh : hit i s ω := (Finset.mem_filter.mp hvU).2
      have hne : |slotDensity g (fun j t ↦ hit j t ω) i s-p|<e*p/2 := by
        exact lt_of_not_ge (fun h ↦ hvB (Finset.mem_filter.mpr ⟨hvU,h⟩))
      have h := slot_degree_near g (fun j t ↦ hit j t ω) hg i s hh
        (e := e/2) (p := p) (by nlinarith only [hne])
      convert h using 1 ; ring) (by
      rintro ⟨i,s⟩ _ ⟨j,t⟩ _ hne
      exact slot_codegree g (fun a u ↦ hit a u ω) hg hpair (i,s) (j,t) hne)
  exact ⟨ω,M,hM,hdis,(mul_le_mul_of_nonneg_left hnB (sub_nonneg.mpr hη₁)).trans hMsize⟩
end RandomMatching
end
end AsymptoticallyMinimalLittlewood.Packing

namespace AsymptoticallyMinimalLittlewood.Packing
noncomputable section
open scoped BigOperators
open Finset Nibble
open Classical

lemma concrete_slot_variance {r q : ℕ} [Fact q.Prime] (d : Fin r → ℕ)
    (R K : ℕ) (i₀ : Fin r) (hK : 0<K)
    (hq : 2*(K*(R*periodLength (oddLengths d)))<q)
    {V : Type uV} [AddCommGroup V] [Module (ZMod q) V] [Fintype V] [DecidableEq V]
    (g : Fin r → V →ₗ[ZMod q] ZMod q)
    (hg : ∀ i, Function.Surjective (g i))
    (hpair : ∀ i j, i≠j → Function.Surjective ((g i).prod (g j))) (i : Fin r) :
    avg (fun ω : SlotChoices d K ↦ avg (fun s : ZMod q ↦
      (slotDensity g (fun j t ↦ slotHit d R K q j ω t) i s-
        (1/(2*periodLength (oddLengths d) : ℝ))^(r-1))^2)) ≤
      3*(2*((r-1 : ℕ)*(q-(catalogSet d R K q).card : ℝ)/q+
          2*((r-1 : ℕ) : ℝ)^2*(shortResidues q (R*periodLength (oddLengths d))).card/q)+
        ((r-1 : ℕ) : ℝ)^2*
          (((q-(catalogSet d R K q).card+2*((R-2)*periodLength (oddLengths d))) : ℕ) : ℝ)/q) := by
  have hL := periodLength_pos d i₀
  have : Nonempty (Fin (periodLength (oddLengths d))) := ⟨⟨0,hL⟩⟩
  obtain ⟨chunk,hchunk,hhit,hB,hcollision⟩ := catalog_chunk_system d R K q i₀ hK hq
  have h := averaged_density_variance (g i)
    (fun j : {j : Fin r // j≠i} ↦ g j) (hg i) (fun j ↦ hg j)
    (fun j ↦ hpair i j (Ne.symm j.2))
    (fun j l hjl ↦ hpair j l (fun h ↦ hjl (Subtype.ext h)))
    (catalogSet d R K q) (shortResidues q (R*periodLength (oddLengths d))) chunk hcollision
    (fun j t ω ↦ slotHit d R K q j ω t) (fun j ↦ hhit j)
    (B := (((q-(catalogSet d R K q).card+2*((R-2)*periodLength (oddLengths d))) : ℕ) : ℝ))
    (fun k ↦ by exact_mod_cast hB k)
  have hc : Fintype.card {j : Fin r // j≠i}=r-1 := by
    simp [Fintype.card_subtype_compl]
  convert h using 1 <;>
    simp only [slotDensity, hc, Fintype.card_prod, Fintype.card_fin,Fintype.card_bool,ZMod.card,
      Nat.cast_mul, Nat.cast_ofNat, mul_comm (periodLength (oddLengths d) : ℝ) 2]

lemma concrete_slot_vertices_card {r q : ℕ} [Fact q.Prime] (d : Fin r → ℕ)
    (R K : ℕ) (hq : 2*(K*(R*periodLength (oddLengths d)))<q) (ω : SlotChoices d K) :
    (slotVertices (fun i t ↦ slotHit d R K q i ω t)).card=r*K*(R-1) := by
  rw [slotVertices_card]
  simp only [slotHit_card d R K q _ hq ω,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul, Nat.cast_id]
  ring

end
end AsymptoticallyMinimalLittlewood.Packing

end OAI



namespace OAI

universe uV

/-! Parameter choices for the concrete signed-slot packing. The chunk
length is chosen first and remains fixed while the prime modulus grows. -/
namespace AsymptoticallyMinimalLittlewood.Packing
noncomputable section
open Filter Topology
open scoped BigOperators

def chunkCount (B q : ℕ) : ℕ := (q-1)/B

lemma chunkCount_bounds {B q : ℕ} (hB : 0<B) (hq : 0<q) :
    B*chunkCount B q<q ∧ q≤B*(chunkCount B q+1) := by
  have hm := Nat.mod_lt (q-1) hB
  have he := Nat.mod_add_div (q-1) B
  dsimp [chunkCount]
  constructor
  · have hd := Nat.mul_div_le (q-1) B
    omega
  · nlinarith only [hm,he,show q-1+1=q by omega]

lemma chunkCount_pos {B q : ℕ} (hB : 0<B) (hq : B<q) : 0<chunkCount B q := by
  exact Nat.div_pos (by omega) hB

lemma chunkCount_ratio_error {B q : ℕ} (hB : 0<B) (hq : 0<q) :
    |(chunkCount B q : ℝ)/q-1/(B : ℝ)|≤1/(q : ℝ) := by
  obtain ⟨hlo,hhi⟩ := chunkCount_bounds hB hq
  have hB' : (0 : ℝ)<B := by exact_mod_cast hB
  have hq' : (0 : ℝ)<q := by exact_mod_cast hq
  have hlo' : (B : ℝ)*chunkCount B q≤q := by exact_mod_cast hlo.le
  have hhi' : (q : ℝ)≤B*(chunkCount B q+1) := by exact_mod_cast hhi
  rw [abs_le]
  constructor
  · apply (mul_le_mul_iff_of_pos_right (mul_pos hB' hq')).mp
    field_simp
    nlinarith only [hhi']
  · apply (mul_le_mul_iff_of_pos_right (mul_pos hB' hq')).mp
    field_simp
    nlinarith only [hlo']

lemma chunkCount_ratio_tendsto {B : ℕ} (hB : 0<B) :
    Tendsto (fun q : ℕ ↦ (chunkCount B q : ℝ)/q) atTop (𝓝 (1/(B : ℝ))) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero' (Filter.Eventually.of_forall (fun q ↦ norm_nonneg _))
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with q hq
    simpa only [Real.norm_eq_abs] using chunkCount_ratio_error hB hq
  · exact tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop

def packingAV (r L R q : ℕ) : ℝ :=
  let k := (chunkCount (2*R*L) q : ℝ)/(q : ℝ)
  let u := 1/(q : ℝ)
  3*(2*(((r-1 : ℕ) : ℝ)*(1-2*((R : ℝ)-2)*L*k)+
    2*((r-1 : ℕ) : ℝ)^2*(2*(R : ℝ)*L+1)*u)+
    ((r-1 : ℕ) : ℝ)^2*(1-2*((R : ℝ)-2)*L*k+2*((R : ℝ)-2)*L*u))

def packingNV (r L R q : ℕ) : ℝ :=
  (r : ℝ)*((R : ℝ)-1)*((chunkCount (2*R*L) q : ℝ)/(q : ℝ))

def packingALimit (r R : ℕ) : ℝ :=
  6*(2*((r-1 : ℕ) : ℝ)+((r-1 : ℕ) : ℝ)^2)/(R : ℝ)

def packingNLimit (r L R : ℕ) : ℝ :=
  (r : ℝ)*(1-1/(R : ℝ))/(2*(L : ℝ))

lemma packingAV_tendsto {r L R : ℕ} (hL : 0<L) (hR : 0<R) :
    Tendsto (packingAV r L R) atTop (𝓝 (packingALimit r R)) := by
  have hk := chunkCount_ratio_tendsto (show 0<2*R*L by positivity)
  have hq : Tendsto (fun q : ℕ ↦ 1/(q : ℝ)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  let a := ((r-1 : ℕ) : ℝ)
  let c := 2*((R : ℝ)-2)*L
  have hb := tendsto_const_nhds (x := (1 : ℝ)) |>.sub (hk.const_mul c)
  have ht := (((hb.const_mul a).add (hq.const_mul (2*a^2*(2*(R : ℝ)*L+1)))).const_mul 2 |>.add
    ((hb.add (hq.const_mul c)).const_mul (a^2))).const_mul 3
  have he : 3*(2*(a*(1-c*(1/((2*R*L : ℕ) : ℝ)))+
      2*a^2*(2*(R : ℝ)*L+1)*0)+a^2*(1-c*(1/((2*R*L : ℕ) : ℝ))+c*0)) =
      packingALimit r R := by
    dsimp [a,c,packingALimit]
    have hRn : (R : ℝ)≠0 := by exact_mod_cast hR.ne'
    have hLn : (L : ℝ)≠0 := by exact_mod_cast hL.ne'
    push_cast
    field_simp
    ring
  rw [he] at ht
  exact ht

lemma packingNV_tendsto {r L R : ℕ} (hL : 0<L) (hR : 0<R) :
    Tendsto (packingNV r L R) atTop (𝓝 (packingNLimit r L R)) := by
  have hk := chunkCount_ratio_tendsto (show 0<2*R*L by positivity)
  have ht := hk.const_mul ((r : ℝ)*((R : ℝ)-1))
  have he : (r : ℝ)*((R : ℝ)-1)*(1/((2*R*L : ℕ) : ℝ))=packingNLimit r L R := by
    dsimp [packingNLimit]
    have hRn : (R : ℝ)≠0 := by exact_mod_cast hR.ne'
    have hLn : (L : ℝ)≠0 := by exact_mod_cast hL.ne'
    push_cast
    field_simp

  rw [he] at ht
  exact ht

lemma packingALimit_tendsto (r : ℕ) :
    Tendsto (packingALimit r) atTop (𝓝 (0 : ℝ)) := by
  exact tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop

lemma packingNLimit_tendsto (r L : ℕ) :
    Tendsto (packingNLimit r L) atTop (𝓝 ((r : ℝ)/(2*L))) := by
  have hq : Tendsto (fun R : ℕ ↦ 1/(R : ℝ)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  unfold packingNLimit
  simpa only [sub_zero, mul_one] using
    (((tendsto_const_nhds (x := (1 : ℝ))).sub hq).const_mul (r : ℝ)).div_const (2*L)

def packingBV (r L R : ℕ) (e p : ℝ) (q : ℕ) : ℝ :=
  (r : ℝ)*max (packingAV r L R q) 0/(e*p/2)^2

def packingBLimit (r R : ℕ) (e p : ℝ) : ℝ :=
  (r : ℝ)*packingALimit r R/(e*p/2)^2

lemma packingBV_nonneg (r L R q : ℕ) (e p : ℝ) :
    0≤packingBV r L R e p q := by
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (le_max_right _ _)) (sq_nonneg _)

lemma packingBV_tendsto {r L R : ℕ} (hL : 0<L) (hR : 0<R) (e p : ℝ) :
    Tendsto (packingBV r L R e p) atTop (𝓝 (packingBLimit r R e p)) := by
  have hA : 0≤packingALimit r R := by unfold packingALimit; positivity
  have h := (((packingAV_tendsto (r := r) hL hR).max
    (tendsto_const_nhds (x := (0 : ℝ)))).const_mul (r : ℝ)).div_const ((e*p/2)^2)
  unfold packingBV packingBLimit
  simpa only [max_eq_left hA] using h

lemma packingBLimit_tendsto (r : ℕ) (e p : ℝ) :
    Tendsto (fun R ↦ packingBLimit r R e p) atTop (𝓝 (0 : ℝ)) := by
  have h := ((packingALimit_tendsto r).const_mul (r : ℝ)).div_const ((e*p/2)^2)
  unfold packingBLimit
  simpa only [mul_zero,zero_div] using h

lemma packing_choose_R {r L : ℕ} (hr : 0<r) (hL : 0<L)
    {e p η t : ℝ} (he : 0<e) (hp : 0<p)
    (hmargin : (r : ℝ)*t<(1-η)*((r : ℝ)/(2*L))) :
    ∃ R : ℕ, 3≤R ∧
      packingBLimit r R e p<e*p/2 ∧
      0<packingNLimit r L R-packingBLimit r R e p ∧
      packingNLimit r L R<(r : ℝ) ∧
      (r : ℝ)*t<(1-η)*(packingNLimit r L R-packingBLimit r R e p) := by
  have hNpos : (0 : ℝ)<(r : ℝ)/(2*L) := by positivity
  have hNlt : (r : ℝ)/(2*L)<r := by
    have hl : (1 : ℝ)≤L := by exact_mod_cast hL
    have hr' : (0 : ℝ)<r := by exact_mod_cast hr
    apply (div_lt_iff₀ (by positivity : (0 : ℝ)<2*L)).mpr
    nlinarith
  have hN := packingNLimit_tendsto r L
  have hB := packingBLimit_tendsto r e p
  have hS := hN.sub hB
  have hSp : Tendsto (fun R ↦ packingNLimit r L R-packingBLimit r R e p) atTop
      (𝓝 ((r : ℝ)/(2*L))) := by simpa using hS
  have hev : ∀ᶠ R : ℕ in atTop, 3≤R ∧
      packingBLimit r R e p<e*p/2 ∧
      0<packingNLimit r L R-packingBLimit r R e p ∧
      packingNLimit r L R<(r : ℝ) ∧
      (r : ℝ)*t<(1-η)*(packingNLimit r L R-packingBLimit r R e p) := by
    filter_upwards [eventually_ge_atTop 3,
      hB.eventually (gt_mem_nhds (show (0 : ℝ)<e*p/2 by positivity)),
      hSp.eventually (lt_mem_nhds hNpos),hN.eventually (gt_mem_nhds hNlt),
      (hSp.const_mul (1-η)).eventually (lt_mem_nhds hmargin)] with R hR h1 h2 h3 h4
    exact ⟨hR,h1,h2,h3,h4⟩
  exact hev.exists

lemma packing_eventual_parameters {r L R : ℕ} (hL : 0<L) (hR : 0<R)
    {e p η t T : ℝ} (he : 0<e) (hp : 0<p)
    (hB : packingBLimit r R e p<e*p/2)
    (hS : 0<packingNLimit r L R-packingBLimit r R e p)
    (hN : packingNLimit r L R<(r : ℝ))
    (hM : (r : ℝ)*t<(1-η)*(packingNLimit r L R-packingBLimit r R e p)) :
    ∀ᶠ q : ℕ in atTop,
      1/(q : ℝ)≤e*p ∧ T/(q : ℝ)≤p ∧
      T/(q : ℝ)≤packingNV r L R q-packingBV r L R e p q ∧
      packingBV r L R e p q≤e*p/2 ∧ packingNV r L R q≤(r : ℝ) ∧
      (r : ℝ)*t<(1-η)*(packingNV r L R q-packingBV r L R e p q) := by
  have hNt := packingNV_tendsto (r := r) hL hR
  have hBt := packingBV_tendsto (r := r) hL hR e p
  have hSt := hNt.sub hBt
  have hq : Tendsto (fun q : ℕ ↦ 1/(q : ℝ)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hT : Tendsto (fun q : ℕ ↦ T/(q : ℝ)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  filter_upwards [hq.eventually (gt_mem_nhds (mul_pos he hp)),
    hT.eventually (gt_mem_nhds hp),hT.eventually_lt hSt hS,
    hBt.eventually (gt_mem_nhds hB),hNt.eventually (gt_mem_nhds hN),
    (hSt.const_mul (1-η)).eventually (lt_mem_nhds hM)] with q h1 h2 h3 h4 h5 h6
  exact ⟨h1.le,h2.le,h3.le,h4.le,h5.le,h6⟩

end
end AsymptoticallyMinimalLittlewood.Packing

namespace AsymptoticallyMinimalLittlewood.Packing
noncomputable section
open scoped BigOperators
open Finset Nibble Filter Topology
open Classical

lemma concrete_slot_variance_le_av {r q : ℕ} [Fact q.Prime]
    (d : Fin r → ℕ) (R : ℕ) (i₀ : Fin r) (hR : 2≤R)
    (hq' : 2*R*periodLength (oddLengths d)<q)
    {V : Type uV} [AddCommGroup V] [Module (ZMod q) V] [Fintype V] [DecidableEq V]
    (g : Fin r → V →ₗ[ZMod q] ZMod q)
    (hg : ∀ i, Function.Surjective (g i))
    (hpair : ∀ i j, i≠j → Function.Surjective ((g i).prod (g j))) (i : Fin r) :
    let K := chunkCount (2*R*periodLength (oddLengths d)) q
    avg (fun ω : SlotChoices d K ↦ avg (fun s : ZMod q ↦
      (slotDensity g (fun j t ↦ slotHit d R K q j ω t) i s-
        (1/(2*periodLength (oddLengths d) : ℝ))^(r-1))^2)) ≤
      packingAV r (periodLength (oddLengths d)) R q := by
  dsimp only
  let L := periodLength (oddLengths d)
  let K := chunkCount (2*R*L) q
  have hL : 0<L := periodLength_pos d i₀
  have hq0 : 0<q := (Fact.out : q.Prime).pos
  have hq : 2*(K*(R*L))<q := by
    have h := (chunkCount_bounds (show 0<2*R*L by positivity) hq0).1
    dsimp [K]
    nlinarith only [h]
  have hK : 0<K := chunkCount_pos (by positivity) hq'
  have h := concrete_slot_variance d R K i₀ hK hq g hg hpair i
  have hcat : (catalogSet d R K q).card≤q := by
    simpa only [ZMod.card] using (Finset.card_le_univ (catalogSet d R K q))
  have hc := catalogSet_card d R K q i₀ hq
  have hs : ((shortResidues q (R*L)).card : ℝ)≤2*(R : ℝ)*L+1 := by
    simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one,mul_assoc] using
      (Nat.cast_le.mpr (shortResidues_card q (R*L)) : ((shortResidues q (R*L)).card : ℝ)≤((2*(R*L)+1 : ℕ) : ℝ))
  have hR2 : ((R-2 : ℕ) : ℝ)=(R : ℝ)-2 := by rw [Nat.cast_sub hR]; norm_num
  have hqpos : (0 : ℝ)<q := by exact_mod_cast hq0
  apply h.trans
  rw [Nat.cast_add,Nat.cast_sub hcat]
  simp only [hc,Nat.cast_mul,Nat.cast_ofNat,hR2]
  change 3*(2*(((r-1 : ℕ) : ℝ)*((q : ℝ)-2*(K : ℝ)*(((R : ℝ)-2)*L))/q+
      2*((r-1 : ℕ) : ℝ)^2*((shortResidues q (R*L)).card : ℝ)/q)+
      ((r-1 : ℕ) : ℝ)^2*((q : ℝ)-2*(K : ℝ)*(((R : ℝ)-2)*L)+2*(((R : ℝ)-2)*L))/q)≤_
  have hshort := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hs (by positivity : (0 : ℝ)≤2*((r-1 : ℕ) : ℝ)^2)) hqpos.le
  dsimp [packingAV]
  change _≤3*(2*(((r-1 : ℕ) : ℝ)*(1-2*((R : ℝ)-2)*L*((K : ℝ)/q))+
      2*((r-1 : ℕ) : ℝ)^2*(2*(R : ℝ)*L+1)*(1/q))+
      ((r-1 : ℕ) : ℝ)^2*(1-2*((R : ℝ)-2)*L*((K : ℝ)/q)+2*((R : ℝ)-2)*L*(1/q)))
  have hqne := hqpos.ne'
  field_simp at hshort ⊢
  nlinarith only [hshort]

lemma concrete_slot_nv {r q R : ℕ} [Fact q.Prime]
    (d : Fin r → ℕ) (i₀ : Fin r) (hR : 1≤R)
    (ω : SlotChoices d (chunkCount (2*R*periodLength (oddLengths d)) q)) :
    ((slotVertices (fun i t ↦ slotHit d R
      (chunkCount (2*R*periodLength (oddLengths d)) q) q i ω t)).card : ℝ)=
      (q : ℝ)*packingNV r (periodLength (oddLengths d)) R q := by
  have hL := periodLength_pos d i₀
  have hq0 := (Fact.out : q.Prime).pos
  have hq : 2*(chunkCount (2*R*periodLength (oddLengths d)) q*
      (R*periodLength (oddLengths d)))<q := by
    have h := (chunkCount_bounds (show 0<2*R*periodLength (oddLengths d) by positivity) hq0).1
    nlinarith only [h]
  rw [concrete_slot_vertices_card d R _ hq]
  simp only [Nat.cast_mul,Nat.cast_sub hR,Nat.cast_one]
  unfold packingNV
  have hqne : (q : ℝ)≠0 := by exact_mod_cast hq0.ne'
  field_simp

end
end AsymptoticallyMinimalLittlewood.Packing

end OAI



namespace OAI

namespace AsymptoticallyMinimalLittlewood.Packing
noncomputable section
open scoped BigOperators
open Finset Nibble Filter Topology
open Classical

lemma scaled_slot_conditions {q v e p T n b r : ℝ} (hq : 0<q) (hp : 0<p)
    (hv : q^2≤v) (h1 : 1/q≤e*p) (h2 : T/q≤p) (h3 : T/q≤n-b)
    (h4 : b≤e*p/2) (h5 : n≤r) :
    T≤(v/q)*p ∧ T≤q*n-q*b ∧ v/q^2≤e*((v/q)*p) ∧
      (q*n)*(v/q^2)≤(r/p)*((v/q)*p) ∧
      (q*b)*(v/q^2)≤e*((v/q)*p)/2 := by
  let C := v/q^2
  have hC : 1≤C := (le_div_iff₀ (sq_pos_of_pos hq)).mpr (by simpa using hv)
  have hC0 : 0≤C := le_trans zero_le_one hC
  have hD : (v/q)*p=q*p*C := by dsimp [C]; field_simp
  have h1' : 1≤q*(e*p) := by simpa only [mul_comm] using (div_le_iff₀ hq).mp h1
  have h2' : T≤q*p := by simpa only [mul_comm] using (div_le_iff₀ hq).mp h2
  have h3' : T≤q*(n-b) := by simpa only [mul_comm] using (div_le_iff₀ hq).mp h3
  rw [hD]
  refine ⟨h2'.trans ?_,by nlinarith only [h3'],?_,?_,?_⟩
  · nlinarith only [hC,mul_pos hq hp]
  · change C≤e*(q*p*C)
    have h := mul_le_mul_of_nonneg_right h1' hC0
    nlinarith only [h]
  · change (q*n)*C≤(r/p)*(q*p*C)
    rw [show (r/p)*(q*p*C)=q*r*C by field_simp]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h5 hq.le) hC0
  · change (q*b)*C≤e*(q*p*C)/2
    have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h4 hq.le) hC0
    nlinarith only [h]

lemma choose_matching_loss {r L : ℕ} (hr : 0<r) (hL : 0<L) {t : ℝ}
    (ht0 : 0≤t) (ht : t<1/(2*L : ℝ)) :
    ∃ η : ℝ, 0<η ∧ η≤1 ∧ (r : ℝ)*t<(1-η)*((r : ℝ)/(2*L)) := by
  let η := (1-2*L*t)/2
  have hL' : (0 : ℝ)<2*L := by positivity
  have ht' := (lt_div_iff₀ hL').mp ht
  have hlt : t<(1-η)/(2*L) := by apply (lt_div_iff₀ hL').mpr; dsimp [η]; nlinarith
  have hr' : (0 : ℝ)<r := by exact_mod_cast hr
  refine ⟨η,by dsimp [η]; nlinarith,by dsimp [η]; nlinarith,?_⟩
  calc
    (r : ℝ)*t < r*((1-η)/(2*L)) := mul_lt_mul_of_pos_left hlt hr'
    _ = (1-η)*((r : ℝ)/(2*L)) := by ring

lemma integer_slot_matching {r m : ℕ} (hr : 2≤r)
    (a : Fin r → Fin m → ℤ)
    (ha : ∀ j, (fun k ↦ (a j k : ℚ))≠0)
    (hnp : ∀ j l, j≠l → ∀ c : ℚ,
      (fun k ↦ (a l k : ℚ))≠c • (fun k ↦ (a j k : ℚ)))
    (d : Fin r → ℕ) {t : ℝ} (ht0 : 0<t) (ht : t<1/(2*periodLength (oddLengths d) : ℝ)) :
    ∃ q R K : ℕ, q.Prime ∧ 3≤R ∧ 0<K ∧ 2*(K*(R*periodLength (oddLengths d)))<q ∧
      ∃ ω : SlotChoices d K, ∃ M : Finset (Fin m → ZMod q),
        (∀ y∈M, ∀ i, slotHit d R K q i ω (dotProduct (fun k ↦ (a i k : ZMod q)) y)) ∧
        (∀ y∈M, ∀ z∈M, y≠z → ∀ i,
          dotProduct (fun k ↦ (a i k : ZMod q)) y≠dotProduct (fun k ↦ (a i k : ZMod q)) z) ∧
        t*q<(M.card : ℝ) := by
  classical
  let i₀ : Fin r := ⟨0,by omega⟩
  let i₁ : Fin r := ⟨1,by omega⟩
  have hi : i₀≠i₁ := by intro h; have := congrArg Fin.val h; simp [i₀,i₁] at this
  have hr0 : 0<r := by omega
  let L := periodLength (oddLengths d)
  have hL : 0<L := periodLength_pos d i₀
  let p : ℝ := (1/(2*L : ℝ))^(r-1)
  have hp : 0<p := by dsimp [p]; positivity
  obtain ⟨η,hη,hη₁,hmargin⟩ := choose_matching_loss hr0 hL ht0.le ht
  obtain ⟨e,T,he,hT,hmatch⟩ := random_slot_matching (I := Fin r)
    (by simpa only [Fintype.card_fin] using (show 1≤r by omega)) (K₀ := (r : ℝ)/p) (by positivity) hη hη₁
  obtain ⟨R,hR,hBR,hSR,hNR,hMR⟩ := packing_choose_R hr0 hL he hp hmargin
  have hR0 : 0<R := by omega
  obtain ⟨Q,hQ⟩ := Filter.eventually_atTop.mp (packing_eventual_parameters hL hR0 he hp hBR hSR hNR hMR (T := T))
  obtain ⟨Q₀,hQ₀⟩ := integer_rows_eventual_pair_rank a ha hnp
  obtain ⟨q,hqq,hprime⟩ := Nat.exists_infinite_primes (max Q (max (Q₀+1) (2*R*L+1)))
  have hq0 : 0<q := hprime.pos
  have : Fact q.Prime := ⟨hprime⟩
  have hqpos : (0 : ℝ)<q := by exact_mod_cast hq0
  have hqq' : 2*R*L<q := by omega
  have hqpar := hQ q (by omega)
  let K := chunkCount (2*R*L) q
  have hK : 0<K := chunkCount_pos (by positivity) hqq'
  have hqslot : 2*(K*(R*L))<q := by
    have h := (chunkCount_bounds (show 0<2*R*L by positivity) hq0).1
    nlinarith only [h]
  let g : Fin r → (Fin m → ZMod q) →ₗ[ZMod q] ZMod q :=
    fun i ↦ dotForm (fun k ↦ (a i k : ZMod q))
  have hpair : ∀ i j, i≠j → Function.Surjective ((g i).prod (g j)) :=
    hQ₀ q inferInstance (by omega)
  have hg (i : Fin r) : Function.Surjective (g i) := by
    have hj : ∃ j : Fin r, i≠j := by
      by_cases h : i=i₀
      · exact ⟨i₁,h ▸ hi⟩
      · exact ⟨i₀,h⟩
    obtain ⟨j,hj⟩ := hj
    intro s
    obtain ⟨y,hy⟩ := hpair i j hj (s,0)
    exact ⟨y,congrArg Prod.fst hy⟩
  have hV : (q : ℝ)^2≤Fintype.card (Fin m → ZMod q) := by
    have h := Fintype.card_le_of_surjective _ (hpair i₀ i₁ hi)
    have h' : q*q≤Fintype.card (Fin m → ZMod q) := by
      simpa only [Fintype.card_prod,ZMod.card] using h
    rw [pow_two]
    exact_mod_cast h'
  have hc := scaled_slot_conditions hqpos hp hV hqpar.1 hqpar.2.1 hqpar.2.2.1
    hqpar.2.2.2.1 hqpar.2.2.2.2.1
  have : Nonempty (Fin L) := ⟨⟨0,hL⟩⟩
  obtain ⟨ω,M,hM,hdis,hsize⟩ := hmatch g (fun i s ω ↦ slotHit d R K q i ω s)
    p (max (packingAV r L R q) 0) ((q : ℝ)*packingBV r L R e p q) ((q : ℝ)*packingNV r L R q)
    hg hpair hp (mul_nonneg hqpos.le (packingBV_nonneg r L R q e p))
    (fun i ↦ (concrete_slot_variance_le_av d R i₀ (by omega) hqq' g hg hpair i).trans (le_max_left _ _))
    (by simp only [Fintype.card_fin,ZMod.card,packingBV]; ring_nf; exact le_rfl)
    (fun ω ↦ concrete_slot_nv d i₀ (by omega) ω)
    (by simpa only [ZMod.card] using hc.1)
    hc.2.1
    (by simpa only [ZMod.card] using hc.2.2.1)
    (by simpa only [ZMod.card] using hc.2.2.2.1)
    (by simpa only [ZMod.card] using hc.2.2.2.2)
  refine ⟨q,R,K,hprime,hR,hK,hqslot,ω,M,?_,?_,?_⟩
  · intro y hy i
    have hm := hM hy
    simp only [slotEdges,Finset.mem_filter,Finset.mem_univ,true_and] at hm
    exact hm i
  · intro y hy z hz hyz i hEq
    have hd := hdis hy hz hyz
    have hyv : (i,g i y)∈slotSupport g y := by simp [slotSupport]
    change g i y=g i z at hEq
    have hzv : (i,g i y)∈slotSupport g z := by rw [hEq]; simp [slotSupport]
    exact Finset.disjoint_left.mp hd hyv hzv
  · have hstrict := mul_lt_mul_of_pos_right hqpar.2.2.2.2.2 hqpos
    simp only [Fintype.card_fin] at hsize
    have hrpos : (0 : ℝ)<r := by exact_mod_cast hr0
    nlinarith only [hstrict,hsize,hrpos]

end
end AsymptoticallyMinimalLittlewood.Packing

namespace AsymptoticallyMinimalLittlewood.Packing
noncomputable section
open scoped BigOperators
open Finset

def circleInterval (c : UnitAddCircle) (ℓ : ℝ) : Set UnitAddCircle :=
  {z | ∃ t : ℝ, |t|≤ℓ/2 ∧ z=c+(t : UnitAddCircle)}

lemma circleInterval_disjoint_of_lifts {a b u v : ℝ}
    (ha : |a|+u/2<1/2) (hb : |b|+v/2<1/2) (hsep : (u+v)/2< |a-b|) :
    Disjoint (circleInterval (a : UnitAddCircle) u) (circleInterval (b : UnitAddCircle) v) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨t,ht,hz⟩ ⟨s,hs,hz'⟩
  have he : ((a+t : ℝ) : UnitAddCircle)=((b+s : ℝ) : UnitAddCircle) := by
    simpa only [AddCircle.coe_add] using hz.symm.trans hz'
  have ht' : |a+t|<1/2 := by linarith [abs_add_le a t]
  have hs' : |b+s|<1/2 := by linarith [abs_add_le b s]
  have he' : a+t=b+s := (AddCircle.coe_eq_coe_iff_of_mem_Ico
    (a := (-1/2 : ℝ)) (p := (1 : ℝ))
    (show a+t∈Set.Ico (-1/2 : ℝ) (-1/2+1) from ⟨by linarith [(abs_lt.mp ht').1],by linarith [(abs_lt.mp ht').2]⟩)
    (show b+s∈Set.Ico (-1/2 : ℝ) (-1/2+1) from ⟨by linarith [(abs_lt.mp hs').1],by linarith [(abs_lt.mp hs').2]⟩)).mp he
  have h : |a-b|≤(u+v)/2 := by
    rw [show a-b=s-t by linarith]
    have hst := abs_sub s t
    linarith
  exact (not_lt_of_ge h) hsep

lemma slots_separated {r K R : ℕ} (d : Fin r → ℕ) (ω : SlotChoices d K)
    (k l : Fin K) (p t : Fin (R-1)) (i j : Fin r)
    (hne : (k,p,i)≠(l,t,j)) :
    slotLeft (oddLengths d) R (ω k).1 k p i+oddLengths d i≤
      slotLeft (oddLengths d) R (ω l).1 l t j ∨
    slotLeft (oddLengths d) R (ω l).1 l t j+oddLengths d j≤
      slotLeft (oddLengths d) R (ω k).1 k p i := by
  have hp : (p : ℕ)+1<R := by omega
  have ht : (t : ℕ)+1<R := by omega
  rcases lt_trichotomy k l with hkl | rfl | hlk
  · exact Or.inl (slots_separated_chunks _ R (ω k).1.isLt hp hkl i j).le
  · rcases lt_trichotomy p t with hpt | rfl | htp
    · exact Or.inl (slots_separated_same_chunk _ R (ω k).1 k (i := i) (j := j) (Or.inl hpt))
    · have hij : i≠j := fun h ↦ hne (by rw [h])
      rcases lt_or_gt_of_ne hij with hij | hji
      · exact Or.inl (slots_separated_same_chunk _ R (ω k).1 k (i := i) (j := j) (Or.inr ⟨rfl,hij⟩))
      · exact Or.inr (slots_separated_same_chunk _ R (ω k).1 k (i := j) (j := i) (Or.inr ⟨rfl,hji⟩))
    · exact Or.inr (slots_separated_same_chunk _ R (ω k).1 k (i := j) (j := i) (Or.inl htp))
  · exact Or.inr (slots_separated_chunks _ R (ω l).1.isLt ht hlk j i).le

lemma actual_centers_separated {r K R : ℕ} (d : Fin r → ℕ) (ω : SlotChoices d K)
    (k l : Fin K) (p t : Fin (R-1)) (i j : Fin r)
    (hne : (k,p,i)≠(l,t,j)) :
    ((oddLengths d i : ℝ)+oddLengths d j)/2 ≤
      |(siteCenter d R (ω k).1 k p i : ℝ)-siteCenter d R (ω l).1 l t j| := by
  obtain h | h := slots_separated d ω k l p t i j hne
  · have h' : ((slotLeft (oddLengths d) R (ω k).1 k p i : ℕ) : ℝ)+oddLengths d i≤
        slotLeft (oddLengths d) R (ω l).1 l t j := by exact_mod_cast h
    apply le_trans _ (neg_le_abs _)
    dsimp [siteCenter,oddLengths] at *
    push_cast at *
    linarith
  · have h' : ((slotLeft (oddLengths d) R (ω l).1 l t j : ℕ) : ℝ)+oddLengths d j≤
        slotLeft (oddLengths d) R (ω k).1 k p i := by exact_mod_cast h
    apply le_trans _ (le_abs_self _)
    dsimp [siteCenter,oddLengths] at *
    push_cast at *
    linarith

lemma siteCenter_margin {r K R : ℕ} (d : Fin r → ℕ) (ω : SlotChoices d K)
    (k : Fin K) (p : Fin (R-1)) (i : Fin r) :
    (oddLengths d i : ℝ)/2 < siteCenter d R (ω k).1 k p i ∧
    (siteCenter d R (ω k).1 k p i : ℝ)+(oddLengths d i : ℝ)/2 <
      K*(R*periodLength (oddLengths d)) := by
  have h := (slotLeft_bounds (oddLengths d) R (chunk := (k : ℕ)) (ω k).1.isLt
    (show (p : ℕ)+1<R by omega) i).2
  have hk : ((k : ℕ)+1)*(R*periodLength (oddLengths d))≤K*(R*periodLength (oddLengths d)) :=
    Nat.mul_le_mul_right _ (by omega)
  have hb : (slotLeft (oddLengths d) R (ω k).1 k p i : ℝ)+oddLengths d i+1≤
      K*(R*periodLength (oddLengths d)) := by
    have hh : slotLeft (oddLengths d) R (ω k).1 k p i+oddLengths d i+1≤K*(R*periodLength (oddLengths d)) := by omega
    exact_mod_cast hh
  have hz : (0 : ℝ) ≤ slotLeft (oddLengths d) R (ω k).1 k p i := Nat.cast_nonneg _
  dsimp [siteCenter,oddLengths] at *
  push_cast at *
  constructor <;> linarith

def signedLift (e : Bool) (x : ℝ) : ℝ := if e then x else -x

lemma signedLift_abs (e : Bool) (x : ℝ) : |signedLift e x|=|x| := by cases e <;> simp [signedLift]

lemma signedLift_separation {x y u v : ℝ} (hx : u/2<x) (hy : v/2<y)
    (e f : Bool) (h : e=f → (u+v)/2≤|x-y|) :
    (u+v)/2≤|signedLift e x-signedLift f y| := by
  cases e <;> cases f <;> simp only [signedLift,Bool.false_eq_true,↓reduceIte] at *
  · simpa only [neg_sub_neg,abs_sub_comm] using h trivial
  · have hh : (u+v)/2<x+y := by linarith
    have hl := le_abs_self (x+y)
    rw [show -x-y=-(x+y) by ring,abs_neg]
    exact hh.le.trans hl
  · have hh : (u+v)/2<x+y := by linarith
    rw [sub_neg_eq_add]
    exact hh.le.trans (le_abs_self _)
  · exact h trivial

lemma circle_slots_disjoint {r K R q : ℕ} (d : Fin r → ℕ) (ω : SlotChoices d K)
    (hq : 2*(K*(R*periodLength (oddLengths d)))<q)
    (k l : Fin K) (p t : Fin (R-1)) (i j : Fin r) (e f : Bool)
    (hne : (e,k,p,i)≠(f,l,t,j)) {u v : ℝ}
    (hu : u<(oddLengths d i : ℝ)/q) (hv : v<(oddLengths d j : ℝ)/q) :
    Disjoint (circleInterval ((signedLift e (siteCenter d R (ω k).1 k p i)/q : ℝ) : UnitAddCircle) u)
      (circleInterval ((signedLift f (siteCenter d R (ω l).1 l t j)/q : ℝ) : UnitAddCircle) v) := by
  have hq0 : (0 : ℝ)<q := by exact_mod_cast (show 0<q by omega)
  have hq' : (2 : ℝ)*(K*(R*periodLength (oddLengths d)))<q := by exact_mod_cast hq
  have ⟨hxi,hx⟩ := siteCenter_margin d ω k p i
  have ⟨hyj,hy⟩ := siteCenter_margin d ω l t j
  have hxi0 : (0 : ℝ)<siteCenter d R (ω k).1 k p i := lt_trans (by dsimp [oddLengths]; positivity) hxi
  have hyj0 : (0 : ℝ)<siteCenter d R (ω l).1 l t j := lt_trans (by dsimp [oddLengths]; positivity) hyj
  apply circleInterval_disjoint_of_lifts
  · rw [abs_div,signedLift_abs,abs_of_pos hq0,abs_of_pos hxi0]
    have hu' := (lt_div_iff₀ hq0).mp hu
    apply (lt_div_iff₀ (by norm_num : (0 : ℝ)<2)).mpr
    have hxx : 2*(siteCenter d R (ω k).1 k p i : ℝ)+u*q<q := by linarith
    have hd : (2*(siteCenter d R (ω k).1 k p i : ℝ)+u*q)/q<1 := (div_lt_iff₀ hq0).mpr (by simpa using hxx)
    have he : (siteCenter d R (ω k).1 k p i / (q : ℝ)+u/2)*2 = (2*(siteCenter d R (ω k).1 k p i : ℝ)+u*q)/q := by field_simp
    rw [he]
    exact hd
  · rw [abs_div,signedLift_abs,abs_of_pos hq0,abs_of_pos hyj0]
    have hv' := (lt_div_iff₀ hq0).mp hv
    apply (lt_div_iff₀ (by norm_num : (0 : ℝ)<2)).mpr
    have hyy : 2*(siteCenter d R (ω l).1 l t j : ℝ)+v*q<q := by linarith
    have hd : (2*(siteCenter d R (ω l).1 l t j : ℝ)+v*q)/q<1 := (div_lt_iff₀ hq0).mpr (by simpa using hyy)
    have he : (siteCenter d R (ω l).1 l t j / (q : ℝ)+v/2)*2 = (2*(siteCenter d R (ω l).1 l t j : ℝ)+v*q)/q := by field_simp
    rw [he]
    exact hd
  · rw [← sub_div,abs_div,abs_of_pos hq0]
    apply (lt_div_iff₀ hq0).mpr
    have hu' := (lt_div_iff₀ hq0).mp hu
    have hv' := (lt_div_iff₀ hq0).mp hv
    have hsep := signedLift_separation hxi hyj e f (by
      intro hef
      apply actual_centers_separated d ω k l p t i j
      intro heq
      apply hne
      obtain ⟨rfl,rfl,rfl⟩ := Prod.mk.inj heq |>.imp_left id
      exact hef ▸ rfl)
    nlinarith only [hu',hv',hsep]

end
end AsymptoticallyMinimalLittlewood.Packing

namespace AsymptoticallyMinimalLittlewood.Packing
noncomputable section
open scoped BigOperators
open Finset

def signedCircle (e : Bool) (z : UnitAddCircle) : UnitAddCircle := if e then z else -z

lemma zmod_dot_circle {q m : ℕ} [NeZero q] (a : Fin m → ℤ) (y : Fin m → ZMod q) :
    ZMod.toAddCircle (dotProduct (fun k ↦ (a k : ZMod q)) y)=
      ∑ k, (a k) • ZMod.toAddCircle (y k) := by
  simp only [dotProduct,← zsmul_eq_mul,map_sum,map_zsmul]

lemma signedSite_circle {q : ℕ} [NeZero q] (e f : Bool) (c : ℕ) :
    signedCircle e (ZMod.toAddCircle (signedSite q f c))=
      ((signedLift (e==f) c/(q : ℝ) : ℝ) : UnitAddCircle) := by
  cases e <;> cases f <;>
    simp [signedCircle,signedSite,signedLift,ZMod.toAddCircle_natCast,neg_div]

theorem signed_interval_packing {r m : ℕ} (hr : 2≤r)
    (a : Fin r → Fin m → ℤ)
    (ha : ∀ j, (fun k ↦ (a j k : ℚ))≠0)
    (hnp : ∀ j l, j≠l → ∀ c : ℚ,
      (fun k ↦ (a l k : ℚ))≠c • (fun k ↦ (a j k : ℚ)))
    (w : Fin r → ℝ) (hw : ∀ i, 0<w i) (hs : 2*∑ i, w i<1) :
    ∃ H : ℕ, 1≤H ∧ ∃ θ : Fin H → Fin m → UnitAddCircle,
      ∀ e f : Bool, ∀ i j : Fin r, ∀ h v : Fin H, (e,i,h)≠(f,j,v) →
        Disjoint (circleInterval (signedCircle e (∑ k, a i k • θ h k)) (w i/H))
          (circleInterval (signedCircle f (∑ k, a j k • θ v k)) (w j/H)) := by
  classical
  have : Nonempty (Fin r) := ⟨⟨0,by omega⟩⟩
  obtain ⟨d,hd⟩ := choose_odd_lengths w hw hs
  let L := periodLength (oddLengths d)
  have hLi (i : Fin r) : (0 : ℝ)<oddLengths d i := by dsimp [oddLengths]; positivity
  have hL : (0 : ℝ)<L := by exact_mod_cast periodLength_pos d (Classical.arbitrary (Fin r))
  have hdr (i : Fin r) : w i/(oddLengths d i : ℝ)<1/(2*L) := by
    have hdi : w i<(oddLengths d i : ℝ)/(2*L) := by
      simpa only [L,periodLength,oddLengths,Nat.cast_sum,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] using hd i
    rw [div_lt_div_iff₀ (hLi i) (by positivity)]
    have hh := (lt_div_iff₀ (by positivity : (0 : ℝ)<2*L)).mp hdi
    simpa only [one_mul] using hh
  obtain ⟨i₀,_,himax⟩ := Finset.exists_max_image Finset.univ (fun i ↦ w i/(oddLengths d i : ℝ)) Finset.univ_nonempty
  obtain ⟨t,htlow,hthi⟩ := exists_between (hdr i₀)
  have ht0 : 0<t := (div_pos (hw i₀) (hLi i₀)).trans htlow
  have hti (i : Fin r) : w i/(oddLengths d i : ℝ)<t := (himax i (Finset.mem_univ i)).trans_lt htlow
  obtain ⟨q,R,K,hq,hR,hK,hqslot,ω,M,hhit,hdis,hsize⟩ := integer_slot_matching hr a ha hnp d ht0 hthi
  have : NeZero q := ⟨hq.ne_zero⟩
  have hq0 : (0 : ℝ)<q := by exact_mod_cast hq.pos
  have hM0 : 0<M.card := by have hh := (mul_pos ht0 hq0).trans hsize; exact_mod_cast hh
  have hMpos : (0 : ℝ)<M.card := by exact_mod_cast hM0
  let y : Fin M.card → M := M.equivFin.symm
  have hyinj : Function.Injective y := M.equivFin.symm.injective
  have hyhit (i : Fin r) (h : Fin M.card) : ∃ k : Fin K, ∃ p : Fin (R-1),
      dotProduct (fun k ↦ (a i k : ZMod q)) (y h).val=
        signedSite q (ω k).2 (siteCenter d R (ω k).1 k p i) := hhit (y h) (y h).property i
  choose k p hcenter using hyhit
  let θ : Fin M.card → Fin m → UnitAddCircle := fun h l ↦ ZMod.toAddCircle ((y h).val l)
  have hwidth (i : Fin r) : w i/(M.card : ℝ)<(oddLengths d i : ℝ)/q := by
    have hh := (div_lt_iff₀ (hLi i)).mp (hti i)
    have hhmul := mul_lt_mul_of_pos_right hh hq0
    have hsmul := mul_lt_mul_of_pos_left hsize (hLi i)
    rw [div_lt_div_iff₀ hMpos hq0]
    nlinarith only [hhmul,hsmul]
  have hcircle (e : Bool) (i : Fin r) (h : Fin M.card) :
      signedCircle e (∑ l, a i l • θ h l)=
        ((signedLift (e==(ω (k i h)).2) (siteCenter d R (ω (k i h)).1 (k i h) (p i h) i)/q : ℝ) : UnitAddCircle) := by
    change signedCircle e (∑ l, a i l • ZMod.toAddCircle ((y h).val l))=_
    rw [← zmod_dot_circle,hcenter i h]
    exact signedSite_circle e (ω (k i h)).2 _
  refine ⟨M.card,by omega,θ,?_⟩
  intro e f i j h v hne
  rw [hcircle,hcircle]
  apply circle_slots_disjoint d ω hqslot (k i h) (k j v) (p i h) (p j v) i j
    (e==(ω (k i h)).2) (f==(ω (k j v)).2) ?_ (hwidth i) (hwidth j)
  intro heq
  obtain ⟨hef,hpair⟩ := Prod.mk.inj heq
  obtain ⟨hk,hpair⟩ := Prod.mk.inj hpair
  obtain ⟨hp,hij⟩ := Prod.mk.inj hpair
  subst j
  have hdot : dotProduct (fun l ↦ (a i l : ZMod q)) (y h).val=
      dotProduct (fun l ↦ (a i l : ZMod q)) (y v).val := by
    rw [hcenter,hcenter,hk,hp]
  have hy : (y h).val=(y v).val := by
    by_contra hy
    exact hdis (y h) (y h).property (y v) (y v).property hy i hdot
  have hv : h=v := hyinj (Subtype.ext hy)
  subst v
  have hef' : e=f := by cases e <;> cases f <;> cases (ω (k i h)).2 <;> simp_all
  exact hne (by rw [hef'])

end
end AsymptoticallyMinimalLittlewood.Packing

namespace AsymptoticallyMinimalLittlewood.Packing
noncomputable section
open scoped BigOperators
open Finset

lemma signed_interval_packing_fintype {I J : Type} [Fintype I] [Fintype J]
    (hr : 2≤Fintype.card I) (a : I → J → ℤ)
    (ha : ∀ i, a i≠0)
    (hnp : ∀ i j, i≠j → ∀ c : ℝ, ¬∀ k, (a j k : ℝ)=c*(a i k : ℝ))
    (w : I → ℝ) (hw : ∀ i, 0<w i) (hs : 2*∑ i, w i<1) :
    ∃ H : ℕ, 1≤H ∧ ∃ θ : Fin H → J → UnitAddCircle,
      ∀ e f : Bool, ∀ i j : I, ∀ h v : Fin H, (e,i,h)≠(f,j,v) →
        Disjoint (circleInterval (signedCircle e (∑ k, a i k • θ h k)) (w i/H))
          (circleInterval (signedCircle f (∑ k, a j k • θ v k)) (w j/H)) := by
  classical
  let E := Fintype.equivFin I
  let F := Fintype.equivFin J
  let A (i : Fin (Fintype.card I)) (k : Fin (Fintype.card J)) := a (E.symm i) (F.symm k)
  have hA (i) : (fun k ↦ (A i k : ℚ))≠0 := by
    intro hz
    apply ha (E.symm i)
    funext k
    have hh := congrFun hz (F k)
    simpa only [A,Equiv.symm_apply_apply,Pi.zero_apply,Int.cast_eq_zero] using hh
  have hNP (i j) (hij : i≠j) (c : ℚ) :
      (fun k ↦ (A j k : ℚ))≠c • (fun k ↦ (A i k : ℚ)) := by
    intro he
    apply hnp (E.symm i) (E.symm j) (fun h ↦ hij (E.symm.injective h)) (c : ℝ)
    intro k
    have hh := congrFun he (F k)
    simp only [A,Equiv.symm_apply_apply,Pi.smul_apply,smul_eq_mul] at hh
    exact_mod_cast hh
  obtain ⟨H,hH,θ,hθ⟩ := signed_interval_packing hr A hA hNP (w ∘ E.symm)
    (fun i ↦ hw _) (by simpa only [Function.comp_apply,Equiv.sum_comp] using hs)
  refine ⟨H,hH,(fun h k ↦ θ h (F k)),?_⟩
  intro e f i j h v hne
  have hh := hθ e f (E i) (E j) h v (by
    intro he
    apply hne
    obtain ⟨hef,hij,hv⟩ := Prod.mk.inj he |>.imp id Prod.mk.inj
    exact Prod.ext hef (Prod.ext (E.injective hij) hv))
  simpa only [A,Function.comp_apply,Equiv.symm_apply_apply,← Equiv.sum_comp F] using hh

/-- The minor degenerate-cardinality case is absorbed by a zero-coefficient
fresh frequency. Only geometry is padded; the auxiliary polynomial is unchanged. -/
theorem signed_interval_packing_general {I J : Type} [Fintype I] [Fintype J]
    [Nonempty I] (a : I → J → ℤ) (ha : ∀ i, a i≠0)
    (hnp : ∀ i j, i≠j → ∀ c : ℝ, ¬∀ k, (a j k : ℝ)=c*(a i k : ℝ))
    (w : I → ℝ) (hw : ∀ i, 0<w i) (hs : 2*∑ i, w i<1) :
    ∃ H : ℕ, 1≤H ∧ ∃ θ : Fin H → J → UnitAddCircle,
      ∀ e f : Bool, ∀ i j : I, ∀ h v : Fin H, (e,i,h)≠(f,j,v) →
        Disjoint (circleInterval (signedCircle e (∑ k, a i k • θ h k)) (w i/H))
          (circleInterval (signedCircle f (∑ k, a j k • θ v k)) (w j/H)) := by
  classical
  let A : Option I → Option J → ℤ := fun i k ↦ match i,k with
    | none,none => 1 | some i,some k => a i k | _,_ => 0
  let W : Option I → ℝ := fun i ↦ match i with
    | none => (1-2*∑ i, w i)/4 | some i => w i
  have hcard : 2≤Fintype.card (Option I) := by
    rw [Fintype.card_option]
    have := Fintype.card_pos_iff.mpr (inferInstance : Nonempty I)
    omega
  have hA (i : Option I) : A i≠0 := by
    cases i with
    | none => intro h; have := congrFun h none; simp [A] at this
    | some i =>
      intro h
      apply ha i
      funext k
      have := congrFun h (some k)
      simpa [A] using this
  have hNP (i j : Option I) (hij : i≠j) (c : ℝ) :
      ¬∀ k, (A j k : ℝ)=c*(A i k : ℝ) := by
    intro he
    cases i with
    | none =>
      cases j with
      | none => exact hij rfl
      | some j =>
        apply ha j
        funext k
        have hh := he (some k)
        simpa [A] using hh
    | some i =>
      cases j with
      | none => have hh := he none; norm_num [A] at hh
      | some j =>
        exact hnp i j (fun h ↦ hij (congrArg some h)) c (fun k ↦ by simpa [A] using he (some k))
  have hW (i : Option I) : 0<W i := by
    cases i with
    | none => dsimp [W]; linarith
    | some i => exact hw i
  have hsum : 2*∑ i, W i<1 := by
    rw [Fintype.sum_option]
    change 2*((1-2*∑ i, w i)/4+∑ i, w i)<1
    linarith
  obtain ⟨H,hH,θ,hθ⟩ := signed_interval_packing_fintype hcard A hA hNP W hW hsum
  refine ⟨H,hH,(fun h k ↦ θ h (some k)),?_⟩
  intro e f i j h v hne
  have hh := hθ e f (some i) (some j) h v (by
    intro he
    apply hne
    obtain ⟨hef,hij,hv⟩ := Prod.mk.inj he |>.imp id Prod.mk.inj
    exact Prod.ext hef (Prod.ext (Option.some.inj hij) hv))
  simpa only [Fintype.sum_option,A,zero_smul,zero_add,W] using hh

end
end AsymptoticallyMinimalLittlewood.Packing

end OAI

theorem lift_separation {a b u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (q : ℤ) (h : ∀ x : ℝ, |x-a| ≤ u/2 → ¬ |x-(b+q)| ≤ v/2) :
    (u+v)/2 < |a-b-q| := by
  by_contra! hab
  obtain ⟨hl,hr⟩ := abs_le.mp hab
  let x := max (a-u/2) (b+q-v/2)
  have hlo : a-u/2 ≤ x := le_max_left _ _
  have hlo' : b+q-v/2 ≤ x := le_max_right _ _
  have hhi : x ≤ a+u/2 := max_le (by linarith) (by linarith)
  have hhi' : x ≤ b+q+v/2 := max_le (by linarith) (by linarith)
  exact h x (abs_le.mpr ⟨by linarith, by linarith⟩) (abs_le.mpr ⟨by linarith, by linarith⟩)

theorem circle_disjoint_separation {a b u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hd : Disjoint (OAI.AsymptoticallyMinimalLittlewood.Packing.circleInterval (a : UnitAddCircle) u) (OAI.AsymptoticallyMinimalLittlewood.Packing.circleInterval (b : UnitAddCircle) v))
    (q : ℤ) : (u+v)/2 < |a-b-q| := by
  apply lift_separation hu hv q
  intro x hx hy
  have hq : ((q : ℝ) : UnitAddCircle) = 0 := by
    simpa only [zsmul_eq_mul, mul_one, AddCircle.coe_period, smul_zero] using
      (AddCircle.coe_zsmul (p := (1 : ℝ)) (n := q) (x := (1 : ℝ)))
  have hmem : (x : UnitAddCircle) ∈ OAI.AsymptoticallyMinimalLittlewood.Packing.circleInterval (a : UnitAddCircle) u := by
    exact ⟨x-a, hx, by rw [← AddCircle.coe_add]; congr 1; ring⟩
  apply Set.disjoint_left.mp hd hmem
  refine ⟨x-(b+q), hy, ?_⟩
  rw [← AddCircle.coe_add, show b+(x-(b+q))=x-q by ring, AddCircle.coe_sub, hq, sub_zero]

open scoped BigOperators
noncomputable def phaseLift (z : UnitAddCircle) : ℝ := Classical.choose (QuotientAddGroup.mk_surjective z)
lemma coe_phaseLift (z : UnitAddCircle) : ((phaseLift z : ℝ) : UnitAddCircle) = z := Classical.choose_spec (QuotientAddGroup.mk_surjective z)

lemma signed_phaseLift {m : ℕ} (e : Bool) (a : Fin m → ℤ) (z : Fin m → UnitAddCircle) :
    (((if e then (1 : ℝ) else -1) * (∑ k, (a k : ℝ) * phaseLift (z k)) : ℝ) : UnitAddCircle) =
    (if e then ∑ k, a k • z k else -(∑ k, a k • z k)) := by
  let π : ℝ →+ UnitAddCircle := QuotientAddGroup.mk' _
  have hx : π (∑ k, (a k : ℝ) * phaseLift (z k)) = ∑ k, a k • z k := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [← zsmul_eq_mul, map_zsmul]
    exact congrArg (fun t : UnitAddCircle ↦ a k • t) (coe_phaseLift _)
  cases e <;> simp only [Bool.false_eq_true, ↓reduceIte, one_mul, neg_one_mul, AddCircle.coe_neg] <;> rw [← hx] <;> rfl


theorem OMA.solution : OMA.R_Green84_green_84_variants_littlewood_R1.H2 := by
  classical
  intro r m hr a ha hn w hw hs
  obtain ⟨H,hH,z,hz⟩ := OAI.AsymptoticallyMinimalLittlewood.Packing.signed_interval_packing_fintype (I := Fin r) (J := Fin m) (by simpa using hr) a (fun i he ↦ by
    obtain ⟨k,hk⟩ := ha i
    exact hk (by simpa using congrFun he k)) hn w hw hs
  refine ⟨H,hH,fun h k ↦ phaseLift (z h k),?_⟩
  intro e f i j h s hne q
  have hd := hz e f i j h s hne
  unfold OAI.AsymptoticallyMinimalLittlewood.Packing.signedCircle at hd
  rw [← signed_phaseLift e (a i) (z h), ← signed_phaseLift f (a j) (z s)] at hd
  have hsep := circle_disjoint_separation (div_nonneg (hw i).le (Nat.cast_nonneg H))
    (div_nonneg (hw j).le (Nat.cast_nonneg H)) hd q
  convert hsep using 1 <;> ring
