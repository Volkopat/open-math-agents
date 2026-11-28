import OMAReductions.R_ERH_extended_riemann_hypothesis_R3

-- Credit: @deepqntm

/-!
# From two zero-free strips to the sampled Jensen bound

An entire continuation of the normalized ideal series determines the Taylor sum at two.
Removing the archimedean factors identifies its zeros off the pole by analytic continuation.
The class-number residue deals with the pole itself. Jensen's formula then gives equality
at every real height, including heights where the circle passes through a critical-line zero.

The Taylor comparison, pole calculation and open-disk Jensen argument adapt @deepqntm's
local R3 development in Converse.lean, CompletedBoundary.lean and SmallCircles.lean.
The reciprocal archimedean factor argument adapts the local DedekindReflection development.
The Jensen theorem used here is from Mathlib.Analysis.Complex.JensenFormula,
copyright (c) 2025 Stefan Kebekus. All rights reserved.
The outer half-plane is the conclusion of Dean Cureton and Jesse Thorner's Theorem 1.1,
formalized in AxiomMath/DedekindZetaZeroFree, Solution/DedekindZetaSolution.lean,
revision 15f9d0d31f2336fbc38f8c111e8d3b46e337bfe4.
Released under the Apache License, Version 2.0, reproduced at the end of this file.
-/

namespace OMA.R_ERH_extended_riemann_hypothesis_R3_H2_R1

open Complex Filter MeromorphicOn Metric NumberField NumberField.InfinitePlace Set
open scoped Topology NumberField

/-- The pole-cleared, completed Dirichlet series on its half-plane of absolute convergence
extends to an entire function. -/
def H1 : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], ∃ X : ℂ → ℂ, Differentiable ℂ X ∧
    ∀ s : ℂ, 1 < s.re →
      X s = s * (s - 1) * (Complex.exp (s * (Real.log (discr K).natAbs / 2 : ℝ)) *
        Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K) * dedekindZeta K s

/-- A Dedekind continuation exists that is zero-free above 31/32, off its pole. -/
def H2 : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], ∃ Z : ℂ → ℂ, ERH.IsDedekindZeta K Z ∧
    ∀ s : ℂ, 31 / 32 < s.re → s ≠ 1 → Z s ≠ 0

/-- The remaining strip includes its right edge and excludes the critical line. -/
def H3 : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (Z : ℂ → ℂ), ERH.IsDedekindZeta K Z →
    ∀ s : ℂ, 1 / 2 < s.re → s.re ≤ 31 / 32 → Z s ≠ 0

/-- Boundary zeros have zero Jensen weight, so nonvanishing in the open ball suffices. -/
theorem circleAverage_eq_of_nonzero_ball {X : ℂ → ℂ} (hX : Differentiable ℂ X)
    {c : ℂ} {r : ℝ} (hr : 0 < r) (hn : ∀ z ∈ ball c r, X z ≠ 0) :
    Real.circleAverage (fun z => Real.log ‖X z‖) c r = Real.log ‖X c‖ := by
  have hB : AnalyticOnNhd ℂ X (closedBall c |r|) :=
    (hX.differentiableOn.analyticOnNhd isOpen_univ).mono (subset_univ _)
  rw [hB.circleAverage_log_norm hr.ne' (hn c (mem_ball_self hr))]
  suffices ∀ z, (divisor X (closedBall c |r|) z : ℝ) * Real.log (r * ‖c - z‖⁻¹) = 0 by
    simp [this]
  intro z
  by_cases hz : z ∈ closedBall c |r|
  · by_cases hin : z ∈ ball c r
    · rw [hB.divisor_apply hz, (hB z hz).analyticOrderAt_eq_zero.mpr (hn z hin)]
      simp
    · have hle : ‖c - z‖ ≤ r := by simpa [mem_closedBall, dist_eq_norm', abs_of_pos hr] using hz
      have hge : r ≤ ‖c - z‖ := by simpa [mem_ball, dist_eq_norm'] using hin
      rw [le_antisymm hle hge, mul_inv_cancel₀ hr.ne', Real.log_one, mul_zero]
  · simp [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hz]

/-- The residue on the real axis determines the value of the entire regularization at one. -/
private theorem regularized_value_one (K : Type) [Field K] [NumberField K]
    {W : ℂ → ℂ} (hW : Differentiable ℂ W)
    (hseries : ∀ s : ℂ, 1 < s.re → W s = s * (s - 1) * dedekindZeta K s) :
    W 1 = (dedekindZeta_residue K : ℂ) := by
  have hcoe : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[>] 1) (𝓝 (1 : ℂ)) := by
    simpa using (continuous_ofReal.continuousAt (x := (1 : ℝ))).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Ioi 1))
  apply tendsto_nhds_unique ((hW.continuous.tendsto 1).comp hcoe)
  have hres : Tendsto (fun x : ℝ => (x : ℂ) * (↑(x - 1) * dedekindZeta K x))
      (𝓝[>] 1) (𝓝 (dedekindZeta_residue K : ℂ)) := by
    simpa using hcoe.mul (tendsto_sub_one_mul_dedekindZeta_nhdsGT K)
  apply hres.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  change _ = W (x : ℂ)
  rw [hseries x hx, ofReal_sub, ofReal_one, mul_assoc]

/-- On the punctured plane the regularization equals the polynomial times any continuation.
At the omitted point its residue is nonzero. -/
private theorem regularized_nonzero (K : Type) [Field K] [NumberField K] {W Z : ℂ → ℂ}
    (hW : Differentiable ℂ W)
    (hseries : ∀ s : ℂ, 1 < s.re → W s = s * (s - 1) * dedekindZeta K s)
    (hZ : ERH.IsDedekindZeta K Z) (hfree : ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 → Z s ≠ 0)
    {s : ℂ} (hs : 1 / 2 < s.re) : W s ≠ 0 := by
  rcases eq_or_ne s 1 with rfl | hs₁
  · rw [regularized_value_one K hW hseries]
    exact ofReal_ne_zero.mpr (dedekindZeta_residue_ne_zero K)
  have hagree : EqOn W (fun z => z * (z - 1) * Z z) ({1}ᶜ : Set ℂ) := by
    apply (hW.differentiableOn.analyticOnNhd isOpen_compl_singleton).eqOn_of_preconnected_of_eventuallyEq
      ((analyticOnNhd_id.mul (analyticOnNhd_id.sub analyticOnNhd_const)).mul
        (hZ.1.analyticOnNhd isOpen_compl_singleton))
      (isConnected_compl_singleton_of_one_lt_rank (Complex.rank_real_complex ▸ Nat.one_lt_ofNat) _).isPreconnected
      (show (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) by norm_num)
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
      (show 1 < (2 : ℂ).re by norm_num)] with z hz
    change W z = z * (z - 1) * Z z
    rw [hseries z hz, hZ.2 z hz]
  rw [hagree (show s ∈ ({1}ᶜ : Set ℂ) from hs₁)]
  exact mul_ne_zero (mul_ne_zero (ne_zero_of_re_pos (by linarith)) (sub_ne_zero.mpr hs₁))
    (hfree s hs hs₁)

theorem main : H1 → H2 → H3 → OMA.R_ERH_extended_riemann_hypothesis_R3.H2 := by
  intro hcompletion houter hinner K _ _
  obtain ⟨X, hX, hseries⟩ := hcompletion K
  obtain ⟨Z, hZ, hcollar⟩ := houter K
  let A (s : ℂ) := Complex.exp (s * (Real.log (discr K).natAbs / 2 : ℝ)) *
    Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K
  let G (s : ℂ) := s * (s - 1) * A s * dedekindZeta K s
  let F (z : ℂ) := ∑' n : ℕ, (n.factorial : ℂ)⁻¹ * iteratedDeriv n G 2 * (z - 2) ^ n
  change ∀ s : ℂ, 1 < s.re → X s = G s at hseries
  have hgerm : X =ᶠ[𝓝 (2 : ℂ)] G := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
      (show 1 < (2 : ℂ).re by norm_num)] with s hs using hseries s hs
  have hTaylor : F = X := by
    funext z
    simpa only [F, ← fun n => hgerm.iteratedDeriv_eq n] using
      Complex.taylorSeries_eq_of_entire' (c := 2) (z := z) hX

  let W (s : ℂ) := (A s)⁻¹ * X s
  have hInv : Differentiable ℂ (fun s => (A s)⁻¹) := by
    simp only [A, mul_inv, ← inv_pow, ← Complex.exp_neg]
    fun_prop
  have hW : Differentiable ℂ W := hInv.mul hX
  have hWseries (s : ℂ) (hs : 1 < s.re) : W s = s * (s - 1) * dedekindZeta K s := by
    have hR := Gammaℝ_ne_zero_of_re_pos (zero_lt_one.trans hs)
    have hC : Gammaℂ s ≠ 0 := by
      rw [← Gammaℝ_mul_Gammaℝ_add_one]
      exact mul_ne_zero hR (Gammaℝ_ne_zero_of_re_pos (by simp; linarith))
    have hA : A s ≠ 0 :=
      mul_ne_zero (mul_ne_zero (exp_ne_zero _) (pow_ne_zero _ hR)) (pow_ne_zero _ hC)
    dsimp only [W]
    rw [hseries s hs]
    dsimp only [G]
    field_simp [hA]
  have hfree (s : ℂ) (hs : 1 / 2 < s.re) (hp : s ≠ 1) : Z s ≠ 0 := by
    rcases lt_or_ge (31 / 32) s.re with ho | hi
    · exact hcollar s ho hp
    · exact hinner K Z hZ s hs hi
  have hright (s : ℂ) (hs : 1 / 2 < s.re) : X s ≠ 0 :=
    right_ne_zero_of_mul (regularized_nonzero K hW hWseries hZ hfree hs)

  have hmean (t : ℝ) : Real.circleAverage (fun z => Real.log ‖X z‖) (1 + I * t) (1 / 2) =
      Real.log ‖X (1 + I * t)‖ := by
    apply circleAverage_eq_of_nonzero_ball hX (by norm_num)
    intro s hs
    have hd : ‖(1 + I * t) - s‖ < 1 / 2 := by simpa [mem_ball, dist_eq_norm'] using hs
    have hre := (re_le_norm ((1 + I * t) - s)).trans_lt hd
    simp at hre
    exact hright s (by linarith)
  dsimp only
  intro a b hab ε hε
  obtain ⟨q, haq, hqb⟩ := exists_between hab
  refine ⟨q, haq, hqb, ?_⟩
  change Real.circleAverage (fun z => Real.log ‖F z‖) (1 + I * (q : ℝ)) (1 / 2) <
    Real.log ‖F (1 + I * (q : ℝ))‖ + ε
  rw [hTaylor, hmean]
  exact lt_add_of_pos_right _ hε

end OMA.R_ERH_extended_riemann_hypothesis_R3_H2_R1

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
      boilerplate notice, with the fields enclosed by brackets "{}"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright {yyyy} {name of copyright owner}

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
