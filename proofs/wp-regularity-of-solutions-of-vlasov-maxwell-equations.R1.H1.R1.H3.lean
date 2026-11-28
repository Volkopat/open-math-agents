import OMAReductions.R_wp_regularity_of_solutions_of_vlasov_maxwell_equations_R1_H1_R1
/- Physical finite-prefix adaptation of OpenAI, openai/math@3344da59991ed94f9ba711217b29c1d760badfa6. Modified for SI units and finitely many species.
Credit: @my-other-github-account
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
namespace SITransport
open OMA.S_wp_regularity_of_solutions_of_vlasov_maxwell_equations MeasureTheory Set
open scoped Pointwise
noncomputable section
variable {ι : Type} [Fintype ι] (P : Plasma ι)
def gammaN (v : Vec) := Real.sqrt (1 + ‖v‖^2)
def vel (v : Vec) := (gammaN v)⁻¹ • v
def moment (a : ι) := P.mass a * P.c
def weight (a : ι) := P.charge a / P.ε₀
theorem velocity_scale (a : ι) (v : Vec) : velocity P a (moment P a • v) = P.c • vel v := by
  have hm := P.mass_pos a
  have hc := P.c_pos
  have h : 0 < P.mass a * P.c := mul_pos hm hc
  simp only [moment,velocity,vel,gammaN,norm_smul, Real.norm_eq_abs,abs_of_pos h,mul_pow,mul_div_cancel_left₀ _ (pow_ne_zero 2 h.ne'),smul_smul]
  congr 1
  field_simp
  <;> ring
def fNorm (g : ι → Phase → ℝ) (a : ι) (z : Phase) := (moment P a)^3 * g a (z.1,moment P a • z.2)
theorem jac {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (r : ℝ) (h : 0 < r) (g : Vec → F) : (r^3) • (∫ p : Vec, g (r • p)) = ∫ p, g p := by
  rw [Measure.integral_comp_smul_of_nonneg volume g r (hR := h.le)]
  simp [Vec, smul_smul, h.ne']
theorem rho (g : ι → Phase → ℝ) (x : Vec) : (∑ a, weight P a * ∫ v : Vec, fNorm P g a (x,v)) = chargeDensity P g x / P.ε₀ := by
  rw [chargeDensity, Finset.sum_div]; apply Finset.sum_congr rfl; intro a _
  unfold fNorm; rw [integral_const_mul]
  rw [show (moment P a)^3 * (∫ v : Vec, g a (x,moment P a • v)) = _ from jac _ (mul_pos (P.mass_pos a) P.c_pos) (fun v => g a (x,v))]; unfold weight; ring
theorem current (g : ι → Phase → ℝ) (x : Vec) : (P.c * P.ε₀) • (∑ a, weight P a • ∫ v : Vec, fNorm P g a (x,v) • vel v) = currentDensity P g x := by
  rw [currentDensity,Finset.smul_sum]; apply Finset.sum_congr rfl; intro a _
  rw [← jac (moment P a) (mul_pos (P.mass_pos a) P.c_pos) (fun p => g a (x,p) • velocity P a p)]
  simp only [fNorm,velocity_scale, mul_smul, integral_smul,smul_comm (g a _) P.c]
  simp only [smul_smul]
  congr 1; unfold weight; field_simp [P.ε₀_pos.ne']
theorem partial_mul (g : Vec → ℝ) (a : ℝ) (x : Vec) (i) : partialDeriv (fun y => a * g y) x i = a * partialDeriv g x i := by
  unfold partialDeriv; change fderiv ℝ (a • g) x _ = _; rw [fderiv_const_smul_field]; rfl
theorem div_scale (F : Vec → Vec) (b : ℝ) (x : Vec) : divergence (fun y => b • F y) x = b * divergence F x := by
  unfold divergence; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; apply partial_mul
theorem DT {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : ℝ → F) (a b t : ℝ) (ha : 0 < a) (ht : 0 ≤ t) : derivWithin (fun u => b • f (a*u)) (Ici 0) t = (b*a) • derivWithin f (Ici 0) (a*t) := by
  have hs : a • (Ici (0:ℝ)) = Ici 0 := by
    ext x; constructor
    · rintro ⟨y,hy,rfl⟩; exact mul_nonneg ha.le hy
    · intro hx; exact ⟨x/a,div_nonneg hx ha.le, by change a*(x/a)=x; field_simp⟩
  change derivWithin (b • (fun u => f (a • u))) _ _ = _
  rw [derivWithin_const_smul_field]; unfold derivWithin; rw [fderivWithin_comp_smul a (uniqueDiffOn_Ici _ t ht),hs]; simp [smul_smul]
theorem curl_scale (F : Vec → Vec) (b : ℝ) (x : Vec) : curl (fun y => b • F y) x = b • curl F x := by
  ext i; fin_cases i <;> simp [curl,PiLp.smul_apply,partial_mul,mul_sub]
theorem amp (e b j : Vec) : (P.c⁻¹ • e - P.c • b = -j) ↔ (b = P.μ₀ • ((P.c*P.ε₀) • j) + (P.μ₀ * P.ε₀) • e) := by
  have hm : P.μ₀ * P.ε₀ = P.c⁻¹ * P.c⁻¹ := by field_simp [P.c_pos.ne']; nlinarith [P.maxwell_const]
  have hj : P.μ₀ * (P.c * P.ε₀) = P.c⁻¹ := by rw [mul_left_comm,hm]; field_simp
  rw [smul_smul,hj,hm]; constructor
  · intro h; have hh := congrArg (P.c⁻¹ • ·) h
    simp only [smul_sub,smul_neg,smul_smul,inv_mul_cancel₀ P.c_pos.ne',one_smul] at hh; abel_nf at *; linear_combination (norm := abel) -hh
  · rintro rfl; simp [smul_add,smul_smul,P.c_pos.ne']
theorem far (b e : Vec) : (b + e = 0) ↔ (e = -b) := by rw [eq_neg_iff_add_eq_zero,add_comm]
end
end SITransport
open OMA.S_wp_regularity_of_solutions_of_vlasov_maxwell_equations SITransport MeasureTheory Set
theorem OMA.solution : OMA.R_wp_regularity_of_solutions_of_vlasov_maxwell_equations_R1_H1_R1.H3 := by
  intro ι _ P s t ht v m n u h
  obtain ⟨ha,hf,hd,hdB⟩ := h
  refine ⟨?_,?_,?_,?_⟩
  · intro x
    have hh := ha x
    have dt := DT (fun u => s.E (u,x)) P.c⁻¹ 1 t (inv_pos.mpr P.c_pos) ht
    simp only [one_smul,one_mul] at dt
    rw [← current P]
    apply (amp P _ _ _).mp
    simpa only [n,dt,curl_scale,weight,fNorm,vel,gammaN,v,m,moment,u] using hh
  · intro x
    apply (far _ _).mp
    have hh := hf x
    simpa only [n,DT (fun u => s.B (u,x)) _ _ t (inv_pos.mpr P.c_pos) ht,mul_inv_cancel₀ P.c_pos.ne',one_smul] using hh
  · intro x; rw [← rho P]; exact hd x
  · intro x; have hh := hdB x; change divergence (fun y => P.c • s.B (u,y)) x = 0 at hh
    rw [div_scale,mul_eq_zero] at hh; exact hh.resolve_left P.c_pos.ne'
