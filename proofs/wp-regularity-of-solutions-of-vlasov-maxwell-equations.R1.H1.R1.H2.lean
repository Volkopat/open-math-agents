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
def kappa (a : ι) := P.charge a / (P.mass a * P.c^2)
theorem velocity_scale (a : ι) (v : Vec) : velocity P a (moment P a • v) = P.c • vel v := by
  have hm := P.mass_pos a
  have hc := P.c_pos
  have h : 0 < P.mass a * P.c := mul_pos hm hc
  simp only [moment,velocity,vel,gammaN,norm_smul, Real.norm_eq_abs,abs_of_pos h,mul_pow,mul_div_cancel_left₀ _ (pow_ne_zero 2 h.ne'),smul_smul]
  congr 1
  field_simp
  <;> ring
def normSol (s : Solution ι) : Solution ι where
  f a z := (moment P a)^3 * s.f a (P.c⁻¹ * z.1,z.2.1,moment P a • z.2.2)
  E z := s.E (P.c⁻¹ * z.1,z.2)
  B z := P.c • s.B (P.c⁻¹ * z.1,z.2)
theorem hm (a : ι) : 0 < moment P a := mul_pos (P.mass_pos a) P.c_pos
theorem partial_mul (g : Vec → ℝ) (a : ℝ) (x : Vec) (i) : partialDeriv (fun y => a * g y) x i = a * partialDeriv g x i := by
  unfold partialDeriv; change fderiv ℝ (a • g) x _ = _; rw [fderiv_const_smul_field]; rfl
theorem DT {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : ℝ → F) (a b t : ℝ) (ha : 0 < a) (ht : 0 ≤ t) : derivWithin (fun u => b • f (a*u)) (Ici 0) t = (b*a) • derivWithin f (Ici 0) (a*t) := by
  have hs : a • (Ici (0:ℝ)) = Ici 0 := by
    ext x; constructor
    · rintro ⟨y,hy,rfl⟩; exact mul_nonneg ha.le hy
    · intro hx; exact ⟨x/a,div_nonneg hx ha.le, by change a*(x/a)=x; field_simp⟩
  change derivWithin (b • (fun u => f (a • u))) _ _ = _
  rw [derivWithin_const_smul_field]; unfold derivWithin; rw [fderivWithin_comp_smul a (uniqueDiffOn_Ici _ t ht),hs]; simp [smul_smul]
theorem DP (g : Vec → ℝ) (a b : ℝ) (x : Vec) (i) : partialDeriv (fun y => b * g (a • y)) x i = (b*a) * partialDeriv g (a • x) i := by
  rw [partial_mul]; unfold partialDeriv; rw [fderiv_comp_smul]; simp [mul_assoc]
def vr (s : Solution ι) (a : ι) (t : ℝ) (x p : Vec) := derivWithin (fun u => s.f a (u,x,p)) (Ici 0) t + (∑ i, velocity P a p i * partialDeriv (fun y => s.f a (t,y,p)) x i) + P.charge a * (∑ i, (s.E (t,x) + cross (velocity P a p) (s.B (t,x))) i * partialDeriv (fun w => s.f a (t,x,w)) p i)
def vn (s : Solution ι) (a : ι) (t : ℝ) (x p : Vec) := derivWithin (fun u => s.f a (u,x,p)) (Ici 0) t + (∑ i, vel p i * partialDeriv (fun y => s.f a (t,y,p)) x i) + (∑ i, (kappa P a • (s.E (t,x) + cross (vel p) (s.B (t,x)))) i * partialDeriv (fun w => s.f a (t,x,w)) p i)
theorem cross_shift (a : ℝ) (u b : Vec) : cross (a • u) b = cross u (a • b) := by ext i; fin_cases i <;> simp [cross,PiLp.smul_apply] <;> ring
theorem vr_scale (s : Solution ι) (a : ι) (t : ℝ) (ht : 0 ≤ t) (x p : Vec) : vn P (normSol P s) a t x p = ((moment P a)^3 * P.c⁻¹) * vr P s a (P.c⁻¹*t) x (moment P a • p) := by
  unfold vn vr normSol; dsimp only
  rw [show derivWithin (fun u => moment P a ^ 3 * s.f a (P.c⁻¹*u,x,moment P a • p)) (Ici 0) t = _ from DT (fun u => s.f a (u,x,moment P a • p)) _ _ t (inv_pos.mpr P.c_pos) ht,velocity_scale,cross_shift]
  have hp (i : Fin 3) := DP (fun w => s.f a (P.c⁻¹*t,x,w)) (moment P a) ((moment P a)^3) p i
  simp only [hp,partial_mul,PiLp.smul_apply,smul_eq_mul,mul_add,Finset.mul_sum]
  congr 1
  · congr 1; apply Finset.sum_congr rfl; intro i _; field_simp [P.c_pos.ne']
  · apply Finset.sum_congr rfl; intro i _; unfold kappa moment; field_simp [P.c_pos.ne',(P.mass_pos a).ne']
end
end SITransport
open OMA.S_wp_regularity_of_solutions_of_vlasov_maxwell_equations SITransport MeasureTheory Set
theorem OMA.solution : OMA.R_wp_regularity_of_solutions_of_vlasov_maxwell_equations_R1_H1_R1.H2 := by
  intro ι _ P s t ht v m n u h i x p
  have hh := h i x ((moment P i)⁻¹ • p)
  change vn P (normSol P s) i t x ((moment P i)⁻¹ • p) = 0 at hh
  rw [vr_scale P s i t ht, mul_eq_zero] at hh
  have hz : (moment P i)^3 * P.c⁻¹ ≠ 0 := mul_ne_zero (pow_ne_zero _ (hm P i).ne') (inv_ne_zero P.c_pos.ne')
  change vr P s i (P.c⁻¹*t) x p = 0
  simpa only [smul_smul,mul_inv_cancel₀ (hm P i).ne',one_smul] using hh.resolve_left hz
