import OMAReductions.R_wp_regularity_of_solutions_of_vlasov_maxwell_equations_R1
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
namespace OMA.R_wp_regularity_of_solutions_of_vlasov_maxwell_equations_R1_H1_R1
open OMA.S_wp_regularity_of_solutions_of_vlasov_maxwell_equations MeasureTheory Set
open scoped ContDiff
noncomputable section
theorem smooth_field {F : Field} {S U : Set ℝ} {n : WithTop ℕ∞} (a b : ℝ) (hmap : MapsTo (fun t => a*t) S U) (h : ContDiffOn ℝ n F {z | z.1 ∈ U}) : ContDiffOn ℝ n (fun z : ℝ × Vec => b • F (a*z.1,z.2)) {z | z.1 ∈ S} := by
  apply ContDiffOn.const_smul; apply h.comp (f := fun z : ℝ × Vec => (a*z.1,z.2)) _ (fun _ hz => hmap (show _ ∈ S from hz)); exact ((contDiff_const.mul contDiff_fst).prodMk contDiff_snd).contDiffOn
theorem smooth_f {f : Density} {S U : Set ℝ} {n : WithTop ℕ∞} (a b r : ℝ) (hmap : MapsTo (fun t => a*t) S U) (h : ContDiffOn ℝ n f {z | z.1 ∈ U}) : ContDiffOn ℝ n (fun z : ℝ × Phase => b * f (a*z.1,z.2.1,r • z.2.2)) {z | z.1 ∈ S} := by
  apply contDiffOn_const.mul; apply h.comp (f := fun z : ℝ × Phase => (a*z.1,z.2.1,r • z.2.2)) _ (fun _ hz => hmap (show _ ∈ S from hz)); apply ContDiff.contDiffOn; fun_prop
theorem pullL {F : Field} {S U : Set ℝ} (a b : ℝ) (hm : MapsTo (fun t => a*t) S U)
    (h : ∃ G : ℝ → Lp Vec 2 (volume : Measure Vec), ContinuousOn G U ∧ ∀ t ∈ U, (G t : Vec → Vec) =ᵐ[volume] fun x => F (t,x)) :
    ∃ G : ℝ → Lp Vec 2 (volume : Measure Vec), ContinuousOn G S ∧ ∀ t ∈ S, (G t : Vec → Vec) =ᵐ[volume] fun x => b • F (a*t,x) := by
  obtain ⟨G,hG,he⟩ := h
  refine ⟨fun t => b • G (a*t),(hG.comp (continuous_const.mul continuous_id).continuousOn hm).const_smul b,?_⟩
  intro t ht; filter_upwards [Lp.coeFn_smul b (G (a*t)),he _ (hm ht)] with x hx hx'; rw [hx]; simp [hx']

def H1 : Prop := ∀ (ι : Type) [Fintype ι] (P : Plasma ι) (d : Datum ι), Admissible P d →
  let v := fun p : Vec => (Real.sqrt (1+‖p‖^2))⁻¹ • p
  let m := fun i => P.mass i * P.c
  ∀ H : ℝ, 0 ≤ H → ∃ U : ℝ, H < U ∧ ∃ n : Solution ι,
  (∀ i, ContDiffOn ℝ ∞ (n.f i) (densitySlab U)) ∧ ContDiffOn ℝ ∞ n.E (fieldSlab U) ∧ ContDiffOn ℝ ∞ n.B (fieldSlab U) ∧
  (∀ i, ∀ t ∈ Icc 0 U, ∀ z, 0 ≤ n.f i (t,z)) ∧
  (∀ F ∈ ({n.E,n.B} : Set Field), ∃ G : ℝ → Lp Vec 2 (volume : Measure Vec), ContinuousOn G (Icc 0 U) ∧ ∀ t∈Icc 0 U, (G t : Vec → Vec) =ᵐ[volume] fun x => F (t,x)) ∧
  (∃ K : Set Phase, IsCompact K ∧ ∀ i, ∀ t ∈ Icc 0 U, tsupport (fun z => n.f i (t,z)) ⊆ K) ∧
  (∀ t, 0 ≤ t → t < U → (∀ i x p, derivWithin (fun r => n.f i (r,x,p)) (Ici 0) t + (∑ j, v p j * partialDeriv (fun y => n.f i (t,y,p)) x j) + (∑ j, ((P.charge i / (P.mass i * P.c^2)) • (n.E (t,x)+cross (v p) (n.B (t,x)))) j * partialDeriv (fun w => n.f i (t,x,w)) p j) = 0) ∧ (∀ x, derivWithin (fun r => n.E (r,x)) (Ici 0) t - curl (fun y => n.B (t,y)) x = -(∑ i, (P.charge i / P.ε₀) • ∫ p : Vec, n.f i (t,x,p) • v p)) ∧ (∀ x, derivWithin (fun r => n.B (r,x)) (Ici 0) t + curl (fun y => n.E (t,y)) x = 0) ∧ (∀ x, divergence (fun y => n.E (t,y)) x = ∑ i, (P.charge i / P.ε₀) * ∫ p : Vec, n.f i (t,x,p)) ∧ ∀ x, divergence (fun y => n.B (t,y)) x = 0) ∧
  (∀ i z, n.f i (0,z) = (m i)^3 * d.f₀ i (z.1,m i • z.2)) ∧ (∀ x, n.E (0,x)=d.E₀ x) ∧ ∀ x, n.B (0,x)=P.c • d.B₀ x

def H2 : Prop := ∀ (ι : Type) [Fintype ι] (P : Plasma ι) (s : Solution ι) (t : ℝ), 0 ≤ t →
  let v := fun p : Vec => (Real.sqrt (1+‖p‖^2))⁻¹ • p
  let m := fun i => P.mass i * P.c
  let n : Solution ι := ⟨fun i z => (m i)^3 * s.f i (P.c⁻¹*z.1,z.2.1,m i • z.2.2),fun z => s.E (P.c⁻¹*z.1,z.2),fun z => P.c • s.B (P.c⁻¹*z.1,z.2)⟩
  let u := P.c⁻¹*t
  (∀ i x p, derivWithin (fun r => n.f i (r,x,p)) (Ici 0) t + (∑ j, v p j * partialDeriv (fun y => n.f i (t,y,p)) x j) + (∑ j, ((P.charge i / (P.mass i * P.c^2)) • (n.E (t,x)+cross (v p) (n.B (t,x)))) j * partialDeriv (fun w => n.f i (t,x,w)) p j) = 0) → (∀ α x p,
    derivWithin (fun u' => s.f α (u', x, p)) (Ici 0) u +
    (∑ i : Fin 3, velocity P α p i * partialDeriv (fun y => s.f α (u, y, p)) x i) +
    P.charge α * (∑ i : Fin 3, (s.E (u, x) + cross (velocity P α p) (s.B (u, x))) i *
      partialDeriv (fun p' => s.f α (u, x, p')) p i) = 0)

def H3 : Prop := ∀ (ι : Type) [Fintype ι] (P : Plasma ι) (s : Solution ι) (t : ℝ), 0 ≤ t →
  let v := fun p : Vec => (Real.sqrt (1+‖p‖^2))⁻¹ • p
  let m := fun i => P.mass i * P.c
  let n : Solution ι := ⟨fun i z => (m i)^3 * s.f i (P.c⁻¹*z.1,z.2.1,m i • z.2.2),fun z => s.E (P.c⁻¹*z.1,z.2),fun z => P.c • s.B (P.c⁻¹*z.1,z.2)⟩
  let u := P.c⁻¹*t
  ((∀ x, derivWithin (fun r => n.E (r,x)) (Ici 0) t - curl (fun y => n.B (t,y)) x = -(∑ i, (P.charge i / P.ε₀) • ∫ p : Vec, n.f i (t,x,p) • v p)) ∧ (∀ x, derivWithin (fun r => n.B (r,x)) (Ici 0) t + curl (fun y => n.E (t,y)) x = 0) ∧ (∀ x, divergence (fun y => n.E (t,y)) x = ∑ i, (P.charge i / P.ε₀) * ∫ p : Vec, n.f i (t,x,p)) ∧ ∀ x, divergence (fun y => n.B (t,y)) x = 0) → (∀ x, curl (fun y => s.B (u, y)) x =
    P.μ₀ • currentDensity P (fun α z => s.f α (u, z)) x +
      (P.μ₀ * P.ε₀) • derivWithin (fun u' => s.E (u', x)) (Ici 0) u) ∧
  (∀ x, curl (fun y => s.E (u, y)) x = -derivWithin (fun u' => s.B (u', x)) (Ici 0) u) ∧
  (∀ x, divergence (fun y => s.E (u, y)) x =
    chargeDensity P (fun α z => s.f α (u, z)) x / P.ε₀) ∧
  (∀ x, divergence (fun y => s.B (u, y)) x = 0)

theorem main : H1 → H2 → H3 → OMA.R_wp_regularity_of_solutions_of_vlasov_maxwell_equations_R1.H1 := by
  intro solv hv he ι _ P d hd L A H hH
  obtain ⟨U,hU,n,f,E,B,hpos,hL,⟨K,hK,hk⟩,eqn,f0,e0,b0⟩ := solv ι P d hd (P.c*H) (mul_nonneg P.c_pos.le hH)
  let m := fun i => P.mass i * P.c
  have hm (i) : 0 < m i := mul_pos (P.mass_pos i) P.c_pos
  let s : Solution ι := ⟨fun i z => ((m i)^3)⁻¹ * n.f i (P.c*z.1,z.2.1,(m i)⁻¹ • z.2.2),fun z => n.E (P.c*z.1,z.2),fun z => P.c⁻¹ • n.B (P.c*z.1,z.2)⟩
  have invn : (⟨fun i z => (m i)^3 * s.f i (P.c⁻¹*z.1,z.2.1,m i • z.2.2),fun z => s.E (P.c⁻¹*z.1,z.2),fun z => P.c • s.B (P.c⁻¹*z.1,z.2)⟩ : Solution ι) = n := by
    cases n; congr <;> funext <;> simp [s,← mul_assoc,smul_smul,P.c_pos.ne',(hm _).ne']
  have hmap : MapsTo (fun t => P.c*t) (Icc 0 (U/P.c)) (Icc 0 U) := fun t ht => ⟨mul_nonneg P.c_pos.le ht.1,by change P.c*t ≤ U; rw [mul_comm]; exact (le_div_iff₀ P.c_pos).mp ht.2⟩
  refine ⟨U/P.c,(lt_div_iff₀ P.c_pos).mpr (by simpa [mul_comm] using hU),s,?_⟩
  refine ⟨fun i => smooth_f _ _ _ hmap (f i),?_,smooth_field _ _ hmap B,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · have hh := smooth_field _ 1 hmap E; simp only [one_smul] at hh; exact hh
  · intro i t ht z; exact mul_nonneg (by have := hm i; positivity) (hpos i _ (hmap ht) _)
  · simpa only [one_smul] using pullL _ 1 hmap (hL n.E (by simp))
  · exact pullL _ _ hmap (hL n.B (by simp))
  · let e (i : ι) : Phase ≃ₜ Phase := (Homeomorph.refl Vec).prodCongr (Homeomorph.smul (Units.mk0 (m i)⁻¹ (inv_ne_zero (hm i).ne')))
    refine ⟨⋃ i, (e i) ⁻¹' K,isCompact_iUnion (fun i => (e i).isCompact_preimage.mpr hK),?_⟩
    intro i t ht; apply Subset.trans _ (subset_iUnion (fun j => (e j) ⁻¹' K) i)
    apply closure_minimal _ (hK.isClosed.preimage (e i).continuous)
    intro z hz; apply hk i _ (hmap ht); apply subset_closure
    intro hh; apply hz; change ((m i)^3)⁻¹ * n.f i (P.c*t,(e i) z) = 0; change n.f i (P.c*t,(e i) z) = 0 at hh; rw [hh,mul_zero]
  · intro t ht htU
    have hn := eqn (P.c*t) (mul_nonneg P.c_pos.le ht) (by rw [mul_comm]; exact (lt_div_iff₀ P.c_pos).mp htU)
    rw [← invn] at hn
    have h₁ := hv ι P s _ (mul_nonneg P.c_pos.le ht) hn.1
    have h₂ := he ι P s _ (mul_nonneg P.c_pos.le ht) hn.2
    simpa only [← mul_assoc, inv_mul_cancel₀ P.c_pos.ne',one_mul] using And.intro h₁ h₂
  · intro i z; change ((m i)^3)⁻¹ * n.f i (P.c*0,z.1,(m i)⁻¹ • z.2) = _; rw [mul_zero,f0]; change ((m i)^3)⁻¹ * ((m i)^3 * d.f₀ i (z.1,m i • ((m i)⁻¹ • z.2))) = _; simp [smul_smul,(hm i).ne']
  · intro x; simp [s,e0]
  · intro x; simp [s,b0,smul_smul,P.c_pos.ne']
end
end OMA.R_wp_regularity_of_solutions_of_vlasov_maxwell_equations_R1_H1_R1
