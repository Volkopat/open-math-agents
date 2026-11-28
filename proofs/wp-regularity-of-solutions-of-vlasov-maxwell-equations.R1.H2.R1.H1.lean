import OMAReductions.R_wp_regularity_of_solutions_of_vlasov_maxwell_equations_R1_H2_R1
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
section

namespace OAI

/-! The one-species relativistic Vlasov–Maxwell system on three-dimensional Euclidean space. -/

noncomputable section
open MeasureTheory Set
open scoped ContDiff

namespace RVM

abbrev Vec := EuclideanSpace ℝ (Fin 3)
abbrev Phase := Vec × Vec
abbrev Particle := ℝ × Phase → ℝ
abbrev Field := ℝ × Vec → Vec

def q (v : Vec) : ℝ := Real.sqrt (1 + ‖v‖ ^ 2)
def velocity (v : Vec) : Vec := (q v)⁻¹ • v

def basis (i : Fin 3) : Vec := WithLp.toLp 2 (Pi.single i (1 : ℝ))
def dot (a b : Vec) : ℝ := ∑ i : Fin 3, a i * b i
def cross (a b : Vec) : Vec := WithLp.toLp 2
  ![a 1 * b 2 - a 2 * b 1, a 2 * b 0 - a 0 * b 2,
    a 0 * b 1 - a 1 * b 0]

def spatialPartial (g : Vec → ℝ) (x : Vec) (i : Fin 3) : ℝ :=
  fderiv ℝ g x (basis i)
def divergence (F : Vec → Vec) (x : Vec) : ℝ :=
  ∑ i : Fin 3, spatialPartial (fun y => F y i) x i

def curl (F : Vec → Vec) (x : Vec) : Vec := WithLp.toLp 2
  ![spatialPartial (fun y => F y 2) x 1 - spatialPartial (fun y => F y 1) x 2,
    spatialPartial (fun y => F y 0) x 2 - spatialPartial (fun y => F y 2) x 0,
    spatialPartial (fun y => F y 1) x 0 - spatialPartial (fun y => F y 0) x 1]

def rho (g : Phase → ℝ) (x : Vec) : ℝ := ∫ v : Vec, g (x, v)
def current (g : Phase → ℝ) (x : Vec) : Vec :=
  ∫ v : Vec, g (x, v) • velocity v




structure Solution where
  f : Particle
  E : Field
  B : Field

def particleHalfSpace : Set (ℝ × Phase) := {z | 0 ≤ z.1}
def fieldHalfSpace : Set (ℝ × Vec) := {z | 0 ≤ z.1}

def TimeContinuousL2 (F : Field) : Prop :=
  ∃ F₂ : ℝ → Lp Vec 2 (volume : Measure Vec),
    ContinuousOn F₂ (Ici 0) ∧
    ∀ t, 0 ≤ t → (F₂ t : Vec → Vec) =ᵐ[volume] (fun x => F (t, x))


def CompactOnFiniteHorizons (s : Solution) : Prop :=
  ∀ T : ℝ, 0 ≤ T → ∃ K : Set Phase, IsCompact K ∧
    ∀ t ∈ Icc 0 T, tsupport (fun z => s.f (t, z)) ⊆ K




end RVM
end

end OAI

end

section

namespace OAI

/-! Elementary relativistic geometry needed by the retarded-force identity. -/

noncomputable section
open MeasureTheory Set
open scoped ContDiff

namespace RVM

lemma q_pos (v : Vec) : 0 < q v := by
  exact Real.sqrt_pos.2 (by positivity)

lemma q_sq (v : Vec) : q v ^ 2 = 1 + ‖v‖ ^ 2 := by
  exact Real.sq_sqrt (by positivity)

lemma norm_lt_q (v : Vec) : ‖v‖ < q v := by
  have hp := q_pos v
  have hs := q_sq v
  nlinarith [sq_nonneg ‖v‖, norm_nonneg v]

lemma norm_velocity_lt_one (v : Vec) : ‖velocity v‖ < 1 := by
  rw [velocity, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 (q_pos v))]
  rw [← div_eq_inv_mul]
  exact (div_lt_one (q_pos v)).2 (norm_lt_q v)




lemma dot_smul_left (r : ℝ) (a b : Vec) : dot (r • a) b = r * dot a b := by
  simp [dot, mul_assoc, Finset.mul_sum]




lemma dot_eq_inner (a b : Vec) : dot a b = inner ℝ a b := by
  simp [dot, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]

lemma dot_self (a : Vec) : dot a a = ‖a‖ ^ 2 := by
  rw [dot_eq_inner, real_inner_self_eq_norm_sq]




































open scoped Topology

end RVM
end

end OAI

end

section

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped ContDiff

namespace RVM
open scoped Topology





lemma hasDerivAt_particle_energy {V : ℝ → Vec} {K : Vec} {s : ℝ}
    (hV : HasDerivAt V K s) :
    HasDerivAt (fun t => q (V t)) (dot (velocity (V s)) K) s := by
  have hp : 1+‖V s‖^2 ≠ 0 := ne_of_gt (by positivity)
  have h := ((hV.norm_sq).const_add 1).sqrt hp
  convert h using 1 <;> try rfl
  rw [velocity, dot_smul_left, dot_eq_inner]
  dsimp [q]
  have hq : Real.sqrt (1+‖V s‖^2) ≠ 0 := ne_of_gt (q_pos (V s))
  field_simp

lemma hasDerivAt_particle_velocity {V : ℝ → Vec} {K : Vec} {s : ℝ}
    (hV : HasDerivAt V K s) :
    HasDerivAt (fun t => velocity (V t))
      ((q (V s))⁻¹ • (K-dot (velocity (V s)) K • velocity (V s))) s := by
  have hq := hasDerivAt_particle_energy hV
  have h := (hq.inv (ne_of_gt (q_pos (V s)))).smul hV
  convert h using 1 <;> try rfl
  ext i
  simp only [Pi.inv_apply, velocity, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring



lemma contDiff_q {k : ℕ∞ω} : ContDiff ℝ k q := by
  exact ((contDiff_const : ContDiff ℝ k (fun _ : Vec => (1 : ℝ))).add
    (contDiff_id.norm_sq ℝ)).sqrt (fun v => by positivity)

lemma contDiff_velocity {k : ℕ∞ω} : ContDiff ℝ k velocity := by
  exact (contDiff_q.inv (fun v => ne_of_gt (q_pos v))).smul contDiff_id

lemma contDiff_cross {k : ℕ∞ω} : ContDiff ℝ k (fun z : Vec × Vec => cross z.1 z.2) := by
  apply contDiff_euclidean.mpr
  intro i
  fin_cases i
  · change ContDiff ℝ k (fun z : Vec × Vec => z.1 1 * z.2 2 - z.1 2 * z.2 1)
    fun_prop
  · change ContDiff ℝ k (fun z : Vec × Vec => z.1 2 * z.2 0 - z.1 0 * z.2 2)
    fun_prop
  · change ContDiff ℝ k (fun z : Vec × Vec => z.1 0 * z.2 1 - z.1 1 * z.2 0)
    fun_prop




lemma sum_basis (v : Vec) : ∑ i : Fin 3, v i • basis i = v := by
  ext j
  simp [basis, Pi.single_apply]

lemma clm_sum_basis (L : Vec →L[ℝ] ℝ) (v : Vec) :
    L v = ∑ i : Fin 3, v i * L (basis i) := by
  conv_lhs => rw [← sum_basis v]
  simp only [map_sum, map_smul, smul_eq_mul]

lemma full_directional_derivative {f : Particle} {t : ℝ} {x v u K : Vec}
    (hf : DifferentiableAt ℝ f (t,x,v)) :
    fderiv ℝ f (t,x,v) (1,u,K) =
      deriv (fun t' => f (t',x,v)) t +
      (∑ i : Fin 3, u i * spatialPartial (fun y => f (t,y,v)) x i) +
      (∑ i : Fin 3, K i * spatialPartial (fun v' => f (t,x,v')) v i) := by
  let L := fderiv ℝ f (t,x,v)
  have hT := hf.hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t (x,v)))
  have hιX : HasFDerivAt (fun y : Vec => (t,y,v))
      ((0 : Vec →L[ℝ] ℝ).prod ((ContinuousLinearMap.id ℝ Vec).prod 0)) x := by
    exact (hasFDerivAt_const t x).prodMk
      ((hasFDerivAt_id x).prodMk (hasFDerivAt_const v x))
  have hιV : HasFDerivAt (fun y : Vec => (t,x,y))
      ((0 : Vec →L[ℝ] ℝ).prod ((0 : Vec →L[ℝ] Vec).prod (ContinuousLinearMap.id ℝ Vec))) v := by
    exact (hasFDerivAt_const t v).prodMk
      ((hasFDerivAt_const x v).prodMk (hasFDerivAt_id v))
  have hX := hf.hasFDerivAt.comp x hιX
  have hV := hf.hasFDerivAt.comp v hιV
  have ht : deriv (fun t' => f (t',x,v)) t = L (1,0,0) := by
    have h := hT.deriv
    exact h
  have hx : fderiv ℝ (fun y => f (t,y,v)) x u = L (0,u,0) := by
    have h := congrArg (fun F : Vec →L[ℝ] ℝ => F u) hX.fderiv
    convert h using 1 <;> rfl
  have hv : fderiv ℝ (fun v' => f (t,x,v')) v K = L (0,0,K) := by
    have h := congrArg (fun F : Vec →L[ℝ] ℝ => F K) hV.fderiv
    convert h using 1 <;> rfl
  change L (1,u,K) = deriv (fun t' => f (t',x,v)) t +
    (∑ i : Fin 3, u i * fderiv ℝ (fun y => f (t,y,v)) x (basis i)) +
    (∑ i : Fin 3, K i * fderiv ℝ (fun v' => f (t,x,v')) v (basis i))
  rw [← clm_sum_basis, ← clm_sum_basis, ht, hx, hv]
  rw [← map_add, ← map_add]
  congr 1
  ext <;> simp


lemma particle_differentiableAt_positive {s : Solution}
    (hreg : ContDiffOn ℝ 1 s.f particleHalfSpace) {t : ℝ} (ht : 0 < t) (x v : Vec) :
    DifferentiableAt ℝ s.f (t,x,v) := by
  have hnhds : particleHalfSpace ∈ nhds (t,x,v) := by
    have hopen : IsOpen {z : ℝ × Phase | 0 < z.1} :=
      isOpen_lt continuous_const continuous_fst
    apply Filter.mem_of_superset (hopen.mem_nhds ht)
    intro z hz
    change 0 ≤ z.1
    exact le_of_lt hz
  exact ((hreg (t,x,v) ht.le).contDiffAt hnhds).differentiableAt (by norm_num)





lemma cross_dot_square (a b : Vec) :
    dot (cross a b) (cross a b) = dot a a * dot b b - (dot a b)^2 := by
  simp [dot, cross, Fin.sum_univ_succ]
  ring

lemma norm_cross_le (a b : Vec) : ‖cross a b‖ ≤ ‖a‖*‖b‖ := by
  have h := cross_dot_square a b
  simp only [dot_self] at h
  nlinarith [norm_nonneg (cross a b), norm_nonneg a, norm_nonneg b,
    mul_nonneg (norm_nonneg a) (norm_nonneg b), sq_nonneg (dot a b)]




lemma fderiv_velocity_apply (v h : Vec) :
    fderiv ℝ velocity v h = (q v)⁻¹ • (h-dot (velocity v) h • velocity v) := by
  have hc : HasDerivAt (fun r : ℝ => v+r • h) h 0 := by
    have hh := (hasDerivAt_const (0 : ℝ) v).add
      ((hasDerivAt_id (0 : ℝ)).smul_const h)
    change HasDerivAt (fun r : ℝ => v+r • h) (0+(1 : ℝ) • h) 0 at hh
    simpa only [zero_add, one_smul] using hh
  have hv : HasFDerivAt velocity (fderiv ℝ velocity v) (v+(0 : ℝ) • h) := by
    simpa only [zero_smul, add_zero] using
      (contDiff_velocity.differentiable (by simp : (1 : ℕ∞ω) ≠ 0) v).hasFDerivAt
  have h₁ := hv.comp_hasDerivAt 0 hc
  have h₂ := hasDerivAt_particle_velocity hc
  have he := h₁.unique h₂
  simpa using he

lemma spatialPartial_velocity (v : Vec) (i j : Fin 3) :
    spatialPartial (fun w => velocity w j) v i =
      (q v)⁻¹ * ((if i=j then 1 else 0)-velocity v i*velocity v j) := by
  have hv : DifferentiableAt ℝ velocity v := contDiff_velocity.differentiable (by simp : (1 : ℕ∞ω) ≠ 0) v
  have hj := (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) j).hasFDerivAt.comp v hv.hasFDerivAt
  have hp := congrArg (fun L : Vec →L[ℝ] ℝ => L (basis i)) hj.fderiv
  have h : spatialPartial (fun w => velocity w j) v i =
      (fderiv ℝ velocity v (basis i)) j := by
    convert hp using 1 <;> rfl
  rw [h, fderiv_velocity_apply]
  simp [basis, dot, eq_comm]

lemma spatialPartial_mul {f g : Vec → ℝ} {x : Vec}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (i : Fin 3) :
    spatialPartial (fun y => f y*g y) x i =
      f x*spatialPartial g x i+g x*spatialPartial f x i := by
  change fderiv ℝ (f*g) x (basis i) = _
  rw [fderiv_mul hf hg]
  rfl

lemma spatialPartial_sub {f g : Vec → ℝ} {x : Vec}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (i : Fin 3) :
    spatialPartial (fun y => f y-g y) x i =
      spatialPartial f x i-spatialPartial g x i := by
  change fderiv ℝ (f-g) x (basis i) = _
  rw [fderiv_sub hf hg]
  rfl

lemma divergence_magnetic_force (v B : Vec) :
    divergence (fun w => cross (velocity w) B) v = 0 := by
  have hd (j : Fin 3) : DifferentiableAt ℝ (fun w : Vec => velocity w j) v :=
    (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) j).differentiableAt.comp v
      (contDiff_velocity.differentiable (by simp : (1 : ℕ∞ω) ≠ 0) v)
  simp only [divergence, Fin.sum_univ_succ]
  change spatialPartial (fun w => velocity w 1 * B 2 - velocity w 2 * B 1) v 0 +
    (spatialPartial (fun w => velocity w 2 * B 0 - velocity w 0 * B 2) v 1 +
    (spatialPartial (fun w => velocity w 0 * B 1 - velocity w 1 * B 0) v 2 + 0)) = 0
  simp only [spatialPartial_sub ((hd _).mul_const _) ((hd _).mul_const _),
    spatialPartial_mul (hd _) (differentiableAt_const _), spatialPartial_velocity]
  simp [spatialPartial]
  ring

lemma divergence_cross {F G : Vec → Vec} {x : Vec}
    (hF : DifferentiableAt ℝ F x) (hG : DifferentiableAt ℝ G x) :
    divergence (fun y => cross (F y) (G y)) x =
      dot (G x) (curl F x) - dot (F x) (curl G x) := by
  have hf (i : Fin 3) : DifferentiableAt ℝ (fun y => F y i) x :=
    (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) i).differentiableAt.comp x hF
  have hg (i : Fin 3) : DifferentiableAt ℝ (fun y => G y i) x :=
    (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) i).differentiableAt.comp x hG
  simp only [divergence, Fin.sum_univ_succ]
  change spatialPartial (fun y => F y 1 * G y 2 - F y 2 * G y 1) x 0 +
    (spatialPartial (fun y => F y 2 * G y 0 - F y 0 * G y 2) x 1 +
    (spatialPartial (fun y => F y 0 * G y 1 - F y 1 * G y 0) x 2+0)) = _
  have hm (i j k : Fin 3) :
      spatialPartial ((fun y => F y i) * (fun y => G y j)) x k =
        F x i * spatialPartial (fun y => G y j) x k +
        G x j * spatialPartial (fun y => F y i) x k :=
    spatialPartial_mul (hf i) (hg j) k
  have hs (i j k l r : Fin 3) := spatialPartial_sub ((hf i).mul (hg j)) ((hf k).mul (hg l)) r
  simp only [Pi.mul_apply] at hs
  simp only [hs, hm]
  simp [dot, curl, Fin.sum_univ_succ]
  ring

lemma hasDerivAt_field_energy {E B : ℝ → Vec} {e b : Vec} {t : ℝ}
    (he : HasDerivAt E e t) (hb : HasDerivAt B b t) :
    HasDerivAt (fun s => (‖E s‖^2+‖B s‖^2)/2)
      (dot (E t) e + dot (B t) b) t := by
  have h := (he.norm_sq.add hb.norm_sq).div_const 2
  have h2 : (2 * inner ℝ (E t) e + 2 * inner ℝ (B t) b) / 2 = dot (E t) e + dot (B t) b := by
    rw [← dot_eq_inner, ← dot_eq_inner]; ring
  rw [h2] at h
  exact h

lemma maxwell_energy_balance {E B : Field} {j : Vec} {t : ℝ} {x : Vec}
    (hE : DifferentiableAt ℝ E (t,x)) (hB : DifferentiableAt ℝ B (t,x))
    (he : deriv (fun s => E (s,x)) t - curl (fun y => B (t,y)) x = -j)
    (hb : deriv (fun s => B (s,x)) t + curl (fun y => E (t,y)) x = 0) :
    deriv (fun s => (‖E (s,x)‖^2+‖B (s,x)‖^2)/2) t +
      divergence (fun y => cross (E (t,y)) (B (t,y))) x = -dot (E (t,x)) j := by
  have heT : DifferentiableAt ℝ (fun s => E (s,x)) t :=
    hE.comp t (differentiableAt_id.prodMk (differentiableAt_const x))
  have hbT : DifferentiableAt ℝ (fun s => B (s,x)) t :=
    hB.comp t (differentiableAt_id.prodMk (differentiableAt_const x))
  have heX : DifferentiableAt ℝ (fun y => E (t,y)) x :=
    hE.comp x ((differentiableAt_const t).prodMk differentiableAt_id)
  have hbX : DifferentiableAt ℝ (fun y => B (t,y)) x :=
    hB.comp x ((differentiableAt_const t).prodMk differentiableAt_id)
  rw [(hasDerivAt_field_energy heT.hasDerivAt hbT.hasDerivAt).deriv,
    divergence_cross heX hbX]
  have he' : deriv (fun s => E (s,x)) t = curl (fun y => B (t,y)) x-j := by
    apply sub_eq_iff_eq_add.mp at he
    simpa only [sub_eq_add_neg, add_comm] using he
  have hb' : deriv (fun s => B (s,x)) t = -curl (fun y => E (t,y)) x :=
    eq_neg_of_add_eq_zero_left hb
  rw [he', hb']
  simp only [dot, PiLp.sub_apply, PiLp.neg_apply, mul_sub, mul_neg,
    Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  ring

end RVM
end

end OAI

end

section

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped ContDiff

namespace RVM
open scoped Topology



lemma integral_mul_spatialPartial {F g : Vec → ℝ}
    (hF : ContDiff ℝ 1 F) (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g)
    (i : Fin 3) :
    (∫ v, F v * spatialPartial g v i) =
      -(∫ v, spatialPartial F v i * g v) := by
  apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
  · exact (((hF.continuous_fderiv (by simp)).clm_apply continuous_const).mul hg.continuous).integrable_of_hasCompactSupport hc.mul_left
  · exact (hF.continuous.mul
      ((hg.continuous_fderiv (by simp)).clm_apply continuous_const)).integrable_of_hasCompactSupport (hc.fderiv_apply ℝ (basis i)).mul_left
  · exact (hF.continuous.mul hg.continuous).integrable_of_hasCompactSupport hc.mul_left
  · exact fun x _ => hF.differentiable (by simp) x
  · exact fun x _ => hg.differentiable (by simp) x



lemma contDiff_lorentz (E B : Vec) {k : ℕ∞ω} :
    ContDiff ℝ k (fun v => E+cross (velocity v) B) := by
  exact contDiff_const.add (contDiff_cross.comp (contDiff_velocity.prodMk contDiff_const))

lemma divergence_lorentz (v E B : Vec) :
    divergence (fun w => E+cross (velocity w) B) v = 0 := by
  have hh (i : Fin 3) : spatialPartial (fun w => (E+cross (velocity w) B) i) v i =
      spatialPartial (fun w => cross (velocity w) B i) v i := by
    simp only [PiLp.add_apply, spatialPartial]
    rw [fderiv_const_add]
  simpa only [divergence, hh] using divergence_magnetic_force v B



lemma hasFDerivAt_integral_uniform_support
    {H W : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {U : Set H} {K : Set Vec} {F : H × Vec → W} {p : H}
    (hU : IsOpen U) (hK : IsCompact K) (hp : p ∈ U)
    (hF : ContDiffOn ℝ 1 F (U ×ˢ univ))
    (hzero : ∀ x ∈ U, ∀ v ∉ K, F (x,v) = 0) :
    HasFDerivAt (fun x => ∫ v : Vec, F (x,v))
      ((∫ v : Vec, fderiv ℝ F (p,v)).comp (ContinuousLinearMap.inl ℝ H Vec)) p := by
  have h := hasFDerivAt_convolution_right_with_param
    (μ := (volume : Measure Vec)) (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] W →L[ℝ] W)
    (g := fun x v => F (x,v)) hU hK (fun x v hx hv => hzero x hx v hv)
    (locallyIntegrable_const (1 : ℝ)) hF (p,0) hp
  have hi : HasFDerivAt (fun x : H => (x,(0 : Vec)))
      (ContinuousLinearMap.inl ℝ H Vec) p := by
    convert (hasFDerivAt_id p).prodMk (hasFDerivAt_const (0 : Vec) p) using 1 <;> rfl
  have hc := h.comp p hi
  have hls : (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] W →L[ℝ] W) 1 =
      ContinuousLinearMap.id ℝ W := by ext w; simp
  change HasFDerivAt (fun x => convolution (fun _ => (1 : ℝ)) (fun v => F (x,v))
    (ContinuousLinearMap.lsmul ℝ ℝ) volume 0)
    ((convolution (fun _ => (1 : ℝ)) (fun v => fderiv ℝ F (p,v))
      (ContinuousLinearMap.precompR (H × Vec) (ContinuousLinearMap.lsmul ℝ ℝ)) volume 0).comp
      (ContinuousLinearMap.inl ℝ H Vec)) p at hc
  simp only [convolution_def, zero_sub, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.precompR_apply, ContinuousLinearMap.compL_apply, hls,
    ContinuousLinearMap.id_comp] at hc
  have hn (x : H) : (∫ v : Vec, F (x,-v)) = ∫ v : Vec, F (x,v) :=
    integral_neg_eq_self (fun v : Vec => F (x,v)) volume
  have hn' : (∫ v : Vec, fderiv ℝ F (p,-v)) = ∫ v : Vec, fderiv ℝ F (p,v) :=
    integral_neg_eq_self (fun v : Vec => fderiv ℝ F (p,v)) volume
  simpa only [hn, hn'] using hc

lemma compactSupport_of_zero_off {W : Type*} [Zero W]
    {K : Set Vec} {g : Vec → W} (hK : IsCompact K)
    (hz : ∀ v ∉ K, g v = 0) : HasCompactSupport g := by
  apply hK.of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ hK.isClosed
  intro v hv
  by_contra hn
  exact hv (hz v hn)

lemma compactSupport_param_fderiv
    {H W : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {U : Set H} {K : Set Vec} {F : H × Vec → W} {p : H}
    (hU : IsOpen U) (hK : IsCompact K) (hp : p ∈ U)
    (hzero : ∀ x ∈ U, ∀ v ∉ K, F (x,v) = 0) :
    HasCompactSupport (fun v : Vec => fderiv ℝ F (p,v)) := by
  apply compactSupport_of_zero_off hK
  intro v hv
  have hn : U ×ˢ Kᶜ ∈ 𝓝 (p,v) :=
    (hU.prod hK.isClosed.isOpen_compl).mem_nhds ⟨hp,hv⟩
  have hz : F =ᶠ[𝓝 (p,v)] (fun _ => 0) := by
    filter_upwards [hn] with y hy
    exact hzero y.1 hy.1 y.2 hy.2
  simpa only [fderiv_const_apply] using hz.fderiv_eq (𝕜 := ℝ)

lemma integrable_param_fderiv
    {H W : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {U : Set H} {K : Set Vec} {F : H × Vec → W} {p : H}
    (hU : IsOpen U) (hK : IsCompact K) (hp : p ∈ U)
    (hF : ContDiffOn ℝ 1 F (U ×ˢ univ))
    (hzero : ∀ x ∈ U, ∀ v ∉ K, F (x,v) = 0) :
    Integrable (fun v : Vec => fderiv ℝ F (p,v)) := by
  have hc : Continuous (fun v : Vec => fderiv ℝ F (p,v)) :=
    (hF.continuousOn_fderiv_of_isOpen (hU.prod isOpen_univ) le_rfl).comp_continuous
      (continuous_const.prodMk continuous_id) (fun _ => ⟨hp, mem_univ _⟩)
  exact hc.integrable_of_hasCompactSupport (compactSupport_param_fderiv hU hK hp hzero)

lemma fderiv_integral_uniform_support_apply
    {H W : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {U : Set H} {K : Set Vec} {F : H × Vec → W} {p : H}
    (hU : IsOpen U) (hK : IsCompact K) (hp : p ∈ U)
    (hF : ContDiffOn ℝ 1 F (U ×ˢ univ))
    (hzero : ∀ x ∈ U, ∀ v ∉ K, F (x,v) = 0) (b : H) :
    fderiv ℝ (fun x => ∫ v : Vec, F (x,v)) p b =
      ∫ v : Vec, fderiv ℝ F (p,v) (b,0) := by
  rw [(hasFDerivAt_integral_uniform_support hU hK hp hF hzero).fderiv]
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply] using
    (ContinuousLinearMap.integral_apply (integrable_param_fderiv hU hK hp hF hzero) (b,0))

lemma fderiv_weighted_param {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {F : H × Vec → ℝ} {w : Vec → ℝ} {p : H} {v : Vec}
    (hF : DifferentiableAt ℝ F (p,v)) (hw : DifferentiableAt ℝ w v) (b : H) :
    fderiv ℝ (fun z : H × Vec => w z.2 * F z) (p,v) (b,0) =
      w v * fderiv ℝ F (p,v) (b,0) := by
  have hdw := hw.hasFDerivAt.comp (p,v) (hasFDerivAt_snd (𝕜 := ℝ) (p := (p,v)))
  have he := congrArg (fun L : (H × Vec) →L[ℝ] ℝ => L (b,0)) (hdw.mul hF.hasFDerivAt).fderiv
  change fderiv ℝ (fun z : H × Vec => w z.2 * F z) (p,v) (b,0) =
    w v * fderiv ℝ F (p,v) (b,0) + F (p,v) * fderiv ℝ w v 0 at he
  simpa only [map_zero, mul_zero, add_zero] using he

lemma fderiv_weighted_integral_uniform_support_apply
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {U : Set H} {K : Set Vec} {F : H × Vec → ℝ} {p : H} {w : Vec → ℝ}
    (hU : IsOpen U) (hK : IsCompact K) (hp : p ∈ U)
    (hF : ContDiffOn ℝ 1 F (U ×ˢ univ)) (hw : ContDiff ℝ 1 w)
    (hzero : ∀ x ∈ U, ∀ v ∉ K, F (x,v) = 0) (b : H) :
    fderiv ℝ (fun x => ∫ v : Vec, w v * F (x,v)) p b =
      ∫ v : Vec, w v * fderiv ℝ F (p,v) (b,0) := by
  have hG : ContDiffOn ℝ 1 (fun z : H × Vec => w z.2 * F z) (U ×ˢ univ) :=
    (hw.comp contDiff_snd).contDiffOn.mul hF
  rw [fderiv_integral_uniform_support_apply hU hK hp hG
    (fun x hx v hv => by simp only [hzero x hx v hv, mul_zero])]
  apply integral_congr_ae
  filter_upwards [] with v
  exact fderiv_weighted_param
    (((hF (p,v) ⟨hp,mem_univ _⟩).contDiffAt
      ((hU.prod isOpen_univ).mem_nhds ⟨hp,mem_univ _⟩)).differentiableAt (by simp))
    (hw.differentiable (by simp) v) b

lemma clm_spacetime_velocity_split (L : ((ℝ × Vec) × Vec) →L[ℝ] ℝ)
    (u K : Vec) :
    L ((1,u),K) = L ((1,0),0) +
      ∑ i : Fin 3, u i * L ((0,basis i),0) +
      ∑ i : Fin 3, K i * L ((0,0),basis i) := by
  let A : Vec →L[ℝ] ((ℝ × Vec) × Vec) :=
    ((0 : Vec →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ Vec)).prod 0
  let B : Vec →L[ℝ] ((ℝ × Vec) × Vec) :=
    (0 : Vec →L[ℝ] (ℝ × Vec)).prod (ContinuousLinearMap.id ℝ Vec)
  have hu := clm_sum_basis (L.comp A) u
  have hK := clm_sum_basis (L.comp B) K
  change L ((0,u),0) = ∑ i : Fin 3, u i * L ((0,basis i),0) at hu
  change L ((0,0),K) = ∑ i : Fin 3, K i * L ((0,0),basis i) at hK
  rw [← hu, ← hK, ← map_add, ← map_add]
  congr 1
  ext <;> simp

lemma fderiv_velocity_slice {F : (ℝ × Vec) × Vec → ℝ} {p : ℝ × Vec} {v : Vec}
    (hF : DifferentiableAt ℝ F (p,v)) (b : Vec) :
    fderiv ℝ (fun w => F (p,w)) v b = fderiv ℝ F (p,v) ((0,0),b) := by
  have he := hF.hasFDerivAt.comp v
    ((hasFDerivAt_const p v).prodMk (hasFDerivAt_id v))
  exact congrArg (fun L : Vec →L[ℝ] ℝ => L b) he.fderiv

lemma integrable_param_fderiv_apply_weight
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {U : Set H} {K : Set Vec} {F : H × Vec → ℝ} {p : H} {w : Vec → ℝ}
    (hU : IsOpen U) (hK : IsCompact K) (hp : p ∈ U)
    (hF : ContDiffOn ℝ 1 F (U ×ˢ univ)) (hw : Continuous w)
    (hzero : ∀ x ∈ U, ∀ v ∉ K, F (x,v) = 0) (b : H × Vec) :
    Integrable (fun v => w v * fderiv ℝ F (p,v) b) := by
  have hc : Continuous (fun v : Vec => fderiv ℝ F (p,v)) :=
    (hF.continuousOn_fderiv_of_isOpen (hU.prod isOpen_univ) le_rfl).comp_continuous
      (continuous_const.prodMk continuous_id) (fun _ => ⟨hp, mem_univ _⟩)
  apply (hw.mul (hc.clm_apply continuous_const)).integrable_of_hasCompactSupport
  apply (compactSupport_param_fderiv hU hK hp hzero).comp_left
    (g := fun L : (H × Vec) →L[ℝ] ℝ => L b) (by simp) |>.mul_left



def particleBySpacetime (f : Particle) : (ℝ × Vec) × Vec → ℝ :=
  fun z => f (z.1.1,z.1.2,z.2)

lemma contDiff_reassociate {k : ℕ∞ω} :
    ContDiff ℝ k (fun z : (ℝ × Vec) × Vec => (z.1.1,z.1.2,z.2)) :=
  contDiff_fst.fst.prodMk (contDiff_fst.snd.prodMk contDiff_snd)

lemma particle_spacetime_local_data {s : Solution} {t : ℝ} (x : Vec)
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace)
    (hc : CompactOnFiniteHorizons s) (ht : 0 < t) :
    ∃ (U : Set (ℝ × Vec)) (K : Set Vec),
      IsOpen U ∧ IsCompact K ∧ (t,x) ∈ U ∧
      ContDiffOn ℝ 1 (particleBySpacetime s.f) (U ×ˢ univ) ∧
      ∀ p ∈ U, ∀ v ∉ K, particleBySpacetime s.f (p,v) = 0 := by
  obtain ⟨K₀,hK₀,hzero⟩ := hc (t+1) (by linarith)
  let U : Set (ℝ × Vec) := {p | p.1 ∈ Ioo 0 (t+1)}
  refine ⟨U, Prod.snd '' K₀, isOpen_Ioo.preimage continuous_fst,
    hK₀.image continuous_snd, ⟨ht,by linarith⟩, ?_, ?_⟩
  · exact hf.comp contDiff_reassociate.contDiffOn (fun z hz => le_of_lt hz.1.1)
  · intro p hp v hv
    change s.f (p.1,p.2,v) = 0
    by_contra hn
    have hh : (p.2,v) ∈ tsupport (fun z => s.f (p.1,z)) := subset_tsupport _ hn
    have hm := hzero p.1 ⟨le_of_lt hp.1, le_of_lt hp.2⟩ hh
    exact hv ⟨(p.2,v),hm,rfl⟩

lemma fderiv_particleBySpacetime {f : Particle} {t : ℝ} {x v u K : Vec}
    (hf : DifferentiableAt ℝ f (t,x,v)) :
    fderiv ℝ (particleBySpacetime f) ((t,x),v) ((1,u),K) =
      fderiv ℝ f (t,x,v) (1,u,K) := by
  let A : ((ℝ × Vec) × Vec) →L[ℝ] (ℝ × Phase) :=
    ((ContinuousLinearMap.fst ℝ ℝ Vec).comp
      (ContinuousLinearMap.fst ℝ (ℝ × Vec) Vec)).prod
      (((ContinuousLinearMap.snd ℝ ℝ Vec).comp
        (ContinuousLinearMap.fst ℝ (ℝ × Vec) Vec)).prod
          (ContinuousLinearMap.snd ℝ (ℝ × Vec) Vec))
  have hA : HasFDerivAt (fun z : (ℝ × Vec) × Vec => (z.1.1,z.1.2,z.2)) A
      ((t,x),v) :=
    hasFDerivAt_fst.fst.prodMk (hasFDerivAt_fst.snd.prodMk hasFDerivAt_snd)
  have he := congrArg (fun L : ((ℝ × Vec) × Vec) →L[ℝ] ℝ => L ((1,u),K))
    (hf.hasFDerivAt.comp ((t,x),v) hA).fderiv
  exact he



lemma contDiffOn_integral_uniform_support
    {H W : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {n : ℕ∞} {U : Set H} {K : Set Vec} {F : H × Vec → W}
    (hU : IsOpen U) (hK : IsCompact K)
    (hF : ContDiffOn ℝ n F (U ×ˢ univ))
    (hzero : ∀ x ∈ U, ∀ v ∉ K, F (x,v) = 0) :
    ContDiffOn ℝ n (fun x => ∫ v : Vec, F (x,v)) U := by
  have h := contDiffOn_convolution_right_with_param_comp
    (μ := (volume : Measure Vec)) (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] W →L[ℝ] W)
    (v := fun _ : H => (0 : Vec)) contDiffOn_const (g := fun x v => F (x,v))
    hU hK (fun x v hx hv => hzero x hx v hv) (locallyIntegrable_const (1 : ℝ)) hF
  have hn (x : H) : convolution (fun _ : Vec => (1 : ℝ)) (fun v => F (x,v))
      (ContinuousLinearMap.lsmul ℝ ℝ) volume 0 = ∫ v : Vec, F (x,v) := by
    simp only [convolution_def, zero_sub, ContinuousLinearMap.lsmul_apply, one_smul]
    exact integral_neg_eq_self (fun v : Vec => F (x,v)) volume
  simpa only [hn] using h








end RVM
end

end OAI

end

section

namespace OAI

noncomputable section

section
open MeasureTheory Set
open scoped ContDiff

namespace RVM
open scoped Topology

lemma deriv_time_slice {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {G : ℝ × Vec → W} {t : ℝ} {x : Vec} (hG : DifferentiableAt ℝ G (t,x)) :
    deriv (fun r => G (r,x)) t = fderiv ℝ G (t,x) (1,0) :=
  (hG.hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))).deriv

lemma spatialPartial_time_slice {G : ℝ × Vec → ℝ} {t : ℝ} {x : Vec}
    (hG : DifferentiableAt ℝ G (t,x)) (i : Fin 3) :
    spatialPartial (fun y => G (t,y)) x i = fderiv ℝ G (t,x) (0,basis i) := by
  exact congrArg (fun L : Vec →L[ℝ] ℝ => L (basis i))
    (hG.hasFDerivAt.comp x ((hasFDerivAt_const t x).prodMk (hasFDerivAt_id x))).fderiv



lemma field_differentiableAt_positive {F : Field}
    (hF : ContDiffOn ℝ 1 F fieldHalfSpace) {t : ℝ} (ht : 0 < t) (x : Vec) :
    DifferentiableAt ℝ F (t,x) := by
  apply (hF.contDiffAt _).differentiableAt (by simp)
  apply Filter.mem_of_superset
    ((isOpen_lt continuous_const continuous_fst).mem_nhds ht)
  intro z hz
  change 0 ≤ z.1
  exact le_of_lt hz

lemma divergence_add {F G : Vec → Vec} {x : Vec}
    (hF : DifferentiableAt ℝ F x) (hG : DifferentiableAt ℝ G x) :
    divergence (fun y => F y+G y) x = divergence F x + divergence G x := by
  have hf (i : Fin 3) : DifferentiableAt ℝ (fun y => F y i) x :=
    (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) i).differentiableAt.comp x hF
  have hg (i : Fin 3) : DifferentiableAt ℝ (fun y => G y i) x :=
    (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) i).differentiableAt.comp x hG
  have ha (i : Fin 3) := congrArg (fun L : Vec →L[ℝ] ℝ => L (basis i))
    (fderiv_add (hf i) (hg i))
  change ∀ i : Fin 3, fderiv ℝ (fun y => F y i + G y i) x (basis i) =
    fderiv ℝ (fun y => F y i) x (basis i) + fderiv ℝ (fun y => G y i) x (basis i) at ha
  simp only [divergence, PiLp.add_apply, spatialPartial, ha, Finset.sum_add_distrib]







lemma continuousOn_integral_uniform_support
    {H W : Type*} [TopologicalSpace H]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {U : Set H} {K : Set Vec} {F : H × Vec → W}
    (hK : IsCompact K) (hF : ContinuousOn F (U ×ˢ univ))
    (hzero : ∀ x ∈ U, ∀ v ∉ K, F (x,v) = 0) :
    ContinuousOn (fun x => ∫ v : Vec, F (x,v)) U := by
  have h := continuousOn_convolution_right_with_param_comp
    (μ := (volume : Measure Vec)) (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] W →L[ℝ] W)
    (v := fun _ : H => (0 : Vec)) continuousOn_const (g := fun x v => F (x,v))
    hK (fun x v hx hv => hzero x hx v hv) (locallyIntegrable_const (1 : ℝ)) hF
  have hn (x : H) : convolution (fun _ : Vec => (1 : ℝ)) (fun v => F (x,v))
      (ContinuousLinearMap.lsmul ℝ ℝ) volume 0 = ∫ v : Vec, F (x,v) := by
    simp only [convolution_def, zero_sub, ContinuousLinearMap.lsmul_apply, one_smul]
    exact integral_neg_eq_self (fun v : Vec => F (x,v)) volume
  simpa only [hn] using h

lemma TimeContinuousL2.memLp {F : Field} (hF : TimeContinuousL2 F)
    {t : ℝ} (ht : 0 ≤ t) : MemLp (fun x => F (t,x)) 2 volume := by
  obtain ⟨F₂,hc,heq⟩ := hF
  exact (Lp.memLp (F₂ t)).ae_eq (heq t ht)

lemma TimeContinuousL2.integrable_norm_sq {F : Field} (hF : TimeContinuousL2 F)
    {t : ℝ} (ht : 0 ≤ t) : Integrable (fun x => ‖F (t,x)‖^2) := by
  have hm := hF.memLp ht
  exact (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm

lemma TimeContinuousL2.continuous_integral_norm_sq {F : Field} (hF : TimeContinuousL2 F) :
    ContinuousOn (fun t => ∫ x : Vec, ‖F (t,x)‖^2) (Ici 0) := by
  obtain ⟨F₂,hc,heq⟩ := hF
  have hh : ∀ t ∈ Ici (0:ℝ), (∫ x : Vec, ‖F (t,x)‖^2) = ‖F₂ t‖^2 := by
    intro t ht
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [heq t ht] with x hx
    rw [hx, real_inner_self_eq_norm_sq]
  exact (hc.norm.pow 2).congr (fun t ht => hh t ht)








lemma integral_mul_divergence {F : Vec → Vec} {g : Vec → ℝ}
    (hF : ContDiff ℝ 1 F) (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g) :
    (∫ x, g x * divergence F x) = -(∫ x, fderiv ℝ g x (F x)) := by
  have hFi (i : Fin 3) : ContDiff ℝ 1 (fun x => F x i) :=
    (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) i).contDiff.comp hF
  have hI (i : Fin 3) : Integrable (fun x => g x * spatialPartial (fun y => F y i) x i) :=
    (hg.continuous.mul (((hFi i).continuous_fderiv (by simp)).clm_apply continuous_const)).integrable_of_hasCompactSupport hc.mul_right
  have hJ (i : Fin 3) : Integrable (fun x => F x i * spatialPartial g x i) :=
    ((hFi i).continuous.mul ((hg.continuous_fderiv (by simp)).clm_apply continuous_const)).integrable_of_hasCompactSupport
      (hc.fderiv_apply ℝ (basis i)).mul_left
  simp only [divergence, Finset.mul_sum]
  conv_rhs => enter [1,2,x]; rw [clm_sum_basis]
  change (∫ x, ∑ i : Fin 3, g x * spatialPartial (fun y => F y i) x i) =
    -(∫ x, ∑ i : Fin 3, F x i * spatialPartial g x i)
  rw [integral_finsetSum _ (fun i _ => hI i), integral_finsetSum _ (fun i _ => hJ i)]
  simp_rw [mul_comm (g _) (spatialPartial _ _ _)]
  have he (i : Fin 3) : (∫ x, spatialPartial (fun y => F y i) x i * g x) =
      -(∫ x, F x i * spatialPartial g x i) := by
    have hh := integral_mul_spatialPartial (hFi i) hg hc i
    linarith
  simp only [he, Finset.sum_neg_distrib]






def energyBump : ContDiffBump (0 : Vec) := ⟨1,2,by norm_num,by norm_num⟩
def energyCutoff (n : ℕ) (x : Vec) : ℝ := energyBump (((n:ℝ)+1)⁻¹ • x)

lemma energyCutoff_smooth (n : ℕ) : ContDiff ℝ 1 (energyCutoff n) :=
  energyBump.contDiff.comp ((contDiff_const : ContDiff ℝ 1 (fun _ : Vec => ((n:ℝ)+1)⁻¹)).smul
    (contDiff_id : ContDiff ℝ 1 (fun x : Vec => x)))

lemma energyCutoff_compact (n : ℕ) : HasCompactSupport (energyCutoff n) := by
  apply compactSupport_of_zero_off (isCompact_closedBall (0:Vec) (2*((n:ℝ)+1)))
  intro x hx
  have hn : 0 < (n:ℝ)+1 := by positivity
  have hnX : 2 * ((n:ℝ)+1) < ‖x‖ := by simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hx
  have hnx : (((n:ℝ)+1)⁻¹ • x) ∉ Function.support energyBump := by
    rw [energyBump.support_eq]
    simp only [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hn), energyBump]
    have hh : 2 < ((n:ℝ)+1)⁻¹ * ‖x‖ := by
      rw [← div_eq_inv_mul, lt_div_iff₀ hn]
      exact hnX
    exact not_lt.mpr hh.le
  exact Function.notMem_support.mp hnx

lemma energyCutoff_bounds (n : ℕ) (x : Vec) : 0 ≤ energyCutoff n x ∧ energyCutoff n x ≤ 1 :=
  ⟨energyBump.nonneg,energyBump.le_one⟩

lemma energyCutoff_deriv_bound : ∃ C : ℝ, 0 ≤ C ∧
    ∀ n : ℕ, ∀ x : Vec, ‖fderiv ℝ (energyCutoff n) x‖ ≤ C / ((n:ℝ)+1) := by
  have hd : ContDiff ℝ 1 (energyBump : Vec → ℝ) := energyBump.contDiff
  obtain ⟨C,hC⟩ := (hd.continuous_fderiv (by simp)).bounded_above_of_compact_support
    (energyBump.hasCompactSupport.fderiv ℝ)
  have hCp : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  refine ⟨C,hCp,?_⟩
  intro n x
  have hn : 0 < (n:ℝ)+1 := by positivity
  have hh := (hd.differentiable (by simp) (((n:ℝ)+1)⁻¹ • x)).hasFDerivAt.comp x
    ((hasFDerivAt_id (𝕜 := ℝ) x).const_smul (((n:ℝ)+1)⁻¹))
  have heq := hh.fderiv
  change fderiv ℝ (energyCutoff n) x = _ at heq
  rw [heq]
  calc
    _ ≤ ‖fderiv ℝ (energyBump : Vec → ℝ) (((n:ℝ)+1)⁻¹ • x)‖ *
        ‖((n:ℝ)+1)⁻¹ • ContinuousLinearMap.id ℝ Vec‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ = ‖fderiv ℝ (energyBump : Vec → ℝ) (((n:ℝ)+1)⁻¹ • x)‖ * ((n:ℝ)+1)⁻¹ := by
      simp [norm_smul, abs_of_pos hn]
    _ ≤ C * ((n:ℝ)+1)⁻¹ := mul_le_mul_of_nonneg_right (hC _) (inv_pos.mpr hn).le
    _ = _ := div_eq_mul_inv _ _ |>.symm

lemma energyCutoff_tendsto (x : Vec) : Filter.Tendsto (fun n => energyCutoff n x) Filter.atTop (𝓝 1) := by
  have hi : Filter.Tendsto (fun n : ℕ => ((n:ℝ)+1)⁻¹) Filter.atTop (𝓝 0) := by
    exact tendsto_inv_atTop_zero.comp (Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
  have hzero : energyBump (0:Vec) = 1 := energyBump.one_of_mem_closedBall (by simp [energyBump])
  simpa only [energyCutoff, zero_smul,hzero,Function.comp_def] using! energyBump.continuous.continuousAt.tendsto.comp (hi.smul_const x)

lemma energyCutoff_integral_tendsto {F : Vec → ℝ} (hF : Integrable F) :
    Filter.Tendsto (fun n => ∫ x : Vec, energyCutoff n x * F x) Filter.atTop (𝓝 (∫ x : Vec, F x)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => ‖F x‖)
  · intro n
    exact (energyCutoff_smooth n).continuous.aestronglyMeasurable.mul hF.aestronglyMeasurable
  · exact hF.norm
  · intro n
    filter_upwards [] with x
    rw [norm_mul, Real.norm_of_nonneg (energyCutoff_bounds n x).1]
    exact mul_le_of_le_one_left (norm_nonneg _) (energyCutoff_bounds n x).2
  · filter_upwards [] with x
    simpa only [one_mul] using (energyCutoff_tendsto x).mul_const (F x)


end RVM

end

open Filter Set
open Set MeasureTheory Filter
open scoped Topology ContDiff

namespace RVM

lemma scalar_gronwall_interior {f : ℝ → ℝ} {K ε T : ℝ}
    (hK : 0 ≤ K) (hε : 0 ≤ ε) (hT : 0 ≤ T)
    (hc : ContinuousOn f (Icc 0 T)) (h0 : f 0 = 0)
    (hd : ∀ t ∈ Ioo 0 T, DifferentiableAt ℝ f t)
    (hb : ∀ t ∈ Ioo 0 T, deriv f t ≤ K*f t+ε) :
    f T ≤ ε*T*Real.exp (K*T) := by
  rcases eq_or_lt_of_le hT with he | ht
  · subst T; simp [h0]
  let g : ℝ → ℝ := fun t => f t * Real.exp (-K*t)
  have hgc : ContinuousOn g (Icc 0 T) := hc.mul (by fun_prop)
  have hgd (t : ℝ) (htt : t ∈ Ioo 0 T) :
      HasDerivAt g ((deriv f t-K*f t)*Real.exp (-K*t)) t := by
    convert (hd t htt).hasDerivAt.mul (((hasDerivAt_id t).const_mul (-K)).exp) using 1 <;> try rfl
    simp only [id_eq]
    ring
  obtain ⟨c,hc',heq⟩ := exists_deriv_eq_slope g ht hgc
    (fun t ht => (hgd t ht).differentiableAt.differentiableWithinAt)
  have he' : Real.exp (-K*c) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [hc'.1])
  have hg' : deriv g c ≤ ε := by
    rw [(hgd c hc').deriv]
    calc
      _ ≤ ε*Real.exp (-K*c) := mul_le_mul_of_nonneg_right (by linarith [hb c hc']) (Real.exp_pos _).le
      _ ≤ ε := mul_le_of_le_one_right hε he'
  rw [heq,sub_zero,show g 0=0 by simp [g,h0],sub_zero] at hg'
  have hlast := (div_le_iff₀ ht).mp hg'
  have hx := mul_le_mul_of_nonneg_right hlast (Real.exp_pos (K*T)).le
  simpa only [g,mul_assoc,← Real.exp_add,neg_mul,neg_add_cancel,Real.exp_zero,mul_one] using hx

lemma weighted_density_hasDerivAt
    {e : ℝ × Vec → ℝ} {g : Vec → ℝ} {t : ℝ}
    (he : ContDiffOn ℝ 1 e (Ioi 0 ×ˢ (univ : Set Vec)))
    (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g) (ht : 0 < t) :
    HasDerivAt (fun r => ∫ x : Vec, g x*e (r,x))
      (∫ x : Vec, g x*fderiv ℝ e (t,x) (1,0)) t := by
  have hF : ContDiffOn ℝ 1 (fun p : ℝ × Vec => g p.2*e p)
      (Ioi 0 ×ˢ (univ : Set Vec)) := (hg.comp contDiff_snd).contDiffOn.mul he
  have hz : ∀ r ∈ Ioi (0:ℝ), ∀ x ∉ tsupport g, g x*e (r,x)=0 := by
    intro r _ x hx
    rw [image_eq_zero_of_notMem_tsupport hx,zero_mul]
  have hi := fderiv_integral_uniform_support_apply isOpen_Ioi hc ht hF hz (1:ℝ)
  have hd := hasFDerivAt_integral_uniform_support isOpen_Ioi hc ht hF hz
  have heq (x : Vec) : fderiv ℝ (fun p : ℝ × Vec => g p.2*e p) (t,x) (1,0) =
      g x*fderiv ℝ e (t,x) (1,0) := by
    have he' := he.contDiffAt (x := (t,x)) ((isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨ht,mem_univ x⟩)
    have heT : DifferentiableAt ℝ (fun r => e (r,x)) t :=
      DifferentiableAt.comp t (f := fun r : ℝ => (r,x)) (g := e)
        (he'.differentiableAt (by simp))
        (differentiableAt_id.prodMk (differentiableAt_const x))
    have hgT := heT.hasDerivAt.const_mul (g x)
    have hf := hF.contDiffAt (x := (t,x)) ((isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨ht,mem_univ x⟩)
    rw [← deriv_time_slice (hf.differentiableAt (by simp)), hgT.deriv,
      deriv_time_slice (he'.differentiableAt (by simp))]
  have hid : deriv (fun r => ∫ x : Vec, g x*e (r,x)) t =
      ∫ x : Vec, g x*fderiv ℝ e (t,x) (1,0) := by
    change fderiv ℝ (fun r => ∫ x : Vec, g x*e (r,x)) t 1 = _
    rw [hi]
    simp only [heq]
  exact hid ▸ hd.differentiableAt.hasDerivAt

lemma continuous_divergence {F : Vec → Vec} (hF : ContDiff ℝ 1 F) :
    Continuous (divergence F) := by
  unfold divergence spatialPartial
  apply continuous_finsetSum
  intro i _
  have hi : ContDiff ℝ 1 (fun x => F x i) :=
    (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) i).contDiff.comp hF
  exact (hi.continuous_fderiv (by simp)).clm_apply continuous_const

lemma weighted_density_deriv_le
    {e : ℝ × Vec → ℝ} {F : ℝ × Vec → Vec} {g : Vec → ℝ} {t K C : ℝ}
    (he : ContDiffOn ℝ 1 e (Ioi 0 ×ˢ (univ : Set Vec)))
    (hF : ContDiffOn ℝ 1 F (Ioi 0 ×ˢ (univ : Set Vec)))
    (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g) (ht : 0 < t)
    (hg0 : ∀ x, 0 ≤ g x) (hC : 0 ≤ C) (hgb : ∀ x, ‖fderiv ℝ g x‖ ≤ C)
    (heI : Integrable (fun x : Vec => e (t,x)))
    (hflux : ∀ x : Vec, ‖F (t,x)‖ ≤ e (t,x))
    (hineq : ∀ x : Vec, fderiv ℝ e (t,x) (1,0) + divergence (fun y => F (t,y)) x ≤ K*e (t,x)) :
    deriv (fun r => ∫ x : Vec, g x*e (r,x)) t ≤
      K*(∫ x : Vec, g x*e (t,x))+C*(∫ x : Vec, e (t,x)) := by
  have hes : Continuous (fun x : Vec => e (t,x)) := he.continuousOn.comp_continuous
    (continuous_const.prodMk continuous_id) (fun _ => ⟨ht,mem_univ _⟩)
  have hfs : ContDiff ℝ 1 (fun x : Vec => F (t,x)) := by
    apply contDiffOn_univ.mp
    exact hF.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ _ => ⟨ht,mem_univ _⟩)
  have hedc : Continuous (fun x : Vec => fderiv ℝ e (t,x) (1,0)) :=
    ((he.continuousOn_fderiv_of_isOpen (isOpen_Ioi.prod isOpen_univ) le_rfl).comp_continuous
      (continuous_const.prodMk continuous_id) (fun _ => ⟨ht,mem_univ _⟩)).clm_apply continuous_const
  have hi₁ : Integrable (fun x : Vec => g x*fderiv ℝ e (t,x) (1,0)) :=
    (hg.continuous.mul hedc).integrable_of_hasCompactSupport hc.mul_right
  have hi₂ : Integrable (fun x : Vec => g x*e (t,x)) :=
    (hg.continuous.mul hes).integrable_of_hasCompactSupport hc.mul_right
  have hi₃ : Integrable (fun x : Vec => g x*divergence (fun y => F (t,y)) x) :=
    (hg.continuous.mul (continuous_divergence hfs)).integrable_of_hasCompactSupport hc.mul_right
  have hi₄ : Integrable (fun x : Vec => fderiv ℝ g x (F (t,x))) :=
    ((hg.continuous_fderiv (by simp)).clm_apply hfs.continuous).integrable_of_hasCompactSupport
      (compactSupport_of_zero_off (hc.fderiv ℝ) (by
        intro x hx
        rw [image_eq_zero_of_notMem_tsupport hx, zero_apply]))
  rw [(weighted_density_hasDerivAt he hg hc ht).deriv]
  calc
    _ ≤ ∫ x : Vec, K*(g x*e (t,x))-g x*divergence (fun y => F (t,y)) x := by
      apply integral_mono hi₁ ((hi₂.const_mul K).sub hi₃)
      intro x
      change g x * fderiv ℝ e (t,x) (1,0) ≤ K*(g x*e (t,x))-g x*divergence (fun y => F (t,y)) x
      nlinarith [mul_le_mul_of_nonneg_left (hineq x) (hg0 x)]
    _ = K*(∫ x : Vec, g x*e (t,x))+(∫ x : Vec, fderiv ℝ g x (F (t,x))) := by
      rw [integral_sub (hi₂.const_mul K) hi₃, integral_const_mul, integral_mul_divergence hfs hg hc]
      ring
    _ ≤ _ := by
      apply add_le_add_right
      calc
        _ ≤ ∫ x : Vec, C*e (t,x) := by
          apply integral_mono hi₄ (heI.const_mul C)
          intro x
          exact (le_abs_self _).trans ((ContinuousLinearMap.le_opNorm _ _).trans
            (mul_le_mul (hgb x) (hflux x) (norm_nonneg _) hC))
        _ = _ := integral_const_mul _ _

theorem local_energy_inequality_vanishes
    {e : ℝ × Vec → ℝ} {F : ℝ × Vec → Vec} {K T : ℝ}
    (hK : 0 ≤ K) (hT : 0 ≤ T)
    (he : ContDiffOn ℝ 1 e (Ioi 0 ×ˢ (univ : Set Vec)))
    (hF : ContDiffOn ℝ 1 F (Ioi 0 ×ˢ (univ : Set Vec)))
    (hec : ContinuousOn e (Icc 0 T ×ˢ (univ : Set Vec)))
    (he0 : ∀ t ∈ Icc 0 T, ∀ x : Vec, 0 ≤ e (t,x))
    (heI : ∀ t ∈ Icc 0 T, Integrable (fun x : Vec => e (t,x)))
    (hcont : ContinuousOn (fun t => ∫ x : Vec, e (t,x)) (Icc 0 T))
    (hflux : ∀ t ∈ Ioo 0 T, ∀ x : Vec, ‖F (t,x)‖ ≤ e (t,x))
    (hineq : ∀ t ∈ Ioo 0 T, ∀ x : Vec,
      fderiv ℝ e (t,x) (1,0)+divergence (fun y => F (t,y)) x ≤ K*e (t,x))
    (hinit : ∀ x : Vec, e (0,x)=0) :
    ∀ x : Vec, e (T,x)=0 := by
  obtain ⟨C,hC,hCb⟩ := energyCutoff_deriv_bound
  obtain ⟨B,hB⟩ := (isCompact_Icc : IsCompact (Icc (0:ℝ) T)).bddAbove_image hcont
  have hB' : ∀ t ∈ Icc 0 T, (∫ x : Vec, e (t,x)) ≤ B := fun t ht => hB ⟨t,ht,rfl⟩
  have hBn : 0 ≤ B := by
    have ht0 : (0:ℝ) ∈ Icc 0 T := ⟨le_rfl,hT⟩
    exact (integral_nonneg (he0 0 ht0)).trans (hB' 0 ht0)
  have hbound (n : ℕ) : (∫ x : Vec, energyCutoff n x*e (T,x)) ≤
      ((C/((n:ℝ)+1))*B)*T*Real.exp (K*T) := by
    let f : ℝ → ℝ := fun t => ∫ x : Vec, energyCutoff n x*e (t,x)
    have hfc : ContinuousOn f (Icc 0 T) := by
      apply continuousOn_integral_uniform_support (energyCutoff_compact n)
        (((energyCutoff_smooth n).continuous.comp continuous_snd).continuousOn.mul hec)
      intro t _ x hx
      change energyCutoff n x * e (t,x) = 0
      rw [image_eq_zero_of_notMem_tsupport hx,zero_mul]
    apply scalar_gronwall_interior hK (mul_nonneg (div_nonneg hC (by positivity)) hBn) hT hfc
    · simp only [f,hinit,mul_zero,integral_zero]
    · intro t ht
      exact (weighted_density_hasDerivAt he (energyCutoff_smooth n) (energyCutoff_compact n) ht.1).differentiableAt
    · intro t ht
      have hder := weighted_density_deriv_le he hF (energyCutoff_smooth n)
        (energyCutoff_compact n) ht.1 (fun x => (energyCutoff_bounds n x).1)
        (div_nonneg hC (by positivity)) (hCb n) (heI t ⟨ht.1.le,ht.2.le⟩)
        (hflux t ht) (hineq t ht)
      exact hder.trans (add_le_add_right
        (mul_le_mul_of_nonneg_left (hB' t ⟨ht.1.le,ht.2.le⟩) (div_nonneg hC (by positivity))) _)
  have hl := energyCutoff_integral_tendsto (heI T ⟨hT,le_rfl⟩)
  have hr : Tendsto (fun n : ℕ => ((C/((n:ℝ)+1))*B)*T*Real.exp (K*T)) atTop (nhds 0) := by
    have hi : Tendsto (fun n : ℕ => ((n:ℝ)+1)⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
    simpa only [div_eq_mul_inv,mul_zero,zero_mul] using (((hi.const_mul C).mul_const B).mul_const T).mul_const (Real.exp (K*T))
  have hz : (∫ x : Vec, e (T,x))=0 := le_antisymm
    (le_of_tendsto_of_tendsto' hl hr hbound) (integral_nonneg (he0 T ⟨hT,le_rfl⟩))
  have hae := (integral_eq_zero_iff_of_nonneg (he0 T ⟨hT,le_rfl⟩) (heI T ⟨hT,le_rfl⟩)).mp hz
  have hes : Continuous (fun x : Vec => e (T,x)) := hec.comp_continuous
    (continuous_const.prodMk continuous_id) (fun _ => ⟨⟨hT,le_rfl⟩,mem_univ _⟩)
  exact fun x => congrFun (Measure.eq_of_ae_eq (μ := volume) hae hes continuous_const) x

def RegularParticle (f : Particle) : Prop :=
  ContDiffOn ℝ 1 f particleHalfSpace ∧
    CompactOnFiniteHorizons ⟨f,0,0⟩


lemma RegularParticle.local_data {f : Particle} (hf : RegularParticle f)
    {t : ℝ} (ht : 0 < t) (x : Vec) :
    ∃ (U : Set (ℝ × Vec)) (K : Set Vec),
      IsOpen U ∧ IsCompact K ∧ (t,x) ∈ U ∧
      ContDiffOn ℝ 1 (particleBySpacetime f) (U ×ˢ univ) ∧
      ∀ p ∈ U, ∀ v ∉ K, particleBySpacetime f (p,v) = 0 :=
  particle_spacetime_local_data (s := ⟨f,0,0⟩) x hf.1 hf.2 ht

lemma RegularParticle.slice {f : Particle} (hf : RegularParticle f)
    {t : ℝ} (ht : 0 ≤ t) (x : Vec) :
    ContDiff ℝ 1 (fun v : Vec => f (t,x,v)) ∧ HasCompactSupport (fun v : Vec => f (t,x,v)) := by
  constructor
  · apply contDiffOn_univ.mp
    exact hf.1.comp (contDiff_const.prodMk (contDiff_const.prodMk contDiff_id)).contDiffOn
      (fun _ _ => ht)
  · obtain ⟨K,hK,hz⟩ := hf.2 t ht
    apply compactSupport_of_zero_off (hK.image continuous_snd)
    intro v hv
    by_contra hn
    exact hv ⟨(x,v),hz t ⟨ht,le_rfl⟩ (subset_tsupport _ hn),rfl⟩

def particleMoment {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (f : Particle) (w : Vec → W) (p : ℝ × Vec) : W :=
  ∫ v : Vec, f (p.1,p.2,v) • w v

lemma RegularParticle.moment_integrable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {f : Particle} (hf : RegularParticle f) {w : Vec → W} (hw : Continuous w)
    {t : ℝ} (ht : 0 ≤ t) (x : Vec) :
    Integrable (fun v : Vec => f (t,x,v) • w v) := by
  obtain ⟨hs,hc⟩ := hf.slice ht x
  exact (hs.continuous.smul hw).integrable_of_hasCompactSupport hc.smul_right

lemma RegularParticle.moment_regular {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W] {f : Particle} (hf : RegularParticle f)
    {w : Vec → W} (hw : ContDiff ℝ 1 w) :
    ContDiffOn ℝ 1 (particleMoment f w) (Ioi 0 ×ˢ (univ : Set Vec)) := by
  intro p hp
  obtain ⟨U,K,hU,hK,hp',hF,hzero⟩ := hf.local_data hp.1 p.2
  have hs := contDiffOn_integral_uniform_support (n := 1) hU hK
    (hF.smul (hw.comp contDiff_snd).contDiffOn)
    (fun p hp v hv => by
      change particleBySpacetime f (p,v) • w v = 0
      rw [hzero p hp v hv,zero_smul])
  exact (hs.contDiffAt (hU.mem_nhds hp')).contDiffWithinAt

lemma RegularParticle.moment_continuous_slab {W : Type*}
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {f : Particle} (hf : RegularParticle f) {w : Vec → W} (hw : Continuous w)
    {T : ℝ} (hT : 0 ≤ T) :
    ContinuousOn (particleMoment f w) (Icc 0 T ×ˢ (univ : Set Vec)) := by
  obtain ⟨K,hK,hzero⟩ := hf.2 T hT
  change ContinuousOn (fun p : ℝ × Vec => ∫ v : Vec, f (p.1,p.2,v) • w v) _
  apply continuousOn_integral_uniform_support
    (F := fun z : (ℝ × Vec) × Vec => f (z.1.1,z.1.2,z.2) • w z.2) (hK.image continuous_snd)
  · apply ContinuousOn.smul ?_ (hw.comp continuous_snd).continuousOn
    exact hf.1.continuousOn.comp (contDiff_reassociate (k := 1)).continuous.continuousOn
      (fun z hz => hz.1.1.1)
  · intro p hp v hv
    have hz : f (p.1,p.2,v) = 0 := by
      by_contra hn
      exact hv ⟨(p.2,v),hzero p.1 hp.1 (subset_tsupport _ hn),rfl⟩
    simp only [hz,zero_smul]

lemma RegularParticle.moment_compact {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {f : Particle} (hf : RegularParticle f) (w : Vec → W) {T : ℝ} (hT : 0 ≤ T) :
    ∃ K : Set Vec, IsCompact K ∧ ∀ t ∈ Icc 0 T, ∀ x ∉ K, particleMoment f w (t,x) = 0 := by
  obtain ⟨K,hK,hzero⟩ := hf.2 T hT
  refine ⟨Prod.fst '' K,hK.image continuous_fst,?_⟩
  intro t ht x hx
  apply integral_eq_zero_of_ae
  filter_upwards [] with v
  have hz : f (t,x,v) = 0 := by
    by_contra hn
    exact hx ⟨(x,v),hzero t ht (subset_tsupport _ hn),rfl⟩
  simp only [hz,zero_smul,Pi.zero_apply]

lemma RegularParticle.spatial_moment_integrable {W : Type*}
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {f : Particle} (hf : RegularParticle f) {w : Vec → W} (hw : Continuous w)
    {t : ℝ} (ht : 0 ≤ t) : Integrable (fun x : Vec => particleMoment f w (t,x)) := by
  obtain ⟨K,hK,hz⟩ := hf.moment_compact w ht
  have hc := (hf.moment_continuous_slab hw ht).comp_continuous
    (continuous_const.prodMk continuous_id)
    (fun x : Vec => show (t,x) ∈ Icc 0 t ×ˢ (univ : Set Vec) from ⟨⟨ht,le_rfl⟩,mem_univ _⟩)
  exact hc.integrable_of_hasCompactSupport (compactSupport_of_zero_off hK (hz t ⟨ht,le_rfl⟩))

lemma RegularParticle.integrated_moment_continuous {W : Type*}
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {f : Particle} (hf : RegularParticle f) {w : Vec → W} (hw : Continuous w)
    {T : ℝ} (hT : 0 ≤ T) :
    ContinuousOn (fun t => ∫ x : Vec, particleMoment f w (t,x)) (Icc 0 T) := by
  obtain ⟨K,hK,hz⟩ := hf.moment_compact w hT
  exact continuousOn_integral_uniform_support hK (hf.moment_continuous_slab hw hT) hz

lemma RegularParticle.velocity_flux_bound {f : Particle} (hf : RegularParticle f)
    {t : ℝ} (ht : 0 ≤ t) (x : Vec) (hpos : ∀ v, 0 ≤ f (t,x,v)) :
    ‖particleMoment f velocity (t,x)‖ ≤ particleMoment f (fun _ => (1:ℝ)) (t,x) := by
  dsimp [particleMoment]
  simp only [mul_one]
  calc
    _ ≤ ∫ v : Vec, ‖f (t,x,v) • velocity v‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ v : Vec, f (t,x,v) := by
      have hi := hf.moment_integrable (contDiff_velocity (k := 1)).continuous ht x
      have hfI : Integrable (fun v : Vec => f (t,x,v)) :=
        (hf.slice ht x).1.continuous.integrable_of_hasCompactSupport (hf.slice ht x).2
      apply integral_mono hi.norm hfI
      intro v
      change ‖f (t,x,v) • velocity v‖ ≤ f (t,x,v)
      rw [norm_smul,Real.norm_of_nonneg (hpos v)]
      exact mul_le_of_le_one_right (hpos v) (norm_velocity_lt_one v).le

lemma TimeContinuousL2.sub {E F : Field} (hE : TimeContinuousL2 E) (hF : TimeContinuousL2 F) :
    TimeContinuousL2 (E-F) := by
  obtain ⟨E₂,hEc,hEe⟩ := hE
  obtain ⟨F₂,hFc,hFe⟩ := hF
  refine ⟨E₂-F₂,hEc.sub hFc,?_⟩
  intro t ht
  filter_upwards [Lp.coeFn_sub (E₂ t) (F₂ t),hEe t ht,hFe t ht] with x hsub he hf
  exact hsub.trans (by simp only [he,hf,Pi.sub_apply])

lemma uniqueDiffOn_particleHalfSpace : UniqueDiffOn ℝ particleHalfSpace := by
  have he : particleHalfSpace = Ici (0:ℝ) ×ˢ (univ : Set Phase) := by
    ext p; simp [particleHalfSpace]
  rw [he]
  exact (uniqueDiffOn_Ici 0).prod uniqueDiffOn_univ

lemma RegularParticle.velocity_derivative_bound {f : Particle} (hf : RegularParticle f)
    {T : ℝ} (hT : 0 ≤ T) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ t ∈ Ioo 0 T, ∀ x v : Vec,
      ‖fderiv ℝ (fun w => f (t,x,w)) v‖ ≤ L := by
  obtain ⟨K,hK,hz⟩ := hf.2 T hT
  have hfullc := (hf.1.continuousOn_fderivWithin uniqueDiffOn_particleHalfSpace le_rfl).norm
  have hsub : Icc 0 T ×ˢ K ⊆ particleHalfSpace := fun p hp => hp.1.1
  obtain ⟨B,hB⟩ := ((isCompact_Icc : IsCompact (Icc (0:ℝ) T)).prod hK).bddAbove_image
    (hfullc.mono hsub)
  refine ⟨max 0 B,le_max_left _ _,?_⟩
  intro t ht x v
  by_cases hmem : (x,v) ∈ K
  · have hd := particle_differentiableAt_positive (s := ⟨f,0,0⟩) hf.1 ht.1 x v
    have hnhds : particleHalfSpace ∈ nhds (t,x,v) :=
      mem_of_superset ((isOpen_Ioi.preimage (continuous_fst : Continuous (Prod.fst : ℝ × Phase → ℝ))).mem_nhds ht.1)
        (fun p hp => show p.1 ≥ 0 from le_of_lt hp)
    have hb : ‖fderiv ℝ f (t,x,v)‖ ≤ max 0 B := by
      rw [← fderivWithin_of_mem_nhds hnhds]
      exact (hB ⟨(t,x,v),⟨⟨ht.1.le,ht.2.le⟩,hmem⟩,rfl⟩).trans (le_max_right _ _)
    have hinj : HasFDerivAt (fun w : Vec => (t,x,w))
        ((0 : Vec →L[ℝ] ℝ).prod ((0 : Vec →L[ℝ] Vec).prod (ContinuousLinearMap.id ℝ Vec))) v := by
      fun_prop
    have hs := hd.hasFDerivAt.comp v hinj
    apply ContinuousLinearMap.opNorm_le_bound _ (le_max_left 0 B)
    intro w
    have he : fderiv ℝ (fun w => f (t,x,w)) v w = fderiv ℝ f (t,x,v) (0,0,w) := by
      exact congrArg (fun A : Vec →L[ℝ] ℝ => A w) hs.fderiv
    rw [he]
    calc
      _ ≤ ‖fderiv ℝ f (t,x,v)‖ * ‖((0,0,w) : ℝ × Phase)‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ _ := by simpa using mul_le_mul_of_nonneg_right hb (norm_nonneg w)
  · have hzero : (fun w : Vec => f (t,x,w)) =ᶠ[nhds v] (fun _ => 0) := by
      have hn := (hK.isClosed.isOpen_compl.preimage (continuous_const.prodMk continuous_id)).mem_nhds hmem
      filter_upwards [hn] with w hw
      by_contra hne
      exact hw (hz t ⟨ht.1.le,ht.2.le⟩ (subset_tsupport _ hne))
    rw [hzero.fderiv_eq (𝕜 := ℝ)]
    simp

lemma integral_lorentz_derivative_zero {g : Vec → ℝ}
    (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g) (E B : Vec) :
    (∫ v : Vec, fderiv ℝ g v (E + cross (velocity v) B)) = 0 := by
  have h := integral_mul_divergence (contDiff_lorentz E B) hg hc
  simp only [divergence_lorentz,mul_zero,integral_zero] at h
  linarith

lemma particle_number_balance_param
    {U : Set (ℝ × Vec)} {K : Set Vec} {F : (ℝ × Vec) × Vec → ℝ}
    {p : ℝ × Vec} (E B : Vec)
    (hU : IsOpen U) (hK : IsCompact K) (hp : p ∈ U)
    (hF : ContDiffOn ℝ 1 F (U ×ˢ univ))
    (hzero : ∀ x ∈ U, ∀ v ∉ K, F (x,v) = 0) :
    fderiv ℝ (fun y => ∫ v : Vec, F (y,v)) p (1,0) +
      ∑ i : Fin 3, fderiv ℝ (fun y => ∫ v : Vec, velocity v i * F (y,v)) p (0,basis i) =
      ∫ v : Vec, fderiv ℝ F (p,v) ((1,velocity v), E + cross (velocity v) B) := by
  have hdiff (v : Vec) : DifferentiableAt ℝ F (p,v) :=
    (hF.contDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨hp, mem_univ _⟩)).differentiableAt (by simp)
  have hs : ContDiff ℝ 1 (fun v : Vec => F (p,v)) := by
    apply contDiffOn_univ.mp
    exact hF.comp ((contDiff_const.prodMk contDiff_id).contDiffOn)
      (fun v _ => ⟨hp,mem_univ v⟩)
  have hc : HasCompactSupport (fun v : Vec => F (p,v)) :=
    compactSupport_of_zero_off hK (hzero p hp)
  have hvel (i : Fin 3) : ContDiff ℝ 1 (fun v => velocity v i) :=
    (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) i).contDiff.comp contDiff_velocity
  have hint : Integrable (fun v : Vec => fderiv ℝ F (p,v) ((1,0),0)) := by
    simpa only [one_mul] using integrable_param_fderiv_apply_weight hU hK hp hF
      (continuous_const (y := (1:ℝ))) hzero (((1:ℝ),(0:Vec)),(0:Vec))
  have hint' (i : Fin 3) := integrable_param_fderiv_apply_weight hU hK hp hF
    (hvel i).continuous hzero (((0:ℝ),basis i),(0:Vec))
  have hintK : Integrable (fun v : Vec => fderiv ℝ F (p,v) ((0,0),E + cross (velocity v) B)) := by
    have hd : Continuous (fun v : Vec => fderiv ℝ F (p,v)) :=
      (hF.continuousOn_fderiv_of_isOpen (hU.prod isOpen_univ) le_rfl).comp_continuous
        (continuous_const.prodMk continuous_id) (fun _ => ⟨hp,mem_univ _⟩)
    apply (hd.clm_apply (continuous_const.prodMk (contDiff_lorentz (k := 1) E B).continuous)).integrable_of_hasCompactSupport
    apply compactSupport_of_zero_off (compactSupport_param_fderiv hU hK hp hzero)
    intro v hv
    rw [image_eq_zero_of_notMem_tsupport hv,zero_apply]
  have hK0 : (∫ v : Vec, fderiv ℝ F (p,v) ((0,0),E + cross (velocity v) B)) = 0 := by
    simpa only [fderiv_velocity_slice (hdiff _)] using integral_lorentz_derivative_zero hs hc E B
  have he (v : Vec) : fderiv ℝ F (p,v) ((1,velocity v),E + cross (velocity v) B) =
      fderiv ℝ F (p,v) ((1,0),0) +
        (∑ i : Fin 3, velocity v i * fderiv ℝ F (p,v) ((0,basis i),0)) +
        fderiv ℝ F (p,v) ((0,0),E + cross (velocity v) B) := by
    rw [clm_spacetime_velocity_split]
    congr 1
    symm
    have h := clm_spacetime_velocity_split (fderiv ℝ F (p,v)) (0:Vec) (E + cross (velocity v) B)
    have h' : fderiv ℝ F (p,v) ((1,0),E + cross (velocity v) B) =
        fderiv ℝ F (p,v) ((1,0),0) + fderiv ℝ F (p,v) ((0,0),E + cross (velocity v) B) := by
      rw [← map_add]; congr 1; ext <;> simp
    simp only [PiLp.zero_apply,zero_mul,Finset.sum_const_zero,add_zero] at h
    linarith
  rw [fderiv_integral_uniform_support_apply hU hK hp hF hzero]
  simp_rw [fderiv_weighted_integral_uniform_support_apply hU hK hp hF (hvel _) hzero]
  rw [← integral_finsetSum _ (fun i _ => hint' i), ← integral_add hint
    (integrable_finsetSum Finset.univ (fun i _ => hint' i))]
  calc
    _ = (∫ v : Vec, fderiv ℝ F (p,v) ((1,0),0) +
      ∑ i : Fin 3, velocity v i * fderiv ℝ F (p,v) ((0,basis i),0)) +
       (∫ v : Vec, fderiv ℝ F (p,v) ((0,0),E + cross (velocity v) B)) := by rw [hK0,add_zero]
    _ = _ := by
      calc
        _ = ∫ v : Vec, (fderiv ℝ F (p,v) ((1,0),0) +
          ∑ i : Fin 3, velocity v i * fderiv ℝ F (p,v) ((0,basis i),0)) +
            fderiv ℝ F (p,v) ((0,0),E + cross (velocity v) B) :=
          (integral_add (hint.add (integrable_finsetSum Finset.univ (fun i _ => hint' i))) hintK).symm
        _ = _ := by
          apply integral_congr_ae
          filter_upwards [] with v
          exact (he v).symm

lemma fderiv_square_half {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {g : H → ℝ} {p b : H} (hg : DifferentiableAt ℝ g p) :
    fderiv ℝ (fun z => (g z)^2/2) p b = g p * fderiv ℝ g p b := by
  have h := (hg.hasFDerivAt.pow 2).mul_const (2:ℝ)⁻¹
  simp only [div_eq_mul_inv]
  rw [h.fderiv]
  simp only [smul_apply,smul_eq_mul]
  norm_num
  ring

def squareDifference (s₁ s₂ : Solution) : Particle :=
  fun z => (s₁.f z-s₂.f z)^2/2




end RVM

end

end OAI

end

section

namespace OAI

noncomputable section

section
open MeasureTheory Set
open scoped ContDiff
open Filter Set
open scoped Topology
open Set MeasureTheory Filter
open scoped Topology ContDiff

namespace RVM



lemma particleMoment_one (f : Particle) (p : ℝ × Vec) :
    particleMoment f (fun _ => (1:ℝ)) p = ∫ v : Vec, f (p.1,p.2,v) := by
  simp [particleMoment]

lemma RegularParticle.moment_component {f : Particle} (hf : RegularParticle f)
    {w : Vec → Vec} (hw : Continuous w) {t : ℝ} (ht : 0 ≤ t) (x : Vec) (i : Fin 3) :
    particleMoment f w (t,x) i = ∫ v : Vec, w v i * f (t,x,v) := by
  have hi := hf.moment_integrable hw ht x
  have he := (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) i).integral_comp_comm hi
  simpa [particleMoment,mul_comm] using he.symm


lemma curl_sub {F G : Vec → Vec} {x : Vec}
    (hF : DifferentiableAt ℝ F x) (hG : DifferentiableAt ℝ G x) :
    curl (F-G) x = curl F x - curl G x := by
  have h (i : Fin 3) : fderiv ℝ (fun y => F y i-G y i) x =
      fderiv ℝ (fun y => F y i) x - fderiv ℝ (fun y => G y i) x := by
    exact fderiv_sub
      ((PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) i).differentiableAt.comp x hF)
      ((PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) i).differentiableAt.comp x hG)
  ext i
  fin_cases i <;> simp [curl,spatialPartial,h] <;> ring


















end RVM

end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace

namespace RVM














end RVM

end

end OAI

end

section
-- generalized from OpenAI OAI.RVM, openai/math@3344da5

namespace OAI

/-! The multispecies relativistic Vlasov–Maxwell system on three-dimensional Euclidean space. -/

noncomputable section
open MeasureTheory Set
open scoped ContDiff

namespace RVMS

abbrev Vec := EuclideanSpace ℝ (Fin 3)
abbrev Phase := Vec × Vec
abbrev Particle := ℝ × Phase → ℝ
abbrev Field := ℝ × Vec → Vec

def q (v : Vec) : ℝ := Real.sqrt (1 + ‖v‖ ^ 2)
def velocity (v : Vec) : Vec := (q v)⁻¹ • v

def basis (i : Fin 3) : Vec := WithLp.toLp 2 (Pi.single i (1 : ℝ))
def dot (a b : Vec) : ℝ := ∑ i : Fin 3, a i * b i
def cross (a b : Vec) : Vec := WithLp.toLp 2
  ![a 1 * b 2 - a 2 * b 1, a 2 * b 0 - a 0 * b 2,
    a 0 * b 1 - a 1 * b 0]

def spatialPartial (g : Vec → ℝ) (x : Vec) (i : Fin 3) : ℝ :=
  fderiv ℝ g x (basis i)
def divergence (F : Vec → Vec) (x : Vec) : ℝ :=
  ∑ i : Fin 3, spatialPartial (fun y => F y i) x i

def curl (F : Vec → Vec) (x : Vec) : Vec := WithLp.toLp 2
  ![spatialPartial (fun y => F y 2) x 1 - spatialPartial (fun y => F y 1) x 2,
    spatialPartial (fun y => F y 0) x 2 - spatialPartial (fun y => F y 2) x 0,
    spatialPartial (fun y => F y 1) x 0 - spatialPartial (fun y => F y 0) x 1]

structure Species (ι : Type) [Fintype ι] where
  kappa : ι → ℝ
  weight : ι → ℝ
  kappa_ne : ∀ a, kappa a ≠ 0
  weight_ne : ∀ a, weight a ≠ 0
  ratio_pos : ∀ a, 0 < weight a / kappa a

variable {ι : Type} [Fintype ι]

def rho (σ : Species ι) (g : ι → Phase → ℝ) (x : Vec) : ℝ :=
  ∑ a, σ.weight a * ∫ v : Vec, g a (x, v)
def current (σ : Species ι) (g : ι → Phase → ℝ) (x : Vec) : Vec :=
  ∑ a, σ.weight a • ∫ v : Vec, g a (x, v) • velocity v

structure Datum (ι : Type) where
  f₀ : ι → Phase → ℝ
  E₀ : Vec → Vec
  B₀ : Vec → Vec



structure Solution (ι : Type) where
  f : ι → Particle
  E : Field
  B : Field

def particleHalfSpace : Set (ℝ × Phase) := {z | 0 ≤ z.1}
def fieldHalfSpace : Set (ℝ × Vec) := {z | 0 ≤ z.1}



def CompactOnFiniteHorizons (s : Solution ι) : Prop :=
  ∀ T : ℝ, 0 ≤ T → ∃ K : Set Phase, IsCompact K ∧
    ∀ a, ∀ t ∈ Icc 0 T, tsupport (fun z => s.f a (t, z)) ⊆ K




end RVMS
end

end OAI

end

section

namespace OAI

noncomputable section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff ENNReal
open Set
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

section PositiveExtension
variable {H W : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

def positiveTimeCut (a t : ℝ) : ℝ := Real.smoothTransition ((t-a/4)/(a/4))


lemma contDiff_positiveTimeCut (a : ℝ) : ContDiff ℝ ∞ (positiveTimeCut a) :=
  Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const (a/4))
lemma positiveTimeCut_zero {a t : ℝ} (ha : 0<a) (ht : t≤a/4) : positiveTimeCut a t=0 :=
  Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) (by positivity))
lemma positiveTimeCut_one {a t : ℝ} (ha : 0<a) (ht : a/2≤t) : positiveTimeCut a t=1 := by
  apply Real.smoothTransition.one_of_one_le
  apply (le_div_iff₀ (by positivity : 0<a/4)).mpr
  linarith






end PositiveExtension








end RVM

end

end OAI

end

section

namespace OAI

noncomputable section

namespace RVM

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set MeasureTheory
open Set MeasureTheory Filter
open scoped Topology ContDiff
open Set MeasureTheory Metric Filter ODE
open scoped Topology NNReal ContDiff

section WithinFlow
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]






omit [NormedSpace ℝ E] in



variable [FiniteDimensional ℝ E]







end WithinFlow


lemma cross_smul_right (a b : Vec) (c : ℝ) : cross a (c • b) = c • cross a b := by
  ext i
  fin_cases i <;> simp [cross] <;> ring





open Set MeasureTheory Filter Metric ODE

section SlabUniqueness
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

end SlabUniqueness





open Set MeasureTheory Filter Metric

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]




omit [FiniteDimensional ℝ E] in




end












section HaarFlow
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]


end HaarFlow






open Set Filter Metric MeasureTheory















end RVM

end

end OAI

end

section

namespace OAI

noncomputable section

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set
open Set MeasureTheory
open scoped ENNReal
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff
open scoped Topology ContDiff NNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace

namespace RVM

def upperTimeCut (τ H t : ℝ) : ℝ := positiveTimeCut (2*(H-τ)) (H-t)

lemma contDiff_upperTimeCut (τ H : ℝ) : ContDiff ℝ ∞ (upperTimeCut τ H) :=
  (contDiff_positiveTimeCut _).comp (contDiff_const.sub contDiff_id)


lemma upperTimeCut_one {τ H t : ℝ} (hτ : τ < H) (ht : t ≤ τ) :
    upperTimeCut τ H t = 1 := by
  apply positiveTimeCut_one (by linarith)
  linarith

lemma upperTimeCut_zero {τ H t : ℝ} (hτ : τ < H) (ht : (τ+H)/2 ≤ t) :
    upperTimeCut τ H t = 0 := by
  apply positiveTimeCut_zero (by linarith)
  linarith

section Generic
variable {X W : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

def upperTimeExtend (τ H : ℝ) (F : ℝ × X → W) (p : ℝ × X) : W :=
  upperTimeCut τ H p.1 • F p

omit [NormedAddCommGroup X] [NormedSpace ℝ X] in
lemma upperTimeExtend_eq {τ H t : ℝ} (hτ : τ < H) (ht : t ≤ τ)
    (F : ℝ × X → W) (x : X) : upperTimeExtend τ H F (t,x)=F (t,x) := by
  simp only [upperTimeExtend,upperTimeCut_one hτ ht,one_smul]


omit [NormedSpace ℝ X] in
lemma upperTimeExtend_eventually_zero {τ H : ℝ} (hτ : τ < H)
    (F : ℝ × X → W) {p : ℝ × X} (hp : (τ+H)/2 < p.1) :
    upperTimeExtend τ H F =ᶠ[𝓝 p] (fun _ => 0) := by
  filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds hp] with q hq
  simp only [upperTimeExtend,upperTimeCut_zero hτ hq.le,zero_smul]


omit [NormedAddCommGroup X] [NormedSpace ℝ X] in
lemma derivWithin_upperTimeExtend {τ H t : ℝ} (hτ : τ < H) (ht : t < τ)
    (F : ℝ × X → W) (x : X) (S : Set ℝ) :
    derivWithin (fun r => upperTimeExtend τ H F (r,x)) S t =
      derivWithin (fun r => F (r,x)) S t := by
  have he : (fun r => upperTimeExtend τ H F (r,x)) =ᶠ[𝓝 t] (fun r => F (r,x)) := by
    filter_upwards [Iio_mem_nhds ht] with r hr
    exact upperTimeExtend_eq hτ hr.le F x
  exact he.filter_mono nhdsWithin_le_nhds |>.derivWithin_eq (upperTimeExtend_eq hτ ht.le F x)
end Generic

lemma timeContinuousL2_upperTimeExtend {τ H : ℝ} (hτ : τ < H) (hH : 0 ≤ H)
    {F : Field} (hF : ∃ F₂ : ℝ → Lp Vec 2 (volume : Measure Vec),
      ContinuousOn F₂ (Icc 0 H) ∧ ∀ t ∈ Icc 0 H,
        (F₂ t : Vec → Vec) =ᵐ[volume] (fun x => F (t,x))) :
    TimeContinuousL2 (upperTimeExtend τ H F) := by
  obtain ⟨F₂,hc,he⟩ := hF
  refine ⟨fun t => upperTimeCut τ H t • F₂ (min t H),?_,?_⟩
  · exact (contDiff_upperTimeCut τ H).continuous.continuousOn.smul
      (hc.comp (continuous_id.min continuous_const).continuousOn
        (fun t ht => ⟨le_min ht hH,min_le_right _ _⟩))
  · intro t ht
    have hl := Lp.coeFn_smul (upperTimeCut τ H t) (F₂ (min t H))
    by_cases htH : t ≤ H
    · rw [min_eq_left htH] at hl
      filter_upwards [hl,he t ⟨ht,htH⟩] with x hx hx'
      simpa only [min_eq_left htH,upperTimeExtend,Pi.smul_apply,hx'] using hx
    · have hz := upperTimeCut_zero hτ (show (τ+H)/2 ≤ t by linarith)
      filter_upwards [hl] with x hx
      simpa only [hz,upperTimeExtend,zero_smul,Pi.zero_apply,Pi.smul_apply] using hx







end RVM

end

end OAI

end

section
-- generalized from OpenAI OAI.RVM, openai/math@3344da5

namespace OAI.RVMS
noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff
variable {ι : Type} [Fintype ι]

/-- A density and the common fields. This slice need not solve single-species Maxwell. -/
def sourceSlice (s : Solution ι) (b : ι) : RVM.Solution := ⟨s.f b,s.E,s.B⟩

omit [Fintype ι] in
lemma sourceSlice_compact {s : Solution ι} (hc : CompactOnFiniteHorizons s) (b : ι) :
    RVM.CompactOnFiniteHorizons (sourceSlice s b) := by
  intro T ht
  obtain ⟨K,hK,h⟩ := hc T ht
  exact ⟨K,hK,h b⟩



end
end OAI.RVMS

end

section
-- generalized from OpenAI OAI.RVM, openai/math@3344da5
namespace OAI.RVMS
noncomputable section
open Set MeasureTheory
variable {ι : Type} [Fintype ι] {σ : Species ι} {s : Solution ι} {d : Datum ι}
/-- Kernel adapter only: these scaled fields need not solve Maxwell for this density. -/
def kernelSlice (σ : Species ι) (s : Solution ι) (b : ι) : RVM.Solution :=
  ⟨s.f b, fun p => σ.kappa b • s.E p, fun p => σ.kappa b • s.B p⟩
end
end OAI.RVMS

end

section
-- generalized from OpenAI OAI.RVM, openai/math@3344da5
namespace OAI.RVMS.MomentDivision
open OAI.RVM
noncomputable section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set
open Set MeasureTheory
open scoped ENNReal
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff
open scoped Topology ContDiff NNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace





def VB (s : RVM.Solution) (H : ℝ) : Prop :=
  ContDiffOn ℝ 1 s.f RVM.particleHalfSpace ∧ ContDiffOn ℝ 1 s.E RVM.fieldHalfSpace ∧
  ContDiffOn ℝ 1 s.B RVM.fieldHalfSpace ∧ True ∧ True ∧ True ∧ RVM.CompactOnFiniteHorizons s ∧
  (∀ {r : ℝ}, 0 < r → r < H → ∀ x v : RVM.Vec,
    fderiv ℝ s.f (r,x,v) (1, RVM.velocity v, s.E (r,x) + RVM.cross (RVM.velocity v) (s.B (r,x))) = 0) ∧ True


lemma VB.regularParticle {s : RVM.Solution} {H : ℝ}
    (hs : VB s H) : RegularParticle s.f := ⟨hs.1,hs.2.2.2.2.2.2.1⟩





end
end OAI.RVMS.MomentDivision

namespace OAI.RVMS
noncomputable section
variable {ι : Type} [Fintype ι] {σ : Species ι} {s : Solution ι}
end
end OAI.RVMS

end

section
-- generalized from OpenAI OAI.RVM, openai/math@3344da5
namespace OAI.RVMS
noncomputable section
open MeasureTheory Set
open scoped ContDiff
variable {ι : Type} [Fintype ι]
def EquationsBefore (σ : Species ι) (s : Solution ι) (H : ℝ) : Prop := ∀ t, 0 ≤ t → t < H →
  (∀ a x v,
    derivWithin (fun t' => s.f a (t', x, v)) (Ici 0) t +
    (∑ i : Fin 3, velocity v i * spatialPartial (fun y => s.f a (t, y, v)) x i) +
    (∑ i : Fin 3, (σ.kappa a • (s.E (t, x) + cross (velocity v) (s.B (t, x)))) i *
      spatialPartial (fun v' => s.f a (t, x, v')) v i) = 0) ∧
  (∀ x, derivWithin (fun t' => s.E (t', x)) (Ici 0) t -
    curl (fun y => s.B (t, y)) x = -current σ (fun a z => s.f a (t, z)) x) ∧
  (∀ x, derivWithin (fun t' => s.B (t', x)) (Ici 0) t +
    curl (fun y => s.E (t, y)) x = 0) ∧
  (∀ x, divergence (fun y => s.E (t, y)) x = rho σ (fun a z => s.f a (t, z)) x) ∧
  (∀ x, divergence (fun y => s.B (t, y)) x = 0)






end
end OAI.RVMS

end

section
-- generalized from OpenAI OAI.RVM, openai/math@3344da5
namespace OAI.RVMS
noncomputable section
open Set MeasureTheory Metric Filter
open scoped Topology
open scoped ContDiff
variable {ι : Type} [Fintype ι] {σ : Species ι} {s : Solution ι} {d : Datum ι} {H : ℝ}

/-- Classical regularity on the half-space, with the equations required only before `H`. -/
structure ClassicalUpTo (σ : Species ι) (s : Solution ι) (H : ℝ) : Prop where
  f1 : ∀ b, ContDiffOn ℝ 1 (s.f b) particleHalfSpace
  E1 : ContDiffOn ℝ 1 s.E fieldHalfSpace
  B1 : ContDiffOn ℝ 1 s.B fieldHalfSpace
  compact : CompactOnFiniteHorizons s
  eq : EquationsBefore σ s H

lemma kernelSlice_VB_before (hs : ClassicalUpTo σ s H) (b : ι) :
    MomentDivision.VB (kernelSlice σ s b) H := by
  refine ⟨hs.f1 b, (contDiffOn_const (c:=σ.kappa b)).smul hs.E1,
    (contDiffOn_const (c:=σ.kappa b)).smul hs.B1, trivial, trivial,
    trivial, sourceSlice_compact hs.compact b, ?_, trivial⟩
  intro r hr hrH z v
  simp only [kernelSlice, RVM.cross_smul_right, ← smul_add]
  have hd : DifferentiableAt ℝ (s.f b) (r,z,v) :=
    RVM.particle_differentiableAt_positive (s:=sourceSlice s b) (hs.f1 b) hr z v
  rw [RVM.full_directional_derivative hd]
  have h := (hs.eq r hr.le hrH).1 b z v
  rwa [derivWithin_of_mem_nhds (Ici_mem_nhds hr)] at h
















/-- Multispecies upper time cutoff of a prefix (generalizes OpenAI `cutoffPrefix`). -/
def msCutoff (τ H : ℝ) (s : Solution ι) : Solution ι :=
  ⟨fun b => RVM.upperTimeExtend τ H (s.f b), RVM.upperTimeExtend τ H s.E, RVM.upperTimeExtend τ H s.B⟩

omit [Fintype ι] in
lemma msCutoff_eq {τ t : ℝ} (hτH : τ < H) (ht : t ≤ τ) (s : Solution ι) :
    (∀ b z, (msCutoff τ H s).f b (t,z)=s.f b (t,z)) ∧
    (∀ x, (msCutoff τ H s).E (t,x)=s.E (t,x)) ∧
    (∀ x, (msCutoff τ H s).B (t,x)=s.B (t,x)) :=
  ⟨fun b => RVM.upperTimeExtend_eq hτH ht (s.f b), RVM.upperTimeExtend_eq hτH ht s.E,
    RVM.upperTimeExtend_eq hτH ht s.B⟩


lemma msCutoff_equations {τ : ℝ} (hτH : τ < H) (hs : EquationsBefore σ s H) :
    EquationsBefore σ (msCutoff τ H s) τ := by
  intro t ht htτ
  have hh := hs t ht (htτ.trans hτH)
  have hf (b : ι) (x v : Vec) := RVM.derivWithin_upperTimeExtend hτH htτ (s.f b) (x,v) (Ici 0)
  have hE (x : Vec) := RVM.derivWithin_upperTimeExtend hτH htτ s.E x (Ici 0)
  have hB (x : Vec) := RVM.derivWithin_upperTimeExtend hτH htτ s.B x (Ici 0)
  simp only [msCutoff]
  simp only [hf,hE,hB]
  simpa only [RVM.upperTimeExtend,RVM.upperTimeCut_one hτH htτ.le,one_smul] using hh




end
end OAI.RVMS

end

section
-- generalized from OpenAI OAI.RVM, openai/math@3344da5
namespace OAI.RVM
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology RealInnerProductSpace
lemma particle_difference_direction_before_msVB {H : ℝ} {s₁ s₂ : Solution}
    (hs₁ : RVMS.MomentDivision.VB s₁ H) (hs₂ : RVMS.MomentDivision.VB s₂ H) {t : ℝ} (ht : 0 < t) (hth : t < H) (x v : Vec) :
    fderiv ℝ (particleBySpacetime (squareDifference s₁ s₂)) ((t,x),v)
      ((1,velocity v),s₁.E (t,x)+cross (velocity v) (s₁.B (t,x))) =
      -(s₁.f (t,x,v)-s₂.f (t,x,v)) *
        fderiv ℝ (fun w => s₂.f (t,x,w)) v
          ((s₁.E (t,x)-s₂.E (t,x))+cross (velocity v) (s₁.B (t,x)-s₂.B (t,x))) := by
  have hd₁ := particle_differentiableAt_positive hs₁.1 ht x v
  have hd₂ := particle_differentiableAt_positive hs₂.1 ht x v
  have hsp₁ : DifferentiableAt ℝ (particleBySpacetime s₁.f) ((t,x),v) :=
    (hd₁.comp ((t,x),v) ((contDiff_reassociate (k := 1)).differentiable (by simp) _))
  have hsp₂ : DifferentiableAt ℝ (particleBySpacetime s₂.f) ((t,x),v) :=
    (hd₂.comp ((t,x),v) ((contDiff_reassociate (k := 1)).differentiable (by simp) _))
  have he₁ := hs₁.2.2.2.2.2.2.2.1 ht hth x v
  rw [← fderiv_particleBySpacetime hd₁] at he₁
  have he₂ := hs₂.2.2.2.2.2.2.2.1 ht hth x v
  rw [← fderiv_particleBySpacetime hd₂] at he₂
  change fderiv ℝ (fun z => ((particleBySpacetime s₁.f-particleBySpacetime s₂.f) z)^2/2)
     ((t,x),v) _ = _
  rw [fderiv_square_half (hsp₁.sub hsp₂), fderiv_sub hsp₁ hsp₂]
  simp only [sub_apply,Pi.sub_apply,he₁,zero_sub]
  have hcross : cross (velocity v) (s₁.B (t,x)-s₂.B (t,x)) =
      cross (velocity v) (s₁.B (t,x))-cross (velocity v) (s₂.B (t,x)) := by
    ext i; fin_cases i <;> simp [cross] <;> ring
  rw [hcross]
  have hh : (((1:ℝ),velocity v),s₁.E (t,x)+cross (velocity v) (s₁.B (t,x))) =
      ((1,velocity v),s₂.E (t,x)+cross (velocity v) (s₂.B (t,x))) +
        ((0,0),(s₁.E (t,x)-s₂.E (t,x))+(cross (velocity v) (s₁.B (t,x))-cross (velocity v) (s₂.B (t,x)))) := by
    apply Prod.ext
    · simp
    · dsimp
      abel
  rw [hh,map_add,he₂,zero_add]
  have hv := fderiv_velocity_slice hsp₂
  change ∀ b, fderiv ℝ (fun v => s₂.f (t,x,v)) v b =
    fderiv ℝ (particleBySpacetime s₂.f) ((t,x),v) ((0,0),b) at hv
  rw [← hv]
  simp only [particleBySpacetime]
  ring

lemma squareDifference_regular_before_msVB {H : ℝ} {s₁ s₂ : Solution}
    (h₁ : RVMS.MomentDivision.VB s₁ H) (h₂ : RVMS.MomentDivision.VB s₂ H) :
    RegularParticle (squareDifference s₁ s₂) := by
  refine ⟨((h₁.1.sub h₂.1).pow 2).div_const 2,?_⟩
  intro T hT
  obtain ⟨K₁,hK₁,hz₁⟩ := h₁.regularParticle.2 T hT
  obtain ⟨K₂,hK₂,hz₂⟩ := h₂.regularParticle.2 T hT
  refine ⟨K₁ ∪ K₂,hK₁.union hK₂,?_⟩
  intro t ht
  apply closure_minimal ?_ (hK₁.union hK₂).isClosed
  intro z hz
  by_contra hn
  have hf₁ : s₁.f (t,z)=0 := image_eq_zero_of_notMem_tsupport (f := fun z => s₁.f (t,z))
    (fun hh => hn (Or.inl (hz₁ t ht hh)))
  have hf₂ : s₂.f (t,z)=0 := image_eq_zero_of_notMem_tsupport (f := fun z => s₂.f (t,z))
    (fun hh => hn (Or.inr (hz₂ t ht hh)))
  exact hz (by simp [squareDifference,hf₁,hf₂])

lemma particle_difference_local_before_msVB {H : ℝ} {s₁ s₂ : Solution}
    (h₁ : RVMS.MomentDivision.VB s₁ H) (h₂ : RVMS.MomentDivision.VB s₂ H) {t : ℝ} (ht : 0 < t) (hth : t < H) (x : Vec) :
    deriv (fun r => particleMoment (squareDifference s₁ s₂) (fun _ => (1:ℝ)) (r,x)) t +
      divergence (fun y => particleMoment (squareDifference s₁ s₂) velocity (t,y)) x =
      ∫ v : Vec, -(s₁.f (t,x,v)-s₂.f (t,x,v)) *
        fderiv ℝ (fun w => s₂.f (t,x,w)) v
          ((s₁.E (t,x)-s₂.E (t,x))+cross (velocity v) (s₁.B (t,x)-s₂.B (t,x))) := by
  have hf := squareDifference_regular_before_msVB h₁ h₂
  obtain ⟨U,K,hU,hK,hp,hF,hz⟩ := hf.local_data ht x
  have he := particle_number_balance_param (s₁.E (t,x)) (s₁.B (t,x)) hU hK hp hF hz
  have he' : (∫ v : Vec, fderiv ℝ (particleBySpacetime (squareDifference s₁ s₂)) ((t,x),v)
      ((1,velocity v),s₁.E (t,x)+cross (velocity v) (s₁.B (t,x)))) = _ :=
    integral_congr_ae (Filter.Eventually.of_forall (particle_difference_direction_before_msVB h₁ h₂ ht hth x))
  rw [he'] at he
  have hn := (hf.moment_regular (w := fun _ => (1:ℝ)) contDiff_const).contDiffAt (x := (t,x))
    ((isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨ht,mem_univ _⟩)
  rw [deriv_time_slice (hn.differentiableAt (by simp))]
  apply Eq.trans ?_ he
  congr 1
  · congr 2
    ext p
    exact particleMoment_one _ p
  · apply Finset.sum_congr rfl
    intro i _
    have hflux := (hf.moment_regular contDiff_velocity).contDiffAt (x := (t,x))
      ((isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨ht,mem_univ _⟩)
    have hc : DifferentiableAt ℝ (fun p => particleMoment (squareDifference s₁ s₂) velocity p i) (t,x) :=
      (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) i).differentiableAt.comp (t,x)
        (hflux.differentiableAt (by simp))
    rw [spatialPartial_time_slice hc]
    have heq : (fun p : ℝ × Vec => particleMoment (squareDifference s₁ s₂) velocity p i) =ᶠ[nhds (t,x)]
        (fun p => ∫ v : Vec, velocity v i * particleBySpacetime (squareDifference s₁ s₂) (p,v)) := by
      filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds ht] with p hp
      exact hf.moment_component (contDiff_velocity (k := 1)).continuous hp.le p.2 i
    rw [heq.fderiv_eq (𝕜 := ℝ)]

end
end OAI.RVM
namespace OAI.RVMS
noncomputable section
lemma ms_difference_maxwell_local_before {ι : Type} [Fintype ι] {σ : Species ι} {H : ℝ} {s₁ s₂ : Solution ι}
    (h₁ : ClassicalUpTo σ s₁ H) (h₂ : ClassicalUpTo σ s₂ H) {t : ℝ} (ht : 0 < t) (hth : t < H) (x : Vec) :
    deriv (fun r => (‖s₁.E (r,x)-s₂.E (r,x)‖^2+‖s₁.B (r,x)-s₂.B (r,x)‖^2)/2) t +
      divergence (fun y => cross (s₁.E (t,y)-s₂.E (t,y)) (s₁.B (t,y)-s₂.B (t,y))) x =
        -dot (s₁.E (t,x)-s₂.E (t,x))
          (current σ (fun b z => s₁.f b (t,z)) x-current σ (fun b z => s₂.f b (t,z)) x) := by
  have hE₁ := RVM.field_differentiableAt_positive h₁.E1 ht x
  have hB₁ := RVM.field_differentiableAt_positive h₁.B1 ht x
  have hE₂ := RVM.field_differentiableAt_positive h₂.E1 ht x
  have hB₂ := RVM.field_differentiableAt_positive h₂.B1 ht x
  have hE₁t : DifferentiableAt ℝ (fun r : ℝ => s₁.E (r,x)) t := hE₁.comp t (differentiableAt_id.prodMk (differentiableAt_const x))
  have hB₁t : DifferentiableAt ℝ (fun r : ℝ => s₁.B (r,x)) t := hB₁.comp t (differentiableAt_id.prodMk (differentiableAt_const x))
  have hE₂t : DifferentiableAt ℝ (fun r : ℝ => s₂.E (r,x)) t := hE₂.comp t (differentiableAt_id.prodMk (differentiableAt_const x))
  have hB₂t : DifferentiableAt ℝ (fun r : ℝ => s₂.B (r,x)) t := hB₂.comp t (differentiableAt_id.prodMk (differentiableAt_const x))
  have hE₁x : DifferentiableAt ℝ (fun y : Vec => s₁.E (t,y)) x := hE₁.comp x ((differentiableAt_const t).prodMk differentiableAt_id)
  have hB₁x : DifferentiableAt ℝ (fun y : Vec => s₁.B (t,y)) x := hB₁.comp x ((differentiableAt_const t).prodMk differentiableAt_id)
  have hE₂x : DifferentiableAt ℝ (fun y : Vec => s₂.E (t,y)) x := hE₂.comp x ((differentiableAt_const t).prodMk differentiableAt_id)
  have hB₂x : DifferentiableAt ℝ (fun y : Vec => s₂.B (t,y)) x := hB₂.comp x ((differentiableAt_const t).prodMk differentiableAt_id)
  have he₁ := (h₁.eq t ht.le hth).2.1 x
  have hb₁ := (h₁.eq t ht.le hth).2.2.1 x
  have he₂ := (h₂.eq t ht.le hth).2.1 x
  have hb₂ := (h₂.eq t ht.le hth).2.2.1 x
  rw [derivWithin_of_mem_nhds (Ici_mem_nhds ht)] at he₁ hb₁ he₂ hb₂
  apply RVM.maxwell_energy_balance (E := s₁.E-s₂.E) (B := s₁.B-s₂.B) (hE₁.sub hE₂) (hB₁.sub hB₂)
  · change deriv ((fun r => s₁.E (r,x))-(fun r => s₂.E (r,x))) t -
      RVM.curl ((fun y => s₁.B (t,y))-(fun y => s₂.B (t,y))) x = _
    rw [deriv_sub hE₁t hE₂t,RVM.curl_sub hB₁x hB₂x]
    calc
      _ = (deriv (fun r => s₁.E (r,x)) t-curl (fun y => s₁.B (t,y)) x)-
        (deriv (fun r => s₂.E (r,x)) t-curl (fun y => s₂.B (t,y)) x) := by abel
      _ = _ := by rw [he₁,he₂]; abel
  · change deriv ((fun r => s₁.B (r,x))-(fun r => s₂.B (r,x))) t +
      RVM.curl ((fun y => s₁.E (t,y))-(fun y => s₂.E (t,y))) x = _
    rw [deriv_sub hB₁t hB₂t,RVM.curl_sub hE₁x hE₂x]
    calc
      _ = (deriv (fun r => s₁.B (r,x)) t+curl (fun y => s₁.E (t,y)) x)-
        (deriv (fun r => s₂.B (r,x)) t+curl (fun y => s₂.E (t,y)) x) := by abel
      _ = _ := by rw [hb₁,hb₂]; simp

end
end OAI.RVMS

end

section
-- generalized from OpenAI OAI.RVM, openai/math@3344da5
namespace OAI.RVM
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology RealInnerProductSpace
lemma signed_difference_source_pointwise (k w : ℝ) {g L : ℝ} {D : Vec →L[ℝ] ℝ} {E B : Vec}
    (hL : 0 ≤ L) (hD : ‖D‖ ≤ L) (v : Vec) :
    -k*(g*D (E+cross (velocity v) B))-w*dot E (g • velocity v) ≤
      (2*(|k| *L+|w|))*(g^2/2+(‖E‖^2+‖B‖^2)/2) := by
  have hu := (norm_velocity_lt_one v).le
  have hK : ‖E+cross (velocity v) B‖ ≤ ‖E‖+‖B‖ :=
    (norm_add_le _ _).trans (add_le_add le_rfl
      ((norm_cross_le _ _).trans (mul_le_of_le_one_left (norm_nonneg B) hu)))
  have hd : |D (E+cross (velocity v) B)| ≤ L*(‖E‖+‖B‖) :=
    (D.le_opNorm _).trans (mul_le_mul hD hK (norm_nonneg _) hL)
  have hdot : |dot E (g • velocity v)| ≤ ‖E‖*|g| := by
    rw [dot_eq_inner]
    apply (abs_real_inner_le_norm _ _).trans
    rw [norm_smul,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_right (abs_nonneg g) hu) (norm_nonneg E)
  have hab : |g| *(‖E‖+‖B‖) ≤ g^2+(‖E‖^2+‖B‖^2)/2 := by
    nlinarith [sq_nonneg (|g|-‖E‖),sq_nonneg (|g|-‖B‖),sq_abs g]
  calc
    _ ≤ |k| *(|g| *|D (E+cross (velocity v) B)|)+|w| *|dot E (g • velocity v)| := by
      have h := neg_le_abs (k*(g*D (E+cross (velocity v) B)))
      have h' := neg_le_abs (w*dot E (g • velocity v))
      simp only [abs_mul] at h h'; linarith
    _ ≤ |k| *(|g| *(L*(‖E‖+‖B‖)))+|w| *(‖E‖*|g|) := by gcongr
    _ ≤ (|k| *L+|w|)*(|g| *(‖E‖+‖B‖)) := by
      nlinarith [mul_nonneg (mul_nonneg (abs_nonneg w) (abs_nonneg g)) (norm_nonneg B)]
    _ ≤ (|k| *L+|w|)*(g^2+(‖E‖^2+‖B‖^2)/2) := by gcongr
    _ ≤ _ := by nlinarith [mul_nonneg (show 0 ≤ |k| *L+|w| by positivity) (add_nonneg (sq_nonneg ‖E‖) (sq_nonneg ‖B‖))]

lemma compact_signed_difference_source_bound
    (k w : ℝ) {g : Vec → ℝ} {D : Vec → (Vec →L[ℝ] ℝ)} {K : Set Vec} {L : ℝ} (E B : Vec)
    (hg : Continuous g) (hD : Continuous D) (hK : IsCompact K)
    (hz : ∀ v ∉ K, g v=0) (hL : 0 ≤ L) (hDb : ∀ v, ‖D v‖ ≤ L) :
    (∫ v : Vec, -k*(g v * D v (E+cross (velocity v) B))-w*dot E (g v • velocity v)) ≤
      ((2*(|k| *L+|w|))*(1+(volume K).toReal))*
        ((‖E‖^2+‖B‖^2)/2+(∫ v : Vec, (g v)^2/2)) := by
  let c : ℝ := (‖E‖^2+‖B‖^2)/2
  have hc : 0 ≤ c := div_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (by norm_num)
  have hgI : Integrable (fun v : Vec => (g v)^2/2) :=
    ((hg.pow 2).div_const 2).integrable_of_hasCompactSupport (by
      apply compactSupport_of_zero_off hK
      intro v hv
      simp [hz v hv])
  have hsC : Continuous (fun v : Vec => -k*(g v * D v (E+cross (velocity v) B))-w*dot E (g v • velocity v)) := by
    apply Continuous.sub (continuous_const.mul (hg.mul (hD.clm_apply (contDiff_lorentz (k := 1) E B).continuous)))
    simp_rw [dot_eq_inner]
    exact continuous_const.mul (continuous_const.inner (hg.smul (contDiff_velocity (k := 1)).continuous))
  have hs0 : ∀ v ∉ K, -k*(g v * D v (E+cross (velocity v) B))-w*dot E (g v • velocity v) = 0 := by
    intro v hv
    simp [hz v hv,dot]
  have hsI : Integrable (fun v : Vec => -k*(g v * D v (E+cross (velocity v) B))-w*dot E (g v • velocity v)) := hsC.integrable_of_hasCompactSupport (compactSupport_of_zero_off hK hs0)
  have hcI : IntegrableOn (fun _ : Vec => c) K volume :=
    integrableOn_const hK.measure_lt_top.ne
  have hm : (∫ v : Vec, (g v)^2/2) ≥ 0 := integral_nonneg (fun v => by positivity)
  calc
    _ = ∫ v in K, -k*(g v * D v (E+cross (velocity v) B))-w*dot E (g v • velocity v) :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero hs0).symm
    _ ≤ ∫ v in K, (2*(|k| *L+|w|))*((g v)^2/2+c) := by
      apply integral_mono hsI.integrableOn ((hgI.integrableOn.add hcI).const_mul _)
      intro v
      exact signed_difference_source_pointwise k w hL (hDb v) v
    _ = (2*(|k| *L+|w|))*((∫ v : Vec, (g v)^2/2)+(volume K).toReal*c) := by
      rw [integral_const_mul,integral_add hgI.integrableOn hcI,
        setIntegral_eq_integral_of_forall_compl_eq_zero (fun v hv => by simp [hz v hv]),
        integral_const]
      simp [measureReal_def]
    _ ≤ _ := by
      have hv := ENNReal.toReal_nonneg (a := volume K)
      dsimp [c] at *
      nlinarith [mul_nonneg hv hm,mul_nonneg (by positivity : 0 ≤ 2*(|k| *L+|w|))
        (add_nonneg (mul_nonneg hv hm) hc)]


end
end OAI.RVM

end

section
-- generalized from OpenAI OAI.RVM, openai/math@3344da5
namespace OAI.RVMS
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology RealInnerProductSpace
variable {ι : Type} [Fintype ι] {σ : Species ι} {H : ℝ} {s₁ s₂ : Solution ι}
abbrev msSq (s₁ s₂ : Solution ι) (b : ι) : Particle := fun p => (s₁.f b p-s₂.f b p)^2/2
abbrev msPN (s₁ s₂ : Solution ι) (b : ι) := RVM.particleMoment (msSq s₁ s₂ b) (fun _ => (1:ℝ))
abbrev msPF (s₁ s₂ : Solution ι) (b : ι) := RVM.particleMoment (msSq s₁ s₂ b) velocity
abbrev msDJ (s₁ s₂ : Solution ι) (b : ι) (t : ℝ) (x : Vec) := RVM.current (fun z => s₁.f b (t,z)) x - RVM.current (fun z => s₂.f b (t,z)) x
lemma msSq_regular (h₁ : ClassicalUpTo σ s₁ H) (h₂ : ClassicalUpTo σ s₂ H) (b : ι) :
    RVM.RegularParticle (msSq s₁ s₂ b) := RVM.squareDifference_regular_before_msVB (kernelSlice_VB_before h₁ b) (kernelSlice_VB_before h₂ b)
lemma species_difference_estimate (h₁ : ClassicalUpTo σ s₁ H) (h₂ : ClassicalUpTo σ s₂ H) (b : ι)
    {T : ℝ} (hT : 0 ≤ T) (hTH : T ≤ H) : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ioo 0 T, ∀ x : Vec,
    deriv (fun r => msPN s₁ s₂ b (r,x)) t + divergence (fun y => msPF s₁ s₂ b (t,y)) x -
      σ.weight b * dot (s₁.E (t,x)-s₂.E (t,x)) (msDJ s₁ s₂ b t x) ≤
      C * ((‖s₁.E (t,x)-s₂.E (t,x)‖^2+‖s₁.B (t,x)-s₂.B (t,x)‖^2)/2+msPN s₁ s₂ b (t,x)) := by
  have r₁ := (kernelSlice_VB_before h₁ b).regularParticle
  have r₂ := (kernelSlice_VB_before h₂ b).regularParticle
  obtain ⟨K₁,hK₁,hs₁⟩ := r₁.2 T hT
  obtain ⟨K₂,hK₂,hs₂⟩ := r₂.2 T hT
  let K : Set Vec := Prod.snd '' (K₁ ∪ K₂)
  have hK : IsCompact K := (hK₁.union hK₂).image continuous_snd
  obtain ⟨L,hL,hLb⟩ := r₂.velocity_derivative_bound hT
  refine ⟨(2*(|σ.kappa b| * L + |σ.weight b|))*(1+(volume K).toReal),by positivity,?_⟩
  intro t ht x

  have hf₁ := r₁.slice ht.1.le x
  have hf₂ := r₂.slice ht.1.le x
  have hz : ∀ v ∉ K, s₁.f b (t,x,v)-s₂.f b (t,x,v)=0 := by
    intro v hv
    have hnot₁ : (x,v) ∉ tsupport (fun z => s₁.f b (t,z)) := by
      intro hh
      exact hv ⟨(x,v),Or.inl (hs₁ t ⟨ht.1.le,ht.2.le⟩ hh),rfl⟩
    have hnot₂ : (x,v) ∉ tsupport (fun z => s₂.f b (t,z)) := by
      intro hh
      exact hv ⟨(x,v),Or.inr (hs₂ t ⟨ht.1.le,ht.2.le⟩ hh),rfl⟩
    rw [image_eq_zero_of_notMem_tsupport hnot₁,image_eq_zero_of_notMem_tsupport hnot₂,sub_self]
  let E := s₁.E (t,x)-s₂.E (t,x)
  let B := s₁.B (t,x)-s₂.B (t,x)
  let g := fun v : Vec => s₁.f b (t,x,v)-s₂.f b (t,x,v)
  let D := fderiv ℝ (fun w => s₂.f b (t,x,w))
  have hgc : Continuous g := hf₁.1.continuous.sub hf₂.1.continuous
  have hdc : Continuous D := hf₂.1.continuous_fderiv (by simp)
  have hgK : HasCompactSupport g := hf₁.2.sub hf₂.2
  have hi : Integrable (fun v => -σ.kappa b*(g v * D v (E+RVM.cross (RVM.velocity v) B))) :=
    (continuous_const.mul (hgc.mul (hdc.clm_apply (RVM.contDiff_lorentz (k:=1) E B).continuous))).integrable_of_hasCompactSupport
      (hgK.mul_right.mul_left)
  have hjI : Integrable (fun v => g v • RVM.velocity v) := (hgc.smul (RVM.contDiff_velocity (k:=1)).continuous).integrable_of_hasCompactSupport hgK.smul_right
  have hj : (∫ v : Vec, g v • RVM.velocity v) = msDJ s₁ s₂ b t x := by
    simp only [g,sub_smul,msDJ,RVM.current]
    exact integral_sub (r₁.moment_integrable (RVM.contDiff_velocity (k:=1)).continuous ht.1.le x)
      (r₂.moment_integrable (RVM.contDiff_velocity (k:=1)).continuous ht.1.le x)
  have hb := RVM.compact_signed_difference_source_bound (σ.kappa b) (σ.weight b) E B hgc hdc hK hz hL (hLb t ht x)
  simp only [RVM.dot_eq_inner] at hb
  rw [integral_sub hi ((hjI.const_inner E).const_mul _),integral_const_mul (σ.weight b),integral_inner hjI,hj] at hb
  have hp := RVM.particle_difference_local_before_msVB (kernelSlice_VB_before h₁ b) (kernelSlice_VB_before h₂ b) ht.1 (ht.2.trans_le hTH) x
  change deriv (fun r => msPN s₁ s₂ b (r,x)) t + divergence (fun y => msPF s₁ s₂ b (t,y)) x = _ at hp
  rw [hp]
  change _ - σ.weight b * RVM.dot E (msDJ s₁ s₂ b t x) ≤ _
  rw [RVM.dot_eq_inner, msPN, RVM.particleMoment_one]
  convert hb using 2
  apply integral_congr_ae
  filter_upwards [] with v
  simp only [kernelSlice,←smul_sub,RVM.cross_smul_right,←smul_add,map_smul,smul_eq_mul]
  dsimp [D,E,B,g]; ring

end
end OAI.RVMS

end

section
-- generalized from OpenAI OAI.RVM, openai/math@3344da5
namespace OAI.RVMS
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
variable {ι : Type} [Fintype ι] {σ : Species ι} {s : Solution ι} {d : Datum ι}




lemma divergence_finsum {F : ι → Vec → Vec} (c : ι → ℝ) {x : Vec}
    (hF : ∀ b, DifferentiableAt ℝ (F b) x) :
    RVM.divergence (fun y => ∑ b, c b • F b y) x = ∑ b, c b * RVM.divergence (F b) x := by
  have h : HasFDerivAt (fun y => ∑ b, c b • F b y) (∑ b, c b • fderiv ℝ (F b) x) x :=
    HasFDerivAt.fun_sum (fun b _ => ((hF b).hasFDerivAt.const_smul (c b)))
  unfold RVM.divergence RVM.spatialPartial
  simp only [Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  have hci : ∀ b, HasFDerivAt (fun y => F b y i) ((PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).comp
      (fderiv ℝ (F b) x)) x := fun b =>
    (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).hasFDerivAt.comp x (hF b).hasFDerivAt
  have hc' : HasFDerivAt (fun y => (∑ b, c b • F b y) i)
      (∑ b, c b • (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).comp (fderiv ℝ (F b) x)) x := by
    have := HasFDerivAt.fun_sum (u := Finset.univ) (fun b _ => ((hci b).const_smul (c b)))
    refine this.congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)
    simp
  rw [show (fun y => ((fun y => ∑ b, c b • F b y) y).ofLp i) = fun y => (∑ b, c b • F b y) i from rfl,
    hc'.fderiv]
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
    smul_eq_mul]
  apply Finset.sum_congr rfl
  intro b _
  rw [show (fun y => (F b y).ofLp i) = fun y => F b y i from rfl, (hci b).fderiv]







end
end OAI.RVMS

end

section
-- generalized from OpenAI OAI.RVM, openai/math@3344da5
namespace OAI.RVMS
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology RealInnerProductSpace
variable {ι : Type} [Fintype ι] {σ : Species ι} {H : ℝ} {s₁ s₂ : Solution ι}
abbrev msFE (a b : Solution ι) (p : ℝ × Vec) := (‖a.E p-b.E p‖^2+‖a.B p-b.B p‖^2)/2
abbrev msFF (a b : Solution ι) (p : ℝ × Vec) := RVM.cross (a.E p-b.E p) (a.B p-b.B p)
abbrev msDE (a b : Solution ι) (p : ℝ × Vec) := msFE a b p + ∑ i, msPN a b i p
abbrev msDF (a b : Solution ι) (p : ℝ × Vec) := msFF a b p + ∑ i, msPF a b i p
lemma msPN_nonneg (b : ι) (p : ℝ × Vec) : 0 ≤ msPN s₁ s₂ b p := by
  rw [msPN,RVM.particleMoment_one]; exact integral_nonneg (fun v => by dsimp [msSq]; positivity)
lemma msFE_regular (h₁ : ClassicalUpTo σ s₁ H) (h₂ : ClassicalUpTo σ s₂ H) :
    ContDiffOn ℝ 1 (msFE s₁ s₂) fieldHalfSpace :=
  (((h₁.E1.sub h₂.E1).norm_sq ℝ).add ((h₁.B1.sub h₂.B1).norm_sq ℝ)).div_const 2
lemma msFF_regular (h₁ : ClassicalUpTo σ s₁ H) (h₂ : ClassicalUpTo σ s₂ H) :
    ContDiffOn ℝ 1 (msFF s₁ s₂) fieldHalfSpace := RVM.contDiff_cross.contDiffOn.comp ((h₁.E1.sub h₂.E1).prodMk (h₁.B1.sub h₂.B1)) (fun _ _ => mem_univ _)
lemma msDE_regular (h₁ : ClassicalUpTo σ s₁ H) (h₂ : ClassicalUpTo σ s₂ H) :
    ContDiffOn ℝ 1 (msDE s₁ s₂) (Ioi 0 ×ˢ (univ : Set Vec)) :=
  ((msFE_regular h₁ h₂).mono (show Ioi 0 ×ˢ (univ : Set Vec) ⊆ fieldHalfSpace from fun p hp => show 0 ≤ p.1 from hp.1.le)).add (ContDiffOn.sum (fun b _ => (msSq_regular h₁ h₂ b).moment_regular contDiff_const))
lemma msDF_regular (h₁ : ClassicalUpTo σ s₁ H) (h₂ : ClassicalUpTo σ s₂ H) :
    ContDiffOn ℝ 1 (msDF s₁ s₂) (Ioi 0 ×ˢ (univ : Set Vec)) :=
  ((msFF_regular h₁ h₂).mono (show Ioi 0 ×ˢ (univ : Set Vec) ⊆ fieldHalfSpace from fun p hp => show 0 ≤ p.1 from hp.1.le)).add (ContDiffOn.sum (fun b _ => (msSq_regular h₁ h₂ b).moment_regular RVM.contDiff_velocity))
lemma msDE_differential_bound_before (h₁ : ClassicalUpTo σ s₁ H) (h₂ : ClassicalUpTo σ s₂ H)
    {T : ℝ} (hT : 0 ≤ T) (hTH : T ≤ H) : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ioo 0 T, ∀ x : Vec,
    fderiv ℝ (msDE s₁ s₂) (t,x) (1,0)+RVM.divergence (fun y => msDF s₁ s₂ (t,y)) x ≤ C*msDE s₁ s₂ (t,x) := by
  classical
  choose C hC hc using fun b => species_difference_estimate h₁ h₂ b hT hTH
  refine ⟨∑ b,C b, Finset.sum_nonneg (fun b _ => hC b),?_⟩
  intro t ht x
  have nh : Ioi (0:ℝ) ×ˢ (univ : Set Vec) ∈ 𝓝 (t,x) := (isOpen_Ioi.prod (isOpen_univ (X:=Vec))).mem_nhds (x:=(t,x)) ⟨ht.1,mem_univ _⟩
  have nh' : fieldHalfSpace ∈ 𝓝 (t,x) := mem_of_superset nh (fun p hp => show 0 ≤ p.1 from hp.1.le)
  have hf : DifferentiableAt ℝ (msFE s₁ s₂) (t,x) := ((msFE_regular h₁ h₂).contDiffAt nh').differentiableAt (by simp)
  have hft : DifferentiableAt ℝ (fun r => msFE s₁ s₂ (r,x)) t := hf.comp (f := fun r : ℝ => (r,x)) t (differentiableAt_id.prodMk (differentiableAt_const x))
  have hfx : DifferentiableAt ℝ (fun y => msFF s₁ s₂ (t,y)) x := (((msFF_regular h₁ h₂).contDiffAt nh').differentiableAt (by simp)).comp (f := fun y : Vec => (t,y)) x ((differentiableAt_const t).prodMk differentiableAt_id)
  have hpt (b : ι) : DifferentiableAt ℝ (fun r => msPN s₁ s₂ b (r,x)) t :=
    ((((msSq_regular h₁ h₂ b).moment_regular (w:=fun _ => (1:ℝ)) contDiff_const).contDiffAt nh).differentiableAt (by simp)).comp (f := fun r : ℝ => (r,x)) t (differentiableAt_id.prodMk (differentiableAt_const x))
  have hpx (b : ι) : DifferentiableAt ℝ (fun y => msPF s₁ s₂ b (t,y)) x :=
    ((((msSq_regular h₁ h₂ b).moment_regular RVM.contDiff_velocity).contDiffAt nh).differentiableAt (by simp)).comp (f := fun y : Vec => (t,y)) x ((differentiableAt_const t).prodMk differentiableAt_id)
  have hm := ms_difference_maxwell_local_before h₁ h₂ ht.1 (ht.2.trans_le hTH) x
  have hj : current σ (fun b z => s₁.f b (t,z)) x-current σ (fun b z => s₂.f b (t,z)) x = ∑ b, σ.weight b • msDJ s₁ s₂ b t x := by simp [current,msDJ,RVM.current,smul_sub,Finset.sum_sub_distrib] <;> rfl
  change _ + _ = -RVM.dot _ _ at hm
  rw [hj,RVM.dot_eq_inner,inner_sum] at hm
  simp only [real_inner_smul_right,←RVM.dot_eq_inner] at hm
  have hh := Finset.sum_le_sum (s:=Finset.univ) (fun b _ => hc b t ht x)
  have hb : (∑ b, C b * (msFE s₁ s₂ (t,x)+msPN s₁ s₂ b (t,x))) ≤ (∑ b,C b)*msDE s₁ s₂ (t,x) := by
    rw [Finset.sum_mul]; apply Finset.sum_le_sum; intro b _
    apply mul_le_mul_of_nonneg_left _ (hC b); unfold msDE; gcongr
    exact Finset.single_le_sum (fun i _ => msPN_nonneg i _) (Finset.mem_univ b)
  rw [← RVM.deriv_time_slice (((msDE_regular h₁ h₂).contDiffAt nh).differentiableAt (by simp))]
  change deriv ((fun r => msFE s₁ s₂ (r,x)) + fun r => ∑ b, msPN s₁ s₂ b (r,x)) t + RVM.divergence (fun y => msFF s₁ s₂ (t,y) + ∑ b, msPF s₁ s₂ b (t,y)) x ≤ _
  rw [deriv_add hft (DifferentiableAt.fun_sum (fun b _ => hpt b)),deriv_fun_sum (fun b _ => hpt b), RVM.divergence_add hfx (DifferentiableAt.fun_sum (u := Finset.univ) (fun b _ => hpx b))]
  have hhdiv := divergence_finsum (fun _ : ι => (1:ℝ)) hpx
  simp only [one_smul,one_mul] at hhdiv; rw [hhdiv]
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib] at hh
  change _ + _ = _ at hm
  apply le_trans _ hb
  dsimp only [msFE,msFF] at *
  change _ - (∑ b, σ.weight b * RVM.dot _ (msDJ s₁ s₂ b t x)) ≤ _ at hh
  change deriv (fun r => msFE s₁ s₂ (r,x)) t + RVM.divergence (fun y => msFF s₁ s₂ (t,y)) x = _ at hm
  change (∑ i, deriv (fun r => msPN s₁ s₂ i (r,x)) t) + (∑ i, RVM.divergence (fun y => msPF s₁ s₂ i (t,y)) x) - _ ≤ _ at hh
  dsimp only [msFE,msFF] at hm
  linarith only [hh, hm]

end
end OAI.RVMS

end

section
-- generalized from OpenAI OAI.RVM, openai/math@3344da5
namespace OAI.RVMS
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology RealInnerProductSpace
variable {ι : Type} [Fintype ι] {σ : Species ι} {H : ℝ} {s₁ s₂ : Solution ι}
lemma msDE_vanish (h₁ : ClassicalUpTo σ s₁ H) (h₂ : ClassicalUpTo σ s₂ H)
    (he : RVM.TimeContinuousL2 (s₁.E-s₂.E)) (hb : RVM.TimeContinuousL2 (s₁.B-s₂.B))
    {T : ℝ} (hT : 0 ≤ T) (hTH : T ≤ H) (hz : ∀ x, msDE s₁ s₂ (0,x)=0) :
    ∀ x, msDE s₁ s₂ (T,x)=0 := by
  classical
  obtain ⟨C,hC,hineq⟩ := msDE_differential_bound_before h₁ h₂ hT hTH
  have hiP (t : ℝ) (ht : 0 ≤ t) (b : ι) : Integrable (fun x : Vec => msPN s₁ s₂ b (t,x)) :=
    (msSq_regular h₁ h₂ b).spatial_moment_integrable continuous_const ht
  have hiF (t : ℝ) (ht : 0 ≤ t) : Integrable (fun x : Vec => msFE s₁ s₂ (t,x)) :=
    ((he.integrable_norm_sq ht).add (hb.integrable_norm_sq ht)).div_const 2
  apply RVM.local_energy_inequality_vanishes hC hT (msDE_regular h₁ h₂) (msDF_regular h₁ h₂) _ _ _ _ _ hineq hz
  · apply ((msFE_regular h₁ h₂).continuousOn.mono (show Icc 0 T ×ˢ (univ : Set Vec) ⊆ fieldHalfSpace from fun p hp => hp.1.1)).add
    exact continuousOn_finsetSum _ (fun b _ => (msSq_regular h₁ h₂ b).moment_continuous_slab continuous_const hT)
  · intro t ht x; unfold msDE; exact add_nonneg (by unfold msFE; positivity) (Finset.sum_nonneg fun b _ => msPN_nonneg b _)
  · intro t ht; exact (hiF t ht.1).add (integrable_finsetSum _ (fun b _ => hiP t ht.1 b))
  · have hF := ((he.continuous_integral_norm_sq.add hb.continuous_integral_norm_sq).div_const 2).mono (Icc_subset_Ici_self : Icc 0 T ⊆ Ici (0:ℝ))
    have hP (b : ι) := (msSq_regular h₁ h₂ b).integrated_moment_continuous (w := fun _ => (1:ℝ)) continuous_const hT
    apply (hF.add (continuousOn_finsetSum Finset.univ (fun b _ => hP b))).congr
    intro t ht
    change (∫ x : Vec, msFE s₁ s₂ (t,x) + ∑ b, msPN s₁ s₂ b (t,x)) = _
    rw [integral_add (hiF t ht.1) (integrable_finsetSum _ (fun b _ => hiP t ht.1 b)), integral_finsetSum _ (fun b _ => hiP t ht.1 b)]
    change (∫ x : Vec, (‖(s₁.E-s₂.E) (t,x)‖^2 + ‖(s₁.B-s₂.B) (t,x)‖^2)/2) + _ = _
    rw [integral_div, integral_add (he.integrable_norm_sq ht.1) (hb.integrable_norm_sq ht.1)]; rfl
  · intro t ht x; apply (norm_add_le _ _).trans; apply add_le_add
    · apply (RVM.norm_cross_le _ _).trans; unfold msFE; nlinarith [sq_nonneg (‖s₁.E (t,x)-s₂.E (t,x)‖-‖s₁.B (t,x)-s₂.B (t,x)‖)]
    · apply (norm_sum_le _ _).trans; apply Finset.sum_le_sum; intro b _
      exact (msSq_regular h₁ h₂ b).velocity_flux_bound ht.1.le x (fun v => by dsimp [msSq]; positivity)

lemma msDE_zero_iff_agree (h₁ : ClassicalUpTo σ s₁ H) (h₂ : ClassicalUpTo σ s₂ H)
    {t : ℝ} (ht : 0 ≤ t) (x : Vec) : msDE s₁ s₂ (t,x)=0 ↔
    s₁.E (t,x)=s₂.E (t,x) ∧ s₁.B (t,x)=s₂.B (t,x) ∧ ∀ b v, s₁.f b (t,x,v)=s₂.f b (t,x,v) := by
  classical
  constructor
  · intro hz
    have hF : 0 ≤ msFE s₁ s₂ (t,x) := by unfold msFE; positivity
    have hP := Finset.sum_nonneg (s:=Finset.univ) (fun b _ => msPN_nonneg (s₁:=s₁) (s₂:=s₂) b (t,x))
    unfold msDE at hz
    have hF0 : msFE s₁ s₂ (t,x)=0 := by linarith
    unfold msFE at hF0
    refine ⟨sub_eq_zero.mp (norm_eq_zero.mp ?_),sub_eq_zero.mp (norm_eq_zero.mp ?_),?_⟩
    · nlinarith [sq_nonneg ‖s₁.B (t,x)-s₂.B (t,x)‖]
    · nlinarith [sq_nonneg ‖s₁.E (t,x)-s₂.E (t,x)‖]
    intro b v
    have hle := Finset.single_le_sum (fun i _ => msPN_nonneg (s₁:=s₁) (s₂:=s₂) i (t,x)) (Finset.mem_univ b)
    have hz' : msPN s₁ s₂ b (t,x)=0 := by linarith [msPN_nonneg (s₁:=s₁) (s₂:=s₂) b (t,x)]
    rw [msPN,RVM.particleMoment_one] at hz'
    have hs := (msSq_regular h₁ h₂ b).slice ht x
    have hae := (integral_eq_zero_iff_of_nonneg (fun w : Vec => show 0 ≤ msSq s₁ s₂ b (t,x,w) by unfold msSq; positivity) (hs.1.continuous.integrable_of_hasCompactSupport hs.2)).mp hz'
    have eq := congrFun (Measure.eq_of_ae_eq (μ:=volume) hae hs.1.continuous continuous_const) v
    change (s₁.f b (t,x,v)-s₂.f b (t,x,v))^2/2=0 at eq
    nlinarith [sq_nonneg (s₁.f b (t,x,v)-s₂.f b (t,x,v))]
  · rintro ⟨he,hb,hf⟩; simp [msDE,msFE,msPN,RVM.particleMoment_one,msSq,he,hb,hf]


end
end OAI.RVMS

end

namespace MSUnits
open OMA.S_wp_regularity_of_solutions_of_vlasov_maxwell_equations
open MeasureTheory Set
noncomputable section
variable {ι : Type} [Fintype ι] (P : Plasma ι)
def moment (a : ι) := P.mass a * P.c
def kappa (a : ι) := P.charge a / (P.mass a * P.c^2)
def weight (a : ι) := P.charge a / P.ε₀
theorem ratio (a : ι) : weight P a / kappa P a = P.mass a * P.c^2 / P.ε₀ := by
  unfold weight kappa
  field_simp [P.charge_ne a,P.mass_pos a |>.ne',P.c_pos.ne',P.ε₀_pos.ne']
theorem ratio_pos (a : ι) : 0 < weight P a / kappa P a := by
  rw [ratio]; exact div_pos (mul_pos (P.mass_pos a) (sq_pos_of_pos P.c_pos)) P.ε₀_pos
theorem velocity_scale (a : ι) (v : Vec) : velocity P a (moment P a • v) = P.c • OAI.RVM.velocity v := by
  have hm := P.mass_pos a
  have hc := P.c_pos
  have h : 0 < P.mass a * P.c := mul_pos hm hc
  simp only [moment,velocity,OAI.RVM.velocity,OAI.RVM.q,norm_smul, Real.norm_eq_abs,abs_of_pos h,mul_pow,mul_div_cancel_left₀ _ (pow_ne_zero 2 h.ne'),smul_smul]
  congr 1
  field_simp
  <;> ring
end
end MSUnits

namespace MSUnits
open OMA.S_wp_regularity_of_solutions_of_vlasov_maxwell_equations
open MeasureTheory Set
noncomputable section
variable {ι : Type} [Fintype ι] (P : Plasma ι)
def fNorm (g : ι → Phase → ℝ) (a : ι) (z : Phase) := (moment P a)^3 * g a (z.1,moment P a • z.2)
theorem jac {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (r : ℝ) (h : 0 < r) (g : Vec → F) : (r^3) • (∫ p : Vec, g (r • p)) = ∫ p, g p := by
  rw [Measure.integral_comp_smul_of_nonneg volume g r (hR := h.le)]
  simp [Vec, smul_smul, h.ne']
theorem rho (g : ι → Phase → ℝ) (x : Vec) : (∑ a, weight P a * ∫ v : Vec, fNorm P g a (x,v)) = chargeDensity P g x / P.ε₀ := by
  rw [chargeDensity, Finset.sum_div]; apply Finset.sum_congr rfl; intro a _
  unfold fNorm; rw [integral_const_mul]
  rw [show (moment P a)^3 * (∫ v : Vec, g a (x,moment P a • v)) = _ from jac _ (mul_pos (P.mass_pos a) P.c_pos) (fun v => g a (x,v))]; unfold weight; ring
theorem current (g : ι → Phase → ℝ) (x : Vec) : (P.c * P.ε₀) • (∑ a, weight P a • ∫ v : Vec, fNorm P g a (x,v) • OAI.RVM.velocity v) = currentDensity P g x := by
  rw [currentDensity,Finset.smul_sum]; apply Finset.sum_congr rfl; intro a _
  rw [← jac (moment P a) (mul_pos (P.mass_pos a) P.c_pos) (fun p => g a (x,p) • velocity P a p)]
  simp only [fNorm,velocity_scale, mul_smul, integral_smul,smul_comm (g a _) P.c]
  simp only [smul_smul]
  congr 1; unfold weight; field_simp [P.ε₀_pos.ne']
end
end MSUnits

namespace MSUnits
open OMA.S_wp_regularity_of_solutions_of_vlasov_maxwell_equations
open MeasureTheory Set
open scoped ContDiff
noncomputable section
variable {ι : Type} [Fintype ι] (P : Plasma ι)
def species : OAI.RVMS.Species ι := ⟨kappa P,weight P,fun a => div_ne_zero (P.charge_ne a) (mul_ne_zero (P.mass_pos a).ne' (pow_ne_zero _ P.c_pos.ne')),fun a => div_ne_zero (P.charge_ne a) P.ε₀_pos.ne', ratio_pos P⟩
def datum (d : Datum ι) : OAI.RVMS.Datum ι := ⟨fNorm P d.f₀,d.E₀,fun x => P.c • d.B₀ x⟩
def phaseEquiv (r : ℝ) (hr : r ≠ 0) : Phase ≃ₜ Phase := (Homeomorph.refl Vec).prodCongr (Homeomorph.smul (Units.mk0 r hr))
theorem partial_mul (g : Vec → ℝ) (a : ℝ) (x : Vec) (i) : partialDeriv (fun y => a * g y) x i = a * partialDeriv g x i := by
  unfold partialDeriv; change fderiv ℝ (a • g) x _ = _; rw [fderiv_const_smul_field]; rfl
theorem div_scale (F : Vec → Vec) (b : ℝ) (x : Vec) : divergence (fun y => b • F y) x = b * divergence F x := by
  unfold divergence; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; apply partial_mul
end
end MSUnits

namespace MSUnits
open OMA.S_wp_regularity_of_solutions_of_vlasov_maxwell_equations
open MeasureTheory Set
noncomputable section
variable {ι : Type} [Fintype ι] (P : Plasma ι)
def normSol (s : Solution ι) : OAI.RVMS.Solution ι where
  f a z := (moment P a)^3 * s.f a (P.c⁻¹ * z.1,z.2.1,moment P a • z.2.2)
  E z := s.E (P.c⁻¹ * z.1,z.2)
  B z := P.c • s.B (P.c⁻¹ * z.1,z.2)
theorem hm (a : ι) : 0 < moment P a := mul_pos (P.mass_pos a) P.c_pos
end
end MSUnits

namespace MSUnits
open OMA.S_wp_regularity_of_solutions_of_vlasov_maxwell_equations
open MeasureTheory Set
open scoped Pointwise
noncomputable section
theorem DT {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : ℝ → F) (a b t : ℝ) (ha : 0 < a) (ht : 0 ≤ t) : derivWithin (fun u => b • f (a*u)) (Ici 0) t = (b*a) • derivWithin f (Ici 0) (a*t) := by
  have hs : a • (Ici (0:ℝ)) = Ici 0 := by
    ext x; constructor
    · rintro ⟨y,hy,rfl⟩; exact mul_nonneg ha.le hy
    · intro hx; exact ⟨x/a,div_nonneg hx ha.le, by change a*(x/a)=x; field_simp⟩
  change derivWithin (b • (fun u => f (a • u))) _ _ = _
  rw [derivWithin_const_smul_field]; unfold derivWithin; rw [fderivWithin_comp_smul a (uniqueDiffOn_Ici _ t ht),hs]; simp [smul_smul]
theorem DP (g : Vec → ℝ) (a b : ℝ) (x : Vec) (i) : partialDeriv (fun y => b * g (a • y)) x i = (b*a) * partialDeriv g (a • x) i := by
  rw [partial_mul]; unfold partialDeriv; rw [fderiv_comp_smul]; simp [mul_assoc]
theorem curl_scale (F : Vec → Vec) (b : ℝ) (x : Vec) : curl (fun y => b • F y) x = b • curl F x := by
  ext i; fin_cases i <;> simp [curl,PiLp.smul_apply,partial_mul,mul_sub]
end
end MSUnits

namespace MSUnits
open OMA.S_wp_regularity_of_solutions_of_vlasov_maxwell_equations
open MeasureTheory Set
noncomputable section
variable {ι : Type} [Fintype ι] (P : Plasma ι)
def vr (s : Solution ι) (a : ι) (t : ℝ) (x p : Vec) := derivWithin (fun u => s.f a (u,x,p)) (Ici 0) t + (∑ i, velocity P a p i * partialDeriv (fun y => s.f a (t,y,p)) x i) + P.charge a * (∑ i, (s.E (t,x) + cross (velocity P a p) (s.B (t,x))) i * partialDeriv (fun w => s.f a (t,x,w)) p i)
def vn (s : OAI.RVMS.Solution ι) (a : ι) (t : ℝ) (x p : Vec) := derivWithin (fun u => s.f a (u,x,p)) (Ici 0) t + (∑ i, OAI.RVM.velocity p i * partialDeriv (fun y => s.f a (t,y,p)) x i) + (∑ i, (kappa P a • (s.E (t,x) + cross (OAI.RVM.velocity p) (s.B (t,x)))) i * partialDeriv (fun w => s.f a (t,x,w)) p i)
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
end MSUnits

namespace MSUnits
open OMA.S_wp_regularity_of_solutions_of_vlasov_maxwell_equations
open MeasureTheory Set
noncomputable section
variable {ι : Type} [Fintype ι] (P : Plasma ι)
theorem amp (e b j : Vec) : (P.c⁻¹ • e - P.c • b = -j) ↔ (b = P.μ₀ • ((P.c*P.ε₀) • j) + (P.μ₀ * P.ε₀) • e) := by
  have hm : P.μ₀ * P.ε₀ = P.c⁻¹ * P.c⁻¹ := by field_simp [P.c_pos.ne']; nlinarith [P.maxwell_const]
  have hj : P.μ₀ * (P.c * P.ε₀) = P.c⁻¹ := by rw [mul_left_comm,hm]; field_simp
  rw [smul_smul,hj,hm]; constructor
  · intro h; have hh := congrArg (P.c⁻¹ • ·) h
    simp only [smul_sub,smul_neg,smul_smul,inv_mul_cancel₀ P.c_pos.ne',one_smul] at hh; abel_nf at *; linear_combination (norm := abel) -hh
  · rintro rfl; simp [smul_add,smul_smul,P.c_pos.ne']
theorem far (b e : Vec) : (b + e = 0) ↔ (e = -b) := by rw [eq_neg_iff_add_eq_zero,add_comm]
theorem point (s : Solution ι) (t : ℝ) (ht : 0 ≤ t) :
  (let n := normSol P s; (∀ a x v, vn P n a t x v = 0) ∧
  (∀ x, derivWithin (fun u => n.E (u,x)) (Ici 0) t - curl (fun y => n.B (t,y)) x = - OAI.RVMS.current (species P) (fun a z => n.f a (t,z)) x) ∧
  (∀ x, derivWithin (fun u => n.B (u,x)) (Ici 0) t + curl (fun y => n.E (t,y)) x = 0) ∧
  (∀ x, divergence (fun y => n.E (t,y)) x = OAI.RVMS.rho (species P) (fun a z => n.f a (t,z)) x) ∧
  (∀ x, divergence (fun y => n.B (t,y)) x = 0)) ↔
  (let u := P.c⁻¹*t; (∀ a x p, vr P s a u x p = 0) ∧
  (∀ x, curl (fun y => s.B (u,y)) x = P.μ₀ • currentDensity P (fun a z => s.f a (u,z)) x + (P.μ₀*P.ε₀) • derivWithin (fun t' => s.E (t',x)) (Ici 0) u) ∧
  (∀ x, curl (fun y => s.E (u,y)) x = -derivWithin (fun t' => s.B (t',x)) (Ici 0) u) ∧
  (∀ x, divergence (fun y => s.E (u,y)) x = chargeDensity P (fun a z => s.f a (u,z)) x / P.ε₀) ∧
  (∀ x, divergence (fun y => s.B (u,y)) x = 0)) := by
  dsimp only
  apply and_congr
  · simp only [vr_scale P s _ t ht,mul_eq_zero]
    constructor
    · intro h a x p; simpa [smul_smul,(hm P a).ne',P.c_pos.ne'] using h a x ((moment P a)⁻¹ • p)
    · intro h a x p; exact Or.inr (h _ _ _)
  apply and_congr
  · apply forall_congr'; intro x
    have h := DT (fun u => s.E (u,x)) P.c⁻¹ 1 t (inv_pos.mpr P.c_pos) ht
    simp only [one_smul,one_mul] at h
    simp only [normSol,curl_scale,h]; rw [← current P]; apply amp
  apply and_congr
  · apply forall_congr'; intro x; simp only [normSol]; rw [DT (fun u => s.B (u,x)) _ _ t (inv_pos.mpr P.c_pos) ht,mul_inv_cancel₀ P.c_pos.ne',one_smul]; apply far
  apply and_congr
  · apply forall_congr'; intro x; rw [← rho P]; rfl
  · simp [normSol,div_scale,P.c_pos.ne']
end
end MSUnits

namespace MSUnits
open OMA.S_wp_regularity_of_solutions_of_vlasov_maxwell_equations
open MeasureTheory Set
open scoped ContDiff
noncomputable section
variable {ι : Type} [Fintype ι]
theorem smooth_field {F : Field} {S U : Set ℝ} {n : WithTop ℕ∞} (a b : ℝ) (hmap : MapsTo (fun t => a*t) S U) (h : ContDiffOn ℝ n F {z | z.1 ∈ U}) : ContDiffOn ℝ n (fun z : ℝ × Vec => b • F (a*z.1,z.2)) {z | z.1 ∈ S} := by
  apply ContDiffOn.const_smul; apply h.comp (f := fun z : ℝ × Vec => (a*z.1,z.2)) _ (fun _ hz => hmap (show _ ∈ S from hz)); exact ((contDiff_const.mul contDiff_fst).prodMk contDiff_snd).contDiffOn
theorem smooth_f {f : Density} {S U : Set ℝ} {n : WithTop ℕ∞} (a b r : ℝ) (hmap : MapsTo (fun t => a*t) S U) (h : ContDiffOn ℝ n f {z | z.1 ∈ U}) : ContDiffOn ℝ n (fun z : ℝ × Phase => b * f (a*z.1,z.2.1,r • z.2.2)) {z | z.1 ∈ S} := by
  apply contDiffOn_const.mul; apply h.comp (f := fun z : ℝ × Phase => (a*z.1,z.2.1,r • z.2.2)) _ (fun _ hz => hmap (show _ ∈ S from hz)); apply ContDiff.contDiffOn; fun_prop
end
end MSUnits

namespace OAI.RVM
open Filter Set
open scoped Topology ContDiff
variable {X W : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

lemma c1cut {τ H : ℝ} (hτ : τ < H) {F : ℝ × X → W}
    (hF : ContDiffOn ℝ 1 F {p | p.1 ∈ Icc 0 H}) :
    ContDiffOn ℝ 1 (upperTimeExtend τ H F) {p | 0 ≤ p.1} := by
  intro p hp
  by_cases hpt : p.1 < H
  · have hlocal : {q : ℝ × X | q.1 ∈ Icc 0 H} ∈ 𝓝[{q | 0 ≤ q.1}] p := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds
        ((isOpen_lt continuous_fst continuous_const).mem_nhds hpt),
        self_mem_nhdsWithin] with q hq hq0
      exact ⟨hq0,hq.le⟩
    exact ((((contDiff_upperTimeCut τ H).of_le (by decide : (1 : WithTop ℕ∞) ≤ ∞)).comp contDiff_fst).contDiffAt.contDiffWithinAt).smul
      ((hF p ⟨hp,hpt.le⟩).mono_of_mem_nhdsWithin hlocal)
  · exact (contDiffAt_const.congr_of_eventuallyEq
      (upperTimeExtend_eventually_zero hτ F (show (τ+H)/2 < p.1 by linarith))).contDiffWithinAt
end OAI.RVM
namespace PhysDifference
open OMA.S_wp_regularity_of_solutions_of_vlasov_maxwell_equations MeasureTheory Set MSUnits
open scoped ContDiff
noncomputable section
variable {ι : Type} [Fintype ι]
private def L (F : Field) (U : ℝ) := ∃ G : ℝ → Lp Vec 2 (volume : Measure Vec), ContinuousOn G (Icc 0 U) ∧ ∀ t ∈ Icc 0 U, (G t : Vec → Vec) =ᵐ[volume] fun x => F (t,x)
private theorem sl2 {F U} (h : L F U) (P : Plasma ι) (b : ℝ) : L (fun z => b • F (P.c⁻¹ * z.1,z.2)) (P.c*U) := by
  obtain ⟨G,hG,he⟩ := h
  have hm : MapsTo (fun t => P.c⁻¹*t) (Icc 0 (P.c*U)) (Icc 0 U) := by
    intro t ht; refine ⟨mul_nonneg (inv_pos.mpr P.c_pos).le ht.1,?_⟩
    simpa [← mul_assoc,P.c_pos.ne'] using mul_le_mul_of_nonneg_left ht.2 (inv_pos.mpr P.c_pos).le
  refine ⟨fun t => b • G (P.c⁻¹*t), (hG.comp (continuous_const.mul continuous_id).continuousOn hm).const_smul b,?_⟩
  intro t ht; filter_upwards [Lp.coeFn_smul b (G (P.c⁻¹*t)), he _ (hm ht)] with x h h'; rw [h]; simp [h']
private theorem pack (P : Plasma ι) (s : Solution ι) {U t : ℝ} (ht : 0 ≤ t) (hU : t < U)
    (hf : ∀ i, ContDiffOn ℝ 1 (s.f i) (densitySlab U)) (hE : ContDiffOn ℝ 1 s.E (fieldSlab U))
    (hB : ContDiffOn ℝ 1 s.B (fieldSlab U)) (he : L s.E U) (hb : L s.B U)
    (hk : ∃ K : Set Phase, IsCompact K ∧ ∀ i r, r ∈ Icc 0 U → tsupport (fun z => s.f i (r,z)) ⊆ K)
    (eqn : OAI.RVMS.EquationsBefore (species P) (normSol P s) (P.c*U)) :
    let q := OAI.RVMS.msCutoff (P.c*t) (P.c*U) (normSol P s)
    OAI.RVMS.ClassicalUpTo (species P) q (P.c*t) ∧ OAI.RVM.TimeContinuousL2 q.E ∧ OAI.RVM.TimeContinuousL2 q.B := by
  dsimp only
  have htU := mul_lt_mul_of_pos_left hU P.c_pos
  have hU0 := mul_nonneg P.c_pos.le (ht.trans hU.le)
  have hm' : MapsTo (fun t => P.c⁻¹*t) (Icc 0 (P.c*U)) (Icc 0 U) := by
    intro r hr; refine ⟨mul_nonneg (inv_pos.mpr P.c_pos).le hr.1,?_⟩
    simpa [← mul_assoc,P.c_pos.ne'] using mul_le_mul_of_nonneg_left hr.2 (inv_pos.mpr P.c_pos).le
  have eL := sl2 he P 1; simp only [one_smul] at eL
  refine ⟨⟨fun i => OAI.RVM.c1cut htU (smooth_f _ _ _ hm' (hf i)),?_, OAI.RVM.c1cut htU (smooth_field _ _ hm' hB),?_,OAI.RVMS.msCutoff_equations htU eqn⟩, OAI.RVM.timeContinuousL2_upperTimeExtend htU hU0 eL, OAI.RVM.timeContinuousL2_upperTimeExtend htU hU0 (sl2 hb P P.c)⟩
  · have hh := smooth_field _ 1 hm' hE; simp only [one_smul] at hh; exact OAI.RVM.c1cut htU hh
  · obtain ⟨K,hK,hk⟩ := hk
    let e (i : ι) := phaseEquiv (moment P i) (hm P i).ne'
    intro T _; refine ⟨⋃ i, (e i) ⁻¹' K, isCompact_iUnion fun i => (e i).isCompact_preimage.mpr hK,?_⟩
    intro i r hr; apply Subset.trans _ (subset_iUnion (fun j => (e j) ⁻¹' K) i)
    apply closure_minimal _ (hK.isClosed.preimage (e i).continuous)
    intro z hz; by_cases hu : r ≤ P.c*U
    · apply hk i _ (hm' ⟨hr.1,hu⟩); apply subset_closure; intro hh; apply hz
      change s.f i (_,z.1,moment P i • z.2) = 0 at hh
      change OAI.RVM.upperTimeCut _ _ r • ((moment P i)^3 * s.f i (_,z.1,moment P i • z.2)) = 0
      rw [hh,mul_zero,smul_zero]
    · exfalso; apply hz; simp [OAI.RVMS.msCutoff,OAI.RVM.upperTimeExtend,OAI.RVM.upperTimeCut_zero htU (show (P.c*t+P.c*U)/2 ≤ r by linarith)]
end
end PhysDifference
open OMA.S_wp_regularity_of_solutions_of_vlasov_maxwell_equations MSUnits MeasureTheory Set
open scoped ContDiff
theorem OMA.solution : OMA.R_wp_regularity_of_solutions_of_vlasov_maxwell_equations_R1_H2_R1.H1 := by
  intro ι _ P d _ L A s b U V t hs hb ht hU hV x
  let cut (v : Solution ι) (W : ℝ) := OAI.RVMS.msCutoff (P.c*t) (P.c*W) (normSol P v)
  have pk (v : Solution ι) (W : ℝ) (hv : A v W) (hw : t < W) :
      OAI.RVMS.ClassicalUpTo (species P) (cut v W) (P.c*t) ∧ OAI.RVM.TimeContinuousL2 (cut v W).E ∧ OAI.RVM.TimeContinuousL2 (cut v W).B := by
    obtain ⟨f,E,B,_,e,b,K,h,rest⟩ := hv
    apply PhysDifference.pack P v ht hw f E B e b K
    intro r hr hrW; apply (point P v r hr).mpr
    apply h _ (mul_nonneg (inv_pos.mpr P.c_pos).le hr)
    simpa [← mul_assoc,P.c_pos.ne'] using mul_lt_mul_of_pos_left hrW (inv_pos.mpr P.c_pos)
  have p1 := pk s U hs hU
  have p2 := pk b V hb hV
  have nt := mul_nonneg P.c_pos.le ht
  have init (v : Solution ι) (W : ℝ) (hv : A v W) (hw : t < W) :
      (∀ i z, (cut v W).f i (0,z) = (datum P d).f₀ i z) ∧
      (∀ y, (cut v W).E (0,y) = (datum P d).E₀ y) ∧ ∀ y, (cut v W).B (0,y) = (datum P d).B₀ y := by
    obtain ⟨_,_,_,_,_,_,_,_,f,e,b⟩ := hv
    have h := OAI.RVMS.msCutoff_eq (mul_lt_mul_of_pos_left hw P.c_pos) nt (normSol P v)
    exact ⟨fun i z => (h.1 i z).trans (by simp [normSol,datum,fNorm,f]),fun y => (h.2.1 y).trans (by simp [normSol,datum,e]),fun y => (h.2.2 y).trans (by simp [normSol,datum,b])⟩
  have i1 := init s U hs hU
  have i2 := init b V hb hV
  have zero (y : Vec) : OAI.RVMS.msDE (cut s U) (cut b V) (0,y)=0 :=
    (OAI.RVMS.msDE_zero_iff_agree p1.1 p2.1 le_rfl y).mpr ⟨(i1.2.1 y).trans (i2.2.1 y).symm,(i1.2.2 y).trans (i2.2.2 y).symm,fun i v => (i1.1 i _).trans (i2.1 i _).symm⟩
  have eq := (OAI.RVMS.msDE_zero_iff_agree p1.1 p2.1 nt x).mp (OAI.RVMS.msDE_vanish p1.1 p2.1 (p1.2.1.sub p2.2.1) (p1.2.2.sub p2.2.2) nt le_rfl zero x)
  have a1 := OAI.RVMS.msCutoff_eq (mul_lt_mul_of_pos_left hU P.c_pos) (le_refl (P.c*t)) (normSol P s)
  have a2 := OAI.RVMS.msCutoff_eq (mul_lt_mul_of_pos_left hV P.c_pos) (le_refl (P.c*t)) (normSol P b)
  have e : s.E (t,x) = b.E (t,x) := by simpa [normSol,← mul_assoc,P.c_pos.ne'] using (a1.2.1 x).symm.trans (eq.1.trans (a2.2.1 x))
  have m := congrArg (P.c⁻¹ • ·) ((a1.2.2 x).symm.trans (eq.2.1.trans (a2.2.2 x)))
  simp [normSol,smul_smul,← mul_assoc,P.c_pos.ne'] at m
  have f (i : ι) (v : Vec) : s.f i (t,x,v) = b.f i (t,x,v) := by
    let u := (moment P i)⁻¹ • v
    have h := (a1.1 i (x,u)).symm.trans ((eq.2.2 i u).trans (a2.1 i (x,u)))
    simpa [normSol,u,smul_smul,← mul_assoc,P.c_pos.ne',(hm P i).ne'] using h
  simp [f,e,m]
