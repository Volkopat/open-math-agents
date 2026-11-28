import OMAStatements.S_wp_regularity_of_solutions_of_vlasov_maxwell_equations
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
namespace OMA.R_wp_regularity_of_solutions_of_vlasov_maxwell_equations_R1
open OMA.S_wp_regularity_of_solutions_of_vlasov_maxwell_equations Set Filter MeasureTheory
open scoped Topology ContDiff
noncomputable section
lemma time_slab_mem_nhdsWithin {X : Type*} [TopologicalSpace X]
    {p : ℝ × X} {H : ℝ} (hp : p.1<H) :
    {z : ℝ × X | z.1∈Icc (0:ℝ) H} ∈ 𝓝[{z : ℝ × X | 0 ≤ z.1}] p := by
  have hh : {z : ℝ × X | z.1<H} ∈ 𝓝 p :=
    (isOpen_lt continuous_fst continuous_const).mem_nhds hp
  filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds hh] with z hz hzH
  exact ⟨hz,hzH.le⟩

lemma contDiffOn_halfspace_of_slabs {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f : ℝ × X → Y} {k : ℕ∞ω}
    (hf : ∀ T : ℝ, 0 ≤ T → ContDiffOn ℝ k f {z : ℝ × X | z.1∈Icc (0:ℝ) T}) :
    ContDiffOn ℝ k f {z : ℝ × X | 0 ≤ z.1} := by
  intro p hp
  change 0 ≤ p.1 at hp
  exact (hf (p.1+1) (by linarith) p ⟨hp,by linarith⟩).mono_of_mem_nhdsWithin
    (time_slab_mem_nhdsWithin (by linarith))

lemma timeContinuousL2_of_slabs {F : Field}
    (hF : ∀ H : ℝ, 0 ≤ H → ∃ G : ℝ → Lp Vec 2 (volume : Measure Vec),
      ContinuousOn G (Icc (0:ℝ) H) ∧
      ∀ t∈Icc (0:ℝ) H, (G t : Vec → Vec) =ᵐ[volume] (fun x => F (t,x))) :
    TimeContinuousL2 F := by
  choose G hG he using fun H : ℝ => hF (max H 0) (le_max_right H 0)
  let g : ℝ → Lp Vec 2 (volume : Measure Vec) := fun t => G t t
  have hself (t : ℝ) (ht : 0 ≤ t) : (g t : Vec → Vec) =ᵐ[volume] (fun x => F (t,x)) :=
    he t t ⟨ht,le_max_left t 0⟩
  have heq (H t : ℝ) (ht : t∈Icc (0:ℝ) H) : g t=G H t := by
    apply Lp.ext
    exact (hself t ht.1).trans (he H t ⟨ht.1,ht.2.trans (le_max_left H 0)⟩).symm
  refine ⟨g,?_,hself⟩
  intro t ht
  have hmem : Icc (0:ℝ) (max (t+1) 0) ∈ 𝓝[Ici 0] t := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show t<t+1 by linarith))] with r hr hrH
    exact ⟨hr,hrH.le.trans (le_max_left (t+1) 0)⟩
  have hc := (hG (t+1) t ⟨ht,by linarith [le_max_left (t+1) 0]⟩).mono_of_mem_nhdsWithin hmem
  apply hc.congr_of_eventuallyEq_of_mem ?_ ht
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show t<t+1 by linarith))] with r hr hrH
  exact heq (t+1) r ⟨hr,hrH.le⟩

def H1 : Prop := ∀ (ι : Type) [Fintype ι] (P : Plasma ι) (d : Datum ι), Admissible P d →
  let L := fun (F : Field) (U : ℝ) => ∃ G : ℝ → Lp Vec 2 (volume : Measure Vec), ContinuousOn G (Icc 0 U) ∧ ∀ t ∈ Icc 0 U, (G t : Vec → Vec) =ᵐ[volume] fun x => F (t,x)
  let A := fun (s : Solution ι) (U : ℝ) =>
    (∀ i, ContDiffOn ℝ ∞ (s.f i) (densitySlab U)) ∧ ContDiffOn ℝ ∞ s.E (fieldSlab U) ∧ ContDiffOn ℝ ∞ s.B (fieldSlab U) ∧
    (∀ i t, t ∈ Icc 0 U → ∀ z, 0 ≤ s.f i (t,z)) ∧ L s.E U ∧ L s.B U ∧
    (∃ C : Set Phase, IsCompact C ∧ ∀ i t, t ∈ Icc 0 U → tsupport (fun z => s.f i (t,z)) ⊆ C) ∧
    (∀ t, 0 ≤ t → t < U → (∀ α x p,
    derivWithin (fun t' => s.f α (t', x, p)) (Ici 0) t +
    (∑ i : Fin 3, velocity P α p i * partialDeriv (fun y => s.f α (t, y, p)) x i) +
    P.charge α * (∑ i : Fin 3, (s.E (t, x) + cross (velocity P α p) (s.B (t, x))) i *
      partialDeriv (fun p' => s.f α (t, x, p')) p i) = 0) ∧
  (∀ x, curl (fun y => s.B (t, y)) x =
    P.μ₀ • currentDensity P (fun α z => s.f α (t, z)) x +
      (P.μ₀ * P.ε₀) • derivWithin (fun t' => s.E (t', x)) (Ici 0) t) ∧
  (∀ x, curl (fun y => s.E (t, y)) x = -derivWithin (fun t' => s.B (t', x)) (Ici 0) t) ∧
  (∀ x, divergence (fun y => s.E (t, y)) x =
    chargeDensity P (fun α z => s.f α (t, z)) x / P.ε₀) ∧
  (∀ x, divergence (fun y => s.B (t, y)) x = 0)) ∧
    (∀ i z, s.f i (0,z) = d.f₀ i z) ∧ (∀ x, s.E (0,x) = d.E₀ x) ∧ ∀ x, s.B (0,x) = d.B₀ x
  ∀ H : ℝ, 0 ≤ H → ∃ U : ℝ, H < U ∧ ∃ s, A s U

def H2 : Prop := ∀ (ι : Type) [Fintype ι] (P : Plasma ι) (d : Datum ι), Admissible P d →
  let L := fun (F : Field) (U : ℝ) => ∃ G : ℝ → Lp Vec 2 (volume : Measure Vec), ContinuousOn G (Icc 0 U) ∧ ∀ t ∈ Icc 0 U, (G t : Vec → Vec) =ᵐ[volume] fun x => F (t,x)
  let A := fun (s : Solution ι) (U : ℝ) =>
    (∀ i, ContDiffOn ℝ 1 (s.f i) (densitySlab U)) ∧ ContDiffOn ℝ 1 s.E (fieldSlab U) ∧ ContDiffOn ℝ 1 s.B (fieldSlab U) ∧
    (∀ i t, t ∈ Icc 0 U → ∀ z, 0 ≤ s.f i (t,z)) ∧ L s.E U ∧ L s.B U ∧
    (∃ C : Set Phase, IsCompact C ∧ ∀ i t, t ∈ Icc 0 U → tsupport (fun z => s.f i (t,z)) ⊆ C) ∧
    (∀ t, 0 ≤ t → t < U → (∀ α x p,
    derivWithin (fun t' => s.f α (t', x, p)) (Ici 0) t +
    (∑ i : Fin 3, velocity P α p i * partialDeriv (fun y => s.f α (t, y, p)) x i) +
    P.charge α * (∑ i : Fin 3, (s.E (t, x) + cross (velocity P α p) (s.B (t, x))) i *
      partialDeriv (fun p' => s.f α (t, x, p')) p i) = 0) ∧
  (∀ x, curl (fun y => s.B (t, y)) x =
    P.μ₀ • currentDensity P (fun α z => s.f α (t, z)) x +
      (P.μ₀ * P.ε₀) • derivWithin (fun t' => s.E (t', x)) (Ici 0) t) ∧
  (∀ x, curl (fun y => s.E (t, y)) x = -derivWithin (fun t' => s.B (t', x)) (Ici 0) t) ∧
  (∀ x, divergence (fun y => s.E (t, y)) x =
    chargeDensity P (fun α z => s.f α (t, z)) x / P.ε₀) ∧
  (∀ x, divergence (fun y => s.B (t, y)) x = 0)) ∧
    (∀ i z, s.f i (0,z) = d.f₀ i z) ∧ (∀ x, s.E (0,x) = d.E₀ x) ∧ ∀ x, s.B (0,x) = d.B₀ x
  ∀ s b U V t, A s U → A b V → 0 ≤ t → t < U → t < V → (∀ i z, s.f i (t,z) = b.f i (t,z)) ∧ (∀ x, s.E (t,x) = b.E (t,x)) ∧ ∀ x, s.B (t,x) = b.B (t,x)

theorem main : H1 → H2 → type_of% @OMA.S_wp_regularity_of_solutions_of_vlasov_maxwell_equations.main := by
  intro he hu ι _ P d hd
  have hpre := he ι P d hd
  choose U hU a hab using fun H : ℝ => hpre (max H 0) (le_max_right H 0)
  have un := hu ι P d hd
  have ha (t : ℝ) := hab t
  let s : Solution ι := ⟨fun i p => (a p.1).f i p,fun p => (a p.1).E p,fun p => (a p.1).B p⟩
  have heq (H t : ℝ) (ht : t∈Icc (0:ℝ) H) :
      (∀ i z, s.f i (t,z)=(a H).f i (t,z)) ∧
      (∀ x, s.E (t,x)=(a H).E (t,x)) ∧ (∀ x, s.B (t,x)=(a H).B (t,x)) := by
    apply un (a t) (a H) (U t) (U H) t _ _ ht.1 ((le_max_left t 0).trans_lt (hU t)) ((ht.2.trans (le_max_left H 0)).trans_lt (hU H)) <;>
      first | exact ⟨fun i => ((ha _).1 i).of_le (by simp), (ha _).2.1.of_le (by simp), (ha _).2.2.1.of_le (by simp), (ha _).2.2.2⟩
  have hsm : SmoothOnFiniteHorizons s := by
    intro T hT
    have htU : T ≤ U T := (le_max_left T 0).trans (hU T).le
    have sub {X : Type} : {z : ℝ × X | z.1 ∈ Icc 0 T} ⊆ {z | z.1 ∈ Icc 0 (U T)} := fun _ hp => ⟨hp.1,hp.2.trans htU⟩
    have hh := ha T
    exact ⟨fun i => ((hh.1 i).mono sub).congr (fun p hp => (heq T p.1 hp).1 i p.2),
      (hh.2.1.mono sub).congr (fun p hp => (heq T p.1 hp).2.1 p.2),
      (hh.2.2.1.mono sub).congr (fun p hp => (heq T p.1 hp).2.2 p.2)⟩
  have hregf (i : ι) : ContDiffOn ℝ 1 (s.f i) densityHalfSpace :=
    contDiffOn_halfspace_of_slabs (fun T ht => ((hsm T ht).1 i).of_le (by simp))
  have hregE : ContDiffOn ℝ 1 s.E fieldHalfSpace :=
    contDiffOn_halfspace_of_slabs (fun T ht => (hsm T ht).2.1.of_le (by simp))
  have hregB : ContDiffOn ℝ 1 s.B fieldHalfSpace :=
    contDiffOn_halfspace_of_slabs (fun T ht => (hsm T ht).2.2.of_le (by simp))
  have hpos (t : ℝ) (ht : 0 ≤ t) (i : ι) (z : Phase) : 0 ≤ s.f i (t,z) :=
    (ha t).2.2.2.1 i t ⟨ht,(le_max_left t 0).trans (hU t).le⟩ z
  have hL2E : TimeContinuousL2 s.E := by
    apply timeContinuousL2_of_slabs
    intro H hH
    obtain ⟨G,hG,hrep⟩ := (ha H).2.2.2.2.1
    refine ⟨G,hG.mono (Icc_subset_Icc_right ((le_max_left H 0).trans (hU H).le)),?_⟩
    intro t ht
    exact (hrep t ⟨ht.1,ht.2.trans ((le_max_left H 0).trans (hU H).le)⟩).trans
      (Filter.Eventually.of_forall fun x => ((heq H t ht).2.1 x).symm)
  have hL2B : TimeContinuousL2 s.B := by
    apply timeContinuousL2_of_slabs
    intro H hH
    obtain ⟨G,hG,hrep⟩ := (ha H).2.2.2.2.2.1
    refine ⟨G,hG.mono (Icc_subset_Icc_right ((le_max_left H 0).trans (hU H).le)),?_⟩
    intro t ht
    exact (hrep t ⟨ht.1,ht.2.trans ((le_max_left H 0).trans (hU H).le)⟩).trans
      (Filter.Eventually.of_forall fun x => ((heq H t ht).2.2 x).symm)
  have hcompact : CompactOnFiniteHorizons s := by
    intro H hH
    obtain ⟨K,hK,hk⟩ := (ha H).2.2.2.2.2.2.1
    refine ⟨K,hK,?_⟩
    intro i t ht
    rw [show (fun z => s.f i (t,z))=(fun z => (a H).f i (t,z)) from funext ((heq H t ht).1 i)]
    exact hk i t ⟨ht.1,ht.2.trans ((le_max_left H 0).trans (hU H).le)⟩
  have hequations : Equations P s := by
    intro t ht
    let H := t+1
    have htH : t ≤ H := by dsimp [H]; linarith
    have htU : t<U H := lt_of_le_of_lt (htH.trans (le_max_left H 0)) (hU H)
    have hh := (ha H).2.2.2.2.2.2.2.1 t ht htU
    have heqt := heq H t ⟨ht,htH⟩
    have hf (i : ι) (z : Phase) :
        derivWithin (fun r => s.f i (r,z)) (Ici 0) t =
          derivWithin (fun r => (a H).f i (r,z)) (Ici 0) t := by
      apply Filter.EventuallyEq.derivWithin_eq_of_mem (hx:=ht)
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show t<H by dsimp [H]; linarith))] with r hr hrH
      exact (heq H r ⟨hr,hrH.le⟩).1 i z
    have hE (x : Vec) :
        derivWithin (fun r => s.E (r,x)) (Ici 0) t =
          derivWithin (fun r => (a H).E (r,x)) (Ici 0) t := by
      apply Filter.EventuallyEq.derivWithin_eq_of_mem (hx:=ht)
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show t<H by dsimp [H]; linarith))] with r hr hrH
      exact (heq H r ⟨hr,hrH.le⟩).2.1 x
    have hB (x : Vec) :
        derivWithin (fun r => s.B (r,x)) (Ici 0) t =
          derivWithin (fun r => (a H).B (r,x)) (Ici 0) t := by
      apply Filter.EventuallyEq.derivWithin_eq_of_mem (hx:=ht)
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show t<H by dsimp [H]; linarith))] with r hr hrH
      exact (heq H r ⟨hr,hrH.le⟩).2.2 x
    simpa only [hf,hE,hB,heqt.1,heqt.2.1,heqt.2.2] using hh
  have hc : Classical P d s := ⟨hregf,hregE,hregB,(fun i t ht => hpos t ht i),hL2E,hL2B,hcompact,hequations,
    (ha 0).2.2.2.2.2.2.2.2.1,(ha 0).2.2.2.2.2.2.2.2.2.1,(ha 0).2.2.2.2.2.2.2.2.2.2⟩
  refine ⟨s,hc,hsm,?_⟩
  intro b hb t ht
  let V := t + 1
  have hv : t < V := by dsimp [V]; linarith
  apply un s b V V t _ _ ht hv hv
  case _ =>
    obtain ⟨f,e,b',p,⟨L,hL,rL⟩,⟨M,hM,rM⟩,k,q,i,j,u⟩ := hc
    exact ⟨fun α => (f α).mono (fun _ h => h.1),e.mono (fun _ h => h.1),b'.mono (fun _ h => h.1),fun α r hr => p α r hr.1,
      ⟨L,hL.mono Icc_subset_Ici_self,fun r hr => rL r hr.1⟩,⟨M,hM.mono Icc_subset_Ici_self,fun r hr => rM r hr.1⟩,k V (ht.trans hv.le),fun r hr _ => q r hr,i,j,u⟩
  case _ =>
    obtain ⟨f,e,b',p,⟨L,hL,rL⟩,⟨M,hM,rM⟩,k,q,i,j,u⟩ := hb
    exact ⟨fun α => (f α).mono (fun _ h => h.1),e.mono (fun _ h => h.1),b'.mono (fun _ h => h.1),fun α r hr => p α r hr.1,
      ⟨L,hL.mono Icc_subset_Ici_self,fun r hr => rL r hr.1⟩,⟨M,hM.mono Icc_subset_Ici_self,fun r hr => rM r hr.1⟩,k V (ht.trans hv.le),fun r hr _ => q r hr,i,j,u⟩

end
end OMA.R_wp_regularity_of_solutions_of_vlasov_maxwell_equations_R1
